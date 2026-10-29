# Concurrent writers in cairn: a comparison of designs

## Decision

The owner implements **B now**: one writer per shard, no global mutex. That is `ShardSet` on `main`: one `DB` per shard, the mutex only of that shard, `shardOf` to route. Each shard is still design A (one mutex, one log, one `sync`). **C** (serializable OCC inside the shard, with read and write sets) only if one shard falls short. D, E, and several writers of the same shard are not implemented. The phase report is in `docs/shards.md`.

`cairn-design-bench` (`Bench/Design.lean`) is the router bench: 1, 2, and 4 shards, file with `fdatasync` and memory, plus group commit and four tasks on a single shard. It is not part of `lake test`. It is not the program that produced the tables below.

The figures in the tables are from before `fdatasync` (PR #2) and from before `ShardSet`. They came from a harness that opened loose `DB`s and called `Handle.flush`. That source is not in the tree. They measure `flush`, not a disk barrier. The numbers with a real `sync` and with the router are in the README and in `docs/shards.md`. They are not redone here and they are not averaged with those.

## What this document was

A decision document. It does not implement concurrent writers. When it was written, `main` had one writer per `DB` (`Std.Mutex` per database, reads of an immutable `View`). The text keeps that comparison. The executable from then is not part of `lake test` and is no longer `Bench/Design.lean`.

Each figure below is one of two things:

- **Measured:** it came from a program in this repo, on the machine and with the method stated. The three repetitions are copied, not replaced by an invented mean.
- **Estimated:** there is no implementation to measure. The estimate rests on the measured cost of the current critical section and on the primitives Lean 4.35 has or does not have. It is marked.

## How to read this before deciding

1. On this disk, a file `put` costs tens of microseconds of Lean path. A `write` of a 31-byte record plus a `Handle` `flush`, measured separately, is under a microsecond. Joining several `flush`es (A's "group commit") **did not raise** the throughput of `DB.commit` across the three repetitions.
2. Four tasks on **the same** file `DB`, disjoint keys, lowered the aggregate relative to the single thread. The mutex does not parallelize a shard.
3. Four distinct file `DB`s (four mutexes, four logs), 500 `put`s each, kept per-operation latency near that of a single shard and raised the aggregate. That is already design B, and today it is obtained by opening N databases. What is missing is an owner that dispatches them; a new lock protocol is not missing.
4. OCC (C), 2PL (D), and a log per task (E) are not implemented. With Lean 4.35's primitives, validation and the sequencer fall back on a mutex: there is no compare-and-swap and no fetch-add in `Std` or in `Init`. D and E make recovery, proofs, or lock-free reads worse. They are not the path.
5. Recommendation: leave A as the writer of each shard; expose B (one `DB` per shard, no global mutex) if real writers are wanted on keys of different shards; leave C for later, and only as **serializable** OCC (read set and write set), beside `commit`, not in its place. F is that sequence, not a third system. The detail and the table are at the end.

## What there is today

A `DB` is a log, an in-memory index, and a `Std.Mutex Unit`. `DB.commit` enters the mutex, rejects the empty batch and the cross-shard batch, writes **one** record, does `Store.sync`, and only then publishes the `View` with `IO.Ref.set`. `set` discards the value of `ST.Ref.swap`. The comment on `swap` in Lean 4.35 says the exchange is atomic (`Init/System/ST.lean`). Readers (`snapshot`, `get`, `iterate`, `readLog`, `readEpoch`) only do `view.get`.

The mutex admission order is the serial order of the `Cairn.Hist` model (`Cairn/Snapshot.lean`): `state_eq_serial` and `snapshot_stable`. That file does not formalize the C++ memory model. The README says so. This comparison does not change that.

`Store.sync` in the code that measured this document was `Handle.flush`. In memory it is `pure ()`. Lean 4.35 has no `fsync` in the runtime: PR #2 added it with a C shim, and that barrier is not in the tables below. A `flush` survived `kill -9` in the demo already published (one run: 268 keys, a prefix). A power cut is not covered. The `kill -9` after the shim recovered 147 keys in another run; that is not a power cut either.

The index is an associative list (`Cairn/Map.lean`): `insert` walks the list. The `DB`'s in-memory log is `v.log ++ [record]` on every commit (it copies the spine). The memory backend, in addition, does `buf.modify (· ++ b)` and copies **every** byte of the log on every append (`Cairn/Store.lean`). `Ref.modify` is `implemented_by` an unsafe `take`/`put`; the memory backend uses that. The file backend writes the `ByteArray` to the descriptor.

Each `DB` has its own mutex. Opening N files is already N writers that do not share a lock. The README non-goal ("several writers at once") talks about several writers of the **same** `DB`. Across shards, B's parallelism does not require a new lock: it requires a place that owns the array of `DB`s and dispatches with `shardOf`.

A `DB.commit` batch is already one record and one `flush`. Several keys, one shard, one record's atomicity. That is group commit of **one** record. It is not "several records, one flush".

## Lean 4.35 primitives

Inventory read on the toolchain `leanprover/lean4:v4.35.0` (the repo pin). It is not an estimate.

Present, in `Std.Sync`: `Mutex`, `RecursiveMutex`, `SharedMutex` (one readers/writer lock, not a table per key), `Semaphore`, `Channel`, `Barrier`, `Notify`, `Broadcast`, `CancellationToken`, `StreamMap`. `BaseMutex.lock` documents that re-entering is undefined behavior, inherited from C++. `SharedMutex` the same.

Present: `IO.asTask`, `IO.wait` (on `IO` tasks it returns `Except IO.Error`), `Task.Priority.dedicated` (priority 9). The `Task.Priority` documentation says that above `Priority.max` (8) the task goes to a dedicated thread, and that the normal pool does not exceed the number of cores. On a single system thread, a task is still a computation: the design has to be correct if those tasks do not advance at once.

Present: `IO.Ref` / `ST.Ref`: `get`, `swap` (documented atomic), `set` = discard `swap`, `modify` logically as get+set but compiled with `take`/`put`. Present: `IO.monoNanosNow` and `IO.monoMsNow`.

Present on the file handle: `read`, `write`, `flush`, `rewind`, `truncate`, `lock` / `tryLock` / `unlock`. That `lock` is the system's lock on the descriptor (a whole file), not a lock per key.

Absent, searched in `Std` and `Init` as a concurrency primitive: compare-and-swap, fetch-add, and a user atomic word. Without FFI one cannot build a lock-free sequencer or a lock-free OCC validation. Cairn's core does not use FFI. Any concurrent commit on this list ends up serializing the moment "this record enters the log" with a mutex, a channel, or a single thread.

There is no `fsync` or `fdatasync` on `IO.FS.Handle`.

`IO.sleep` exists. It does not replace a disk barrier.

## How it was measured

This describes the `Handle.flush` harness, not the current `cairn-design-bench`. The current one prints `file-shards-N` / `mem-shards-N` rows through `ShardSet`.

Machine of this run, read before the bench:

- 4 CPUs online, 1 thread per core, Intel Xeon model 207, KVM hypervisor, x86_64.
- `/`, `/tmp`, and the workspace on `/dev/vdc`, ext4. The temporary directory from `IO.FS.createTempDir` falls on that volume. It is not a production disk and not a power cut.

Command of that harness (the binary had the same name, the source is gone): three passes in a row (`rep` 1, 2, and 3) in the same process, after 100 warmup `put`s. Clock: `IO.monoNanosNow`. Throughput: `ops * 1000000000 / wall_ns`, integer division. Percentile: the latency list is sorted and the index `(n - 1) * numer / denom` is taken. With 1000 samples, p50 is index 499 and p99 is 989. With 8 samples, p99 does not describe a tail: it is published anyway and is not used to decide. The **per-operation** timer (two clock reads) is inside the mean and the percentile. On a `put` of ~30 µs it is a small fraction. On a `write` of hundreds of nanoseconds it is a large fraction: those means are a ceiling.

What each row does:

| Row | What it times |
| --- | --- |
| `file_seq_put` / `mem_seq_put` | 1000 `DB.putStr` of distinct keys, on the calling thread. The per-operation clock includes building the key. |
| `file_batch_K` | 1024 operations split into batches of K. The batch is built **before** the clock. The clock is one `DB.commit` (one record, one `flush`). Latency is per commit, not per key. `ops_s` is per key. |
| `raw_records_then_one_flush` | 1024 `Handle.write` of the same 31-byte record and **one** `flush` at the end. One clock for the whole loop. |
| `raw_record_group_K` | Groups of K copies of that record, each group one `write` and one `flush`. |
| `file_parallel_shards_T` | T files, T `DB`s, T `Priority.dedicated` tasks, 500 disjoint `putStr` each. The `open`s happen before the clock. |
| `contended_file_*_4` / `contended_mem_*_4` | 4 tasks, **one** `DB`, 250 `put`s each. `disjoint`: distinct keys. `overlap`: all four write `ov0`…`ov249`. `hotkey`: all four write the key `"hot"`. |

The bench does not implement C, D, E, or F. It does not call `fsync`. It does not measure WASM, Android, or ESP32. It does not measure a power cut. The `kill -9` cited further down is the existing demo, one run, not this bench.

Measured size: `record_bytes=31` for the key `"k"` and the value `"v"`. After 1000 sequential `putStr` the file measures 33898 bytes in all three repetitions.

### Results (the three repetitions)

`ops_s` is key operations per second, integer. `mean_ns`, `p50_ns`, and `p99_ns` are from the per-operation sample, except on the batches (per commit) and on `raw_records_then_one_flush` (a single sample: the wall; the percentile adds nothing).

**File, one thread, distinct keys**

| rep | ops | wall_ns | ops_s | mean_ns | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1000 | 30327189 | 32973 | 30281 | 29730 | 61018 |
| 2 | 1000 | 29642816 | 33734 | 29599 | 28855 | 59704 |
| 3 | 1000 | 30073536 | 33251 | 30029 | 30115 | 61481 |

**Memory, one thread, distinct keys**

| rep | ops | wall_ns | ops_s | mean_ns | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1000 | 134083599 | 7458 | 134035 | 128133 | 302851 |
| 2 | 1000 | 132259971 | 7560 | 132212 | 126908 | 282331 |
| 3 | 1000 | 133708409 | 7478 | 133660 | 127202 | 294245 |

**`DB.commit` on a file, 1024 keys, batches of K (latency = one commit)**

| K | rep | commits in the sample | ops_s | mean_ns of the commit | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 1024 | 16584 | 59844 | 67724 | 117647 |
| 1 | 2 | 1024 | 20162 | 49242 | 50311 | 97765 |
| 1 | 3 | 1024 | 19836 | 50041 | 50150 | 98964 |
| 8 | 1 | 128 | 24278 | 327543 | 322777 | 708151 |
| 8 | 2 | 128 | 24927 | 319070 | 326325 | 654509 |
| 8 | 3 | 128 | 24500 | 324617 | 321285 | 669822 |
| 32 | 1 | 32 | 21743 | 1464644 | 1468048 | 2694297 |
| 32 | 2 | 32 | 22117 | 1439966 | 1445510 | 2674061 |
| 32 | 3 | 32 | 21818 | 1459746 | 1448231 | 2723044 |
| 128 | 1 | 8 | 19935 | 6392529 | 5799160 | 10058328 |
| 128 | 2 | 8 | 20351 | 6261311 | 5571880 | 10244928 |
| 128 | 3 | 8 | 20438 | 6235317 | 5546633 | 10069056 |

p99 with 8 or 32 samples is not used to decide.

**Raw handle, 31-byte record, 1024 records**

| series | rep | wall_ns | ops_s | note |
| --- | ---: | ---: | ---: | --- |
| 1024 `write`, one `flush` | 1 | 51019 | 20070953 | one clock for the loop |
| 1024 `write`, one `flush` | 2 | 35236 | 29061187 | |
| 1024 `write`, one `flush` | 3 | 39755 | 25757766 | |
| `write`+`flush` of 1 record | 1 | 426033 | 2403569 | mean per group 385 ns; includes two clocks |
| `write`+`flush` of 1 record | 2 | 398992 | 2566467 | mean 359 ns |
| `write`+`flush` of 1 record | 3 | 417547 | 2452418 | mean 377 ns |
| group 8 | 1 | 64407 | 15898892 | mean per group 471 ns |
| group 8 | 2 | 62677 | 16337731 | mean 458 ns |
| group 8 | 3 | 66644 | 15365224 | mean 489 ns |
| group 32 | 1 | 25894 | 39545840 | mean 774 ns |
| group 32 | 2 | 24615 | 41600650 | mean 733 ns |
| group 32 | 3 | 31357 | 32656185 | mean 935 ns |
| group 128 | 1 | 18370 | 55743059 | 8 groups; mean 2247 ns |
| group 128 | 2 | 16383 | 62503814 | mean 2000 ns |
| group 128 | 3 | 20836 | 49145709 | mean 2546 ns |

**Parallel shards (distinct files)**

| tasks | rep | ops | wall_ns | ops_s | mean_ns | p50_ns | p99_ns |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 500 | 21465036 | 23293 | 41871 | 41142 | 82692 |
| 1 | 2 | 500 | 21465646 | 23293 | 41956 | 41208 | 81566 |
| 1 | 3 | 500 | 21694253 | 23047 | 42171 | 41511 | 88691 |
| 2 | 1 | 1000 | 21909382 | 45642 | 42747 | 41673 | 87635 |
| 2 | 2 | 1000 | 21929511 | 45600 | 42777 | 41984 | 96426 |
| 2 | 3 | 1000 | 22062723 | 45325 | 42885 | 41766 | 89411 |
| 4 | 1 | 2000 | 22041037 | 90739 | 42820 | 42177 | 83238 |
| 4 | 2 | 2000 | 35770199 | 55912 | 56445 | 54307 | 134512 |
| 4 | 3 | 2000 | 26788890 | 74657 | 45959 | 44063 | 88509 |

**Four tasks, a single `DB`**

| series | rep | ops_s | mean_ns | p50_ns | p99_ns |
| --- | ---: | ---: | ---: | ---: | ---: |
| file disjoint | 1 | 13563 | 152125 | 73699 | 149284 |
| file disjoint | 2 | 12829 | 152500 | 83550 | 143432 |
| file disjoint | 3 | 13599 | 148896 | 74030 | 152469 |
| file overlap | 1 | 23712 | 106468 | 48676 | 76936 |
| file overlap | 2 | 20905 | 104212 | 48403 | 80611 |
| file overlap | 3 | 22551 | 93892 | 48362 | 71362 |
| file hotkey | 1 | 49098 | 40026 | 20210 | 37206 |
| file hotkey | 2 | 48085 | 42690 | 20172 | 37589 |
| file hotkey | 3 | 48984 | 39530 | 19960 | 39162 |
| mem disjoint | 1 | 1788 | 1050493 | 552890 | 1135407 |
| mem disjoint | 2 | 1773 | 1054985 | 554654 | 1148339 |
| mem disjoint | 3 | 1777 | 1058169 | 556095 | 1172176 |
| mem overlap | 1 | 1946 | 969363 | 508179 | 1092374 |
| mem overlap | 2 | 1938 | 1001232 | 514643 | 1071759 |
| mem overlap | 3 | 1884 | 987175 | 510487 | 1310214 |
| mem hotkey | 1 | 2270 | 838787 | 439628 | 885268 |
| mem hotkey | 2 | 2170 | 890297 | 447402 | 980083 |
| mem hotkey | 3 | 2247 | 853707 | 439758 | 890955 |

Earlier measurements, **one** run, millisecond clock (`IO.monoMsNow` in `cairn-bench`), copied from the README. They are not 1:1 comparable with the nanosecond table: 20 ms has 1 ms granularity, and that loop does not take a clock per operation.

```
file put: 1000 ops in 20 ms (50000 ops/s)
file get: 1000 ops in 9 ms (111111 ops/s)
concurrent get (4 tasks x 2000): 8000 ops in 409 ms (19559 ops/s)
```

`kill -9` demo, one run already published: `recovered 268 keys, a prefix of the committed writes`.

### What can be read from those numbers

The `flush` of this ext4, with the kernel page cache, does not explain the `put`. The cleanest I/O figure is 1024 `write`s and one `flush`: 35236, 39755, and 51019 ns (between about 20 and 29 million records/s). A `write`+`flush` per record, with the clock inside the loop, gives means of 359, 377, and 385 ns. A `file_seq_put` sits at means of 29599, 30029, and 30281 ns. The `DB.putStr` path is on the order of eighty times that `write`+`flush` with the clock included, and on the order of a thousand times the loop with a single `flush`. **Estimated from that subtraction:** removing `flush` from the path, or grouping them, moves less than a microsecond of a `put` of ~30 µs. **Measured, consistent with that:** batches of 8, 32, and 128 keys did 19935–24927 ops/s, below the 32973–33734 of the sequential `put`. Making the record larger did not pay. The batch of 1 key (16584–20162 ops/s) also landed below the sequential `putStr`: the batch keys are longer and the process had already run the memory sweep. That difference is not isolated.

Sequential memory (7458–7560 ops/s, mean ~132–134 µs) is slower than the file on the same growing index. The code copies the entire byte list on every append. That is a defect of the memory backend for this bench, not a model of "pure CPU".

Four tasks on one file, disjoint keys: 12829–13599 ops/s, below the single thread. The per-operation mean (~149–153 µs) includes the mutex wait; the wall also gets worse (about 74–78 ms against about 30 ms). Overlapping 250 keys lands in the middle (20905–23712). The key `"hot"` rises to 48085–49098 ops/s with p50 ~20 µs, **with four tasks on the same mutex**. The map stays at one entry. The direction fits the cost of `insert` on a list that grows, but this bench does not separate index, encoding, the `log ++ [record]` copy, and the mutex with a profiler. I do not attribute the whole 30 µs to the list. What is measured: in the current design, "more key contention" is not the term that dominates; the large term across these series is the size of the map and the fact of sharing one mutex and one log.

Distinct shards: 1 dedicated task, 500 puts, 23047–23293 ops/s, p50 ~41 µs (the thread hop already costs relative to the calling thread at ~33k). 2 tasks, 1000 puts: the wall stays at ~22 ms and the aggregate rises to 45325–45642 ops/s; p50 stays ~42 µs. 4 tasks, 2000 puts: walls 22041037, 26788890, and 35770199 ns; aggregates 90739, 74657, and 55912 ops/s. Two repetitions scale near one shard's wall; the second does not. Per-operation latency stays in one shard's band on the first and the third (p50 42177 and 44063 ns) and rises on the second (p50 54307). **Measured:** there is real parallelism across files on 4 vCPU, with scatter, and it is not a clean 4×. **Measured:** it does not appear inside one file.

Concurrent reads were not measured again here. The old figure (4 tasks reading, 19559 ops/s, a millisecond clock) is still a single run. The read design (one `Ref.get` of an immutable `View`) is the one A–F can keep. C and D lose it if a read takes an exclusive lock.

## The designs

In all of them, a record is still the atomic batch of one shard. A batch with keys from two shards is rejected. There is no two-phase commit. Reads that do not take the mutex still see an old `View` or a new one, not a half one, to the extent that `swap` is the exchange the runtime documents. That is not proved in the Lean kernel.

### A. One writer, mutex, group commit

This is today's `DB`, with the option of joining several commits into fewer `flush`es.

**Isolation.** The current model is serializable by admission order: `Hist` is a sequence of batches, `state_eq_serial` says the state is the fold of that sequence, `snapshot_stable` says a snapshot does not change when the history grows. It is not snapshot isolation. There is no write skew: whoever writes, writes only inside the mutex, seeing the map of the previous commit.

**Conflicts.** There are no aborts by key. Two `put`s of the same key are ordered. The second wins. An empty or cross-shard batch fails and is not appended (`commitNow`'s code, covered by tests).

**Performance, disjoint keys.** **Measured** on one `DB`: 32973–33734 ops/s, p50 ~29–30 µs, p99 ~60–61 µs, 1000 keys. **Measured:** grouping 8, 32, or 128 operations into one record and one `flush` did not beat that figure (19935–24927 ops/s). **Estimated:** on a future backend with a real disk barrier (it does not exist in Lean 4.35; `fsync` was not measured), grouping would lower the number of barriers. Today the `flush` saving fits in the fraction of a microsecond the handle already measured, beside a `put` of ~30 µs.

**Performance, contention.** **Measured:** 4 tasks, one file, disjoint keys, 12829–13599 ops/s. The mutex queue lengthens latency (p50 ~74–84 µs, p99 ~143–152 µs). The single key was faster because of the small map, not because the mutex scales.

**Complexity in Lean.** The smallest. `commitNow` already exists. A group commit of several **records** would be a loop of append and one `sync`, still under the same mutex. CAS is not needed. It fits in 32 bits: it does not touch the codec.

**Proofs.** What is already there: the `Hist` model, the crash prefix (`recovery_prefix`, `decodeFile_prefix`), the stable snapshot. A group commit that writes several records and does one `flush` is **not** a single atomic step against a cut: `recovery_prefix` says a prefix of records survives. That would have to be stated, not redone. What cannot be proved: that the C++ mutex admits no two sections, that `swap` is atomic, that `flush` is durable, that the CRC catches everything.

**Crash, compaction, shards, replicas.** One log, one prefix, one compaction that reassigns LSNs and forces `installSnapshot`. Each shard that is a `DB` stays the same. The follower that diverges loses the suffix (the leader wins). A does not change that.

**WASM / ESP32.** Correct on one thread. The mutex is a queue; if there are no threads, the queue has one client. No parallelism is gained. That runtime was not measured.

**What is lost.** Parallelism inside the shard and, if the caller uses a single `DB` for every key, also across shards. Isolation and the prefix theorem are not lost.

### B. One writer per shard

Parallel across shards, serialized inside. Each shard is a cairn with its log, its mutex, and its commit point. There is no global mutex.

**Isolation.** Serializable **inside** the shard, by the same `Hist`. There is no global serial order. Two commits on different shards are not ordered with respect to each other. That is already the project's rule: a batch does not cross a shard. A read that joins several shards sees a mix of snapshots; it is not a cross-cutting snapshot. That has to be said in the router's API.

**Conflicts.** The same as A inside the shard. Zero aborts from a race across shards: the keys do not overlap, by `key_one_shard` (one key, one id, in one epoch).

**Performance, disjoint keys.** **Measured** with N file `DB`s, still without a router (the dispatch would be a call to `shardOf` plus an array; **estimated** negligible beside 30 µs):

- 1 shard on a dedicated task: 23047–23293 ops/s, p50 ~41 µs.
- 2 shards: 45325–45642 ops/s, p50 ~42 µs, wall ~22 ms, the same as 500 puts.
- 4 shards: 55912, 74657, and 90739 ops/s. The best wall (22041037 ns for 2000 puts) matches one shard of 500; the worst (35770199 ns) does not. Real scatter on 4 shared vCPU.

**Estimated:** on one thread (WASM without pthreads, ESP32) the aggregate returns to that of one writer, because the tasks do not advance at once. Correctness does not depend on that.

**Performance, contention.** A hot key lives on one shard. That shard is A. **Measured** the case of one `DB`: it does not scale. **Estimated:** splitting the range to split the hot key cannot be done if it is a single key; that would need C or splitting the value, and splitting the value is another product.

**Complexity.** Small and additive. A module that owns `Array DB` (or a list), opens one file per id, and routes `put`/`get`/`commit`. `sameShard` already rejects the crossed batch. `commitNow` is not rewritten. The mutex per `DB` is already there. It fits the 32-bit targets: the router is byte arithmetic and an array of databases.

**Proofs.** Already: `shardOf` total and deterministic, `key_one_shard`, `rebalance_partition`, `move_replays`. Can be added: the id the router chooses is the array index (a function, easy). Each shard keeps its `Hist`; a global `Hist` is not needed, and a global `Hist` would be false. The temporal overlap of the threads cannot be proved. The stress test (two shards, tasks) is the evidence of parallelism, not a theorem.

**Crash, compaction, shards, replicas.** Each log recovers on its own, with today's prefix. A compaction rewrites the LSN of **that** shard; that shard's follower does `installSnapshot`. The other shards do not hear about it. `adopt` remains the local move. A half cut across two shards does not appear, because there is no commit that covers them: either each one committed, or it did not. A crash can leave shard 0 updated and shard 1 not. That is what "no transaction across shards" means on disk.

**WASM / ESP32.** The same code runs on one thread. Several files mean several descriptors; on a microcontroller the limit is the number of open files and the index RAM per shard, not the lock. **Estimated**, with no measurement on ESP32.

**What is lost.** A serial order of the whole process. A snapshot that cuts every shard at once. Nothing of the intra-shard isolation.

### C. Optimistic MVCC inside the shard

`transact`: a `View` is taken, reads and writes happen in private, and at commit it is validated against what entered after the snapshot. If it fails, nothing is appended and it retries. The append is still a short section.

Two variants, and they do not give the same isolation:

- **Write-write only** (the write set collides with a later commit): snapshot isolation. Reads are the snapshot. Two transactions can read the same two values and each write a different key; both commit. That is write skew. The state is not that of any serial order. Today's `Hist` **rejects** that interleaving because the second writer would have seen the first's write.
- **Write-write and read-write** (the read set collides with the write set of a later commit), validated in the same step as the append: serializable OCC, equivalent to commit order. This is the one that keeps the sentence "commit order is a serial order".

I recommend not implementing the weak variant. Dropping to SI without saying so would break the guarantee `state_eq_serial` states for the single writer.

**Conflicts.** Abort if validation fails. The abort does not write. Under disjoint keys and transactions that do not read what another writes, **estimated:** almost no aborts. Under a hot key, **estimated:** retries in a chain; there can be livelock if everyone retries without waiting. There is no measurement: there is no `transact`. A random wait uses `IO.sleep` (millisecond granularity) or a loop; both are awkward, and neither is measured here.

Validation has to happen in the same section that decides the LSN and the append. Without CAS, that section is the shard mutex (or a single actor). OCC does not take the commit out of the mutex. It takes out of the mutex the work **before**: the user's reads and computation.

**Performance, disjoint keys.** A `put` of an already prepared key is almost all critical section (encode, append, index, publish). **Measured** that block: ~30 µs mean on a file, of which the `flush` is a fraction of 1 µs. **Estimated:** OCC does not multiply the throughput of today's `put`/`commit`, because there is no work to move outside the lock. It can help a transaction that reads several keys, computes, and writes: snapshot readers do not take the mutex (same as now) and only the commit takes it. The ceiling of commits per second of one shard is still A's.

**Performance, contention.** **Estimated:** worse than A on a hot key, because of the retry. A queues and each attempt writes once. C queues the same way at validation and, in addition, throws the work away if it collides. The read set costs RAM; on an ESP32 that matters before the CPU.

**Complexity.** Large. Transaction types, sets, retry, and a protocol for "compaction and epoch change invalidate in-flight snapshots". If they are not invalidated, a transaction validates against a log that is no longer the index's. `follow` / `installSnapshot` also change the log under the mutex: a snapshot taken before is stale in epoch, not only in LSN.

Lean is enough to write it: `IO.Ref`, mutex, `Task`. It is not enough to validate without a lock.

**Proofs.** In a new model (not in the C++):

- A commit that passes WW+RW validation is an extension of `Hist` in commit order, and the state is the serial fold. This is provable if validation is written as a pure function on the history.
- An abort does not appear in `Hist.commits`.
- The WW-only variant does **not** satisfy `state_eq_serial` for every interleaving of reads. The write-skew counterexample can be given as a negative theorem (there exists a history accepted by the weak validation whose map is not any serial fold of those read transactions). It is worth proving so that SI does not slip into the README.

Cannot be proved: absence of livelock, that the retry loop implements the model, the memory model, or that a snapshot read by `Ref.get` is the one validation believes.

**Crash.** The record of a validated commit is the usual one: either it enters whole or the cut drops it (`recovery_prefix`). An abort has no bytes. A group commit of several validated commits in one `flush` returns to the prefix: the crash can keep the first records of the group. Each record stays atomic by the length framing. Validation does not survive the process; on reopen there are no half-done transactions. That is an advantage over locks stored in the log.

**Compaction, replicas, shards.** Compaction changes the LSNs. An in-flight transaction has to abort if the epoch or the identity of the log changes (`compact`, `adopt`, `installSnapshot`). The replica still receives already committed records, not read sets. B+C (see F) leaves the replica as it is.

**WASM / ESP32.** Retry is correct on one thread if the commit does not re-enter the mutex. A `Task` that takes the mutex and waits for another `Task` on the same thread blocks. C's code must not wait inside the lock. Read sets are the RAM cost.

**What is lost**, if SI is chosen: serializability, and the README's current statement. If serializable OCC is chosen: nothing of the isolation, and a new class of failures is gained (aborts) that A does not have. A single-key `put` should not pay them: it can stay on A's path.

### D. 2PL, locks per key or per range

Two-phase locking: shared locks to read, exclusive locks to write, release them all after the commit. Done right, the lock order is serializable (conflict-serializable). It is not SI. A read set is not needed if the locks are held until the end.

**Conflicts.** Wait, not abort, except for deadlock. Deadlock is this design's failure in Lean: the mutex is not re-entrant, the task pool is finite (on the order of the cores, `Task.Priority` documentation), and a lock order that is not total blocks. A lock per key with `Std.Mutex` would be a huge table and each lock is a runtime object. `SharedMutex` is **one** lock, not a table. `Handle.lock` locks the whole file: it serves as a latch between processes, not as key 2PL.

To keep the lock-free read one would need MV2PL (write locks plus read versions). That is more machinery than C, and the versions are already given by the `View`.

**Performance.** **Estimated**, anchored to the measurement: each `put` of A already enters a mutex. Adding per-key locks **inside** that mutex does not parallelize. Taking them **outside** requires either many mutexes (memory, deadlock) or a lock manager. Disjoint keys could advance at once only in the section that does not touch the log. The log is still one, so the append serializes the same way as in C. The commit ceiling is A's, with more instructions per operation. Contention: queues per key and deadlock risk; **estimated** worse latency than A, with no numbers.

**Complexity.** The highest on the list along with E, and the worst fit for the repo's style. A total order of keys has to be defined to avoid deadlocks (the byte order already exists: `keyLe`) and it has to be proved that all the code respects it, including `compact` and `follow`, which today take the `DB` mutex and cannot take a key lock without a hierarchy. `compact` under 2PL is a transaction of every key.

**Proofs.** A model of schedules, a wait graph, and "total lock order ⇒ no cycle" is provable and long. Connecting it to `Hist` too. It does not cover the runtime or the UB of re-entering. It is more surface than pure OCC, where validation is a function on lists.

**Crash.** A lock is not durable. A crash drops the locks when the process dies; the log recovers as today if the append is still the commit point. Whoever wanted locks in the log (for transactions that survive the process) leaves cairn's model. It is not needed.

**Compaction, replicas, targets.** Compaction has to take every lock or abort the holders: easy to get wrong. The replica does not see locks, it sees records: fine. On a single thread, waiting for a lock the same task holds is a sure deadlock. On ESP32 the lock table competes with the index for RAM. 32 bits: the codec does not change; the table may not fit.

**What is lost.** The `Ref.get` read, if reads take shared locks. Simplicity of the model is lost. A commit ceiling above A is not gained.

### E. A log per writer, merge by LSN

Each task appends to its own log. A global LSN orders the merge. It looks like the per-core structured-log pattern.

**Isolation.** It depends on the merge.

- A merge by LSN of writes only, last LSN wins: updates are lost. It is not even SI. Two `put`s of the same key on two logs do not see each other until the merge, and the loser disappears.
- A merge that applies OCC (read sets included): it is C plus N logs. The isolation is C's. Recovery is worse than C's.

**Conflicts.** Without read sets, the conflict is resolved by dropping a value (lost update), not by aborting. With sets, aborts as in C, and in addition one has to merge before validating or validate in the merge.

**The LSN.** Assigning a unique increasing LSN with no durable gaps requires a sequencer. There is no fetch-add. The real options are: a mutex (then the sequencer is A, and the split logs only parallelize the `write`), or an LSN per log plus a clock that does **not** give a total order reproducible after a crash. A crash can leave the files at lengths that do not determine which record "went first" if the LSN was not persisted in one place before the ack. **Estimated** the failure; the absence of the primitive is a fact of the toolchain.

**Performance, disjoint keys.** Parallel `write` is what the shard bench already measured (several files). The bottleneck of a `put` is not the `write`. **Estimated:** N logs do not bring the `put` near the 20–29 million records/s of the raw handle, because the index, the encoding, and publishing the `View` stay somewhere serial if a coherent snapshot is wanted. If each log has its own index, that is B under another name and without the deterministic router: worse, because a key could fall in two logs.

**Performance, contention.** **Estimated:** the merge of a hot key is a single thread, plus the cost of reading N logs. Worse than A.

**Complexity.** High. N file handlers, a merge format, a criterion of "already durable". It clashes with the current codec, which assumes one byte stream and one prefix.

**Proofs.** `decodeFile_prefix` is per stream. There would be a new theorem: if a durable total order exists (a list of LSNs written in one place before answering the client), the merge is a function and replay matches that order. Without that place, the statement is false and must not be pretended. Compaction of N logs to one snapshot is `moved` at large scale; provable, and it forces followers to install, not to append across the boundary (same as today, per log).

**Crash, replicas.** Today's follower applies **one** log (`appendEntries` with `prev` = length). N logs are N replica units or a merge before replicating. Merging before replicating returns the bottleneck to one log. Replicating N logs pushes consensus out of reach (the project has no quorum and no term). A cut in the middle of the merge has to fall on the prefix of **each** stream and on an agreed order. That is the point where E loses what cairn has already proved.

**WASM / ESP32.** N files and N buffers on a device without threads: the complexity is paid and the parallelism is not. Few descriptors.

**What is lost.** The one-prefix theorem, the replica unit, compaction of one log, the deterministic order after a cut if the sequencer is not durable. It is not a good trade: the I/O parallelism E would look for was already measured in B, and I/O is not the bottleneck.

### F. Hybrid B+C

One logical writer per shard for the append (B's mutex) and, inside the shard, serializable optimistic transactions (C) whose pre-commit work runs without the lock.

It is not B+D or B+E. Putting 2PL or split logs inside the shard drags the problems of D and E into each range.

**Isolation.** Across shards, B's (no global order). Inside, C's serializable isolation if validation is WW+RW. The composition is: each key one shard (`key_one_shard`), and inside that shard the commit order is a `Hist`. A transaction does not touch two shards. Write skew **across** shards can exist even if each shard is serializable: it is the same limitation the project already has, not a new one. Inside the shard it must not exist.

**Conflicts.** Aborts only intra-shard. A key on another shard does not abort.

**Performance.** B's on keys of different shards (**measured** the N-files case). C's inside the hot shard (**estimated**: it does not improve the short `put`; it does let computation run outside the lock). Group commit inside the shard's commit: **measured** that a large record does not raise ops/s with `flush`. It still serves as batch atomicity, which is already `DB.commit`.

**Complexity.** The sum, in that order. Implementing C before having the router of N `DB`s optimizes the hot shard and leaves the disjoint case, which is the one the bench does speed up, in the caller's hands.

**Proofs.** B's plus C's. A product proof is not needed if the transaction does not cross the shard: prove that `transact` only looks at its `DB`'s `Hist`.

**Crash, compaction, replicas, targets.** The same as B for the disk and the replica (one log per shard, already validated records). The same as C for in-flight snapshots against `compact` and `adopt`. On one thread, B+C is A plus a retry that must not re-enter the mutex.

**What is lost.** What is lost in C (aborts, set RAM) on each shard that turns `transact` on. Shards that only do `put` do not have to lose it.

### Something the bench suggests that is not a writer

The gap between the raw handle and `DB.put`, and the gap between the single key and the 1000 distinct keys, are not closed with locks. Two costs are in the code and show up in the figures, without this bench isolating them with a profiler:

- The memory backend copies every byte on every append. **Measured** the aggregate effect: 7458–7560 ops/s against 32973–33734 for the file, same key pattern.
- The index walks a list, and `v.log ++ [record]` copies the spine on both backends. The `hotkey` series (p50 ~20 µs, a one-key map, even with four tasks) against `file_seq_put` (p50 ~29–30 µs, a growing map, one thread) goes in that direction. It is not a controlled experiment: the threads and the map size change at once.

**Estimated:** an index with a flatter cost and a buffer that is not `List UInt8` raise one shard's `put` more than grouping `flush` does. There is no figure for an alternative index. Touching `Map` reopens the `get`/`insert`/`replay` theorems. It does not change the log format. It is independent of A–F and, in performance, prior to C and to E. It does not replace B: B multiplies shards; the index speeds each one.

## Table

"Disjoint" and "contention" are key throughput. Where it says measured, the range is the minimum and the maximum of the three repetitions on this machine. Where it says estimated, there is no code.

| | Isolation | Aborts | Disjoint keys | Contention on one shard | Lean 4.35 | What can be proved | Crash and replica | One thread / small RAM | What is lost |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **A** mutex ± group commit | Serializable by admission (`Hist`) | Not by key | **Measured** 33.0–33.7k ops/s one thread. Batches 8–128: 19.9–24.9k, they do not improve | **Measured** 4 tasks, one file, disjoint: 12.8–13.6k ops/s | Mutex and `Ref`. No CAS. No `fsync` | Already: `state_eq_serial`, `snapshot_stable`, prefix. Not: C++, `flush`, CRC | One log, prefix. Several records in one `flush` are still a prefix, not an atomic group | Correct. No speedup | Parallelism |
| **B** one writer per shard | Serializable in the shard. No global order | No | **Measured** 4 files: 55.9–90.7k ops/s; p50 ~42–54 µs | Same as A on the hot shard | Same. N `DB`s already have N mutexes | `key_one_shard` + one `Hist` per `DB`. Not the overlap of threads | N logs, each with today's prefix. Replica per shard | Correct in series. N files, N indexes | Global snapshot and global order |
| **C** OCC in the shard | Serializable if WW+RW. SI if WW only (write skew) | Yes, and retry. Livelock possible | **Estimated:** the short `put` does not pass A's ceiling (~30 µs). It helps if there is computation outside the lock | **Estimated:** worse than A (retries). No measurement | Validation under the mutex. No CAS to avoid it | Pure model: commit = extension of `Hist`; abort outside the log; negative theorem for SI | The validated record uses the current prefix. Snapshots die on compaction and on epoch change | Correct if one does not wait inside the lock. Read sets spend RAM | Aborts. SI would lose the current serializability |
| **D** 2PL | Conflict-serializable if there is no deadlock | Wait; deadlock if the order is not total | **Estimated:** commit ceiling = A, with more work. The log is still one | **Estimated:** queues and deadlocks. `SharedMutex` is not a table | Non-reentrant mutex + finite pool. `Handle.lock` is the whole file | Schedule and lock order, long. Not the runtime | Locks are not durable. The log, if the append is the commit, recovers as A | Deadlock is easy on one thread. Lock table in RAM | The lock-free read, if the read blocks |
| **E** log per task + LSN | Lost update, or C if the merge validates | Depends on the merge | **Estimated:** the parallel I/O was already seen in B and is not the `put`'s bottleneck | **Estimated:** the hot-key merge is one thread | Without fetch-add the durable LSN is a mutex | Prefix **per stream**. Total order only if the sequencer is durable and unique | Breaks the replica unit or rebuilds it at the merge. The crash does not determine the order if the LSN was not stored before the ack | N files, zero real parallelism | The one-log theorem, the simple replica, the order after the cut |
| **F** B then C | B across shards, serializable C inside | Only inside the shard | B's, **measured** | C's, **estimated** | Sum of B and C | Composition: `transact` does not look at another shard's `Hist` | One log per shard of already validated records | Same as B and C | C's, only on the shards that use `transact` |

## Recommendation

Leave the writer of each `DB` as it is (A). Do not invest in grouping `flush` to gain ops/s: on this ext4, with `Handle.flush` and without `fsync`, the three repetitions say it does not. Keep `DB.commit` as the group commit it already is: one record, one `flush`, several keys of one shard.

If the goal is "real writers", the step the measurements support is B: a value that owns one `DB` per shard and dispatches with `shardOf`, with no global mutex. Parallelism across files has already been seen (aggregate 55.9k–90.7k ops/s on 4 shards against 23.0k–23.3k of one shard on a dedicated task, with one repetition clearly worse). Inside the shard the contract does not change, so the `Hist` and recovery proofs stay. The API has to say that there is no serial order across shards and no snapshot that cuts them at once.

Do not do D. Do not do E. Both cost more than the bench says can be gained, and E lets go of the single prefix that is already proved.

Do not do C yet. When there are transactions that read, compute, and write inside a hot shard, make it serializable (WW and RW), under that shard's mutex, with an abort that does not append, and leave `put` / `commit` on A's path. Declaring SI would lower the guarantee of the current model. F is exactly "B first, and C only if one shard falls short": a design with another name is not needed.

Before expecting more ops/s from a single shard, measure an index that does not walk a list and a memory backend that does not copy the whole log. It is an estimate of where the time is; the only firm figure is the gap already measured between `put` (~30 µs) and the handle (the loop of 1024 `write` and one `flush`, 35–51 µs **in total**).

## Phased plan

No deadlines. The size is that of the modules and of the proof surface.

**Phase 0. This note.** Branch `docs/concurrencia` (the branch name from when the note was written). It does not enter `main` until it is merged by hand. It does not change the runtime.

**Phase 1. Owner of N databases (B).** A new module beside `Cairn/Router.lean` and `Cairn/DB.lean`. It opens one file (or one `Store`) per shard id, keeps the array, and routes get/put/commit/iterate. It does not add a mutex above. `commit` of a batch that crosses the range still fails. New proofs: the array id is `shardOf`; a test with tasks on two files, in the style of the stress test that already exists. Proofs that are reused: `key_one_shard`, `Hist` per each `DB`, `recovery_prefix` per each file. The codec is not touched. Correct if the runtime runs the tasks on a single thread; the speedup is native only. This branch's bench is used again, pointed at the router instead of at the loop that opens the `DB`s by hand.

**Phase 2. Do not do, unless a disk barrier appears.** Join several records into one `flush` inside `commitNow`. Short code. The README has to say that a cut can keep a prefix of the group (`recovery_prefix` already gives that). Throughput: not the goal, with the figures above. Truly blocked if durability under power loss is wanted: `IO.FS.Handle` has no `fsync`, and the core does not use FFI. An external backend that does sync would be a new `Store`, outside this phase.

**Phase 3. Serializable OCC in one shard (the C half of F).** Only with a real use of long transactions. A new module (`transact`, sets, retry with a cap). The commit validates and appends under the existing mutex. `compact`, `adopt`, `installSnapshot`, and `setEpoch` mark live snapshots invalid. A single-key `put` does not go through there. A new model beside `Snapshot.lean`: pure validation, extension of `Hist`, abort absent from the log, and a theorem that WW-only validation admits a write skew. Stress tests against a sequential model, disjoint and in conflict, plus a cut in the middle of a commit (the half record is already covered by the prefix). Large surface, localized: it does not rewrite the router or the codec. It is still not a proof of the C++ mutex.

**Explicitly out:** D, E, commit across shards, quorum, and any lock-free sequencer.

**Cross-cutting, when one wants to bring the ~30 µs down:** an index and buffer experiment, with the same bench, before taking it as given that C is needed. If `Map` changes, the lemmas that unfold `insert` and `remove` are redone. The log file does not change format.
