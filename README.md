# cairn

A small key-value store written in Lean 4 (toolchain `v4.35.0`, the same pin as [uvl](https://github.com/kidandcat/uvl)). One process, one writer, an append-only log, and an in-memory index rebuilt on open. The log and the router are shaped so a later version can run several independent cairn processes as shards and replicas without replacing the codec or the map.

It is meant for Lean apps that need to keep a map (game state, settings) on the targets uvl cares about: native Linux and macOS now, WebAssembly, Android, and a 32-bit microcontroller later. The core does not call FFI. Lengths in the codec are `UInt32` and sequence numbers are `UInt64`. There is no `USize` in the codec.

This is not a SQL database.

## Guarantees

- `put` and `delete` are applied by folding one record. A record is one batch. `get` after a batch that ends in `put k v` is `some v`. A batch that ends in `delete k` removes `k`.
- A crash that keeps a byte prefix of a well-formed encoding decodes as a prefix of the records (`decodeFile_prefix`, `recovery_prefix`, both under `RecordsFit`). `recovery_keeps_synced` is the sync contract: if that prefix covers every byte of the groups whose `sync` had already returned, those groups are in the recovered state, and the state is still a prefix of what was sent. The failure model is a synced stable image plus any sector-prefix of the unsynced tail, or none of that tail. It is not a theorem about arbitrary junk after a valid file.
- `Storage.sync` is the barrier. The native file backend implements it with `fdatasync` on Linux and `F_FULLFSYNC` (then `fsync` if that fails) on macOS, and it `fsync`s the parent directory after creating or renaming a file. A commit is acknowledged only after `sync` returns. Compaction writes a new file, data-syncs it, renames it, then fsyncs the directory. The memory backend's `sync` returns immediately; it is not a disk.
- Frames are aligned to 4096 bytes. The proof treats that as the sector size. A larger physical sector can tear bytes a successful `sync` already returned.
- The frame checksum is non-reflected CRC-32, polynomial `0x04C11DB7`, init 0, no final xor (`sum32`). Proved: every error whose set bits lie in some window of 32 consecutive positions, at every message length. A one-bit error is that window with width 1. Two bits at distance 1 to 31 are the same window. Proved false: that every odd-weight error is detected (`sum32 [1, 4, 0xC1, 0x1D, 0xB7] = 0`, Hamming weight 15). Not proved: two bits farther apart. No fixed-width checksum rejects every altered string.
- A torn tail is truncated. A bad frame with a later valid frame is `corrupt log` and `openFile` throws. `openFileRepair` truncates that damage on purpose. A file that is not a cairn file is left in place. None of these paths drops a bad frame silently.
- Each record still carries the reflected ISO CRC-32 (`crc32`). That is a different function from the frame checksum.
- `kill -9` is not a power loss. One run of `scripts/crash_demo.sh` on this machine recovered 147 keys, a prefix of the writes. The process was killed; the disk was not.

## Non-goals

- SQL, a query planner, or a page cache.
- A cross-shard transaction. A batch whose keys fall in more than one shard is rejected. There is no two-phase commit.
- Network, elections, terms, votes, quorums, or a commit index. See [Replication](#replication).
- Several writers at once stays a non-goal. Callers may overlap; the mutex runs their commits one at a time.
- Hardware that reports a successful flush without writing the bytes. A physical sector larger than 4096 bytes. Checksum collisions outside the classes named above. Two-bit errors at distance greater than 31.
- The macOS `F_FULLFSYNC` branch is compiled only under `__APPLE__`. It was not executed here.
- A proof of the C++ memory model behind `IO.Ref` and `Std.Mutex`.

## Concurrency

Lean 4.35's `ST.Ref.swap` is documented as atomic. `Ref.set` is that swap, discarding the old value. Readers only `get` one immutable `View` (the map, the log, the next sequence number, and the epoch). They see the previous view or the new one.

Commits take a `Std.Mutex Unit`. The lock is not re-entrant. The byte append and `sync` happen before `set`, so a reader does not observe a view whose bytes have not been synced. The order the mutex admits commits is the serial order.

The formal model is `Cairn.Hist` in `Cairn/Snapshot.lean`: a history is a list of batches, its state is the fold of those batches, and a `Snapshot` is the map value at the moment it was taken. Extending the history does not rewrite that value. `state_eq_serial` says the state equals the fold of the committed batches. That is a model of the lock, not a proof about the runtime. Overlapping `Task`s are covered by `lake test` (a batch's two keys are both visible or neither is).

## Sharding

`shardOf bounds k` is the number of bounds `≤ k`. It is a total function. For one epoch (one bound list), each key has exactly one shard id, and that id is in `0 .. bounds.length` (`key_one_shard`). The same bounds and key always give the same id. Empty bounds means one shard, which is the single-node database.

Bounds ought to be strictly increasing if the ranges should be non-empty. The uniqueness proof does not need that.

`shardHash n k` is `crc32(k) % n` (0 when `n = 0`). It is a static partition for callers who want it. `commit` does not use it. `sameShard` uses `shardOf`.

An `Epoch` is a generation plus the bounds. `Epoch.rebalance` increments the generation and stores the new bounds. It does not move bytes. `rebalance_partition` says an entry is still in the map iff it sits in its home shard under the new bounds: reassignment does not drop keys.

`moved` compacts one shard's entries into a fresh log. `move_replays` says replaying that log is exactly those entries. `DB.adopt` writes that log and publishes the new epoch in one view. That is the local half of a split or a move. Nothing here ships the bytes to another machine, and nothing elects a leader.

## Replication

A shard is an independent cairn with its own log. Records carry a `UInt64` sequence number and a CRC. `applyRpc` is the apply step a future transport would call:

- `appendEntries` appends when the epoch matches and `prev` is the follower's current length. Otherwise the log stays as it is.
- `installSnapshot` replaces the log when the epoch matches.

`catchUp` uses that. If the follower log is a prefix, the missing suffix is appended and the states match (`catchUp_state`, `prefix_log_catchup`, `truncate_catchup`). If it is not a prefix, the leader log is installed and the follower's extra suffix is dropped. That is primary/secondary repair, not a merge, and not Raft. `crash_is_prefix` plus `catchUp` say a byte-prefix crash of the leader log is some record prefix, and catch-up then replays to the leader map.

`InProc` is an in-memory mailbox (`send` / `drain`) so tests can pass those messages around. The record codec is the payload a real transport would send (`encodeRecord`, `encodeLog`).

Not implemented, on purpose:

- sockets or any byte frame beyond the record
- Raft terms, votes, election timeouts
- quorum and commit index
- membership changes
- an automatic rebalancer

`resync` in `Cairn/Cluster.lean` is the in-process shape: every follower of a list catches up to the head. `resync_states` needs equal epochs.

## Quick start

```lean
import Cairn
open Cairn

def main : IO Unit := do
  let db ← DB.openFile "state.cairn"
  db.putStr "lives" "3"
  IO.println (repr (← db.getStr "lives"))
  db.close
```

```
lake build
lake test
```

`lake test` is the deterministic suite (unit, crash cuts, file reopen, in-process shards, task stress). It does not run the benchmark or the `kill -9` demo.

## API

| Call | What it does |
| --- | --- |
| `DB.openFile path epoch` | Open or create a file. Default epoch: generation 0, no bounds. |
| `DB.openMem epoch` | In-memory store. |
| `DB.get` / `DB.put` / `DB.delete` | One key. `*Str` variants take `String`. |
| `DB.commit ops` | One record, then `sync`. Empty batches and cross-shard batches fail. |
| `DB.commitMany batches` | One segment of several records, one `sync`. A tear drops the whole segment. |
| `DB.openFileRepair` | Truncate a torn tail or mid-log corruption. A foreign file is left in place. |
| `DB.iterate` | Entries in lexicographic key order. |
| `DB.snapshot` | The current immutable view. |
| `DB.compact` | Rewrite the live map. Sequence numbers change. |
| `DB.close` | Flush and refuse later commits. |
| `DB.follow` / `followSuffix` / `installSnapshot` | Apply a replication message under the writer lock. |
| `DB.adopt epoch records` | Replace the log and publish `epoch` together. Local shard move. |
| `DB.setEpoch` | Change the epoch only. Prefer `adopt` when data moves too. |

Reads do not take the mutex. `get` is one `Ref.get` plus a lookup.

## On disk

Version 2. A file is a header frame (`CAIR`, version `UInt32` 2) and then segment frames (`SEG1`). Each frame is magic, `UInt32` length, `sum32` of those eight bytes, payload, `sum32` of the payload, then zero padding out to a multiple of 4096. The header payload is the version. A segment payload is `encodeLog` of one or more records. A record is still `REC1`, `UInt64` sequence number, `UInt32` operation count, operations (tag 1 put, tag 2 delete, each string a `UInt32` length plus bytes), then reflected `crc32` of that body. Strings must be shorter than 2^32 bytes, and a frame payload must be shorter than 2^32 bytes.

`DB.commitMany` writes several records into one segment and data-syncs once. A crash before that `sync` drops the group. A tear inside the segment drops the whole segment. Both results are a prefix of the submitted groups.

Compaction writes `path.cairn-tmp`, data-syncs it, closes that descriptor, `rename`s it over the live file, and fsyncs the directory. The append descriptor is closed first: on Linux it would keep the old inode. A crash before the rename leaves the previous file. A crash after the rename and before the directory fsync can show either name; both files were data-synced.

A bit flip in the last segment is indistinguishable from a tear and is truncated. A damaged length that no longer fits the file looks like a tear and drops the tail. Bit rot in the header of a complete file is a reject at offset 0, not a silent truncate. `openFile` does not rewrite a clean file.

## What is proved

The library does not declare `axiom`, `sorry`, or `partial`. `#print axioms` on the theorems below reports only kernel axioms: `propext`, `Quot.sound`, and in some proofs `Classical.choice` (from `omega`). There are no `bv_decide` axioms.

| Theorem | Statement |
| --- | --- |
| `get_after_put`, `get_after_del`, `get_batch_put`, `get_batch_del` | A batch ending in put or delete has that effect. |
| `decodeRecord_write`, `decodeLog_encode` | Encode then decode is the identity for a record and a log. |
| `decodeFile_prefix`, `recovery_prefix` | Under `RecordsFit`, a byte prefix of an encoded file decodes as a prefix of the records, and replay of that is the recovered map. |
| `recovery_keeps_synced` | Under `GroupsFit`, a prefix long enough to cover the synced groups keeps those groups and is still a prefix of the synced groups plus the in-flight ones. |
| `sum32_burst`, `sum32_one_bit`, `sum32_two_close`, `sum32_weight_one`, `sum32_detects_burst` | `sum32` is nonzero on a burst of width at most 32 bits, on a single set bit, on two bits at distance 1..31, and on Hamming weight 1. Xoring that error into an equal-length message changes the checksum. |
| `not_all_odd_weight` | `sum32` of `[1, 4, 0xC1, 0x1D, 0xB7]` is 0 and the weight is odd. |
| `nodup_replay` | Replay from empty has no duplicate keys. |
| `compact_eq`, `compact_roundtrip` | Compaction replays to the same map, including through the codec. |
| `entries_sorted`, `entries_perm` | Iteration is a sorted permutation of the map. |
| `key_one_shard`, `shardOf_deterministic`, `shardOf_range` | One shard id per key per bounds, in range, a function of the inputs. |
| `shardHash_range` | The hash id is `< n` when `n > 0`. |
| `rebalance_partition`, `inShard_disjoint` | Rebinding ranges keeps every entry in exactly one home shard. |
| `move_replays`, `moved_state` | The snapshot log of one shard replays to that shard's entries. |
| `state_eq_serial`, `snapshot_stable` | In the history model, state is the serial fold, and a taken snapshot stays that state. |
| `catchUp_state`, `prefix_log_catchup`, `truncate_catchup`, `crash_is_prefix` | Same-epoch catch-up matches the leader, including after a byte-prefix crash. |
| `append_extends`, `install_replaces`, `append_rejects_epoch` | The apply step appends, replaces, or keeps the log. |
| `resync_states` | Followers with the leader's epoch match the leader after `resync`. |

`#print axioms` on `sum32_burst`, `sum32_detects_burst`, `recovery_keeps_synced`, `decodeFile_prefix`, and `recovery_prefix` reports `propext`, `Quot.sound`, and `Classical.choice`.

Not proved: that `IO.Ref.set` is atomic, that the mutex admits no two critical sections, that the C shim's `fdatasync` / `fsync` / `rename` match POSIX (the calls are what `strace` showed; the kernel's meaning is assumed), that `sum32` detects every change, two-bit errors farther than 31 bits, or anything about a network. The byte-prefix theorems are about a prefix of a well-formed encoding. A checksum collision can append a frame that is not a prefix; that is outside the theorem. The crash-cut test checks a sample of indexes (`sampleCuts`: the first 80 bytes, the 4096-byte edges, and the offsets 17 and 40 into each frame). The proof is for every index.

## What is tested

`lake test` checks the memory store, sampled cuts of a 12-record log (the reopened keys are `0 .. k-1`), a real file (batch, `commitMany` of two puts lands in 8192 bytes, compact, reopen, a torn tail, `"HI"` and `NOTACAIR` rejected, a 3-byte header prefix opened as empty), an in-process router, two writer tasks plus four reader tasks, a simulated store that drops or reorders unsynced frames, and a bit/byte fuzz of one valid log.

The fault injection keeps two synced puts when the unsynced frame is torn, accepts a kept unsynced frame only as a longer prefix, and throws `corrupt log` when a zeroed pending frame is followed by a kept one. The fuzz, seed `0xC0FFEE`, multiplier `6364136223846793005`, was 512 header bits, 768 bits at the start of the first segment, 200 random bits, and 200 random nonzero byte masks (1680 flips). The run printed:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
```

`miss` would have accepted the altered bytes as the original records. `forge` would have produced a record list that is not a prefix. Both stayed at 0 on this set. That is a measurement, not a proof that every flip is caught. The 89 torn results are prefixes and are truncated.

`strace` of `cairn-crash-writer` (two puts) showed `fdatasync` of the new file, `fsync` of the directory, then `fdatasync` after each put. `strace` of `cairn-sync-trace` showed the same create barrier, `fdatasync` of `path.cairn-tmp`, `rename` onto the live path, and `fsync` of the directory. This machine has no `dmsetup` or `modprobe`, so `dm-flakey` was not run. The power cord was not pulled. `kill -9` is a separate demo: `scripts/crash_demo.sh` waits 0.3 s and kills the writer. One run printed `recovered 147 keys, a prefix of the committed writes`.

## Benchmarks

`cairn-bench` and `cairn-durable-bench` are not part of `lake test`. Older `cairn-bench` numbers were `flush` without `fsync`. They are not durability numbers and are not repeated here.

`cairn-durable-bench`, one run, 4 vCPU, `Intel(R) Xeon(R) Processor` at the 2400 MHz `/proc/cpuinfo` reports, ext4 on `/dev/vdc`. Three repetitions. `sync-per-commit` is 100 `putStr`s, each data-synced. The group rows are 256 puts packed into segments of 8, 32, or 128 records, one `fdatasync` per segment. The checksum rows fold 4096 bytes, 401 times, and keep the digest (401 is odd, so the xor sink is the digest itself).

```
sync-per-commit n=100  282891ns/op 3534ops/s  166494ns/op 6006ops/s  322710ns/op 3098ops/s
group-8 n=256  33787ns/op 29597ops/s  35793ns/op 27938ops/s  48203ns/op 20745ops/s
group-32 n=256  25519ns/op 39186ops/s  20269ns/op 49336ops/s  17335ns/op 57686ops/s
group-128 n=256  6133ns/op 163052ops/s  10651ns/op 93887ops/s  11090ns/op 90171ops/s
checksum crc32 bytes=4096 reps=401  8ns/byte sink=3563452679
checksum sum32 bytes=4096 reps=401  8ns/byte sink=1106225055
checksum sum64 bytes=4096 reps=401  8ns/byte sink=169702108233435973
checksum mix128 bytes=4096 reps=401  12ns/byte sink=16824937962598406005
```

The three checksum repetitions of each function printed the same nanoseconds and the same sink; one line each is enough. `fdatasync` on this VM moved between about 0.17 ms and 0.32 ms per single put in this run. A 4096-byte `sum32` is about 33 µs, smaller than that barrier and the same speed here as reflected `crc32` and as CRC-64. `mix128` was slower and is not a proved checksum. The on-disk frame checksum stays `sum32`, because the burst proof is about that polynomial and a wider unproved checksum does not get cheaper than the barrier.

These numbers are one measurement on this machine. They are not a claim about other disks. A disk that waits for stable media will be slower than this ext4.

## Building

```
lake build
lake test
./scripts/crash_demo.sh
./.lake/build/bin/cairn-bench
./.lake/build/bin/cairn-durable-bench
```

GitHub Actions runs `lake build` and `lake test` once per push (the workflow is `on: push` only, via `leanprover/lean-action` with `test: true`).

## License

MIT. Copyright (c) 2026 kidandcat.
