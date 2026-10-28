# cairn

A small key-value store written in Lean 4 (toolchain `v4.35.0`, the same pin as [uvl](https://github.com/kidandcat/uvl)). One process, one writer per shard, an append-only log per shard, and an in-memory index rebuilt on open. The index is a persistent size-balanced tree (`Std.TreeMap`, delta 3, ratio 2). `get` is that tree's lookup. `insert` shares the branches a reader did not need. `ShardSet` is the cluster surface: it owns one `DB` per shard id and routes with `shardOf`. A later network plugs into `Directory` and `Mailbox` without replacing the codec or the map.

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
- `kill -9` is not a power loss. One run of `scripts/crash_demo.sh` on this machine recovered 147 keys, a prefix of the writes. A later run recovered 144 keys, also a prefix. The process was killed; the disk was not.
- Inside one shard the admission order of that shard's mutex is the serial order (`shard_hist_serial`, which is `state_eq_serial` on that shard's `Hist`). Two commits on different shards commute (`steps_commute`). There is no global snapshot and no serial order across shards.
- `ShardSet.iterate` is the sorted merge of one snapshot per shard (`mergeAll`, `clusterEntries`). Each snapshot is that shard's `View` at the moment it was read. A commit on another shard can land between those reads. `cluster_partition` says that merging the home shards of one map returns exactly that map's entries. The runtime merge is of the views that were actually read, which need not be one moment.
- A batch whose keys fall in more than one shard is rejected. The id a single-shard batch is sent to is `shardOf` of its key (`route_is_shardOf`).
- A crash is per file. `crash_shard_independent` is `decodeFile_prefix` on that shard's bytes. `crash_others` says every other shard id is unchanged. Truncating `shard-0.cairn` does not rewrite `shard-1.cairn`.

## Non-goals

- SQL, a query planner, or a page cache.
- A cross-shard transaction. A batch whose keys fall in more than one shard is rejected. There is no two-phase commit.
- Network, elections, terms, votes, quorums, a commit index, and a membership protocol. The seams are in place (`Locate.remote`, `ShardReq`, `Mailbox`, `planCatchup`). Nothing dials a socket. See [Cluster](#cluster).
- Several writers of the same shard. Callers of one `DB` may overlap; that shard's mutex runs their commits one at a time. Optimistic concurrency inside a shard (design C in the comparison) waits until one shard is the bottleneck.
- A global snapshot, or a serial order of commits that touch different shards.
- Hardware that reports a successful flush without writing the bytes. A physical sector larger than 4096 bytes. Checksum collisions outside the classes named above. Two-bit errors at distance greater than 31.
- The macOS `F_FULLFSYNC` branch is compiled only under `__APPLE__`. It was not executed here.
- A proof of the C++ memory model behind `IO.Ref` and `Std.Mutex`.

## Concurrency

Lean 4.35's `ST.Ref.swap` is documented as atomic. `Ref.set` is that swap, discarding the old value. Readers only `get` one immutable `View` (the tree, the newest-first log, the next sequence number, and the epoch). They see the previous view or the new one. A commit conses the new record and inserts into the tree; both share structure with the view the reader may still hold.

Each `DB` has its own `Std.Mutex Unit`. The lock is not re-entrant. The byte append and `sync` happen before `set`, so a reader does not observe a view whose bytes have not been synced. The order that shard's mutex admits commits is the serial order of that shard. `ShardSet` does not take a mutex around the set. Two commits whose keys route to different shards do not share a lock.

The formal model is `Cairn.Hist` in `Cairn/Snapshot.lean`, one history per shard in `Cairn.Worlds`. A history is a list of batches, its state is the fold of those batches, and a `Snapshot` is the map value at the moment it was taken. Extending the history does not rewrite that value. `state_eq_serial` says the state equals the fold of the committed batches. `shard_hist_serial` is that fact for whichever shard you point at. `steps_commute` says writing shard `s` and shard `t` (`s ≠ t`) is the same `Worlds` either way. That is a model of the locks, not a proof about the runtime. Overlapping `Task`s are covered by `lake test` (a batch's two keys are both visible or neither is, including when four shards run at once).

## Sharding

`shardOf bounds k` is the number of bounds `≤ k`. It is a total function. For one epoch (one bound list), each key has exactly one shard id, and that id is in `0 .. bounds.length` (`key_one_shard`). The same bounds and key always give the same id. Empty bounds means one shard, which is the single-node database.

Bounds ought to be strictly increasing if the ranges should be non-empty. The uniqueness proof does not need that.

`shardHash n k` is `crc32(k) % n` (0 when `n = 0`). It is a static partition for callers who want it. `commit` does not use it. `sameShard` uses `shardOf`.

An `Epoch` is a generation plus the bounds. `Epoch.rebalance` increments the generation and stores the new bounds. It does not move bytes. `rebalance_partition` says an entry is still in the map iff it sits in its home shard under the new bounds: reassignment does not drop keys.

`moved` compacts one shard's entries into a fresh log. `move_replays` says replaying that log has the same `entries`. The tree shape may differ. `DB.adopt` writes that log and publishes the new epoch in one view. That is the local half of a split or a move. Nothing here ships the bytes to another machine, and nothing elects a leader.

`routeOf` is the router's decision for a batch: `some (shardOf bounds k)` when every key is that shard, `none` when the batch is empty or crosses a shard (`route_is_shardOf`). `ShardSet.commit` uses that rule and then calls the one `DB`.

## Cluster

`ShardSet` is what a process runs. It holds `slots : Array (Option DB)`, an `Epoch`, and a `Directory`. Slot `i` is shard `i`. There is no lock beside the `DB` you route to.

`HostId` names a process. `ShardHost` is the list of shard ids that process serves (`Directory.hostView`). `Directory` is the versioned map from shard id to `ShardOwner` (leader host, leader `NodeId`, follower `NodeId`s). `reassign` bumps `gen` (`reassign_gen`) and the new owner is what `owner?` returns (`reassign_owner`). `Locate` is `here`, `remote leader`, or `missing` (`locate_here`, `locate_remote`). A remote call goes through `ShardSet.remote`, whose default throws `remote shard`. `ShardSet.serve` is the function a socket handler would call. The test wires two hosts in-process through that function. Replacing it with a byte codec over a connection is the network work that is left.

`NodeId` is still the mailbox address of one replica of one shard. `InProc` is that mailbox. `Mailbox` is the `send`/`drain` pair a wire would implement (`InProc.mailbox`).

Replication stays per shard. `planCatchup` chooses `appendEntries` of the missing suffix or `installSnapshot` of the leader log, and `plan_agrees` says applying that `Rpc` is `catchUp`. `ShardSet.pushLog` sends it. The follower applies it with `DB.follow`. The follower's log length is an argument: a later heartbeat would supply it. There is no election and no quorum. A directory publish does not move bytes; `adopt` still does the local half of a move.

Files are `dir/shard-<id>.cairn`, one store each. `openFiles` is the durable router. `openMem` is the same router without a disk.

What is still missing before this is a cluster you can point at another machine:

- a byte encoding of `ShardReq` / `Rpc` and a socket (or other transport) behind `Mailbox` and `remote`
- a membership protocol that calls `publish` after `adopt`, and decides who is leader
- a consensus or quorum rule if a shard must survive a leader dying (this phase is primary/secondary copy, leader wins)
- heartbeats that carry the follower length into `planCatchup`

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
| `DB.range` / `DB.prefix` | One snapshot, ordered page. `lo` inclusive, `hi` exclusive, `after` strict. |
| `DB.snapshot` | The current immutable view. |
| `DB.compact` | Rewrite the live map. Sequence numbers change. |
| `DB.close` | Flush and refuse later commits. |
| `DB.follow` / `followSuffix` / `installSnapshot` | Apply a replication message under the writer lock. |
| `DB.adopt epoch records` | Replace the log and publish `epoch` together. Local shard move. |
| `DB.setEpoch` | Change the epoch only. Prefer `adopt` when data moves too. |
| `ShardSet.openMem` / `openFiles` / `openHosted` | One `DB` per shard. `openFiles` uses `dir/shard-<id>.cairn`. `openHosted` leaves the other slots empty. |
| `ShardSet.get` / `put` / `delete` / `commit` / `commitMany` | Route with `shardOf`. A cross-shard batch throws. A remote shard calls `remote`. |
| `ShardSet.iterate` | Sorted merge of one snapshot per shard. Not a global snapshot. |
| `ShardSet.range` / `prefix` | Same merge, then the page. A prefix may cross shards. Still not one snapshot. |
| `collInsert` / `collGet` / `collUpdate` / `collDelete` / `collList` | A collection is a key prefix. Versioned compare-and-set. `collList` is `prefix`. |
| `Queue.enqueueWith` / `claim` / `ack` / `nack` | Jobs in key order. Outbox is one batch; a cross-shard batch is refused. |
| `Ttl.put` / `Ttl.sweep` | Expiry index is the key order under prefix `04`. |
| `ShardSet.watch` | One shard's log from an LSN, filtered by prefix. No cross-shard order. |
| `ShardSet.serve` | Handle a `ShardReq` for a shard this host owns. |
| `ShardSet.publish` | Bump the directory generation and set the owner. Does not move bytes. |
| `ShardSet.pushLog` | `planCatchup` then `Mailbox.send` for one shard. |

Reads do not take the mutex. `get` is one `Ref.get` plus a tree lookup. `ShardSet.iterate` does one such read per shard, in shard-id order, with no lock across them. `range` and `prefix` do the same reads and then keep the keys inside the interval. The memory backend appends by consing a frame. `readAll` joins those chunks. The record list in the `View` is newest-first for the same reason.

## Collections

A collection is a byte prefix: tag `1`, a `UInt32` length, the name, tag `2`, then a 16-byte id. The id is a `Ulid` (48-bit milliseconds, then 80 bits), big-endian, so lexicographic order is time order (`Ulid.encode_lt_of_lt`). `IdGen` takes a `Clock`. Tests pass a counter.

The stored value is a `UInt64` version plus a `Val` (`bytes`, `str`, or `nat`). `collInsert` fails if the id exists. `collUpdate` and `collDelete` run under that key's writer lock and write only when the version matches (`resolve_*`). The version does not wrap (`expect + 1 ≠ 0`). One document is one key, so it is one shard. `collList` is `ShardSet.prefix`: a prefix can cross shards, and the page is the merge of the snapshots that were read. There is no global snapshot. A remote shard throws `remote shard` on a collection write. `Demo/Backend.lean` inserts two items and checks the order. CI builds `cairn-backend` and runs it.

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
| `compact_eq`, `compact_roundtrip` | Compaction replays to the same `entries`, including through the codec. Not the same tree shape. |
| `entries_sorted`, `entries_nodup`, `entries_of_get` | Iteration is sorted by key bytes, lists each key once, and agrees with `get`. |
| `rangeHits_mem`, `prefixHits_mem`, `rangeHits_sorted`, `rangeHits_nodup`, `prefixHits_sorted`, `prefixHits_nodup` | A range or prefix is exactly the entries inside the interval, in order, each key once. |
| `resume_hits`, `resume_prefix` | The next page, using the cursor, is the tail of that hit list. |
| `mergedHits_mem` | A merged page contains an entry iff some shard snapshot did and the predicate matches. |
| `Ulid.encode_lt_of_lt`, `Ulid.fresh_increases` | Byte order follows time order. The pure id step is strictly increasing. |
| `resolve_insert_fresh`, `resolve_insert_taken`, `resolve_update_ok`, `resolve_update_conflict`, `resolve_delete_ok`, `resolve_delete_conflict` | Compare-and-set writes the next version only when the stored version matches. |
| `Job.claim_blocks`, `Job.claim_spec`, `Job.enqueue_idem`, `outbox_both` | A live lease is not claimed again. The same state claims the same id. An idempotency key is not enqueued twice. One outbox batch shows both keys. |
| `Feed.visible_mem`, `Feed.visible_since`, `Feed.visible_prefix` | A watch hit is an op in that shard's log at or after the LSN, and the key has the prefix. |
| `Job.due_mem` | A TTL row is due exactly when its expiry is `≤ now`. |
| `get_insert`, `get_insert_ne`, `get_remove` | Tree insert and erase have the map equations the list index had. |
| `key_one_shard`, `shardOf_deterministic`, `shardOf_range` | One shard id per key per bounds, in range, a function of the inputs. |
| `shardHash_range` | The hash id is `< n` when `n > 0`. |
| `rebalance_partition`, `inShard_disjoint` | Rebinding ranges keeps every entry in exactly one home shard. |
| `move_replays`, `moved_state` | The snapshot log of one shard replays to that shard's `entries`. |
| `state_eq_serial`, `snapshot_stable` | In the history model, state is the serial fold, and a taken snapshot stays that state. |
| `catchUp_state`, `prefix_log_catchup`, `truncate_catchup`, `crash_is_prefix` | Same-epoch catch-up matches the leader, including after a byte-prefix crash. |
| `append_extends`, `install_replaces`, `append_rejects_epoch` | The apply step appends, replaces, or keeps the log. |
| `resync_states` | Followers with the leader's epoch match the leader after `resync`. |
| `route_is_shardOf` | A single-shard batch is sent to `shardOf` of its key. An empty or cross-shard batch routes nowhere. |
| `step_home`, `step_other`, `shard_hist_serial` | A routed step writes that shard's `Hist` only, and that history's state is its own serial fold. |
| `steps_commute` | Writes to two different shards yield the same `Worlds` in either order. |
| `clusterEntries_mem`, `clusterEntries_sorted`, `cluster_partition` | The sorted merge contains exactly the entries of the parts. Merging the home shards of one map returns that map's entries. |
| `crash_shard_independent`, `crash_others` | A byte prefix of one shard decodes as a record prefix of that shard. Every other shard id is unchanged. |
| `reassign_gen`, `reassign_owner`, `locate_here`, `locate_remote` | Publishing an owner bumps the directory generation, and a host either serves the shard or points at the remote leader. |
| `plan_agrees` | The `Rpc` chosen by `planCatchup` applies to the same log as `catchUp`. |

`#print axioms` on `sum32_burst`, `sum32_detects_burst`, `recovery_keeps_synced`, `decodeFile_prefix`, and `recovery_prefix` reports `propext`, `Quot.sound`, and `Classical.choice`.

Not proved: a big-O bound on the tree. `Std.TreeMap` keeps the size-balance invariant (delta 3, ratio 2) inside the library; cairn proves the `get` / `insert` / `erase` equations and that `entries` is the sorted binding list. Not proved: that `IO.Ref.set` is atomic, that the mutex admits no two critical sections, that the C shim's `fdatasync` / `fsync` / `rename` match POSIX (the calls are what `strace` showed; the kernel's meaning is assumed), that `sum32` detects every change, two-bit errors farther than 31 bits, or anything about a network. The byte-prefix theorems are about a prefix of a well-formed encoding. A checksum collision can append a frame that is not a prefix; that is outside the theorem. The crash-cut test checks a sample of indexes (`sampleCuts`: the first 80 bytes, the 4096-byte edges, and the offsets 17 and 40 into each frame). The proof is for every index.

## What is tested

`lake test` checks the memory store, sampled cuts of a 12-record log (the reopened keys are `0 .. k-1`), a real file (batch, `commitMany` of two puts lands in 8192 bytes, compact, reopen, a torn tail, `"HI"` and `NOTACAIR` rejected, a 3-byte header prefix opened as empty), an in-process router, two writer tasks plus four reader tasks, a simulated store that drops or reorders unsynced frames, a bit/byte fuzz of one valid log, and `ShardSet`: the routed id is `shardOf`, a cross-shard batch is rejected, each shard's log replays without the other shard's keys, `iterate` equals `mergeAll` of the shard snapshots, two hosts forward through `remote`/`serve`, `pushLog` plus `DB.follow` copies one shard, truncating `shard-0.cairn` to the header drops that shard's keys and leaves shard 1, and four shard tasks plus two readers keep each pair intact and the final iterate equal to the merge.

The fault injection keeps two synced puts when the unsynced frame is torn, accepts a kept unsynced frame only as a longer prefix, and throws `corrupt log` when a zeroed pending frame is followed by a kept one. The fuzz, seed `0xC0FFEE`, multiplier `6364136223846793005`, was 512 header bits, 768 bits at the start of the first segment, 200 random bits, and 200 random nonzero byte masks (1680 flips). The run printed:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
```

`miss` would have accepted the altered bytes as the original records. `forge` would have produced a record list that is not a prefix. Both stayed at 0 on this set. That is a measurement, not a proof that every flip is caught. The 89 torn results are prefixes and are truncated.

`strace` of `cairn-crash-writer` (two puts) showed `fdatasync` of the new file, `fsync` of the directory, then `fdatasync` after each put. `strace` of `cairn-sync-trace` showed the same create barrier, `fdatasync` of `path.cairn-tmp`, `rename` onto the live path, and `fsync` of the directory. This machine has no `dmsetup` or `modprobe`, so `dm-flakey` was not run. The power cord was not pulled. `kill -9` is a separate demo: `scripts/crash_demo.sh` waits 0.3 s and kills the writer. One run printed `recovered 147 keys, a prefix of the committed writes`. A run after the tree index printed `recovered 144 keys, a prefix of the committed writes`.

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

`cairn-design-bench` is the same machine, through `ShardSet` (the router), not through a raw `DB`. Opens are outside the clock. `file-shards-N` is N dedicated tasks, N files, 100 `put`s each, one `fdatasync` per put. `mem-shards-N` is the same shape on the memory backend. `file-group-32-shards-4` packs 128 puts per shard into segments of 32, one `fdatasync` per segment, four shards at once. `file-contended-1-tasks-4` is four tasks writing one shard. Each block below is one run of three repetitions. They are not averaged.

Before the tree and the chunked memory log (associative list, `buf ++ frame`, `v.log ++ [record]`):

```
file-shards-1 ops=100  206093ns/op 4852ops/s  276915ns/op 3611ops/s  195993ns/op 5102ops/s
file-shards-2 ops=200  120833ns/op 8275ops/s  86026ns/op 11624ops/s  109377ns/op 9142ops/s
file-shards-4 ops=400  61085ns/op 16370ops/s  57966ns/op 17251ops/s  58748ns/op 17021ops/s
mem-shards-1 ops=100  5478466ns/op 182ops/s  5409442ns/op 184ops/s  5391236ns/op 185ops/s
mem-shards-2 ops=200  2803036ns/op 356ops/s  2784675ns/op 359ops/s  2722233ns/op 367ops/s
mem-shards-4 ops=400  1406929ns/op 710ops/s  1394600ns/op 717ops/s  1380735ns/op 724ops/s
file-group-32-shards-4 ops=512  11336ns/op 88214ops/s  5189ns/op 192715ops/s  5644ns/op 177179ops/s
file-contended-1-tasks-4 ops=400  195137ns/op 5124ops/s  213681ns/op 4679ops/s  233684ns/op 4279ops/s
```

After (`Std.TreeMap`, memory frames consed, record list newest-first):

```
file-shards-1 ops=100  190454ns/op 5250ops/s  168778ns/op 5924ops/s  208253ns/op 4801ops/s
file-shards-2 ops=200  78123ns/op 12800ops/s  92477ns/op 10813ops/s  115542ns/op 8654ops/s
file-shards-4 ops=400  53649ns/op 18639ops/s  70828ns/op 14118ops/s  53762ns/op 18600ops/s
mem-shards-1 ops=100  59268ns/op 16872ops/s  38080ns/op 26260ops/s  33897ns/op 29501ops/s
mem-shards-2 ops=200  35357ns/op 28282ops/s  18389ns/op 54380ops/s  17948ns/op 55716ops/s
mem-shards-4 ops=400  19539ns/op 51179ops/s  18866ns/op 53005ops/s  9567ns/op 104525ops/s
file-group-32-shards-4 ops=512  9212ns/op 108554ops/s  8485ns/op 117855ops/s  8311ns/op 120322ops/s
file-contended-1-tasks-4 ops=400  153274ns/op 6524ops/s  154198ns/op 6485ops/s  153646ns/op 6508ops/s
```

On this ext4 the file rows stay on the `fdatasync` cost: one shard about 0.17–0.28 ms/op in both runs, four shards about 14–19k ops/s. Four tasks on one shard stay on that shard's mutex. The group row is one barrier per 32 records, about 5–12 µs/op across the two runs. The memory rows were the copy. One shard went from about 5.4–5.5 ms/op to about 34–59 µs/op. Two and four shards still scale. Those memory rows are not a disk, and 100 keys do not show the tree's asymptotic gap against the old linear scan: the byte-log copy dominated that benchmark. An earlier list-index run of this harness is in the history of this file; it is not part of this pair.

A later run, after range and collections, kept the shard rows in that same band (file one shard about 0.16–0.18 ms/op, memory one shard about 42–50 µs/op). `mem-prefix-pages` puts 1000 keys outside the clock, then walks them in pages of 40. The clock is the walk.

```
mem-prefix-pages ops=1000  1131ns/op 884173ops/s  1012ns/op 988142ops/s  931ns/op 1074113ops/s
```

The walk filters each shard's entry list. It is not a tree lower bound. About 1 µs per key on this machine is that filter plus the merge.

A later run after the job queue, on the same machine:

```
mem-prefix-pages ops=1000  1006ns/op 994035ops/s  883ns/op 1132502ops/s  917ns/op 1090512ops/s
mem-claim-100 ops=100  178963ns/op 5587ops/s  181739ns/op 5502ops/s  179097ns/op 5583ops/s
```

`mem-claim-100` enqueues 100 jobs outside the clock, then claims each. About 0.18 ms per claim is another scan of the prefix. The file rows of that run stayed on `fdatasync` (one shard about 0.16–0.37 ms/op).

## Building

```
lake build
lake test
./scripts/crash_demo.sh
./.lake/build/bin/cairn-bench
./.lake/build/bin/cairn-durable-bench
./.lake/build/bin/cairn-design-bench
./.lake/build/bin/cairn-backend
```

GitHub Actions runs `lake build` and `lake test` once per push (the workflow is `on: push` only, via `leanprover/lean-action` with `test: true`).

## License

MIT. Copyright (c) 2026 kidandcat.
