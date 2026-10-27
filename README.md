# cairn

A small key-value store written in Lean 4 (toolchain `v4.35.0`, the same pin as [uvl](https://github.com/kidandcat/uvl)). One process, one writer, an append-only log, and an in-memory index rebuilt on open. The log and the router are shaped so a later version can run several independent cairn processes as shards and replicas without replacing the codec or the map.

It is meant for Lean apps that need to keep a map (game state, settings) on the targets uvl cares about: native Linux and macOS now, WebAssembly, Android, and a 32-bit microcontroller later. The core does not call FFI. Lengths in the codec are `UInt32` and sequence numbers are `UInt64`. There is no `USize` in the codec.

This is not a SQL database.

## Guarantees

- `put` and `delete` are applied by folding one record. A record is one batch. `get` after a batch that ends in `put k v` is `some v`. A batch that ends in `delete k` removes `k`.
- A crash is modelled as a prefix of the byte string (a torn tail). Decoding that prefix yields some prefix of the committed records, then replay. A record is not split. Bytes shorter than the 8-byte header decode as an empty log, because a torn header cannot be told apart from a short non-file.
- A file whose first 8 bytes are not `CAIR` plus version 1 is rejected.
- Compaction rewrites the live map as one put per key and replays to the same map. It assigns new sequence numbers. A replica cannot append across that boundary; it has to install the new log.
- CRC-32 is stored with each record and checked on decode. The truncation proof does not assume CRC is collision-free. A bad checksum stops the scan; earlier records are kept. Bit flips are filtered, not proved absent.
- On open, the file is rewritten to the bytes of the records that decoded. That drops a torn tail. `Handle.flush` runs after appends and before the in-memory view is published. Lean 4.35 has no `fsync`. A flushed file survived `kill -9` in the demo below. Power loss is not covered.

## Non-goals

- SQL, a query planner, or a page cache.
- Several writers at once. Callers may overlap; the mutex runs their commits one at a time.
- A cross-shard transaction. A batch whose keys fall in more than one shard is rejected. There is no two-phase commit.
- Network, elections, terms, votes, quorums, or a commit index. See [Replication](#replication).
- Power-loss durability, and a proof that CRC catches every corruption.
- A proof of the C++ memory model behind `IO.Ref` and `Std.Mutex`.

## Concurrency

Lean 4.35's `ST.Ref.swap` is documented as atomic. `Ref.set` is that swap, discarding the old value. Readers only `get` one immutable `View` (the map, the log, the next sequence number, and the epoch). They see the previous view or the new one.

Commits take a `Std.Mutex Unit`. The lock is not re-entrant. The byte append and `flush` happen before `set`, so a reader does not observe a view that has not been flushed. The order the mutex admits commits is the serial order.

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
| `DB.commit ops` | One record. Empty batches and cross-shard batches fail. |
| `DB.iterate` | Entries in lexicographic key order. |
| `DB.snapshot` | The current immutable view. |
| `DB.compact` | Rewrite the live map. Sequence numbers change. |
| `DB.close` | Flush and refuse later commits. |
| `DB.follow` / `followSuffix` / `installSnapshot` | Apply a replication message under the writer lock. |
| `DB.adopt epoch records` | Replace the log and publish `epoch` together. Local shard move. |
| `DB.setEpoch` | Change the epoch only. Prefer `adopt` when data moves too. |

Reads do not take the mutex. `get` is one `Ref.get` plus a lookup.

## On disk

`CAIR`, version `UInt32` 1, then records. A record is `REC1`, `UInt64` sequence number, `UInt32` operation count, then operations (tag 1 put, tag 2 delete, each string a `UInt32` length plus bytes), then CRC-32 of that body. Each string must be shorter than 2^32 bytes. There is no length wrapping the whole record, so a put's key and value are limited one at a time.

Compaction writes `path.cairn-tmp`, flushes, drops that handle, and `rename`s it over the live file. The append handle is cleared first so it does not keep the old inode. A crash before the rename leaves the previous file.

## What is proved

The library does not declare `axiom`, `sorry`, or `partial`. `#print axioms` on the theorems below reports only kernel axioms: `propext`, `Quot.sound`, and in some proofs `Classical.choice` (from `omega`). There are no `bv_decide` axioms.

| Theorem | Statement |
| --- | --- |
| `get_after_put`, `get_after_del`, `get_batch_put`, `get_batch_del` | A batch ending in put or delete has that effect. |
| `decodeRecord_write`, `decodeLog_encode`, `decodeFile_encode` | Encode then decode is the identity. |
| `decodeFile_prefix`, `recovery_prefix` | A byte prefix of an encoded file decodes as a prefix of the records, and replay of that is the recovered map. |
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

Not proved: that `IO.Ref.set` is atomic, that the mutex admits no two critical sections, that `rename` or `flush` does what POSIX says, that CRC detects every change, or anything about a network.

## What is tested

`lake test` checks the memory store (put, delete, batch, empty batch, compact, reopen), every cut of a 12-record byte log (the reopened keys are `0 .. k-1`), a real file (batch, compact, reopen, a torn tail, a bad magic, a short header), an in-process router with two shards and a follower each (mailbox, epoch mismatch, diverged follower, `adopt` of a split), and two writer tasks plus four reader tasks (no torn batch).

The `kill -9` demo is `scripts/crash_demo.sh`. It builds `cairn-crash-writer` and `cairn-recover`, starts a writer of 2000 keys with 1 ms between flushes, waits 0.3 s, sends `kill -9`, and reopens. The recovered keys must be exactly `0 .. k-1` for some `k`. One run on this machine printed:

```
recovered 268 keys, a prefix of the committed writes
```

## Benchmarks

`cairn-bench` is not part of `lake test`. One run, file backend, this machine, 1000 distinct keys then 1000 gets, then four tasks reading key `"0"`:

```
file put: 1000 ops in 20 ms (50000 ops/s)
file get: 1000 ops in 9 ms (111111 ops/s)
concurrent get (4 tasks x 2000): 8000 ops in 409 ms (19559 ops/s)
```

These numbers are one measurement. They include opening and flushing each put. They are not a claim about other machines.

## Building

```
lake build
lake test
./scripts/crash_demo.sh
./.lake/build/bin/cairn-bench
```

GitHub Actions runs `lake build` and `lake test` once per push (the workflow is `on: push` only, via `leanprover/lean-action` with `test: true`).

## License

MIT. Copyright (c) 2026 kidandcat.
