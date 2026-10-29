# One writer per shard

Report from the branch `cursor/shard-writer-35e9`. It is phase 1 of the concurrency comparison: design B. Each shard is a `DB` with its mutex, its file, and its `Hist`. There is no global mutex. C (OCC inside one shard) waits until a single shard is not enough.

## What the layer does

`ShardSet` owns an optional `DB` per id. `get`, `put`, `delete`, `commit`, and `commitMany` compute `shardOf` and enter only that `DB`'s mutex. A batch with keys from two shards is rejected. `iterate` reads one snapshot per shard and merges them in key order (`mergeAll`). That merge is not a global snapshot: a commit can land on shard 1 between the read of shard 0 and the read of shard 1. There is no serial order across shards.

The cluster seam, without a network:

- `HostId` is the process. `ShardHost` is the list of shards it hosts (`Directory.hostView`).
- `Directory` is the versioned map shard → owner (`ShardOwner`: leader host, the leader's `NodeId`, followers). `publish` / `reassign` bumps the generation and does not move bytes.
- `Locate` says `here`, `remote`, or `missing`. The remote arm calls `ShardSet.remote`. By default it throws `remote shard`. `serve` is what a socket handler would call.
- `Mailbox` is `send`/`drain`. `InProc.mailbox` is the mailbox that was already there. `planCatchup` chooses `appendEntries` or `installSnapshot` the same way `catchUp` does, and `pushLog` sends it. The follower applies it with `DB.follow`. The caller passes the follower length: a future heartbeat would bring it.

Files are `dir/shard-<id>.cairn`. A cut of one file does not rewrite the others.

## What is proved

Reused: `key_one_shard`, `state_eq_serial`, `decodeFile_prefix` / `recovery_prefix`.

Added, in Lean, with no `sorry` and no declared `axiom`:

- `route_is_shardOf`: the id of a single-shard batch is `shardOf` of its key.
- `step_home`, `step_other`, `shard_hist_serial`: the step writes that shard's `Hist` and no other, and the state is the serial fold of its own commits.
- `steps_commute`: two writes on different shards commute. There is no global order to recover.
- `clusterEntries_sorted`, `clusterEntries_mem`, `cluster_partition`: the sorted merge contains exactly the entries of the parts, and splitting a map with `inShard` and merging it again returns those entries. The theorem talks about the snapshots it is given, not about one common instant.
- `crash_shard_independent` and `crash_others`: the byte prefix of one shard is a prefix of its records; the other ids do not change.
- `reassign_gen`, `reassign_owner`, `locate_here`, `locate_remote`, `plan_agrees`.

Not proved: that two `Task`s advance at once, that the C++ mutex does not admit two sections, or anything about a socket.

## What is only tested

`lake test` finished with `cairn tests ok` (the usual fuzz: detect 1591, torn 89, miss 0, forge 0). Also:

- The id `ShardSet` chooses matches `shardOf`. The crossed batch and the empty batch fail. Each shard's log, on replay, does not contain the other shard's keys.
- `iterate` equals `mergeAll` of the per-shard snapshots, and comes out sorted.
- Two hosts in memory: a put of a key owned by the other host goes through `remote`/`serve` and shows up on both sides. `iterate` merges the two snapshots.
- `pushLog` of a shard with an empty follower sends one message; `DB.follow` leaves the key. A different epoch sends nothing.
- Four writer tasks (one per shard, batches of two keys) and two readers. Each shard snapshot has the whole pair or does not have it. At the end, 40 entries per shard and `iterate` equal to the merge.
- Files: two tasks, one shard each. After close, `shard-0.cairn` is cut to the 4096-byte header. On reopen, shard 0's keys are gone and shard 1's remain.

## Numbers

One pass of `cairn-design-bench`, three repetitions, 4 vCPU, `Intel(R) Xeon(R) Processor` at 2400 MHz, ext4 on `/dev/vdc`. The clock does not include `open`. Each file put does one `fdatasync`.

```
file-shards-1 ops=100  224989ns/op 4444ops/s  156568ns/op 6387ops/s  163593ns/op 6112ops/s
file-shards-2 ops=200  127894ns/op 7818ops/s  103404ns/op 9670ops/s  93035ns/op 10748ops/s
file-shards-4 ops=400  56760ns/op 17618ops/s  53457ns/op 18706ops/s  61310ns/op 16310ops/s
mem-shards-1 ops=100  5482020ns/op 182ops/s  5406456ns/op 184ops/s  5383518ns/op 185ops/s
mem-shards-2 ops=200  2725123ns/op 366ops/s  2713650ns/op 368ops/s  2726411ns/op 366ops/s
mem-shards-4 ops=400  1428210ns/op 700ops/s  1440656ns/op 694ops/s  1428952ns/op 699ops/s
file-group-32-shards-4 ops=512  6425ns/op 155642ops/s  5400ns/op 185185ops/s  5601ns/op 178539ops/s
file-contended-1-tasks-4 ops=400  209802ns/op 4766ops/s  181693ns/op 5503ops/s  208523ns/op 4795ops/s
```

On a file, 4 shards did about three times the rate of 1 shard (about 16–19k ops/s against about 4.4–6.4k). 2 shards lands in between. Four tasks on a single shard stay at one shard's rate: the mutex does not parallelize inside. The group commit of 32, with 4 shards, drops to about 5–6 µs per put because the barrier is paid once per segment.

The memory rows scale the same way (double, then quadruple) but the absolute is the memory backend copying the 4096-byte frame on every append. They do not measure the router alone and they are not a disk.

## What is still missing for the cluster

A network (a codec for `ShardReq` and `Rpc`, and a transport behind `Mailbox` and `remote`), a membership protocol that calls `publish` after `adopt`, and consensus or a quorum if a shard has to survive the leader dying. This phase is primary/secondary copy: the leader wins. Several writers of the same shard stay out.
