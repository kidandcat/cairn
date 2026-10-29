# Copy, compaction, schema, and metrics

Phase 4. The copy of a shard is the log prefix up to an LSN. Compaction runs on a task. The schema version is a key. The counters live on the `ShardSet`.

## What it does

`upTo n` walks the chronological log and stops at the first record with `lsn > n`. `upTo_is_prefix` says that is `take k` for some `k`. Cairn LSNs grow by one, so that cut is the state up to `n`. `DB.backupFile` writes it with `writeDurable` (the same `fdatasync` and directory fsync as a compaction). Restore is `openFile` of that image.

`DB.compactAsync` runs `DB.compact` on a task. It is still the same writer: the shard mutex serializes compaction with commits.

`migrate` reads the key `schemaKey` (`[0]`) and, if the stored version is lower, writes the step and the new version in one batch. If that batch crosses a shard, it throws and does not publish. `schema_visible` is `get_after_put` of that key.

`ShardSet.counts` returns reads, local commits, and the nanoseconds of the last commit. It is not a histogram. `ShardSet.commit`, `ShardSet.transact`, and `ShardSet.modifyKey` increment `commits` and record `lastCommitNs` on return. A `transact` that writes nothing still counts: it held the mutex. A remote commit does not go through that counter.

## Proved

`upTo_is_prefix` and `schema_visible`. The rest of durability is still `recovery_prefix` and `recovery_keeps_synced` on the written image.

## Tested

`lake test`: `cairn tests ok`, fuzz detect 1591, torn 89, miss 0, forge 0, same 0. The new case opens a file, copies up to the second record, reopens the copy (`a` and `b` are there, `c` is not), compacts on a task and `b` remains, migrates to version 2, and the counters for one `put` and one `get` go up. `scripts/crash_demo.sh`: `recovered 144 keys, a prefix of the committed writes`.

`cairn-design-bench` with the counters in place, same machine, three repetitions. One shard in memory: 49271, 38709, and 36317 ns/op. One shard on a file: 182679, 151965, and 159001 ns/op. Still in the `fdatasync` and tree band; the counter is not visible next to that.
