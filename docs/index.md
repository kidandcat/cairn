# Tree index and a log that is not copied

Report of the single-shard change. The index stops being an associative list. The memory backend stops copying the byte log on every `append`, and the `View` stops doing `v.log ++ [record]`. There is still one writer per shard. The `View` is published with `IO.Ref.set` and read with `IO.Ref.get`.

## What changed

The map is `Std.TreeMap` with the key-byte comparator. The library keeps a size-balanced tree (delta 3, ratio 2). `get` is `TreeMap.get?`. `insert` and `erase` return another root and share the branches they do not touch. A reader that already did `Ref.get` keeps the previous tree.

`entries` is the inorder: lexicographic order of the key, each key once. Compaction emits one `put` per live key and, on replay, recovers those entries. Two trees with the same entries need not have the same shape, so `compact_eq`, `compact_roundtrip`, `move_replays`, and `moved_state` equate `entries`, not the roots. `state_eq_serial` and `snapshot_stable` are still structural equality: both sides fold the same sequence of `insert`.

The `View` log stores the newest record at the head. A `commit` does `record :: revLog`. `commitMany` copies only the new group (`built ++ revLog`) and shares the tail. `readLog`, `follow`, and the file see chronological order, which is the reverse.

`Store.mem` stores a list of frames, the new one in front. `append` is a cons. `readAll` reverses and flattens. `replaceAll` replaces with a single frame. The fault store (`FaultState`) still concatenates flat bytes: it is the cut injector, not the memory backend.

## What is proved

No `sorry` and no declared `axiom`. `#print axioms` of `get_insert`, `get_insert_ne`, `get_remove`, `nodup_replay`, `compact_eq`, `compact_roundtrip`, `entries_sorted`, `entries_nodup`, `entries_rebuilt`, `move_replays`, `moved_state`, `state_eq_serial`, `snapshot_stable`, `cluster_partition`, and `catchUp_state` reports `propext`, `Classical.choice`, and `Quot.sound`. `steps_commute` does not pull in `Classical.choice`.

- `get_insert`, `get_insert_ne`, `get_remove`, `get_remove_ne`: the list-index equations, on the tree.
- `entries_sorted`, `entries_nodup`, `entries_of_get`: iteration is sorted, does not repeat keys, and agrees with `get`.
- `nodup_replay` and the `nodup_*` lemmas for insert, erase, and filter by shard. The tree does not admit duplicate keys; the lemmas say so.
- `compact_eq` and `compact_roundtrip`: replaying the compacted log, including through the codec, returns the same `entries`.
- `move_replays` and `moved_state`: one shard's log, replayed, has the `entries` of `inShard`.
- `mem_inShard`, `rebalance_partition`, `cluster_partition`, `state_eq_serial`, `snapshot_stable`, `catchUp_state`, `steps_commute`: they still hold. The shard filter is `TreeMap.filter`.

An O(log n) bound is not proved. Balance is `Std.TreeMap`'s internal invariant, not a cairn theorem. It is also not proved that `IO.Ref.set` is atomic or that the mutex excludes two writers.

## What is only tested

`lake test` finished with `cairn tests ok`. The fuzz, seed `0xC0FFEE`, printed:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
```

The same five counters as before. Cuts of a 12-record log, the file (including the 8192-byte group commit and the torn tail), the router, the tasks, the fault store, and `ShardSet` are in that same `lake test`.

`scripts/crash_demo.sh` (`kill -9` at 0.3 s, which is not a power cut) printed `recovered 144 keys, a prefix of the committed writes`. An earlier pass, with the list index, had printed 147. Both are a prefix; the number depends on when the signal arrives.

## Numbers

One pass of `cairn-design-bench` before and one after, on the same machine: 4 vCPU, `Intel(R) Xeon(R) Processor` at 2400 MHz, ext4 on `/dev/vdc`. Three repetitions, not averaged. `open` stays outside the clock. `file-*` does `fdatasync`. `mem-*` is the same router in memory.

Before (associative list, `++` of the byte log and of the record log):

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

After:

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

On a file, one shard stays on the `fdatasync` cost (about 0.17–0.28 ms/op across the two passes). Four shards stay above one. Four tasks on a single shard stay on that shard's mutex. The group commit of 32 stays around 5–12 µs/op. The one-shard memory row goes from about 5.4–5.5 ms/op to about 34–59 µs/op. With 100 keys that drop is from no longer copying the 4096-byte frames, not a measurement of the tree's asymptotic gap against the linear scan.
