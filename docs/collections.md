# Ranges and collections

Phase 1 report. A `range` or a `prefix` is an ordered page. A collection is a key prefix, with a time-ordered id and version compare-and-set.

## How it is built

`rangeHits` and `prefixHits` filter `entries`. `lo` is inclusive, `hi` is exclusive, `after` is a strict cursor. The page is the `take` of that list. `pageCursor` is the last key if the page filled the limit.

On a `DB` that is one snapshot. On a `ShardSet` each shard contributes its snapshot, they are merged with `mergeAll`, and then the page is cut. A prefix may cross shards. There is no global snapshot: a commit can land between the read of one shard and the read of the next.

`rangeHits` and `prefixHits` remain the specification (the filter of `entries`). The runtime does not walk that list. `rangeWalk` and `prefixWalk` descend to the first key of the interval in the `TreeMap` (the slice's `get`) and stop after the first `limit` hits. `rangeWalk_eq` and `prefixWalk_eq` say that page is `rangePage` / `prefixPage`. On `ShardSet`, each local shard asks for only `limit` rows; `take_mergeAll` says the merge of those pages is the page of the full lists. A remote shard still sends the whole snapshot: the cut happens afterwards, on that list.

There is no big-O theorem. `Std.TreeMap`'s zipper is what stops after `limit`; cairn proves equality with the filter, not the height of the tree.

A document key is `01`, the `UInt32` length of the name, the name, `02`, and 16 bytes of `Ulid`. The byte order of the id is the time order. `IdGen` uses an injectable `Clock`. The value is a `UInt64` version plus a `Val` (`bytes`, `str`, or `nat`). `collUpdate` and `collDelete` read and write under the mutex of the shard of that key. If the version does not match, there is no write. The version does not wrap. One document is one key, so it falls in a single shard. Writing a collection on a remote shard throws `remote shard`.

## What is proved

No `sorry`. The axioms are still the core's (`propext`, `Quot.sound`, and `Classical.choice` where `omega` is used).

- `rangeHits_mem`, `prefixHits_mem`: an entry is in the result exactly when it is in the map and falls in the interval.
- `rangeHits_sorted`, `prefixHits_sorted`, `rangeHits_nodup`, `prefixHits_nodup`, and the same for the page: sorted, with no repeated keys.
- `resume_hits`, `resume_prefix`: the next page, using the cursor, is the tail of that list.
- `mergedHits_mem`: in the merge, an entry is present if some shard had it and it met the predicate.
- `Ulid.encode_lt_of_lt`: if the time or the random part is smaller, the bytes are smaller.
- `Ulid.fresh_increases`, `Ulid.bump_lt`: the pure step does not repeat an earlier id.
- `resolve_insert_fresh`, `resolve_insert_taken`, `resolve_update_ok`, `resolve_update_conflict`, `resolve_update_missing`, `resolve_delete_ok`, `resolve_delete_conflict`, `resolve_delete_missing`.
- `decodeDoc_encode`, `decode_encode_bytes`, `decode_encode_nat`.

- `rangeWalk_eq`, `prefixWalk_eq`: the page that comes out of the tree is the filter's page.
- `rangeWalk_cursor`, `prefixWalk_cursor`: that page's cursor is the full list's cursor.
- `isPrefixOf_iff_bounds`: a byte prefix is the interval `[p, prefixSucc p)`.
- `take_mergeAll`: the page of the merge is the merge of the pages.

Not proved: that `IO.Ref` publishes the `View` atomically, or an O(log n) bound on the zipper.

## What is only tested

`lake test` finished with `cairn tests ok` and the usual fuzz:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
```

That covers the range (`b` inclusive, `d` exclusive, a page of 2 and the rest, prefix `a`), the collection crossing two shards (times 1 and 5000, list order, version conflict, delete), and the counter clock. `scripts/crash_demo.sh` printed `recovered 135 keys, a prefix of the committed writes`. `cairn-backend` printed `backend demo ok`.

## Numbers

Same machine: 4 vCPU, Intel Xeon at 2400 MHz, ext4 on `/dev/vdc`. `cairn-design-bench`, three repetitions, not averaged. The shard rows stay in the post-tree band (one shard on a file about 0.16–0.18 ms/op, one shard in memory about 42–50 µs/op). The new row is the walk:

```
mem-prefix-pages ops=1000  1131ns/op 884173ops/s  1012ns/op 988142ops/s  931ns/op 1074113ops/s
```

One thousand keys, pages of 40, the `put` outside the clock. About 1 µs per key. That row is the list filter, from before the lower bound.

Afterwards, the same measurement binary (`cairn-scale-bench`) with the filter and with the tree. Ten pages of 100 keys, and twenty `claim`s on a queue of that size. The fill stays outside the clock. Three repetitions, total nanoseconds, not averaged. Same machine.

Filter:

```
prefix-pages n=1000 pages=10  500492ns  466960ns  449819ns
claim n=1000 takes=20  1797119ns  1893193ns  1742987ns
prefix-pages n=10000 pages=10  13078117ns  8042702ns  12331033ns
claim n=10000 takes=20  16361743ns  16722090ns  14686359ns
prefix-pages n=100000 pages=10  110819467ns  108574008ns  125024519ns
claim n=100000 takes=20  167798621ns  172838368ns  175225740ns
```

Tree:

```
prefix-pages n=1000 pages=10  177897ns  181377ns  159859ns
claim n=1000 takes=20  1259110ns  1132926ns  1072969ns
prefix-pages n=10000 pages=10  216441ns  200111ns  204997ns
claim n=10000 takes=20  2109340ns  1297754ns  1317937ns
prefix-pages n=100000 pages=10  219607ns  220689ns  245824ns
claim n=100000 takes=20  2075694ns  2100954ns  1406594ns
```

At 100000 keys, ten pages drop from about 110–125 ms to about 0.22–0.25 ms. The twenty claims drop from about 168–175 ms to about 1.4–2.1 ms. The prefix barely grows from 1000 to 100000 keys. That is the measurement; the bound is not proved.
