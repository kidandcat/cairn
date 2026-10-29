# Durability under power loss, and CRC

Report from the branch `cursor/durability-crc-35e9`. It is not merged. The owner decides when it lands on `main`. The concurrency comparison stays in its own PR. Several writers at once remains a non-goal.

The Lean core does not call FFI. The only C is `native/cairn_sync.c`, and only the file backend uses it (`Cairn.Posix`, imported by `Cairn.Store`). Lengths are `UInt32`, LSNs are `UInt64`, and there is no `USize` in the codec. There is no `sorry`, no declared `axiom`, no `partial`, no `bv_decide`, and no `native_decide`.

## The `sync` contract

After `sync` returns, every `append` and every `replaceAll` since the previous `sync` survives a cut. What has not passed through a completed `sync` may be lost, torn, reordered, or written only in part, at sector granularity.

The formal model is a stable image (what is already synced, block-aligned) plus a pending tail. `Tail.lost` keeps nothing of that tail. `Tail.take n` keeps a byte prefix. The sector case is `n` a multiple of `blockSize` (4096). A missing destination sector stays zeros in its place: the disk does not shift later sectors. The simulated `Storage` in `Cairn.Crash` exercises that. The theorem `recovery_keeps_synced` covers the byte prefix, which includes the sector prefix: if `n` covers the encoding of the groups already synced, `decodeFile` of that prefix returns those groups (and, if the cut fell further along, a prefix of what was in flight). The result is a prefix of what was sent. `GroupsFit` / `RecordsFit` is required: without that hypothesis `UInt32.ofNat` wraps and the statement is false.

The order of a commit is write, `sync`, and only then publish the view. Compaction is a new file, `fdatasync`, atomic `rename`, `fsync` of the directory. A rename never happens before the `fdatasync`. A cut after the `rename` and before the directory `fsync` can show the old name or the new one; both files were already data-synced.

The memory backend does `sync` and returns. It is not a disk.

## What is proved

On recovery, in Lean:

- `decodeFile_prefix` and `recovery_prefix`: a byte prefix of a well-formed encoding is a prefix of the records, and replay of that is the recovered map. `RecordsFit` is required.
- `recovery_keeps_synced`: if the prefix includes everything already synced, those operations are in the result, and the result is still a prefix of what was sent (synced plus in flight). `GroupsFit` is required.

That does not say that arbitrary junk pasted after a valid file is a prefix. A checksum collision could add a frame. It also does not cover a physical sector larger than 4096 bytes: that cut can split data that `sync` already treated as done.

On non-reflected CRC-32 (`sum32`, polynomial `0x04C11DB7`, init 0, no final xor), which is the checksum of the header and of each frame:

- `sum32_burst`: if the set bits fit in a window of 32 consecutive positions (`polyOf = B * 2^t` with `0 < B < 2^32`), the checksum is not zero. The limit is the width of the window, not the length of the message. It holds for any length.
- `sum32_one_bit` and `sum32_weight_one`: a single bit, or Hamming weight 1, is that window.
- `sum32_two_close`: two bits at distance `d` with `1 ≤ d ≤ 31`.
- `sum32_xor` and `sum32_detects_burst`: on two strings of the same length, the checksum of the xor is the xor of the checksums, so a burst of that kind changes the message checksum.
- `not_all_odd_weight`: `sum32 [1, 4, 0xC1, 0x1D, 0xB7] = 0` and the weight is odd (15). The polynomial does not detect every odd-weight error. `(x+1)` does not divide this polynomial; the counterexample is the proof, not a conjecture.

Not proved: two bits at distance greater than 31 (that would need the order of `x` modulo the polynomial). A fixed-width checksum is not promised to detect every corruption.

The reflected CRC of each record (`crc32`) stays. It is not `sum32`. The burst proof is about `sum32`.

`#print axioms` of `sum32_burst`, `sum32_detects_burst`, `recovery_keeps_synced`, `decodeFile_prefix`, and `recovery_prefix` reports only `propext`, `Quot.sound`, and `Classical.choice` (from `omega`).

## Corruption policy

`scan` separates four cases:

- `clean`: every byte belongs to a valid frame. Open does not rewrite the file.
- `torn`: a suffix is missing. It is truncated to what was consumed. A prefix of a valid encoding is `torn` or `clean`, never `corrupt`.
- `corrupt`: a complete frame fails and later there is another valid `SEG1` frame. `openFile` throws `corrupt log`. It does not return a half map.
- `reject`: it is not a cairn file (`"HI"`, `NOTACAIR`). It is not truncated and not overwritten. A real three-byte prefix of the header does open as an empty log.

`openFileRepair` truncates a torn tail and mid-log corruption on purpose. A `reject` still fails.

Two gaps that look like a torn tail and are therefore truncated, and are not flagged as mid-log corruption: a bit damaged only in the last segment, and a length field so damaged that the frame no longer fits in the file. They are documented. They are not silence: the result is a prefix, or an error if a valid frame follows.

## What is only tested

- The simulated `Storage` (`Cairn.Crash`): two synced puts and one unsynced frame in `.torn` mode of 10 bytes keep the prefix of length 2; `.keep` gives prefix 2 or 3; two pending frames `[.zero, .keep]` throw `corrupt log`. `lake test` checks this.
- Cuts of a 12-record log. The test walks `sampleCuts` (the first 80 bytes, the edges of each 4096-byte frame, and offsets 17 and 40). The proof covers every index.
- Fuzz of one valid three-record log, seed `0xC0FFEE`, multiplier `6364136223846793005`. 512 header bits, 768 bits at the start of the first segment, 200 random bits, and 200 nonzero byte masks. Total 1680. Result of this run:

```
fuzz [(detect, 1591), (torn, 89), (miss, 0), (forge, 0), (same, 0)]
cairn tests ok
```

`miss` would have accepted the altered bytes as the original records. `forge` would have produced a list that is not a prefix. Both stayed at zero on this set. The 89 `torn` results are prefixes and are truncated. This is a measurement of the classes covered, not a proof of every corruption. A burst of 4096 bytes is not a burst of ≤ 32 bits.

- `strace` on this Linux machine. Two puts (`cairn-crash-writer`): `open` with `O_TRUNC`, a `write` of 4096, `fdatasync`, `open` of the directory with `O_DIRECTORY`, `fsync`, and an `fdatasync` after each put. Compaction (`cairn-sync-trace`): `fdatasync` of the temporary `path.cairn-tmp`, `rename` onto the live file, `fsync` of the directory. The macOS path was not executed.
- `kill -9` (`scripts/crash_demo.sh`, wait 0.3 s, 2000 keys requested): `recovered 147 keys, a prefix of the committed writes`. That kills the process. It does not cut the power.

## What stays out

- A physical power cut. It cannot be provoked on this VM.
- `dm-flakey`. There is `sudo` and `loop` devices, but no `dmsetup` or `modprobe`, so the module was not loaded.
- A disk that answers `fsync` without having written.
- A physical sector larger than 4096 bytes.
- CRC collisions outside the proved classes, and two bits at distance greater than 31.
- Several concurrent writers.
- The macOS `F_FULLFSYNC` branch, compiled only under `__APPLE__`.

## Checksum decision

Measured: reflected CRC-32 (`crc32`, the one on records), `sum32` (the one on frames), CRC-64-ECMA (`sum64`, polynomial `0x42F0E1EBA9EA3693`, init 0, no final xor), and `mix128` (a multiply-and-xor mix in pure Lean: it is not xxHash, not BLAKE, not a cryptographic hash). `sum64` and `mix128` are not written to disk. The burst proof is about `sum32`. Moving the disk to a checksum without that proof does not pay: in this build the three CRCs come out at the same cost, and `mix128` is slower.

## How it was checked, and the numbers

Machine: 4 vCPU, `Intel(R) Xeon(R) Processor`, 2400 MHz according to `/proc/cpuinfo`, ext4 on `/dev/vdc`.

`lake test` finished in about 1.1 s with `cairn tests ok` and the fuzz above.

`cairn-durable-bench` is not part of `lake test`. One run, three repetitions. `sync-per-commit` is 100 `putStr`s, each with its own `fdatasync`. The groups are 256 puts in segments of 8, 32, or 128 records, one `fdatasync` per segment. The checksum folds 4096 bytes, 401 times, and keeps the digest.

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

The three repetitions of each checksum printed the same nanoseconds and the same sink; one line is kept here. On this run a put with `fdatasync` cost between 166 µs and 323 µs. A `sum32` of 4096 bytes comes out at about 33 µs. Group commit lowers the cost per put because the barrier is paid once per segment. The `fdatasync` latency on this VM moves from one run to another; it is not a disk that waits for stable media, and it does not apply to another machine.

There is no number for a real power cut, because one was not done.
