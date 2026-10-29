# Contributing

## Build and test

The pin is `leanprover/lean4:v4.35.0` (`lean-toolchain`). [elan](https://github.com/leanprover/elan) installs it.

```
lake build
lake test
sh scripts/check_version.sh
```

`lake test` is the deterministic suite: unit checks, sampled crash cuts, a
real file, in-process shards, and overlapping tasks. It prints
`cairn tests ok` and a fuzz tally. It does not run the benchmarks or the
`kill -9` demos.

```
./scripts/crash_demo.sh
./scripts/actor_crash.sh
./.lake/build/bin/cairn-backend
```

The bench binaries (`cairn-bench`, `cairn-durable-bench`,
`cairn-design-bench`, `cairn-scale-bench`, `cairn-copy-bench`,
`cairn-actor-bench`) are not part of CI. If you publish a number, copy the
repetitions. Do not replace them with an average.

## Proofs and axioms

The library does not declare `axiom`, `sorry`, or `partial`. `#print axioms`
on the theorems in the README should report only kernel axioms: `propext`,
`Quot.sound`, and `Classical.choice` where `omega` uses it. Do not add
`bv_decide` axioms.

A pull request that states a new guarantee names the theorem, or it says
the claim is a test or a measurement. Do not describe `IO.Ref`,
`Std.Mutex`, the C shim, or a future socket as proved. The byte-prefix
theorems are about a prefix of a well-formed encoding. A checksum collision
and a power cut are outside those theorems unless a new proof says
otherwise.

There is no separate axioms script in the tree. The check is the absence of
`sorry` / `axiom` / `partial` in the library, plus the theorems `lake build`
typechecks.

## Pull requests

- One change, with the tests or theorems that cover it.
- English: code, comments, docs, errors, and the pull request text.
- Update `CHANGELOG.md` only when you are cutting a version. Day-to-day
  work waits for `RELEASING.md`.
- Keep the README honest if the proved / tested / not-verified split moved.
- CI on push runs `scripts/check_version.sh`, `lake build`, `lake test`,
  and the backend demo. Do not weaken that to get a green run.
