# Releasing

Versions are SemVer: `MAJOR.MINOR.PATCH`. This repository is on `0.x`
until a release is declared stable. Tags look like `v0.1.0` (a leading
`v`, no other prefix). Do not tag from a pull request; tag the commit on
`main` after it is merged.

Three strings must stay equal. `scripts/check_version.sh` fails CI if they
differ:

- `version := v!"X.Y.Z"` in `lakefile.lean`
- the top `## [X.Y.Z]` heading in `CHANGELOG.md`
- `def version : String := "X.Y.Z"` in `Cairn/Version.lean` (no leading `v`)

## Steps

1. Pick the next version from the change since the last tag.
   - `PATCH` for a fix that does not change the stated guarantees.
   - `MINOR` for a backwards-compatible addition while still on `0.x`, or
     for a notable addition after `1.0.0`.
   - `MAJOR` for a break callers cannot absorb, and for the first release
     that is willing to call itself stable (`1.0.0`). Lake's own note
     applies: a Lean package can break at any bump. The number says how
     hard the migration is meant to be.
2. Bump the three strings above in one commit.
3. Write the changelog section for that version at the top, dated the day
   you cut it (`## [X.Y.Z] - YYYY-MM-DD`). Say what is proved, what is
   only tested, and what is still out of scope when that changed.
4. Merge to `main`. Wait until CI is green, including the version check,
   `lake build`, and `lake test`.
5. Tag the merge commit: `git tag -a vX.Y.Z -m "vX.Y.Z"` and push the tag.
6. Create a GitHub release for that tag. Use the changelog section as the
   body. Do not attach a claim the README does not already stand behind.
