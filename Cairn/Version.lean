namespace Cairn

/--
Package version, SemVer `major.minor.patch`, without a leading `v`.

The same string is `version := v!"0.1.0"` in `lakefile.lean` and the top
heading of `CHANGELOG.md`. `scripts/check_version.sh` checks the three.
-/
def version : String := "0.1.0"

end Cairn
