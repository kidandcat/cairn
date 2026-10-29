#!/bin/sh
# The lakefile version, the top CHANGELOG entry, and Cairn.version must match.
set -eu
cd "$(dirname "$0")/.."

lake=$(sed -n 's/^[[:space:]]*version := v!"\([0-9][0-9A-Za-z.+-]*\)".*/\1/p' lakefile.lean | head -n 1)
log=$(sed -n 's/^## \[\([0-9][0-9A-Za-z.+-]*\)\].*/\1/p' CHANGELOG.md | head -n 1)
code=$(sed -n 's/^def version : String := "\([0-9][0-9A-Za-z.+-]*\)".*/\1/p' Cairn/Version.lean | head -n 1)

if [ -z "$lake" ] || [ -z "$log" ] || [ -z "$code" ]; then
  echo "version check: could not read a version string" >&2
  echo "lakefile='${lake}' changelog='${log}' code='${code}'" >&2
  exit 1
fi

if [ "$lake" != "$log" ] || [ "$lake" != "$code" ]; then
  echo "version mismatch: lakefile=${lake} changelog=${log} code=${code}" >&2
  exit 1
fi

echo "version ${lake}"
