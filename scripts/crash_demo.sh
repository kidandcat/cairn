#!/bin/sh
# Start a writer, kill -9 it mid-run, reopen, and require a prefix of the keys.
set -eu
cd "$(dirname "$0")/.."
# shellcheck disable=SC1091
. "$HOME/.elan/env"
lake build cairn-crash-writer cairn-recover
tmp="$(mktemp)"
./.lake/build/bin/cairn-crash-writer "$tmp" 2000 &
pid=$!
sleep 0.3
kill -9 "$pid" 2>/dev/null || true
wait "$pid" 2>/dev/null || true
./.lake/build/bin/cairn-recover "$tmp"
rm -f "$tmp"
