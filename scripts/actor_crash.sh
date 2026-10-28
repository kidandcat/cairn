#!/bin/sh
# Send actor messages, kill -9, reopen. Committed notices apply once.
set -eu
cd "$(dirname "$0")/.."
# shellcheck disable=SC1091
. "$HOME/.elan/env"
lake build cairn-actor-writer cairn-actor-recover
tmp="$(mktemp -d)"
./.lake/build/bin/cairn-actor-writer "$tmp" 40 &
pid=$!
sleep 0.4
kill -9 "$pid" 2>/dev/null || true
wait "$pid" 2>/dev/null || true
./.lake/build/bin/cairn-actor-recover "$tmp"
rm -rf "$tmp"
