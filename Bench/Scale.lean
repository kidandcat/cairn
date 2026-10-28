/-
Prefix pages and claims at 1k, 10k and 100k keys. Not part of `lake test`.
The fill is outside the clock. Three repetitions.
-/

import Cairn

open Cairn

def keyOf (i : Nat) : FitBytes where
  bytes := [0, UInt8.ofNat ((i / 65536) % 256), UInt8.ofNat ((i / 256) % 256), UInt8.ofNat (i % 256)]
  hlen := by
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    decide

def showOnce (name : String) (run : IO Nat) : IO Unit := do
  let mut line := name
  for _ in [0:3] do
    let dt ← run
    line := line ++ s!"  {dt}ns"
  IO.println line

def timePrefix (n pages : Nat) : IO Nat := do
  let s ← ShardSet.openMem Epoch.single
  for i in [0:n] do
    s.put (keyOf i) (keyOf i)
  let t0 ← IO.monoNanosNow
  let mut after : Option FitBytes := none
  for _ in [0:pages] do
    let (_, cur) ← s.prefix [0] after 100
    after := cur
  let t1 ← IO.monoNanosNow
  s.close
  return t1 - t0

def timeClaim (n takes : Nat) : IO Nat := do
  let s ← ShardSet.openMem Epoch.single
  for i in [0:n] do
    if ht : i < 2 ^ 48 then
      Queue.enqueue s 1 0 ⟨i, 0, ht, by decide⟩ [1]
  let t0 ← IO.monoNanosNow
  for _ in [0:takes] do
    let _ ← Queue.claim s 0 1000000000
  let t1 ← IO.monoNanosNow
  s.close
  return t1 - t0

def main : IO UInt32 := do
  for n in [1000, 10000, 100000] do
    showOnce s!"prefix-pages n={n} pages=10" (timePrefix n 10)
    showOnce s!"claim n={n} takes=20" (timeClaim n 20)
  return 0
