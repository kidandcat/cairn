/-
Drain 1000 actor notices. Not part of `lake test`.
The sends are outside the clock. Three repetitions.
-/

import Cairn

open Cairn

def once (n : Nat) : IO Nat := do
  let s ← ShardSet.openMem Epoch.single
  for i in [0:n] do
    let p : FitBytes := ⟨[UInt8.ofNat (i % 256)], by
      rw [List.length_cons, List.length_nil]
      decide⟩
    s.transactOn 0 fun tx =>
      tx.enqueue 0 (.msg p) (i % 65536)
  let t0 ← IO.monoNanosNow
  let _ ← propagate s 0 0 fun payload tx => do
    tx.putLocal payload payload
  let t1 ← IO.monoNanosNow
  s.close
  return t1 - t0

def main : IO UInt32 := do
  let mut line := "actor-drain n=1000"
  for _ in [0:3] do
    let dt ← once 1000
    line := line ++ s!"  {dt}ns"
  IO.println line
  return 0
