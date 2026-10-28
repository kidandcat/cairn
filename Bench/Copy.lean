/-
Propagate 1000 notices. Not part of `lake test`.
The home writes are outside the clock. Three repetitions.
-/

import Cairn

open Cairn

def keyA : FitBytes := ⟨[UInt8.ofNat 97], by decide⟩
def keyZ : FitBytes := ⟨[UInt8.ofNat 122], by decide⟩

def once (n : Nat) : IO Nat := do
  let s ← ShardSet.openMem { gen := 0, bounds := ["m".toUTF8.toList] }
  for i in [0:n] do
    let v : FitBytes := ⟨[UInt8.ofNat (i % 256)], by
      rw [List.length_cons, List.length_nil]
      decide⟩
    let _ ← commitCross s [.put keyA v, .put keyZ v]
  let t0 ← IO.monoNanosNow
  let _ ← propagate s 0 1 (fun _ _ => pure ())
  let t1 ← IO.monoNanosNow
  s.close
  return t1 - t0

def main : IO UInt32 := do
  let mut line := "propagate n=1000"
  for _ in [0:3] do
    let dt ← once 1000
    line := line ++ s!"  {dt}ns"
  IO.println line
  return 0
