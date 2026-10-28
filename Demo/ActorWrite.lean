/-
Send durable actor messages, then sleep so a kill can land after some syncs.
-/

import Cairn

open Cairn

def main (args : List String) : IO UInt32 := do
  let [path, ns] := args | throw (IO.userError "usage: cairn-actor-writer PATH COUNT")
  let some n := ns.toNat? | throw (IO.userError "count")
  let s ← ShardSet.openFiles path Epoch.single
  for i in [0:n] do
    let p : FitBytes := ⟨[UInt8.ofNat (i % 256)], by
      rw [List.length_cons, List.length_nil]
      decide⟩
    s.send 0 { origin := 0, payload := p }
  IO.sleep 30000
  s.close
  return 0
