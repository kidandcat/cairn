/-
Reopen after a kill and apply the durable inbox once.
-/

import Cairn

open Cairn

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: cairn-actor-recover PATH")
  Store.repairFile (path ++ "/shard-0.cairn")
  let s ← ShardSet.openFiles path Epoch.single
  let (rows, _) ← s.localPrefix 0 (outPrefix 0) none 10000
  let notices := rows.length
  let n ← propagate s 0 0 fun payload tx => do
    tx.put payload payload
  let n2 ← propagate s 0 0 fun payload tx => do
    tx.put payload (⟨[9], by decide⟩)
  if n2 != 0 then
    throw (IO.userError "duplicate apply")
  if n != notices then
    throw (IO.userError s!"lost notices: applied {n} of {notices}")
  IO.println s!"actor recovered {notices} notices, applied once"
  s.close
  return 0
