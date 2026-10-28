/-
Small backend on one process: a collection of items, minted with an
injectable clock. The job queue and the change feed land in later phases.
-/

import Cairn

open Cairn

def main : IO UInt32 := do
  let s ← ShardSet.openMem Epoch.single
  let tick ← IO.mkRef 0
  let gen ← IdGen.new (Clock.counter tick)
  let a ← gen.next
  let b ← gen.next
  let ra ← collInsert s "items" a (.str "one")
  let rb ← collInsert s "items" b (.nat 2)
  if ra != .ok 1 || rb != .ok 1 then
    throw (IO.userError "insert failed")
  let (rows, _) ← collList s "items" none 10
  match rows with
  | [x, y] =>
      if x.id.time > y.id.time then
        throw (IO.userError "list order")
  | _ => throw (IO.userError "list length")
  let updated ← collUpdate s "items" a 1 (.str "uno")
  if updated != .ok 2 then
    throw (IO.userError "update failed")
  let clash ← collUpdate s "items" a 1 (.str "no")
  if clash != .conflict then
    throw (IO.userError "cas failed")
  let id ← gen.next
  match FitBytes.ofList? [1, 2, 3] with
  | some anchor => Queue.enqueueWith s anchor [] 1 0 id [7]
  | none => throw (IO.userError "anchor")
  match ← Queue.claim s 0 1000 with
  | some _ => pure ()
  | none => throw (IO.userError "claim failed")
  let events ← s.watch 0 0 []
  if events.isEmpty then
    throw (IO.userError "feed empty")
  IO.println "backend demo ok"
  s.close
  return 0
