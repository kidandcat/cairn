import Cairn

open Cairn

/-
Write keys "0" .. "COUNT-1", flushing each one, with a short pause so a
`kill -9` lands between commits. Each commit is one record.
-/

def main (args : List String) : IO UInt32 := do
  let [path, ns] := args
    | throw (IO.userError "usage: cairn-crash-writer PATH COUNT")
  let some n := ns.toNat?
    | throw (IO.userError s!"not a count: {ns}")
  let db ← DB.openFile path
  for i in [0:n] do
    db.putStr (toString i) "1"
    IO.sleep 1
  db.close
  return 0
