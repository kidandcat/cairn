import Cairn

open Cairn

/- One put and a compact, so a trace can see data sync, rename, and directory fsync. -/
def main (args : List String) : IO UInt32 := do
  let [path] := args
    | throw (IO.userError "usage: cairn-sync-trace PATH")
  let db ← DB.openFile path
  db.putStr "k" "v"
  db.compact
  db.close
  return 0
