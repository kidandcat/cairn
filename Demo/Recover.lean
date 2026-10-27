import Cairn

open Cairn

def parseNat (s : String) : Option Nat :=
  let rec go : List Char → Nat → Option Nat
    | [], n => some n
    | c :: cs, n =>
        if c < '0' || '9' < c then
          none
        else
          go cs (n * 10 + (c.toNat - '0'.toNat))
  if s.isEmpty then none else go s.toList 0

def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

def sortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNat xs)

/-
Reopen `PATH` and require the recovered keys to be exactly `0 .. k-1` for some `k`.
An empty file is the empty prefix.
-/

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | throw (IO.userError "usage: cairn-recover PATH")
  let db ← DB.openFile path
  let mut ns : List Nat := []
  for e in (← db.iterate) do
    let some s := String.fromUTF8? e.1.bytes.toByteArray
      | throw (IO.userError "non-utf8 key")
    let some n := parseNat s
      | throw (IO.userError s!"key is not a decimal: {s}")
    ns := n :: ns
  let sorted := sortNat ns
  if sorted != List.range sorted.length then
    throw (IO.userError s!"recovered keys are not a prefix of 0,1,2,... ({sorted.length} keys)")
  IO.println s!"recovered {sorted.length} keys, a prefix of the committed writes"
  return 0
