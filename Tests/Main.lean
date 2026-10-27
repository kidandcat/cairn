import Cairn

open Cairn System

def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError name)

def mustFit (s : String) : IO FitBytes := do
  match FitBytes.ofString? s with
  | some f => return f
  | none => throw (IO.userError s!"too long: {s}")

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

def keyNats (ents : List (FitBytes × FitBytes)) : IO (List Nat) := do
  let mut ns : List Nat := []
  for e in ents do
    let some s := String.fromUTF8? e.1.bytes.toByteArray
      | throw (IO.userError "non-utf8 key")
    let some n := parseNat s
      | throw (IO.userError s!"key {s}")
    ns := n :: ns
  return ns

def expectPrefix (ents : List (FitBytes × FitBytes)) : IO Nat := do
  let ns ← keyNats ents
  let sorted := sortNat ns
  check "recovered keys are not a prefix" (sorted == List.range sorted.length)
  return sorted.length

def testMem : IO Unit := do
  let buf ← IO.mkRef ([] : Bytes)
  let db ← DB.openStore (Store.mem buf)
  db.putStr "a" "1"
  check "get a" ((← db.getStr "a") == some "1")
  db.deleteStr "a"
  check "deleted a" ((← db.getStr "a") == none)
  let k1 ← mustFit "p"
  let v1 ← mustFit "left"
  let k2 ← mustFit "q"
  let v2 ← mustFit "right"
  db.commit [.put k1 v1, .put k2 v2]
  check "batch p" ((← db.getStr "p") == some "left")
  check "batch q" ((← db.getStr "q") == some "right")
  let emptyFailed ← try
    db.commit []
    pure false
  catch _ =>
    pure true
  check "empty batch rejected" emptyFailed
  db.putStr "z" "9"
  db.compact
  db.close
  let db2 ← DB.openStore (Store.mem buf)
  check "compact p" ((← db2.getStr "p") == some "left")
  check "compact z" ((← db2.getStr "z") == some "9")
  check "compact a gone" ((← db2.getStr "a") == none)

def testCrashCuts : IO Unit := do
  let buf ← IO.mkRef ([] : Bytes)
  let db ← DB.openStore (Store.mem buf)
  for i in [0:12] do
    db.putStr (toString i) "x"
  let bytes ← buf.get
  check "full prefix" ((← expectPrefix (← db.iterate)) == 12)
  for cut in [0:bytes.length + 1] do
    let cutBuf ← IO.mkRef (bytes.take cut)
    let db2 ← DB.openStore (Store.mem cutBuf)
    let n ← expectPrefix (← db2.iterate)
    check "cut grew the log" (n ≤ 12)

def testFile : IO Unit := do
  let dir ← IO.FS.createTempDir
  try
    let path := FilePath.mk (dir.toString ++ "/db")
    let db ← DB.openFile path
    db.putStr "a" "1"
    db.putStr "b" "2"
    db.deleteStr "a"
    let k ← mustFit "c"
    let v ← mustFit "3"
    db.commit [.put k v, .del (← mustFit "b")]
    db.putStr "d" "4"
    db.compact
    db.close
    let db2 ← DB.openFile path
    check "file a" ((← db2.getStr "a") == none)
    check "file b" ((← db2.getStr "b") == none)
    check "file c" ((← db2.getStr "c") == some "3")
    check "file d" ((← db2.getStr "d") == some "4")
    db2.close
    let h ← IO.FS.Handle.mk path .append
    h.write [0, 1, 2, 3, 4].toByteArray
    h.flush
    let db3 ← DB.openFile path
    check "torn tail kept d" ((← db3.getStr "d") == some "4")
    db3.close
    let bad := FilePath.mk (dir.toString ++ "/bad")
    IO.FS.writeBinFile bad "NOTACAIR".toUTF8
    let rejected ← try
      let _ ← DB.openFile bad
      pure false
    catch _ =>
      pure true
    check "bad magic rejected" rejected
    let short := FilePath.mk (dir.toString ++ "/short")
    IO.FS.writeBinFile short "HI".toUTF8
    let db4 ← DB.openFile short
    check "torn header is empty" ((← db4.iterate).isEmpty)
  finally
    IO.FS.removeDirAll dir

def testRouterAndReplicas : IO Unit := do
  let bounds : List Bytes := ["n".toUTF8.toList]
  let epoch : Epoch := { gen := 3, bounds := bounds }
  check "empty router" (shardOf [] [1] == 0)
  check "hash in range" (shardHash 4 [1, 2, 3] < 4)
  check "hash zero" (shardHash 0 [1] == 0)
  let s0 ← DB.openMem epoch
  let s1 ← DB.openMem epoch
  let keys := ["a", "c", "m", "z", "n", "b"]
  for k in keys do
    let shard := shardOf bounds k.toUTF8.toList
    let db := if shard == 0 then s0 else s1
    db.putStr k k
  let a ← mustFit "a"
  let z ← mustFit "z"
  let crossed ← try
    s0.commit [.put a a, .put z z]
    pure false
  catch _ =>
    pure true
  check "cross-shard rejected" crossed
  s0.commit [.put a a, .put (← mustFit "b") (← mustFit "b")]
  let r0 ← DB.openMem epoch
  let r1 ← DB.openMem epoch
  let log0 ← s0.readLog
  let log1 ← s1.readLog
  let box ← InProc.new
  box.send { shard := 0, replica := 0 } { shard := 0, replica := 1 } (.appendEntries epoch.gen 0 log0)
  box.send { shard := 1, replica := 0 } { shard := 1, replica := 1 } (.appendEntries epoch.gen 0 log1)
  let m0 ← box.drain { shard := 0, replica := 1 }
  let m1 ← box.drain { shard := 1, replica := 1 }
  check "mailbox 0" (m0.length == 1)
  check "mailbox 1" (m1.length == 1)
  for rpc in m0 do
    let reply ← r0.follow rpc
    check "follow 0" (reply == .ok log0.length)
  for rpc in m1 do
    let reply ← r1.follow rpc
    check "follow 1" (reply == .ok log1.length)
  for k in keys do
    let shard := shardOf bounds k.toUTF8.toList
    let lead := if shard == 0 then s0 else s1
    let foll := if shard == 0 then r0 else r1
    check s!"replica {k}" ((← foll.getStr k) == (← lead.getStr k))
  let stale ← r0.followSuffix 99 0 []
  check "epoch mismatch" (stale == .epochMismatch)
  let leader : Replica := { epochGen := epoch.gen, log := log0 }
  for n in [0:log0.length + 1] do
    check "truncate catch-up" ((catchUp (leader.truncate n) leader).state == leader.state)
  let enc := encodeFile log0
  for n in [0:enc.length + 1] do
    match leader.crashBytes n with
    | .error msg => throw (IO.userError s!"prefix rejected: {msg}")
    | .ok f =>
        check "byte crash catch-up" ((catchUp f leader).state == leader.state)
  let stray := recordsOf 50 [.put (← mustFit "stray") (← mustFit "x")]
  let diverged : Replica := { epochGen := epoch.gen, log := log0 ++ stray }
  check "leader wins" ((catchUp diverged leader).log == leader.log)
  let src ← DB.openMem
  for k in ["a", "b", "m", "z"] do
    src.putStr k k
  let idx := (← src.snapshot).index
  let d0 ← DB.openMem
  let d1 ← DB.openMem
  let moved0 := moved idx bounds 0 7
  let moved1 := moved idx bounds 1 7
  d0.adopt { gen := 7, bounds := bounds } moved0.log
  d1.adopt { gen := 7, bounds := bounds } moved1.log
  check "move a" ((← d0.getStr "a") == some "a")
  check "move b" ((← d0.getStr "b") == some "b")
  check "move m stays" ((← d0.getStr "m") == some "m")
  check "z not on 0" ((← d0.getStr "z") == none)
  check "z on 1" ((← d1.getStr "z") == some "z")
  check "a not on 1" ((← d1.getStr "a") == none)
  check "epoch published" ((← d0.readEpoch).gen == 7)

def checkView (db : DB) : IO Unit := do
  let v ← db.snapshot
  for w in [0:2] do
    for i in [0:20] do
      let tag := s!"{w}-{i}"
      let k1 ← mustFit (tag ++ "a")
      let k2 ← mustFit (tag ++ "b")
      match Cairn.get v.index k1, Cairn.get v.index k2 with
      | none, none => pure ()
      | some x, some y =>
          check "pair value" (x == k1 && y == k2)
      | _, _ => throw (IO.userError s!"torn batch {tag}")

def testConcurrent : IO Unit := do
  let db ← DB.openMem
  let mut tasks : List (Task (Except IO.Error Unit)) := []
  for w in [0:2] do
    let t ← IO.asTask (prio := .dedicated) do
      for i in [0:20] do
        let tag := s!"{w}-{i}"
        db.commit [.put (← mustFit (tag ++ "a")) (← mustFit (tag ++ "a")),
          .put (← mustFit (tag ++ "b")) (← mustFit (tag ++ "b"))]
    tasks := t :: tasks
  for _ in [0:4] do
    let t ← IO.asTask (prio := .dedicated) do
      for _ in [0:30] do
        checkView db
    tasks := t :: tasks
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => throw e
  checkView db
  check "final pair" ((← db.getStr "1-19a") == some "1-19a")
  check "final pair b" ((← db.getStr "0-0b") == some "0-0b")

def main : IO UInt32 := do
  testMem
  testCrashCuts
  testFile
  testRouterAndReplicas
  testConcurrent
  IO.println "cairn tests ok"
  return 0
