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
  let buf ← IO.mkRef ([] : List Bytes)
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

/-- Cuts the proof covers every index of. The test checks the header, frame edges, and a stride. -/
def sampleCuts (n : Nat) : List Nat :=
  let head := List.range (min n 80)
  let edges := (List.range (n / 4096 + 2)).flatMap fun i =>
    [min n (i * 4096), min n (i * 4096 + 17), min n (i * 4096 + 40)]
  head ++ edges ++ [n]

def testCrashCuts : IO Unit := do
  let buf ← IO.mkRef ([] : List Bytes)
  let db ← DB.openStore (Store.mem buf)
  for i in [0:12] do
    db.putStr (toString i) "x"
  let bytes ← db.store.readAll
  check "full prefix" ((← expectPrefix (← db.iterate)) == 12)
  for cut in sampleCuts bytes.length do
    let cutBuf ← IO.mkRef [bytes.take cut]
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
    let rejectedShort ← try
      let _ ← DB.openFile short
      pure false
    catch _ =>
      pure true
    check "non-prefix short rejected" rejectedShort
    let pref := FilePath.mk (dir.toString ++ "/pref")
    IO.FS.writeBinFile pref (encodeHeader.take 3).toByteArray
    let db4 ← DB.openFile pref
    check "header prefix is empty" ((← db4.iterate).isEmpty)
    db4.close
    let gpath := FilePath.mk (dir.toString ++ "/group")
    let gdb ← DB.openFile gpath
    gdb.commitMany [[.put (← mustFit "0") (← mustFit "a")],
      [.put (← mustFit "1") (← mustFit "b")]]
    gdb.close
    let gbytes ← IO.FS.readBinFile gpath
    check "group commit is one segment" (gbytes.size == 8192)
    let gdb2 ← DB.openFile gpath
    check "group 0" ((← gdb2.getStr "0") == some "a")
    check "group 1" ((← gdb2.getStr "1") == some "b")
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
  for n in sampleCuts enc.length do
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

def frameOf (lsn : UInt64) (k v : String) : IO Bytes := do
  let recd := Record.ofBatch lsn (Batch.single (.put (← mustFit k) (← mustFit v)))
  return encodeFrame segMagic (encodeRecord recd)

def testFault : IO Unit := do
  let st ← FaultState.new
  let db ← DB.openStore st.store
  db.putStr "0" "a"
  db.putStr "1" "b"
  st.store.append (← frameOf 50 "2" "c")
  let torn ← st.crash [.torn 10]
  let tbuf ← IO.mkRef [torn]
  let dbT ← DB.openStore (Store.mem tbuf)
  check "torn keeps synced" ((← expectPrefix (← dbT.iterate)) == 2)
  let kept ← st.crash [.keep]
  let kbuf ← IO.mkRef [kept]
  let dbK ← DB.openStore (Store.mem kbuf)
  let n ← expectPrefix (← dbK.iterate)
  check "kept tail is still a prefix" (n == 2 || n == 3)
  st.store.append (← frameOf 51 "3" "d")
  let holed ← st.crash [.zero, .keep]
  let bad ← try
    let hbuf ← IO.mkRef [holed]
    let _ ← DB.openStore (Store.mem hbuf)
    pure false
  catch e =>
    pure (e.toString == "corrupt log")
  check "hole then valid frame is corrupt" bad

def xorByte (bs : Bytes) (i : Nat) (mask : UInt8) : Bytes :=
  bs.take i ++
    match bs.drop i with
    | [] => []
    | b :: rest => (b ^^^ mask) :: rest

def flipBit (bs : Bytes) (bit : Nat) : Bytes :=
  xorByte bs (bit / 8) (1 <<< (bit % 8).toUInt8)

def lcg (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1

/-- `detect` / `torn` keep a prefix or refuse the file. `miss` accepts altered bytes unchanged. -/
def classFlip (orig : List Record) (origBytes altered : Bytes) : String :=
  let s := scan altered
  match s.kind with
  | .corrupt | .reject => "detect"
  | .torn => if s.records.isPrefixOf orig then "torn" else "forge"
  | .clean =>
      if altered == origBytes then "same"
      else if s.records == orig then "miss"
      else if s.records.isPrefixOf orig then "torn"
      else "forge"

def tally (counts : List (String × Nat)) (name : String) : List (String × Nat) :=
  counts.map fun p => if p.1 == name then (p.1, p.2 + 1) else p

def testFuzz : IO Unit := do
  let buf ← IO.mkRef ([] : List Bytes)
  let db ← DB.openStore (Store.mem buf)
  db.putStr "0" "a"
  db.putStr "1" "b"
  db.putStr "2" "c"
  let bytes ← db.store.readAll
  let orig ← db.readLog
  let mut counts : List (String × Nat) := [("detect", 0), ("torn", 0), ("miss", 0), ("forge", 0), ("same", 0)]
  -- Every bit of the header checksum region and the first segment header.
  for bit in [0:64 * 8] do
    counts := tally counts (classFlip orig bytes (flipBit bytes bit))
  for bit in [0:96 * 8] do
    counts := tally counts (classFlip orig bytes (flipBit bytes (4096 * 8 + bit)))
  -- A bit in the first segment, with two valid segments after it, is mid-log damage.
  let mid := scan (flipBit bytes (4096 * 8 + 16 * 8))
  check "mid-log bit is corrupt" (mid.kind == .corrupt)
  let mut state : UInt64 := 0xC0FFEE
  for _ in [0:200] do
    state := lcg state
    let bit := state.toNat % (bytes.length * 8)
    counts := tally counts (classFlip orig bytes (flipBit bytes bit))
  for _ in [0:200] do
    state := lcg state
    let i := state.toNat % bytes.length
    state := lcg state
    let mask := UInt8.ofNat (state.toNat % 255 + 1)
    counts := tally counts (classFlip orig bytes (xorByte bytes i mask))
  IO.println s!"fuzz {counts}"
  check "fuzz missed a flip" ((counts.lookup "miss") == some 0)
  check "fuzz forged a record" ((counts.lookup "forge") == some 0)

def fk (shard i : Nat) (tag : UInt8) : FitBytes where
  bytes := [UInt8.ofNat shard, UInt8.ofNat i, tag]
  hlen := by
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    decide

def isSorted : List (FitBytes × FitBytes) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => keyLe a b && isSorted (b :: rest)

def hasKey (es : List (FitBytes × FitBytes)) (b : Bytes) : Bool :=
  es.any fun e => e.1.bytes == b && e.2.bytes == b

/-- A visible tag from a pair means the whole pair is in this snapshot. -/
def pairsOk (es : List (FitBytes × FitBytes)) : Bool :=
  es.all fun e =>
    match e.1.bytes with
    | [s, i, _] => hasKey es [s, i, 1] && hasKey es [s, i, 2] && e.2.bytes == e.1.bytes
    | _ => false

def testShardSet : IO Unit := do
  let bounds : List Bytes := ["n".toUTF8.toList]
  let epoch : Epoch := { gen := 1, bounds := bounds }
  let s ← ShardSet.openMem epoch
  for k in ["a", "b", "m", "z"] do
    s.putStr k k
    let id ← s.shardId (← mustFit k)
    check s!"route {k}" (id == shardOf bounds (← mustFit k).bytes)
  check "a home" ((← s.shardId (← mustFit "a")) == 0)
  check "z home" ((← s.shardId (← mustFit "z")) == 1)
  let crossed ← try
    s.commit [.put (← mustFit "a") (← mustFit "a"), .put (← mustFit "z") (← mustFit "z")]
    pure false
  catch _ => pure true
  check "set cross-shard rejected" crossed
  let empty ← try
    s.commit []
    pure false
  catch _ => pure true
  check "set empty rejected" empty
  let log0 ← s.readLog 0
  let log1 ← s.readLog 1
  check "shard 0 keeps its hist" (Cairn.get (replay log0) (← mustFit "a") == some (← mustFit "a"))
  check "z not in shard 0" (Cairn.get (replay log0) (← mustFit "z") == none)
  check "shard 1 keeps its hist" (Cairn.get (replay log1) (← mustFit "z") == some (← mustFit "z"))
  check "a not in shard 1" (Cairn.get (replay log1) (← mustFit "a") == none)
  let merged := mergeAll [← s.localEntries 0, ← s.localEntries 1]
  let got ← s.iterate
  check "iterate is the merge" (got == merged)
  check "iterate sorted" (isSorted got)
  let view ← s.hostView
  check "host serves both" (view.serving == [0, 1])
  let before ← s.directory.get
  s.publish (ShardOwner.primary 0 { n := 0 } [{ shard := 0, replica := 1 }])
  let after ← s.directory.get
  check "publish bumps gen" (after.gen == before.gen + 1)
  check "publish keeps the leader" ((after.owner? 0).map (·.host) == some { n := 0 })
  let h0 ← ShardSet.openHosted epoch { n := 0 } [0]
  let h1 ← ShardSet.openHosted epoch { n := 1 } [1]
  let owners := [ShardOwner.primary 0 { n := 0 }, ShardOwner.primary 1 { n := 1 }]
  h0.directory.set { gen := 2, owners := owners }
  h1.directory.set { gen := 2, owners := owners }
  h0.remote.set fun dst req => h1.serve dst.shard req
  h1.remote.set fun dst req => h0.serve dst.shard req
  h0.putStr "a" "va"
  h0.putStr "z" "vz"
  check "remote put landed" ((← h1.getStr "z") == some "vz")
  check "local read of remote" ((← h0.getStr "z") == some "vz")
  check "remote read of local" ((← h1.getStr "a") == some "va")
  let remoteIter ← h0.iterate
  check "remote iterate length" (remoteIter.length == 2)
  check "remote iterate sorted" (isSorted remoteIter)
  let leader ← ShardSet.openMem Epoch.single
  leader.putStr "k" "v"
  let follower ← DB.openMem Epoch.single
  let box ← InProc.new
  let emptyRep : Replica := { epochGen := 0, log := [] }
  leader.pushLog box.mailbox 0 emptyRep { shard := 0, replica := 1 }
  let msgs ← box.drain { shard := 0, replica := 1 }
  check "catch-up mailed" (msgs.length == 1)
  for rpc in msgs do
    let reply ← follower.follow rpc
    check "follower applied" (reply == .ok 1)
  check "follower has k" ((← follower.getStr "k") == some "v")
  let mismatched ← try
    leader.pushLog box.mailbox 0 { epochGen := 9, log := [] } { shard := 0, replica := 1 }
    pure false
  catch _ => pure true
  check "epoch mismatch sends nothing" mismatched

def testShardFiles : IO Unit := do
  let dir ← IO.FS.createTempDir
  try
    let bounds : List Bytes := ["n".toUTF8.toList]
    let epoch : Epoch := { gen := 1, bounds := bounds }
    let s ← ShardSet.openFiles dir epoch
    s.putStr "a" "a"
    s.putStr "b" "b"
    s.putStr "z" "z"
    let t0 ← IO.asTask (prio := .dedicated) do
      for i in [0:4] do
        s.putStr s!"a{i}" "v"
    let t1 ← IO.asTask (prio := .dedicated) do
      for i in [0:4] do
        s.putStr s!"z{i}" "v"
    match ← IO.wait t0 with
    | .ok () => pure ()
    | .error e => throw e
    match ← IO.wait t1 with
    | .ok () => pure ()
    | .error e => throw e
    s.close
    let path0 := dir.toString ++ "/shard-0.cairn"
    let raw ← IO.FS.readBinFile path0
    check "shard file has a header" (raw.size ≥ 4096)
    IO.FS.writeBinFile path0 (raw.extract 0 4096)
    let s2 ← ShardSet.openFiles dir epoch
    check "crashed shard dropped its tail" ((← s2.getStr "a") == none)
    check "other shard kept z" ((← s2.getStr "z") == some "z")
    check "other shard kept z0" ((← s2.getStr "z0") == some "v")
    s2.close
  finally
    IO.FS.removeDirAll dir

def testShardStress : IO Unit := do
  let bounds : List Bytes := [[1], [2], [3]]
  let epoch : Epoch := { gen := 0, bounds := bounds }
  let s ← ShardSet.openMem epoch
  let mut tasks : List (Task (Except IO.Error Unit)) := []
  for shard in [0:4] do
    let t ← IO.asTask (prio := .dedicated) do
      for i in [0:20] do
        s.commit [.put (fk shard i 1) (fk shard i 1), .put (fk shard i 2) (fk shard i 2)]
    tasks := t :: tasks
  for _ in [0:2] do
    let t ← IO.asTask (prio := .dedicated) do
      for _ in [0:15] do
        let es ← s.iterate
        check "live merge sorted" (isSorted es)
        for shard in [0:4] do
          check "live pair" (pairsOk (← s.localEntries shard))
    tasks := t :: tasks
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => throw e
  let mut parts : List (List (FitBytes × FitBytes)) := []
  for shard in [0:4] do
    let es ← s.localEntries shard
    check "final pair" (pairsOk es)
    check s!"shard count {shard}" (es.length == 40)
    parts := parts ++ [es]
    for i in [0:20] do
      let id ← s.shardId (fk shard i 1)
      check "stress route" (id == shardOf bounds (fk shard i 1).bytes)
  check "stress iterate is the merge" ((← s.iterate) == mergeAll parts)
  check "stress iterate sorted" (isSorted (← s.iterate))

def earlyId : Ulid :=
  ⟨1, 0, by decide, by decide⟩

def lateId : Ulid :=
  ⟨5000, 0, by decide, by decide⟩

def requireKey (name : String) (id : Ulid) : IO FitBytes := do
  match docKey? (name.toUTF8.toList) id with
  | some k => return k
  | none => throw (IO.userError "key")

def testRange : IO Unit := do
  let db ← DB.openMem
  for s in ["a", "b", "c", "d", "ab", "ac"] do
    db.putStr s s
  let b ← mustFit "b"
  let d ← mustFit "d"
  let (mid, cur) ← db.range (some b) (some d) none 10
  check "range keys" (mid.map (·.1.bytes) == ["b".toUTF8.toList, "c".toUTF8.toList])
  check "range short cursor" (cur == none)
  let (page, more) ← db.range none none none 2
  check "page length" (page.length == 2)
  check "page cursor" (more == page.getLast?.map (·.1))
  let (rest, done) ← db.range none none more 10
  check "second page" (rest.map (·.1) == ((← db.iterate).map (·.1)).drop 2)
  check "second cursor" (done == none)
  let (pref, _) ← db.prefix ("a".toUTF8.toList) none 10
  check "prefix" (pref.map (·.1.bytes) == ["a".toUTF8.toList, "ab".toUTF8.toList, "ac".toUTF8.toList])
  db.close

def testColl : IO Unit := do
  let early := earlyId
  let late := lateId
  let name := "box"
  let kLate := (docKey? (name.toUTF8.toList) late).getD (← mustFit "missing")
  let epoch : Epoch := { gen := 0, bounds := [kLate.bytes] }
  let s ← ShardSet.openMem epoch
  check "insert early" ((← collInsert s name early (.str "e")) == .ok 1)
  check "insert late" ((← collInsert s name late (.nat 7)) == .ok 1)
  check "insert again" ((← collInsert s name early (.str "no")) == .conflict)
  check "homes differ" ((← s.shardId (← requireKey name early)) != (← s.shardId (← requireKey name late)))
  let (rows, _) ← collList s name none 10
  check "list length" (rows.length == 2)
  check "list order" (rows.map (·.id.time) == [1, 5000])
  check "list values" (rows.map (·.val) == [.str "e", .nat 7])
  check "bad update" ((← collUpdate s name early 9 (.str "x")) == .conflict)
  check "update" ((← collUpdate s name early 1 (.str "E")) == .ok 2)
  check "get" ((← collGet s name early) == some (2, .str "E"))
  check "bad delete" ((← collDelete s name early 1) == .conflict)
  check "delete" ((← collDelete s name early 2) == .ok 0)
  check "gone" ((← collGet s name early) == none)
  let (left, _) ← collList s name none 10
  check "one left" (left.map (·.id.time) == [5000])
  let gen ← IdGen.new (Clock.counter (← IO.mkRef 10))
  let a ← gen.next
  let b ← gen.next
  check "mint order" (a.time < b.time)
  check "mint insert" ((← collInsert s "gen" a (.bytes [1, 2])) == .ok 1)
  let (page, cur) ← collList s "gen" none 1
  check "gen page" (page.length == 1 && cur.map (·.time) == some a.time)
  let (rest, _) ← collList s "gen" cur 10
  check "gen rest empty" (rest.isEmpty)
  s.close

def main : IO UInt32 := do
  testMem
  testCrashCuts
  testFile
  testRouterAndReplicas
  testConcurrent
  testFault
  testFuzz
  testShardSet
  testShardFiles
  testShardStress
  testRange
  testColl
  IO.println "cairn tests ok"
  return 0
