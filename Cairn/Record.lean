/-
Length-prefixed, checksummed records.

A record is one atomic batch. The on-disk frame is

  magic `REC1` ‖ lsn : UInt64 ‖ count : UInt32 ‖ ops ‖ crc32(body)

Each key and value carries its own `UInt32` length (`FitBytes`). A crash is
modelled as taking a prefix of the byte string. A proper prefix cannot meet a
length field, so `decode` of a truncated log is a prefix of the committed
records. CRC-32 is a deterministic filter for bit flips; the truncation proof
does not assume it is collision-free.
-/

import Cairn.Bytes

namespace Cairn

/-! ## Operations -/

inductive Op where
  | put (k v : FitBytes)
  | del (k : FitBytes)
  deriving Repr

def Op.key : Op → FitBytes
  | .put k _ => k
  | .del k => k

instance : BEq Op where
  beq
    | .put a b, .put c d => a == c && b == d
    | .del a, .del b => a == b
    | _, _ => false

/-- A batch small enough that its length fits in the `UInt32` count. -/
structure Batch where
  ops : List Op
  hlen : ops.length < UInt32.size

def Batch.ofList? (ops : List Op) : Option Batch :=
  if h : ops.length < UInt32.size then some ⟨ops, h⟩ else none

def Batch.single (op : Op) : Batch where
  ops := [op]
  hlen := by
    have h : [op].length = 1 := by simp
    rw [h]
    decide

def encodeOp : Op → Bytes
  | .put k v => (1 : UInt8) :: (writeFit k ++ writeFit v)
  | .del k => (2 : UInt8) :: writeFit k

def decodeOp : Bytes → Option (Op × Bytes)
  | [] => none
  | b :: bs =>
      if b == 1 then
        Option.bind (readFit bs) fun p =>
          Option.bind (readFit p.2) fun q =>
            some (.put p.1 q.1, q.2)
      else if b == 2 then
        Option.bind (readFit bs) fun p =>
          some (.del p.1, p.2)
      else
        none

theorem encodeOp_pos (op : Op) : 0 < (encodeOp op).length := by
  cases op <;> simp [encodeOp, writeFit_length]

theorem decodeOp_write (op : Op) (rest : Bytes) :
    decodeOp (encodeOp op ++ rest) = some (op, rest) := by
  cases op with
  | put k v =>
      rw [encodeOp, List.cons_append, decodeOp, beq_self_eq_true, ite_eq_left rfl,
        List.append_assoc, readFit_write, Option.bind_some, readFit_write, Option.bind_some]
  | del k =>
      rw [encodeOp, List.cons_append, decodeOp]
      simp [readFit_write, Option.bind_some]

theorem readTwoFits_prefix (k v : FitBytes) (n : Nat)
    (hn : n < (writeFit k ++ writeFit v).length) :
    (Option.bind (readFit ((writeFit k ++ writeFit v).take n)) fun p =>
        Option.bind (readFit p.2) fun q => some (Op.put p.1 q.1, q.2)) = none := by
  by_cases hlt : n < (writeFit k).length
  · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), readFit_prefix k n hlt, Option.bind_none]
  · have hge : (writeFit k).length ≤ n := by omega
    rw [List.take_append, List.take_of_length_le hge, readFit_write, Option.bind_some]
    have hn2 : n - (writeFit k).length < (writeFit v).length := by
      rw [List.length_append] at hn
      omega
    rw [readFit_prefix v _ hn2, Option.bind_none]

theorem decodeOp_prefix (op : Op) (n : Nat) (hn : n < (encodeOp op).length) :
    decodeOp ((encodeOp op).take n) = none := by
  cases op with
  | del k =>
      cases n with
      | zero => simp [encodeOp, decodeOp]
      | succ n =>
          have hn' : n < (writeFit k).length := by
            simp [encodeOp, List.length_cons] at hn
            omega
          simp [encodeOp, decodeOp, List.take_succ_cons, readFit_prefix k n hn', Option.bind_none]
  | put k v =>
      cases n with
      | zero => simp [encodeOp, decodeOp]
      | succ n =>
          have hn' : n < (writeFit k ++ writeFit v).length :=
            Nat.lt_of_succ_lt_succ (by simpa [encodeOp, List.length_cons] using hn)
          simp [encodeOp, decodeOp, List.take_succ_cons, readTwoFits_prefix k v n hn']

def encodeOps : List Op → Bytes
  | [] => []
  | op :: ops => encodeOp op ++ encodeOps ops

def decodeOps : Nat → Bytes → Option (List Op × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
      Option.bind (decodeOp bs) fun p =>
        Option.bind (decodeOps n p.2) fun q =>
          some (p.1 :: q.1, q.2)

theorem decodeOps_write : ∀ (ops : List Op) (rest : Bytes),
    decodeOps ops.length (encodeOps ops ++ rest) = some (ops, rest)
  | [], rest => by unfold decodeOps encodeOps; simp
  | op :: ops, rest => by
      rw [List.length_cons, decodeOps.eq_2, encodeOps, List.append_assoc, decodeOp_write,
        Option.bind_some, decodeOps_write ops, Option.bind_some]

theorem decodeOps_prefix : ∀ (ops : List Op) (n : Nat),
    n < (encodeOps ops).length → decodeOps ops.length ((encodeOps ops).take n) = none
  | [], n, hn => by simp [encodeOps] at hn
  | op :: ops, n, hn => by
      rw [encodeOps] at hn
      rw [List.length_append] at hn
      rw [List.length_cons, decodeOps.eq_2, encodeOps]
      by_cases hlt : n < (encodeOp op).length
      · rw [List.take_append_of_le_length (Nat.le_of_lt hlt),
          decodeOp_prefix op n hlt, Option.bind_none]
      · have hge : (encodeOp op).length ≤ n := by omega
        rw [List.take_append, List.take_of_length_le hge, decodeOp_write, Option.bind_some]
        have hn2 : n - (encodeOp op).length < (encodeOps ops).length := by
          omega
        rw [decodeOps_prefix ops _ hn2, Option.bind_none]

/-! ## Records -/

structure Record where
  lsn : UInt64
  ops : List Op
  hops : ops.length < UInt32.size

theorem Record.ext {a b : Record} (hl : a.lsn = b.lsn) (ho : a.ops = b.ops) : a = b := by
  cases a
  cases b
  cases hl
  cases ho
  rfl

instance : BEq Record where
  beq a b := a.lsn == b.lsn && a.ops == b.ops

def Record.ofBatch (lsn : UInt64) (b : Batch) : Record where
  lsn := lsn
  ops := b.ops
  hops := b.hlen

/-- `REC1` -/
def recMagic : Bytes := [82, 69, 67, 49]

def bodyBytes (r : Record) : Bytes :=
  recMagic ++
    (writeU64 r.lsn ++
      (writeU32 (UInt32.ofNat r.ops.length) ++ encodeOps r.ops))

def encodeRecord (r : Record) : Bytes :=
  bodyBytes r ++ writeU32 (crc32 (bodyBytes r))

theorem bodyBytes_pos (r : Record) : 0 < (bodyBytes r).length := by
  simp [bodyBytes, recMagic, List.length_append]

theorem encodeRecord_pos (r : Record) : 0 < (encodeRecord r).length := by
  have h := bodyBytes_pos r
  simp [encodeRecord, List.length_append]
  omega

def readToken (tok : Bytes) (bs : Bytes) : Option (Unit × Bytes) :=
  Option.bind (readExact tok.length bs) fun p =>
    if p.1 == tok then some ((), p.2) else none

theorem readToken_write (tok rest : Bytes) :
    readToken tok (tok ++ rest) = some ((), rest) := by
  rw [readToken, readExact_write, Option.bind_some, beq_self_eq_true, ite_eq_left rfl]

theorem readToken_prefix (tok : Bytes) (n : Nat) (hn : n < tok.length) :
    readToken tok (tok.take n) = none := by
  have hlen : (tok.take n).length = n := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
  rw [readToken, readExact_none (by simpa [hlen] using hn), Option.bind_none]

/-- Run `d1`, then `d2` on the value and the unread suffix. -/
def seq {α β : Type} (d1 : Bytes → Option (α × Bytes))
    (d2 : α → Bytes → Option (β × Bytes)) (bs : Bytes) : Option (β × Bytes) :=
  Option.bind (d1 bs) fun p => d2 p.1 p.2

theorem seq_write {α β : Type} (d1 : Bytes → Option (α × Bytes))
    (d2 : α → Bytes → Option (β × Bytes)) (e1 e2 : Bytes) (a : α) (b : β)
    (h1 : ∀ rest, d1 (e1 ++ rest) = some (a, rest))
    (h2 : ∀ rest, d2 a (e2 ++ rest) = some (b, rest)) (rest : Bytes) :
    seq d1 d2 (e1 ++ (e2 ++ rest)) = some (b, rest) := by
  rw [seq, h1, Option.bind_some, h2]

theorem seq_prefix {α β : Type} (d1 : Bytes → Option (α × Bytes))
    (d2 : α → Bytes → Option (β × Bytes)) (e1 e2 : Bytes) (a : α)
    (h1 : ∀ rest, d1 (e1 ++ rest) = some (a, rest))
    (h1p : ∀ n, n < e1.length → d1 (e1.take n) = none)
    (h2p : ∀ n, n < e2.length → d2 a (e2.take n) = none)
    (n : Nat) (hn : n < e1.length + e2.length) :
    seq d1 d2 ((e1 ++ e2).take n) = none := by
  by_cases hlt : n < e1.length
  · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), seq, h1p _ hlt, Option.bind_none]
  · have hge : e1.length ≤ n := by omega
    rw [List.take_append, List.take_of_length_le hge, seq, h1, Option.bind_some]
    exact h2p _ (by omega)

def decodeChecked (lsn : UInt64) (count : UInt32) (bs : Bytes) : Option (Record × Bytes) :=
  Option.bind (decodeOps count.toNat bs) fun p =>
    if h : p.1.length < UInt32.size ∧ count = UInt32.ofNat p.1.length then
      some (⟨lsn, p.1, h.1⟩, p.2)
    else
      none

theorem decodeChecked_write (r : Record) (rest : Bytes) :
    decodeChecked r.lsn (UInt32.ofNat r.ops.length) (encodeOps r.ops ++ rest) = some (r, rest) := by
  have hn : (UInt32.ofNat r.ops.length).toNat = r.ops.length :=
    UInt32.toNat_ofNat_of_lt r.hops
  rw [decodeChecked, hn, decodeOps_write, Option.bind_some, dite_eq_left ⟨r.hops, rfl⟩]

theorem decodeChecked_prefix (lsn : UInt64) (count : UInt32) (ops : List Op)
    (hc : count.toNat = ops.length) (n : Nat) (hn : n < (encodeOps ops).length) :
    decodeChecked lsn count ((encodeOps ops).take n) = none := by
  rw [decodeChecked, hc, decodeOps_prefix ops n hn, Option.bind_none]

def decodeBody (bs : Bytes) : Option (Record × Bytes) :=
  seq (readToken recMagic) (fun _ =>
    seq readU64 (fun lsn =>
      seq readU32 (fun count =>
        decodeChecked lsn count))) bs

theorem decodeBody_write (r : Record) (rest : Bytes) :
    decodeBody (bodyBytes r ++ rest) = some (r, rest) := by
  unfold decodeBody bodyBytes
  rw [List.append_assoc]
  refine seq_write (readToken recMagic)
      (fun _ => seq readU64 (fun lsn => seq readU32 (fun count => decodeChecked lsn count)))
      recMagic
      (writeU64 r.lsn ++ (writeU32 (UInt32.ofNat r.ops.length) ++ encodeOps r.ops))
      () r ?tok ?tail rest
  · intro rest'
    exact readToken_write recMagic rest'
  · intro rest'
    rw [List.append_assoc]
    refine seq_write readU64
        (fun lsn => seq readU32 (fun count => decodeChecked lsn count))
        (writeU64 r.lsn)
        (writeU32 (UInt32.ofNat r.ops.length) ++ encodeOps r.ops)
        r.lsn r ?lsn ?after rest'
    · intro rest''
      exact readU64_write r.lsn rest''
    · intro rest''
      rw [List.append_assoc]
      refine seq_write readU32 (fun count => decodeChecked r.lsn count)
          (writeU32 (UInt32.ofNat r.ops.length)) (encodeOps r.ops)
          (UInt32.ofNat r.ops.length) r ?cnt ?ops rest''
      · intro rest'''
        exact readU32_write _ rest'''
      · intro rest'''
        exact decodeChecked_write r rest'''

theorem decodeBody_prefix (r : Record) (n : Nat) (hn : n < (bodyBytes r).length) :
    decodeBody ((bodyBytes r).take n) = none := by
  unfold decodeBody
  simp only [bodyBytes] at hn ⊢
  refine seq_prefix (readToken recMagic)
      (fun _ =>
        seq readU64 (fun lsn =>
          seq readU32 (fun count => decodeChecked lsn count)))
      recMagic
      (writeU64 r.lsn ++ (writeU32 (UInt32.ofNat r.ops.length) ++ encodeOps r.ops))
      ()
      (fun rest => readToken_write recMagic rest)
      (fun k hk => readToken_prefix recMagic k hk)
      ?_ n ?_
  · intro m hm
    have hm' : m < (writeU64 r.lsn).length +
        (writeU32 (UInt32.ofNat r.ops.length) ++ encodeOps r.ops).length := by
      simpa [List.length_append] using hm
    refine seq_prefix readU64
        (fun lsn => seq readU32 (fun count => decodeChecked lsn count))
        (writeU64 r.lsn)
        (writeU32 (UInt32.ofNat r.ops.length) ++ encodeOps r.ops)
        r.lsn
        (fun rest => readU64_write r.lsn rest)
        (fun k hk => readU64_prefix r.lsn k hk)
        ?_ m hm'
    intro m2 hm2
    have hm2' : m2 < (writeU32 (UInt32.ofNat r.ops.length)).length + (encodeOps r.ops).length := by
      simpa [List.length_append] using hm2
    refine seq_prefix readU32
        (fun count => decodeChecked r.lsn count)
        (writeU32 (UInt32.ofNat r.ops.length))
        (encodeOps r.ops)
        (UInt32.ofNat r.ops.length)
        (fun rest => readU32_write _ rest)
        (fun k hk => readU32_prefix _ k hk)
        ?_ m2 hm2'
    intro m3 hm3
    exact decodeChecked_prefix r.lsn (UInt32.ofNat r.ops.length) r.ops
      (UInt32.toNat_ofNat_of_lt r.hops) m3 hm3
  · simpa [List.length_append] using hn

def decodeRecord (bs : Bytes) : Option (Record × Bytes) :=
  Option.bind (decodeBody bs) fun p =>
    Option.bind (readU32 p.2) fun q =>
      if q.1 == crc32 (bodyBytes p.1) then
        some (p.1, q.2)
      else
        none

theorem decodeRecord_nil : decodeRecord [] = none := by
  simp [decodeRecord, decodeBody, seq, readToken, readExact, recMagic, Option.bind_none]

theorem decodeRecord_write (r : Record) (rest : Bytes) :
    decodeRecord (encodeRecord r ++ rest) = some (r, rest) := by
  rw [decodeRecord, encodeRecord, List.append_assoc, decodeBody_write, Option.bind_some,
    readU32_write, Option.bind_some, beq_self_eq_true, ite_eq_left rfl]

theorem encodeRecord_length (r : Record) :
    (encodeRecord r).length = (bodyBytes r).length + 4 := by
  simp [encodeRecord, writeU32_length, List.length_append]

theorem decodeRecord_prefix (r : Record) (n : Nat) (hn : n < (encodeRecord r).length) :
    decodeRecord ((encodeRecord r).take n) = none := by
  rw [encodeRecord] at hn ⊢
  by_cases hlt : n < (bodyBytes r).length
  · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), decodeRecord,
      decodeBody_prefix r n hlt, Option.bind_none]
  · have hge : (bodyBytes r).length ≤ n := by omega
    have hcrc : n - (bodyBytes r).length < 4 := by
      simp [writeU32_length, List.length_append] at hn
      omega
    rw [List.take_append, List.take_of_length_le hge, decodeRecord, decodeBody_write,
      Option.bind_some, readU32_prefix _ _ hcrc, Option.bind_none]

/-! ## Logs and files -/

def encodeLog (rs : List Record) : Bytes :=
  rs.flatMap encodeRecord

/-- `CAIR` + version 1. -/
def fileMagic : Bytes := [67, 65, 73, 82]

def fileVersion : UInt32 := 1

def fileHeader : Bytes := fileMagic ++ writeU32 fileVersion

theorem fileHeader_length : fileHeader.length = 8 := by
  simp [fileHeader, fileMagic, writeU32_length]

def encodeFile (rs : List Record) : Bytes :=
  fileHeader ++ encodeLog rs

def decodeGo : Nat → Bytes → List Record
  | 0, _ => []
  | fuel + 1, bs =>
      (decodeRecord bs).elim [] fun p =>
        if p.2.length < bs.length then
          p.1 :: decodeGo fuel p.2
        else
          []

def decodeLog (bs : Bytes) : List Record :=
  decodeGo bs.length bs

theorem decodeGo_encode : ∀ (fuel : Nat) (rs : List Record),
    rs.length ≤ fuel → decodeGo fuel (encodeLog rs) = rs
  | 0, [], _ => by rw [decodeGo]
  | 0, _ :: _, h => by simp at h
  | fuel + 1, [], _ => by
      rw [decodeGo, encodeLog, List.flatMap_nil, decodeRecord_nil, Option.elim_none]
  | fuel + 1, r :: rs, h => by
      have hr : rs.length ≤ fuel := by simp at h; omega
      have hdec := decodeRecord_write r (encodeLog rs)
      have hlt : (encodeLog rs).length < (encodeRecord r ++ encodeLog rs).length := by
        have hp := encodeRecord_pos r
        simp [List.length_append]
        omega
      simp only [encodeLog] at hdec hlt
      simp only [encodeLog, List.flatMap_cons]
      rw [decodeGo, hdec, Option.elim_some, ite_eq_left hlt]
      exact congrArg (fun t => r :: t) (decodeGo_encode fuel rs hr)

theorem decodeLog_encode (rs : List Record) : decodeLog (encodeLog rs) = rs := by
  have hlen : rs.length ≤ (encodeLog rs).length := by
    induction rs with
    | nil => simp [encodeLog]
    | cons r rs ih =>
        have hp := encodeRecord_pos r
        simp [encodeLog, List.flatMap_cons, List.length_append] at ih ⊢
        omega
  simpa [decodeLog] using decodeGo_encode (encodeLog rs).length rs hlen

theorem decodeGo_prefix : ∀ (fuel : Nat) (rs : List Record) (bs : Bytes),
    bs.length ≤ fuel → (∃ n, bs = (encodeLog rs).take n) →
      ∃ k, k ≤ rs.length ∧ decodeGo fuel bs = rs.take k
  | 0, rs, bs, hfuel, _ => by
      have hz : bs.length = 0 := Nat.eq_zero_of_le_zero hfuel
      have hnil : bs = [] := List.eq_nil_of_length_eq_zero hz
      subst hnil
      exact ⟨0, Nat.zero_le _, by rw [decodeGo, List.take_zero]⟩
  | fuel + 1, [], bs, _, hpre => by
      obtain ⟨n, rfl⟩ := hpre
      rw [encodeLog, List.flatMap_nil, List.take_nil, decodeGo, decodeRecord_nil, Option.elim_none]
      exact ⟨0, Nat.le_refl _, rfl⟩
  | fuel + 1, r :: rs, bs, hfuel, hpre => by
      obtain ⟨n, hn⟩ := hpre
      simp only [encodeLog, List.flatMap_cons] at hn hfuel
      subst hn
      by_cases hlt : n < (encodeRecord r).length
      · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), decodeGo,
          decodeRecord_prefix r n hlt, Option.elim_none]
        exact ⟨0, Nat.zero_le _, by simp [List.take_zero]⟩
      · have hge : (encodeRecord r).length ≤ n := by omega
        have hbs : (encodeRecord r ++ rs.flatMap encodeRecord).take n =
            encodeRecord r ++ (rs.flatMap encodeRecord).take (n - (encodeRecord r).length) := by
          rw [List.take_append, List.take_of_length_le hge]
        rw [hbs, decodeGo, decodeRecord_write, Option.elim_some]
        generalize hsuf :
          (rs.flatMap encodeRecord).take (n - (encodeRecord r).length) = suffix
        have hpos := encodeRecord_pos r
        have hlt2 : suffix.length < (encodeRecord r ++ suffix).length := by
          rw [← hsuf]
          simp [List.length_append]
          omega
        rw [ite_eq_left hlt2]
        have hfuel' : suffix.length ≤ fuel := by
          have hbsLen : (encodeRecord r ++ suffix).length ≤ fuel + 1 := by
            rw [hbs, hsuf] at hfuel
            exact hfuel
          simp [List.length_append] at hbsLen
          omega
        obtain ⟨k, hk, hkdec⟩ :=
          decodeGo_prefix fuel rs suffix hfuel'
            ⟨n - (encodeRecord r).length, by simpa [encodeLog] using hsuf.symm⟩
        refine ⟨k + 1, ?_, ?_⟩
        · simp [List.length_cons]
          omega
        simp [hkdec, List.take_succ_cons]

/--
Files shorter than the header decode as an empty log (a torn header is an empty
prefix). A longer file whose header is not `CAIR`/version 1 is rejected.
-/
def decodeFile (bs : Bytes) : Except String (List Record) :=
  if bs.length < fileHeader.length then
    .ok []
  else if bs.take fileHeader.length != fileHeader then
    .error "not a cairn file"
  else
    .ok (decodeLog (bs.drop fileHeader.length))

theorem decodeFile_encode (rs : List Record) : decodeFile (encodeFile rs) = .ok rs := by
  have hnot : ¬ (encodeFile rs).length < fileHeader.length := by
    simp [encodeFile, fileHeader_length, List.length_append]
  rw [decodeFile, ite_eq_right hnot]
  have heq : (encodeFile rs).take fileHeader.length = fileHeader := by
    simp [encodeFile, fileHeader_length]
  have hkeep : ((encodeFile rs).take fileHeader.length != fileHeader) = false := by
    simp [heq]
  rw [hkeep, ite_eq_right (by decide)]
  simp [encodeFile, fileHeader_length, decodeLog_encode]

theorem decodeFile_prefix (rs : List Record) (n : Nat) :
    ∃ k, decodeFile ((encodeFile rs).take n) = .ok (rs.take k) := by
  by_cases hlt : n < fileHeader.length
  · have hshort : ((encodeFile rs).take n).length < fileHeader.length := by
      have hfull : fileHeader.length ≤ (encodeFile rs).length := by
        simp [encodeFile, fileHeader_length, List.length_append]
      simp [List.length_take, Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt hlt) hfull)]
      exact hlt
    refine ⟨0, ?_⟩
    rw [decodeFile, ite_eq_left hshort, List.take_zero]
  · have hge : fileHeader.length ≤ n := by omega
    have htake : (encodeFile rs).take n =
        fileHeader ++ (encodeLog rs).take (n - fileHeader.length) := by
      simp only [encodeFile]
      rw [List.take_append, List.take_of_length_le hge]
    have hlen : fileHeader.length ≤ ((encodeFile rs).take n).length := by
      simp [htake, fileHeader_length, List.length_append]
    have hhead : ((encodeFile rs).take n).take fileHeader.length = fileHeader := by
      simp [htake, fileHeader_length]
    have hdrop : ((encodeFile rs).take n).drop fileHeader.length =
        (encodeLog rs).take (n - fileHeader.length) := by
      simp [htake, fileHeader_length]
    obtain ⟨k, hk, hdec⟩ := decodeGo_prefix
      ((encodeLog rs).take (n - fileHeader.length)).length rs
      ((encodeLog rs).take (n - fileHeader.length))
      (Nat.le_refl _) ⟨n - fileHeader.length, rfl⟩
    refine ⟨k, ?_⟩
    have hnot : ¬ ((encodeFile rs).take n).length < fileHeader.length := Nat.not_lt_of_ge hlen
    rw [decodeFile, ite_eq_right hnot]
    have hkeep : (((encodeFile rs).take n).take fileHeader.length != fileHeader) = false := by
      simp [hhead, bne]
    rw [hkeep, ite_eq_right (by decide), hdrop]
    simp only [decodeLog]
    exact congrArg Except.ok hdec

instance : LawfulBEq FitBytes where
  rfl {a} := by simpa [BEq.beq] using (@BEq.rfl (List UInt8) _ _ a.bytes)
  eq_of_beq {a b} h := by
    have hb : (a.bytes == b.bytes) = true := by simpa [BEq.beq] using h
    exact FitBytes.eq_of_bytes (eq_of_beq hb)

instance : LawfulBEq Op where
  rfl {op} := by
    cases op with
    | put k v =>
        have hk : List.beq k.bytes k.bytes = true := by
          simpa [BEq.beq] using (@BEq.rfl (List UInt8) _ _ k.bytes)
        have hv : List.beq v.bytes v.bytes = true := by
          simpa [BEq.beq] using (@BEq.rfl (List UInt8) _ _ v.bytes)
        simp only [BEq.beq, hk, hv]
        decide
    | del k =>
        have hk : List.beq k.bytes k.bytes = true := by
          simpa [BEq.beq] using (@BEq.rfl (List UInt8) _ _ k.bytes)
        simp only [BEq.beq, hk]
  eq_of_beq {a b} h := by
    cases a with
    | put k v =>
        cases b with
        | put k' v' =>
            have hkv : (List.beq k.bytes k'.bytes && List.beq v.bytes v'.bytes) = true := by
              simpa [BEq.beq] using h
            have hk : List.beq k.bytes k'.bytes = true := by
              cases hkk : List.beq k.bytes k'.bytes <;> simp_all
            have hv : List.beq v.bytes v'.bytes = true := by
              simp [hk] at hkv
              exact hkv
            have hk' : k = k' := eq_of_beq (by simpa [BEq.beq] using hk)
            have hv' : v = v' := eq_of_beq (by simpa [BEq.beq] using hv)
            cases hk'
            cases hv'
            rfl
        | del _ => simp [BEq.beq] at h
    | del k =>
        cases b with
        | put _ _ => simp [BEq.beq] at h
        | del k' =>
            have hk : List.beq k.bytes k'.bytes = true := by simpa [BEq.beq] using h
            have hk' : k = k' := eq_of_beq (by simpa [BEq.beq] using hk)
            cases hk'
            rfl

instance : LawfulBEq Record where
  rfl {a} := by
    show ((a.lsn == a.lsn) && (a.ops == a.ops)) = true
    rw [show (a.lsn == a.lsn) = true from BEq.rfl]
    rw [show (a.ops == a.ops) = true from BEq.rfl]
    decide
  eq_of_beq {a b} h := by
    have h' : (a.lsn == b.lsn && a.ops == b.ops) = true := by simpa only [BEq.beq] using h
    have hl : (a.lsn == b.lsn) = true := by
      cases hlsn : (a.lsn == b.lsn) <;> simp_all
    have ho : (a.ops == b.ops) = true := by
      simp only [hl, Bool.true_and] at h'
      exact h'
    exact Record.ext (eq_of_beq hl) (eq_of_beq ho)

end Cairn
