/-
On-disk frames.

A file is a header frame (`CAIR`, version 2) followed by segment frames
(`SEG1`). Each frame is padded to `blockSize` (4096) bytes. The header
checksum covers magic and length. The body checksum covers the payload.
Padding is inside the frame, after the body checksum, so a later append
never rewrites a block that a completed `sync` already published: the
caller only appends whole frames and syncs after the append.

`scan` distinguishes

* `clean` — every byte belongs to a valid frame
* `torn` — a proper tail is missing; the frames before it are kept
* `corrupt` — a complete frame fails, and a later frame is still valid
* `reject` — the bytes are not a cairn file (do not truncate them)

A byte prefix of a well-formed file is `clean` or `torn`, never `corrupt`
or `reject`, and its records are a prefix of the original list.
-/

import Cairn.Record
import Cairn.Sum32

namespace Cairn

def blockSize : Nat := 4096

theorem blockSize_pos : 0 < blockSize := by decide

def alignUp (n : Nat) : Nat :=
  let r := n % blockSize
  if r = 0 then n else n + (blockSize - r)

theorem alignUp_ge (n : Nat) : n ≤ alignUp n := by
  unfold alignUp
  by_cases h : n % blockSize = 0
  · simp [h]
  · simp [h]

theorem alignUp_mod (n : Nat) : alignUp n % blockSize = 0 := by
  unfold alignUp
  by_cases h : n % blockSize = 0
  · simp [h]
  · simp [h]
    have hr : n % blockSize < blockSize := Nat.mod_lt n blockSize_pos
    have hdiv := Nat.div_add_mod n blockSize
    have hsum : n % blockSize + (blockSize - n % blockSize) = blockSize := by
      omega
    have hn := congrArg (fun x => x + (blockSize - n % blockSize)) hdiv.symm
    have hn2 : n + (blockSize - n % blockSize) = blockSize * (n / blockSize) + blockSize := by
      rw [hn, Nat.add_assoc, hsum]
    have hn3 : blockSize * (n / blockSize) + blockSize = (n / blockSize + 1) * blockSize := by
      have hcomm := congrArg (fun x => x + blockSize) (Nat.mul_comm blockSize (n / blockSize))
      rw [hcomm]
      have hstep := congrArg (fun x => n / blockSize * blockSize + x) (Nat.one_mul blockSize).symm
      rw [hstep, ← Nat.add_mul]
    rw [hn2, hn3, Nat.mul_comm]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right _ _)

def frameTotal (payloadLen : Nat) : Nat :=
  alignUp (16 + payloadLen)

/-- `CAIR` -/
def fileMagic : Bytes := [67, 65, 73, 82]

/-- `SEG1` -/
def segMagic : Bytes := [83, 69, 71, 49]

def fileVersion : UInt32 := 2

def versionPayload : Bytes := writeU32 fileVersion

theorem fileMagic_length : fileMagic.length = 4 := by simp [fileMagic]

theorem segMagic_length : segMagic.length = 4 := by simp [segMagic]

theorem versionPayload_length : versionPayload.length = 4 := by
  simp [versionPayload, writeU32_length]

theorem versionPayload_fit : versionPayload.length < UInt32.size := by
  simp [versionPayload_length, UInt32.size]

def encodeFrame (magic payload : Bytes) : Bytes :=
  let lenWord := writeU32 (UInt32.ofNat payload.length)
  let head := magic ++ lenWord
  let body := head ++ writeU32 (sum32 head) ++ payload ++ writeU32 (sum32 payload)
  body ++ List.replicate (frameTotal payload.length - body.length) 0

def bytesZero (bs : Bytes) : Bool :=
  bs.all (fun b => b == 0)

def encodeHeader : Bytes :=
  encodeFrame fileMagic versionPayload

theorem encodeFrame_body_length (magic payload : Bytes) (hm : magic.length = 4) :
    (magic ++ writeU32 (UInt32.ofNat payload.length) ++
        writeU32 (sum32 (magic ++ writeU32 (UInt32.ofNat payload.length))) ++
          payload ++ writeU32 (sum32 payload)).length =
      16 + payload.length := by
  simp [List.length_append, writeU32_length, hm]
  omega

theorem encodeFrame_length (magic payload : Bytes) (hm : magic.length = 4) :
    (encodeFrame magic payload).length = frameTotal payload.length := by
  unfold encodeFrame
  simp only [List.length_append, List.length_replicate, writeU32_length, hm]
  have hle : 16 + payload.length ≤ frameTotal payload.length := by
    unfold frameTotal
    exact alignUp_ge _
  omega

theorem encodeHeader_length : encodeHeader.length = blockSize := by
  rw [encodeHeader, encodeFrame_length _ _ fileMagic_length]
  simp [frameTotal, versionPayload_length, alignUp, blockSize]

inductive Parsed where
  | ok (payload rest : Bytes)
  | need
  | badHeader
  | badBody (rest : Bytes)

def parseFrame (magic bs : Bytes) : Parsed :=
  match readExact 4 bs with
  | none => .need
  | some (m, bs1) =>
      if m != magic then
        .badHeader
      else
        match readU32 bs1 with
        | none => .need
        | some (len, bs2) =>
            match readU32 bs2 with
            | none => .need
            | some (hcrc, bs3) =>
                let head := m ++ writeU32 len
                if hcrc != sum32 head then
                  .badHeader
                else
                  match readExact len.toNat bs3 with
                  | none => .need
                  | some (payload, bs4) =>
                      match readU32 bs4 with
                      | none => .need
                      | some (bcrc, bs5) =>
                          if bcrc != sum32 payload then
                            .badBody (bs.drop (frameTotal len.toNat))
                          else
                            let padn := frameTotal len.toNat - (16 + len.toNat)
                            match readExact padn bs5 with
                            | none => .need
                            | some (pad, rest) =>
                                -- Padding is outside the body checksum. It has to be
                                -- zeros, or a torn sector full of zeros would be invisible
                                -- and a flipped pad bit would be silent.
                                if bytesZero pad then
                                  .ok payload rest
                                else
                                  .badBody rest

def RecordsFit (rs : List Record) : Prop :=
  ∀ r, r ∈ rs → (encodeRecord r).length < UInt32.size

def GroupsFit (gs : List (List Record)) : Prop :=
  ∀ g, g ∈ gs → (encodeLog g).length < UInt32.size

theorem recordsFit_cons {r : Record} {rs : List Record}
    (h : RecordsFit (r :: rs)) : RecordsFit rs := by
  intro x hx
  exact h x (List.mem_cons_of_mem _ hx)

theorem recordsFit_head {r : Record} {rs : List Record}
    (h : RecordsFit (r :: rs)) : (encodeRecord r).length < UInt32.size :=
  h r List.mem_cons_self

def encodeFrames : List Record → Bytes
  | [] => []
  | r :: rs => encodeFrame segMagic (encodeRecord r) ++ encodeFrames rs

def encodeFile (rs : List Record) : Bytes :=
  encodeHeader ++ encodeFrames rs

/-- One segment frame per group. A group is the records written by one sync. -/
def encodeSegList : List (List Record) → Bytes
  | [] => []
  | g :: gs => encodeFrame segMagic (encodeLog g) ++ encodeSegList gs

def encodeGroups (gs : List (List Record)) : Bytes :=
  encodeHeader ++ encodeSegList gs

def joinGroups : List (List Record) → List Record
  | [] => []
  | g :: gs => g ++ joinGroups gs

theorem encodeGroups_nil : encodeGroups [] = encodeHeader := by
  simp [encodeGroups, encodeSegList]

def takeFrames (fuel : Nat) (magic : Bytes) (acc : List Record) (bs : Bytes) :
    List Record × Bytes :=
  match fuel with
  | 0 => (acc, bs)
  | fuel + 1 =>
      match parseFrame magic bs with
      | .ok payload rest =>
          if rest.length < bs.length then
            if magic == fileMagic then
              if payload == versionPayload then
                takeFrames fuel segMagic acc rest
              else
                (acc, bs)
            else
              let rs := decodeLog payload
              if encodeLog rs == payload then
                takeFrames fuel segMagic (acc ++ rs) rest
              else
                (acc, bs)
          else
            (acc, bs)
      | _ => (acc, bs)

def findFrame (fuel : Nat) (bs : Bytes) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      match parseFrame segMagic bs with
      | .ok _ _ => true
      | _ =>
          if bs.length ≤ blockSize then
            false
          else
            findFrame fuel (bs.drop blockSize)

/-- A later valid segment means the failure is not the torn tail. -/
def laterFrame (bs : Bytes) : Bool :=
  if bs.length ≤ blockSize then
    false
  else
    findFrame bs.length (bs.drop blockSize)

inductive ScanKind where
  | clean
  | torn
  | corrupt
  | reject
  deriving BEq, Repr

structure Scan where
  records : List Record
  consumed : Nat
  kind : ScanKind

/-- Classify `rest` after `takeFrames` has kept `recs`. -/
def scanFrom (bs : Bytes) (recs : List Record) (rest : Bytes) : Scan :=
  let consumed := bs.length - rest.length
  if rest.isEmpty then
    {records := recs, consumed := consumed, kind := .clean}
  else
    match parseFrame (if consumed = 0 then fileMagic else segMagic) rest with
    | .need =>
        -- `consumed = 0` is only the header. A header prefix is a torn
        -- empty file; anything else that fails before the first frame is
        -- not ours.
        if consumed = 0 then
          if bs.isPrefixOf encodeHeader then
            {records := recs, consumed := consumed, kind := .torn}
          else
            {records := [], consumed := 0, kind := .reject}
        else
          {records := recs, consumed := consumed, kind := .torn}
    | .badHeader =>
        if consumed = 0 then
          {records := [], consumed := 0, kind := .reject}
        else if laterFrame rest then
          {records := recs, consumed := consumed, kind := .corrupt}
        else
          {records := recs, consumed := consumed, kind := .torn}
    | .badBody restAfter =>
        if parseFrame segMagic restAfter matches .ok _ _ || laterFrame rest then
          {records := recs, consumed := consumed, kind := .corrupt}
        else
          {records := recs, consumed := consumed, kind := .torn}
    | .ok _ _ =>
        if consumed = 0 then
          {records := [], consumed := 0, kind := .reject}
        else
          {records := recs, consumed := consumed, kind := .corrupt}

def scan (bs : Bytes) : Scan :=
  if bs.isEmpty then
    {records := [], consumed := 0, kind := .torn}
  else
    let got := takeFrames (bs.length + 1) fileMagic [] bs
    scanFrom bs got.1 got.2

def decodeFile (bs : Bytes) : Except String (List Record) :=
  match (scan bs).kind with
  | .reject => .error "not a cairn file"
  | .corrupt => .error "corrupt log"
  | .clean | .torn => .ok (scan bs).records

def repairedBytes (bs : Bytes) : Bytes :=
  let s := scan bs
  match s.kind with
  | .reject => encodeHeader
  | .clean => bs.take s.consumed
  | .torn | .corrupt =>
      if s.consumed = 0 then encodeHeader else bs.take s.consumed

end Cairn
