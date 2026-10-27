import Cairn.FileFmt

namespace Cairn

theorem bytesZero_replicate (n : Nat) : bytesZero (List.replicate n (0 : UInt8)) = true := by
  simp [bytesZero, List.all_replicate]

theorem readExact_len (data rest : Bytes) (n : Nat) (hn : data.length = n) :
    readExact n (data ++ rest) = some (data, rest) := by
  simpa [hn] using readExact_write data rest

theorem readExact_four (data rest : Bytes) (hm : data.length = 4) :
    readExact 4 (data ++ rest) = some (data, rest) := by
  simpa [hm] using readExact_write data rest

theorem parseFrame_encode (magic payload rest : Bytes) (hm : magic.length = 4)
    (hp : payload.length < UInt32.size) :
    parseFrame magic (encodeFrame magic payload ++ rest) = .ok payload rest := by
  have hlen : (UInt32.ofNat payload.length).toNat = payload.length :=
    UInt32.toNat_ofNat_of_lt hp
  simp only [encodeFrame, parseFrame, List.append_assoc]
  rw [show 4 = magic.length from hm.symm, readExact_write]
  simp [bne, hlen, readU32_write]
  rw [readExact_write]
  simp
  rw [readU32_write]
  simp
  have hcount :
      frameTotal payload.length -
          (magic.length +
            ((writeU32 (UInt32.ofNat payload.length)).length +
              ((writeU32 (sum32 (magic ++ writeU32 (UInt32.ofNat payload.length)))).length +
                (payload.length + (writeU32 (sum32 payload)).length)))) =
        frameTotal payload.length - (16 + payload.length) := by
    simp [writeU32_length, hm]
    omega
  rw [hcount]
  rw [readExact_len (List.replicate (frameTotal payload.length - (16 + payload.length)) 0) rest _
    List.length_replicate]
  simp [bytesZero_replicate]

theorem encodeFrame_parts (magic payload : Bytes) (hm : magic.length = 4) :
    encodeFrame magic payload =
      magic ++
        (writeU32 (UInt32.ofNat payload.length) ++
          (writeU32 (sum32 (magic ++ writeU32 (UInt32.ofNat payload.length))) ++
            (payload ++
              (writeU32 (sum32 payload) ++
                List.replicate (frameTotal payload.length - (16 + payload.length)) 0)))) := by
  simp only [encodeFrame, List.append_assoc, List.length_append, writeU32_length, hm]
  have hnum : 4 + (4 + (4 + (payload.length + 4))) = 16 + payload.length := by omega
  rw [hnum]

theorem parseFrame_prefix (magic payload : Bytes) (hm : magic.length = 4)
    (hp : payload.length < UInt32.size) (n : Nat)
    (hn : n < (encodeFrame magic payload).length) :
    parseFrame magic ((encodeFrame magic payload).take n) = .need := by
  have hlen : (UInt32.ofNat payload.length).toNat = payload.length :=
    UInt32.toNat_ofNat_of_lt hp
  rw [encodeFrame_parts magic payload hm]
  by_cases h4 : n < 4
  · rw [List.take_append_of_le_length (by simpa [hm] using Nat.le_of_lt h4), parseFrame,
      readExact_none (by
        simp [List.length_take, hm, Nat.min_eq_left (Nat.le_of_lt h4)]
        omega)]
  · have h4le : 4 ≤ n := by omega
    rw [List.take_append, List.take_of_length_le (by simpa [hm] using h4le)]
    simp only [parseFrame]
    rw [readExact_four magic _ hm]
    simp [bne, hm]
    by_cases h8 : n < 8
    · have hlt : n - 4 < 4 := by omega
      rw [List.take_append_of_le_length (by simp [writeU32_length]; omega),
        readU32_prefix _ _ hlt]
    · have h8le : 8 ≤ n := by omega
      rw [List.take_append, List.take_of_length_le (by simp [writeU32_length]; omega), readU32_write]
      simp [hlen, writeU32_length]
      have hsub8 : n - 4 - 4 = n - 8 := by omega
      rw [hsub8]
      by_cases h12 : n < 12
      · have hlt : n - 8 < 4 := by omega
        rw [List.take_append_of_le_length (by simp [writeU32_length]; omega),
          readU32_prefix _ _ hlt]
      · have h12le : 12 ≤ n := by omega
        rw [List.take_append, List.take_of_length_le (by simp [writeU32_length]; omega), readU32_write]
        simp [writeU32_length]
        have hsub12 : n - 8 - 4 = n - 12 := by omega
        rw [hsub12]
        by_cases hpay : n < 12 + payload.length
        · have hlt : n - 12 < payload.length := by omega
          rw [List.take_append_of_le_length (by omega : n - 12 ≤ payload.length),
            readExact_none (by
              simp [List.length_take, Nat.min_eq_left (by omega : n - 12 ≤ payload.length)]
              omega)]
        · have hpayle : 12 + payload.length ≤ n := by omega
          rw [List.take_append, List.take_of_length_le (by omega : payload.length ≤ n - 12),
            readExact_write]
          simp
          by_cases hcrc : n - 12 - payload.length < 4
          · rw [List.take_append_of_le_length (by
                simp [writeU32_length]
                omega),
              readU32_prefix _ _ hcrc]
          · have hcrcle : 4 ≤ n - 12 - payload.length := by omega
            rw [List.take_append, List.take_of_length_le (by
              simp [writeU32_length]
              exact hcrcle), readU32_write]
            simp [writeU32_length]
            have hpad :
                (List.replicate (min (n - 12 - payload.length - 4)
                  (frameTotal payload.length - (16 + payload.length))) (0 : UInt8)).length <
                  frameTotal payload.length - (16 + payload.length) := by
              simp [List.length_replicate]
              have hflen := encodeFrame_length magic payload hm
              rw [encodeFrame_parts magic payload hm] at hn
              simp [List.length_append, List.length_replicate, writeU32_length, hm] at hn
              omega
            rw [readExact_none hpad]

theorem parse_header (rest : Bytes) :
    parseFrame fileMagic (encodeHeader ++ rest) = .ok versionPayload rest := by
  simpa [encodeHeader] using
    parseFrame_encode fileMagic versionPayload rest fileMagic_length versionPayload_fit

theorem parse_segment (r : Record) (rest : Bytes) (h : (encodeRecord r).length < UInt32.size) :
    parseFrame segMagic (encodeFrame segMagic (encodeRecord r) ++ rest) =
      .ok (encodeRecord r) rest :=
  parseFrame_encode segMagic (encodeRecord r) rest segMagic_length h

theorem encodeHeader_pos : 0 < encodeHeader.length := by
  rw [encodeHeader_length]
  decide

theorem encodeFrame_pos (magic payload : Bytes) (hm : magic.length = 4) :
    0 < (encodeFrame magic payload).length := by
  rw [encodeFrame_length magic payload hm]
  have h := alignUp_ge (16 + payload.length)
  unfold frameTotal
  omega

theorem segment_canon (r : Record) : encodeLog (decodeLog (encodeRecord r)) = encodeRecord r := by
  have h := decodeLog_encode [r]
  simp [encodeLog, List.flatMap_cons, List.flatMap_nil] at h
  simpa [encodeLog, List.flatMap_cons, List.flatMap_nil] using congrArg encodeLog h

def fitSegs : List (List Record) → Nat → Nat
  | [], _ => 0
  | g :: gs, n =>
      let fl := (encodeFrame segMagic (encodeLog g)).length
      if n < fl then 0 else fitSegs gs (n - fl) + 1

def dropSegs : List (List Record) → Nat → Bytes
  | [], _ => []
  | g :: gs, n =>
      let frame := encodeFrame segMagic (encodeLog g)
      if n < frame.length then (frame ++ encodeSegList gs).take n
      else dropSegs gs (n - frame.length)

theorem groupsFit_tail {g : List Record} {gs : List (List Record)}
    (h : GroupsFit (g :: gs)) : GroupsFit gs := by
  intro x hx
  exact h x (List.mem_cons_of_mem _ hx)

theorem groupsFit_head {g : List Record} {gs : List (List Record)}
    (h : GroupsFit (g :: gs)) : (encodeLog g).length < UInt32.size :=
  h g List.mem_cons_self

theorem isEmpty_eq_false_of_pos {bs : Bytes} (h : 0 < bs.length) : bs.isEmpty = false := by
  cases hem : bs.isEmpty with
  | false => rfl
  | true =>
      have hz := (List.isEmpty_iff_length_eq_zero).mp hem
      exact False.elim ((Nat.ne_of_gt h) hz)

theorem takeFrames_need (fuel : Nat) (magic : Bytes) (acc : List Record) (bs : Bytes)
    (hp : parseFrame magic bs = .need) (hf : 0 < fuel) :
    takeFrames fuel magic acc bs = (acc, bs) := by
  cases fuel with
  | zero => omega
  | succ _ =>
      simp [takeFrames, hp]

theorem takeFrames_header (fuel : Nat) (rest : Bytes) (acc : List Record) :
    takeFrames (fuel + 1) fileMagic acc (encodeHeader ++ rest) =
      takeFrames fuel segMagic acc rest := by
  have hlt : rest.length < (encodeHeader ++ rest).length := by
    rw [List.length_append]
    exact Nat.lt_add_of_pos_left encodeHeader_pos
  simp only [takeFrames, parse_header]
  rw [ite_eq_left hlt]
  simp

theorem takeFrames_group (fuel : Nat) (g : List Record) (rest : Bytes) (acc : List Record)
    (hfit : (encodeLog g).length < UInt32.size) :
    takeFrames (fuel + 1) segMagic acc (encodeFrame segMagic (encodeLog g) ++ rest) =
      takeFrames fuel segMagic (acc ++ g) rest := by
  have hlt : rest.length < (encodeFrame segMagic (encodeLog g) ++ rest).length := by
    rw [List.length_append]
    exact Nat.lt_add_of_pos_left (encodeFrame_pos segMagic (encodeLog g) segMagic_length)
  simp only [takeFrames, parseFrame_encode segMagic (encodeLog g) rest segMagic_length hfit]
  rw [ite_eq_left hlt]
  have hmag : (segMagic == fileMagic) = false := by decide
  simp only [hmag, decodeLog_encode, beq_self_eq_true, Bool.false_eq_true, ite_false, ite_true]

theorem dropSegs_le (gs : List (List Record)) (n : Nat) :
    (dropSegs gs n).length ≤ ((encodeSegList gs).take n).length := by
  induction gs generalizing n with
  | nil => simp [dropSegs, encodeSegList]
  | cons g gs ih =>
      by_cases hlt : n < (encodeFrame segMagic (encodeLog g)).length
      · simp [dropSegs, encodeSegList, hlt]
      · have hge : (encodeFrame segMagic (encodeLog g)).length ≤ n := by omega
        simp only [dropSegs, encodeSegList, hlt]
        rw [List.take_append, List.take_of_length_le hge, List.length_append]
        exact Nat.le_trans (ih _) (Nat.le_add_left _ _)

theorem drop_need (gs : List (List Record)) (n : Nat) (h : GroupsFit gs) :
    dropSegs gs n = [] ∨ parseFrame segMagic (dropSegs gs n) = .need := by
  induction gs generalizing n with
  | nil => simp [dropSegs]
  | cons g gs ih =>
      by_cases hlt : n < (encodeFrame segMagic (encodeLog g)).length
      · right
        simp [dropSegs, hlt]
        rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
        exact parseFrame_prefix segMagic (encodeLog g) segMagic_length (groupsFit_head h) n hlt
      · simp [dropSegs, hlt]
        exact ih (n - (encodeFrame segMagic (encodeLog g)).length) (groupsFit_tail h)

theorem takeFrames_segs (fuel : Nat) (gs : List (List Record)) (n : Nat) (acc : List Record)
    (hfit : GroupsFit gs) (hf : ((encodeSegList gs).take n).length + 1 ≤ fuel) :
    takeFrames fuel segMagic acc ((encodeSegList gs).take n) =
      (acc ++ joinGroups (gs.take (fitSegs gs n)), dropSegs gs n) := by
  induction gs generalizing fuel n acc with
  | nil =>
      cases fuel with
      | zero => simp [encodeSegList, List.take_nil] at hf
      | succ _ =>
          simp [encodeSegList, fitSegs, dropSegs, joinGroups, List.take_nil, takeFrames, parseFrame,
            readExact_none (by decide : ([] : Bytes).length < 4)]
  | cons g gs ih =>
      cases fuel with
      | zero =>
          simp [encodeSegList, List.length_take] at hf
      | succ fuel =>
          by_cases hlt : n < (encodeFrame segMagic (encodeLog g)).length
          · have htake :=
              List.take_append_of_le_length (l₁ := encodeFrame segMagic (encodeLog g))
                (l₂ := encodeSegList gs) (Nat.le_of_lt hlt)
            simp only [encodeSegList]
            rw [htake, takeFrames_need (fuel + 1) segMagic acc ((encodeFrame segMagic (encodeLog g)).take n)
              (parseFrame_prefix segMagic (encodeLog g) segMagic_length (groupsFit_head hfit) n hlt)
              (Nat.succ_pos _)]
            simp only [fitSegs, dropSegs, hlt, ite_true, List.take_zero, joinGroups,
              List.append_nil, htake]
          · have hge : (encodeFrame segMagic (encodeLog g)).length ≤ n := by omega
            have htake :
                (encodeFrame segMagic (encodeLog g) ++ encodeSegList gs).take n =
                  encodeFrame segMagic (encodeLog g) ++
                    (encodeSegList gs).take (n - (encodeFrame segMagic (encodeLog g)).length) := by
              rw [List.take_append, List.take_of_length_le hge]
            simp only [encodeSegList]
            rw [htake, takeFrames_group fuel g ((encodeSegList gs).take
              (n - (encodeFrame segMagic (encodeLog g)).length)) acc (groupsFit_head hfit)]
            have hfuel :
                ((encodeSegList gs).take (n - (encodeFrame segMagic (encodeLog g)).length)).length + 1 ≤ fuel := by
              have hlen := hf
              simp only [encodeSegList, htake, List.length_append] at hlen
              have hpos := encodeFrame_pos segMagic (encodeLog g) segMagic_length
              omega
            have ih' := ih fuel (n - (encodeFrame segMagic (encodeLog g)).length) (acc ++ g)
              (groupsFit_tail hfit) hfuel
            simpa [fitSegs, dropSegs, hlt, ite_false, List.take_succ_cons, joinGroups, List.append_assoc]
              using ih'

theorem take_short_header (n fuel : Nat) (hn : n < encodeHeader.length) (hf : 0 < fuel) :
    takeFrames fuel fileMagic [] (encodeHeader.take n) = ([], encodeHeader.take n) := by
  cases fuel with
  | zero => omega
  | succ _ =>
      rw [encodeHeader, takeFrames,
        parseFrame_prefix fileMagic versionPayload fileMagic_length versionPayload_fit n
          (by simpa [encodeHeader] using hn)]

theorem header_is_prefix (n : Nat) : (encodeHeader.take n).isPrefixOf encodeHeader = true := by
  have h : encodeHeader.take n <+: encodeHeader := List.take_prefix n encodeHeader
  exact List.isPrefixOf_iff_prefix.mpr h

theorem take_groups_prefix (gs : List (List Record)) (n : Nat) (h : GroupsFit gs)
    (hge : encodeHeader.length ≤ n) :
    takeFrames (((encodeGroups gs).take n).length + 1) fileMagic [] ((encodeGroups gs).take n) =
      (joinGroups (gs.take (fitSegs gs (n - encodeHeader.length))),
        dropSegs gs (n - encodeHeader.length)) := by
  have hbs : (encodeGroups gs).take n =
      encodeHeader ++ (encodeSegList gs).take (n - encodeHeader.length) := by
    rw [encodeGroups, List.take_append, List.take_of_length_le hge]
  rw [hbs]
  have hlen : (encodeHeader ++ (encodeSegList gs).take (n - encodeHeader.length)).length =
      encodeHeader.length + ((encodeSegList gs).take (n - encodeHeader.length)).length := by
    simp [List.length_append]
  rw [hlen, takeFrames_header]
  have hfuel : ((encodeSegList gs).take (n - encodeHeader.length)).length + 1 ≤
      encodeHeader.length + ((encodeSegList gs).take (n - encodeHeader.length)).length := by
    have hpos := encodeHeader_pos
    omega
  simpa [List.append_nil] using
    takeFrames_segs (encodeHeader.length + ((encodeSegList gs).take (n - encodeHeader.length)).length)
      gs (n - encodeHeader.length) [] h hfuel

theorem scan_step (bs : Bytes) (recs : List Record) (rest : Bytes)
    (hne : bs.isEmpty = false)
    (h : takeFrames (bs.length + 1) fileMagic [] bs = (recs, rest)) :
    scan bs = scanFrom bs recs rest := by
  rw [scan, hne]
  simp only [Bool.false_eq_true, ite_false, h]

theorem decodeGroups_short (gs : List (List Record)) (n : Nat) (hn : n < encodeHeader.length) :
    decodeFile ((encodeGroups gs).take n) = .ok [] := by
  cases n with
  | zero =>
      simp [decodeFile, scan, List.take_zero]
  | succ n =>
      have hpre : (encodeGroups gs).take (n.succ) = encodeHeader.take (n.succ) := by
        rw [encodeGroups, List.take_append_of_le_length (Nat.le_of_lt hn)]
      have hlen : (encodeHeader.take (n.succ)).length = n.succ := by
        rw [List.length_take_of_le (Nat.le_of_lt hn)]
      have hempty := isEmpty_eq_false_of_pos (bs := encodeHeader.take (n.succ)) (by
        rw [hlen]; omega)
      have htf := take_short_header (n.succ) (n.succ + 1) hn (by omega)
      have hscan := scan_step (encodeHeader.take (n.succ)) [] (encodeHeader.take (n.succ)) hempty
        (by rw [hlen]; exact htf)
      rw [decodeFile, hpre, hscan, scanFrom, hlen, hempty]
      simp only [Nat.sub_self, Bool.false_eq_true, ite_false]
      have hneed := parseFrame_prefix fileMagic versionPayload fileMagic_length versionPayload_fit
        (n.succ) (by simpa [encodeHeader] using hn)
      simp only [ite_true, encodeHeader]
      rw [hneed]
      have hprex : ((encodeFrame fileMagic versionPayload).take (n.succ)).isPrefixOf
          (encodeFrame fileMagic versionPayload) = true := by
        simpa [encodeHeader] using header_is_prefix (n.succ)
      simp only [hprex, ite_true]

theorem decodeGroups_long (gs : List (List Record)) (n : Nat) (h : GroupsFit gs)
    (hge : encodeHeader.length ≤ n) :
    decodeFile ((encodeGroups gs).take n) =
      .ok (joinGroups (gs.take (fitSegs gs (n - encodeHeader.length)))) := by
  have htf := take_groups_prefix gs n h hge
  have hbs : (encodeGroups gs).take n =
      encodeHeader ++ (encodeSegList gs).take (n - encodeHeader.length) := by
    rw [encodeGroups, List.take_append, List.take_of_length_le hge]
  have hempty : ((encodeGroups gs).take n).isEmpty = false := by
    rw [hbs]
    exact isEmpty_eq_false_of_pos (by
      rw [List.length_append]
      have hpos := encodeHeader_pos
      omega)
  have hscan := scan_step ((encodeGroups gs).take n)
    (joinGroups (gs.take (fitSegs gs (n - encodeHeader.length))))
    (dropSegs gs (n - encodeHeader.length)) hempty htf
  rw [decodeFile, hscan, scanFrom]
  by_cases hem : dropSegs gs (n - encodeHeader.length) = []
  · simp only [hem, List.isEmpty_nil, ite_true]
  · have hneed := drop_need gs (n - encodeHeader.length) h
    cases hneed with
    | inl hnil => exact absurd hnil hem
    | inr hparse =>
        have hdroppos : 0 < (dropSegs gs (n - encodeHeader.length)).length := by
          have hne : (dropSegs gs (n - encodeHeader.length)).length ≠ 0 := by
            intro hz
            exact hem (List.eq_nil_of_length_eq_zero hz)
          omega
        have hemptyRest : (dropSegs gs (n - encodeHeader.length)).isEmpty = false :=
          isEmpty_eq_false_of_pos hdroppos
        have hne : ¬ ((encodeGroups gs).take n).length -
            (dropSegs gs (n - encodeHeader.length)).length = 0 := by
          have hle := dropSegs_le gs (n - encodeHeader.length)
          rw [hbs, List.length_append]
          have hpos := encodeHeader_pos
          omega
        simp only [hemptyRest, Bool.false_eq_true, ite_false]
        rw [ite_eq_right hne, hparse, ite_eq_right hne]

theorem decodeGroups_prefix (gs : List (List Record)) (n : Nat) (h : GroupsFit gs) :
    ∃ k, decodeFile ((encodeGroups gs).take n) = .ok (joinGroups (gs.take k)) := by
  by_cases hshort : n < encodeHeader.length
  · exact ⟨0, by simpa [List.take_zero, joinGroups] using decodeGroups_short gs n hshort⟩
  · have hge : encodeHeader.length ≤ n := by omega
    exact ⟨fitSegs gs (n - encodeHeader.length), decodeGroups_long gs n h hge⟩

theorem encodeLog_singleton (r : Record) : encodeLog [r] = encodeRecord r := by
  simp [encodeLog, List.flatMap_cons, List.flatMap_nil]

theorem encodeFrames_segs (rs : List Record) :
    encodeFrames rs = encodeSegList (rs.map (fun r => [r])) := by
  induction rs with
  | nil => simp [encodeFrames, encodeSegList]
  | cons r rs ih =>
      simp [encodeFrames, encodeSegList, encodeLog_singleton, ih]

theorem encodeFile_groups (rs : List Record) :
    encodeFile rs = encodeGroups (rs.map (fun r => [r])) := by
  simp [encodeFile, encodeGroups, encodeFrames_segs]

theorem join_singletons (rs : List Record) :
    joinGroups (rs.map (fun r => [r])) = rs := by
  induction rs with
  | nil => simp [joinGroups]
  | cons r rs ih => simp [joinGroups, ih]

theorem groupsFit_singletons (rs : List Record) (h : RecordsFit rs) :
    GroupsFit (rs.map (fun r => [r])) := by
  intro g hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
  simpa [encodeLog_singleton] using h r hr

theorem decodeFile_prefix (rs : List Record) (n : Nat) (h : RecordsFit rs) :
    ∃ k, decodeFile ((encodeFile rs).take n) = .ok (rs.take k) := by
  obtain ⟨k, hk⟩ := decodeGroups_prefix (rs.map (fun r => [r])) n (groupsFit_singletons rs h)
  refine ⟨k, ?_⟩
  rw [encodeFile_groups, hk]
  rw [show joinGroups ((rs.map (fun r => [r])).take k) = rs.take k from by
    rw [← List.map_take]
    exact join_singletons (rs.take k)]

theorem fitSegs_all (gs : List (List Record)) (n : Nat)
    (hn : (encodeSegList gs).length ≤ n) : fitSegs gs n = gs.length := by
  induction gs generalizing n with
  | nil => simp [fitSegs]
  | cons g gs ih =>
      simp only [encodeSegList, List.length_append, fitSegs] at hn ⊢
      simp [show ¬ n < (encodeFrame segMagic (encodeLog g)).length from by omega]
      have ih' := ih (n - (encodeFrame segMagic (encodeLog g)).length) (by omega)
      omega

theorem joinGroups_append (a b : List (List Record)) :
    joinGroups (a ++ b) = joinGroups a ++ joinGroups b := by
  induction a with
  | nil => simp [joinGroups]
  | cons g a ih => simp [joinGroups, ih, List.append_assoc]

theorem join_take_prefix (gs : List (List Record)) (k : Nat) :
    joinGroups (gs.take k) <+: joinGroups gs := by
  induction gs generalizing k with
  | nil => simp [joinGroups]
  | cons g gs ih =>
      cases k with
      | zero =>
          simp [joinGroups, List.take_zero]
      | succ k =>
          simp [joinGroups, List.take_succ_cons, List.prefix_append_right_inj, ih]

theorem fitSegs_append (a b : List (List Record)) (n : Nat)
    (hn : (encodeSegList a).length ≤ n) : a.length ≤ fitSegs (a ++ b) n := by
  induction a generalizing n with
  | nil => simp
  | cons g a ih =>
      have hsum : (encodeSegList (g :: a)).length =
          (encodeFrame segMagic (encodeLog g)).length + (encodeSegList a).length := by
        simp [encodeSegList, List.length_append]
      have hge : (encodeFrame segMagic (encodeLog g)).length ≤ n := by omega
      have hnot : ¬ n < (encodeFrame segMagic (encodeLog g)).length := by omega
      have hrest : (encodeSegList a).length ≤
          n - (encodeFrame segMagic (encodeLog g)).length := by omega
      have ih' := ih _ hrest
      simp only [List.length_cons, List.cons_append, fitSegs, hnot, ite_false]
      omega

theorem take_ge (a b : List (List Record)) (k : Nat) (hk : a.length ≤ k) :
    ∃ t, (a ++ b).take k = a ++ t := by
  refine ⟨b.take (k - a.length), ?_⟩
  rw [List.take_append, List.take_of_length_le hk]

/--
A byte prefix that still contains every synced frame replays to the synced
records followed by a prefix of the records that were in flight.
-/
theorem recovery_keeps_synced (synced inflight : List (List Record)) (n : Nat)
    (h : GroupsFit (synced ++ inflight))
    (hn : (encodeGroups synced).length ≤ n) :
    ∃ extra, decodeFile ((encodeGroups (synced ++ inflight)).take n) =
        .ok (joinGroups synced ++ extra) ∧
      joinGroups synced ++ extra <+: joinGroups (synced ++ inflight) := by
  have hge : encodeHeader.length ≤ n := by
    rw [encodeGroups, List.length_append] at hn
    omega
  have hdec := decodeGroups_long (synced ++ inflight) n h hge
  have hm : (encodeSegList synced).length ≤ n - encodeHeader.length := by
    rw [encodeGroups, List.length_append] at hn
    omega
  have hfit := fitSegs_append synced inflight (n - encodeHeader.length) hm
  obtain ⟨t, ht⟩ := take_ge synced inflight _ hfit
  refine ⟨joinGroups t, ?_, ?_⟩
  · rw [hdec, ht, joinGroups_append]
  · rw [← joinGroups_append, ← ht]
    exact join_take_prefix (synced ++ inflight) _

end Cairn
