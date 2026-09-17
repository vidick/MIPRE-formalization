/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.FieldFml

/-!
# The kinds of variables, on fields and as formulas

For the fields `F` of an index, the predicates `IsCell`, `IsHead`, … saying that `F` denotes a
variable of that kind (with its range checks), the characterization of `decodeVar` by them
(`decodeVar_cell_iff`, …), the numeric equality of two fields records (`Fields.numEq`, the
same variable up to the aliasing of unused fields), and the formulas computing all of these
on the field formulas of a literal (`isCellF`, `numEqF`, …) with their semantics
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open SAT Cost Fml

/-! ## Numeric equality of fields -/

/-- The numeric fields of two records agree (the flags may differ: an answer index and the
structured index of the same cell). -/
def Fields.numEq (F F' : Fields) : Prop :=
  F.tag = F'.tag ∧ F.t = F'.t ∧ F.d = F'.d ∧ F.p = F'.p ∧ F.v = F'.v ∧ F.q = F'.q ∧
    (∀ k, F.js k = F'.js k) ∧ F.g = F'.g

theorem Fields.numEq_refl (F : Fields) : F.numEq F := ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩

/-- The lengths of the field formulas of a literal. -/
structure FieldsF.Lengths (e G : ℕ) (A : FieldsF) : Prop where
  tag : A.tag.length = 3
  t : A.t.length = W e
  d : A.d.length = 4
  p : A.p.length = W e
  v : A.v.length = 3
  q : A.q.length = Qb
  js : ∀ k, (A.js k).length = W e
  g : A.g.length = Gb G

theorem litFields_lengths (e G T b : ℕ) : (litFields e G T b).Lengths e G where
  tag := by simp [litFields, length_muxList]
  t := by simp [litFields, length_muxList]
  d := by simp only [litFields]; rw [length_muxList _ _ _ (by rw [length_dAns]; simp)]; simp
  p := by simp only [litFields]; rw [length_muxList _ _ _ (by rw [length_pAnsF]; simp)]; simp
  v := by simp only [litFields]; rw [length_muxList _ _ _ (by rw [length_vAns]; simp)]; simp
  q := by simp [litFields, length_muxList]
  js k := by simp [litFields, length_muxList]
  g := by simp [litFields, length_muxList]

/-- The formula: the numeric fields of `A` and `B` agree. -/
def numEqF (A B : FieldsF) : Fml :=
  andList ([eqFields A.tag B.tag, eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p,
    eqFields A.v B.v, eqFields A.q B.q, eqFields A.g B.g] ++
    List.ofFn fun k : Fin 13 => eqFields (A.js k) (B.js k))

theorem eval_numEqF {e G : ℕ} {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool) :
    (numEqF A B).eval x = true ↔ (evalFields A x).numEq (evalFields B x) := by
  simp only [numEqF, eval_andList_eq_true, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false, Fields.numEq, evalFields]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k => ?_, ?_⟩
    · exact (eval_eqFields_iff _ _ (by rw [hA.tag, hB.tag]) x).mp (h _ (Or.inl (Or.inl rfl)))
    · exact (eval_eqFields_iff _ _ (by rw [hA.t, hB.t]) x).mp (h _ (Or.inl (Or.inr (Or.inl rfl))))
    · exact (eval_eqFields_iff _ _ (by rw [hA.d, hB.d]) x).mp (h _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
    · exact (eval_eqFields_iff _ _ (by rw [hA.p, hB.p]) x).mp
        (h _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact (eval_eqFields_iff _ _ (by rw [hA.v, hB.v]) x).mp
        (h _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    · exact (eval_eqFields_iff _ _ (by rw [hA.q, hB.q]) x).mp
        (h _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    · exact (eval_eqFields_iff _ _ (by rw [hA.js, hB.js]) x).mp (h _ (Or.inr ⟨k, rfl⟩))
    · exact (eval_eqFields_iff _ _ (by rw [hA.g, hB.g]) x).mp
        (h _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ f hf
    rcases hf with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, rfl⟩
    · exact (eval_eqFields_iff _ _ (by rw [hA.tag, hB.tag]) x).mpr h1
    · exact (eval_eqFields_iff _ _ (by rw [hA.t, hB.t]) x).mpr h2
    · exact (eval_eqFields_iff _ _ (by rw [hA.d, hB.d]) x).mpr h3
    · exact (eval_eqFields_iff _ _ (by rw [hA.p, hB.p]) x).mpr h4
    · exact (eval_eqFields_iff _ _ (by rw [hA.v, hB.v]) x).mpr h5
    · exact (eval_eqFields_iff _ _ (by rw [hA.q, hB.q]) x).mpr h6
    · exact (eval_eqFields_iff _ _ (by rw [hA.g, hB.g]) x).mpr h8
    · exact (eval_eqFields_iff _ _ (by rw [hA.js, hB.js]) x).mpr (h7 k)

/-! ## Kinds -/

section Kinds

/-- The fields denote a cell variable. -/
def IsCell (e : ℕ) (F : Fields) : Prop :=
  (F.flag = true ∧ F.tag = 0 ∧ F.t ≤ Sof e ∧ F.d < 13 ∧ F.p < numCells (Sof e) ∧ F.v < 7) ∨
  (F.flag = false ∧ F.ansOk = true ∧ F.tag = 0 ∧ F.t = 0 ∧ F.d < 7 ∧ F.p < numCells (Sof e) ∧ F.v < 7)

/-- The fields denote a head variable. -/
def IsHead (e : ℕ) (F : Fields) : Prop :=
  F.flag = true ∧ F.tag = 1 ∧ F.t ≤ Sof e ∧ F.d < 13 ∧ F.p < numCells (Sof e)

/-- The fields denote a state variable. -/
def IsState (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 2 ∧ F.t ≤ Sof e ∧ F.q < QC

/-- The fields denote an `emitOne` variable. -/
def IsEmitOne (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 3 ∧ F.t < Sof e

/-- The fields denote an `emitBad` variable. -/
def IsEmitBad (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 4 ∧ F.t < Sof e

/-- The fields denote an `emitted` variable. -/
def IsEmitted (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 5 ∧ F.t ≤ Sof e

/-- The fields denote a gate variable. -/
def IsAux (e G : ℕ) (F : Fields) : Prop :=
  F.flag = true ∧ F.tag = 6 ∧ F.t < Sof e ∧ (∀ k, F.js k < 2 * Sof e + 3) ∧ F.g < G

theorem tape_eq_inl_of_lt (d : Tape 7 6) (h : tapeCode d < 7) : d = .inl ⟨tapeCode d, h⟩ := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩
  · rfl
  · simp [tapeCode] at h

/-! ### Decoding by kind -/

variable (e G : ℕ)

theorem decodeVar_cell_iff (F : Fields) (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e))
    (v : CellVal Interp.Sym) :
    decodeVar e G F = some (.cell t d p v) ↔
      IsCell e F ∧ F.t = t ∧ F.d = tapeCode d ∧ F.p = p ∧ F.v = symCode v := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · rename_i htag
        split at h
        · rename_i hb
          split at h
          · rename_i d' v' hd hv
            cases h
            have hd' := tapeOfCode_eq_some hd
            have hv' := symOfCode_eq_some hv
            refine ⟨Or.inl ⟨hflag, htag, hb.1, ?_, hb.2, ?_⟩, rfl, hd'.symm, rfl, hv'.symm⟩
            · rw [← hd']; exact tapeCode_lt _
            · rw [← hv']; exact symCode_lt _
          · cases h
        · cases h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · rename_i hflag
      split at h
      · rename_i hok
        split at h
        · rename_i hb
          split at h
          · rename_i v' hv
            cases h
            have hv' := symOfCode_eq_some hv
            refine ⟨Or.inr ⟨by simpa using hflag, hok.1, hok.2.1, hok.2.2, hb.1, hb.2, ?_⟩,
              by rw [hok.2.2]; rfl, by simp [tapeCode], rfl, hv'.symm⟩
            rw [← hv']; exact symCode_lt _
          · cases h
        · cases h
      · cases h
  · rintro ⟨hk, ht, hd, hp, hv⟩
    unfold decodeVar
    rcases hk with ⟨hf, htag, hb1, hb2, hb3, hb4⟩ | ⟨hf, hok, htag, ht0, hb2, hb3, hb4⟩
    · rw [if_pos hf, if_pos htag, dif_pos ⟨hb1, hb3⟩, hd, hv, tapeOfCode_tapeCode, symOfCode_symCode]
      simp only [Option.some.injEq]
      congr 1 <;> ext <;> simp [ht, hp]
    · rw [if_neg (by simp [hf]), if_pos ⟨hok, htag, ht0⟩, dif_pos ⟨hb2, hb3⟩, hv, symOfCode_symCode]
      simp only [Option.some.injEq]
      have hd' : d = .inl ⟨tapeCode d, by omega⟩ := tape_eq_inl_of_lt d (by omega)
      rw [hd']
      congr 1
      · ext; simp [← ht, ht0]
      · congr 1; ext; simp [hd]
      · ext; simp [hp]

theorem decodeVar_head_iff (F : Fields) (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) :
    decodeVar e G F = some (.head t d p) ↔
      IsHead e F ∧ F.t = t ∧ F.d = tapeCode d ∧ F.p = p := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
      · split at h
        · rename_i htag
          split at h
          · rename_i hb
            split at h
            · rename_i d' hd
              cases h
              have hd' := tapeOfCode_eq_some hd
              exact ⟨⟨hflag, htag, hb.1, by rw [← hd']; exact tapeCode_lt _, hb.2⟩, rfl, hd'.symm, rfl⟩
            · cases h
          · cases h
        · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · exfalso; split_ifs at h <;> (try split at h) <;> cases h
  · rintro ⟨⟨hf, htag, hb1, hb2, hb3⟩, ht, hd, hp⟩
    unfold decodeVar
    rw [if_pos hf, if_neg (by rw [htag]; decide), if_pos htag, dif_pos ⟨hb1, hb3⟩, hd, tapeOfCode_tapeCode]
    simp only [Option.some.injEq]
    congr 1 <;> ext <;> simp [ht, hp]

theorem decodeVar_state_iff (F : Fields) (t : Fin (Sof e + 1)) (q : Option Interp.Ctl) :
    decodeVar e G F = some (.state t q) ↔ IsState e F ∧ F.t = t ∧ F.q = qCode q := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
      · split at h
        · exfalso; split_ifs at h <;> (try split at h) <;> cases h
        · split at h
          · rename_i htag
            split at h
            · rename_i hb
              split at h
              · rename_i q' hq
                cases h
                have hq' := qOfCode_eq_some hq
                exact ⟨⟨hflag, htag, hb, by rw [← hq']; exact qCode_lt _⟩, rfl, hq'.symm⟩
              · cases h
            · cases h
          · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · exfalso; split_ifs at h <;> (try split at h) <;> cases h
  · rintro ⟨⟨hf, htag, hb1, hb2⟩, ht, hq⟩
    unfold decodeVar
    rw [if_pos hf, if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide), if_pos htag,
      dif_pos hb1, hq, qOfCode_qCode]
    simp only [Option.some.injEq]
    congr 1; ext; simp [ht]

theorem decodeVar_emitOne_iff (F : Fields) (t : Fin (Sof e)) :
    decodeVar e G F = some (.emitOne t) ↔ IsEmitOne e F ∧ F.t = t := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
      · split at h
        · exfalso; split_ifs at h <;> (try split at h) <;> cases h
        · split at h
          · exfalso; split_ifs at h <;> (try split at h) <;> cases h
          · split at h
            · rename_i htag
              split at h
              · rename_i hb
                cases h
                exact ⟨⟨hflag, htag, hb⟩, rfl⟩
              · cases h
            · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · exfalso; split_ifs at h <;> (try split at h) <;> cases h
  · rintro ⟨⟨hf, htag, hb⟩, ht⟩
    unfold decodeVar
    rw [if_pos hf, if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide),
      if_neg (by rw [htag]; decide), if_pos htag, dif_pos hb]
    simp only [Option.some.injEq]
    congr 1; ext; simp [ht]

theorem decodeVar_emitBad_iff (F : Fields) (t : Fin (Sof e)) :
    decodeVar e G F = some (.emitBad t) ↔ IsEmitBad e F ∧ F.t = t := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
      · split at h
        · exfalso; split_ifs at h <;> (try split at h) <;> cases h
        · split at h
          · exfalso; split_ifs at h <;> (try split at h) <;> cases h
          · split at h
            · exfalso; split_ifs at h <;> (try split at h) <;> cases h
            · split at h
              · rename_i htag
                split at h
                · rename_i hb
                  cases h
                  exact ⟨⟨hflag, htag, hb⟩, rfl⟩
                · cases h
              · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · exfalso; split_ifs at h <;> (try split at h) <;> cases h
  · rintro ⟨⟨hf, htag, hb⟩, ht⟩
    unfold decodeVar
    rw [if_pos hf, if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide),
      if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide), if_pos htag, dif_pos hb]
    simp only [Option.some.injEq]
    congr 1; ext; simp [ht]

theorem decodeVar_emitted_iff (F : Fields) (t : Fin (Sof e + 1)) :
    decodeVar e G F = some (.emitted t) ↔ IsEmitted e F ∧ F.t = t := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
      · split at h
        · exfalso; split_ifs at h <;> (try split at h) <;> cases h
        · split at h
          · exfalso; split_ifs at h <;> (try split at h) <;> cases h
          · split at h
            · exfalso; split_ifs at h <;> (try split at h) <;> cases h
            · split at h
              · exfalso; split_ifs at h <;> (try split at h) <;> cases h
              · split at h
                · rename_i htag
                  split at h
                  · rename_i hb
                    cases h
                    exact ⟨⟨hflag, htag, hb⟩, rfl⟩
                  · cases h
                · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · exfalso; split_ifs at h <;> (try split at h) <;> cases h
  · rintro ⟨⟨hf, htag, hb⟩, ht⟩
    unfold decodeVar
    rw [if_pos hf, if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide),
      if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide),
      if_pos htag, dif_pos hb]
    simp only [Option.some.injEq]
    congr 1; ext; simp [ht]

theorem decodeVar_aux_iff (F : Fields) (t : Fin (Sof e)) (js : Tape 7 6 → Center (Sof e)) (g : Fin G) :
    decodeVar e G F = some (.aux t js g) ↔
      IsAux e G F ∧ F.t = t ∧ (∀ d, F.js ⟨tapeCode d, tapeCode_lt d⟩ = js d) ∧ F.g = g := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
      · split at h
        · exfalso; split_ifs at h <;> (try split at h) <;> cases h
        · split at h
          · exfalso; split_ifs at h <;> (try split at h) <;> cases h
          · split at h
            · exfalso; split_ifs at h <;> (try split at h) <;> cases h
            · split at h
              · exfalso; split_ifs at h <;> (try split at h) <;> cases h
              · split at h
                · exfalso; split_ifs at h <;> (try split at h) <;> cases h
                · split at h
                  · rename_i htag
                    split at h
                    · rename_i hb
                      cases h
                      exact ⟨⟨hflag, htag, hb.1, hb.2.1, hb.2.2⟩, rfl, fun d => rfl, rfl⟩
                    · cases h
                  · cases h
    · exfalso; split_ifs at h <;> (try split at h) <;> cases h
  · rintro ⟨⟨hf, htag, hb1, hb2, hb3⟩, ht, hjs, hg⟩
    unfold decodeVar
    rw [if_pos hf, if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide),
      if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide), if_neg (by rw [htag]; decide),
      if_neg (by rw [htag]; decide), if_pos htag, dif_pos ⟨hb1, hb2, hb3⟩]
    simp only [Option.some.injEq]
    congr 1
    · ext; simp [ht]
    · funext d; ext; simp [hjs d]
    · ext; simp [hg]

/-! ### Kinds as formulas -/

/-- The formula: `A` denotes a cell variable. -/
def isCellF (A : FieldsF) : Fml :=
  or (andList [A.flag, eqConst A.tag (nbits 3 0), ltConst A.t (nbits (W e) (Sof e + 1)),
      ltConst A.d (nbits 4 13), ltConst A.p (nbits (W e) (numCells (Sof e))), ltConst A.v (nbits 3 7)])
    (andList [not A.flag, A.ansOk, eqConst A.tag (nbits 3 0), eqConst A.t (nbits (W e) 0),
      ltConst A.d (nbits 4 7), ltConst A.p (nbits (W e) (numCells (Sof e))), ltConst A.v (nbits 3 7)])

/-- The formula: `A` denotes a head variable. -/
def isHeadF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 1), ltConst A.t (nbits (W e) (Sof e + 1)),
    ltConst A.d (nbits 4 13), ltConst A.p (nbits (W e) (numCells (Sof e)))]

/-- The formula: `A` denotes a state variable. -/
def isStateF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 2), ltConst A.t (nbits (W e) (Sof e + 1)),
    ltConst A.q (nbits Qb QC)]

/-- The formula: `A` denotes an `emitOne` variable. -/
def isEmitOneF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 3), ltConst A.t (nbits (W e) (Sof e))]

/-- The formula: `A` denotes an `emitBad` variable. -/
def isEmitBadF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 4), ltConst A.t (nbits (W e) (Sof e))]

/-- The formula: `A` denotes an `emitted` variable. -/
def isEmittedF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 5), ltConst A.t (nbits (W e) (Sof e + 1))]

/-- The formula: `A` denotes a gate variable. -/
def isAuxF (A : FieldsF) : Fml :=
  andList ([A.flag, eqConst A.tag (nbits 3 6), ltConst A.t (nbits (W e) (Sof e)),
    ltConst A.g (nbits (Gb G) G)] ++
    List.ofFn fun k : Fin 13 => ltConst (A.js k) (nbits (W e) (2 * Sof e + 3)))

section KindFormulas

variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA

theorem eval_eqTag (k : ℕ) (hk : k < 8) :
    (eqConst A.tag (nbits 3 k)).eval x = true ↔ val A.tag x = k := by
  rw [eval_eqConst_iff _ _ (by rw [hA.tag, length_nbits]), bitsVal_nbits_of_lt hk]

theorem eval_ltT (k : ℕ) (hk : k < 2 ^ W e) :
    (ltConst A.t (nbits (W e) k)).eval x = true ↔ val A.t x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.t, length_nbits]), bitsVal_nbits_of_lt hk]

theorem eval_ltD (k : ℕ) (hk : k < 16) :
    (ltConst A.d (nbits 4 k)).eval x = true ↔ val A.d x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.d, length_nbits]), bitsVal_nbits_of_lt hk]

theorem eval_ltP (k : ℕ) (hk : k < 2 ^ W e) :
    (ltConst A.p (nbits (W e) k)).eval x = true ↔ val A.p x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.p, length_nbits]), bitsVal_nbits_of_lt hk]

theorem eval_ltV (k : ℕ) (hk : k < 8) :
    (ltConst A.v (nbits 3 k)).eval x = true ↔ val A.v x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.v, length_nbits]), bitsVal_nbits_of_lt hk]

omit hA in
theorem S_succ_lt : Sof e + 1 < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega

theorem eval_isCellF : (isCellF e A).eval x = true ↔ IsCell e (evalFields A x) := by
  have hS := S_succ_lt e
  have hC := numCells_lt_two_pow_W e
  simp only [isCellF, IsCell, evalFields, eval, Bool.or_eq_true, eval_andList_eq_true,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, and_true, Bool.not_eq_true',
    eval_eqTag e G hA x 0 (by omega), eval_ltT e G hA x _ hS, eval_ltD e G hA x 13 (by omega),
    eval_ltD e G hA x 7 (by omega), eval_ltP e G hA x _ hC, eval_ltV e G hA x 7 (by omega),
    eval_eqConst_iff A.t (nbits (W e) 0) (by rw [hA.t, length_nbits]), bitsVal_nbits, Nat.zero_mod,
    Nat.lt_succ_iff]

theorem eval_isHeadF : (isHeadF e A).eval x = true ↔ IsHead e (evalFields A x) := by
  have hS := S_succ_lt e
  have hC := numCells_lt_two_pow_W e
  simp only [isHeadF, IsHead, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 1 (by omega), eval_ltT e G hA x _ hS,
    eval_ltD e G hA x 13 (by omega), eval_ltP e G hA x _ hC, Nat.lt_succ_iff]

theorem eval_isStateF : (isStateF e A).eval x = true ↔ IsState e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isStateF, IsState, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 2 (by omega), eval_ltT e G hA x _ hS,
    eval_ltConst_iff A.q (nbits Qb QC) (by rw [hA.q, length_nbits]), bitsVal_nbits_of_lt QC_lt_two_pow_Qb,
    Nat.lt_succ_iff]

theorem eval_isEmitOneF : (isEmitOneF e A).eval x = true ↔ IsEmitOne e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isEmitOneF, IsEmitOne, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 3 (by omega), eval_ltT e G hA x (Sof e) (by omega)]

theorem eval_isEmitBadF : (isEmitBadF e A).eval x = true ↔ IsEmitBad e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isEmitBadF, IsEmitBad, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 4 (by omega), eval_ltT e G hA x (Sof e) (by omega)]

theorem eval_isEmittedF : (isEmittedF e A).eval x = true ↔ IsEmitted e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isEmittedF, IsEmitted, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 5 (by omega), eval_ltT e G hA x _ hS,
    Nat.lt_succ_iff]

theorem eval_isAuxF : (isAuxF e G A).eval x = true ↔ IsAux e G (evalFields A x) := by
  have hS := S_succ_lt e
  have hC := numCells_lt_two_pow_W e
  have h2 : 2 * Sof e + 3 < 2 ^ W e := by unfold numCells at hC; omega
  simp only [isAuxF, IsAux, evalFields, eval_andList_eq_true, List.mem_append, List.mem_cons,
    List.mem_ofFn, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨h _ (Or.inl (Or.inl rfl)), ?_, ?_, fun k => ?_, ?_⟩
    · exact (eval_eqTag e G hA x 6 (by omega)).mp (h _ (Or.inl (Or.inr (Or.inl rfl))))
    · exact (eval_ltT e G hA x _ (by omega)).mp (h _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
    · have := h _ (Or.inr ⟨k, rfl⟩)
      rwa [eval_ltConst_iff _ _ (by rw [hA.js, length_nbits]), bitsVal_nbits_of_lt h2] at this
    · have := h _ (Or.inl (Or.inr (Or.inr (Or.inr rfl))))
      rwa [eval_ltConst_iff _ _ (by rw [hA.g, length_nbits]), bitsVal_nbits_of_lt (G_lt_two_pow_Gb G)] at this
  · rintro ⟨h1, h2', h3, h4, h5⟩ f hf
    rcases hf with (rfl | rfl | rfl | rfl) | ⟨k, rfl⟩
    · exact h1
    · exact (eval_eqTag e G hA x 6 (by omega)).mpr h2'
    · exact (eval_ltT e G hA x _ (by omega)).mpr h3
    · rw [eval_ltConst_iff _ _ (by rw [hA.g, length_nbits]), bitsVal_nbits_of_lt (G_lt_two_pow_Gb G)]
      exact h5
    · rw [eval_ltConst_iff _ _ (by rw [hA.js, length_nbits]), bitsVal_nbits_of_lt h2]
      exact h4 k

end KindFormulas

end Kinds

end MIPRE.TM.CookLevin.Desc
