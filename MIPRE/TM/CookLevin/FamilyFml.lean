/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Window

/-!
# The clause families as formulas

For each family predicate of `Families.lean` and `Window.lean`, the formula computing it on a
candidate of field formulas (`CandF`: three `FieldsF` and three sign formulas), with its
exact semantics (`eval_startF`, …, `eval_windowF`) and its input bound. The fixed input
tapes enter through value formulas (`cellValF` for a listed string, `unaryValF` for the
unary time bound), tied to `fixed` by `TapeSpec`; the free tapes through the list of their
indices (`FreeSpec`) (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## Helpers -/

theorem Bool.eq_decide_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) :
    b = decide P := by
  cases b
  · simp only [Bool.false_eq_true, false_iff] at h
    simp [h]
  · simp only [true_iff] at h
    simp [h]

theorem eval_eqN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (eqConst fs (nbits w k)).eval x = true ↔ val fs x = k := by
  rw [eval_eqConst_iff _ _ (by rw [hl, length_nbits]), bitsVal_nbits_of_lt hk]

theorem eval_eqN_eq {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (eqConst fs (nbits w k)).eval x = decide (val fs x = k) :=
  Bool.eq_decide_of_iff (eval_eqN hl hk x)

theorem eval_ltN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (ltConst fs (nbits w k)).eval x = true ↔ val fs x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hl, length_nbits]), bitsVal_nbits_of_lt hk]

theorem eval_eqF {fs gs : List Fml} {w : ℕ} (hl : fs.length = w) (hg : gs.length = w) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = true ↔ val fs x = val gs x :=
  eval_eqFields_iff _ _ (by rw [hl, hg]) x

theorem eval_ltF {fs gs : List Fml} {w : ℕ} (hl : fs.length = w) (hg : gs.length = w) (x : ℕ → Bool) :
    (ltFields fs gs).eval x = true ↔ val fs x < val gs x :=
  eval_ltFields_iff _ _ (by rw [hl, hg]) x

theorem eval_addN {fs gs : List Fml} {w k : ℕ} (hl : fs.length = w) (hg : gs.length = w)
    (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (addConstRel fs gs (nbits w k)).eval x = true ↔ val gs x = val fs x + k := by
  rw [eval_addConstRel_iff _ _ _ (by rw [hl, length_nbits]) (by rw [hl, hg]), bitsVal_nbits_of_lt hk]

theorem eval_xnor_iff (f g : Fml) (x : ℕ → Bool) : (xnor f g).eval x = true ↔ f.eval x = g.eval x := by
  rw [eval_xnor, beq_iff_eq]

theorem eval_sign (σ f : Fml) (x : ℕ → Bool) {P : Prop} [Decidable P] (hf : f.eval x = true ↔ P) :
    (xnor σ f).eval x = true ↔ σ.eval x = decide P := by
  rw [eval_xnor_iff, Bool.eq_decide_of_iff hf]

theorem eval_signConst (σ : Fml) (b : Bool) (x : ℕ → Bool) :
    (xnor σ (const b)).eval x = true ↔ σ.eval x = b := by
  rw [eval_xnor_iff]; rfl

theorem eval_not_iff (f : Fml) (x : ℕ → Bool) : (not f).eval x = true ↔ ¬ f.eval x = true := by
  simp [eval]

theorem eval_and_iff (f g : Fml) (x : ℕ → Bool) : (and f g).eval x = true ↔ f.eval x = true ∧ g.eval x = true := by
  simp [eval]

theorem eval_or_iff (f g : Fml) (x : ℕ → Bool) : (or f g).eval x = true ↔ f.eval x = true ∨ g.eval x = true := by
  simp [eval]

theorem eval_andList₂ (a b : Fml) (x : ℕ → Bool) :
    (andList [a, b]).eval x = true ↔ a.eval x = true ∧ b.eval x = true := by
  simp [eval_andList_eq_true]

theorem eval_andList₃ (a b c : Fml) (x : ℕ → Bool) :
    (andList [a, b, c]).eval x = true ↔ a.eval x = true ∧ b.eval x = true ∧ c.eval x = true := by
  simp [eval_andList_eq_true]

theorem eval_andList₄ (a b c d : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true := by
  simp [eval_andList_eq_true]

theorem eval_andList₅ (a b c d f : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true := by
  simp [eval_andList_eq_true]

theorem eval_andList₆ (a b c d f g : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true := by
  simp [eval_andList_eq_true]

theorem eval_andList₇ (a b c d f g h : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g, h]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true ∧ h.eval x = true := by
  simp [eval_andList_eq_true]

theorem eval_andList₈ (a b c d f g h i : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g, h, i]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true ∧ h.eval x = true ∧ i.eval x = true := by
  simp [eval_andList_eq_true]

theorem eval_andList₉ (a b c d f g h i j : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g, h, i, j]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true ∧ h.eval x = true ∧ i.eval x = true ∧ j.eval x = true := by
  simp [eval_andList_eq_true]

theorem InputsLt.and' {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.and f g).InputsLt n := ⟨hf, hg⟩

theorem InputsLt.or' {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.or f g).InputsLt n := ⟨hf, hg⟩

theorem InputsLt.not' {n : ℕ} {f : Fml} (hf : f.InputsLt n) : (Fml.not f).InputsLt n := hf

theorem InputsLt.const' {n : ℕ} (b : Bool) : (Fml.const b).InputsLt n := trivial

theorem InputsLt.list_cons {n : ℕ} {f : Fml} {l : List Fml} (hf : f.InputsLt n) (hl : ∀ g ∈ l, g.InputsLt n) :
    ∀ g ∈ f :: l, g.InputsLt n := by
  simpa [List.forall_mem_cons] using ⟨hf, hl⟩

theorem InputsLt.list_nil {n : ℕ} : ∀ g ∈ ([] : List Fml), g.InputsLt n := by simp

theorem InputsLt.nbitsC {n w c : ℕ} : ∀ f ∈ constBits (nbits w c), f.InputsLt n := InputsLt.constBits _

/-! ## Input bounds of the field formulas -/

/-- The field formulas read only inputs below `n`. -/
structure FieldsF.InputsLt (n : ℕ) (A : FieldsF) : Prop where
  flag : A.flag.InputsLt n
  tag : ∀ f ∈ A.tag, f.InputsLt n
  t : ∀ f ∈ A.t, f.InputsLt n
  d : ∀ f ∈ A.d, f.InputsLt n
  p : ∀ f ∈ A.p, f.InputsLt n
  v : ∀ f ∈ A.v, f.InputsLt n
  q : ∀ f ∈ A.q, f.InputsLt n
  js : ∀ k, ∀ f ∈ A.js k, f.InputsLt n
  g : ∀ f ∈ A.g, f.InputsLt n
  ansOk : A.ansOk.InputsLt n

theorem InputsLt.muxList {n : ℕ} {s : Fml} {as bs : List Fml} (hs : s.InputsLt n)
    (ha : ∀ f ∈ as, f.InputsLt n) (hb : ∀ f ∈ bs, f.InputsLt n) :
    ∀ f ∈ muxList s as bs, f.InputsLt n := by
  intro f hf
  rw [Desc.muxList, List.mem_iff_getElem] at hf
  obtain ⟨i, hi, rfl⟩ := hf
  rw [List.getElem_zipWith]
  exact InputsLt.mux hs (ha _ (List.getElem_mem _)) (hb _ (List.getElem_mem _))

theorem InputsLt.cst {n w c : ℕ} : ∀ f ∈ cst w c, f.InputsLt n := InputsLt.constBits _

theorem InputsLt.take {n : ℕ} {l : List Fml} (h : ∀ f ∈ l, f.InputsLt n) (k : ℕ) :
    ∀ f ∈ l.take k, f.InputsLt n := fun f hf => h f (List.mem_of_mem_take hf)

theorem InputsLt.tail {n : ℕ} {l : List Fml} (h : ∀ f ∈ l, f.InputsLt n) :
    ∀ f ∈ l.tail, f.InputsLt n := fun f hf => h f (List.mem_of_mem_tail hf)

theorem InputsLt.headD {n : ℕ} {l : List Fml} (h : ∀ f ∈ l, f.InputsLt n) :
    (l.headD (const false)).InputsLt n := by
  cases l with
  | nil => trivial
  | cons a l => exact h a (List.mem_cons_self ..)

section LitInputs

variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn

theorem InputsLt.flagF : (flagF e G b).InputsLt n := by
  show b + flagOff e G < n
  unfold flagOff mOf at *
  omega

theorem InputsLt.jF : ∀ f ∈ jF e G b, f.InputsLt n :=
  InputsLt.field (by unfold flagOff mOf at *; omega)

theorem InputsLt.rF : ∀ f ∈ rF e G T b, f.InputsLt n :=
  InputsLt.muxList (InputsLt.ltConst _ (InputsLt.jF e G b n hn)) (InputsLt.jF e G b n hn)
    (InputsLt.subConstBits _ (InputsLt.jF e G b n hn))

theorem InputsLt.pAnsF : ∀ f ∈ pAnsF e G T b, f.InputsLt n :=
  InputsLt.addConstBits _ (InputsLt.take (InputsLt.tail (InputsLt.rF e G T b n hn)) _)

theorem InputsLt.fieldOff (off w : ℕ) (h : off + w ≤ mOf e G) : ∀ f ∈ field (b + off) w, f.InputsLt n :=
  InputsLt.field (by omega)

omit hn in
theorem jsOff_add_le (k : Fin 13) : jsOff e k + W e ≤ mOf e G := by
  unfold jsOff mOf
  have : (k : ℕ) * W e + W e ≤ 13 * W e := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by have := k.isLt; omega)
  generalize Qb = q at *
  omega

omit hn in
theorem qOff_add_le : qOff e + Qb ≤ mOf e G := by
  unfold qOff mOf
  generalize Qb = q
  omega

omit hn in
theorem gOff_add_le : gOff e + Gb G ≤ mOf e G := by
  unfold gOff mOf
  generalize Qb = q
  generalize Gb G = g
  omega

theorem litFields_inputsLt : (litFields e G T b).InputsLt n := by
  have hf := InputsLt.flagF e G b n hn
  have hj := InputsLt.jF e G b n hn
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn tagOff 3 (by unfold tagOff mOf; omega)) InputsLt.cst
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn tOff (W e) (by unfold tOff mOf; omega)) InputsLt.cst
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (dOff e) 4 (by unfold dOff mOf; omega))
      (InputsLt.muxList (InputsLt.ltConst _ hj) InputsLt.cst InputsLt.cst)
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (pOff e) (W e) (by unfold pOff mOf; omega))
      (InputsLt.pAnsF e G T b n hn)
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (vOff e) 3 (by unfold vOff mOf; omega))
      (InputsLt.muxList (InputsLt.headD (InputsLt.rF e G T b n hn)) InputsLt.cst InputsLt.cst)
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (qOff e) Qb (qOff_add_le e G)) InputsLt.cst
  · intro k
    exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (jsOff e k) (W e) (jsOff_add_le e G k))
      InputsLt.cst
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (gOff e) (Gb G) (gOff_add_le e G))
      InputsLt.cst
  · exact InputsLt.and' (InputsLt.not' hf) (InputsLt.ltConst _ hj)

end LitInputs

section KindInputs

variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA

theorem InputsLt.isCellF : (isCellF e A).InputsLt n :=
  InputsLt.or' (InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) (InputsLt.list_cons (InputsLt.ltConst _ hA.d)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.p) (InputsLt.list_cons (InputsLt.ltConst _ hA.v) InputsLt.list_nil)))))))
    (InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' hA.flag) (InputsLt.list_cons hA.ansOk
    (InputsLt.list_cons (InputsLt.eqConst _ hA.tag) (InputsLt.list_cons (InputsLt.eqConst _ hA.t)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.d) (InputsLt.list_cons (InputsLt.ltConst _ hA.p)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.v) InputsLt.list_nil))))))))

theorem InputsLt.isHeadF : (isHeadF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) (InputsLt.list_cons (InputsLt.ltConst _ hA.d)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.p) InputsLt.list_nil)))))

theorem InputsLt.isStateF : (isStateF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) (InputsLt.list_cons (InputsLt.ltConst _ hA.q) InputsLt.list_nil))))

theorem InputsLt.isEmitOneF : (isEmitOneF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) InputsLt.list_nil)))

theorem InputsLt.isEmitBadF : (isEmitBadF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) InputsLt.list_nil)))

theorem InputsLt.isEmittedF : (isEmittedF e A).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons hA.flag (InputsLt.list_cons (InputsLt.eqConst _ hA.tag)
    (InputsLt.list_cons (InputsLt.ltConst _ hA.t) InputsLt.list_nil)))

theorem InputsLt.isAuxF : (isAuxF e G A).InputsLt n := by
  refine InputsLt.andList _ ?_
  intro f hf
  rw [List.mem_append, List.mem_ofFn] at hf
  rcases hf with hf | ⟨k, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact hA.flag
    · exact InputsLt.eqConst _ hA.tag
    · exact InputsLt.ltConst _ hA.t
    · exact InputsLt.ltConst _ hA.g
  · exact InputsLt.ltConst _ (hA.js k)

end KindInputs

/-! ## Candidates of formulas -/

/-- A candidate of formulas: three field records and three sign formulas. -/
structure CandF where
  A₁ : FieldsF
  σ₁ : Fml
  A₂ : FieldsF
  σ₂ : Fml
  A₃ : FieldsF
  σ₃ : Fml

/-- The candidate a candidate of formulas evaluates to. -/
def evalCand (C : CandF) (x : ℕ → Bool) : Cand :=
  ⟨evalFields C.A₁ x, C.σ₁.eval x, evalFields C.A₂ x, C.σ₂.eval x, evalFields C.A₃ x, C.σ₃.eval x⟩

/-- The three records have the field lengths. -/
structure CandF.Lengths (e G : ℕ) (C : CandF) : Prop where
  A₁ : C.A₁.Lengths e G
  A₂ : C.A₂.Lengths e G
  A₃ : C.A₃.Lengths e G

/-- The candidate reads only inputs below `n`. -/
structure CandF.InputsLt (n : ℕ) (C : CandF) : Prop where
  A₁ : C.A₁.InputsLt n
  σ₁ : C.σ₁.InputsLt n
  A₂ : C.A₂.InputsLt n
  σ₂ : C.σ₂.InputsLt n
  A₃ : C.A₃.InputsLt n
  σ₃ : C.σ₃.InputsLt n

variable (e G : ℕ)

/-! ### Same-variable formulas -/

/-- `cellEq`. -/
def cellEqF (A B : FieldsF) : Fml :=
  andList [eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p, eqFields A.v B.v]

/-- `headEq`. -/
def headEqF (A B : FieldsF) : Fml := andList [eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p]

/-- `stateEq`. -/
def stateEqF (A B : FieldsF) : Fml := andList [eqFields A.t B.t, eqFields A.q B.q]

/-- `auxEq`. -/
def auxEqF (A B : FieldsF) : Fml :=
  andList ([eqFields A.t B.t, eqFields A.g B.g] ++ List.ofFn fun k : Fin 13 => eqFields (A.js k) (B.js k))

/-- `samePos`. -/
def samePosF (A B : FieldsF) : Fml := andList [eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p]

section EqF

variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB

theorem eval_cellEqF : (cellEqF A B).eval x = true ↔ cellEq (evalFields A x) (evalFields B x) := by
  rw [cellEqF, eval_andList₄, eval_eqF hA.t hB.t, eval_eqF hA.d hB.d, eval_eqF hA.p hB.p, eval_eqF hA.v hB.v]
  rfl

theorem eval_headEqF : (headEqF A B).eval x = true ↔ headEq (evalFields A x) (evalFields B x) := by
  rw [headEqF, eval_andList₃, eval_eqF hA.t hB.t, eval_eqF hA.d hB.d, eval_eqF hA.p hB.p]
  rfl

theorem eval_stateEqF : (stateEqF A B).eval x = true ↔ stateEq (evalFields A x) (evalFields B x) := by
  rw [stateEqF, eval_andList₂, eval_eqF hA.t hB.t, eval_eqF hA.q hB.q]
  rfl

theorem eval_samePosF : (samePosF A B).eval x = true ↔ samePos (evalFields A x) (evalFields B x) := by
  rw [samePosF, eval_andList₃, eval_eqF hA.t hB.t, eval_eqF hA.d hB.d, eval_eqF hA.p hB.p]
  rfl

theorem eval_tEqF : (eqFields A.t B.t).eval x = true ↔ (evalFields A x).t = (evalFields B x).t :=
  eval_eqF hA.t hB.t x

theorem eval_auxEqF : (auxEqF A B).eval x = true ↔ auxEq (evalFields A x) (evalFields B x) := by
  simp only [auxEqF, eval_andList_eq_true, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false, auxEq, evalFields]
  constructor
  · intro h
    exact ⟨(eval_eqF hA.t hB.t x).mp (h _ (Or.inl (Or.inl rfl))),
      fun k => (eval_eqF (hA.js k) (hB.js k) x).mp (h _ (Or.inr ⟨k, rfl⟩)),
      (eval_eqF hA.g hB.g x).mp (h _ (Or.inl (Or.inr rfl)))⟩
  · rintro ⟨h1, h2, h3⟩ f hf
    rcases hf with (rfl | rfl) | ⟨k, rfl⟩
    · exact (eval_eqF hA.t hB.t x).mpr h1
    · exact (eval_eqF hA.g hB.g x).mpr h3
    · exact (eval_eqF (hA.js k) (hB.js k) x).mpr (h2 k)

end EqF

section EqInputs

variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB

theorem InputsLt.cellEqF : (cellEqF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t) (InputsLt.list_cons (InputsLt.eqFields hA.d hB.d)
    (InputsLt.list_cons (InputsLt.eqFields hA.p hB.p) (InputsLt.list_cons (InputsLt.eqFields hA.v hB.v) InputsLt.list_nil))))

theorem InputsLt.headEqF : (headEqF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t) (InputsLt.list_cons (InputsLt.eqFields hA.d hB.d)
    (InputsLt.list_cons (InputsLt.eqFields hA.p hB.p) InputsLt.list_nil)))

theorem InputsLt.stateEqF : (stateEqF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t)
    (InputsLt.list_cons (InputsLt.eqFields hA.q hB.q) InputsLt.list_nil))

theorem InputsLt.samePosF : (samePosF A B).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hA.t hB.t) (InputsLt.list_cons (InputsLt.eqFields hA.d hB.d)
    (InputsLt.list_cons (InputsLt.eqFields hA.p hB.p) InputsLt.list_nil)))

theorem InputsLt.tEqF : (eqFields A.t B.t).InputsLt n := InputsLt.eqFields hA.t hB.t

theorem InputsLt.auxEqF : (auxEqF A B).InputsLt n := by
  refine InputsLt.andList _ ?_
  intro f hf
  rw [List.mem_append, List.mem_ofFn] at hf
  rcases hf with hf | ⟨k, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact InputsLt.eqFields hA.t hB.t
    · exact InputsLt.eqFields hA.g hB.g
  · exact InputsLt.eqFields (hA.js k) (hB.js k)

end EqInputs

/-! ### Unit clauses and signs -/

/-- `UnitCell`. -/
def unitCellF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, cellEqF C.A₁ C.A₂, cellEqF C.A₁ C.A₃]

/-- `UnitHead`. -/
def unitHeadF (C : CandF) : Fml :=
  andList [isHeadF e C.A₁, isHeadF e C.A₂, isHeadF e C.A₃, headEqF C.A₁ C.A₂, headEqF C.A₁ C.A₃]

/-- `UnitState`. -/
def unitStateF (C : CandF) : Fml :=
  andList [isStateF e C.A₁, isStateF e C.A₂, isStateF e C.A₃, stateEqF C.A₁ C.A₂, stateEqF C.A₁ C.A₃]

/-- `UnitEmitBad`. -/
def unitEmitBadF (C : CandF) : Fml :=
  andList [isEmitBadF e C.A₁, isEmitBadF e C.A₂, isEmitBadF e C.A₃, eqFields C.A₁.t C.A₂.t,
    eqFields C.A₁.t C.A₃.t]

/-- `UnitEmitted`. -/
def unitEmittedF (C : CandF) : Fml :=
  andList [isEmittedF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, eqFields C.A₁.t C.A₂.t,
    eqFields C.A₁.t C.A₃.t]

/-- `UnitAux`. -/
def unitAuxF (C : CandF) : Fml :=
  andList [isAuxF e G C.A₁, isAuxF e G C.A₂, isAuxF e G C.A₃, auxEqF C.A₁ C.A₂, auxEqF C.A₁ C.A₃]

/-- `SameSigns`. -/
def sameSignsF (C : CandF) : Fml := and (xnor C.σ₂ C.σ₁) (xnor C.σ₃ C.σ₁)

section UnitF

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

theorem eval_unitCellF : (unitCellF e C).eval x = true ↔ UnitCell e (evalCand C x) := by
  rw [unitCellF, eval_andList₅, eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃,
    eval_cellEqF e G hC.A₁ hC.A₂, eval_cellEqF e G hC.A₁ hC.A₃]
  rfl

theorem eval_unitHeadF : (unitHeadF e C).eval x = true ↔ UnitHead e (evalCand C x) := by
  rw [unitHeadF, eval_andList₅, eval_isHeadF e G hC.A₁, eval_isHeadF e G hC.A₂, eval_isHeadF e G hC.A₃,
    eval_headEqF e G hC.A₁ hC.A₂, eval_headEqF e G hC.A₁ hC.A₃]
  rfl

theorem eval_unitStateF : (unitStateF e C).eval x = true ↔ UnitState e (evalCand C x) := by
  rw [unitStateF, eval_andList₅, eval_isStateF e G hC.A₁, eval_isStateF e G hC.A₂, eval_isStateF e G hC.A₃,
    eval_stateEqF e G hC.A₁ hC.A₂, eval_stateEqF e G hC.A₁ hC.A₃]
  rfl

theorem eval_unitEmitBadF : (unitEmitBadF e C).eval x = true ↔ UnitEmitBad e (evalCand C x) := by
  rw [unitEmitBadF, eval_andList₅, eval_isEmitBadF e G hC.A₁, eval_isEmitBadF e G hC.A₂,
    eval_isEmitBadF e G hC.A₃, eval_tEqF e G hC.A₁ hC.A₂, eval_tEqF e G hC.A₁ hC.A₃]
  rfl

theorem eval_unitEmittedF : (unitEmittedF e C).eval x = true ↔ UnitEmitted e (evalCand C x) := by
  rw [unitEmittedF, eval_andList₅, eval_isEmittedF e G hC.A₁, eval_isEmittedF e G hC.A₂,
    eval_isEmittedF e G hC.A₃, eval_tEqF e G hC.A₁ hC.A₂, eval_tEqF e G hC.A₁ hC.A₃]
  rfl

theorem eval_unitAuxF : (unitAuxF e G C).eval x = true ↔ UnitAux e G (evalCand C x) := by
  rw [unitAuxF, eval_andList₅, eval_isAuxF e G hC.A₁, eval_isAuxF e G hC.A₂, eval_isAuxF e G hC.A₃,
    eval_auxEqF e G hC.A₁ hC.A₂, eval_auxEqF e G hC.A₁ hC.A₃]
  rfl

omit hC in
theorem eval_sameSignsF : (sameSignsF C).eval x = true ↔ SameSigns (evalCand C x) := by
  rw [sameSignsF, eval_and_iff, eval_xnor_iff, eval_xnor_iff]
  rfl

end UnitF

section UnitInputs

variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC

theorem InputsLt.unitCellF : (unitCellF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.cellEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.cellEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))

theorem InputsLt.unitHeadF : (unitHeadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isHeadF hC.A₁) (InputsLt.list_cons (InputsLt.isHeadF hC.A₂)
    (InputsLt.list_cons (InputsLt.isHeadF hC.A₃) (InputsLt.list_cons (InputsLt.headEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.headEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))

theorem InputsLt.unitStateF : (unitStateF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isStateF hC.A₁) (InputsLt.list_cons (InputsLt.isStateF hC.A₂)
    (InputsLt.list_cons (InputsLt.isStateF hC.A₃) (InputsLt.list_cons (InputsLt.stateEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.stateEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))

theorem InputsLt.unitEmitBadF : (unitEmitBadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitBadF hC.A₁) (InputsLt.list_cons (InputsLt.isEmitBadF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmitBadF hC.A₃) (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))

theorem InputsLt.unitEmittedF : (unitEmittedF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmittedF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.tEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))

theorem InputsLt.unitAuxF : (unitAuxF e G C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isAuxF hC.A₁) (InputsLt.list_cons (InputsLt.isAuxF hC.A₂)
    (InputsLt.list_cons (InputsLt.isAuxF hC.A₃) (InputsLt.list_cons (InputsLt.auxEqF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.auxEqF hC.A₁ hC.A₃) InputsLt.list_nil)))))

theorem InputsLt.sameSignsF : (sameSignsF C).InputsLt n :=
  InputsLt.and' (InputsLt.xnor hC.σ₂ hC.σ₁) (InputsLt.xnor hC.σ₃ hC.σ₁)

end UnitInputs

/-! ### Positions and values -/

/-- `Bdry S p`. -/
def bdryF (A : FieldsF) : Fml :=
  or (ltConst A.p (nbits (W e) 2)) (not (ltConst A.p (nbits (W e) (2 * Sof e + 5))))

/-- `p = 3` for an input tape, `S + 3` for a work tape: the start cell. -/
def startCellF (A : FieldsF) : Fml :=
  mux (ltConst A.d (nbits 4 7)) (eqConst A.p (nbits (W e) 3)) (eqConst A.p (nbits (W e) (Sof e + 3)))

/-- `v = workCode S p`. -/
def workValF (A : FieldsF) : Fml :=
  mux (bdryF e A) (eqConst A.v (nbits 3 6)) (eqConst A.v (nbits 3 5))

/-- The lookup table of a string of codes from cell `k`: `p = k + i ∧ v = codes[i]`. -/
def lookupList (A : FieldsF) : ℕ → List ℕ → List Fml
  | _, [] => []
  | k, c :: cs => and (eqConst A.p (nbits (W e) k)) (eqConst A.v (nbits 3 c)) :: lookupList A (k + 1) cs

/-- `v = cellCode x S p` for the string `x` of codes `codes`, of length at most `S`. -/
def cellValF (A : FieldsF) (codes : List ℕ) : Fml :=
  mux (bdryF e A) (eqConst A.v (nbits 3 6))
    (mux (and (not (ltConst A.p (nbits (W e) 3))) (ltConst A.p (nbits (W e) (codes.length + 3))))
      (orList (lookupList e A 3 codes)) (eqConst A.v (nbits 3 5)))

/-- `v = cellCode 1^T S p`. -/
def unaryValF (T : ℕ) (A : FieldsF) : Fml :=
  mux (bdryF e A) (eqConst A.v (nbits 3 6))
    (mux (and (not (ltConst A.p (nbits (W e) 3))) (ltConst A.p (nbits (W e) (T + 3))))
      (eqConst A.v (nbits 3 1)) (eqConst A.v (nbits 3 5)))

/-- The codes of a string. -/
def codesOf (x : List Sym) : List ℕ := x.map fun s => symCode (.sym s)

theorem codesOf_lt (x : List Sym) : ∀ c ∈ codesOf x, c < 7 := by
  intro c hc
  rw [codesOf, List.mem_map] at hc
  obtain ⟨s, -, rfl⟩ := hc
  exact symCode_lt _

theorem twoS5_lt : 2 * Sof e + 5 < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega

theorem S_lt_two_pow : Sof e < 2 ^ W e := by have := twoS5_lt e; omega

section ValF

variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA

theorem eval_bdryF : (bdryF e A).eval x = true ↔ Bdry (Sof e) (evalFields A x).p := by
  rw [bdryF, eval_or_iff, eval_not_iff, eval_ltN hA.p (by have := twoS5_lt e; omega),
    eval_ltN hA.p (twoS5_lt e)]
  dsimp only [evalFields]
  simp only [not_lt]
  exact Iff.rfl

theorem eval_startCellF :
    (startCellF e A).eval x = true ↔
      (evalFields A x).p = if (evalFields A x).d < 7 then 3 else Sof e + 3 := by
  have hS := twoS5_lt e
  rw [startCellF, eval_mux]
  have h7 : (ltConst A.d (nbits 4 7)).eval x = decide (val A.d x < 7) :=
    Bool.eq_decide_of_iff (eval_ltN hA.d (by norm_num) x)
  rw [h7]
  show _ ↔ val A.p x = if val A.d x < 7 then 3 else Sof e + 3
  by_cases h : val A.d x < 7
  · rw [if_pos (by simpa using h), if_pos h]; exact eval_eqN hA.p (by omega) x
  · rw [if_neg (by simpa using h), if_neg h]; exact eval_eqN hA.p (by omega) x

theorem eval_workValF :
    (workValF e A).eval x = true ↔ (evalFields A x).v = workCode (Sof e) (evalFields A x).p := by
  rw [workValF, eval_mux, workCode]
  by_cases hb : Bdry (Sof e) (evalFields A x).p
  · rw [if_pos ((eval_bdryF e G hA x).mpr hb),
      if_pos (show (evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p from hb)]
    exact eval_eqN (k := 6) hA.v (by norm_num) x
  · rw [if_neg (fun h => hb ((eval_bdryF e G hA x).mp h)),
      if_neg (show ¬ ((evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p) from hb)]
    exact eval_eqN (k := 5) hA.v (by norm_num) x

theorem eval_lookupList (codes : List ℕ) (hc : ∀ c ∈ codes, c < 8) :
    ∀ k, k + codes.length < 2 ^ W e →
      ((orList (lookupList e A k codes)).eval x = true ↔
        ∃ i, ∃ h : i < codes.length, val A.p x = k + i ∧ val A.v x = codes[i]) := by
  induction codes with
  | nil => intro k _; simp [lookupList, orList, eval]
  | cons c cs ih =>
    intro k hk
    simp only [List.length_cons] at hk
    rw [lookupList, eval_orList_eq_true]
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [← eval_orList_eq_true, ih (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) (k + 1) (by omega),
      eval_and_iff, eval_eqN hA.p (by omega), eval_eqN hA.v (hc c (List.mem_cons_self ..))]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨i, hi, h1, h2⟩)
      · exact ⟨0, by simp, by omega, by simpa using h2⟩
      · exact ⟨i + 1, by simp; omega, by omega, by simpa using h2⟩
    · rintro ⟨i, hi, h1, h2⟩
      cases i with
      | zero => exact Or.inl ⟨by omega, by simpa using h2⟩
      | succ i => exact Or.inr ⟨i, by simp at hi; omega, by omega, by simpa using h2⟩

theorem eval_cellValF (s : List Sym) (hs : s.length ≤ Sof e) :
    (cellValF e A (codesOf s)).eval x = true ↔
      (evalFields A x).v = cellCode s (Sof e) (evalFields A x).p := by
  have hS := twoS5_lt e
  have hlen : (codesOf s).length = s.length := by simp [codesOf]
  have hp : (evalFields A x).p = val A.p x := rfl
  have hv : (evalFields A x).v = val A.v x := rfl
  rw [cellValF, eval_mux, cellCode]
  by_cases hb : Bdry (Sof e) (evalFields A x).p
  · rw [if_pos ((eval_bdryF e G hA x).mpr hb),
      if_pos (show (evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p from hb)]
    exact eval_eqN (k := 6) hA.v (by norm_num) x
  · rw [if_neg (fun h => hb ((eval_bdryF e G hA x).mp h)),
      if_neg (show ¬ ((evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p) from hb), eval_mux]
    have hrange : (and (not (ltConst A.p (nbits (W e) 3)))
        (ltConst A.p (nbits (W e) ((codesOf s).length + 3)))).eval x = true ↔
        3 ≤ (evalFields A x).p ∧ (evalFields A x).p - 3 < s.length := by
      rw [eval_and_iff, eval_not_iff, eval_ltN hA.p (by omega), eval_ltN hA.p (by omega)]
      omega
    by_cases hr : 3 ≤ (evalFields A x).p ∧ (evalFields A x).p - 3 < s.length
    · rw [if_pos (hrange.mpr hr), dif_pos hr,
        eval_lookupList e G hA x _ (fun c hc => by have := codesOf_lt s c hc; omega) 3 (by omega)]
      constructor
      · rintro ⟨i, hi, hpi, hvi⟩
        obtain rfl : i = (evalFields A x).p - 3 := by omega
        rw [hv, hvi]
        simp only [codesOf, List.getElem_map]
      · intro hvs
        refine ⟨(evalFields A x).p - 3, by omega, by omega, ?_⟩
        rw [← hv, hvs]
        simp only [codesOf, List.getElem_map]
    · rw [if_neg (fun h => hr (hrange.mp h)), dif_neg hr]
      exact eval_eqN (k := 5) hA.v (by norm_num) x

theorem eval_unaryValF (T : ℕ) (hT : T ≤ Sof e) :
    (unaryValF e T A).eval x = true ↔
      (evalFields A x).v = cellCode (List.replicate T .one) (Sof e) (evalFields A x).p := by
  have hS := twoS5_lt e
  have hp : (evalFields A x).p = val A.p x := rfl
  rw [unaryValF, eval_mux, cellCode_replicate]
  by_cases hb : Bdry (Sof e) (evalFields A x).p
  · rw [if_pos ((eval_bdryF e G hA x).mpr hb),
      if_pos (show (evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p from hb)]
    exact eval_eqN (k := 6) hA.v (by norm_num) x
  · rw [if_neg (fun h => hb ((eval_bdryF e G hA x).mp h)),
      if_neg (show ¬ ((evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p) from hb), eval_mux]
    have hrange : (and (not (ltConst A.p (nbits (W e) 3))) (ltConst A.p (nbits (W e) (T + 3)))).eval x = true ↔
        3 ≤ (evalFields A x).p ∧ (evalFields A x).p < T + 3 := by
      rw [eval_and_iff, eval_not_iff, eval_ltN hA.p (by omega), eval_ltN hA.p (by omega)]
      omega
    by_cases hr : 3 ≤ (evalFields A x).p ∧ (evalFields A x).p < T + 3
    · rw [if_pos (hrange.mpr hr), if_pos hr]
      exact eval_eqN (k := 1) hA.v (by norm_num) x
    · rw [if_neg (fun h => hr (hrange.mp h)), if_neg hr]
      exact eval_eqN (k := 5) hA.v (by norm_num) x

end ValF

section ValInputs

variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA

theorem InputsLt.bdryF : (bdryF e A).InputsLt n :=
  InputsLt.or' (InputsLt.ltConst _ hA.p) (InputsLt.not' (InputsLt.ltConst _ hA.p))

theorem InputsLt.startCellF : (startCellF e A).InputsLt n :=
  InputsLt.mux (InputsLt.ltConst _ hA.d) (InputsLt.eqConst _ hA.p) (InputsLt.eqConst _ hA.p)

theorem InputsLt.workValF : (workValF e A).InputsLt n :=
  InputsLt.mux (InputsLt.bdryF e hA) (InputsLt.eqConst _ hA.v) (InputsLt.eqConst _ hA.v)

theorem InputsLt.lookupList (codes : List ℕ) : ∀ k, ∀ f ∈ lookupList e A k codes, f.InputsLt n := by
  induction codes with
  | nil => intro k f hf; simp [Desc.lookupList] at hf
  | cons c cs ih =>
    intro k f hf
    simp only [Desc.lookupList, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact InputsLt.and' (InputsLt.eqConst _ hA.p) (InputsLt.eqConst _ hA.v)
    · exact ih _ f hf

theorem InputsLt.cellValF (codes : List ℕ) : (cellValF e A codes).InputsLt n :=
  InputsLt.mux (InputsLt.bdryF e hA) (InputsLt.eqConst _ hA.v)
    (InputsLt.mux (InputsLt.and' (InputsLt.not' (InputsLt.ltConst _ hA.p)) (InputsLt.ltConst _ hA.p))
      (InputsLt.orList _ (InputsLt.lookupList e hA codes 3)) (InputsLt.eqConst _ hA.v))

theorem InputsLt.unaryValF (T : ℕ) : (unaryValF e T A).InputsLt n :=
  InputsLt.mux (InputsLt.bdryF e hA) (InputsLt.eqConst _ hA.v)
    (InputsLt.mux (InputsLt.and' (InputsLt.not' (InputsLt.ltConst _ hA.p)) (InputsLt.ltConst _ hA.p))
      (InputsLt.eqConst _ hA.v) (InputsLt.eqConst _ hA.v))

end ValInputs


/-! ## More helpers -/

theorem eval_andList_cons (a : Fml) (l : List Fml) (x : ℕ → Bool) :
    (andList (a :: l)).eval x = true ↔ a.eval x = true ∧ (andList l).eval x = true := by
  rw [eval_andList_eq_true, eval_andList_eq_true, List.forall_mem_cons]

theorem eval_andList_nil (x : ℕ → Bool) : (andList []).eval x = true ↔ True := by
  simp [andList, eval]

theorem eval_not_false (f : Fml) (x : ℕ → Bool) : (not f).eval x = true ↔ f.eval x = false := by
  simp [eval]

theorem eval_gtN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k + 1 < 2 ^ w) (x : ℕ → Bool) :
    (not (ltConst fs (nbits w (k + 1)))).eval x = true ↔ k < val fs x := by
  rw [eval_not_iff, eval_ltN hl hk]
  omega

theorem eval_geN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (not (ltConst fs (nbits w k))).eval x = true ↔ k ≤ val fs x := by
  rw [eval_not_iff, eval_ltN hl hk]
  omega

/-- The tapes `fixed j = none` are the indices `frees`. -/
structure FreeSpec (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ) : Prop where
  lt : ∀ j ∈ frees, j < 7
  iff : ∀ j : Fin 7, fixed j = none ↔ (j : ℕ) ∈ frees

/-- The entries `(j, vf)` of `tabs` are the fixed tapes `fixed j = some x`, with `vf` computing
`v = cellCode x S p` on the record `A`. -/
structure TapeSpec (e : ℕ) (A : FieldsF) (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml)) :
    Prop where
  entry : ∀ jv ∈ tabs, ∃ (j : Fin 7) (x : List Sym), jv.1 = j ∧ fixed j = some x ∧
    ∀ x' : ℕ → Bool, jv.2.eval x' = decide ((evalFields A x').v = cellCode x (Sof e) (evalFields A x').p)
  complete : ∀ (j : Fin 7) (x : List Sym), fixed j = some x → ∃ vf, ((j : ℕ), vf) ∈ tabs

variable (e G : ℕ)

/-- `FreeTape`. -/
def freeTapeF (frees : List ℕ) (A : FieldsF) : Fml := orList (frees.map fun j => eqConst A.d (nbits 4 j))

theorem eval_freeTapeF {fixed : Fin 7 → Option (List Sym)} {frees : List ℕ} (hs : FreeSpec fixed frees)
    {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool) :
    (freeTapeF frees A).eval x = true ↔ FreeTape fixed (evalFields A x) := by
  rw [freeTapeF, eval_orList_eq_true]
  simp only [List.mem_map, exists_exists_and_eq_and, FreeTape]
  constructor
  · rintro ⟨j, hj, h⟩
    have hj7 := hs.lt j hj
    refine ⟨⟨j, hj7⟩, (hs.iff _).mpr hj, ?_⟩
    exact (eval_eqN hA.d (by omega) x).mp h
  · rintro ⟨j, hj, h⟩
    exact ⟨j, (hs.iff j).mp hj, (eval_eqN hA.d (by have := j.isLt; omega) x).mpr h⟩

theorem InputsLt.freeTapeF {n : ℕ} (frees : List ℕ) {A : FieldsF} (hA : A.InputsLt n) :
    (freeTapeF frees A).InputsLt n := by
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨j, -, rfl⟩ := hf
  exact InputsLt.eqConst _ hA.d

/-- `t = 0`. -/
def tZeroF (A : FieldsF) : Fml := eqConst A.t (nbits (W e) 0)

theorem eval_tZeroF {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool) :
    (tZeroF e A).eval x = true ↔ (evalFields A x).t = 0 :=
  eval_eqN hA.t (Nat.two_pow_pos _) x

theorem InputsLt.tZeroF {n : ℕ} {A : FieldsF} (hA : A.InputsLt n) : (tZeroF e A).InputsLt n :=
  InputsLt.eqConst _ hA.t

/-! ## The start family -/

section Start

variable (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml))

/-- `StartHead`. -/
def startHeadF (C : CandF) : Fml :=
  andList [unitHeadF e C, sameSignsF C, tZeroF e C.A₁, xnor C.σ₁ (startCellF e C.A₁)]

/-- `StartState`. -/
noncomputable def startStateF (C : CandF) : Fml :=
  andList [unitStateF e C, sameSignsF C, tZeroF e C.A₁,
    xnor C.σ₁ (eqConst C.A₁.q (nbits Qb (qCode (some U.q₀))))]

/-- `StartFixed`, for the tapes `tabs`. -/
def startFixedF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁,
    orList (tabs.map fun jv => and (eqConst C.A₁.d (nbits 4 jv.1)) (xnor C.σ₁ jv.2))]

/-- `StartWork`. -/
def startWorkF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, not (ltConst C.A₁.d (nbits 4 7)),
    xnor C.σ₁ (workValF e C.A₁)]

/-- `StartPred`. -/
noncomputable def startF (C : CandF) : Fml :=
  orList [startHeadF e C, startStateF e C, startFixedF e tabs C, startWorkF e C]

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

theorem eval_startHeadF : (startHeadF e C).eval x = true ↔ StartHead e (evalCand C x) := by
  rw [startHeadF, eval_andList₄, eval_unitHeadF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_sign _ _ _ (eval_startCellF e G hC.A₁ x)]
  rfl

theorem eval_startStateF : (startStateF e C).eval x = true ↔ StartState e (evalCand C x) := by
  rw [startStateF, eval_andList₄, eval_unitStateF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_sign _ _ _ (eval_eqN hC.A₁.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb) x)]
  rfl

theorem eval_startFixedF (hs : TapeSpec e C.A₁ fixed tabs) :
    (startFixedF e tabs C).eval x = true ↔ StartFixed e fixed (evalCand C x) := by
  rw [startFixedF, eval_andList₄, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_orList_eq_true]
  simp only [List.mem_map, exists_exists_and_eq_and, eval_and_iff, eval_xnor_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · rintro ⟨jv, hjv, hd, hσ⟩
    obtain ⟨j, s, hj, hx, hv⟩ := hs.entry jv hjv
    refine ⟨j, s, hx, ?_, ?_⟩
    · rw [← hj]; exact (eval_eqN hC.A₁.d (by rw [hj]; have := j.isLt; omega) x).mp hd
    · show C.σ₁.eval x = _
      rw [hσ, hv]
      rfl
  · rintro ⟨j, s, hx, hd, hσ⟩
    obtain ⟨vf, hvf⟩ := hs.complete j s hx
    obtain ⟨j', s', hj, hx', hv⟩ := hs.entry _ hvf
    have hjj : j' = j := Fin.ext (by simpa using hj.symm)
    subst hjj
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    refine ⟨(j', vf), hvf, (eval_eqN hC.A₁.d (by have := j'.isLt; omega) x).mpr hd, ?_⟩
    show C.σ₁.eval x = _
    rw [hv]
    exact hσ

theorem eval_startWorkF : (startWorkF e C).eval x = true ↔ StartWork e (evalCand C x) := by
  rw [startWorkF, eval_andList₅, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_geN hC.A₁.d (by norm_num), eval_sign _ _ _ (eval_workValF e G hC.A₁ x)]
  rfl

theorem eval_startF (hs : TapeSpec e C.A₁ fixed tabs) :
    (startF e tabs C).eval x = true ↔ StartPred e fixed (evalCand C x) := by
  rw [startF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_startHeadF e G hC, eval_startStateF e G hC, eval_startFixedF e G fixed tabs hC x hs,
    eval_startWorkF e G hC]
  rfl

end Start

section StartInputs

variable {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n) {C : CandF}
  (hC : C.InputsLt n)
include hC

theorem InputsLt.startHeadF : (startHeadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitHeadF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.startCellF e hC.A₁))
    InputsLt.list_nil))))

theorem InputsLt.startStateF : (startStateF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitStateF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.q))
    InputsLt.list_nil))))

include htabs in
theorem InputsLt.startFixedF : (startFixedF e tabs C).InputsLt n := by
  refine InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons ?_ InputsLt.list_nil))))
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨jv, hjv, rfl⟩ := hf
  exact InputsLt.and' (InputsLt.eqConst _ hC.A₁.d) (InputsLt.xnor hC.σ₁ (htabs jv hjv))

theorem InputsLt.startWorkF : (startWorkF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hC.A₁.d))
    (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.workValF e hC.A₁)) InputsLt.list_nil)))))

include htabs in
theorem InputsLt.startF : (startF e tabs C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.startHeadF e hC) (InputsLt.list_cons (InputsLt.startStateF e hC)
    (InputsLt.list_cons (InputsLt.startFixedF e tabs htabs hC) (InputsLt.list_cons (InputsLt.startWorkF e hC)
    InputsLt.list_nil))))

end StartInputs

/-! ## The free family -/

section Free

variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)

/-- `FreeBdry`. -/
def freeBdryF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, freeTapeF frees C.A₁, bdryF e C.A₁,
    xnor C.σ₁ (eqConst C.A₁.v (nbits 3 6))]

/-- `FreeOther`. -/
def freeOtherF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, freeTapeF frees C.A₁, not (bdryF e C.A₁),
    not (eqConst C.A₁.v (nbits 3 0)), not (eqConst C.A₁.v (nbits 3 1)), not (eqConst C.A₁.v (nbits 3 5)),
    not C.σ₁]

/-- `FreeTwo`. -/
def freeTwoF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, freeTapeF frees C.A₁,
    eqConst C.A₁.p (nbits (W e) 2), xnor C.σ₁ (eqConst C.A₁.v (nbits 3 5))]

/-- `FreeOneOf`. -/
def freeOneOfF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, samePosF C.A₁ C.A₂, samePosF C.A₁ C.A₃,
    tZeroF e C.A₁, freeTapeF frees C.A₁, not (bdryF e C.A₁), eqConst C.A₁.v (nbits 3 0),
    eqConst C.A₂.v (nbits 3 1), eqConst C.A₃.v (nbits 3 5), C.σ₁, C.σ₂, C.σ₃]

/-- `FreeNand`. -/
def freeNandF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, samePosF C.A₁ C.A₂, cellEqF C.A₂ C.A₃,
    tZeroF e C.A₁, freeTapeF frees C.A₁, not (bdryF e C.A₁), not (eqFields C.A₁.v C.A₂.v),
    not C.σ₁, not C.σ₂, not C.σ₃]

/-- `FreeBlank`. -/
def freeBlankF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, cellEqF C.A₂ C.A₃, tZeroF e C.A₁,
    freeTapeF frees C.A₁, eqFields C.A₂.t C.A₁.t, eqFields C.A₂.d C.A₁.d,
    not (ltConst C.A₁.p (nbits (W e) 3)), not (bdryF e C.A₂), ltFields C.A₁.p C.A₂.p,
    eqConst C.A₁.v (nbits 3 5), eqConst C.A₂.v (nbits 3 5), not C.σ₁, C.σ₂, C.σ₃]

/-- `FreePred`. -/
def freeF (C : CandF) : Fml :=
  orList [freeBdryF e frees C, freeOtherF e frees C, freeTwoF e frees C, freeOneOfF e frees C,
    freeNandF e frees C, freeBlankF e frees C]

variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC

theorem eval_freeBdryF : (freeBdryF e frees C).eval x = true ↔ FreeBdry e fixed (evalCand C x) := by
  rw [freeBdryF, eval_andList₆, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_freeTapeF e G hs hC.A₁, eval_bdryF e G hC.A₁, eval_sign _ _ _ (eval_eqN hC.A₁.v (by norm_num) x)]
  rfl

theorem eval_freeOtherF : (freeOtherF e frees C).eval x = true ↔ FreeOther e fixed (evalCand C x) := by
  rw [freeOtherF, eval_andList₉, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_freeTapeF e G hs hC.A₁, eval_not_iff, eval_bdryF e G hC.A₁, eval_not_iff,
    eval_eqN hC.A₁.v (by norm_num), eval_not_iff, eval_eqN hC.A₁.v (by norm_num), eval_not_iff,
    eval_eqN hC.A₁.v (by norm_num), eval_not_false]
  rfl

theorem eval_freeTwoF : (freeTwoF e frees C).eval x = true ↔ FreeTwo e fixed (evalCand C x) := by
  rw [freeTwoF, eval_andList₆, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_freeTapeF e G hs hC.A₁, eval_eqN hC.A₁.p (by have := twoS5_lt e; omega),
    eval_sign _ _ _ (eval_eqN hC.A₁.v (by norm_num) x)]
  rfl

theorem eval_freeOneOfF : (freeOneOfF e frees C).eval x = true ↔ FreeOneOf e fixed (evalCand C x) := by
  simp only [freeOneOfF, eval_andList_cons, eval_andList_nil, and_true]
  rw [eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃, eval_samePosF e G hC.A₁ hC.A₂,
    eval_samePosF e G hC.A₁ hC.A₃, eval_tZeroF e G hC.A₁, eval_freeTapeF e G hs hC.A₁, eval_not_iff,
    eval_bdryF e G hC.A₁, eval_eqN hC.A₁.v (by norm_num), eval_eqN hC.A₂.v (by norm_num),
    eval_eqN hC.A₃.v (by norm_num)]
  rfl

theorem eval_freeNandF : (freeNandF e frees C).eval x = true ↔ FreeNand e fixed (evalCand C x) := by
  simp only [freeNandF, eval_andList_cons, eval_andList_nil, and_true]
  rw [eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃, eval_samePosF e G hC.A₁ hC.A₂,
    eval_cellEqF e G hC.A₂ hC.A₃, eval_tZeroF e G hC.A₁, eval_freeTapeF e G hs hC.A₁, eval_not_iff,
    eval_bdryF e G hC.A₁, eval_not_iff, eval_eqF hC.A₁.v hC.A₂.v, eval_not_false, eval_not_false,
    eval_not_false]
  rfl

theorem eval_freeBlankF : (freeBlankF e frees C).eval x = true ↔ FreeBlank e fixed (evalCand C x) := by
  simp only [freeBlankF, eval_andList_cons, eval_andList_nil, and_true]
  rw [eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃, eval_cellEqF e G hC.A₂ hC.A₃,
    eval_tZeroF e G hC.A₁, eval_freeTapeF e G hs hC.A₁, eval_eqF hC.A₂.t hC.A₁.t, eval_eqF hC.A₂.d hC.A₁.d,
    eval_gtN hC.A₁.p (by have := twoS5_lt e; omega), eval_not_iff, eval_bdryF e G hC.A₂,
    eval_ltF hC.A₁.p hC.A₂.p, eval_eqN hC.A₁.v (by norm_num), eval_eqN hC.A₂.v (by norm_num), eval_not_false]
  rfl

theorem eval_freeF : (freeF e frees C).eval x = true ↔ FreePred e fixed (evalCand C x) := by
  rw [freeF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_freeBdryF e G fixed frees hs hC, eval_freeOtherF e G fixed frees hs hC,
    eval_freeTwoF e G fixed frees hs hC, eval_freeOneOfF e G fixed frees hs hC,
    eval_freeNandF e G fixed frees hs hC, eval_freeBlankF e G fixed frees hs hC]
  rfl

end Free

section FreeInputs

variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC

theorem InputsLt.freeBdryF : (freeBdryF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.bdryF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.v))
    InputsLt.list_nil))))))

theorem InputsLt.freeOtherF : (freeOtherF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₁))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqConst _ hC.A₁.v))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqConst _ hC.A₁.v))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqConst _ hC.A₁.v))
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil)))))))))

theorem InputsLt.freeTwoF : (freeTwoF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.p)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.v)) InputsLt.list_nil))))))

theorem InputsLt.freeOneOfF : (freeOneOfF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.samePosF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.samePosF hC.A₁ hC.A₃) (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁)
    (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁) (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₁))
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.v) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₂.v)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₃.v) (InputsLt.list_cons hC.σ₁ (InputsLt.list_cons hC.σ₂
    (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))))))))

theorem InputsLt.freeNandF : (freeNandF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.samePosF hC.A₁ hC.A₂)
    (InputsLt.list_cons (InputsLt.cellEqF hC.A₂ hC.A₃) (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁)
    (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁) (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₁))
    (InputsLt.list_cons (InputsLt.not' (InputsLt.eqFields hC.A₁.v hC.A₂.v))
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) (InputsLt.list_cons (InputsLt.not' hC.σ₂)
    (InputsLt.list_cons (InputsLt.not' hC.σ₃) InputsLt.list_nil))))))))))))

theorem InputsLt.freeBlankF : (freeBlankF e frees C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hC.A₁) (InputsLt.list_cons (InputsLt.isCellF hC.A₂)
    (InputsLt.list_cons (InputsLt.isCellF hC.A₃) (InputsLt.list_cons (InputsLt.cellEqF hC.A₂ hC.A₃)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.freeTapeF frees hC.A₁)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₂.t hC.A₁.t) (InputsLt.list_cons (InputsLt.eqFields hC.A₂.d hC.A₁.d)
    (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hC.A₁.p)) (InputsLt.list_cons (InputsLt.not' (InputsLt.bdryF e hC.A₂))
    (InputsLt.list_cons (InputsLt.ltFields hC.A₁.p hC.A₂.p) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.v)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₂.v) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))))))))))

theorem InputsLt.freeF : (freeF e frees C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.freeBdryF e frees hC) (InputsLt.list_cons (InputsLt.freeOtherF e frees hC)
    (InputsLt.list_cons (InputsLt.freeTwoF e frees hC) (InputsLt.list_cons (InputsLt.freeOneOfF e frees hC)
    (InputsLt.list_cons (InputsLt.freeNandF e frees hC) (InputsLt.list_cons (InputsLt.freeBlankF e frees hC)
    InputsLt.list_nil))))))

end FreeInputs

/-! ## The boundary, emission and final families -/

/-- `BdryCell`. -/
def bdryCellF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, bdryF e C.A₁, xnor C.σ₁ (eqConst C.A₁.v (nbits 3 6))]

/-- `BdryHead`. -/
def bdryHeadF (C : CandF) : Fml :=
  andList [unitHeadF e C, sameSignsF C, bdryF e C.A₁, not C.σ₁]

/-- `BdryPred`. -/
def bdryPredF (C : CandF) : Fml := or (bdryCellF e C) (bdryHeadF e C)

/-- `EmitZero`. -/
def emitZeroF (C : CandF) : Fml :=
  andList [unitEmittedF e C, sameSignsF C, tZeroF e C.A₁, not C.σ₁]

/-- `EmitStep`. -/
def emitStepF (C : CandF) : Fml :=
  andList [isEmittedF e C.A₁, isEmittedF e C.A₂, isEmitOneF e C.A₃, addConstRel C.A₃.t C.A₁.t (nbits (W e) 1),
    eqFields C.A₂.t C.A₃.t, not C.σ₁, C.σ₂, C.σ₃]

/-- `EmitMono`. -/
def emitMonoF (C : CandF) : Fml :=
  andList [isEmittedF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, ltConst C.A₁.t (nbits (W e) (Sof e)),
    addConstRel C.A₁.t C.A₂.t (nbits (W e) 1), eqFields C.A₃.t C.A₂.t, not C.σ₁, C.σ₂, C.σ₃]

/-- `EmitOne`. -/
def emitOneF (C : CandF) : Fml :=
  andList [isEmitOneF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, addConstRel C.A₁.t C.A₂.t (nbits (W e) 1),
    eqFields C.A₃.t C.A₂.t, not C.σ₁, C.σ₂, C.σ₃]

/-- `EmitOnce`. -/
def emitOnceF (C : CandF) : Fml :=
  andList [isEmitOneF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, eqFields C.A₂.t C.A₁.t,
    eqFields C.A₃.t C.A₂.t, not C.σ₁, not C.σ₂, not C.σ₃]

/-- `EmitBad`. -/
def emitBadF (C : CandF) : Fml := andList [unitEmitBadF e C, sameSignsF C, not C.σ₁]

/-- `EmitPred`. -/
def emitPredF (C : CandF) : Fml :=
  orList [emitZeroF e C, emitStepF e C, emitMonoF e C, emitOneF e C, emitOnceF e C, emitBadF e C]

/-- `FinalState`. -/
noncomputable def finalStateF (C : CandF) : Fml :=
  andList [unitStateF e C, sameSignsF C, eqConst C.A₁.t (nbits (W e) (Sof e)),
    eqConst C.A₁.q (nbits Qb (qCode none)), C.σ₁]

/-- `FinalEmitted`. -/
def finalEmittedF (C : CandF) : Fml :=
  andList [unitEmittedF e C, sameSignsF C, eqConst C.A₁.t (nbits (W e) (Sof e)), C.σ₁]

/-- `FinalPred`. -/
noncomputable def finalPredF (C : CandF) : Fml := or (finalStateF e C) (finalEmittedF e C)

section BEF

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

theorem eval_bdryCellF : (bdryCellF e C).eval x = true ↔ BdryCell e (evalCand C x) := by
  rw [bdryCellF, eval_andList₄, eval_unitCellF e G hC, eval_sameSignsF, eval_bdryF e G hC.A₁,
    eval_sign _ _ _ (eval_eqN hC.A₁.v (by norm_num) x)]
  rfl

theorem eval_bdryHeadF : (bdryHeadF e C).eval x = true ↔ BdryHead e (evalCand C x) := by
  rw [bdryHeadF, eval_andList₄, eval_unitHeadF e G hC, eval_sameSignsF, eval_bdryF e G hC.A₁, eval_not_false]
  rfl

theorem eval_bdryPredF : (bdryPredF e C).eval x = true ↔ BdryPred e (evalCand C x) := by
  rw [bdryPredF, eval_or_iff, eval_bdryCellF e G hC, eval_bdryHeadF e G hC]
  rfl

theorem eval_emitZeroF : (emitZeroF e C).eval x = true ↔ EmitZero e (evalCand C x) := by
  rw [emitZeroF, eval_andList₄, eval_unitEmittedF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁, eval_not_false]
  rfl

theorem eval_emitStepF : (emitStepF e C).eval x = true ↔ EmitStep e (evalCand C x) := by
  rw [emitStepF, eval_andList₈, eval_isEmittedF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmitOneF e G hC.A₃,
    eval_addN hC.A₃.t hC.A₁.t (by have := twoS5_lt e; omega), eval_eqF hC.A₂.t hC.A₃.t, eval_not_false]
  rfl

theorem eval_emitMonoF : (emitMonoF e C).eval x = true ↔ EmitMono e (evalCand C x) := by
  rw [emitMonoF, eval_andList₉, eval_isEmittedF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmittedF e G hC.A₃,
    eval_ltN hC.A₁.t (S_lt_two_pow e), eval_addN hC.A₁.t hC.A₂.t (by have := twoS5_lt e; omega),
    eval_eqF hC.A₃.t hC.A₂.t, eval_not_false]
  rfl

theorem eval_emitOneF : (emitOneF e C).eval x = true ↔ EmitOne e (evalCand C x) := by
  rw [emitOneF, eval_andList₈, eval_isEmitOneF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmittedF e G hC.A₃,
    eval_addN hC.A₁.t hC.A₂.t (by have := twoS5_lt e; omega), eval_eqF hC.A₃.t hC.A₂.t, eval_not_false]
  rfl

theorem eval_emitOnceF : (emitOnceF e C).eval x = true ↔ EmitOnce e (evalCand C x) := by
  rw [emitOnceF, eval_andList₈, eval_isEmitOneF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmittedF e G hC.A₃,
    eval_eqF hC.A₂.t hC.A₁.t, eval_eqF hC.A₃.t hC.A₂.t, eval_not_false, eval_not_false, eval_not_false]
  rfl

theorem eval_emitBadF : (emitBadF e C).eval x = true ↔ EmitBad e (evalCand C x) := by
  rw [emitBadF, eval_andList₃, eval_unitEmitBadF e G hC, eval_sameSignsF, eval_not_false]
  rfl

theorem eval_emitPredF : (emitPredF e C).eval x = true ↔ EmitPred e (evalCand C x) := by
  rw [emitPredF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_emitZeroF e G hC, eval_emitStepF e G hC, eval_emitMonoF e G hC, eval_emitOneF e G hC,
    eval_emitOnceF e G hC, eval_emitBadF e G hC]
  rfl

theorem eval_finalStateF : (finalStateF e C).eval x = true ↔ FinalState e (evalCand C x) := by
  rw [finalStateF, eval_andList₅, eval_unitStateF e G hC, eval_sameSignsF, eval_eqN hC.A₁.t (S_lt_two_pow e),
    eval_eqN hC.A₁.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb)]
  rfl

theorem eval_finalEmittedF : (finalEmittedF e C).eval x = true ↔ FinalEmitted e (evalCand C x) := by
  rw [finalEmittedF, eval_andList₄, eval_unitEmittedF e G hC, eval_sameSignsF, eval_eqN hC.A₁.t (S_lt_two_pow e)]
  rfl

theorem eval_finalPredF : (finalPredF e C).eval x = true ↔ FinalPred e (evalCand C x) := by
  rw [finalPredF, eval_or_iff, eval_finalStateF e G hC, eval_finalEmittedF e G hC]
  rfl

end BEF

section BEFInputs

variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC

theorem InputsLt.bdryCellF : (bdryCellF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.bdryF e hC.A₁) (InputsLt.list_cons (InputsLt.xnor hC.σ₁ (InputsLt.eqConst _ hC.A₁.v))
    InputsLt.list_nil))))

theorem InputsLt.bdryHeadF : (bdryHeadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitHeadF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.bdryF e hC.A₁) (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil))))

theorem InputsLt.bdryPredF : (bdryPredF e C).InputsLt n :=
  InputsLt.or' (InputsLt.bdryCellF e hC) (InputsLt.bdryHeadF e hC)

theorem InputsLt.emitZeroF : (emitZeroF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitEmittedF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁) (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil))))

theorem InputsLt.emitStepF : (emitStepF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmittedF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmitOneF hC.A₃) (InputsLt.list_cons (InputsLt.addConstRel _ hC.A₃.t hC.A₁.t)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₂.t hC.A₃.t) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))

theorem InputsLt.emitMonoF : (emitMonoF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmittedF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.ltConst _ hC.A₁.t)
    (InputsLt.list_cons (InputsLt.addConstRel _ hC.A₁.t hC.A₂.t) (InputsLt.list_cons (InputsLt.eqFields hC.A₃.t hC.A₂.t)
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil)))))))))

theorem InputsLt.emitOneF : (emitOneF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitOneF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.addConstRel _ hC.A₁.t hC.A₂.t)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₃.t hC.A₂.t) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons hC.σ₂ (InputsLt.list_cons hC.σ₃ InputsLt.list_nil))))))))

theorem InputsLt.emitOnceF : (emitOnceF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitOneF hC.A₁) (InputsLt.list_cons (InputsLt.isEmittedF hC.A₂)
    (InputsLt.list_cons (InputsLt.isEmittedF hC.A₃) (InputsLt.list_cons (InputsLt.eqFields hC.A₂.t hC.A₁.t)
    (InputsLt.list_cons (InputsLt.eqFields hC.A₃.t hC.A₂.t) (InputsLt.list_cons (InputsLt.not' hC.σ₁)
    (InputsLt.list_cons (InputsLt.not' hC.σ₂) (InputsLt.list_cons (InputsLt.not' hC.σ₃) InputsLt.list_nil))))))))

theorem InputsLt.emitBadF : (emitBadF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitEmitBadF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.not' hC.σ₁) InputsLt.list_nil)))

theorem InputsLt.emitPredF : (emitPredF e C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.emitZeroF e hC) (InputsLt.list_cons (InputsLt.emitStepF e hC)
    (InputsLt.list_cons (InputsLt.emitMonoF e hC) (InputsLt.list_cons (InputsLt.emitOneF e hC)
    (InputsLt.list_cons (InputsLt.emitOnceF e hC) (InputsLt.list_cons (InputsLt.emitBadF e hC) InputsLt.list_nil))))))

theorem InputsLt.finalStateF : (finalStateF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitStateF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.t) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.q)
    (InputsLt.list_cons hC.σ₁ InputsLt.list_nil)))))

theorem InputsLt.finalEmittedF : (finalEmittedF e C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitEmittedF e hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.t) (InputsLt.list_cons hC.σ₁ InputsLt.list_nil))))

theorem InputsLt.finalPredF : (finalPredF e C).InputsLt n :=
  InputsLt.or' (InputsLt.finalStateF e hC) (InputsLt.finalEmittedF e hC)

end BEFInputs

/-! ## The five explicit families -/

/-- `MainPred`. -/
noncomputable def mainF (tabs : List (ℕ × Fml)) (frees : List ℕ) (C : CandF) : Fml :=
  orList [startF e tabs C, freeF e frees C, bdryPredF e C, emitPredF e C, finalPredF e C]

theorem eval_mainF {fixed : Fin 7 → Option (List Sym)} {tabs : List (ℕ × Fml)} {frees : List ℕ}
    {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool) (ht : TapeSpec e C.A₁ fixed tabs)
    (hf : FreeSpec fixed frees) :
    (mainF e tabs frees C).eval x = true ↔ MainPred e fixed (evalCand C x) := by
  rw [mainF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_startF e G fixed tabs hC x ht, eval_freeF e G fixed frees hf hC, eval_bdryPredF e G hC,
    eval_emitPredF e G hC, eval_finalPredF e G hC]
  rfl

theorem InputsLt.mainF {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n)
    (frees : List ℕ) {C : CandF} (hC : C.InputsLt n) : (mainF e tabs frees C).InputsLt n :=
  InputsLt.orList _ (InputsLt.list_cons (InputsLt.startF e tabs htabs hC) (InputsLt.list_cons (InputsLt.freeF e frees hC)
    (InputsLt.list_cons (InputsLt.bdryPredF e hC) (InputsLt.list_cons (InputsLt.emitPredF e hC)
    (InputsLt.list_cons (InputsLt.finalPredF e hC) InputsLt.list_nil)))))


/-! ## The window family

The templates of the check circuit enter the formula as data: a window variable is a
*descriptor* (`WDesc`: a one-hot kind, and the tape, offset, value and state as bit strings),
a literal spec an `LDesc`, so that the describer program builds the window formula by a fold
over a constant list of descriptors, never inspecting a `WinVar` or a `Gate`. -/

/-- The one-hot vector of length `n` with its `k`-th entry set. -/
def oneHot (n k : ℕ) : List Bool := (List.range n).map fun i => decide (i = k)

@[simp] theorem length_oneHot (n k : ℕ) : (oneHot n k).length = n := by simp [oneHot]

theorem getElem_oneHot (n k i : ℕ) (h : i < (oneHot n k).length) : (oneHot n k)[i] = decide (i = k) := by
  simp [oneHot]

/-- Select by a one-hot vector: `⋁ᵢ bᵢ ∧ fᵢ`. -/
def selectF (hot : List Bool) (fs : List Fml) : Fml :=
  orList (List.zipWith (fun b f => and (const b) f) hot fs)

theorem eval_selectF (hot : List Bool) (fs : List Fml) (x : ℕ → Bool) :
    (selectF hot fs).eval x = true ↔
      ∃ i, ∃ h : i < (List.zipWith (fun b f => and (const b) f) hot fs).length,
        hot[i]'(List.lt_length_left_of_zipWith h) = true ∧
          (fs[i]'(List.lt_length_right_of_zipWith h)).eval x = true := by
  rw [selectF, eval_orList_eq_true]
  constructor
  · rintro ⟨f, hf, h⟩
    rw [List.mem_iff_getElem] at hf
    obtain ⟨i, hi, rfl⟩ := hf
    rw [List.getElem_zipWith, eval_and_iff] at h
    exact ⟨i, hi, by simpa [eval] using h.1, h.2⟩
  · rintro ⟨i, hi, hb, hf⟩
    refine ⟨_, List.getElem_mem hi, ?_⟩
    rw [List.getElem_zipWith, eval_and_iff]
    exact ⟨by simp [eval, hb], hf⟩

theorem eval_selectF_oneHot (n k : ℕ) (fs : List Fml) (hl : fs.length = n) (hk : k < n) (x : ℕ → Bool) :
    (selectF (oneHot n k) fs).eval x = true ↔ (fs[k]'(by omega)).eval x = true := by
  rw [eval_selectF]
  have hlen : (List.zipWith (fun b f => and (const b) f) (oneHot n k) fs).length = n := by
    simp [List.length_zipWith, hl]
  constructor
  · rintro ⟨i, hi, hb, hf⟩
    rw [getElem_oneHot, decide_eq_true_iff] at hb
    subst hb
    exact hf
  · intro hf
    exact ⟨k, by omega, by rw [getElem_oneHot]; simp, hf⟩

theorem eval_selectF_none (n : ℕ) (fs : List Fml) (x : ℕ → Bool) :
    (selectF (List.replicate n false) fs).eval x = false := by
  rw [← Bool.not_eq_true, eval_selectF]
  rintro ⟨i, hi, hb, -⟩
  rw [List.getElem_replicate] at hb
  cases hb

theorem InputsLt.selectF {n : ℕ} (hot : List Bool) {fs : List Fml} (hfs : ∀ f ∈ fs, f.InputsLt n) :
    (selectF hot fs).InputsLt n := by
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_iff_getElem] at hf
  obtain ⟨i, hi, rfl⟩ := hf
  rw [List.getElem_zipWith]
  exact InputsLt.and' trivial (hfs _ (List.getElem_mem _))

/-- A window variable as data: the kind (one-hot over `cellPre`, `headPre`, `cellPost`,
`headPost`, `statePre`, `statePost`, `emitOne`, `emitBad`), the tape (4 bits, and one-hot over
the 13 tapes), the offset (3 bits), the value (3 bits), the state (`Qb` bits). -/
structure WDesc where
  kind : List Bool
  d : BitStr
  dHot : List Bool
  δ : BitStr
  v : BitStr
  q : BitStr

/-- The descriptor of a window variable. -/
noncomputable def wvDesc : WinVar 7 6 Sym Ctl → WDesc
  | .cellPre d δ v =>
    ⟨oneHot 8 0, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 δ, nbits 3 (symCode v), nbits Qb 0⟩
  | .headPre d δ => ⟨oneHot 8 1, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 δ, nbits 3 0, nbits Qb 0⟩
  | .cellPost d v =>
    ⟨oneHot 8 2, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 2, nbits 3 (symCode v), nbits Qb 0⟩
  | .headPost d => ⟨oneHot 8 3, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 2, nbits 3 0, nbits Qb 0⟩
  | .statePre q => ⟨oneHot 8 4, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb (qCode q)⟩
  | .statePost q => ⟨oneHot 8 5, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb (qCode q)⟩
  | .emitOne => ⟨oneHot 8 6, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb 0⟩
  | .emitBad => ⟨oneHot 8 7, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb 0⟩

/-- The descriptor of nothing: no kind. -/
def badDesc : WDesc := ⟨List.replicate 8 false, [], [], [], [], []⟩

/-- `p = js_d + δ`, the tape `d` given one-hot. -/
def posF (Fa A : FieldsF) (dHot : List Bool) (δ : BitStr) : Fml :=
  selectF dHot ((List.ofFn Fa.js).map fun js => addConstRel js A.p (padBits (W e) δ))

/-- `WinMatch`, on a descriptor. -/
def winMatchN (Fa A : FieldsF) (w : WDesc) : Fml :=
  selectF w.kind [
    andList [isCellF e A, eqFields A.t Fa.t, eqConst A.d w.d, posF e Fa A w.dHot w.δ, eqConst A.v w.v],
    andList [isHeadF e A, eqFields A.t Fa.t, eqConst A.d w.d, posF e Fa A w.dHot w.δ],
    andList [isCellF e A, addConstRel Fa.t A.t (nbits (W e) 1), eqConst A.d w.d, posF e Fa A w.dHot w.δ,
      eqConst A.v w.v],
    andList [isHeadF e A, addConstRel Fa.t A.t (nbits (W e) 1), eqConst A.d w.d, posF e Fa A w.dHot w.δ],
    andList [isStateF e A, eqFields A.t Fa.t, eqConst A.q w.q],
    andList [isStateF e A, addConstRel Fa.t A.t (nbits (W e) 1), eqConst A.q w.q],
    andList [isEmitOneF e A, eqFields A.t Fa.t],
    andList [isEmitBadF e A, eqFields A.t Fa.t]]

/-- `SpecMatch` for a gate spec, with the gate index as bits. -/
def auxMatchN (Fa A : FieldsF) (u : BitStr) : Fml :=
  andList ([isAuxF e G A, eqFields A.t Fa.t, eqConst A.g u] ++
    List.ofFn fun k : Fin 13 => eqFields (A.js k) (Fa.js k))

/-- A literal spec as data. -/
structure LDesc where
  isAux : Bool
  u : BitStr
  w : WDesc

/-- `SpecMatch`, on a descriptor. -/
def specMatchN (Fa A : FieldsF) (l : LDesc) : Fml :=
  mux (const l.isAux) (auxMatchN e G Fa A l.u) (winMatchN e Fa A l.w)

/-- The descriptors of the window variables, in the canonical order. -/
noncomputable def wvDescs : List WDesc :=
  (List.finRange (winCard 7 6 Sym Ctl)).map fun i => wvDesc ((Fintype.equivFin _).symm i)

/-- The descriptor of a spec. -/
noncomputable def LitSpec.toN : LitSpec → LDesc
  | .aux u => ⟨true, nbits (Gb G) u, badDesc⟩
  | .win n => ⟨false, [], wvDescs.getD n badDesc⟩

/-- A template as data. -/
abbrev NTpl := (LDesc × Bool) × (LDesc × Bool) × (LDesc × Bool)

/-- The descriptor of a template. -/
noncomputable def Tpl.toN (tp : Tpl) : NTpl :=
  ((LitSpec.toN G tp.1.1, tp.1.2), (LitSpec.toN G tp.2.1.1, tp.2.1.2), (LitSpec.toN G tp.2.2.1, tp.2.2.2))

/-- `TplMatch`, on a descriptor. -/
def tplN (tp : NTpl) (C : CandF) : Fml :=
  andList [specMatchN e G C.A₃ C.A₁ tp.1.1, xnor C.σ₁ (const tp.1.2), specMatchN e G C.A₃ C.A₂ tp.2.1.1,
    xnor C.σ₂ (const tp.2.1.2), specMatchN e G C.A₃ C.A₃ tp.2.2.1, xnor C.σ₃ (const tp.2.2.2)]

/-- The template descriptors of the gates `gs`, numbered from `g₀`. -/
noncomputable def tplsFrom : ℕ → List Gate → List (List NTpl)
  | _, [] => []
  | g, gate :: gs => (gateTemplates g gate).map (Tpl.toN G) :: tplsFrom (g + 1) gs

/-- The template descriptors of the check circuit: the constant of the describer. -/
noncomputable def tplsOf (chk : Circuit) : List (List NTpl) := tplsFrom G 0 chk.gates

/-- `WindowGates`, on the descriptors `tpls`. -/
def windowGatesN (tpls : List (List NTpl)) (C : CandF) : Fml :=
  orList (tpls.map fun l => orList (l.map fun tp => tplN e G tp C))

/-- `WindowOut`. -/
def windowOutF (C : CandF) : Fml :=
  andList [unitAuxF e G C, sameSignsF C, eqConst C.A₁.g (nbits (Gb G) (G - 1)), C.σ₁]

/-- `WindowPred`. -/
def windowN (tpls : List (List NTpl)) (C : CandF) : Fml := or (windowGatesN e G tpls C) (windowOutF e G C)

section WindowEval

variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA

theorem eval_posF (d : Tape 7 6) (δ : ℕ) (hδ : δ < 8) :
    (posF e Fa A (oneHot 13 (tapeCode d)) (nbits 3 δ)).eval x = true ↔
      val A.p x = val (Fa.js ⟨tapeCode d, tapeCode_lt d⟩) x + δ := by
  have hS := twoS5_lt e
  rw [posF, eval_selectF_oneHot 13 _ _ (by simp) (tapeCode_lt d), List.getElem_map, List.getElem_ofFn]
  have hpad : (padBits (W e) (nbits 3 δ)).length = W e := length_padBits _ _ (by rw [length_nbits]; unfold W; omega)
  rw [eval_addConstRel_iff _ _ _ (by rw [hFa.js, hpad]) (by rw [hFa.js, hA.p]), bitsVal_padBits,
    bitsVal_nbits_of_lt hδ]

theorem eval_winMatchN (wv : WinVar 7 6 Sym Ctl) :
    (winMatchN e Fa A (wvDesc wv)).eval x = true ↔ WinMatch e (evalFields Fa x) wv (evalFields A x) := by
  have hS := twoS5_lt e
  cases wv with
  | cellPre d δ v =>
    rw [wvDesc]
    rw [winMatchN]
    rw [eval_selectF_oneHot 8 0 _ rfl (by norm_num)]
    rw [WinMatch]
    simp only [List.getElem_cons_zero]
    rw [eval_andList₅, eval_isCellF e G hA, eval_eqF hA.t hFa.t, eval_eqN hA.d (by have := tapeCode_lt d; omega),
      eval_posF e G hFa hA x d δ (by have := δ.isLt; omega), eval_eqN hA.v (by have := symCode_lt v; omega)]
    rfl
  | headPre d δ =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 1 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₄, eval_isHeadF e G hA, eval_eqF hA.t hFa.t, eval_eqN hA.d (by have := tapeCode_lt d; omega),
      eval_posF e G hFa hA x d δ (by have := δ.isLt; omega)]
    rfl
  | cellPost d v =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 2 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₅, eval_isCellF e G hA, eval_addN hFa.t hA.t (by omega),
      eval_eqN hA.d (by have := tapeCode_lt d; omega), eval_posF e G hFa hA x d 2 (by norm_num),
      eval_eqN hA.v (by have := symCode_lt v; omega)]
    rfl
  | headPost d =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 3 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₄, eval_isHeadF e G hA, eval_addN hFa.t hA.t (by omega),
      eval_eqN hA.d (by have := tapeCode_lt d; omega), eval_posF e G hFa hA x d 2 (by norm_num)]
    rfl
  | statePre q =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 4 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₃, eval_isStateF e G hA, eval_eqF hA.t hFa.t,
      eval_eqN hA.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb)]
    rfl
  | statePost q =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 5 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₃, eval_isStateF e G hA, eval_addN hFa.t hA.t (by omega),
      eval_eqN hA.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb)]
    rfl
  | emitOne =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 6 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₂, eval_isEmitOneF e G hA, eval_eqF hA.t hFa.t]
    rfl
  | emitBad =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 7 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₂, eval_isEmitBadF e G hA, eval_eqF hA.t hFa.t]
    rfl

omit hFa hA in
theorem eval_winMatchN_bad : (winMatchN e Fa A badDesc).eval x = false := by
  rw [winMatchN, badDesc]
  exact eval_selectF_none 8 _ x

theorem eval_auxMatchN (u : ℕ) (hu : u < G) :
    (auxMatchN e G Fa A (nbits (Gb G) u)).eval x = true ↔
      SpecMatch e G (evalFields Fa x) (.aux u) (evalFields A x) := by
  simp only [auxMatchN, SpecMatch, eval_andList_eq_true, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false, evalFields]
  constructor
  · intro h
    refine ⟨(eval_isAuxF e G hA x).mp (h _ (Or.inl (Or.inl rfl))),
      (eval_eqF hA.t hFa.t x).mp (h _ (Or.inl (Or.inr (Or.inl rfl)))),
      fun k => (eval_eqF (hA.js k) (hFa.js k) x).mp (h _ (Or.inr ⟨k, rfl⟩)),
      (eval_eqN hA.g (lt_trans hu (G_lt_two_pow_Gb G)) x).mp (h _ (Or.inl (Or.inr (Or.inr rfl))))⟩
  · rintro ⟨h1, h2, h3, h4⟩ f hf
    rcases hf with (rfl | rfl | rfl) | ⟨k, rfl⟩
    · exact (eval_isAuxF e G hA x).mpr h1
    · exact (eval_eqF hA.t hFa.t x).mpr h2
    · exact (eval_eqN hA.g (lt_trans hu (G_lt_two_pow_Gb G)) x).mpr h4
    · exact (eval_eqF (hA.js k) (hFa.js k) x).mpr (h3 k)

theorem eval_specMatchN_aux (u : ℕ) (hu : u < G) :
    (specMatchN e G Fa A (LitSpec.toN G (.aux u))).eval x = true ↔
      SpecMatch e G (evalFields Fa x) (.aux u) (evalFields A x) := by
  rw [LitSpec.toN, specMatchN, eval_mux]
  simp only [eval, if_true]
  exact eval_auxMatchN e G hFa hA x u hu

omit hFa hA in
theorem wvDescs_getD (n : ℕ) :
    wvDescs.getD n badDesc =
      if h : n < winCard 7 6 Sym Ctl then wvDesc ((Fintype.equivFin _).symm ⟨n, h⟩) else badDesc := by
  rw [wvDescs, List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by rw [List.length_finRange]; exact h), List.getElem_finRange]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_finRange]; omega)]
    rfl

theorem eval_specMatchN_win (n : ℕ) :
    (specMatchN e G Fa A (LitSpec.toN G (.win n))).eval x = true ↔
      SpecMatch e G (evalFields Fa x) (.win n) (evalFields A x) := by
  rw [LitSpec.toN, specMatchN, eval_mux]
  simp only [eval, Bool.false_eq_true, if_false]
  rw [wvDescs_getD, SpecMatch]
  by_cases h : n < winCard 7 6 Sym Ctl
  · rw [dif_pos h, eval_winMatchN e G hFa hA]
    exact ⟨fun m => ⟨h, m⟩, fun ⟨_, m⟩ => m⟩
  · rw [dif_neg h, eval_winMatchN_bad]
    simp [h]

theorem eval_specMatchN (sp : LitSpec) (hsp : ∀ u, sp = .aux u → u < G) :
    (specMatchN e G Fa A (LitSpec.toN G sp)).eval x = true ↔
      SpecMatch e G (evalFields Fa x) sp (evalFields A x) := by
  cases sp with
  | aux u => exact eval_specMatchN_aux e G hFa hA x u (hsp u rfl)
  | win n => exact eval_specMatchN_win e G hFa hA x n

end WindowEval

section WindowEval'

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

theorem eval_tplN (tp : Tpl) (hsp : ∀ sp, (sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) → ∀ u, sp = .aux u → u < G) :
    (tplN e G (Tpl.toN G tp) C).eval x = true ↔ TplMatch e G tp (evalCand C x) := by
  rw [tplN, Tpl.toN, TplMatch, eval_andList₆, eval_specMatchN e G hC.A₃ hC.A₁ x _ (hsp _ (Or.inl rfl)),
    eval_specMatchN e G hC.A₃ hC.A₂ x _ (hsp _ (Or.inr (Or.inl rfl))),
    eval_specMatchN e G hC.A₃ hC.A₃ x _ (hsp _ (Or.inr (Or.inr rfl))), eval_signConst, eval_signConst,
    eval_signConst]
  rfl

omit hC in
theorem mem_tplsFrom (gs : List Gate) : ∀ (g₀ : ℕ) (l : List NTpl), l ∈ tplsFrom G g₀ gs ↔
    ∃ i, ∃ h : i < gs.length, l = (gateTemplates (g₀ + i) gs[i]).map (Tpl.toN G) := by
  induction gs with
  | nil => intro g₀ l; simp [tplsFrom]
  | cons gate gs ih =>
    intro g₀ l
    rw [tplsFrom, List.mem_cons, ih (g₀ + 1)]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp [Nat.add_assoc, Nat.add_comm 1 i]⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => exact Or.inl (by simp)
      | succ i => exact Or.inr ⟨i, by simp at hi; omega, by simp [Nat.add_assoc, Nat.add_comm 1 i]⟩

theorem eval_windowGatesN (chk : Circuit) (hG : G = chk.gates.length) (hC' : chk.RefsLt) (hin : chk.InputsLt)
    (hinp : chk.inputs = winCard 7 6 Sym Ctl) :
    (windowGatesN e G (tplsOf G chk) C).eval x = true ↔ WindowGates e G chk (evalCand C x) := by
  subst hG
  rw [windowGatesN, eval_orList_eq_true, WindowGates, tplsOf]
  simp only [List.mem_map, mem_tplsFrom, Nat.zero_add]
  constructor
  · rintro ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, h⟩
    rw [eval_orList_eq_true] at h
    obtain ⟨_, htp, h⟩ := h
    rw [List.mem_map] at htp
    obtain ⟨_, htp, rfl⟩ := htp
    rw [List.mem_map] at htp
    obtain ⟨tp, htp, rfl⟩ := htp
    refine ⟨⟨i, hi⟩, tp, htp, (eval_tplN e _ hC x tp ?_).mp h⟩
    intro sp hsp u hu
    rcases spec_lt chk hC' hin hinp ⟨i, hi⟩ tp htp sp hsp with ⟨u', hu', hlt⟩ | ⟨i', hi', -⟩
    · rw [hu] at hu'; cases hu'; exact hlt
    · rw [hu] at hi'; cases hi'
  · rintro ⟨g, tp, htp, h⟩
    refine ⟨_, ⟨_, ⟨g, g.isLt, rfl⟩, rfl⟩, ?_⟩
    rw [eval_orList_eq_true]
    refine ⟨_, List.mem_map_of_mem (List.mem_map_of_mem htp), (eval_tplN e _ hC x tp ?_).mpr h⟩
    intro sp hsp u hu
    rcases spec_lt chk hC' hin hinp g tp htp sp hsp with ⟨u', hu', hlt⟩ | ⟨i', hi', -⟩
    · rw [hu] at hu'; cases hu'; exact hlt
    · rw [hu] at hi'; cases hi'

theorem eval_windowOutF : (windowOutF e G C).eval x = true ↔ WindowOut e G (evalCand C x) := by
  rw [windowOutF, eval_andList₄, eval_unitAuxF e G hC, eval_sameSignsF,
    eval_eqN hC.A₁.g (lt_of_le_of_lt (Nat.sub_le G 1) (G_lt_two_pow_Gb G))]
  rfl

theorem eval_windowN (chk : Circuit) (hG : G = chk.gates.length) (hC' : chk.RefsLt) (hin : chk.InputsLt)
    (hinp : chk.inputs = winCard 7 6 Sym Ctl) :
    (windowN e G (tplsOf G chk) C).eval x = true ↔ WindowPred e G chk (evalCand C x) := by
  rw [windowN, eval_or_iff, eval_windowGatesN e G hC x chk hG hC' hin hinp, eval_windowOutF e G hC]
  rfl

end WindowEval'

section WindowInputs

variable {n : ℕ}

theorem InputsLt.posF {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (dHot : List Bool)
    (δ : BitStr) : (posF e Fa A dHot δ).InputsLt n := by
  refine InputsLt.selectF _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨js, hjs, rfl⟩ := hf
  rw [List.mem_ofFn] at hjs
  obtain ⟨k, rfl⟩ := hjs
  exact InputsLt.addConstRel _ (hFa.js k) hA.p

theorem InputsLt.winMatchN {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (w : WDesc) :
    (winMatchN e Fa A w).InputsLt n := by
  refine InputsLt.selectF _ ?_
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.v) InputsLt.list_nil)))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isHeadF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _) InputsLt.list_nil))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isCellF hA) (InputsLt.list_cons (InputsLt.addConstRel _ hFa.t hA.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.v) InputsLt.list_nil)))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isHeadF hA) (InputsLt.list_cons (InputsLt.addConstRel _ hFa.t hA.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.d) (InputsLt.list_cons (InputsLt.posF e hFa hA _ _) InputsLt.list_nil))))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isStateF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.q) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isStateF hA) (InputsLt.list_cons (InputsLt.addConstRel _ hFa.t hA.t)
      (InputsLt.list_cons (InputsLt.eqConst _ hA.q) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitOneF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.isEmitBadF hA) (InputsLt.list_cons (InputsLt.eqFields hA.t hFa.t)
      InputsLt.list_nil))

theorem InputsLt.auxMatchN {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (u : BitStr) :
    (auxMatchN e G Fa A u).InputsLt n := by
  refine InputsLt.andList _ ?_
  intro f hf
  rw [List.mem_append, List.mem_ofFn] at hf
  rcases hf with hf | ⟨k, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact InputsLt.isAuxF hA
    · exact InputsLt.eqFields hA.t hFa.t
    · exact InputsLt.eqConst _ hA.g
  · exact InputsLt.eqFields (hA.js k) (hFa.js k)

theorem InputsLt.specMatchN {Fa A : FieldsF} (hFa : Fa.InputsLt n) (hA : A.InputsLt n) (l : LDesc) :
    (specMatchN e G Fa A l).InputsLt n :=
  InputsLt.mux trivial (InputsLt.auxMatchN e G hFa hA _) (InputsLt.winMatchN e hFa hA _)

theorem InputsLt.tplN {C : CandF} (hC : C.InputsLt n) (tp : NTpl) : (tplN e G tp C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.specMatchN e G hC.A₃ hC.A₁ _)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₁ trivial) (InputsLt.list_cons (InputsLt.specMatchN e G hC.A₃ hC.A₂ _)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₂ trivial) (InputsLt.list_cons (InputsLt.specMatchN e G hC.A₃ hC.A₃ _)
    (InputsLt.list_cons (InputsLt.xnor hC.σ₃ trivial) InputsLt.list_nil))))))

theorem InputsLt.windowGatesN {C : CandF} (hC : C.InputsLt n) (tpls : List (List NTpl)) :
    (windowGatesN e G tpls C).InputsLt n := by
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨l, -, rfl⟩ := hf
  refine InputsLt.orList _ ?_
  intro f hf
  rw [List.mem_map] at hf
  obtain ⟨tp, -, rfl⟩ := hf
  exact InputsLt.tplN e G hC tp

theorem InputsLt.windowOutF {C : CandF} (hC : C.InputsLt n) : (windowOutF e G C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitAuxF e G hC) (InputsLt.list_cons (InputsLt.sameSignsF hC)
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.g) (InputsLt.list_cons hC.σ₁ InputsLt.list_nil))))

theorem InputsLt.windowN {C : CandF} (hC : C.InputsLt n) (tpls : List (List NTpl)) :
    (windowN e G tpls C).InputsLt n :=
  InputsLt.or' (InputsLt.windowGatesN e G hC tpls) (InputsLt.windowOutF e G hC)

end WindowInputs

/-! ## The whole tableau -/

/-- The formula of the tableau on a candidate: the five explicit families or the window family. -/
noncomputable def tableauF (tabs : List (ℕ × Fml)) (frees : List ℕ) (tpls : List (List NTpl)) (C : CandF) : Fml :=
  or (mainF e tabs frees C) (windowN e G tpls C)

/-- **The tableau formula is exact**: it accepts a candidate iff the candidate decodes to a
clause of `tableau U 0 1 S fixed chk`. -/
theorem eval_tableauF {fixed : Fin 7 → Option (List Sym)} {tabs : List (ℕ × Fml)} {frees : List ℕ}
    {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool) (ht : TapeSpec e C.A₁ fixed tabs)
    (hf : FreeSpec fixed frees) (chk : Circuit) (hG : G = chk.gates.length) (hC' : chk.RefsLt)
    (hin : chk.InputsLt) (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ []) :
    (tableauF e G tabs frees (tplsOf G chk) C).eval x = true ↔
      ∃ cl ∈ tableau U Sym.zero Sym.one (Sof e) fixed chk, (evalCand C x).Dec e chk.gates.length cl := by
  rw [tableauF, eval_or_iff, eval_mainF e G hC x ht hf, eval_windowN e G hC x chk hG hC' hin hinp]
  subst hG
  exact tableau_dec_iff e fixed chk hC' hin hinp hne _

theorem InputsLt.tableauF {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n)
    (frees : List ℕ) (tpls : List (List NTpl)) {C : CandF} (hC : C.InputsLt n) :
    (tableauF e G tabs frees tpls C).InputsLt n :=
  InputsLt.or' (InputsLt.mainF e tabs htabs frees hC) (InputsLt.windowN e G hC tpls)

end MIPRE.TM.CookLevin.Desc
