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

end MIPRE.TM.CookLevin.Desc
