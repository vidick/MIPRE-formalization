/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Params

/-!
# The answer tapes end at `T`

Two clauses beyond the tableau: the cell at position `T + 3` of each of the two free tapes
holds the blank. They are what makes the soundness direction of the describer give answers of
length at most `T`: the free-tape clauses force the blanks of a free tape to be trailing
(`freeClauses`), so a blank at `T + 3` bounds the string read off the time-`0` row by `T`
(`freeLen`, `Sound.lean`). An accepting run on answers of length at most `T` satisfies them,
so they cost the completeness direction nothing.

`tableauPlus` is the tableau together with them, `tableauPlusF` the formula, and
`eval_tableauPlusF` its exactness (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

variable (e G T : ℕ)

/-- The two clauses: the cell at position `T + 3` of a free tape holds the blank. -/
def ansEndClauses : Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G) :=
  {c | ∃ (j : Fin 7) (p : Pos (Sof e)), ((j : ℕ) = 5 ∨ (j : ℕ) = 6) ∧ (p : ℕ) = T + 3 ∧
    c = unit (.cell 0 (.inl j) p .blank) true}

/-- The candidate is one of the two answer-end clauses. -/
def AnsEnd (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ (c.F₁.d = 5 ∨ c.F₁.d = 6) ∧ c.F₁.p = T + 3 ∧
    c.F₁.v = 5 ∧ c.s₁ = true

theorem ansEnd_iff (c : Cand) :
    AnsEnd e T c ↔ ∃ cl ∈ ansEndClauses e G T, c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hd, hp, hv, hs⟩
    obtain ⟨t, d, p, v, hdec⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hdec
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j, rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd]; omega)
    have hvb : v = .blank := symCode_inj.mp (by rw [← hvv, hv]; rfl)
    subst hvb
    refine ⟨_, ⟨j, p, ?_, ?_, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hdec, hu, hs, hss⟩⟩
    · rw [tapeCode_inl] at hdd; omega
    · omega
  · rintro ⟨_, ⟨j, p, hj, hp, rfl⟩, hdec⟩
    obtain ⟨hdec', hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p .blank).mp hdec'
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ?_, by rw [hpp, hp], by rw [hvv]; rfl, hs⟩
    rw [hdd, tapeCode_inl]
    exact hj

/-- The tableau together with the two answer-end clauses: the clause set the describer
describes. -/
noncomputable def tableauPlus (fixed : Fin 7 → Option (List Sym)) (chk : Circuit) :
    Cnf3 (TabVar 7 6 Sym Ctl (Sof e) chk.gates.length) :=
  tableau U Sym.zero Sym.one (Sof e) fixed chk ∪ ansEndClauses e chk.gates.length T

/-! ## As a formula -/

/-- `AnsEnd`. -/
def ansEndF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁,
    or (eqConst C.A₁.d (nbits 4 5)) (eqConst C.A₁.d (nbits 4 6)),
    eqConst C.A₁.p (nbits (W e) (T + 3)), eqConst C.A₁.v (nbits 3 5), C.σ₁]

theorem eval_ansEndF {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool) (hT : T + 3 < 2 ^ W e) :
    (ansEndF e T C).eval x = true ↔ AnsEnd e T (evalCand C x) := by
  rw [ansEndF, eval_andList₇, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_or_iff, eval_eqN hC.A₁.d (by norm_num), eval_eqN hC.A₁.d (by norm_num),
    eval_eqN hC.A₁.p hT, eval_eqN hC.A₁.v (by norm_num)]
  rfl

theorem InputsLt.ansEndF {n : ℕ} {C : CandF} (hC : C.InputsLt n) : (ansEndF e T C).InputsLt n :=
  InputsLt.andList _ (InputsLt.list_cons (InputsLt.unitCellF e hC)
    (InputsLt.list_cons (InputsLt.sameSignsF hC) (InputsLt.list_cons (InputsLt.tZeroF e hC.A₁)
    (InputsLt.list_cons (InputsLt.or' (InputsLt.eqConst _ hC.A₁.d) (InputsLt.eqConst _ hC.A₁.d))
    (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.p) (InputsLt.list_cons (InputsLt.eqConst _ hC.A₁.v)
    (InputsLt.list_cons hC.σ₁ InputsLt.list_nil)))))))

/-- The formula of the whole clause set. -/
noncomputable def tableauPlusF (tabs : List (ℕ × Fml)) (frees : List ℕ) (tpls : List (List NTpl))
    (C : CandF) : Fml :=
  or (tableauF e G tabs frees tpls C) (ansEndF e T C)

/-- **The describer's formula is exact**: it accepts a candidate iff the candidate decodes to
a clause of `tableauPlus`. -/
theorem eval_tableauPlusF {fixed : Fin 7 → Option (List Sym)} {tabs : List (ℕ × Fml)}
    {frees : List ℕ} {C : CandF} (hC : C.Lengths e chk.gates.length) (x : ℕ → Bool)
    (ht : TapeSpec e C.A₁ fixed tabs) (hf : FreeSpec fixed frees) (hT : T + 3 < 2 ^ W e) :
    (tableauPlusF e chk.gates.length T tabs frees (tplsOf chk.gates.length chk) C).eval x = true ↔
      ∃ cl ∈ tableauPlus e T fixed chk, (evalCand C x).Dec e chk.gates.length cl := by
  rw [tableauPlusF, eval_or_iff,
    eval_tableauF e chk.gates.length hC x ht hf chk rfl chk_refsLt chk_inputsLt chk_inputs
      chk_gates_ne,
    eval_ansEndF e chk.gates.length T hC x hT, ansEnd_iff e chk.gates.length T, tableauPlus,
    exists_mem_union]

theorem InputsLt.tableauPlusF {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n)
    (frees : List ℕ) (tpls : List (List NTpl)) {C : CandF} (hC : C.InputsLt n) :
    (tableauPlusF e G T tabs frees tpls C).InputsLt n :=
  InputsLt.or' (InputsLt.tableauF e G tabs htabs frees tpls hC) (InputsLt.ansEndF e T hC)

end MIPRE.TM.CookLevin.Desc
