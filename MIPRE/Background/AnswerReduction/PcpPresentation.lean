/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Presentation
import MIPRE.Foundations.SAT.Pcp

/-!
# The PCP sampler of answer reduction, over `F_q`

Piece AR-3a of `planning/answer-reduction.md`: the typed PCP sampler `Ŝ^pcp` of the paper's
`sec:ar-verifier` (`ld_compiler.tex`, `eq:V-pcp`), as CL presentations over `F_q`.

The ambient space is
`V^pcp = ⊕_{i≤5} (V_{i,pt} ⊕ V_{i,coord} ⊕ V_{i,dir}) ⊕ V_{aux,pt} ⊕ V_{6,coord} ⊕ V_{aux,dir}`,
with coordinates `Coord P` (`10m + 2s + 16` of them, `card_coord`). There are six copies of the
seeded low-degree test on it (`regs`, `regs6`):

* copy `i ≤ 5` is the test in `m` variables on its own three registers;
* copy `6` is the test in `m' = 5m + 5 + s` variables whose point and direction registers are the
  *concatenations* `V_{6,pt} = ⊕_{i≤5} V_{i,pt} ⊕ V_{aux,pt}` and `V_{6,dir}` likewise, with its
  own seed coordinate.

The overlap is the point of the construction: the `i`-th block of the sixth copy's point, in the
block order `SAT.PcpParams.block` of the PCP, is the `i`-th copy's point (`block_ptOf_regs6`).
That is what the answer-reduced decider's consistency subtests compare.

The types are `Fin 6 × LIDT.CL.Ty`, eighteen of them, each presented in three levels (`pres`),
exactly on the whole space (`pres_exactlyOn`), with full evaluation the seeded question of its
copy (`question_eval`).
-/

noncomputable section

namespace MIPRE.AnswerReduction.Pcp

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT

/-! ## The coordinates -/

/-- The coordinates of `V^pcp`. -/
inductive Coord (P : PcpParams)
  /-- `V_{i,pt}`, `i ≤ 5`. -/
  | pt (i : Fin 5) (j : Fin P.m)
  /-- `V_{i,dir}`, `i ≤ 5`. -/
  | dir (i : Fin 5) (j : Fin P.m)
  /-- `V_{i,coord}`, `i ≤ 6`. -/
  | coord (i : Fin 6)
  /-- `V_{aux,pt}`. -/
  | auxPt (j : Fin (5 + P.s))
  /-- `V_{aux,dir}`. -/
  | auxDir (j : Fin (5 + P.s))
  deriving DecidableEq

namespace Coord

variable (P : PcpParams)

/-- The coordinates as a sum. -/
def equivSum : Coord P ≃ (Fin 5 × Fin P.m) ⊕ (Fin 5 × Fin P.m) ⊕ Fin 6 ⊕ Fin (5 + P.s) ⊕
    Fin (5 + P.s) where
  toFun
    | .pt i j => .inl (i, j)
    | .dir i j => .inr (.inl (i, j))
    | .coord i => .inr (.inr (.inl i))
    | .auxPt j => .inr (.inr (.inr (.inl j)))
    | .auxDir j => .inr (.inr (.inr (.inr j)))
  invFun
    | .inl (i, j) => .pt i j
    | .inr (.inl (i, j)) => .dir i j
    | .inr (.inr (.inl i)) => .coord i
    | .inr (.inr (.inr (.inl j))) => .auxPt j
    | .inr (.inr (.inr (.inr j))) => .auxDir j
  left_inv c := by cases c <;> rfl
  right_inv c := by rcases c with ⟨i, j⟩ | ⟨i, j⟩ | i | j | j <;> rfl

instance : Fintype (Coord P) := Fintype.ofEquiv _ (equivSum P).symm

theorem card_coord : Fintype.card (Coord P) = 10 * P.m + 2 * P.s + 16 := by
  rw [Fintype.card_congr (equivSum P)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

end Coord

/-! ## The six copies -/

variable (P : PcpParams)

/-- The registers of copy `i ≤ 5`. -/
def regs (i : Fin 5) : Regs (Coord P) P.m where
  pt j := .pt i j
  dir j := .dir i j
  coord := .coord i.castSucc
  pt_injective _ _ h := by cases h; rfl
  dir_injective _ _ h := by cases h; rfl
  pt_ne_dir _ _ h := by cases h
  pt_ne_coord _ h := by cases h
  dir_ne_coord _ h := by cases h

/-- The `k`-th coordinate of the concatenated point register `V_{6,pt}`: the `(k mod m)`-th
coordinate of `V_{⌊k/m⌋,pt}` for `k < 5m`, and of `V_{aux,pt}` beyond. -/
def pt6 (k : Fin P.m') : Coord P :=
  if h : (k : ℕ) < 5 * P.m then
    .pt ⟨k / P.m, by
      have hm : 0 < P.m := by omega
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h)⟩ ⟨k % P.m, Nat.mod_lt _ (by omega)⟩
  else .auxPt ⟨k - 5 * P.m, by have := k.isLt; simp only [PcpParams.m'] at this; omega⟩

/-- The `k`-th coordinate of the concatenated direction register `V_{6,dir}`. -/
def dir6 (k : Fin P.m') : Coord P :=
  if h : (k : ℕ) < 5 * P.m then
    .dir ⟨k / P.m, by
      have hm : 0 < P.m := by omega
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h)⟩ ⟨k % P.m, Nat.mod_lt _ (by omega)⟩
  else .auxDir ⟨k - 5 * P.m, by have := k.isLt; simp only [PcpParams.m'] at this; omega⟩

theorem pt6_injective : Function.Injective (pt6 P) := by
  intro k k' h
  apply Fin.ext
  by_cases h1 : (k : ℕ) < 5 * P.m <;> by_cases h2 : (k' : ℕ) < 5 * P.m <;>
    simp only [pt6, h1, h2, dite_true, dite_false, reduceCtorEq, Coord.pt.injEq,
      Coord.auxPt.injEq, Fin.mk.injEq] at h
  · rw [← Nat.div_add_mod (k : ℕ) P.m, ← Nat.div_add_mod (k' : ℕ) P.m, h.1, h.2]
  · omega

theorem dir6_injective : Function.Injective (dir6 P) := by
  intro k k' h
  apply Fin.ext
  by_cases h1 : (k : ℕ) < 5 * P.m <;> by_cases h2 : (k' : ℕ) < 5 * P.m <;>
    simp only [dir6, h1, h2, dite_true, dite_false, reduceCtorEq, Coord.dir.injEq,
      Coord.auxDir.injEq, Fin.mk.injEq] at h
  · rw [← Nat.div_add_mod (k : ℕ) P.m, ← Nat.div_add_mod (k' : ℕ) P.m, h.1, h.2]
  · omega

/-- The registers of copy `6`. -/
def regs6 : Regs (Coord P) P.m' where
  pt := pt6 P
  dir := dir6 P
  coord := .coord 5
  pt_injective := pt6_injective P
  dir_injective := dir6_injective P
  pt_ne_dir k k' h := by unfold pt6 dir6 at h; split_ifs at h
  pt_ne_coord k h := by unfold pt6 at h; split_ifs at h
  dir_ne_coord k h := by unfold dir6 at h; split_ifs at h

/-- The `j`-th coordinate of the `i`-th block of `V_{6,pt}` is the `j`-th coordinate of
`V_{i,pt}`. -/
theorem pt6_block (i : Fin 5) (j : Fin P.m) :
    pt6 P ⟨i * P.m + j, by
      have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
      have h2 : (j : ℕ) < P.m := j.isLt
      simp only [PcpParams.m']
      omega⟩ = .pt i j := by
  have hj : (j : ℕ) < P.m := j.isLt
  have hi : (i : ℕ) < 5 := i.isLt
  have hlt : (i : ℕ) * P.m + j < 5 * P.m := by nlinarith
  have hm : 0 < P.m := by omega
  simp only [pt6, dif_pos hlt]
  congr 1
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_div_left _ _ hm,
      Nat.div_eq_of_lt hj, zero_add]
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj]

/-- **The overlap**: the `i`-th block of the sixth copy's point, in the PCP's block order, is the
`i`-th copy's point. -/
theorem block_ptOf_regs6 {F : Type*} [Field F] (i : Fin 5) (x : Coord P → F) :
    P.block i ((regs6 P).ptOf x) = (regs P i).ptOf x := by
  funext j
  simp only [PcpParams.block, Regs.ptOf, regs6, regs]
  rw [pt6_block]

/-! ## The eighteen types -/

/-- The PCP types: a copy and a low-degree test type. -/
abbrev PcpTy := Fin 6 × LIDT.CL.Ty

instance : NeZero P.m' := ⟨by simp [PcpParams.m']⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm')

/-- **The three-level presentation** of the PCP type `t`. -/
def pres (t : PcpTy) : MIPRE.CL.CLFun F (Coord P) 3 :=
  if h : (t.1 : ℕ) < 5 then (regs P ⟨t.1, h⟩).pres S t.2 else (regs6 P).pres S' t.2

theorem pres_exactlyOn (t : PcpTy) :
    (pres P S S' t : MIPRE.CL.CLFun F (Coord P) 3).ExactlyOn univ := by
  unfold pres
  split_ifs
  · exact Regs.pres_exactlyOn _ _ _
  · exact Regs.pres_exactlyOn _ _ _

/-- The question of a PCP type, read off a vector: a question of the `m`-variable test for the
first five copies, of the `m'`-variable test for the sixth. -/
def questionOf (t : PcpTy) (x : Coord P → F) :
    LIDT.CL.Question F P.m ⊕ LIDT.CL.Question F P.m' :=
  if h : (t.1 : ℕ) < 5 then .inl ((regs P ⟨t.1, h⟩).questionOf S t.2 x)
  else .inr ((regs6 P).questionOf S' t.2 x)

/-- **The presentation computes the seeded question** of its copy. -/
theorem question_eval (t : PcpTy) (x : Coord P → F) :
    questionOf P S S' t ((pres P S S' t).eval x)
      = if h : (t.1 : ℕ) < 5 then .inl (((regs P ⟨t.1, h⟩).sampleOf S t.2 x).question hm t.2)
        else .inr (((regs6 P).sampleOf S' t.2 x).question hm' t.2) := by
  unfold questionOf pres
  split_ifs with h
  · rw [Regs.questionOf_eval]
  · rw [Regs.questionOf_eval]

end MIPRE.AnswerReduction.Pcp

end
