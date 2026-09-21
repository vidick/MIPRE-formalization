/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Adapter.Strategy
import MIPRE.Foundations.POVMValue

/-!
# The value of a strategy for the seeded test, sample by sample

The seeded test's question distribution is the push-forward of the uniform distribution on
`Sample F m` under the two typed question maps. A strategy's failure probability is therefore the
average over samples of the conditional failure at the two questions the sample generates
(`one_sub_povmValue_clGame`), and that average splits into the nine ordered type pairs
(`sum_sample_eq`). The padded strategy of the Pauli basis test is analysed one type pair at a
time, which is what these two identities are for.

The file also records two facts about a seeded line question that the analysis reads off the
geometry: a point lies on its own line at the parameter `lineParam` computes, whether or not the
direction vanishes (`rep_add_lineParam_smul`), and a degenerate diagonal direction is rare
(`sum_indicator_zeroBelow_eq_zero_le`).
-/

namespace MIPRE.LIDT.CL

open Finset MIPRE

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}

/-! ## The sample space -/

/-- The verifier's random choices, split into the two types and the ambient triple. -/
def sampleEquiv (F : Type*) (m : ℕ) :
    Sample F m ≃ (Ty × Ty) × (Point F m × F × Point F m) where
  toFun sm := ((sm.tyA, sm.tyB), (sm.u, sm.s, sm.v))
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_ty : Fintype.card Ty = 3 := rfl

omit [Field F] [DecidableEq F] in
theorem card_sample :
    Fintype.card (Sample F m) = 9 * Fintype.card (Point F m × F × Point F m) := by
  rw [Fintype.card_congr (sampleEquiv F m), Fintype.card_prod, Fintype.card_prod, card_ty]

omit [Field F] [DecidableEq F] in
/-- A sum over samples, as a sum over the two types and the ambient triple. -/
theorem sum_sample_eq {M : Type*} [AddCommMonoid M] (f : Sample F m → M) :
    ∑ sm, f sm
      = ∑ tA : Ty, ∑ tB : Ty, ∑ x : Point F m × F × Point F m,
          f ⟨tA, tB, x.1, x.2.1, x.2.2⟩ := by
  rw [Fintype.sum_equiv (sampleEquiv F m) f (fun p => f ((sampleEquiv F m).symm p))
    (fun sm => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type, Fintype.sum_prod_type]
  rfl

/-! ## A point lies on its own line -/

omit [Fintype F] in
/-- **Every point lies on its own seeded line, at the parameter `lineParam` computes**, whether
or not the direction vanishes. -/
theorem rep_add_lineParam_smul (w u : Point F m) :
    rep w u + lineParam (rep w u) w u • w = u := by
  by_cases hw : ∃ j, w j ≠ 0
  · set c : F := u (Fin.find (fun j => w j ≠ 0) hw) / w (Fin.find (fun j => w j ≠ 0) hw) with hc
    have hu : u = rep w u + c • w := by
      rw [rep, Adapter.rep_eq hw u, sub_add_cancel]
    have hpar : lineParam (rep w u) w u = c := by
      have h := Adapter.lineParam_eq_of_mem hw (rep w u) c
      rwa [← hu] at h
    rw [hpar]
    exact hu.symm
  · have hw0 : w = 0 := funext fun j => not_not.mp fun h => hw ⟨j, h⟩
    subst hw0
    rw [smul_zero, add_zero, rep, Set.singleton_zero, Submodule.span_zero, Adapter.canonLin_bot]

omit [Fintype F] in
/-- Moving the point along a non-degenerate line by `t` moves its parameter by `t`, and keeps the
base point. -/
theorem lineParam_rep_add_smul {w : Point F m} (hw : ∃ j, w j ≠ 0) (u : Point F m) (t : F) :
    lineParam (rep w (u + t • w)) w (u + t • w) = lineParam (rep w u) w u + t := by
  have hrep : rep w (u + t • w) = rep w u := Adapter.rep_add_smul w u t
  rw [hrep]
  have hu : u + t • w = rep w u + (lineParam (rep w u) w u + t) • w := by
    conv_lhs => rw [← rep_add_lineParam_smul w u]
    rw [add_smul, add_assoc]
  rw [hu, Adapter.lineParam_eq_of_mem hw]

/-! ## Degenerate diagonal directions are rare -/

/-- The number of vectors with a prescribed value at one coordinate does not depend on the
value. -/
theorem sum_indicator_apply_eq (i : Fin m) (c : F) :
    ∑ v : Point F m, (if v i = c then (1 : ℝ) else 0)
      = ∑ v : Point F m, (if v i = 0 then (1 : ℝ) else 0) := by
  rw [← Equiv.sum_comp (Equiv.addRight (Pi.single i c))
    (fun v : Point F m => if v i = c then (1 : ℝ) else 0)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Equiv.coe_addRight, Pi.add_apply, Pi.single_eq_same, add_eq_right]

theorem sum_indicator_apply_eq_zero (i : Fin m) :
    ∑ v : Point F m, (if v i = 0 then (1 : ℝ) else 0)
      = (Fintype.card (Point F m) : ℝ) / Fintype.card F := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [eq_div_iff hq]
  calc (∑ v : Point F m, if v i = 0 then (1 : ℝ) else 0) * Fintype.card F
      = ∑ c : F, ∑ v : Point F m, (if v i = c then (1 : ℝ) else 0) := by
        rw [Finset.sum_congr rfl fun c _ => sum_indicator_apply_eq i c, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ = ∑ v : Point F m, ∑ c : F, (if v i = c then (1 : ℝ) else 0) := Finset.sum_comm
    _ = Fintype.card (Point F m) := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **A degenerate diagonal direction is rare**: the truncation `zeroBelow i` vanishes on at most
a `1/q` fraction of the raw directions. -/
theorem sum_indicator_zeroBelow_eq_zero_le (i : Fin m) :
    ∑ v : Point F m, (if zeroBelow i v = 0 then (1 : ℝ) else 0)
      ≤ (Fintype.card (Point F m) : ℝ) / Fintype.card F := by
  rw [← sum_indicator_apply_eq_zero i]
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases h : zeroBelow i v = 0
  · rw [if_pos h, if_pos]
    have h' := congrFun h i
    simpa [zeroBelow] using h'
  · rw [if_neg h]
    split_ifs <;> norm_num

/-! ## The failure probability, sample by sample -/

variable [NeZero m] (hm : m ∣ Fintype.card F)

/-- **The failure probability of a POVM strategy in the seeded test is the average over the
verifier's samples of the conditional failure at the two questions the sample generates.** -/
theorem one_sub_povmValue_clGame {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : dA × dB → ℂ) (MA : Question F m → POVM (Answer F m d ldc) dA)
    (MB : Question F m → POVM (Answer F m d ldc) dB) :
    1 - povmValue (clGame (d := d) (ldc := ldc) hm) ψ MA MB
      = (Fintype.card (Sample F m) : ℝ)⁻¹ * ∑ sm : Sample F m,
          condFail (clGame hm) ψ MA MB (sm.question hm sm.tyA) (sm.question hm sm.tyB) := by
  classical
  rw [one_sub_povmValue_eq, Finset.mul_sum]
  set c : ℝ := (Fintype.card (Sample F m) : ℝ)⁻¹ with hc
  set T : Question F m → Question F m → Sample F m → ℝ := fun x y sm =>
    (c * if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0)
      * condFail (clGame hm) ψ MA MB x y with hT
  have hμ : ∀ x y, (clGame (d := d) (ldc := ldc) hm).μ x y * condFail (clGame hm) ψ MA MB x y
      = ∑ sm : Sample F m, T x y sm := fun x y => by
    rw [hT]
    show (∑ sm : Sample F m, c * if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y)
      then (1 : ℝ) else 0) * condFail (clGame hm) ψ MA MB x y = _
    rw [Finset.sum_mul]
  simp only [hμ]
  calc ∑ x, ∑ y, ∑ sm, T x y sm
      = ∑ x, ∑ sm, ∑ y, T x y sm := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ sm, ∑ x, ∑ y, T x y sm := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun sm _ => ?_
  rw [← Fintype.sum_prod_type' fun x y => T x y sm]
  simp only [hT, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Prod.mk.eta, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end MIPRE.LIDT.CL
