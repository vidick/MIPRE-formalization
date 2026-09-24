/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game

/-!
# A polynomial on a block of the variables

A coefficient vector in `n` variables read on a block of them, as a coefficient vector in the
block's `n'` variables (`LowIndDegPoly.blockPoly`), and the exponent vectors that carry it
(`expandIdx`). Moved from `MIPRE/Background/QLD/Complete.lean`, where the Pauli basis test's
completion uses them, so that answer reduction can use them without importing that test.
-/

noncomputable section

/-! ## A polynomial on a block of the variables -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n n' d : ℕ}

/-- The exponent vector on `Fin n` carried by the injection `idx` from one on `Fin n'`, zero off
the range. -/
def expandIdx (idx : Fin n' → Fin n) (e' : Fin n' → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if h : ∃ j, idx j = k then e' h.choose else 0

theorem expandIdx_apply_idx {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    (e' : Fin n' → Fin (d + 1)) (j : Fin n') : expandIdx idx e' (idx j) = e' j := by
  have h : ∃ j', idx j' = idx j := ⟨j, rfl⟩
  rw [expandIdx, dif_pos h, hinj h.choose_spec]

theorem expandIdx_apply_of_not {idx : Fin n' → Fin n} (e' : Fin n' → Fin (d + 1)) {k : Fin n}
    (hk : ∀ j, idx j ≠ k) : expandIdx idx e' k = 0 := by
  rw [expandIdx, dif_neg]
  rintro ⟨j, hj⟩
  exact hk j hj

/-- The monomial of an expanded exponent vector is the monomial on the block. -/
theorem prod_pow_expandIdx {idx : Fin n' → Fin n} (hinj : Function.Injective idx) (u : Point F n)
    (e' : Fin n' → Fin (d + 1)) :
    ∏ k, u k ^ ((expandIdx idx e' k : Fin (d + 1)) : ℕ)
      = ∏ j, u (idx j) ^ ((e' j : Fin (d + 1)) : ℕ) := by
  classical
  rw [← Finset.prod_subset (Finset.subset_univ (univ.image idx)) (fun k _ hk => ?_)]
  · rw [Finset.prod_image (fun x _ y _ h => hinj h)]
    exact Finset.prod_congr rfl fun j _ => by rw [expandIdx_apply_idx hinj]
  · rw [Finset.mem_image] at hk
    push Not at hk
    rw [expandIdx_apply_of_not _ fun j hj => hk j (mem_univ j) hj, Fin.val_zero, pow_zero]

/-- **A coefficient vector read on a block of the variables**, as a coefficient vector on the
block. -/
def LowIndDegPoly.blockPoly (idx : Fin n' → Fin n) (H : LowIndDegPoly (F := F) (m := n) (d := d)) :
    LowIndDegPoly (F := F) (m := n') (d := d) :=
  fun e' => H (expandIdx idx e')

/-- **A vector supported on the range of `idx` evaluates through the block.** -/
theorem LowIndDegPoly.eval_blockPoly {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    {H : LowIndDegPoly (F := F) (m := n) (d := d)}
    (hsupp : ∀ e, H e ≠ 0 → ∀ k, (∀ j, idx j ≠ k) → e k = 0) (u : Point F n) :
    (H.blockPoly idx).eval (fun j => u (idx j)) = H.eval u := by
  classical
  simp only [LowIndDegPoly.eval, LowIndDegPoly.blockPoly]
  refine Finset.sum_bij_ne_zero (fun e' _ _ => expandIdx idx e') (fun _ _ _ => mem_univ _)
    (fun e₁ _ _ e₂ _ _ h => ?_) (fun e _ hne => ?_) (fun e' _ _ => ?_)
  · funext j
    have := congrArg (fun e => e (idx j)) h
    simpa only [expandIdx_apply_idx hinj] using this
  · have hH : H e ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
    have heq : expandIdx idx (fun j => e (idx j)) = e := by
      funext k
      by_cases hk : ∃ j, idx j = k
      · obtain ⟨j, rfl⟩ := hk
        rw [expandIdx_apply_idx hinj]
      · push Not at hk
        rw [expandIdx_apply_of_not _ hk, hsupp e hH k hk]
    have hp := prod_pow_expandIdx hinj u (fun j => e (idx j))
    rw [heq] at hp
    refine ⟨fun j => e (idx j), mem_univ _, ?_, heq⟩
    rw [heq, ← hp]
    exact hne
  · congr 1
    exact (prod_pow_expandIdx hinj u e').symm

/-- **A coefficient vector in a block's variables, placed on the block**: zero on every monomial
that reads a variable off the block. -/
def LowIndDegPoly.liftIdx (idx : Fin n' → Fin n) (g : LowIndDegPoly (F := F) (m := n') (d := d)) :
    LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if ∀ k, (∀ j, idx j ≠ k) → e k = 0 then g (fun j => e (idx j)) else 0

/-- Reading a placed vector back on its block gives it back. -/
theorem LowIndDegPoly.blockPoly_liftIdx {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    (g : LowIndDegPoly (F := F) (m := n') (d := d)) : (g.liftIdx idx).blockPoly idx = g := by
  funext e'
  simp only [LowIndDegPoly.blockPoly, LowIndDegPoly.liftIdx]
  rw [if_pos (fun k hk => expandIdx_apply_of_not e' hk)]
  congr 1
  funext j
  exact expandIdx_apply_idx hinj e' j

theorem LowIndDegPoly.liftIdx_injective {idx : Fin n' → Fin n} (hinj : Function.Injective idx) :
    Function.Injective (LowIndDegPoly.liftIdx (F := F) (d := d) idx) := fun g g' h => by
  rw [← LowIndDegPoly.blockPoly_liftIdx hinj g, h, LowIndDegPoly.blockPoly_liftIdx hinj]

/-- **A placed vector evaluates through the block.** -/
theorem LowIndDegPoly.eval_liftIdx {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    (g : LowIndDegPoly (F := F) (m := n') (d := d)) (u : Point F n) :
    (g.liftIdx idx).eval u = g.eval (fun j => u (idx j)) := by
  have hsupp : ∀ e, g.liftIdx idx e ≠ 0 → ∀ k, (∀ j, idx j ≠ k) → e k = 0 := by
    intro e he k hk
    simp only [LowIndDegPoly.liftIdx] at he
    split_ifs at he with h
    · exact h k hk
    · exact absurd rfl he
  rw [← LowIndDegPoly.eval_blockPoly hinj hsupp u, LowIndDegPoly.blockPoly_liftIdx hinj]

end MIPRE.LIDT

end
