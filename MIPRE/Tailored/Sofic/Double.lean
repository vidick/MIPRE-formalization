/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Robust
public import Mathlib.Logic.Equiv.Fin.Basic
public import MIPRE.Tactics

@[expose] public section

/-!
# The doubled action

The disjoint union `σ ⊕ σ` of a finite action with itself, on `Fin 2 × Fin N ≃ Fin (2N)`. Every
stabilizer occurs twice as often on twice as many points, so every challenge is passed with the
same probability and the value is unchanged (`value_double`). The swap of the two copies is a
fixed-point-free involution commuting with every letter (`dblSwap`).

This replaces the paper's padding of an odd set by one point (Claim I:2582 and the proof of
Proposition I:2267): on the doubled set, the fixed points of an involution commuting with the
swap can be sent along the swap, and every distance is measured on a single point set.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue Finset FiniteActionLemmas

variable {n : ℕ} (σ : FiniteAction n)

/-- The disjoint union of `σ` with itself. -/
def double : FiniteAction n where
  N := 2 * σ.N
  N_pos := by have := σ.N_pos; omega
  σ k := finProdFinEquiv.permCongr ((Equiv.refl (Fin 2)).prodCongr (σ.σ k))

theorem double_N : (double σ).N = 2 * σ.N := rfl

/-- The two copies of the points of `σ`, as the points of `double σ`. -/
def dblE : Fin 2 × Fin σ.N ≃ Fin (double σ).N := finProdFinEquiv

theorem double_σ_apply (k : Fin n) (i : Fin 2) (p : Fin σ.N) :
    (double σ).σ k (dblE σ (i, p)) = dblE σ (i, σ.σ k p) := by
  show finProdFinEquiv.permCongr ((Equiv.refl (Fin 2)).prodCongr (σ.σ k))
    (finProdFinEquiv (i, p)) = finProdFinEquiv (i, σ.σ k p)
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem double_σ_inv_apply (k : Fin n) (i : Fin 2) (p : Fin σ.N) :
    ((double σ).σ k)⁻¹ (dblE σ (i, p)) = dblE σ (i, (σ.σ k)⁻¹ p) := by
  rw [Equiv.Perm.inv_eq_iff_eq, double_σ_apply]
  simp

theorem double_letterPerm (l : Letter) (i : Fin 2) (p : Fin σ.N) :
    (double σ).letterPerm l (dblE σ (i, p)) = dblE σ (i, σ.letterPerm l p) := by
  unfold FiniteAction.letterPerm
  by_cases h : l.1 < n
  · rw [dite_eq_left h, dite_eq_left h]
    split_ifs
    · exact double_σ_inv_apply σ _ i p
    · exact double_σ_apply σ _ i p
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

theorem double_wordPerm (w : Word) (i : Fin 2) (p : Fin σ.N) :
    (double σ).wordPerm w (dblE σ (i, p)) = dblE σ (i, σ.wordPerm w p) := by
  induction w with
  | nil => simp [wordPerm_nil]
  | cons l w ih =>
    rw [wordPerm_cons, wordPerm_cons, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
      double_letterPerm]

theorem double_inStab (w : Word) (i : Fin 2) (p : Fin σ.N) :
    (double σ).InStab (dblE σ (i, p)) w ↔ σ.InStab p w := by
  unfold FiniteAction.InStab
  rw [double_wordPerm, (dblE σ).apply_eq_iff_eq]
  simp

theorem double_passes (K : List Word) (C : List (List (ℕ × Bool))) (i : Fin 2) (p : Fin σ.N) :
    (double σ).Passes K C (dblE σ (i, p)) ↔ σ.Passes K C p := by
  unfold FiniteAction.Passes FiniteAction.LitHolds
  simp only [decide_eq_decide.mpr (double_inStab σ _ i p)]

theorem double_passProb (K : List Word) (C : List (List (ℕ × Bool))) :
    (double σ).passProb K C = σ.passProb K C := by
  unfold FiniteAction.passProb
  have hcard : (univ.filter fun q : Fin (double σ).N => (double σ).Passes K C q).card =
      2 * (univ.filter fun p : Fin σ.N => σ.Passes K C p).card := by
    have h1 : (univ.filter fun q : Fin (double σ).N => (double σ).Passes K C q).card =
        ((univ : Finset (Fin 2)) ×ˢ (univ.filter fun p : Fin σ.N => σ.Passes K C p)).card := by
      symm
      apply Finset.card_equiv (dblE σ)
      rintro ⟨i, p⟩
      simp only [mem_product, mem_univ, mem_filter, true_and]
      exact (double_passes σ K C i p).symm
    rw [h1, card_product, card_univ, Fintype.card_fin]
  rw [hcard, double_N]
  have hN : (σ.N : ℝ) ≠ 0 := by have := σ.N_pos; positivity
  push_cast
  field_simp

/-- **Doubling does not change the value.** -/
theorem value_double (T : SubgroupTestData) (σ : FiniteAction T.nGen) :
    T.value (double σ) = T.value σ := by
  simp only [SubgroupTestData.value, double_passProb]

/-- The swap of the two copies. -/
def dblSwap : Equiv.Perm (Fin (double σ).N) :=
  (dblE σ).permCongr ((Equiv.swap 0 1).prodCongr (Equiv.refl _))

theorem dblSwap_apply (i : Fin 2) (p : Fin σ.N) :
    dblSwap σ (dblE σ (i, p)) = dblE σ (Equiv.swap 0 1 i, p) := by
  simp [dblSwap, Equiv.permCongr_apply]

theorem dblSwap_invol (q : Fin (double σ).N) : dblSwap σ (dblSwap σ q) = q := by
  obtain ⟨⟨i, p⟩, rfl⟩ := (dblE σ).surjective q
  rw [dblSwap_apply, dblSwap_apply, Equiv.swap_apply_self]

theorem dblSwap_free (q : Fin (double σ).N) : dblSwap σ q ≠ q := by
  obtain ⟨⟨i, p⟩, rfl⟩ := (dblE σ).surjective q
  rw [dblSwap_apply, Ne, (dblE σ).apply_eq_iff_eq, Prod.mk.injEq]
  intro h
  fin_cases i <;> simp at h

theorem dblSwap_comm (l : Letter) (q : Fin (double σ).N) :
    (double σ).letterPerm l (dblSwap σ q) = dblSwap σ ((double σ).letterPerm l q) := by
  obtain ⟨⟨i, p⟩, rfl⟩ := (dblE σ).surjective q
  rw [dblSwap_apply, double_letterPerm, double_letterPerm, dblSwap_apply]

end MIPRE.Tailored.Sofic

end
