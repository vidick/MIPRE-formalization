/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-!
# The Schwartz–Zippel lemma, in the form the low-degree machinery uses

Blueprint `lem:schwartz-zippel`: two *unequal* polynomials `f, g : 𝔽_q^m → 𝔽_q` of total
degree at most `d` agree at a uniformly random point with probability at most `d / q`.

Mathlib proves the lemma for a single nonzero polynomial and a product of arbitrary finite
subsets (`MvPolynomial.schwartz_zippel_totalDegree`, `schwartz_zippel_sum_degreeOf`).
Everything here is the specialization the paper and the blueprint actually quote:

* the subsets are all of `F`, so the denominator is `q ^ m` rather than `∏ #(S i)`;
* the event is `f = g` rather than `f - g = 0`;
* the bound is stated over `ℝ`, which is where the low-degree machinery's error terms live.

Three forms, because three different consumers want three different shapes:

* `prob_agree_le_totalDegree` — the blueprint's statement, a probability over `ℝ`;
* `prob_agree_le_individualDegree` — the individual-degree variant the blueprint asks for
  alongside it (`m * d / q`, since a polynomial of individual degree `d` in `m` variables
  has total degree at most `m * d`, and this route avoids that lossy step);
* `card_agree_le_of_natDegree` — the univariate case as a count rather than a probability,
  which is the form `lem:lidt-sync-transfer` uses ("two distinct univariate polynomials of
  degree `d` agree at no more than `d` of the `q` points").

The `ℚ≥0`-valued intermediate is kept private: it is Mathlib's shape, not ours.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- The points of `𝔽_q^m` at which two polynomials agree. -/
def agree (f g : MvPolynomial (Fin m) F) : Finset (Fin m → F) :=
  {x ∈ univ | eval x f = eval x g}

@[simp] theorem mem_agree {f g : MvPolynomial (Fin m) F} {x : Fin m → F} :
    x ∈ agree f g ↔ eval x f = eval x g := by
  simp [agree]

/-- `agree f g` is the zero set of `f - g`, in the shape Mathlib's lemma states. -/
private theorem agree_eq_filter (f g : MvPolynomial (Fin m) F) :
    agree f g = {x ∈ Fintype.piFinset fun _ : Fin m => (univ : Finset F) | eval x (f - g) = 0} := by
  ext x
  simp [agree, sub_eq_zero]

/-- The `ℚ≥0`-valued bound, straight from Mathlib, with the denominators evaluated. -/
private theorem nnrat_prob_agree_le {f g : MvPolynomial (Fin m) F} (hfg : f ≠ g) :
    ((agree f g).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ m
      ≤ ((f - g).totalDegree : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
  have h := MvPolynomial.schwartz_zippel_totalDegree (sub_ne_zero.mpr hfg) (univ : Finset F)
  rw [agree_eq_filter]
  simpa [Finset.card_univ] using h

/-- **Schwartz–Zippel** (blueprint `lem:schwartz-zippel`): two unequal polynomials of total
degree at most `d` in `m` variables over a finite field of size `q` agree at a uniformly
random point of `𝔽_q^m` with probability at most `d / q`. -/
theorem prob_agree_le_totalDegree {f g : MvPolynomial (Fin m) F} (hfg : f ≠ g) {d : ℕ}
    (hf : f.totalDegree ≤ d) (hg : g.totalDegree ≤ d) :
    ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤ (d : ℝ) / Fintype.card F := by
  have h := nnrat_prob_agree_le hfg
  have hd : (f - g).totalDegree ≤ d := (MvPolynomial.totalDegree_sub f g).trans (max_le hf hg)
  have hstep : ((f - g).totalDegree : ℚ≥0) / (Fintype.card F : ℚ≥0)
      ≤ (d : ℚ≥0) / (Fintype.card F : ℚ≥0) := by gcongr
  have h' := NNRat.cast_mono (K := ℝ) (h.trans hstep)
  push_cast at h'
  exact h'

/-- The individual-degree variant: if `f ≠ g` and both have degree at most `d` in each of
the `m` variables separately, they agree with probability at most `m * d / q`. -/
theorem prob_agree_le_individualDegree {f g : MvPolynomial (Fin m) F} (hfg : f ≠ g) {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
    ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m ≤ (m : ℝ) * d / Fintype.card F := by
  have h : ((agree f g).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ m
      ≤ ∑ i : Fin m, ((f - g).degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
    have h₀ := MvPolynomial.schwartz_zippel_sum_degreeOf (sub_ne_zero.mpr hfg)
      (fun _ : Fin m => (univ : Finset F))
    rw [agree_eq_filter]
    simpa [Finset.card_univ, Finset.prod_const] using h₀
  have hd : ∀ i, (f - g).degreeOf i ≤ d := fun i =>
    (MvPolynomial.degreeOf_sub_le i f g).trans (max_le (hf i) (hg i))
  have hstep : ∑ i : Fin m, ((f - g).degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0)
      ≤ (m : ℚ≥0) * d / (Fintype.card F : ℚ≥0) := by
    calc ∑ i : Fin m, ((f - g).degreeOf i : ℚ≥0) / (Fintype.card F : ℚ≥0)
        ≤ ∑ _i : Fin m, (d : ℚ≥0) / (Fintype.card F : ℚ≥0) :=
          Finset.sum_le_sum fun i _ => by gcongr; exact_mod_cast hd i
      _ = (m : ℚ≥0) * d / (Fintype.card F : ℚ≥0) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_div_assoc]
  have h' := NNRat.cast_mono (K := ℝ) (h.trans hstep)
  push_cast at h'
  exact h'

/-- **The majority test used by the classical PCP.** If the field has at least
`2 * m * d` elements, agreement at more than half the points forces polynomial equality.
The strict acceptance threshold is essential when the field-size bound is an equality. -/
theorem eq_of_majority_agree {f g : MvPolynomial (Fin m) F} {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d)
    (hsize : 2 * (m * d) ≤ Fintype.card F)
    (hmajority : Fintype.card F ^ m < 2 * (agree f g).card) : f = g := by
  by_contra hne
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card F : ℝ) ^ m := pow_pos hq _
  have hcount : (Fintype.card F : ℝ) ^ m < 2 * ((agree f g).card : ℝ) := by
    exact_mod_cast hmajority
  have hs : 2 * ((m : ℝ) * d) ≤ Fintype.card F := by exact_mod_cast hsize
  have hlow : (1 / 2 : ℝ) < ((agree f g).card : ℝ) / (Fintype.card F : ℝ) ^ m := by
    apply (lt_div_iff₀ hpow).mpr
    linarith
  have hupp : (m : ℝ) * d / Fintype.card F ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hq).mpr
    linarith
  exact (not_lt_of_ge ((prob_agree_le_individualDegree hne hf hg).trans hupp)) hlow

/-- A verifier may impose other tests as well: agreement on any accepted set larger
than half the field cube already forces the same identity. -/
theorem eq_of_majority_subset {f g : MvPolynomial (Fin m) F} {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d)
    (hsize : 2 * (m * d) ≤ Fintype.card F) (S : Finset (Fin m → F))
    (hS : ∀ x ∈ S, eval x f = eval x g)
    (hmajority : Fintype.card F ^ m < 2 * S.card) : f = g := by
  apply eq_of_majority_agree hf hg hsize
  apply hmajority.trans_le
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro x hx
  exact mem_agree.mpr (hS x hx)

/-- The univariate case, as a count: two unequal polynomials of degree at most `d` over a
field agree at no more than `d` points. This is the form `lem:lidt-sync-transfer` uses. -/
theorem card_agree_le_of_natDegree {p q : Polynomial F} (hpq : p ≠ q) {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    #{t ∈ (univ : Finset F) | p.eval t = q.eval t} ≤ d := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsubset : ({t ∈ (univ : Finset F) | p.eval t = q.eval t} : Finset F).val ⊆ (p - q).roots := by
    intro t ht
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [Polynomial.mem_roots hne]
    simpa [Polynomial.IsRoot, sub_eq_zero] using ht
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    ((Polynomial.natDegree_sub_le p q).trans (max_le hp hq))

end MIPRE.LowDegree

end
