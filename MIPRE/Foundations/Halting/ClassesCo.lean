/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Classes
public import MIPRE.Foundations.VerifierValueCo

@[expose] public section

/-!
# The class of small commuting-operator value, at the level of verifiers

The `MIP^co = coRE` track (`planning/mipco-track.md`, Phase 0) runs the nested
compressibility criterion (`Cost.compressibility_criterion_nested`) with three classes: the
class `A` of the main theorem — a perfect PCC strategy, `Verifier.InClassA` — as the smaller
of the two nested ones; the class of commuting-operator value `1`, read on the tabulation, as
the larger; and, in the role that `InClassB` plays for `RE`, the class of *small
commuting-operator value* defined here:

* `Verifier.InClassBCo n T`: `n`-bounded, rejects every answer longer than `T` at index `n`,
  and `ω_co(𝒱_n) ≤ 1/2` at answer bound `T`. It is contained in `InClassB`
  (`InClassBCo.inClassB`, since `val* ≤ ω_co`) and so disjoint from `InClassA`.
* `Verifier.inClassBCo_of_rejects_all`: a decider accepting nothing at `n` is in it, which is
  where the distinguished string `y_no` of the co reduction comes from — the same `y_no` as
  for `RE`, now read in `ω_co`.
* `Verifier.freeze_valCo`, `Verifier.freeze_inClassBCo`: transport along the frozen verifier,
  as `freeze_valStar` and `freeze_inClassB`.
-/

namespace MIPRE

open Cost

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The class `B^co` at level `n`, with answer-length bound `T`: the verifier is `n`-bounded,
its decider rejects every answer longer than `T` at index `n`, and its `n`-th game has
commuting-operator value at most `1/2`. -/
def InClassBCo (n T : ℕ) : Prop := V.IsBounded n ∧ V.RejectsLong n T ∧ V.valCo n T ≤ 1 / 2

/-- Small commuting-operator value is small quantum value. -/
theorem InClassBCo.inClassB {n T : ℕ} (h : V.InClassBCo n T) : V.InClassB n T :=
  ⟨h.1, h.2.1, (V.valStar_le_valCo n T).trans h.2.2⟩

/-- The class `B^co` is disjoint from the class `A`. -/
theorem not_inClassBCo_of_inClassA {n T : ℕ} (h : V.InClassA n T) : ¬ V.InClassBCo n T :=
  fun h' => V.not_inClassB_of_inClassA h h'.inClassB

/-- A verifier that accepts nothing at index `n` and is `n`-bounded is in the class `B^co`. -/
theorem inClassBCo_of_rejects_all {n T : ℕ} (hb : V.IsBounded n)
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.InClassBCo n T := by
  refine ⟨hb, fun x y a b _ => hrej x y a b, ?_⟩
  rw [V.valCo_eq_zero_of_rejects_all hrej]
  norm_num

/-! ## Transport along the frozen verifier -/

/-- The commuting-operator value of the frozen verifier at any index is the value of `V` at
the frozen index. -/
theorem freeze_valCo (k n T : ℕ) : (V.freeze k).valCo n T = V.valCo k T := by
  unfold valCo
  refine commutingOperatorValue_eq_of_equiv (V.game k T) ((V.freeze k).game n T) (Equiv.refl _)
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (fun _ _ => rfl) fun x y a b => ?_
  exact decide_eq_decide.2 (V.decider.freeze_accepts k n _ _ _ _)

theorem freeze_inClassBCo {k n T : ℕ} (hb : (V.freeze k).IsBounded n) (hrej : V.RejectsLong k T)
    (h : V.valCo k T ≤ 1 / 2) : (V.freeze k).InClassBCo n T :=
  ⟨hb, (V.freeze_rejectsLong k n T).2 hrej, by rw [V.freeze_valCo k n T]; exact h⟩

end Verifier

end MIPRE

end
