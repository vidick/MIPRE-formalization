/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/PairLaw.lean
-/
/-
# OTQCS: the pair answer law and the sampling resource (Section 6, interfaces)

The interface layer of audit node 1.3, split out of `OTQCS/Main.lean` so that
the §6 construction (`OTQCS/Compile.lean`) and the root theorem
(`OTQCS/Main.lean`, `otqcs_sampling`) can both consume it: the tracial pair
answer law `q_{st}(a,b) = ⟪u, L(E) R(F) u⟫` with its probability-law facts, the
`π`-averaged alignment defect `Δ`, and the question-independent
`SamplingResource`. Anchors: 06_otqcs.tex, thm otqcs items 1–3, the displays
defining `q_{st}`, `q̂_{st}` and `Δ`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

/-- The pair answer law realized by tracial data: for labels `s, t`,
vectors `u s t`, Alice effects `E s a` acting left and Bob effects `F t b`
acting right, `q_{st}(a,b) = ⟪u_{st}, L(E_s^a) R(F_t^b) u_{st}⟫`.
[06_otqcs.tex, display defining q_{st}; 05_prerounding.tex, eq
prerounding-ideal-success] -/
noncomputable def tracialPairLaw (N : StdTracialAlgebra.{0})
    {S T A B : Type} (u : S → T → N.H)
    (E : S → A → N.A) (F : T → B → N.A)
    (s : S) (t : T) (a : A) (b : B) : ℝ :=
  (⟪u s t, N.L (E s a) (N.Rop (F t b) (u s t))⟫_ℂ).re

/-- The pair law of full POVM families on a unit vector is a probability
law over answers: `∑_{a,b} q_{st}(a,b) = 1` (completeness through `L` and
the right action, as in `CommutingStrategy.correlation_sum`). The
family-level hypotheses are for call-site convenience; per-label
instances would suffice. -/
theorem tracialPairLaw_sum (N : StdTracialAlgebra.{0})
    {S T A B : Type} [Fintype A] [Fintype B]
    (u : S → T → N.H) (E : S → A → N.A) (F : T → B → N.A)
    (hu : ∀ s t, ‖u s t‖ = 1)
    (hE : ∀ s, (∑ a : A, E s a) = 1) (hF : ∀ t, (∑ b : B, F t b) = 1)
    (s : S) (t : T) :
    (∑ a : A, ∑ b : B, tracialPairLaw N u E F s t a b) = 1 := by
  classical
  have key : (∑ a : A, ∑ b : B,
      (⟪u s t, N.L (E s a) (N.Rop (F t b) (u s t))⟫_ℂ)) = 1 := by
    calc (∑ a : A, ∑ b : B,
        (⟪u s t, N.L (E s a) (N.Rop (F t b) (u s t))⟫_ℂ))
        = ⟪u s t, (∑ a : A, N.L (E s a))
            ((∑ b : B, N.Rop (F t b)) (u s t))⟫_ℂ := by
          simp [ContinuousLinearMap.sum_apply, inner_sum, map_sum]
          rw [Finset.sum_comm]
      _ = ⟪u s t, u s t⟫_ℂ := by
          have hL : (∑ a : A, N.L (E s a)) = 1 := by
            rw [← map_sum, hE s, map_one]
          have hR : (∑ b : B, N.Rop (F t b)) = 1 := by
            simp only [StdTracialAlgebra.Rop]
            rw [← map_sum, ← Finset.op_sum, hF t, MulOpposite.op_one,
              map_one]
          rw [hL, hR]
          simp
      _ = 1 := by
          rw [inner_self_eq_norm_sq_to_K, hu s t]
          norm_num
  calc (∑ a : A, ∑ b : B, tracialPairLaw N u E F s t a b)
      = (∑ a : A, ∑ b : B,
          (⟪u s t, N.L (E s a) (N.Rop (F t b) (u s t))⟫_ℂ)).re := by
        simp only [tracialPairLaw, Complex.re_sum]
    _ = 1 := by rw [key]; simp

/-- The pair law is pointwise nonnegative: the joint effect
`L(E) R(F)` of commuting positive actions is a positive operator
(`Commute.mul_nonneg` through the Loewner order, as in
`jointEffect_isPositive`). -/
theorem tracialPairLaw_nonneg (N : StdTracialAlgebra.{0})
    {S T A B : Type} (u : S → T → N.H)
    (E : S → A → N.A) (F : T → B → N.A)
    (hE : ∀ s a, IsPosElem (E s a)) (hF : ∀ t b, IsPosElem (F t b))
    (s : S) (t : T) (a : A) (b : B) :
    0 ≤ tracialPairLaw N u E F s t a b := by
  have hE' : (0 : N.H →L[ℂ] N.H) ≤ N.L (E s a) := by
    rw [ContinuousLinearMap.le_def]
    simpa using N.L_isPositive (hE s a)
  have hF' : (0 : N.H →L[ℂ] N.H) ≤ N.Rop (F t b) := by
    rw [ContinuousLinearMap.le_def]
    simpa using N.Rop_isPositive (hF t b)
  have hcomm : Commute (N.L (E s a)) (N.Rop (F t b)) :=
    N.LR_commute (E s a) (F t b)
  have hmul := Commute.mul_nonneg hE' hF' hcomm
  rw [ContinuousLinearMap.le_def] at hmul
  simp only [sub_zero] at hmul
  have h := hmul.2 (u s t)
  rw [tracialPairLaw, ← RCLike.re_to_complex, inner_re_symm]
  simpa [ContinuousLinearMap.reApplyInnerSelf] using h

/-- The `π`-averaged alignment defect
`Δ = E_π(‖u_{st} − x_s‖² + ‖u_{st} − y_t‖²)`.
[06_otqcs.tex, display defining Δ; 05_prerounding.tex, eq
prerounding-delta] -/
noncomputable def piAlignment {S T : Type} [Fintype S] [Fintype T]
    {H : Type*} [NormedAddCommGroup H]
    (π : S → T → ℝ) (u : S → T → H) (xv : S → H) (yv : T → H) : ℝ :=
  ∑ s : S, ∑ t : T, π s t * (‖u s t - xv s‖ ^ 2 + ‖u s t - yv t‖ ^ 2)

/-- A question-independent sampling resource on label sets `S, T` and
answer alphabets `A, B`: one standard-form algebra, ONE unit vector `Ω`
(independence from the realized `(s,t)` is structural — there is a single
state field), and full label-indexed POVMs, Alice's used on the left and
Bob's on the right. [06_otqcs.tex, thm otqcs, items 1–3] -/
structure SamplingResource (S T A B : Type)
    [Fintype A] [Fintype B] : Type 1 where
  N : StdTracialAlgebra.{0}
  Ω : N.H
  Ω_norm : ‖Ω‖ = 1
  E : S → A → N.A
  F : T → B → N.A
  E_pos : ∀ s a, IsPosElem (E s a)
  F_pos : ∀ t b, IsPosElem (F t b)
  E_sum : ∀ s, (∑ a : A, E s a) = 1
  F_sum : ∀ t, (∑ b : B, F t b) = 1

namespace SamplingResource

variable {S T A B : Type} [Fintype A] [Fintype B]

/-- The resource's answer law
`q̂_{st}(a,b) = ⟪Ω, L(Â_s^a) R(B̂_t^b) Ω⟫`. [06_otqcs.tex, display
defining q̂_{st}] -/
noncomputable def answerLaw (R : SamplingResource S T A B) :
    S → T → A → B → ℝ :=
  tracialPairLaw R.N (fun _ _ => R.Ω) R.E R.F

end SamplingResource

end CommutingRepetition
