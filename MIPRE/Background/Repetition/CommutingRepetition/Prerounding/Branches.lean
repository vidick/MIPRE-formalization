/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Branches.lean
-/
/-
# Exact branch effects (node 1.2.4)

The operator layer over the reveal histories of node 1.2.3
(05_prerounding.tex, "Reveal histories and exact branch effects", second
half: eqs WD-t-z context, effective-HK, branch-probability,
live-refinements, bar-HK). Given a tracial strategy on word alphabets
(downstream: the repeated strategy of eq repeated-tracial-law), the core
effects `E_{x^n}^{a_D}` are the POVM effects summed over the answers
outside the core; the effective effects `H_{r,x}, K_{r,y}` are their
conditional expectations given `(T₀, X_i)` resp. `(T₀, Y_i)`, encoded as
weight-averaged sums with the reveal-layer weights; and the exact branch
probability identity (eq branch-probability) expresses the conditional
core-answer probability as `τ(σ* H_{r,x} σ K_{r,y})`.

Encoding notes (for the fidelity review):
- Reference words `x₀, y₀` package the revealed question values of
  `T₀ = (λ, X_{C_X}, Y_{C_Y})` together with the live questions
  `X_i = x₀ i`, `Y_i = y₀ i`, as in `priorWeight` (reviewed, #7).
- The one-sided weights `xWeight`/`yWeight` are the `(T₀, X_i)`- resp.
  `(T₀, Y_i)`-conditioned unnormalized laws of one player's word; the
  factorization `priorWeight = pinnedWeight · xWeight · yWeight`
  (eq reveal-cover ⇒ eq prior-factorization) is exactly reviewer #7's
  note-N3 bridge between the symmetric conditioning `(T₀, X_i, Y_i)` and
  the manuscript's asymmetric factors.
- Conditional expectations are weighted averages with an inverse-mass
  scalar; per the manuscript, "Question conditionals are used only on
  positive marginal support", so the normalized statements carry the
  positive-mass hypothesis and Lean's `0⁻¹ = 0` junk value is never
  consumed.
- Operator-norm contractivity of `H, K` ("positive contractions") is not
  statable in the bare `StdTracialAlgebra` interface (D6); it is a
  `CStarLayer` fact, deferred to Stage B. Only algebraic positivity is
  claimed here.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Reveal
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Strategy
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.Arena

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

universe u

/-- Average of a family of vectors in a ℂ-module under a real weight
function: `(∑ w)⁻¹ • ∑ᵢ wᵢ • fᵢ`. With Lean's `0⁻¹ = 0` convention the
value is `0` at zero total mass; every consuming statement guards its
mass. Auxiliary. -/
noncomputable def weightedAvg {ι : Type*} [Fintype ι] {V : Type*}
    [AddCommMonoid V] [Module ℂ V] (w : ι → ℝ) (f : ι → V) : V :=
  (((∑ i : ι, w i : ℝ) : ℂ))⁻¹ • ∑ i : ι, ((w i : ℝ) : ℂ) • f i

namespace RevealDatum

variable {n : ℕ} {X Y : Type} [Fintype X] [Fintype Y]
variable [DecidableEq X] [DecidableEq Y]
variable {D : Finset (Fin n)} (d : RevealDatum n D)

/-- The `(T₀, X_i)`-conditioned unnormalized law of Alice's full question
word: consistency with the revealed values on `C_X ∪ {i}`, times the
pinned-Bob halves of the free coordinates' joint laws (every coordinate
outside `C_X ∪ {i}` lies in `C_Y` by eq reveal-cover). -/
noncomputable def xWeight (μ : X → Y → ℝ) (x₀ : Fin n → X)
    (y₀ : Fin n → Y) (w : Fin n → X) : ℝ :=
  if agreesOn (insert d.i d.CX) w x₀ then
    ∏ j ∈ (insert d.i d.CX)ᶜ, μ (w j) (y₀ j)
  else 0

/-- The `(T₀, Y_i)`-conditioned unnormalized law of Bob's full question
word. -/
noncomputable def yWeight (μ : X → Y → ℝ) (x₀ : Fin n → X)
    (y₀ : Fin n → Y) (v : Fin n → Y) : ℝ :=
  if agreesOn (insert d.i d.CY) v y₀ then
    ∏ j ∈ (insert d.i d.CY)ᶜ, μ (x₀ j) (v j)
  else 0

/-- The doubly revealed coordinates' contribution: the joint law at the
pinned values on `(C_X ∪ {i}) ∩ (C_Y ∪ {i})`. -/
noncomputable def pinnedWeight (μ : X → Y → ℝ) (x₀ : Fin n → X)
    (y₀ : Fin n → Y) : ℝ :=
  ∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (x₀ j) (y₀ j)

theorem xWeight_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (w : Fin n → X) :
    0 ≤ d.xWeight μ x₀ y₀ w := by
  unfold xWeight
  split
  · exact Finset.prod_nonneg fun j _ => hμ _ _
  · exact le_refl 0

theorem yWeight_nonneg (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (v : Fin n → Y) :
    0 ≤ d.yWeight μ x₀ y₀ v := by
  unfold yWeight
  split
  · exact Finset.prod_nonneg fun j _ => hμ _ _
  · exact le_refl 0

/-- **Weight factorization** (node 1.2.4 bridge; eq reveal-cover ⇒ eq
prior-factorization): the symmetric `(T₀, X_i, Y_i)`-conditioned prior
weight splits into the doubly pinned block times the two one-sided
conditioned laws. This is the exact form of reviewer #7's note-N3
bridge: it makes the one-sided weights the marginals of the symmetric
conditioning. -/
theorem priorWeight_eq_mul (μ : X → Y → ℝ) (x₀ : Fin n → X)
    (y₀ : Fin n → Y) (w : Fin n → X) (v : Fin n → Y) :
    priorWeight d μ x₀ y₀ w v
      = d.pinnedWeight μ x₀ y₀ *
        (d.xWeight μ x₀ y₀ w * d.yWeight μ x₀ y₀ v) := by
  classical
  have hcover : ∀ j : Fin n, j ∈ insert d.i d.CX ∨ j ∈ insert d.i d.CY := by
    intro j
    by_cases hji : j = d.i
    · exact Or.inl (hji ▸ Finset.mem_insert_self _ _)
    · have hj : j ∈ d.CX ∪ d.CY := by
        rw [d.union_eq_compl_singleton]
        simpa using hji
      rcases Finset.mem_union.mp hj with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr (Finset.mem_insert_of_mem h)
  unfold priorWeight xWeight yWeight pinnedWeight
  by_cases hx : agreesOn (insert d.i d.CX) w x₀
  · by_cases hy : agreesOn (insert d.i d.CY) v y₀
    · rw [if_pos ⟨hx, hy⟩, if_pos hx, if_pos hy]
      have hsdiff : (insert d.i d.CX : Finset (Fin n)) \ insert d.i d.CY
          = (insert d.i d.CY : Finset (Fin n))ᶜ := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_compl]
        exact ⟨fun h => h.2, fun h => ⟨(hcover j).resolve_right h, h⟩⟩
      have hsplitI : (∏ j ∈ insert d.i d.CX, μ (w j) (v j))
          = (∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (w j) (v j)) *
            ∏ j ∈ (insert d.i d.CY : Finset (Fin n))ᶜ, μ (w j) (v j) := by
        rw [← Finset.prod_filter_mul_prod_filter_not (insert d.i d.CX)
          (fun j => j ∈ insert d.i d.CY) (fun j => μ (w j) (v j)),
          Finset.filter_mem_eq_inter, ← Finset.sdiff_eq_filter, hsdiff]
      have e1 : (∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (w j) (v j))
          = ∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (x₀ j) (y₀ j) :=
        Finset.prod_congr rfl fun j hj => by
          rw [hx j (Finset.mem_inter.mp hj).1,
            hy j (Finset.mem_inter.mp hj).2]
      have e2 : (∏ j ∈ (insert d.i d.CY : Finset (Fin n))ᶜ, μ (w j) (v j))
          = ∏ j ∈ (insert d.i d.CY : Finset (Fin n))ᶜ, μ (x₀ j) (v j) :=
        Finset.prod_congr rfl fun j hj => by
          rw [hx j ((hcover j).resolve_right (Finset.mem_compl.mp hj))]
      have e3 : (∏ j ∈ (insert d.i d.CX : Finset (Fin n))ᶜ, μ (w j) (v j))
          = ∏ j ∈ (insert d.i d.CX : Finset (Fin n))ᶜ, μ (w j) (y₀ j) :=
        Finset.prod_congr rfl fun j hj => by
          rw [hy j ((hcover j).resolve_left (Finset.mem_compl.mp hj))]
      calc (∏ j, μ (w j) (v j))
          = (∏ j ∈ insert d.i d.CX, μ (w j) (v j)) *
            ∏ j ∈ (insert d.i d.CX : Finset (Fin n))ᶜ, μ (w j) (v j) :=
            (Finset.prod_mul_prod_compl _ _).symm
        _ = ((∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (w j) (v j)) *
            ∏ j ∈ (insert d.i d.CY : Finset (Fin n))ᶜ, μ (w j) (v j)) *
            ∏ j ∈ (insert d.i d.CX : Finset (Fin n))ᶜ, μ (w j) (v j) := by
            rw [hsplitI]
        _ = (∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (x₀ j) (y₀ j)) *
            ((∏ j ∈ (insert d.i d.CX : Finset (Fin n))ᶜ, μ (w j) (y₀ j)) *
             ∏ j ∈ (insert d.i d.CY : Finset (Fin n))ᶜ, μ (x₀ j) (v j)) := by
            rw [e1, e2, e3]; ring
    · rw [if_neg (fun h => hy h.2), if_neg hy, mul_zero, mul_zero]
  · rw [if_neg (fun h => hx h.1), if_neg hx, zero_mul, mul_zero]

/-- Total-mass factorization: summing `priorWeight_eq_mul` over both
words (Fubini). -/
theorem priorWeight_mass_eq (μ : X → Y → ℝ) (x₀ : Fin n → X)
    (y₀ : Fin n → Y) :
    (∑ w : Fin n → X, ∑ v : Fin n → Y, priorWeight d μ x₀ y₀ w v)
      = d.pinnedWeight μ x₀ y₀ *
        ((∑ w : Fin n → X, d.xWeight μ x₀ y₀ w) *
         (∑ v : Fin n → Y, d.yWeight μ x₀ y₀ v)) := by
  classical
  calc (∑ w : Fin n → X, ∑ v : Fin n → Y, priorWeight d μ x₀ y₀ w v)
      = ∑ w : Fin n → X, ∑ v : Fin n → Y, d.pinnedWeight μ x₀ y₀ *
          (d.xWeight μ x₀ y₀ w * d.yWeight μ x₀ y₀ v) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ =>
          d.priorWeight_eq_mul μ x₀ y₀ w v
    _ = d.pinnedWeight μ x₀ y₀ * ∑ w : Fin n → X, ∑ v : Fin n → Y,
          d.xWeight μ x₀ y₀ w * d.yWeight μ x₀ y₀ v := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
    _ = d.pinnedWeight μ x₀ y₀ *
        ((∑ w : Fin n → X, d.xWeight μ x₀ y₀ w) *
         (∑ v : Fin n → Y, d.yWeight μ x₀ y₀ v)) := by
        rw [Finset.sum_mul_sum]

end RevealDatum

namespace TracialStrategy

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable (S : TracialStrategy.{u}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))

/-- Alice's core effect `E_{x^n}^{a_D}`: the repeated POVM effect at the
question word `w` summed over all answer words agreeing with the core
answer word `zA` on `D` (05_prerounding.tex, "Let `E_{x^n}^{a_D}` and
`F_{y^n}^{b_D}` be the repeated POVM effects after summing all answers
outside `D`"). The core word is carried by a full-word representative;
only its `D`-coordinates matter. -/
noncomputable def coreEffectA (D : Finset (Fin n)) (w : Fin n → X)
    (zA : Fin n → A) : S.M.A :=
  ∑ as : Fin n → A, if agreesOn D as zA then S.E w as else 0

/-- Bob's core effect `F_{y^n}^{b_D}`. -/
noncomputable def coreEffectB (D : Finset (Fin n)) (v : Fin n → Y)
    (zB : Fin n → B) : S.M.A :=
  ∑ bs : Fin n → B, if agreesOn D bs zB then S.F v bs else 0

theorem coreEffectA_isPosElem (D : Finset (Fin n)) (w : Fin n → X)
    (zA : Fin n → A) : IsPosElem (S.coreEffectA D w zA) := by
  refine isPosElem_sum _ _ fun as _ => ?_
  split
  · exact S.E_pos _ _
  · exact isPosElem_zero

theorem coreEffectB_isPosElem (D : Finset (Fin n)) (v : Fin n → Y)
    (zB : Fin n → B) : IsPosElem (S.coreEffectB D v zB) := by
  refine isPosElem_sum _ _ fun bs _ => ?_
  split
  · exact S.F_pos _ _
  · exact isPosElem_zero

/-- Bilinear collapse of the core-answer correlation mass: the
probability of answering consistently with the core word `z = (zA, zB)`
at questions `(w, v)` is the trace pairing of the two core effects
(05_prerounding.tex, eq WD-t-z context with eq
tracial-correlation-formula). -/
theorem coreEffect_correlation (D : Finset (Fin n)) (w : Fin n → X)
    (v : Fin n → Y) (zA : Fin n → A) (zB : Fin n → B) :
    (∑ as : Fin n → A, ∑ bs : Fin n → B,
        if agreesOn D as zA ∧ agreesOn D bs zB then
          S.correlation w v as bs else 0)
      = (S.M.τ (star S.σ *
          (S.coreEffectA D w zA * S.σ * S.coreEffectB D v zB))).re := by
  classical
  have hexp : star S.σ *
      (S.coreEffectA D w zA * S.σ * S.coreEffectB D v zB)
      = ∑ as : Fin n → A, ∑ bs : Fin n → B, star S.σ *
          ((if agreesOn D as zA then S.E w as else 0) * S.σ *
            (if agreesOn D bs zB then S.F v bs else 0)) := by
    unfold coreEffectA coreEffectB
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun as _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hexp, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun bs _ => ?_
  by_cases hA : agreesOn D as zA
  · by_cases hB : agreesOn D bs zB
    · rw [if_pos hA, if_pos hB,
        if_pos (show agreesOn D as zA ∧ agreesOn D bs zB from ⟨hA, hB⟩)]
      rfl
    · simp [hA, hB]
  · simp [hA]

variable {D : Finset (Fin n)}

/-- The effective Alice branch effect `H_{r,x} = 𝔼[E_{X^n}^{a_D} ∣ T₀ =
t, X_i = x]` (05_prerounding.tex, eq effective-HK): the
`xWeight`-average of the core effects over Alice's full question word.
The reference word `x₀` carries the revealed values and the live
question `x = x₀ i`; the history's core answers are `zA`. -/
noncomputable def effectiveH (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A) : S.M.A :=
  weightedAvg (d.xWeight μ x₀ y₀) fun w => S.coreEffectA D w zA

/-- The effective Bob branch effect `K_{r,y} = 𝔼[F_{Y^n}^{b_D} ∣ T₀ = t,
Y_i = y]`. -/
noncomputable def effectiveK (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zB : Fin n → B) : S.M.A :=
  weightedAvg (d.yWeight μ x₀ y₀) fun v => S.coreEffectB D v zB

/-- Effective effects are algebraically positive — "finite convex
combinations of positive contractions in `M`" (eq effective-HK;
positivity half, see the header note on contractivity). -/
theorem effectiveH_isPosElem (d : RevealDatum n D) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (x₀ : Fin n → X) (y₀ : Fin n → Y)
    (zA : Fin n → A) : IsPosElem (S.effectiveH d μ x₀ y₀ zA) := by
  unfold effectiveH weightedAvg
  rw [show ((((∑ w : Fin n → X, d.xWeight μ x₀ y₀ w : ℝ)) : ℂ))⁻¹
      = ((((∑ w : Fin n → X, d.xWeight μ x₀ y₀ w)⁻¹ : ℝ)) : ℂ) from
    (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun w _ =>
      d.xWeight_nonneg μ hμ x₀ y₀ w))
  refine isPosElem_sum _ _ fun w _ => ?_
  exact (S.coreEffectA_isPosElem D w zA).smul_ofReal
    (d.xWeight_nonneg μ hμ x₀ y₀ w)

theorem effectiveK_isPosElem (d : RevealDatum n D) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (x₀ : Fin n → X) (y₀ : Fin n → Y)
    (zB : Fin n → B) : IsPosElem (S.effectiveK d μ x₀ y₀ zB) := by
  unfold effectiveK weightedAvg
  rw [show ((((∑ v : Fin n → Y, d.yWeight μ x₀ y₀ v : ℝ)) : ℂ))⁻¹
      = ((((∑ v : Fin n → Y, d.yWeight μ x₀ y₀ v)⁻¹ : ℝ)) : ℂ) from
    (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun v _ =>
      d.yWeight_nonneg μ hμ x₀ y₀ v))
  refine isPosElem_sum _ _ fun v _ => ?_
  exact (S.coreEffectB_isPosElem D v zB).smul_ofReal
    (d.yWeight_nonneg μ hμ x₀ y₀ v)

/-- The live refinement `H_{r,x}^a` (05_prerounding.tex, eq
live-refinements): the effective effect further restricted to live
answer `a` at the live coordinate. -/
noncomputable def effectiveHLive (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A) (a : A) :
    S.M.A :=
  weightedAvg (d.xWeight μ x₀ y₀) fun w =>
    ∑ as : Fin n → A,
      if agreesOn D as zA ∧ as d.i = a then S.E w as else 0

/-- The live refinement of Bob's effective effect. -/
noncomputable def effectiveKLive (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zB : Fin n → B) (b : B) :
    S.M.A :=
  weightedAvg (d.yWeight μ x₀ y₀) fun v =>
    ∑ bs : Fin n → B,
      if agreesOn D bs zB ∧ bs d.i = b then S.F v bs else 0

/-- `H_{r,x} = ∑_a H_{r,x}^a` (eq live-refinements): the live answers
partition each answer word. -/
theorem effectiveH_eq_sum_live (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A) :
    S.effectiveH d μ x₀ y₀ zA
      = ∑ a : A, S.effectiveHLive d μ x₀ y₀ zA a := by
  classical
  have hsplit : ∀ w : Fin n → X, S.coreEffectA D w zA
      = ∑ a : A, ∑ as : Fin n → A,
          if agreesOn D as zA ∧ as d.i = a then S.E w as else 0 := by
    intro w
    unfold coreEffectA
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun as _ => ?_
    by_cases h : agreesOn D as zA
    · simp [h, Finset.sum_ite_eq]
    · simp [h]
  unfold effectiveH effectiveHLive weightedAvg
  rw [← Finset.smul_sum]
  congr 1
  calc (∑ w : Fin n → X,
        ((d.xWeight μ x₀ y₀ w : ℝ) : ℂ) • S.coreEffectA D w zA)
      = ∑ w : Fin n → X, ∑ a : A, ((d.xWeight μ x₀ y₀ w : ℝ) : ℂ) •
          ∑ as : Fin n → A,
            (if agreesOn D as zA ∧ as d.i = a then S.E w as else 0) :=
        Finset.sum_congr rfl fun w _ => by
          rw [hsplit w, Finset.smul_sum]
    _ = ∑ a : A, ∑ w : Fin n → X, ((d.xWeight μ x₀ y₀ w : ℝ) : ℂ) •
          ∑ as : Fin n → A,
            (if agreesOn D as zA ∧ as d.i = a then S.E w as else 0) :=
        Finset.sum_comm

/-- `K_{r,y} = ∑_b K_{r,y}^b` (eq live-refinements). -/
theorem effectiveK_eq_sum_live (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zB : Fin n → B) :
    S.effectiveK d μ x₀ y₀ zB
      = ∑ b : B, S.effectiveKLive d μ x₀ y₀ zB b := by
  classical
  have hsplit : ∀ v : Fin n → Y, S.coreEffectB D v zB
      = ∑ b : B, ∑ bs : Fin n → B,
          if agreesOn D bs zB ∧ bs d.i = b then S.F v bs else 0 := by
    intro v
    unfold coreEffectB
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun bs _ => ?_
    by_cases h : agreesOn D bs zB
    · simp [h, Finset.sum_ite_eq]
    · simp [h]
  unfold effectiveK effectiveKLive weightedAvg
  rw [← Finset.smul_sum]
  congr 1
  calc (∑ v : Fin n → Y,
        ((d.yWeight μ x₀ y₀ v : ℝ) : ℂ) • S.coreEffectB D v zB)
      = ∑ v : Fin n → Y, ∑ b : B, ((d.yWeight μ x₀ y₀ v : ℝ) : ℂ) •
          ∑ bs : Fin n → B,
            (if agreesOn D bs zB ∧ bs d.i = b then S.F v bs else 0) :=
        Finset.sum_congr rfl fun v _ => by
          rw [hsplit v, Finset.smul_sum]
    _ = ∑ b : B, ∑ v : Fin n → Y, ((d.yWeight μ x₀ y₀ v : ℝ) : ℂ) •
          ∑ bs : Fin n → B,
            (if agreesOn D bs zB ∧ bs d.i = b then S.F v bs else 0) :=
        Finset.sum_comm

/-- The locally describable average `H̄_{r,y} = ∑_{x'} μ(x' ∣ y)
H_{r,x'}` (05_prerounding.tex, eq bar-HK): the effective Alice effect
averaged over the live Alice question with the conditional question law
given the live Bob question `y = y₀ i`. -/
noncomputable def effectiveHBar (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A) : S.M.A :=
  weightedAvg (fun x' : X => μ x' (y₀ d.i)) fun x' =>
    S.effectiveH d μ (Function.update x₀ d.i x') y₀ zA

/-- The locally describable average `K̄_{r,x} = ∑_{y'} μ(y' ∣ x)
K_{r,y'}` (eq bar-HK). -/
noncomputable def effectiveKBar (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zB : Fin n → B) : S.M.A :=
  weightedAvg (fun y' : Y => μ (x₀ d.i) y') fun y' =>
    S.effectiveK d μ x₀ (Function.update y₀ d.i y') zB

/-- **Exact branch probability, division-free core** (node 1.2.4;
05_prerounding.tex, eq branch-probability via eq prior-factorization):
the prior-weighted core-answer correlation mass equals the pinned-block
weight times the trace pairing of the unnormalized weighted core
effects. Dividing by the total mass (`branch_probability` below) gives
the manuscript's `p_r(x,y) = τ(σ* H_{r,x} σ K_{r,y})`. -/
theorem branch_probability_core (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A)
    (zB : Fin n → B) :
    (∑ w : Fin n → X, ∑ v : Fin n → Y, priorWeight d μ x₀ y₀ w v *
        ∑ as : Fin n → A, ∑ bs : Fin n → B,
          (if agreesOn D as zA ∧ agreesOn D bs zB then
            S.correlation w v as bs else 0))
      = d.pinnedWeight μ x₀ y₀ *
        (S.M.τ (star S.σ *
          ((∑ w : Fin n → X,
              ((d.xWeight μ x₀ y₀ w : ℝ) : ℂ) • S.coreEffectA D w zA) *
            S.σ *
            (∑ v : Fin n → Y,
              ((d.yWeight μ x₀ y₀ v : ℝ) : ℂ) •
                S.coreEffectB D v zB)))).re := by
  classical
  have hexp : star S.σ *
      ((∑ w : Fin n → X,
          ((d.xWeight μ x₀ y₀ w : ℝ) : ℂ) • S.coreEffectA D w zA) *
        S.σ *
        (∑ v : Fin n → Y,
          ((d.yWeight μ x₀ y₀ v : ℝ) : ℂ) • S.coreEffectB D v zB))
      = ∑ w : Fin n → X, ∑ v : Fin n → Y,
          ((d.xWeight μ x₀ y₀ w : ℝ) : ℂ) •
            (((d.yWeight μ x₀ y₀ v : ℝ) : ℂ) •
              (star S.σ *
                (S.coreEffectA D w zA * S.σ * S.coreEffectB D v zB))) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      mul_smul_comm]
  rw [hexp, map_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [d.priorWeight_eq_mul μ x₀ y₀ w v, S.coreEffect_correlation D w v zA zB]
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

/-- **Exact branch probability** (node 1.2.4; 05_prerounding.tex, eq
branch-probability): on positive conditioning mass, the conditional
probability of the core answers given `(T₀, X_i, Y_i)` is the trace
pairing of the effective effects, `p_r(x,y) = τ(σ* H_{r,x} σ K_{r,y})`.
The mass hypothesis is the manuscript's "Question conditionals are used
only on positive marginal support". -/
theorem branch_probability (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A) (zB : Fin n → B)
    (hmass : 0 < ∑ w : Fin n → X, ∑ v : Fin n → Y,
      priorWeight d μ x₀ y₀ w v) :
    (∑ w : Fin n → X, ∑ v : Fin n → Y, priorWeight d μ x₀ y₀ w v *
        ∑ as : Fin n → A, ∑ bs : Fin n → B,
          (if agreesOn D as zA ∧ agreesOn D bs zB then
            S.correlation w v as bs else 0)) /
      (∑ w : Fin n → X, ∑ v : Fin n → Y, priorWeight d μ x₀ y₀ w v)
      = (S.M.τ (star S.σ *
          (S.effectiveH d μ x₀ y₀ zA * S.σ *
            S.effectiveK d μ x₀ y₀ zB))).re := by
  classical
  have hmassEq := d.priorWeight_mass_eq μ x₀ y₀
  have hP0 : (∑ w : Fin n → X, ∑ v : Fin n → Y,
      priorWeight d μ x₀ y₀ w v) ≠ 0 := ne_of_gt hmass
  have hfac : d.pinnedWeight μ x₀ y₀ *
      ((∑ w : Fin n → X, d.xWeight μ x₀ y₀ w) *
       (∑ v : Fin n → Y, d.yWeight μ x₀ y₀ v)) ≠ 0 := by
    rw [← hmassEq]; exact hP0
  have hc0 : d.pinnedWeight μ x₀ y₀ ≠ 0 := left_ne_zero_of_mul hfac
  have hmx : (∑ w : Fin n → X, d.xWeight μ x₀ y₀ w) ≠ 0 :=
    left_ne_zero_of_mul (right_ne_zero_of_mul hfac)
  have hmy : (∑ v : Fin n → Y, d.yWeight μ x₀ y₀ v) ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul hfac)
  have hRHS : (S.M.τ (star S.σ *
      (S.effectiveH d μ x₀ y₀ zA * S.σ * S.effectiveK d μ x₀ y₀ zB))).re
      = ((∑ w : Fin n → X, d.xWeight μ x₀ y₀ w)⁻¹ *
         (∑ v : Fin n → Y, d.yWeight μ x₀ y₀ v)⁻¹) *
        (S.M.τ (star S.σ *
          ((∑ w : Fin n → X,
              ((d.xWeight μ x₀ y₀ w : ℝ) : ℂ) • S.coreEffectA D w zA) *
            S.σ *
            (∑ v : Fin n → Y,
              ((d.yWeight μ x₀ y₀ v : ℝ) : ℂ) •
                S.coreEffectB D v zB)))).re := by
    unfold effectiveH effectiveK weightedAvg
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv,
      smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  rw [S.branch_probability_core d μ x₀ y₀ zA zB, hRHS, hmassEq]
  field_simp

end TracialStrategy

/-! ## Candidates and the ideal answer law (node 1.2.7)

The consumed corner layer of 05_prerounding.tex, "The common finite
resolver corner" (eqs normalized-candidates, candidate-positivity-order,
ideal-answer-law): normalized candidate vectors from arena branches,
the ideal answer law as the ratio of the arena's two exact identities,
and the positivity orders that keep the local denominators nonzero on
positive posterior edges. The specific wiring of labels
`s = (i, r, x)`, `t = (i, r, y)`, the fallback choices at zero edges,
and the assembly into a `PreroundedStrategy` are node 1.2.11. -/

namespace ResolverArena

open scoped InnerProductSpace

variable {M : StdTracialAlgebra.{0}}
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable {F : I → A → M.A} {G : J → B → M.A}

/-- The normalized candidate vector `u = Φ/‖Φ‖` of eq
normalized-candidates (with Lean's `0⁻¹ = 0`, the zero branch yields the
zero vector; the manuscript's arbitrary fixed unit vectors at zero edges
are a choice of node 1.2.11 that "changes no π-average"). -/
noncomputable def candidate (R : ResolverArena M F G) (σ : M.A)
    (i : I) (j : J) : R.N.H :=
  ((‖R.branch σ i j‖⁻¹ : ℝ) : ℂ) • R.branch σ i j

/-- On a positive branch the candidate is a unit vector ("evaluation by
the relevant positive vector functional proves strictly positive
norm"). -/
theorem candidate_norm (R : ResolverArena M F G) (σ : M.A) (i : I)
    (j : J) (hb : R.branch σ i j ≠ 0) :
    ‖R.candidate σ i j‖ = 1 := by
  unfold candidate
  rw [norm_smul]
  have h0 : ‖R.branch σ i j‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  simp [h0]

/-- **The ideal answer law** (node 1.2.7; 05_prerounding.tex, eq
ideal-answer-law): on a positive branch, the normalized candidate's
answer pairing is the ratio of the arena's exact refinement identity to
its norm identity —
`⟨u, L(A_i^a) R(B_j^b) u⟩ = τ(σ* F_i^a σ G_j^b) / τ(σ* F_i σ G_j)`,
"which is exactly `ℚ(A_i = a, B_i = b ∣ R = r, X_i = x, Y_i = y)`". -/
theorem candidate_answer (R : ResolverArena M F G) (σ : M.A) (i : I)
    (j : J) (a : A) (b : B) (hb : R.branch σ i j ≠ 0) :
    ⟪R.candidate σ i j,
        R.N.L (R.Ameas i a)
          (R.N.Rop (R.Bmeas j b) (R.candidate σ i j))⟫_ℂ
      = M.τ (star σ * (F i a * σ * G j b)) /
        M.τ (star σ * ((∑ a' : A, F i a') * σ * (∑ b' : B, G j b'))) := by
  unfold candidate
  rw [map_smul, map_smul, inner_smul_left, inner_smul_right,
    R.branch_answer σ i j a b, ← R.branch_norm σ i j,
    inner_self_eq_norm_sq_to_K, Complex.conj_ofReal, Complex.ofReal_inv]
  have hnorm : ‖R.branch σ i j‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  norm_cast
  field_simp
  show (((1 / ‖R.branch σ i j‖ : ℝ)) : ℂ) ^ 2 *
      M.τ (star σ * (F i a * σ * G j b))
    = M.τ (star σ * (F i a * σ * G j b)) / ((‖R.branch σ i j‖ ^ 2 : ℝ) : ℂ)
  rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hnorm))]
  have hsc : (((1 / ‖R.branch σ i j‖ : ℝ)) : ℂ) ^ 2 *
      ((‖R.branch σ i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  calc (((1 / ‖R.branch σ i j‖ : ℝ)) : ℂ) ^ 2 *
        M.τ (star σ * (F i a * σ * G j b)) *
        ((‖R.branch σ i j‖ ^ 2 : ℝ) : ℂ)
      = ((((1 / ‖R.branch σ i j‖ : ℝ)) : ℂ) ^ 2 *
          ((‖R.branch σ i j‖ ^ 2 : ℝ) : ℂ)) *
          M.τ (star σ * (F i a * σ * G j b)) := by ring
    _ = M.τ (star σ * (F i a * σ * G j b)) := by rw [hsc, one_mul]

end ResolverArena

namespace TracialStrategy

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable (S : TracialStrategy.{u}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}

/-- **Candidate positivity order, Bob side** (node 1.2.7;
05_prerounding.tex, eq candidate-positivity-order):
`K̄_{r,x} ≽ μ(y ∣ x) K_{r,y}` in the D13 cone — the bar average
dominates each conditional multiple of a single live effect, because the
difference is the nonnegative combination of the remaining live
questions. True with the junk conventions at a vanishing live marginal
(both sides collapse to `0`). -/
theorem effectiveKBar_sub_isPosElem (d : RevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (x₀ : Fin n → X)
    (y₀ : Fin n → Y) (zB : Fin n → B) (y : Y) :
    IsPosElem (S.effectiveKBar d μ x₀ y₀ zB -
      (((μ (x₀ d.i) y / ∑ y' : Y, μ (x₀ d.i) y' : ℝ)) : ℂ) •
        S.effectiveK d μ x₀ (Function.update y₀ d.i y) zB) := by
  have hidentity : S.effectiveKBar d μ x₀ y₀ zB -
      (((μ (x₀ d.i) y / ∑ y' : Y, μ (x₀ d.i) y' : ℝ)) : ℂ) •
        S.effectiveK d μ x₀ (Function.update y₀ d.i y) zB
      = ((((∑ y' : Y, μ (x₀ d.i) y' : ℝ)) : ℂ))⁻¹ •
          ∑ y' ∈ Finset.univ.erase y,
            ((μ (x₀ d.i) y' : ℝ) : ℂ) •
              S.effectiveK d μ x₀ (Function.update y₀ d.i y') zB := by
    simp only [effectiveKBar, weightedAvg]
    rw [Complex.ofReal_div, div_eq_mul_inv,
      mul_comm ((μ (x₀ d.i) y : ℝ) : ℂ), ← smul_smul, ← smul_sub]
    congr 1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ y),
      add_sub_cancel_right]
  rw [hidentity,
    show ((((∑ y' : Y, μ (x₀ d.i) y' : ℝ)) : ℂ))⁻¹
        = ((((∑ y' : Y, μ (x₀ d.i) y')⁻¹ : ℝ)) : ℂ) from
      (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun y' _ => hμ _ _))
  exact isPosElem_sum _ _ fun y' _ =>
    (S.effectiveK_isPosElem d μ hμ x₀ _ zB).smul_ofReal (hμ _ _)

/-- **Candidate positivity order, Alice side** (eq
candidate-positivity-order): `H̄_{r,y} ≽ μ(x ∣ y) H_{r,x}`. -/
theorem effectiveHBar_sub_isPosElem (d : RevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (x₀ : Fin n → X)
    (y₀ : Fin n → Y) (zA : Fin n → A) (x : X) :
    IsPosElem (S.effectiveHBar d μ x₀ y₀ zA -
      (((μ x (y₀ d.i) / ∑ x' : X, μ x' (y₀ d.i) : ℝ)) : ℂ) •
        S.effectiveH d μ (Function.update x₀ d.i x) y₀ zA) := by
  have hidentity : S.effectiveHBar d μ x₀ y₀ zA -
      (((μ x (y₀ d.i) / ∑ x' : X, μ x' (y₀ d.i) : ℝ)) : ℂ) •
        S.effectiveH d μ (Function.update x₀ d.i x) y₀ zA
      = ((((∑ x' : X, μ x' (y₀ d.i) : ℝ)) : ℂ))⁻¹ •
          ∑ x' ∈ Finset.univ.erase x,
            ((μ x' (y₀ d.i) : ℝ) : ℂ) •
              S.effectiveH d μ (Function.update x₀ d.i x') y₀ zA := by
    simp only [effectiveHBar, weightedAvg]
    rw [Complex.ofReal_div, div_eq_mul_inv,
      mul_comm ((μ x (y₀ d.i) : ℝ) : ℂ), ← smul_smul, ← smul_sub]
    congr 1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ x),
      add_sub_cancel_right]
  rw [hidentity,
    show ((((∑ x' : X, μ x' (y₀ d.i) : ℝ)) : ℂ))⁻¹
        = ((((∑ x' : X, μ x' (y₀ d.i))⁻¹ : ℝ)) : ℂ) from
      (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun x' _ => hμ _ _))
  exact isPosElem_sum _ _ fun x' _ =>
    (S.effectiveH_isPosElem d μ hμ _ y₀ zA).smul_ofReal (hμ _ _)

end TracialStrategy

end CommutingRepetition
