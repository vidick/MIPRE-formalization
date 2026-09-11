/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Alignment.lean
-/
/-
# Reveal martingales and live increments (node 1.2.8, operator half)

The reveal martingales of the reverse experiments (05_prerounding.tex,
eqs alice-reveal-martingale, alice-fixed-bob-effect,
alice-live-increment, bob-reveal-martingale, bob-live-increment) over
the classical reverse data of `Prerounding/Histories.lean` and the
signed branch effects of `Prerounding/Branches.lean` (node 1.2.4).

Encoding notes (for the fidelity review):

- The conditional expectations `F_{j,z}(U_A) = 𝔼[E^{a_D} ∣ U_A,
  X_{π_Y[1]}, …, X_{π_Y[j]}]` are encoded by the general revealed-set
  effect `setEffectA`: the reference words pin the revealed
  coordinates, and the unrevealed coordinates are averaged with the
  unnormalized product weights `∏ μ(w_c, yref_c)` — `weightedAvg`
  normalizes, so the weights realize the manuscript's independent
  conditionals `μ(·∣Y_c)` exactly as in the signed `xWeight` (review
  #9). `effectiveH` is literally `setEffectA` at the revealed set
  `{i} ∪ C_X`, and the reveal martingale is `setEffectA` at
  `D ∪ L_X ∪ π_Y[1..j]`.
- The tower property (the martingale property of eq
  alice-reveal-martingale) is the single general step identity
  `setEffectA_reveal`: revealing one more coordinate is averaging over
  its conditional law. It is stated division-free-junk-safe: at a
  vanishing conditional marginal both sides collapse to `0` (given
  `hμ`), so no positivity side condition appears.
- The live-increment identities (eq alice-live-increment) wire the
  martingale at the cut to the signed 1.2.4 effects of the FORWARD
  datum. The forward datum `r` enters as a variable constrained by the
  carryover facts of the signed pushforward statements (review #11)
  PLUS the order-compatibility facts (`r.prefixY` / `r.prefixX` as
  sets) that review #11 recorded as deferred to this operator half —
  here they are explicit hypotheses, discharged by the bijections of
  `aliceReveal_pushforward_eq` / `bobReveal_pushforward_eq` when the
  layer is consumed.
- Only the Alice-reveal chain and its Bob mirror are stated. The
  σ-paired increment bound (eq random-martingale-increment) is the
  entropy budget of node 1.2.6 (`Resolver/EntropyBudget.lean`)
  instantiated at these martingales; the instantiation lives with the
  arena invocation (node 1.2.11).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Histories
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Branches

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

universe u

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-- The revealed-set one-sided weight (generalizing the signed
`RevealDatum.xWeight`, review #9): the `S`-revealed conditioned
unnormalized law of Alice's full question word — consistency with the
reference on the revealed set `S`, times the pinned-Bob halves of the
free coordinates' joint laws. -/
noncomputable def setWeightX (S : Finset (Fin n)) (μ : X → Y → ℝ)
    (xref : Fin n → X) (yref : Fin n → Y) (w : Fin n → X) : ℝ :=
  if agreesOn S w xref then ∏ j ∈ Sᶜ, μ (w j) (yref j) else 0

/-- The revealed-set one-sided weight for Bob's word. -/
noncomputable def setWeightY (S : Finset (Fin n)) (μ : X → Y → ℝ)
    (xref : Fin n → X) (yref : Fin n → Y) (v : Fin n → Y) : ℝ :=
  if agreesOn S v yref then ∏ j ∈ Sᶜ, μ (xref j) (v j) else 0

namespace TracialStrategy

variable (S : TracialStrategy.{u}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}

/-- The revealed-set Alice effect
`𝔼[E^{a_D} ∣ X revealed on R₀, Bob's word]` (05_prerounding.tex, the
conditional expectations of eq alice-reveal-martingale, general
revealed set): the `setWeightX`-average of the core effects. -/
noncomputable def setEffectA (D : Finset (Fin n)) (R₀ : Finset (Fin n))
    (μ : X → Y → ℝ) (xref : Fin n → X) (yref : Fin n → Y)
    (zA : Fin n → A) : S.M.A :=
  weightedAvg (setWeightX R₀ μ xref yref) fun w => S.coreEffectA D w zA

/-- The revealed-set Bob effect (mirror). -/
noncomputable def setEffectB (D : Finset (Fin n)) (R₀ : Finset (Fin n))
    (μ : X → Y → ℝ) (xref : Fin n → X) (yref : Fin n → Y)
    (zB : Fin n → B) : S.M.A :=
  weightedAvg (setWeightY R₀ μ xref yref) fun v => S.coreEffectB D v zB

/-- `effectiveH` is the revealed-set effect at `{i} ∪ C_X` (the signed
node-1.2.4 encoding, re-expressed; definitional). -/
theorem effectiveH_eq_setEffectA (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zA : Fin n → A) :
    S.effectiveH d μ x₀ y₀ zA
      = S.setEffectA D (insert d.i d.CX) μ x₀ y₀ zA := rfl

/-- `effectiveK` is the revealed-set effect at `{i} ∪ C_Y`
(definitional). -/
theorem effectiveK_eq_setEffectB (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y) (zB : Fin n → B) :
    S.effectiveK d μ x₀ y₀ zB
      = S.setEffectB D (insert d.i d.CY) μ x₀ y₀ zB := rfl

/-- **One-step reveal identity, Alice side** (the tower property making
eq alice-reveal-martingale a martingale): revealing one more
coordinate `c` is averaging over its conditional law `μ(·∣yref c)`.
Junk-safe: at a vanishing conditional marginal both sides are `0`. -/
theorem setEffectA_reveal (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y)
    (zA : Fin n → A) (c : Fin n) (hc : c ∉ R₀) :
    S.setEffectA D R₀ μ xref yref zA
      = weightedAvg (fun x' : X => μ x' (yref c)) fun x' =>
          S.setEffectA D (insert c R₀) μ (Function.update xref c x')
            yref zA := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI : Nonempty (Fin n) := ⟨c⟩
    simp only [setEffectA, weightedAvg]
    rw [Finset.univ_eq_empty (α := Fin n → X), Finset.univ_eq_empty (α := X)]
    simp
  set e := Equiv.piSplitAt c (fun _ : Fin n => X) with he
  have hsymm_c : ∀ (v : X) (g : {j : Fin n // j ≠ c} → X),
      e.symm (v, g) c = v := by
    intro v g
    simp [he, Equiv.piSplitAt_symm_apply]
  have hsymm_ne : ∀ (v : X) (g : {j : Fin n // j ≠ c} → X) (j : Fin n)
      (hj : j ≠ c), e.symm (v, g) j = g ⟨j, hj⟩ := by
    intro v g j hj
    simp [he, Equiv.piSplitAt_symm_apply, hj]
  -- reindex word sums through the split at `c`
  have hsumA : ∀ (F : (Fin n → X) → S.M.A),
      (∑ w : Fin n → X, F w)
        = ∑ v : X, ∑ g : {j : Fin n // j ≠ c} → X, F (e.symm (v, g)) := by
    intro F
    rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
      (fun w => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
  have hsumR : ∀ (F : (Fin n → X) → ℝ),
      (∑ w : Fin n → X, F w)
        = ∑ v : X, ∑ g : {j : Fin n // j ≠ c} → X, F (e.symm (v, g)) := by
    intro F
    rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
      (fun w => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
  -- the inner weight after recombination, and its two key properties
  set W1 : X → ({j : Fin n // j ≠ c} → X) → ℝ := fun v g =>
    setWeightX (insert c R₀) μ (Function.update xref c v) yref
      (e.symm (v, g)) with hW1def
  -- (F2) off-diagonal vanishing: the full inner weight at reference `x'`
  -- vanishes on recombined words with `v ≠ x'`
  have hF2 : ∀ (x' v : X) (g : {j : Fin n // j ≠ c} → X), v ≠ x' →
      setWeightX (insert c R₀) μ (Function.update xref c x') yref
        (e.symm (v, g)) = 0 := by
    intro x' v g hne
    unfold setWeightX
    rw [if_neg]
    intro hagree
    have h1 := hagree c (Finset.mem_insert_self c R₀)
    rw [hsymm_c, Function.update_self] at h1
    exact hne h1
  -- (F1) weight split: the outer weight factors through the live value
  have hsplit : ∀ (v : X) (g : {j : Fin n // j ≠ c} → X),
      setWeightX R₀ μ xref yref (e.symm (v, g))
        = μ v (yref c) * W1 v g := by
    intro v g
    simp only [hW1def]
    unfold setWeightX
    by_cases hA : agreesOn R₀ (e.symm (v, g)) xref
    · have hA' : agreesOn (insert c R₀) (e.symm (v, g))
          (Function.update xref c v) := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjR
        · rw [hsymm_c, Function.update_self]
        · have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
          rw [Function.update_of_ne hjc, hA j hjR]
      rw [if_pos hA, if_pos hA',
        ← Finset.mul_prod_erase (R₀ᶜ) _ (Finset.mem_compl.mpr hc),
        hsymm_c, ← Finset.compl_insert]
    · have hA' : ¬agreesOn (insert c R₀) (e.symm (v, g))
          (Function.update xref c v) := by
        intro hagree
        refine hA fun j hjR => ?_
        have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
        have := hagree j (Finset.mem_insert_of_mem hjR)
        rwa [Function.update_of_ne hjc] at this
      rw [if_neg hA, if_neg hA', mul_zero]
  -- the inner weight and the recombined effect do not see the live slot
  have hW1indep : ∀ (v v' : X) (g : {j : Fin n // j ≠ c} → X),
      W1 v g = W1 v' g := by
    intro v v' g
    simp only [hW1def]
    unfold setWeightX
    have hiff : ∀ (a : X),
        agreesOn (insert c R₀) (e.symm (a, g)) (Function.update xref c a)
          ↔ ∀ j (hjR : j ∈ R₀), g ⟨j, fun hjc => hc (hjc ▸ hjR)⟩ = xref j := by
      intro a
      constructor
      · intro hagree j hjR
        have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
        have := hagree j (Finset.mem_insert_of_mem hjR)
        rwa [hsymm_ne a g j hjc, Function.update_of_ne hjc] at this
      · intro hg j hj
        rcases Finset.mem_insert.mp hj with rfl | hjR
        · rw [hsymm_c, Function.update_self]
        · have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
          rw [hsymm_ne a g j hjc, Function.update_of_ne hjc]
          exact hg j hjR
    have hprod : ∀ (a : X),
        (∏ j ∈ (insert c R₀)ᶜ, μ (e.symm (a, g) j) (yref j))
          = ∏ j ∈ (insert c R₀)ᶜ,
              μ (e.symm (v, g) j) (yref j) := by
      intro a
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjc : j ≠ c := by
        intro hjc
        exact (Finset.mem_compl.mp hj) (hjc ▸ Finset.mem_insert_self c R₀)
      rw [hsymm_ne a g j hjc, hsymm_ne v g j hjc]
    rw [if_congr ((hiff v).trans (hiff v').symm) (hprod v').symm rfl]
  -- collapse a full-word inner sum to the matching live value
  have hinnerR : ∀ (x' : X),
      (∑ w : Fin n → X,
          setWeightX (insert c R₀) μ (Function.update xref c x') yref w)
        = ∑ g : {j : Fin n // j ≠ c} → X, W1 x' g := by
    intro x'
    rw [hsumR]
    refine Fintype.sum_eq_single x' (fun v hv => ?_) |>.trans ?_
    · exact Finset.sum_eq_zero fun g _ => hF2 x' v g hv
    · rfl
  have hinnerA : ∀ (x' : X),
      (∑ w : Fin n → X,
          ((setWeightX (insert c R₀) μ (Function.update xref c x') yref w
            : ℝ) : ℂ) • S.coreEffectA D w zA)
        = ∑ g : {j : Fin n // j ≠ c} → X,
            ((W1 x' g : ℝ) : ℂ) • S.coreEffectA D (e.symm (x', g)) zA := by
    intro x'
    rw [hsumA]
    refine Fintype.sum_eq_single x' (fun v hv => ?_) |>.trans ?_
    · exact Finset.sum_eq_zero fun g _ => by
        rw [hF2 x' v g hv]
        simp
    · rfl
  -- assemble
  simp only [setEffectA, weightedAvg]
  rw [hsumR, hsumA]
  have hmass : (∑ v : X, ∑ g : {j : Fin n // j ≠ c} → X,
      setWeightX R₀ μ xref yref (e.symm (v, g)))
      = ∑ v : X, μ v (yref c) * ∑ g : {j : Fin n // j ≠ c} → X, W1 v g := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => hsplit v g
  have hnum : (∑ v : X, ∑ g : {j : Fin n // j ≠ c} → X,
      ((setWeightX R₀ μ xref yref (e.symm (v, g)) : ℝ) : ℂ) •
        S.coreEffectA D (e.symm (v, g)) zA)
      = ∑ v : X, ((μ v (yref c) : ℝ) : ℂ) •
          ∑ g : {j : Fin n // j ≠ c} → X,
            ((W1 v g : ℝ) : ℂ) • S.coreEffectA D (e.symm (v, g)) zA := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hsplit v g, Complex.ofReal_mul, smul_smul]
  rw [hmass, hnum]
  -- rewrite the right side's inner averages via the collapse lemmas
  have hRHS : ∀ (x' : X),
      ((((∑ w : Fin n → X, setWeightX (insert c R₀) μ
          (Function.update xref c x') yref w : ℝ)) : ℂ))⁻¹ •
        (∑ w : Fin n → X,
          ((setWeightX (insert c R₀) μ (Function.update xref c x') yref w
            : ℝ) : ℂ) • S.coreEffectA D w zA)
        = ((((∑ g : {j : Fin n // j ≠ c} → X, W1 x' g : ℝ)) : ℂ))⁻¹ •
            ∑ g : {j : Fin n // j ≠ c} → X,
              ((W1 x' g : ℝ) : ℂ) • S.coreEffectA D (e.symm (x', g)) zA := by
    intro x'
    rw [hinnerR, hinnerA]
  simp only [hRHS]
  -- mass constancy lets the inner normalization be pulled out
  set K : ℝ := ∑ g : {j : Fin n // j ≠ c} → X, W1 (Classical.arbitrary X) g
    with hKdef
  have hKconst : ∀ (v : X),
      (∑ g : {j : Fin n // j ≠ c} → X, W1 v g) = K := by
    intro v
    rw [hKdef]
    exact Finset.sum_congr rfl fun g _ => hW1indep v (Classical.arbitrary X) g
  simp only [hKconst]
  have hmass2 : (∑ v : X, μ v (yref c) * K)
      = (∑ v : X, μ v (yref c)) * K := by
    rw [Finset.sum_mul]
  rw [hmass2, Complex.ofReal_mul, mul_inv]
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_smul, smul_comm (((K : ℝ) : ℂ))⁻¹ (((μ v (yref c) : ℝ)) : ℂ)]

/-- **One-step reveal identity, Bob side** (the tower property of eq
bob-reveal-martingale). -/
theorem setEffectB_reveal (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y)
    (zB : Fin n → B) (c : Fin n) (hc : c ∉ R₀) :
    S.setEffectB D R₀ μ xref yref zB
      = weightedAvg (fun y' : Y => μ (xref c) y') fun y' =>
          S.setEffectB D (insert c R₀) μ xref (Function.update yref c y')
            zB := by
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · haveI : Nonempty (Fin n) := ⟨c⟩
    simp only [setEffectB, weightedAvg]
    rw [Finset.univ_eq_empty (α := Fin n → Y), Finset.univ_eq_empty (α := Y)]
    simp
  set e := Equiv.piSplitAt c (fun _ : Fin n => Y) with he
  have hsymm_c : ∀ (v : Y) (g : {j : Fin n // j ≠ c} → Y),
      e.symm (v, g) c = v := by
    intro v g
    simp [he, Equiv.piSplitAt_symm_apply]
  have hsymm_ne : ∀ (v : Y) (g : {j : Fin n // j ≠ c} → Y) (j : Fin n)
      (hj : j ≠ c), e.symm (v, g) j = g ⟨j, hj⟩ := by
    intro v g j hj
    simp [he, Equiv.piSplitAt_symm_apply, hj]
  have hsumA : ∀ (F : (Fin n → Y) → S.M.A),
      (∑ w : Fin n → Y, F w)
        = ∑ v : Y, ∑ g : {j : Fin n // j ≠ c} → Y, F (e.symm (v, g)) := by
    intro F
    rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
      (fun w => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
  have hsumR : ∀ (F : (Fin n → Y) → ℝ),
      (∑ w : Fin n → Y, F w)
        = ∑ v : Y, ∑ g : {j : Fin n // j ≠ c} → Y, F (e.symm (v, g)) := by
    intro F
    rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
      (fun w => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
  set W1 : Y → ({j : Fin n // j ≠ c} → Y) → ℝ := fun v g =>
    setWeightY (insert c R₀) μ xref (Function.update yref c v)
      (e.symm (v, g)) with hW1def
  have hF2 : ∀ (y' v : Y) (g : {j : Fin n // j ≠ c} → Y), v ≠ y' →
      setWeightY (insert c R₀) μ xref (Function.update yref c y')
        (e.symm (v, g)) = 0 := by
    intro y' v g hne
    unfold setWeightY
    rw [if_neg]
    intro hagree
    have h1 := hagree c (Finset.mem_insert_self c R₀)
    rw [hsymm_c, Function.update_self] at h1
    exact hne h1
  have hsplit : ∀ (v : Y) (g : {j : Fin n // j ≠ c} → Y),
      setWeightY R₀ μ xref yref (e.symm (v, g))
        = μ (xref c) v * W1 v g := by
    intro v g
    simp only [hW1def]
    unfold setWeightY
    by_cases hA : agreesOn R₀ (e.symm (v, g)) yref
    · have hA' : agreesOn (insert c R₀) (e.symm (v, g))
          (Function.update yref c v) := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjR
        · rw [hsymm_c, Function.update_self]
        · have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
          rw [Function.update_of_ne hjc, hA j hjR]
      rw [if_pos hA, if_pos hA',
        ← Finset.mul_prod_erase (R₀ᶜ) _ (Finset.mem_compl.mpr hc),
        hsymm_c, ← Finset.compl_insert]
    · have hA' : ¬agreesOn (insert c R₀) (e.symm (v, g))
          (Function.update yref c v) := by
        intro hagree
        refine hA fun j hjR => ?_
        have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
        have := hagree j (Finset.mem_insert_of_mem hjR)
        rwa [Function.update_of_ne hjc] at this
      rw [if_neg hA, if_neg hA', mul_zero]
  have hW1indep : ∀ (v v' : Y) (g : {j : Fin n // j ≠ c} → Y),
      W1 v g = W1 v' g := by
    intro v v' g
    simp only [hW1def]
    unfold setWeightY
    have hiff : ∀ (a : Y),
        agreesOn (insert c R₀) (e.symm (a, g)) (Function.update yref c a)
          ↔ ∀ j (hjR : j ∈ R₀), g ⟨j, fun hjc => hc (hjc ▸ hjR)⟩ = yref j := by
      intro a
      constructor
      · intro hagree j hjR
        have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
        have := hagree j (Finset.mem_insert_of_mem hjR)
        rwa [hsymm_ne a g j hjc, Function.update_of_ne hjc] at this
      · intro hg j hj
        rcases Finset.mem_insert.mp hj with rfl | hjR
        · rw [hsymm_c, Function.update_self]
        · have hjc : j ≠ c := fun hjc => hc (hjc ▸ hjR)
          rw [hsymm_ne a g j hjc, Function.update_of_ne hjc]
          exact hg j hjR
    have hprod : ∀ (a : Y),
        (∏ j ∈ (insert c R₀)ᶜ, μ (xref j) (e.symm (a, g) j))
          = ∏ j ∈ (insert c R₀)ᶜ,
              μ (xref j) (e.symm (v, g) j) := by
      intro a
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjc : j ≠ c := by
        intro hjc
        exact (Finset.mem_compl.mp hj) (hjc ▸ Finset.mem_insert_self c R₀)
      rw [hsymm_ne a g j hjc, hsymm_ne v g j hjc]
    rw [if_congr ((hiff v).trans (hiff v').symm) (hprod v').symm rfl]
  have hinnerR : ∀ (y' : Y),
      (∑ w : Fin n → Y,
          setWeightY (insert c R₀) μ xref (Function.update yref c y') w)
        = ∑ g : {j : Fin n // j ≠ c} → Y, W1 y' g := by
    intro y'
    rw [hsumR]
    refine Fintype.sum_eq_single y' (fun v hv => ?_) |>.trans ?_
    · exact Finset.sum_eq_zero fun g _ => hF2 y' v g hv
    · rfl
  have hinnerA : ∀ (y' : Y),
      (∑ w : Fin n → Y,
          ((setWeightY (insert c R₀) μ xref (Function.update yref c y') w
            : ℝ) : ℂ) • S.coreEffectB D w zB)
        = ∑ g : {j : Fin n // j ≠ c} → Y,
            ((W1 y' g : ℝ) : ℂ) • S.coreEffectB D (e.symm (y', g)) zB := by
    intro y'
    rw [hsumA]
    refine Fintype.sum_eq_single y' (fun v hv => ?_) |>.trans ?_
    · exact Finset.sum_eq_zero fun g _ => by
        rw [hF2 y' v g hv]
        simp
    · rfl
  simp only [setEffectB, weightedAvg]
  rw [hsumR, hsumA]
  have hmass : (∑ v : Y, ∑ g : {j : Fin n // j ≠ c} → Y,
      setWeightY R₀ μ xref yref (e.symm (v, g)))
      = ∑ v : Y, μ (xref c) v * ∑ g : {j : Fin n // j ≠ c} → Y, W1 v g := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => hsplit v g
  have hnum : (∑ v : Y, ∑ g : {j : Fin n // j ≠ c} → Y,
      ((setWeightY R₀ μ xref yref (e.symm (v, g)) : ℝ) : ℂ) •
        S.coreEffectB D (e.symm (v, g)) zB)
      = ∑ v : Y, ((μ (xref c) v : ℝ) : ℂ) •
          ∑ g : {j : Fin n // j ≠ c} → Y,
            ((W1 v g : ℝ) : ℂ) • S.coreEffectB D (e.symm (v, g)) zB := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hsplit v g, Complex.ofReal_mul, smul_smul]
  rw [hmass, hnum]
  have hRHS : ∀ (y' : Y),
      ((((∑ w : Fin n → Y, setWeightY (insert c R₀) μ xref
          (Function.update yref c y') w : ℝ)) : ℂ))⁻¹ •
        (∑ w : Fin n → Y,
          ((setWeightY (insert c R₀) μ xref (Function.update yref c y') w
            : ℝ) : ℂ) • S.coreEffectB D w zB)
        = ((((∑ g : {j : Fin n // j ≠ c} → Y, W1 y' g : ℝ)) : ℂ))⁻¹ •
            ∑ g : {j : Fin n // j ≠ c} → Y,
              ((W1 y' g : ℝ) : ℂ) • S.coreEffectB D (e.symm (y', g)) zB := by
    intro y'
    rw [hinnerR, hinnerA]
  simp only [hRHS]
  set K : ℝ := ∑ g : {j : Fin n // j ≠ c} → Y, W1 (Classical.arbitrary Y) g
    with hKdef
  have hKconst : ∀ (v : Y),
      (∑ g : {j : Fin n // j ≠ c} → Y, W1 v g) = K := by
    intro v
    rw [hKdef]
    exact Finset.sum_congr rfl fun g _ => hW1indep v (Classical.arbitrary Y) g
  simp only [hKconst]
  have hmass2 : (∑ v : Y, μ (xref c) v * K)
      = (∑ v : Y, μ (xref c) v) * K := by
    rw [Finset.sum_mul]
  rw [hmass2, Complex.ofReal_mul, mul_inv]
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_smul, smul_comm (((K : ℝ) : ℂ))⁻¹ (((μ (xref c) v : ℝ)) : ℂ)]

end TracialStrategy

namespace AliceRevealDatum

variable {D : Finset (Fin n)} (d : AliceRevealDatum n D)

/-- The first `j` entries of the reverse Bob-block order `π_Y`, as a
set: the progressively revealed coordinates of eq
alice-reveal-martingale. -/
def revealPrefix (j : Fin (d.LYp.card + 1)) : Finset (Fin n) :=
  (Finset.univ.filter fun t : Fin d.LYp.card => (t : ℕ) < (j : ℕ)).image
    fun t => (d.πY t : Fin n)

/-- The forward Alice-block prefix `π_X^{≤ k_X}` carried by the reverse
datum, as a set. -/
def alicePrefixX : Finset (Fin n) :=
  (Finset.univ.filter fun t : Fin d.LX.card => (t : ℕ) < (d.kX : ℕ)).image
    fun t => (d.πX t : Fin n)

/-- The reveal prefix grows by exactly the live coordinate at the cut:
`π_Y[1..k_Y+1] = {π_Y[k_Y+1]} ∪ π_Y[1..k_Y]` (aux). -/
theorem revealPrefix_succ :
    d.revealPrefix d.kY.succ
      = insert d.liveIdx (d.revealPrefix d.kY.castSucc) := by
  ext c
  simp only [revealPrefix, liveIdx, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Fin.val_succ,
    Fin.coe_castSucc]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact Or.inr ⟨t, h, rfl⟩
    · exact Or.inl (by rw [Fin.ext h])
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨d.kY, Nat.lt_succ_self _, rfl⟩
    · exact ⟨t, Nat.lt_succ_of_lt ht, rfl⟩

end AliceRevealDatum

namespace BobRevealDatum

variable {D : Finset (Fin n)} (d : BobRevealDatum n D)

/-- The first `j` entries of the reverse Alice-block order `π_X`, as a
set (eq bob-reveal-martingale). -/
def revealPrefix (j : Fin (d.LXp.card + 1)) : Finset (Fin n) :=
  (Finset.univ.filter fun t : Fin d.LXp.card => (t : ℕ) < (j : ℕ)).image
    fun t => (d.πX t : Fin n)

/-- The forward Bob-block prefix `π_Y^{≤ k_Y}` carried by the reverse
datum, as a set. -/
def bobPrefixY : Finset (Fin n) :=
  (Finset.univ.filter fun t : Fin d.LY.card => (t : ℕ) < (d.kY : ℕ)).image
    fun t => (d.πY t : Fin n)

/-- The reveal prefix grows by exactly the live coordinate at the cut
(aux, mirror). -/
theorem revealPrefix_succ :
    d.revealPrefix d.kX.succ
      = insert d.liveIdx (d.revealPrefix d.kX.castSucc) := by
  ext c
  simp only [revealPrefix, liveIdx, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Fin.val_succ,
    Fin.coe_castSucc]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact Or.inr ⟨t, h, rfl⟩
    · exact Or.inl (by rw [Fin.ext h])
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨d.kX, Nat.lt_succ_self _, rfl⟩
    · exact ⟨t, Nat.lt_succ_of_lt ht, rfl⟩

end BobRevealDatum

namespace TracialStrategy

variable (S : TracialStrategy.{u}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}

/-- **The Alice reveal martingale** `F_{j,z}(U_A)`
(05_prerounding.tex, eq alice-reveal-martingale): the revealed-set
Alice effect after the background `D ∪ L_X` plus the first `j` entries
of the Bob-block order. -/
noncomputable def revealMartA (d : AliceRevealDatum n D)
    (μ : X → Y → ℝ) (xref : Fin n → X) (yref : Fin n → Y)
    (zA : Fin n → A) (j : Fin (d.LYp.card + 1)) : S.M.A :=
  S.setEffectA D (D ∪ d.LX ∪ d.revealPrefix j) μ xref yref zA

/-- **The Bob reveal martingale** `G_{j,z}(U_B)` (eq
bob-reveal-martingale, mirror). -/
noncomputable def revealMartB (d : BobRevealDatum n D)
    (μ : X → Y → ℝ) (xref : Fin n → X) (yref : Fin n → Y)
    (zB : Fin n → B) (j : Fin (d.LXp.card + 1)) : S.M.A :=
  S.setEffectB D (D ∪ d.LY ∪ d.revealPrefix j) μ xref yref zB

/-- **Live increment, Alice side, lower cut** (node 1.2.8;
05_prerounding.tex, eq alice-live-increment first identity):
`F_{k_Y,z} = H̄_{r,Y_i}` — at the cut, the reveal martingale is the
bar-averaged effective effect of the forward datum. The forward datum
`r` is pinned by the signed pushforward carryover (review #11) plus
the order-compatibility facts deferred to this operator half. -/
theorem revealMartA_cut_eq_effectiveHBar (d : AliceRevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X)
    (yref : Fin n → Y) (zA : Fin n → A) (r : RevealDatum n D)
    (hi : r.i = d.liveIdx) (hLX : r.LX = d.LX)
    (hpre : r.prefixY = d.revealPrefix d.kY.castSucc) :
    S.revealMartA d μ xref yref zA d.kY.castSucc
      = S.effectiveHBar r μ xref yref zA := by
  have hCX : r.CX = D ∪ d.LX ∪ d.revealPrefix d.kY.castSucc := by
    rw [show r.CX = D ∪ r.LX ∪ r.prefixY from rfl, hLX, hpre]
  have hnotmem : d.liveIdx ∉ D ∪ d.LX ∪ d.revealPrefix d.kY.castSucc := by
    simp only [Finset.mem_union, not_or]
    refine ⟨⟨d.liveIdx_notMem_core, fun h => ?_⟩, fun h => ?_⟩
    · exact Finset.disjoint_left.mp d.disjoint h d.liveIdx_mem
    · simp only [AliceRevealDatum.revealPrefix, AliceRevealDatum.liveIdx,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSucc] at h
      obtain ⟨t, ht, heq⟩ := h
      have h2 : t = d.kY := d.πY.injective (Subtype.ext heq)
      rw [h2] at ht
      exact lt_irrefl _ ht
  rw [show S.revealMartA d μ xref yref zA d.kY.castSucc
      = S.setEffectA D (D ∪ d.LX ∪ d.revealPrefix d.kY.castSucc) μ
          xref yref zA from rfl,
    S.setEffectA_reveal D _ μ hμ xref yref zA d.liveIdx hnotmem]
  simp only [effectiveHBar, effectiveH_eq_setEffectA, hi, hCX]

/-- **Live increment, Alice side, upper cut** (eq alice-live-increment
second identity): `F_{k_Y+1,z} = H_{r,X_i}` — one step past the cut,
the reveal martingale is the effective effect itself. -/
theorem revealMartA_cutSucc_eq_effectiveH (d : AliceRevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X)
    (yref : Fin n → Y) (zA : Fin n → A) (r : RevealDatum n D)
    (hi : r.i = d.liveIdx) (hLX : r.LX = d.LX)
    (hpre : r.prefixY = d.revealPrefix d.kY.castSucc) :
    S.revealMartA d μ xref yref zA d.kY.succ
      = S.effectiveH r μ xref yref zA := by
  have hCX : r.CX = D ∪ d.LX ∪ d.revealPrefix d.kY.castSucc := by
    rw [show r.CX = D ∪ r.LX ∪ r.prefixY from rfl, hLX, hpre]
  rw [show S.revealMartA d μ xref yref zA d.kY.succ
      = S.setEffectA D (D ∪ d.LX ∪ d.revealPrefix d.kY.succ) μ
          xref yref zA from rfl,
    S.effectiveH_eq_setEffectA r μ xref yref zA, hi, hCX,
    d.revealPrefix_succ, Finset.union_insert]

/-- **The fixed Bob effect under the Alice-reveal background** (eq
alice-fixed-bob-effect with eq alice-live-increment third identity):
`K_z(U_A) = 𝔼[F^{b_D} ∣ U_A] = K_{r,Y_i}` — Bob's word is revealed on
`D ∪ L_Y⁺ ∪ π_X^{≤k_X}`, which is exactly the forward `{i} ∪ C_Y`. -/
theorem aliceFixedBobEffect_eq_effectiveK (d : AliceRevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X)
    (yref : Fin n → Y) (zB : Fin n → B) (r : RevealDatum n D)
    (hi : r.i = d.liveIdx) (hLY : r.LY = d.LYp.erase d.liveIdx)
    (hpx : r.prefixX = d.alicePrefixX) :
    S.setEffectB D (D ∪ d.LYp ∪ d.alicePrefixX) μ xref yref zB
      = S.effectiveK r μ xref yref zB := by
  have hCY : r.CY = D ∪ d.LYp.erase d.liveIdx ∪ d.alicePrefixX := by
    rw [show r.CY = D ∪ r.LY ∪ r.prefixX from rfl, hLY, hpx]
  rw [S.effectiveK_eq_setEffectB r μ xref yref zB, hi, hCY,
    ← Finset.insert_union, ← Finset.union_insert,
    Finset.insert_erase d.liveIdx_mem]

/-- **Live increment, Bob side, lower cut** (eq bob-live-increment
first identity): `G_{k_X,z} = K̄_{r,X_i}`. -/
theorem revealMartB_cut_eq_effectiveKBar (d : BobRevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X)
    (yref : Fin n → Y) (zB : Fin n → B) (r : RevealDatum n D)
    (hi : r.i = d.liveIdx) (hLY : r.LY = d.LY)
    (hpre : r.prefixX = d.revealPrefix d.kX.castSucc) :
    S.revealMartB d μ xref yref zB d.kX.castSucc
      = S.effectiveKBar r μ xref yref zB := by
  have hCY : r.CY = D ∪ d.LY ∪ d.revealPrefix d.kX.castSucc := by
    rw [show r.CY = D ∪ r.LY ∪ r.prefixX from rfl, hLY, hpre]
  have hnotD : d.liveIdx ∉ D := by
    have h1 : d.liveIdx ∈ Dᶜ := by
      rw [← d.partition]
      exact Finset.mem_union_left _ d.liveIdx_mem
    exact Finset.mem_compl.mp h1
  have hnotmem : d.liveIdx ∉ D ∪ d.LY ∪ d.revealPrefix d.kX.castSucc := by
    simp only [Finset.mem_union, not_or]
    refine ⟨⟨hnotD, fun h => ?_⟩, fun h => ?_⟩
    · exact Finset.disjoint_left.mp d.disjoint d.liveIdx_mem h
    · simp only [BobRevealDatum.revealPrefix, BobRevealDatum.liveIdx,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSucc] at h
      obtain ⟨t, ht, heq⟩ := h
      have h2 : t = d.kX := d.πX.injective (Subtype.ext heq)
      rw [h2] at ht
      exact lt_irrefl _ ht
  rw [show S.revealMartB d μ xref yref zB d.kX.castSucc
      = S.setEffectB D (D ∪ d.LY ∪ d.revealPrefix d.kX.castSucc) μ
          xref yref zB from rfl,
    S.setEffectB_reveal D _ μ hμ xref yref zB d.liveIdx hnotmem]
  simp only [effectiveKBar, effectiveK_eq_setEffectB, hi, hCY]

/-- **Live increment, Bob side, upper cut** (eq bob-live-increment
second identity): `G_{k_X+1,z} = K_{r,Y_i}`. -/
theorem revealMartB_cutSucc_eq_effectiveK (d : BobRevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X)
    (yref : Fin n → Y) (zB : Fin n → B) (r : RevealDatum n D)
    (hi : r.i = d.liveIdx) (hLY : r.LY = d.LY)
    (hpre : r.prefixX = d.revealPrefix d.kX.castSucc) :
    S.revealMartB d μ xref yref zB d.kX.succ
      = S.effectiveK r μ xref yref zB := by
  have hCY : r.CY = D ∪ d.LY ∪ d.revealPrefix d.kX.castSucc := by
    rw [show r.CY = D ∪ r.LY ∪ r.prefixX from rfl, hLY, hpre]
  rw [show S.revealMartB d μ xref yref zB d.kX.succ
      = S.setEffectB D (D ∪ d.LY ∪ d.revealPrefix d.kX.succ) μ
          xref yref zB from rfl,
    S.effectiveK_eq_setEffectB r μ xref yref zB, hi, hCY,
    d.revealPrefix_succ, Finset.union_insert]

/-- **The fixed Alice effect under the Bob-reveal background** (eq
bob-live-increment third identity): `H_z(U_B) = H_{r,X_i}`. -/
theorem bobFixedAliceEffect_eq_effectiveH (d : BobRevealDatum n D)
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X)
    (yref : Fin n → Y) (zA : Fin n → A) (r : RevealDatum n D)
    (hi : r.i = d.liveIdx) (hLX : r.LX = d.LXp.erase d.liveIdx)
    (hpy : r.prefixY = d.bobPrefixY) :
    S.setEffectA D (D ∪ d.LXp ∪ d.bobPrefixY) μ xref yref zA
      = S.effectiveH r μ xref yref zA := by
  have hCX : r.CX = D ∪ d.LXp.erase d.liveIdx ∪ d.bobPrefixY := by
    rw [show r.CX = D ∪ r.LX ∪ r.prefixY from rfl, hLX, hpy]
  rw [S.effectiveH_eq_setEffectA r μ xref yref zA, hi, hCX,
    ← Finset.insert_union, ← Finset.union_insert,
    Finset.insert_erase d.liveIdx_mem]

end TracialStrategy

/-! ## Strengthened pushforwards (review-#14 note N3)

The signed pushforward statements (review #11) carry the live
coordinate, the blocks, and the cut values, and defer order
compatibility; the wiring identities above take that compatibility as
prefix-set hypotheses. The strengthened forms below expose exactly
those prefix conjuncts, so the arena invocation (node 1.2.11) can
discharge the wiring hypotheses from one bijection. Provable by the
same order surgery as the signed `aliceReveal_pushforward_eq` /
`bobReveal_pushforward_eq` (deleting at the cut preserves the strict
prefix and the untouched forward-side order). -/

/-- **Alice-reveal pushforward, strengthened carryover** (node 1.2.8;
05_prerounding.tex "Both reverse experiments have exactly the forward
law", with the order compatibility deferred by review #11 now
explicit): the datum bijection matches laws pointwise and carries over
the live coordinate, blocks, cut values, AND both prefix sets. -/
theorem aliceReveal_pushforward_strong (n : ℕ) (D : Finset (Fin n)) :
    ∃ e : AliceRevealDatum n D ≃ RevealDatum n D,
      (∀ d : AliceRevealDatum n D, d.law = (e d).revealLaw) ∧
      (∀ d : AliceRevealDatum n D,
        (e d).i = d.liveIdx ∧ (e d).LX = d.LX ∧
        (e d).LY = d.LYp.erase d.liveIdx ∧
        ((e d).kX : ℕ) = (d.kX : ℕ) ∧ ((e d).kY : ℕ) = (d.kY : ℕ) ∧
        (e d).prefixY = d.revealPrefix d.kY.castSucc ∧
        (e d).prefixX = d.alicePrefixX) := by
  refine ⟨aliceRevealEquiv n D, fun d => d.law_toReveal,
    fun d => ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩⟩
  show d.toReveal.prefixY = d.revealPrefix d.kY.castSucc
  ext z
  simp only [RevealDatum.prefixY, AliceRevealDatum.revealPrefix,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.val_castSucc]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨(t : ℕ), lt_trans ht d.kY.isLt⟩, ht,
      (d.toReveal_πY_of_lt t ⟨(t : ℕ), lt_trans ht d.kY.isLt⟩ rfl ht).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hb : (s : ℕ) < d.toReveal.LY.card := by
      have h1 := d.kY.isLt
      have h2 : d.toReveal.LY.card = d.LYp.card - 1 :=
        Finset.card_erase_of_mem d.liveIdx_mem
      omega
    exact ⟨⟨(s : ℕ), hb⟩, hs, d.toReveal_πY_of_lt ⟨(s : ℕ), hb⟩ s rfl hs⟩

/-- **Bob-reveal pushforward, strengthened carryover** (mirror). -/
theorem bobReveal_pushforward_strong (n : ℕ) (D : Finset (Fin n)) :
    ∃ e : BobRevealDatum n D ≃ RevealDatum n D,
      (∀ d : BobRevealDatum n D, d.law = (e d).revealLaw) ∧
      (∀ d : BobRevealDatum n D,
        (e d).i = d.liveIdx ∧ (e d).LY = d.LY ∧
        (e d).LX = d.LXp.erase d.liveIdx ∧
        ((e d).kY : ℕ) = (d.kY : ℕ) ∧ ((e d).kX : ℕ) = (d.kX : ℕ) ∧
        (e d).prefixX = d.revealPrefix d.kX.castSucc ∧
        (e d).prefixY = d.bobPrefixY) := by
  refine ⟨bobRevealEquiv n D, fun d => d.law_toReveal,
    fun d => ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩⟩
  show d.toReveal.prefixX = d.revealPrefix d.kX.castSucc
  ext z
  simp only [RevealDatum.prefixX, BobRevealDatum.revealPrefix,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.val_castSucc]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨(t : ℕ), lt_trans ht d.kX.isLt⟩, ht,
      (d.toReveal_πX_of_lt t ⟨(t : ℕ), lt_trans ht d.kX.isLt⟩ rfl ht).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hb : (s : ℕ) < d.toReveal.LX.card := by
      have h1 := d.kX.isLt
      have h2 : d.toReveal.LX.card = d.LXp.card - 1 :=
        Finset.card_erase_of_mem d.liveIdx_mem
      omega
    exact ⟨⟨(s : ℕ), hb⟩, hs, d.toReveal_πX_of_lt ⟨(s : ℕ), hb⟩ s rfl hs⟩

end CommutingRepetition
