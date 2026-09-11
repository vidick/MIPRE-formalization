/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/CostsLemmas0.lean
-/
/-
# Proof-side helpers for the prior alignment bound, base layer (node 1.2.9)

Support lemmas consumed by the proofs in `Prerounding/Costs.lean`
(review #15 chain): general revealed-set effect facts (congruence, the
`univ` collapse to the core effects, positivity, the covering-pair
tower collapse), order-prefix combinatorics for the reverse
experiments, local copies of the canonical-label builders (bridged to
the `Costs.lean` originals by `rfl`), word splitting along a
coordinate block, and the core-mass normalization bound. Everything
here is proof-side: no statement of the frozen batch is restated. The
scenario martingales and the budget consumption are the second layer,
`Prerounding/CostsLemmas.lean`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Alignment
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Entropy
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Information
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.EntropyBudget

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

set_option linter.unusedSectionVars false

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]

/-! ## Order prefixes (standalone form of the reverse-experiment
prefix sets) -/

/-- The first `j` entries of an order of a block, as a set (the
standalone form of `AliceRevealDatum.revealPrefix` /
`BobRevealDatum.revealPrefix`, with a bare `ℕ` cut so that adjacent
cuts share one definition). -/
def ordPrefix {L : Finset (Fin n)}
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (j : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun t : Fin L.card => (t : ℕ) < j).image
    fun t => (π t : Fin n)

theorem ordPrefix_subset {L : Finset (Fin n)}
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (j : ℕ) :
    ordPrefix π j ⊆ L := by
  intro c hc
  simp only [ordPrefix, Finset.mem_image, Finset.mem_filter] at hc
  obtain ⟨t, _, rfl⟩ := hc
  exact (π t).2

theorem ordPrefix_succ {L : Finset (Fin n)}
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (s : Fin L.card) :
    ordPrefix π ((s : ℕ) + 1) = insert ((π s : Fin n)) (ordPrefix π (s : ℕ)) := by
  ext c
  simp only [ordPrefix, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact Or.inr ⟨t, h, rfl⟩
    · exact Or.inl (by rw [Fin.ext h])
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨s, Nat.lt_succ_self _, rfl⟩
    · exact ⟨t, Nat.lt_succ_of_lt ht, rfl⟩

theorem notMem_ordPrefix_self {L : Finset (Fin n)}
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) (s : Fin L.card) :
    ((π s : Fin n)) ∉ ordPrefix π (s : ℕ) := by
  intro h
  simp only [ordPrefix, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  obtain ⟨t, ht, heq⟩ := h
  have h2 : t = s := π.injective (Subtype.ext heq)
  rw [h2] at ht
  exact lt_irrefl _ ht

theorem ordPrefix_zero {L : Finset (Fin n)}
    (π : Fin L.card ≃ {j : Fin n // j ∈ L}) :
    ordPrefix π 0 = ∅ := by
  simp [ordPrefix]

/-- The full product prior over both question words has total mass one
when the base law does. -/
theorem sum_prod_mu_eq_one (μ : X → Y → ℝ)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1) :
    (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      ∏ j : Fin n, μ (xw j) (yw j)) = 1 := by
  classical
  have h1 : ∀ xw : Fin n → X,
      (∑ yw : Fin n → Y, ∏ j : Fin n, μ (xw j) (yw j))
        = ∏ j : Fin n, ∑ y : Y, μ (xw j) y := by
    intro xw
    have hps := Finset.prod_univ_sum
      (fun _ : Fin n => (Finset.univ : Finset Y))
      (fun j v => μ (xw j) v)
    rw [Fintype.piFinset_univ] at hps
    exact hps.symm
  rw [Finset.sum_congr rfl fun xw _ => h1 xw]
  have h2 : (∑ xw : Fin n → X, ∏ j : Fin n, ∑ y : Y, μ (xw j) y)
      = ∏ _j : Fin n, ∑ x : X, ∑ y : Y, μ x y := by
    have hps := Finset.prod_univ_sum
      (fun _ : Fin n => (Finset.univ : Finset X))
      (fun _j v => ∑ y : Y, μ v y)
    rw [Fintype.piFinset_univ] at hps
    exact hps.symm
  rw [h2, Finset.prod_congr rfl fun j _ => hμsum, Finset.prod_const_one]

/-! ## Revealed-set effect facts -/

namespace TracialStrategy

variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}

/-- `setEffectA` reads its `xref` only on the revealed set and its
`yref` only off it. -/
theorem setEffectA_congr (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    {x x' : Fin n → X} {y y' : Fin n → Y} (zA : Fin n → A)
    (hx : ∀ j ∈ R₀, x j = x' j) (hy : ∀ j ∉ R₀, y j = y' j) :
    S.setEffectA D R₀ μ x y zA = S.setEffectA D R₀ μ x' y' zA := by
  have hw : setWeightX R₀ μ x y = setWeightX R₀ μ x' y' := by
    funext u
    simp only [setWeightX]
    have hiff : agreesOn R₀ u x ↔ agreesOn R₀ u x' :=
      ⟨fun h j hj => (h j hj).trans (hx j hj),
       fun h j hj => (h j hj).trans (hx j hj).symm⟩
    have hprod : (∏ j ∈ R₀ᶜ, μ (u j) (y j))
        = ∏ j ∈ R₀ᶜ, μ (u j) (y' j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [hy j (Finset.mem_compl.mp hj)]
    rw [if_congr hiff hprod rfl]
  simp only [setEffectA]
  rw [hw]

/-- Mirror congruence for `setEffectB`. -/
theorem setEffectB_congr (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    {x x' : Fin n → X} {y y' : Fin n → Y} (zB : Fin n → B)
    (hx : ∀ j ∉ R₀, x j = x' j) (hy : ∀ j ∈ R₀, y j = y' j) :
    S.setEffectB D R₀ μ x y zB = S.setEffectB D R₀ μ x' y' zB := by
  have hw : setWeightY R₀ μ x y = setWeightY R₀ μ x' y' := by
    funext v
    simp only [setWeightY]
    have hiff : agreesOn R₀ v y ↔ agreesOn R₀ v y' :=
      ⟨fun h j hj => (h j hj).trans (hy j hj),
       fun h j hj => (h j hj).trans (hy j hj).symm⟩
    have hprod : (∏ j ∈ R₀ᶜ, μ (x j) (v j))
        = ∏ j ∈ R₀ᶜ, μ (x' j) (v j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [hx j (Finset.mem_compl.mp hj)]
    rw [if_congr hiff hprod rfl]
  simp only [setEffectB]
  rw [hw]

/-- At the fully revealed set the revealed-set effect is the core
effect: the weight is the point mass at the reference word. -/
theorem setEffectA_univ (μ : X → Y → ℝ) (x : Fin n → X)
    (y : Fin n → Y) (zA : Fin n → A) :
    S.setEffectA D Finset.univ μ x y zA = S.coreEffectA D x zA := by
  have hw : ∀ u : Fin n → X,
      setWeightX Finset.univ μ x y u = if u = x then 1 else 0 := by
    intro u
    simp only [setWeightX, Finset.compl_univ, Finset.prod_empty]
    congr 1
    · simp only [eq_iff_iff]
      constructor
      · intro h
        exact funext fun j => h j (Finset.mem_univ j)
      · rintro rfl
        exact fun j _ => rfl
  simp only [setEffectA, weightedAvg]
  rw [Finset.sum_congr rfl fun u _ => hw u,
    Finset.sum_ite_eq' Finset.univ x (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ x)]
  rw [show (∑ u : Fin n → X,
        (((setWeightX Finset.univ μ x y u : ℝ)) : ℂ) • S.coreEffectA D u zA)
      = ∑ u : Fin n → X,
        (if u = x then ((1 : ℝ) : ℂ) • S.coreEffectA D u zA else 0) from
    Finset.sum_congr rfl fun u _ => by
      rw [hw u]
      split_ifs <;> simp]
  rw [Finset.sum_ite_eq' Finset.univ x
      (fun u => ((1 : ℝ) : ℂ) • S.coreEffectA D u zA),
    if_pos (Finset.mem_univ x)]
  simp

/-- Mirror `univ` collapse for `setEffectB`. -/
theorem setEffectB_univ (μ : X → Y → ℝ) (x : Fin n → X)
    (y : Fin n → Y) (zB : Fin n → B) :
    S.setEffectB D Finset.univ μ x y zB = S.coreEffectB D y zB := by
  have hw : ∀ v : Fin n → Y,
      setWeightY Finset.univ μ x y v = if v = y then 1 else 0 := by
    intro v
    simp only [setWeightY, Finset.compl_univ, Finset.prod_empty]
    congr 1
    · simp only [eq_iff_iff]
      constructor
      · intro h
        exact funext fun j => h j (Finset.mem_univ j)
      · rintro rfl
        exact fun j _ => rfl
  simp only [setEffectB, weightedAvg]
  rw [Finset.sum_congr rfl fun v _ => hw v,
    Finset.sum_ite_eq' Finset.univ y (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ y)]
  rw [show (∑ v : Fin n → Y,
        (((setWeightY Finset.univ μ x y v : ℝ)) : ℂ) • S.coreEffectB D v zB)
      = ∑ v : Fin n → Y,
        (if v = y then ((1 : ℝ) : ℂ) • S.coreEffectB D v zB else 0) from
    Finset.sum_congr rfl fun v _ => by
      rw [hw v]
      split_ifs <;> simp]
  rw [Finset.sum_ite_eq' Finset.univ y
      (fun v => ((1 : ℝ) : ℂ) • S.coreEffectB D v zB),
    if_pos (Finset.mem_univ y)]
  simp

/-- Scalar expansion of a `weightedAvg` in the left slot of the trace
pairing. Junk-safe through Lean's `0⁻¹ = 0`. -/
theorem re_pairing_weightedAvg_left {ι : Type*} [Fintype ι]
    (wgt : ι → ℝ) (f : ι → S.M.A) (K : S.M.A) :
    (S.M.τ (star S.σ * (weightedAvg wgt f * S.σ * K))).re
      = (∑ i : ι, wgt i)⁻¹ *
          ∑ i : ι, wgt i * (S.M.τ (star S.σ * (f i * S.σ * K))).re := by
  have hexp : star S.σ * (weightedAvg wgt f * S.σ * K)
      = (((((∑ i : ι, wgt i)⁻¹ : ℝ)) : ℂ)) •
          ∑ i : ι, (((wgt i : ℝ)) : ℂ) •
            (star S.σ * (f i * S.σ * K)) := by
    unfold weightedAvg
    rw [← Complex.ofReal_inv, smul_mul_assoc, smul_mul_assoc,
      mul_smul_comm, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  rw [hexp, map_smul, smul_eq_mul, Complex.re_ofReal_mul, map_sum,
    Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- Scalar expansion of a `weightedAvg` in the right slot. -/
theorem re_pairing_weightedAvg_right {ι : Type*} [Fintype ι]
    (wgt : ι → ℝ) (f : ι → S.M.A) (H : S.M.A) :
    (S.M.τ (star S.σ * (H * S.σ * weightedAvg wgt f))).re
      = (∑ i : ι, wgt i)⁻¹ *
          ∑ i : ι, wgt i * (S.M.τ (star S.σ * (H * S.σ * f i))).re := by
  have hexp : star S.σ * (H * S.σ * weightedAvg wgt f)
      = (((((∑ i : ι, wgt i)⁻¹ : ℝ)) : ℂ)) •
          ∑ i : ι, (((wgt i : ℝ)) : ℂ) •
            (star S.σ * (H * S.σ * f i)) := by
    unfold weightedAvg
    rw [← Complex.ofReal_inv, mul_smul_comm, mul_smul_comm,
      Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, mul_smul_comm]
  rw [hexp, map_smul, smul_eq_mul, Complex.re_ofReal_mul, map_sum,
    Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- The `D`-measurable-weighted prior pairing of the two revealed-set
effects at a pair of revealed sets. The covering-pair tower collapse
(`pairSum_eq_core` below) states its independence of the sets. -/
noncomputable def pairSum (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (W : (Fin n → X) → (Fin n → Y) → ℝ) (zAf : Fin n → A)
    (zBf : Fin n → B) (SA SB : Finset (Fin n)) : ℝ :=
  ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
    (∏ j : Fin n, μ (xw j) (yw j)) *
      (W xw yw * (S.M.τ (star S.σ *
        (S.setEffectA D SA μ xw yw zAf * S.σ *
          S.setEffectB D SB μ xw yw zBf))).re)

/-- One tower step on the Alice side: revealing one more coordinate to
Alice does not change the prior pairing, provided the coordinate is
already revealed to Bob. -/
theorem pairSum_insertA (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (W : (Fin n → X) → (Fin n → Y) → ℝ)
    (hWx : ∀ (x x' : Fin n → X) (y : Fin n → Y),
      agreesOn D x x' → W x y = W x' y)
    (zAf : Fin n → A) (zBf : Fin n → B) (SA SB : Finset (Fin n))
    (hDA : D ⊆ SA) (c : Fin n) (hcA : c ∉ SA) (hcB : c ∈ SB) :
    S.pairSum D μ W zAf zBf SA SB
      = S.pairSum D μ W zAf zBf (insert c SA) SB := by
  classical
  unfold pairSum
  rw [Finset.sum_comm, Finset.sum_comm
    (s := (Finset.univ : Finset (Fin n → X)))]
  refine Finset.sum_congr rfl fun yw _ => ?_
  -- Split the Alice word at the revealed coordinate.
  set e := Equiv.piSplitAt c (fun _ : Fin n => X) with he
  have hsymm_c : ∀ (v : X) (g : {j : Fin n // j ≠ c} → X),
      e.symm (v, g) c = v := by
    intro v g
    simp [he, Equiv.piSplitAt_symm_apply]
  have hsymm_ne : ∀ (v : X) (g : {j : Fin n // j ≠ c} → X) (j : Fin n)
      (hj : j ≠ c), e.symm (v, g) j = g ⟨j, hj⟩ := by
    intro v g j hj
    simp [he, Equiv.piSplitAt_symm_apply, hj]
  have hsum : ∀ (F : (Fin n → X) → ℝ),
      (∑ w : Fin n → X, F w)
        = ∑ v : X, ∑ g : {j : Fin n // j ≠ c} → X, F (e.symm (v, g)) := by
    intro F
    rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
      (fun w => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
  rw [hsum, hsum]
  -- The v-independent data.
  have hagree : ∀ (v v' : X) (g : {j : Fin n // j ≠ c} → X),
      agreesOn D (e.symm (v, g)) (e.symm (v', g)) := by
    intro v v' g j hj
    have hjc : j ≠ c := fun hjc => hcA (hjc ▸ hDA hj)
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  have hprod : ∀ (v : X) (g : {j : Fin n // j ≠ c} → X),
      (∏ j : Fin n, μ (e.symm (v, g) j) (yw j))
        = μ v (yw c) *
            ∏ j ∈ Finset.univ.erase c,
              μ (e.symm (v, g) j) (yw j) := by
    intro v g
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
      hsymm_c]
  have hprod_ind : ∀ (v v' : X) (g : {j : Fin n // j ≠ c} → X),
      (∏ j ∈ Finset.univ.erase c, μ (e.symm (v, g) j) (yw j))
        = ∏ j ∈ Finset.univ.erase c, μ (e.symm (v', g) j) (yw j) := by
    intro v v' g
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjc : j ≠ c := Finset.ne_of_mem_erase hj
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  have hEB : ∀ (v v' : X) (g : {j : Fin n // j ≠ c} → X),
      S.setEffectB D SB μ (e.symm (v, g)) yw zBf
        = S.setEffectB D SB μ (e.symm (v', g)) yw zBf := by
    intro v v' g
    refine S.setEffectB_congr D SB μ zBf (fun j hj => ?_) (fun _ _ => rfl)
    have hjc : j ≠ c := fun hjc => hj (hjc ▸ hcB)
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  have hEA0 : ∀ (v v' : X) (g : {j : Fin n // j ≠ c} → X),
      S.setEffectA D SA μ (e.symm (v, g)) yw zAf
        = S.setEffectA D SA μ (e.symm (v', g)) yw zAf := by
    intro v v' g
    refine S.setEffectA_congr D SA μ zAf (fun j hj => ?_) (fun _ _ => rfl)
    have hjc : j ≠ c := fun hjc => hcA (hjc ▸ hj)
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  -- The child effect at live value v is the updated-reference effect.
  have hchild : ∀ (v : X) (g : {j : Fin n // j ≠ c} → X),
      S.setEffectA D (insert c SA) μ (e.symm (v, g)) yw zAf
        = S.setEffectA D (insert c SA) μ
            (Function.update (e.symm (v, g)) c v) yw zAf := by
    intro v g
    refine S.setEffectA_congr D (insert c SA) μ zAf (fun j hj => ?_)
      (fun _ _ => rfl)
    rcases Finset.mem_insert.mp hj with rfl | hjS
    · rw [hsymm_c, Function.update_self]
    · have hjc : j ≠ c := fun hjc => hcA (hjc ▸ hjS)
      rw [Function.update_of_ne hjc]
  refine Finset.sum_comm.trans (Eq.trans ?_ (Finset.sum_comm
    (t := (Finset.univ : Finset X))))
  refine Finset.sum_congr rfl fun g _ => ?_
  -- Fixed g: the one-step reveal identity in scalar form.
  have hreveal := S.setEffectA_reveal D SA μ hμ
    (e.symm (Classical.arbitrary X, g)) yw zAf c hcA
  -- Left side collapses to a single ν-weighted term.
  have hL : (∑ v : X,
      (∏ j : Fin n, μ (e.symm (v, g) j) (yw j)) *
        (W (e.symm (v, g)) yw *
          (S.M.τ (star S.σ * (S.setEffectA D SA μ (e.symm (v, g)) yw zAf *
            S.σ * S.setEffectB D SB μ (e.symm (v, g)) yw zBf))).re))
      = (∏ j ∈ Finset.univ.erase c,
          μ (e.symm (Classical.arbitrary X, g) j) (yw j)) *
        (W (e.symm (Classical.arbitrary X, g)) yw *
          ((∑ v : X, μ v (yw c)) *
            (S.M.τ (star S.σ *
              (S.setEffectA D SA μ (e.symm (Classical.arbitrary X, g)) yw zAf *
                S.σ *
                S.setEffectB D SB μ (e.symm (Classical.arbitrary X, g)) yw
                  zBf))).re)) := by
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hprod v g, hprod_ind v (Classical.arbitrary X) g,
      hWx (e.symm (v, g)) (e.symm (Classical.arbitrary X, g)) yw
        (hagree v (Classical.arbitrary X) g),
      hEA0 v (Classical.arbitrary X) g, hEB v (Classical.arbitrary X) g]
    ring
  rw [hL]
  -- Right side: same prefactors, updated child effects.
  have hR : (∑ v : X,
      (∏ j : Fin n, μ (e.symm (v, g) j) (yw j)) *
        (W (e.symm (v, g)) yw *
          (S.M.τ (star S.σ *
            (S.setEffectA D (insert c SA) μ (e.symm (v, g)) yw zAf *
              S.σ * S.setEffectB D SB μ (e.symm (v, g)) yw zBf))).re))
      = (∏ j ∈ Finset.univ.erase c,
          μ (e.symm (Classical.arbitrary X, g) j) (yw j)) *
        (W (e.symm (Classical.arbitrary X, g)) yw *
          (∑ v : X, μ v (yw c) *
            (S.M.τ (star S.σ *
              (S.setEffectA D (insert c SA) μ
                  (Function.update (e.symm (Classical.arbitrary X, g)) c v) yw
                  zAf *
                S.σ *
                S.setEffectB D SB μ (e.symm (Classical.arbitrary X, g)) yw
                  zBf))).re)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hupd : Function.update (e.symm (v, g)) c v
        = Function.update (e.symm (Classical.arbitrary X, g)) c v := by
      funext j
      by_cases hjc : j = c
      · subst hjc
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hjc, Function.update_of_ne hjc,
          hsymm_ne v g j hjc, hsymm_ne (Classical.arbitrary X) g j hjc]
    rw [hprod v g, hprod_ind v (Classical.arbitrary X) g,
      hWx (e.symm (v, g)) (e.symm (Classical.arbitrary X, g)) yw
        (hagree v (Classical.arbitrary X) g),
      hchild v g, hupd, hEB v (Classical.arbitrary X) g]
    ring
  rw [hR]
  -- The ν-weighted parent pairing equals the μ-weighted child sum.
  congr 2
  rw [hreveal, S.re_pairing_weightedAvg_left]
  by_cases hν : (∑ v : X, μ v (yw c)) = 0
  · have hz : ∀ v : X, μ v (yw c) = 0 := fun v =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => hμ v (yw c))).mp hν v (Finset.mem_univ v)
    rw [hν, zero_mul]
    exact (Finset.sum_eq_zero fun v _ => by rw [hz v, zero_mul]).symm
  · rw [← mul_assoc, mul_inv_cancel₀ hν, one_mul]

/-- One tower step on the Bob side (mirror). -/
theorem pairSum_insertB (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (W : (Fin n → X) → (Fin n → Y) → ℝ)
    (hWy : ∀ (x : Fin n → X) (y y' : Fin n → Y),
      agreesOn D y y' → W x y = W x y')
    (zAf : Fin n → A) (zBf : Fin n → B) (SA SB : Finset (Fin n))
    (hDB : D ⊆ SB) (c : Fin n) (hcB : c ∉ SB) (hcA : c ∈ SA) :
    S.pairSum D μ W zAf zBf SA SB
      = S.pairSum D μ W zAf zBf SA (insert c SB) := by
  classical
  unfold pairSum
  refine Finset.sum_congr rfl fun xw _ => ?_
  set e := Equiv.piSplitAt c (fun _ : Fin n => Y) with he
  have hsymm_c : ∀ (v : Y) (g : {j : Fin n // j ≠ c} → Y),
      e.symm (v, g) c = v := by
    intro v g
    simp [he, Equiv.piSplitAt_symm_apply]
  have hsymm_ne : ∀ (v : Y) (g : {j : Fin n // j ≠ c} → Y) (j : Fin n)
      (hj : j ≠ c), e.symm (v, g) j = g ⟨j, hj⟩ := by
    intro v g j hj
    simp [he, Equiv.piSplitAt_symm_apply, hj]
  have hsum : ∀ (F : (Fin n → Y) → ℝ),
      (∑ w : Fin n → Y, F w)
        = ∑ v : Y, ∑ g : {j : Fin n // j ≠ c} → Y, F (e.symm (v, g)) := by
    intro F
    rw [Fintype.sum_equiv e F (fun p => F (e.symm p))
      (fun w => by rw [Equiv.symm_apply_apply]), Fintype.sum_prod_type]
  rw [hsum, hsum]
  have hagree : ∀ (v v' : Y) (g : {j : Fin n // j ≠ c} → Y),
      agreesOn D (e.symm (v, g)) (e.symm (v', g)) := by
    intro v v' g j hj
    have hjc : j ≠ c := fun hjc => hcB (hjc ▸ hDB hj)
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  have hprod : ∀ (v : Y) (g : {j : Fin n // j ≠ c} → Y),
      (∏ j : Fin n, μ (xw j) (e.symm (v, g) j))
        = μ (xw c) v *
            ∏ j ∈ Finset.univ.erase c,
              μ (xw j) (e.symm (v, g) j) := by
    intro v g
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
      hsymm_c]
  have hprod_ind : ∀ (v v' : Y) (g : {j : Fin n // j ≠ c} → Y),
      (∏ j ∈ Finset.univ.erase c, μ (xw j) (e.symm (v, g) j))
        = ∏ j ∈ Finset.univ.erase c, μ (xw j) (e.symm (v', g) j) := by
    intro v v' g
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjc : j ≠ c := Finset.ne_of_mem_erase hj
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  have hEA : ∀ (v v' : Y) (g : {j : Fin n // j ≠ c} → Y),
      S.setEffectA D SA μ xw (e.symm (v, g)) zAf
        = S.setEffectA D SA μ xw (e.symm (v', g)) zAf := by
    intro v v' g
    refine S.setEffectA_congr D SA μ zAf (fun _ _ => rfl) (fun j hj => ?_)
    have hjc : j ≠ c := fun hjc => hj (hjc ▸ hcA)
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  have hEB0 : ∀ (v v' : Y) (g : {j : Fin n // j ≠ c} → Y),
      S.setEffectB D SB μ xw (e.symm (v, g)) zBf
        = S.setEffectB D SB μ xw (e.symm (v', g)) zBf := by
    intro v v' g
    refine S.setEffectB_congr D SB μ zBf (fun _ _ => rfl) (fun j hj => ?_)
    have hjc : j ≠ c := fun hjc => hcB (hjc ▸ hj)
    rw [hsymm_ne v g j hjc, hsymm_ne v' g j hjc]
  have hchild : ∀ (v : Y) (g : {j : Fin n // j ≠ c} → Y),
      S.setEffectB D (insert c SB) μ xw (e.symm (v, g)) zBf
        = S.setEffectB D (insert c SB) μ xw
            (Function.update (e.symm (v, g)) c v) zBf := by
    intro v g
    refine S.setEffectB_congr D (insert c SB) μ zBf (fun _ _ => rfl)
      (fun j hj => ?_)
    rcases Finset.mem_insert.mp hj with rfl | hjS
    · rw [hsymm_c, Function.update_self]
    · have hjc : j ≠ c := fun hjc => hcB (hjc ▸ hjS)
      rw [Function.update_of_ne hjc]
  refine Finset.sum_comm.trans (Eq.trans ?_ (Finset.sum_comm
    (t := (Finset.univ : Finset Y))))
  refine Finset.sum_congr rfl fun g _ => ?_
  have hreveal := S.setEffectB_reveal D SB μ hμ xw
    (e.symm (Classical.arbitrary Y, g)) zBf c hcB
  have hL : (∑ v : Y,
      (∏ j : Fin n, μ (xw j) (e.symm (v, g) j)) *
        (W xw (e.symm (v, g)) *
          (S.M.τ (star S.σ * (S.setEffectA D SA μ xw (e.symm (v, g)) zAf *
            S.σ * S.setEffectB D SB μ xw (e.symm (v, g)) zBf))).re))
      = (∏ j ∈ Finset.univ.erase c,
          μ (xw j) (e.symm (Classical.arbitrary Y, g) j)) *
        (W xw (e.symm (Classical.arbitrary Y, g)) *
          ((∑ v : Y, μ (xw c) v) *
            (S.M.τ (star S.σ *
              (S.setEffectA D SA μ xw (e.symm (Classical.arbitrary Y, g)) zAf *
                S.σ *
                S.setEffectB D SB μ xw (e.symm (Classical.arbitrary Y, g))
                  zBf))).re)) := by
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hprod v g, hprod_ind v (Classical.arbitrary Y) g,
      hWy xw (e.symm (v, g)) (e.symm (Classical.arbitrary Y, g))
        (hagree v (Classical.arbitrary Y) g),
      hEA v (Classical.arbitrary Y) g, hEB0 v (Classical.arbitrary Y) g]
    ring
  rw [hL]
  have hR : (∑ v : Y,
      (∏ j : Fin n, μ (xw j) (e.symm (v, g) j)) *
        (W xw (e.symm (v, g)) *
          (S.M.τ (star S.σ *
            (S.setEffectA D SA μ xw (e.symm (v, g)) zAf *
              S.σ * S.setEffectB D (insert c SB) μ xw (e.symm (v, g)) zBf))).re))
      = (∏ j ∈ Finset.univ.erase c,
          μ (xw j) (e.symm (Classical.arbitrary Y, g) j)) *
        (W xw (e.symm (Classical.arbitrary Y, g)) *
          (∑ v : Y, μ (xw c) v *
            (S.M.τ (star S.σ *
              (S.setEffectA D SA μ xw (e.symm (Classical.arbitrary Y, g)) zAf *
                S.σ *
                S.setEffectB D (insert c SB) μ xw
                  (Function.update (e.symm (Classical.arbitrary Y, g)) c v)
                  zBf))).re)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hupd : Function.update (e.symm (v, g)) c v
        = Function.update (e.symm (Classical.arbitrary Y, g)) c v := by
      funext j
      by_cases hjc : j = c
      · subst hjc
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hjc, Function.update_of_ne hjc,
          hsymm_ne v g j hjc, hsymm_ne (Classical.arbitrary Y) g j hjc]
    rw [hprod v g, hprod_ind v (Classical.arbitrary Y) g,
      hWy xw (e.symm (v, g)) (e.symm (Classical.arbitrary Y, g))
        (hagree v (Classical.arbitrary Y) g),
      hchild v g, hupd, hEA v (Classical.arbitrary Y) g]
    ring
  rw [hR]
  congr 2
  rw [hreveal, S.re_pairing_weightedAvg_right]
  by_cases hν : (∑ v : Y, μ (xw c) v) = 0
  · have hz : ∀ v : Y, μ (xw c) v = 0 := fun v =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => hμ (xw c) v)).mp hν v (Finset.mem_univ v)
    rw [hν, zero_mul]
    exact (Finset.sum_eq_zero fun v _ => by rw [hz v, zero_mul]).symm
  · rw [← mul_assoc, mul_inv_cancel₀ hν, one_mul]

/-- **The covering-pair tower collapse**: for any pair of revealed
sets containing the core and jointly covering every coordinate, the
`D`-measurable-weighted prior pairing of the revealed-set effects
equals the corresponding core-effect pairing (eq p-q-m through the
tower property; the general form of the review-#15 trap-5 telescope). -/
theorem pairSum_eq_core (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (W : (Fin n → X) → (Fin n → Y) → ℝ)
    (hWx : ∀ (x x' : Fin n → X) (y : Fin n → Y),
      agreesOn D x x' → W x y = W x' y)
    (hWy : ∀ (x : Fin n → X) (y y' : Fin n → Y),
      agreesOn D y y' → W x y = W x y')
    (zAf : Fin n → A) (zBf : Fin n → B) (SA SB : Finset (Fin n))
    (hDA : D ⊆ SA) (hDB : D ⊆ SB)
    (hcov : SA ∪ SB = Finset.univ) :
    S.pairSum D μ W zAf zBf SA SB
      = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) *
            (W xw yw * (S.M.τ (star S.σ *
              (S.coreEffectA D xw zAf * S.σ *
                S.coreEffectB D yw zBf))).re) := by
  classical
  -- Phase 1: fill the Alice side up to `univ`.
  have fillA : ∀ (k : ℕ) (SA' : Finset (Fin n)), (SA'ᶜ).card = k →
      D ⊆ SA' → SA' ∪ SB = Finset.univ →
      S.pairSum D μ W zAf zBf SA' SB
        = S.pairSum D μ W zAf zBf Finset.univ SB := by
    intro k
    induction k with
    | zero =>
      intro SA' hcard _ _
      have hSA' : SA' = Finset.univ := by
        have h1 : SA'ᶜ = ∅ := Finset.card_eq_zero.mp hcard
        rwa [Finset.compl_eq_empty_iff] at h1
      rw [hSA']
    | succ k ih =>
      intro SA' hcard hDA' hcov'
      have hne : (SA'ᶜ).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨c, hc⟩ := hne
      have hcA : c ∉ SA' := Finset.mem_compl.mp hc
      have hcB : c ∈ SB := by
        have hmem : c ∈ SA' ∪ SB := hcov' ▸ Finset.mem_univ c
        rcases Finset.mem_union.mp hmem with h | h
        · exact absurd h hcA
        · exact h
      rw [S.pairSum_insertA μ hμ W hWx zAf zBf SA' SB hDA' c hcA hcB]
      refine ih (insert c SA') ?_
        (hDA'.trans (Finset.subset_insert c SA')) ?_
      · rw [Finset.compl_insert, Finset.card_erase_of_mem hc, hcard]
        omega
      · rw [Finset.insert_union, hcov']
        exact Finset.insert_eq_self.mpr (Finset.mem_univ c)
  -- Phase 2: fill the Bob side up to `univ`.
  have fillB : ∀ (k : ℕ) (SB' : Finset (Fin n)), (SB'ᶜ).card = k →
      D ⊆ SB' →
      S.pairSum D μ W zAf zBf Finset.univ SB'
        = S.pairSum D μ W zAf zBf Finset.univ Finset.univ := by
    intro k
    induction k with
    | zero =>
      intro SB' hcard _
      have hSB' : SB' = Finset.univ := by
        have h1 : SB'ᶜ = ∅ := Finset.card_eq_zero.mp hcard
        rwa [Finset.compl_eq_empty_iff] at h1
      rw [hSB']
    | succ k ih =>
      intro SB' hcard hDB'
      have hne : (SB'ᶜ).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨c, hc⟩ := hne
      have hcB : c ∉ SB' := Finset.mem_compl.mp hc
      rw [S.pairSum_insertB μ hμ W hWy zAf zBf Finset.univ SB' hDB' c hcB
        (Finset.mem_univ c)]
      refine ih (insert c SB') ?_
        (hDB'.trans (Finset.subset_insert c SB'))
      rw [Finset.compl_insert, Finset.card_erase_of_mem hc, hcard]
      omega
  rw [fillA (SAᶜ).card SA rfl hDA hcov, fillB (SBᶜ).card SB rfl hDB]
  unfold pairSum
  refine Finset.sum_congr rfl fun xw _ => Finset.sum_congr rfl fun yw _ => ?_
  rw [S.setEffectA_univ μ xw yw zAf, S.setEffectB_univ μ xw yw zBf]

/-! ## The core-mass normalization bound -/

/-- The core answer assignments tile the full answer words: summing the
core effect over every core assignment (canonically extended) recovers
the POVM total. -/
theorem sum_coreEffectA_ext (D : Finset (Fin n)) (xw : Fin n → X)
    (ext : ({j : Fin n // j ∈ D} → A) → Fin n → A)
    (hext : ∀ (zD : {j : Fin n // j ∈ D} → A) (j : Fin n) (hj : j ∈ D),
      ext zD j = zD ⟨j, hj⟩) :
    (∑ zD : {j : Fin n // j ∈ D} → A, S.coreEffectA D xw (ext zD)) = 1 := by
  classical
  unfold coreEffectA
  rw [Finset.sum_comm]
  have hinner : ∀ as : Fin n → A,
      (∑ zD : {j : Fin n // j ∈ D} → A,
        if agreesOn D as (ext zD) then S.E xw as else 0) = S.E xw as := by
    intro as
    have hiff : ∀ zD : {j : Fin n // j ∈ D} → A,
        agreesOn D as (ext zD) ↔ (fun j : {j : Fin n // j ∈ D} => as j) = zD := by
      intro zD
      constructor
      · intro h
        funext j
        rw [show as (j : Fin n) = ext zD j from h j j.2, hext zD j j.2]
      · rintro rfl
        intro j hj
        rw [hext _ j hj]
    rw [Finset.sum_congr rfl fun zD _ => if_congr (hiff zD) rfl rfl,
      Finset.sum_ite_eq Finset.univ
        (fun j : {j : Fin n // j ∈ D} => as j) (fun _ => S.E xw as),
      if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun as _ => hinner as, S.E_sum xw]

/-- Mirror tiling for Bob. -/
theorem sum_coreEffectB_ext (D : Finset (Fin n)) (yw : Fin n → Y)
    (ext : ({j : Fin n // j ∈ D} → B) → Fin n → B)
    (hext : ∀ (zD : {j : Fin n // j ∈ D} → B) (j : Fin n) (hj : j ∈ D),
      ext zD j = zD ⟨j, hj⟩) :
    (∑ zD : {j : Fin n // j ∈ D} → B, S.coreEffectB D yw (ext zD)) = 1 := by
  classical
  unfold coreEffectB
  rw [Finset.sum_comm]
  have hinner : ∀ bs : Fin n → B,
      (∑ zD : {j : Fin n // j ∈ D} → B,
        if agreesOn D bs (ext zD) then S.F yw bs else 0) = S.F yw bs := by
    intro bs
    have hiff : ∀ zD : {j : Fin n // j ∈ D} → B,
        agreesOn D bs (ext zD) ↔ (fun j : {j : Fin n // j ∈ D} => bs j) = zD := by
      intro zD
      constructor
      · intro h
        funext j
        rw [show bs (j : Fin n) = ext zD j from h j j.2, hext zD j j.2]
      · rintro rfl
        intro j hj
        rw [hext _ j hj]
    rw [Finset.sum_congr rfl fun zD _ => if_congr (hiff zD) rfl rfl,
      Finset.sum_ite_eq Finset.univ
        (fun j : {j : Fin n // j ∈ D} => bs j) (fun _ => S.F yw bs),
      if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun bs _ => hinner bs, S.F_sum yw]

/-- **The weighted core mass is at most one** (needed to give the
alignment bound's right side its sign): with a `[0,1]`-valued weight,
the weighted core-correlation mass is at most `τ(σ*σ) = 1`. -/
theorem coreMass_raw_le_one (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (extA : ({j : Fin n // j ∈ D} → A) → Fin n → A)
    (hextA : ∀ (zD : {j : Fin n // j ∈ D} → A) (j : Fin n) (hj : j ∈ D),
      extA zD j = zD ⟨j, hj⟩)
    (extB : ({j : Fin n // j ∈ D} → B) → Fin n → B)
    (hextB : ∀ (zD : {j : Fin n // j ∈ D} → B) (j : Fin n) (hj : j ∈ D),
      extB zD j = zD ⟨j, hj⟩) :
    (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 *
            (S.M.τ (star S.σ *
              (S.coreEffectA D xw (extA zD.1) * S.σ *
                S.coreEffectB D yw (extB zD.2)))).re) ≤ 1 := by
  classical
  have hinner : ∀ (xw : Fin n → X) (yw : Fin n → Y),
      (∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        w xw yw zD.1 zD.2 *
          (S.M.τ (star S.σ *
            (S.coreEffectA D xw (extA zD.1) * S.σ *
              S.coreEffectB D yw (extB zD.2)))).re) ≤ 1 := by
    intro xw yw
    have hle : (∑ zD : ({j : Fin n // j ∈ D} → A) ×
        ({j : Fin n // j ∈ D} → B),
        w xw yw zD.1 zD.2 *
          (S.M.τ (star S.σ *
            (S.coreEffectA D xw (extA zD.1) * S.σ *
              S.coreEffectB D yw (extB zD.2)))).re)
        ≤ ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            (S.M.τ (star S.σ *
              (S.coreEffectA D xw (extA zD.1) * S.σ *
                S.coreEffectB D yw (extB zD.2)))).re := by
      refine Finset.sum_le_sum fun zD _ => ?_
      exact mul_le_of_le_one_left
        (S.M.pairing_nonneg S.σ (S.coreEffectA_isPosElem D xw (extA zD.1))
          (S.coreEffectB_isPosElem D yw (extB zD.2)))
        (hw1 _ _ _ _)
    refine hle.trans (le_of_eq ?_)
    have hexp : star S.σ *
        ((∑ zA : {j : Fin n // j ∈ D} → A, S.coreEffectA D xw (extA zA)) *
          S.σ *
          (∑ zB : {j : Fin n // j ∈ D} → B, S.coreEffectB D yw (extB zB)))
        = ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            star S.σ * (S.coreEffectA D xw (extA zD.1) * S.σ *
              S.coreEffectB D yw (extB zD.2)) := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun zA _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
    have h1 := congrArg (fun z => (S.M.τ z).re) hexp
    simp only [map_sum, Complex.re_sum] at h1
    rw [← h1, S.sum_coreEffectA_ext D xw extA hextA,
      S.sum_coreEffectB_ext D yw extB hextB, one_mul, mul_one,
      S.σ_normalized, Complex.one_re]
  calc (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 *
            (S.M.τ (star S.σ *
              (S.coreEffectA D xw (extA zD.1) * S.σ *
                S.coreEffectB D yw (extB zD.2)))).re)
      ≤ ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) * 1 := by
        refine Finset.sum_le_sum fun xw _ => Finset.sum_le_sum fun yw _ => ?_
        exact mul_le_mul_of_nonneg_left (hinner xw yw)
          (Finset.prod_nonneg fun j _ => hμ _ _)
    _ = 1 := by
        rw [Finset.sum_congr rfl fun xw _ => Finset.sum_congr rfl
          fun yw _ => mul_one _]
        exact sum_prod_mu_eq_one μ hμsum

end TracialStrategy

/-! ## Canonical label builders

Local copies of the `Costs.lean` canonicalization maps (`keepOn`,
`keepOff`, `extendCoreA/B`, `aLabel`, `bLabel`), with definitionally
identical bodies, so that the alignment-bound helpers below can be
stated before `Costs.lean` elaborates; the bridge in `Costs.lean` is
`rfl`. -/

/-- Local copy of `keepOn` (definitionally equal). -/
noncomputable def mkKeepOn {α : Type} [Nonempty α] (R₀ : Finset (Fin n))
    (wd : Fin n → α) : Fin n → α :=
  fun j => if j ∈ R₀ then wd j else Classical.arbitrary α

/-- Local copy of `keepOff` (definitionally equal). -/
noncomputable def mkKeepOff {α : Type} [Nonempty α] (R₀ : Finset (Fin n))
    (wd : Fin n → α) : Fin n → α :=
  fun j => if j ∈ R₀ then Classical.arbitrary α else wd j

/-- Local copy of `extendCoreA` (definitionally equal). -/
noncomputable def mkExtA (D : Finset (Fin n))
    (zD : {j : Fin n // j ∈ D} → A) : Fin n → A :=
  fun j => if h : j ∈ D then zD ⟨j, h⟩ else Classical.arbitrary A

/-- Local copy of `extendCoreB` (definitionally equal). -/
noncomputable def mkExtB (D : Finset (Fin n))
    (zD : {j : Fin n // j ∈ D} → B) : Fin n → B :=
  fun j => if h : j ∈ D then zD ⟨j, h⟩ else Classical.arbitrary B

/-- Local copy of the canonical Alice label `aLabel` (definitionally
equal; the codomain is the unfolding of the `ALabel` abbreviation). -/
noncomputable def mkALabel (D R₀ : Finset (Fin n)) (xw : Fin n → X)
    (yw : Fin n → Y) (zD : {j : Fin n // j ∈ D} → A) :
    Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A) :=
  (R₀, mkKeepOn R₀ xw, mkKeepOff R₀ yw, mkExtA D zD)

/-- Local copy of the canonical Bob label `bLabel` (definitionally
equal). -/
noncomputable def mkBLabel (D R₀ : Finset (Fin n)) (xw : Fin n → X)
    (yw : Fin n → Y) (zD : {j : Fin n // j ∈ D} → B) :
    Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B) :=
  (R₀, mkKeepOff R₀ xw, mkKeepOn R₀ yw, mkExtB D zD)

theorem mkKeepOn_eq_on {α : Type} [Nonempty α] (R₀ : Finset (Fin n))
    (wd : Fin n → α) {j : Fin n} (hj : j ∈ R₀) :
    mkKeepOn R₀ wd j = wd j := if_pos hj

theorem mkKeepOff_eq_off {α : Type} [Nonempty α] (R₀ : Finset (Fin n))
    (wd : Fin n → α) {j : Fin n} (hj : j ∉ R₀) :
    mkKeepOff R₀ wd j = wd j := if_neg hj

/-- The Alice label reads its `xw` only on `R₀` and its `yw` only off
`R₀`. -/
theorem mkALabel_congr (D R₀ : Finset (Fin n)) {xw xw' : Fin n → X}
    {yw yw' : Fin n → Y} (zD : {j : Fin n // j ∈ D} → A)
    (hx : ∀ j ∈ R₀, xw j = xw' j) (hy : ∀ j ∉ R₀, yw j = yw' j) :
    mkALabel D R₀ xw yw zD = mkALabel D R₀ xw' yw' zD := by
  unfold mkALabel
  have h1 : mkKeepOn R₀ xw = mkKeepOn R₀ xw' := by
    funext j
    unfold mkKeepOn
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj, hx j hj]
    · rw [if_neg hj, if_neg hj]
  have h2 : mkKeepOff R₀ yw = mkKeepOff R₀ yw' := by
    funext j
    unfold mkKeepOff
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, hy j hj]
  rw [h1, h2]

/-- The Bob label reads its `xw` only off `R₀` and its `yw` only on
`R₀`. -/
theorem mkBLabel_congr (D R₀ : Finset (Fin n)) {xw xw' : Fin n → X}
    {yw yw' : Fin n → Y} (zD : {j : Fin n // j ∈ D} → B)
    (hx : ∀ j ∉ R₀, xw j = xw' j) (hy : ∀ j ∈ R₀, yw j = yw' j) :
    mkBLabel D R₀ xw yw zD = mkBLabel D R₀ xw' yw' zD := by
  unfold mkBLabel
  have h1 : mkKeepOff R₀ xw = mkKeepOff R₀ xw' := by
    funext j
    unfold mkKeepOff
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, hx j hj]
  have h2 : mkKeepOn R₀ yw = mkKeepOn R₀ yw' := by
    funext j
    unfold mkKeepOn
    by_cases hj : j ∈ R₀
    · rw [if_pos hj, if_pos hj, hy j hj]
    · rw [if_neg hj, if_neg hj]
  rw [h1, h2]

/-! ## Weight positivity, effect positivity, canonical reads -/

theorem setWeightX_nonneg (S₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y)
    (w : Fin n → X) : 0 ≤ setWeightX S₀ μ xref yref w := by
  unfold setWeightX
  split
  · exact Finset.prod_nonneg fun j _ => hμ _ _
  · exact le_refl 0

theorem setWeightY_nonneg (S₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y)
    (v : Fin n → Y) : 0 ≤ setWeightY S₀ μ xref yref v := by
  unfold setWeightY
  split
  · exact Finset.prod_nonneg fun j _ => hμ _ _
  · exact le_refl 0

namespace TracialStrategy

variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}

/-- Revealed-set effects are algebraically positive (Alice). -/
theorem setEffectA_isPosElem (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y)
    (zA : Fin n → A) : IsPosElem (S.setEffectA D R₀ μ xref yref zA) := by
  unfold setEffectA weightedAvg
  rw [show ((((∑ w : Fin n → X, setWeightX R₀ μ xref yref w : ℝ)) : ℂ))⁻¹
      = ((((∑ w : Fin n → X, setWeightX R₀ μ xref yref w)⁻¹ : ℝ)) : ℂ) from
    (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun w _ =>
      setWeightX_nonneg R₀ μ hμ xref yref w))
  refine isPosElem_sum _ _ fun w _ => ?_
  exact (S.coreEffectA_isPosElem D w zA).smul_ofReal
    (setWeightX_nonneg R₀ μ hμ xref yref w)

/-- Revealed-set effects are algebraically positive (Bob). -/
theorem setEffectB_isPosElem (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (xref : Fin n → X) (yref : Fin n → Y)
    (zB : Fin n → B) : IsPosElem (S.setEffectB D R₀ μ xref yref zB) := by
  unfold setEffectB weightedAvg
  rw [show ((((∑ v : Fin n → Y, setWeightY R₀ μ xref yref v : ℝ)) : ℂ))⁻¹
      = ((((∑ v : Fin n → Y, setWeightY R₀ μ xref yref v)⁻¹ : ℝ)) : ℂ) from
    (Complex.ofReal_inv _).symm]
  refine IsPosElem.smul_ofReal ?_
    (inv_nonneg.mpr (Finset.sum_nonneg fun v _ =>
      setWeightY_nonneg R₀ μ hμ xref yref v))
  refine isPosElem_sum _ _ fun v _ => ?_
  exact (S.coreEffectB_isPosElem D v zB).smul_ofReal
    (setWeightY_nonneg R₀ μ hμ xref yref v)

/-- Canonicalized reference words read back to the raw words (Alice). -/
theorem setEffectA_canon (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (xw : Fin n → X) (yw : Fin n → Y) (zA : Fin n → A) :
    S.setEffectA D R₀ μ (mkKeepOn R₀ xw) (mkKeepOff R₀ yw) zA
      = S.setEffectA D R₀ μ xw yw zA :=
  S.setEffectA_congr D R₀ μ zA (fun j hj => mkKeepOn_eq_on R₀ xw hj)
    (fun j hj => mkKeepOff_eq_off R₀ yw hj)

/-- Canonicalized reference words read back to the raw words (Bob). -/
theorem setEffectB_canon (D R₀ : Finset (Fin n)) (μ : X → Y → ℝ)
    (xw : Fin n → X) (yw : Fin n → Y) (zB : Fin n → B) :
    S.setEffectB D R₀ μ (mkKeepOff R₀ xw) (mkKeepOn R₀ yw) zB
      = S.setEffectB D R₀ μ xw yw zB :=
  S.setEffectB_congr D R₀ μ zB (fun j hj => mkKeepOff_eq_off R₀ xw hj)
    (fun j hj => mkKeepOn_eq_on R₀ yw hj)

end TracialStrategy

/-! ## Word splitting along a coordinate block -/

/-- Split a word into its values on a block `L` and off it. -/
def wordSplit (L : Finset (Fin n)) (α : Type) :
    (Fin n → α) ≃
      (({j : Fin n // j ∈ L} → α) × ({j : Fin n // ¬ j ∈ L} → α)) :=
  Equiv.piEquivPiSubtypeProd (fun j => j ∈ L) (fun _ => α)

theorem wordSplit_symm_mem (L : Finset (Fin n)) (α : Type)
    (ω : {j : Fin n // j ∈ L} → α) (g : {j : Fin n // ¬ j ∈ L} → α)
    {j : Fin n} (hj : j ∈ L) :
    (wordSplit L α).symm (ω, g) j = ω ⟨j, hj⟩ := by
  simp [wordSplit, Equiv.piEquivPiSubtypeProd_symm_apply, hj]

theorem wordSplit_symm_notMem (L : Finset (Fin n)) (α : Type)
    (ω : {j : Fin n // j ∈ L} → α) (g : {j : Fin n // ¬ j ∈ L} → α)
    {j : Fin n} (hj : ¬ j ∈ L) :
    (wordSplit L α).symm (ω, g) j = g ⟨j, hj⟩ := by
  simp [wordSplit, Equiv.piEquivPiSubtypeProd_symm_apply, hj]

/-- Reindex a word sum through the block split. -/
theorem sum_wordSplit {α : Type} [Fintype α] {V : Type*} [AddCommMonoid V]
    (L : Finset (Fin n)) (F : (Fin n → α) → V) :
    (∑ xw : Fin n → α, F xw)
      = ∑ ω : {j : Fin n // j ∈ L} → α,
          ∑ g : {j : Fin n // ¬ j ∈ L} → α,
            F ((wordSplit L α).symm (ω, g)) := by
  rw [← Equiv.sum_comp (wordSplit L α).symm F, Fintype.sum_prod_type]

/-- Split a full-coordinate product along the block. -/
theorem prod_wordSplit (L : Finset (Fin n)) (f : Fin n → ℝ) :
    (∏ j : Fin n, f j)
      = (∏ c : {j : Fin n // j ∈ L}, f c) *
        ∏ c : {j : Fin n // ¬ j ∈ L}, f c := by
  rw [← Finset.prod_mul_prod_compl L f]
  congr 1
  · exact Finset.prod_subtype L (fun x => Iff.rfl) f
  · exact Finset.prod_subtype Lᶜ (fun x => Finset.mem_compl) f

/-- The product prior through a split Alice word. -/
theorem prod_mu_wordSplit (L : Finset (Fin n)) (μ : X → Y → ℝ)
    (yw : Fin n → Y) (ω : {j : Fin n // j ∈ L} → X)
    (g : {j : Fin n // ¬ j ∈ L} → X) :
    (∏ j : Fin n, μ ((wordSplit L X).symm (ω, g) j) (yw j))
      = (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) *
        ∏ c : {j : Fin n // ¬ j ∈ L}, μ (g c) (yw c) := by
  rw [prod_wordSplit L (fun j => μ ((wordSplit L X).symm (ω, g) j) (yw j))]
  congr 1
  · exact Finset.prod_congr rfl fun c _ => by
      rw [wordSplit_symm_mem L X ω g c.2]
  · exact Finset.prod_congr rfl fun c _ => by
      rw [wordSplit_symm_notMem L X ω g c.2]

/-- The product prior through a split Bob word (mirror). -/
theorem prod_mu_wordSplit' (L : Finset (Fin n)) (μ : X → Y → ℝ)
    (xw : Fin n → X) (ω : {j : Fin n // j ∈ L} → Y)
    (g : {j : Fin n // ¬ j ∈ L} → Y) :
    (∏ j : Fin n, μ (xw j) ((wordSplit L Y).symm (ω, g) j))
      = (∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) *
        ∏ c : {j : Fin n // ¬ j ∈ L}, μ (xw c) (g c) := by
  rw [prod_wordSplit L (fun j => μ (xw j) ((wordSplit L Y).symm (ω, g) j))]
  congr 1
  · exact Finset.prod_congr rfl fun c _ => by
      rw [wordSplit_symm_mem L Y ω g c.2]
  · exact Finset.prod_congr rfl fun c _ => by
      rw [wordSplit_symm_notMem L Y ω g c.2]

/-- Fubini for a product over a block: total conditional mass. -/
theorem sum_prod_pi_subtype {α : Type} [Fintype α] (L : Finset (Fin n))
    (f : {j : Fin n // j ∈ L} → α → ℝ) :
    (∑ ω : {j : Fin n // j ∈ L} → α, ∏ c, f c (ω c))
      = ∏ c : {j : Fin n // j ∈ L}, ∑ v : α, f c v := by
  have hps := Finset.prod_univ_sum
    (fun _ : {j : Fin n // j ∈ L} => (Finset.univ : Finset α)) f
  rw [Fintype.piFinset_univ] at hps
  exact hps.symm

end CommutingRepetition
