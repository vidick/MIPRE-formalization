/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core/FiniteProbability.lean, from a snapshot of the `main` branch supplied on 2026-09-25
(archive, no commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import Mathlib

/-!
# Finite probability distributions on finite types

Canonical owner of the finite-distribution vocabulary shared by every later
module of the core.

Source: `Blueprint/Nodes/B23-Games/Parts/01-GamesAndStrategies.tex`, `def:game`
item (3), and `Blueprint/Nodes/B05-NPA-Core/Math.tex`, `def:n7b` ("a probability
distribution `μ` on `X × Y`").

A distribution carries its pointwise nonnegativity and its total-mass-one proof
as structure fields, so that no later module has to re-assume them.

## The consolidation visit (2026-08-04, `CAMPAIGN.md` §8.4 / the c38 ratified
Core visit)

Everything from `ext` onwards was placed here at that visit, because the nodes
had been re-proving it: extensionality existed **five** times (`B16.prob_ext`,
`B12.finiteProbability_ext`, and privates in `B07`, `B09` and `B23`), the
pushforward of a finite law **three** times (`B09Glue.probabilityMap`,
`B23.finProbMap`, `B16.map`), and the uniform law on a finite type **three**
times (`B13Var.uniform`, `B29.uniformFin`, `B28.uniformFinProb`).  The copies
that re-root without changing a definitional shape now do; the ones that do
not are named in the ledger with their measured cost.

`finProbOfPMF` moved here from `Nodes/B24/LDGamePacking.lean` under ruling
M-1.a (`CAMPAIGN.md` §8.9): every game whose question datum is a `PMF` needs
it, and its node-level home forced `B23 → B24`, an inversion recorded at c36
and retired here.
-/

namespace Tsirelson

universe u v w

/-- A probability distribution on a finite type: a real weight function together
with proofs of pointwise nonnegativity and total mass one. -/
structure FiniteProbability (Ω : Type u) [Fintype Ω] where
  /-- The weight of each point. -/
  prob : Ω → ℝ
  /-- Weights are nonnegative. -/
  nonneg : ∀ ω, 0 ≤ prob ω
  /-- Weights sum to one. -/
  sum_eq_one : ∑ ω, prob ω = 1

namespace FiniteProbability

variable {Ω : Type u} [Fintype Ω]

@[simp] theorem sum_prob (μ : FiniteProbability Ω) : ∑ ω, μ.prob ω = 1 := μ.sum_eq_one

theorem prob_le_one (μ : FiniteProbability Ω) (ω : Ω) : μ.prob ω ≤ 1 := by
  rw [← μ.sum_eq_one]
  exact Finset.single_le_sum (fun i _ => μ.nonneg i) (Finset.mem_univ ω)

theorem prob_mem_Icc (μ : FiniteProbability Ω) (ω : Ω) : μ.prob ω ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨μ.nonneg ω, μ.prob_le_one ω⟩

/-- Total mass one forces the carrier to be nonempty. -/
theorem nonempty (μ : FiniteProbability Ω) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h0 : ∑ ω, μ.prob ω = 0 := by simp
  rw [μ.sum_eq_one] at h0
  exact one_ne_zero h0

/-- The support of a distribution: the points of strictly positive weight.

This is the set `S` of `Blueprint/Nodes/B23-Games/Parts/01-GamesAndStrategies.tex`,
`def:comm-strategy`, which restricts local commutation of a PCC strategy. -/
def support (μ : FiniteProbability Ω) : Set Ω := {ω | 0 < μ.prob ω}

@[simp] theorem mem_support {μ : FiniteProbability Ω} {ω : Ω} :
    ω ∈ μ.support ↔ 0 < μ.prob ω := Iff.rfl

theorem support_nonempty (μ : FiniteProbability Ω) : (μ.support).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hz : ∀ ω : Ω, μ.prob ω = 0 := by
    intro ω
    have : ω ∉ μ.support := by rw [h]; exact Set.notMem_empty ω
    rw [mem_support, not_lt] at this
    exact le_antisymm this (μ.nonneg ω)
  have : ∑ ω, μ.prob ω = 0 := Finset.sum_eq_zero fun ω _ => hz ω
  rw [μ.sum_eq_one] at this
  exact one_ne_zero this

/-- A weighted sum of numbers in `[0,1]` again lies in `[0,1]`.

This is the arithmetic core of every payoff bound in `Core/Value.lean`. -/
theorem sum_mul_mem_Icc (μ : FiniteProbability Ω) {f : Ω → ℝ}
    (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) :
    ∑ ω, μ.prob ω * f ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (h0 ω)
  · calc ∑ ω, μ.prob ω * f ω
        ≤ ∑ ω, μ.prob ω * 1 :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (h1 ω) (μ.nonneg ω)
      _ = 1 := by simp

/-! ## Extensionality

Two laws with the same weights are equal: the remaining fields are proofs. -/

/-- **Extensionality.**  The five node-level copies this retires all proved it
by the same `cases`-then-`funext`; the `@[ext]` attribute is what none of them
could supply, and two files (`B28/SuccinctS4.lean`, `B29/Part06Components.lean`)
carried its absence as a written remark. -/
@[ext] theorem ext {μ ν : FiniteProbability Ω} (h : ∀ ω, μ.prob ω = ν.prob ω) : μ = ν := by
  cases μ
  cases ν
  simp only [FiniteProbability.mk.injEq]
  exact funext h

/-- Two **distinct** points carry at most the whole mass.

Stated without a `DecidableEq` binder — the statement mentions no `Finset`, and
the instance the proof needs is classical. -/
theorem prob_add_prob_le_one (μ : FiniteProbability Ω) {a b : Ω} (hab : a ≠ b) :
    μ.prob a + μ.prob b ≤ 1 := by
  classical
  calc μ.prob a + μ.prob b = ∑ ω ∈ ({a, b} : Finset Ω), μ.prob ω :=
        (Finset.sum_pair hab).symm
    _ ≤ ∑ ω, μ.prob ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun ω _ _ => μ.nonneg ω)
    _ = 1 := μ.sum_eq_one

/-! ## Pushforward

The image law along a map of finite types: the fibre sums.  The body is the
`Finset.filter` form, which is the one `B09Glue.probabilityMap` and
`B23.finProbMap` already had, so both re-root to it with their `_prob` lemmas
still true by `rfl`. -/

section Map

variable {Ω' : Type v} {Ω'' : Type w} [Fintype Ω'] [Fintype Ω''] [DecidableEq Ω'] [DecidableEq Ω'']

/-- **Push a finite law forward along a map**: the mass of a point is the mass
of its fibre. -/
noncomputable def map (f : Ω → Ω') (μ : FiniteProbability Ω) : FiniteProbability Ω' where
  prob ω' := ∑ ω ∈ Finset.univ.filter (fun ω => f ω = ω'), μ.prob ω
  nonneg _ := Finset.sum_nonneg fun _ _ => μ.nonneg _
  sum_eq_one := by
    rw [Finset.sum_fiberwise]
    exact μ.sum_eq_one

@[simp] theorem map_prob (f : Ω → Ω') (μ : FiniteProbability Ω) (ω' : Ω') :
    (map f μ).prob ω' = ∑ ω ∈ Finset.univ.filter (fun ω => f ω = ω'), μ.prob ω := rfl

/-- The pushforward's weights as a sum over the whole type. -/
theorem map_prob_eq_sum_ite (f : Ω → Ω') (μ : FiniteProbability Ω) (ω' : Ω') :
    (map f μ).prob ω' = ∑ ω, if f ω = ω' then μ.prob ω else 0 := by
  rw [map_prob, Finset.sum_filter]

/-- **A point's mass is at most its fibre's.**  Pushing forward can only
concentrate: `f ω` collects `ω` together with everything else `f` identifies
with it.  Injectivity of `f` would make it an equality.

This is the domination lemma the `hmu` obligation of `CAMPAIGN.md` §8.9 runs
on; it existed for none of the three node-level pushforwards. -/
theorem le_map_prob (f : Ω → Ω') (μ : FiniteProbability Ω) (ω : Ω) :
    μ.prob ω ≤ (map f μ).prob (f ω) := by
  rw [map_prob]
  exact Finset.single_le_sum (fun x _ => μ.nonneg x)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ ω, rfl⟩)

/-- A point outside the image of `f` carries no mass. -/
theorem map_prob_eq_zero (f : Ω → Ω') (μ : FiniteProbability Ω) {ω' : Ω'}
    (hω : ω' ∉ Set.range f) : (map f μ).prob ω' = 0 := by
  rw [map_prob]
  refine Finset.sum_eq_zero fun ω hω' => ?_
  rw [Finset.mem_filter] at hω'
  exact absurd ⟨ω, hω'.2⟩ hω

/-- **Integrating after a pushforward is integrating the pullback.** -/
theorem sum_map_prob (f : Ω → Ω') (μ : FiniteProbability Ω) (g : Ω' → ℝ) :
    ∑ ω', (map f μ).prob ω' * g ω' = ∑ ω, μ.prob ω * g (f ω) := by
  simp only [map_prob, Finset.sum_mul]
  calc ∑ ω', ∑ ω ∈ Finset.univ.filter (fun ω => f ω = ω'), μ.prob ω * g ω'
      = ∑ ω', ∑ ω ∈ Finset.univ.filter (fun ω => f ω = ω'), μ.prob ω * g (f ω) :=
        Finset.sum_congr rfl fun ω' _ =>
          Finset.sum_congr rfl fun ω hω => by rw [(Finset.mem_filter.mp hω).2]
    _ = ∑ ω, μ.prob ω * g (f ω) := Finset.sum_fiberwise _ _ _

/-- **Pushing forward twice is pushing forward along the composite.** -/
theorem map_map (f : Ω → Ω') (g : Ω' → Ω'') (μ : FiniteProbability Ω) :
    map g (map f μ) = map (g ∘ f) μ := by
  ext ω''
  rw [map_prob_eq_sum_ite, map_prob_eq_sum_ite]
  calc ∑ ω', (if g ω' = ω'' then (map f μ).prob ω' else 0)
      = ∑ ω', (map f μ).prob ω' * (if g ω' = ω'' then 1 else 0) := by
        refine Finset.sum_congr rfl fun ω' _ => ?_
        split <;> simp_all
    _ = ∑ ω, μ.prob ω * (if g (f ω) = ω'' then 1 else 0) := sum_map_prob f μ _
    _ = ∑ ω, (if (g ∘ f) ω = ω'' then μ.prob ω else 0) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [Function.comp_apply]
        split <;> simp_all

end Map

/-! ## The uniform law -/

/-- **The uniform law on a nonempty finite type.** -/
noncomputable def uniform (α : Type u) [Fintype α] [Nonempty α] : FiniteProbability α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_eq_one := by
    have hcard : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

@[simp] theorem uniform_prob {α : Type u} [Fintype α] [Nonempty α] (a : α) :
    (uniform α).prob a = (Fintype.card α : ℝ)⁻¹ := rfl

end FiniteProbability

/-! ## The `PMF` bridge

`CAMPAIGN.md` §8.9, ruling M-1: a sampler's distribution is data derived by
pushforward of a uniform seed law, and every consumer takes it as a
`FiniteProbability`.  The conversion is unconditional on a finite type. -/

/-- **Every `PMF` on a finite type is a `FiniteProbability`.**

Placed here by the c39 consolidation visit; it lived in
`Nodes/B24/LDGamePacking.lean`, which forced the `B23 → B24` import inversion
recorded at c36. -/
noncomputable def finProbOfPMF {Ω : Type u} [Fintype Ω] (p : PMF Ω) : FiniteProbability Ω where
  prob := fun w => (p w).toReal
  nonneg := fun _ => ENNReal.toReal_nonneg
  sum_eq_one := by
    have hne : ∀ w : Ω, p w ≠ ⊤ := fun w => PMF.apply_ne_top p w
    have hsum : (∑ w, p w) = 1 := by
      have h := p.tsum_coe
      rwa [tsum_fintype] at h
    calc ∑ w, (p w).toReal
        = (∑ w, p w).toReal := (ENNReal.toReal_sum fun w _ => hne w).symm
      _ = 1 := by rw [hsum, ENNReal.toReal_one]

@[simp] theorem finProbOfPMF_prob {Ω : Type u} [Fintype Ω] (p : PMF Ω) (w : Ω) :
    (finProbOfPMF p).prob w = (p w).toReal := rfl

/-- **The conversion commutes with pushforward.**  Turning a `PMF` into a
`FiniteProbability` and then pushing forward is pushing forward and then
converting — an `ℝ≥0∞`-valued `tsum` against a real-valued `Finset` sum.

This is the arithmetic ruling M-1.a's game-law tie rests on. -/
theorem finProbOfPMF_map {Ω : Type u} {Ω' : Type v} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']
    (f : Ω → Ω') (p : PMF Ω) :
    finProbOfPMF (p.map f) = FiniteProbability.map f (finProbOfPMF p) := by
  refine FiniteProbability.ext fun ω' => ?_
  simp only [finProbOfPMF_prob, FiniteProbability.map_prob]
  rw [Finset.sum_filter, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hfω : f ω = ω'
    · rw [if_pos hfω.symm, if_pos hfω]
    · rw [if_neg fun hc : ω' = f ω => hfω hc.symm, if_neg hfω, ENNReal.toReal_zero]
  · intro ω _
    split
    · exact PMF.apply_ne_top p ω
    · exact ENNReal.zero_ne_top

/-- The seed law is uniform, pointwise. -/
theorem finProbOfPMF_uniformOfFintype_prob {Ω : Type u} [Fintype Ω] [Nonempty Ω] (ω : Ω) :
    (finProbOfPMF (PMF.uniformOfFintype Ω)).prob ω = (Fintype.card Ω : ℝ)⁻¹ := by
  rw [finProbOfPMF_prob, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
  simp

/-- **The `PMF`-shaped seed law IS the canonical uniform law.**  This is the tie
that lets the nodes writing `finProbOfPMF (PMF.uniformOfFintype _)`
(`B26.seedLaw`, `B27.ar2SeedLaw`) meet the ones writing the constant. -/
theorem finProbOfPMF_uniformOfFintype {Ω : Type u} [Fintype Ω] [Nonempty Ω] :
    finProbOfPMF (PMF.uniformOfFintype Ω) = FiniteProbability.uniform Ω :=
  FiniteProbability.ext fun ω => by
    rw [finProbOfPMF_uniformOfFintype_prob, FiniteProbability.uniform_prob]

end Tsirelson
