/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/EntropyBudget.lean
-/
/-
# The resolver entropy budget, consumed form (node 1.2.6)

The resolver entropy inequality (04_resolver_corner.tex, lem
resolver-entropy-cutoffs) is a one-step operator inequality in the
source corner: for a finitely supported random positive contraction `F`
with mean `F̄`, all values in the arena family,
`𝔼 (c_F − c_F̄)*(c_F − c_F̄) ≼ (H₁(F̄) − 𝔼 H₁(F)) p₀`, with the
adjoint-oriented row version for Bob (`H₁(t) = −t log t`, the scalar
entropy of 04_resolver_corner.tex eq H1-definition, extended by
functional calculus).

Section 5 consumes this lemma ONLY through σ-pairings of martingale
increments, telescoped (05_prerounding.tex, eqs positive-functional,
functional-probability-bridge, positive-functional-jensen,
random-martingale-increment): the one-step corner inequalities are
evaluated by the positive functional `ω_K(C) = τ(σ* C σ K)` of mass at
most one, the intermediate operator entropies telescope away, the
nonnegative bottom entropy is dropped, and a single top-level Jensen
step (eq positive-functional-jensen) converts the remaining operator
entropy into the scalar entropy of the branch probability
`p = ω_K(F₀)`.  The increment pairings are exactly squared L²-distances
of the arena's branch vectors, so the telescoped consequence is a
statement about the `ResolverArena` alone:

  `∑ steps 𝔼 ‖Φ(σ, idx_{s+1}, j) − Φ(σ, idx_s, j)‖² ≤ H₁(re τ(σ* F_{i₀} σ K))`.

This file states node 1.2.6 in that consumed form (DIFFERENCES.md D15):

- `EffectMartingale` — the finite martingale datum: a finite path space
  with a probability law and an index path into the effect family, with
  deterministic start.  Conditioning is on the current index fiber (the
  mass-weighted per-fiber mean condition `IsMeanTower`), which is
  implied by adaptedness to any finer filtration, so the Lean
  hypothesis is weaker than the manuscript's question filtration and
  the stated budget correspondingly stronger.
- `ResolverArena.ColEntropyBudget` / `RowEntropyBudget` — the
  telescoped scalar budgets (Alice: column increments against a fixed
  Bob index; Bob: row increments against a fixed Alice index).
- `resolver_arena_entropic` — the existence upgrade of the signed
  `resolver_arena`: an arena satisfying both budgets.  The budgets are
  properties of the corner construction (the cross terms of distinct
  columns are not pinned by the arena identities), so they are packaged
  with the existence claim, not asserted for every arena; the
  `Cornered` extension of `Resolver/EntropyLemma.lean` is the
  construction vocabulary for its proof (nodes 1.2.5.x, 1.2.6).

The per-step normalization `1/N_A` of eq random-martingale-increment is
the uniform live cut and stays in section 5: the budget here is the sum
over all steps, which section 5 divides by the number of steps.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.Arena
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.EntropicArenaBudget

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

/-- A finite effect-martingale datum (05_prerounding.tex, eqs
alice-reveal-martingale, bob-reveal-martingale, abstracted): a finite
path space `Ω` with a probability law and, at each of `steps + 1`
times, an index into the effect family, deterministic at time `0` (the
background-conditioned mean, eq alice-reveal-martingale at `j = 0`).
The martingale property relative to a family is `IsMeanTower` below. -/
structure EffectMartingale (I : Type) (steps : ℕ) : Type 1 where
  Ω : Type
  [instFintypeΩ : Fintype Ω]
  law : Ω → ℝ
  law_nonneg : ∀ ω, 0 ≤ law ω
  law_sum : ∑ ω : Ω, law ω = 1
  idx : Fin (steps + 1) → Ω → I
  idx_zero : ∀ ω ω' : Ω, idx 0 ω = idx 0 ω'

attribute [instance] EffectMartingale.instFintypeΩ

namespace EffectMartingale

variable {I : Type} {steps : ℕ}

/-- The mass-weighted martingale condition relative to a family
`E : I → M.A` (the tower property making eq alice-reveal-martingale a
"positive-contraction martingale"): on each fiber of the time-`s`
index, the law-weighted sum of the time-`(s+1)` family elements equals
the fiber mass times the current element.  Division-free, so zero-mass
fibers carry no condition; conditioning on the index fiber is implied
by conditioning on any finer background, so this hypothesis is weaker
than the manuscript's question filtration. -/
def IsMeanTower [DecidableEq I] {M : StdTracialAlgebra.{0}}
    (X : EffectMartingale I steps) (E : I → M.A) : Prop :=
  ∀ (s : Fin steps) (i : I),
    (((∑ ω ∈ Finset.univ.filter fun ω => X.idx s.castSucc ω = i,
        X.law ω : ℝ) : ℂ)) • E i
      = ∑ ω ∈ Finset.univ.filter fun ω => X.idx s.castSucc ω = i,
          (((X.law ω : ℝ) : ℂ)) • E (X.idx s.succ ω)

end EffectMartingale

namespace ResolverArena

variable {M : StdTracialAlgebra.{0}}
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable {F : I → A → M.A} {G : J → B → M.A}

/-- **The Alice-column entropy budget** (node 1.2.6, consumed form;
04_resolver_corner.tex eq alice-resolver-entropy telescoped and
σ-paired per 05_prerounding.tex eqs positive-functional through
random-martingale-increment): for every effect martingale over the
Alice totals, every unit density, and every fixed Bob index, the total
law-weighted squared L²-increment of the branch vectors along the
martingale is at most the scalar entropy `H₁ = Real.negMulLog` of the
initial branch pairing `re τ(σ* F_{i₀} σ G_j)` (the branch probability
of eq functional-probability-bridge).  The per-step factor `1/N_A` of
eq random-martingale-increment is the uniform cut and stays in
section 5. -/
def ColEntropyBudget [DecidableEq I] (R : ResolverArena M F G) : Prop :=
  ∀ (steps : ℕ) (X : EffectMartingale I steps),
    X.IsMeanTower (fun i => ∑ a : A, F i a) →
    ∀ (σ : M.A), M.τ (star σ * σ) = 1 →
    ∀ (j : J) (ω₀ : X.Ω),
      ∑ s : Fin steps, ∑ ω : X.Ω, X.law ω *
          ‖R.branch σ (X.idx s.succ ω) j
              - R.branch σ (X.idx s.castSucc ω) j‖ ^ 2
        ≤ Real.negMulLog
            (M.τ (star σ * ((∑ a : A, F (X.idx 0 ω₀) a) * σ *
              (∑ b : B, G j b)))).re

/-- **The Bob-row entropy budget** (node 1.2.6, consumed form; the
adjoint-oriented mirror, 04_resolver_corner.tex eq
bob-resolver-entropy telescoped and σ-paired): martingale over the Bob
totals, fixed Alice index, increments in the second branch slot. -/
def RowEntropyBudget [DecidableEq J] (R : ResolverArena M F G) : Prop :=
  ∀ (steps : ℕ) (X : EffectMartingale J steps),
    X.IsMeanTower (fun j => ∑ b : B, G j b) →
    ∀ (σ : M.A), M.τ (star σ * σ) = 1 →
    ∀ (i : I) (ω₀ : X.Ω),
      ∑ s : Fin steps, ∑ ω : X.Ω, X.law ω *
          ‖R.branch σ i (X.idx s.succ ω)
              - R.branch σ i (X.idx s.castSucc ω)‖ ^ 2
        ≤ Real.negMulLog
            (M.τ (star σ * ((∑ a : A, F i a) * σ *
              (∑ b : B, G (X.idx 0 ω₀) b)))).re

end ResolverArena

/-- **Entropic resolver arena** (nodes 1.2.5 + 1.2.6;
04_resolver_corner.tex, thm common-resolver-arena together with lem
resolver-entropy-cutoffs in the consumed form of DIFFERENCES.md D15):
every pair of finite refined `[0,1]`-effect families over nonempty
answer sets admits a resolver arena satisfying both telescoped entropy
budgets.  The budgets hold for the corner construction (the `Cornered`
vocabulary of `Resolver/EntropyLemma.lean`), not for an arbitrary
arena, so they are part of the existence claim. -/
theorem resolver_arena_entropic (M : StdTracialAlgebra.{0})
    {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [DecidableEq I] [DecidableEq J] [Nonempty A] [Nonempty B]
    (F : I → A → M.A) (G : J → B → M.A)
    (hF : ∀ i a, IsPosElem (F i a)) (hG : ∀ j b, IsPosElem (G j b))
    (hF1 : ∀ i, IsPosElem (1 - ∑ a : A, F i a))
    (hG1 : ∀ j, IsPosElem (1 - ∑ b : B, G j b)) :
    ∃ R : ResolverArena M F G, R.ColEntropyBudget ∧ R.RowEntropyBudget := by
  classical
  -- factor the refinements (D13 witnesses)
  choose kA xA hxA using hF
  choose kB yB hyB using hG
  have h : EntropicArena.Hyp M F G :=
    ⟨fun i a => ⟨kA i a, xA i a, hxA i a⟩, fun j b => ⟨kB j b, yB j b, hyB j b⟩, hF1, hG1⟩
  refine ⟨EntropicArena.arena M h kA xA hxA kB yB hyB, ?_, ?_⟩
  · intro steps X hX σ hσ j ω₀
    exact EntropicArena.col_budget M h kA xA hxA kB yB hyB steps X.law X.law_nonneg X.law_sum
      X.idx X.idx_zero hX σ hσ j ω₀
  · intro steps X hX σ hσ i ω₀
    exact EntropicArena.row_budget M h kA xA hxA kB yB hyB steps X.law X.law_nonneg X.law_sum
      X.idx X.idx_zero hX σ hσ i ω₀

end CommutingRepetition
