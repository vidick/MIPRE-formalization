/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Bernoulli/
FromHToG/MoveLemmas/TailStage.lean, to the symmetric model of `planning/c6b-plan.md`; not a
vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.Bernoulli.FromHToG.MoveLemmas.Basic
public import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.MoveLemmas.TailStage

@[expose] public section

/-!
# Section 12 pasting: from-H-to-G head-tail stage reindexing

The head-tail reindexing lemmas for the adjacent-stage source expression in the paper's
`from H to G` chain: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas/TailStage.lean` in the
port of `planning/c6b-plan.md` (milestone M11, section "Port conventions").

The slice family is an `IdxPolyFamily params 𝔓`, so the sandwiched family, its outcomes and the
recurrence weights are local operators in `𝔓`, and `ᴴ` is `star`. The vendored second bipartite
state `ψbi : QuantumState (ι × ι)` both places and evaluates, so it is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; `leftTensor (ι₂ := ι)`/
`rightTensor (ι₁ := ι)` are `S.L`/`S.R`. The vendored weight operator, also named `S` (an explicit
argument of `fromHToG_cons_type_outcome_sum`, a `let` in
`fromHToGTailStageMass_cons_eq_adjacentStageA0_branch`), is renamed `W`; it is positional, so
callers are unaffected. No vendored lemma here has a swap, density or normalization hypothesis.

## Not ported

- `fromHToG_gHatTupleType_cons_eq`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq PointTuple uniformDistribution avgOver avgOver_congr
  avgOver_uniform_equiv avgOver_uniform_prod)
open MIPStarRE.LDT.Pasting (GHatType GHatOutcome GHatTupleOutcome prependTypeBit gHatTupleType
  gHatTupleOutcomeConsEquiv' pointTupleConsEquiv fromHToG_gHatTupleType_cons_eq)
open MIPRE.LIDT.Co (SymModel IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Head-tail unfolding of one completed-slice sandwich outcome. -/
theorem fromHToG_gHatSandwichFamily_cons_outcome (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params 𝔓) {n : ℕ}
    (x : Fq params) (xs : PointTuple params n)
    (g : GHatOutcome params) (gs : GHatTupleOutcome params n) :
    (gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome (Fin.cons g gs) =
      let U := (gHatIdxMeas params family x).outcome g
      let T := gHatHalfProductOutcomeOperator params family n xs gs
      U * T * star T * U := by
  change (gHatIdxMeas params family x).outcome g *
      gHatHalfProductOutcomeOperator params family n xs gs *
        star ((gHatIdxMeas params family x).outcome g *
          gHatHalfProductOutcomeOperator params family n xs gs) = _
  rw [star_mul, fromHToG_gHatIdxMeas_outcome_isHermitian, ← mul_assoc]

/-- Reindex a filtered sum over nonempty completed-outcome tuples into head and
tail filtered sums. -/
theorem fromHToG_cons_type_outcome_sum (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) {n : ℕ}
    (b : Bool) (τ : GHatType n) (x : Fq params) (xs : PointTuple params n) (W : 𝔓) :
    (∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
        gHatTupleType gs' = prependTypeBit b τ,
      S.ev (S.L ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
        S.R W)) =
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          S.ev (S.L (U * T * star T * U) * S.R W) := by
  classical
  simp only [Finset.sum_filter]
  rw [← (gHatTupleOutcomeConsEquiv' params n).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : g.isSome = b
  · rw [ite_eq_left hg]
    refine Finset.sum_congr rfl fun gs _ => ?_
    rw [show (gHatTupleOutcomeConsEquiv' params n).symm (g, gs) = Fin.cons g gs from rfl,
      fromHToG_gHatSandwichFamily_cons_outcome]
    simp only [fromHToG_gHatTupleType_cons_eq, hg, true_and]
  · rw [ite_eq_right hg]
    refine Finset.sum_eq_zero fun gs _ => ite_eq_right_iff.2 fun h => ?_
    exact absurd ((fromHToG_gHatTupleType_cons_eq params b τ g gs).1 h).1 hg

/-- Fold a tail point/outcome average written directly with the sandwich-family
outcomes into `averagedSandwichByTypeSubMeas`. -/
theorem fromHToG_avgOver_tail_type_ev_sandwich (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓) (n : ℕ) (τ : GHatType n) (B : 𝔓) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        S.ev (S.L ((gHatSandwichFamily params family n xs).outcome gs) * S.R B)) =
      S.ev (S.L (averagedSandwichByTypeSubMeas params family n τ).total * S.R B) :=
  fromHToG_avgOver_tail_type_ev params S family n τ B

/-- A fixed head-bit branch of a nonterminal Lean stage expands to the paper's
adjacent-stage source expression. -/
theorem fromHToGTailStageMass_cons_eq_adjacentStageA0_branch (params : Parameters)
    [FieldModel params.q] (S : SymModel 𝔓 K) (family : IdxPolyFamily params 𝔓)
    (ℓ n : ℕ) (b : Bool) (τ : GHatType n) :
    fromHToGTailStageMass params S family ℓ (prependTypeBit b τ) =
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              S.ev (S.L (U * T * star T * U) * S.R W) := by
  let W := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
  let F : Fq params → PointTuple params n → ℝ := fun x xs =>
    ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        S.ev (S.L (U * T * star T * U) * S.R W)
  calc
    fromHToGTailStageMass params S family ℓ (prependTypeBit b τ)
        = avgOver (uniformDistribution (PointTuple params (n + 1))) (fun xs' =>
            ∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
                gHatTupleType gs' = prependTypeBit b τ,
              S.ev (S.L ((gHatSandwichFamily params family (n + 1) xs').outcome gs') *
                S.R W)) :=
          (fromHToG_avgOver_tail_type_ev_sandwich params S family (n + 1)
            (prependTypeBit b τ) W).symm
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
              gHatTupleType gs' = prependTypeBit b τ,
            S.ev (S.L ((gHatSandwichFamily params family (n + 1)
              ((pointTupleConsEquiv params n).symm q)).outcome gs') * S.R W)) :=
          avgOver_uniform_equiv (pointTupleConsEquiv params n) _
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          F q.1 q.2) :=
          avgOver_congr _ _ _ fun q =>
            fromHToG_cons_type_outcome_sum params S family b τ q.1 q.2 W
    _ = _ := avgOver_uniform_prod (α := Fq params) (β := PointTuple params n) (f := F)

end MIPRE.LIDT.Co.Pasting

end
