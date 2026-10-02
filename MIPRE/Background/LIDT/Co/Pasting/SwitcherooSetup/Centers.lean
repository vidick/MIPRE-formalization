/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/
SwitcherooSetup/Centers.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Pasting.SwitcherooSetup.Infrastructure

@[expose] public section

/-!
# Section 12 pasting: switcheroo centers

Switcheroo center terms and their sandwich rewrites: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/SwitcherooSetup/Centers.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The vendored second bipartite state `ψbi : QuantumState (ι × ι)` is the symmetric model
`S : SymModel 𝔓 K`, in the vendored argument position; the slice family is an
`IdxPolyFamily params 𝔓` and the auxiliary family `M` an `IdxProjSubMeas (Fq params) Outcome 𝔓`.
The vendored hypothesis `hnorm : ψbi.IsNormalized` of `switcheroo_first_term_close` is dropped,
normalization being a theorem of the model (section "Swap symmetry is a theorem"); callers pass
`params S family M omega hselfM`.

The two sandwich rewrites split the slice-pair average by `avgOver_uniform_prod` and identify
the summands by `S.leftTensor_mul_leftTensor` (the middle one by definitional equality), in place
of the vendored `simp` on `avgOver`.

## Not ported

Nothing: every declaration of the vendored file is ported here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT (Parameters FieldModel Fq avgOver avgOver_congr avgOver_sub
  avgOver_uniform_prod avgOver_uniform_le_const uniformDistribution
  uniformDistribution_weight_sum_le_one)
open MIPStarRE.LDT.Pasting (SliceQuestion SlicePairQuestion avgOver_abs_le_avgOver_abs)
open MIPRE.LIDT.Co (SymModel SubMeas IdxProjSubMeas IdxPolyFamily)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The common comparison scalar `⟨ψ, G ⊗ M ψ⟩` from the switcheroo proof. -/
noncomputable def switcherooAggregateTarget
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      S.ev (S.L ((completePartSubMeas params family q.1).total) * S.R ((M q.2).outcome o))

/-- The first positive term in the switcheroo expansion. -/
noncomputable def switcherooAggregateFirstTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) : ℝ :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      S.ev
        (S.L
          ((M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o))

/-- Rewrite the first positive switcheroo term as a left-sandwich average. -/
theorem switcherooAggregateFirstTerm_eq_leftSandwich
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    switcherooAggregateFirstTerm params S family M =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          Preliminaries.leftSandwichExpectation S
            (uniformDistribution (SliceQuestion params))
            M
            ((completePartSubMeas params family x).total)) := by
  refine (avgOver_uniform_prod (α := SliceQuestion params) (β := SliceQuestion params)
    (fun x y => ∑ o : Outcome, S.ev (S.L ((M y).outcome o *
      (completePartSubMeas params family x).total * (M y).outcome o)))).trans ?_
  refine avgOver_congr _ _ _ fun x => avgOver_congr _ _ _ fun y =>
    Finset.sum_congr rfl fun o _ => ?_
  rw [S.leftTensor_mul_leftTensor, S.leftTensor_mul_leftTensor]

/-- Rewrite the `G ⊗ M` switcheroo center as a middle-sandwich average. -/
theorem switcherooAggregateTarget_eq_middleSandwich
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓) :
    switcherooAggregateTarget params S family M =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          Preliminaries.middleSandwichExpectation S
            (uniformDistribution (SliceQuestion params))
            M
            ((completePartSubMeas params family x).total)) :=
  avgOver_uniform_prod (α := SliceQuestion params) (β := SliceQuestion params)
    (fun x y => ∑ o : Outcome,
      S.ev (S.L ((completePartSubMeas params family x).total) * S.R ((M y).outcome o)))

/-- The first positive switcheroo term is close to the `G ⊗ M` center via the
self-consistency of `M`. -/
theorem switcheroo_first_term_close
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : SymModel 𝔓 K)
    (family : IdxPolyFamily params 𝔓)
    (M : IdxProjSubMeas (Fq params) Outcome 𝔓)
    (omega : ℝ)
    (hselfM : S.SDDRel
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft S params M)
      (switcherooSelfConsistencyRight S params M)
      omega) :
    let firstTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x => Preliminaries.leftSandwichExpectation S
          (uniformDistribution (SliceQuestion params))
          M ((completePartSubMeas params family x).total))
    let commonTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x => Preliminaries.middleSandwichExpectation S
          (uniformDistribution (SliceQuestion params))
          M ((completePartSubMeas params family x).total))
    |firstTerm - commonTerm| ≤ 2 * Real.sqrt omega := by
  intro firstTerm commonTerm
  let L : Fq params → ℝ := fun x =>
    Preliminaries.leftSandwichExpectation S
      (uniformDistribution (SliceQuestion params))
      M ((completePartSubMeas params family x).total)
  let C : Fq params → ℝ := fun x =>
    Preliminaries.middleSandwichExpectation S
      (uniformDistribution (SliceQuestion params))
      M ((completePartSubMeas params family x).total)
  have hselfM_bip := switcherooSelfConsistency_bip params S M omega hselfM
  have hpoint : ∀ x, |L x - C x| ≤ 2 * Real.sqrt omega := fun x =>
    (Preliminaries.switchSandwich S
      (uniformDistribution (SliceQuestion params))
      (uniformDistribution_weight_sum_le_one (SliceQuestion params))
      M
      ((completePartSubMeas params family x).total)
      ⟨(completePartSubMeas params family x).total_nonneg,
        sub_nonneg.mpr (completePartSubMeas params family x).total_le_one⟩
      omega
      hselfM_bip).leftSandwichTransfer
  calc |firstTerm - commonTerm|
      = |avgOver (uniformDistribution (SliceQuestion params)) (fun x => L x - C x)| := by
        rw [avgOver_sub]
    _ ≤ avgOver (uniformDistribution (SliceQuestion params)) (fun x => |L x - C x|) :=
        avgOver_abs_le_avgOver_abs _ _
    _ ≤ 2 * Real.sqrt omega :=
        avgOver_uniform_le_const (fun x : SliceQuestion params => |L x - C x|)
          (2 * Real.sqrt omega) hpoint

end MIPRE.LIDT.Co.Pasting

end
