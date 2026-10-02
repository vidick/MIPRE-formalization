/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Completion
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Local
public import MIPRE.Background.LIDT.Co.Preliminaries.SwitchSandwichPrep.ApproxDelta
public import MIPRE.Background.LIDT.Co.Basic.MeasurementLift

@[expose] public section

/-!
# Preliminary comparison theorems: completion and chain rules

Completion lemmas (`prop:completing-to-measurement`) and the chain inequalities for the
operator-family distance (`prop:triangle-inequality-for-approx_delta`) from the preliminaries
chapter. This is the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean` in the port of
`planning/c6b-plan.md` (milestone M3, section "Port conventions").

The statements whose vendored state is on one space (`closenessAfterCompletion_core_local`,
`sddOpRel_triangle`, `sddOpRel_mono`, `questionSDDOp_chain`, `sddOpRel_chain`) take a vector
state `V : VecState K` and joint operators in `K →L[ℂ] K`; the bipartite ones
(`closenessAfterCompletion_core`, `completingToMeasurement`) take a symmetric model
`S : SymModel 𝔓 K` with local operators in `𝔓`. Each takes the state as an explicit first
argument in the namespace `Preliminaries`, as the vendored lemmas do.

The vendored hypotheses `hψ : ψ.IsNormalized` (of `closenessAfterCompletion_core_local`,
`closenessAfterCompletion_core` and `completingToMeasurement`) and `hperm : PermInvState ψ` (of
the last two) are dropped: normalization is `V.ev_one_of_isNormalized`, and swap symmetry
enters through `bipartiteSSC_implies_localSSC_liftLeft`, which uses the model's
`S.ev_L_eq_ev_R`.

The proof of `closenessAfterCompletion_core_local` bounds the two overlap gaps with
`question_overlap_gap_left` and `question_overlap_gap_right` directly, where the vendored proof
goes through `easyApproxFromApproxDelta_twoFamily` on constant families. In
`closenessAfterCompletion_core` the completion of the left lift and the left lift of the
completion have the same outcomes by `map_add`, `map_sub` and `map_one` of `S.L`, where the
vendored proof compares Kronecker entries.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver avgOver_mono avgOver_const_mul avgOver_sum
  uniformDistribution)

section VecState

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Local (single-register) version of the completion bound: if the measurement `A` is
`ζ`-strongly self-consistent and `δ`-close to `B`, then `A` is
`(2δ + 4√δ + 2ζ)`-close to the completion of `B` at `a0`. The vendored lemma asks for a
normalized state. -/
theorem closenessAfterCompletion_core_local {Outcome : Type*} [Fintype Outcome]
    (V : VecState K)
    (A : Measurement Outcome (K →L[ℂ] K)) (B : SubMeas Outcome (K →L[ℂ] K))
    (a0 : Outcome) (δ ζ : ℝ) :
    V.SSCRel (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
    V.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B) δ →
    V.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily (completeAtOutcome B a0).toSubMeas)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ) := by
  intro ⟨hζ⟩ ⟨hδ⟩
  rw [constFamily_ssc_unit] at hζ
  rw [constFamily_sdd_unit] at hδ
  have hsqrt := Real.sqrt_le_sqrt hδ
  have hgapA := (abs_le.mp (question_overlap_gap_left V A.toSubMeas B)).2
  have hgapB := (abs_le.mp (question_overlap_gap_right V A.toSubMeas B)).2
  have hdiagA : V.ev A.total - ∑ a, V.ev (A.outcome a * A.outcome a) ≤ ζ :=
    (le_max_right 0 _).trans hζ
  have hdiagB := subMeas_diagMass_le_mass V B
  rw [A.total_eq_one, V.ev_one_of_isNormalized] at hdiagA
  have hresidual : V.ev ((1 - B.total) * (1 - B.total)) ≤ 2 * Real.sqrt δ + ζ :=
    calc V.ev ((1 - B.total) * (1 - B.total))
        ≤ V.ev (1 - B.total) :=
          V.ev_mono _ _ (sq_le_self (sub_nonneg.mpr B.total_le_one)
            (sub_le_self _ B.total_nonneg))
      _ = 1 - V.ev B.total := by rw [V.ev_sub, V.ev_one_of_isNormalized]
      _ ≤ 2 * Real.sqrt δ + ζ := by linarith
  refine ⟨?_⟩
  rw [constFamily_sdd_unit]
  calc V.qSDD A.toSubMeas (completeAtOutcome B a0).toSubMeas
      ≤ 2 * (V.qSDD A.toSubMeas B + V.qSDD B (completeAtOutcome B a0).toSubMeas) :=
        questionSDD_triangle V A.toSubMeas B (completeAtOutcome B a0).toSubMeas
    _ = 2 * (V.qSDD A.toSubMeas B + V.ev ((1 - B.total) * (1 - B.total))) := by
        rw [completion_self_distance V B a0]
    _ ≤ 2 * (δ + (2 * Real.sqrt δ + ζ)) := by gcongr
    _ = 2 * δ + 4 * Real.sqrt δ + 2 * ζ := by ring

/-- Triangle inequality for state-dependent operator distance. -/
theorem sddOpRel_triangle {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ₁ δ₂ : ℝ) :
    V.SDDOpRel 𝒟 A B δ₁ →
    V.SDDOpRel 𝒟 B C δ₂ →
    V.SDDOpRel 𝒟 A C (2 * (δ₁ + δ₂)) :=
  stateDependentDistanceOpRel_triangle V 𝒟 A B C δ₁ δ₂

/-- Monotonicity for `SDDOpRel`. -/
theorem sddOpRel_mono {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome (K →L[ℂ] K)) (δ δ' : ℝ) :
    V.SDDOpRel 𝒟 A B δ → δ ≤ δ' → V.SDDOpRel 𝒟 A B δ' :=
  fun h hle => stateDependentDistanceOpRel_mono V 𝒟 A B δ δ' hle h

/-- Questionwise `n`-step chain bound: the squared distance between the
first and last operator family telescopes and is bounded by
`n * ∑ individual squared distances` via `ev_sum_conjTranspose_mul_sum_le`. -/
theorem questionSDDOp_chain {Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (n : ℕ)
    (families : Fin (n + 1) → OpFamily Outcome (K →L[ℂ] K)) :
    V.qSDDOp (families 0) (families (Fin.last n)) ≤
      (n : ℝ) * ∑ i : Fin n,
        V.qSDDOp (families i.castSucc) (families i.succ) := by
  let D : Fin n → Outcome → K →L[ℂ] K := fun i a =>
    (families i.castSucc).outcome a - (families i.succ).outcome a
  have htelescope : ∀ a,
      (families 0).outcome a - (families (Fin.last n)).outcome a = ∑ i : Fin n, D i a := by
    intro a
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add]
    exact (Fin.sum_univ_succ (fun j => (families j).outcome a)).symm.trans
      (Fin.sum_univ_castSucc (fun j => (families j).outcome a))
  calc V.qSDDOp (families 0) (families (Fin.last n))
      = ∑ a, V.ev (star (∑ i : Fin n, D i a) * (∑ i : Fin n, D i a)) :=
        Finset.sum_congr rfl fun a _ => by rw [htelescope a]
    _ ≤ ∑ a, ((n : ℝ) * ∑ i : Fin n, V.ev (star (D i a) * D i a)) :=
        Finset.sum_le_sum fun a _ => by
          simpa only [Fintype.card_fin] using V.ev_sum_conjTranspose_mul_sum_le (fun i => D i a)
    _ = (n : ℝ) * ∑ i : Fin n, V.qSDDOp (families i.castSucc) (families i.succ) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        rfl

/-- `n`-step `SDDOpRel` chain lemma via vector Cauchy–Schwarz.

Given `n` consecutive `SDDOpRel` bounds, the endpoints satisfy an `SDDOpRel`
bound with error `n * (∑ individual errors)`. This improves on naive
triangle-inequality chaining, which would give exponential blowup.

Paper reference: `prop:triangle-inequality-for-approx_delta`. -/
theorem sddOpRel_chain {Question Outcome : Type*} [Fintype Outcome]
    (V : VecState K) (𝒟 : Distribution Question)
    (n : ℕ)
    (families : Fin (n + 1) → IdxOpFamily Question Outcome (K →L[ℂ] K))
    (errors : Fin n → ℝ)
    (hsteps : ∀ i : Fin n,
      V.SDDOpRel 𝒟 (families i.castSucc) (families i.succ) (errors i)) :
    V.SDDOpRel 𝒟 (families 0) (families (Fin.last n))
      ((n : ℝ) * ∑ i : Fin n, errors i) := by
  refine ⟨?_⟩
  calc V.sddErrorOp 𝒟 (families 0) (families (Fin.last n))
      ≤ avgOver 𝒟 (fun q => (n : ℝ) * ∑ i : Fin n,
          V.qSDDOp (families i.castSucc q) (families i.succ q)) :=
        avgOver_mono 𝒟 _ _ fun q => questionSDDOp_chain V n (fun j => families j q)
    _ = (n : ℝ) * ∑ i : Fin n, V.sddErrorOp 𝒟 (families i.castSucc) (families i.succ) := by
        rw [avgOver_const_mul, avgOver_sum]
        rfl
    _ ≤ (n : ℝ) * ∑ i : Fin n, errors i :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => (hsteps i).squaredDistanceBound)
          (Nat.cast_nonneg n)

end VecState

section Model

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Bipartite wrapper for the completion bound.

Bipartite strong self-consistency of `A` gives local strong self-consistency of its left lift
(`bipartiteSSC_implies_localSSC_liftLeft`); `closenessAfterCompletion_core_local`, applied to the
left-lifted measurement against the vector state of `S`, then bounds the distance to the
completion of the lifted `B`, which has the same outcomes as the lift of the completion of `B`.
The vendored lemma asks for a permutation-invariant, normalized state. -/
theorem closenessAfterCompletion_core {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : Measurement Outcome 𝔓) (B : SubMeas Outcome 𝔓)
    (a0 : Outcome) (δ ζ : ℝ) :
    S.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
    S.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (A.toSubMeas.liftLeft S))
        (constSubMeasFamily (B.liftLeft S)) δ →
    S.SDDRel (uniformDistribution Unit)
      (constSubMeasFamily (A.toSubMeas.liftLeft S))
      (constSubMeasFamily ((completeAtOutcome B a0).toSubMeas.liftLeft S))
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ) := by
  intro hbipartite hsdd
  have hlocal := (closenessAfterCompletion_core_local S.toVecState
    (S.leftLiftedMeasurement A) (B.liftLeft S) a0 δ ζ
    (bipartiteSSC_implies_localSSC_liftLeft S _ _ ζ hbipartite) hsdd).squaredDistanceBound
  rw [constFamily_sdd_unit] at hlocal
  have hout : (completeAtOutcome (B.liftLeft S) a0).outcome =
      ((completeAtOutcome B a0).toSubMeas.liftLeft S).outcome := funext fun a => by
    show _ = S.L _
    by_cases h : a = a0
    · subst h
      simp only [completeAtOutcome, ↓reduceDIte]
      rw [map_add S.L, ← S.leftTensor_sub, S.leftTensor_one]
      rfl
    · simp only [completeAtOutcome, h, ↓reduceDIte]
      rfl
  refine ⟨?_⟩
  rw [constFamily_sdd_unit]
  show S.qSDDCore _ ((completeAtOutcome B a0).toSubMeas.liftLeft S).outcome ≤ _
  rw [← hout]
  exact hlocal

/-- `prop:completing-to-measurement`.

The completion `completeAtOutcome B a0` of `B` is a measurement whose left lift is
`(2δ + 4√δ + 2ζ)`-close to that of `A`. The vendored theorem asks for a permutation-invariant,
normalized state. -/
theorem completingToMeasurement {Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K)
    (A : Measurement Outcome 𝔓) (B : SubMeas Outcome 𝔓)
    (a0 : Outcome) (δ ζ : ℝ) :
    S.BipartiteSSCRel (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
      S.SDDRel (uniformDistribution Unit)
        (constSubMeasFamily (A.toSubMeas.liftLeft S))
        (constSubMeasFamily (B.liftLeft S)) δ →
      ∃ C : Measurement Outcome 𝔓,
        C = completeAtOutcome B a0 ∧ CompletingToMeasStmt S A B C a0 δ ζ :=
  fun hsc hdist => ⟨completeAtOutcome B a0, rfl,
    ⟨closenessAfterCompletion_core S A B a0 δ ζ hsc hdist⟩⟩

end Model

end MIPRE.LIDT.Co.Preliminaries

end
