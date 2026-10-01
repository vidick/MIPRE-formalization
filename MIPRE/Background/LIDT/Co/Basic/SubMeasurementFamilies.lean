/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
SubMeasurementFamilies.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored
file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.Distribution
public import MIPRE.Background.LIDT.Co.Basic.TensorPlacement

@[expose] public section

/-!
# Indexed and bipartite submeasurement infrastructure

Indexed measurement families, tensor placements, and lift/placement constructors: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean` in the
port of `planning/c6b-plan.md` (milestone M0, section "Port conventions").

As in `Co/Basic/SubMeasurementCore.lean`, the families are generic over an ordered `⋆`-ring `R`
(the vendored `Op ι`): local families take `R = 𝔓`, joint ones `R = K →L[ℂ] K`. Each declaration
asks for what its proof uses: `[StarOrderedRing R]` for the positivity of postprocessed and
completed outcomes, a C*-algebra for the projective postprocessing (through the orthogonality
`ProjSubMeas.outcome_orthogonal`), and the real ordered-module structure of
`averageOperatorOverDistribution` for `averageIdxSubMeas`.

The placements take the symmetric model `S` as an argument, in place of the vendored named
carriers `(ιA := ιA)`, `(ιB := ιB)`: a local family is placed on the first or second factor by
`SubMeas.map` along `S.L` or `S.R` (`Co/Basic/SubMeasurementCore.lean`), so
`S.mkLeftPlacedSubMeas A = A.map S.L` and `(A.liftLeft S).outcome a = S.L (A.outcome a)` hold by
`rfl`. The square and the general bipartite placements of the vendored file coincide here, since
the model has one local algebra.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

open MIPStarRE.LDT (Distribution)

/-! ### Indexed measurement families -/

section Indexed

variable (Question Outcome : Type*) (R : Type*) [Fintype Outcome] [Ring R] [StarRing R]
  [PartialOrder R]

/-- Question-indexed family of submeasurements. -/
abbrev IdxSubMeas := Question → SubMeas Outcome R

/-- Question-indexed family of measurements. -/
abbrev IdxMeas := Question → Measurement Outcome R

/-- Question-indexed family of projective submeasurements. -/
abbrev IdxProjSubMeas := Question → ProjSubMeas Outcome R

/-- Question-indexed family of projective measurements. -/
abbrev IdxProjMeas := Question → ProjMeas Outcome R

end Indexed

section IndexedForget

variable {Question Outcome : Type*} {R : Type*} [Fintype Outcome] [Ring R] [StarRing R]
  [PartialOrder R]

/-- Forget completeness from an indexed measurement family. -/
def IdxMeas.toIdxSubMeas (A : IdxMeas Question Outcome R) : IdxSubMeas Question Outcome R :=
  fun q => (A q).toSubMeas

/-- Forget projectivity from an indexed projective submeasurement family. -/
def IdxProjSubMeas.toIdxSubMeas (A : IdxProjSubMeas Question Outcome R) :
    IdxSubMeas Question Outcome R :=
  fun q => (A q).toSubMeas

/-- Forget projectivity from an indexed projective measurement family. -/
def IdxProjMeas.toIdxMeas (A : IdxProjMeas Question Outcome R) : IdxMeas Question Outcome R :=
  fun q => (A q).toMeasurement

/-- Forget both projectivity and completeness from an indexed projective measurement family. -/
def IdxProjMeas.toIdxSubMeas (A : IdxProjMeas Question Outcome R) :
    IdxSubMeas Question Outcome R :=
  fun q => (A q).toSubMeas

end IndexedForget

/-! ### Postprocessing and transport -/

section Postprocess

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- Transport a submeasurement along an equivalence of outcome types. -/
noncomputable def SubMeas.transport {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : SubMeas α R) : SubMeas β R where
  outcome := fun b => A.outcome (e.symm b)
  total := A.total
  outcome_pos := fun b => A.outcome_pos (e.symm b)
  sum_eq_total := (Equiv.sum_comp e.symm A.outcome).trans A.sum_eq_total
  total_le_one := A.total_le_one

@[simp] theorem SubMeas.transport_outcome {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : SubMeas α R) (b : β) :
    (SubMeas.transport e A).outcome b = A.outcome (e.symm b) :=
  rfl

@[simp] theorem SubMeas.transport_total {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : SubMeas α R) :
    (SubMeas.transport e A).total = A.total :=
  rfl

/-- Transport a measurement along an equivalence of outcome types. -/
noncomputable def Measurement.transport {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Measurement α R) : Measurement β R where
  toSubMeas := SubMeas.transport e A.toSubMeas
  total_eq_one := A.total_eq_one

/-- Transport a projective submeasurement along an equivalence of outcome types. -/
noncomputable def ProjSubMeas.transport {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : ProjSubMeas α R) : ProjSubMeas β R where
  toSubMeas := SubMeas.transport e A.toSubMeas
  proj := fun b => A.proj (e.symm b)

/-- Transport a projective measurement along an equivalence of outcome types. -/
noncomputable def ProjMeas.transport {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : ProjMeas α R) : ProjMeas β R where
  toMeasurement := Measurement.transport e A.toMeasurement
  proj := fun b => A.proj (e.symm b)

@[simp] theorem ProjMeas.transport_toSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : ProjMeas α R) :
    (ProjMeas.transport e A).toSubMeas = SubMeas.transport e A.toSubMeas :=
  rfl

/-- Constant indexed family taking the same submeasurement on every question. -/
def constSubMeasFamily {α : Type*} [Fintype α] (A : SubMeas α R) : IdxSubMeas Unit α R :=
  fun _ => A

variable [StarOrderedRing R]

open scoped Classical in
/-- Post-process the outcomes of a submeasurement. The processed operator at `b` is the
sum of the operators of all `a` with `f a = b`. -/
noncomputable def postprocess {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α R) (f : α → β) : SubMeas β R where
  outcome := fun b =>
    ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
  total := A.total
  outcome_pos := fun _ => Finset.sum_nonneg fun a _ => A.outcome_pos a
  sum_eq_total := (Finset.sum_fiberwise Finset.univ f A.outcome).trans A.sum_eq_total
  total_le_one := A.total_le_one

namespace SubMeas

/-- The outcome of a postprocessed submeasurement is the sum over the fiber of
the readout map. -/
@[simp] theorem postprocess_outcome {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : SubMeas α R) (f : α → β) (b : β) :
    (postprocess A f).outcome b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a := by
  classical
  simp only [postprocess]
  exact Finset.sum_congr (by ext a; simp) fun _ _ => rfl

/-- Postprocessing a submeasurement by the identity readout leaves it unchanged. -/
@[simp] theorem postprocess_id {α : Type*} [Fintype α] (A : SubMeas α R) :
    postprocess A (fun a : α => a) = A := by
  classical
  refine SubMeas.ext (fun a => ?_) rfl
  simp only [postprocess, Finset.sum_filter]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _hb hba
    simp [hba]
  · intro ha
    simp at ha

/-- Postprocessing after transporting outcomes along an equivalence agrees with
postprocessing the original submeasurement after precomposing the readout map
with the same equivalence. -/
theorem postprocess_transport {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : α ≃ β) (A : SubMeas α R) (f : β → γ) :
    postprocess (transport e A) f = postprocess A (fun a => f (e a)) := by
  classical
  refine SubMeas.ext (fun c => ?_) rfl
  have hsum :
      (∑ b : β, if f b = c then A.outcome (e.symm b) else (0 : R)) =
        ∑ a : α, if f (e a) = c then A.outcome a else (0 : R) := by
    simpa using
      (Equiv.sum_comp e (fun b => if f b = c then A.outcome (e.symm b) else (0 : R))).symm
  calc
    (postprocess (transport e A) f).outcome c
        = ∑ a : β, if f a = c then A.outcome (e.symm a) else (0 : R) := by
            simp [postprocess, SubMeas.transport, Finset.sum_filter]
    _ = ∑ a : α, if f (e a) = c then A.outcome a else (0 : R) := hsum
    _ = (postprocess A (fun a => f (e a))).outcome c := by
            simp [postprocess, Finset.sum_filter]

/-- Naturality of postprocessing with respect to transport along equivalences on
both the source and target outcome alphabets. -/
theorem postprocess_transport_equiv {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (eα : α ≃ β) (eγ : γ ≃ δ) (A : SubMeas α R)
    (f : α → γ) (g : β → δ)
    (h : ∀ a, g (eα a) = eγ (f a)) :
    postprocess (transport eα A) g = transport eγ (postprocess A f) := by
  classical
  refine SubMeas.ext (fun d => ?_) rfl
  have hsum :
      (∑ b : β, if g b = d then A.outcome (eα.symm b) else 0) =
        ∑ a : α, if g (eα a) = d then A.outcome a else 0 := by
    simpa using
      (Equiv.sum_comp eα (fun b : β => if g b = d then A.outcome (eα.symm b) else 0)).symm
  calc
    (postprocess (transport eα A) g).outcome d
        = ∑ b : β, if g b = d then A.outcome (eα.symm b) else 0 := by
            simp [postprocess, transport, Finset.sum_filter]
    _ = ∑ a : α, if g (eα a) = d then A.outcome a else 0 := hsum
    _ = ∑ a : α, if f a = eγ.symm d then A.outcome a else 0 := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [h a, ← Equiv.eq_symm_apply]
    _ = (transport eγ (postprocess A f)).outcome d := by
            simp [postprocess, transport, Finset.sum_filter]

/-- Postprocessing is functorial: postprocessing by `f` and then by `g`
agrees with a single postprocessing by the composite `g ∘ f`. -/
@[simp] theorem postprocess_comp {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α R) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (fun a => g (f a)) := by
  classical
  refine SubMeas.ext (fun c => ?_) rfl
  simp only [postprocess_outcome]
  rw [← Finset.sum_biUnion]
  · congr 1
    ext a
    simp
  · intro b₁ _ b₂ _ hb
    simp only [Function.onFun]
    exact Finset.disjoint_filter.2 fun a _ h₁ h₂ => hb (h₁.symm.trans h₂)

end SubMeas

/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
noncomputable def completeSubMeas {α : Type*} [Fintype α] (A : SubMeas α R) :
    Measurement (Option α) R where
  toSubMeas := {
    outcome := fun
      | some a => A.outcome a
      | none => 1 - A.total
    total := 1
    outcome_pos := fun
      | some a => A.outcome_pos a
      | none => sub_nonneg.mpr A.total_le_one
    sum_eq_total := (Fintype.sum_option _).trans <|
      (congrArg (1 - A.total + ·) A.sum_eq_total).trans (sub_add_cancel 1 A.total)
    total_le_one := le_rfl
  }
  total_eq_one := rfl

@[simp] theorem ProjMeas.transport_trivialDistinguishedOutcome {α : Type*} [Fintype α]
    (e : α ≃ α) (a₀ : α) :
    ProjMeas.transport e (ProjMeas.trivialDistinguishedOutcome (R := R) a₀) =
      ProjMeas.trivialDistinguishedOutcome (e a₀) := by
  classical
  refine ProjMeas.ext fun a => ?_
  simp only [ProjMeas.transport, Measurement.transport, SubMeas.transport,
    ProjMeas.trivialDistinguishedOutcome, Measurement.trivialDistinguishedOutcome,
    Equiv.symm_apply_eq]

end Postprocess

section ProjectivePostprocess

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
theorem ProjSubMeas.postprocess_outcome_proj {α β : Type*} [Fintype α] [Fintype β]
    (P : ProjSubMeas α R) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  classical
  simp only [SubMeas.postprocess_outcome, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_eq_single a]
  · exact P.proj a
  · exact fun a' _ hne => P.outcome_orthogonal a' a hne
  · exact fun h => (h ha).elim

/-- Postprocess a projective measurement along a relabeling of the outcome type.

The fiber of each output value is a sum of mutually orthogonal projectors, so
postprocessing preserves projectivity as well as completeness. -/
noncomputable def ProjMeas.postprocess {α β : Type*} [Fintype α] [Fintype β]
    (A : ProjMeas α R) (f : α → β) : ProjMeas β R where
  toMeasurement := {
    toSubMeas := MIPRE.LIDT.Co.postprocess A.toSubMeas f
    total_eq_one := A.total_eq_one
  }
  proj := fun b => ProjSubMeas.postprocess_outcome_proj ⟨A.toSubMeas, A.proj⟩ f b

@[simp] theorem ProjMeas.postprocess_toSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : ProjMeas α R) (f : α → β) :
    (ProjMeas.postprocess A f).toSubMeas = MIPRE.LIDT.Co.postprocess A.toSubMeas f :=
  rfl

/-- Postprocessed outcomes from the same ProjMeas commute. -/
theorem ProjMeas.postprocess_outcome_commute {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : ProjMeas α R) (f : α → β) (g : α → γ) (b : β) (c : γ) :
    (MIPRE.LIDT.Co.postprocess P.toSubMeas f).outcome b *
      (MIPRE.LIDT.Co.postprocess P.toSubMeas g).outcome c =
    (MIPRE.LIDT.Co.postprocess P.toSubMeas g).outcome c *
      (MIPRE.LIDT.Co.postprocess P.toSubMeas f).outcome b := by
  classical
  simp only [MIPRE.LIDT.Co.postprocess]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => P.outcome_commute y x

end ProjectivePostprocess

/-! ### Averages of indexed families -/

/-- Average an indexed submeasurement family against a finite distribution.

The hypothesis `∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1` says that `𝒟` is a sub-probability
distribution (total mass at most `1`); this is all that is needed to keep the
averaged total operator below `1`. -/
noncomputable def averageIdxSubMeas {Question Outcome : Type*} [Fintype Outcome]
    {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [Module ℝ R] [IsOrderedAddMonoid R]
    [PosSMulMono ℝ R] [SMulPosMono ℝ R] [ZeroLEOneClass R]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome R)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    SubMeas Outcome R where
  outcome := fun a =>
    averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
  total :=
    averageOperatorOverDistribution 𝒟 (fun q => (A q).total)
  outcome_pos := fun a =>
    averageOperatorOverDistribution_nonneg 𝒟
      (fun q => (A q).outcome a) (fun q => (A q).outcome_pos a)
  sum_eq_total :=
    (averageOperatorOverDistribution_sum 𝒟 (fun q a => (A q).outcome a)).symm.trans
      (averageOperatorOverDistribution_congr 𝒟 _ _ fun q => (A q).sum_eq_total)
  total_le_one :=
    averageOperatorOverDistribution_le_one_of_weight_sum_le_one 𝒟
      (fun q => (A q).total) h𝒟 (fun q => (A q).total_le_one)

/-! ### Tensor-placement constructors -/

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-- Place a submeasurement on the first factor: each outcome `A_a` becomes `S.L A_a` (the
vendored `A_a ⊗ 1`). -/
noncomputable def mkLeftPlacedSubMeas {α : Type*} [Fintype α] (A : SubMeas α 𝔓) : SubMeas α (K →L[ℂ] K) :=
  A.map S.L

/-- Place a submeasurement on the second factor: each outcome `A_a` becomes `S.R A_a` (the
vendored `1 ⊗ A_a`). -/
noncomputable def mkRightPlacedSubMeas {α : Type*} [Fintype α] (A : SubMeas α 𝔓) : SubMeas α (K →L[ℂ] K) :=
  A.map S.R

/-- Helper-level projection equation for left-placed outcomes. -/
@[simp] theorem mkLeftPlacedSubMeas_outcome {α : Type*} [Fintype α] (A : SubMeas α 𝔓) (a : α) :
    (S.mkLeftPlacedSubMeas A).outcome a = S.L (A.outcome a) :=
  rfl

/-- Helper-level projection equation for left-placed totals. -/
@[simp] theorem mkLeftPlacedSubMeas_total {α : Type*} [Fintype α] (A : SubMeas α 𝔓) :
    (S.mkLeftPlacedSubMeas A).total = S.L A.total :=
  rfl

/-- Helper-level projection equation for right-placed outcomes. -/
@[simp] theorem mkRightPlacedSubMeas_outcome {α : Type*} [Fintype α] (A : SubMeas α 𝔓)
    (a : α) :
    (S.mkRightPlacedSubMeas A).outcome a = S.R (A.outcome a) :=
  rfl

/-- Helper-level projection equation for right-placed totals. -/
@[simp] theorem mkRightPlacedSubMeas_total {α : Type*} [Fintype α] (A : SubMeas α 𝔓) :
    (S.mkRightPlacedSubMeas A).total = S.R A.total :=
  rfl

end SymModel

/-! ### Square bipartite lifts -/

section Lifts

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Lift a submeasurement to the first factor. Each outcome operator `A_a : 𝔓` becomes
`S.L A_a` (the vendored `A_a ⊗ I`). -/
noncomputable def SubMeas.liftLeft {α : Type*} [Fintype α] (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) :
    SubMeas α (K →L[ℂ] K) :=
  S.mkLeftPlacedSubMeas A

/-- Lift an indexed submeasurement family to the first factor. -/
noncomputable def IdxSubMeas.liftLeft {Question Outcome : Type*} [Fintype Outcome] (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓) : IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => S.mkLeftPlacedSubMeas (A q)

/-- Lift a projective submeasurement to the first factor. -/
noncomputable def ProjSubMeas.liftLeft {α : Type*} [Fintype α] (S : SymModel 𝔓 K) (A : ProjSubMeas α 𝔓) :
    ProjSubMeas α (K →L[ℂ] K) :=
  { toSubMeas := A.toSubMeas.liftLeft S
    proj := (A.map S.L).proj }

/-- Lift a submeasurement to the second factor. Each outcome operator `A_a : 𝔓` becomes
`S.R A_a` (the vendored `I ⊗ A_a`). -/
noncomputable def SubMeas.liftRight {α : Type*} [Fintype α] (S : SymModel 𝔓 K) (A : SubMeas α 𝔓) :
    SubMeas α (K →L[ℂ] K) :=
  S.mkRightPlacedSubMeas A

/-- Lift an indexed submeasurement family to the second factor. -/
noncomputable def IdxSubMeas.liftRight {Question Outcome : Type*} [Fintype Outcome] (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓) : IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => S.mkRightPlacedSubMeas (A q)

end Lifts

/-! ### General bipartite placement -/

namespace SymModel

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (S : SymModel 𝔓 K)

/-- Place a submeasurement on the first factor. -/
noncomputable def leftPlacedSubMeas {α : Type*} [Fintype α] (A : SubMeas α 𝔓) : SubMeas α (K →L[ℂ] K) :=
  S.mkLeftPlacedSubMeas A

/-- Outcome operators of a left-placed submeasurement are left placements. -/
@[simp] theorem leftPlacedSubMeas_outcome {α : Type*} [Fintype α] (A : SubMeas α 𝔓) (a : α) :
    (S.leftPlacedSubMeas A).outcome a = S.L (A.outcome a) :=
  rfl

/-- The total operator of a left-placed submeasurement is a left placement. -/
@[simp] theorem leftPlacedSubMeas_total {α : Type*} [Fintype α] (A : SubMeas α 𝔓) :
    (S.leftPlacedSubMeas A).total = S.L A.total :=
  rfl

/-- Place a submeasurement on the second factor. -/
noncomputable def rightPlacedSubMeas {α : Type*} [Fintype α] (A : SubMeas α 𝔓) : SubMeas α (K →L[ℂ] K) :=
  S.mkRightPlacedSubMeas A

/-- Outcome operators of a right-placed submeasurement are right placements. -/
@[simp] theorem rightPlacedSubMeas_outcome {α : Type*} [Fintype α] (A : SubMeas α 𝔓) (a : α) :
    (S.rightPlacedSubMeas A).outcome a = S.R (A.outcome a) :=
  rfl

/-- The total operator of a right-placed submeasurement is a right placement. -/
@[simp] theorem rightPlacedSubMeas_total {α : Type*} [Fintype α] (A : SubMeas α 𝔓) :
    (S.rightPlacedSubMeas A).total = S.R A.total :=
  rfl

end SymModel

section Placements

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Lift an indexed submeasurement family to the first factor (general bipartite placement). -/
noncomputable def IdxSubMeas.placeLeft {Question Outcome : Type*} [Fintype Outcome] (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓) : IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => S.mkLeftPlacedSubMeas (A q)

/-- Lift an indexed submeasurement family to the second factor (general bipartite
placement). -/
noncomputable def IdxSubMeas.placeRight {Question Outcome : Type*} [Fintype Outcome] (S : SymModel 𝔓 K)
    (A : IdxSubMeas Question Outcome 𝔓) : IdxSubMeas Question Outcome (K →L[ℂ] K) :=
  fun q => S.mkRightPlacedSubMeas (A q)

end Placements

end MIPRE.LIDT.Co

end
