/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveAnswerDecode
public import MIPRE.Foundations.Introspection.AdaptiveNextStrategy
public import MIPRE.Foundations.Introspection.IntrospectCanonicalization

@[expose] public section

/-! # The decoded next-prefix invariant

The actual next residual measurement reports a full option-valued answer.
Its decoder overwrites the visited coordinates and retains the remaining
tail. Attainable prefixes give the required valid-answer support, while
unattainable prefixes use the constant malformed residual measurement.
The selected raw replacement has exactly this decoded product form.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the decoded next residual
PVMs are measurements of block matrices over the remaining coordinates of the next prefix whose
entries are block matrices over the ancilla `T` with entries in any algebra `𝒜`, and the selected
full-answer measurement is the registered replacement, a POVM in
`Matrix (ι → F) (ι → F) (Matrix T T 𝒜)`, the first player's algebra of the register model
`(Ξ.expandA t₀).reg (ι → F)` of the returned strategy. The decoder is unchanged. At an
unattainable prefix the malformed residual is the register readout of the constant answer
`none`, entering as `smulKron 1 _`, so its valid-answer operators vanish; projectivity is
`IsPVMIn`, and the product-form identity (`registeredReplacement_nextOption_mats`) is an identity
of operators `.op`.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {ι F A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Decode a retained answer using only its new prefix and its unvisited tail. -/
def nextOptionDecoder (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ((ι → F) × Option ((ι → F) × A)) → Option ((ι → F) × A) :=
  fun p => p.2.map (fun a =>
    (p.1 + CL.proj (stageRemaining P (k + 1) p.1) a.1, a.2))

theorem nextOptionDecoder_none (P : CL.CLFun F ι ℓ) (k : ℕ) (v : ι → F) :
    nextOptionDecoder (A := A) P k (v, none) = none := rfl

theorem stageAnswerDecode_nextOptionDecoder {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F)
    (z : Fin (Fintype.card (P.factorOfPrefix k y)) → F)
    (a : Option ((ι → F) × A)) :
    stageAnswerDecode P k y z a = nextOptionDecoder P k (advancePrefix P k y z, a) :=
  stageAnswerDecode_next hP k y z a

theorem nextOptionDecoder_advanceStageAnswer {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ)
    (p : AdaptiveStageAnswer P k (Option ((ι → F) × A))) :
    nextOptionDecoder P k (advanceStageAnswer P k p) =
      stageAnswerDecode P k p.1 p.2.1 p.2.2 :=
  (stageAnswerDecode_nextOptionDecoder hP k p.1 p.2.1 p.2.2).symm

/-- Decoded coordinates have the claimed next prefix on every attainable
branch. No corresponding assertion is made for arbitrary invalid prefixes. -/
theorem nextOptionDecoder_prefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (v : ι → F)
    (hv : v ∈ prefixOutcomes P (k + 1)) (x : ι → F) :
    P.outputPrefix (k + 1) (v + CL.proj (stageRemaining P (k + 1) v) x) = v := by
  calc
    _ = P.outputPrefix (k + 1) v := by
      apply CLChecks.outputPrefix_eq_of_agree
      intro i hi
      simp [stageRemaining, CL.proj_apply, hi]
    _ = v := outputPrefix_of_mem_prefixOutcomes hP (k + 1) v hv

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [StarProper 𝒜]
variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The full option-valued next residual measurement is projective. -/
theorem nextPrefixDecodedPOVM_option_isPVM (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k 𝒜 T (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVMIn (D y z)) (v : ι → F) :
    IsPVMIn (nextPrefixDecodedPOVM P hP k none D hD (nextOptionDecoder P k) v).op :=
  nextPrefixDecodedPOVM_isPVM P hP k none D hD (nextOptionDecoder P k) v

/-- Every valid decoded answer has the correct next prefix, for every
branch. Off-image branches use the constant `none` residual, rather than a
coordinate claim about an unattainable prefix. -/
theorem nextPrefixDecodedPOVM_some_support (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k 𝒜 T (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVMIn (D y z)) (v x : ι → F) (a : A)
    (hx : P.outputPrefix (k + 1) x ≠ v) :
    (nextPrefixDecodedPOVM P hP k none D hD (nextOptionDecoder P k) v).op (some (x, a)) = 0 := by
  unfold nextPrefixDecodedPOVM
  rw [POVMIn.map_op]
  apply Finset.sum_eq_zero
  intro b hb
  have he : nextOptionDecoder P k (v, b) = some (x, a) := (mem_filter.mp hb).2
  cases b with
  | none => simp only [nextOptionDecoder_none, reduceCtorEq] at he
  | some b =>
    by_cases hv : v ∈ prefixOutcomes P (k + 1)
    · have hxv : v + CL.proj (stageRemaining P (k + 1) v) b.1 = x :=
        congrArg Prod.fst (Option.some.inj he)
      have hp := nextOptionDecoder_prefix hP k v hv b.1
      rw [hxv] at hp
      exact False.elim (hx hp)
    · change nextPrefixResidual P hP k none D v (some b) = 0
      rw [nextPrefixResidual, dite_eq_right hv]
      ext i j
      simp [readout, smulKron_apply]

variable {X PauliAnswer : Type*} [Fintype X] [DecidableEq X] [Fintype PauliAnswer]

/-- Projecting the actual raw selected replacement recovers exactly the
canonical option-valued next joint measurement. -/
theorem registeredReplacement_nextOption_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k 𝒜 T (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVMIn (D y z))
    (MA : X → POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (q : X) :
    (registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p)))) q).map
        TypedEstimates.introspectPair =
      (nextPrefixJointPOVM P hP k none D hD).map (nextOptionDecoder P k) := by
  rw [registeredReplacement_next_at P hP k none D hD MA q
    (fun p => restoreIntroAnswer (nextOptionDecoder P k p)), POVMIn.map_map]
  simp only [introspectPair_restoreIntroAnswer]

/-- The actual selected full-answer measurement satisfies the next
product-form invariant with the concrete decoded residual PVMs. -/
theorem registeredReplacement_nextOption_mats (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k 𝒜 T (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVMIn (D y z))
    (MA : X → POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (q : X) (a : Option ((ι → F) × A)) :
    ((registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p)))) q).map
        TypedEstimates.introspectPair).op a =
      ∑ v, prefixResidualOp P (k + 1) v
        ((nextPrefixDecodedPOVM P hP k none D hD (nextOptionDecoder P k) v).op a) := by
  rw [registeredReplacement_nextOption_at P hP k D hD MA q]
  exact nextPrefixJointPOVM_map_mats P hP k none D hD (nextOptionDecoder P k) a

end MIPRE.Introspection
end

end
