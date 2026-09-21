/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AdaptiveAnswerDecode
import MIPRE.Foundations.Introspection.AdaptiveNextStrategy
import MIPRE.Foundations.Introspection.IntrospectCanonicalization

/-! # The decoded next-prefix invariant

The actual next residual measurement reports a full option-valued answer.
Its decoder overwrites the visited coordinates and retains the remaining
tail. Attainable prefixes give the required valid-answer support, while
unattainable prefixes use the constant malformed residual measurement.
The selected raw replacement has exactly this decoded product form.
-/

noncomputable section
namespace MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false

variable {ι F H A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] {ℓ : ℕ}

/-- Decode a retained answer using only its new prefix and its unvisited tail. -/
def nextOptionDecoder (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ((ι → F) × Option ((ι → F) × A)) → Option ((ι → F) × A) :=
  fun p => p.2.map (fun a =>
    (p.1 + CL.proj (stageRemaining P (k + 1) p.1) a.1, a.2))

theorem nextOptionDecoder_none (P : CL.CLFun F ι ℓ) (k : ℕ) (v : ι → F) :
    nextOptionDecoder (A := A) P k (v, none) = none := rfl

theorem nextOptionDecoder_some (P : CL.CLFun F ι ℓ) (k : ℕ)
    (v x : ι → F) (a : A) :
    nextOptionDecoder P k (v, some (x, a)) =
      some (v + CL.proj (stageRemaining P (k + 1) v) x, a) := rfl

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

/-- The full option-valued next residual measurement is projective. -/
theorem nextPrefixDecodedPOVM_option_isPVM (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVM (D y z)) (v : ι → F) :
    IsPVM (fun a =>
      ((nextPrefixDecodedPOVM P hP k none D hD (nextOptionDecoder P k) v).mats a).val) :=
  nextPrefixDecodedPOVM_isPVM P hP k none D hD (nextOptionDecoder P k) v

/-- Every valid decoded answer has the correct next prefix, for every
branch. Off-image branches use the constant `none` residual, rather than a
coordinate claim about an unattainable prefix. -/
theorem nextPrefixDecodedPOVM_some_support (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVM (D y z)) (v x : ι → F) (a : A)
    (hx : P.outputPrefix (k + 1) x ≠ v) :
    ((nextPrefixDecodedPOVM P hP k none D hD (nextOptionDecoder P k) v).mats
      (some (x, a))).val = 0 := by
  unfold nextPrefixDecodedPOVM
  rw [POVM.map_mats]
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
      rw [nextPrefixResidual, dif_neg hv]
      ext i j
      simp [readout]

variable {X PauliAnswer : Type*} [Fintype X] [DecidableEq X] [Fintype PauliAnswer]

/-- Projecting the actual raw selected replacement recovers exactly the
canonical option-valued next joint measurement. -/
theorem registeredReplacement_nextOption_at (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (q : X) :
    (registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p)))) q).map
        TypedEstimates.introspectPair =
      (nextPrefixJointPOVM P hP k none D hD).map (nextOptionDecoder P k) := by
  rw [registeredReplacement_next_at P hP k none D hD MA q
    (fun p => restoreIntroAnswer (nextOptionDecoder P k p)), POVM.map_map]
  simp only [introspectPair_restoreIntroAnswer]

/-- The actual selected full-answer measurement satisfies the next
product-form invariant with the concrete decoded residual PVMs. -/
theorem registeredReplacement_nextOption_mats (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (q : X)
    (a : Option ((ι → F) × A)) :
    (((registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
      (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p)))) q).map
        TypedEstimates.introspectPair).mats a).val =
      ∑ v, prefixResidualOp P (k + 1) v
        ((nextPrefixDecodedPOVM P hP k none D hD (nextOptionDecoder P k) v).mats a).val := by
  rw [registeredReplacement_nextOption_at P hP k D hD MA q]
  exact nextPrefixJointPOVM_map_mats P hP k none D hD (nextOptionDecoder P k) a

theorem registeredReplacement_nextOption_isPVM (P : CL.CLFun F ι ℓ)
    (hP : P.SupportedOn univ) (k : ℕ)
    (D : AdaptiveDilationFamily P k H (Option ((ι → F) × A)))
    (hD : ∀ y z, IsPVM (D y z))
    (MA : X → POVM (ParsedAnswer (ι → F) A PauliAnswer) ((ι → F) × H)) (q : X) :
    IsPVM (fun a =>
      (((registeredReplacement MA q ((adaptiveReplacementPOVM P hP k D hD).map
        (fun p => restoreIntroAnswer (nextOptionDecoder P k (advanceStageAnswer P k p)))) q).map
          TypedEstimates.introspectPair).mats a).val) := by
  rw [registeredReplacement_nextOption_at P hP k D hD MA q]
  exact isPVM_povm_map _ (nextPrefixJoint_isPVM P hP k none D hD) (nextOptionDecoder P k)

end MIPRE.Introspection
end
