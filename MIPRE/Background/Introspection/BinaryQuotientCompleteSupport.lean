/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.BinaryQuotientComplete

/-! # Format support of the honest explicit Pauli measurements -/

noncomputable section
namespace MIPRE.Introspection.BinaryComplete
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (hL : ∀ w, (L w).SupportedOn univ)

theorem strategy_nonzero_pauli_format (side : Bool) (p : QLD.Ty)
    (payload : Fin ((3*m+3)*t) → ZMod 2) (a : QLD.Answer F m d)
    (ha : (strategy L D R hm b hL).P.M (side,.inl p,payload) (.pauli a) ≠ 0) :
    (QLD.PauliCL.binaryQuestion b p payload).fmtOk a = true := by
  by_contra hn
  have hf : (QLD.PauliCL.binaryQuestion b p payload).fmtOk a = false :=
    Bool.eq_false_iff.mpr hn
  apply ha
  change registerOp _ (pauliLift b L D R
    (QLD.Honest.answerOp hm (QLD.PauliCL.binaryQuestion b p payload) a)) = 0
  rw [QLD.Honest.answerOp_format_zero hm _ _ hf, pauliLift_zero]
  rfl

theorem quotientHonest_pauli_format (χ : F → Fin m) (π : F ≃ F)
    (side : Bool) (p : QLD.Ty) (payload : Fin ((3*m+3)*t) → ZMod 2)
    (a : QLD.Answer F m d)
    (ha : (quotientHonest L D R hm b hL χ π).P.M (side,.inl p,payload) (.pauli a) ≠ 0) :
    (QLD.PauliCL.ExplicitSeed.binaryDecode π b p payload).fmtOk a = true := by
  have h := strategy_nonzero_pauli_format L D R hm b hL side p
    (QLD.PauliCL.ExplicitSeed.binaryOutputPermutation π b p payload) a ha
  rwa [QLD.PauliCL.ExplicitSeed.binaryQuestion_outputPermutation] at h

end MIPRE.Introspection.BinaryComplete
end
