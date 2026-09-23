/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelSoundness
import MIPRE.Background.Introspection.NumberedComplete

/-! # Identification of the kernel's finite semantics with the explicit game -/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost SAT
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem finitePauliCheck_toBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (x y : Fin ((3 * 2 ^ j + 3) * k) → CL.𝔽₂) (T U : QLD.Ty) :
    finitePauliCheck k hk hodd j hm (CL.toBits x) (CL.toBits y) T U =
      ExplicitGame.pauliCheck (d := 1) hm
        (QLD.PauliCL.ExplicitSeed.seedPermutation (shoupBinField k hk))
        (shoupSelfDualNormalBasis k hk hodd) T U x y := by
  simp only [finitePauliCheck, QLD.PauliBinaryProgram.questionOfBits, CL.ofBits_toBits]
  rfl

theorem pauliProject_eq_numbered {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} (basis : Module.Basis (Fin k) (ZMod 2) F)
    (a : QLD.Answer F m 1) :
    Answer.pauliProject basis a = fun i => BinaryComplete.project basis a
      ((QLD.PauliFullAnswerProgram.registerNumbering m k).symm i) := by
  cases a <;> rfl

/-- Raw kernel acceptance gives the exact finite game used by the source
soundness theorem, including the executable full-register numbering. -/
theorem program_sound_numbered (W : ClockedUniversalMachine) {lam n : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (hs : V.sampler.dim (2 ^ n) ≤ 2 ^ (2 ^ j) * k)
    (hQ : 4 ≤ 2 ^ (2 ^ j) * k) (hR : 3 * ((2 ^ n)^lam) ≤ 2 ^ (2 ^ j) * k)
    (χ : (shoupBinField k hk).carrier → Fin (2 ^ j))
    (T U : Label) (x y : Fin ((3 * 2 ^ j + 3) * k) → CL.𝔽₂) (a b : BitStr)
    (h : program W (canonicalInput V lam n (2 ^ (2 ^ j) * k) ((2 ^ n)^lam)
      (unary k,unary j,unary (2 ^ j)) T U (CL.toBits x) (CL.toBits y) a b) = true) :
    (NumberedComplete.game (d := 1)
      (QLD.PauliFullAnswerProgram.registerNumbering (2 ^ j) k).symm
      (AuxiliaryDecision.padded V hs) (finiteSourcePredicate (R := (2 ^ n)^lam) V hs)
      hm (shoupSelfDualNormalBasis k hk hodd) χ
      (QLD.PauliCL.ExplicitSeed.seedPermutation (shoupBinField k hk))).D (T,x) (U,y)
      (Answer.decode (shoupBinField k hk) (2 ^ j) (2 ^ (2 ^ j) * k) ((2 ^ n)^lam) T a)
      (Answer.decode (shoupBinField k hk) (2 ^ j) (2 ^ (2 ^ j) * k) ((2 ^ n)^lam) U b) = true := by
  have hh := program_sound W V hV hn k hk hodd j hj hm hs hQ hR T U
    (CL.toBits x) (CL.toBits y) a b h
  have hp : Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd) =
      NumberedComplete.project (d := 1)
        (QLD.PauliFullAnswerProgram.registerNumbering (2 ^ j) k).symm
        (shoupSelfDualNormalBasis k hk hodd) := by
    funext a
    exact pauliProject_eq_numbered _ a
  have hDP : finitePauliCheck k hk hodd j hm (CL.toBits x) (CL.toBits y) =
      fun T U => ExplicitGame.pauliCheck (d := 1) hm
        (QLD.PauliCL.ExplicitSeed.seedPermutation (shoupBinField k hk))
        (shoupSelfDualNormalBasis k hk hodd) T U x y := by
    funext T U
    exact finitePauliCheck_toBits k hk hodd j hm x y T U
  rw [hp,hDP] at hh
  exact hh

end MIPRE.Introspection.DecisionKernel
end
