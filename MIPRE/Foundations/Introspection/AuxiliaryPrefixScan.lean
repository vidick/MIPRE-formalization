/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryPrefixSolve

/-! # The Gaussian scan invariant for source sampler queries

Every successful stage carries a genuine seed witnessing the claimed prefix.
Failed linear solves reject. Honest outputs pass every stage. The scan uses
one polynomial-time matrix solve per stage, with no enumeration of seeds.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryPrefix
open Finset CLChecks
variable {n ℓ : ℕ}

def scan (P : CL.CLFun CL.𝔽₂ (Fin n) ℓ) (y : Fin n → CL.𝔽₂) :
    ℕ → Option (Fin n → CL.𝔽₂)
  | 0 => some 0
  | k + 1 => (scan P y k).bind fun x =>
      let u := P.outputPrefix k y
      let L := P.mapOfPrefix k u
      let v := CL.proj (P.factorOfPrefix k y) y
      let z := solveStage L v
      if L z = v then some (replaceSeed P k u x z) else none

theorem scan_sound {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) (y : Fin n → CL.𝔽₂) (k : ℕ) (x : Fin n → CL.𝔽₂)
    (hx : scan P y k = some x) : (P.truncate k).eval x = P.outputPrefix k y := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    simp only [scan, Option.bind_eq_some_iff] at hx
    obtain ⟨x', hx', hx⟩ := hx
    split_ifs at hx with hz
    · cases Option.some.inj hx
      exact extend_claimed hP k y x' _ (ih x' hx') hz

theorem stage_of_honest {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) (k : ℕ) (x : Fin n → CL.𝔽₂) :
    P.mapOfPrefix k (P.outputPrefix k (P.eval x)) x =
      CL.proj (P.factorOfPrefix k (P.eval x)) (P.eval x) := by
  have h := truncate_eval_step hP k x
  rw [← CL.RegLinear.toLinearMap_apply, stageLinear_toLinearMap] at h
  rw [← hP.outputPrefix_eval (k + 1) x, ← hP.outputPrefix_eval k x,
    outputPrefix_step hP] at h
  exact (add_left_cancel h).symm

/-- Honest answers never fail the consistency guard of any matrix solve. -/
theorem scan_honest {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) (x : Fin n → CL.𝔽₂) (k : ℕ) :
    ∃ z, scan P (P.eval x) k = some z := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨z, hz⟩ := ih
    have hs := solveStage_correct (P.mapOfPrefix k (P.outputPrefix k (P.eval x)))
      (CL.proj (P.factorOfPrefix k (P.eval x)) (P.eval x))
      ⟨x, stage_of_honest hP k x⟩
    simp only [scan, hz, Option.bind_some, hs, if_true]
    exact ⟨_, rfl⟩

/-- This is precisely the source interface's legal-prefix premise. -/
theorem scan_legal_query {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) (y : Fin n → CL.𝔽₂) (k : ℕ) (x : Fin n → CL.𝔽₂)
    (hx : scan P y k = some x) :
    ∃ z, CL.toBits (P.outputPrefix k y) = CL.toBits ((P.truncate k).eval z) :=
  ⟨x, congrArg CL.toBits (scan_sound hP y k x hx).symm⟩

end MIPRE.Introspection.AuxiliaryPrefix
end
