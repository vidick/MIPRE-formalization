/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryScanProgram
import MIPRE.Foundations.Introspection.AuxiliaryPrefixScan

/-! # Correctness of the actual attained-prefix scan

The only query hypotheses are the source interface's legal-prefix clauses.
The returned witness proves the next call is legal. Honest outputs pass all
stages, while arbitrary malformed or unattainable claims may be rejected.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryScan
open Cost LowDegree.BinaryLinear CLChecks
variable {n ℓ : ℕ}

theorem earlier_attained {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) {j k : ℕ} (hj : j ≤ k) (y x : Fin n → CL.𝔽₂)
    (hx : (P.truncate k).eval x = P.outputPrefix k y) :
    (P.truncate j).eval x = P.outputPrefix j y := by
  have he : P.outputPrefix k (P.eval x) = P.outputPrefix k y :=
    (hP.outputPrefix_eval k x).trans hx
  have h := congrArg (P.outputPrefix j) he
  rw [outputPrefix_outputPrefix hP _ hj, outputPrefix_outputPrefix hP _ hj,
    hP.outputPrefix_eval] at h
  exact h

theorem stage_of_attained_next {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) (k : ℕ) (y x : Fin n → CL.𝔽₂)
    (hx : (P.truncate (k + 1)).eval x = P.outputPrefix (k + 1) y) :
    P.mapOfPrefix k (P.outputPrefix k y) x = CL.proj (P.factorOfPrefix k y) y := by
  have hp := earlier_attained hP (Nat.le_succ k) y x hx
  have hs := truncate_eval_step hP k x
  rw [hx, hp, ← CL.RegLinear.toLinearMap_apply, stageLinear_toLinearMap,
    AuxiliaryPrefix.outputPrefix_step hP] at hs
  exact (add_left_cancel hs).symm

def QueriesCorrectAt (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    (P : CL.CLFun CL.𝔽₂ (Fin n) ℓ) (k : ℕ) : Prop :=
  ∀ u : Fin n → CL.𝔽₂, (∃ x, (P.truncate k).eval x = u) →
    f (contextAt ctx (k + 1) (CL.toBits u)) = CL.indicatorBits (P.factorOfPrefix k u) ∧
    m (contextAt ctx (k + 1) (CL.toBits u)) = matrixBits (LinearMap.toMatrix' (P.mapOfPrefix k u))

theorem stage_at_claimed (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (k : ℕ) (y x : Fin n → CL.𝔽₂) (hx : (P.truncate k).eval x = P.outputPrefix k y)
    (hq : QueriesCorrectAt f m ctx P k) :
    stage f m (contextAt ctx (k + 1) (CL.toBits (P.outputPrefix k y)), CL.toBits y, CL.toBits x) =
      let v := CL.proj (P.factorOfPrefix k y) y
      let L := P.mapOfPrefix k (P.outputPrefix k y)
      let z := AuxiliaryPrefix.solveStage L v
      (decide (L z = v), CL.toBits (P.outputPrefix (k + 1) y),
        CL.toBits (AuxiliaryPrefix.replaceSeed P k (P.outputPrefix k y) x z)) := by
  obtain ⟨hf, hm⟩ := hq _ ⟨x, hx⟩
  rw [factorOfPrefix_outputPrefix hP] at hf
  rw [stage_correct f m _ _ _ _ _ _ rfl hf hm]
  dsimp only
  rw [AuxiliaryPrefix.outputPrefix_step hP, AuxiliaryPrefix.replaceSeed,
    factorOfPrefix_outputPrefix hP]

/-- A successful scan gives both the claimed prefix and a seed witnessing it. -/
theorem program_sound (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (y : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j < k, QueriesCorrectAt f m ctx P j)
    (hok : (program f m k (ctx, CL.toBits y)).1 = true) :
    ∃ x, program f m k (ctx, CL.toBits y) =
      (true, CL.toBits (P.outputPrefix k y), CL.toBits x) ∧
      (P.truncate k).eval x = P.outputPrefix k y := by
  induction k with
  | zero =>
    refine ⟨0, ?_, by simp⟩
    rw [program_zero, zeros_toBits]
    simp
  | succ k ih =>
    have hp : (program f m k (ctx, CL.toBits y)).1 = true := by
      by_contra hn
      have hb : (program f m k (ctx, CL.toBits y)).1 = false := Bool.eq_false_iff.mpr hn
      rw [program_succ] at hok
      generalize hs : program f m k (ctx, CL.toBits y) = s at *
      rcases s with ⟨b, u, x⟩
      simp only at hb
      rw [advance_apply, hb] at hok
      contradiction
    obtain ⟨x, he, hx⟩ := ih (fun j hj => hq j (by omega)) hp
    have hs := stage_at_claimed f m ctx hP k y x hx (hq k (by omega))
    have hp' : program f m (k + 1) (ctx, CL.toBits y) =
        stage f m (contextAt ctx (k + 1) (CL.toBits (P.outputPrefix k y)),
          CL.toBits y, CL.toBits x) := by
      rw [program_succ, he, advance_apply]
      rfl
    have hr := hp'.trans hs
    rw [hr] at hok
    dsimp only at hok
    have hz := of_decide_eq_true hok
    refine ⟨AuxiliaryPrefix.replaceSeed P k (P.outputPrefix k y) x
      (AuxiliaryPrefix.solveStage (P.mapOfPrefix k (P.outputPrefix k y))
        (CL.proj (P.factorOfPrefix k y) y)), ?_, ?_⟩
    · rw [hr]
      simp only [hz, decide_true]
    · exact AuxiliaryPrefix.extend_claimed hP k y x _ hx hz

/-- Every honest full output passes the actual executable scan. -/
theorem program_honest (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (x : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j < k, QueriesCorrectAt f m ctx P j) :
    (program f m k (ctx, CL.toBits (P.eval x))).1 = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := ih (fun j hj => hq j (by omega))
    obtain ⟨z, he, hz⟩ := program_sound f m ctx hP (P.eval x) k
      (fun j hj => hq j (by omega)) hp
    have hs := stage_at_claimed f m ctx hP k (P.eval x) z hz (hq k (by omega))
    rw [program_succ, he, advance_apply]
    simp only [if_true]
    rw [hs]
    dsimp only
    apply decide_eq_true
    exact AuxiliaryPrefix.solveStage_correct _ _ ⟨x, AuxiliaryPrefix.stage_of_honest hP k x⟩

/-- Hiding answers only need the prefix requested at their own level to be
attainable; the unvisited components are unrestricted. -/
theorem program_complete (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (y : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j < k, QueriesCorrectAt f m ctx P j)
    (ha : ∃ x, (P.truncate k).eval x = P.outputPrefix k y) :
    (program f m k (ctx, CL.toBits y)).1 = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x, hx⟩ := ha
    have hp := ih (fun j hj => hq j (by omega))
      ⟨x, earlier_attained hP (Nat.le_succ k) y x hx⟩
    obtain ⟨z, he, hz⟩ := program_sound f m ctx hP y k
      (fun j hj => hq j (by omega)) hp
    have hs := stage_at_claimed f m ctx hP k y z hz (hq k (by omega))
    rw [program_succ, he, advance_apply]
    simp only [if_true]
    rw [hs]
    dsimp only
    apply decide_eq_true
    exact AuxiliaryPrefix.solveStage_correct _ _ ⟨x, stage_of_attained_next hP k y x hx⟩

end MIPRE.Introspection.AuxiliaryScan
end
