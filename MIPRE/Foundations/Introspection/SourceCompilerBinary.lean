/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourceCompiler

/-! # Binary-uniform compilation of the cross-Introspect component -/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program ClockSimulation

def parameterStageCompiler (c : ℕ) : PolyTimeFun ℕ Prog :=
  (codeRoute ClockProgram.clockRoute treePair).comp
    ((smn ℕ).comp ((const (boundsProg c)).pair (PolyTimeFun.id ℕ)))

def dimensionStageCompiler (k : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun (Prog × ℕ) Prog :=
  (codeRoute dimensionRoute treePair).comp (ap₂ codeLet ((clockStageCompiler k).comp snd)
    (ap₂ codeLet (reindexStageCompiler.comp fst) (const U.univT)))

def finalStageCompiler (k : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun (Prog × ℕ) Prog :=
  (codeRoute finalRoute snd).comp ((codeRoute projectedRoute snd).comp (ClockSimulation.compiler k U))

/-- One fixed ambient compiler reads both source descriptions and binary lambda. -/
def crossCompiler (c k : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun (Prog × Prog × ℕ) Prog :=
  ap₂ codeLet ((parameterStageCompiler c).comp (snd.comp snd))
    (ap₂ codeLet ((dimensionStageCompiler k U).comp (fst.pair (snd.comp snd)))
      ((finalStageCompiler k U).comp snd))

theorem crossCompiler_apply (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog) :
    crossCompiler c k U (S,D,lam) = crossProg c k lam U S D := rfl

theorem crossCompiler_binary_bounds (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog) :
    esize (crossProg c k lam U S D) ≤
      (crossCompiler c k U).timeBound.eval (esize S + esize D + 4*Nat.size lam + 3) ∧
    ∃ t ≤ (crossCompiler c k U).timeBound.eval (esize S + esize D + 4*Nat.size lam + 3),
      (crossCompiler c k U).code.Runs (encode (S,D,lam)) (encode (crossProg c k lam U S D)) t := by
  have he : esize (S,D,lam) ≤ esize S + esize D + 4*Nat.size lam + 3 := by
    simp only [esize_prod]
    have := esize_nat_le lam
    omega
  have hb := polynomial_eval_mono (crossCompiler c k U).timeBound he
  obtain ⟨t,ht,hr⟩ := (crossCompiler c k U).computes (S,D,lam)
  exact ⟨((crossCompiler c k U).esize_apply_le (S,D,lam)).trans hb,t,ht.trans hb,hr⟩

end MIPRE.Introspection.SourceCompiler

end
