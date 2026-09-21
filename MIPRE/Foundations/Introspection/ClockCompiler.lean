/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockSimulation

/-! # A binary compiler for the complete clocked source decider

The compiler constructs the actual program syntax from the source description
and binary parameter. Both compilation time and output description size are
polynomial in their encoded lengths, for fixed exponent and universal machine.
-/

noncomputable section

namespace MIPRE.Introspection.ClockSimulation

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program

def codeConst : PolyTimeFun Data Prog :=
  cast (ap₂ treePair (const (Data.ofNat 6)) (PolyTimeFun.id Data)) Prog.const (by intro d; rfl)

def codeCons : PolyTimeFun (Prog × Prog) Prog :=
  cast (ap₂ treePair (const (Data.ofNat 2))
    (ap₂ treePair (encoded.comp fst) (encoded.comp snd)))
    (fun p => .cons p.1 p.2) (by intro p; rfl)

def codeLet : PolyTimeFun (Prog × Prog) Prog :=
  cast (ap₂ treePair (const (Data.ofNat 4))
    (ap₂ treePair (encoded.comp fst) (encoded.comp snd)))
    (fun p => .let_ p.1 p.2) (by intro p; rfl)

def codeElim : PolyTimeFun (Prog × Prog) Prog :=
  cast (ap₂ treePair (const (Data.ofNat 3)) (ap₂ treePair (const Data.nil)
    (ap₂ treePair (encoded.comp fst) (encoded.comp snd))))
    (fun p => .elim 0 p.1 p.2) (by intro p; rfl)

def codeCall (i : ℕ) : PolyTimeFun Prog Prog :=
  ap₂ codeLet (const (.var i)) (PolyTimeFun.id Prog)

def codeContext : PolyTimeFun (Prog × Prog) Prog :=
  ap₂ codeLet (const fstProg)
    (ap₂ codeLet fst (ap₂ codeLet (const (.cons (callVar 2 sndProg) (.var 0))) snd))

theorem codeContext_apply (p : Prog) (post : PolyTimeFun (Data × Data) Data) :
    codeContext (p, post.code) = callWithContext p post := rfl

def codeRoute (route : PolyTimeFun Data (Bool × Data)) (post : PolyTimeFun (Data × Data) Data) :
    PolyTimeFun Prog Prog :=
  ap₂ codeLet (const route.code)
    (ap₂ codeElim (const .nil) (ap₂ codeElim (const (.var 1))
      ((codeCall 3).comp (codeContext.comp ((PolyTimeFun.id Prog).pair (const post.code))))))

theorem codeRoute_apply (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (p : Prog) :
    codeRoute route post p = routeOneCall route p post := rfl

def clockStageCompiler (k : ℕ) : PolyTimeFun ℕ Prog :=
  (codeRoute ClockProgram.clockRoute treePair).comp (growingClockCompiler k)

def simulationInputCompiler : PolyTimeFun Prog Prog :=
  ap₂ codeElim (const .nil)
    (ap₂ codeCons (const (.var 0))
      (ap₂ codeCons (codeConst.comp encoded) (const (.var 1))))

def reindexStageCompiler : PolyTimeFun Prog Prog :=
  codeContext.comp ((const reindexProg).pair simulationInputCompiler)

/-- An actual ambient compiler for the existing clocked decider program. -/
def compiler (k : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun (Prog × ℕ) Prog :=
  ap₂ codeLet
    (ap₂ codeLet ((clockStageCompiler k).comp snd)
      (ap₂ codeLet (reindexStageCompiler.comp fst) (const U.univT)))
    (const ClockProgram.checkResult.code)

theorem compiler_apply (k : ℕ) (U : ClockedUniversalMachine) (source : Prog) (lam : ℕ) :
    compiler k U (source, lam) = (decider k lam U source).prog := rfl

theorem compiler_runs (k : ℕ) (U : ClockedUniversalMachine) (source : Prog) (lam : ℕ) :
    ∃ time ≤ (compiler k U).timeBound.eval (esize source + esize lam + 1),
      (compiler k U).code.Runs (encode (source, lam)) (encode (decider k lam U source).prog) time :=
  (compiler k U).computes (source, lam)

theorem decider_size_le (k : ℕ) (U : ClockedUniversalMachine) (source : Prog) (lam : ℕ) :
    esize (decider k lam U source).prog ≤
      (compiler k U).timeBound.eval (esize source + esize lam + 1) :=
  (compiler k U).esize_apply_le (source, lam)

/-- The parameter enters both compiler cost and description length through its bits. -/
theorem compiler_binary_bounds (k : ℕ) (U : ClockedUniversalMachine) (source : Prog) (lam : ℕ) :
    esize (decider k lam U source).prog ≤
        (compiler k U).timeBound.eval (esize source + 4 * Nat.size lam + 2) ∧
    ∃ time ≤ (compiler k U).timeBound.eval (esize source + 4 * Nat.size lam + 2),
      (compiler k U).code.Runs (encode (source, lam)) (encode (decider k lam U source).prog) time := by
  have h := polynomial_eval_mono (compiler k U).timeBound
    (show esize source + esize lam + 1 ≤ esize source + 4 * Nat.size lam + 2 by
      have := esize_nat_le lam; omega)
  obtain ⟨time, ht, hr⟩ := compiler_runs k U source lam
  exact ⟨(decider_size_le k U source lam).trans h, time, ht.trans h, hr⟩

end MIPRE.Introspection.ClockSimulation
