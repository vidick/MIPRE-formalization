/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockCost

/-! # Executable clocked simulation at the original exponential index

The clock is computed at index `n`; the source program receives index `2^n`.
Both transformations are actual programs. The repaired exponent-five bound
preserves the original bounded decider on its legal question and answer cut.
-/

noncomputable section

namespace MIPRE.Introspection.ClockSimulation

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program

def indexReader : PolyTimeFun Data ℕ := readNat.comp treeHead

def reindexed (x : Data) : Data := .cons (encode (2 ^ indexReader x)) (treeTail x)

def reindexProg : Prog :=
  .let_ indexReader.code (.let_ toUnaryProg (.let_ expBitsProg
    (.cons (.var 0) (callVar 3 treeTail.code))))

theorem reindexProg_closed : reindexProg.WellScoped 1 :=
  ⟨indexReader.closed, toUnaryProg_wellScoped.mono (by omega) _,
    expBitsProg_wellScoped.mono (by omega) _, by simp [WellScoped],
    callVar_wellScoped (by omega) treeTail.closed⟩

/-- The source-index adapter is total even when the incoming index is malformed. -/
theorem reindexProg_runs (x : Data) : ∃ time, reindexProg.Runs x (reindexed x) time := by
  obtain ⟨ti, _, hi⟩ := indexReader.computes x
  obtain ⟨tu, _, hu⟩ := toUnaryProg_runs (indexReader x)
  obtain ⟨te, _, he⟩ := expBitsProg_runs (indexReader x)
  obtain ⟨td, _, hd⟩ := treeTail.computes x
  exact ⟨_, Eval.let_ hi (Eval.let_ (Eval.append_of_wellScoped hu toUnaryProg_wellScoped _)
    (Eval.let_ (Eval.append_of_wellScoped he expBitsProg_wellScoped _)
      (Eval.cons (Eval.var_of_get (i := 0) (by simp))
        (callVar_eval (i := 3) treeTail.closed (by simp) hd))))⟩

theorem reindexed_cons (n : ℕ) (d : Data) :
    reindexed (.cons (encode n) d) = .cons (encode (2 ^ n)) d := by
  simp only [reindexed, indexReader, comp_apply, treeHead_cons, treeTail_cons, readNat_encode]

def clockStage (k lam : ℕ) : Prog :=
  Prog.routeOneCall ClockProgram.clockRoute (growingClock k lam).prog treePair

theorem clockStage_closed (k lam : ℕ) : (clockStage k lam).WellScoped 1 :=
  Prog.routeOneCall_closed _ (growingClock k lam).closed _

theorem clockStage_runs (k lam : ℕ) (x : Data) :
    ∃ time, (clockStage k lam).Runs x (.cons x (.ofNat (ansBound k lam (indexReader x)))) time := by
  obtain ⟨time, hr⟩ := (growingClock k lam).runs (indexReader x)
  exact Prog.routeOneCall_indirect ClockProgram.clockRoute (growingClock k lam).closed
    treePair x _ x _ time rfl hr

def simulationInput (source : Prog) : PolyTimeFun (Data × Data) Data where
  toFun p := .cons p.1 (.cons (encode source) p.2)
  code := .elim 0 .nil (.cons (.var 0) (.cons (.const (encode source)) (.var 1)))
  closed := by simp [WellScoped]
  timeBound := Polynomial.X + Polynomial.C (esize source + 4)
  computes p := by
    rcases p with ⟨ctx, r⟩
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ctx) (b := r) (by rfl)
      (Eval.cons (Eval.var_of_get (i := 0) (by simp))
        (Eval.cons (Eval.const _ _) (Eval.var_of_get (i := 1) (by simp))))⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod, esize_data]
    change _ ≤ ctx.size + r.size + 1 + ((encode source).size + 4)
    omega

def reindexStage (source : Prog) : Prog := callWithContext reindexProg (simulationInput source)

theorem reindexStage_closed (source : Prog) : (reindexStage source).WellScoped 1 :=
  callWithContext_closed reindexProg_closed _

theorem reindexStage_runs (source : Prog) (x : Data) (budget : ℕ) :
    ∃ time, (reindexStage source).Runs (.cons x (.ofNat budget))
      (.cons (.ofNat budget) (.cons (encode source) (reindexed x))) time := by
  obtain ⟨time, hr⟩ := reindexProg_runs x
  exact callWithContext_runs reindexProg_closed (simulationInput source) x (.ofNat budget)
    (reindexed x) time hr

/-- This program computes the growing budget, changes the source index, and simulates. -/
def prog (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) : Prog :=
  .let_ (clockStage k lam) (.let_ (reindexStage source) U.univT)

theorem prog_closed (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) :
    (prog k lam U source).WellScoped 1 :=
  ⟨clockStage_closed k lam, (reindexStage_closed source).mono (by omega) _,
    U.closed.mono (by omega) _⟩

theorem prog_runs (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) (x : Data) :
    ∃ time, (prog k lam U source).Runs x
      (clockedResult source (reindexed x) (ansBound k lam (indexReader x))) time := by
  obtain ⟨tc, hc⟩ := clockStage_runs k lam x
  obtain ⟨tr, hr⟩ := reindexStage_runs source x (ansBound k lam (indexReader x))
  obtain ⟨tu, _, hu⟩ := U.run source (reindexed x) (ansBound k lam (indexReader x))
  exact ⟨_, Eval.let_ hc (Eval.append_of_wellScoped
    (Eval.let_ hr (Eval.append_of_wellScoped hu U.closed _))
      ⟨reindexStage_closed source, U.closed.mono (by omega) _⟩ _)⟩

theorem prog_halts (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) (x : Data) :
    Halts (prog k lam U source) x := by
  obtain ⟨time, hr⟩ := prog_runs k lam U source x
  exact ⟨_, time, hr⟩

/-- The resulting ordinary decider rejects timeouts and all nonaccepting results. -/
def decider (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) : MIPRE.Decider where
  prog := .let_ (prog k lam U source) ClockProgram.checkResult.code
  closed := ⟨prog_closed k lam U source, ClockProgram.checkResult.closed.mono (by omega) _⟩

theorem decider_runs (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) (x : Data) :
    ∃ time, (decider k lam U source).prog.Runs x
      (encode (decide (clockedResult source (reindexed x) (ansBound k lam (indexReader x)) =
        .cons (encode true) (encode true)))) time := by
  obtain ⟨time, hr⟩ := prog_runs k lam U source x
  obtain ⟨tc, _, hc⟩ := ClockProgram.checkResult.computes
    (clockedResult source (reindexed x) (ansBound k lam (indexReader x)))
  exact ⟨_, Eval.let_ hr (Eval.append_of_wellScoped hc ClockProgram.checkResult.closed _)⟩

theorem decider_halts (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) (x : Data) :
    Halts (decider k lam U source).prog x := by
  obtain ⟨time, hr⟩ := decider_runs k lam U source x
  exact ⟨_, time, hr⟩

theorem decider_accepts_iff (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog)
    (n : ℕ) (x y a b : BitStr) :
    (decider k lam U source).Accepts n x y a b ↔
      ∃ time ≤ ansBound k lam n, source.Runs (encode (2 ^ n, x, y, a, b)) (encode true) time := by
  obtain ⟨time, hout⟩ := decider_runs k lam U source (encode (n, x, y, a, b))
  have hi : indexReader (encode (n, x, y, a, b)) = n := readNat_encode n
  have he : reindexed (encode (n, x, y, a, b)) = encode (2 ^ n, x, y, a, b) :=
    reindexed_cons n (encode (x, y, a, b))
  rw [hi, he] at hout
  rw [← ClockProgram.clockedResult_eq_iff]
  constructor
  · rintro ⟨t, hr⟩
    exact of_decide_eq_true (encode_injective (hout.deterministic hr).1)
  · intro h
    exact ⟨time, by simpa only [h, decide_true] using hout⟩

/-- The concrete exponent-five clock preserves the original bounded verifier on
the original legal answer alphabet, without enlarging that alphabet. -/
theorem original_decider_preserved {ℓ lam n : ℕ} (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (x y a b : BitStr)
    (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
    (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
    (decider 5 lam U V.decider.prog).Accepts n x y a b ↔
      V.decider.Accepts (2 ^ n) x y a b := by
  rw [decider_accepts_iff]
  constructor
  · rintro ⟨time, _, hr⟩; exact ⟨time, hr⟩
  · rintro ⟨time, hr⟩
    obtain ⟨r, t, ht, hout⟩ := original_decider_haltsWithin V hV hn x y a b hx hy ha hb
    exact ⟨time, (hout.deterministic hr).2 ▸ ht, hr⟩

end MIPRE.Introspection.ClockSimulation
