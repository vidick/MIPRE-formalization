/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockArithmetic

/-! # The actual growing introspection clock

The closed clock program writes the exact repaired introspection budget in
unary. Hardwiring the binary parameter has linear description overhead, and
the compiler itself is an actual polynomial-time ambient program.
-/

noncomputable section

namespace MIPRE.Introspection

open Cost Cost.PolyTimeFun ClockArithmetic

/-- The executable polynomial-exponent clock, with the parameter stored in binary. -/
def growingClock (k lam : ℕ) : CL.Detyping.ClockProgram where
  budget := ansBound k lam
  prog := hardcode (uniformProg k) (encode lam)
  closed := hardcode_wellScoped (uniformProg_closed k) _
  runs n := by
    obtain ⟨time, _, hr⟩ := uniformProg_runs k lam n
    exact ⟨_, hardcode_time (uniformProg_closed k) hr⟩

theorem growingClock_budget (k lam n : ℕ) :
    (growingClock k lam).budget n = ansBound k lam n := rfl

theorem growingClock_runs (k lam n : ℕ) :
    ∃ time ≤ uniformCost k lam n + esize lam + esize n + 3,
      (growingClock k lam).prog.Runs (encode n) (.ofNat (ansBound k lam n)) time := by
  obtain ⟨time, ht, hr⟩ := uniformProg_runs k lam n
  refine ⟨_, ?_, hardcode_time (uniformProg_closed k) hr⟩
  change time + esize lam + esize n + 3 ≤ _
  omega

theorem growingClock_haltsWithin (k lam n : ℕ) :
    HaltsWithin (growingClock k lam).prog (encode n)
      (uniformCost k lam n + esize lam + esize n + 3) := by
  obtain ⟨time, ht, hr⟩ := growingClock_runs k lam n
  exact ⟨_, time, ht, hr⟩

/-- No unary parameter or budget is embedded in the program description. -/
theorem growingClock_size (k lam : ℕ) :
    esize (growingClock k lam).prog = esize (uniformProg k) + esize lam + 35 :=
  hardcode_size _ _

theorem growingClock_size_le (k lam : ℕ) :
    esize (growingClock k lam).prog ≤ esize (uniformProg k) + 4 * Nat.size lam + 36 := by
  rw [growingClock_size]
  have := esize_nat_le lam
  omega

/-- The actual uniform compiler for the parameterized clocks. -/
def growingClockCompiler (k : ℕ) : PolyTimeFun ℕ Prog :=
  (smn ℕ).comp ((const (uniformProg k)).pair (PolyTimeFun.id ℕ))

theorem growingClockCompiler_apply (k lam : ℕ) :
    growingClockCompiler k lam = (growingClock k lam).prog := rfl

/-- Compiler execution takes polynomial time in the binary parameter length. -/
theorem growingClockCompiler_runs (k lam : ℕ) :
    ∃ time ≤ (growingClockCompiler k).timeBound.eval (esize lam),
      (growingClockCompiler k).code.Runs (encode lam) (encode (growingClock k lam).prog) time :=
  (growingClockCompiler k).computes lam

end MIPRE.Introspection
