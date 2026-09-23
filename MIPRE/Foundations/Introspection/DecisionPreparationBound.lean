/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.DecisionPreparationCost

/-! # Ambient input-size bounds for the compiled introspection decision kernel

The shared exponential resources depend only on the binary source parameter
and index. Arbitrarily long or malformed payloads cost a fixed polynomial in
their own encoding size. This separates those two contributions explicitly.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionPreparation
open Cost Polynomial

/-- A single fixed exponent bounds arbitrary raw inputs after linear metadata
clamping. No promise on the raw question or answer lengths is used. -/
theorem compiler_ambient_time {c : ℕ} (hc : 1 ≤ c)
    (kernel : PolyTimeFun KernelInput Bool) :
    ∃ C, ∀ (M : Metadata) (x : Data),
      1 ≤ M.2 → 1 ≤ ClockSimulation.indexReader x →
      esize M ≤ 13 * (M.2 + 1) →
      ∃ time ≤ ansBound C M.2 (ClockSimulation.indexReader x) * (x.size + 1)^C,
        (compiler c kernel M).Runs x (encode (kernel (kernelInput c M x))) time := by
  obtain ⟨d, hd⟩ := (PolyBounded.eval (compiledPoly c kernel) PolyBounded.id).exists_le_pow
  obtain ⟨C, hC⟩ := polynomial_ansBound ((28 * X)^d) 5
  refine ⟨max C d, fun M x hl hn hM => ?_⟩
  let B := ansBound 5 M.2 (ClockSimulation.indexReader x)
  have hB : 2 ≤ B := by
    change 2^1 ≤ 2^((M.2*ClockSimulation.indexReader x+1)^5)
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.one_le_pow _ _ (by omega)
  have hlB : M.2 ≤ B := (ClockArithmetic.clock_arguments_le (by decide : 1 ≤ 5) hl hn).1
  have hmB : esize M ≤ 26*B := by omega
  let v := (28*B)*(x.size+1)
  have hv : 2 ≤ v := by dsimp [v]; nlinarith
  have hz : esize M+x.size+1 ≤ v := by dsimp [v]; nlinarith
  have hb : B ≤ v := by dsimp [v]; nlinarith
  obtain ⟨t, ht, hr⟩ := compiler_runs_poly hc kernel M x hl hn hz hb
  have he : (28*B)^d ≤ ansBound C M.2 (ClockSimulation.indexReader x) := by
    simpa only [eval_pow, eval_mul, eval_ofNat, eval_X] using hC M.2 _ hl hn
  have hmono : ansBound C M.2 (ClockSimulation.indexReader x) ≤
      ansBound (max C d) M.2 (ClockSimulation.indexReader x) := by
    unfold ansBound
    exact Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_right (by omega) (le_max_left C d))
  refine ⟨t, ht.trans ((hd v hv).trans ?_), hr⟩
  calc v^d = (28*B)^d * (x.size+1)^d := by dsimp [v]; rw [mul_pow]
    _ ≤ ansBound (max C d) M.2 (ClockSimulation.indexReader x) * (x.size+1)^(max C d) :=
      Nat.mul_le_mul (he.trans hmono)
        (Nat.pow_le_pow_right (by omega) (le_max_right C d))

end MIPRE.Introspection.DecisionPreparation
