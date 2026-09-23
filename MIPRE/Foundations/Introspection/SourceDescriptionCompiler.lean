/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.SizeProgram
import MIPRE.Foundations.Cost.Binary
import MIPRE.Foundations.Cost.BinaryCompare
import MIPRE.Foundations.Cost.Growth
import MIPRE.Foundations.Verifier

/-! # Uniformly bounded source descriptions for polynomial-time compilers

The compiler accepts arbitrary source descriptions. Each description exceeding
the supplied binary parameter is replaced by a fixed program before compilation.
This leaves every bounded verifier unchanged and gives a uniform polynomial
output-size bound in the parameter, including at zero.
-/

noncomputable section
namespace MIPRE.Introspection.SourceDescriptionCompiler
open Cost Cost.PolyTimeFun Polynomial

abbrev Input := (Prog × Prog) × ℕ

/-- Actual program encoding size, computed in binary after a linear-size count. -/
def programSize : PolyTimeFun Prog ℕ := unaryToBin.comp (encodedSizeU Prog)

@[simp] theorem programSize_apply (p : Prog) : programSize p = esize p := by
  simp [programSize]

/-- Only an oversized description is replaced. The cutoff stays binary. -/
def clampProgram : PolyTimeFun (Prog × ℕ) Prog :=
  ite (leNat.comp ((programSize.comp fst).pair snd)) fst (const Prog.nil)

@[simp] theorem clampProgram_apply (p : Prog) (lam : ℕ) :
    clampProgram (p, lam) = if esize p ≤ lam then p else Prog.nil := by
  simp [clampProgram, PolyTimeFun.ite_apply]

/-- Clamp sampler and decider independently while retaining the parameter. -/
def clamp : PolyTimeFun Input Input :=
  ((clampProgram.comp ((fst.comp fst).pair snd)).pair
    (clampProgram.comp ((snd.comp fst).pair snd))).pair snd

@[simp] theorem clamp_apply (S D : Prog) (lam : ℕ) :
    clamp ((S, D), lam) = ((clampProgram (S, lam), clampProgram (D, lam)), lam) := rfl

theorem clamp_eq_self (S D : Prog) (lam : ℕ)
    (hS : esize S ≤ lam) (hD : esize D ≤ lam) : clamp ((S, D), lam) = ((S, D), lam) := by
  simp [hS, hD]

/-- The verifier's size clause is exactly the preservation premise. -/
theorem clamp_bounded {ℓ lam : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam) :
    clamp ((V.sampler.prog, V.decider.prog), lam) = ((V.sampler.prog, V.decider.prog), lam) := by
  apply clamp_eq_self
  · exact (le_max_left V.sampler.size V.decider.size).trans hV.2
  · exact (le_max_right V.sampler.size V.decider.size).trans hV.2

theorem clampProgram_size (p : Prog) (lam : ℕ) : esize (clampProgram (p, lam)) ≤ lam + 5 := by
  rw [clampProgram_apply]
  split_ifs with h
  · omega
  · change 5 ≤ lam + 5
    omega

/-- The entire clamped compiler input has size linear in `λ+1`, even at zero. -/
theorem clamp_size (S D : Prog) (lam : ℕ) : esize (clamp ((S, D), lam)) ≤ 13 * (lam + 1) := by
  have hS := clampProgram_size S lam
  have hD := clampProgram_size D lam
  have hn : Nat.size lam ≤ lam := Nat.size_le.mpr Nat.lt_two_pow_self
  have hl := esize_nat_le lam
  rw [clamp_apply, esize_prod, esize_prod]
  omega

variable {β : Type*} [SizedEncoding β]

/-- The final transformation is itself a single polynomial-time function. -/
def compiler (F : PolyTimeFun Input β) : PolyTimeFun Input β := F.comp clamp

theorem compiler_bounded (F : PolyTimeFun Input β) {ℓ lam : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) :
    compiler F ((V.sampler.prog, V.decider.prog), lam) =
      F ((V.sampler.prog, V.decider.prog), lam) := by
  simp only [compiler, comp_apply, clamp_bounded V hV]

/-- The output polynomial uses only the fixed compiler and the parameter. -/
theorem compiler_size_le_eval (F : PolyTimeFun Input β) (S D : Prog) (lam : ℕ) :
    esize (compiler F ((S, D), lam)) ≤ F.timeBound.eval (13 * (lam + 1)) :=
  (F.esize_apply_le _).trans (polynomial_eval_mono F.timeBound (clamp_size S D lam))

/-- A single constant absorbs the compiler's coefficient sum and degree.
There is no lower-bound assumption on the supplied parameter. -/
theorem exists_compiler_size (F : PolyTimeFun Input β) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (S D : Prog) (lam : ℕ),
      esize (compiler F ((S, D), lam)) ≤ C * (lam + 1) ^ C := by
  let d := F.timeBound.natDegree
  let a := ∑ i ∈ Finset.range (d + 1), F.timeBound.coeff i
  let C := a * 13 ^ d + d + 1
  refine ⟨C, by omega, fun S D lam => ?_⟩
  have he : F.timeBound.eval (13 * (lam + 1)) ≤ a * (13 * (lam + 1)) ^ d :=
    polynomial_eval_le_sum_coeff_mul_pow F.timeBound (by omega)
  calc
    esize (compiler F ((S, D), lam)) ≤ F.timeBound.eval (13 * (lam + 1)) :=
      compiler_size_le_eval F S D lam
    _ ≤ a * (13 * (lam + 1)) ^ d := he
    _ = (a * 13 ^ d) * (lam + 1) ^ d := by rw [mul_pow, mul_assoc]
    _ ≤ C * (lam + 1) ^ C := Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (by omega))

end MIPRE.Introspection.SourceDescriptionCompiler
