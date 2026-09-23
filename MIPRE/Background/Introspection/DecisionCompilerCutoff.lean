/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.DecisionPreparationCost
import MIPRE.Foundations.Cost.BinaryArithmetic

/-! # A binary answer cutoff for the compiled introspection decider

The cutoff covers full register triples and original answers. Its computation
uses binary comparison and three binary shifts; its numeric value is never
expanded into a unary counter.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost Cost.PolyTimeFun Polynomial

def answerBound (Q R : ℕ) : ℕ := 8 * max 1 (max Q R)

def maxNat : PolyTimeFun (ℕ × ℕ) ℕ := ite leNat snd fst
@[simp] theorem maxNat_apply (x : ℕ × ℕ) : maxNat x = max x.1 x.2 := by
  simp only [maxNat, PolyTimeFun.ite_apply, leNat_apply, snd_apply, fst_apply,
    decide_eq_true_eq]
  split_ifs with h
  · exact (Nat.max_eq_right h).symm
  · exact (Nat.max_eq_left (by omega)).symm

def doubleNat : PolyTimeFun ℕ ℕ := natBit.comp ((const false).pair (PolyTimeFun.id ℕ))
@[simp] theorem doubleNat_apply (n : ℕ) : doubleNat n = 2*n := by
  simp [doubleNat, Nat.bit_val]

def cutoff : PolyTimeFun (ℕ × ℕ) ℕ :=
  (doubleNat.comp (doubleNat.comp doubleNat)).comp
    (maxNat.comp ((const 1).pair maxNat))

@[simp] theorem cutoff_apply (Q R : ℕ) : cutoff (Q,R) = answerBound Q R := by
  simp [cutoff, answerBound]
  omega

theorem answerBound_covers (Q R : ℕ) : 3*Q+R+3 ≤ answerBound Q R := by
  have hQ := (le_max_left Q R).trans (le_max_right 1 (max Q R))
  have hR := (le_max_right Q R).trans (le_max_right 1 (max Q R))
  have h1 := le_max_left 1 (max Q R)
  unfold answerBound
  omega

/-- The concrete binary cutoff fits one fixed introspection answer budget. -/
theorem answerBound_ansBound {c : ℕ} (hc : 1 ≤ c) :
    ∃ K, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n) ≤
        ansBound K lam n := by
  let d := 2*(3*c+1)
  obtain ⟨K,hK⟩ := polynomial_ansBound (8*X^d) 1
  refine ⟨K, fun lam n hl hn => ?_⟩
  let u := lam*n
  let H := PauliSamplerParameters.widthBound c u
  let B := ansBound 1 lam n
  obtain ⟨hk, _, hm⟩ := PauliSamplerParameters.parameters_le_widthBound hc (le_refl u)
  have hH : H ≤ (3*c+1)*(u+1) := by
    dsimp [H, PauliSamplerParameters.widthBound]
    nlinarith
  have hQ : SourceCompiler.registerBits c lam n ≤ B^d := by
    calc SourceCompiler.registerBits c lam n
        ≤ 2^H * 2^H := Nat.mul_le_mul
          (Nat.pow_le_pow_right (by decide) hm)
          (hk.trans (Nat.lt_two_pow_self.le))
      _ = 2^(2*H) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2^((u+1)*d) := Nat.pow_le_pow_right (by decide) (by dsimp [d]; nlinarith)
      _ = B^d := by simp [B, ansBound, u, pow_mul]
  have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hR : SourceCompiler.originalBound lam n ≤ B^d := by
    calc SourceCompiler.originalBound lam n ≤ B := by
          apply Nat.pow_le_pow_right (by decide)
          change u ≤ (u+1)^1
          simp
      _ ≤ B^d := by simpa only [pow_one] using Nat.pow_le_pow_right hB hd
  have hmB : max 1 (max (SourceCompiler.registerBits c lam n)
      (SourceCompiler.originalBound lam n)) ≤ B^d :=
    max_le (Nat.one_le_pow _ _ hB) (max_le hQ hR)
  calc answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n)
      ≤ 8*B^d := Nat.mul_le_mul_left _ hmB
    _ ≤ ansBound K lam n := by
      simpa only [eval_mul, eval_ofNat, eval_pow, eval_X] using hK lam n hl hn

end MIPRE.Introspection.DecisionCompiler
