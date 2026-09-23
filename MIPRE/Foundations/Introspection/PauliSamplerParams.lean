/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourceCompilerParams

/-! # Canonical parameters for the executable Pauli sampler

The selector width, field width and point dimension are computed from the
same canonical parameters as the source compiler. The program returns unary
parameters, which are the input format of the uniform field algorithms.
-/

noncomputable section
namespace MIPRE.Introspection.PauliSamplerParameters
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler

def selectorBits (c lam n : ℕ) : ℕ := (c * canonicalLog lam n + 1).size - 1

theorem registerPower_eq (c lam n : ℕ) :
    registerPower c lam n = 2 ^ selectorBits c lam n := rfl

theorem fieldBits_pos (c lam n : ℕ) : 1 ≤ fieldBits c lam n := by
  unfold fieldBits
  omega

instance fieldBits_neZero (c lam n : ℕ) : NeZero (fieldBits c lam n) :=
  ⟨by have := fieldBits_pos c lam n; omega⟩

theorem fieldBits_odd {c : ℕ} (hc : Even c) (lam n : ℕ) :
    Odd (fieldBits c lam n) := by
  obtain ⟨a, ha⟩ := hc
  refine ⟨a * (canonicalLog lam n - 1).size, ?_⟩
  simp only [fieldBits, ha]
  ring

theorem registerPower_pos (c lam n : ℕ) : 1 ≤ registerPower c lam n := by
  exact Nat.one_le_pow _ _ (by decide)

theorem registerPower_le (c lam n : ℕ) :
    registerPower c lam n ≤ c * canonicalLog lam n + 1 := by
  apply Nat.lt_size.mp
  have h := Nat.size_pos.mpr (show 0 < c * canonicalLog lam n + 1 by omega)
  omega

theorem canonicalLog_lt_registerPower {c : ℕ} (hc : 2 ≤ c) (lam n : ℕ) :
    canonicalLog lam n < registerPower c lam n := by
  let t := canonicalLog lam n
  have hs := Nat.size_pos.mpr (show 0 < c * t + 1 by omega)
  have hp := Nat.lt_size_self (c * t + 1)
  have he : (c * t + 1).size = ((c * t + 1).size - 1) + 1 := by omega
  rw [he, pow_succ] at hp
  change c * t + 1 < registerPower c lam n * 2 at hp
  have hc' : 2 * t ≤ c * t := Nat.mul_le_mul_right t hc
  change t < registerPower c lam n
  omega

theorem fieldBits_le (c lam n : ℕ) :
    fieldBits c lam n ≤ c * canonicalLog lam n + 1 := by
  have hs : (canonicalLog lam n - 1).size ≤ canonicalLog lam n :=
    (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (Nat.sub_le _ _)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left c hs) 1

theorem selectorBits_le_fieldBits {c : ℕ} (hc : 1 ≤ c) (lam n : ℕ) :
    selectorBits c lam n ≤ fieldBits c lam n := by
  let t := canonicalLog lam n
  let s := (t - 1).size
  have ht : 2 ≤ t := le_max_left _ _
  have hs : 1 ≤ s := Nat.size_pos.mpr (by omega)
  have htPow : t ≤ 2 ^ s := by
    have := Nat.lt_size_self (t - 1)
    change t ≤ 2 ^ (t - 1).size
    omega
  have he : c + s ≤ c * s + 1 := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hc
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hs
    rw [ha, hb]
    nlinarith
  have hp : c * t + 1 ≤ 2 ^ (c * s + 1) := by
    calc
      c * t + 1 ≤ (c + 1) * t := by nlinarith
      _ ≤ 2 ^ c * 2 ^ s := Nat.mul_le_mul Nat.lt_two_pow_self htPow
      _ = 2 ^ (c + s) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (c * s + 1) := Nat.pow_le_pow_right (by decide) he
  have hsize := Nat.size_le_size hp
  rw [Nat.size_pow] at hsize
  change (c * t + 1).size - 1 ≤ c * s + 1
  omega

theorem four_le_registerBits {c : ℕ} (hc : 2 ≤ c) (lam n : ℕ) :
    4 ≤ registerBits c lam n := by
  have hm : 2 ≤ registerPower c lam n := by
    have ht := canonicalLog_lt_registerPower hc lam n
    have h2 : 2 ≤ canonicalLog lam n := le_max_left _ _
    omega
  have hp : 4 ≤ 2 ^ registerPower c lam n :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm
  exact hp.trans (Nat.le_mul_of_pos_right _ (fieldBits_pos c lam n))

theorem originalBound_three_le_registerBits {c : ℕ} (hc : 2 ≤ c) (lam n : ℕ) :
    3 * originalBound lam n ≤ registerBits c lam n := by
  have hs : 1 ≤ (canonicalLog lam n - 1).size := Nat.size_pos.mpr (by
    have : 2 ≤ canonicalLog lam n := le_max_left _ _
    omega)
  have hk : 3 ≤ fieldBits c lam n := by
    have := Nat.mul_le_mul hc hs
    unfold fieldBits
    omega
  have hm : lam * n ≤ registerPower c lam n :=
    (le_max_right _ _).trans (canonicalLog_lt_registerPower hc lam n).le
  calc
    3 * originalBound lam n ≤ fieldBits c lam n * 2 ^ registerPower c lam n :=
      Nat.mul_le_mul hk (Nat.pow_le_pow_right (by decide) hm)
    _ = registerBits c lam n := Nat.mul_comm _ _

abbrev Parameters := Unary × Unary × Unary

def parameters (c lam n : ℕ) : Parameters :=
  (unary (fieldBits c lam n), unary (selectorBits c lam n), unary (registerPower c lam n))

/-- Retain the selector width while its power of two is computed. -/
def powerInput : PolyTimeFun (Unary × Unary × Unary) Data :=
  ap₂ treePair (encoded.comp fst)
    (ap₂ treePair (encoded.comp (snd.comp snd)) (encoded.comp fst))

def powerPost : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (treeHead.comp fst) (ap₂ treePair (treeTail.comp fst) snd)

def prog (c : ℕ) : Prog :=
  .let_ ClockArithmetic.bothUnary (.let_ mulProg (.let_ (parameterSeed c).code
    (.let_ powerInput.code (callWithContext powerUnaryProg powerPost))))

theorem prog_closed (c : ℕ) : (prog c).WellScoped 1 :=
  ⟨ClockArithmetic.bothUnary_closed, mulProg_wellScoped.mono (by omega) _,
    (parameterSeed c).closed.mono (by omega) _, powerInput.closed.mono (by omega) _,
    (callWithContext_closed powerUnaryProg_closed powerPost).mono (by omega) _⟩

theorem prog_runs (c lam n : ℕ) : ∃ time,
    (prog c).Runs (encode (lam, n)) (encode (parameters c lam n)) time := by
  obtain ⟨t₁, _, h₁⟩ := ClockArithmetic.bothUnary_runs lam n
  obtain ⟨t₂, _, h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃, _, h₃⟩ := (parameterSeed c).computes (unary (lam * n))
  have hs : parameterSeed c (unary (lam * n)) =
      (unary (selectorBits c lam n), unary (lam * n), unary (fieldBits c lam n)) := by
    simp only [parameterSeed_apply, length_unary, canonicalLog, selectorBits, fieldBits]
  rw [hs] at h₃
  obtain ⟨t₄, _, h₄⟩ := powerInput.computes
    (unary (selectorBits c lam n), unary (lam * n), unary (fieldBits c lam n))
  have hi : powerInput (unary (selectorBits c lam n), unary (lam * n),
      unary (fieldBits c lam n)) =
      .cons (.ofNat (selectorBits c lam n))
        (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n))) := by
    simp [powerInput, encode_unary]
  rw [hi] at h₄
  obtain ⟨t₅, h₅⟩ := powerUnaryProg_runs (selectorBits c lam n)
  obtain ⟨t₆, h₆⟩ := callWithContext_runs powerUnaryProg_closed powerPost _
    (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n))) _ t₅ h₅
  have ho : powerPost
      (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n)),
        .ofNat (2 ^ selectorBits c lam n)) = encode (parameters c lam n) := by
    simp [powerPost, parameters, encode_prod, encode_unary, registerPower_eq]
  rw [ho] at h₆
  simp only [encode_unary] at h₃
  exact ⟨_, Eval.let_ h₁ (Eval.append_of_wellScoped (Eval.let_ h₂
    (Eval.append_of_wellScoped (Eval.let_ h₃ (Eval.append_of_wellScoped
      (Eval.let_ h₄ (Eval.append_of_wellScoped h₆
        (callWithContext_closed powerUnaryProg_closed powerPost) _))
      ⟨powerInput.closed, (callWithContext_closed powerUnaryProg_closed powerPost).mono
        (by omega) _⟩ _))
      ⟨(parameterSeed c).closed, powerInput.closed.mono (by omega) _,
        (callWithContext_closed powerUnaryProg_closed powerPost).mono (by omega) _⟩ _))
    ⟨mulProg_wellScoped, (parameterSeed c).closed.mono (by omega) _,
      powerInput.closed.mono (by omega) _,
      (callWithContext_closed powerUnaryProg_closed powerPost).mono (by omega) _⟩ _)⟩

end MIPRE.Introspection.PauliSamplerParameters
end
