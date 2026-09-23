/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliSamplerParams
import MIPRE.Foundations.Introspection.SourceCompilerParamsCost

/-! # Execution cost of the canonical Pauli parameters -/

noncomputable section
namespace MIPRE.Introspection.PauliSamplerParameters
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler ClockArithmetic

def cost (c lam n : ℕ) : ℕ :=
  let u := lam * n
  let j := selectorBits c lam n
  let k := fieldBits c lam n
  let m := registerPower c lam n
  unaryCost lam + unaryCost n + esize lam + esize n + 2 * lam + 2 * n + 20 +
    mulCost lam n + (parameterSeed c).timeBound.eval (2 * u + 1) +
    powerInput.timeBound.eval (2 * j + 2 * u + 2 * k + 5) +
    contextCost powerPost (.ofNat j) (.cons (.ofNat k) (.ofNat j)) (.ofNat m)
      (powerUnaryCost j) + 4

theorem prog_runs_cost (c lam n : ℕ) : ∃ time ≤ cost c lam n,
    (prog c).Runs (encode (lam, n)) (encode (parameters c lam n)) time := by
  obtain ⟨t₁, ht₁, h₁⟩ := bothUnary_runs lam n
  obtain ⟨t₂, ht₂, h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃, ht₃, h₃⟩ := (parameterSeed c).computes (unary (lam * n))
  have hs : parameterSeed c (unary (lam * n)) =
      (unary (selectorBits c lam n), unary (lam * n), unary (fieldBits c lam n)) := by
    simp only [parameterSeed_apply, length_unary, canonicalLog, selectorBits, fieldBits]
  rw [hs] at h₃
  obtain ⟨t₄, ht₄, h₄⟩ := powerInput.computes
    (unary (selectorBits c lam n), unary (lam * n), unary (fieldBits c lam n))
  have hi : powerInput (unary (selectorBits c lam n), unary (lam * n),
      unary (fieldBits c lam n)) =
      .cons (.ofNat (selectorBits c lam n))
        (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n))) := by
    simp [powerInput, encode_unary]
  rw [hi] at h₄
  obtain ⟨t₅, ht₅, h₅⟩ := powerUnaryProg_runs_cost (selectorBits c lam n)
  obtain ⟨t₆, ht₆, h₆⟩ := callWithContext_cost powerUnaryProg_closed powerPost _
    (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n))) _ t₅ h₅
  have ho : powerPost
      (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n)),
        .ofNat (2 ^ selectorBits c lam n)) = encode (parameters c lam n) := by
    simp [powerPost, parameters, encode_prod, encode_unary, registerPower_eq]
  rw [ho] at h₆
  simp only [encode_unary] at h₃
  refine ⟨_, ?_, Eval.let_ h₁ (Eval.append_of_wellScoped (Eval.let_ h₂
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
  change t₂ ≤ mulCost lam n at ht₂
  simp only [esize_prod, esize_unary] at ht₃ ht₄
  have hm : 2 ^ selectorBits c lam n = registerPower c lam n := rfl
  rw [hm] at ht₆
  dsimp only [cost, contextCost]
  have harg : 2 * selectorBits c lam n + 1 +
      (2 * (lam * n) + 1 + (2 * fieldBits c lam n + 1) + 1) + 1 =
      2 * selectorBits c lam n + 2 * (lam * n) + 2 * fieldBits c lam n + 5 := by omega
  rw [harg] at ht₄
  omega

/-- A polynomial upper bound for binary-to-unary conversion. -/
def unaryMajorant (v : ℕ) : ℕ :=
  (v + 2) * ((v + 1) * (4 * v + 14) + 7 * (4 * v + 1) + 8 * v + 90)

theorem unaryCost_le {x v : ℕ} (hx : x ≤ v) : unaryCost x ≤ unaryMajorant v := by
  have hsize : x.size ≤ v := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hx
  have henc : esize x ≤ 4 * v + 1 := (esize_nat_le x).trans (by omega)
  unfold unaryCost unaryMajorant
  gcongr

def widthBound (c v : ℕ) : ℕ := c * (v + 2) + 1

def costMajorant (c v : ℕ) : ℕ :=
  let h := widthBound c v
  2 * unaryMajorant v + 2 * (4 * v + 1) + 4 * v + 20 + mulCost v v +
    (parameterSeed c).timeBound.eval (2 * v + 1) +
    powerInput.timeBound.eval (6 * h + 5) +
    (2 * (2 * h + 1) + 2 * (4 * h + 3) + (2 * h + 1) +
      (exponentBitsCost h + unaryMajorant h + 1) +
      powerPost.timeBound.eval (6 * h + 5) + 12) + 4

theorem parameters_le_widthBound {c lam n v : ℕ} (hc : 1 ≤ c) (hu : lam * n ≤ v) :
    fieldBits c lam n ≤ widthBound c v ∧
    selectorBits c lam n ≤ widthBound c v ∧
    registerPower c lam n ≤ widthBound c v := by
  have ht : canonicalLog lam n ≤ v + 2 := by unfold canonicalLog; omega
  have hw : c * canonicalLog lam n + 1 ≤ widthBound c v := by
    unfold widthBound
    gcongr
  have hk := (fieldBits_le c lam n).trans hw
  exact ⟨hk, (selectorBits_le_fieldBits hc lam n).trans hk,
    (registerPower_le c lam n).trans hw⟩

theorem parameters_size_le {c lam n v : ℕ} (hc : 1 ≤ c) (hu : lam * n ≤ v) :
    esize (parameters c lam n) ≤ 6 * widthBound c v + 5 := by
  obtain ⟨hk, hj, hm⟩ := parameters_le_widthBound hc hu
  simp only [parameters, esize_prod, esize_unary]
  omega

theorem cost_le_majorant {c lam n v : ℕ} (hc : 1 ≤ c)
    (hl : lam ≤ v) (hn : n ≤ v) (hu : lam * n ≤ v) :
    cost c lam n ≤ costMajorant c v := by
  obtain ⟨hk, hj, hm⟩ := parameters_le_widthBound hc hu
  have hv : v ≤ widthBound c v := by
    have := Nat.mul_le_mul_right (v + 2) hc
    unfold widthBound
    omega
  have hel : esize lam ≤ 4 * v + 1 := (esize_nat_le lam).trans (by
    have h := (Nat.size_le.mpr Nat.lt_two_pow_self : lam.size ≤ lam)
    omega)
  have hen : esize n ≤ 4 * v + 1 := (esize_nat_le n).trans (by
    have h := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n)
    omega)
  have hul := unaryCost_le hl
  have hun := unaryCost_le hn
  have hmm : mulCost lam n ≤ mulCost v v := by unfold mulCost; gcongr
  have hseed := polynomial_eval_mono (parameterSeed c).timeBound
    (show 2 * (lam * n) + 1 ≤ 2 * v + 1 by omega)
  have hinput := polynomial_eval_mono powerInput.timeBound
    (show 2 * selectorBits c lam n + 2 * (lam * n) + 2 * fieldBits c lam n + 5 ≤
      6 * widthBound c v + 5 by omega)
  have hpower : powerUnaryCost (selectorBits c lam n) ≤
      exponentBitsCost (widthBound c v) + unaryMajorant (widthBound c v) + 1 := by
    have hexp : exponentBitsCost (selectorBits c lam n) ≤
        exponentBitsCost (widthBound c v) := by unfold exponentBitsCost; gcongr
    have hu' := unaryCost_le hm
    change unaryCost (2 ^ selectorBits c lam n) ≤ unaryMajorant (widthBound c v) at hu'
    unfold powerUnaryCost
    omega
  have hpost := polynomial_eval_mono powerPost.timeBound
    (show (Data.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n))).size +
      (Data.ofNat (registerPower c lam n)).size + 1 ≤ 6 * widthBound c v + 5 by
      simp only [Data.size_cons, Data.size_ofNat]
      omega)
  unfold cost costMajorant contextCost
  simp only [Data.size_cons, Data.size_ofNat] at hpost ⊢
  omega

theorem costMajorant_polyBounded (c : ℕ) : PolyBounded (costMajorant c) := by
  unfold costMajorant widthBound unaryMajorant mulCost exponentBitsCost
  repeat' first
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.eval
    | apply PolyBounded.const
    | exact PolyBounded.id

end MIPRE.Introspection.PauliSamplerParameters
end
