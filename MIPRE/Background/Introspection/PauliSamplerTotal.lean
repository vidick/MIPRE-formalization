/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.PauliSamplerZero

/-! # The uniformly bounded sampler at every index

The positive-index sampler is unchanged. The exceptional branches have no
question coordinates and execute without inspecting the source description.
-/

noncomputable section
namespace MIPRE.Introspection.PauliSampler
open Cost Cost.Prog Cost.PolyTimeFun CL

def finalSampler (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam : ℕ) : CL.Sampler 5 :=
  if lam = 0 then ZeroIndexSampler.emptySampler 5
  else ZeroIndexSampler.atZero (fullSampler c hc he ℓ lam)

def finalCompiler (c ℓ : ℕ) : PolyTimeFun ℕ Prog :=
  Cost.PolyTimeFun.ite
    (SAT.ArrayProg.eqNat.comp ((Cost.PolyTimeFun.id ℕ).pair (const 0)))
    (const Prog.nil) (ZeroIndexSampler.compiler.comp (fullCompiler c ℓ))

theorem finalCompiler_apply (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam : ℕ) :
    finalCompiler c ℓ lam = (finalSampler c hc he ℓ lam).prog := by
  by_cases hl : lam = 0 <;>
    simp [finalCompiler, finalSampler, hl, ZeroIndexSampler.emptySampler,
      ZeroIndexSampler.atZero, fullCompiler_apply c hc he]

@[simp] theorem finalSampler_dim_lam_zero (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ n : ℕ) :
    (finalSampler c hc he ℓ 0).dim n = 0 := rfl

@[simp] theorem finalSampler_dim_index_zero (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam : ℕ) :
    (finalSampler c hc he ℓ lam).dim 0 = 0 := by
  by_cases hl : lam = 0 <;> simp [finalSampler, hl, ZeroIndexSampler.emptySampler]

theorem finalSampler_dim_zero (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam n : ℕ)
    (h : lam * n = 0) : (finalSampler c hc he ℓ lam).dim n = 0 := by
  rcases Nat.mul_eq_zero.mp h with hl | hn
  · subst lam; exact finalSampler_dim_lam_zero c hc he ℓ n
  · subst n; exact finalSampler_dim_index_zero c hc he ℓ lam

theorem finalSampler_dim_pos (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam n : ℕ)
    (hl : lam ≠ 0) (hn : n ≠ 0) :
    (finalSampler c hc he ℓ lam).dim n = (fullSampler c hc he ℓ lam).dim n := by
  simp only [finalSampler, hl, ↓reduceIte]
  exact ZeroIndexSampler.atZero_dim_pos _ hn

theorem finalSampler_cl_pos (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam n : ℕ)
    (hl : lam ≠ 0) (hn : n ≠ 0) (w : Player) :
    HEq ((finalSampler c hc he ℓ lam).cl n w) ((fullSampler c hc he ℓ lam).cl n w) := by
  have hproj (A B : CL.Sampler 5) (h : A = B) : HEq (A.cl n w) (B.cl n w) := by
    subst B
    rfl
  have hS : finalSampler c hc he ℓ lam =
      ZeroIndexSampler.atZero (fullSampler c hc he ℓ lam) := if_neg hl
  exact (hproj _ _ hS).trans (ZeroIndexSampler.atZero_cl_pos _ hn w)

/-- One exponent controls all indices, including both exceptional zero cases. -/
theorem finalSampler_uniform_bound (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ : ℕ) :
    ∃ C, ∀ lam n,
      (finalSampler c hc he ℓ lam).TimeBoundAt n ((lam * n + 1) ^ C) C ∧
      (finalSampler c hc he ℓ lam).dim n ≤ (lam * n + 1) ^ C := by
  obtain ⟨C, hC⟩ := fullSampler_uniform_bound c hc he ℓ
  have hp : PolyBounded (fun v => v ^ C + 4 * v + 6) :=
    ((PolyBounded.id.pow C).add ((PolyBounded.const 4).mul PolyBounded.id)).add
      (PolyBounded.const 6)
  obtain ⟨D, hD⟩ := hp.exists_le_pow
  refine ⟨max D (max C 2), fun lam n => ?_⟩
  by_cases hl : lam = 0
  · subst lam
    simp only [finalSampler, ↓reduceIte, Nat.zero_mul, Nat.zero_add, one_pow]
    exact ⟨(ZeroIndexSampler.emptySampler_timeBound 5 n).mono (by rfl) (by omega), by simp [ZeroIndexSampler.emptySampler]⟩
  by_cases hn : n = 0
  · subst n
    simp only [finalSampler, hl, ↓reduceIte, Nat.mul_zero, Nat.zero_add, one_pow]
    exact ⟨(ZeroIndexSampler.atZero_timeBound_zero _).mono (by rfl) (by omega), by simp⟩
  have hlp : 1 ≤ lam := by omega
  have hnp : 1 ≤ n := by omega
  obtain ⟨ht, hd⟩ := hC lam n hlp hnp
  have hnv : n ≤ lam * n + 1 := by nlinarith
  have hv : 2 ≤ lam * n + 1 := by nlinarith
  have hs := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n)
  have he' := esize_nat_le n
  have hcoef : (lam * n + 1) ^ C + esize n + 5 ≤
      (lam * n + 1) ^ (max D (max C 2)) := by
    have hb := hD (lam * n + 1) hv
    have hpow := Nat.pow_le_pow_right (show 1 ≤ lam * n + 1 by omega)
      (le_max_left D (max C 2))
    omega
  have hdim := Nat.pow_le_pow_right (show 1 ≤ lam * n + 1 by omega)
    (show C ≤ max D (max C 2) by omega)
  constructor
  · simp only [finalSampler, hl, ↓reduceIte]
    exact (ZeroIndexSampler.atZero_timeBound_pos _ hn ht).mono hcoef (by omega)
  · rw [finalSampler_dim_pos c hc he ℓ lam n hl hn]
    exact hd.trans hdim

end MIPRE.Introspection.PauliSampler
end
