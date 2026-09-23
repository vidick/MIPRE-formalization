/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliarySamplingCorrect

/-! # The common source clock covers legal factor and linear queries -/

noncomputable section
namespace MIPRE.Introspection.AuxiliarySource
open Cost CL.Detyping

theorem linear_query_size_le (R : ℕ) (hR : 1 ≤ R) (w : Player) (j : ℕ) (u y : BitStr)
    (hj : Nat.size j ≤ R) (hu : u.length ≤ R) (hy : y.length ≤ R) :
    esize (CL.Sampler.Query.linear w j u y) + 1 ≤ 64 * R := by
  have hw : esize w ≤ 3 := by cases w <;> decide
  have hjb := esize_nat_le j
  have hub := esize_bitStr_le u
  have hyb := esize_bitStr_le y
  change esize ((2 : ℕ), w, j, u, y) + 1 ≤ _
  simp only [esize_prod]
  have htwo : esize (2 : ℕ) = 7 := by decide
  rw [htwo]
  omega

theorem factor_query_size_le (R : ℕ) (hR : 1 ≤ R) (w : Player) (j : ℕ) (u : BitStr)
    (hj : Nat.size j ≤ R) (hu : u.length ≤ R) :
    esize (CL.Sampler.Query.factor w j u) + 1 ≤ 64 * R := by
  have hw : esize w ≤ 3 := by cases w <;> decide
  have hjb := esize_nat_le j
  have hub := esize_bitStr_le u
  change esize ((3 : ℕ), w, j, u, ([] : BitStr)) + 1 ≤ _
  simp only [esize_prod]
  have hthree : esize (3 : ℕ) = 9 := by decide
  have hnil : esize ([] : BitStr) = 1 := rfl
  rw [hthree, hnil]
  omega

theorem query_cost_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (b : ℕ)
    (hb : b ≤ 64 * (2 ^ n) ^ lam) : (2 ^ n) ^ lam * b ^ lam ≤ ansBound 5 lam n := by
  let u := lam * n
  have hlu : lam ≤ u := by dsimp [u]; nlinarith
  have hu : 1 ≤ u := hl.trans hlu
  have hR : (2 ^ n) ^ lam = 2 ^ u := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have hs : b ≤ 2 ^ (6 + u) := by simpa [hR, pow_add] using hb
  have he : u + (6 + u) * lam ≤ (u + 1) ^ 5 := by
    have hc : 8 ≤ (u + 1) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc u + (6 + u) * lam ≤ u + (6 + u) * u := by gcongr
      _ ≤ 8 * (u + 1) ^ 2 := by nlinarith
      _ ≤ (u + 1) ^ 3 * (u + 1) ^ 2 := Nat.mul_le_mul_right _ hc
      _ = (u + 1) ^ 5 := by ring
  calc (2 ^ n) ^ lam * b ^ lam ≤ 2 ^ u * (2 ^ (6 + u)) ^ lam := by rw [hR]; gcongr
    _ = 2 ^ (u + (6 + u) * lam) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((u + 1) ^ 5) := Nat.pow_le_pow_right (by decide) he

theorem bounded_query_result {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (q : CL.Sampler.Query) (result : Data)
    (hq : esize q + 1 ≤ 64 * (2 ^ n) ^ lam)
    (hr : ∃ t, V.sampler.prog.Runs (encode (2 ^ n, q)) result t) :
    clockedResult V.sampler.prog (encode (2 ^ n, q)) (ansBound 5 lam n) =
      .cons (encode true) result := by
  obtain ⟨r, t, ht, hr'⟩ := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).2.1 (encode q)
  obtain ⟨tu, hu⟩ := hr
  rw [ClockProgram.clockedResult_eq_iff]
  exact ⟨t, ht.trans (query_cost_le (by have := hV.two_le; omega) hn _ hq),
    (hr'.deterministic hu).1 ▸ hr'⟩

theorem bounded_linear_result {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (w : Player) (j : ℕ) (u y : BitStr) (hj : 1 ≤ j) (hjℓ : j ≤ ℓ)
    (hjR : Nat.size j ≤ (2 ^ n) ^ lam)
    (hu : ∃ x, u = CL.toBits (((V.sampler.cl (2 ^ n) w).truncate (j - 1)).eval x))
    (hy : y.length = V.sampler.dim (2 ^ n)) :
    clockedResult V.sampler.prog (encode (2 ^ n, CL.Sampler.Query.linear w j u y))
      (ansBound 5 lam n) = .cons (encode true) (encode (CL.toBits
        ((V.sampler.cl (2 ^ n) w).mapOfPrefix (j - 1)
          (CL.ofBits (V.sampler.dim (2 ^ n)) u) (CL.ofBits (V.sampler.dim (2 ^ n)) y)))) := by
  have hs := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).1
  have hul : u.length = V.sampler.dim (2 ^ n) := by
    obtain ⟨x, rfl⟩ := hu
    exact CL.length_toBits _
  apply bounded_query_result V hV hn
  · exact linear_query_size_le _ (Nat.one_le_pow _ _ (by positivity)) w j u y hjR (hul ▸ hs) (hy ▸ hs)
  · exact V.sampler.runs_linear _ w j u y hj hjℓ hu hy

theorem bounded_factor_result {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (w : Player) (j : ℕ) (u : BitStr) (hj : 1 ≤ j) (hjℓ : j ≤ ℓ)
    (hjR : Nat.size j ≤ (2 ^ n) ^ lam)
    (hu : ∃ x, u = CL.toBits (((V.sampler.cl (2 ^ n) w).truncate (j - 1)).eval x)) :
    clockedResult V.sampler.prog (encode (2 ^ n, CL.Sampler.Query.factor w j u))
      (ansBound 5 lam n) = .cons (encode true) (encode (CL.indicatorBits
        ((V.sampler.cl (2 ^ n) w).factorOfPrefix (j - 1)
          (CL.ofBits (V.sampler.dim (2 ^ n)) u)))) := by
  have hs := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).1
  have hul : u.length = V.sampler.dim (2 ^ n) := by
    obtain ⟨x, rfl⟩ := hu
    exact CL.length_toBits _
  apply bounded_query_result V hV hn
  · exact factor_query_size_le _ (Nat.one_le_pow _ _ (by positivity)) w j u hjR (hul ▸ hs)
  · exact V.sampler.runs_factor _ w j u hj hjℓ hu

end MIPRE.Introspection.AuxiliarySource
end
