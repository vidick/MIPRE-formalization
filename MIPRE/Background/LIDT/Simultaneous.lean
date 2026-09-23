/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Padding
import MIPRE.Background.LIDT.Adapter.Reduction

/-!
# Quantum soundness of the seeded CL test with several codewords

Blueprint `thm:lidt-cl-soundness`, through `lem:lidt-ldc` and `lem:lidt-ldc-error`: the
simultaneous contract for `r` codewords, from the single-codeword theorem
`MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL`.

The chain is three steps. A strategy for the test with `r` codewords in `m` variables is played
as one for the test with one codeword in `M = K + m` variables (`MIPRE/Background/LIDT/Padding`),
failing at most `9 (K + 1)` times as often; the single-codeword theorem applies to it; and the
extraction of `MIPRE/Background/LIDT/Extraction` reads `r`-tuples of polynomials in the original
`m` variables off its measurements, at an additive cost `M d / q` on the two point conclusions.
`clSoundness_padded` is the three steps at any `K ≥ r`.

## Choosing `M`, and the error

`M` is the least power of two at least `m + r`, so that `M ∣ q` when `q` is a power of two and
`m + r ≤ q`, and `M ≤ 2 (m + r) ≤ 4 m r`. The error is then absorbed into
`δ_sim = a (d m r)^a (ε^b + q^{-b} + 2^{-b m d})` with `b` the single-codeword exponent and `a`
a (large, explicit) constant: `M ≤ 4 m r` controls the polynomial factor, `x^b ≤ x` for `x ≥ 1`
the failure blow-up, and `M ≥ m` the exponential term. When `m + r > q` there is no room to pad,
and the bound is at least one, so any measurements do (`clSoundness`).
-/

noncomputable section

namespace MIPRE.LIDT.Simul

open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]

/-! ## The padded chain -/

/-- **The simultaneous contract, at a padding `K ≥ r`.** -/
theorem clSoundness_padded [NeZero (K + m)] (hm : m ∣ Fintype.card F)
    (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm)) (ε : ℝ) (hε : 0 ≤ ε)
    (hS : 1 - ε ≤ S.value) :
    ∃ GA : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dA) (Fin S.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dB) (Fin S.dB) ℂ),
      inconsistency (uniform (Point F m)) S.ψ (tuplePOVMA hm S) (evalTuplePOVM GB)
          ≤ deltaCL (Fintype.card F) (K + m) d (9 * (K + 1) * ε)
            + (K + m) * d / Fintype.card F ∧
        inconsistency (uniform (Point F m)) S.ψ (evalTuplePOVM GA) (tuplePOVMB hm S)
          ≤ deltaCL (Fintype.card F) (K + m) d (9 * (K + 1) * ε)
            + (K + m) * d / Fintype.card F ∧
        inconsistency (uniform Unit) S.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ deltaCL (Fintype.card F) (K + m) d (9 * (K + 1) * ε) := by
  obtain ⟨σ, hσ⟩ := exists_padded_value hm hM hr hd hK S
  have hS' : 1 - 9 * (K + 1) * ε ≤ (padded hm hM hr S σ).value := by
    have : (0 : ℝ) ≤ 9 * (K + 1) := by positivity
    nlinarith
  obtain ⟨GA', GB', h1, h2, h3⟩ := clSoundness_ldc_one_deltaCL (padded hm hM hr S σ)
    (9 * (K + 1) * ε) (by positivity) hS' (by omega) hd
  have hA : CL.pointPOVMA (padded hm hM hr S σ) = combPOVM hd (tuplePOVMA hm S) :=
    funext (pointPOVMA_padded hm hM hr hd S σ)
  have hB : CL.pointPOVMB (padded hm hM hr S σ) = combPOVM hd (tuplePOVMB hm S) :=
    funext (pointPOVMB_padded hm hM hr hd S σ)
  rw [hA] at h1
  rw [hB] at h2
  obtain ⟨e1, e2, e3⟩ := extracted_conclusions hd hr S.ψ_unit (tuplePOVMA hm S)
    (tuplePOVMB hm S) GA' GB' h1 h2 h3
  exact ⟨extractPM hd hr GA', extractPM hd hr GB', e1, e2, e3⟩

/-! ## The choice of `M` -/

/-- The least power of two at least `m + r`. -/
def padM (m r : ℕ) : ℕ := 2 ^ Nat.clog 2 (m + r)

theorem le_padM (m r : ℕ) : m + r ≤ padM m r := Nat.le_pow_clog (by norm_num) _

omit [NeZero m] in
theorem padM_le (hm1 : 1 ≤ m) (hr : 1 ≤ r) : padM m r ≤ 2 * (m + r) := by
  set c := Nat.clog 2 (m + r) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have := le_padM m r
    rw [padM, ← hc, h0] at this
    omega
  have hlt : 2 ^ (c - 1) < m + r := by
    by_contra hge
    push Not at hge
    have := (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).mpr hge
    omega
  rw [padM, ← hc]
  calc 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * (m + r) := by omega

omit [NeZero m] in
theorem padM_le_mul (hm1 : 1 ≤ m) (hr : 1 ≤ r) : padM m r ≤ 4 * (m * r) := by
  have h := padM_le hm1 hr
  nlinarith

omit [NeZero m] in
theorem padM_dvd {k : ℕ} (hmr : m + r ≤ 2 ^ k) : padM m r ∣ 2 ^ k :=
  pow_dvd_pow 2 (Nat.clog_le_of_le_pow hmr)

/-! ## The error -/

/-- The constant of `δ_sim`. -/
def simA : ℝ := 40 * clA * (4 : ℝ) ^ clA

/-- **`δ_sim`**, the error of the simultaneous contract (blueprint `thm:lidt-cl-soundness`). -/
def deltaSim (q m d r : ℕ) (ε : ℝ) : ℝ :=
  simA * ((d * m * r : ℕ) : ℝ) ^ simA *
    (ε ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)))

theorem forty_le_simA : (40 : ℝ) ≤ simA := by
  have h1 := one_le_clA
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ clA := Real.one_le_rpow (by norm_num) (by linarith)
  rw [simA]
  nlinarith

theorem clA_add_one_le_simA : clA + 1 ≤ simA := by
  have h1 := one_le_clA
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ clA := Real.one_le_rpow (by norm_num) (by linarith)
  rw [simA]
  nlinarith

/-- The polynomial factor dominates: `N^{clA + 1} ≤ N^{simA}` for `N ≥ 1`. -/
theorem rpow_le_rpow_simA {N : ℝ} (hN : 1 ≤ N) : N ^ (clA + 1) ≤ N ^ simA :=
  Real.rpow_le_rpow_of_exponent_le hN clA_add_one_le_simA

omit [NeZero m] in
/-- **Absorbing the padded chain's error** (blueprint `lem:lidt-ldc-error`). -/
theorem deltaCL_padded_le (hm1 : 1 ≤ m) (hd : 1 ≤ d) (hr : 1 ≤ r) {q M : ℕ} (hq : 1 ≤ q)
    (hmM : m ≤ M) (hMr : M ≤ 4 * (m * r)) {K : ℕ} (hKM : K + 1 ≤ M) {ε : ℝ} (hε : 0 ≤ ε) :
    deltaCL q M d (9 * (K + 1) * ε) + M * d / q ≤ deltaSim q m d r ε := by
  set N : ℝ := ((d * m * r : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb0 := clB_pos
  have hb1 := clB_lt_one
  have hA1 := one_le_clA
  set T : ℝ := ε ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)) with hT
  have hT0 : 0 ≤ T := by positivity
  -- `d M ≤ 4 N`
  have hdM : ((d * M : ℕ) : ℝ) ≤ 4 * N := by
    rw [hNdef]
    have : d * M ≤ 4 * (d * m * r) := by nlinarith
    exact_mod_cast this
  -- the failure blow-up
  have hε' : (9 * (K + 1) * ε) ^ clB ≤ 36 * N * ε ^ clB := by
    have hK' : (9 * ((K : ℝ) + 1)) ≤ 36 * N := by
      have : ((K : ℝ) + 1) ≤ M := by exact_mod_cast hKM
      have hMN : (M : ℝ) ≤ 4 * N := by
        rw [hNdef]
        have : M ≤ 4 * (d * m * r) := by nlinarith
        exact_mod_cast this
      linarith
    have h36 : (1 : ℝ) ≤ 36 * N := by linarith
    calc (9 * (K + 1) * ε) ^ clB = (9 * ((K : ℝ) + 1)) ^ clB * ε ^ clB :=
          Real.mul_rpow (by positivity) hε
      _ ≤ (36 * N) ^ clB * ε ^ clB := by gcongr
      _ ≤ (36 * N) ^ (1 : ℝ) * ε ^ clB := by
          gcongr
      _ = 36 * N * ε ^ clB := by rw [Real.rpow_one]
  -- the exponential term
  have hexp : (2 : ℝ) ^ (-(clB * M * d)) ≤ (2 : ℝ) ^ (-(clB * m * d)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (m : ℝ) ≤ M := by exact_mod_cast hmM
    have h : clB * (m : ℝ) * d ≤ clB * M * d := by gcongr
    linarith
  have hsum : (9 * (K + 1) * ε) ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * M * d))
      ≤ 36 * N * T := by
    have h1 : (q : ℝ) ^ (-clB) ≤ 36 * N * (q : ℝ) ^ (-clB) := by
      have : (0 : ℝ) ≤ (q : ℝ) ^ (-clB) := by positivity
      nlinarith
    have h2 : (2 : ℝ) ^ (-(clB * m * d)) ≤ 36 * N * (2 : ℝ) ^ (-(clB * m * d)) := by
      have : (0 : ℝ) ≤ (2 : ℝ) ^ (-(clB * m * d)) := by positivity
      nlinarith
    rw [hT]
    linarith
  -- the polynomial factor
  have hpoly : ((d * M : ℕ) : ℝ) ^ clA ≤ (4 : ℝ) ^ clA * N ^ clA := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hdM (by linarith)
  have hδ : deltaCL q M d (9 * (K + 1) * ε) ≤ clA * ((4 : ℝ) ^ clA * N ^ clA) * (36 * N * T) := by
    rw [deltaCL]
    have hc : (0 : ℝ) ≤ clA := by linarith
    calc clA * ((d * M : ℕ) : ℝ) ^ clA * ((9 * (K + 1) * ε) ^ clB + (q : ℝ) ^ (-clB)
          + (2 : ℝ) ^ (-(clB * M * d)))
        ≤ clA * ((4 : ℝ) ^ clA * N ^ clA) * ((9 * (K + 1) * ε) ^ clB + (q : ℝ) ^ (-clB)
          + (2 : ℝ) ^ (-(clB * M * d))) := by gcongr
      _ ≤ _ := by gcongr
  -- the extraction term
  have hext : (M : ℝ) * d / q ≤ 4 * N * T := by
    have hMd : (M : ℝ) * d ≤ 4 * N := by
      have := hdM
      push_cast at this
      linarith
    have hq1 : (q : ℝ)⁻¹ ≤ (q : ℝ) ^ (-clB) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hqR (by linarith)
    have hqT : (q : ℝ) ^ (-clB) ≤ T := by
      rw [hT]
      have : 0 ≤ ε ^ clB := by positivity
      have : (0 : ℝ) ≤ (2 : ℝ) ^ (-(clB * m * d)) := by positivity
      linarith
    rw [div_eq_mul_inv]
    calc (M : ℝ) * d * (q : ℝ)⁻¹ ≤ 4 * N * (q : ℝ)⁻¹ := by gcongr
      _ ≤ 4 * N * T := by gcongr; exact hq1.trans hqT
  -- assembling
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ clA := Real.one_le_rpow (by norm_num) (by linarith)
  have hNc : (1 : ℝ) ≤ N ^ clA := Real.one_le_rpow hN1 (by linarith)
  have hNpow : N ^ (clA + 1) = N ^ clA * N := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hsimA := rpow_le_rpow_simA hN1
  rw [deltaSim, ← hNdef, ← hT]
  have hkey : clA * ((4 : ℝ) ^ clA * N ^ clA) * (36 * N * T) + 4 * N * T
      ≤ simA * N ^ (clA + 1) * T := by
    rw [hNpow, simA]
    have hprod : 1 ≤ clA * (4 : ℝ) ^ clA * N ^ clA := by
      have := mul_le_mul hA1 h4 zero_le_one (by linarith)
      nlinarith
    have hNT : 0 ≤ N * T := by positivity
    nlinarith
  calc deltaCL q M d (9 * (K + 1) * ε) + M * d / q
      ≤ clA * ((4 : ℝ) ^ clA * N ^ clA) * (36 * N * T) + 4 * N * T := add_le_add hδ hext
    _ ≤ simA * N ^ (clA + 1) * T := hkey
    _ ≤ simA * N ^ simA * T := by
        have := forty_le_simA
        gcongr

omit [NeZero m] in
/-- In the trivial regime the error is at least one. -/
theorem one_le_deltaSim (hm1 : 1 ≤ m) (hd : 1 ≤ d) (hr : 1 ≤ r) {q : ℕ} (hq : 1 ≤ q)
    (hqmr : q < m + r) {ε : ℝ} (hε : 0 ≤ ε) : 1 ≤ deltaSim q m d r ε := by
  set N : ℝ := ((d * m * r : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb0 := clB_pos
  have hb1 := clB_lt_one
  have hq2N : (q : ℝ) ≤ 2 * N := by
    rw [hNdef]
    have h1 : m + r ≤ 2 * (m * r) := by nlinarith
    have h2 : m * r ≤ d * m * r := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ hd
    have : q ≤ 2 * (d * m * r) := by omega
    exact_mod_cast this
  have hqb : (q : ℝ)⁻¹ ≤ (q : ℝ) ^ (-clB) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hqR (by linarith)
  have hinv : (2 * N)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ (by linarith) hq2N
  have hNs : N ≤ N ^ simA := by
    have := Real.rpow_le_rpow_of_exponent_le hN1
      (show (1 : ℝ) ≤ simA by linarith [forty_le_simA])
    rwa [Real.rpow_one] at this
  have hs := forty_le_simA
  rw [deltaSim, ← hNdef]
  have hT : (2 * N)⁻¹ ≤ ε ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)) := by
    have : 0 ≤ ε ^ clB := by positivity
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (-(clB * m * d)) := by positivity
    linarith
  calc (1 : ℝ) ≤ 2 * N * (2 * N)⁻¹ * 1 := by
        rw [mul_inv_cancel₀ (by linarith)]; norm_num
    _ ≤ simA * N ^ simA * (2 * N)⁻¹ * 1 := by
        gcongr
        · nlinarith
    _ ≤ simA * N ^ simA * (ε ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d))) := by
        rw [mul_one]
        gcongr

/-! ## The theorem -/

/-- A measurement with a single outcome. -/
def constPM {A : Type*} [Fintype A] [DecidableEq A] {n : Type*} [Fintype n] [DecidableEq n]
    (a₀ : A) : ProjectiveMeasurement Unit A (Matrix n n ℂ) where
  M _ a := if a = a₀ then 1 else 0
  selfAdjoint _ a := by split_ifs <;> simp
  projective _ a := by split_ifs <;> simp
  normalized _ := by simp

theorem inconsistency_le_one {X A : Type*} [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency (uniform X) ψ M N ≤ 1 := by
  rw [inconsistency_eq_one_sub (sum_uniform_one X) hψ]
  have : 0 ≤ ∑ x, uniform X x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (by simp [uniform]) (Finset.sum_nonneg fun a _ =>
      bornProb_nonneg ψ ((M x).posSemidef a) ((N x).posSemidef a))
  linarith

/-- **Quantum soundness of the seeded CL test** (blueprint `thm:lidt-cl-soundness`, through
`lem:lidt-ldc`): for `q` a power of two, `m ∣ q` and `m, d, r ≥ 1`, every strategy passing the
seeded test with `r` codewords with probability at least `1 - ε` admits projective measurements
of complete `r`-tuples of polynomials on the two players' spaces, each evaluated at a uniform
point consistent with the other player's point measurement, and consistent with each other, all
with error `δ_sim(ε, q, m, d, r)`. -/
theorem clSoundness {k : ℕ} (hq : Fintype.card F = 2 ^ k) (hm : m ∣ Fintype.card F)
    (hd : 1 ≤ d) (hr : 1 ≤ r) (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm))
    (ε : ℝ) (hε : 0 ≤ ε) (hS : 1 - ε ≤ S.value) :
    ∃ GA : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dA) (Fin S.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dB) (Fin S.dB) ℂ),
      inconsistency (uniform (Point F m)) S.ψ (tuplePOVMA hm S) (evalTuplePOVM GB)
          ≤ deltaSim (Fintype.card F) m d r ε ∧
        inconsistency (uniform (Point F m)) S.ψ (evalTuplePOVM GA) (tuplePOVMB hm S)
          ≤ deltaSim (Fintype.card F) m d r ε ∧
        inconsistency (uniform Unit) S.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ deltaSim (Fintype.card F) m d r ε := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  by_cases hmr : m + r ≤ Fintype.card F
  · -- pad to `M = padM m r`
    set M := padM m r with hMdef
    have hmM : m + r ≤ M := le_padM m r
    set K := M - m with hK
    have hKm : K + m = M := by omega
    have hM : (K + m) ∣ Fintype.card F := by
      rw [hKm, hq]; exact padM_dvd (hq ▸ hmr)
    have : NeZero (K + m) := ⟨by omega⟩
    obtain ⟨GA, GB, h1, h2, h3⟩ := clSoundness_padded (K := K) hm hM (by omega) (by omega) hd S
      ε hε hS
    have hle := deltaCL_padded_le (K := K) hm1 hd hr hq1 (M := K + m) (by omega)
      (by rw [hKm]; exact padM_le_mul hm1 hr) (by omega) hε
    have hext : (0 : ℝ) ≤ ((K + m : ℕ) : ℝ) * d / Fintype.card F := by positivity
    push_cast at hle hext
    exact ⟨GA, GB, h1.trans hle, h2.trans hle, h3.trans (by linarith)⟩
  · -- no room to pad: the bound is at least one
    push Not at hmr
    have h1 := one_le_deltaSim hm1 hd hr hq1 hmr hε
    refine ⟨constPM 0, constPM 0, ?_, ?_, ?_⟩ <;>
      exact (inconsistency_le_one S.ψ_unit _ _).trans h1

end MIPRE.LIDT.Simul

end
