/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundExtract

/-!
# Soundness of answer reduction: the error assembly

Piece AR-5f of `planning/answer-reduction.md` (`lem:ar-error-assembly`), its arithmetic half: the
combined error of the decoded strategy's analysis, at a typed failure `θ ≤ Kε`, is at most

  `39204 K Z^{3A} ε^{clB} + (Q + 1)^{-2} + 22 Z^{3A} 2^{-clB Q}`,     `Z = 8 (Q + 1) m'`

(`errE_le`), where `A = ⌈simA⌉` and `Q ≤ m` is the question length, when the field is large:
`Z^{fieldExp} ≤ q` with `fieldExp = 40000 (3A + 4)`. The two prefactors `simA (d m r)^simA` of the
two extractions are at most `Z^{3A}` (`simA_mul_rpow_le`), and the field hypothesis puts
`q^{clB}` above `Z^{3A + 4}` (`rpow_clB_ge`), which kills both field terms.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Real MIPRE.LIDT

/-! ## The constants -/

/-- `simA`, rounded up to a natural number. -/
irreducible_def simAN : ℕ := ⌈Simul.simA⌉₊

theorem simA_le_simAN : Simul.simA ≤ simAN := by rw [simAN_def]; exact Nat.le_ceil _

theorem one_le_simAN : 1 ≤ simAN := by
  have h := Simul.forty_le_simA
  have := simA_le_simAN
  exact_mod_cast (show (1 : ℝ) ≤ simAN by linarith)

/-- **The exponent of the field-size hypothesis**: `q ≥ Z^{fieldExp}` puts `q^{clB}` above
`Z^{3A + 4}`. -/
irreducible_def fieldExp : ℕ := 40000 * (3 * simAN + 4)

/-! ## The prefactor and the field -/

/-- **The prefactor of `δ_sim`** is at most `Z^{3A}` when its argument is at most `Z²`. -/
theorem simA_mul_rpow_le {M Z : ℕ} (hM : 1 ≤ M) (hZ : 2 ≤ Z) (h : M ≤ Z ^ 2) :
    Simul.simA * (M : ℝ) ^ Simul.simA ≤ (Z : ℝ) ^ (3 * simAN) := by
  have hA := simA_le_simAN
  have hA0 : 0 ≤ Simul.simA := by have := Simul.forty_le_simA; linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast (by omega : 1 ≤ Z)
  have h1 : (M : ℝ) ^ Simul.simA ≤ (M : ℝ) ^ (simAN : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hM1 hA
  rw [Real.rpow_natCast] at h1
  have h2 : (M : ℝ) ^ simAN ≤ ((Z : ℝ) ^ 2) ^ simAN :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) _
  have h3 : (simAN : ℝ) ≤ (Z : ℝ) ^ simAN := by
    have h4 : simAN < 2 ^ simAN := Nat.lt_two_pow_self
    have h5 : 2 ^ simAN ≤ Z ^ simAN := Nat.pow_le_pow_left hZ _
    exact_mod_cast (h4.trans_le h5).le
  have hMp : 0 ≤ (M : ℝ) ^ Simul.simA := by positivity
  calc Simul.simA * (M : ℝ) ^ Simul.simA ≤ (simAN : ℝ) * ((Z : ℝ) ^ 2) ^ simAN :=
        mul_le_mul hA (h1.trans h2) hMp (by positivity)
    _ ≤ (Z : ℝ) ^ simAN * ((Z : ℝ) ^ 2) ^ simAN :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (Z : ℝ) ^ (3 * simAN) := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- **A large field**: `Z^{fieldExp} ≤ q` puts `q^{clB}` above `Z^{3A + 4}`. -/
theorem rpow_clB_ge {q Z : ℕ} (hq : Z ^ fieldExp ≤ q) :
    (Z : ℝ) ^ (3 * simAN + 4) ≤ (q : ℝ) ^ clB := by
  have h1 : ((Z ^ fieldExp : ℕ) : ℝ) ^ clB ≤ (q : ℝ) ^ clB :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hq) clB_pos.le
  refine le_trans (le_of_eq ?_) h1
  rw [Nat.cast_pow, ← Real.rpow_natCast (Z : ℝ) fieldExp, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast (Z : ℝ) (3 * simAN + 4)]
  congr 1
  rw [fieldExp_def, clB]
  push_cast
  ring

/-! ## The combined error -/

/-- **The combined error**, at a typed failure `θ`, over the field of size `q`: the two
extractions' errors, the typed failure, and the Schwartz--Zippel term. -/
def errE (q m m' : ℕ) (θ : ℝ) : ℝ :=
  11 * (Simul.deltaSim q m' 7 (m' + 6) (324 * θ) + 2916 * θ + Simul.deltaSim q m 7 1 (324 * θ))
    + (m' : ℝ) * 7 / q

/-- One extraction's error, term by term. -/
theorem deltaSim_le_of {q m d r : ℕ} {x x' Pw β E : ℝ} (hx0 : 0 ≤ x)
    (hP : Simul.simA * ((d * m * r : ℕ) : ℝ) ^ Simul.simA ≤ Pw) (hx : x ^ clB ≤ x')
    (hb : Pw * (q : ℝ) ^ (-clB) ≤ β) (hc : (2 : ℝ) ^ (-(clB * m * d)) ≤ E) :
    Simul.deltaSim q m d r x ≤ Pw * x' + β + Pw * E := by
  have hA0 : 0 ≤ Simul.simA := by have := Simul.forty_le_simA; linarith
  have hP0 : 0 ≤ Simul.simA * ((d * m * r : ℕ) : ℝ) ^ Simul.simA := by positivity
  have hPw : 0 ≤ Pw := hP0.trans hP
  have ha : 0 ≤ x ^ clB := Real.rpow_nonneg hx0 _
  have hb0 : 0 ≤ (q : ℝ) ^ (-clB) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc0 : 0 ≤ (2 : ℝ) ^ (-(clB * m * d)) := Real.rpow_nonneg (by norm_num) _
  unfold Simul.deltaSim
  calc Simul.simA * ((d * m * r : ℕ) : ℝ) ^ Simul.simA
        * (x ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d)))
      ≤ Pw * (x ^ clB + (q : ℝ) ^ (-clB) + (2 : ℝ) ^ (-(clB * m * d))) :=
        mul_le_mul_of_nonneg_right hP (by positivity)
    _ = Pw * x ^ clB + Pw * (q : ℝ) ^ (-clB) + Pw * (2 : ℝ) ^ (-(clB * m * d)) := by ring
    _ ≤ Pw * x' + β + Pw * E :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx hPw) hb)
          (mul_le_mul_of_nonneg_left hc hPw)

/-- **The combined error at a typed failure `θ ≤ Kε`**, over a large field. -/
theorem errE_le {q m m' Q : ℕ} (hm : 1 ≤ m) (hmm : m ≤ m') (hQm : Q ≤ m)
    (hq : (8 * ((Q + 1) * m')) ^ fieldExp ≤ q) {θ ε K : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ K * ε)
    (hK : 1 ≤ K) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    errE q m m' θ ≤ 39204 * K * ((8 * ((Q + 1) * m') : ℕ) : ℝ) ^ (3 * simAN) * ε ^ clB
      + 1 / ((Q : ℝ) + 1) ^ 2
      + 22 * ((8 * ((Q + 1) * m') : ℕ) : ℝ) ^ (3 * simAN) * (2 : ℝ) ^ (-(clB * Q)) := by
  set Z : ℕ := 8 * ((Q + 1) * m') with hZ
  have hm' : 1 ≤ m' := hm.trans hmm
  have hZ2 : 2 ≤ Z := by rw [hZ]; nlinarith
  have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast (by omega : 1 ≤ Z)
  set Pw : ℝ := (Z : ℝ) ^ (3 * simAN) with hPw
  have hPw1 : 1 ≤ Pw := one_le_pow₀ hZ1
  have hq1 : 1 ≤ q := (Nat.one_le_pow _ _ (by omega)).trans hq
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  set F : ℝ := (q : ℝ) ^ clB with hFdef
  have hF := rpow_clB_ge hq
  have hZ4 : (0 : ℝ) < (Z : ℝ) ^ 4 := by positivity
  have hFpos : 0 < F := lt_of_lt_of_le (by positivity) hF
  have hFq : F ≤ q := by
    have := Real.rpow_le_rpow_of_exponent_le hq1' clB_lt_one.le
    rwa [Real.rpow_one] at this
  have hPF : Pw * (q : ℝ) ^ (-clB) ≤ 1 / (Z : ℝ) ^ 4 := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← hFdef, ← div_eq_mul_inv, div_le_div_iff₀ hFpos hZ4,
      one_mul, hPw, ← pow_add]
    exact hF
  -- the two prefactors
  have hQm' : m' ≤ (Q + 1) * m' := Nat.le_mul_of_pos_left _ (by omega)
  have hM6 : 7 * m' * (m' + 6) ≤ Z ^ 2 := by
    have h1 : 7 * m' * (m' + 6) ≤ 7 * m' * (7 * m') := Nat.mul_le_mul_left _ (by omega)
    have h2 : m' * m' ≤ ((Q + 1) * m') * ((Q + 1) * m') := Nat.mul_le_mul hQm' hQm'
    rw [hZ]
    nlinarith
  have hP6 : Simul.simA * ((7 * m' * (m' + 6) : ℕ) : ℝ) ^ Simul.simA ≤ Pw :=
    simA_mul_rpow_le (by nlinarith) hZ2 hM6
  have hP1 : Simul.simA * ((7 * m * 1 : ℕ) : ℝ) ^ Simul.simA ≤ Pw :=
    simA_mul_rpow_le (by omega) hZ2 (by
      have h1 : 7 * m * 1 ≤ 7 * m' * (m' + 6) := by nlinarith
      exact h1.trans hM6)
  -- the typed failure
  have hεb : ε ≤ ε ^ clB := Real.self_le_rpow_of_le_one hε0 hε1 clB_lt_one.le
  have hεb0 : 0 ≤ ε ^ clB := Real.rpow_nonneg hε0 _
  have hx : (324 * θ) ^ clB ≤ 324 * K * ε ^ clB := by
    have h1 : (324 * θ) ^ clB ≤ (324 * K * ε) ^ clB :=
      Real.rpow_le_rpow (by positivity) (by linarith) clB_pos.le
    rw [Real.mul_rpow (by positivity) hε0] at h1
    have h2 : (324 * K) ^ clB ≤ 324 * K := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 324 * K)
        clB_lt_one.le
      rwa [Real.rpow_one] at this
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hεb0)
  have hθb : θ ≤ K * ε ^ clB := hθ.trans (mul_le_mul_of_nonneg_left hεb (by linarith))
  -- the low-degree test's exponential term
  set E : ℝ := (2 : ℝ) ^ (-(clB * Q)) with hE
  have hE6 : (2 : ℝ) ^ (-(clB * m' * (7 : ℕ))) ≤ E := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hQ' : (Q : ℝ) ≤ m' * 7 := by exact_mod_cast (by omega : Q ≤ m' * 7)
    have := clB_pos
    simp only [Nat.cast_ofNat]
    nlinarith
  have hE1 : (2 : ℝ) ^ (-(clB * m * (7 : ℕ))) ≤ E := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hQ' : (Q : ℝ) ≤ m * 7 := by exact_mod_cast (by omega : Q ≤ m * 7)
    have := clB_pos
    simp only [Nat.cast_ofNat]
    nlinarith
  have e6 := deltaSim_le_of (r := m' + 6) (by positivity) hP6 hx hPF hE6
  have e1 := deltaSim_le_of (r := 1) (by positivity) hP1 hx hPF hE1
  -- the Schwartz--Zippel term
  have hSZ : (m' : ℝ) * 7 / q ≤ 7 * m' / (Z : ℝ) ^ 4 := by
    have hZF : (Z : ℝ) ^ 4 ≤ q := by
      have h4 : (Z : ℝ) ^ 4 ≤ (Z : ℝ) ^ (3 * simAN + 4) :=
        pow_le_pow_right₀ hZ1 (by omega)
      linarith
    rw [div_le_div_iff₀ (by positivity) hZ4]
    have : (0 : ℝ) ≤ m' * 7 := by positivity
    nlinarith
  -- the powers of `Z`
  have hZe : (Z : ℝ) = 8 * ((Q + 1) * m') := by rw [hZ]; push_cast; ring
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hm'1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'
  have hsmall : 22 / (Z : ℝ) ^ 4 + 7 * m' / (Z : ℝ) ^ 4 ≤ 1 / ((Q : ℝ) + 1) ^ 2 := by
    rw [← add_div, div_le_div_iff₀ hZ4 (by positivity), one_mul, hZe]
    have h1 : (1 : ℝ) ≤ ((Q : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    have h2 : (m' : ℝ) ≤ (m' : ℝ) ^ 4 := le_self_pow₀ hm'1 (by norm_num)
    have h3 : (1 : ℝ) ≤ (m' : ℝ) ^ 4 := one_le_pow₀ hm'1
    have h4 : (1 : ℝ) ≤ ((Q : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
    have h5 : ((Q : ℝ) + 1) ^ 2 ≤ ((Q : ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : (8 * (((Q : ℝ) + 1) * m')) ^ 4 = 4096 * ((Q : ℝ) + 1) ^ 4 * (m' : ℝ) ^ 4 := by ring
    rw [this]
    nlinarith
  have hE0 : 0 ≤ E := Real.rpow_nonneg (by norm_num) _
  have hKP : K * ε ^ clB ≤ K * Pw * ε ^ clB := by
    have : K * ε ^ clB * 1 ≤ K * ε ^ clB * Pw :=
      mul_le_mul_of_nonneg_left hPw1 (mul_nonneg (by linarith) hεb0)
    linarith
  unfold errE
  linear_combination 11 * e6 + 11 * e1 + 32076 * hθb + 32076 * hKP + hSZ + hsmall

end MIPRE.AnswerReduction

end
