/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundExtract
import MIPRE.Foundations.Cost.Growth

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

/-! ## The threshold -/

/-- **Past a threshold, `2^{clB Q}` beats every polynomial in `Q`**, and `Q ≥ 8064`. -/
theorem exists_threshold_clB (c p : ℕ) : ∃ Q0 : ℕ, ∀ Q : ℕ, Q0 ≤ Q →
    8064 ≤ Q ∧ 177408 * c * (Q : ℝ) ^ (p + 1) ≤ (2 : ℝ) ^ (clB * Q) := by
  set A' := 177408 * c * 80000 ^ (p + 1) with hA'
  refine ⟨40000 * (A' * (p + 2) ^ (p + 2) + 1) + 8064, fun Q hQ => ⟨by omega, ?_⟩⟩
  set s := Q / 40000 with hs
  have hs1 : A' * (p + 2) ^ (p + 2) + 1 ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have hQs : Q ≤ 80000 * s := by
    have := Nat.lt_mul_div_succ Q (show 0 < 40000 by norm_num)
    rw [← hs] at this
    omega
  have hnat : 177408 * c * Q ^ (p + 1) ≤ 2 ^ s := by
    have h1 : Q ^ (p + 1) ≤ 80000 ^ (p + 1) * s ^ (p + 1) := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left hQs _
    have h2 := Cost.mul_pow_le_two_pow A' (p + 1) s (by
      show A' * (p + 2) ^ (p + 2) ≤ s
      omega)
    calc 177408 * c * Q ^ (p + 1) ≤ 177408 * c * (80000 ^ (p + 1) * s ^ (p + 1)) :=
          Nat.mul_le_mul_left _ h1
      _ = A' * s ^ (p + 1) := by rw [hA']; ring
      _ ≤ 2 ^ s := h2
  have hreal : 177408 * c * (Q : ℝ) ^ (p + 1) ≤ (2 : ℝ) ^ (s : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast hnat
  refine hreal.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  have h40 : 40000 * s ≤ Q := by rw [hs]; exact Nat.mul_div_le Q 40000
  have : (40000 : ℝ) * s ≤ Q := by exact_mod_cast h40
  rw [clB]
  linarith

/-! ## The soundness loss -/

/-- **The exponent `a` of the soundness loss**, from the constants `c, p` of the polynomial bound
`Z^{3A} ≤ c Q^p σ^p` and the detyping factor `K`. -/
def aOf (c p K : ℕ) : ℕ := 4032 * 39204 * K * c + 2 * p + 1

theorem one_le_aOf (c p K : ℕ) : 1 ≤ aOf c p K := by unfold aOf; omega

/-- **The error is below the soundness loss**: with `N = λn`, `Q` between `N^μ` and `N^{2μ}` and
past the threshold, the bound of `errE_le` gives `24 √(7 e) ≤ σ^a (N^{μa} ε^{clB/2} +
N^{-μ clB/2})`. -/
theorem sqrt_le_delta {N μ σ Q c p K : ℕ} (hN : 2 ≤ N) (hμ : 1 ≤ μ) (hσ : 1 ≤ σ)
    (hQN : Q ≤ N ^ (2 * μ)) (hNQ : N ^ μ ≤ Q) (hQ8 : 8064 ≤ Q)
    (hc : 177408 * c * (Q : ℝ) ^ (p + 1) ≤ (2 : ℝ) ^ (clB * Q)) {G e ε : ℝ}
    (hG : G ≤ c * (Q : ℝ) ^ p * (σ : ℝ) ^ p) (hε0 : 0 ≤ ε)
    (he : e ≤ 39204 * K * G * ε ^ clB + 1 / ((Q : ℝ) + 1) ^ 2
      + 22 * G * (2 : ℝ) ^ (-(clB * Q))) :
    24 * √(7 * e) ≤ (σ : ℝ) ^ (aOf c p K : ℝ) *
      ((N : ℝ) ^ ((μ : ℝ) * aOf c p K) * ε ^ (clB / 2) + (N : ℝ) ^ (-((μ : ℝ) * (clB / 2)))) := by
  set a := aOf c p K with ha
  set D := 4032 * 39204 * K * c with hD
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hS : (σ : ℝ) ^ (a : ℝ) = (σ : ℝ) ^ a := Real.rpow_natCast _ _
  have hM : (N : ℝ) ^ ((μ : ℝ) * a) = (N : ℝ) ^ (μ * a) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [hS, hM]
  set S := (σ : ℝ) ^ a with hSdef
  set M := (N : ℝ) ^ (μ * a) with hMdef
  set w := ε ^ (clB / 2) with hwdef
  set v := (N : ℝ) ^ (-((μ : ℝ) * (clB / 2))) with hvdef
  have hw2 : w ^ 2 = ε ^ clB := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hε0]; norm_num
  have hv2 : v ^ 2 = (N : ℝ) ^ (-((μ : ℝ) * clB)) := by
    rw [hvdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
  have hS1 : 1 ≤ S := one_le_pow₀ hσ1
  have hw0 : 0 ≤ w := Real.rpow_nonneg hε0 _
  have hv0 : 0 ≤ v := Real.rpow_nonneg (by positivity) _
  have hM0 : 0 ≤ M := by positivity
  have hεb : 0 ≤ ε ^ clB := Real.rpow_nonneg hε0 _
  -- `v² ≥ 1/Q`
  have hvQ : 1 / (Q : ℝ) ≤ v ^ 2 := by
    rw [hv2, Real.rpow_neg (by positivity), one_div]
    refine inv_anti₀ (by positivity) ?_
    have hμ1 : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
    have h1 : (N : ℝ) ^ ((μ : ℝ) * clB) ≤ (N : ℝ) ^ (μ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1
        (mul_le_of_le_one_right (by positivity) clB_lt_one.le)
    rw [Real.rpow_natCast] at h1
    exact h1.trans (by exact_mod_cast hNQ)
  -- the polynomial part, in `ℕ`
  have h3 : σ ^ p ≤ (σ ^ a) ^ 2 := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right hσ (by rw [ha, aOf]; omega)
  have hnat : D * Q ^ p * σ ^ p ≤ (N ^ (μ * a)) ^ 2 * (σ ^ a) ^ 2 := by
    have h1 : D ≤ N ^ (μ * D) := Nat.lt_two_pow_self.le.trans
      ((Nat.pow_le_pow_left hN _).trans (Nat.pow_le_pow_right (by omega)
        (Nat.le_mul_of_pos_left _ hμ)))
    have h2 : Q ^ p ≤ N ^ (2 * μ * p) := by rw [pow_mul]; exact Nat.pow_le_pow_left hQN _
    have h4 : N ^ (μ * D) * N ^ (2 * μ * p) ≤ (N ^ (μ * a)) ^ 2 := by
      rw [← pow_add, ← pow_mul]
      refine Nat.pow_le_pow_right (by omega) ?_
      have : μ * (D + 2 * p + 1) * 2 = μ * D + 2 * μ * p + (μ * D + 2 * μ * p + 2 * μ) := by
        ring
      rw [ha, aOf, ← hD, this]
      omega
    calc D * Q ^ p * σ ^ p ≤ N ^ (μ * D) * N ^ (2 * μ * p) * (σ ^ a) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ ≤ (N ^ (μ * a)) ^ 2 * (σ ^ a) ^ 2 := Nat.mul_le_mul_right _ h4
  have hreal : (D : ℝ) * (Q : ℝ) ^ p * (σ : ℝ) ^ p ≤ M ^ 2 * S ^ 2 := by
    rw [hMdef, hSdef]; exact_mod_cast hnat
  have h3r : (σ : ℝ) ^ p ≤ S ^ 2 := by rw [hSdef]; exact_mod_cast h3
  -- (i) the main term
  have hi : 4032 * (39204 * K * G * ε ^ clB) ≤ S ^ 2 * M ^ 2 * ε ^ clB := by
    have hK : (0 : ℝ) ≤ 4032 * 39204 * K := by positivity
    have h1 : 4032 * 39204 * (K : ℝ) * G ≤ 4032 * 39204 * K * (c * (Q : ℝ) ^ p * (σ : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left hG hK
    have h2 : 4032 * 39204 * (K : ℝ) * (c * (Q : ℝ) ^ p * (σ : ℝ) ^ p)
        = (D : ℝ) * (Q : ℝ) ^ p * (σ : ℝ) ^ p := by rw [hD]; push_cast; ring
    have h5 : 4032 * 39204 * (K : ℝ) * G ≤ S ^ 2 * M ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_right h5 hεb
    linear_combination this
  -- (ii) the field terms
  have hii : 4032 * (1 / ((Q : ℝ) + 1) ^ 2) ≤ 1 / 2 * (1 / (Q : ℝ)) := by
    have hQ8r : (8064 : ℝ) ≤ Q := by exact_mod_cast hQ8
    rw [mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hQ8r]
  -- (iii) the exponential term
  have hiii : 4032 * (22 * G * (2 : ℝ) ^ (-(clB * Q))) ≤ 1 / 2 * (1 / (Q : ℝ)) * S ^ 2 := by
    set T2 := (2 : ℝ) ^ (clB * Q) with hT2
    have hT2pos : 0 < T2 := by positivity
    rw [Real.rpow_neg (by norm_num), ← hT2]
    have hG' : G * T2⁻¹ ≤ c * (Q : ℝ) ^ p * (σ : ℝ) ^ p * T2⁻¹ :=
      mul_le_mul_of_nonneg_right hG (by positivity)
    have hkey : 177408 * c * (Q : ℝ) ^ (p + 1) * (σ : ℝ) ^ p ≤ T2 * S ^ 2 :=
      mul_le_mul hc h3r (by positivity) hT2pos.le
    have hgoal : 4032 * (22 * (c * (Q : ℝ) ^ p * (σ : ℝ) ^ p * T2⁻¹))
        ≤ 1 / 2 * (1 / (Q : ℝ)) * S ^ 2 := by
      have e1 : 4032 * (22 * (c * (Q : ℝ) ^ p * (σ : ℝ) ^ p * T2⁻¹))
          = 177408 * c * (Q : ℝ) ^ (p + 1) * (σ : ℝ) ^ p / (2 * Q * T2) := by
        field_simp; ring
      rw [e1, div_le_iff₀ (by positivity)]
      have e2 : 1 / 2 * (1 / (Q : ℝ)) * S ^ 2 * (2 * Q * T2) = T2 * S ^ 2 := by
        field_simp
      rw [e2]
      exact hkey
    have : 4032 * (22 * G * T2⁻¹) ≤ 4032 * (22 * (c * (Q : ℝ) ^ p * (σ : ℝ) ^ p * T2⁻¹)) := by
      linear_combination (4032 * 22 : ℝ) * hG'
    exact this.trans hgoal
  -- assembling
  have htot : 4032 * e ≤ (S * (M * w + v)) ^ 2 := by
    have h1 : 4032 * e ≤ S ^ 2 * M ^ 2 * ε ^ clB + S ^ 2 * v ^ 2 := by
      have hvQ' : 1 / 2 * (1 / (Q : ℝ)) * S ^ 2 ≤ 1 / 2 * v ^ 2 * S ^ 2 := by
        have := mul_le_mul_of_nonneg_right hvQ (by positivity : (0 : ℝ) ≤ 1 / 2 * S ^ 2)
        linear_combination this
      have hS2 : 1 / 2 * (1 / (Q : ℝ)) ≤ 1 / 2 * (1 / (Q : ℝ)) * S ^ 2 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hS1)
      linear_combination 4032 * he + hi + hii + hiii + hS2 + 2 * hvQ'
    have h2 : S ^ 2 * M ^ 2 * ε ^ clB + S ^ 2 * v ^ 2 ≤ (S * (M * w + v)) ^ 2 := by
      rw [← hw2]
      have : 0 ≤ S ^ 2 * (2 * M * w * v) := by positivity
      linear_combination this
    linarith
  have hsq : 24 * √(7 * e) = √(4032 * e) := by
    rw [show (4032 : ℝ) * e = 24 ^ 2 * (7 * e) by ring]
    conv_rhs => rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 24 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 24)]
  rw [hsq]
  calc √(4032 * e) ≤ √((S * (M * w + v)) ^ 2) := Real.sqrt_le_sqrt htot
    _ = S * (M * w + v) := Real.sqrt_sq (by positivity)

end MIPRE.AnswerReduction

end
