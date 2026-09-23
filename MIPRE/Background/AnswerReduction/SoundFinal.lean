/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundPcp
import MIPRE.Background.AnswerReduction.SoundSetup
import MIPRE.Background.AnswerReduction.SoundError

/-!
# Soundness of answer reduction

Piece AR-5f of `planning/answer-reduction.md`, concluded (`lem:ar-soundness`,
`lem:ar-error-assembly`): the `soundness` clause of the `AnswerReduction` contract for
`arVerifier` (`arVerifier_soundness`), under a new hypothesis on the PCP decider, `FieldLarge`:
for every exponent `e`, its field eventually has at least `(8 (Q + 1) m')^e` elements.

The chain: a strategy of value above `1 - ε` for the answer-reduced verifier at the answer cut
(the output verifier rejects longer answers, so its value at any larger bound is the same) gives a
typed strategy of failure `θ ≤ 16^{54} ε` (`typedStrategy_value_ge`), which gives
`val*(𝒱_n) ≥ 1 - 24 √(7 errE(θ))` (`valStar_ge_of_typedGame`). The combined error is bounded over
the large field by `errE_le`, the size of the parameters by `ParamsBound` (`z_le`), and the result
compared with `δ(ε, n)` by `sqrt_le_delta`, past a threshold on `n` (`exists_threshold_clB`). At
`μ = 0` or `ε ≥ 1` the loss is at least `1` and there is nothing to prove.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp Cost

/-- **The PCP's field is eventually large**: for every exponent `e`, past a threshold on `Q`, at
least `(8 (Q + 1) m')^e` elements. At `e = fieldExp` the low-degree test's field term `q^{-clB}`
then kills its prefactor, a polynomial of degree about `2 simA` in `m'`. `thm:pcp-decider` does
not carry the paper's lower bound on `q` (`eq:pcp-q-choice`); this is it, as a hypothesis on the
decider, like `ParamsBound` and `ShoupField`. It asks for no particular constant, so a field of
`2^{O(log² (Q m'))}` elements satisfies it. -/
def FieldLarge (PD : PcpDecider) : Prop :=
  ∀ e : ℕ, ∃ Q₀ : ℕ, ∀ n T Q σ, Q₀ ≤ Q →
    (8 * ((Q + 1) * (PD.params n T Q σ).m')) ^ e ≤ (PD.params n T Q σ).q

/-! ## The size of the parameters -/

section Params

variable (PD : PcpDecider) (R : Polynomial ℕ)

/-- The coefficient sum of `R`. -/
def coeffSum : ℕ := ∑ i ∈ Finset.range (R.natDegree + 1), R.coeff i

/-- The constant of the bound on `Z = 8 (Q + 1) m'`. -/
def zC : ℕ := 160 * (coeffSum R + 1) * 10 ^ R.natDegree

/-- The exponent of the bound on `Z`. -/
def zE : ℕ := 2 * R.natDegree + 1

theorem one_le_arQ {lam mu n : ℕ} : 1 ≤ arQ lam mu n := Nat.one_le_pow _ _ (by omega)

/-- **The parameters are polynomial**: `Z = 8 (Q + 1) m' ≤ zC (Q σ)^{zE}`. -/
theorem z_le (hR : ParamsBound PD R) {lam mu sigma n : ℕ} (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hs : 1 ≤ sigma) (hn : 1 ≤ n) :
    8 * ((arQ lam mu n + 1) * (arPar PD lam mu sigma n).m')
      ≤ zC R * (arQ lam mu n * sigma) ^ zE R := by
  set Q := arQ lam mu n with hQ
  set P := arPar PD lam mu sigma n with hP
  set D := R.natDegree with hD
  set A := coeffSum R with hA
  have hQ1 : 1 ≤ Q := one_le_arQ
  -- `n, μ + 1 ≤ Q`
  have hnQ : n + 1 ≤ Q := by
    have h1 : lam * n + 1 ≤ (lam * n + 1) ^ mu := Nat.le_self_pow (by omega) _
    have h2 : n ≤ lam * n := Nat.le_mul_of_pos_left _ hlam
    rw [hQ, arQ]; omega
  have hμQ : mu + 1 ≤ Q := by
    have h1 : mu < 2 ^ mu := Nat.lt_two_pow_self
    have h2 : 2 ^ mu ≤ (lam * n + 1) ^ mu := by
      exact Nat.pow_le_pow_left (by nlinarith) _
    rw [hQ, arQ]; omega
  -- the argument of `R`
  set W := Nat.size n + Nat.size (tPcp lam mu n) + Q + sigma with hW
  have hsn : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsT : Nat.size (tPcp lam mu n) = (Q + 5) * (mu + 1) + 1 := by
    rw [tPcp, Nat.size_pow]
  have hW1 : 1 ≤ W := by omega
  have hWle : W ≤ 10 * Q ^ 2 * sigma := by
    have h1 : (Q + 5) * (mu + 1) ≤ (Q + 5) * Q := Nat.mul_le_mul_left _ hμQ
    have h2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) _
    have h3 : Q ^ 2 ≤ Q ^ 2 * sigma := Nat.le_mul_of_pos_right _ hs
    rw [hW, hsT]
    nlinarith
  have hRW : R.eval W ≤ A * (10 * Q ^ 2 * sigma) ^ D :=
    (polynomial_eval_le_sum_coeff_mul_pow R hW1).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hWle _))
  have hpar := hR n (tPcp lam mu n) Q sigma
  have hm' : P.m' ≤ 5 * R.eval W + 5 := by
    have : P.m' = 5 * P.m + 5 + P.s := rfl
    change (PD.params n (tPcp lam mu n) Q sigma).k + (PD.params n (tPcp lam mu n) Q sigma).m
      + (PD.params n (tPcp lam mu n) Q sigma).s ≤ R.eval W at hpar
    change P.k + P.m + P.s ≤ R.eval W at hpar
    omega
  have hX1 : 1 ≤ (10 * Q ^ 2 * sigma) ^ D := Nat.one_le_pow _ _ (by positivity)
  have hm'2 : P.m' ≤ 10 * (A + 1) * (10 * Q ^ 2 * sigma) ^ D := by nlinarith
  have hpow : (10 * Q ^ 2 * sigma) ^ D * Q ≤ 10 ^ D * (Q * sigma) ^ (2 * D + 1) := by
    rw [mul_pow, mul_pow, ← pow_mul, pow_succ, mul_pow]
    have h1 : sigma ^ D ≤ sigma ^ (2 * D) := Nat.pow_le_pow_right hs (by omega)
    have h2 : 1 ≤ sigma := hs
    calc 10 ^ D * Q ^ (2 * D) * sigma ^ D * Q
        ≤ 10 ^ D * Q ^ (2 * D) * sigma ^ (2 * D) * (Q * sigma) := by
          gcongr
          nlinarith
      _ = 10 ^ D * (Q ^ (2 * D) * sigma ^ (2 * D) * (Q * sigma)) := by ring
  calc 8 * ((Q + 1) * P.m') ≤ 8 * ((2 * Q) * (10 * (A + 1) * (10 * Q ^ 2 * sigma) ^ D)) := by
        gcongr; omega
    _ = 160 * (A + 1) * ((10 * Q ^ 2 * sigma) ^ D * Q) := by ring
    _ ≤ 160 * (A + 1) * (10 ^ D * (Q * sigma) ^ (2 * D + 1)) := Nat.mul_le_mul_left _ hpow
    _ = zC R * (Q * sigma) ^ zE R := by rw [zC, zE, ← hA, ← hD]; ring

end Params

/-! ## The soundness clause -/

section Final

variable (PD : PcpDecider) {ℓ : ℕ}

/-- The detyping factor `16^{54}`, as a natural number. -/
abbrev kDet : ℕ := 16 ^ Fintype.card ArTy

/-- **The loss is trivial at least `1`**: then there is nothing to prove. -/
theorem sub_delta_le_of_one_le {V : Verifier (ℓ + 1)} {n B : ℕ} {δ : ℝ} (h : 1 ≤ δ) :
    1 - δ ≤ V.valStar n B :=
  (sub_nonpos.mpr h).trans (quantumValue_nonneg _)

/-- **A strategy above `1 - ε`**, from the value of a game above it. -/
theorem exists_value_gt {X Y A₁ B₁ : Type*} [Fintype X] [Fintype Y] [Fintype A₁] [Fintype B₁]
    {G : Game X Y A₁ B₁} {ε : ℝ} (hε : ε < 1) (h : 1 - ε < quantumValue G) :
    ∃ R : TensorProductStrategy G, 1 - ε ≤ R.value := by
  by_contra hno
  push Not at hno
  exact absurd h (not_lt.mpr (Real.iSup_le (fun R => (hno R).le) (by linarith)))

set_option maxHeartbeats 1000000 in
/-- **Soundness of answer reduction** (`lem:ar-soundness`, the `soundness` clause of the
`AnswerReduction` contract, at any answer bound above the answer cut): `val*` of the
answer-reduced verifier above `1 - ε` gives `val*(𝒱_n) ≥ 1 - δ(ε, n)`, for `n` past a threshold,
with `a` depending only on `R` and `b = clB / 2`. -/
theorem arVerifier_soundness (R : Polynomial ℕ) (hF : ShoupField PD) (hR : ParamsBound PD R)
    (hL : FieldLarge PD) :
    ∃ (a b : ℝ) (C : ℕ), 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ) (ε : ℝ) (B : ℕ), C ≤ n → 2 ≤ n → 1 ≤ lam →
        V.Within n (inBudget lam mu n) → V.decider.size ≤ sigma → 0 < ε →
        cutVal (arPar PD lam mu sigma n) ≤ B →
        1 - ε < (arVerifier PD lam mu sigma V).valStar n B →
        1 - delta a b lam mu sigma n ε ≤ V.valStar n (inAns lam mu n) := by
  set c : ℕ := zC R ^ (3 * simAN) with hc
  set p : ℕ := 3 * simAN * zE R with hp
  obtain ⟨Q0, hQ0⟩ := exists_threshold_clB c p
  obtain ⟨Q1, hQ1⟩ := hL fieldExp
  refine ⟨aOf c p kDet, clB / 2, max Q0 Q1, by exact_mod_cast one_le_aOf c p kDet,
    by have := clB_pos; linarith, by have := clB_lt_one; linarith, ?_⟩
  intro V lam mu sigma n ε B hC hn2 hlam hV hsz hε hcut hval
  set a : ℕ := aOf c p kDet with ha
  have ha1 : 1 ≤ a := one_le_aOf c p kDet
  have hs1 : 1 ≤ sigma := Nat.succ_le_of_lt ((esize_pos V.decider.prog).trans_le hsz)
  have hσ1 : (1 : ℝ) ≤ sigma := by exact_mod_cast hs1
  have hN2 : 2 ≤ lam * n := le_trans hn2 (Nat.le_mul_of_pos_left _ hlam)
  have hNr : (lam : ℝ) * n = ((lam * n : ℕ) : ℝ) := by push_cast; ring
  have hN1 : (1 : ℝ) ≤ (lam : ℝ) * n := by rw [hNr]; exact_mod_cast (by omega : 1 ≤ lam * n)
  have hSa : (1 : ℝ) ≤ (sigma : ℝ) ^ (a : ℝ) := Real.one_le_rpow hσ1 (by positivity)
  -- the trivial cases
  rcases Nat.eq_zero_or_pos mu with hmu0 | hmu
  · refine sub_delta_le_of_one_le ?_
    simp only [delta, hmu0, Nat.cast_zero, zero_mul, neg_zero, Real.rpow_zero, one_mul]
    have := Real.rpow_nonneg hε.le (clB / 2)
    nlinarith
  by_cases hε1 : 1 ≤ ε
  · refine sub_delta_le_of_one_le ?_
    have h1 : 1 ≤ ((lam : ℝ) * n) ^ ((mu : ℝ) * a) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 1 ≤ ε ^ (clB / 2) := Real.one_le_rpow hε1 (by have := clB_pos; linarith)
    have h3 : 0 ≤ ((lam : ℝ) * n) ^ (-((mu : ℝ) * (clB / 2))) := by positivity
    unfold delta
    have : 1 ≤ ((lam : ℝ) * n) ^ ((mu : ℝ) * a) * ε ^ (clB / 2) :=
      one_le_mul_of_one_le_of_one_le h1 h2
    nlinarith
  push Not at hε1
  -- a strategy at the answer cut
  have hrej := CL.Detyping.DeciderProgram.verifier_rejectsLong graph
    (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
    (arCut PD lam mu sigma) (by unfold level; omega) (total PD V lam mu sigma) n
  rw [(arVerifier PD lam mu sigma V).valStar_eq_of_rejects hcut hrej] at hval
  obtain ⟨Rs, hRs⟩ := exists_value_gt hε1 hval
  set T := typedStrategy PD lam mu sigma V n Rs with hT
  have hTv := typedStrategy_value_ge PD lam mu sigma V n Rs hRs
  have hK : (kDet : ℝ) = (16 : ℝ) ^ Fintype.card ArTy := by push_cast; rfl
  rw [← hK] at hTv
  have hmain := valStar_ge_of_typedGame PD lam mu sigma V n hF hlam hmu hV hsz _ T
  -- the parameters
  set P := arPar PD lam mu sigma n with hP
  set Q := arQ lam mu n with hQ
  have hmQ : (Q + 5) * (mu + 1) + 1 ≤ P.m := by
    have h := PD.two_mul_le n (tPcp lam mu n) Q sigma
    rw [tPcp, ← pow_succ'] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have hQm : Q ≤ P.m := by nlinarith
  have hm1 : 1 ≤ P.m := by nlinarith
  have : NeZero P.m := ⟨by omega⟩
  have hmm : P.m ≤ P.m' :=
    (Nat.le_mul_of_pos_left _ (by norm_num)).trans (PcpParams.five_mul_m_le P)
  have hq : (8 * ((Q + 1) * P.m')) ^ fieldExp
      ≤ Fintype.card (Fq P (arPar_hk PD lam mu sigma n)) := by
    rw [card_fq]
    refine hQ1 n (tPcp lam mu n) Q sigma ?_
    have : n + 1 ≤ Q := by
      have h1 : lam * n + 1 ≤ (lam * n + 1) ^ mu := Nat.le_self_pow (by omega) _
      have h2 : n ≤ lam * n := Nat.le_mul_of_pos_left _ hlam
      rw [hQ, arQ]; omega
    omega
  have hθ0 : 0 ≤ 1 - T.value := one_sub_value_nonneg V n P _ _ _ _ _ T
  have herr := errE_le hm1 hmm hQm hq hθ0 (show 1 - T.value ≤ (kDet : ℝ) * ε by linarith)
    (by exact_mod_cast Nat.one_le_pow _ _ (by norm_num)) hε.le hε1.le
  -- the size of `Z`
  have hZ := z_le PD R hR hlam hmu hs1 (by omega : 1 ≤ n)
  have hG : ((8 * ((Q + 1) * P.m') : ℕ) : ℝ) ^ (3 * simAN)
      ≤ c * (Q : ℝ) ^ p * (sigma : ℝ) ^ p := by
    have h1 : (8 * ((Q + 1) * P.m')) ^ (3 * simAN) ≤ (zC R * (Q * sigma) ^ zE R) ^ (3 * simAN) :=
      Nat.pow_le_pow_left hZ _
    have h2 : (zC R * (Q * sigma) ^ zE R) ^ (3 * simAN) = c * Q ^ p * sigma ^ p := by
      rw [hc, hp, mul_pow, ← pow_mul, mul_pow, mul_comm (zE R)]; ring
    rw [h2] at h1
    exact_mod_cast h1
  -- `Q` against `N = λn`
  have hQN : Q ≤ (lam * n) ^ (2 * mu) := by
    rw [hQ, arQ, pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) _
  have hNQ : (lam * n) ^ mu ≤ Q := Nat.pow_le_pow_left (by omega) _
  have hQQ0 : Q0 ≤ Q := by
    have : n + 1 ≤ Q := by
      have h1 : lam * n + 1 ≤ (lam * n + 1) ^ mu := Nat.le_self_pow (by omega) _
      have h2 : n ≤ lam * n := Nat.le_mul_of_pos_left _ hlam
      rw [hQ, arQ]; omega
    omega
  obtain ⟨hQ8, hthr⟩ := hQ0 Q hQQ0
  have hfin := sqrt_le_delta hN2 hmu hs1 hQN hNQ hQ8 hthr hG hε.le herr
  -- conclusion
  have hdel : delta (a : ℝ) (clB / 2) lam mu sigma n ε = (sigma : ℝ) ^ (a : ℝ) *
      (((lam * n : ℕ) : ℝ) ^ ((mu : ℝ) * a) * ε ^ (clB / 2)
        + ((lam * n : ℕ) : ℝ) ^ (-((mu : ℝ) * (clB / 2)))) := by
    rw [delta, hNr]
  rw [hdel]
  have hmain' : 1 - 24 * √(7 * errE (Fintype.card (Fq P (arPar_hk PD lam mu sigma n))) P.m P.m'
      (1 - T.value)) ≤ V.valStar n (inAns lam mu n) := hmain
  have hfin' : 24 * √(7 * errE (Fintype.card (Fq P (arPar_hk PD lam mu sigma n))) P.m P.m'
      (1 - T.value)) ≤ (sigma : ℝ) ^ (a : ℝ) * (((lam * n : ℕ) : ℝ) ^ ((mu : ℝ) * a)
        * ε ^ (clB / 2) + ((lam * n : ℕ) : ℝ) ^ (-((mu : ℝ) * (clB / 2)))) := hfin
  linarith

end Final

end MIPRE.AnswerReduction

end
