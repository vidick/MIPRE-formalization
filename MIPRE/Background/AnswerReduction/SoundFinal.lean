/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.AnswerReduction.SoundPcp
public import MIPRE.Background.AnswerReduction.SoundSetup
public import MIPRE.Background.AnswerReduction.SoundError
public import MIPRE.Background.LIDT.FinModel

@[expose] public section

/-!
# Soundness of answer reduction

Piece AR-5f of `planning/answer-reduction.md`, concluded (`lem:ar-soundness`,
`lem:ar-error-assembly`): the `soundness` clause of the `AnswerReduction` contract for
`arVerifier` (`arVerifier_soundness`), under a new hypothesis on the PCP decider, `FieldLarge`:
for every exponent `e`, its field eventually has at least `(8 (Q + 1) m')^e` elements.

The chain: a projective strategy of value at least `1 - ε` for the answer-reduced verifier at the
answer cut, in a bipartite model where the seeded CL test is sound, gives a typed strategy of
failure `θ ≤ 16^{54} ε` (`typedStrategy_value_ge`), which gives
`ω(𝒱_n) ≥ 1 - 24 √(7 errE(θ))` (`val_ge_of_typedGame`) in every value model `ω` where
oracularization is sound and which dominates the model. The combined error is bounded over the
large field by `errE_le`, the size of the parameters by `ParamsBound` (`z_le`), and the result
compared with `δ(ε, n)` by `sqrt_le_delta`, past a threshold on `n` (`exists_threshold_clB`):
`val_ge_of_arStrategy`, at the explicit constants `soundA`, `clB / 2`, `soundC`.

The clause then holds, at the same constants, in every value model where oracularization is sound
and which is approached by projective strategies of models it dominates where the seeded test is
sound (`LIDT.Simul.ApproxSoundIn`, `arVerifier_soundness_of_approx`). So it holds in `val*`
(`arVerifier_soundness_tensor`), a tensor-product strategy being a projective strategy in its
tensor-product model, where the seeded test is sound; and in `ω_co`
(`arVerifier_soundness_commuting`) given the seeded test's soundness in the commuting-operator
model, `ω_co` being approached by projective strategies in the models of commuting-operator
strategies. The output verifier rejects answers longer than the cut, so its value at any larger
bound is the same; at `μ = 0` or `ε ≥ 1` the loss is at least `1` and there is nothing to prove.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp Cost
open scoped MatrixOrder

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

/-- **The exponent `a` of the soundness loss**, which depends only on the parameter polynomial
`R`. -/
def soundA (R : Polynomial ℕ) : ℕ := aOf (zC R ^ (3 * simAN)) (3 * simAN * zE R) kDet

theorem one_le_soundA (R : Polynomial ℕ) : 1 ≤ soundA R := one_le_aOf _ _ _

/-- **The threshold `C` of the soundness clause**: past the threshold of the error comparison
(`exists_threshold_clB`) and past the one from which the PCP's field is large enough
(`FieldLarge` at `fieldExp`). Explicit, so that the clause holds in each value model at the same
constants (`arVerifier_soundness_of_approx`). -/
def soundC (R : Polynomial ℕ) (hL : FieldLarge PD) : ℕ :=
  max (exists_threshold_clB (zC R ^ (3 * simAN)) (3 * simAN * zE R)).choose (hL fieldExp).choose

/-- **The loss is trivial at least `1`**: then there is nothing to prove, in any value model. -/
theorem sub_delta_le_of_one_le (ω : ValueModel) {V : Verifier (ℓ + 1)} {n B : ℕ} {δ : ℝ}
    (h : 1 ≤ δ) : 1 - δ ≤ V.val ω n B :=
  (sub_nonpos.mpr h).trans (ω.nonneg _)

/-- **The loss is at least `1` when `μ = 0` or `ε ≥ 1`.** -/
theorem one_le_delta_of_trivial {a : ℕ} (ha : 1 ≤ a) {lam mu sigma n : ℕ} {ε : ℝ}
    (hs1 : 1 ≤ sigma) (hN1 : (1 : ℝ) ≤ (lam : ℝ) * n) (hε : 0 < ε) (h : mu = 0 ∨ 1 ≤ ε) :
    1 ≤ delta (a : ℝ) (clB / 2) lam mu sigma n ε := by
  have hσ1 : (1 : ℝ) ≤ sigma := by exact_mod_cast hs1
  have hSa : (1 : ℝ) ≤ (sigma : ℝ) ^ (a : ℝ) := Real.one_le_rpow hσ1 (by positivity)
  rcases h with hmu0 | hε1
  · simp only [delta, hmu0, Nat.cast_zero, zero_mul, neg_zero, Real.rpow_zero, one_mul]
    have := Real.rpow_nonneg hε.le (clB / 2)
    nlinarith
  · have h1 : 1 ≤ ((lam : ℝ) * n) ^ ((mu : ℝ) * a) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 1 ≤ ε ^ (clB / 2) := Real.one_le_rpow hε1 (by have := clB_pos; linarith)
    have h3 : 0 ≤ ((lam : ℝ) * n) ^ (-((mu : ℝ) * (clB / 2))) := by positivity
    unfold delta
    have : 1 ≤ ((lam : ℝ) * n) ^ ((mu : ℝ) * a) * ε ^ (clB / 2) :=
      one_le_mul_of_one_le_of_one_le h1 h2
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **Soundness of answer reduction, for a projective strategy in a bipartite model**
(`lem:ar-error-assembly`): in a model in which the low-individual-degree test is sound, a
projective strategy of value at least `1 - ε` for the answer-reduced verifier's game at the answer
cut puts `ω(𝒱_n)` at least `1 - δ(ε, n)`, past the threshold, for every value model `ω` in which
oracularization is sound and which dominates the model. The typed strategy fails with probability
`θ ≤ 16^{54} ε` (`typedStrategy_value_ge`), which gives `ω(𝒱_n) ≥ 1 - 24 √(7 errE(θ))`
(`val_ge_of_typedGame`); the rest compares that with `δ(ε, n)`, and is the same in every model. -/
theorem val_ge_of_arStrategy (R : Polynomial ℕ) (hF : ShoupField PD) (hR : ParamsBound PD R)
    (hL : FieldLarge PD) {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜]
    [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
    (hLD : LIDT.Simul.SoundIn M) {ω : ValueModel} (hω : ω.OracularSound) (hdom : ω.Dominates M)
    {V : Verifier (ℓ + 1)} {lam mu sigma n : ℕ} {ε : ℝ} (hC : soundC PD R hL ≤ n) (hn2 : 2 ≤ n)
    (hlam : 1 ≤ lam) (hV : V.Within n (inBudget lam mu n)) (hsz : V.decider.size ≤ sigma)
    (hε : 0 < ε) (hmu : 1 ≤ mu) (hε1 : ε < 1)
    (Rs : M.ProjStrat ((arVerifier PD lam mu sigma V).game n (cutVal (arPar PD lam mu sigma n))))
    (hRs : 1 - ε ≤ Rs.value) :
    1 - delta (soundA R : ℝ) (clB / 2) lam mu sigma n ε ≤ V.val ω n (inAns lam mu n) := by
  set c : ℕ := zC R ^ (3 * simAN) with hc
  set p : ℕ := 3 * simAN * zE R with hp
  have hQ0 := (exists_threshold_clB c p).choose_spec
  have hQ1 := (hL fieldExp).choose_spec
  have hC0 : (exists_threshold_clB c p).choose ≤ n := le_trans (le_max_left _ _) hC
  have hC1 : (hL fieldExp).choose ≤ n := le_trans (le_max_right _ _) hC
  set a : ℕ := soundA R with ha
  have hs1 : 1 ≤ sigma := Nat.succ_le_of_lt ((esize_pos V.decider.prog).trans_le hsz)
  have hN2 : 2 ≤ lam * n := le_trans hn2 (Nat.le_mul_of_pos_left _ hlam)
  have hNr : (lam : ℝ) * n = ((lam * n : ℕ) : ℝ) := by push_cast; ring
  -- the typed strategy
  set T := typedStrategy PD lam mu sigma V n Rs with hT
  have hTv := typedStrategy_value_ge PD lam mu sigma V n Rs hRs
  have hK : (kDet : ℝ) = (16 : ℝ) ^ Fintype.card ArTy := by push_cast; rfl
  rw [← hK] at hTv
  have hmain := val_ge_of_typedGame PD lam mu sigma V n hLD hω hdom hF hlam hmu hV hsz _ T
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
  have hnQ : n + 1 ≤ Q := by
    have h1 : lam * n + 1 ≤ (lam * n + 1) ^ mu := Nat.le_self_pow (by omega) _
    have h2 : n ≤ lam * n := Nat.le_mul_of_pos_left _ hlam
    rw [hQ, arQ]; omega
  have hq : (8 * ((Q + 1) * P.m')) ^ fieldExp
      ≤ Fintype.card (Fq P (arPar_hk PD lam mu sigma n)) := by
    rw [card_fq]
    exact hQ1 n (tPcp lam mu n) Q sigma (by omega)
  have hθ0 : 0 ≤ 1 - T.value := sub_nonneg.mpr T.value_le_one
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
  obtain ⟨hQ8, hthr⟩ := hQ0 Q (by omega)
  have hfin := sqrt_le_delta hN2 hmu hs1 hQN hNQ hQ8 hthr hG hε.le herr
  -- conclusion
  have hdel : delta (a : ℝ) (clB / 2) lam mu sigma n ε = (sigma : ℝ) ^ (a : ℝ) *
      (((lam * n : ℕ) : ℝ) ^ ((mu : ℝ) * a) * ε ^ (clB / 2)
        + ((lam * n : ℕ) : ℝ) ^ (-((mu : ℝ) * (clB / 2)))) := by
    rw [delta, hNr]
  rw [hdel]
  have hmain' : 1 - 24 * √(7 * errE (Fintype.card (Fq P (arPar_hk PD lam mu sigma n))) P.m P.m'
      (1 - T.value)) ≤ V.val ω n (inAns lam mu n) := hmain
  have hfin' : 24 * √(7 * errE (Fintype.card (Fq P (arPar_hk PD lam mu sigma n))) P.m P.m'
      (1 - T.value)) ≤ (sigma : ℝ) ^ (a : ℝ) * (((lam * n : ℕ) : ℝ) ^ ((mu : ℝ) * a)
        * ε ^ (clB / 2) + ((lam * n : ℕ) : ℝ) ^ (-((mu : ℝ) * (clB / 2)))) := hfin
  linarith

/-- **Soundness of answer reduction in a value model approached in sound models**
(`lem:ar-soundness`, at any answer bound above the answer cut), at the explicit constants
`soundA`, `clB / 2`, `soundC`: in a value model `ω` where oracularization is sound and which is
approached by projective strategies of models it dominates where the low-individual-degree test is
sound (`LIDT.Simul.ApproxSoundIn`), `ω` of the answer-reduced verifier above `1 - ε` gives
`ω(𝒱_n) ≥ 1 - δ(ε, n)`, for `n` past the threshold. A projective strategy above `1 - ε` in such
a model carries the analysis (`val_ge_of_arStrategy`). -/
theorem arVerifier_soundness_of_approx (R : Polynomial ℕ) (hF : ShoupField PD)
    (hR : ParamsBound PD R) (hL : FieldLarge PD) {ω : ValueModel}
    (hA : LIDT.Simul.ApproxSoundIn ω) (hω : ω.OracularSound) (V : Verifier (ℓ + 1))
    (lam mu sigma n : ℕ) (ε : ℝ) (B : ℕ) (hC : soundC PD R hL ≤ n) (hn2 : 2 ≤ n)
    (hlam : 1 ≤ lam) (hV : V.Within n (inBudget lam mu n)) (hsz : V.decider.size ≤ sigma)
    (hε : 0 < ε) (hcut : cutVal (arPar PD lam mu sigma n) ≤ B)
    (hval : 1 - ε < (arVerifier PD lam mu sigma V).val ω n B) :
    1 - delta (soundA R : ℝ) (clB / 2) lam mu sigma n ε ≤ V.val ω n (inAns lam mu n) := by
  have hs1 : 1 ≤ sigma := Nat.succ_le_of_lt ((esize_pos V.decider.prog).trans_le hsz)
  have hN1 : (1 : ℝ) ≤ (lam : ℝ) * n := by
    have : 1 ≤ lam * n := le_trans (by omega) (Nat.le_mul_of_pos_left _ hlam)
    exact_mod_cast this
  by_cases htriv : mu = 0 ∨ 1 ≤ ε
  · exact sub_delta_le_of_one_le ω (one_le_delta_of_trivial (one_le_soundA R) hs1 hN1 hε htriv)
  push Not at htriv
  obtain ⟨hmu0, hε1⟩ := htriv
  have hrej := CL.Detyping.DeciderProgram.verifier_rejectsLong graph
    (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
    (arCut PD lam mu sigma) (by unfold level; omega) (total PD V lam mu sigma) n
  rw [(arVerifier PD lam mu sigma V).val_eq_of_rejects ω hcut hrej] at hval
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, M, hM, hdom, Rs, hRs⟩ :=
    hA _ (by linarith) hval
  exact val_ge_of_arStrategy PD R hF hR hL hM hω hdom hC hn2 hlam hV hsz hε
    (Nat.one_le_iff_ne_zero.mpr hmu0) hε1 Rs hRs.le

/-- **Soundness of answer reduction in the tensor-product value** (`lem:ar-soundness`, the
`soundness` clause of the `AnswerReduction` contract, at any answer bound above the answer cut),
at the explicit constants `soundA`, `clB / 2`, `soundC`: `val*` of the answer-reduced verifier
above `1 - ε` gives `val*(𝒱_n) ≥ 1 - δ(ε, n)`, for `n` past the threshold. A tensor-product
strategy is a projective strategy in its tensor-product model, where the low-individual-degree
test is sound (`LIDT.Simul.approxSoundIn_tensor`). -/
theorem arVerifier_soundness_tensor (R : Polynomial ℕ) (hF : ShoupField PD)
    (hR : ParamsBound PD R) (hL : FieldLarge PD) (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ)
    (ε : ℝ) (B : ℕ) (hC : soundC PD R hL ≤ n) (hn2 : 2 ≤ n) (hlam : 1 ≤ lam)
    (hV : V.Within n (inBudget lam mu n)) (hsz : V.decider.size ≤ sigma) (hε : 0 < ε)
    (hcut : cutVal (arPar PD lam mu sigma n) ≤ B)
    (hval : 1 - ε < (arVerifier PD lam mu sigma V).valStar n B) :
    1 - delta (soundA R : ℝ) (clB / 2) lam mu sigma n ε ≤ V.valStar n (inAns lam mu n) :=
  arVerifier_soundness_of_approx PD R hF hR hL LIDT.Simul.approxSoundIn_tensor
    ValueModel.tensor_oracularSound V lam mu sigma n ε B hC hn2 hlam hV hsz hε hcut hval

/-- **Soundness of answer reduction in the commuting-operator value** (`thm:ar-sound-co`),
at the same constants as in the tensor-product value, given the soundness of the
low-individual-degree test in the commuting-operator model (`LIDT.Simul.SoundCo`, Phase 6 of
`planning/mipco-track.md`): `ω_co` of the answer-reduced verifier above `1 - ε` gives
`ω_co(𝒱_n) ≥ 1 - δ(ε, n)`, for `n` past the threshold. `ω_co` is approached by projective
strategies in the models of commuting-operator strategies
(`LIDT.Simul.approxSoundIn_commuting`). -/
theorem arVerifier_soundness_commuting (R : Polynomial ℕ) (hF : ShoupField PD)
    (hR : ParamsBound PD R) (hL : FieldLarge PD) (hLD : LIDT.Simul.SoundCo)
    (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ) (ε : ℝ) (B : ℕ) (hC : soundC PD R hL ≤ n)
    (hn2 : 2 ≤ n) (hlam : 1 ≤ lam) (hV : V.Within n (inBudget lam mu n))
    (hsz : V.decider.size ≤ sigma) (hε : 0 < ε) (hcut : cutVal (arPar PD lam mu sigma n) ≤ B)
    (hval : 1 - ε < (arVerifier PD lam mu sigma V).val .commuting n B) :
    1 - delta (soundA R : ℝ) (clB / 2) lam mu sigma n ε ≤ V.val .commuting n (inAns lam mu n) :=
  arVerifier_soundness_of_approx PD R hF hR hL (LIDT.Simul.approxSoundIn_commuting hLD)
    ValueModel.commuting_oracularSound V lam mu sigma n ε B hC hn2 hlam hV hsz hε hcut hval

/-- **Soundness of answer reduction** (`lem:ar-soundness`, the `soundness` clause of the
`AnswerReduction` contract, at any answer bound above the answer cut): `val*` of the
answer-reduced verifier above `1 - ε` gives `val*(𝒱_n) ≥ 1 - δ(ε, n)`, for `n` past a threshold,
with `a` depending only on `R` and `b = clB / 2` (`arVerifier_soundness_tensor`, at its explicit
constants). -/
theorem arVerifier_soundness (R : Polynomial ℕ) (hF : ShoupField PD) (hR : ParamsBound PD R)
    (hL : FieldLarge PD) :
    ∃ (a b : ℝ) (C : ℕ), 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ) (ε : ℝ) (B : ℕ), C ≤ n → 2 ≤ n → 1 ≤ lam →
        V.Within n (inBudget lam mu n) → V.decider.size ≤ sigma → 0 < ε →
        cutVal (arPar PD lam mu sigma n) ≤ B →
        1 - ε < (arVerifier PD lam mu sigma V).valStar n B →
        1 - delta a b lam mu sigma n ε ≤ V.valStar n (inAns lam mu n) :=
  ⟨soundA R, clB / 2, soundC PD R hL, by exact_mod_cast one_le_soundA R,
    by have := clB_pos; linarith, by have := clB_lt_one; linarith,
    fun V lam mu sigma n ε B => arVerifier_soundness_tensor PD R hF hR hL V lam mu sigma n ε B⟩

end Final

end MIPRE.AnswerReduction

end

end
