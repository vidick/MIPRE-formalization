/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArInstance
public import MIPRE.Background.Tailored.AnswerReduction.ArError
public import MIPRE.Tailored.Stages

@[expose] public section

/-!
# The answer reduction's contract, from its routine

Slice P4i of `planning/aldous-lyons-track.md`: the output verifier of the routine `arRoutine`
inhabits `TailoredAnswerReduction 5` (`tailoredAnswerReductionOf`), given the two facts about the
field the soundness clause needs: the field-size conditions of `valStar_sound_output` and the
bound of its error `24 √(errAR (16⁹ ε))` by the contract's loss `AnswerReduction.delta`. Every
other clause is proved here:

* the programs and the output are the routine's (`arSamplerProg`, `lenPF`, `lpPF`, `output`);
* the complexity clause is `output_within` at the routine's `ParTime`, the calculator's totality
  `lenD_total`;
* completeness is `hasPerfectZPC_output` at the honest PCPs' hypotheses
  (`honestHyp_arRoutine`), for `λ, μ ≥ 1`;
* soundness is `valStar_sound_output` and the error bound for `μ ≥ 1`; for `μ = 0` the loss is
  at least `1` and there is nothing to prove.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost MIPRE.CL MIPRE.SAT

/-- At `μ = 0` the loss is at least `1`. -/
theorem one_le_delta_mu_zero {a b : ℝ} (ha : 0 ≤ a) {lam sigma n : ℕ} (hs : 1 ≤ sigma)
    {ε : ℝ} (hε : 0 < ε) : 1 ≤ AnswerReduction.delta a b lam 0 sigma n ε := by
  unfold AnswerReduction.delta
  have hσ : (1 : ℝ) ≤ (sigma : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hs) ha
  simp only [Nat.cast_zero, zero_mul, neg_zero, Real.rpow_zero, one_mul]
  have := Real.rpow_nonneg hε.le b
  nlinarith

/-- A verifier's description length is at least `1`. -/
theorem one_le_size {ℓ : ℕ} (V : TailoredVerifier ℓ) : 1 ≤ V.size :=
  (esize_pos V.sampler.prog).trans_le (le_max_left _ _)

variable (κ : Params.ArConsts) (hE : 1 ≤ κ.E₂)

/-- The output verifier of the routine, for a `5`-level input. -/
abbrev arOut (V : TailoredVerifier 5) (lam mu sigma : ℕ) : TailoredVerifier 7 :=
  (arRoutine κ hE).output (ℓ := 4) V lam mu sigma

/-- **The answer reduction's contract**, from the routine, given the field-size conditions and the
bound of the soundness error by the contract's loss, or the loss at least `1`. -/
def tailoredAnswerReductionOf (hE₁ : 2 * lstarE ≤ κ.E₁) (hc₀ : κ.c₀ = lstarProgSize₀)
    (a b : ℝ) (C : ℕ) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hq : ∀ lam mu sigma n, 2 * ((2 ^ Params.pJ κ lam mu sigma n + 1) * Params.pD) ≤
      Fintype.card (Fq (Params.pTw κ lam mu sigma n) (Params.one_le_pTw κ lam mu sigma n hE)))
    (hτ : ∀ lam mu sigma n, 2 * ((Params.pL κ lam mu sigma n).m * chkDeg 5 Params.pD) ≤
      Fintype.card (Fq (Params.pTw κ lam mu sigma n) (Params.one_le_pTw κ lam mu sigma n hE)))
    (herr : ∀ (lam mu sigma n : ℕ) (ε : ℝ), C ≤ n → 2 ≤ n → 1 ≤ lam → 1 ≤ sigma → 0 < ε →
      24 * √(errAR (Params.pTw κ lam mu sigma n) (Params.one_le_pTw κ lam mu sigma n hE)
        (Params.pJ κ lam mu sigma n) Params.pD (Params.pL κ lam mu sigma n) (16 ^ 9 * ε)) ≤
        AnswerReduction.delta a b lam mu sigma n ε ∨ 1 ≤ AnswerReduction.delta a b lam mu sigma n ε) :
    TailoredAnswerReduction 5 where
  a := a
  b := b
  one_le_a := ha
  b_pos := hb0
  b_le_one := hb1
  C := C
  bound := (ArRoutine.output_within (arRoutine_parTime κ hE) 4).choose
  deg := (ArRoutine.output_within (arRoutine_parTime κ hE) 4).choose_spec.choose
  sampler S lam mu sigma := (arRoutine κ hE).toLd.arSampler lam mu sigma S
  samplerProg := (arRoutine κ hE).toLd.arSamplerProg 4
  samplerProg_eq _ _ _ _ := rfl
  len lam mu sigma := (arRoutine κ hE).lenD lam mu sigma
  lenProg := (arRoutine κ hE).lenPF
  lenProg_eq _ _ _ := rfl
  compute := (arRoutine κ hE).lpPF 4
  output V lam mu sigma := arOut κ hE V lam mu sigma
  output_sampler _ _ _ _ := rfl
  output_len _ _ _ _ := rfl
  output_lp _ _ _ _ := rfl
  within V lam mu sigma n hV hsz :=
    (ArRoutine.output_within (arRoutine_parTime κ hE) 4).choose_spec.choose_spec V lam mu sigma n
      hV hsz
  len_total V lam mu sigma n := (arRoutine κ hE).lenD_total lam mu sigma n _
  completeness V lam mu sigma n _ hlam hmu hV hsz h :=
    (arRoutine κ hE).hasPerfectZPC_output V lam mu sigma n
      (Finset.univ.sup fun u => len (Params.pTw κ lam mu sigma n) (Params.pJ κ lam mu sigma n)
        Params.pD (Params.pL κ lam mu sigma n) u)
      (honestHyp_arRoutine κ hE hE₁ hc₀ V hlam hmu hV hsz) (le_refl 17)
      (fun u => Finset.le_sup (f := fun u => len (Params.pTw κ lam mu sigma n)
        (Params.pJ κ lam mu sigma n) Params.pD (Params.pL κ lam mu sigma n) u)
        (Finset.mem_univ u)) h
  soundness V lam mu sigma n ε hC hn2 hlam hV hsz hε hv := by
    have hs : 1 ≤ sigma := (one_le_size V).trans hsz
    rcases Nat.eq_zero_or_pos mu with rfl | hmu
    · exact (sub_nonpos.mpr (one_le_delta_mu_zero (by linarith) hs hε)).trans
        (quantumValue_nonneg _)
    · have h := (arRoutine κ hE).valStar_sound_output V lam mu sigma n
        (Finset.univ.sup fun u => len (Params.pTw κ lam mu sigma n) (Params.pJ κ lam mu sigma n)
          Params.pD (Params.pL κ lam mu sigma n) u)
        (honestHyp_arRoutine κ hE hE₁ hc₀ V hlam hmu hV hsz) (show 1 ≤ 17 by norm_num)
        (fun u => Finset.le_sup (f := fun u => len (Params.pTw κ lam mu sigma n)
          (Params.pJ κ lam mu sigma n) Params.pD (Params.pL κ lam mu sigma n) u)
          (Finset.mem_univ u)) (hq lam mu sigma n) (hτ lam mu sigma n) hε hv
      rcases herr lam mu sigma n ε hC hn2 hlam hs hε with he | he
      · exact (sub_le_sub_left he 1).trans h
      · exact (sub_nonpos.mpr he).trans (quantumValue_nonneg _)

/-! ## The constants -/

/-- **The constants of the answer reduction**: `E₁ = 2E` for the running time of `L*`, `E₂` the
field width's threshold of the soundness error, `c₀` the size of `L*`'s program. -/
def arConsts : Params.ArConsts := ⟨2 * lstarE, e2Min, lstarProgSize₀⟩

theorem one_le_arConsts_E₂ : 1 ≤ arConsts.E₂ := by
  have := seven_le_e2Min; unfold arConsts; dsimp only; omega

/-- **Answer reduction for tailored verifiers** (`thm:tailored-ar`, II:6883): the contract
`TailoredAnswerReduction 5` is inhabited. -/
def tailoredAnswerReduction : TailoredAnswerReduction 5 :=
  tailoredAnswerReductionOf arConsts one_le_arConsts_E₂ le_rfl rfl (errA arConsts : ℝ)
    (LIDT.clB / 2) (errC arConsts) (by exact_mod_cast one_le_errA arConsts)
    (by have := LIDT.clB_pos; linarith) (by have := LIDT.clB_lt_one; linarith)
    (fun lam mu sigma n => (field_hyps arConsts (seven_le_e2Min.trans le_rfl) lam mu sigma n).1)
    (fun lam mu sigma n => (field_hyps arConsts (seven_le_e2Min.trans le_rfl) lam mu sigma n).2)
    (fun _ _ _ _ _ hC hn2 hlam hs hε => errAR_le_delta_or arConsts le_rfl hC hn2 hlam hs hε)

end MIPRE.Tailored.AnsRed.Typed

end

end
