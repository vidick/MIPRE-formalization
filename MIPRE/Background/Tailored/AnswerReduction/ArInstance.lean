/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArCirc
public import MIPRE.Background.Tailored.AnswerReduction.ArParCoreCost
public import MIPRE.Background.Tailored.AnswerReduction.ArWithin

@[expose] public section

/-!
# The routine of the answer reduction, fixed

Slice P4i of `planning/aldous-lyons-track.md`: the parameter routine of the answer-reduced
verifier (`ArRoutine`) at the parameters of `MIPRE/Tailored/AnsRed/ArParams.lean`, for constants
`κ` with `E₂ ≥ 1` (`arRoutine`): the field and selector widths `t, j`, the degree `17`, the
PCP's dimensions, the parameter program `arParCore` and the circuit function `arCircF` at the
builder `lstarProgF` of the output indicator's program. Its parameter program runs in polynomial
time (`arRoutine_parTime`), and its circuits are those of the honest PCPs' hypotheses
(`arRoutine_circ`), which hold for every input within the input budget (`honestHyp_arRoutine`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT

variable (κ : Params.ArConsts) (hE : 1 ≤ κ.E₂)

/-- The field and selector widths at `(λ, μ, σ)`. -/
def arFam (lam mu sigma : ℕ) : LdFamily where
  t n := Params.pTw κ lam mu sigma n
  ht n := Params.one_le_pTw κ lam mu sigma n hE
  j n := Params.pJ κ lam mu sigma n
  hjt n := Params.pJ_le_pTw κ lam mu sigma n hE

set_option maxRecDepth 100000 in
/-- **The routine of the answer reduction.** -/
def arRoutine : ArRoutine where
  fam := arFam κ hE
  d _ _ _ _ := Params.pD
  L := Params.pL κ
  hLM lam mu sigma n := Params.pL_m_le κ lam mu sigma n
  extra := Params.pExtra κ
  parCore := arParCore κ
  closed := arParCore_closed κ
  runs := arParCore_runs κ
  circF := arCircF lstarProgF
  circ_wf := arCircF_wf
  circ_inputs V lam mu sigma n x y :=
    arCircF_inputs (fun L P p => lstarProgF_apply L P p) κ V lam mu sigma n x y
  circ_size V lam mu sigma n x y :=
    arCircF_size (fun L P p => lstarProgF_apply L P p) κ V lam mu sigma n x y

theorem arRoutine_params (lam mu sigma n : ℕ) :
    (arRoutine κ hE).params lam mu sigma n = arParams (Params.pTw κ lam mu sigma n)
      (Params.pJ κ lam mu sigma n) Params.pD (Params.pL κ lam mu sigma n)
      (Params.pExtra κ lam mu sigma n) := rfl

/-- **The routine's parameter program runs in polynomial time.** -/
theorem arRoutine_parTime : (arRoutine κ hE).ParTime := arParCore_time κ

set_option maxRecDepth 100000 in
/-- **The routine's circuits are those of the honest PCPs' hypotheses.** -/
theorem arRoutine_circ {ℓ : ℕ} (V : TailoredVerifier ℓ) (lam mu sigma n : ℕ) :
    (arRoutine κ hE).circ lam mu sigma n V =
      Params.arCc (κ := κ) (lam := lam) (mu := mu) (sigma := sigma) V := by
  funext z
  exact arCircF_apply (fun L P p => lstarProgF_apply L P p) κ V.progs lam mu sigma n _ _

/-- The constant of `L*`'s running time. -/
def lstarE : ℕ := Params.exists_lstarTime.choose

theorem one_le_lstarE : 1 ≤ lstarE := Params.exists_lstarTime.choose_spec.1

theorem lstarTime_lstarE : Params.LstarTime lstarE := Params.exists_lstarTime.choose_spec.2

/-- **The honest PCPs' hypotheses hold for the routine's circuits**, for an input within the
input budget with `|𝒱| ≤ σ` and `λ, μ ≥ 1`, once `E₁ ≥ 2E` and `c₀` is the size of `L*`'s
program. -/
theorem honestHyp_arRoutine (hE₁ : 2 * lstarE ≤ κ.E₁) (hc₀ : κ.c₀ = lstarProgSize₀) {ℓ : ℕ}
    (V : TailoredVerifier ℓ) {lam mu sigma n : ℕ} (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hV : V.Within n (AnswerReduction.inBudget lam mu n)) (hsz : V.size ≤ sigma) :
    HonestHyp ((arRoutine κ hE).L lam mu sigma n) V n (Params.arPrm lam mu n)
      ((arRoutine κ hE).circ lam mu sigma n V) (Params.pT κ lam mu n) := by
  rw [arRoutine_circ]
  have hS : Params.LstarSize κ.c₀ := hc₀ ▸ Params.lstarSize_lstarProgSize₀
  exact Params.honestHyp_ar hE₁ one_le_lstarE lstarTime_lstarE hS V hlam hmu hV hsz

end MIPRE.Tailored.AnsRed.Typed

end

end
