/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Toolkit
import MIPRE.Foundations.Cost.Universal

/-!
# Efficient Kleene recursion

The efficient fixed-point theorem `efficient_fixed_point` (blueprint `lem:kleene`;
[MNY, Lemma 2.3]), by the classical construction: for a polynomial-time map `F` on
programs, let `G` be the program that on `cons x v` (with `x` the description of a program
`x'`) computes `s(x', x') = hardcode x' (encode x')`, applies `F` to it, and runs the result
on `v` through the universal machine; the fixed point is `e = hardcode G (encode G)`, since
`e` on `v` is `G` on `cons (encode G) v`, which runs `F (hardcode G (encode G)) = F e` on
`v`. The time transfer is the universal machine's, plus the fixed cost of computing `F e`
and a copy of the input.
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- Inverting a call: a run of `callVar i q` is a run of the closed `q` on the value of
variable `i`. -/
theorem callVar_runs_rev {env : Env} {i : ℕ} {q : Prog} (hq : q.WellScoped 1) {r : Data}
    {t : ℕ} (h : Eval env (callVar i q) r t) : ∃ t' ≤ t, q.Runs (env.get i) r t' := by
  change Eval env (.let_ (.var i) q) r t at h
  cases h with
  | let_ h₁ h₂ =>
    cases h₁
    exact ⟨_, by omega,
      Eval.of_append_of_wellScoped (env := [env.get i]) (extra := env) h₂ hq⟩

/-- The two-argument program of the fixed-point construction: on `cons x v`, compute the
description of `hardcode x' (encode x')` (where `x = encode x'`), apply `F` to it, and run
the result on `v` through the universal program `univ`. -/
def kleeneProg (univ : Prog) (F : PolyTimeFun Prog Prog) : Prog :=
  .elim 0 .nil
    (.let_ (.cons (.var 0) (.var 0))
      (.let_ (callVar 0 smnProg)
        (.let_ (callVar 0 F.code)
          (.let_ (.cons (.var 0) (.var 4))
            (callVar 0 univ)))))

theorem kleeneProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (F : PolyTimeFun Prog Prog) :
    (kleeneProg univ F).WellScoped 1 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) smnProg_wellScoped,
    callVar_wellScoped (by decide) F.closed,
    ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) hU⟩

/-- The run of the pairing prefix of `kleeneProg`. -/
theorem kleeneProg_pair_eval (x : Prog) (v : Data) :
    Eval [encode x, v, Data.cons (encode x) v] (.cons (.var 0) (.var 0))
      (.cons (encode x) (encode x)) ((encode x).size + 1 + ((encode x).size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := encode x) (by simp))
    (Eval.var_of_get (i := 0) (v := encode x) (by simp))

/-- The run of the s-m-n step of `kleeneProg`. -/
theorem kleeneProg_smn_eval (x : Prog) (v : Data) :
    Eval [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v]
      (callVar 0 smnProg) (encode (hardcode x (encode x)))
      ((Data.cons (encode x) (encode x)).size + 1 + ((encode x).size + (encode x).size + 38) + 1) :=
  callVar_eval (i := 0) smnProg_wellScoped (v := .cons (encode x) (encode x)) (by simp)
    (smnProg_runs (encode x) (encode x))

/-- The run of the final pairing step of `kleeneProg`. -/
theorem kleeneProg_pair2_eval (x : Prog) (v : Data) (F : PolyTimeFun Prog Prog) :
    Eval (encode (F (hardcode x (encode x))) :: encode (hardcode x (encode x)) ::
        [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
      (.cons (.var 0) (.var 4)) (.cons (encode (F (hardcode x (encode x)))) v)
      ((encode (F (hardcode x (encode x)))).size + 1 + (v.size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := encode (F (hardcode x (encode x)))) (by simp))
    (Eval.var_of_get (i := 4) (v := v) (by simp))

/-- Forward run of `kleeneProg`: a run of `F (hardcode x (encode x))` on `v` yields a run of
`kleeneProg` on `cons (encode x) v`, at the universal machine's overhead plus the fixed
cost of computing `F (hardcode x (encode x))` and copies of the input. -/
theorem kleeneProg_runs (U : UniversalMachine) (F : PolyTimeFun Prog Prog) (x : Prog)
    {v r : Data} {t : ℕ} (h : (F (hardcode x (encode x))).Runs v r t) :
    ∃ T ≤ 6 * esize x + esize (hardcode x (encode x)) +
        F.timeBound.eval (esize (hardcode x (encode x))) +
        2 * esize (F (hardcode x (encode x))) + 2 * v.size +
        U.bound.eval (esize (F (hardcode x (encode x))) + v.size + t) + 57,
      (kleeneProg U.univ F).Runs (.cons (encode x) v) r T := by
  obtain ⟨tF, htF, hF⟩ := F.computes (hardcode x (encode x))
  obtain ⟨tU, htU, hU⟩ := U.time_le _ v r t h
  have s3 := callVar_eval
    (env := encode (hardcode x (encode x)) ::
      [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
    (i := 0) F.closed (v := encode (hardcode x (encode x))) (by simp) hF
  have s5 := callVar_eval
    (env := Data.cons (encode (F (hardcode x (encode x)))) v ::
      encode (F (hardcode x (encode x))) :: encode (hardcode x (encode x)) ::
      [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
    (i := 0) U.closed (v := .cons (encode (F (hardcode x (encode x)))) v) (by simp) hU
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons (encode x) v]) (i := 0) (n := .nil)
    (a := encode x) (b := v) (by simp)
    (Eval.let_ (kleeneProg_pair_eval x v) (Eval.let_ (kleeneProg_smn_eval x v)
      (Eval.let_ s3 (Eval.let_ (kleeneProg_pair2_eval x v F) s5))))⟩
  have e1 : (encode x).size = esize x := rfl
  have e2 : (encode (hardcode x (encode x))).size = esize (hardcode x (encode x)) := rfl
  have e3 : (encode (F (hardcode x (encode x)))).size = esize (F (hardcode x (encode x))) :=
    rfl
  simp only [Data.size_cons]
  omega

/-- Backward: a run of `kleeneProg` on `cons (encode x) v` yields a run of
`F (hardcode x (encode x))` on `v` (through `UniversalMachine.halts_of`). -/
theorem kleeneProg_halts_of (U : UniversalMachine) (F : PolyTimeFun Prog Prog) (x : Prog)
    {v r : Data} {T : ℕ} (h : (kleeneProg U.univ F).Runs (.cons (encode x) v) r T) :
    ∃ t, (F (hardcode x (encode x))).Runs v r t := by
  obtain ⟨tF, -, hF⟩ := F.computes (hardcode x (encode x))
  have s3 := callVar_eval
    (env := encode (hardcode x (encode x)) ::
      [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
    (i := 0) F.closed (v := encode (hardcode x (encode x))) (by simp) hF
  change Eval [Data.cons (encode x) v] (.elim 0 .nil _) r T at h
  cases h with
  | elim_nil hget _ => simp at hget
  | elim_cons hget h₁ =>
    rw [Env.get_cons_zero] at hget
    obtain ⟨rfl, rfl⟩ := Data.cons.inj hget
    cases h₁ with
    | let_ h₂ h₃ =>
      obtain ⟨rfl, -⟩ := h₂.deterministic (kleeneProg_pair_eval x v)
      cases h₃ with
      | let_ h₄ h₅ =>
        obtain ⟨rfl, -⟩ := h₄.deterministic (kleeneProg_smn_eval x v)
        cases h₅ with
        | let_ h₆ h₇ =>
          obtain ⟨rfl, -⟩ := h₆.deterministic s3
          cases h₇ with
          | let_ h₈ h₉ =>
            obtain ⟨rfl, -⟩ := h₈.deterministic (kleeneProg_pair2_eval x v F)
            obtain ⟨tU, -, hU⟩ := callVar_runs_rev U.closed h₉
            rw [Env.get_cons_zero] at hU
            exact U.halts_of _ _ _ _ hU

end Prog

/-! ## The fixed-point theorem (blueprint `lem:kleene`; [MNY, Lemma 2.3]) -/

/-- **Efficient Kleene fixed point**: for a polynomial-time map on programs, a closed
program `e` with the same input/output behavior as `F e`, whose runs are bounded by the
runs of `F e` at polynomial overhead. The construction is `e = hardcode G (encode G)` for
the program `G = kleeneProg U.univ F`, and the polynomial `p` is the universal machine's
`bound` shifted by the size of `F e`, plus a linear term and a constant covering the
fixed computation of `F e` and the copies of the input.

Departure from [MNY, Lemma 2.3], which states the runtimes of `e` and `F e` as
*polynomially equivalent*: only the direction "runs of `F e` bound runs of `e`" is used by
the recursive compression argument (it is what makes the fixed point polynomial-time), and
only that direction follows from `UniversalMachine.time_le`. The converse would need a
lower-bound clause on the universal machine ("a simulation is never faster than the
simulated run"); it is omitted to keep the universal-machine obligation minimal and can be
restored with such a clause if a consumer needs it. -/
theorem efficient_fixed_point (F : PolyTimeFun Prog Prog) :
    ∃ (e : Prog) (p : Polynomial ℕ),
      e.WellScoped 1 ∧
      (∀ v r, (∃ t, e.Runs v r t) ↔ ∃ t, (F e).Runs v r t) ∧
      ∀ v r t, (F e).Runs v r t → ∃ t' ≤ p.eval (v.size + t), e.Runs v r t' := by
  obtain ⟨U⟩ := exists_efficient_universal
  have hGw : (Prog.kleeneProg U.univ F).WellScoped 1 := Prog.kleeneProg_wellScoped U.closed F
  refine ⟨hardcode (Prog.kleeneProg U.univ F) (encode (Prog.kleeneProg U.univ F)),
    U.bound.comp (X + C (esize (F (hardcode (Prog.kleeneProg U.univ F)
        (encode (Prog.kleeneProg U.univ F)))))) + C 3 * X +
      C (7 * esize (Prog.kleeneProg U.univ F) +
        esize (hardcode (Prog.kleeneProg U.univ F) (encode (Prog.kleeneProg U.univ F))) +
        F.timeBound.eval (esize (hardcode (Prog.kleeneProg U.univ F)
          (encode (Prog.kleeneProg U.univ F)))) +
        2 * esize (F (hardcode (Prog.kleeneProg U.univ F)
          (encode (Prog.kleeneProg U.univ F)))) + 60),
    hardcode_wellScoped hGw _, fun v r => ⟨?_, ?_⟩, fun v r t h => ?_⟩
  · rintro ⟨t', h⟩
    obtain ⟨T, -, hT⟩ := hardcode_time_rev hGw h
    exact Prog.kleeneProg_halts_of U F _ hT
  · rintro ⟨t, h⟩
    obtain ⟨T, -, hT⟩ := Prog.kleeneProg_runs U F _ h
    exact ⟨_, hardcode_time hGw hT⟩
  · obtain ⟨T, hT, hrun⟩ := Prog.kleeneProg_runs U F _ h
    refine ⟨_, ?_, hardcode_time hGw hrun⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_X, Polynomial.eval_C]
    have hm := polynomial_eval_mono U.bound
      (show esize (F (hardcode (Prog.kleeneProg U.univ F) (encode (Prog.kleeneProg U.univ F)))) +
          v.size + t ≤
        v.size + t + esize (F (hardcode (Prog.kleeneProg U.univ F)
          (encode (Prog.kleeneProg U.univ F)))) by omega)
    have e1 : (encode (Prog.kleeneProg U.univ F)).size = esize (Prog.kleeneProg U.univ F) := rfl
    omega

end MIPRE.Cost
