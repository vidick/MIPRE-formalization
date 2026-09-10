/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Interpreter
import MIPRE.Foundations.Cost.MachineBound
import MIPRE.Foundations.Cost.Unary
import MIPRE.Foundations.Cost.Toolkit

/-!
# The self-interpreter, II: the universal machines

The two universal machines of the toolkit (`Cost/Toolkit.lean`), built from the step
program `stepProg` of `Cost/Interpreter.lean`:

* `univProg` runs the evaluation machine (`Cost/Machine.lean`) from the initial
  configuration of `c` on `v` until a final configuration, as a `loop` whose body tests
  finality (`isFinalProg`) and otherwise steps. A halting run of cost `t` takes at most
  `3 t` machine steps (`eval_steps_count`), each on a configuration of size polynomial in
  `esize c + v.size + t` (`eval_steps_bound_forever`, `size_toData_le`), which gives the
  polynomial overhead (`UniversalMachine.time_le`); conversely a run of the loop is a
  machine run reaching a final configuration, hence a derivation (`halts_iff`).
* `univTProg` is the clocked variant: the loop additionally carries the remaining cost
  budget and a step budget `3 k + 1`, both in unary, and a size guard `Θ` (a polynomial in
  `k + esize c + v.size` computed in unary). The step budget makes the loop terminate; the
  cost budget, decremented by the exact cost of each step (`stepCostProg`, matching
  `stepCost`), decides whether the simulated run halts within cost `k`; the size guard keeps
  the configurations handled by the loop polynomially bounded even when the simulated run
  does not halt — it never fires on a run that halts within the budget, whose
  configurations are bounded by `Θ`.

This discharges `exists_efficient_universal` and `exists_clocked_universal` (blueprint
`lem:universal-tm`).
-/

namespace MIPRE.Cost

open Polynomial

namespace Machine

open Prog

/-! ## The final-configuration test -/

/-- On the encoding of a configuration: `cons nil r` if it is final with value `r`, `nil`
otherwise. -/
def isFinalProg : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil (.elim 5 .nil (.elim 1 (.cons .nil (.var 5)) .nil))))

theorem isFinalProg_wellScoped : isFinalProg.WellScoped 1 := by simp [isFinalProg, WellScoped]

theorem isFinalProg_final (r : Data) (e : Env) :
    ∃ t ≤ r.size + 8, isFinalProg.Runs (Cfg.toData ⟨.ret r, e, []⟩) (.cons .nil r) t := by
  have run : Eval [Cfg.toData ⟨.ret r, e, []⟩] isFinalProg (.cons .nil r) _ :=
    Eval.elim_cons (i := 0) (a := retD r) (b := .cons (.list e) .nil)
      (by simp [Cfg.toData, Ctrl.toData])
      (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := r) (by simp [retD])
        (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
          (Eval.elim_cons (i := 5) (a := .list e) (b := .nil) (by simp)
            (Eval.elim_nil (i := 1) (by simp)
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := r) (by simp)))))))
  exact ⟨_, by omega, run⟩

theorem isFinalProg_nonfinal (c : Cfg) (h : ¬ IsFinal c) :
    ∃ t ≤ 8, isFinalProg.Runs c.toData .nil t := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    have run : Eval [Cfg.toData ⟨.ev p, env, kont⟩] isFinalProg .nil _ :=
      Eval.elim_cons (i := 0) (a := evD p.toData)
        (b := .cons (.list env) (.list (kont.map Frame.toData))) (by simp [Cfg.toData, Ctrl.toData])
        (Eval.elim_cons (i := 0) (a := .nil) (b := p.toData) (by simp [evD])
          (Eval.elim_nil (i := 0) (by simp) (Eval.nil _)))
    exact ⟨_, by omega, run⟩
  | ret v =>
    cases kont with
    | nil => exact absurd ⟨v, env, rfl⟩ h
    | cons f k =>
      have run : Eval [Cfg.toData ⟨.ret v, env, f :: k⟩] isFinalProg .nil _ :=
        Eval.elim_cons (i := 0) (a := retD v)
          (b := .cons (.list env) (.cons (Frame.toData f) (.list (k.map Frame.toData))))
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
              (Eval.elim_cons (i := 5) (a := .list env)
                (b := .cons (Frame.toData f) (.list (k.map Frame.toData))) (by simp)
                (Eval.elim_cons (i := 1) (a := Frame.toData f) (b := .list (k.map Frame.toData))
                  (by simp) (Eval.nil _)))))
      exact ⟨_, by omega, run⟩

/-! ## The interpreter loop -/

/-- Body of the interpreter loop: on a configuration, stop with its value if it is final,
otherwise continue with the next configuration. -/
def interpBody : Prog :=
  .let_ (callVar 0 isFinalProg)
    (.elim 0 (.cons (.cons .nil .nil) (callVar 1 stepProg)) (.cons .nil (.var 1)))

theorem interpBody_wellScoped : interpBody.WellScoped 1 :=
  ⟨callVar_wellScoped (by decide) isFinalProg_wellScoped,
    ⟨by decide, ⟨⟨trivial, trivial⟩, callVar_wellScoped (by decide) stepProg_wellScoped⟩,
      ⟨trivial, by simp [WellScoped]⟩⟩⟩

/-- Cost of one iteration of the interpreter loop on a configuration of size at most `S`. -/
def interpBodyBound (S : ℕ) : ℕ := stepBound S + 3 * S + 30

theorem stepBound_mono {S T : ℕ} (h : S ≤ T) : stepBound S ≤ stepBound T :=
  Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) _

theorem interpBodyBound_mono {S T : ℕ} (h : S ≤ T) : interpBodyBound S ≤ interpBodyBound T := by
  unfold interpBodyBound; have := stepBound_mono h; omega

theorem interpBody_final (r : Data) (e env : Env) :
    ∃ t ≤ 3 * (Cfg.toData ⟨.ret r, e, []⟩).size + 30,
      Eval (Cfg.toData ⟨.ret r, e, []⟩ :: env) interpBody (.cons .nil r) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_final r e
  have run : Eval (Cfg.toData ⟨.ret r, e, []⟩ :: env) interpBody (.cons .nil r) _ :=
    Eval.let_ (callVar_eval (i := 0) isFinalProg_wellScoped (v := Cfg.toData ⟨.ret r, e, []⟩)
        (by simp) h₁)
      (Eval.elim_cons (i := 0) (a := .nil) (b := r) (by simp)
        (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := r) (by simp))))
  refine ⟨_, ?_, run⟩
  have : r.size ≤ (Cfg.toData ⟨.ret r, e, []⟩).size := by
    simp only [Cfg.toData, Ctrl.toData, retD, Data.size_cons]; omega
  omega

theorem interpBody_step (c : Cfg) (h : ¬ IsFinal c) (env : Env) :
    ∃ t ≤ interpBodyBound (Cfg.toData c).size,
      Eval (c.toData :: env) interpBody (.cons (.cons .nil .nil) (step c).toData) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_nonfinal c h
  obtain ⟨t₂, ht₂, h₂⟩ := stepProg_runs c
  have run : Eval (c.toData :: env) interpBody (.cons (.cons .nil .nil) (step c).toData) _ :=
    Eval.let_ (callVar_eval (i := 0) isFinalProg_wellScoped (v := c.toData) (by simp) h₁)
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (callVar_eval (i := 1) stepProg_wellScoped (v := c.toData) (by simp) h₂)))
  refine ⟨_, ?_, run⟩
  unfold interpBodyBound
  omega

/-- The interpreter loop, from the `n`-th configuration of a run that reaches a final
configuration at step `N`, all of whose configurations have size at most `S`. -/
theorem interpLoop_runs (c₀ : Cfg) (S : ℕ) (hS : ∀ n, (step^[n] c₀).toData.size ≤ S)
    (r : Data) (e : Env) (N : ℕ) (hN : step^[N] c₀ = ⟨.ret r, e, []⟩) (env : Env) :
    ∀ m n, n + m = N → ∃ t ≤ (m + 1) * (interpBodyBound S + 1),
      Eval ((step^[n] c₀).toData :: env) (.loop interpBody) r t := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have hn' : step^[n] c₀ = ⟨.ret r, e, []⟩ := by rw [← hN, ← hn, Nat.add_zero]
    rw [hn']
    obtain ⟨t, ht, hb⟩ := interpBody_final r e env
    refine ⟨t + 1, ?_, Eval.loop_stop hb⟩
    have h1 := hS n
    rw [hn'] at h1
    have h2 := Nat.le_mul_of_pos_left (interpBodyBound S + 1) (show 0 < 0 + 1 by omega)
    unfold interpBodyBound at h2 ⊢
    omega
  | succ m ih =>
    intro n hn
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r', e', hr'⟩ := hf
      have hN' : (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r', e', []⟩ := by
        rw [← hN, show N = (m + 1) + n by omega, Function.iterate_add_apply, hr', step_final]
      obtain ⟨rfl, rfl⟩ : r = r' ∧ e = e' := by simpa using hN'
      rw [hr']
      obtain ⟨t, ht, hb⟩ := interpBody_final r e env
      refine ⟨t + 1, ?_, Eval.loop_stop hb⟩
      have h1 := hS n
      rw [hr'] at h1
      have h2 := Nat.le_mul_of_pos_left (interpBodyBound S + 1) (show 0 < m + 1 + 1 by omega)
      unfold interpBodyBound at h2 ⊢
      omega
    · obtain ⟨t₁, ht₁, hb⟩ := interpBody_step (step^[n] c₀) hf env
      obtain ⟨t₂, ht₂, hrest⟩ := ih (n + 1) (by omega)
      rw [Function.iterate_succ_apply'] at hrest
      refine ⟨t₁ + t₂ + 1, ?_, Eval.loop_step hb hrest⟩
      have hmono := interpBodyBound_mono (hS n)
      rw [Nat.succ_mul]
      omega

/-- The loop, backwards: a run of the interpreter loop from a configuration reaches a final
configuration with the same value. -/
theorem interpLoop_rev : ∀ (t : ℕ) (c : Cfg) (env : Env) (r : Data),
    Eval (c.toData :: env) (.loop interpBody) r t → ∃ N e, step^[N] c = ⟨.ret r, e, []⟩ := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
  intro c env r h
  by_cases hf : IsFinal c
  · obtain ⟨r', e', rfl⟩ := hf
    obtain ⟨t₁, -, hb⟩ := interpBody_final r' e' env
    cases h with
    | loop_nil hb' => exact absurd (Eval.deterministic hb hb').1 (by simp)
    | loop_stop hb' =>
      have h1 := (Eval.deterministic hb hb').1
      simp only [Data.cons.injEq, true_and] at h1
      subst h1
      exact ⟨0, e', rfl⟩
    | loop_step hb' _ => exact absurd (Eval.deterministic hb hb').1 (by simp)
  · obtain ⟨t₁, -, hb⟩ := interpBody_step c hf env
    cases h with
    | loop_nil hb' => exact absurd (Eval.deterministic hb hb').1 (by simp)
    | loop_stop hb' => exact absurd (Eval.deterministic hb hb').1 (by simp)
    | loop_step hb' hrest =>
      have h1 := (Eval.deterministic hb hb').1
      simp only [Data.cons.injEq] at h1
      obtain ⟨-, h1⟩ := h1
      subst h1
      obtain ⟨N, e, hN⟩ := ih _ (by omega) (step c) env r hrest
      exact ⟨N + 1, e, by rw [Function.iterate_succ_apply, hN]⟩

/-! ## The universal program -/

/-- On `cons c v`: the initial configuration of `c` on `v`, as data. -/
def univPrelude : Prog :=
  .elim 0 .nil (.cons (.cons .nil (.var 0)) (.cons (.cons (.var 1) .nil) .nil))

theorem univPrelude_runs (c v : Data) :
    ∃ t ≤ c.size + v.size + 10, Eval [Data.cons c v] univPrelude (initData c v) t := by
  have run : Eval [Data.cons c v] univPrelude (initData c v) _ :=
    Eval.elim_cons (i := 0) (a := c) (b := v) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := c) (by simp)))
        (Eval.cons (Eval.cons (Eval.var_of_get (i := 1) (v := v) (by simp)) (Eval.nil _))
          (Eval.nil _)))
  exact ⟨_, by omega, run⟩

/-- The universal program: on `cons (encode c) v`, build the initial configuration of `c`
on `v` and run the interpreter loop. -/
def univProg : Prog := .let_ univPrelude (.loop interpBody)

theorem univProg_wellScoped : univProg.WellScoped 1 :=
  ⟨⟨by decide, trivial, ⟨⟨trivial, by simp [WellScoped]⟩,
      ⟨⟨by simp [WellScoped], trivial⟩, trivial⟩⟩⟩,
    ⟨by decide, interpBody_wellScoped.mono (by omega) _⟩⟩

/-- The size bound on the configurations of a halting run, in terms of
`X = esize c + v.size + t`. -/
def sigmaFun (X : ℕ) : ℕ := cfgSizeBound X (3 * X) X (2 * X)

/-- The time bound of the universal program, in terms of `X = esize c + v.size + t`. -/
def univBoundFun (X : ℕ) : ℕ := (3 * X + 1) * (interpBodyBound (sigmaFun X) + 1) + 2 * X + 11

theorem univProg_time_le (c : Prog) (v r : Data) (t : ℕ) (h : c.Runs v r t) :
    ∃ t' ≤ univBoundFun (esize c + v.size + t), univProg.Runs (.cons (encode c) v) r t' := by
  set X := esize c + v.size + t with hX
  have hb : CfgBound X X X X ⟨.ev c, [v], []⟩ :=
    ⟨fun _ hv => by simp at hv,
      fun p hp => by
        simp only [Ctrl.ev.injEq] at hp
        subst hp
        omega,
      by
        simp only [List.length_cons, List.length_nil]
        have := esize_pos c
        omega,
      fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        omega,
      by simp,
      fun f hf => by simp at hf⟩
  obtain ⟨N, e, hs, hbound⟩ := eval_steps_bound_forever h X X X X hb (by omega)
  have hsize : ∀ n, (step^[n] ⟨.ev c, [v], []⟩).toData.size ≤ sigmaFun X := fun n =>
    size_toData_le ((hbound n).mono le_rfl (by omega) le_rfl (by omega))
  obtain ⟨N', e', hs', hN'⟩ := eval_steps_count h []
  obtain ⟨t₀, ht₀, h₀⟩ := univPrelude_runs c.toData v
  obtain ⟨t₁, ht₁, h₁⟩ := interpLoop_runs ⟨.ev c, [v], []⟩ (sigmaFun X) hsize r e' N' hs'.1
    [Data.cons c.toData v] N' 0 (by omega)
  rw [Function.iterate_zero_apply] at h₁
  refine ⟨t₀ + t₁ + 1, ?_, Eval.let_ h₀ h₁⟩
  have hP : esize c = c.toData.size := rfl
  have hmul := Nat.mul_le_mul_right (interpBodyBound (sigmaFun X) + 1)
    (show N' + 1 ≤ 3 * X + 1 by omega)
  unfold univBoundFun
  omega

theorem univProg_halts_of (c : Prog) (v r : Data) (t' : ℕ)
    (h : univProg.Runs (.cons (encode c) v) r t') : ∃ t, c.Runs v r t := by
  change Eval [Data.cons c.toData v] (.let_ univPrelude (.loop interpBody)) r t' at h
  cases h with
  | let_ h₀ h₁ =>
    obtain ⟨t₀, -, h₀'⟩ := univPrelude_runs c.toData v
    obtain ⟨rfl, -⟩ := Eval.deterministic h₀' h₀
    obtain ⟨N, e, hN⟩ := interpLoop_rev _ ⟨.ev c, [v], []⟩ _ r h₁
    exact (halts_iff c v r).2 ⟨N, e, hN⟩


/-! ## Unary arithmetic for the clock -/

/-- Loop body of `subProg`: on `cons a b` (unary), stop with the flagged difference
`cons (cons nil nil) (b - a)` if `a ≤ b`, with `nil` otherwise. -/
def subBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.cons (.cons .nil .nil) (.var 1)))
    (.elim 3 (.cons .nil .nil) (.cons (.cons .nil .nil) (.cons (.var 3) (.var 1)))))

/-- Unary subtraction with comparison: `subProg` on `cons (ofNat a) (ofNat b)` computes
`subResult a b`. -/
def subProg : Prog := .loop subBody

theorem subBody_wellScoped : subBody.WellScoped 1 := by simp [subBody, WellScoped]

theorem subProg_wellScoped : subProg.WellScoped 1 := ⟨Nat.zero_lt_one, subBody_wellScoped⟩

/-- The value of `subProg`: the flagged difference, or `nil` when `b < a`. -/
def subResult (a b : ℕ) : Data :=
  if a ≤ b then .cons (.cons .nil .nil) (.ofNat (b - a)) else .nil

/-- Cost bound of `subProg` on `cons (ofNat a) (ofNat b)`. -/
def subBound (a b : ℕ) : ℕ := (a + 1) * (2 * a + 2 * b + 14)

theorem subBound_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : subBound a b ≤ subBound a' b' :=
  Nat.mul_le_mul (by omega) (by omega)

theorem subProg_runs (a : ℕ) : ∀ (b : ℕ) (env : Env),
    ∃ t ≤ subBound a b,
      Eval (Data.cons (.ofNat a) (.ofNat b) :: env) subProg (subResult a b) t := by
  induction a with
  | zero =>
    intro b env
    have run : Eval (Data.cons (.ofNat 0) (.ofNat b) :: env) subBody
        (.cons .nil (.cons (.cons .nil .nil) (.ofNat b))) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .ofNat b) (by simp)
        (Eval.elim_nil (i := 0) (by simp [Data.ofNat])
          (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.var_of_get (i := 1) (v := .ofNat b) (by simp)))))
    refine ⟨_, ?_, by simpa [subResult, subProg] using Eval.loop_stop run⟩
    unfold subBound
    try simp only [Data.size_ofNat]
    nlinarith
  | succ a ih =>
    intro b env
    cases b with
    | zero =>
      have run : Eval (Data.cons (.ofNat (a + 1)) (.ofNat 0) :: env) subBody
          (.cons .nil .nil) _ :=
        Eval.elim_cons (i := 0) (a := .ofNat (a + 1)) (b := .ofNat 0) (by simp)
          (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat a) (by simp [Data.ofNat])
            (Eval.elim_nil (i := 3) (by simp [Data.ofNat])
              (Eval.cons (Eval.nil _) (Eval.nil _))))
      refine ⟨_, ?_, by simpa [subResult, subProg] using Eval.loop_stop run⟩
      unfold subBound
      nlinarith
    | succ b =>
      obtain ⟨t, ht, hrest⟩ := ih b env
      have run : Eval (Data.cons (.ofNat (a + 1)) (.ofNat (b + 1)) :: env) subBody
          (.cons (.cons .nil .nil) (.cons (.ofNat a) (.ofNat b))) _ :=
        Eval.elim_cons (i := 0) (a := .ofNat (a + 1)) (b := .ofNat (b + 1)) (by simp)
          (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat a) (by simp [Data.ofNat])
            (Eval.elim_cons (i := 3) (a := .nil) (b := .ofNat b) (by simp [Data.ofNat])
              (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.cons (Eval.var_of_get (i := 3) (v := .ofNat a) (by simp))
                  (Eval.var_of_get (i := 1) (v := .ofNat b) (by simp))))))
      have hres : subResult (a + 1) (b + 1) = subResult a b := by
        simp [subResult, Nat.succ_sub_succ]
      refine ⟨_, ?_, by rw [hres]; exact Eval.loop_step run hrest⟩
      unfold subBound at ht ⊢
      try simp only [Data.size_ofNat]
      nlinarith [ht]

/-- Loop body of `tripleProg`: on `cons (ofNat n) (ofNat m)`, `ofNat (3 n + m)`. -/
def tripleBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil)
      (.cons (.var 1) (.cons .nil (.cons .nil (.cons .nil (.var 3)))))))

/-- `tripleProg` on `cons (ofNat n) (ofNat m)` computes `ofNat (3 n + m)`. -/
def tripleProg : Prog := .loop tripleBody

theorem tripleBody_wellScoped : tripleBody.WellScoped 1 := by simp [tripleBody, WellScoped]

theorem tripleProg_wellScoped : tripleProg.WellScoped 1 := ⟨Nat.zero_lt_one, tripleBody_wellScoped⟩

theorem tripleProg_runs (n : ℕ) : ∀ (m : ℕ) (env : Env),
    ∃ t ≤ (n + 1) * (8 * n + 2 * m + 30),
      Eval (Data.cons (.ofNat n) (.ofNat m) :: env) tripleProg (.ofNat (3 * n + m)) t := by
  induction n with
  | zero =>
    intro m env
    have run : Eval (Data.cons (.ofNat 0) (.ofNat m) :: env) tripleBody
        (.cons .nil (.ofNat m)) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .ofNat m) (by simp)
        (Eval.elim_nil (i := 0) (by simp [Data.ofNat])
          (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .ofNat m) (by simp))))
    refine ⟨_, ?_, by simpa [tripleProg] using Eval.loop_stop run⟩
    try simp only [Data.size_ofNat]
    nlinarith
  | succ n ih =>
    intro m env
    obtain ⟨t, ht, hrest⟩ := ih (m + 3) env
    have run : Eval (Data.cons (.ofNat (n + 1)) (.ofNat m) :: env) tripleBody
        (.cons (.cons .nil .nil) (.cons (.ofNat n) (.ofNat (m + 3)))) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat (n + 1)) (b := .ofNat m) (by simp)
        (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat n) (by simp [Data.ofNat])
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 1) (v := .ofNat n) (by simp))
              (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _)
                (Eval.var_of_get (i := 3) (v := .ofNat m) (by simp))))))))
    have h3 : 3 * (n + 1) + m = 3 * n + (m + 3) := by omega
    refine ⟨_, ?_, by rw [h3]; exact Eval.loop_step run hrest⟩
    try simp only [Data.size_ofNat]
    nlinarith [ht]

/-- Loop body of `repProg`: on `cons (ofNat n) (cons d acc)`, `n` copies of `d` consed
onto `acc`. -/
def repBody : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.var 2) (.cons (.var 2) (.var 3)))))))

/-- `repProg` on `cons (ofNat n) (cons d (list acc))` computes `list (replicate n d ++ acc)`. -/
def repProg : Prog := .loop repBody

theorem repBody_wellScoped : repBody.WellScoped 1 := by simp [repBody, WellScoped]

theorem repProg_wellScoped : repProg.WellScoped 1 := ⟨Nat.zero_lt_one, repBody_wellScoped⟩

/-- Cost bound of `repProg` for `n` copies of a value of size `d` onto an accumulator of
size `a`. -/
def repBound (n d a : ℕ) : ℕ := (n + 1) * (4 * n + 4 * d + 2 * a + 30) + n * (n + 1) * (d + 1)

theorem repProg_runs (n : ℕ) (d : Data) : ∀ (acc : List Data) (env : Env),
    ∃ t ≤ repBound n d.size (Data.list acc).size,
      Eval (Data.cons (.ofNat n) (.cons d (.list acc)) :: env) repProg
        (.list (List.replicate n d ++ acc)) t := by
  induction n with
  | zero =>
    intro acc env
    have run : Eval (Data.cons (.ofNat 0) (.cons d (.list acc)) :: env) repBody
        (.cons .nil (.list acc)) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .cons d (.list acc)) (by simp)
        (Eval.elim_cons (i := 1) (a := d) (b := .list acc) (by simp)
          (Eval.elim_nil (i := 2) (by simp [Data.ofNat])
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .list acc) (by simp)))))
    refine ⟨_, ?_, by simpa [repProg] using Eval.loop_stop run⟩
    unfold repBound
    nlinarith
  | succ n ih =>
    intro acc env
    obtain ⟨t, ht, hrest⟩ := ih (d :: acc) env
    have run : Eval (Data.cons (.ofNat (n + 1)) (.cons d (.list acc)) :: env) repBody
        (.cons (.cons .nil .nil) (.cons (.ofNat n) (.cons d (.list (d :: acc))))) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat (n + 1)) (b := .cons d (.list acc)) (by simp)
        (Eval.elim_cons (i := 1) (a := d) (b := .list acc) (by simp)
          (Eval.elim_cons (i := 2) (a := .nil) (b := .ofNat n) (by simp [Data.ofNat])
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.cons (Eval.var_of_get (i := 1) (v := .ofNat n) (by simp))
                (Eval.cons (Eval.var_of_get (i := 2) (v := d) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 2) (v := d) (by simp))
                    (Eval.var_of_get (i := 3) (v := .list acc) (by simp))))))))
    have hlist : List.replicate (n + 1) d ++ acc = List.replicate n d ++ (d :: acc) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    refine ⟨_, ?_, by rw [hlist]; exact Eval.loop_step run hrest⟩
    unfold repBound at ht ⊢
    try simp only [Data.size_ofNat, Data.list_cons, Data.size_cons] at ht ⊢
    nlinarith [ht]

theorem size_list_replicate (n : ℕ) (d : Data) :
    (Data.list (List.replicate n d)).size = n * (d.size + 1) + 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, Data.list_cons, Data.size_cons, ih]; ring

/-! ## The cost of a step, as a program -/

/-- Cost of a `var` step: `cons body env ↦ ofNat ((getList env body).size + 1)`. -/
def costVar : Prog :=
  .elim 0 .nil (.let_ (.cons (.var 1) (.var 0)) (.let_ (callVar 0 getListProg)
    (.let_ (callVar 0 sizeProg) (.cons .nil (.var 0)))))

/-- Cost of a `const` step: `cons d env ↦ ofNat d.size`. -/
def costConst : Prog := .elim 0 .nil (callVar 0 sizeProg)

/-- The case programs of the cost of an "evaluate" step, indexed by the tag. -/
def costCases : List Prog :=
  [costVar, .const (.ofNat 1), .const (.ofNat 1), .const (.ofNat 1), .const (.ofNat 1), .nil,
    costConst]

theorem costVar_wellScoped : costVar.WellScoped 1 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped,
    callVar_wellScoped (by decide) sizeProg_wellScoped, ⟨trivial, by simp [WellScoped]⟩⟩

theorem costConst_wellScoped : costConst.WellScoped 1 :=
  ⟨by decide, trivial, callVar_wellScoped (by decide) sizeProg_wellScoped⟩

theorem costCases_wellScoped : ∀ c ∈ costCases, c.WellScoped 1 := by
  intro c hc
  simp only [costCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [costVar_wellScoped, trivial, trivial, trivial, trivial, trivial, costConst_wellScoped]

/-- The cost of an "evaluate" step; environment `[tag, payload, ctrl, rest, d]`. -/
def stepCostEv : Prog :=
  .elim 1 .nil (.let_ (.cons (.var 1) (projLeft 5)) (dispatch costCases 1 0))

/-- The cost of a "return" step: `1` at a `loop1` frame, `0` otherwise; environment
`[t₁, t₂, tag, payload, ctrl, rest, d]`. -/
def stepCostRet : Prog :=
  .elim 5 .nil (.elim 1 .nil (.elim 0 .nil (.elim 0 .nil (.elim 1 .nil
    (.elim 1 .nil (.const (.ofNat 1)))))))

/-- On the encoding of a configuration `c`: `ofNat (stepCost c)`. -/
def stepCostProg : Prog := .elim 0 .nil (.elim 0 .nil (.elim 0 stepCostEv stepCostRet))

theorem stepCostRet_wellScoped : stepCostRet.WellScoped 7 := by simp [stepCostRet, WellScoped]

theorem stepCostEv_wellScoped : stepCostEv.WellScoped 5 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [projLeft, WellScoped]⟩,
    dispatch_wellScoped costCases 1 0 8 (by omega) (by omega) costCases_wellScoped⟩

theorem stepCostProg_wellScoped : stepCostProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, stepCostEv_wellScoped, stepCostRet_wellScoped⟩

/-- Cost bound of `stepCostProg` on a configuration of size `S`. -/
def stepCostBound (S : ℕ) : ℕ := (S + 1) * (7 * S + 32) + 13 * S + 50

theorem stepCostBound_mono {S T : ℕ} (h : S ≤ T) : stepCostBound S ≤ stepCostBound T := by
  unfold stepCostBound
  have := Nat.mul_le_mul (Nat.add_le_add_right h 1) (show 7 * S + 32 ≤ 7 * T + 32 by omega)
  omega

/-- The prefix of `stepCostProg` on an "evaluate" configuration, up to the dispatch. -/
theorem stepCostProg_ev (k : ℕ) (body env kont r : Data) {t : ℕ}
    (hk : k < costCases.length)
    (h : Eval [Data.cons body env] (costCases.getD k .nil) r t) :
    ∃ s ≤ t + 2 * body.size + 2 * env.size + kont.size + k + 14,
      Eval [Data.cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)] stepCostProg r s := by
  obtain ⟨s₁, hs₁, hpl⟩ := projLeft_runs
    (E := [Data.ofNat k, body, .nil, .cons (.ofNat k) body, .cons .nil (.cons (.ofNat k) body),
      .cons env kont, .cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)])
    (i := 5) (d := .cons env kont) (by simp)
  obtain ⟨s₂, hs₂, hd⟩ := dispatch_runs costCases k 1 0
    (Data.cons body env :: [Data.ofNat k, body, .nil, .cons (.ofNat k) body,
      .cons .nil (.cons (.ofNat k) body), .cons env kont,
      .cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)])
    (Data.cons body env) r t hk costCases_wellScoped (by simp) (by simp) h
  have run : Eval [Data.cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)] stepCostProg
      r _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil (.cons (.ofNat k) body)) (b := .cons env kont)
      (by simp)
      (Eval.elim_cons (i := 0) (a := .nil) (b := .cons (.ofNat k) body) (by simp)
        (Eval.elim_nil (i := 0) (by simp)
          (Eval.elim_cons (i := 1) (a := .ofNat k) (b := body) (by simp)
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := body) (by simp)) hpl) hd))))
  refine ⟨_, ?_, run⟩
  simp only [Data.size_cons] at hs₁ hs₂
  omega

theorem stepCost_le_size (c : Cfg) : stepCost c ≤ (Cfg.toData c).size := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    cases p with
    | var i =>
      have h1 : (Env.get env i).size ≤ (Data.list env).size := by
        rw [← Data.getList_list]; exact size_getList_le _ _
      simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons,
        Data.size_nil, Data.size_ofNat]
      omega
    | nil => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | const d =>
      simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons]; omega
    | cons h t => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | elim i n c => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | let_ e b => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | loop b => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
  | ret v =>
    cases kont with
    | nil => simp only [stepCost, Cfg.toData, Ctrl.toData, retD, Data.size_cons]; omega
    | cons f k =>
      cases f <;> simp only [stepCost, Cfg.toData, Ctrl.toData, retD, Data.size_cons] <;> omega

/-- `stepCostProg` computes the cost of a step, at a cost quadratic in the size of the
configuration. -/
theorem stepCostProg_runs (c : Cfg) :
    ∃ t ≤ stepCostBound (Cfg.toData c).size,
      stepCostProg.Runs c.toData (.ofNat (stepCost c)) t := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    -- the dispatch environment
    cases p with
    | var i =>
      obtain ⟨tg, htg, hg⟩ := getListProg_runs (.ofNat i) (.list env) []
      set w := Data.getList (.list env) (Data.unaryToNat (.ofNat i)) with hw
      obtain ⟨ts, hts, hsz⟩ := sizeProg_runs w
      have hcase : Eval [Data.cons (.ofNat i) (.list env)] (costCases.getD 0 .nil)
          (.ofNat (w.size + 1)) _ :=
        Eval.elim_cons (i := 0) (a := .ofNat i) (b := .list env) (by simp)
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := .list env) (by simp))
              (Eval.var_of_get (i := 0) (v := .ofNat i) (by simp)))
            (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped
                (v := .cons (.list env) (.ofNat i)) (by simp) hg)
              (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := w) (by simp) hsz)
                (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := .ofNat w.size) (by simp))))))
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 0 (.ofNat i) (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) hcase
      refine ⟨s, ?_, ?_⟩
      · have hw' : w.size ≤ (Data.list env).size := size_getList_le _ _
        obtain ⟨E, hE⟩ : ∃ E, E = (Data.ofNat i).size + (Data.list env).size +
          (Data.list (kont.map Frame.toData)).size + 6 := ⟨_, rfl⟩
        have hS : E ≤ (Cfg.toData ⟨.ev (.var i), env, kont⟩).size := by
          rw [hE]
          simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
            Data.size_ofNat]
          omega
        refine le_trans ?_ (stepCostBound_mono hS)
        have h1 : ((Data.ofNat i).size + 1) * ((Data.list env).size + (Data.ofNat i).size + 12) ≤
            (E + 1) * (2 * E + 12) := Nat.mul_le_mul (by omega) (by omega)
        have h2 : (w.size + 1) * (5 * w.size + 20) ≤ (E + 1) * (5 * E + 20) :=
          Nat.mul_le_mul (by omega) (by omega)
        have h3 : (E + 1) * (7 * E + 32) = (E + 1) * (2 * E + 12) + (E + 1) * (5 * E + 20) := by
          ring
        unfold stepCostBound
        try simp only [Data.size_cons, Data.size_ofNat] at hs hts htg h1 hE ⊢
        omega
      · have hval : stepCost ⟨.ev (.var i), env, kont⟩ = w.size + 1 := by
          simp only [stepCost, hw, Data.unaryToNat_ofNat, Data.getList_list]
        rw [hval]
        simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData] using run
    | nil =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 1 .nil (.list env) (.list (kont.map Frame.toData))
        _ (by simp [costCases]) (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | const d =>
      obtain ⟨ts, hts, hsz⟩ := sizeProg_runs d
      have hcase : Eval [Data.cons d (.list env)] (costCases.getD 6 .nil) (.ofNat d.size) _ :=
        Eval.elim_cons (i := 0) (a := d) (b := .list env) (by simp)
          (callVar_eval (i := 0) sizeProg_wellScoped (v := d) (by simp) hsz)
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 6 d (.list env) (.list (kont.map Frame.toData))
        _ (by simp [costCases]) hcase
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      obtain ⟨E, hE⟩ : ∃ E, E = d.size + (Data.list env).size +
        (Data.list (kont.map Frame.toData)).size + 18 := ⟨_, rfl⟩
      have hS : E ≤ (Cfg.toData ⟨.ev (.const d), env, kont⟩).size := by
        rw [hE]
        simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
          Data.size_ofNat]
        omega
      refine le_trans ?_ (stepCostBound_mono hS)
      have h2 : (d.size + 1) * (5 * d.size + 20) ≤ (E + 1) * (7 * E + 32) :=
        Nat.mul_le_mul (by omega) (by omega)
      unfold stepCostBound
      try simp only [Data.size_cons, Data.size_ofNat] at hs hts ⊢
      omega
    | cons h t =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 2 (.cons h.toData t.toData) (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | elim i n c =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 3 (.cons (.ofNat i) (.cons n.toData c.toData))
        (.list env) (.list (kont.map Frame.toData)) _ (by simp [costCases])
        (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | let_ e b =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 4 (.cons e.toData b.toData) (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) (Eval.const _ (.ofNat 1))
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost]
        using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
    | loop b =>
      obtain ⟨s, hs, run⟩ := stepCostProg_ev 5 b.toData (.list env)
        (.list (kont.map Frame.toData)) _ (by simp [costCases]) (Eval.nil _)
      refine ⟨s, ?_, by simpa [Prog.Runs, Cfg.toData, Ctrl.toData, evD, Prog.toData, stepCost,
        Data.ofNat] using run⟩
      unfold stepCostBound
      try simp only [Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons, Data.size_nil,
        Data.size_ofNat] at hs ⊢
      omega
  | ret v =>
    cases kont with
    | nil =>
      have run : Eval [Cfg.toData ⟨.ret v, env, []⟩] stepCostProg .nil _ :=
        Eval.elim_cons (i := 0) (a := retD v) (b := .cons (.list env) .nil)
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
              (Eval.elim_cons (i := 5) (a := .list env) (b := .nil) (by simp)
                (Eval.elim_nil (i := 1) (by simp) (Eval.nil _)))))
      refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
      unfold stepCostBound
      omega
    | cons f k =>
      cases f with
      | cons1 t env' =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .cons1 t env' :: k⟩] stepCostProg .nil _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.cons1 t env'))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.cons1 t env')) (.list (k.map Frame.toData)))
                  (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.cons1 t env'))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .cons t.toData (.list env'))
                      (by simp [Frame.toData])
                      (Eval.elim_nil (i := 0) (by simp [Data.ofNat]) (Eval.nil _)))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
        unfold stepCostBound
        omega
      | cons2 a =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .cons2 a :: k⟩] stepCostProg .nil _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.cons2 a))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.cons2 a)) (.list (k.map Frame.toData))) (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.cons2 a))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 1) (b := a) (by simp [Frame.toData])
                      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat 0) (by simp [Data.ofNat])
                        (Eval.elim_nil (i := 1) (by simp [Data.ofNat]) (Eval.nil _))))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
        unfold stepCostBound
        omega
      | let1 b env' =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .let1 b env' :: k⟩] stepCostProg .nil _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.let1 b env'))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.let1 b env')) (.list (k.map Frame.toData)))
                  (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.let1 b env'))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 2) (b := .cons b.toData (.list env'))
                      (by simp [Frame.toData])
                      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat 1) (by simp [Data.ofNat])
                        (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat 0)
                          (by simp [Data.ofNat])
                          (Eval.elim_nil (i := 1) (by simp [Data.ofNat]) (Eval.nil _)))))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost, Data.ofNat] using run⟩
        unfold stepCostBound
        omega
      | loop1 b env' =>
        have run : Eval [Cfg.toData ⟨.ret v, env, .loop1 b env' :: k⟩] stepCostProg
            (.ofNat 1) _ :=
          Eval.elim_cons (i := 0) (a := retD v)
            (b := .cons (.list env) (.cons (Frame.toData (.loop1 b env'))
              (.list (k.map Frame.toData)))) (by simp [Cfg.toData, Ctrl.toData])
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
              (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
                (Eval.elim_cons (i := 5) (a := .list env)
                  (b := .cons (Frame.toData (.loop1 b env')) (.list (k.map Frame.toData)))
                  (by simp)
                  (Eval.elim_cons (i := 1) (a := Frame.toData (.loop1 b env'))
                    (b := .list (k.map Frame.toData)) (by simp)
                    (Eval.elim_cons (i := 0) (a := .ofNat 3) (b := .cons b.toData (.list env'))
                      (by simp [Frame.toData])
                      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat 2) (by simp [Data.ofNat])
                        (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat 1)
                          (by simp [Data.ofNat])
                          (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat 0)
                            (by simp [Data.ofNat]) (Eval.const _ (.ofNat 1))))))))))
        refine ⟨_, ?_, by simpa [Prog.Runs, stepCost] using run⟩
        unfold stepCostBound
        try simp only [Data.size_ofNat]
        omega

/-! ## The clocked interpreter loop -/

/-- The state of the clocked loop: the configuration, the remaining cost budget, the
remaining step budget and the size guard (the last three in unary). -/
def clockState (d rem budget theta : Data) : Data := .cons d (.cons rem (.cons budget theta))

/-- Second half of a step of the clocked loop, after the cost subtraction succeeded:
step, then check the size of the new configuration against the guard; environment
`[cons nil nil, rem', sub, cr, nil, budget', nil, budget, theta, rem, r₂, d, r₁, s]`. -/
def clockRest : Prog :=
  .let_ (callVar 11 stepProg)
    (.let_ (.let_ (callVar 0 sizeProg) (.cons (.var 0) (.var 10)))
      (.let_ (callVar 0 subProg)
        (.elim 0 (.cons .nil .nil)
          (.cons (.cons .nil .nil)
            (.cons (.var 4) (.cons (.var 6) (.cons (.var 10) (.var 13))))))))

/-- The step of the clocked loop on a non-final configuration; environment
`[flag, budget, theta, rem, r₂, d, r₁, s]` with `flag = nil`: stop with `nil` if the step
budget is exhausted or the cost of the step exceeds the remaining cost budget, else
`clockRest`. -/
def clockStep : Prog :=
  .elim 1 (.cons .nil .nil)
    (.let_ (.cons (callVar 7 stepCostProg) (.var 5))
      (.let_ (callVar 0 subProg) (.elim 0 (.cons .nil .nil) clockRest)))

/-- Body of the clocked loop: stop with the flagged value of a final configuration,
otherwise `clockStep`. -/
def clockBody : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.let_ (callVar 4 isFinalProg)
    (.elim 0 clockStep (.cons .nil (.cons (.cons .nil .nil) (.var 1)))))))

theorem clockRest_wellScoped : clockRest.WellScoped 14 := by
  simp [clockRest, WellScoped, callVar_wellScoped (show 11 < 14 by decide) stepProg_wellScoped,
    callVar_wellScoped (show 0 < 15 by decide) sizeProg_wellScoped,
    callVar_wellScoped (show 0 < 16 by decide) subProg_wellScoped]

theorem clockStep_wellScoped : clockStep.WellScoped 8 := by
  simp [clockStep, WellScoped, callVar_wellScoped (show 7 < 10 by decide) stepCostProg_wellScoped,
    callVar_wellScoped (show 0 < 11 by decide) subProg_wellScoped, clockRest_wellScoped]

theorem clockBody_wellScoped : clockBody.WellScoped 1 := by
  simp [clockBody, WellScoped, callVar_wellScoped (show 4 < 7 by decide) isFinalProg_wellScoped,
    clockStep_wellScoped]

/-- Cost bound of `sizeProg` on a value of size `s` (as in `sizeProg_runs`). -/
def sizeBound (s : ℕ) : ℕ := (s + 1) * (5 * s + 20) + s + 6

theorem sizeBound_mono {s t : ℕ} (h : s ≤ t) : sizeBound s ≤ sizeBound t := by
  unfold sizeBound
  have := Nat.mul_le_mul (Nat.add_le_add_right h 1) (show 5 * s + 20 ≤ 5 * t + 20 by omega)
  omega

/-- Bound on the second half of a step of the clocked loop, in terms of the configuration
size `S`, the guard `Θ`, the remaining cost `rem` and the step budget `b`. -/
def clockRestBound (S Θ rem b : ℕ) : ℕ :=
  S + stepBound S + sizeBound (stepBound S) + subBound (stepBound S) Θ + 6 * stepBound S +
    6 * Θ + 2 * rem + 2 * b + 50

/-- Bound of one iteration of the clocked loop, on configurations of size at most `Θ`,
with cost budget at most `k` (and step budget at most `3 k + 1`). -/
def clockBodyBound (Θ k : ℕ) : ℕ :=
  stepCostBound Θ + subBound Θ k + stepBound Θ + sizeBound (stepBound Θ) +
    subBound (stepBound Θ) Θ + 6 * stepBound Θ + 12 * Θ + 30 * k + 200

theorem clockBody_final (r : Data) (e : Env) (rem budget theta : Data) (env : Env) :
    ∃ t ≤ 3 * (Cfg.toData ⟨.ret r, e, []⟩).size + 30,
      Eval (clockState (Cfg.toData ⟨.ret r, e, []⟩) rem budget theta :: env) clockBody
        (.cons .nil (.cons (.cons .nil .nil) r)) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_final r e
  have run : Eval (clockState (Cfg.toData ⟨.ret r, e, []⟩) rem budget theta :: env) clockBody
      (.cons .nil (.cons (.cons .nil .nil) r)) _ :=
    Eval.elim_cons (i := 0) (a := Cfg.toData ⟨.ret r, e, []⟩) (b := .cons rem (.cons budget theta))
      (by simp [clockState])
      (Eval.elim_cons (i := 1) (a := rem) (b := .cons budget theta) (by simp)
        (Eval.elim_cons (i := 1) (a := budget) (b := theta) (by simp)
          (Eval.let_ (callVar_eval (i := 4) isFinalProg_wellScoped
              (v := Cfg.toData ⟨.ret r, e, []⟩) (by simp) h₁)
            (Eval.elim_cons (i := 0) (a := .nil) (b := r) (by simp)
              (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.var_of_get (i := 1) (v := r) (by simp))))))))
  refine ⟨_, ?_, run⟩
  have : r.size ≤ (Cfg.toData ⟨.ret r, e, []⟩).size := by
    simp only [Cfg.toData, Ctrl.toData, retD, Data.size_cons]; omega
  omega

theorem clockBody_budget0 (c : Cfg) (hc : ¬ IsFinal c) (rem theta : Data) (env : Env) :
    ∃ t ≤ (Cfg.toData c).size + 20,
      Eval (clockState c.toData rem (.ofNat 0) theta :: env) clockBody (.cons .nil .nil) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_nonfinal c hc
  have run : Eval (clockState c.toData rem (.ofNat 0) theta :: env) clockBody
      (.cons .nil .nil) _ :=
    Eval.elim_cons (i := 0) (a := c.toData) (b := .cons rem (.cons (.ofNat 0) theta))
      (by simp [clockState])
      (Eval.elim_cons (i := 1) (a := rem) (b := .cons (.ofNat 0) theta) (by simp)
        (Eval.elim_cons (i := 1) (a := .ofNat 0) (b := theta) (by simp)
          (Eval.let_ (callVar_eval (i := 4) isFinalProg_wellScoped (v := c.toData) (by simp) h₁)
            (Eval.elim_nil (i := 0) (by simp)
              (Eval.elim_nil (i := 1) (by simp [Data.ofNat])
                (Eval.cons (Eval.nil _) (Eval.nil _)))))))
  exact ⟨_, by omega, run⟩

/-- The environment of `clockStep` after the cost subtraction, on a configuration `c` with
remaining cost `rem`, step budget `b + 1` and guard `Θ`. -/
def clockEnv (c : Cfg) (rem b Θ : ℕ) (env : Env) : Env :=
  subResult (stepCost c) rem :: .cons (.ofNat (stepCost c)) (.ofNat rem) :: .nil :: .ofNat b ::
    .nil :: .ofNat (b + 1) :: .ofNat Θ :: .ofNat rem :: .cons (.ofNat (b + 1)) (.ofNat Θ) ::
    c.toData :: .cons (.ofNat rem) (.cons (.ofNat (b + 1)) (.ofNat Θ)) ::
    clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env

/-- The first half of a step of the clocked loop on a non-final configuration with a
positive step budget: the finality test, the cost of the step and its subtraction. -/
theorem clockBody_prefix (c : Cfg) (hc : ¬ IsFinal c) (rem b Θ : ℕ) (env : Env) (r : Data)
    {t : ℕ} (hrest : Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest) r t) :
    ∃ s ≤ t + stepCostBound (Cfg.toData c).size + subBound (stepCost c) rem +
        4 * (Cfg.toData c).size + 4 * rem + 30,
      Eval (clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env) clockBody r s := by
  obtain ⟨t₁, ht₁, h₁⟩ := isFinalProg_nonfinal c hc
  obtain ⟨t₂, ht₂, h₂⟩ := stepCostProg_runs c
  obtain ⟨t₃, ht₃, h₃⟩ := subProg_runs (stepCost c) rem []
  have hcost := stepCost_le_size c
  have run : Eval (clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env) clockBody
      r _ :=
    Eval.elim_cons (i := 0) (a := c.toData)
      (b := .cons (.ofNat rem) (.cons (.ofNat (b + 1)) (.ofNat Θ))) (by simp [clockState])
      (Eval.elim_cons (i := 1) (a := .ofNat rem) (b := .cons (.ofNat (b + 1)) (.ofNat Θ)) (by simp)
        (Eval.elim_cons (i := 1) (a := .ofNat (b + 1)) (b := .ofNat Θ) (by simp)
          (Eval.let_ (callVar_eval (i := 4) isFinalProg_wellScoped (v := c.toData) (by simp) h₁)
            (Eval.elim_nil (i := 0) (by simp)
              (Eval.elim_cons (i := 1) (a := .nil) (b := .ofNat b) (by simp [Data.ofNat])
                (Eval.let_ (Eval.cons (callVar_eval (i := 7) stepCostProg_wellScoped
                      (v := c.toData) (by simp) h₂)
                    (Eval.var_of_get (i := 5) (v := .ofNat rem) (by simp)))
                  (Eval.let_ (callVar_eval (i := 0) subProg_wellScoped
                      (v := .cons (.ofNat (stepCost c)) (.ofNat rem)) (by simp) h₃)
                    hrest)))))))
  refine ⟨_, ?_, run⟩
  try simp only [Data.size_cons, Data.size_ofNat] at *
  omega

theorem clockRest_stop (c : Cfg) (rem b Θ : ℕ) (env : Env) (hle : stepCost c ≤ rem)
    (hΘ : Θ < ((step c).toData).size) :
    ∃ t ≤ clockRestBound (Cfg.toData c).size Θ rem b,
      Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest) (.cons .nil .nil) t := by
  obtain ⟨ts, hts, hstep⟩ := stepProg_runs c
  obtain ⟨tz, htz, hsz⟩ := sizeProg_runs (step c).toData
  obtain ⟨tu, htu, hsub⟩ := subProg_runs ((step c).toData).size Θ []
  have hsize : ((step c).toData).size ≤ ts := hstep.size_le
  have run : Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest)
      (.cons .nil .nil) _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := .ofNat (rem - stepCost c))
      (by simp [clockEnv, subResult, hle])
      (Eval.let_ (callVar_eval (i := 11) stepProg_wellScoped (v := c.toData) (by simp [clockEnv])
          hstep)
        (Eval.let_ (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := (step c).toData)
              (by simp) hsz)
            (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat ((step c).toData).size) (by simp))
              (Eval.var_of_get (i := 10) (v := .ofNat Θ) (by simp [clockEnv]))))
          (Eval.let_ (callVar_eval (i := 0) subProg_wellScoped
              (v := .cons (.ofNat ((step c).toData).size) (.ofNat Θ)) (by simp) hsub)
            (Eval.elim_nil (i := 0) (by simp [subResult, Nat.not_le.2 hΘ])
              (Eval.cons (Eval.nil _) (Eval.nil _))))))
  refine ⟨_, ?_, run⟩
  have h1 : tz ≤ sizeBound ((step c).toData).size := htz
  have h2 := sizeBound_mono (hsize.trans hts)
  have h3 := subBound_mono (hsize.trans hts) (le_refl Θ)
  unfold clockRestBound
  try simp only [Data.size_cons, Data.size_ofNat] at *
  omega

theorem clockRest_continue (c : Cfg) (rem b Θ : ℕ) (env : Env) (hle : stepCost c ≤ rem)
    (hΘ : ((step c).toData).size ≤ Θ) :
    ∃ t ≤ clockRestBound (Cfg.toData c).size Θ rem b,
      Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest)
        (.cons (.cons .nil .nil)
          (clockState (step c).toData (.ofNat (rem - stepCost c)) (.ofNat b) (.ofNat Θ))) t := by
  obtain ⟨ts, hts, hstep⟩ := stepProg_runs c
  obtain ⟨tz, htz, hsz⟩ := sizeProg_runs (step c).toData
  obtain ⟨tu, htu, hsub⟩ := subProg_runs ((step c).toData).size Θ []
  have hsize : ((step c).toData).size ≤ ts := hstep.size_le
  have run : Eval (clockEnv c rem b Θ env) (.elim 0 (.cons .nil .nil) clockRest)
      (.cons (.cons .nil .nil)
        (clockState (step c).toData (.ofNat (rem - stepCost c)) (.ofNat b) (.ofNat Θ))) _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := .ofNat (rem - stepCost c))
      (by simp [clockEnv, subResult, hle])
      (Eval.let_ (callVar_eval (i := 11) stepProg_wellScoped (v := c.toData) (by simp [clockEnv])
          hstep)
        (Eval.let_ (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := (step c).toData)
              (by simp) hsz)
            (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat ((step c).toData).size) (by simp))
              (Eval.var_of_get (i := 10) (v := .ofNat Θ) (by simp [clockEnv]))))
          (Eval.let_ (callVar_eval (i := 0) subProg_wellScoped
              (v := .cons (.ofNat ((step c).toData).size) (.ofNat Θ)) (by simp) hsub)
            (Eval.elim_cons (i := 0) (a := .cons .nil .nil)
              (b := .ofNat (Θ - ((step c).toData).size)) (by simp [subResult, hΘ])
              (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.cons (Eval.var_of_get (i := 4) (v := (step c).toData) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 6) (v := .ofNat (rem - stepCost c)) (by simp))
                    (Eval.cons (Eval.var_of_get (i := 10) (v := .ofNat b) (by simp [clockEnv]))
                      (Eval.var_of_get (i := 13) (v := .ofNat Θ) (by simp [clockEnv]))))))))))
  refine ⟨_, ?_, run⟩
  have h1 : tz ≤ sizeBound ((step c).toData).size := htz
  have h2 := sizeBound_mono (hsize.trans hts)
  have h3 := subBound_mono (hsize.trans hts) (le_refl Θ)
  unfold clockRestBound
  try simp only [Data.size_cons, Data.size_ofNat] at *
  omega

/-- The cost of one non-final iteration is at most `clockBodyBound Θ k`. -/
theorem clockBody_cost_le {S Θ k rem b cost t₂ t₁ : ℕ} (hS : S ≤ Θ) (hrem : rem ≤ k)
    (hb : b ≤ 3 * k) (hcost : cost ≤ S) (ht₂ : t₂ ≤ clockRestBound S Θ rem b)
    (ht₁ : t₁ ≤ t₂ + stepCostBound S + subBound cost rem + 4 * S + 4 * rem + 30) :
    t₁ ≤ clockBodyBound Θ k := by
  have h1 : stepCostBound S ≤ stepCostBound Θ := stepCostBound_mono hS
  have h2 : subBound cost rem ≤ subBound Θ k := subBound_mono (hcost.trans hS) hrem
  have h3 : stepBound S ≤ stepBound Θ := stepBound_mono hS
  have h4 : sizeBound (stepBound S) ≤ sizeBound (stepBound Θ) := sizeBound_mono h3
  have h5 : subBound (stepBound S) Θ ≤ subBound (stepBound Θ) Θ := subBound_mono h3 le_rfl
  unfold clockRestBound at ht₂
  unfold clockBodyBound
  omega

/-! ## The semantics of the clocked loop -/

/-- The value of a configuration: the returned value, `nil` on an "evaluate" control. -/
def Cfg.val : Cfg → Data
  | ⟨.ret v, _, _⟩ => v
  | ⟨.ev _, _, _⟩ => .nil

open Classical in
/-- The result of the clocked loop from the `n`-th configuration of the run of `c₀`, with
step budget `b`, cost budget `k` and size guard `Θ`. -/
noncomputable def clockRun (c₀ : Cfg) (k Θ : ℕ) : ℕ → ℕ → Data
  | 0, n => if IsFinal (step^[n] c₀) then .cons (.cons .nil .nil) (step^[n] c₀).val else .nil
  | b + 1, n =>
    if IsFinal (step^[n] c₀) then .cons (.cons .nil .nil) (step^[n] c₀).val
    else if costSum c₀ (n + 1) ≤ k ∧ (step^[n + 1] c₀).toData.size ≤ Θ then
      clockRun c₀ k Θ b (n + 1)
    else .nil

theorem clockBodyBound_ge (Θ k : ℕ) : 12 * Θ + 200 ≤ clockBodyBound Θ k := by
  unfold clockBodyBound; omega

/-- The clocked loop computes `clockRun`. -/
theorem clockLoop_runs (c₀ : Cfg) (k Θ : ℕ) (env : Env) : ∀ (b n : ℕ), b ≤ 3 * k + 1 →
    costSum c₀ n ≤ k → (step^[n] c₀).toData.size ≤ Θ →
    ∃ t ≤ (b + 1) * (clockBodyBound Θ k + 1),
      Eval (clockState (step^[n] c₀).toData (.ofNat (k - costSum c₀ n)) (.ofNat b) (.ofNat Θ)
          :: env) (.loop clockBody) (clockRun c₀ k Θ b n) t := by
  intro b
  induction b with
  | zero =>
    intro n hb hcost hΘ
    have hB := clockBodyBound_ge Θ k
    have hmul := Nat.le_mul_of_pos_left (clockBodyBound Θ k + 1) (show 0 < 0 + 1 by omega)
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r, e, hr⟩ := id hf
      simp only [clockRun, if_pos hf]
      rw [hr] at hΘ ⊢
      obtain ⟨t, ht, hbody⟩ :=
        clockBody_final r e (.ofNat (k - costSum c₀ n)) (.ofNat 0) (.ofNat Θ) env
      exact ⟨t + 1, by omega, Eval.loop_stop hbody⟩
    · simp only [clockRun, if_neg hf]
      obtain ⟨t, ht, hbody⟩ := clockBody_budget0 (step^[n] c₀) hf (.ofNat (k - costSum c₀ n))
        (.ofNat Θ) env
      exact ⟨t + 1, by omega, Eval.loop_stop hbody⟩
  | succ b ih =>
    intro n hb hcost hΘ
    have hB := clockBodyBound_ge Θ k
    have hmul := Nat.le_mul_of_pos_left (clockBodyBound Θ k + 1) (show 0 < b + 1 + 1 by omega)
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r, e, hr⟩ := id hf
      simp only [clockRun, if_pos hf]
      rw [hr] at hΘ ⊢
      obtain ⟨t, ht, hbody⟩ :=
        clockBody_final r e (.ofNat (k - costSum c₀ n)) (.ofNat (b + 1)) (.ofNat Θ) env
      exact ⟨t + 1, by omega, Eval.loop_stop hbody⟩
    · simp only [clockRun, if_neg hf]
      have hcost' := stepCost_le_size (step^[n] c₀)
      by_cases hc : costSum c₀ (n + 1) ≤ k
      · have hle : stepCost (step^[n] c₀) ≤ k - costSum c₀ n := by
          rw [costSum_succ] at hc; omega
        have hrem : k - costSum c₀ n - stepCost (step^[n] c₀) = k - costSum c₀ (n + 1) := by
          rw [costSum_succ]; omega
        by_cases hΘ' : (step^[n + 1] c₀).toData.size ≤ Θ
        · rw [if_pos ⟨hc, hΘ'⟩]
          obtain ⟨t₂, ht₂, hrest⟩ := clockRest_continue (step^[n] c₀) (k - costSum c₀ n) b Θ env
            hle (by rwa [Function.iterate_succ_apply'] at hΘ')
          obtain ⟨t₁, ht₁, hbody⟩ := clockBody_prefix (step^[n] c₀) hf (k - costSum c₀ n) b Θ
            env _ hrest
          obtain ⟨t₃, ht₃, hloop⟩ := ih (n + 1) (by omega) hc hΘ'
          rw [Function.iterate_succ_apply', ← hrem] at hloop
          refine ⟨t₁ + t₃ + 1, ?_, Eval.loop_step hbody hloop⟩
          have : t₁ ≤ clockBodyBound Θ k := clockBody_cost_le hΘ (by omega) (by omega) hcost' ht₂ ht₁
          rw [Nat.succ_mul]
          omega
        · rw [if_neg (fun h => hΘ' h.2)]
          obtain ⟨t₂, ht₂, hrest⟩ := clockRest_stop (step^[n] c₀) (k - costSum c₀ n) b Θ env
            hle (by rw [Function.iterate_succ_apply'] at hΘ'; omega)
          obtain ⟨t₁, ht₁, hbody⟩ := clockBody_prefix (step^[n] c₀) hf (k - costSum c₀ n) b Θ
            env _ hrest
          refine ⟨t₁ + 1, ?_, Eval.loop_stop hbody⟩
          have : t₁ ≤ clockBodyBound Θ k := clockBody_cost_le hΘ (by omega) (by omega) hcost' ht₂ ht₁
          omega
      · rw [if_neg (fun h => hc h.1)]
        have hlt : k - costSum c₀ n < stepCost (step^[n] c₀) := by
          rw [costSum_succ] at hc; omega
        have hrest : Eval (clockEnv (step^[n] c₀) (k - costSum c₀ n) b Θ env)
            (.elim 0 (.cons .nil .nil) clockRest) (.cons .nil .nil) _ :=
          Eval.elim_nil (i := 0) (by simp [clockEnv, subResult, Nat.not_le.2 hlt])
            (Eval.cons (Eval.nil _) (Eval.nil _))
        obtain ⟨t₁, ht₁, hbody⟩ := clockBody_prefix (step^[n] c₀) hf (k - costSum c₀ n) b Θ
          env _ hrest
        refine ⟨t₁ + 1, ?_, Eval.loop_stop hbody⟩
        have : t₁ ≤ clockBodyBound Θ k := clockBody_cost_le hΘ (by omega) (by omega) hcost'
          (show 4 ≤ clockRestBound (Cfg.toData (step^[n] c₀)).size Θ (k - costSum c₀ n) b by
            unfold clockRestBound; omega) ht₁
        omega

/-- On a run reaching a final configuration at step `N` within the cost budget, whose
configurations are all within the guard, the clocked loop returns the flagged value. -/
theorem clockRun_of_final (c₀ : Cfg) (k Θ : ℕ) (N : ℕ) (r : Data) (e : Env)
    (hN : step^[N] c₀ = ⟨.ret r, e, []⟩) (hcost : costSum c₀ N ≤ k)
    (hΘ : ∀ n, (step^[n] c₀).toData.size ≤ Θ) :
    ∀ b n, n ≤ N → N ≤ n + b → clockRun c₀ k Θ b n = .cons (.cons .nil .nil) r := by
  intro b
  induction b with
  | zero =>
    intro n h1 h2
    have hn : n = N := by omega
    subst hn
    simp only [clockRun, if_pos (show IsFinal (step^[n] c₀) from ⟨r, e, hN⟩), hN, Cfg.val]
  | succ b ih =>
    intro n h1 h2
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r', e', hr'⟩ := id hf
      have hN' : (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r', e', []⟩ := by
        rw [← hN, show N = (N - n) + n by omega, Function.iterate_add_apply, hr', step_final]
      obtain ⟨rfl, rfl⟩ : r = r' ∧ e = e' := by simpa using hN'
      simp only [clockRun, if_pos hf, hr', Cfg.val]
    · have hlt : n < N := by
        rcases Nat.lt_or_ge n N with h | h
        · exact h
        · exact absurd ⟨r, e, by
            rw [show n = (n - N) + N by omega, Function.iterate_add_apply, hN, step_final]⟩ hf
      have hc : costSum c₀ (n + 1) ≤ k :=
        (costSum_le_of_le c₀ (show n + 1 ≤ N by omega)).trans hcost
      simp only [clockRun, if_neg hf, if_pos (And.intro hc (hΘ (n + 1)))]
      exact ih (n + 1) (by omega) (by omega)

/-- If `c` does not halt on `v` within cost `k`, the clocked loop returns `nil`. -/
theorem clockRun_of_not (c : Prog) (v : Data) (k Θ : ℕ)
    (hno : ¬ ∃ r t, t ≤ k ∧ c.Runs v r t) :
    ∀ b n, costSum ⟨.ev c, [v], []⟩ n ≤ k → clockRun ⟨.ev c, [v], []⟩ k Θ b n = .nil := by
  have hnf : ∀ n, costSum ⟨.ev c, [v], []⟩ n ≤ k → ¬ IsFinal (step^[n] ⟨.ev c, [v], []⟩) := by
    rintro n hn ⟨r, e, hr⟩
    obtain ⟨r', t', M, e', N', hM, hev, hs⟩ := eval_of_steps n c [v] [] r e hr
    refine hno ⟨r', t', ?_, hev⟩
    have := costSum_le_of_le ⟨.ev c, [v], []⟩ (show M ≤ n by omega)
    rw [hs.2] at this
    omega
  intro b
  induction b with
  | zero => intro n hn; simp only [clockRun, if_neg (hnf n hn)]
  | succ b ih =>
    intro n hn
    simp only [clockRun, if_neg (hnf n hn)]
    split_ifs with h
    · exact ih (n + 1) h.1
    · rfl

/-- The clocked loop from the initial configuration, with step budget `3 k + 1`, computes
`clockedResult c v k`, provided the guard `Θ` bounds the configurations of any run of `c`
on `v` of cost at most `k`. -/
theorem clockRun_eq (c : Prog) (v : Data) (k Θ : ℕ)
    (hΘ : ∀ r t, t ≤ k → c.Runs v r t → ∀ n, (step^[n] ⟨.ev c, [v], []⟩).toData.size ≤ Θ) :
    clockRun ⟨.ev c, [v], []⟩ k Θ (3 * k + 1) 0 = clockedResult c v k := by
  by_cases h : ∃ r t, t ≤ k ∧ c.Runs v r t
  · obtain ⟨t, ht, hrun⟩ := h.choose_spec
    obtain ⟨N, e, hs, hN⟩ := eval_steps_count hrun []
    rw [clockRun_of_final ⟨.ev c, [v], []⟩ k Θ N h.choose e hs.1 (by rw [hs.2]; exact ht)
      (hΘ _ _ ht hrun) (3 * k + 1) 0 (by omega) (by omega)]
    simp only [clockedResult, evalWithin, dif_pos h]
  · rw [clockRun_of_not c v k Θ h (3 * k + 1) 0 (by simp [costSum])]
    simp only [clockedResult, evalWithin, dif_neg h]

/-! ## The clocked universal program -/

/-- The size guard of the clocked simulation, as a function of `X = k + esize c + v.size`:
`Y = 9 X + 4` (two applications of `tripleProg`)... -/
def guardFun (X : ℕ) : ℕ := 3 * (3 * X + 1) + 1

/-- ...the size of `Y` copies of `ofNat Y`... -/
def t1Fun (X : ℕ) : ℕ := guardFun X * (2 * guardFun X + 1 + 1) + 1

/-- ...and the size of `Y` copies of that list: the guard `Θ`. -/
def thetaFun (X : ℕ) : ℕ := guardFun X * (t1Fun X + 1) + 1

theorem guardFun_le_thetaFun (X : ℕ) : guardFun X ≤ thetaFun X := by
  unfold thetaFun
  have := Nat.le_mul_of_pos_right (guardFun X) (show 0 < t1Fun X + 1 by omega)
  omega

/-- The guard dominates the size bound of the configurations of a run of cost at most `k`. -/
theorem sigmaFun_le_thetaFun (X : ℕ) : sigmaFun X ≤ thetaFun X := by
  unfold sigmaFun cfgSizeBound thetaFun t1Fun guardFun
  nlinarith [Nat.zero_le (X * X * X), Nat.zero_le (X * X), Nat.zero_le X]

/-- The clocked universal program: on `cons (ofNat k) (cons (encode c) v)`, compute
`X = k + esize c + v.size` and the guard `Θ` in unary, build the initial configuration and
the state of the clocked loop, and run it with step budget `3 k + 1`. -/
def univTProg : Prog :=
  .elim 0 .nil (.elim 1 .nil
    (.let_ (callVar 0 sizeProg)
    (.let_ (callVar 2 sizeProg)
    (.let_ (.cons (.var 0) (.var 1))
    (.let_ (callVar 0 addProg)
    (.let_ (.cons (.var 6) (.var 0))
    (.let_ (callVar 0 addProg)
    (.let_ (.cons (.var 0) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 0) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 0) (.cons (.var 0) .nil))
    (.let_ (callVar 0 repProg)
    (.let_ (.cons (.var 2) (.cons (.var 0) .nil))
    (.let_ (callVar 0 repProg)
    (.let_ (callVar 0 sizeProg)
    (.let_ (.cons (.cons .nil (.var 15)) (.cons (.cons (.var 16) .nil) .nil))
    (.let_ (.cons (.var 18) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 2) (.cons (.var 20) (.cons (.var 0) (.var 3))))
      (.loop clockBody)))))))))))))))))))))

theorem univTProg_wellScoped : univTProg.WellScoped 1 := by
  simp [univTProg, WellScoped, callVar_wellScoped, sizeProg_wellScoped, addProg_wellScoped,
    tripleProg_wellScoped, repProg_wellScoped,
    Prog.WellScoped.mono (show 1 ≤ 24 by omega) clockBody clockBody_wellScoped]

/-- Cost bound of `addProg` (as in `addProg_runs`). -/
def addBound (a b : ℕ) : ℕ := (a + 1) * (4 * a + 2 * b + 15)

theorem addBound_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : addBound a b ≤ addBound a' b' :=
  Nat.mul_le_mul (by omega) (by omega)

/-- Cost bound of `tripleProg` (as in `tripleProg_runs`). -/
def tripleBound (n m : ℕ) : ℕ := (n + 1) * (8 * n + 2 * m + 30)

theorem clockBodyBound_mono_right {Θ k k' : ℕ} (h : k ≤ k') :
    clockBodyBound Θ k ≤ clockBodyBound Θ k' := by
  unfold clockBodyBound
  have := subBound_mono (le_refl Θ) h
  omega

/-- The time bound of the clocked universal program, as a function of
`X = k + esize c + v.size`. -/
def univTBoundFun (X : ℕ) : ℕ :=
  2 * sizeBound X + addBound X X + addBound X X + tripleBound X 1 + tripleBound (3 * X + 1) 1 +
    tripleBound X 1 + repBound (guardFun X) (2 * guardFun X + 1) 1 +
    repBound (guardFun X) (t1Fun X) 1 + sizeBound (thetaFun X) +
    (3 * X + 2) * (clockBodyBound (thetaFun X) X + 1) +
    20 * thetaFun X + 20 * t1Fun X + 60 * guardFun X + 100 * X + 500

theorem univTProg_runs (c : Prog) (v : Data) (k : ℕ) :
    ∃ t ≤ univTBoundFun (k + esize c + v.size),
      univTProg.Runs (.cons (.ofNat k) (.cons (encode c) v)) (clockedResult c v k) t := by
  set X := k + esize c + v.size with hX
  have hPX : c.toData.size ≤ X := by rw [← Prog.esize_eq_size_toData]; omega
  have hVX : v.size ≤ X := by omega
  have hkX : k ≤ X := by omega
  have hP1 : 1 ≤ c.toData.size := Data.size_pos _
  -- the components of the prelude
  obtain ⟨tP, htP, hP⟩ := sizeProg_runs c.toData
  obtain ⟨tV, htV, hV⟩ := sizeProg_runs v
  obtain ⟨tA1, htA1, hA1⟩ := addProg_runs v.size c.toData.size []
  obtain ⟨tA2, htA2, hA2⟩ := addProg_runs k (v.size + c.toData.size) []
  have hX₀ : k + (v.size + c.toData.size) = X := by rw [hX, Prog.esize_eq_size_toData]; omega
  rw [hX₀] at hA2
  obtain ⟨tT1, htT1, hT1⟩ := tripleProg_runs X 1 []
  obtain ⟨tT2, htT2, hT2⟩ := tripleProg_runs (3 * X + 1) 1 []
  have hY : 3 * (3 * X + 1) + 1 = guardFun X := rfl
  rw [hY] at hT2
  obtain ⟨tR1, htR1, hR1⟩ := repProg_runs (guardFun X) (.ofNat (guardFun X)) [] []
  rw [List.append_nil] at hR1
  obtain ⟨tR2, htR2, hR2⟩ :=
    repProg_runs (guardFun X) (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) [] []
  rw [List.append_nil] at hR2
  have hT1s : (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))).size = t1Fun X := by
    rw [size_list_replicate, Data.size_ofNat]; rfl
  have hT2s : (Data.list (List.replicate (guardFun X)
      (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))))).size = thetaFun X := by
    rw [size_list_replicate, hT1s]; rfl
  obtain ⟨tΘ, htΘ, hΘ⟩ := sizeProg_runs (Data.list (List.replicate (guardFun X)
    (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X))))))
  rw [hT2s] at hΘ htΘ
  obtain ⟨tT3, htT3, hT3⟩ := tripleProg_runs k 1 []
  -- the guard bounds the configurations of a run within the budget
  have hb : CfgBound X X X X ⟨.ev c, [v], []⟩ :=
    ⟨fun _ hv => by simp at hv,
      fun p hp => by
        simp only [Ctrl.ev.injEq] at hp
        subst hp
        omega,
      by
        simp only [List.length_cons, List.length_nil]
        omega,
      fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        omega,
      by simp,
      fun f hf => by simp at hf⟩
  have hguard : ∀ r t, t ≤ k → c.Runs v r t →
      ∀ n, (step^[n] ⟨.ev c, [v], []⟩).toData.size ≤ thetaFun X := by
    intro r t ht hrun n
    obtain ⟨N, e, hs, hbound⟩ := eval_steps_bound_forever hrun X X X X hb (by omega)
    exact (size_toData_le ((hbound n).mono le_rfl (by omega) le_rfl (by omega))).trans
      (sigmaFun_le_thetaFun X)
  have h0 : (Cfg.toData ⟨.ev c, [v], []⟩).size ≤ thetaFun X := by
    have := guardFun_le_thetaFun X
    unfold guardFun at this
    simp only [Cfg.toData, Ctrl.toData, evD, Data.list_cons, Data.list_nil, List.map_nil,
      Data.size_cons, Data.size_nil]
    omega
  -- the loop
  obtain ⟨tL, htL, hloop⟩ := clockLoop_runs ⟨.ev c, [v], []⟩ k (thetaFun X)
    [Data.ofNat (3 * k + 1), .cons (.ofNat k) (.cons .nil .nil), initData c.toData v,
      .ofNat (thetaFun X),
      Data.list (List.replicate (guardFun X)
        (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X))))),
      .cons (.ofNat (guardFun X))
        (.cons (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) .nil),
      Data.list (List.replicate (guardFun X) (.ofNat (guardFun X))),
      .cons (.ofNat (guardFun X)) (.cons (.ofNat (guardFun X)) .nil), .ofNat (guardFun X),
      .cons (.ofNat (3 * X + 1)) (.cons .nil .nil), .ofNat (3 * X + 1),
      .cons (.ofNat X) (.cons .nil .nil), .ofNat X,
      .cons (.ofNat k) (.ofNat (v.size + c.toData.size)), .ofNat (v.size + c.toData.size),
      .cons (.ofNat v.size) (.ofNat c.toData.size), .ofNat v.size, .ofNat c.toData.size,
      c.toData, v, .ofNat k, .cons c.toData v, .cons (.ofNat k) (.cons c.toData v)]
    (3 * k + 1) 0 le_rfl (by simp [costSum]) (by simpa using h0)
  rw [clockRun_eq c v k (thetaFun X) hguard] at hloop
  simp only [Function.iterate_zero_apply, costSum, Nat.sub_zero] at hloop
  have run : Eval [Data.cons (.ofNat k) (.cons c.toData v)] univTProg (clockedResult c v k) _ :=
    Eval.elim_cons (i := 0) (a := .ofNat k) (b := .cons c.toData v) (by simp)
    (Eval.elim_cons (i := 1) (a := c.toData) (b := v) (by simp)
    (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped (v := c.toData) (by simp) hP)
    (Eval.let_ (callVar_eval (i := 2) sizeProg_wellScoped (v := v) (by simp) hV)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat v.size) (by simp))
        (Eval.var_of_get (i := 1) (v := .ofNat c.toData.size) (by simp)))
    (Eval.let_ (callVar_eval (i := 0) addProg_wellScoped
        (v := .cons (.ofNat v.size) (.ofNat c.toData.size)) (by simp) hA1)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 6) (v := .ofNat k) (by simp))
        (Eval.var_of_get (i := 0) (v := .ofNat (v.size + c.toData.size)) (by simp)))
    (Eval.let_ (callVar_eval (i := 0) addProg_wellScoped
        (v := .cons (.ofNat k) (.ofNat (v.size + c.toData.size))) (by simp) hA2)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat X) (by simp))
        (Eval.cons (Eval.nil _) (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) tripleProg_wellScoped
        (v := .cons (.ofNat X) (.cons .nil .nil)) (by simp) hT1)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (3 * X + 1)) (by simp))
        (Eval.cons (Eval.nil _) (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) tripleProg_wellScoped
        (v := .cons (.ofNat (3 * X + 1)) (.cons .nil .nil)) (by simp) hT2)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (guardFun X)) (by simp))
        (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (guardFun X)) (by simp))
          (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) repProg_wellScoped
        (v := .cons (.ofNat (guardFun X)) (.cons (.ofNat (guardFun X)) .nil)) (by simp) hR1)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := .ofNat (guardFun X)) (by simp))
        (Eval.cons (Eval.var_of_get (i := 0)
            (v := Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) (by simp))
          (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) repProg_wellScoped
        (v := .cons (.ofNat (guardFun X))
          (.cons (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))) .nil))
        (by simp) hR2)
    (Eval.let_ (callVar_eval (i := 0) sizeProg_wellScoped
        (v := Data.list (List.replicate (guardFun X)
          (Data.list (List.replicate (guardFun X) (.ofNat (guardFun X)))))) (by simp) hΘ)
    (Eval.let_ (Eval.cons (Eval.cons (Eval.nil _)
          (Eval.var_of_get (i := 15) (v := c.toData) (by simp)))
        (Eval.cons (Eval.cons (Eval.var_of_get (i := 16) (v := v) (by simp)) (Eval.nil _))
          (Eval.nil _)))
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 18) (v := .ofNat k) (by simp))
        (Eval.cons (Eval.nil _) (Eval.nil _)))
    (Eval.let_ (callVar_eval (i := 0) tripleProg_wellScoped
        (v := .cons (.ofNat k) (.cons .nil .nil)) (by simp) hT3)
    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := initData c.toData v) (by simp [initData, evD]))
        (Eval.cons (Eval.var_of_get (i := 20) (v := .ofNat k) (by simp))
          (Eval.cons (Eval.var_of_get (i := 0) (v := .ofNat (3 * k + 1)) (by simp))
            (Eval.var_of_get (i := 3) (v := .ofNat (thetaFun X)) (by simp)))))
      hloop))))))))))))))))))))
  refine ⟨_, ?_, run⟩
  -- the bound
  have bP : tP ≤ sizeBound c.toData.size := htP
  have bV : tV ≤ sizeBound v.size := htV
  have bA1 : tA1 ≤ addBound v.size c.toData.size := htA1
  have bA2 : tA2 ≤ addBound k (v.size + c.toData.size) := htA2
  have bT1 : tT1 ≤ tripleBound X 1 := htT1
  have bT2 : tT2 ≤ tripleBound (3 * X + 1) 1 := htT2
  have bT3 : tT3 ≤ tripleBound k 1 := htT3
  have bΘ : tΘ ≤ sizeBound (thetaFun X) := htΘ
  have mP := sizeBound_mono hPX
  have mV := sizeBound_mono hVX
  have mA1 := addBound_mono hVX hPX
  have mA2 : addBound k (v.size + c.toData.size) ≤ addBound X X := addBound_mono hkX (by omega)
  have mT3 : tripleBound k 1 ≤ tripleBound X 1 := Nat.mul_le_mul (by omega) (by omega)
  have mL : (3 * k + 1 + 1) * (clockBodyBound (thetaFun X) k + 1) ≤
      (3 * X + 2) * (clockBodyBound (thetaFun X) X + 1) :=
    Nat.mul_le_mul (by omega) (Nat.add_le_add_right (clockBodyBound_mono_right hkX) 1)
  have hΘg := guardFun_le_thetaFun X
  have ht1 : guardFun X ≤ t1Fun X := by
    unfold t1Fun; have := Nat.le_mul_of_pos_right (guardFun X) (show 0 < 2 * guardFun X + 1 + 1 by omega); omega
  simp only [Data.size_ofNat, Data.list_nil, Data.size_nil] at htR1 htR2
  rw [hT1s] at htR2
  have bR1 : tR1 ≤ repBound (guardFun X) (2 * guardFun X + 1) 1 := htR1
  have bR2 : tR2 ≤ repBound (guardFun X) (t1Fun X) 1 := htR2
  unfold univTBoundFun
  simp only [initData, evD, Data.size_cons, Data.size_nil, Data.size_ofNat, hT1s, hT2s]
  omega

/-! ## Polynomial packaging -/

/-- `stepBound` as a polynomial. -/
noncomputable def stepPoly : Polynomial ℕ := (X + C 1) * (X + C 40) + C 200

theorem stepPoly_eval (x : ℕ) : stepPoly.eval x = stepBound x := by
  simp only [stepPoly, eval_add, eval_mul, eval_X, eval_C, stepBound]

/-- `interpBodyBound` as a polynomial. -/
noncomputable def interpBodyPoly : Polynomial ℕ := stepPoly + C 3 * X + C 30

theorem interpBodyPoly_eval (x : ℕ) : interpBodyPoly.eval x = interpBodyBound x := by
  simp only [interpBodyPoly, eval_add, eval_mul, eval_X, eval_C, stepPoly_eval, interpBodyBound]

/-- `sigmaFun` as a polynomial. -/
noncomputable def sigmaPoly : Polynomial ℕ :=
  X + X + (C 3 * X) * X + C 3 * X + (C 2 * X) * (X + X + (C 3 * X) * X + C 3 * X + C 10) +
    C 2 * X + C 8

theorem sigmaPoly_eval (x : ℕ) : sigmaPoly.eval x = sigmaFun x := by
  simp only [sigmaPoly, eval_add, eval_mul, eval_X, eval_C, sigmaFun, cfgSizeBound]

/-- `univBoundFun` as a polynomial. -/
noncomputable def univPoly : Polynomial ℕ :=
  (C 3 * X + C 1) * (interpBodyPoly.comp sigmaPoly + C 1) + C 2 * X + C 11

theorem univPoly_eval (x : ℕ) : univPoly.eval x = univBoundFun x := by
  simp only [univPoly, eval_add, eval_mul, eval_X, eval_C, eval_comp, interpBodyPoly_eval,
    sigmaPoly_eval, univBoundFun]

/-- `sizeBound` of a polynomial. -/
noncomputable def sizePoly (p : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 5 * p + C 20) + p + C 6

theorem sizePoly_eval (p : Polynomial ℕ) (x : ℕ) : (sizePoly p).eval x = sizeBound (p.eval x) := by
  simp only [sizePoly, eval_add, eval_mul, eval_C, sizeBound]

/-- `addBound` of polynomials. -/
noncomputable def addPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 4 * p + C 2 * q + C 15)

theorem addPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (addPoly p q).eval x = addBound (p.eval x) (q.eval x) := by
  simp only [addPoly, eval_add, eval_mul, eval_C, addBound]

/-- `tripleBound` of polynomials. -/
noncomputable def triplePoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 8 * p + C 2 * q + C 30)

theorem triplePoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (triplePoly p q).eval x = tripleBound (p.eval x) (q.eval x) := by
  simp only [triplePoly, eval_add, eval_mul, eval_C, tripleBound]

/-- `repBound` of polynomials. -/
noncomputable def repPoly (p q r : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 4 * p + C 4 * q + C 2 * r + C 30) + p * (p + C 1) * (q + C 1)

theorem repPoly_eval (p q r : Polynomial ℕ) (x : ℕ) :
    (repPoly p q r).eval x = repBound (p.eval x) (q.eval x) (r.eval x) := by
  simp only [repPoly, eval_add, eval_mul, eval_C, repBound]

/-- `subBound` of polynomials. -/
noncomputable def subPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 2 * p + C 2 * q + C 14)

theorem subPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (subPoly p q).eval x = subBound (p.eval x) (q.eval x) := by
  simp only [subPoly, eval_add, eval_mul, eval_C, subBound]

/-- `stepCostBound` of a polynomial. -/
noncomputable def stepCostPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 7 * p + C 32) + C 13 * p + C 50

theorem stepCostPoly_eval (p : Polynomial ℕ) (x : ℕ) :
    (stepCostPoly p).eval x = stepCostBound (p.eval x) := by
  simp only [stepCostPoly, eval_add, eval_mul, eval_C, stepCostBound]

/-- `clockBodyBound` of polynomials. -/
noncomputable def clockBodyPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  stepCostPoly p + subPoly p q + stepPoly.comp p + sizePoly (stepPoly.comp p) +
    subPoly (stepPoly.comp p) p + C 6 * stepPoly.comp p + C 12 * p + C 30 * q + C 200

theorem clockBodyPoly_eval (p q : Polynomial ℕ) (x : ℕ) :
    (clockBodyPoly p q).eval x = clockBodyBound (p.eval x) (q.eval x) := by
  simp only [clockBodyPoly, eval_add, eval_mul, eval_C, eval_comp, stepCostPoly_eval, subPoly_eval,
    stepPoly_eval, sizePoly_eval, clockBodyBound]

/-- `guardFun`, `t1Fun`, `thetaFun` as polynomials. -/
noncomputable def guardPoly : Polynomial ℕ := C 3 * (C 3 * X + C 1) + C 1

theorem guardPoly_eval (x : ℕ) : guardPoly.eval x = guardFun x := by
  simp only [guardPoly, eval_add, eval_mul, eval_C, eval_X, guardFun]

noncomputable def t1Poly : Polynomial ℕ := guardPoly * (C 2 * guardPoly + C 1 + C 1) + C 1

theorem t1Poly_eval (x : ℕ) : t1Poly.eval x = t1Fun x := by
  simp only [t1Poly, eval_add, eval_mul, eval_C, guardPoly_eval, t1Fun]

noncomputable def thetaPoly : Polynomial ℕ := guardPoly * (t1Poly + C 1) + C 1

theorem thetaPoly_eval (x : ℕ) : thetaPoly.eval x = thetaFun x := by
  simp only [thetaPoly, eval_add, eval_mul, eval_C, guardPoly_eval, t1Poly_eval, thetaFun]

/-- `univTBoundFun` as a polynomial. -/
noncomputable def univTPoly : Polynomial ℕ :=
  C 2 * sizePoly X + addPoly X X + addPoly X X + triplePoly X (C 1) +
    triplePoly (C 3 * X + C 1) (C 1) + triplePoly X (C 1) +
    repPoly guardPoly (C 2 * guardPoly + C 1) (C 1) + repPoly guardPoly t1Poly (C 1) +
    sizePoly thetaPoly + (C 3 * X + C 2) * (clockBodyPoly thetaPoly X + C 1) +
    C 20 * thetaPoly + C 20 * t1Poly + C 60 * guardPoly + C 100 * X + C 500

theorem univTPoly_eval (x : ℕ) : univTPoly.eval x = univTBoundFun x := by
  simp only [univTPoly, eval_add, eval_mul, eval_C, eval_X, sizePoly_eval, addPoly_eval,
    triplePoly_eval, repPoly_eval, clockBodyPoly_eval, guardPoly_eval, t1Poly_eval,
    thetaPoly_eval, univTBoundFun]

end Machine

/-- The universal machine given by the self-interpreter. -/
noncomputable def selfUniversal : UniversalMachine where
  univ := Machine.univProg
  closed := Machine.univProg_wellScoped
  bound := Machine.univPoly
  time_le c v r t h := by
    rw [Machine.univPoly_eval]
    exact Machine.univProg_time_le c v r t h
  halts_of := Machine.univProg_halts_of

/-- Existence of an efficient universal machine (blueprint `lem:universal-tm`). -/
theorem exists_efficient_universal : Nonempty UniversalMachine := ⟨selfUniversal⟩

/-- The clocked universal machine given by the self-interpreter. -/
noncomputable def selfClockedUniversal : ClockedUniversalMachine where
  univT := Machine.univTProg
  closed := Machine.univTProg_wellScoped
  bound := Machine.univTPoly
  run c v k := by
    rw [Machine.univTPoly_eval]
    exact Machine.univTProg_runs c v k

/-- Existence of a clocked universal machine (blueprint `lem:universal-tm`). -/
theorem exists_clocked_universal : Nonempty ClockedUniversalMachine := ⟨selfClockedUniversal⟩

end MIPRE.Cost
