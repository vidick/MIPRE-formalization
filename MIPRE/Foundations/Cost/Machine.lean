/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.PolyTime
import Mathlib.Logic.Function.Iterate

/-!
# The evaluation machine

A small-step abstract machine (CEK style) for the ambient language: a configuration is a
control (a program to evaluate, or a value being returned), an environment and a stack of
continuation frames. It is the common core of the two "universal" artifacts of the
project:

* Mathlib-computability of ambient evaluation (`Cost/Partrec.lean`): the step function,
  transported to `Data`, is primitive recursive and evaluation is its `PFun.fix`;
* the self-interpreter of the ambient model in the ambient model (route β of the
  universal-machine gate): a program implementing the step function inside a `loop`.

The machine charges the cost of each `Eval` rule at a designated step (`stepCost`), so
that the accumulated cost of a run is exactly the cost of the `Eval` derivation. The two
directions of the correspondence are `eval_steps` (a derivation yields a run of the
machine) and `eval_of_steps` (a halting run of the machine yields a derivation).
-/

namespace MIPRE.Cost

namespace Machine

/-- Continuation frames. -/
inductive Frame
  /-- Evaluating the head of `cons h t`; next evaluate `t` in `env`. -/
  | cons1 (t : Prog) (env : Env)
  /-- The head value `a` of a `cons`; next return `cons a v`. -/
  | cons2 (a : Data)
  /-- Evaluating the binding of `let_ e b`; next evaluate `b` in `v :: env`. -/
  | let1 (b : Prog) (env : Env)
  /-- Evaluating the body of `loop b` in `env`; next dispatch on the value. -/
  | loop1 (b : Prog) (env : Env)
  deriving DecidableEq

/-- The control: a program to evaluate, or a value being returned. -/
inductive Ctrl
  | ev (p : Prog)
  | ret (v : Data)
  deriving DecidableEq

/-- Configurations. -/
structure Cfg where
  ctrl : Ctrl
  env : Env
  kont : List Frame
  deriving DecidableEq

/-- One step of the machine. Final configurations (a value with an empty stack) are fixed. -/
def step : Cfg → Cfg
  | ⟨.ev (.var i), env, k⟩ => ⟨.ret (env.get i), env, k⟩
  | ⟨.ev .nil, env, k⟩ => ⟨.ret .nil, env, k⟩
  | ⟨.ev (.const d), env, k⟩ => ⟨.ret d, env, k⟩
  | ⟨.ev (.cons h t), env, k⟩ => ⟨.ev h, env, .cons1 t env :: k⟩
  | ⟨.ev (.elim i n c), env, k⟩ =>
    match env.get i with
    | .nil => ⟨.ev n, env, k⟩
    | .cons a b => ⟨.ev c, a :: b :: env, k⟩
  | ⟨.ev (.let_ e b), env, k⟩ => ⟨.ev e, env, .let1 b env :: k⟩
  | ⟨.ev (.loop b), env, k⟩ => ⟨.ev b, env, .loop1 b env :: k⟩
  | ⟨.ret v, env, []⟩ => ⟨.ret v, env, []⟩
  | ⟨.ret v, _, .cons1 t env :: k⟩ => ⟨.ev t, env, .cons2 v :: k⟩
  | ⟨.ret v, env, .cons2 a :: k⟩ => ⟨.ret (.cons a v), env, k⟩
  | ⟨.ret v, _, .let1 b env :: k⟩ => ⟨.ev b, v :: env, k⟩
  | ⟨.ret v, _, .loop1 b env :: k⟩ =>
    match v with
    | .nil => ⟨.ret .nil, env, k⟩
    | .cons .nil r => ⟨.ret r, env, k⟩
    | .cons (.cons _ _) v' => ⟨.ev b, v' :: env.tail, .loop1 b (v' :: env.tail) :: k⟩

/-- The `Eval` cost charged at a step: the rule's own unit (plus the size of the value
read, for `var` and `const`); `loop` rules are charged when the body's value is
dispatched. -/
def stepCost : Cfg → ℕ
  | ⟨.ev (.var i), env, _⟩ => (env.get i).size + 1
  | ⟨.ev .nil, _, _⟩ => 1
  | ⟨.ev (.const d), _, _⟩ => d.size
  | ⟨.ev (.cons _ _), _, _⟩ => 1
  | ⟨.ev (.elim _ _ _), _, _⟩ => 1
  | ⟨.ev (.let_ _ _), _, _⟩ => 1
  | ⟨.ev (.loop _), _, _⟩ => 0
  | ⟨.ret _, _, .loop1 _ _ :: _⟩ => 1
  | ⟨.ret _, _, _⟩ => 0

/-- The cost accumulated over `n` steps. -/
def costSum (c : Cfg) : ℕ → ℕ
  | 0 => 0
  | n + 1 => stepCost c + costSum (step c) n

/-- `Steps c N c' t`: `N` steps lead from `c` to `c'`, accumulating cost `t`. -/
def Steps (c : Cfg) (N : ℕ) (c' : Cfg) (t : ℕ) : Prop :=
  step^[N] c = c' ∧ costSum c N = t

theorem costSum_add (c : Cfg) (m n : ℕ) :
    costSum c (m + n) = costSum c m + costSum (step^[m] c) n := by
  induction m generalizing c with
  | zero => simp [costSum]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, costSum, ih (step c), costSum,
      Function.iterate_succ_apply]
    omega

namespace Steps

theorem one (c : Cfg) : Steps c 1 (step c) (stepCost c) := ⟨rfl, by simp [costSum]⟩

theorem trans {c₁ c₂ c₃ : Cfg} {m n t₁ t₂ : ℕ} (h₁ : Steps c₁ m c₂ t₁) (h₂ : Steps c₂ n c₃ t₂) :
    Steps c₁ (m + n) c₃ (t₁ + t₂) := by
  obtain ⟨h₁, c₁'⟩ := h₁
  obtain ⟨h₂, c₂'⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]
  · rw [costSum_add, h₁, c₁', c₂']

theorem cast {c c' : Cfg} {N t t' : ℕ} (h : Steps c N c' t) (e : t = t') : Steps c N c' t' :=
  e ▸ h

theorem of_succ {c c' : Cfg} {N t : ℕ} (h : Steps c (N + 1) c' t) :
    ∃ t', t = stepCost c + t' ∧ Steps (step c) N c' t' := by
  obtain ⟨h, hc⟩ := h
  refine ⟨costSum (step c) N, ?_, ?_, rfl⟩
  · rw [← hc, costSum]
  · rw [← h, Function.iterate_succ_apply]

theorem ne_zero {p : Prog} {env : Env} {k : List Frame} {N : ℕ} {r : Data} {e : Env} {t : ℕ}
    (h : Steps ⟨.ev p, env, k⟩ N ⟨.ret r, e, k⟩ t) : N ≠ 0 := by
  rintro rfl
  obtain ⟨h, -⟩ := h
  simp at h

end Steps

/-! ## Forward: derivations give machine runs -/

theorem eval_steps {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (k : List Frame) :
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t := by
  induction h generalizing k with
  | var env i => exact ⟨1, env, Steps.one _⟩
  | nil env => exact ⟨1, env, Steps.one _⟩
  | const env d => exact ⟨1, env, Steps.one _⟩
  | cons h₁ h₂ ih₁ ih₂ =>
    rename_i env h t a b s u
    obtain ⟨N₁, e₁, h₁⟩ := ih₁ (.cons1 t env :: k)
    obtain ⟨N₂, e₂, h₂⟩ := ih₂ (.cons2 a :: k)
    have := (((Steps.one ⟨.ev (.cons h t), env, k⟩).trans h₁).trans
      ((Steps.one ⟨.ret a, e₁, .cons1 t env :: k⟩).trans h₂)).trans
      (Steps.one ⟨.ret b, e₂, .cons2 a :: k⟩)
    exact ⟨_, e₂, this.cast (by simp [stepCost]; omega)⟩
  | elim_nil hget h₁ ih =>
    rename_i env i n c r t
    obtain ⟨N, e, h⟩ := ih k
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev n, env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    exact ⟨_, e, (h0.trans h).cast (by omega)⟩
  | elim_cons hget h₁ ih =>
    rename_i env i n c a b r t
    obtain ⟨N, e, h⟩ := ih k
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev c, a :: b :: env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    exact ⟨_, e, (h0.trans h).cast (by omega)⟩
  | let_ h₁ h₂ ih₁ ih₂ =>
    rename_i env e b v r s t
    obtain ⟨N₁, e₁, h₁⟩ := ih₁ (.let1 b env :: k)
    obtain ⟨N₂, e₂, h₂⟩ := ih₂ k
    have := (((Steps.one ⟨.ev (.let_ e b), env, k⟩).trans h₁).trans
      (Steps.one ⟨.ret v, e₁, .let1 b env :: k⟩)).trans h₂
    exact ⟨_, e₂, this.cast (by simp [stepCost]; omega)⟩
  | loop_nil h₁ ih =>
    rename_i env b t
    obtain ⟨N, e, h⟩ := ih (.loop1 b env :: k)
    have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans h).trans
      (Steps.one ⟨.ret .nil, e, .loop1 b env :: k⟩)
    exact ⟨_, env, this.cast (by simp [stepCost])⟩
  | loop_stop h₁ ih =>
    rename_i env b r t
    obtain ⟨N, e, h⟩ := ih (.loop1 b env :: k)
    have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans h).trans
      (Steps.one ⟨.ret (.cons .nil r), e, .loop1 b env :: k⟩)
    exact ⟨_, env, this.cast (by simp [stepCost])⟩
  | loop_step h₁ h₂ ih₁ ih₂ =>
    rename_i env b x y v r s t
    obtain ⟨N₁, e₁, h₁⟩ := ih₁ (.loop1 b env :: k)
    obtain ⟨N₂, e₂, h₂⟩ := ih₂ k
    -- the recursive run starts with the (free) `loop` step
    obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h₂.ne_zero
    obtain ⟨t₂, ht₂, h₂'⟩ := h₂.of_succ
    have := (((Steps.one ⟨.ev (.loop b), env, k⟩).trans h₁).trans
      (Steps.one ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩)).trans h₂'
    exact ⟨_, e₂, this.cast (by simp only [stepCost] at ht₂ ⊢; omega)⟩

/-! ## Backward: halting runs give derivations -/

/-- A final configuration: a value with an empty stack. -/
def IsFinal (c : Cfg) : Prop := ∃ r e, c = ⟨.ret r, e, []⟩

theorem eval_of_steps : ∀ (N : ℕ) (p : Prog) (env : Env) (k : List Frame) (r : Data) (e : Env),
    step^[N] ⟨.ev p, env, k⟩ = ⟨.ret r, e, []⟩ →
    ∃ r' t M e' N', N = M + N' ∧ Eval env p r' t ∧ Steps ⟨.ev p, env, k⟩ M ⟨.ret r', e', k⟩ t := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
  intro p env k r e hN
  -- one step is always taken
  obtain ⟨N₀, rfl⟩ : ∃ N₀, N = N₀ + 1 := by
    cases N with
    | zero => simp at hN
    | succ N₀ => exact ⟨N₀, rfl⟩
  rw [Function.iterate_succ_apply] at hN
  cases p with
  | var i =>
    exact ⟨env.get i, _, 1, env, N₀, by omega, Eval.var env i, Steps.one _⟩
  | nil => exact ⟨.nil, 1, 1, env, N₀, by omega, Eval.nil env, Steps.one _⟩
  | const d => exact ⟨d, d.size, 1, env, N₀, by omega, Eval.const env d, Steps.one _⟩
  | cons h t =>
    simp only [step] at hN
    obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) h env (.cons1 t env :: k) r e hN
    -- the remaining run starts from the return to the `cons1` frame
    have hrest : step^[N₁] ⟨.ret r₁, e₁, .cons1 t env :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₁, Nat.add_comm, Function.iterate_add_apply, s₁.1] at hN
      exact hN
    obtain ⟨N₂, rfl⟩ : ∃ N₂, N₁ = N₂ + 1 := by
      cases N₁ with
      | zero => simp at hrest
      | succ N₂ => exact ⟨N₂, rfl⟩
    rw [Function.iterate_succ_apply] at hrest
    simp only [step] at hrest
    obtain ⟨r₂, t₂, M₂, e₂, N₃, hN₃, h₂, s₂⟩ := ih N₂ (by omega) t env (.cons2 r₁ :: k) r e hrest
    have hrest₂ : step^[N₃] ⟨.ret r₂, e₂, .cons2 r₁ :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₃, Nat.add_comm, Function.iterate_add_apply, s₂.1] at hrest
      exact hrest
    obtain ⟨N₄, rfl⟩ : ∃ N₄, N₃ = N₄ + 1 := by
      cases N₃ with
      | zero => simp at hrest₂
      | succ N₄ => exact ⟨N₄, rfl⟩
    refine ⟨.cons r₁ r₂, t₁ + t₂ + 1, 1 + M₁ + (1 + M₂) + 1, e₂, N₄, by omega,
      Eval.cons h₁ h₂, ?_⟩
    have := (((Steps.one ⟨.ev (.cons h t), env, k⟩).trans s₁).trans
      ((Steps.one ⟨.ret r₁, e₁, .cons1 t env :: k⟩).trans s₂)).trans
      (Steps.one ⟨.ret r₂, e₂, .cons2 r₁ :: k⟩)
    exact this.cast (by simp [stepCost]; omega)
  | elim i n c =>
    rcases hget : env.get i with _ | ⟨a, b⟩
    · simp only [step, hget] at hN
      obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) n env k r e hN
      refine ⟨r₁, t₁ + 1, 1 + M₁, e₁, N₁, by omega, Eval.elim_nil hget h₁, ?_⟩
      have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev n, env, k⟩ 1 := by
        have := Steps.one ⟨.ev (.elim i n c), env, k⟩
        simp only [step, stepCost, hget] at this
        exact this
      exact (h0.trans s₁).cast (by omega)
    · simp only [step, hget] at hN
      obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ :=
        ih N₀ (by omega) c (a :: b :: env) k r e hN
      refine ⟨r₁, t₁ + 1, 1 + M₁, e₁, N₁, by omega, Eval.elim_cons hget h₁, ?_⟩
      have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev c, a :: b :: env, k⟩ 1 := by
        have := Steps.one ⟨.ev (.elim i n c), env, k⟩
        simp only [step, stepCost, hget] at this
        exact this
      exact (h0.trans s₁).cast (by omega)
  | let_ e' b =>
    simp only [step] at hN
    obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) e' env (.let1 b env :: k) r e hN
    have hrest : step^[N₁] ⟨.ret r₁, e₁, .let1 b env :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₁, Nat.add_comm, Function.iterate_add_apply, s₁.1] at hN
      exact hN
    obtain ⟨N₂, rfl⟩ : ∃ N₂, N₁ = N₂ + 1 := by
      cases N₁ with
      | zero => simp at hrest
      | succ N₂ => exact ⟨N₂, rfl⟩
    rw [Function.iterate_succ_apply] at hrest
    simp only [step] at hrest
    obtain ⟨r₂, t₂, M₂, e₂, N₃, hN₃, h₂, s₂⟩ := ih N₂ (by omega) b (r₁ :: env) k r e hrest
    refine ⟨r₂, t₁ + t₂ + 1, 1 + M₁ + 1 + M₂, e₂, N₃, by omega, Eval.let_ h₁ h₂, ?_⟩
    have := (((Steps.one ⟨.ev (.let_ e' b), env, k⟩).trans s₁).trans
      (Steps.one ⟨.ret r₁, e₁, .let1 b env :: k⟩)).trans s₂
    exact this.cast (by simp [stepCost]; omega)
  | loop b =>
    simp only [step] at hN
    obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) b env (.loop1 b env :: k) r e hN
    have hrest : step^[N₁] ⟨.ret r₁, e₁, .loop1 b env :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₁, Nat.add_comm, Function.iterate_add_apply, s₁.1] at hN
      exact hN
    obtain ⟨N₂, rfl⟩ : ∃ N₂, N₁ = N₂ + 1 := by
      cases N₁ with
      | zero => simp at hrest
      | succ N₂ => exact ⟨N₂, rfl⟩
    rw [Function.iterate_succ_apply] at hrest
    rcases r₁ with _ | ⟨_ | ⟨x, y⟩, v⟩
    · -- `loop_nil`
      simp only [step] at hrest
      refine ⟨.nil, t₁ + 1, 1 + M₁ + 1, env, N₂, by omega, Eval.loop_nil h₁, ?_⟩
      have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans s₁).trans
        (Steps.one ⟨.ret .nil, e₁, .loop1 b env :: k⟩)
      exact this.cast (by simp [stepCost])
    · -- `loop_stop`
      simp only [step] at hrest
      refine ⟨v, t₁ + 1, 1 + M₁ + 1, env, N₂, by omega, Eval.loop_stop h₁, ?_⟩
      have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans s₁).trans
        (Steps.one ⟨.ret (.cons .nil v), e₁, .loop1 b env :: k⟩)
      exact this.cast (by simp [stepCost])
    · -- `loop_step`: the continuation is the `loop` at the new environment
      simp only [step] at hrest
      have hrest' : step^[N₂ + 1] ⟨.ev (.loop b), v :: env.tail, k⟩ = ⟨.ret r, e, []⟩ := by
        rw [Function.iterate_succ_apply]
        exact hrest
      have hM₁ := s₁.ne_zero
      obtain ⟨r₂, t₂, M₂, e₂, N₃, hN₃, h₂, s₂⟩ :=
        ih (N₂ + 1) (by omega) (.loop b) (v :: env.tail) k r e hrest'
      obtain ⟨M₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero s₂.ne_zero
      obtain ⟨t₂', ht₂', s₂'⟩ := s₂.of_succ
      refine ⟨r₂, t₁ + t₂ + 1, 1 + M₁ + 1 + M₂', e₂, N₃, by omega, Eval.loop_step h₁ h₂, ?_⟩
      have := (((Steps.one ⟨.ev (.loop b), env, k⟩).trans s₁).trans
        (Steps.one ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩)).trans s₂'
      refine this.cast ?_
      simp only [stepCost] at ht₂' ⊢
      omega

/-- The two directions together: `p` on `x` halts with `r` iff the machine started at
`⟨ev p, [x], []⟩` reaches the final configuration with value `r`. -/
theorem halts_iff (p : Prog) (x r : Data) :
    (∃ t, p.Runs x r t) ↔ ∃ N e, step^[N] ⟨.ev p, [x], []⟩ = ⟨.ret r, e, []⟩ := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨N, e, hs⟩ := eval_steps h []
    exact ⟨N, e, hs.1⟩
  · rintro ⟨N, e, h⟩
    obtain ⟨r', t, M, e', N', hN, hev, hs⟩ := eval_of_steps N p [x] [] r e h
    -- the final configuration is fixed, so `r' = r`
    have hfix : ∀ n, step^[n] (⟨.ret r', e', []⟩ : Cfg) = ⟨.ret r', e', []⟩ := fun n =>
      Function.iterate_fixed rfl n
    rw [hN, Nat.add_comm, Function.iterate_add_apply, hs.1, hfix] at h
    obtain rfl := Ctrl.ret.inj (Cfg.mk.inj h).1
    exact ⟨t, hev⟩

end Machine

end MIPRE.Cost
