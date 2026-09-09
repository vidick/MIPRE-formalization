/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.MachineData
import MIPRE.Foundations.Cost.Closure
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The self-interpreter, I: the step function as a program

Programs of the ambient model implementing the step function of the evaluation machine on
data (`Machine.stepData`, `Cost/MachineData.lean`): `stepEvProg` for "evaluate" controls,
`stepRetProg` for "return" controls, and `stepProg` combining them. Each is proved to
compute `stepData` on encoded configurations, at a cost quadratic in the size of the
configuration (the only non-constant work is the walk `getListProg` along the environment,
which copies the remaining environment at each of its steps).

Conventions: every sub-program is closed and receives its input, a tuple built with
`cons`, at variable `0`; tuples are taken apart with `elim` (free), and the pieces are read
back with `var` (paid by size). Tag dispatch on a unary numeral is a chain of `elim`s; the
case programs are called through `callVar` on a packaged tuple whose index grows by two
per level of the chain.
-/

namespace MIPRE.Cost

namespace Machine

open Prog

/-- Discharge a linear inequality between costs and sizes, after expanding the sizes of
constructors and of encoded configurations. -/
macro "size_omega" : tactic =>
  `(tactic| ((try simp only [Data.size_cons, Data.size_nil, Data.size_ofNat, Frame.toData,
      Cfg.toData, Ctrl.toData, evD, retD, Prog.toData, Data.list_cons, Data.list_nil,
      List.map_cons, List.map_nil] at *); all_goals omega))

/-! ## Projections at an arbitrary index -/

/-- `left` of the value of variable `i`. -/
def projLeft (i : ℕ) : Prog := .elim i .nil (.var 0)

/-- `right` of the value of variable `i`. -/
def projRight (i : ℕ) : Prog := .elim i .nil (.var 1)

theorem projLeft_runs {E : Env} {i : ℕ} {d : Data} (h : E.get i = d) :
    ∃ s ≤ d.size + 2, Eval E (projLeft i) d.left s := by
  cases d with
  | nil => exact ⟨2, by simp, Eval.elim_nil (i := i) h (Eval.nil _)⟩
  | cons a b =>
    refine ⟨a.size + 1 + 1, by simp; omega, ?_⟩
    exact Eval.elim_cons (i := i) (a := a) (b := b) h (Eval.var_of_get (i := 0) (v := a) (by simp))

theorem projRight_runs {E : Env} {i : ℕ} {d : Data} (h : E.get i = d) :
    ∃ s ≤ d.size + 2, Eval E (projRight i) d.right s := by
  cases d with
  | nil => exact ⟨2, by simp, Eval.elim_nil (i := i) h (Eval.nil _)⟩
  | cons a b =>
    refine ⟨b.size + 1 + 1, by simp; omega, ?_⟩
    exact Eval.elim_cons (i := i) (a := a) (b := b) h (Eval.var_of_get (i := 1) (v := b) (by simp))

theorem size_left_le (d : Data) : d.left.size ≤ d.size := by cases d <;> simp; omega

theorem size_right_le (d : Data) : d.right.size ≤ d.size := by cases d <;> simp; omega

theorem size_getList_le (env : Data) (n : ℕ) : (Data.getList env n).size ≤ env.size := by
  unfold Data.getList
  refine (size_left_le _).trans ?_
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; exact (size_right_le _).trans ih

/-! ## The environment walk -/

/-- Body of `getListProg`: on the state `cons env idx`, stop with `left env` if `idx` is
exhausted, else continue with `cons (right env) idx'`. -/
def getListBody : Prog :=
  .elim 0 .nil (.elim 1 (.cons .nil (projLeft 0))
    (.cons (.cons .nil .nil) (.cons (projRight 2) (.var 1))))

/-- `getListProg` on `cons env idx` computes `getList env (unaryToNat idx)`. -/
def getListProg : Prog := .loop getListBody

theorem getListBody_wellScoped : getListBody.WellScoped 1 := by
  simp [getListBody, projLeft, projRight, WellScoped]

theorem getListProg_wellScoped : getListProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, getListBody_wellScoped⟩

theorem getListProg_runs (idx env : Data) (rest : Env) :
    ∃ t ≤ (idx.size + 1) * (env.size + idx.size + 12),
      Eval (.cons env idx :: rest) getListProg (Data.getList env (Data.unaryToNat idx)) t := by
  induction idx generalizing env with
  | nil =>
    obtain ⟨s, hs, hl⟩ := projLeft_runs (E := env :: Data.nil :: Data.cons env .nil :: rest)
      (i := 0) (d := env) (by simp)
    have hbody : Eval (Data.cons env .nil :: rest) getListBody (.cons .nil env.left) _ :=
      Eval.elim_cons (i := 0) (a := env) (b := .nil) (by simp)
        (Eval.elim_nil (i := 1) (by simp) (Eval.cons (Eval.nil _) hl))
    have run := Eval.loop_stop hbody
    refine ⟨_, ?_, by simpa [getListProg, Data.getList] using run⟩
    size_omega
  | cons i₁ idx' _ ih =>
    obtain ⟨t, ht, hrun⟩ := ih env.right
    obtain ⟨s, hs, hr⟩ := projRight_runs
      (E := i₁ :: idx' :: env :: Data.cons i₁ idx' :: Data.cons env (.cons i₁ idx') :: rest)
      (i := 2) (d := env) (by simp)
    have hbody : Eval (Data.cons env (.cons i₁ idx') :: rest) getListBody
        (.cons (.cons .nil .nil) (.cons env.right idx')) _ :=
      Eval.elim_cons (i := 0) (a := env) (b := .cons i₁ idx') (by simp)
        (Eval.elim_cons (i := 1) (a := i₁) (b := idx') (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons hr (Eval.var_of_get (i := 1) (v := idx') (by simp)))))
    have hrun' : Eval (Data.cons env.right idx' :: rest) getListProg
        (Data.getList env (Data.unaryToNat (.cons i₁ idx'))) t := by
      simpa [Data.getList, Function.iterate_succ_apply] using hrun
    have run := Eval.loop_step hbody hrun'
    refine ⟨_, ?_, by simpa [getListProg] using run⟩
    · have h1 : (Data.cons i₁ idx').size = i₁.size + idx'.size + 1 := rfl
      have h2 : env.right.size ≤ env.size := size_right_le env
      have h3 : (idx'.size + 1) * (env.right.size + idx'.size + 12) ≤
          (idx'.size + 1) * (env.size + i₁.size + idx'.size + 13) :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (i₁.size + idx'.size + 1 + 1) * (env.size + (i₁.size + idx'.size + 1) + 12) =
          (idx'.size + 1) * (env.size + i₁.size + idx'.size + 13) +
          (i₁.size + 1) * (env.size + i₁.size + idx'.size + 13) := by ring
      have h5 : env.size + i₁.size + idx'.size + 13 ≤
          (i₁.size + 1) * (env.size + i₁.size + idx'.size + 13) :=
        Nat.le_mul_of_pos_left _ (by omega)
      rw [h1]
      omega

/-! ## The "evaluate" cases -/

/-- Cases of `stepEvProg`; input `cons body (cons env kont)`. After the two `elim`s the
environment is `[env, kont, body, cons env kont, input]`. -/
def evVar : Prog :=
  .elim 0 .nil (.elim 1 .nil (.let_ (.cons (.var 0) (.var 2))
    (.let_ (callVar 0 getListProg) (.cons (.cons (.cons .nil .nil) (.var 0)) (.var 5)))))

def evNil : Prog :=
  .elim 0 .nil (.elim 1 .nil (.cons (.const (.cons (.cons .nil .nil) .nil)) (.var 3)))

def evCons : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.var 2)
      (.cons (.cons (.const (.ofNat 0)) (.cons (.var 1) (.var 2))) (.var 3))))))

def evElim : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil (.elim 1 .nil
    (.let_ (.cons (.var 4) (.var 2)) (.let_ (callVar 0 getListProg)
      (.elim 0 (.cons (.cons .nil (.var 2)) (.var 9))
        (.cons (.cons .nil (.var 5)) (.cons (.cons (.var 0) (.cons (.var 1) (.var 8))) (.var 9)))))))))

def evLet : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.var 2)
      (.cons (.cons (.const (.ofNat 2)) (.cons (.var 1) (.var 2))) (.var 3))))))

def evLoop : Prog :=
  .elim 0 .nil (.elim 1 .nil
    (.cons (.cons .nil (.var 2)) (.cons (.var 0)
      (.cons (.cons (.const (.ofNat 3)) (.cons (.var 2) (.var 0))) (.var 1)))))

def evConst : Prog :=
  .elim 0 .nil (.elim 1 .nil (.cons (.cons (.cons .nil .nil) (.var 2)) (.var 3)))

theorem evVar_wellScoped : evVar.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped, ⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩,
    by simp [WellScoped]⟩

theorem evNil_wellScoped : evNil.WellScoped 1 := by simp [evNil, WellScoped]
theorem evCons_wellScoped : evCons.WellScoped 1 := by simp [evCons, WellScoped]
theorem evLet_wellScoped : evLet.WellScoped 1 := by simp [evLet, WellScoped]
theorem evLoop_wellScoped : evLoop.WellScoped 1 := by simp [evLoop, WellScoped]
theorem evConst_wellScoped : evConst.WellScoped 1 := by simp [evConst, WellScoped]

theorem evElim_wellScoped : evElim.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) getListProg_wellScoped, by simp [WellScoped]⟩

theorem evVar_runs (body env kont : Data) :
    ∃ s ≤ (body.size + 1) * (env.size + body.size + 12) + 4 * env.size + 3 * body.size +
      2 * kont.size + 20,
      Eval [Data.cons body (.cons env kont)] evVar
        (.cons (retD (Data.getList env (Data.unaryToNat body))) (.cons env kont)) s := by
  obtain ⟨t, ht, hg⟩ := getListProg_runs body env []
  have hv := size_getList_le env (Data.unaryToNat body)
  have run : Eval [Data.cons body (.cons env kont)] evVar
      (.cons (retD (Data.getList env (Data.unaryToNat body))) (.cons env kont)) _ :=
    Eval.elim_cons (i := 0) (a := body) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := env) (by simp))
          (Eval.var_of_get (i := 2) (v := body) (by simp)))
        (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped (v := .cons env body) (by simp) hg)
          (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.var_of_get (i := 0) (v := Data.getList env (Data.unaryToNat body)) (by simp)))
            (Eval.var_of_get (i := 5) (v := .cons env kont) (by simp))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem evNil_runs (body env kont : Data) :
    ∃ s ≤ env.size + kont.size + 12,
      Eval [Data.cons body (.cons env kont)] evNil (.cons (retD .nil) (.cons env kont)) s := by
  have run : Eval [Data.cons body (.cons env kont)] evNil (.cons (retD .nil) (.cons env kont)) _ :=
    Eval.elim_cons (i := 0) (a := body) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.cons (Eval.const _ (.cons (.cons .nil .nil) .nil))
        (Eval.var_of_get (i := 3) (v := .cons env kont) (by simp))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem evCons_runs (h t env kont : Data) :
    ∃ s ≤ h.size + t.size + 2 * env.size + kont.size + 20,
      Eval [Data.cons (.cons h t) (.cons env kont)] evCons
        (.cons (evD h) (.cons env (.cons (.cons (.ofNat 0) (.cons t env)) kont))) s := by
  have run : Eval [Data.cons (.cons h t) (.cons env kont)] evCons
      (.cons (evD h) (.cons env (.cons (.cons (.ofNat 0) (.cons t env)) kont))) _ :=
    Eval.elim_cons (i := 0) (a := .cons h t) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.elim_cons (i := 2) (a := h) (b := t) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := h) (by simp)))
          (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
            (Eval.cons (Eval.cons (Eval.const _ (.ofNat 0))
                (Eval.cons (Eval.var_of_get (i := 1) (v := t) (by simp))
                  (Eval.var_of_get (i := 2) (v := env) (by simp))))
              (Eval.var_of_get (i := 3) (v := kont) (by simp)))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem evLet_runs (e b env kont : Data) :
    ∃ s ≤ e.size + b.size + 2 * env.size + kont.size + 24,
      Eval [Data.cons (.cons e b) (.cons env kont)] evLet
        (.cons (evD e) (.cons env (.cons (.cons (.ofNat 2) (.cons b env)) kont))) s := by
  have run : Eval [Data.cons (.cons e b) (.cons env kont)] evLet
      (.cons (evD e) (.cons env (.cons (.cons (.ofNat 2) (.cons b env)) kont))) _ :=
    Eval.elim_cons (i := 0) (a := .cons e b) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.elim_cons (i := 2) (a := e) (b := b) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := e) (by simp)))
          (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
            (Eval.cons (Eval.cons (Eval.const _ (.ofNat 2))
                (Eval.cons (Eval.var_of_get (i := 1) (v := b) (by simp))
                  (Eval.var_of_get (i := 2) (v := env) (by simp))))
              (Eval.var_of_get (i := 3) (v := kont) (by simp)))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem evLoop_runs (b env kont : Data) :
    ∃ s ≤ 2 * b.size + 2 * env.size + kont.size + 26,
      Eval [Data.cons b (.cons env kont)] evLoop
        (.cons (evD b) (.cons env (.cons (.cons (.ofNat 3) (.cons b env)) kont))) s := by
  have run : Eval [Data.cons b (.cons env kont)] evLoop
      (.cons (evD b) (.cons env (.cons (.cons (.ofNat 3) (.cons b env)) kont))) _ :=
    Eval.elim_cons (i := 0) (a := b) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 2) (v := b) (by simp)))
        (Eval.cons (Eval.var_of_get (i := 0) (v := env) (by simp))
          (Eval.cons (Eval.cons (Eval.const _ (.ofNat 3))
              (Eval.cons (Eval.var_of_get (i := 2) (v := b) (by simp))
                (Eval.var_of_get (i := 0) (v := env) (by simp))))
            (Eval.var_of_get (i := 1) (v := kont) (by simp))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem evConst_runs (d env kont : Data) :
    ∃ s ≤ d.size + env.size + kont.size + 12,
      Eval [Data.cons d (.cons env kont)] evConst (.cons (retD d) (.cons env kont)) s := by
  have run : Eval [Data.cons d (.cons env kont)] evConst (.cons (retD d) (.cons env kont)) _ :=
    Eval.elim_cons (i := 0) (a := d) (b := .cons env kont) (by simp)
    (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
      (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 2) (v := d) (by simp)))
        (Eval.var_of_get (i := 3) (v := .cons env kont) (by simp))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem evElim_runs (i n c env kont : Data) :
    ∃ s ≤ (i.size + 1) * (env.size + i.size + 12) + 5 * env.size + 3 * i.size + n.size + c.size +
      2 * kont.size + 40,
      Eval [Data.cons (.cons i (.cons n c)) (.cons env kont)] evElim
        (if Data.getList env (Data.unaryToNat i) = .nil then .cons (evD n) (.cons env kont)
        else .cons (evD c) (.cons (.cons (Data.getList env (Data.unaryToNat i)).left
          (.cons (Data.getList env (Data.unaryToNat i)).right env)) kont)) s := by
  obtain ⟨t, ht, hg⟩ := getListProg_runs i env []
  have hv := size_getList_le env (Data.unaryToNat i)
  rcases hget : Data.getList env (Data.unaryToNat i) with _ | ⟨a, b⟩
  · rw [hget] at hg
    have run : Eval [Data.cons (.cons i (.cons n c)) (.cons env kont)] evElim
        (.cons (evD n) (.cons env kont)) _ :=
      Eval.elim_cons (i := 0) (a := .cons i (.cons n c)) (b := .cons env kont) (by simp)
        (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
          (Eval.elim_cons (i := 2) (a := i) (b := .cons n c) (by simp)
            (Eval.elim_cons (i := 1) (a := n) (b := c) (by simp)
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := env) (by simp))
                  (Eval.var_of_get (i := 2) (v := i) (by simp)))
                (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped (v := .cons env i)
                    (by simp) hg)
                  (Eval.elim_nil (i := 0) (by simp)
                    (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 2) (v := n) (by simp)))
                      (Eval.var_of_get (i := 9) (v := .cons env kont) (by simp)))))))))
    refine ⟨_, ?_, run⟩
    size_omega
  · rw [hget] at hg hv
    have run : Eval [Data.cons (.cons i (.cons n c)) (.cons env kont)] evElim
        (.cons (evD c) (.cons (.cons a (.cons b env)) kont)) _ :=
      Eval.elim_cons (i := 0) (a := .cons i (.cons n c)) (b := .cons env kont) (by simp)
        (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
          (Eval.elim_cons (i := 2) (a := i) (b := .cons n c) (by simp)
            (Eval.elim_cons (i := 1) (a := n) (b := c) (by simp)
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := env) (by simp))
                  (Eval.var_of_get (i := 2) (v := i) (by simp)))
                (Eval.let_ (callVar_eval (i := 0) getListProg_wellScoped (v := .cons env i)
                    (by simp) hg)
                  (Eval.elim_cons (i := 0) (a := a) (b := b) (by simp)
                    (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := c) (by simp)))
                      (Eval.cons (Eval.cons (Eval.var_of_get (i := 0) (v := a) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 1) (v := b) (by simp))
                            (Eval.var_of_get (i := 8) (v := env) (by simp))))
                        (Eval.var_of_get (i := 9) (v := kont) (by simp))))))))))
    refine ⟨_, ?_, run⟩
    size_omega

/-! ## Tag dispatch -/

/-- `dispatch cs i idx`: case analysis on the unary numeral at variable `i`, calling the
`k`-th program of `cs` on the tuple at variable `idx + 2 k` (each level of the chain binds
two more variables). -/
def dispatch : List Prog → ℕ → ℕ → Prog
  | [], _, _ => .nil
  | [c], _, idx => callVar idx c
  | c :: c' :: cs, i, idx => .elim i (callVar idx c) (dispatch (c' :: cs) 1 (idx + 2))

theorem dispatch_wellScoped : ∀ (cs : List Prog) (i idx n : ℕ), i < n → idx < n →
    (∀ c ∈ cs, c.WellScoped 1) → (dispatch cs i idx).WellScoped n
  | [], _, _, _, _, _, _ => trivial
  | [c], _, idx, n, _, hidx, hcs => callVar_wellScoped hidx (hcs c (by simp))
  | c :: c' :: cs, i, idx, n, hi, hidx, hcs =>
    ⟨hi, callVar_wellScoped hidx (hcs c (by simp)),
      dispatch_wellScoped (c' :: cs) 1 (idx + 2) (n + 2) (by omega) (by omega)
        (fun d hd => hcs d (List.mem_cons_of_mem c hd))⟩

theorem dispatch_runs : ∀ (cs : List Prog) (k i idx : ℕ) (E : Env) (pk r : Data) (t : ℕ),
    k < cs.length → (∀ c ∈ cs, c.WellScoped 1) → E.get i = Data.ofNat k → E.get idx = pk →
    Eval [pk] (cs.getD k .nil) r t →
    ∃ s ≤ t + pk.size + k + 3, Eval E (dispatch cs i idx) r s
  | [], k, _, _, _, _, _, _, hk, _, _, _, _ => by simp at hk
  | [c], k, i, idx, E, pk, r, t, hk, hcs, hi, hidx, h => by
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨_, by omega, callVar_eval (i := idx) (hcs c (by simp)) hidx h⟩
  | c :: c' :: cs, k, i, idx, E, pk, r, t, hk, hcs, hi, hidx, h => by
    cases k with
    | zero =>
      exact ⟨_, by omega, Eval.elim_nil (i := i) hi (callVar_eval (i := idx) (hcs c (by simp)) hidx h)⟩
    | succ k' =>
      obtain ⟨s, hs, hd⟩ := dispatch_runs (c' :: cs) k' 1 (idx + 2) (Data.nil :: Data.ofNat k' :: E)
        pk r t (by simp at hk ⊢; omega) (fun d hd => hcs d (List.mem_cons_of_mem c hd))
        (by simp) (by simpa using hidx) (by simpa using h)
      exact ⟨_, by omega, Eval.elim_cons (i := i) (a := .nil) (b := .ofNat k')
        (by rw [hi]; rfl) hd⟩

/-! ## The "evaluate" step -/

/-- The case programs of `stepEvProg`, indexed by the tag of the program. -/
def evCases : List Prog := [evVar, evNil, evCons, evElim, evLet, evLoop, evConst]

theorem evCases_wellScoped : ∀ c ∈ evCases, c.WellScoped 1 := by
  intro c hc
  simp only [evCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [evVar_wellScoped, evNil_wellScoped, evCons_wellScoped, evElim_wellScoped,
    evLet_wellScoped, evLoop_wellScoped, evConst_wellScoped]

/-- The step on "evaluate `p`"; input `cons (toData p) (cons env kont)`. -/
def stepEvProg : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 .nil
    (.let_ (.cons (.var 1) (.cons (.var 2) (.var 3))) (.let_ (.var 1) (dispatch evCases 0 1)))))

theorem stepEvProg_wellScoped : stepEvProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    ⟨by simp [WellScoped], dispatch_wellScoped evCases 0 1 9 (by omega) (by omega) evCases_wellScoped⟩⟩

/-- The environment in which the dispatch of `stepEvProg` runs, for a program with tag `k`
and body `body`. -/
def dispEnv (k : ℕ) (body env kont : Data) : Env :=
  [Data.ofNat k, .cons body (.cons env kont), .ofNat k, body, env, kont, .cons (.ofNat k) body,
    .cons env kont, .cons (.cons (.ofNat k) body) (.cons env kont)]

/-- The prefix of `stepEvProg` up to the dispatch. -/
theorem stepEvProg_prefix (k : ℕ) (body env kont r : Data) {s : ℕ}
    (hd : Eval (dispEnv k body env kont) (dispatch evCases 0 1) r s) :
    ∃ c ≤ s + body.size + env.size + kont.size + (Data.ofNat k).size + 12,
      Eval [Data.cons (.cons (.ofNat k) body) (.cons env kont)] stepEvProg r c := by
  have run : Eval [Data.cons (.cons (.ofNat k) body) (.cons env kont)] stepEvProg r _ :=
    Eval.elim_cons (i := 0) (a := .cons (.ofNat k) body) (b := .cons env kont) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := kont) (by simp)
        (Eval.elim_cons (i := 2) (a := .ofNat k) (b := body) (by simp)
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := body) (by simp))
              (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
                (Eval.var_of_get (i := 3) (v := kont) (by simp))))
            (Eval.let_ (Eval.var_of_get (i := 1) (v := .ofNat k) (by simp)) hd))))
  exact ⟨_, by omega, run⟩

/-- Bound of one "evaluate" step in terms of `S = esize p + env.size + kont.size`. -/
def stepEvBound (S : ℕ) : ℕ := (S + 1) * (S + 30) + 100

theorem stepEvProg_runs (p : Prog) (env kont : Data) :
    ∃ s ≤ stepEvBound (esize p + env.size + kont.size),
      stepEvProg.Runs (.cons p.toData (.cons env kont)) (stepEv p.toData env kont) s := by
  have hsplit : ∀ S : ℕ, stepEvBound S = (S + 1) * (S + 12) + 18 * (S + 1) + 100 := fun S => by
    unfold stepEvBound; ring
  cases p with
  | var i =>
    obtain ⟨c₀, hc₀, hcase⟩ := evVar_runs (.ofNat i) env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 0 0 1 (dispEnv 0 (.ofNat i) env kont)
      (Data.cons (.ofNat i) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.ofNat i) (.cons env kont)] (evCases.getD 0 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 0 (.ofNat i) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.var i) = 2 * i + 3 := by
      simp only [Prog.esize_eq_size_toData]; size_omega
    rw [hsplit, hE]
    simp only [Data.size_ofNat, Data.size_cons] at hc₀ hs hc' ⊢
    have hq : (2 * i + 1 + 1) * (env.size + (2 * i + 1) + 12) ≤
        (2 * i + 3 + env.size + kont.size + 1) * (2 * i + 3 + env.size + kont.size + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  | nil =>
    obtain ⟨c₀, hc₀, hcase⟩ := evNil_runs .nil env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 1 0 1 (dispEnv 1 .nil env kont)
      (Data.cons .nil (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons .nil (.cons env kont)] (evCases.getD 1 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 1 .nil env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize Prog.nil = 5 := by
      simp only [Prog.esize_eq_size_toData]; size_omega
    rw [hsplit, hE]
    size_omega
  | cons h t =>
    obtain ⟨c₀, hc₀, hcase⟩ := evCons_runs h.toData t.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 2 0 1 (dispEnv 2 (.cons h.toData t.toData) env kont)
      (Data.cons (.cons h.toData t.toData) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.cons h.toData t.toData) (.cons env kont)] (evCases.getD 2 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 2 (.cons h.toData t.toData) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.cons h t) = esize h + esize t + 7 := by
      simp only [Prog.esize_eq_size_toData]; size_omega
    have h_h : h.toData.size = esize h := rfl
    have h_t : t.toData.size = esize t := rfl
    rw [hsplit, hE]
    size_omega
  | elim i n c =>
    obtain ⟨c₀, hc₀, hcase⟩ := evElim_runs (.ofNat i) n.toData c.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 3 0 1 (dispEnv 3 (.cons (.ofNat i) (.cons n.toData c.toData)) env kont)
      (Data.cons (.cons (.ofNat i) (.cons n.toData c.toData)) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.cons (.ofNat i) (.cons n.toData c.toData)) (.cons env kont)] (evCases.getD 3 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 3 (.cons (.ofNat i) (.cons n.toData c.toData)) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.elim i n c) = 2 * i + esize n + esize c + 11 := by
      simp only [Prog.esize_eq_size_toData]; size_omega
    have h_n : n.toData.size = esize n := rfl
    have h_c : c.toData.size = esize c := rfl
    rw [hsplit, hE]
    simp only [Data.size_ofNat, Data.size_cons] at hc₀ hs hc' ⊢
    have hq : (2 * i + 1 + 1) * (env.size + (2 * i + 1) + 12) ≤
        (2 * i + esize n + esize c + 11 + env.size + kont.size + 1) *
          (2 * i + esize n + esize c + 11 + env.size + kont.size + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  | let_ e b =>
    obtain ⟨c₀, hc₀, hcase⟩ := evLet_runs e.toData b.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 4 0 1 (dispEnv 4 (.cons e.toData b.toData) env kont)
      (Data.cons (.cons e.toData b.toData) (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons (.cons e.toData b.toData) (.cons env kont)] (evCases.getD 4 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 4 (.cons e.toData b.toData) env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.let_ e b) = esize e + esize b + 11 := by
      simp only [Prog.esize_eq_size_toData]; size_omega
    have h_e : e.toData.size = esize e := rfl
    have h_b : b.toData.size = esize b := rfl
    rw [hsplit, hE]
    size_omega
  | loop b =>
    obtain ⟨c₀, hc₀, hcase⟩ := evLoop_runs b.toData env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 5 0 1 (dispEnv 5 b.toData env kont)
      (Data.cons b.toData (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons b.toData (.cons env kont)] (evCases.getD 5 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 5 b.toData env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.loop b) = esize b + 12 := by
      simp only [Prog.esize_eq_size_toData]; size_omega
    have h_b : b.toData.size = esize b := rfl
    rw [hsplit, hE]
    size_omega
  | const d =>
    obtain ⟨c₀, hc₀, hcase⟩ := evConst_runs d env kont
    obtain ⟨s, hs, hd⟩ := dispatch_runs evCases 6 0 1 (dispEnv 6 d env kont)
      (Data.cons d (.cons env kont)) _ c₀ (by simp [evCases]) evCases_wellScoped
      (by simp [dispEnv]) (by simp [dispEnv])
      (show Eval [Data.cons d (.cons env kont)] (evCases.getD 6 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepEvProg_prefix 6 d env kont _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepEv, Prog.toData] using run⟩
    have hE : esize (Prog.const d) = d.size + 14 := by
      simp only [Prog.esize_eq_size_toData]; size_omega
    rw [hsplit, hE]
    size_omega

/-! ## The "return" cases -/

/-- Cases of `stepRetProg`; input `cons v (cons env (cons fb k))` with `fb` the payload of
the top frame. After the three `elim`s the environment is
`[fb, k, env, cons fb k, v, cons env (cons fb k), input]`. -/
def retCons1 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 0 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.var 1) (.cons (.cons (.const (.ofNat 1)) (.var 6)) (.var 3)))))))

def retCons2 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil
    (.cons (.cons (.cons .nil .nil) (.cons (.var 0) (.var 4))) (.cons (.var 2) (.var 1)))))

def retLet1 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 0 .nil
    (.cons (.cons .nil (.var 0)) (.cons (.cons (.var 6) (.var 1)) (.var 3))))))

def retLoop1 : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 0 .nil
    (.elim 6 (.cons (.const (.cons (.cons .nil .nil) .nil)) (.cons (.var 1) (.var 3)))
      (.elim 0 (.cons (.cons (.cons .nil .nil) (.var 1)) (.cons (.var 3) (.var 5)))
        (.cons (.cons .nil (.var 4)) (.cons (.cons (.var 3) (projRight 5))
          (.cons (.cons (.const (.ofNat 3)) (.cons (.var 4) (.cons (.var 3) (projRight 5))))
            (.var 7)))))))))

theorem retCons1_wellScoped : retCons1.WellScoped 1 := by simp [retCons1, WellScoped]
theorem retCons2_wellScoped : retCons2.WellScoped 1 := by simp [retCons2, WellScoped]
theorem retLet1_wellScoped : retLet1.WellScoped 1 := by simp [retLet1, WellScoped]
theorem retLoop1_wellScoped : retLoop1.WellScoped 1 := by
  simp [retLoop1, projRight, WellScoped]

theorem retCons1_runs (t' env' v env k : Data) :
    ∃ s ≤ t'.size + env'.size + v.size + k.size + 20,
      Eval [Data.cons v (.cons env (.cons (.cons t' env') k))] retCons1
        (.cons (evD t') (.cons env' (.cons (.cons (.ofNat 1) v) k))) s := by
  have run : Eval [Data.cons v (.cons env (.cons (.cons t' env') k))] retCons1
      (.cons (evD t') (.cons env' (.cons (.cons (.ofNat 1) v) k))) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons (.cons t' env') k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons t' env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons t' env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := t') (b := env') (by simp)
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := t') (by simp)))
              (Eval.cons (Eval.var_of_get (i := 1) (v := env') (by simp))
                (Eval.cons (Eval.cons (Eval.const _ (.ofNat 1))
                    (Eval.var_of_get (i := 6) (v := v) (by simp)))
                  (Eval.var_of_get (i := 3) (v := k) (by simp))))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem retCons2_runs (a v env k : Data) :
    ∃ s ≤ a.size + v.size + env.size + k.size + 16,
      Eval [Data.cons v (.cons env (.cons a k))] retCons2
        (.cons (retD (.cons a v)) (.cons env k)) s := by
  have run : Eval [Data.cons v (.cons env (.cons a k))] retCons2
      (.cons (retD (.cons a v)) (.cons env k)) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons a k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons a k) (by simp)
        (Eval.elim_cons (i := 1) (a := a) (b := k) (by simp)
          (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.cons (Eval.var_of_get (i := 0) (v := a) (by simp))
                (Eval.var_of_get (i := 4) (v := v) (by simp))))
            (Eval.cons (Eval.var_of_get (i := 2) (v := env) (by simp))
              (Eval.var_of_get (i := 1) (v := k) (by simp))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem retLet1_runs (b env' v env k : Data) :
    ∃ s ≤ b.size + v.size + env'.size + k.size + 16,
      Eval [Data.cons v (.cons env (.cons (.cons b env') k))] retLet1
        (.cons (evD b) (.cons (.cons v env') k)) s := by
  have run : Eval [Data.cons v (.cons env (.cons (.cons b env') k))] retLet1
      (.cons (evD b) (.cons (.cons v env') k)) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons (.cons b env') k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := b) (by simp)))
              (Eval.cons (Eval.cons (Eval.var_of_get (i := 6) (v := v) (by simp))
                  (Eval.var_of_get (i := 1) (v := env') (by simp)))
                (Eval.var_of_get (i := 3) (v := k) (by simp)))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem retLoop1_runs_nil (b env' env k : Data) :
    ∃ s ≤ env'.size + k.size + 16,
      Eval [Data.cons .nil (.cons env (.cons (.cons b env') k))] retLoop1
        (.cons (retD .nil) (.cons env' k)) s := by
  have run : Eval [Data.cons .nil (.cons env (.cons (.cons b env') k))] retLoop1
      (.cons (retD .nil) (.cons env' k)) _ :=
    Eval.elim_cons (i := 0) (a := .nil) (b := .cons env (.cons (.cons b env') k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.elim_nil (i := 6) (by simp)
              (Eval.cons (Eval.const _ (.cons (.cons .nil .nil) .nil))
                (Eval.cons (Eval.var_of_get (i := 1) (v := env') (by simp))
                  (Eval.var_of_get (i := 3) (v := k) (by simp))))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem retLoop1_runs_stop (b env' c env k : Data) :
    ∃ s ≤ c.size + env'.size + k.size + 18,
      Eval [Data.cons (.cons .nil c) (.cons env (.cons (.cons b env') k))] retLoop1
        (.cons (retD c) (.cons env' k)) s := by
  have run : Eval [Data.cons (.cons .nil c) (.cons env (.cons (.cons b env') k))] retLoop1
      (.cons (retD c) (.cons env' k)) _ :=
    Eval.elim_cons (i := 0) (a := .cons .nil c) (b := .cons env (.cons (.cons b env') k))
      (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.elim_cons (i := 6) (a := .nil) (b := c) (by simp)
              (Eval.elim_nil (i := 0) (by simp)
                (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                    (Eval.var_of_get (i := 1) (v := c) (by simp)))
                  (Eval.cons (Eval.var_of_get (i := 3) (v := env') (by simp))
                    (Eval.var_of_get (i := 5) (v := k) (by simp)))))))))
  refine ⟨_, ?_, run⟩
  size_omega

theorem retLoop1_runs_step (b env' a₁ a₂ c env k : Data) :
    ∃ s ≤ 2 * b.size + 2 * c.size + 2 * env'.size + k.size + 40,
      Eval [Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b env') k))] retLoop1
        (.cons (evD b) (.cons (.cons c env'.right)
          (.cons (.cons (.ofNat 3) (.cons b (.cons c env'.right))) k))) s := by
  obtain ⟨s₁, hs₁, hr₁⟩ := projRight_runs (E := a₁ :: a₂ :: Data.cons a₁ a₂ :: c :: b :: env' ::
    Data.cons b env' :: k :: env :: Data.cons (.cons b env') k :: Data.cons (.cons a₁ a₂) c ::
    Data.cons env (.cons (.cons b env') k) ::
    [Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b env') k))]) (i := 5) (d := env')
    (by simp)
  have run : Eval [Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b env') k))] retLoop1
      (.cons (evD b) (.cons (.cons c env'.right)
        (.cons (.cons (.ofNat 3) (.cons b (.cons c env'.right))) k))) _ :=
    Eval.elim_cons (i := 0) (a := .cons (.cons a₁ a₂) c) (b := .cons env (.cons (.cons b env') k))
      (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons b env') k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons b env') (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := b) (b := env') (by simp)
            (Eval.elim_cons (i := 6) (a := .cons a₁ a₂) (b := c) (by simp)
              (Eval.elim_cons (i := 0) (a := a₁) (b := a₂) (by simp)
                (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 4) (v := b) (by simp)))
                  (Eval.cons (Eval.cons (Eval.var_of_get (i := 3) (v := c) (by simp)) hr₁)
                    (Eval.cons (Eval.cons (Eval.const _ (.ofNat 3))
                        (Eval.cons (Eval.var_of_get (i := 4) (v := b) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 3) (v := c) (by simp)) hr₁)))
                      (Eval.var_of_get (i := 7) (v := k) (by simp))))))))))
  refine ⟨_, ?_, run⟩
  size_omega

/-! ## The "return" step -/

/-- The case programs of `stepRetProg`, indexed by the tag of the top frame. -/
def retCases : List Prog := [retCons1, retCons2, retLet1, retLoop1]

theorem retCases_wellScoped : ∀ c ∈ retCases, c.WellScoped 1 := by
  intro c hc
  simp only [retCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  exacts [retCons1_wellScoped, retCons2_wellScoped, retLet1_wellScoped, retLoop1_wellScoped]

/-- The step on "return `v`"; input `cons v (cons env kont)`. -/
def stepRetProg : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 (.cons (.cons (.cons .nil .nil) (.var 2)) (.var 3))
    (.elim 0 .nil (.let_ (.cons (.var 6) (.cons (.var 4) (.cons (.var 1) (.var 3))))
      (.let_ (.var 1) (dispatch retCases 0 1))))))

theorem stepRetProg_wellScoped : stepRetProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide,
    ⟨⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩, by simp [WellScoped]⟩,
    by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    ⟨by simp [WellScoped], dispatch_wellScoped retCases 0 1 11 (by omega) (by omega) retCases_wellScoped⟩⟩

theorem stepRetProg_runs_nil (v env : Data) :
    ∃ s ≤ v.size + env.size + 12,
      stepRetProg.Runs (.cons v (.cons env .nil)) (stepRet v env .nil) s := by
  have run : Eval [Data.cons v (.cons env .nil)] stepRetProg (.cons (retD v) (.cons env .nil)) _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env .nil) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .nil) (by simp)
        (Eval.elim_nil (i := 1) (by simp)
          (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.var_of_get (i := 2) (v := v) (by simp)))
            (Eval.var_of_get (i := 3) (v := .cons env .nil) (by simp)))))
  refine ⟨_, ?_, by simpa [Prog.Runs, stepRet] using run⟩
  size_omega

/-- The environment in which the dispatch of `stepRetProg` runs, for a top frame with tag
`ftag` and payload `fb`. -/
def retDispEnv (ftag : ℕ) (fb v env k : Data) : Env :=
  [Data.ofNat ftag, .cons v (.cons env (.cons fb k)), .ofNat ftag, fb, .cons (.ofNat ftag) fb, k,
    env, .cons (.cons (.ofNat ftag) fb) k, v, .cons env (.cons (.cons (.ofNat ftag) fb) k),
    .cons v (.cons env (.cons (.cons (.ofNat ftag) fb) k))]

theorem stepRetProg_prefix (ftag : ℕ) (fb v env k r : Data) {s : ℕ}
    (hd : Eval (retDispEnv ftag fb v env k) (dispatch retCases 0 1) r s) :
    ∃ c ≤ s + v.size + env.size + fb.size + k.size + (Data.ofNat ftag).size + 16,
      Eval [Data.cons v (.cons env (.cons (.cons (.ofNat ftag) fb) k))] stepRetProg r c := by
  have run : Eval [Data.cons v (.cons env (.cons (.cons (.ofNat ftag) fb) k))] stepRetProg r _ :=
    Eval.elim_cons (i := 0) (a := v) (b := .cons env (.cons (.cons (.ofNat ftag) fb) k)) (by simp)
      (Eval.elim_cons (i := 1) (a := env) (b := .cons (.cons (.ofNat ftag) fb) k) (by simp)
        (Eval.elim_cons (i := 1) (a := .cons (.ofNat ftag) fb) (b := k) (by simp)
          (Eval.elim_cons (i := 0) (a := .ofNat ftag) (b := fb) (by simp)
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 6) (v := v) (by simp))
                (Eval.cons (Eval.var_of_get (i := 4) (v := env) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 1) (v := fb) (by simp))
                    (Eval.var_of_get (i := 3) (v := k) (by simp)))))
              (Eval.let_ (Eval.var_of_get (i := 1) (v := .ofNat ftag) (by simp)) hd)))))
  exact ⟨_, by omega, run⟩

/-- Bound of one "return" step in terms of `S = v.size + env.size + kont.size`. -/
def stepRetBound (S : ℕ) : ℕ := 8 * S + 120

theorem stepRetProg_runs_cons (v env : Data) (f : Frame) (k : Data) :
    ∃ s ≤ stepRetBound (v.size + env.size + (Frame.toData f).size + k.size),
      stepRetProg.Runs (.cons v (.cons env (.cons (Frame.toData f) k)))
        (stepRet v env (.cons (Frame.toData f) k)) s := by
  cases f with
  | cons1 t' env' =>
    obtain ⟨c₀, hc₀, hcase⟩ := retCons1_runs t'.toData (Data.list env') v env k
    obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 0 0 1
      (retDispEnv 0 (.cons t'.toData (.list env')) v env k)
      (Data.cons v (.cons env (.cons (.cons t'.toData (.list env')) k))) _ c₀ (by simp [retCases])
      retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
      (show Eval [Data.cons v (.cons env (.cons (.cons t'.toData (.list env')) k))]
        (retCases.getD 0 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepRetProg_prefix 0 (.cons t'.toData (.list env')) v env k _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
    unfold stepRetBound
    size_omega
  | cons2 a =>
    obtain ⟨c₀, hc₀, hcase⟩ := retCons2_runs a v env k
    obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 1 0 1 (retDispEnv 1 a v env k)
      (Data.cons v (.cons env (.cons a k))) _ c₀ (by simp [retCases])
      retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
      (show Eval [Data.cons v (.cons env (.cons a k))] (retCases.getD 1 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepRetProg_prefix 1 a v env k _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
    unfold stepRetBound
    size_omega
  | let1 b env' =>
    obtain ⟨c₀, hc₀, hcase⟩ := retLet1_runs b.toData (Data.list env') v env k
    obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 2 0 1
      (retDispEnv 2 (.cons b.toData (.list env')) v env k)
      (Data.cons v (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀ (by simp [retCases])
      retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
      (show Eval [Data.cons v (.cons env (.cons (.cons b.toData (.list env')) k))]
        (retCases.getD 2 .nil) _ _ from hcase)
    obtain ⟨c', hc', run⟩ := stepRetProg_prefix 2 (.cons b.toData (.list env')) v env k _ hd
    refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
    unfold stepRetBound
    size_omega
  | loop1 b env' =>
    rcases v with _ | ⟨_ | ⟨a₁, a₂⟩, c⟩
    · obtain ⟨c₀, hc₀, hcase⟩ := retLoop1_runs_nil b.toData (Data.list env') env k
      obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 3 0 1
        (retDispEnv 3 (.cons b.toData (.list env')) .nil env k)
        (Data.cons .nil (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀ (by simp [retCases])
        retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
        (show Eval [Data.cons .nil (.cons env (.cons (.cons b.toData (.list env')) k))]
          (retCases.getD 3 .nil) _ _ from hcase)
      obtain ⟨c', hc', run⟩ := stepRetProg_prefix 3 (.cons b.toData (.list env')) .nil env k _ hd
      refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
      unfold stepRetBound
      size_omega
    · obtain ⟨c₀, hc₀, hcase⟩ := retLoop1_runs_stop b.toData (Data.list env') c env k
      obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 3 0 1
        (retDispEnv 3 (.cons b.toData (.list env')) (.cons .nil c) env k)
        (Data.cons (.cons .nil c) (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀
        (by simp [retCases]) retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
        (show Eval [Data.cons (.cons .nil c) (.cons env (.cons (.cons b.toData (.list env')) k))]
          (retCases.getD 3 .nil) _ _ from hcase)
      obtain ⟨c', hc', run⟩ :=
        stepRetProg_prefix 3 (.cons b.toData (.list env')) (.cons .nil c) env k _ hd
      refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
      unfold stepRetBound
      size_omega
    · obtain ⟨c₀, hc₀, hcase⟩ := retLoop1_runs_step b.toData (Data.list env') a₁ a₂ c env k
      obtain ⟨s, hs, hd⟩ := dispatch_runs retCases 3 0 1
        (retDispEnv 3 (.cons b.toData (.list env')) (.cons (.cons a₁ a₂) c) env k)
        (Data.cons (.cons (.cons a₁ a₂) c) (.cons env (.cons (.cons b.toData (.list env')) k))) _ c₀
        (by simp [retCases]) retCases_wellScoped (by simp [retDispEnv]) (by simp [retDispEnv])
        (show Eval [Data.cons (.cons (.cons a₁ a₂) c)
          (.cons env (.cons (.cons b.toData (.list env')) k))] (retCases.getD 3 .nil) _ _ from hcase)
      obtain ⟨c', hc', run⟩ :=
        stepRetProg_prefix 3 (.cons b.toData (.list env')) (.cons (.cons a₁ a₂) c) env k _ hd
      refine ⟨_, ?_, by simpa [Prog.Runs, stepRet, Frame.toData] using run⟩
      have hsz := size_right_le (Data.list env')
      unfold stepRetBound
      size_omega

/-! ## The step -/

/-- The step function as a program: on the encoding of a configuration, the encoding of
the next configuration. -/
def stepProg : Prog :=
  .elim 0 .nil (.elim 0 .nil (.let_ (.cons (.var 1) (.var 3))
    (.elim 1 (callVar 0 stepEvProg) (callVar 2 stepRetProg))))

theorem stepProg_wellScoped : stepProg.WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    by decide, callVar_wellScoped (by decide) stepEvProg_wellScoped,
    callVar_wellScoped (by decide) stepRetProg_wellScoped⟩

/-- Bound of one step of the interpreter in terms of the size of the configuration. -/
def stepBound (S : ℕ) : ℕ := (S + 1) * (S + 40) + 200

theorem le_stepBound_of_le {c S T : ℕ} (hc : c ≤ 41 * S + 240) (hS : S ≤ T) :
    c ≤ stepBound T := by
  unfold stepBound; nlinarith [Nat.mul_le_mul hS hS]

theorem le_stepBound_of_quad {c S T : ℕ} (hc : c ≤ (S + 1) * (S + 30) + 100 + 3 * S + 60)
    (hS : S + 4 ≤ T) : c ≤ stepBound T := by
  unfold stepBound; nlinarith [Nat.mul_le_mul hS hS]

/-- `stepProg` computes the step of the machine on encoded configurations, at a cost
quadratic in the size of the configuration. -/
theorem stepProg_runs (c : Cfg) :
    ∃ s ≤ stepBound (Cfg.toData c).size, stepProg.Runs c.toData (step c).toData s := by
  rw [← stepData_toData]
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    obtain ⟨s, hs, hev⟩ := stepEvProg_runs p (Data.list env) (Data.list (kont.map Frame.toData))
    have run : Eval [Cfg.toData ⟨.ev p, env, kont⟩] stepProg
        (stepEv p.toData (Data.list env) (Data.list (kont.map Frame.toData))) _ :=
      Eval.elim_cons (i := 0) (a := evD p.toData)
        (b := .cons (.list env) (.list (kont.map Frame.toData))) (by simp [Cfg.toData, Ctrl.toData])
        (Eval.elim_cons (i := 0) (a := .nil) (b := p.toData) (by simp [evD])
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := p.toData) (by simp))
              (Eval.var_of_get (i := 3) (v := .cons (.list env) (.list (kont.map Frame.toData)))
                (by simp)))
            (Eval.elim_nil (i := 1) (by simp)
              (callVar_eval (i := 0) stepEvProg_wellScoped
                (v := .cons p.toData (.cons (.list env) (.list (kont.map Frame.toData))))
                (by simp) hev))))
    refine ⟨_, ?_, by simpa [Prog.Runs, stepData, Cfg.toData, Ctrl.toData, evD] using run⟩
    refine le_stepBound_of_quad
      (S := esize p + (Data.list env).size + (Data.list (kont.map Frame.toData)).size) ?_ ?_
    · unfold stepEvBound at hs
      rw [Prog.esize_eq_size_toData] at hs ⊢
      size_omega
    · rw [Prog.esize_eq_size_toData]
      size_omega
  | ret v =>
    cases kont with
    | nil =>
      obtain ⟨s, hs, hret⟩ := stepRetProg_runs_nil v (Data.list env)
      have run : Eval [Cfg.toData ⟨.ret v, env, []⟩] stepProg (stepRet v (Data.list env) .nil) _ :=
        Eval.elim_cons (i := 0) (a := retD v) (b := .cons (.list env) .nil)
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := v) (by simp))
                (Eval.var_of_get (i := 3) (v := .cons (.list env) .nil) (by simp)))
              (Eval.elim_cons (i := 1) (a := .nil) (b := .nil) (by simp)
                (callVar_eval (i := 2) stepRetProg_wellScoped (v := .cons v (.cons (.list env) .nil))
                  (by simp) hret))))
      refine ⟨_, ?_, by simpa [Prog.Runs, stepData, Cfg.toData, Ctrl.toData, retD] using run⟩
      refine le_stepBound_of_le (S := v.size + (Data.list env).size) ?_ ?_
      · size_omega
      · size_omega
    | cons f k =>
      obtain ⟨s, hs, hret⟩ :=
        stepRetProg_runs_cons v (Data.list env) f (Data.list (k.map Frame.toData))
      have run : Eval [Cfg.toData ⟨.ret v, env, f :: k⟩] stepProg
          (stepRet v (Data.list env) (.cons (Frame.toData f) (Data.list (k.map Frame.toData)))) _ :=
        Eval.elim_cons (i := 0) (a := retD v)
          (b := .cons (.list env) (.cons (Frame.toData f) (Data.list (k.map Frame.toData))))
          (by simp [Cfg.toData, Ctrl.toData])
          (Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := v) (by simp [retD])
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := v) (by simp))
                (Eval.var_of_get (i := 3)
                  (v := .cons (.list env) (.cons (Frame.toData f) (Data.list (k.map Frame.toData))))
                  (by simp)))
              (Eval.elim_cons (i := 1) (a := .nil) (b := .nil) (by simp)
                (callVar_eval (i := 2) stepRetProg_wellScoped
                  (v := .cons v (.cons (.list env)
                    (.cons (Frame.toData f) (Data.list (k.map Frame.toData)))))
                  (by simp) hret))))
      refine ⟨_, ?_, by simpa [Prog.Runs, stepData, Cfg.toData, Ctrl.toData, retD] using run⟩
      refine le_stepBound_of_le
        (S := v.size + (Data.list env).size + (Frame.toData f).size +
          (Data.list (k.map Frame.toData)).size) ?_ ?_
      · unfold stepRetBound at hs
        size_omega
      · size_omega

end Machine

end MIPRE.Cost
