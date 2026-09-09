/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Machine
import MIPRE.Foundations.Cost.Codable

/-!
# The evaluation machine on data

Configurations of the evaluation machine (`Cost/Machine.lean`) encoded as `Data`
(`Machine.Cfg.toData`), and the step function transported to `Data` (`Machine.stepData`),
defined by the first-order operations `left`, `right`, `cons`, `unaryToNat`, `getList`
only — so that it is primitive recursive (`Cost/Partrec.lean`) and implementable by a
program of the ambient model (the self-interpreter). The correspondence is
`stepData_toData : stepData c.toData = (step c).toData`.

Encoding: a control is `cons nil (toData p)` ("evaluate `p`") or `cons (cons nil nil) v`
("return `v`"); a configuration is `cons ctrl (cons env kont)` with the environment and the
stack as `cons`-chains; a frame is `cons (ofNat tag) payload` with tags `0`–`3` for
`cons1 t env` (payload `cons t env`), `cons2 a` (payload `a`), `let1 b env`, `loop1 b env`.
-/

namespace MIPRE.Cost

namespace Machine

/-! ## Encoding -/

/-- The control "evaluate the program `p`" (as data). -/
def evD (p : Data) : Data := .cons .nil p

/-- The control "return the value `v`". -/
def retD (v : Data) : Data := .cons (.cons .nil .nil) v

/-- Controls as data. -/
def Ctrl.toData : Ctrl → Data
  | .ev p => evD p.toData
  | .ret v => retD v

/-- Frames as data. -/
def Frame.toData : Frame → Data
  | .cons1 t env => .cons (.ofNat 0) (.cons t.toData (.list env))
  | .cons2 a => .cons (.ofNat 1) a
  | .let1 b env => .cons (.ofNat 2) (.cons b.toData (.list env))
  | .loop1 b env => .cons (.ofNat 3) (.cons b.toData (.list env))

/-- Configurations as data. -/
def Cfg.toData (c : Cfg) : Data :=
  .cons c.ctrl.toData (.cons (.list c.env) (.list (c.kont.map Frame.toData)))

/-- The initial configuration for the program `p` (as data) on the input `x`. -/
def initData (p x : Data) : Data := .cons (evD p) (.cons (.cons x .nil) .nil)

theorem initData_eq (p : Prog) (x : Data) : initData p.toData x = Cfg.toData ⟨.ev p, [x], []⟩ :=
  rfl

/-- Final configurations, as data: a returned value with an empty stack. -/
def IsFinalD (d : Data) : Prop := d.left.left ≠ .nil ∧ d.right.right = .nil

instance : DecidablePred IsFinalD := fun d => by unfold IsFinalD; infer_instance

/-- The value of a final configuration. -/
def resultD (d : Data) : Data := d.left.right

theorem isFinalD_toData (c : Cfg) : IsFinalD c.toData ↔ ∃ r e, c = ⟨.ret r, e, []⟩ := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    simp [IsFinalD, Cfg.toData, Ctrl.toData, evD]
  | ret v =>
    cases kont with
    | nil => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]
    | cons f k => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]

theorem resultD_toData (r : Data) (e : Env) : resultD (Cfg.toData ⟨.ret r, e, []⟩) = r := rfl

/-! ## The step function on data -/

/-- The step on "evaluate `p`" with environment `env` and stack `kont`. -/
def stepEv (p env kont : Data) : Data :=
  if Data.unaryToNat p.left = 0 then
    .cons (retD (Data.getList env (Data.unaryToNat p.right))) (.cons env kont)
  else if Data.unaryToNat p.left = 1 then .cons (retD .nil) (.cons env kont)
  else if Data.unaryToNat p.left = 2 then
    .cons (evD p.right.left) (.cons env (.cons (.cons (.ofNat 0) (.cons p.right.right env)) kont))
  else if Data.unaryToNat p.left = 3 then
    if Data.getList env (Data.unaryToNat p.right.left) = .nil then
      .cons (evD p.right.right.left) (.cons env kont)
    else
      .cons (evD p.right.right.right)
        (.cons (.cons (Data.getList env (Data.unaryToNat p.right.left)).left
          (.cons (Data.getList env (Data.unaryToNat p.right.left)).right env)) kont)
  else if Data.unaryToNat p.left = 4 then
    .cons (evD p.right.left) (.cons env (.cons (.cons (.ofNat 2) (.cons p.right.right env)) kont))
  else if Data.unaryToNat p.left = 5 then
    .cons (evD p.right) (.cons env (.cons (.cons (.ofNat 3) (.cons p.right env)) kont))
  else .cons (retD p.right) (.cons env kont)

/-- The step on "return `v`" with environment `env` and stack `kont`. -/
def stepRet (v env kont : Data) : Data :=
  if kont = .nil then .cons (retD v) (.cons env kont)
  else if Data.unaryToNat kont.left.left = 0 then
    .cons (evD kont.left.right.left)
      (.cons kont.left.right.right (.cons (.cons (.ofNat 1) v) kont.right))
  else if Data.unaryToNat kont.left.left = 1 then
    .cons (retD (.cons kont.left.right v)) (.cons env kont.right)
  else if Data.unaryToNat kont.left.left = 2 then
    .cons (evD kont.left.right.left) (.cons (.cons v kont.left.right.right) kont.right)
  else if v = .nil then .cons (retD .nil) (.cons kont.left.right.right kont.right)
  else if v.left = .nil then .cons (retD v.right) (.cons kont.left.right.right kont.right)
  else
    .cons (evD kont.left.right.left)
      (.cons (.cons v.right kont.left.right.right.right)
        (.cons (.cons (.ofNat 3)
          (.cons kont.left.right.left (.cons v.right kont.left.right.right.right)))
          kont.right))

/-- The step function on data. -/
def stepData (d : Data) : Data :=
  if d.left.left = .nil then stepEv d.left.right d.right.left d.right.right
  else stepRet d.left.right d.right.left d.right.right

theorem right_list (l : List Data) : (Data.list l).right = Data.list l.tail := by
  cases l <;> rfl

/-- The step on data agrees with the machine. -/
theorem stepData_toData (c : Cfg) : stepData c.toData = (step c).toData := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    cases p with
    | var i =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepEv, Prog.toData, step,
        Data.getList_list]
    | nil => simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepEv, Prog.toData, step]
    | const d => simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepEv, Prog.toData, step]
    | cons h t =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step, Frame.toData]
    | elim i n c =>
      rcases hget : env.get i with _ | ⟨a, b⟩
      · simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step,
          Data.getList_list, hget]
      · simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step,
          Data.getList_list, hget]
    | let_ e b =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step, Frame.toData]
    | loop b =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step, Frame.toData]
  | ret v =>
    cases kont with
    | nil => simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step]
    | cons f k =>
      cases f with
      | cons1 t env' =>
        simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepRet, step, Frame.toData]
      | cons2 a =>
        simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step, Frame.toData]
      | let1 b env' =>
        simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepRet, step, Frame.toData]
      | loop1 b env' =>
        rcases v with _ | ⟨_ | ⟨x, y⟩, v'⟩
        · simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step, Frame.toData]
        · simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step, Frame.toData]
        · simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepRet, step, Frame.toData,
            right_list]

theorem iterate_stepData_toData (c : Cfg) (N : ℕ) :
    stepData^[N] c.toData = (step^[N] c).toData := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepData_toData, ih]

end Machine

end MIPRE.Cost
