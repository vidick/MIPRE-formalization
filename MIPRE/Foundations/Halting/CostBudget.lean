/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.BoundedEval
import MIPRE.Foundations.Halting.Descriptions

/-!
# Deciding a cost budget

`Machine.runForD` runs a program for a *step* budget, and that is all the tabulation of a game
needs: a program obeying a time bound halts, so one long-enough run settles what it returns.
Obligation **O3** needs the other question — whether a program halts *within a given cost* —
and needs it both ways, because `Obligations.sem_spec` is an equivalence: the semidecider has
to halt on every string whose verifier violates its time bound, and on no other.

That question is not answered by a step budget. A derivation of cost `t` takes at most `3 t`
machine steps (`Machine.eval_steps_count`), but a step is not a unit of cost: reading a
variable or a constant is charged the size of the value (`Machine.stepCost`), so a run of
`3 k` steps can cost far more than `k`, and `runForD` returning a value says only that the
program halted — not that it halted in budget.

So this file carries the cost along the run. `Machine.stepCostD` is `Machine.stepCost` on
encoded configurations — the same seven program tags and four frame tags that
`Machine.stepEv` and `Machine.stepRet` dispatch on — and `Machine.costStep` is the step
function paired with the running total. Then

* `Machine.evalForCostD p x k` iterates it `3 k + 1` times and returns the result only if the
  configuration reached is final *and* the accumulated cost is at most `k`;
* `Machine.haltsWithin_iff_evalForCostD` is its correctness, in both directions: the budget
  `3 k + 1` is enough for every run of cost at most `k` (`eval_steps_count`), and the cost the
  iteration accumulates at a final configuration is the cost of the derivation that reached it
  (`eval_of_steps`, with `costSum_final` absorbing the steps after the end);
* `Machine.primrec_haltsWithinB` and `Cost.decidableHaltsWithin` are what comes out:
  **`Prog.HaltsWithin` is a primitive recursive predicate of the program, the input and the
  budget**, hence decidable. This is the `noncomputable` `Cost.evalWithin` made computable,
  as `runForD` is for `Machine.evalData`.

The file lives under `Halting/` only because it needs `Data.primrec_size`, which
`Halting/Descriptions.lean` proves; nothing in it knows about verifiers or descriptions.
-/

namespace MIPRE.Cost

namespace Machine

/-! ## The cost charged at a step, on encoded configurations -/

/-- The cost charged at an "evaluate `p`" step with environment `env`: the tags are those of
`Prog.toData`, so `0` is `var` (charged the size of the value read), `5` is `loop` (free, its
rules being charged when the body's value is dispatched), `6` and above are `const` (charged
the size of the constant), and `1`–`4` are the remaining rules, each charged one. -/
def stepCostEvD (p env : Data) : ℕ :=
  if Data.unaryToNat p.left = 0 then (Data.getList env (Data.unaryToNat p.right)).size + 1
  else if Data.unaryToNat p.left = 5 then 0
  else if Data.unaryToNat p.left ≤ 5 then 1
  else p.right.size

/-- The cost charged at a "return" step: one when the frame on top is a `loop1` (tag `3`), and
nothing otherwise — in particular nothing at a final configuration, whose stack is empty. -/
def stepCostRetD (kont : Data) : ℕ :=
  if kont = .nil then 0
  else if Data.unaryToNat kont.left.left = 3 then 1
  else 0

/-- `Machine.stepCost` on encoded configurations. -/
def stepCostD (d : Data) : ℕ :=
  if d.left.left = .nil then stepCostEvD d.left.right d.right.left
  else stepCostRetD d.right.right

theorem stepCostD_toData (c : Cfg) : stepCostD c.toData = stepCost c := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    cases p with
    | var i => simp [stepCostD, Cfg.toData, Ctrl.toData, evD, stepCostEvD, Prog.toData,
        Data.getList_list, stepCost]
    | nil => simp [stepCostD, Cfg.toData, Ctrl.toData, evD, stepCostEvD, Prog.toData, stepCost]
    | const d => simp [stepCostD, Cfg.toData, Ctrl.toData, evD, stepCostEvD, Prog.toData, stepCost]
    | cons h t => simp [stepCostD, Cfg.toData, Ctrl.toData, evD, stepCostEvD, Prog.toData, stepCost]
    | elim i n c => simp [stepCostD, Cfg.toData, Ctrl.toData, evD, stepCostEvD, Prog.toData,
        stepCost]
    | let_ e b => simp [stepCostD, Cfg.toData, Ctrl.toData, evD, stepCostEvD, Prog.toData, stepCost]
    | loop b => simp [stepCostD, Cfg.toData, Ctrl.toData, evD, stepCostEvD, Prog.toData, stepCost]
  | ret v =>
    cases kont with
    | nil => simp [stepCostD, Cfg.toData, Ctrl.toData, retD, stepCostRetD, stepCost]
    | cons f rest =>
      cases f with
      | cons1 t e => simp [stepCostD, Cfg.toData, Ctrl.toData, retD, stepCostRetD, Frame.toData,
          stepCost]
      | cons2 a => simp [stepCostD, Cfg.toData, Ctrl.toData, retD, stepCostRetD, Frame.toData,
          stepCost]
      | let1 b e => simp [stepCostD, Cfg.toData, Ctrl.toData, retD, stepCostRetD, Frame.toData,
          stepCost]
      | loop1 b e => simp [stepCostD, Cfg.toData, Ctrl.toData, retD, stepCostRetD, Frame.toData,
          stepCost]

open Primrec in
theorem primrec_stepCostEv : Primrec fun q : Data × Data => stepCostEvD q.1 q.2 := by
  have htag : Primrec fun q : Data × Data => Data.unaryToNat q.1.left := primrec_tag.comp fst
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data => Data.unaryToNat q.1.left = n :=
    fun n => PrimrecRel.comp Primrec.eq htag (const n)
  have hle : PrimrecPred fun q : Data × Data => Data.unaryToNat q.1.left ≤ 5 :=
    PrimrecRel.comp Primrec.nat_le htag (const 5)
  have hvar : Primrec fun q : Data × Data =>
      (Data.getList q.2 (Data.unaryToNat q.1.right)).size + 1 :=
    Primrec.succ.comp (Data.primrec_size.comp
      (Data.primrec_getList.comp snd (Data.primrec_unaryToNat.comp (Data.primrec_right.comp fst))))
  exact Primrec.ite (heq 0) hvar (Primrec.ite (heq 5) (const 0) (Primrec.ite hle (const 1)
    (Data.primrec_size.comp (Data.primrec_right.comp fst))))

open Primrec in
theorem primrec_stepCostRet : Primrec stepCostRetD := by
  have hnil : PrimrecPred fun d : Data => d = Data.nil :=
    PrimrecRel.comp Primrec.eq Primrec.id (const Data.nil)
  have htag : Primrec fun d : Data => Data.unaryToNat d.left.left :=
    Data.primrec_unaryToNat.comp (Data.primrec_left.comp Data.primrec_left)
  have heq : PrimrecPred fun d : Data => Data.unaryToNat d.left.left = 3 :=
    PrimrecRel.comp Primrec.eq htag (const 3)
  exact Primrec.ite hnil (const 0) (Primrec.ite heq (const 1) (const 0))

open Primrec in
theorem primrec_stepCostD : Primrec stepCostD := by
  have hnil : PrimrecPred fun d : Data => d.left.left = Data.nil :=
    PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil)
  exact Primrec.ite hnil
    (primrec_stepCostEv.comp ((Data.primrec_right.comp Data.primrec_left).pair
      (Data.primrec_left.comp Data.primrec_right)))
    (primrec_stepCostRet.comp (Data.primrec_right.comp Data.primrec_right))

/-! ## The run with its accumulated cost -/

/-- One step of the machine, carrying the cost accumulated so far. -/
def costStep (q : Data × ℕ) : Data × ℕ := (stepData q.1, q.2 + stepCostD q.1)

open Primrec in
theorem primrec_costStep : Primrec costStep :=
  (primrec_stepData.comp fst).pair (Primrec.nat_add.comp snd (primrec_stepCostD.comp fst))

theorem costStep_iterate (c : Cfg) (s n : ℕ) :
    costStep^[n] (c.toData, s) = ((step^[n] c).toData, s + costSum c n) := by
  induction n generalizing c s with
  | zero => simp [costSum]
  | succ n ih =>
    rw [Function.iterate_succ_apply, show costStep (c.toData, s) = ((step c).toData,
      s + stepCost c) from by rw [costStep, stepData_toData, stepCostD_toData], ih,
      Function.iterate_succ_apply, costSum, Nat.add_assoc]

/-- The configuration reached after `3 k + 1` cost-carrying steps, with the cost accumulated
along the way. -/
def costRun (pd x : Data) (k : ℕ) : Data × ℕ := costStep^[3 * k + 1] (initData pd x, 0)

theorem costRun_eq (p : Prog) (x : Data) (k : ℕ) :
    costRun (encode p) x k =
      ((step^[3 * k + 1] (⟨.ev p, [x], []⟩ : Cfg)).toData,
        costSum (⟨.ev p, [x], []⟩ : Cfg) (3 * k + 1)) := by
  rw [costRun, show initData (encode p) x = (⟨.ev p, [x], []⟩ : Cfg).toData from initData_eq p x,
    costStep_iterate, Nat.zero_add]

/-- **Running `p` on `x` under a cost budget `k`**: iterate the cost-carrying step `3 k + 1`
times and read off the result if the configuration reached is final and the accumulated cost is
within the budget. Total and primitive recursive. -/
def evalForCostD (pd x : Data) (k : ℕ) : Option Data :=
  if isFinalB (costRun pd x k).1 ∧ (costRun pd x k).2 ≤ k
    then some (resultD (costRun pd x k).1) else none

/-- **Completeness.** A run of cost at most the budget is found. -/
theorem evalForCostD_eq_some {p : Prog} {x r : Data} {t k : ℕ} (h : p.Runs x r t) (hk : t ≤ k) :
    evalForCostD (encode p) x k = some r := by
  obtain ⟨N, e, hs, hN⟩ := eval_steps_count h []
  obtain ⟨m, hm⟩ : ∃ m, 3 * k + 1 = m + N := ⟨3 * k + 1 - N, by omega⟩
  have hm' : 3 * k + 1 = N + m := by omega
  have hfin : step^[3 * k + 1] (⟨.ev p, [x], []⟩ : Cfg) = ⟨.ret r, e, []⟩ := by
    rw [hm, Function.iterate_add_apply, hs.1, step_final]
  have hcost : costSum (⟨.ev p, [x], []⟩ : Cfg) (3 * k + 1) = t := by
    rw [hm', costSum_add, hs.1, hs.2, costSum_final, Nat.add_zero]
  rw [evalForCostD, costRun_eq, hfin, hcost]
  rw [if_pos ⟨(isFinalB_iff _).2 ((isFinalD_toData _).2 ⟨r, e, rfl⟩), hk⟩, resultD_toData]

/-- **Soundness.** Whatever is found is a genuine run of cost at most the budget. -/
theorem haltsWithin_of_evalForCostD {p : Prog} {x r : Data} {k : ℕ}
    (h : evalForCostD (encode p) x k = some r) : HaltsWithin p x k := by
  rw [evalForCostD, costRun_eq] at h
  by_cases hc : isFinalB (step^[3 * k + 1] (⟨.ev p, [x], []⟩ : Cfg)).toData = true ∧
      costSum (⟨.ev p, [x], []⟩ : Cfg) (3 * k + 1) ≤ k
  · obtain ⟨r', e', he⟩ := (isFinalD_toData _).1 ((isFinalB_iff _).1 hc.1)
    obtain ⟨r'', t, M, e'', N', hN, hev, hst⟩ := eval_of_steps (3 * k + 1) p [x] [] r' e' he
    have hcost : costSum (⟨.ev p, [x], []⟩ : Cfg) (3 * k + 1) = t := by
      rw [hN, costSum_add, hst.1, hst.2, costSum_final, Nat.add_zero]
    exact ⟨r'', t, by omega, hev⟩
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- **The decision procedure.** Halting within a cost budget is exactly what the cost-carrying
iteration reports. -/
theorem haltsWithin_iff_evalForCostD (p : Prog) (x : Data) (k : ℕ) :
    HaltsWithin p x k ↔ (evalForCostD (encode p) x k).isSome := by
  refine ⟨fun ⟨r, t, ht, h⟩ => ?_, fun h => ?_⟩
  · rw [evalForCostD_eq_some h ht]; rfl
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
    exact haltsWithin_of_evalForCostD hr

/-! ## Computability -/

open Primrec in
theorem primrec_costRun : Primrec fun q : (Data × Data) × ℕ => costRun q.1.1 q.1.2 q.2 := by
  have hinit : Primrec fun q : (Data × Data) × ℕ => ((initData q.1.1 q.1.2 : Data), (0 : ℕ)) :=
    (primrec_initData.comp (fst.comp fst) (snd.comp fst)).pair (const 0)
  exact Primrec.nat_iterate (Primrec.succ.comp (Primrec.nat_mul.comp (const 3) snd)) hinit
    (primrec_costStep.comp snd).to₂

open Primrec in
theorem primrec_evalForCostD :
    Primrec fun q : (Data × Data) × ℕ => evalForCostD q.1.1 q.1.2 q.2 := by
  have hcfg : Primrec fun q : (Data × Data) × ℕ => (costRun q.1.1 q.1.2 q.2).1 :=
    fst.comp primrec_costRun
  have hcost : Primrec fun q : (Data × Data) × ℕ => (costRun q.1.1 q.1.2 q.2).2 :=
    snd.comp primrec_costRun
  have hcond : PrimrecPred fun q : (Data × Data) × ℕ =>
      isFinalB (costRun q.1.1 q.1.2 q.2).1 = true ∧ (costRun q.1.1 q.1.2 q.2).2 ≤ q.2 :=
    PrimrecPred.and
      ⟨inferInstance, (primrec_isFinalB.comp hcfg).of_eq fun q => Bool.eq_iff_iff.2 (by simp)⟩
      (PrimrecRel.comp Primrec.nat_le hcost snd)
  exact Primrec.ite hcond (Primrec.option_some.comp (primrec_resultD.comp hcfg)) (const none)

/-- Halting within a cost budget, as a `Bool`. -/
def haltsWithinB (pd x : Data) (k : ℕ) : Bool := (evalForCostD pd x k).isSome

theorem primrec_haltsWithinB :
    Primrec fun q : (Data × Data) × ℕ => haltsWithinB q.1.1 q.1.2 q.2 :=
  Primrec.option_isSome.comp primrec_evalForCostD

theorem haltsWithinB_iff (p : Prog) (x : Data) (k : ℕ) :
    haltsWithinB (encode p) x k = true ↔ HaltsWithin p x k :=
  (haltsWithin_iff_evalForCostD p x k).symm

end Machine

/-- **Halting within a cost budget is decidable.** -/
instance decidableHaltsWithin (p : Prog) (x : Data) (k : ℕ) : Decidable (HaltsWithin p x k) :=
  decidable_of_iff _ (Machine.haltsWithinB_iff p x k)

end MIPRE.Cost
