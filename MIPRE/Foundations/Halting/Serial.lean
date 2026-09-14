/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Lists
import Mathlib.Tactic.Linarith

/-!
# Reading and writing descriptions, in the ambient model

The two programs that move between a datum and its postorder serialization
(`Data.toBitsPost`, `Halting/Descriptions.lean`):

* `Prog.parseProg`: the stack machine `Data.stackRun` on a bit string, returning the top of the
  final stack (`Data.parse`). The compressor's decider reads the description it was handed with
  it (`Halting/Compressor.lean`).
* `Prog.serProg`: the postorder serialization of a datum, by a loop over a list of pending
  items — a datum still to be written, or a marker for the closing `1` of a pair — accumulating
  the bits in reverse and reversing at the end. The compressor writes its output with it.

Both run in time quadratic in the size of their input: each step copies the remainder of the
work list and the accumulator.
-/

namespace MIPRE.Cost

namespace Data

/-- A pending item of the serializer: a datum to write (`some d`, as `cons nil d`) or the
closing `1` of a pair (`none`, as `nil`). -/
def itemD : Option Data → Data
  | some d => cons nil d
  | none => nil

/-- The bits still to be written for a list of pending items. -/
def serItems : List (Option Data) → BitStr
  | [] => []
  | some d :: r => d.toBitsPost ++ serItems r
  | none :: r => true :: serItems r

/-- The measure of a list of pending items, decreasing along the serializer's loop. -/
def serMeasure : List (Option Data) → ℕ
  | [] => 0
  | some d :: r => 3 * d.size + 1 + serMeasure r
  | none :: r => 1 + serMeasure r

/-- The same measure, on the data of the pending list (for the loop invariant). -/
def serMeasureD : Data → ℕ
  | nil => 0
  | cons nil r => 1 + serMeasureD r
  | cons (cons _ d) r => 3 * d.size + 1 + serMeasureD r

theorem serMeasureD_list (items : List (Option Data)) :
    serMeasureD (list (items.map itemD)) = serMeasure items := by
  induction items with
  | nil => rfl
  | cons it r ih => cases it <;> simp [itemD, serMeasureD, serMeasure, ih]

theorem size_list_map_itemD (items : List (Option Data)) :
    (list (items.map itemD)).size ≤ 2 * serMeasure items + 1 := by
  induction items with
  | nil => simp
  | cons it r ih =>
    cases it with
    | none => simp only [List.map_cons, itemD, list_cons, size_cons, size_nil, serMeasure]; omega
    | some d =>
      simp only [List.map_cons, itemD, list_cons, size_cons, size_nil, serMeasure]
      have := size_pos d
      omega

end Data

namespace Prog

open Data

/-- Close a cost bound after the run has been built, unfolding list encodings. -/
macro "cost_omega₂" : tactic =>
  `(tactic| (try simp only [Data.list_cons, Data.list_nil, Data.size_cons, Data.size_nil, encode_bool,
      Data.ofBool]) <;> omega)

/-! ## The parser -/

/-- Body of `parseProg`, on the state `cons bits stack`: at the end, stop with the top of the
stack (`nil` if empty); on a `0`, push `nil`; on a `1`, pop two entries and push their pair,
leaving a stack with fewer than two entries alone. -/
def parseBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.elim 1 .nil (.var 0)))
      (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3))))
        (.elim 5 (.cons (.cons .nil .nil) (.cons (.var 3) (.var 5)))
          (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 5) (.var 7)))
            (.cons (.cons .nil .nil)
              (.cons (.var 7) (.cons (.cons (.var 0) (.var 2)) (.var 1))))))))

/-- `parseProg` on an encoded bit string `x` computes `parse x`. -/
def parseProg : Prog := .let_ (.cons (.var 0) .nil) (.loop parseBody)

theorem parseBody_wellScoped : parseBody.WellScoped 1 := by simp [parseBody, WellScoped]

theorem parseProg_wellScoped : parseProg.WellScoped 1 := by simp [parseProg, WellScoped, parseBody]

theorem parseBody_stop (s : List Data) :
    ∃ t ≤ (list s).size + 20,
      Eval [Data.cons (encode ([] : BitStr)) (list s)] parseBody (Data.cons Data.nil (s.headD Data.nil)) t := by
  cases s with
  | nil =>
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := list ([] : List Data)) (by simp)
      (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))))⟩
    cost_omega₂
  | cons top s' =>
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := list (top :: s')) (by simp)
      (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.elim_cons (i := 1) (a := top) (b := list s') (by simp) (Eval.var_of_get (i := 0) (v := top) (by simp)))))⟩
    cost_omega₂

theorem parseBody_false (x : BitStr) (s : List Data) :
    ∃ t ≤ (encode x : Data).size + (list s).size + 20,
      Eval [Data.cons (encode (false :: x)) (list s)] parseBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode x) (list (stackStep s false)))) t := by
  simp only [stackStep_false, list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (false :: x)) (b := list s) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 1) (v := encode x) (by simp)) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 3) (v := list s) (by simp)))))))⟩
  cost_omega₂

theorem parseBody_true (x : BitStr) (s : List Data) :
    ∃ t ≤ (encode x : Data).size + (list s).size + 20,
      Eval [Data.cons (encode (true :: x)) (list s)] parseBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode x) (list (stackStep s true)))) t := by
  rcases s with _ | ⟨top, _ | ⟨top2, s''⟩⟩
  · rw [show stackStep [] true = [] by simp [stackStep]]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: x)) (b := list ([] : List Data)) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_nil (i := 5) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := encode x) (by simp)) (Eval.var_of_get (i := 5) (v := list ([] : List Data)) (by simp)))))))⟩
    cost_omega₂
  · rw [show stackStep [top] true = [top] by simp [stackStep]]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: x)) (b := list [top]) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 5) (a := top) (b := list ([] : List Data)) (by simp)
      (Eval.elim_nil (i := 1) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 5) (v := encode x) (by simp)) (Eval.var_of_get (i := 7) (v := list [top]) (by simp))))))))⟩
    cost_omega₂
  · simp only [stackStep_true_cons_cons, list_cons]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: x)) (b := list (top :: top2 :: s'')) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 5) (a := top) (b := list (top2 :: s'')) (by simp)
      (Eval.elim_cons (i := 1) (a := top2) (b := list s'') (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 7) (v := encode x) (by simp)) (Eval.cons (Eval.cons (Eval.var_of_get (i := 0) (v := top2) (by simp)) (Eval.var_of_get (i := 2) (v := top) (by simp))) (Eval.var_of_get (i := 1) (v := list s'') (by simp)))))))))⟩
    cost_omega₂

/-- The stack size grows by at most two per step. -/
theorem size_list_stackStep (s : List Data) (b : Bool) :
    (list (stackStep s b)).size ≤ (list s).size + 2 := by
  cases b
  · simp only [stackStep_false, list_cons, size_cons, size_nil]; omega
  · rcases s with _ | ⟨top, _ | ⟨top2, s''⟩⟩
    · simp [stackStep]
    · simp [stackStep]
    · simp only [stackStep_true_cons_cons, list_cons, size_cons]; omega

/-- The parsing loop computes the top of the final stack, in time `(|x| + 1) · (S + 21)` for
`S` dominating the sizes along the run. -/
theorem parseLoop_runs (x : BitStr) (s : List Data) (env : Env) (S : ℕ)
    (hS : (encode x : Data).size + (list s).size + 2 * x.length ≤ S) :
    ∃ t ≤ (x.length + 1) * (S + 21),
      Eval (Data.cons (encode x) (list s) :: env) (.loop parseBody) ((stackRun x s).headD Data.nil) t := by
  induction x generalizing s with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := parseBody_stop s
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun parseBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa using hstop⟩
    simp only [List.length_nil, encode_bitStr_nil, Data.size_nil] at hS ⊢
    omega
  | cons b x ih =>
    have hS' : (encode x : Data).size + (list (stackStep s b)).size + 2 * x.length ≤ S := by
      have := size_list_stackStep s b
      simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS
      have := size_pos (ofBool b)
      omega
    obtain ⟨t', ht', hrun'⟩ := ih (stackStep s b) hS'
    have h2 : (x.length + 1 + 1) * (S + 21) = (x.length + 1) * (S + 21) + (S + 21) := Nat.succ_mul _ _
    cases b
    · obtain ⟨t, ht, hrun⟩ := parseBody_false x s
      refine ⟨t + t' + 1, ?_, ?_⟩
      · simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢; omega
      · exact Eval.loop_step (Eval.append_of_wellScoped hrun parseBody_wellScoped env) hrun'
    · obtain ⟨t, ht, hrun⟩ := parseBody_true x s
      refine ⟨t + t' + 1, ?_, ?_⟩
      · simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢; omega
      · exact Eval.loop_step (Eval.append_of_wellScoped hrun parseBody_wellScoped env) hrun'

/-- `parseProg` reads a serialization back. -/
theorem parseProg_runs (x : BitStr) :
    ∃ t ≤ (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25),
      parseProg.Runs (encode x) (parse x) t := by
  obtain ⟨t, ht, hrun⟩ := parseLoop_runs x [] [encode x] ((encode x : Data).size + 2 * x.length + 1)
    (by simp only [list_nil, Data.size_nil]; omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [encode x]) (i := 0) (v := encode x) (by simp))
    (Eval.nil [encode x])
  refine ⟨_, ?_, Eval.let_ hpre (by simpa [parse] using hrun)⟩
  have h2 : (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25) =
      (x.length + 1) * ((encode x : Data).size + 2 * x.length + 25) +
        ((encode x : Data).size + 2 * x.length + 25) := Nat.succ_mul _ _
  have h3 : (x.length + 1) * ((encode x : Data).size + 2 * x.length + 1 + 21) ≤
      (x.length + 1) * ((encode x : Data).size + 2 * x.length + 25) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## The serializer -/

/-- Body of `serProg`, on the state `cons pending acc`: at the end, stop with `acc`; a marker
writes a `1`; the datum `nil` writes a `0`; a pair `cons a b` schedules `a`, `b` and a marker. -/
def serBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.cons .nil .nil) (.var 3))))
        (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 3) (.cons .nil (.var 5))))
          (.cons (.cons .nil .nil)
            (.cons (.cons (.cons .nil (.var 0)) (.cons (.cons .nil (.var 1)) (.cons .nil (.var 5))))
              (.var 7))))))

/-- `serProg` on `d` computes `encode d.toBitsPost`. -/
def serProg : Prog :=
  .let_ (.cons (.cons (.cons .nil (.var 0)) .nil) .nil) (.let_ (.loop serBody) revProg)

theorem serBody_wellScoped : serBody.WellScoped 1 := by simp [serBody, WellScoped]

theorem serProg_wellScoped : serProg.WellScoped 1 := by
  simp [serProg, WellScoped, serBody, revProg, revOntoProg, revOntoBody]

theorem serBody_stop (acc : BitStr) :
    ∃ t ≤ (encode acc : Data).size + 20,
      Eval [Data.cons (list ([] : List Data)) (encode acc)] serBody (Data.cons Data.nil (encode acc)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list ([] : List Data)) (b := encode acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := encode acc) (by simp))))⟩
  cost_omega₂

theorem serBody_marker (rest : List Data) (acc : BitStr) :
    ∃ t ≤ (list rest).size + (encode acc : Data).size + 20,
      Eval [Data.cons (list (Data.nil :: rest)) (encode acc)] serBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (list rest) (encode (true :: acc)))) t := by
  simp only [encode_bitStr_cons, ofBool, list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list (Data.nil :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := list rest) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 1) (v := list rest) (by simp)) (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.var_of_get (i := 3) (v := encode acc) (by simp)))))))⟩
  cost_omega₂

theorem serBody_datanil (rest : List Data) (acc : BitStr) :
    ∃ t ≤ (list rest).size + (encode acc : Data).size + 20,
      Eval [Data.cons (list (Data.cons Data.nil Data.nil :: rest)) (encode acc)] serBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (list rest) (encode (false :: acc)))) t := by
  simp only [encode_bitStr_cons, ofBool, list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list (Data.cons Data.nil Data.nil :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := list rest) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
    (Eval.elim_nil (i := 1) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := list rest) (by simp)) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := encode acc) (by simp))))))))⟩
  cost_omega₂

theorem serBody_datacons (a b : Data) (rest : List Data) (acc : BitStr) :
    ∃ t ≤ a.size + b.size + (list rest).size + (encode acc : Data).size + 30,
      Eval [Data.cons (list (Data.cons Data.nil (Data.cons a b) :: rest)) (encode acc)] serBody
        (Data.cons (Data.cons Data.nil Data.nil)
          (Data.cons (list (Data.cons Data.nil a :: Data.cons Data.nil b :: Data.nil :: rest))
            (encode acc))) t := by
  simp only [list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := list (Data.cons Data.nil (Data.cons a b) :: rest)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.cons Data.nil (Data.cons a b)) (b := list rest) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.cons a b) (by simp)
    (Eval.elim_cons (i := 1) (a := a) (b := b) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := a) (by simp))) (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := b) (by simp))) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := list rest) (by simp))))) (Eval.var_of_get (i := 7) (v := encode acc) (by simp)))))))⟩
  cost_omega₂

/-- The serializer's loop, by the invariant "`acc.reverse ++ serItems items` is the target",
with the measure `serMeasure` and the size bound `S₀`. -/
theorem serLoop_runs (d : Data) (env : Env) :
    ∃ t ≤ (3 * d.size + 2) * (16 * d.size + 42),
      Eval (Data.cons (list [itemD (some d)]) (encode ([] : BitStr)) :: env) (.loop serBody)
        (encode d.toBitsPost.reverse) t := by
  set S₀ := d.size + 6 + 5 * (3 * d.size + 1) with hS₀
  -- the invariant
  let I : Data → Prop := fun st => ∃ (items : List (Option Data)) (acc : BitStr),
    st = Data.cons (list (items.map itemD)) (encode acc) ∧
    acc.reverse ++ serItems items = d.toBitsPost ∧ st.size + 5 * serMeasure items ≤ S₀
  let μ : Data → ℕ := fun st => serMeasureD st.left
  have key := Eval.loop_of_invariant serBody_wellScoped env I μ
    (fun r => r = encode d.toBitsPost.reverse) (S₀ + 30) ?_
    (Data.cons (list [itemD (some d)]) (encode ([] : BitStr))) ?_
  · obtain ⟨r, t, ht, hr, hrun⟩ := key
    subst hr
    refine ⟨t, ?_, hrun⟩
    refine ht.trans ?_
    simp only [μ, Data.left_cons, list_cons, list_nil, itemD, serMeasureD, Data.size_nil, hS₀]
    nlinarith
  · -- the body
    rintro st ⟨items, acc, rfl, hacc, hsize⟩
    rcases items with _ | ⟨it, rest⟩
    · -- done
      left
      obtain ⟨t, ht, hrun⟩ := serBody_stop acc
      refine ⟨encode acc, t, ?_, hrun, ?_⟩
      · simp only [List.map_nil, list_nil, Data.size_cons, Data.size_nil] at hsize ⊢; omega
      · simp only [serItems, List.append_nil] at hacc
        rw [← hacc, List.reverse_reverse]
    · right
      rcases it with _ | d'
      · -- marker
        obtain ⟨t, ht, hrun⟩ := serBody_marker (rest.map itemD) acc
        refine ⟨_, _, _, t, ?_, hrun, ⟨rest, true :: acc, rfl, ?_, ?_⟩, ?_⟩
        · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil] at hsize; omega
        · simpa [serItems, List.reverse_cons] using hacc
        · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil, serMeasure,
            encode_bitStr_cons, ofBool] at hsize ⊢
          omega
        · simp [μ, List.map_cons, itemD, serMeasureD]
      · rcases d' with _ | ⟨a, b⟩
        · -- the datum `nil`
          obtain ⟨t, ht, hrun⟩ := serBody_datanil (rest.map itemD) acc
          refine ⟨_, _, _, t, ?_, by simpa [itemD] using hrun, ⟨rest, false :: acc, rfl, ?_, ?_⟩, ?_⟩
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil] at hsize; omega
          · simpa [serItems, toBitsPost, List.reverse_cons] using hacc
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil, serMeasure,
              encode_bitStr_cons, ofBool] at hsize ⊢
            omega
          · simp [μ, List.map_cons, itemD, serMeasureD]
        · -- a pair
          obtain ⟨t, ht, hrun⟩ := serBody_datacons a b (rest.map itemD) acc
          refine ⟨_, _, _, t, ?_, by simpa [itemD] using hrun,
            ⟨some a :: some b :: none :: rest, acc, by simp [itemD], ?_, ?_⟩, ?_⟩
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil] at hsize; omega
          · simpa [serItems, toBitsPost, List.append_assoc] using hacc
          · simp only [List.map_cons, itemD, list_cons, Data.size_cons, Data.size_nil, serMeasure]
              at hsize ⊢
            omega
          · simp [μ, List.map_cons, itemD, serMeasureD]; omega
  · -- the initial state
    refine ⟨[some d], [], rfl, by simp [serItems], ?_⟩
    simp only [List.map_cons, List.map_nil, itemD, list_cons, list_nil, Data.size_cons, Data.size_nil,
      serMeasure, encode_bitStr_nil, hS₀]
    omega

/-- `serProg` writes the postorder serialization. -/
theorem serProg_runs (d : Data) :
    ∃ t ≤ (3 * d.size + 2) * (16 * d.size + 42) + (d.size + 2) * (5 * d.size + 30),
      serProg.Runs d (encode d.toBitsPost) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := serLoop_runs d [d]
  have hpre := Eval.cons (Eval.cons (Eval.cons (Eval.nil [d])
    (Eval.var_of_get (env := [d]) (i := 0) (v := d) (by simp))) (Eval.nil [d])) (Eval.nil [d])
  obtain ⟨t₂, ht₂, h₂⟩ := revProg_runs (d.toBitsPost.reverse.map ofBool)
  have h₂' : Eval [encode d.toBitsPost.reverse,
      Data.cons (Data.cons (Data.cons Data.nil d) Data.nil) Data.nil, d] revProg
      (encode d.toBitsPost) t₂ := by
    have := Eval.append_of_wellScoped h₂ revProg_wellScoped
      [Data.cons (Data.cons (Data.cons Data.nil d) Data.nil) Data.nil, d]
    rw [encode_bitStr_eq_list, encode_bitStr_eq_list]
    simpa [List.map_reverse] using this
  have h₁' : Eval [Data.cons (Data.cons (Data.cons Data.nil d) Data.nil) Data.nil, d] (.loop serBody)
      (encode d.toBitsPost.reverse) t₁ := by
    simpa [itemD, encode_bitStr_nil] using h₁
  refine ⟨_, ?_, Eval.let_ hpre (Eval.let_ h₁' h₂')⟩
  have hlen : d.toBitsPost.reverse.length = d.size := by simp
  have hsz : (encode d.toBitsPost.reverse : Data).size ≤ 4 * d.size + 1 := by
    have := esize_bitStr_le d.toBitsPost.reverse
    rw [hlen] at this; exact this
  have hB : t₂ ≤ (d.size + 2) * (4 * d.size + 14) := by
    refine ht₂.trans ?_
    rw [← encode_bitStr_eq_list, List.length_map, hlen]
    exact Nat.mul_le_mul_left _ (by omega)
  nlinarith
end Prog

end MIPRE.Cost
