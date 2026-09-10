/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Loops

/-!
# The closure library, part III: unary arithmetic and tree size

Programs on unary numerals (`Data.ofNat`) built from the length loop of `Cost.Loops`:
addition (`addProg`), the bit string of a power of two (`expBitsProg`), and the size of a
tree in unary (`sizeProg`, a stack-driven traversal proved with `Eval.loop_of_invariant`).
These are the ingredients of the threshold function `r e = 2 ^ q(esize e)` of the recursive
compression argument (`planning/compression-track.md`, K3 step 4); multiplication and powers
follow in `Cost.Numeric`.
-/

namespace MIPRE.Cost

namespace Data

/-- Sum of the sizes of the elements of a list. -/
def sumSize : List Data → ℕ
  | [] => 0
  | a :: l => a.size + sumSize l

@[simp] theorem sumSize_nil : sumSize [] = 0 := rfl

@[simp] theorem sumSize_cons (a : Data) (l : List Data) :
    sumSize (a :: l) = a.size + sumSize l := rfl

theorem length_le_sumSize (l : List Data) : l.length ≤ sumSize l := by
  induction l with
  | nil => simp
  | cons a l ih => have := size_pos a; simp only [List.length_cons, sumSize_cons]; omega

theorem size_list_eq (l : List Data) : (list l).size = sumSize l + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [size_list_cons, sumSize_cons, List.length_cons, ih]; omega

/-- The sum of the sizes of the elements of a `cons`-chain, as a function on data (the
measure of the tree-size loop). -/
def nodeSum : Data → ℕ
  | nil => 0
  | cons t rest => t.size + nodeSum rest

theorem nodeSum_list (l : List Data) : nodeSum (list l) = sumSize l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [nodeSum, ih]

/-- The measure of the tree-size loop: the node sum of the stack component. -/
def stackMeasure : Data → ℕ
  | cons st _ => nodeSum st
  | nil => 0

end Data

namespace Prog

/-! ## Addition of unary numerals -/

/-- `addProg` on `cons (ofNat a) (ofNat b)` computes `ofNat (a + b)`: it is the length
loop with the second numeral as accumulator. -/
def addProg : Prog := .loop lenBody

theorem addProg_wellScoped : addProg.WellScoped 1 := ⟨Nat.zero_lt_one, lenBody_wellScoped⟩

theorem addProg_runs (a b : ℕ) (env : Env) :
    ∃ t ≤ (a + 1) * (4 * a + 2 * b + 15),
      Eval (.cons (.ofNat a) (.ofNat b) :: env) addProg (.ofNat (a + b)) t := by
  obtain ⟨t, ht, hrun⟩ := lenLoop_runs (List.replicate a .nil) (List.replicate b .nil) env
    (4 * a + 2 * b + 2) (by
      rw [← Data.ofNat_eq_list_replicate, ← Data.ofNat_eq_list_replicate, Data.size_ofNat,
        Data.size_ofNat, List.length_replicate]
      omega)
  refine ⟨t, by simpa [List.length_replicate] using ht, ?_⟩
  rw [Data.ofNat_eq_list_replicate, Data.ofNat_eq_list_replicate, Data.ofNat_eq_list_replicate,
    List.replicate_add]
  simpa [addProg, List.length_replicate] using hrun

/-! ## Powers of two, as bit strings -/

theorem _root_.Nat.bits_two_pow (j : ℕ) : (2 ^ j).bits = List.replicate j false ++ [true] := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h : 2 ^ (j + 1) = Nat.bit false (2 ^ j) := by
      rw [Nat.bit_val]; simp [Nat.pow_succ, Nat.mul_comm]
    rw [h, Nat.bits_append_bit _ _ (fun h0 => absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos j))),
      ih, List.replicate_succ, List.cons_append]

/-- `expBitsProg` on the unary numeral `ofNat j` computes `encode (2 ^ j)`, the bit string
`false^j ++ [true]`. -/
def expBitsProg : Prog := .let_ (.cons (.var 0) (.const (.cons (.cons .nil .nil) .nil))) (.loop lenBody)

theorem expBitsProg_wellScoped : expBitsProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩, ⟨Nat.zero_lt_succ 1, lenBody_wellScoped.mono (by omega) _⟩⟩

theorem encode_two_pow (j : ℕ) :
    encode (2 ^ j) = Data.list (List.replicate j .nil ++ [.cons .nil .nil]) := by
  show Data.ofList Data.ofBool (2 ^ j).bits = _
  rw [Nat.bits_two_pow, Data.ofList_eq_list, List.map_append, List.map_replicate]
  rfl

theorem expBitsProg_runs (j : ℕ) :
    ∃ t ≤ (j + 1 + 1) * (4 * j + 20), expBitsProg.Runs (.ofNat j) (encode (2 ^ j)) t := by
  obtain ⟨t, ht, hrun⟩ := lenLoop_runs (List.replicate j .nil) [.cons .nil .nil]
    [Data.ofNat j] (4 * j + 7) (by
      rw [← Data.ofNat_eq_list_replicate, Data.size_ofNat, List.length_replicate]
      simp only [Data.size_list_cons, Data.list_nil, Data.size_cons, Data.size_nil]
      omega)
  refine ⟨2 * j + 1 + 1 + 5 + 1 + t + 1, ?_, ?_⟩
  · simp only [List.length_replicate] at ht
    have e1 : 4 * j + 7 + 13 = 4 * j + 20 := by omega
    rw [e1] at ht
    have h2 : (j + 1 + 1) * (4 * j + 20) = (j + 1) * (4 * j + 20) + (4 * j + 20) :=
      Nat.succ_mul _ _
    omega
  · have hpre := Eval.cons (Eval.var_of_get (env := [Data.ofNat j]) (i := 0) (v := .ofNat j)
      (by simp)) (Eval.const [Data.ofNat j] (.cons (.cons .nil .nil) .nil))
    have hpre' : Eval [Data.ofNat j] (.cons (.var 0) (.const (.cons (.cons .nil .nil) .nil)))
        (.cons (.ofNat j) (.cons (.cons .nil .nil) .nil)) (2 * j + 1 + 1 + 5 + 1) := by
      simpa using hpre
    have hrun' : Eval (Data.cons (.ofNat j) (.cons (.cons .nil .nil) .nil) :: [Data.ofNat j])
        (.loop lenBody) (encode (2 ^ j)) t := by
      rw [encode_two_pow]
      have h := hrun
      rw [← Data.ofNat_eq_list_replicate] at h
      simpa [List.length_replicate] using h
    exact Eval.let_ hpre' hrun'

/-! ## Size of a tree, in unary -/

/-- Body of `sizeProg`: the state is `cons stack count` with `stack` a list of pending
subtrees and `count` a unary numeral. Pop a subtree: if it is `nil`, count it; if it is
`cons a b`, count it and push `a` and `b`. Stop with `count` when the stack is empty. -/
def sizeBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.elim 0
      (.cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3))))
      (.cons (.cons .nil .nil)
        (.cons (.cons (.var 0) (.cons (.var 1) (.var 3))) (.cons .nil (.var 5))))))

theorem sizeBody_wellScoped : sizeBody.WellScoped 1 := by simp [sizeBody, WellScoped]

theorem sizeBody_stop (k : ℕ) :
    Eval [.cons (.list []) (.ofNat k)] sizeBody (.cons .nil (.ofNat k)) (2 * k + 6) := by
  have e := Eval.elim_cons (env := [Data.cons (.list []) (.ofNat k)]) (i := 0)
    (n := .nil) (a := .list []) (b := .ofNat k) (by simp)
    (Eval.elim_nil (i := 0)
      (c := .elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3))))
        (.cons (.cons .nil .nil)
          (.cons (.cons (.var 0) (.cons (.var 1) (.var 3))) (.cons .nil (.var 5)))))
      (by simp)
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .ofNat k) (by simp))))
  exact e.cast_cost (by simp only [Data.size_ofNat]; omega)

theorem sizeBody_step_nil (rest : List Data) (k : ℕ) :
    Eval [.cons (.list (.nil :: rest)) (.ofNat k)] sizeBody
      (.cons (.cons .nil .nil) (.cons (.list rest) (.ofNat (k + 1))))
      ((Data.list rest).size + 2 * k + 13) := by
  have e := Eval.elim_cons (env := [Data.cons (.list (.nil :: rest)) (.ofNat k)]) (i := 0)
    (n := .nil) (a := .list (.nil :: rest)) (b := .ofNat k) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := .nil) (b := .list rest) (by simp)
      (Eval.elim_nil (i := 0)
        (c := .cons (.cons .nil .nil)
          (.cons (.cons (.var 0) (.cons (.var 1) (.var 3))) (.cons .nil (.var 5))))
        (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 1) (v := .list rest) (by simp))
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 3) (v := .ofNat k) (by simp)))))))
  exact e.cast_cost (by simp only [Data.size_ofNat]; omega)

theorem sizeBody_step_cons (a b : Data) (rest : List Data) (k : ℕ) :
    Eval [.cons (.list (.cons a b :: rest)) (.ofNat k)] sizeBody
      (.cons (.cons .nil .nil) (.cons (.list (a :: b :: rest)) (.ofNat (k + 1))))
      (a.size + b.size + (Data.list rest).size + 2 * k + 17) := by
  have e := Eval.elim_cons (env := [Data.cons (.list (.cons a b :: rest)) (.ofNat k)]) (i := 0)
    (n := .nil) (a := .list (.cons a b :: rest)) (b := .ofNat k) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := .cons a b) (b := .list rest)
      (by simp)
      (Eval.elim_cons (i := 0)
        (n := .cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3))))
        (a := a) (b := b) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons
            (Eval.cons (Eval.var_of_get (i := 0) (v := a) (by simp))
              (Eval.cons (Eval.var_of_get (i := 1) (v := b) (by simp))
                (Eval.var_of_get (i := 3) (v := .list rest) (by simp))))
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := .ofNat k) (by simp)))))))
  exact e.cast_cost (by simp only [Data.size_ofNat]; omega)

/-- The invariant of the tree-size loop for a tree of size `N`: the state is
`cons stack count` with `count + Σ size (stack) = N`. -/
def sizeInv (N : ℕ) (s : Data) : Prop :=
  ∃ (st : List Data) (k : ℕ), s = .cons (.list st) (.ofNat k) ∧ k + Data.sumSize st = N

theorem sizeLoop_runs (N : ℕ) (env : Env) (s : Data) (hs : sizeInv N s) :
    ∃ t ≤ (Data.stackMeasure s + 1) * (5 * N + 20),
      Eval (s :: env) (.loop sizeBody) (.ofNat N) t := by
  have key := Eval.loop_of_invariant sizeBody_wellScoped env (sizeInv N) Data.stackMeasure
    (fun r => r = .ofNat N) (5 * N + 19) ?_ s hs
  · obtain ⟨r, t, ht, rfl, hrun⟩ := key
    exact ⟨t, ht, hrun⟩
  · rintro s ⟨st, k, rfl, hk⟩
    rcases st with _ | ⟨t, rest⟩
    · -- empty stack: stop with the count
      left
      refine ⟨.ofNat k, 2 * k + 6, ?_, sizeBody_stop k, ?_⟩
      · simp only [Data.sumSize_nil] at hk; omega
      · simp only [Data.sumSize_nil, Nat.add_zero] at hk; rw [hk]
    · right
      have hk' := hk
      simp only [Data.sumSize_cons] at hk'
      have hsz : (Data.list rest).size = Data.sumSize rest + rest.length + 1 := Data.size_list_eq rest
      have hlen := Data.length_le_sumSize rest
      rcases t with _ | ⟨a, b⟩
      · refine ⟨.nil, .nil, _, _, ?_, sizeBody_step_nil rest k, ⟨rest, k + 1, rfl, ?_⟩, ?_⟩
        · simp only [Data.size_nil] at hk'; omega
        · simp only [Data.size_nil] at hk'; omega
        · simp only [Data.stackMeasure, Data.nodeSum_list, Data.sumSize_cons, Data.size_nil]
          omega
      · refine ⟨.nil, .nil, _, _, ?_, sizeBody_step_cons a b rest k, ⟨a :: b :: rest, k + 1, rfl, ?_⟩,
          ?_⟩
        · simp only [Data.size_cons] at hk'; omega
        · simp only [Data.size_cons, Data.sumSize_cons] at hk' ⊢; omega
        · simp only [Data.stackMeasure, Data.nodeSum_list, Data.sumSize_cons, Data.size_cons]
          omega

/-- Size of a tree in unary: `sizeProg` on `d` computes `ofNat d.size`. -/
def sizeProg : Prog := .let_ (.cons (.cons (.var 0) .nil) .nil) (.loop sizeBody)

theorem sizeProg_wellScoped : sizeProg.WellScoped 1 :=
  ⟨⟨⟨Nat.zero_lt_one, trivial⟩, trivial⟩, ⟨Nat.zero_lt_succ 1, sizeBody_wellScoped.mono (by omega) _⟩⟩

theorem sizeProg_runs (d : Data) :
    ∃ t ≤ (d.size + 1) * (5 * d.size + 20) + d.size + 6,
      sizeProg.Runs d (.ofNat d.size) t := by
  obtain ⟨t, ht, hrun⟩ := sizeLoop_runs d.size [d] (.cons (.list [d]) (.ofNat 0))
    ⟨[d], 0, rfl, by simp⟩
  refine ⟨d.size + 1 + 1 + 1 + 1 + 1 + t + 1, ?_, ?_⟩
  · simp only [Data.stackMeasure, Data.nodeSum_list, Data.sumSize_cons, Data.sumSize_nil,
      Nat.add_zero] at ht
    omega
  · have hpre := Eval.cons (Eval.cons (Eval.var_of_get (env := [d]) (i := 0) (v := d) (by simp))
      (Eval.nil [d])) (Eval.nil [d])
    have hrun' : Eval (Data.cons (.cons d .nil) .nil :: [d]) (.loop sizeBody) (.ofNat d.size) t :=
      hrun
    exact Eval.let_ hpre hrun'

end Prog

end MIPRE.Cost
