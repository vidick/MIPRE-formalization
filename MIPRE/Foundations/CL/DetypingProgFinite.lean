/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.TreeBits
import MIPRE.Foundations.SAT.ArrayProg

/-! # Total finite query programs

A fixed finite data table is an actual closed ambient program, total on every
tree and polynomial in the size of that tree. The constants depend on the table;
this lemma makes no uniform polynomial claim about its construction.
-/

namespace MIPRE.Cost.PolyTimeFun

open Polynomial

private theorem bits_prefix_unique (a b : Data) (xs ys : BitStr)
    (h : a.toBits ++ xs = b.toBits ++ ys) : a = b ∧ xs = ys := by
  induction a generalizing b xs ys with
  | nil =>
    cases b with
    | nil => simpa [Data.toBits] using h
    | cons b c => simp [Data.toBits] at h
  | cons a c iha ihc =>
    cases b with
    | nil => simp [Data.toBits] at h
    | cons b d =>
      have h' : a.toBits ++ (c.toBits ++ xs) = b.toBits ++ (d.toBits ++ ys) := by
        simpa [Data.toBits, List.append_assoc] using h
      obtain ⟨hab, hcd⟩ := iha b _ _ h'
      obtain ⟨hcd', hxy⟩ := ihc d xs ys hcd
      exact ⟨by rw [hab, hcd'], hxy⟩

/-- Equality of arbitrary trees, through their injective serialization. -/
noncomputable def treeEq : PolyTimeFun (Data × Data) Bool :=
  congr (ap₂ SAT.ArrayProg.eqBits (toBits.comp fst) (toBits.comp snd))
    (fun p => decide (p.1 = p.2)) (by
      intro p
      simp only [ap₂_apply, comp_apply, toBits_apply, fst_apply, snd_apply,
        SAT.ArrayProg.eqBits_apply]
      congr 1
      apply propext
      constructor
      · intro h
        exact (bits_prefix_unique p.1 p.2 [] [] (by simpa using h)).1
      · exact congrArg Data.toBits)

@[simp] theorem treeEq_apply (p : Data × Data) : treeEq p = decide (p.1 = p.2) := rfl

/-- A tree's right child, with a fixed default for a leaf. -/
noncomputable def treeTail : PolyTimeFun Data Data where
  toFun d := match d with | .nil => .nil | .cons _ b => b
  code := Prog.sndProg
  closed := Prog.sndProg_wellScoped
  timeBound := X + C 2
  computes d := by
    cases d with
    | nil => exact ⟨2, by simp, Eval.elim_nil (by simp) (Eval.nil _)⟩
    | cons a b =>
      exact ⟨b.size + 2, by simp only [esize_data, Data.size_cons,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega,
        Prog.sndProg_runs a b⟩

@[simp] theorem treeTail_cons (a b : Data) : treeTail (.cons a b) = b := rfl

/-- A tree's left child, with a fixed default for a leaf. -/
noncomputable def treeHead : PolyTimeFun Data Data where
  toFun d := match d with | .nil => .nil | .cons a _ => a
  code := Prog.fstProg
  closed := Prog.fstProg_wellScoped
  timeBound := X + C 2
  computes d := by
    cases d with
    | nil => exact ⟨2, by simp, Eval.elim_nil (by simp) (Eval.nil _)⟩
    | cons a b =>
      exact ⟨a.size + 2, by simp only [esize_data, Data.size_cons,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega,
        Prog.fstProg_runs a b⟩

@[simp] theorem treeHead_cons (a b : Data) : treeHead (.cons a b) = a := rfl

/-- Pair two raw trees. -/
noncomputable def treePair : PolyTimeFun (Data × Data) Data :=
  ofEncodeEq (fun p => Data.cons p.1 p.2) (fun _ => rfl)

@[simp] theorem treePair_apply (p : Data × Data) : treePair p = .cons p.1 p.2 := rfl

/-- First matching key, or `nil`. The function assigned to keys need not itself
be computable: only its finitely many values become constants in the program. -/
noncomputable def finiteTable (f : Data → Data) : List Data → PolyTimeFun Data Data
  | [] => const .nil
  | a :: as => ite (ap₂ treeEq (id Data) (const a)) (const (f a)) (finiteTable f as)

theorem finiteTable_apply_of_mem (f : Data → Data) (xs : List Data) (d : Data)
    (hd : d ∈ xs) : finiteTable f xs d = f d := by
  induction xs with
  | nil => simp at hd
  | cons a as ih =>
    simp only [finiteTable, ite_apply, ap₂_apply, treeEq_apply, id_apply, const_apply]
    by_cases h : d = a
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (List.mem_cons.mp hd |>.resolve_left h)

/-- Finite tables return a value on every raw input, including malformed queries. -/
theorem finiteTable_halts (f : Data → Data) (xs : List Data) (d : Data) :
    Halts (finiteTable f xs).code d := by
  obtain ⟨t, _, hr⟩ := (finiteTable f xs).computes d
  exact ⟨_, t, hr⟩

/-- Every fixed function on a finite, faithfully encoded domain has a concrete
polynomial-time table program. No uniform bound in the domain's cardinality is asserted. -/
noncomputable def finiteFunction {α β : Type*} [Fintype α]
    [SizedEncoding α] [SizedEncoding β] (f : α → β) : PolyTimeFun α β := by
  classical
  let xs := (Finset.univ.image (encode : α → Data)).toList
  let answer := fun d => ((decode d : Option α).map (fun a => encode (f a))).getD .nil
  let table := finiteTable answer xs
  exact {
    toFun := f
    code := table.code
    closed := table.closed
    timeBound := table.timeBound
    computes := fun a => by
      obtain ⟨t, ht, hr⟩ := table.computes (encode a)
      have ha : encode a ∈ xs := by simp [xs]
      have he : table (encode a) = encode (f a) := by
        rw [finiteTable_apply_of_mem answer xs _ ha]
        simp [answer, SizedEncoding.decode_encode]
      rw [he] at hr
      exact ⟨t, ht, hr⟩ }

@[simp] theorem finiteFunction_apply {α β : Type*} [Fintype α]
    [SizedEncoding α] [SizedEncoding β] (f : α → β) (a : α) : finiteFunction f a = f a := rfl

end MIPRE.Cost.PolyTimeFun
