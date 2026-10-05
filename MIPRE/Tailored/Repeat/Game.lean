/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.ZPC
public import Mathlib.Algebra.BigOperators.Fin
public import MIPRE.Tactics

@[expose] public section

/-!
# The `k`-fold tailored product of a tailored game

Paper II, §6.3 (II:11377–11396), in its direct form: the `k`-fold product of a tailored game
`G` is the tailored game `G.repeat k` on `k`-tuples of questions, with

* the product distribution `∏ᵢ μ(xᵢ, yᵢ)`;
* the variables at `x⃗` the disjoint union of the variables at the coordinates, the readable
  ones first, as a tailored answer must have them: the readable variables of `x₁, …, x_k`, in
  this order, then their linear variables (`varEquiv`), so that
  `lenR x⃗ = ∑ᵢ lenR xᵢ` and `lenL x⃗ = ∑ᵢ lenL xᵢ`;
* the constraints at `(x⃗, y⃗)` those of every coordinate, each written over all the variables
  by padding it with zeros (`padCons`): the paper's "zero-padded to the global length and
  concatenated" (II:11380). A constraint of the wrong length becomes the rejecting constraint,
  as the canonical decider rejects it in the coordinate.

`repeat_accepts_iff` is the acceptance law: the canonical decider accepts a pair of answers
exactly when they have the right lengths and every coordinate, read off by `coord`, is
accepted. It rests on `satisfies_padCons_iff`, the padded constraint being satisfied by the
whole answers exactly when the constraint is satisfied by the coordinate's.
-/

namespace MIPRE.Tailored

open Finset

variable {X : Type*} [Fintype X]

namespace TailoredGame

variable (G : TailoredGame X) {k : ℕ}

/-! ## The variables of a tuple of questions -/

/-- The readable variables of the coordinates, in order. -/
abbrev lenRSum (x : Fin k → X) : ℕ := ∑ i, G.lenR (x i)

/-- The linear variables of the coordinates, in order. -/
abbrev lenLSum (x : Fin k → X) : ℕ := ∑ i, G.lenL (x i)

/-- **The variables at `x⃗`**: the readable variables of the coordinates, then their linear
variables, matched with the pairs `(i, v)` of a coordinate and a variable `v` of the question
`xᵢ` (readable `v < lenR xᵢ` first, as in `G`). -/
def varEquiv (x : Fin k → X) :
    Fin (G.lenRSum x + G.lenLSum x) ≃ (i : Fin k) × Fin (G.len (x i)) :=
  finSumFinEquiv.symm.trans <|
    (Equiv.sumCongr finSigmaFinEquiv.symm finSigmaFinEquiv.symm).trans <|
      (Equiv.sigmaSumDistrib (fun i => Fin (G.lenR (x i))) fun i => Fin (G.lenL (x i))).symm.trans <|
        Equiv.sigmaCongrRight fun _ => finSumFinEquiv

/-- The readable variable `v` of the coordinate `i` is the readable variable
`∑_{j < i} lenR xⱼ + v` of the tuple. -/
theorem varEquiv_symm_castAdd (x : Fin k → X) (i : Fin k) (v : Fin (G.lenR (x i))) :
    (G.varEquiv x).symm ⟨i, Fin.castAdd (G.lenL (x i)) v⟩ =
      Fin.castAdd (G.lenLSum x) (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, v⟩) := by
  rw [Equiv.symm_apply_eq]
  simp [varEquiv, Equiv.sigmaSumDistrib, Equiv.sigmaCongrRight]
  rfl

/-- The linear variable `w` of the coordinate `i` is the linear variable
`∑_{j < i} lenL xⱼ + w` of the tuple, after all the readable ones. -/
theorem varEquiv_symm_natAdd (x : Fin k → X) (i : Fin k) (w : Fin (G.lenL (x i))) :
    (G.varEquiv x).symm ⟨i, Fin.natAdd (G.lenR (x i)) w⟩ =
      Fin.natAdd (G.lenRSum x) (finSigmaFinEquiv (n := fun j => G.lenL (x j)) ⟨i, w⟩) := by
  rw [Equiv.symm_apply_eq]
  simp [varEquiv, Equiv.sigmaSumDistrib, Equiv.sigmaCongrRight]
  rfl

/-- **Readable variables correspond**: a variable of the tuple is readable exactly when it is a
readable variable of its coordinate. -/
theorem lt_lenRSum_iff (x : Fin k → X) (g : Fin (G.lenRSum x + G.lenLSum x)) :
    g.val < G.lenRSum x ↔ ((G.varEquiv x) g).2.val < G.lenR (x ((G.varEquiv x) g).1) := by
  obtain ⟨⟨i, v⟩, rfl⟩ := (G.varEquiv x).symm.surjective g
  rw [Equiv.apply_symm_apply]
  refine Fin.addCases (fun r => ?_) (fun w => ?_) v
  · rw [varEquiv_symm_castAdd, Fin.val_castAdd]
    exact iff_of_true (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, r⟩).isLt (by simp)
  · rw [varEquiv_symm_natAdd, Fin.val_natAdd]
    exact iff_of_false (by omega) (by simp)

/-! ## Coordinates of answers -/

/-- The answer to the coordinate `i` read off an answer `a` to the tuple `x⃗`. -/
def coord (x : Fin k → X) (a : Cost.BitStr) (i : Fin k) : Cost.BitStr :=
  List.ofFn fun v : Fin (G.len (x i)) => a.getD ((G.varEquiv x).symm ⟨i, v⟩) false

@[simp] theorem length_coord (x : Fin k → X) (a : Cost.BitStr) (i : Fin k) :
    (G.coord x a i).length = G.len (x i) := by simp [coord]

/-- The readable answer to the coordinate `i` read off the readable part `a^R` of an answer:
its `i`-th block, of length `lenR xᵢ`. -/
def coordR (x : Fin k → X) (aR : Cost.BitStr) (i : Fin k) : Cost.BitStr :=
  List.ofFn fun v : Fin (G.lenR (x i)) =>
    aR.getD (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, v⟩) false

/-- The readable part of a coordinate of an answer is the coordinate of its readable part. -/
theorem coordR_take (x : Fin k → X) (a : Cost.BitStr) (i : Fin k) :
    G.coordR x (a.take (G.lenRSum x)) i = (G.coord x a i).take (G.lenR (x i)) := by
  apply List.ext_getElem
  · simp [coordR, coord, len]
  intro v h1 h2
  simp only [coordR, List.getElem_ofFn, coord, List.getElem_take]
  have hv : v < G.lenR (x i) := by simpa [coordR] using h1
  have hlt : (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, ⟨v, hv⟩⟩).val < G.lenRSum x :=
    (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, ⟨v, hv⟩⟩).isLt
  have hcast : (G.varEquiv x).symm ⟨i, ⟨v, by unfold len; omega⟩⟩ =
      Fin.castAdd (G.lenLSum x) (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, ⟨v, hv⟩⟩) :=
    G.varEquiv_symm_castAdd x i ⟨v, hv⟩
  rw [hcast, Fin.val_castAdd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hlt]

/-! ## Padding a constraint of a coordinate -/

/-- **A constraint of the coordinate `i`, written over all the variables** (II:11380): its
coefficient at a variable of `x⃗` is its coefficient at that variable of `xᵢ` when the variable
belongs to the coordinate `i`, and `0` otherwise; likewise for `y⃗`; the affine coefficient is
kept. A constraint of the wrong length becomes the rejecting constraint. -/
def padCons (x y : Fin k → X) (i : Fin k) (c : Cost.BitStr) : Cost.BitStr :=
  if c.length = G.len (x i) + G.len (y i) + 1 then
    List.ofFn (fun g : Fin (G.lenRSum x + G.lenLSum x) =>
        if ((G.varEquiv x) g).1 = i then c.getD ((G.varEquiv x) g).2.val false else false) ++
      List.ofFn (fun g : Fin (G.lenRSum y + G.lenLSum y) =>
        if ((G.varEquiv y) g).1 = i then
          c.getD (G.len (x i) + ((G.varEquiv y) g).2.val) false else false) ++
      [c.getD (G.len (x i) + G.len (y i)) false]
  else rejectConstraint (G.lenRSum x + G.lenLSum x + (G.lenRSum y + G.lenLSum y))

/-! ## The product game -/

/-- **The `k`-fold tailored product** (II:11377): product distribution, the variables of the
coordinates (readable first), and every coordinate's constraints padded to all the
variables. -/
def «repeat» (k : ℕ) : TailoredGame (Fin k → X) where
  μ x y := ∏ i, G.μ (x i) (y i)
  μ_nonneg x y := Finset.prod_nonneg fun i _ => G.μ_nonneg (x i) (y i)
  μ_sum_one := by
    classical
    calc (∑ x : Fin k → X, ∑ y : Fin k → X, ∏ i, G.μ (x i) (y i))
        = ∑ x : Fin k → X, ∏ i, ∑ y, G.μ (x i) y :=
          Finset.sum_congr rfl fun x _ => (Fintype.prod_sum fun i y => G.μ (x i) y).symm
      _ = ∏ _i : Fin k, ∑ x, ∑ y, G.μ x y :=
          (Fintype.prod_sum fun _ x => ∑ y, G.μ x y).symm
      _ = 1 := by simp [G.μ_sum_one]
  lenR x := G.lenRSum x
  lenL x := G.lenLSum x
  cons x y aR bR := (List.finRange k).flatMap fun i =>
    (G.cons (x i) (y i) (G.coordR x aR i) (G.coordR y bR i)).map (G.padCons x y i)

@[simp] theorem repeat_μ (x y : Fin k → X) :
    (G.repeat k).μ x y = ∏ i, G.μ (x i) (y i) := rfl

@[simp] theorem repeat_lenR (x : Fin k → X) : (G.repeat k).lenR x = G.lenRSum x := rfl

@[simp] theorem repeat_lenL (x : Fin k → X) : (G.repeat k).lenL x = G.lenLSum x := rfl

theorem repeat_len (x : Fin k → X) : (G.repeat k).len x = G.lenRSum x + G.lenLSum x := rfl

/-! ## Linear constraints after padding -/

/-- `⟨α, a⟩` is the parity of the number of common ones. -/
theorem dotBit_eq_decide_odd {n : ℕ} (α a : Fin n → Bool) :
    dotBit α a = decide (Odd (univ.filter fun j => (α j && a j) = true).card) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [dotBit_succ, ih, Fin.card_filter_univ_succ]
    by_cases h : (α 0 && a 0) = true
    · simp only [h, ite_true, Nat.odd_add_one, decide_not, Bool.true_xor]
    · simp only [h, Bool.false_eq_true, ite_false, Bool.false_xor]

/-- **A coefficient vector supported on the coordinate `i`** pairs with an answer as its
restriction to the coordinate pairs with the coordinate of the answer. -/
theorem dotBit_varEquiv (x : Fin k → X) (i : Fin k) (f : ℕ → Bool)
    (a : Fin (G.lenRSum x + G.lenLSum x) → Bool) :
    dotBit (fun g => if ((G.varEquiv x) g).1 = i then f ((G.varEquiv x) g).2.val else false) a =
      dotBit (fun v : Fin (G.len (x i)) => f v.val) (fun v => a ((G.varEquiv x).symm ⟨i, v⟩)) := by
  rw [dotBit_eq_decide_odd, dotBit_eq_decide_odd]
  congr 2
  symm
  refine Finset.card_bij (fun v _ => (G.varEquiv x).symm ⟨i, v⟩) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [Equiv.apply_symm_apply]
    simpa using hv
  · intro v _ w _ h
    have := congrArg (G.varEquiv x) h
    simp only [Equiv.apply_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact this
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨⟨j, v⟩, rfl⟩ := (G.varEquiv x).symm.surjective g
    rw [Equiv.apply_symm_apply] at hg
    by_cases hj : j = i
    · subst hj
      refine ⟨v, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hg
    · simp [hj] at hg

/-- A bit string of length `p + q + 1`, cut into its first `p` bits, its next `q` bits and its
last bit. -/
theorem eq_ofFn_append_ofFn_append (c : Cost.BitStr) {p q : ℕ} (h : c.length = p + q + 1) :
    c = List.ofFn (fun v : Fin p => c.getD v false) ++
      List.ofFn (fun w : Fin q => c.getD (p + w) false) ++ [c.getD (p + q) false] := by
  apply List.ext_getElem
  · simp [h]; omega
  intro j h1 h2
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge j p with hj | hj
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp [List.getElem?_eq_getElem h1]
  rcases Nat.lt_or_ge j (p + q) with hj' | hj'
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem_ofFn]
    rw [show p + (j - p) = j by omega, List.getElem?_eq_getElem h1]
    rfl
  · rw [List.getElem_append_right (by simp; omega)]
    have hjq : j = p + q := by
      have : j < p + q + 1 := by omega
      omega
    subst hjq
    simp [List.getElem?_eq_getElem h1]

/-- **The padded constraint is satisfied by the whole answers exactly when the constraint is
satisfied by the coordinate's answers.** -/
theorem satisfies_padCons_iff (x y : Fin k → X) (i : Fin k) (c : Cost.BitStr)
    (a : Fin (G.lenRSum x + G.lenLSum x) → Bool) (b : Fin (G.lenRSum y + G.lenLSum y) → Bool) :
    Satisfies (G.padCons x y i c) (List.ofFn a ++ List.ofFn b ++ [true]) ↔
      Satisfies c (List.ofFn (fun v => a ((G.varEquiv x).symm ⟨i, v⟩)) ++
        List.ofFn (fun w => b ((G.varEquiv y).symm ⟨i, w⟩)) ++ [true]) := by
  unfold padCons
  split_ifs with hc
  · conv_rhs => rw [eq_ofFn_append_ofFn_append c hc]
    rw [satisfies_ofFn_iff, satisfies_ofFn_iff,
      G.dotBit_varEquiv x i (fun n => c.getD n false) a,
      G.dotBit_varEquiv y i (fun n => c.getD (G.len (x i) + n) false) b]
  · refine iff_of_false ?_ ?_
    · exact not_satisfies_rejectConstraint _ _
    · rintro ⟨hlen, -⟩
      exact hc (by simp [len] at hlen ⊢; omega)

/-- **The acceptance law of the product**: the canonical decider accepts a pair of answers to
`(x⃗, y⃗)` exactly when they have the right lengths and every coordinate is accepted. -/
theorem repeat_accepts_iff (x y : Fin k → X) (a b : Cost.BitStr) :
    (G.repeat k).Accepts x y a b ↔
      a.length = (G.repeat k).len x ∧ b.length = (G.repeat k).len y ∧
        ∀ i, G.Accepts (x i) (y i) (G.coord x a i) (G.coord y b i) := by
  unfold Accepts
  refine and_congr_right fun ha => and_congr_right fun hb => ?_
  set av : Fin (G.lenRSum x + G.lenLSum x) → Bool := fun g => a.getD g false
  set bv : Fin (G.lenRSum y + G.lenLSum y) → Bool := fun g => b.getD g false
  have hav : List.ofFn av = a := by
    apply List.ext_getElem (by rw [List.length_ofFn]; exact ha.symm)
    intro j h1 h2
    simp [av, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  have hbv : List.ofFn bv = b := by
    apply List.ext_getElem (by rw [List.length_ofFn]; exact hb.symm)
    intro j h1 h2
    simp [bv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  have hcoordx : ∀ i, G.coord x a i = List.ofFn (fun v => av ((G.varEquiv x).symm ⟨i, v⟩)) :=
    fun _ => rfl
  have hcoordy : ∀ i, G.coord y b i = List.ofFn (fun w => bv ((G.varEquiv y).symm ⟨i, w⟩)) :=
    fun _ => rfl
  simp only [«repeat», List.mem_flatMap, List.mem_finRange, List.mem_map, true_and,
    forall_exists_index, and_imp]
  constructor
  · intro h i
    refine ⟨length_coord _ _ _ _, length_coord _ _ _ _, fun c hc => ?_⟩
    have h' := h _ i c (by rw [coordR_take, coordR_take]; exact hc) rfl
    rw [← hav, ← hbv, satisfies_padCons_iff] at h'
    rw [hcoordx, hcoordy]
    exact h'
  · intro h c' i c hc hc'
    subst hc'
    rw [coordR_take, coordR_take] at hc
    have := (h i).2.2 c hc
    rw [hcoordx, hcoordy] at this
    rw [← hav, ← hbv, satisfies_padCons_iff]
    exact this

end TailoredGame

end MIPRE.Tailored

end
