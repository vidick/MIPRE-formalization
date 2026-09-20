/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.InputRouting
import MIPRE.Foundations.LowDegree.Encoding
import Mathlib.Algebra.CharP.Two

/-!
# Bounded-degree circuit consistency polynomials

In characteristic two, `1 + w + rhs` is the indicator of Boolean gate
consistency. Input-copy routing bounds the uses of external variables as well
as gate variables. The output literal is included explicitly.
-/

noncomputable section

namespace MIPRE.SAT.Circuit

open MvPolynomial LowDegree Finset

variable {F : Type*} [Field F]

/-- A gate's right-hand-side polynomial, with routed input copies. -/
def gateArith (C : Circuit) (k : ℕ) : Gate → MvPolynomial (ℕ ⊕ ℕ) F
  | .input i => X (C.inputRef k i)
  | .const b => MvPolynomial.C (ofBool b)
  | .and u v => X (.inr u) * X (.inr v)
  | .or u v => 1 - (1 - X (.inr u)) * (1 - X (.inr v))
  | .not u => 1 - X (.inr u)

/-- The consistency factor for gate `k`. -/
def consistencyFactor (C : Circuit) (k : ℕ) : MvPolynomial (ℕ ⊕ ℕ) F :=
  1 + X (.inr k) + C.gateArith k (C.gates.getD k (.const false))

/-- All gate-consistency factors, together with the output literal. -/
def routedArith (C : Circuit) : MvPolynomial (ℕ ⊕ ℕ) F :=
  (∏ k ∈ range C.size, C.consistencyFactor k) * X (.inr (C.size - 1))

/-- Contribution from an external-input copy link. -/
def inputWeight (C : Circuit) (k : ℕ) (v : ℕ ⊕ ℕ) : ℕ :=
  match C.gates.getD k (.const false) with
  | .input i => if v = C.inputRef k i then 1 else 0
  | _ => 0

/-- Contribution from ordinary gate references, counting repeated references. -/
def refWeight (g : Gate) : ℕ ⊕ ℕ → ℕ
  | .inl _ => 0
  | .inr j => g.refs.count j

private theorem count_pair (u w j : ℕ) :
    [u, w].count j = (if j = u then 1 else 0) + (if j = w then 1 else 0) := by
  by_cases hu : u = j <;> by_cases hw : w = j <;> simp [hu, hw, eq_comm]

private theorem degree_one_sub (p : MvPolynomial (ℕ ⊕ ℕ) F) (v : ℕ ⊕ ℕ) :
    (1 - p).degreeOf v ≤ p.degreeOf v := by simpa using degreeOf_sub_le v 1 p

theorem degreeOf_gateArith (C : Circuit) (k : ℕ) (v : ℕ ⊕ ℕ) :
    (C.gateArith (F := F) k (C.gates.getD k (.const false))).degreeOf v ≤
      C.inputWeight k v + refWeight (C.gates.getD k (.const false)) v := by
  unfold inputWeight
  generalize C.gates.getD k (.const false) = g
  cases g with
  | input i => cases v <;> simp [gateArith, refWeight, Gate.refs, degreeOf_X]
  | const b => cases v <;> simp [gateArith, refWeight, Gate.refs]
  | and u w =>
    have h := degreeOf_mul_le v (X (.inr u) : MvPolynomial (ℕ ⊕ ℕ) F) (X (.inr w))
    cases v <;> simpa [gateArith, refWeight, Gate.refs, count_pair, degreeOf_X] using h
  | or u w =>
    have ha := degree_one_sub (F := F) ((1 - X (.inr u)) * (1 - X (.inr w))) v
    have hb := degreeOf_mul_le v (1 - X (.inr u) : MvPolynomial (ℕ ⊕ ℕ) F) (1 - X (.inr w))
    have hc := Nat.add_le_add (degree_one_sub (F := F) (X (.inr u)) v)
      (degree_one_sub (F := F) (X (.inr w)) v)
    have h := ha.trans (hb.trans hc)
    cases v <;> simpa [gateArith, refWeight, Gate.refs, count_pair, degreeOf_X] using h
  | not u =>
    have h := degree_one_sub (X (.inr u) : MvPolynomial (ℕ ⊕ ℕ) F) v
    cases v with
    | inl i => simpa [gateArith, refWeight, Gate.refs, degreeOf_X] using h
    | inr j =>
      by_cases hu : u = j <;> simpa [gateArith, refWeight, Gate.refs, degreeOf_X, hu, eq_comm] using h

theorem degreeOf_consistencyFactor (C : Circuit) (k : ℕ) (v : ℕ ⊕ ℕ) :
    (C.consistencyFactor (F := F) k).degreeOf v ≤
      (if v = .inr k then 1 else 0) + C.inputWeight k v +
        refWeight (C.gates.getD k (.const false)) v := by
  have h := degreeOf_gateArith (F := F) C k v
  have h' := degreeOf_add_le v (1 + X (.inr k))
    (C.gateArith (F := F) k (C.gates.getD k (.const false)))
  have h₀ := degreeOf_add_le v (1 : MvPolynomial (ℕ ⊕ ℕ) F) (X (.inr k))
  simp only [degreeOf_one, degreeOf_X, zero_le, max_eq_right] at h₀
  change _ ≤ _ at h'
  unfold consistencyFactor
  exact h'.trans (max_le (by omega) (by omega))

/-- Copy routing contributes at most one occurrence of any variable. -/
theorem sum_inputWeight_le (C : Circuit) (v : ℕ ⊕ ℕ) :
    ∑ k ∈ range C.size, C.inputWeight k v ≤ 1 := by
  rw [Finset.sum_le_one_iff]
  intro a b ha hb hwa hwb
  have key (k : ℕ) (hk : C.inputWeight k v ≠ 0) :
      ∃ i, C.gates.getD k (.const false) = .input i ∧ v = C.inputRef k i := by
    unfold inputWeight at hk
    split at hk <;> try contradiction
    split_ifs at hk with h
    · exact ⟨_, ‹_ = Gate.input _›, h⟩
    · contradiction
  obtain ⟨i, hi, hv⟩ := key a hwa
  obtain ⟨j, hj, hv'⟩ := key b hwb
  refine ⟨inputRef_injective C hi hj (hv.symm.trans hv'), ?_⟩
  simp only [inputWeight, hi, if_pos hv]

private theorem sum_getD (l : List Gate) (f : Gate → ℕ) :
    ∑ k ∈ range l.length, f (l.getD k (.const false)) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, ih, List.map_cons, List.sum_cons]
    omega

theorem sum_refWeight (C : Circuit) (v : ℕ ⊕ ℕ) :
    ∑ k ∈ range C.size, refWeight (C.gates.getD k (.const false)) v =
      match v with | .inl _ => 0 | .inr j => C.fanout j := by
  rw [show C.size = C.gates.length from rfl, sum_getD C.gates (fun g => refWeight g v)]
  cases v with
  | inl i => simp [refWeight]
  | inr j => rfl

/-- A degree-five bound for the characteristic-two construction, stronger than
the degree-six bound required by the PCP interface. -/
theorem degreeOf_routedArith_le (C : Circuit) (hC : C.WellFormed) (v : ℕ ⊕ ℕ) :
    (C.routedArith (F := F)).degreeOf v ≤ 5 := by
  have hf := degreeOf_mul_le v
    (∏ k ∈ range C.size, C.consistencyFactor (F := F) k) (X (.inr (C.size - 1)))
  have hp := (degreeOf_prod_le v (range C.size) (fun k => C.consistencyFactor (F := F) k)).trans
    (Finset.sum_le_sum (fun k _ => degreeOf_consistencyFactor (F := F) C k v))
  simp only [Finset.sum_add_distrib] at hp
  have hi := sum_inputWeight_le C v
  have hr : (∑ k ∈ range C.size, refWeight (C.gates.getD k (.const false)) v) ≤ 2 := by
    rw [sum_refWeight]
    cases v with
    | inl i => exact Nat.zero_le 2
    | inr j => exact hC.fanout_le j
  have hs : (∑ k ∈ range C.size, if v = Sum.inr k then 1 else 0) ≤ 1 := by
    cases v with
    | inl i => simp
    | inr j => simp only [Sum.inr.injEq, sum_ite_eq, mem_range]; split <;> omega
  have ho : (X (.inr (C.size - 1)) : MvPolynomial (ℕ ⊕ ℕ) F).degreeOf v ≤ 1 := by
    rw [degreeOf_X]
    split <;> omega
  change _ ≤ _ at hf
  unfold routedArith
  omega

/-- Boolean evaluation of a gate's polynomial. -/
theorem eval_gateArith (C : Circuit) (k : ℕ) (g : Gate) (x w : ℕ → Bool)
    (href : ∀ u ∈ g.refs, u < k) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      (C.gateArith k g) = ofBool (g.eval
        (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)) := by
  have hv (u : ℕ) (hu : u < k) : (List.ofFn fun j : Fin k => w j).getD u false = w u := by
    simp [List.getD_eq_getElem?_getD, hu]
  cases g with
  | input i =>
    simp only [gateArith, eval_X, Gate.eval]
    cases C.inputRef k i <;> rfl
  | const b => simp [gateArith, Gate.eval]
  | and u v =>
    have hu := hv u (href u (by simp [Gate.refs]))
    have hv' := hv v (href v (by simp [Gate.refs]))
    simp only [gateArith, map_mul, eval_X, Sum.elim_inr, Gate.eval, hu, hv']
    cases w u <;> cases w v <;> simp [ofBool]
  | or u v =>
    have hu := hv u (href u (by simp [Gate.refs]))
    have hv' := hv v (href v (by simp [Gate.refs]))
    simp only [gateArith, map_sub, map_one, map_mul, eval_X, Sum.elim_inr, Gate.eval, hu, hv']
    cases w u <;> cases w v <;> simp [ofBool]
  | not u =>
    have hu := hv u (href u (by simp [Gate.refs]))
    simp only [gateArith, map_sub, map_one, eval_X, Sum.elim_inr, Gate.eval, hu]
    cases w u <;> simp [ofBool]

variable [CharP F 2]

/-- In characteristic two, the factor is exactly the Boolean consistency indicator. -/
theorem eval_consistencyFactor (C : Circuit) (hC : C.WellFormed) (k : ℕ) (hk : k < C.size)
    (x w : ℕ → Bool) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      (C.consistencyFactor k) =
        if w k = (C.gates.getD k (.const false)).eval
          (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)
        then 1 else 0 := by
  have href : ∀ u ∈ (C.gates.getD k (.const false)).refs, u < k := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact hC.refs_lt k hk
  rw [consistencyFactor, map_add, map_add, map_one, eval_X, eval_gateArith C k _ x w href]
  change 1 + ofBool (w k) + ofBool _ = _
  generalize (C.gates.getD k (.const false)).eval
    (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j) = b
  cases w k <;> cases b <;> simp [ofBool, CharTwo.add_self_eq_zero]

/-- The polynomial is one precisely on consistent accepting Boolean assignments. -/
theorem eval_routedArith_iff (C : Circuit) (hC : C.WellFormed) (x w : ℕ → Bool) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      C.routedArith = 1 ↔ C.RoutedConsistent x w ∧ w (C.size - 1) = true := by
  rw [routedArith, map_mul, map_prod, eval_X]
  by_cases hc : C.RoutedConsistent x w
  · have hp : (∏ k ∈ range C.size, MvPolynomial.eval
        (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
        (C.consistencyFactor k)) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      rw [eval_consistencyFactor C hC k (mem_range.mp hk) x w, if_pos (hc k (mem_range.mp hk))]
    rw [hp]
    simp only [one_mul, hc, true_and, Sum.elim_inr]
    cases w (C.size - 1) <;> simp [ofBool]
  · have hn : ∃ k, k < C.size ∧ w k ≠ (C.gates.getD k (.const false)).eval
        (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j) := by
      simpa only [RoutedConsistent, not_forall, exists_prop] using hc
    obtain ⟨k, hk, he⟩ := hn
    have hp : (∏ k ∈ range C.size, MvPolynomial.eval
        (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
        (C.consistencyFactor k)) = 0 := by
      apply Finset.prod_eq_zero (mem_range.mpr hk)
      rw [eval_consistencyFactor C hC k hk x w, if_neg he]
    simp [hp, hc]

omit [CharP F 2] in
private theorem prod_zero_or_one {ι : Type*} (s : Finset ι) (f : ι → F)
    (h : ∀ i ∈ s, f i = 0 ∨ f i = 1) : (∏ i ∈ s, f i) = 0 ∨ (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rcases h a (mem_insert_self _ _) with h₀ | h₁
    · simp [h₀]
    · rw [h₁, one_mul]
      exact ih (fun i hi => h i (mem_insert_of_mem hi))

/-- Every Boolean assignment gives a Boolean field value, including rejected ones. -/
theorem eval_routedArith_bool (C : Circuit) (hC : C.WellFormed) (x w : ℕ → Bool) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      C.routedArith = 0 ∨
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      C.routedArith = 1 := by
  rw [routedArith, map_mul, map_prod, eval_X]
  have hp := prod_zero_or_one (range C.size) (fun k => MvPolynomial.eval
    (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j))) (C.consistencyFactor k))
    (by
      intro k hk
      rw [eval_consistencyFactor C hC k (mem_range.mp hk) x w]
      split <;> simp)
  rcases hp with hp | hp
  · simp [hp]
  · simp only [hp, one_mul, Sum.elim_inr]
    cases w (C.size - 1) <;> simp [ofBool]

/-- Acceptance is equivalent to an auxiliary Boolean assignment on which the
bounded-degree consistency polynomial takes value one. -/
theorem eval_iff_exists_routedArith (C : Circuit) (hC : C.WellFormed) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ w : ℕ → Bool, MvPolynomial.eval
      (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j))) C.routedArith = 1 := by
  simp_rw [eval_routedArith_iff C hC]
  exact eval_iff_routedConsistent C hC.nonempty x

end MIPRE.SAT.Circuit

end
