/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.CircuitFieldEval
import MIPRE.Foundations.SAT.FiniteCircuitArithmetization

/-!
# Correctness of the executable circuit polynomial evaluator
-/

namespace MIPRE.SAT.Circuit

open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset

/-- Routing history at a prefix of the actual circuit. -/
def fieldHistory (C : Circuit) (w : List BitStr) (k : ℕ) : List (Gate × BitStr) :=
  (List.range k).map (fun j => (C.gates.getD j (.const false), w.getD j []))

def fieldPrefix (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) : FieldState :=
  (C.fieldHistory w k).foldl fieldStep ((p, x, w, []), oneBits p)

theorem fieldPrefix_env (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    (C.fieldPrefix p x w k).1 = (p, x, w, C.fieldHistory w k) := by
  simpa [fieldPrefix] using
    (fold_fieldStep (C.fieldHistory w k) ((p, x, w, []), oneBits p)).1

theorem fieldPrefix_succ (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    C.fieldPrefix p x w (k + 1) =
      fieldStep (C.fieldPrefix p x w k) (C.gates.getD k (.const false), w.getD k []) := by
  simp only [fieldPrefix, fieldHistory, List.range_succ, List.map_append,
    List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem fieldPrefix_width (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    (C.fieldPrefix p x w k).2.length = p.length := by
  induction k with
  | zero => exact length_oneBits p
  | succ k ih =>
    rw [fieldPrefix_succ]
    change (mulReduce _ _ _).length = p.length
    rw [show (C.fieldPrefix p x w k).1.1 = p from
      congrArg Prod.fst (fieldPrefix_env C p x w k)]
    exact length_mulReduce _ _ _ ih

theorem readInput_fieldHistory (C : Circuit) (p : BitStr) (x w : List BitStr) (k i : ℕ) :
    readInput (p, x, w, C.fieldHistory w k) i =
      Sum.elim (fun j => x.getD j []) (fun j => w.getD j []) (C.inputRef k i) :=
  lastInputValue_range C k i (fun j => x.getD j []) (fun j => w.getD j [])

private theorem width_getD (p : BitStr) (l : List BitStr)
    (h : ∀ b ∈ l, b.length = p.length) (i : ℕ) (hi : i < l.length) :
    (l.getD i []).length = p.length := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h _ (List.getElem_mem hi)

private theorem gate_ref_width (C : Circuit) (hC : C.WellFormed) (p : BitStr)
    (w : List BitStr) (hwlen : C.size ≤ w.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k < C.size) :
    ∀ j ∈ (C.gates.getD k (.const false)).refs, (w.getD j []).length = p.length := by
  intro j hj
  have hr := hC.refs_lt k hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hj
  exact width_getD p w hw j (lt_of_lt_of_le (lt_trans (hr j hj) hk) hwlen)

private theorem gate_input_width (C : Circuit) (hC : C.WellFormed) (p : BitStr)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k < C.size) :
    ∀ i, C.gates.getD k (.const false) = .input i →
      (readInput (p, x, w, C.fieldHistory w k) i).length = p.length := by
  intro i hi
  rw [readInput_fieldHistory]
  rcases C.inputRef_cases k i with he | ⟨u, hu, he, _⟩
  · rw [he]
    have himem : Gate.input i ∈ C.gates := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hi
      exact hi ▸ List.getElem_mem hk
    exact width_getD p x hx i ((hC.inputs_lt i himem).trans_le hxlen)
  · rw [he]
    exact width_getD p w hw u ((hu.trans hk).trans_le hwlen)

variable {F : Type*} [Field F] [CharP F 2]

/-- Each computed factor evaluates to the corresponding polynomial factor. -/
theorem evalBits_factorBits (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k < C.size) :
    BinaryPolynomial.evalBits z (factorBits (p, x, w, C.fieldHistory w k)
      (C.gates.getD k (.const false), w.getD k [])) =
      MvPolynomial.eval (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i []))
        (fun j => BinaryPolynomial.evalBits z (w.getD j []))) (C.consistencyFactor k) := by
  have hr := gate_ref_width C hC p w hwlen hw k hk
  have hi := gate_input_width C hC p x w hxlen hwlen hx hw k hk
  have hg := length_gateBits p (readInput (p, x, w, C.fieldHistory w k)) w
    (C.gates.getD k (.const false)) hi hr
  have hkwidth := width_getD p w hw k (hk.trans_le hwlen)
  have hl : (xorBits (oneBits p) (w.getD k [])).length = p.length := by
    simp only [length_xorBits, length_oneBits, hkwidth, min_self]
  unfold factorBits
  change BinaryPolynomial.evalBits z (xorBits (xorBits (oneBits p) (w.getD k []))
    (gateBits p (readInput (p, x, w, C.fieldHistory w k)) w
      (C.gates.getD k (.const false)))) = _
  rw [evalBits_xor z _ _ (hl.trans hg.symm),
    evalBits_xor z _ _ (by simpa using hkwidth.symm), evalBits_oneBits z p hp,
    evalBits_gateBits z p hp hroot _ _ _ hr]
  have he : (fun i => BinaryPolynomial.evalBits z (readInput (p, x, w, C.fieldHistory w k) i)) =
      (fun i => Sum.elim (fun j => BinaryPolynomial.evalBits z (x.getD j []))
        (fun j => BinaryPolynomial.evalBits z (w.getD j [])) (C.inputRef k i)) := by
    funext i
    rw [readInput_fieldHistory]
    cases C.inputRef k i <;> rfl
  rw [he, gateValue_eq_eval_gateArith]
  simp [consistencyFactor]

/-- The accumulator is precisely the product of the factors already scanned. -/
theorem evalBits_fieldPrefix (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k ≤ C.size) :
    BinaryPolynomial.evalBits z (C.fieldPrefix p x w k).2 =
      ∏ j ∈ range k, MvPolynomial.eval
        (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i [])) (fun i => BinaryPolynomial.evalBits z (w.getD i [])))
        (C.consistencyFactor j) := by
  induction k with
  | zero => simpa [fieldPrefix, fieldHistory] using evalBits_oneBits z p hp
  | succ k ih =>
    rw [fieldPrefix_succ]
    change BinaryPolynomial.evalBits z (mulReduce _ _ _) = _
    rw [show (C.fieldPrefix p x w k).1 = (p, x, w, C.fieldHistory w k) from
      fieldPrefix_env C p x w k]
    rw [evalBits_mulReduce z p _ _ (fieldPrefix_width C p x w k) hroot,
      evalBits_factorBits C hC z p hp hroot x w hxlen hwlen hx hw k (by omega),
      ih (by omega), Finset.prod_range_succ]

/-- The executable coefficient-vector evaluator computes the complete routed
circuit polynomial at every correctly sized field point. -/
theorem evalBits_circuitBits (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length) :
    BinaryPolynomial.evalBits z (circuitBits p x w C.gates) =
      MvPolynomial.eval (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i []))
        (fun j => BinaryPolynomial.evalBits z (w.getD j []))) C.routedArith := by
  change BinaryPolynomial.evalBits z (mulReduce p (C.fieldPrefix p x w C.size).2
    (w.getD (C.size - 1) [])) = _
  rw [evalBits_mulReduce z p _ _ (fieldPrefix_width C p x w C.size) hroot,
    evalBits_fieldPrefix C hC z p hp hroot x w hxlen hwlen hx hw C.size le_rfl]
  simp [routedArith]

/-- The evaluator always returns the supplied modulus width. -/
theorem length_circuitBits (C : Circuit) (p : BitStr) (x w : List BitStr) :
    (circuitBits p x w C.gates).length = p.length :=
  length_mulReduce p _ _ (fieldPrefix_width C p x w C.size)

/-- The same evaluator computes the polynomial on the exact finite coordinate
set used by the PCP, with the inputs followed by the gate variables. -/
theorem evalBits_circuitBits_finite (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : x.length = C.inputs) (hwlen : w.length = C.size)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length) :
    BinaryPolynomial.evalBits z (circuitBits p x w C.gates) =
      MvPolynomial.eval
        (Fin.addCases (fun i => BinaryPolynomial.evalBits z (x.getD i []))
          (fun j => BinaryPolynomial.evalBits z (w.getD j []))) C.finiteArith := by
  rw [evalBits_circuitBits C hC z p hp hroot x w hxlen.ge hwlen.ge hx hw]
  symm
  apply eval_killCompl_eq
  · intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp
    · simp
  · intro v hv
    cases v with
    | inl i =>
      have hi : ¬ i < C.inputs := by
        intro hi
        exact hv ⟨Fin.castAdd C.size ⟨i, hi⟩, wireEmbedding_input C ⟨i, hi⟩⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i)]
    | inr j =>
      have hj : ¬ j < C.size := by
        intro hj
        exact hv ⟨Fin.natAdd C.inputs ⟨j, hj⟩, wireEmbedding_gate C ⟨j, hj⟩⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ j)]

end MIPRE.SAT.Circuit
