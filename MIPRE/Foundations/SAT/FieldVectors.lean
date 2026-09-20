/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Pcp
import MIPRE.Foundations.SAT.CircuitFieldCorrect

/-! # Encoded field vectors and their circuit-coordinate slices -/

namespace MIPRE.SAT.BinField

open Cost LowDegree LowDegree.BinaryPolynomial

variable {k : ℕ} (E : BinField k)

theorem vecBits_eq_ofFn {n : ℕ} (v : Fin n → E.carrier) :
    E.vecBits v = List.ofFn (fun i => E.toBits (v i)) := by
  simp [vecBits]
  rfl

theorem vecBits_cast {n m : ℕ} (h : n = m) (v : Fin m → E.carrier) :
    E.vecBits (v ∘ Fin.cast h) = E.vecBits v := by
  subst m
  rfl

@[simp] theorem getD_vecBits {n : ℕ} (v : Fin n → E.carrier) (i : Fin n) :
    (E.vecBits v).getD i [] = E.toBits (v i) := by
  simp only [vecBits_eq_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]

/-- Slicing the raw blocks is exactly slicing the typed coordinate function. -/
theorem slice_vecBits {n : ℕ} (v : Fin n → E.carrier) (a b : ℕ) (h : a + b ≤ n) :
    ((E.vecBits v).drop a).take b =
      E.vecBits (fun i : Fin b => v ⟨a + i, by have := i.isLt; omega⟩) := by
  simp only [vecBits_eq_ofFn]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem zip_vecBits {n : ℕ} (v w : Fin n → E.carrier) :
    (E.vecBits v).zip (E.vecBits w) =
      List.ofFn (fun i => (E.toBits (v i), E.toBits (w i))) := by
  simp only [vecBits_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zip, List.getElem_ofFn]

/-- The circuit evaluator on a raw vector computes the finite polynomial at
the original typed point, for any correct coefficient representation. -/
theorem eval_circuitBits_vecBits (C : Circuit) (hC : C.WellFormed)
    (p : BitStr) (hp : p ≠ []) (hpk : p.length = k)
    [CharP E.carrier 2] (root : E.carrier)
    (hroot : root ^ p.length = BinaryPolynomial.evalBits root p)
    (hencode : ∀ a : E.carrier, BinaryPolynomial.evalBits root (E.toBits a) = a)
    (v : Fin (C.inputs + C.size) → E.carrier) :
    BinaryPolynomial.evalBits root (Circuit.circuitBits p
      ((E.vecBits v).take C.inputs) ((E.vecBits v).drop C.inputs) C.gates) =
      MvPolynomial.eval v C.finiteArith := by
  let x := (E.vecBits v).take C.inputs
  let w := (E.vecBits v).drop C.inputs
  have hxlen : x.length = C.inputs := by simp [x]
  have hwlen : w.length = C.size := by simp [w]
  have hx : ∀ b ∈ x, b.length = p.length := by
    intro b hb
    exact (E.width_vecBits v (List.mem_of_mem_take hb)).trans hpk.symm
  have hw : ∀ b ∈ w, b.length = p.length := by
    intro b hb
    exact (E.width_vecBits v (List.mem_of_mem_drop hb)).trans hpk.symm
  rw [Circuit.evalBits_circuitBits_finite C hC root p hp hroot x w hxlen hwlen hx hw]
  congr 2
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp only [Fin.addCases_left]
    have hg : x.getD a [] = E.toBits (v (Fin.castAdd C.size a)) := by
      simp only [x, List.getD_eq_getElem?_getD]
      rw [List.getElem?_take_of_lt a.isLt]
      exact getD_vecBits E v (Fin.castAdd C.size a)
    rw [hg, hencode]
  · simp only [Fin.addCases_right]
    have hg : w.getD b [] = E.toBits (v (Fin.natAdd C.inputs b)) := by
      simp only [w, List.getD_eq_getElem?_getD, List.getElem?_drop]
      exact getD_vecBits E v (Fin.natAdd C.inputs b)
    rw [hg, hencode]

end MIPRE.SAT.BinField
