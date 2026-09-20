/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.CircuitArithmetization
import MIPRE.Foundations.LowDegree.FiniteVariables
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Circuit arithmetization on exactly the input and gate variables

The first `C.inputs` coordinates are the inputs, followed by the `C.size` gate
variables. No new variables are needed for routing repeated input reads.
-/

noncomputable section

namespace MIPRE.SAT.Circuit

open MvPolynomial LowDegree

variable {F : Type*} [Field F]

/-- Embed the exact finite coordinate set into input and gate indices. -/
def wireEmbedding (C : Circuit) : Fin (C.inputs + C.size) → ℕ ⊕ ℕ :=
  Sum.map Fin.val Fin.val ∘ finSumFinEquiv.symm

theorem wireEmbedding_injective (C : Circuit) : Function.Injective C.wireEmbedding :=
  (Fin.val_injective.sumMap Fin.val_injective).comp finSumFinEquiv.symm.injective

@[simp] theorem wireEmbedding_input (C : Circuit) (i : Fin C.inputs) :
    C.wireEmbedding (Fin.castAdd C.size i) = .inl i.val := by simp [wireEmbedding]

@[simp] theorem wireEmbedding_gate (C : Circuit) (j : Fin C.size) :
    C.wireEmbedding (Fin.natAdd C.inputs j) = .inr j.val := by simp [wireEmbedding]

/-- The routed polynomial restricted to the exact finite coordinate set. -/
def finiteArith (C : Circuit) : MvPolynomial (Fin (C.inputs + C.size)) F :=
  killCompl C.wireEmbedding_injective C.routedArith

theorem degreeOf_finiteArith_le (C : Circuit) (hC : C.WellFormed)
    (i : Fin (C.inputs + C.size)) : (C.finiteArith (F := F)).degreeOf i ≤ 5 :=
  (degreeOf_killCompl_le C.wireEmbedding_injective C.routedArith i).trans
    (degreeOf_routedArith_le C hC _)

/-- Read the finite assignment's input part, with false outside the circuit. -/
def inputPart (C : Circuit) (z : Fin (C.inputs + C.size) → Bool) (i : ℕ) : Bool :=
  if h : i < C.inputs then z (Fin.castAdd C.size ⟨i, h⟩) else false

/-- Read the finite assignment's gate part, with false outside the circuit. -/
def gatePart (C : Circuit) (z : Fin (C.inputs + C.size) → Bool) (j : ℕ) : Bool :=
  if h : j < C.size then z (Fin.natAdd C.inputs ⟨j, h⟩) else false

theorem eval_finiteArith (C : Circuit) (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith =
      MvPolynomial.eval (Sum.elim (fun i => ofBool (C.inputPart z i))
        (fun j => ofBool (C.gatePart z j))) C.routedArith := by
  apply eval_killCompl_eq
  · intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp [inputPart]
      rfl
    · simp [gatePart]
      rfl
  · intro v hv
    cases v with
    | inl i =>
      have hi : ¬ i < C.inputs := by
        intro hi
        exact hv ⟨Fin.castAdd C.size ⟨i, hi⟩, wireEmbedding_input C ⟨i, hi⟩⟩
      simp [inputPart, hi, ofBool]
    | inr j =>
      have hj : ¬ j < C.size := by
        intro hj
        exact hv ⟨Fin.natAdd C.inputs ⟨j, hj⟩, wireEmbedding_gate C ⟨j, hj⟩⟩
      simp [gatePart, hj, ofBool]

variable [CharP F 2]

/-- The finite polynomial enforces all gate values and the output literal. -/
theorem eval_finiteArith_iff (C : Circuit) (hC : C.WellFormed)
    (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 ↔
      C.RoutedConsistent (C.inputPart z) (C.gatePart z) ∧ C.gatePart z (C.size - 1) = true := by
  rw [eval_finiteArith, eval_routedArith_iff C hC]

/-- Boolean-valuedness is retained on the exact finite coordinate set. -/
theorem eval_finiteArith_bool (C : Circuit) (hC : C.WellFormed)
    (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 0 ∨
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 := by
  rw [eval_finiteArith]
  exact eval_routedArith_bool C hC _ _

/-- A finite assignment whose input coordinates equal `x` reads `x` on every
input the circuit can use. -/
theorem inputPart_eq (C : Circuit) (x : ℕ → Bool) (z : Fin (C.inputs + C.size) → Bool)
    (h : ∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i) :
    ∀ i < C.inputs, C.inputPart z i = x i := by
  intro i hi
  simp only [inputPart, dif_pos hi]
  exact h ⟨i, hi⟩

/-- Exact-variable arithmetization of the accepting circuit relation. -/
theorem eval_iff_exists_finiteArith (C : Circuit) (hC : C.WellFormed) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ z : Fin (C.inputs + C.size) → Bool,
      (∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i) ∧
      MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 := by
  have hs : 0 < C.size := List.length_pos_iff.mpr hC.nonempty
  constructor
  · intro hx
    let z : Fin (C.inputs + C.size) → Bool :=
      Fin.addCases (fun i => x i) (fun j => C.valueAt x j)
    have hz : ∀ i : Fin C.inputs, z (Fin.castAdd C.size i) = x i := by intro i; simp [z]
    have hg : ∀ j < C.size, C.gatePart z j = C.valueAt x j := by
      intro j hj
      simp only [gatePart, dif_pos hj]
      simp only [z, Fin.addCases_right]
    have he := C.valueAt_congr hC.inputsLt (C.inputPart z) x (inputPart_eq C x z hz)
    refine ⟨z, hz, (eval_finiteArith_iff C hC z).mpr ⟨?_, ?_⟩⟩
    · apply (routedConsistent_iff C _ _).mpr
      intro k hk
      rw [hg k hk, he k]
    · rw [hg _ (by omega)]
      simpa [Circuit.eval, hC.nonempty, size] using hx
  · rintro ⟨z, hz, hp⟩
    have hc := (eval_finiteArith_iff C hC z).mp hp
    have hv := (eval_iff_routedConsistent C hC.nonempty (C.inputPart z)).mpr
      ⟨C.gatePart z, hc⟩
    rw [C.eval_congr hC.inputsLt (C.inputPart z) x (inputPart_eq C x z hz)] at hv
    exact hv

end MIPRE.SAT.Circuit

end
