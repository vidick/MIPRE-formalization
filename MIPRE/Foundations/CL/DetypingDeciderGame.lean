/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingDecider

/-! # The executable detyped predicate agrees with the finite game

The finite typed predicate retains the inner answer cutoff. On the outer
bounded answer alphabet, the extra global cutoff disappears identically.
-/

noncomputable section

namespace MIPRE.CL.Detyping.DeciderProgram

set_option linter.unusedSectionVars false

open Cost Cost.PolyTimeFun Program

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

theorem accepts_selected {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    (P : Question T ι → Question T ι → A → B → Bool)
    (x y : Coord T ι → 𝔽₂) (a : A) (b : B) :
    Detyping.accepts E P x y a b =
      match selectedEdge E (pull .inl x) (pull .inl y) with
      | none => true
      | some uv => P (uv.1, pull .inr x) (uv.2, pull .inr y) a b := by
  unfold Detyping.accepts selectedEdge
  cases select E false (pull .inl x) <;> cases select E true (pull .inl y) <;> simp only
  split_ifs <;> rfl

theorem graphOfBits_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    graphOfBits (toBits (push (registerEquiv s).toEmbedding x)) = pull .inl x := by
  rw [← graphOfBits_take_eq, toBits_register]
  simp only [← length_graphBits (pull .inl x), List.take_left, graphOfBits_graphBits]

theorem drop_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    (toBits (push (registerEquiv s).toEmbedding x)).drop (graphDim T) = toBits (pull .inr x) := by
  rw [toBits_register]
  simp only [← length_graphBits (pull .inl x), List.drop_left]

/-- The source typed decision predicate with its entire-answer cutoff. -/
def typedPredicate (n : ℕ) :
    Question T (Fin (S.dim n)) → Question T (Fin (S.dim n)) →
      MIPRE.Verifier.Answers (C.outer n) → MIPRE.Verifier.Answers (C.outer n) → Bool :=
  fun x y a b => @decide
    (a.val.length ≤ C.inner n ∧ b.val.length ≤ C.inner n ∧
      D.Accepts n x.1 (toBits x.2) y.1 (toBits y.2) a.val b.val) (Classical.propDecidable _)

/-- On the outer answer alphabet, the compiled predicate is exactly the
already-formalized finite detyping predicate, on every pair of questions. -/
theorem bounded_acceptance (hD : D.Total) (n : ℕ)
    (x y : Coord T (Fin (S.dim n)) → 𝔽₂)
    (a b : MIPRE.Verifier.Answers (C.outer n)) :
    @decide ((decider E S D C).Accepts n
      (toBits (push (registerEquiv (S.dim n)).toEmbedding x))
      (toBits (push (registerEquiv (S.dim n)).toEmbedding y)) a.val b.val)
      (Classical.propDecidable _) =
    Detyping.accepts E (typedPredicate S D C n) x y a b := by
  classical
  rw [accepts_selected]
  have h := accepts_iff E S D C hD n
    (toBits (push (registerEquiv (S.dim n)).toEmbedding x))
    (toBits (push (registerEquiv (S.dim n)).toEmbedding y)) a.val b.val
  simp only [length_toBits, graphOfBits_register, drop_register,
    a.property, b.property, true_and] at h
  simp only [h]
  cases selectedEdge E (pull .inl x) (pull .inl y) <;> simp [typedPredicate]

/-- In particular, a genuine edge preserves the source typed acceptance law and cutoff. -/
theorem bounded_acceptance_edge (hD : D.Total) (n : ℕ)
    (x y : Question T (Fin (S.dim n))) (hE : E x.1 y.1)
    (a b : MIPRE.Verifier.Answers (C.outer n)) :
    @decide ((decider E S D C).Accepts n
      (toBits (push (registerEquiv (S.dim n)).toEmbedding (question E false x)))
      (toBits (push (registerEquiv (S.dim n)).toEmbedding (question E true y))) a.val b.val)
      (Classical.propDecidable _) = typedPredicate S D C n x y a b := by
  rw [bounded_acceptance E S D C hD, accepts_question E _ x y hE]

/-- Predicate equality for the actual ambient verifier's finite game. -/
theorem verifier_game_D (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (x y : Coord T (Fin (S.dim n)) → 𝔽₂)
    (a b : MIPRE.Verifier.Answers (C.outer n)) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).D
      (push (registerEquiv (S.dim n)).toEmbedding x)
      (push (registerEquiv (S.dim n)).toEmbedding y) a b =
      Detyping.accepts E (typedPredicate S D C n) x y a b :=
  bounded_acceptance E S D C hD n x y a b

end MIPRE.CL.Detyping.DeciderProgram
