/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingQueries
import MIPRE.Foundations.CL.Sampler
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Contiguous graph and content encodings for detyping

The abstract sum of graph and content registers is numbered with the graph
first. Vector encodings are consequently ordinary concatenations of bit lists.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical
set_option linter.unusedSectionVars false

variable {T : Type*} [Fintype T] [DecidableEq T]

abbrev graphDim (T : Type*) [Fintype T] := Fintype.card (Graph.Coord T)

def graphEquiv : Graph.Coord T ≃ Fin (graphDim T) := Fintype.equivFin _

def registerEquiv (s : ℕ) : Coord T (Fin s) ≃ Fin (graphDim T + s) :=
  (Equiv.sumCongr graphEquiv (Equiv.refl _)).trans finSumFinEquiv

def graphBits (g : Graph.Coord T → 𝔽₂) : Cost.BitStr :=
  toBits (push graphEquiv.toEmbedding g)

def graphOfBits (b : Cost.BitStr) : Graph.Coord T → 𝔽₂ :=
  pull graphEquiv.toEmbedding (ofBits (graphDim T) b)

@[simp] theorem graphOfBits_graphBits (g : Graph.Coord T → 𝔽₂) :
    graphOfBits (graphBits g) = g := by
  simp [graphBits, graphOfBits]

@[simp] theorem length_graphBits (g : Graph.Coord T → 𝔽₂) :
    (graphBits g).length = graphDim T := length_toBits _

theorem ofBits_take_eq (d : ℕ) (l : Cost.BitStr) : ofBits d (l.take d) = ofBits d l := by
  funext i
  simp [ofBits, List.getD_eq_getElem?_getD, i.isLt]

theorem graphOfBits_take_eq (l : Cost.BitStr) :
    graphOfBits (T := T) (l.take (graphDim T)) = graphOfBits l := by
  exact congrArg (pull graphEquiv.toEmbedding) (ofBits_take_eq (graphDim T) l)

theorem push_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    push (registerEquiv s).toEmbedding x =
      Fin.append (push graphEquiv.toEmbedding (pull .inl x)) (pull .inr x) := by
  funext i
  obtain ⟨q, rfl⟩ := (registerEquiv (T := T) s).surjective i
  calc _ = x q := push_apply (registerEquiv s).toEmbedding x q
    _ = _ := by
      cases q with
      | inl q =>
        simp only [registerEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
          Sum.map_inl, finSumFinEquiv_apply_left, Fin.append_left]
        exact (push_apply graphEquiv.toEmbedding (pull .inl x) q).symm
      | inr q => simp [registerEquiv, pull]

theorem toBits_append {m n : ℕ} (x : Fin m → 𝔽₂) (y : Fin n → 𝔽₂) :
    toBits (Fin.append x y) = toBits x ++ toBits y := by
  unfold toBits
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp
  · intro j; simp

/-- Numbering the sum registers is exactly concatenation of their bit strings. -/
theorem toBits_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    toBits (push (registerEquiv s).toEmbedding x) =
      graphBits (pull .inl x) ++ toBits (pull .inr x) := by
  rw [push_register, toBits_append]
  rfl

theorem bits_split (s : ℕ) (z : Fin (graphDim T + s) → 𝔽₂) :
    toBits z =
      graphBits (pull .inl (pull (registerEquiv s).toEmbedding z)) ++
        toBits (pull .inr (pull (registerEquiv s).toEmbedding z)) := by
  rw [← toBits_register]
  congr 1
  funext i
  obtain ⟨q, rfl⟩ := (registerEquiv (T := T) s).surjective i
  exact (push_apply (registerEquiv s).toEmbedding
    (pull (registerEquiv s).toEmbedding z) q).symm

/-- The graph parser reads exactly the graph part of every well-formed vector. -/
theorem graphOfBits_take (s : ℕ) (z : Fin (graphDim T + s) → 𝔽₂) :
    graphOfBits ((toBits z).take (graphDim T)) =
      pull .inl (pull (registerEquiv s).toEmbedding z) := by
  rw [bits_split s z]
  simp only [← length_graphBits (pull .inl (pull (registerEquiv s).toEmbedding z)),
    List.take_left, graphOfBits_graphBits]

/-- The content parser reads exactly the independent content part. -/
theorem ofBits_drop (s : ℕ) (z : Fin (graphDim T + s) → 𝔽₂) :
    ofBits s ((toBits z).drop (graphDim T)) =
      pull .inr (pull (registerEquiv s).toEmbedding z) := by
  rw [bits_split s z]
  simp only [← length_graphBits (pull .inl (pull (registerEquiv s).toEmbedding z)),
    List.drop_left, ofBits_toBits]

/-- The actual numbered detyped CL presentation used by the machine interface. -/
def numbered {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) : CLFun 𝔽₂ (Fin (graphDim T + s)) (ℓ + 2) :=
  (presentation E w.toBool P).embed (registerEquiv s).toEmbedding

theorem numbered_exactlyOn {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ) :
    (numbered E w P).ExactlyOn univ := by
  have h := (presentation_exactlyOn E w.toBool P hP hℓ).embed (registerEquiv s).toEmbedding
  simpa [numbered] using h

end MIPRE.CL.Detyping
