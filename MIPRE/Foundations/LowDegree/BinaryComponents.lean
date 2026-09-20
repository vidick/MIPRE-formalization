/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryGroupAlgebra
import MIPRE.Foundations.LowDegree.IdempotentSplit

/-! # Primitive components computed by fixed-space separation -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The computed generators in their fixed deterministic order. -/
def groupFixedFamily (k : ℕ) [NeZero k] : List (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
  List.ofFn (groupFixedGenerator k)

/-- Separate the components directly in the cyclic algebra, starting with the unit. -/
def groupComponents (k : ℕ) [NeZero k] : List (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
  splitAllComponents [1] (groupFixedFamily k)

theorem groupFixedFamily_idempotent (k : ℕ) [NeZero k] :
    ∀ b ∈ groupFixedFamily k, b * b = b := by
  intro b hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  exact groupFixedGenerator_idempotent k j

theorem groupFixedFamily_spans (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (hz : z * z = z) :
    z ∈ Submodule.span (ZMod 2) {b | b ∈ groupFixedFamily k} := by
  have hs : {b | b ∈ groupFixedFamily k} = Set.range (groupFixedGenerator k) := by
    ext b
    simp [groupFixedFamily]
  rw [hs]
  exact groupFixedGenerator_spans k z hz

private theorem unitComponentFamily (k : ℕ) [NeZero k] :
    ComponentFamily ([1] : List (AddMonoidAlgebra (ZMod 2) (Fin k))) := by
  constructor <;> simp

theorem groupComponents_family (k : ℕ) [NeZero k] : ComponentFamily (groupComponents k) :=
  (unitComponentFamily k).splitAll (groupFixedFamily_idempotent k)

theorem groupComponents_primitive (k : ℕ) [NeZero k] :
    ∀ e ∈ groupComponents k, PrimitiveBinaryComponent e :=
  splitAllComponents_primitive (unitComponentFamily k) (groupFixedFamily_idempotent k)
    (groupFixedFamily_spans k)

theorem groupAlgebra_finrank (k : ℕ) :
    Module.finrank (ZMod 2) (AddMonoidAlgebra (ZMod 2) (Fin k)) = k := by
  rw [(groupCoordinates k).finrank_eq]
  simp

/-- The computation has at most `k` nonzero components, despite repeatedly splitting them. -/
theorem groupComponents_length_le (k : ℕ) [NeZero k] : (groupComponents k).length ≤ k := by
  haveI : Module.Finite (ZMod 2) (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
    Module.Finite.equiv (groupCoordinates k).symm
  simpa only [groupAlgebra_finrank] using (groupComponents_family k).length_le_finrank

/-- Canonical zero of the same raw width. -/
def zeroRow (v : BitStr) : BitStr := v.map (fun _ => false)

theorem zeroRow_vectorBits {k : ℕ} (v : Fin k → ZMod 2) :
    zeroRow (vectorBits v) = vectorBits (0 : Fin k → ZMod 2) := by
  simp [zeroRow, vectorBits, bit]

theorem vectorBits_injective {k : ℕ} : Function.Injective (vectorBits (n := k)) := by
  intro v w h
  have he := congrArg (vectorValue k) h
  simpa using he

def nonzeroRow (v : BitStr) : Bool := decide (v ≠ zeroRow v)

@[simp] theorem nonzeroRow_zero {k : ℕ} :
    nonzeroRow (vectorBits (0 : Fin k → ZMod 2)) = false := by
  simp [nonzeroRow, zeroRow_vectorBits]

theorem nonzeroRow_groupBits (k : ℕ)
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    nonzeroRow (vectorBits (groupCoordinates k z)) = decide (z ≠ 0) := by
  unfold nonzeroRow
  rw [zeroRow_vectorBits, ← (groupCoordinates k).map_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr ((vectorBits_injective (k := k)).eq_iff.trans
    (groupCoordinates k).injective.eq_iff)

/-- One raw split uses cyclic multiplication and XOR, then omits zero vectors. -/
def splitBits (e b : BitStr) : List BitStr :=
  let x := groupMulBitsProg (e, b)
  [x, BinaryPolynomial.xorBits e x].filter nonzeroRow

theorem splitBits_encoding {k : ℕ} [NeZero k]
    (e b : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    splitBits (vectorBits (groupCoordinates k e)) (vectorBits (groupCoordinates k b)) =
      (splitComponent e b).map (fun z => vectorBits (groupCoordinates k z)) := by
  unfold splitBits
  rw [groupMulBitsProg_correct]
  dsimp only
  rw [xorBits_vectorBits, ← map_add]
  have hsecond : e + e * b = e * (1 - b) := by
    rw [CharTwo.sub_eq_add, mul_add, mul_one]
  rw [hsecond]
  unfold splitComponent
  by_cases h₁ : e * b = 0 <;> by_cases h₂ : e * (1 - b) = 0 <;>
    simp [List.filter_cons, nonzeroRow_groupBits, h₁, h₂]

/-- Raw convolution always has the width of its first operand, including malformed inputs. -/
theorem groupMulBitsProg_length (e b : BitStr) : (groupMulBitsProg (e, b)).length = e.length := by
  change (applyBits (circulantBitsProg e) b).length = _
  simp only [applyBits, List.length_map]
  change (transposeBits (unary e.length).length _).length = _
  simp [transposeBits]

theorem splitBits_width (e b : BitStr) : ∀ x ∈ splitBits e b, x.length = e.length := by
  intro x hx
  have hm := (List.mem_filter.mp hx).1
  rcases List.mem_cons.mp hm with rfl | hm
  · exact groupMulBitsProg_length e b
  · have he := List.mem_singleton.mp hm
    rw [he, BinaryPolynomial.length_xorBits, groupMulBitsProg_length, Nat.min_self]

/-- Raw refinement is clipped to the unary dimension; on valid components this clip is inert. -/
def splitBitsCapped (u : Unary) (l : List BitStr) (b : BitStr) : List BitStr :=
  (l.flatMap (fun e => splitBits e b)).take u.length

theorem splitBitsCapped_encoding {k : ℕ} [NeZero k]
    (l : List (AddMonoidAlgebra (ZMod 2) (Fin k))) (hl : ComponentFamily l)
    (b : AddMonoidAlgebra (ZMod 2) (Fin k)) (hb : b * b = b) :
    splitBitsCapped (unary k) (l.map (fun z => vectorBits (groupCoordinates k z)))
      (vectorBits (groupCoordinates k b)) =
      (splitComponents l b).map (fun z => vectorBits (groupCoordinates k z)) := by
  have he : (l.map (fun z => vectorBits (groupCoordinates k z))).flatMap
      (fun e => splitBits e (vectorBits (groupCoordinates k b))) =
      (splitComponents l b).map (fun z => vectorBits (groupCoordinates k z)) := by
    simp only [List.flatMap_map, splitBits_encoding, splitComponents, List.map_flatMap]
  unfold splitBitsCapped
  rw [he, length_unary, List.take_of_length_le]
  haveI : Module.Finite (ZMod 2) (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
    Module.Finite.equiv (groupCoordinates k).symm
  simpa only [List.length_map, groupAlgebra_finrank] using (hl.split hb).length_le_finrank

end MIPRE.LowDegree.BinaryLinear

end
