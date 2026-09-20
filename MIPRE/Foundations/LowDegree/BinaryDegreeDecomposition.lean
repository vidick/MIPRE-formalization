/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.UnaryPrimePower
import MIPRE.Foundations.LowDegree.BinaryDegreeFactors

/-! # Executable prime-power decomposition of a unary requested degree -/

noncomputable section

namespace MIPRE.LowDegree.DegreeArithmetic

open Cost Cost.PolyTimeFun

/-- Enumerate all candidate prime indices in ascending order. -/
def ascendingUnary (u : Unary) : List Unary := (descendingUnary u).reverse

private theorem descendingUnary_cons (u : Unary) :
    descendingUnary (() :: u) = (() :: u) :: descendingUnary u := by
  exact recordIterates_cons List.tail (() :: u) (() :: u)

/-- The enumeration is the bounded canonical unary list from zero to the input. -/
theorem ascendingUnary_eq (u : Unary) :
    ascendingUnary u = List.ofFn (fun i : Fin (u.length + 1) => unary (i : ℕ)) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    cases x
    rw [ascendingUnary, descendingUnary_cons, List.reverse_cons]
    change ascendingUnary u ++ [() :: u] = _
    rw [ih]
    conv_rhs => rw [List.ofFn_succ']
    simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
    have hu : unary (u.length + 1) = () :: u := by
      change () :: unary u.length = () :: u
      rw [unary_length]
    simp only [List.length_cons]
    rw [hu]

/-- A polynomial-time ascending unary enumeration. -/
def ascendingUnaryProg : PolyTimeFun Unary (List Unary) := PolyTimeFun.reverse.comp descendingUnaryProg

@[simp] theorem ascendingUnaryProg_apply (u : Unary) : ascendingUnaryProg u = ascendingUnary u := rfl

/-- Prime indices paired with their maximal dividing prime power; neutral entries have power one. -/
def primePowerPairs (u : Unary) : List (Unary × Unary) :=
  (ascendingUnary u).map (fun q => (q, primePowerUnary u q))

/-- One globally polynomial-time prime-power decomposition program. -/
def primePowerPairsProg : PolyTimeFun Unary (List (Unary × Unary)) :=
  (mapWith (fst.pair (primePowerUnaryProg.comp (snd.pair fst)))).comp
    (ascendingUnaryProg.pair (PolyTimeFun.id _))

@[simp] theorem primePowerPairsProg_apply (u : Unary) : primePowerPairsProg u = primePowerPairs u := rfl

/-- The executing decomposition agrees exactly with the mathematical prime-power factors. -/
theorem primePowerPairs_eq (n : ℕ) :
    primePowerPairs (unary n) = List.ofFn (fun i : Fin (n + 1) =>
      (unary (i : ℕ), unary ((i : ℕ) ^ n.factorization (i : ℕ)))) := by
  rw [primePowerPairs, ascendingUnary_eq, length_unary, List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  rw [primePowerUnary_correct]

/-- Decoding the listed powers gives the factor list whose product is the requested degree. -/
theorem primePowerPairs_degrees (n : ℕ) :
    (primePowerPairs (unary n)).map (fun s => s.2.length) = BinaryDegreeFactors.degreeFactors n := by
  rw [primePowerPairs_eq, List.map_ofFn, BinaryDegreeFactors.degreeFactors]
  congr 1
  funext i
  exact length_unary _

/-- Every positive degree is the product of the computed prime-power contributions. -/
theorem primePowerPairs_prod (n : ℕ) (hn : 0 < n) :
    ((primePowerPairs (unary n)).map (fun s => s.2.length)).prod = n := by
  rw [primePowerPairs_degrees]
  exact BinaryDegreeFactors.degreeFactors_prod n hn

/-- Computed prime-power contributions are pairwise coprime. -/
theorem primePowerPairs_pairwise (n : ℕ) :
    ((primePowerPairs (unary n)).map (fun s => s.2.length)).Pairwise Nat.Coprime := by
  rw [primePowerPairs_degrees]
  exact BinaryDegreeFactors.degreeFactors_pairwise n

end MIPRE.LowDegree.DegreeArithmetic

end
