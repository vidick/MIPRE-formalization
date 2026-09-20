/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.SelfDualize
import MIPRE.Foundations.LowDegree.Encoding
import MIPRE.Foundations.Cost.Fold

/-!
# A polynomial-time square root in the binary cyclic group algebra

For an odd-length coefficient vector, reading the doubled indices means reading
the even positions followed by the odd positions. Splitting those two lists and
appending them is polynomial-time in the ambient cost model. This implements the
square-root step of self-dualization; it does not compute the inverse Gram element
or the initial normal basis.
-/

namespace MIPRE.LowDegree

open Cost

variable {α : Type*}

/-- Split a list into its even-position and odd-position subsequences. -/
def splitParity : List α → List α × List α
  | [] => ([], [])
  | a :: l => (a :: (splitParity l).2, (splitParity l).1)

theorem splitParity_eq_foldr (l : List α) :
    splitParity l = l.foldr (fun a s => (a :: s.2, s.1)) ([], []) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [splitParity, ih]

theorem length_splitParity (l : List α) :
    (splitParity l).1.length = (l.length + 1) / 2 ∧
    (splitParity l).2.length = l.length / 2 := by
  induction l with
  | nil => simp [splitParity]
  | cons a l ih =>
    change (splitParity l).2.length + 1 = (l.length + 1 + 1) / 2 ∧
      (splitParity l).1.length = (l.length + 1) / 2
    rw [ih.1, ih.2]
    constructor <;> omega

theorem getD_splitParity (l : List α) (fallback : α) (n : ℕ) :
    (splitParity l).1.getD n fallback = l.getD (2 * n) fallback ∧
    (splitParity l).2.getD n fallback = l.getD (2 * n + 1) fallback := by
  induction l generalizing n with
  | nil => simp [splitParity]
  | cons a l ih =>
    constructor
    · cases n with
      | zero => simp [splitParity]
      | succ n =>
        simpa [splitParity, Nat.mul_succ, Nat.add_assoc]
          using (ih n).2
    · simpa [splitParity] using (ih n).1

/-- The doubled-index permutation for an odd-length coefficient vector. -/
def rootBits (l : List α) : List α := (splitParity l).1 ++ (splitParity l).2

@[simp] theorem length_rootBits (l : List α) : (rootBits l).length = l.length := by
  have h := length_splitParity l
  simp only [rootBits, List.length_append, h.1, h.2]
  omega

theorem getD_rootBits (l : List α) (fallback : α) (hodd : Odd l.length)
    {i : ℕ} (hi : i < l.length) :
    (rootBits l).getD i fallback = l.getD ((i + i) % l.length) fallback := by
  obtain ⟨r, hr⟩ := hodd
  have he : (splitParity l).1.length = r + 1 := by
    have := (length_splitParity l).1
    omega
  by_cases hsmall : i < r + 1
  · rw [rootBits, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
    change (splitParity l).1.getD i fallback = _
    rw [(getD_splitParity l fallback i).1, Nat.mod_eq_of_lt (by omega), two_mul]
  · rw [rootBits, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    change (splitParity l).2.getD (i - (splitParity l).1.length) fallback = _
    rw [(getD_splitParity l fallback _).2, he]
    congr 1
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

section Programs

variable [SizedEncoding α]

private noncomputable def splitParityStep :
    PolyTimeFun ((List α × List α) × α) (List α × List α) :=
  (PolyTimeFun.cons PolyTimeFun.snd (PolyTimeFun.snd.comp PolyTimeFun.fst)).pair
    (PolyTimeFun.fst.comp PolyTimeFun.fst)

private theorem splitParityStep_size (s : List α × List α) (a : α) :
    esize (splitParityStep (s, a)) ≤ esize s +
      (Polynomial.X + 1 : Polynomial ℕ).eval (esize a) := by
  rcases s with ⟨e, o⟩
  simp [splitParityStep, esize_prod, esize_list_cons]
  omega

/-- The parity split, with an ambient program and polynomial cost proof. -/
noncomputable def splitParityProg : PolyTimeFun (List α) (List α × List α) :=
  PolyTimeFun.congr
    ((PolyTimeFun.foldlAdd splitParityStep (Polynomial.X + 1) splitParityStep_size).comp
      (PolyTimeFun.reverse.pair (PolyTimeFun.const ([], []))))
    splitParity (by
      intro l
      simp only [PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.reverse_apply,
        PolyTimeFun.const_apply, PolyTimeFun.foldlAdd_apply, List.foldl_reverse]
      exact (splitParity_eq_foldr l).symm)

@[simp] theorem splitParityProg_apply (l : List α) : splitParityProg l = splitParity l := rfl

/-- The coefficient square-root permutation, in polynomial time. -/
noncomputable def rootBitsProg : PolyTimeFun (List α) (List α) :=
  PolyTimeFun.append.comp splitParityProg

@[simp] theorem rootBitsProg_apply (l : List α) : rootBitsProg l = rootBits l := rfl

end Programs

/-- On bit vectors, the ambient running time is polynomial in the vector length. -/
theorem rootBitsProg_time_le : ∃ R : Polynomial ℕ, ∀ l : BitStr,
    ∃ t ≤ R.eval l.length,
      (rootBitsProg (α := Bool)).code.Runs (encode l) (encode (rootBits l)) t := by
  refine ⟨(rootBitsProg (α := Bool)).timeBound.comp (4 * Polynomial.X + 1), fun l => ?_⟩
  obtain ⟨t, ht, hr⟩ := (rootBitsProg (α := Bool)).computes l
  refine ⟨t, ht.trans ?_, hr⟩
  simpa using polynomial_eval_mono (rootBitsProg (α := Bool)).timeBound (esize_bitStr_le l)

section GroupAlgebra

variable {k : ℕ} [NeZero k]

/-- A binary coefficient list interpreted in the cyclic group algebra. -/
noncomputable def groupOfBits (l : BitStr) : AddMonoidAlgebra (ZMod 2) (ZMod k) :=
  .ofCoeff (Finsupp.onFinset Finset.univ (fun i => ofBool (l.getD i.val false))
    (fun i _ => Finset.mem_univ i))

@[simp] theorem coeff_groupOfBits (l : BitStr) (i : ZMod k) :
    (groupOfBits l).coeff i = ofBool (l.getD i.val false) := by
  simp [groupOfBits]

/-- The implemented permutation agrees with the algebraic square-root formula. -/
theorem groupOfBits_rootBits (l : BitStr) (hlen : l.length = k) (hk : Odd k) :
    groupOfBits (k := k) (rootBits l) = binarySquareRoot (groupOfBits l) := by
  apply AddMonoidAlgebra.coeff_injective
  ext i
  simp only [coeff_groupOfBits, coeff_binarySquareRoot]
  congr 1
  have hi : i.val < l.length := by rw [hlen]; exact ZMod.val_lt i
  simpa [ZMod.val_add, hlen] using getD_rootBits l false (hlen ▸ hk) hi

/-- Correctness of the polynomial-time square-root program on odd-length vectors. -/
theorem rootBitsProg_square (l : BitStr) (hlen : l.length = k) (hk : Odd k) :
    groupOfBits (k := k) (rootBitsProg l) * groupOfBits (k := k) (rootBitsProg l) =
      groupOfBits l := by
  rw [rootBitsProg_apply, groupOfBits_rootBits l hlen hk]
  exact binarySquareRoot_mul_self (by simpa using hk) _

end GroupAlgebra

end MIPRE.LowDegree
