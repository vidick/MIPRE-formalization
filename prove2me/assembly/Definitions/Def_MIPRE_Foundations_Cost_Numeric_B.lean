/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Numeric.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Numeric does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

/-!
# The closure library, part IV: binary numbers

Programs on binary numbers presented as bit strings (LSB first, as in `Nat.bits`), used by
the bit-query program of the recursive compression argument: the zero test
(`isZeroProg`) and decrement (`decProg`). Decrement flips the leading `false`s to `true`
and the first `true` to `false`; it may leave a non-canonical representation (trailing
`false`s), which is why the specifications are in terms of the *value* `bitsVal` of a bit
string rather than `Nat.bits`.

Costs: every list walk is quadratic in this model (the loop state is rebuilt each
iteration, copying the tail), so bounds have the form `(iterations + 1) · (S + c)` with `S`
dominating the sizes involved.
-/

namespace MIPRE.Cost

/-! ## Bit strings as data -/

theorem size_encode_replicate_false_append (j : ℕ) (rest : BitStr) :
    (encode (List.replicate j false ++ true :: rest)).size = 2 * j + (encode rest).size + 4 := by
  induction j with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_true, Data.size_nil]
    omega
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_false, Data.size_nil, ih]
    omega

theorem bitsVal_bits (n : ℕ) : bitsVal n.bits = n := Nat.foldr_bit_bits n

theorem bitsVal_eq_zero_iff (l : BitStr) : bitsVal l = 0 ↔ l.any id = false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b <;> simp [Nat.bit_val, ih]

theorem bitsVal_replicate_true_append (j : ℕ) (rest : BitStr) :
    bitsVal (List.replicate j true ++ false :: rest) + 1 =
      bitsVal (List.replicate j false ++ true :: rest) := by
  induction j with
  | zero => simp [Nat.bit_val]
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, bitsVal_cons, Nat.bit_val,
      Bool.toNat_false, Bool.toNat_true]
    omega

/-- A bit string with a `true` bit splits as `false^j ++ true :: rest`. -/
theorem exists_split_of_any (l : BitStr) (h : l.any id = true) :
    ∃ j rest, l = List.replicate j false ++ true :: rest := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    cases b with
    | true => exact ⟨0, l, rfl⟩
    | false =>
      simp only [List.any_cons, id, Bool.false_or] at h
      obtain ⟨j, rest, rfl⟩ := ih h
      exact ⟨j + 1, rest, by simp [List.replicate_succ]⟩

namespace Prog

/-! ## Zero test -/

/-! ## Decrement -/

theorem decBody_wellScoped : decBody.WellScoped 1 := by
  simp [decBody, WellScoped]

theorem decProg_wellScoped : decProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩,
    ⟨⟨Nat.zero_lt_succ 1, decBody_wellScoped.mono (by omega) _⟩,
      revOntoProg_wellScoped.mono (by omega) _⟩⟩

end Prog

/-! ## The next level index -/

theorem size_two_mul_add_one (n : ℕ) : Nat.size (2 * n + 1) = Nat.size n + 1 := by
  rw [← Nat.bit_true_apply, Nat.size_bit (by rw [Nat.bit_true_apply]; omega)]

end MIPRE.Cost
