/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientTranslation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial

/-! # Translating binary polynomials in a supplied polynomial quotient -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Horner translation by the represented element `a`. -/
def translateBits (p a : BitStr) : BitStr → List BitStr
  | [] => []
  | b :: bs => linearMulCarry p a (if b then oneBits p else zeroBits p) (translateBits p a bs)

@[simp] theorem length_translateBits (p a g : BitStr) :
    (translateBits p a g).length = g.length := by
  induction g <;> simp [translateBits, *]

variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]

abbrev TranslateState := BitStr × BitStr × List BitStr

def translateStep (s : TranslateState) (b : Bool) : TranslateState :=
  (s.1, s.2.1, linearMulCarry s.1 s.2.1 (if b then oneBits s.1 else zeroBits s.1) s.2.2)

theorem fold_translateStep_shape (pre : BitStr) (p a : BitStr) (cs : List BitStr) :
    (pre.foldl translateStep (p, a, cs)).1 = p ∧
      (pre.foldl translateStep (p, a, cs)).2.1 = a ∧
      (pre.foldl translateStep (p, a, cs)).2.2.length = cs.length + pre.length := by
  induction pre generalizing cs with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons b pre ih =>
    have h := ih (linearMulCarry p a (if b then oneBits p else zeroBits p) cs)
    refine ⟨h.1, h.2.1, ?_⟩
    simpa only [List.foldl_cons, translateStep, length_linearMulCarry, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 pre.length] using h.2.2

theorem fold_translateStep_width (pre : BitStr) (p a : BitStr) (cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hc : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (pre.foldl translateStep (p, a, cs)).2.2, c.length ≤ N := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons b pre ih =>
    apply ih
    apply linearMulCarry_width_le _ _ _ _ N _ hc
    cases b <;> simpa using hp

theorem fold_translateStep_eq (bs : BitStr) (p a : BitStr) (cs : List BitStr) :
    bs.foldl translateStep (p, a, cs) =
      (p, a, bs.foldl (fun acc b => linearMulCarry p a
        (if b then oneBits p else zeroBits p) acc) cs) := by
  induction bs generalizing cs with
  | nil => rfl
  | cons b bs ih => exact ih _

def translateStepProg : PolyTimeFun (TranslateState × Bool) TranslateState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let cs := snd.comp (snd.comp fst)
  congr (p.pair (a.pair (linearMulCarryProg.comp
    (p.pair (a.pair ((ite snd (oneBitsProg.comp p) (zeroBitsProg.comp p)).pair cs))))))
    (fun q => translateStep q.1 q.2) (by
      rintro ⟨⟨p, a, cs⟩, b⟩
      change (p, a, linearMulCarryProg (p, a, if b then oneBits p else zeroBits p, cs)) = _
      rw [linearMulCarryProg_apply]
      rfl)

theorem translateStep_bounded :
    FoldBounded translateStepProg (20 * X ^ 2 + 20 * X + 20) := by
  intro bs s pre post heq
  rcases s with ⟨p, a, cs⟩
  let N := esize (bs, p, a, cs)
  have hs : N = esize bs + esize p + esize a + esize cs + 3 := by simp [N, esize_prod]; omega
  have hp : p.length ≤ N := by have := length_le_esize_bitStr p; omega
  have hc : cs.length ≤ N := by have := length_le_esize_list cs; omega
  have hpre : pre.length ≤ N := by
    have := length_le_esize_list bs
    have he := congrArg List.length heq
    simp only [List.length_append] at he
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    omega
  have hshape := fold_translateStep_shape pre p a cs
  have hsize := esize_coefficients_le _ N (fold_translateStep_width pre p a cs N hp hw)
  have hn : (pre.foldl translateStep (p, a, cs)).2.2.length ≤ 2 * N := by omega
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl translateStep (p, a, cs)) ≤ _
  rw [esize_prod, esize_prod, hshape.1, hshape.2.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + (esize a + esize (pre.foldl translateStep (p, a, cs)).2.2 + 1) + 1 ≤
    20 * N ^ 2 + 20 * N + 20
  nlinarith

/-- One globally polynomial-time binary polynomial translation program. -/
def translateBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) (List BitStr) :=
  let scan := foldl translateStepProg (20 * X ^ 2 + 20 * X + 20) translateStep_bounded
  congr ((snd.comp snd).comp (scan.comp
    ((PolyTimeFun.reverse.comp (snd.comp snd)).pair (fst.pair ((fst.comp snd).pair (const []))))))
    (fun q => translateBits q.1 q.2.1 q.2.2) (by
      rintro ⟨p, a, bs⟩
      change (bs.reverse.foldl translateStep (p, a, [])).2.2 = _
      rw [fold_translateStep_eq, List.foldl_reverse]
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        dsimp only at ih ⊢
        simp only [List.foldr_cons, translateBits, ih])

@[simp] theorem translateBitsProg_apply (p a g : BitStr) :
    translateBitsProg (p, a, g) = translateBits p a g := rfl

end MIPRE.LowDegree.BinaryQuotient

end
