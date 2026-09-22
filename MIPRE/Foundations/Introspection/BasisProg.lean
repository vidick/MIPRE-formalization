/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.EffectiveNormalBasis
import MIPRE.Foundations.SAT.BasisTransport

/-! # Executable conversion to the introspection field basis

The sampler's field arithmetic uses canonical Shoup polynomial coordinates,
whereas downsizing uses the constructed self-dual normal basis. These are two
different encodings. The fixed programs below construct that basis from its
unary odd degree and convert in both directions, including row-wise conversion.
No basis matrix is supplied as an oracle or chosen independently of the code.
-/

noncomputable section
namespace MIPRE.Introspection.BasisProgram
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial

/-- Evaluate supplied basis coordinates in the canonical polynomial basis. -/
def fromBasisProg : PolyTimeFun (Unary × List BitStr × BitStr) BitStr :=
  applyBitsProg.comp
    ((transposeBitsProg.comp (fst.pair (fst.comp snd))).pair (snd.comp snd))

theorem fromBasisProg_correct (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    fromBasisProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)),
      vectorBits (b.equivFun a)) = (shoupBinField k hk).toBits a := by
  change applyBits (transposeBits (unary k).length
    (List.ofFn fun i => (shoupBinField k hk).toBits (b i))) (vectorBits (b.equivFun a)) = _
  rw [length_unary, shoupBasisMatrix_encoding, applyBits_matrixBits,
    shoupBasisMatrix_mulVec, shoupCoordinateEquiv_encoding]

/-- Canonical field bits to the effective self-dual basis coordinates. -/
def toSelfDualProg : PolyTimeFun (Unary × BitStr) BitStr :=
  shoupInBasisProg.comp (fst.pair ((shoupSelfDualNormalBasisProg.comp fst).pair snd))

/-- Effective self-dual coordinates to canonical field bits. -/
def fromSelfDualProg : PolyTimeFun (Unary × BitStr) BitStr :=
  fromBasisProg.comp (fst.pair ((shoupSelfDualNormalBasisProg.comp fst).pair snd))

theorem toSelfDualProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (a : (shoupBinField k hk).carrier) :
    toSelfDualProg (unary k, (shoupBinField k hk).toBits a) =
      vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a) := by
  change shoupInBasisProg (unary k, shoupSelfDualNormalBasisProg (unary k),
    (shoupBinField k hk).toBits a) = _
  rw [shoupSelfDualNormalBasisProg_correct k hk hodd, shoupInBasisProg_correct]

theorem fromSelfDualProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (a : (shoupBinField k hk).carrier) :
    fromSelfDualProg (unary k,
      vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a)) =
      (shoupBinField k hk).toBits a := by
  change fromBasisProg (unary k, shoupSelfDualNormalBasisProg (unary k),
    vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a)) = _
  rw [shoupSelfDualNormalBasisProg_correct k hk hodd, fromBasisProg_correct]

/-- The coordinates used in the CL downsizing definition are literally the
coordinates printed by the conversion program. -/
theorem toSelfDualProg_repr (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (a : (shoupBinField k hk).carrier) :
    toSelfDualProg (unary k, (shoupBinField k hk).toBits a) =
      List.ofFn (fun i => bit ((shoupSelfDualNormalBasis k hk hodd).repr a i)) :=
  toSelfDualProg_correct k hk hodd a

theorem fromSelfDualProg_vector (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (v : Fin k → ZMod 2) :
    fromSelfDualProg (unary k, vectorBits v) =
      (shoupBinField k hk).toBits ((shoupSelfDualNormalBasis k hk hodd).equivFun.symm v) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    fromSelfDualProg_correct k hk hodd ((shoupSelfDualNormalBasis k hk hodd).equivFun.symm v)

theorem toSelfDual_fromSelfDual (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (v : BitStr) (hv : v.length = k) :
    toSelfDualProg (unary k, fromSelfDualProg (unary k, v)) = v := by
  rw [← vectorBits_vectorValue k v hv, fromSelfDualProg_vector k hk hodd,
    toSelfDualProg_correct k hk hodd, LinearEquiv.apply_symm_apply]

theorem fromSelfDual_toSelfDual (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (v : BitStr) (hv : v.length = k) :
    fromSelfDualProg (unary k, toSelfDualProg (unary k, v)) = v := by
  have he := shoupBinField_toBits_ofBits k hk v hv
  rw [← he, toSelfDualProg_correct k hk hodd, fromSelfDualProg_correct k hk hodd, he]

/-- Construct the basis once for the row list, then convert each row. -/
def toSelfDualRowsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  (mapWith (shoupInBasisProg.comp
    ((fst.comp snd).pair ((snd.comp snd).pair fst)))).comp
      (snd.pair (fst.pair (shoupSelfDualNormalBasisProg.comp fst)))

def fromSelfDualRowsProg : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  (mapWith (fromBasisProg.comp
    ((fst.comp snd).pair ((snd.comp snd).pair fst)))).comp
      (snd.pair (fst.pair (shoupSelfDualNormalBasisProg.comp fst)))

theorem toSelfDualRowsProg_apply (k : Unary) (vs : List BitStr) :
    toSelfDualRowsProg (k, vs) = vs.map (fun v => toSelfDualProg (k, v)) := rfl

theorem fromSelfDualRowsProg_apply (k : Unary) (vs : List BitStr) :
    fromSelfDualRowsProg (k, vs) = vs.map (fun v => fromSelfDualProg (k, v)) := rfl

theorem toSelfDualRowsProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    toSelfDualRowsProg (unary k, (shoupBinField k hk).vecBits u) =
      List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i))) := by
  simp only [toSelfDualRowsProg_apply, BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact toSelfDualProg_correct k hk hodd (u i)

theorem fromSelfDualRowsProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    fromSelfDualRowsProg (unary k,
      List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))) =
      (shoupBinField k hk).vecBits u := by
  simp only [fromSelfDualRowsProg_apply, BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact fromSelfDualProg_correct k hk hodd (u i)

theorem toSelfDualProg_runs (x : Unary × BitStr) :
    ∃ r ≤ toSelfDualProg.timeBound.eval (esize x),
      toSelfDualProg.code.Runs (encode x) (encode (toSelfDualProg x)) r :=
  toSelfDualProg.computes x

theorem fromSelfDualProg_runs (x : Unary × BitStr) :
    ∃ r ≤ fromSelfDualProg.timeBound.eval (esize x),
      fromSelfDualProg.code.Runs (encode x) (encode (fromSelfDualProg x)) r :=
  fromSelfDualProg.computes x

theorem toSelfDualRowsProg_runs (x : Unary × List BitStr) :
    ∃ r ≤ toSelfDualRowsProg.timeBound.eval (esize x),
      toSelfDualRowsProg.code.Runs (encode x) (encode (toSelfDualRowsProg x)) r :=
  toSelfDualRowsProg.computes x

theorem fromSelfDualRowsProg_runs (x : Unary × List BitStr) :
    ∃ r ≤ fromSelfDualRowsProg.timeBound.eval (esize x),
      fromSelfDualRowsProg.code.Runs (encode x) (encode (fromSelfDualRowsProg x)) r :=
  fromSelfDualRowsProg.computes x

/-- Uniform cost for either conversion on a canonical-width input. -/
theorem basisProg_time_le : ∃ R : Polynomial ℕ, ∀ (k : ℕ) (v : BitStr), v.length = k →
    (∃ r ≤ R.eval k, toSelfDualProg.code.Runs (encode (unary k, v))
      (encode (toSelfDualProg (unary k, v))) r) ∧
    (∃ r ≤ R.eval k, fromSelfDualProg.code.Runs (encode (unary k, v))
      (encode (fromSelfDualProg (unary k, v))) r) := by
  let B : Polynomial ℕ := 6 * X + 3
  refine ⟨(toSelfDualProg.timeBound + fromSelfDualProg.timeBound).comp B, fun k v hv => ?_⟩
  have hs : esize (unary k, v) ≤ B.eval k := by
    have h := esize_bitStr_le v
    rw [hv] at h
    simp only [esize_prod, esize_unary, B, eval_add, eval_mul, eval_ofNat, eval_X]
    omega
  obtain ⟨r, hr, hrun⟩ := toSelfDualProg_runs (unary k, v)
  obtain ⟨s, hs', hsrun⟩ := fromSelfDualProg_runs (unary k, v)
  constructor
  · refine ⟨r, hr.trans ((polynomial_eval_mono _ hs).trans ?_), hrun⟩
    simp only [eval_comp, eval_add]
    omega
  · refine ⟨s, hs'.trans ((polynomial_eval_mono _ hs).trans ?_), hsrun⟩
    simp only [eval_comp, eval_add]
    omega

end MIPRE.Introspection.BasisProgram
end
