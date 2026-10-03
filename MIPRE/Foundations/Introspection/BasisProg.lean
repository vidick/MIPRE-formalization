/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.SAT.EffectiveNormalBasis
public import MIPRE.Foundations.SAT.BasisTransport

@[expose] public section

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

end MIPRE.Introspection.BasisProgram
end

end
