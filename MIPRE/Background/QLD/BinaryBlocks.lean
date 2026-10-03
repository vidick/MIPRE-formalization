/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.QLD.CLBinary
public import MIPRE.Foundations.Introspection.BinaryBlockProg
public import MIPRE.Foundations.Repeat.Bits

@[expose] public section

/-! # The sampler's actual numbered binary field blocks

The fixed block programs convert exactly between the numbered binary vector
used by `binaryPresentation` and canonical Shoup field rows in the fixed order
`uX`, `uZ`, seed, direction, `rX`, `rZ`. The field basis is the effective
self-dual normal basis, not the computational polynomial basis.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false

/-- Canonical field rows in the explicit ambient coordinate order. -/
def numberedRows {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) : List BitStr :=
  List.ofFn (fun i => E.toBits (x ((coordNumbering m).symm i)))

theorem numberedRows_length {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    (numberedRows E x).length = 3 * m + 3 := List.length_ofFn

theorem numberedRows_getD {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier)
    (c : Coord m) :
    (numberedRows E x).getD (coordNumbering m c).val [] = E.toBits (x c) := by
  simp only [numberedRows, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    (coordNumbering m c).isLt, dite_true, Option.getD_some, Fin.eta,
    Equiv.symm_apply_apply]

theorem numberedRows_eq_vecBits {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    numberedRows E x = E.vecBits (fun i => x ((coordNumbering m).symm i)) := by
  simp only [numberedRows, BinField.vecBits, List.map_ofFn, Function.comp_def]

/-- Exact list order for an arbitrary binary basis: coordinate-major, followed
by the basis bits of that coordinate. -/
theorem binaryVectorEquiv_bits {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (b : Module.Basis (Fin k) (ZMod 2) F) (x : Coord m → F) :
    CL.toBits (binaryVectorEquiv b x) =
      (List.ofFn (fun i : Fin (3 * m + 3) =>
        vectorBits (b.equivFun (x ((coordNumbering m).symm i))))).flatten := by
  unfold CL.toBits vectorBits
  rw [CL.ofFn_eq_flatten_blocks]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he := binaryVectorEquiv_apply b x ((coordNumbering m).symm i) j
  simp only [binaryCoordEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map, Equiv.apply_symm_apply, Equiv.refl_apply] at he
  rw [he]
  rfl

/-- The executable encoder produces the exact numbered CL bit vector. -/
theorem encodeBlocksProg_numberedRows (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {m : ℕ} [NeZero m] (x : Coord m → (shoupBinField k hk).carrier) :
    encodeBlocksProg (unary k, numberedRows (shoupBinField k hk) x) =
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x) := by
  rw [numberedRows_eq_vecBits, encodeBlocksProg_correct k hk hodd, binaryVectorEquiv_bits]

/-- The executable decoder returns the exact canonical field row at each
numbered coordinate of the self-dual downsized vector. -/
theorem decodeBlocksProg_binaryVector (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {m : ℕ} [NeZero m] (x : Coord m → (shoupBinField k hk).carrier) :
    decodeBlocksProg (unary (3 * m + 3), unary k,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      numberedRows (shoupBinField k hk) x := by
  rw [binaryVectorEquiv_bits, decodeBlocksProg_correct k hk hodd, numberedRows_eq_vecBits]

/-- A full-length raw CL bit string is interpreted by the actual inverse
binary coordinate map; no assumption that its bits are polynomial coordinates
is made. -/
theorem decodeBlocksProg_ofBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {m : ℕ} [NeZero m] (z : BitStr) (hz : z.length = (3 * m + 3) * k) :
    decodeBlocksProg (unary (3 * m + 3), unary k, z) =
      numberedRows (shoupBinField k hk)
        ((binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
          (CL.ofBits ((3 * m + 3) * k) z)) := by
  have he := decodeBlocksProg_binaryVector k hk hodd
    ((binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
      (CL.ofBits ((3 * m + 3) * k) z))
  simpa only [LinearEquiv.apply_symm_apply, CL.toBits_ofBits hz] using he

end MIPRE.QLD.PauliCL
end

end
