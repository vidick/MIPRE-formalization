/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.ZPC
public import MIPRE.Foundations.SAT.FieldCoordinates

@[expose] public section

/-!
# Linear checks on answer bits, and their constraint vectors

A tailored game's constraint is a bit vector `c` of length `N + 1`, satisfied by the answer bits
`z` of length `N` when `⟨c, (z, 1)⟩ = 0` (`MIPRE.Tailored.Satisfies`). This file produces such
vectors from *linear checks*: an `F₂`-linear functional `φ` on `F₂^N` and a target `c`, read as
the equation `φ(z) = c`. The constraint of a check (`LinCheck.toCon`) lists the values of `φ`
on the unit vectors, then `c`; `satisfies_toCon_iff` is the statement that it is satisfied
exactly when `φ(z) = c`. So a decision procedure that is a conjunction of affine equations in
the answer bits becomes a constraint list by writing down the functionals, with no coefficient
bookkeeping: the coefficients are whatever the functional gives on the unit vectors, which a
program computes by evaluating the check at those vectors.

The functionals are built from two readers: `getv l`, the bit at position `l`, and, for the
effective binary field `shoupBinField k hk`, `fldAt o`, the field element whose canonical `k`
bits start at position `o` (`MIPRE.SAT.shoupCoordinateEquiv`, under which `toBits` is
`F₂`-linear). An equation `E(z) = κ` between field elements, `E` an `F₂`-linear map to the
field, is the `k` checks of its coordinates (`fieldChecks`, `forall_fieldChecks_iff`).

`reject` is the check `0 = 1`, whose constraint is `rejectConstraint N`.
-/

noncomputable section

namespace MIPRE.Tailored.Intro

open Cost MIPRE.LowDegree MIPRE.LowDegree.BinaryLinear MIPRE.SAT

/-- A linear check on `N` answer bits: the equation `φ(z) = c` over `F₂`. -/
structure LinCheck (N : ℕ) where
  /-- The linear part. -/
  φ : (Fin N → ZMod 2) →ₗ[ZMod 2] ZMod 2
  /-- The target. -/
  c : ZMod 2

/-- The answer bits as a vector of `F₂^N` (bits beyond the string read `0`). -/
def bitVec (N : ℕ) (z : BitStr) : Fin N → ZMod 2 := fun l => ofBool (z.getD l false)

namespace LinCheck

variable {N : ℕ}

/-- The check holds at a vector. -/
def Holds (χ : LinCheck N) (v : Fin N → ZMod 2) : Prop := χ.φ v = χ.c

/-- The constraint vector of a check: the functional on the unit vectors, then the target. -/
def toCon (χ : LinCheck N) : BitStr :=
  List.ofFn (fun l : Fin N => bit (χ.φ fun j => if l = j then 1 else 0)) ++ [bit χ.c]

@[simp] theorem length_toCon (χ : LinCheck N) : χ.toCon.length = N + 1 := by
  simp [toCon]

/-- The check `0 = 1`, which no vector satisfies. -/
def reject (N : ℕ) : LinCheck N := ⟨0, 1⟩

theorem not_holds_reject (v : Fin N → ZMod 2) : ¬(reject N).Holds v := by
  simp [Holds, reject]

@[simp] theorem holds_reject (v : Fin N → ZMod 2) : (reject N).Holds v ↔ False :=
  iff_false_intro (not_holds_reject v)

theorem toCon_reject : (reject N).toCon = rejectConstraint N := by
  simp [toCon, reject, rejectConstraint, bit, List.ofFn_const]

end LinCheck

theorem ofBool_dotBit {n : ℕ} (α a : Fin n → Bool) :
    (ofBool (dotBit α a) : ZMod 2) = ∑ i, ofBool (a i) * ofBool (α i) := by
  induction n with
  | zero => simp [ofBool]
  | succ n ih =>
    rw [dotBit_succ, ofBool_xor, ofBool_and, ih, Fin.sum_univ_succ, mul_comm]

/-- **The constraint of a check is satisfied exactly when the check holds.** -/
theorem satisfies_toCon_iff {N : ℕ} (χ : LinCheck N) (z : BitStr) (hz : z.length = N) :
    Satisfies χ.toCon (z ++ [true]) ↔ χ.Holds (bitVec N z) := by
  subst hz
  have hz : z = List.ofFn (fun l : Fin z.length => z.getD l false) := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp [List.getD_eq_getElem?_getD]
  have key := satisfies_ofFn_iff
    (fun l : Fin z.length => bit (χ.φ fun j => if l = j then 1 else 0))
    (fun l : Fin z.length => z.getD l false) (Fin.elim0 : Fin 0 → Bool) Fin.elim0 (bit χ.c)
  simp only [List.ofFn_zero, List.append_nil, dotBit_zero, Bool.xor_false] at key
  rw [← hz] at key
  unfold LinCheck.toCon
  rw [key, LinCheck.Holds]
  constructor
  · intro h
    have h' := congrArg (ofBool : Bool → ZMod 2) h
    rw [ofBool_bit, ofBool_dotBit] at h'
    rw [← h', LinearMap.pi_apply_eq_sum_univ χ.φ (bitVec z.length z)]
    simp [bitVec, smul_eq_mul]
  · intro h
    apply ofBool_injective
    rw [ofBool_bit, ofBool_dotBit, ← h, LinearMap.pi_apply_eq_sum_univ χ.φ (bitVec z.length z)]
    simp [bitVec, smul_eq_mul]

/-! ## Readers -/

/-- The bit at position `l`, `0` beyond `N`. -/
def getv (N l : ℕ) : (Fin N → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  if h : l < N then LinearMap.proj (⟨l, h⟩ : Fin N) else 0

theorem getv_bitVec {N : ℕ} (z : BitStr) (hz : z.length ≤ N) (l : ℕ) :
    getv N l (bitVec N z) = ofBool (z.getD l false) := by
  unfold getv
  split_ifs with h
  · rfl
  · simp [ofBool, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show z.length ≤ l by omega)]

section Field

variable (k : ℕ) (hk : 1 ≤ k)

/-- The field element whose canonical bits start at position `o`. -/
def fldAt (N o : ℕ) : (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField k hk).carrier :=
  (shoupCoordinateEquiv k hk).symm.toLinearMap ∘ₗ LinearMap.pi fun i : Fin k => getv N (o + i)

variable {k hk}

/-- `fldAt o` reads the field element `x` when the bits from `o` on are those of `x`. -/
theorem fldAt_eq {N o : ℕ} (v : Fin N → ZMod 2) (x : (shoupBinField k hk).carrier)
    (h : ∀ i < k, getv N (o + i) v = ofBool (((shoupBinField k hk).toBits x).getD i false)) :
    fldAt k hk N o v = x := by
  apply (shoupCoordinateEquiv k hk).injective
  simp only [fldAt, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, shoupCoordinateEquiv_apply]
  funext i
  simp [LinearMap.pi_apply, vectorValue, h i i.2]

variable (k hk)

/-- The `k` coordinate checks of the field equation `E(z) = κ`. -/
def fieldChecks {N : ℕ} (E : (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField k hk).carrier)
    (κ : (shoupBinField k hk).carrier) : List (LinCheck N) :=
  List.ofFn fun i : Fin k =>
    ⟨LinearMap.proj i ∘ₗ (shoupCoordinateEquiv k hk).toLinearMap ∘ₗ E,
      shoupCoordinateEquiv k hk κ i⟩

variable {k hk}

/-- **The coordinate checks hold exactly when the field equation does.** -/
theorem forall_fieldChecks_iff {N : ℕ}
    (E : (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField k hk).carrier)
    (κ : (shoupBinField k hk).carrier) (v : Fin N → ZMod 2) :
    (∀ χ ∈ fieldChecks k hk E κ, χ.Holds v) ↔ E v = κ := by
  simp only [fieldChecks, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    LinCheck.Holds, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.coe_proj, Function.eval]
  constructor
  · intro h
    apply (shoupCoordinateEquiv k hk).injective
    funext i
    exact h i
  · rintro h i
    rw [h]

end Field

end MIPRE.Tailored.Intro

end

end
