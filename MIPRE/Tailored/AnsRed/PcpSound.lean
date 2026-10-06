/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.Pcp
public import MIPRE.Tailored.AnsRed.IndicatorProg
public import MIPRE.Foundations.SAT.FiniteCircuitArithmetization
public import MIPRE.Foundations.SAT.Decoupled6
public import Mathlib.Data.List.GetD
public import MIPRE.Tactics

@[expose] public section

/-!
# The soundness of the PCP

The second step of the soundness of prop:completeness_and_soundness_of_PCP_for_V_n, and its
consequence cor:functional_viewpoint_final, clause 2. A PCP satisfying the thirteen checks
identically (`Pcp.Identities`, which `identities_of_dense` derives from passing often) has
assignments that are Boolean on the cube (`isAssignment_of_assignCheck`). Their tables (`res`,
the paper's `Res`) satisfy the system the table of `O` holds (`tableSat_of_identities`) and, read
through the windows, the decoupled 6SAT formula the circuit describes
(`formula6Sat_of_identities`). When the circuit describes the output indicator `L*` through the
windows, the readable tables are then the readable answers and the table of `O` of strings
`L*` accepts, and the linear tables make the game accept (`accepts_of_identities`,
`accepts_of_dense`).
-/

namespace MIPRE.Tailored.AnsRed

open MvPolynomial LowDegree SAT

variable {F : Type*} [Field F] {L : PcpDims}

/-! ## Tables on the Boolean cube -/

/-- The point of the Boolean cube in `F^k` at the binary digits of `c`, least significant first. -/
def bitPt (k c : ℕ) : Fin k → F := pt fun i : Fin k => c.testBit i

open Classical in
/-- **The table of a polynomial on the Boolean cube** (the paper's `Res`): `true` at `c` when the
polynomial is `1` at the binary digits of `c`. -/
noncomputable def res {k : ℕ} (g : MvPolynomial (Fin k) F) (c : ℕ) : Bool :=
  decide (eval (bitPt k c) g = 1)

/-- The table of `g`, as the string of its `2^k` values. -/
noncomputable def resStr {k : ℕ} (g : MvPolynomial (Fin k) F) : Cost.BitStr :=
  List.ofFn fun c : Fin (2 ^ k) => res g c

/-- The table of `g`, valued in `F₂`. -/
noncomputable def resZ {k : ℕ} (g : MvPolynomial (Fin k) F) (c : ℕ) : ZMod 2 := ofBool (res g c)

/-- The table of a window (`lem:ar-window-describer`): at the index whose lowest bit is the parity
and whose other bits are a cell, the tape encoding `π · g(cell)`. -/
noncomputable def winTbl {k : ℕ} (g : MvPolynomial (Fin k) F) (j : ℕ) : Bool :=
  j.testBit 0 && res g (j / 2)

/-- `g` is an **assignment** (Definition def:zero_on_subcube_and_assignments): `0` or `1` at every
point of the Boolean cube. -/
def IsAssignment {k : ℕ} (g : MvPolynomial (Fin k) F) : Prop :=
  ∀ y : Fin k → Bool, eval (pt y) g = 0 ∨ eval (pt y) g = 1

@[simp] theorem length_resStr {k : ℕ} (g : MvPolynomial (Fin k) F) :
    (resStr g).length = 2 ^ k := by
  simp [resStr]

theorem getElem_resStr {k : ℕ} (g : MvPolynomial (Fin k) F) {c : ℕ} (hc : c < (resStr g).length) :
    (resStr g)[c] = res g c := by
  simp [resStr]

theorem ofBool_mul_ofBool (a b : Bool) : (ofBool a : F) * ofBool b = ofBool (a && b) := by
  cases a <;> cases b <;> simp [ofBool]

theorem ofBool_inj {a b : Bool} : (ofBool a : F) = ofBool b ↔ a = b := by
  cases a <;> cases b <;> simp [ofBool]

theorem ofBool_mul_one_sub (b : Bool) : (ofBool b : F) * (1 - ofBool b) = 0 := by
  cases b <;> simp [ofBool]

/-- An assignment takes the value of its table at every point of the cube. -/
theorem eval_bitPt {k : ℕ} {g : MvPolynomial (Fin k) F} (hg : IsAssignment g) (c : ℕ) :
    eval (bitPt k c) g = ofBool (res g c) := by
  unfold res
  rcases hg (fun i : Fin k => c.testBit i) with h | h
  · rw [bitPt, h]; simp [ofBool]
  · rw [bitPt, h]; simp [ofBool]

/-- A certificate sum vanishes on the cube. -/
theorem certSum_pt_eq_zero {k : ℕ} (y : Fin k → Bool) (β : Fin k → MvPolynomial (Fin k) F) :
    ∑ i, pt y i * (1 - pt y i) * eval (pt y) (β i) = (0 : F) :=
  Finset.sum_eq_zero fun i _ => by rw [pt, ofBool_mul_one_sub, zero_mul]

/-- **An assignment check holding on the cube makes an assignment**
(eq:PCP_condition_1, eq:PCP_condition_2): `g (1 - g)` is the certificate sum, `0` on the cube. -/
theorem isAssignment_of_assignCheck {k : ℕ} {g : MvPolynomial (Fin k) F}
    {β : Fin k → MvPolynomial (Fin k) F} (h : ∀ y : Fin k → Bool, AssignCheck g β (pt y)) :
    IsAssignment g := by
  intro y
  have h0 := h y
  unfold AssignCheck at h0
  rw [certSum_pt_eq_zero, mul_eq_zero, sub_eq_zero] at h0
  exact h0.imp id Eq.symm

/-! ## The system -/

section system

theorem tableSize_two_pow (ℓ dm : ℕ) : tableSize (2 ^ ℓ) (2 ^ dm) = 2 ^ (ℓ + ℓ + 3 * dm + 6) := by
  unfold tableSize
  rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

theorem tableSize_eq_oW (L : PcpDims) : tableSize (2 ^ L.ℓ) (2 ^ L.dm) = 2 ^ L.oW :=
  tableSize_two_pow _ _

theorem div_two_pow_div_two_pow (u a b : ℕ) : u / 2 ^ a / 2 ^ b = u / 2 ^ (a + b) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem bitPt_comp_oA (u : ℕ) :
    (bitPt L.oW u : Fin L.oW → F) ∘ L.oA = bitPt L.ℓ (idxA (2 ^ L.ℓ) u) := by
  funext j
  simp [bitPt, pt, PcpDims.oA, idxA, Nat.testBit_mod_two_pow, j.2]

theorem bitPt_comp_oB (u : ℕ) :
    (bitPt L.oW u : Fin L.oW → F) ∘ L.oB = bitPt L.ℓ (idxB (2 ^ L.ℓ) u) := by
  funext j
  simp only [Function.comp_apply, bitPt, pt, PcpDims.oB, idxB, Nat.testBit_mod_two_pow, j.2,
    decide_true, Bool.true_and, Nat.testBit_div_two_pow]
  rw [Nat.add_comm]

theorem bitPt_comp_oL₀ (u : ℕ) :
    (bitPt L.oW u : Fin L.oW → F) ∘ L.oL 0 = bitPt L.dm (idx₁ (2 ^ L.ℓ) (2 ^ L.dm) u) := by
  funext j
  simp only [Function.comp_apply, bitPt, pt, PcpDims.oL, idx₁, Nat.testBit_mod_two_pow, j.2,
    decide_true, Bool.true_and, div_two_pow_div_two_pow, Nat.testBit_div_two_pow]
  congr 2
  simp; omega

theorem bitPt_comp_oL₁ (u : ℕ) :
    (bitPt L.oW u : Fin L.oW → F) ∘ L.oL 1 = bitPt L.dm (idx₂ (2 ^ L.ℓ) (2 ^ L.dm) u) := by
  funext j
  simp only [Function.comp_apply, bitPt, pt, PcpDims.oL, idx₂, Nat.testBit_mod_two_pow, j.2,
    decide_true, Bool.true_and, div_two_pow_div_two_pow, Nat.testBit_div_two_pow]
  congr 2
  simp; omega

theorem bitPt_comp_oL₂ (u : ℕ) :
    (bitPt L.oW u : Fin L.oW → F) ∘ L.oL 2 = bitPt L.dm (idx₃ (2 ^ L.ℓ) (2 ^ L.dm) u) := by
  funext j
  simp only [Function.comp_apply, bitPt, pt, PcpDims.oL, idx₃, Nat.testBit_mod_two_pow, j.2,
    decide_true, Bool.true_and, div_two_pow_div_two_pow, Nat.testBit_div_two_pow]
  congr 2
  simp; omega

theorem bitPt_oSgn (u : ℕ) (k : Fin 6) :
    (bitPt L.oW u : Fin L.oW → F) (L.oSgn k) =
      ofBool ((idxS (2 ^ L.ℓ) (2 ^ L.dm) u).testBit k) := by
  simp only [bitPt, pt, PcpDims.oSgn, idxS, div_two_pow_div_two_pow, Nat.testBit_div_two_pow]
  congr 2
  omega

theorem castHom_ofBool [CharP F 2] (b : Bool) :
    ZMod.castHom (dvd_refl 2) F (ofBool b) = ofBool b := by
  cases b <;> simp [ofBool]

theorem val_two_add_castLE (k : Fin 3) :
    (((2 : Fin 6) + Fin.castLE (by omega : 3 ≤ 6) k : Fin 6) : ℕ) = 2 + k := by
  fin_cases k <;> rfl

theorem val_three_add_castLE (k : Fin 3) :
    (((3 : Fin 6) + Fin.castLE (by omega : 3 ≤ 6) k : Fin 6) : ℕ) = 3 + k := by
  fin_cases k <;> rfl

/-- **The system the table of `O` holds is satisfied by the linear tables**
(eq:induced_system_is_satisfied, eq:system_is_satisfied, Observation obs:satisfiability_vs_PCP):
at an index where `O` is `1`, the system check on the cube makes the equation hold in `F`, hence
in `F₂`. -/
theorem tableSat_of_identities [CharP F 2] {T : MvPolynomial (Fin L.m) F} {P : Pcp L F}
    (h : P.Identities T) :
    TableSat (2 ^ L.ℓ) (2 ^ L.dm) (resStr P.gO) (resZ P.gLa) (resZ P.gLb) (resZ (P.gL 0))
      (resZ (P.gL 1)) (resZ (P.gL 2)) := by
  obtain ⟨-, hsys, -, -, hO, -, hLa, hLb, hL⟩ := h
  have aO := isAssignment_of_assignCheck fun y => hO (pt y)
  have aLa := isAssignment_of_assignCheck fun y => hLa (pt y)
  have aLb := isAssignment_of_assignCheck fun y => hLb (pt y)
  have aL := fun k => isAssignment_of_assignCheck fun y => hL k (pt y)
  intro u hu hOu
  rw [tableSize_eq_oW] at hu
  have hres : res P.gO u = true := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hu)] at hOu
    simpa [getElem_resStr] using hOu
  have hs := hsys (bitPt L.oW u)
  unfold SystemCheck at hs
  rw [show (bitPt L.oW u : Fin L.oW → F) = pt fun i : Fin L.oW => u.testBit i from rfl,
    certSum_pt_eq_zero, ← show (bitPt L.oW u : Fin L.oW → F) = pt fun i : Fin L.oW => u.testBit i
      from rfl, eval_bitPt aO, hres] at hs
  simp only [ofBool, ite_true, one_mul, sub_eq_zero, Fin.sum_univ_three] at hs
  rw [bitPt_comp_oA, bitPt_comp_oB, bitPt_comp_oL₀, bitPt_comp_oL₁, bitPt_comp_oL₂,
    eval_bitPt aLa, eval_bitPt aLb, eval_bitPt (aL 0), eval_bitPt (aL 1), eval_bitPt (aL 2),
    bitPt_oSgn, bitPt_oSgn, bitPt_oSgn, bitPt_oSgn, bitPt_oSgn, bitPt_oSgn] at hs
  have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  have h30 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have h31 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have h32 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [val_two_add_castLE, h5, h30, h31, h32, Fin.val_zero, Fin.val_one] at hs
  apply ZMod.castHom_injective F
  simp only [sgn, resZ, map_add, map_mul, castHom_ofBool]
  linear_combination hs

end system

/-! ## The formula -/

section clauseInput

variable {ℓa ℓb ℓc r : ℕ} (c : Clause6W ℓa ℓb ℓc r)

theorem getD_bitsOfNat_append {m v t : ℕ} (l : List Bool) (ht : t < m) :
    (bitsOfNat m v ++ l).getD t false = v.testBit t := by
  rw [List.getD_append _ _ _ _ (by rw [length_bitsOfNat]; exact ht),
    List.getD_eq_getElem _ _ (by rw [length_bitsOfNat]; exact ht)]
  simp [bitsOfNat]

theorem getD_bitsOfNat_append_right {m v : ℕ} (l : List Bool) (t : ℕ) :
    (bitsOfNat m v ++ l).getD (m + t) false = l.getD t false := by
  rw [List.getD_append_right _ _ _ _ (by rw [length_bitsOfNat]; omega), length_bitsOfNat,
    Nat.add_sub_cancel_left]

/-- The six signs of a clause. -/
def sgns6 : List Bool := [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos, c.l₆.pos]

theorem clauseInput6_assoc : clauseInput6 ℓa ℓb ℓc r c =
    bitsOfNat ℓa c.l₁.var ++ (bitsOfNat ℓb c.l₂.var ++ (bitsOfNat ℓc c.l₃.var ++
      (bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ (bitsOfNat r c.l₆.var ++ sgns6 c))))) := by
  simp only [clauseInput6, sgns6, List.append_assoc]

theorem getD_clauseInput6_one {t : ℕ} (ht : t < ℓa) :
    (clauseInput6 ℓa ℓb ℓc r c).getD t false = (c.l₁.var : ℕ).testBit t := by
  rw [clauseInput6_assoc, getD_bitsOfNat_append _ ht]

theorem getD_clauseInput6_two {i t : ℕ} (hi : i = ℓa + t) (ht : t < ℓb) :
    (clauseInput6 ℓa ℓb ℓc r c).getD i false = (c.l₂.var : ℕ).testBit t := by
  rw [clauseInput6_assoc, hi, getD_bitsOfNat_append_right, getD_bitsOfNat_append _ ht]

theorem getD_clauseInput6_three {i t : ℕ} (hi : i = ℓa + ℓb + t) (ht : t < ℓc) :
    (clauseInput6 ℓa ℓb ℓc r c).getD i false = (c.l₃.var : ℕ).testBit t := by
  rw [clauseInput6_assoc, hi, Nat.add_assoc, getD_bitsOfNat_append_right,
    getD_bitsOfNat_append_right, getD_bitsOfNat_append _ ht]

theorem getD_clauseInput6_four {i t : ℕ} (hi : i = ℓa + ℓb + ℓc + t) (ht : t < r) :
    (clauseInput6 ℓa ℓb ℓc r c).getD i false = (c.l₄.var : ℕ).testBit t := by
  rw [clauseInput6_assoc, hi, Nat.add_assoc, Nat.add_assoc, getD_bitsOfNat_append_right,
    getD_bitsOfNat_append_right, getD_bitsOfNat_append_right, getD_bitsOfNat_append _ ht]

theorem getD_clauseInput6_five {i t : ℕ} (hi : i = ℓa + ℓb + ℓc + r + t) (ht : t < r) :
    (clauseInput6 ℓa ℓb ℓc r c).getD i false = (c.l₅.var : ℕ).testBit t := by
  rw [clauseInput6_assoc, hi, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
    getD_bitsOfNat_append_right, getD_bitsOfNat_append_right, getD_bitsOfNat_append_right,
    getD_bitsOfNat_append_right, getD_bitsOfNat_append _ ht]

theorem getD_clauseInput6_six {i t : ℕ} (hi : i = ℓa + ℓb + ℓc + r + r + t) (ht : t < r) :
    (clauseInput6 ℓa ℓb ℓc r c).getD i false = (c.l₆.var : ℕ).testBit t := by
  rw [clauseInput6_assoc, hi, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
    getD_bitsOfNat_append_right, getD_bitsOfNat_append_right, getD_bitsOfNat_append_right,
    getD_bitsOfNat_append_right, getD_bitsOfNat_append_right, getD_bitsOfNat_append _ ht]

theorem getD_clauseInput6_sgn {i k : ℕ} (hi : i = ℓa + ℓb + ℓc + r + r + r + k) :
    (clauseInput6 ℓa ℓb ℓc r c).getD i false = (sgns6 c).getD k false := by
  rw [clauseInput6_assoc, hi, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc,
    Nat.add_assoc, getD_bitsOfNat_append_right, getD_bitsOfNat_append_right,
    getD_bitsOfNat_append_right, getD_bitsOfNat_append_right, getD_bitsOfNat_append_right,
    getD_bitsOfNat_append_right]

end clauseInput

theorem lit_eval_eq_true_iff {V : Type*} (w : V → Bool) (l : Lit V) :
    l.eval w = true ↔ w l.var = l.pos := by
  unfold Lit.eval
  cases l.pos <;> cases w l.var <;> simp

section formula

variable (L) in
/-- The clauses of the PCP's formula: three windows of index lengths `ℓ + 1, ℓ + 1, |S₀| + 1` and
three witness blocks of index length `r`. -/
abbrev PcpClause : Type := Clause6W (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r

/-- The input wires of the Boolean point `y` hold the clause input of `c`. -/
def InputsAt (y : Fin L.m → Bool) (c : PcpClause L) : Prop :=
  ∀ w : Fin L.m, w.val < L.nIn →
    y w = (clauseInput6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r c).getD w false

variable {y : Fin L.m → Bool} {c : PcpClause L}

theorem nIn_eq (L : PcpDims) :
    L.nIn = (L.ℓ + 1) + (L.ℓ + 1) + (L.oW + 1) + L.r + L.r + L.r + 6 := by
  unfold PcpDims.nIn; omega

theorem pt_πA (hy : InputsAt y c) : (pt y L.πA : F) = ofBool ((c.l₁.var : ℕ).testBit 0) := by
  rw [pt, hy _ (by rw [PcpDims.val_πA, nIn_eq]; omega), PcpDims.val_πA]
  exact congrArg ofBool (getD_clauseInput6_one c (by omega))

theorem pt_comp_vA (hy : InputsAt y c) :
    (pt y : Fin L.m → F) ∘ L.vA = bitPt L.ℓ ((c.l₁.var : ℕ) / 2) := by
  funext t
  have ht := t.2
  simp only [Function.comp_apply, pt, bitPt, Nat.testBit_div_two]
  rw [hy _ (by rw [PcpDims.val_vA, nIn_eq]; omega), PcpDims.val_vA,
    getD_clauseInput6_one c (by omega), Nat.add_comm 1 (t : ℕ)]

theorem pt_πB (hy : InputsAt y c) : (pt y L.πB : F) = ofBool ((c.l₂.var : ℕ).testBit 0) := by
  rw [pt, hy _ (by rw [PcpDims.val_πB, nIn_eq]; omega), PcpDims.val_πB]
  exact congrArg ofBool (getD_clauseInput6_two c rfl (by omega))

theorem pt_comp_vB (hy : InputsAt y c) :
    (pt y : Fin L.m → F) ∘ L.vB = bitPt L.ℓ ((c.l₂.var : ℕ) / 2) := by
  funext t
  have ht := t.2
  simp only [Function.comp_apply, pt, bitPt, Nat.testBit_div_two]
  rw [hy _ (by rw [PcpDims.val_vB, nIn_eq]; omega), PcpDims.val_vB,
    getD_clauseInput6_two c (t := t + 1) (by omega) (by omega)]

theorem pt_πC (hy : InputsAt y c) : (pt y L.πC : F) = ofBool ((c.l₃.var : ℕ).testBit 0) := by
  rw [pt, hy _ (by rw [PcpDims.val_πC, nIn_eq]; omega), PcpDims.val_πC]
  exact congrArg ofBool (getD_clauseInput6_three c rfl (by omega))

theorem pt_comp_vO (hy : InputsAt y c) :
    (pt y : Fin L.m → F) ∘ L.vO = bitPt L.oW ((c.l₃.var : ℕ) / 2) := by
  funext t
  have ht := t.2
  simp only [Function.comp_apply, pt, bitPt, Nat.testBit_div_two]
  rw [hy _ (by rw [PcpDims.val_vO, nIn_eq]; omega), PcpDims.val_vO,
    getD_clauseInput6_three c (t := t + 1) (by omega) (by omega)]

/-- The index of the `k`-th witness literal of a clause. -/
def wVar (c : PcpClause L) (k : Fin 3) : ℕ := ![(c.l₄.var : ℕ), c.l₅.var, c.l₆.var] k

/-- The sign of the `k`-th witness literal of a clause. -/
def wPos (c : PcpClause L) (k : Fin 3) : Bool := ![c.l₄.pos, c.l₅.pos, c.l₆.pos] k

theorem pt_comp_vW (hy : InputsAt y c) (k : Fin 3) :
    (pt y : Fin L.m → F) ∘ L.vW k = bitPt L.r (wVar c k) := by
  funext t
  have ht := t.2
  have hk := k.2
  have hkr : k * L.r + t < 3 * L.r := by nlinarith
  simp only [Function.comp_apply, pt, bitPt]
  rw [hy _ (by rw [PcpDims.val_vW, nIn_eq]; omega), PcpDims.val_vW]
  refine congrArg ofBool ?_
  fin_cases k
  · exact getD_clauseInput6_four c (by simp) ht
  · exact getD_clauseInput6_five c (by simp) ht
  · exact getD_clauseInput6_six c (by simp; omega) ht

theorem pt_sgn (hy : InputsAt y c) (k : Fin 6) :
    (pt y (L.sgn k) : F) = ofBool ((sgns6 c).getD k false) := by
  have hk := k.2
  rw [pt, hy _ (by rw [PcpDims.val_sgn, nIn_eq]; omega), PcpDims.val_sgn]
  exact congrArg ofBool (getD_clauseInput6_sgn c (by omega))

/-- A literal factor of the formula check vanishing at a Boolean point makes its literal true. -/
theorem eq_of_ofBool_sub_eq_zero {a b : Bool} (h : (ofBool a : F) - ofBool b = 0) : a = b :=
  ofBool_inj.1 (sub_eq_zero.1 h)

/-- **The formula the circuit describes is satisfied by the tables**
(eq:Tseitin_satisfiable_induced, eq:formula_is_satisfied, Observation obs:satisfiability_vs_PCP):
for a clause the circuit accepts, the Tseitin polynomial is `1` at the Boolean point holding the
clause's input and the gates' values, so a literal factor vanishes there — the window literal
`π · g(u)` is the table's value at the window's index, and equal to the literal's sign. -/
theorem formula6Sat_of_identities [CharP F 2] {Cc : Circuit} (hWF : Cc.WellFormed)
    (hin : Cc.inputs = L.nIn) (hm : Cc.inputs + Cc.size = L.m) {P : Pcp L F}
    (h : P.Identities (rename (Fin.cast hm) Cc.finiteArith)) :
    (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat (fun j => winTbl P.gA j)
      (fun j => winTbl P.gB j) (fun j => winTbl P.gO j) (fun j => res (P.gW 0) j)
      (fun j => res (P.gW 1) j) (fun j => res (P.gW 2) j) := by
  obtain ⟨hform, -, hA, hB, hO, hW, -⟩ := h
  have aA := isAssignment_of_assignCheck fun y => hA (pt y)
  have aB := isAssignment_of_assignCheck fun y => hB (pt y)
  have aO := isAssignment_of_assignCheck fun y => hO (pt y)
  have aW := fun k => isAssignment_of_assignCheck fun y => hW k (pt y)
  intro c hc
  have hc' : Cc.eval (fun i => (clauseInput6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r c).getD i
      false) = true := hc
  obtain ⟨z, hz, hT⟩ := (Circuit.eval_iff_exists_finiteArith (F := F) Cc hWF _).1 hc'
  let y : Fin L.m → Bool := fun w => z (Fin.cast hm.symm w)
  have hy : InputsAt y c := fun w hw => by
    have := hz ⟨w.val, by omega⟩
    exact (congrArg z (Fin.ext rfl)).trans this
  have hTy : eval (pt y : Fin L.m → F) (rename (Fin.cast hm) Cc.finiteArith) = 1 := by
    rw [eval_rename]
    exact (congrArg (fun f => eval f Cc.finiteArith) (funext fun i => rfl)).trans hT
  have hf := hform (pt y)
  unfold FormulaCheck at hf
  rw [hTy, certSum_pt_eq_zero, one_mul] at hf
  rw [pt_πA hy, pt_comp_vA hy, pt_πB hy, pt_comp_vB hy, pt_πC hy, pt_comp_vO hy,
    pt_sgn hy, pt_sgn hy, pt_sgn hy, eval_bitPt aA, eval_bitPt aB, eval_bitPt aO,
    ofBool_mul_ofBool, ofBool_mul_ofBool, ofBool_mul_ofBool] at hf
  simp only [Clause6.eval, Bool.or_eq_true, lit_eval_eq_true_iff]
  rcases mul_eq_zero.1 hf with hf | hW3
  · rcases mul_eq_zero.1 hf with hf | hC
    · rcases mul_eq_zero.1 hf with hA' | hB'
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (eq_of_ofBool_sub_eq_zero hA')))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (eq_of_ofBool_sub_eq_zero hB')))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (eq_of_ofBool_sub_eq_zero hC))))
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hW3
    rw [pt_comp_vW hy, eval_bitPt (aW k), pt_sgn hy] at hk
    have hk' := eq_of_ofBool_sub_eq_zero hk
    fin_cases k
    · exact Or.inl (Or.inl (Or.inr hk'))
    · exact Or.inl (Or.inr hk')
    · exact Or.inr hk'

end formula

/-! ## The game accepts the decoded answers -/

section accept

open Cost

theorem tapeBits_odd (s : BitStr) {c : ℕ} (hc : c < s.length) : tapeBits s (2 * c + 1) = s[c] := by
  unfold tapeBits
  rw [ite_eq_right (by omega), show (2 * c + 1) / 2 = c by omega, List.getElem?_eq_getElem hc]
  cases s[c] <;> rfl

theorem winTbl_odd {k : ℕ} (g : MvPolynomial (Fin k) F) (c : ℕ) :
    winTbl g (2 * c + 1) = res g c := by
  unfold winTbl
  rw [show (2 * c + 1) / 2 = c by omega, Nat.testBit_zero,
    decide_eq_true (show (2 * c + 1) % 2 = 1 by omega), Bool.true_and]

theorem lenOf_eq_of_lenIs {ℓV : ℕ} (V : TailoredVerifier ℓV) {n : ℕ} {x : BitStr} {κ : Bool}
    {k : ℕ} (h : LenIs V.len n x κ k) : V.lenOf n x κ = k := by
  have hex : ∃ k, LenIs V.len n x κ k := ⟨k, h⟩
  unfold TailoredVerifier.lenOf
  rw [dite_eq_left hex]
  exact hex.choose_spec.unique h

/-- **The game accepts the decoded answers of a PCP satisfying the checks identically**
(cor:functional_viewpoint_final, clause 2, from the identities): when the circuit describes the
output indicator `L*` of `𝒱` through the windows, the tables of the PCP satisfy the formula, so
there are strings `a, b` that `L*` accepts whose tape encodings the windows hold; the readable
tables are the readable answers, the table of `gO` is the table `O` that `L*` compared, and
the linear tables, which satisfy the system that table holds, complete the readable answers to
answers the game accepts. -/
theorem accepts_of_identities [CharP F 2] (prm : PolyTimeFun ℕ (Unary × Unary)) {ℓV : ℕ}
    (V : TailoredVerifier ℓV) {n : ℕ} (xq yq : V.Questions n)
    (hℓ : (prm n).1.length = L.ℓ) (hdm : (prm n).2.length = L.dm) {Cc : Circuit} {Tt : ℕ}
    (hWF : Cc.WellFormed) (hin : Cc.inputs = L.nIn) (hm : Cc.inputs + Cc.size = L.m)
    (hdesc : Cc.DescribesWindows (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r (lstar prm V) n
      (CL.toBits xq) (CL.toBits yq) Tt)
    {P : Pcp L F} (h : P.Identities (rename (Fin.cast hm) Cc.finiteArith)) :
    (V.tgame n).Accepts xq yq
      ((resStr P.gA).take ((V.tgame n).lenR xq) ++ readBlock ((V.tgame n).lenL xq) (resZ P.gLa))
      ((resStr P.gB).take ((V.tgame n).lenR yq) ++
        readBlock ((V.tgame n).lenL yq) (resZ P.gLb)) := by
  have hsat := formula6Sat_of_identities hWF hin hm h
  have htab := tableSat_of_identities h
  obtain ⟨ap, bp, -, -, hA, hB, hC, hacc⟩ := (hdesc _ _ _).1 ⟨_, _, _, hsat⟩
  obtain ⟨lRx, lLx, lRy, lLy, cs, hRx, hLx, hRy, hLy, hcs, hok⟩ :=
    (lstar_accepts_iff prm V n _ _ ap bp).1 hacc.accepts
  rw [hℓ, hdm] at hok
  have hok' := hok
  obtain ⟨hRxN, -, hRyN, -, hbl, hal, -, -⟩ := hok'
  rw [tableSize_eq_oW] at hal
  have hNpos : 0 < 2 ^ L.ℓ := Nat.two_pow_pos _
  have hpow : 2 ^ (L.ℓ + 1) = 2 * 2 ^ L.ℓ := by rw [pow_succ]; ring
  have hpowO : 2 ^ (L.oW + 1) = 2 * 2 ^ L.oW := by rw [pow_succ]; ring
  -- the windows' odd positions hold the tables
  have hapA : ∀ c (hc : c < 2 ^ L.ℓ), ap[c]'(by omega) = res P.gA c := fun c hc => by
    have := hA ⟨2 * c + 1, by omega⟩
    simp only at this
    rw [winTbl_odd, tapeBits_odd _ (by omega)] at this
    exact this.symm
  have hbpB : ∀ c (hc : c < 2 ^ L.ℓ), bp[c]'(by omega) = res P.gB c := fun c hc => by
    have := hB ⟨2 * c + 1, by omega⟩
    simp only at this
    rw [winTbl_odd, tapeBits_odd _ (by omega)] at this
    exact this.symm
  have hapC : ∀ c (hc : c < 2 ^ L.oW), ap[2 ^ L.ℓ + c]'(by omega) = res P.gO c := fun c hc => by
    have := hC ⟨2 * c + 1, by omega⟩
    simp only at this
    rw [winTbl_odd, show 2 ^ (L.ℓ + 1) + (2 * c + 1) = 2 * (2 ^ L.ℓ + c) + 1 by omega,
      tapeBits_odd _ (by omega)] at this
    exact this.symm
  have hdrop : ap.drop (2 ^ L.ℓ) = resStr P.gO := by
    apply List.ext_getElem (by simp; omega)
    intro c h1 h2
    rw [List.getElem_drop, hapC c (by simpa using h2), getElem_resStr]
  have htakeA : ap.take lRx = (resStr P.gA).take lRx := by
    apply List.ext_getElem (by simp; omega)
    intro c h1 h2
    simp only [List.length_take] at h1 h2
    rw [List.getElem_take, List.getElem_take, hapA c (by omega), getElem_resStr]
  have htakeB : bp.take lRy = (resStr P.gB).take lRy := by
    apply List.ext_getElem (by simp; omega)
    intro c h1 h2
    simp only [List.length_take] at h1 h2
    rw [List.getElem_take, List.getElem_take, hbpB c (by omega), getElem_resStr]
  -- the game's lengths and constraints are those `L*` read
  have eRx : (V.tgame n).lenR xq = lRx := lenOf_eq_of_lenIs V hRx
  have eLx : (V.tgame n).lenL xq = lLx := lenOf_eq_of_lenIs V hLx
  have eRy : (V.tgame n).lenR yq = lRy := lenOf_eq_of_lenIs V hRy
  have eLy : (V.tgame n).lenL yq = lLy := lenOf_eq_of_lenIs V hLy
  have hx : V.LenDefined n (CL.toBits xq) := fun κ => by
    cases κ
    · exact ⟨_, hRx⟩
    · exact ⟨_, hLx⟩
  have hy : V.LenDefined n (CL.toBits yq) := fun κ => by
    cases κ
    · exact ⟨_, hRy⟩
    · exact ⟨_, hLy⟩
  have ecs : (V.tgame n).cons xq yq (ap.take lRx) (bp.take lRy) = cs :=
    V.consOf_eq_of hx hy hcs
  rw [← hdrop] at htab
  have hfin := accepts_of_lstarOK (V.tgame n) eRx eLx eRy eLy ecs hNpos hok htab
  rw [htakeA, htakeB] at hfin
  rw [eRx, eLx, eRy, eLy]
  exact hfin

/-- **The soundness of the PCP for the output indicator**
(prop:completeness_and_soundness_of_PCP_for_V_n and cor:functional_viewpoint_final, clause 2): a
PCP of degree `d` passing the thirteen checks on a set of points of density more than
`m · (5 + 6(d + 1)) / q` has decoded answers that the game accepts. -/
theorem accepts_of_dense [CharP F 2] [Fintype F] [DecidableEq F]
    (prm : PolyTimeFun ℕ (Unary × Unary)) {ℓV : ℕ} (V : TailoredVerifier ℓV) {n : ℕ}
    (xq yq : V.Questions n) (hℓ : (prm n).1.length = L.ℓ) (hdm : (prm n).2.length = L.dm)
    {Cc : Circuit} {Tt : ℕ} (hWF : Cc.WellFormed) (hin : Cc.inputs = L.nIn)
    (hm : Cc.inputs + Cc.size = L.m)
    (hdesc : Cc.DescribesWindows (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r (lstar prm V) n
      (CL.toBits xq) (CL.toBits yq) Tt)
    {P : Pcp L F} {d : ℕ} (hP : P.IndDeg d) (S : Finset (Fin L.m → F))
    (hS : ∀ p ∈ S, P.Passes (rename (Fin.cast hm) Cc.finiteArith) p)
    (hdens : (L.m : ℝ) * chkDeg 5 d / Fintype.card F <
      (S.card : ℝ) / (Fintype.card F : ℝ) ^ L.m) :
    (V.tgame n).Accepts xq yq
      ((resStr P.gA).take ((V.tgame n).lenR xq) ++ readBlock ((V.tgame n).lenL xq) (resZ P.gLa))
      ((resStr P.gB).take ((V.tgame n).lenR yq) ++
        readBlock ((V.tgame n).lenL yq) (resZ P.gLb)) := by
  have hT : ∀ i, (rename (Fin.cast hm) (Cc.finiteArith (F := F))).degreeOf i ≤ 5 :=
    degreeOf_rename_le_of_injective (Fin.cast_injective hm) (Circuit.degreeOf_finiteArith_le Cc hWF)
  exact accepts_of_identities prm V xq yq hℓ hdm hWF hin hm hdesc
    (identities_of_dense hT hP S hS hdens)

end accept

end MIPRE.Tailored.AnsRed

end
