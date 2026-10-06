/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.LinearCheck
public import MIPRE.Background.Tailored.Intro.Pauli
public import MIPRE.Background.QLD.PauliBinaryInterface

@[expose] public section

/-!
# The Pauli basis test as controlled linear constraints

The tailored question reduction keeps the Pauli basis test's answers as the introspection
kernel reads them (`MIPRE.Tailored.Intro.pauliLen`): a label `T` has `count T m 1` blocks of
`width T k` bits, each block of width `k` the canonical bits of an element of the effective
field `shoupBinField k hk`, all readable at the `Z`-basis Pauli label and all linear otherwise
(`pauliRead`). A tailored game may decide only by controlled linear constraints: vectors `c`
over the answer bits of both players and an affine coordinate `J`, chosen from the questions
and the readable bits, each satisfied when `⟨c, (a, b, 1)⟩ = 0` over `F₂`. This file presents
the kernel's Pauli conjunct --- `QLD.accepts` on the decoded questions and answers --- in that
form, `pauliCons`.

That is possible because every rule of `fig:decider_pauli` (`QLD.pairTest`) is a conjunction of
`F₂`-affine equations in the answer bits whose coefficients are computed from the questions, and
its disjunctions branch only on the questions:

* equal labels compare the answers (`sameChecks`): bit `l` of `a` is bit `l` of `b`;
* a line against a point (`lineChecks`): whether the point lies on the line is a question
  condition (if it fails, `LinCheck.reject`), and `f(τ) = a` is `F_q`-linear in the coefficients
  of `f` and in `a`, with `τ` the point's parameter;
* the point probe of the Pauli outcome (`pauliChecks`): `g_h(y) = ∑_z h(z) ind_z(y) = a`,
  `F_q`-linear in `h` and `a`;
* the commutation and Magic Square rules (`bitEq`, `prbCheck`, `conVarChecks`,
  `pointVarChecks`) are gated on `γ(ω)` and on the labels, and check equalities of answer bits,
  a parity, and the probe `tr(a · r) = b`, which is `F₂`-linear in `a`.

An `F_q`-equation is the `k` equations of its coordinates in the canonical basis, under which
the field's bit encoding is `F₂`-linear (`MIPRE.Tailored.Intro.fieldChecks`). Each check is an
`F₂`-linear functional on the answer bits with a target (`LinCheck`), and its constraint is the
functional on the unit vectors followed by the target (`LinCheck.toCon`), so `pauliCons` never
reads the readable bits: the readable answer is the `Z`-basis outcome, compared and probed
linearly like the others. The answer bits are read by position: the field element at block `i`
of an answer at offset `o` is `fldAt (o + i k)`, a bit is `getv`.

* `pairChecks_iff`: the checks of a pair of questions hold exactly when `pairTest` accepts the
  formatted answers read off the bit vector;
* `pauliCons_iff`, **the main theorem**: for answers of the label lengths, the constraints are
  satisfied exactly when `QLD.accepts` holds of the decoded questions and answers, which is the
  form `program_pauli_iff` gives the kernel; `length_of_mem_pauliCons` gives every constraint
  the length `|a| + |b| + 1`;
* `endpointValid_iff`: the kernel's endpoint validity is the label's answer length.

The kernel itself is rewritten in `PauliConsKernel.lean`. `pauliCons` is a structural function
of the questions: the coefficients are the values of explicit field operations (multiplication
by question-determined elements, the trace, coordinates) at unit vectors, and the branching is
on question data only, so a polynomial-time program computes it by evaluating each check at the
`|a| + |b|` unit vectors.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.PauliCons

open Cost MIPRE.QLD MIPRE.SAT MIPRE.LowDegree MIPRE.LowDegree.BinaryLinear
open MIPRE.QLD.PauliAnswerProgram MIPRE.Introspection.FieldTableProgram
open MvPolynomial (eval)

variable {k : ℕ} {hk : 1 ≤ k} {M N : ℕ}

/-! ## The checks of each rule -/

section Checks

variable (k hk N)

/-- Equal types: the bits `l` and `L + l` agree, for `l < L`. -/
def sameChecks (L : ℕ) : List (LinCheck N) :=
  List.ofFn fun l : Fin L => ⟨getv N l + getv N (L + l), 0⟩

/-- Two bits agree. -/
def bitEq (o o' : ℕ) : LinCheck N := ⟨getv N o + getv N o', 0⟩

/-- The probe `tr(a · r)` of the field element at `oP` is the bit at `oB`. -/
def prbCheck (r : (shoupBinField k hk).carrier) (oP oB : ℕ) : LinCheck N :=
  ⟨Algebra.trace (ZMod 2) (shoupBinField k hk).carrier ∘ₗ LinearMap.mulRight (ZMod 2) r ∘ₗ
      fldAt k hk N oP + getv N oB, 0⟩

/-- The line-against-point rule: the point lies on the line (a condition on the questions; if
it fails, reject), and the polynomial at `oL`, with `n + 1` coefficients, evaluated at the
parameter of the point, is the point answer at `oP`. -/
def lineChecks (n : ℕ) (oP oL : ℕ) (u₀ w y : Fin M → (shoupBinField k hk).carrier) :
    List (LinCheck N) :=
  if ∃ t : (shoupBinField k hk).carrier, y = u₀ + t • w then
    fieldChecks k hk
      ((∑ i : Fin (n + 1),
          LinearMap.mulRight (ZMod 2) (MIPRE.LIDT.CL.lineParam u₀ w y ^ (i : ℕ)) ∘ₗ
            fldAt k hk N (oL + i * k)) - fldAt k hk N oP) 0
  else [LinCheck.reject N]

/-- The point probe against the full Pauli outcome at `oQ`: the low-degree encoding of the
outcome at `y`, `∑_z h(z) · ind_z(y)`, is the point answer at `oP`. -/
def pauliChecks (oP oQ : ℕ) (y : Fin M → (shoupBinField k hk).carrier) : List (LinCheck N) :=
  fieldChecks k hk
    ((∑ z : Fin M → Bool,
        LinearMap.mulRight (ZMod 2)
            (eval y (ind z : MvPolynomial (Fin M) (shoupBinField k hk).carrier)) ∘ₗ
          fldAt k hk N (oQ + (cubeEnumeration M z : ℕ) * k)) - fldAt k hk N oP) 0

/-- The position of a basis in a `Pair` answer. -/
def basIdx : Bas → ℕ
  | .X => 0
  | .Z => 1

/-- The Magic Square rule, a constraint triple at `oC` against a variable bit at `oV`. -/
def conVarChecks (i : Fin MIPRE.LCS.MagicSquare.layout.r) (j : Fin MIPRE.LCS.MagicSquare.layout.s)
    (ω : Omega (shoupBinField k hk).carrier M) (oC oV : ℕ) : List (LinCheck N) :=
  if gam ω = 0 then []
  else if j ∈ MIPRE.LCS.MagicSquare.layout.V i then
    [⟨getv N oC + getv N (oC + 1) + getv N (oC + 2), MIPRE.LCS.MagicSquare.game.b i⟩,
      bitEq N (oC + (MIPRE.LCS.MagicSquare.cellIdx i j : ℕ)) oV]
  else [LinCheck.reject N]

/-- The Magic Square consistency rule, a point answer at `oP` against a variable bit at `oV`. -/
def pointVarChecks (W : Bas) (j : Fin MIPRE.LCS.MagicSquare.layout.s)
    (ω : Omega (shoupBinField k hk).carrier M) (oP oV : ℕ) : List (LinCheck N) :=
  if gam ω = 0 then []
  else if W = .X ∧ j = MIPRE.LCS.MagicSquare.v 0 then [prbCheck k hk N ω.rX oP oV]
  else if W = .Z ∧ j = MIPRE.LCS.MagicSquare.v 4 then [prbCheck k hk N ω.rZ oP oV]
  else [LinCheck.reject N]

variable [NeZero M] (hm : M ∣ Fintype.card (shoupBinField k hk).carrier)

/-- The checks of `pairTest`, for answers at the offsets `oA` and `oB`: one branch per rule and
orientation, `[]` where `pairTest` accepts unconditionally. -/
def pairChecks :
    Question (shoupBinField k hk).carrier M → Question (shoupBinField k hk).carrier M →
      ℕ → ℕ → List (LinCheck N)
  | .point W y, .aline W' u₀ s, oA, oB =>
      if W = W' then lineChecks k hk N 1 oA oB u₀ (Pi.single (MIPRE.LIDT.CL.chi hm s) 1) y
      else []
  | .aline W' u₀ s, .point W y, oA, oB =>
      if W = W' then lineChecks k hk N 1 oB oA u₀ (Pi.single (MIPRE.LIDT.CL.chi hm s) 1) y
      else []
  | .point W y, .dline W' u₀ _ w, oA, oB =>
      if W = W' then lineChecks k hk N (M * 1) oA oB u₀ w y else []
  | .dline W' u₀ _ w, .point W y, oA, oB =>
      if W = W' then lineChecks k hk N (M * 1) oB oA u₀ w y else []
  | .point W y, .pauli W', oA, oB => if W = W' then pauliChecks k hk N oA oB y else []
  | .pauli W', .point W y, oA, oB => if W = W' then pauliChecks k hk N oB oA y else []
  | .pairB W _, .pair ω, oA, oB => if gam ω ≠ 0 then [] else [bitEq N oA (oB + basIdx W)]
  | .pair ω, .pairB W _, oA, oB => if gam ω ≠ 0 then [] else [bitEq N oB (oA + basIdx W)]
  | .point W _, .pairB W' ω, oA, oB =>
      if W = W' then (if gam ω ≠ 0 then [] else [prbCheck k hk N (ω.r W) oA oB]) else []
  | .pairB W' ω, .point W _, oA, oB =>
      if W = W' then (if gam ω ≠ 0 then [] else [prbCheck k hk N (ω.r W) oB oA]) else []
  | .con i _, .var j ω, oA, oB => conVarChecks k hk N i j ω oA oB
  | .var j ω, .con i _, oA, oB => conVarChecks k hk N i j ω oB oA
  | .point W _, .var j ω, oA, oB => pointVarChecks k hk N W j ω oA oB
  | .var j ω, .point W _, oA, oB => pointVarChecks k hk N W j ω oB oA
  | _, _, _, _ => []

end Checks

/-! ## Reading the answers -/

section Reads

/-- The vector `v` carries the bits `w` from position `o` on. -/
def Reads (v : Fin N → ZMod 2) (o : ℕ) (w : BitStr) : Prop :=
  ∀ l < w.length, getv N (o + l) v = ofBool (w.getD l false)

theorem reads_left (a b : BitStr) (hN : (a ++ b).length ≤ N) :
    Reads (bitVec N (a ++ b)) 0 a := by
  intro l hl
  rw [zero_add, getv_bitVec _ hN, List.getD_append _ _ _ _ hl]

theorem reads_right (a b : BitStr) (hN : (a ++ b).length ≤ N) :
    Reads (bitVec N (a ++ b)) a.length b := by
  intro l _
  rw [getv_bitVec _ hN, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem getD_flatten (rows : List BitStr) (w : ℕ) (hw : ∀ r ∈ rows, r.length = w) (i l : ℕ)
    (hl : l < w) : rows.flatten.getD (i * w + l) false = (rows.getD i []).getD l false := by
  induction rows generalizing i with
  | nil => simp
  | cons r rs ih =>
    have hr := hw r (by simp)
    rw [List.flatten_cons]
    cases i with
    | zero =>
      rw [zero_mul, zero_add, List.getD_append _ _ _ _ (by omega)]
      rfl
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by rw [hr, Nat.succ_mul]; omega)]
      have : (i + 1) * w + l - r.length = i * w + l := by rw [hr, Nat.succ_mul]; omega
      rw [this, ih (fun r' h => hw r' (by simp [h])) i]
      rfl

variable {v : Fin N → ZMod 2} {o : ℕ}

theorem Reads.fld {x : (shoupBinField k hk).carrier}
    (h : Reads v o ((shoupBinField k hk).toBits x)) : fldAt k hk N o v = x :=
  fldAt_eq v x fun i hi => h i (by rw [(shoupBinField k hk).length_toBits]; exact hi)

theorem Reads.vec {n : ℕ} {g : Fin n → (shoupBinField k hk).carrier}
    (h : Reads v o ((shoupBinField k hk).vecBits g).flatten) (i : Fin n) :
    fldAt k hk N (o + i * k) v = g i := by
  have hw : ∀ r ∈ (shoupBinField k hk).vecBits g, r.length = k :=
    fun r hr => (shoupBinField k hk).width_vecBits g hr
  apply fldAt_eq v (g i)
  intro l hl
  have hlen : i * k + l < ((shoupBinField k hk).vecBits g).flatten.length := by
    rw [Introspection.FieldAnswerParser.length_flatten_of_width _ k hw, BinField.length_vecBits]
    have := i.2
    nlinarith
  rw [Nat.add_assoc, h _ hlen, getD_flatten _ k hw i l hl, fieldRow]

end Reads

/-! ## Each rule's checks hold exactly when the rule accepts -/

section Rules

variable (v : Fin N → ZMod 2)

theorem zmod2_add_eq_zero (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

theorem bitEq_holds_iff {o o' : ℕ} {b b' : ZMod 2} (h : getv N o v = b) (h' : getv N o' v = b') :
    (bitEq N o o').Holds v ↔ b = b' := by
  simp only [LinCheck.Holds, bitEq, LinearMap.add_apply, h, h', zmod2_add_eq_zero]

theorem prbCheck_holds_iff (r : (shoupBinField k hk).carrier) {oP oB : ℕ}
    {a : (shoupBinField k hk).carrier} {b : ZMod 2}
    (hP : fldAt k hk N oP v = a) (hB : getv N oB v = b) :
    (prbCheck k hk N r oP oB).Holds v ↔ prb a r = b := by
  simp only [LinCheck.Holds, prbCheck, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, hP, hB, zmod2_add_eq_zero, prb]

theorem lineChecks_iff {n : ℕ} {oP oL : ℕ} (u₀ w y : Fin M → (shoupBinField k hk).carrier)
    {f : Fin (n + 1) → (shoupBinField k hk).carrier} {a : (shoupBinField k hk).carrier}
    (hP : fldAt k hk N oP v = a) (hL : ∀ i : Fin (n + 1), fldAt k hk N (oL + i * k) v = f i) :
    (∀ χ ∈ lineChecks k hk N n oP oL u₀ w y, χ.Holds v) ↔ lowDeg u₀ w y f a = true := by
  unfold lineChecks lowDeg MIPRE.LIDT.CL.lineVsPoint
  split_ifs with hl
  · rw [forall_fieldChecks_iff]
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.mulRight_apply, hP, hL, sub_eq_zero, decide_eq_true_eq, hl, true_and,
      MIPRE.LIDT.LinePoly.eval, forall_const]
  · simp [hl]

theorem pauliChecks_iff {oP oQ : ℕ} (y : Fin M → (shoupBinField k hk).carrier)
    {h : (Fin M → Bool) → (shoupBinField k hk).carrier} {a : (shoupBinField k hk).carrier}
    (hP : fldAt k hk N oP v = a)
    (hQ : ∀ z, fldAt k hk N (oQ + (cubeEnumeration M z : ℕ) * k) v = h z) :
    (∀ χ ∈ pauliChecks k hk N oP oQ y, χ.Holds v) ↔
      decide (eval y (ldEnc h) = a) = true := by
  rw [pauliChecks, forall_fieldChecks_iff]
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, hP, hQ, sub_eq_zero, decide_eq_true_eq, ldEnc, map_sum, map_mul,
    MvPolynomial.eval_C]

theorem conVarChecks_iff (i : Fin MIPRE.LCS.MagicSquare.layout.r)
    (j : Fin MIPRE.LCS.MagicSquare.layout.s) (ω : Omega (shoupBinField k hk).carrier M)
    {oC oV : ℕ} {α : Fin 3 → ZMod 2} {b : ZMod 2}
    (hC : ∀ l : Fin 3, getv N (oC + l) v = α l) (hV : getv N oV v = b) :
    (∀ χ ∈ conVarChecks k hk N i j ω oC oV, χ.Holds v) ↔
      (decide (gam ω = 0) || (decide (j ∈ MIPRE.LCS.MagicSquare.layout.V i) &&
        decide (∑ l, α l = MIPRE.LCS.MagicSquare.game.b i) &&
        decide (α (MIPRE.LCS.MagicSquare.cellIdx i j) = b))) = true := by
  have h0 := hC 0
  have h1 := hC 1
  have h2 := hC 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at h0 h1 h2
  unfold conVarChecks
  split_ifs with hg hj
  · simp [hg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, hg, hj,
      decide_false, decide_true, Bool.false_or, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq]
    rw [bitEq_holds_iff v (hC _) hV]
    simp only [LinCheck.Holds, LinearMap.add_apply, h0, h1, h2, Fin.sum_univ_three]
  · simp [hg, hj]

theorem pointVarChecks_iff (W : Bas) (j : Fin MIPRE.LCS.MagicSquare.layout.s)
    (ω : Omega (shoupBinField k hk).carrier M) {oP oV : ℕ} {a : (shoupBinField k hk).carrier}
    {b : ZMod 2} (hP : fldAt k hk N oP v = a) (hV : getv N oV v = b) :
    (∀ χ ∈ pointVarChecks k hk N W j ω oP oV, χ.Holds v) ↔
      (decide (gam ω = 0) ||
        (decide (W = .X) && decide (j = MIPRE.LCS.MagicSquare.v 0) && decide (prb a ω.rX = b)) ||
        (decide (W = .Z) && decide (j = MIPRE.LCS.MagicSquare.v 4) &&
          decide (prb a ω.rZ = b))) = true := by
  unfold pointVarChecks
  split_ifs with hg h1 h2
  · simp [hg]
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hg, prbCheck_holds_iff v _ hP hV]
  · obtain ⟨rfl, rfl⟩ := h2
    simp [hg, prbCheck_holds_iff v _ hP hV]
  · simp only [not_and] at h1 h2
    cases W
    · simp [hg, h1 rfl]
    · simp [hg, h2 rfl]

end Rules

/-! ## Reading each answer format -/

section Formats

variable {v : Fin N → ZMod 2} {o : ℕ}

local notation "E" => shoupBinField k hk

theorem read_val {x : (shoupBinField k hk).carrier}
    (h : Reads v o (answerBits E (.val x : Answer (shoupBinField k hk).carrier M 1))) :
    fldAt k hk N o v = x :=
  Reads.fld (by simpa [answerBits, answerRows] using h)

theorem read_apoly {f : Fin (1 + 1) → (shoupBinField k hk).carrier}
    (h : Reads v o (answerBits E (.apoly f : Answer (shoupBinField k hk).carrier M 1)))
    (i : Fin (1 + 1)) :
    fldAt k hk N (o + i * k) v = f i :=
  Reads.vec h i

theorem read_dpoly {f : Fin (M * 1 + 1) → (shoupBinField k hk).carrier}
    (h : Reads v o (answerBits E (.dpoly f : Answer (shoupBinField k hk).carrier M 1)))
    (i : Fin (M * 1 + 1)) :
    fldAt k hk N (o + i * k) v = f i :=
  Reads.vec h i

theorem read_pauliAns {g : (Fin M → Bool) → (shoupBinField k hk).carrier}
    (h : Reads v o (answerBits E (.pauliAns g : Answer (shoupBinField k hk).carrier M 1)))
    (z : Fin M → Bool) :
    fldAt k hk N (o + (cubeEnumeration M z : ℕ) * k) v = g z := by
  have := Reads.vec h (cubeEnumeration M z)
  rwa [Equiv.symm_apply_apply] at this

theorem read_bit {b : ZMod 2}
    (h : Reads v o (answerBits E (.bit b : Answer (shoupBinField k hk).carrier M 1))) :
    getv N o v = b := by
  have := h 0 (by simp [answerBits, answerRows])
  simpa [answerBits, answerRows] using this

theorem read_bitPair {β : Bas → ZMod 2}
    (h : Reads v o (answerBits E (.bitPair β : Answer (shoupBinField k hk).carrier M 1)))
    (W : Bas) : getv N (o + basIdx W) v = β W := by
  cases W
  · have := h 0 (by simp [answerBits, answerRows])
    simpa [answerBits, answerRows, basIdx] using this
  · have := h 1 (by simp [answerBits, answerRows])
    simpa [answerBits, answerRows, basIdx] using this

theorem read_bitTriple {α : Fin 3 → ZMod 2}
    (h : Reads v o (answerBits E (.bitTriple α : Answer (shoupBinField k hk).carrier M 1)))
    (l : Fin 3) : getv N (o + l) v = α l := by
  have := h l (by simp [answerBits, answerRows])
  fin_cases l <;> simpa [answerBits, answerRows, List.ofFn_succ] using this

end Formats

/-! ## The checks of `pairTest` -/

section Pair

variable [NeZero M] (hm : M ∣ Fintype.card (shoupBinField k hk).carrier)

/-- **The checks of a pair of questions hold exactly when `pairTest` accepts**, for formatted
answers read at the offsets `oA` and `oB`. -/
theorem pairChecks_iff (qx qy : Question (shoupBinField k hk).carrier M)
    (A B : Answer (shoupBinField k hk).carrier M 1) (hA : qx.fmtOk A = true)
    (hB : qy.fmtOk B = true) (v : Fin N → ZMod 2) (oA oB : ℕ)
    (hvA : Reads v oA (answerBits (shoupBinField k hk) A))
    (hvB : Reads v oB (answerBits (shoupBinField k hk) B)) :
    (∀ χ ∈ pairChecks k hk N hm qx qy oA oB, χ.Holds v) ↔ pairTest hm qx qy A B = true := by
  cases qx <;> cases qy <;>
    (first
      | obtain ⟨_, rfl⟩ := eq_val_of_fmtOk hA
      | obtain ⟨_, rfl⟩ := eq_apoly_of_fmtOk hA
      | obtain ⟨_, rfl⟩ := eq_dpoly_of_fmtOk hA
      | obtain ⟨_, rfl⟩ := eq_pauliAns_of_fmtOk hA
      | obtain ⟨_, rfl⟩ := eq_bit_of_fmtOk_pairB hA
      | obtain ⟨_, rfl⟩ := eq_bitPair_of_fmtOk hA
      | obtain ⟨_, rfl⟩ := eq_bit_of_fmtOk_var hA
      | obtain ⟨_, rfl⟩ := eq_bitTriple_of_fmtOk hA) <;>
    (first
      | obtain ⟨_, rfl⟩ := eq_val_of_fmtOk hB
      | obtain ⟨_, rfl⟩ := eq_apoly_of_fmtOk hB
      | obtain ⟨_, rfl⟩ := eq_dpoly_of_fmtOk hB
      | obtain ⟨_, rfl⟩ := eq_pauliAns_of_fmtOk hB
      | obtain ⟨_, rfl⟩ := eq_bit_of_fmtOk_pairB hB
      | obtain ⟨_, rfl⟩ := eq_bitPair_of_fmtOk hB
      | obtain ⟨_, rfl⟩ := eq_bit_of_fmtOk_var hB
      | obtain ⟨_, rfl⟩ := eq_bitTriple_of_fmtOk hB)
  case point.aline =>
    simp only [pairChecks, pairTest]
    split_ifs
    · exact lineChecks_iff v _ _ _ (read_val hvA) (read_apoly hvB)
    · simp
  case aline.point =>
    simp only [pairChecks, pairTest]
    split_ifs
    · exact lineChecks_iff v _ _ _ (read_val hvB) (read_apoly hvA)
    · simp
  case point.dline =>
    simp only [pairChecks, pairTest]
    split_ifs
    · exact lineChecks_iff v _ _ _ (read_val hvA) (read_dpoly hvB)
    · simp
  case dline.point =>
    simp only [pairChecks, pairTest]
    split_ifs
    · exact lineChecks_iff v _ _ _ (read_val hvB) (read_dpoly hvA)
    · simp
  case point.pauli =>
    simp only [pairChecks, pairTest]
    split_ifs
    · exact pauliChecks_iff v _ (read_val hvA) (read_pauliAns hvB)
    · simp
  case pauli.point =>
    simp only [pairChecks, pairTest]
    split_ifs
    · exact pauliChecks_iff v _ (read_val hvB) (read_pauliAns hvA)
    · simp
  case pairB.pair =>
    simp only [pairChecks, pairTest]
    split_ifs with hg
    · simp [hg]
    · simp [hg, bitEq_holds_iff v (read_bit hvA) (read_bitPair hvB _)]
  case pair.pairB =>
    simp only [pairChecks, pairTest]
    split_ifs with hg
    · simp [hg]
    · simp [hg, bitEq_holds_iff v (read_bit hvB) (read_bitPair hvA _)]
  case point.pairB =>
    simp only [pairChecks, pairTest]
    split_ifs with hW hg
    · simp [hg]
    · simp [hg, prbCheck_holds_iff v _ (read_val hvA) (read_bit hvB)]
    · simp
  case pairB.point =>
    simp only [pairChecks, pairTest]
    split_ifs with hW hg
    · simp [hg]
    · simp [hg, prbCheck_holds_iff v _ (read_val hvB) (read_bit hvA)]
    · simp
  case con.var =>
    simp only [pairChecks, pairTest]
    exact conVarChecks_iff v _ _ _ (read_bitTriple hvA) (read_bit hvB)
  case var.con =>
    simp only [pairChecks, pairTest]
    exact conVarChecks_iff v _ _ _ (read_bitTriple hvB) (read_bit hvA)
  case point.var =>
    simp only [pairChecks, pairTest]
    exact pointVarChecks_iff v _ _ _ (read_val hvA) (read_bit hvB)
  case var.point =>
    simp only [pairChecks, pairTest]
    exact pointVarChecks_iff v _ _ _ (read_val hvB) (read_bit hvA)
  all_goals simp [pairChecks, pairTest]

end Pair

/-! ## Equal types -/

theorem sameChecks_iff (L : ℕ) (a b : BitStr) (ha : a.length = L) (hb : b.length = L)
    (hN : (a ++ b).length ≤ N) :
    (∀ χ ∈ sameChecks N L, χ.Holds (bitVec N (a ++ b))) ↔ a = b := by
  simp only [sameChecks, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    LinCheck.Holds, LinearMap.add_apply, zmod2_add_eq_zero, getv_bitVec _ hN]
  have hl : ∀ l : Fin L, (a ++ b).getD l false = a.getD l false := fun l =>
    List.getD_append _ _ _ _ (by omega)
  have hr : ∀ l : Fin L, (a ++ b).getD (L + l) false = b.getD l false := fun l => by
    rw [List.getD_append_right _ _ _ _ (by omega), ha, Nat.add_sub_cancel_left]
  simp only [hl, hr]
  constructor
  · intro h
    apply List.ext_getElem (ha.trans hb.symm)
    intro l h1 h2
    have := ofBool_injective (h ⟨l, by omega⟩)
    simpa [List.getD_eq_getElem?_getD, h1, h2] using this
  · rintro rfl l
    rfl

/-! ## The constraints -/

section Cons

variable (k hk) [NeZero k] (hodd : Odd k) (j : ℕ)

/-- The decoded question has the type it was decoded at. -/
theorem questionOfBits_ty (t : Ty) (x : BitStr) :
    (PauliBinaryProgram.questionOfBits k hk hodd j t x).ty = t := by
  cases t <;> rfl

omit [NeZero k] in
include hk in
/-- The answer parser succeeds exactly at the label's length. -/
theorem parser_iff_length (T : Ty) (m : ℕ) (a : BitStr) :
    (parser (T, unary m, unary k, unary 1, a)).1 = true ↔ a.length = pauliLen m k T := by
  have hw : 0 < width T k := by cases T <;> simp only [width] <;> omega
  change Introspection.FieldAnswerParser.readyProg (countProg (T, unary m, unary k, unary 1, a),
    widthProg (T, unary m, unary k, unary 1, a), a) = true ↔ _
  rw [Introspection.FieldAnswerParser.readyProg_iff_length, countProg_apply, widthProg_length,
    length_unary, pauliLen]
  simp [hw]

omit [NeZero k] in
include hk in
/-- **The kernel's endpoint validity is the label's answer length.** -/
theorem endpointValid_iff (m : ℕ) (T : Ty) (q a : BitStr) :
    PauliBinaryProgram.endpointValid ((unary k, unary j, unary m), T, q, a) = true ↔
      a.length = pauliLen m k T := by
  rw [PauliBinaryProgram.endpointValid_apply]
  exact parser_iff_length k hk T m a

/-- The number of readable answer bits of a Pauli label. -/
def pauliLenR (m : ℕ) (T : Ty) : ℕ := if pauliRead T then pauliLen m k T else 0

/-- **The controlled linear constraints of the Pauli basis test** at the labels `t, u` and the
question payloads `x, y`, for answers of `pauliLen (2^j) k t` and `pauliLen (2^j) k u` bits.
They depend on the questions only: none of the rules reads the readable answer bits `aR, bR`
other than linearly. Equal labels compare the two answers bit by bit; distinct labels run the
checks of `pairTest` on the decoded questions. -/
def pauliCons (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (t u : Ty)
    (x y _aR _bR : BitStr) : List BitStr :=
  (if t = u then sameChecks (pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u) (pauliLen (2 ^ j) k t)
    else pairChecks k hk (pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u) hm
      (PauliBinaryProgram.questionOfBits k hk hodd j t x)
      (PauliBinaryProgram.questionOfBits k hk hodd j u y) 0 (pauliLen (2 ^ j) k t)).map
    LinCheck.toCon

/-- Every constraint has one coordinate per answer bit and one for `J`. -/
theorem length_of_mem_pauliCons (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (t u : Ty) (x y aR bR c : BitStr) (hc : c ∈ pauliCons k hk hodd j hm t u x y aR bR) :
    c.length = pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u + 1 := by
  obtain ⟨χ, -, rfl⟩ := List.mem_map.1 hc
  exact LinCheck.length_toCon χ

/-- **The Pauli basis test is its controlled linear constraints.** For answers of the label
lengths, the constraints of `pauliCons` at the readable prefixes are all satisfied by the two
answers followed by `J = 1` exactly when the Pauli basis test accepts the decoded questions and
answers, as the introspection kernel evaluates it (`program_pauli_iff`). -/
theorem pauliCons_iff (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (t u : Ty)
    (x y a b : BitStr) (ha : a.length = pauliLen (2 ^ j) k t)
    (hb : b.length = pauliLen (2 ^ j) k u) :
    (∀ c ∈ pauliCons k hk hodd j hm t u x y (a.take (pauliLenR k (2 ^ j) t))
        (b.take (pauliLenR k (2 ^ j) u)), Satisfies c (a ++ b ++ [true])) ↔
      QLD.accepts hm (PauliBinaryProgram.questionOfBits k hk hodd j t x)
        (PauliBinaryProgram.questionOfBits k hk hodd j u y)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 t a)
        (decodeBits (shoupBinField k hk) (2 ^ j) 1 u b) = true := by
  have hN : (a ++ b).length = pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u := by
    rw [List.length_append, ha, hb]
  have hra := answerBits_decodeBits k hk (2 ^ j) 1 t a ((parser_iff_length k hk t _ a).2 ha)
  have hrb := answerBits_decodeBits k hk (2 ^ j) 1 u b ((parser_iff_length k hk u _ b).2 hb)
  have hfA := decodeBits_format (shoupBinField k hk) (d := 1)
    (PauliBinaryProgram.questionOfBits k hk hodd j t x) a
  have hfB := decodeBits_format (shoupBinField k hk) (d := 1)
    (PauliBinaryProgram.questionOfBits k hk hodd j u y) b
  rw [questionOfBits_ty] at hfA hfB
  have hlhs : (∀ c ∈ pauliCons k hk hodd j hm t u x y (a.take (pauliLenR k (2 ^ j) t))
        (b.take (pauliLenR k (2 ^ j) u)), Satisfies c (a ++ b ++ [true])) ↔
      ∀ χ ∈ (if t = u then sameChecks (pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u)
          (pauliLen (2 ^ j) k t)
        else pairChecks k hk (pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u) hm
          (PauliBinaryProgram.questionOfBits k hk hodd j t x)
          (PauliBinaryProgram.questionOfBits k hk hodd j u y) 0 (pauliLen (2 ^ j) k t)),
        χ.Holds (bitVec (pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u) (a ++ b)) := by
    simp only [pauliCons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun χ _ => satisfies_toCon_iff χ _ hN
  rw [hlhs, accepts, hfA, hfB, Bool.true_and, Bool.true_and, subtests, questionOfBits_ty,
    questionOfBits_ty]
  split_ifs with htu
  · subst htu
    rw [sameChecks_iff _ a b ha hb hN.le, decide_eq_true_iff]
    constructor
    · rintro rfl; rfl
    · intro h; rw [← hra, ← hrb, h]
  · refine pairChecks_iff hm _ _ _ _ hfA hfB _ 0 _ ?_ ?_
    · rw [hra]; exact reads_left a b hN.le
    · have h := reads_right a b hN.le
      rw [ha] at h
      rw [hrb]
      exact h

end Cons

end MIPRE.Tailored.Intro.PauliCons

end

end
