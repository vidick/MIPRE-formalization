/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Introspection.HonestPauliMeasurements
public import MIPRE.Background.QLD.PauliAnswerCoding
public import MIPRE.Foundations.SAT.NormalElementProg
public import MIPRE.Tailored.Intro.Binary
public import MIPRE.Tailored.Intro.Bits

@[expose] public section

/-!
# The bits of the honest Pauli basis test measurements

The honest strategy answers the twenty-six Pauli question types with
`MIPRE.QLD.Honest.answerOp`, and the introspection verifier reads the answers through their bit
encoding `QLD.PauliAnswerProgram.answerBits` (field elements in Shoup's polynomial basis, rows
flattened). This file shows that every answer bit is a signed permutation observable, and a
diagonal one at the readable `(Pauli, Z)` question (`isXBit_answerOp`, `isZBit_answerOp_pauliZ`):

* the point, line and Pauli answers are `F_q`-linear functions of the outcome of the `X`- or
  `Z`-basis measurement, and the bits of Shoup's representation are `F₂`-linear
  (`shoupXorBits_correct`), so each answer bit is an `F₂`-linear functional of the outcome, whose
  observable is a Weyl operator (`exists_encObs_proj_linear`); every bit of a `Z`-basis outcome
  is a `±1` diagonal;
* the probe answers read `½(1 ± W(c))` of a Weyl operator, and the Magic Square answers the
  cells of `Introspection.HonestMagicSquare.grid` of two Weyl operators, which are signed
  permutations
  (`isSignedPerm_grid`); in the inactive branches the answer is constant.
-/

namespace MIPRE.Tailored.Intro

open Finset Matrix MIPRE.Weyl MIPRE.QLD MIPRE.QLD.Honest
open MIPRE.LowDegree.BinaryPolynomial
open scoped Kronecker

set_option linter.unusedSectionVars false

/-! ## `F₂`-linear bits -/

/-- A bit that is additive (the bit of a sum is the exclusive or) is an `F₂`-linear
functional. -/
theorem exists_dual_of_xor {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] (β : X → Bool)
    (hβ : ∀ x y, β (x + y) = xor (β x) (β y)) :
    ∃ ψ : Module.Dual (ZMod 2) X, ∀ x, β x = decide (ψ x = 1) := by
  have h0 : β 0 = false := by
    have := hβ 0 0
    rw [add_zero] at this
    cases h : β 0 <;> simp_all
  let g : X →+ ZMod 2 :=
    { toFun := fun x => if β x then 1 else 0
      map_zero' := by simp [h0]
      map_add' := fun x y => by
        rw [hβ]
        cases β x <;> cases β y <;> decide }
  refine ⟨g.toZModLinearMap 2, fun x => ?_⟩
  change β x = decide ((if β x then (1 : ZMod 2) else 0) = 1)
  cases β x <;> decide

theorem getD_xorBits (l l' : Cost.BitStr) (h : l.length = l'.length) (i : ℕ) :
    (xorBits l l').getD i false = xor (l.getD i false) (l'.getD i false) := by
  unfold xorBits
  by_cases hi : i < l.length
  · simp [List.getD_eq_getElem?_getD, hi, h ▸ hi]
  · have hi' : ¬i < l'.length := h ▸ hi
    simp [List.getD_eq_getElem?_getD, hi, hi']

section Shoup

variable {k : ℕ} (hk : 1 ≤ k)

theorem length_flatten_vecBits {n : ℕ} (v : Fin n → (SAT.shoupBinField k hk).carrier) :
    ((SAT.shoupBinField k hk).vecBits v).flatten.length = n * k := by
  induction n with
  | zero => simp [SAT.BinField.vecBits]
  | succ n ih =>
    have := ih (fun i => v i.succ)
    simp only [SAT.BinField.vecBits, List.ofFn_succ, List.map_cons, List.flatten_cons,
      List.length_append, SAT.BinField.length_toBits] at this ⊢
    rw [this]
    ring

/-- **The bits of a vector of field elements are additive.** -/
theorem flatten_vecBits_add {n : ℕ} (v w : Fin n → (SAT.shoupBinField k hk).carrier) :
    ((SAT.shoupBinField k hk).vecBits (v + w)).flatten =
      xorBits ((SAT.shoupBinField k hk).vecBits v).flatten
        ((SAT.shoupBinField k hk).vecBits w).flatten := by
  induction n with
  | zero => simp [SAT.BinField.vecBits, xorBits]
  | succ n ih =>
    have := ih (fun i => v i.succ) (fun i => w i.succ)
    simp only [SAT.BinField.vecBits, List.ofFn_succ, List.map_cons, List.flatten_cons,
      Pi.add_apply] at this ⊢
    rw [show ((fun i : Fin n => v i.succ) + fun i : Fin n => w i.succ) =
      fun i : Fin n => v i.succ + w i.succ from rfl] at this
    rw [this, ← SAT.shoupXorBits_correct, xorBits, xorBits, xorBits, List.zipWith_append]
    rw [SAT.BinField.length_toBits, SAT.BinField.length_toBits]

theorem getD_flatten_vecBits_add {n : ℕ} (v w : Fin n → (SAT.shoupBinField k hk).carrier)
    (i : ℕ) :
    ((SAT.shoupBinField k hk).vecBits (v + w)).flatten.getD i false =
      xor (((SAT.shoupBinField k hk).vecBits v).flatten.getD i false)
        (((SAT.shoupBinField k hk).vecBits w).flatten.getD i false) := by
  rw [flatten_vecBits_add, getD_xorBits _ _ (by rw [length_flatten_vecBits,
    length_flatten_vecBits])]

end Shoup

/-! ## The Pauli measurements -/

section Pauli

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}

theorem isSignedPerm_basis (W : Bas) (c : Register F m) : IsSignedPerm (basis W c) := by
  cases W
  · exact isSignedPerm_wX c
  · exact isSignedPerm_wZ c

/-- **An additive bit of a Pauli outcome is a signed permutation.** -/
theorem isXBit_pauliOp (W : Bas) (β : Register F m → Bool)
    (hβ : ∀ x y, β (x + y) = xor (β x) (β y)) : IsXBit (pauliOp (F := F) (m := m) W) β := by
  obtain ⟨ψ, hψ⟩ := exists_dual_of_xor β hβ
  obtain ⟨c, hc⟩ := exists_encObs_proj_linear (basis (F := F) (m := m) W) (k := 1)
    (fun _ => ψ) 0
  unfold IsXBit
  have e : bitObs (pauliOp (F := F) (m := m) W) β =
      encObs (proj (basis W)) (fun e (j : Fin 1) => decide ((fun _ => ψ) j e = 1)) 0 := by
    rw [encObs_eq_bitObs]
    exact congrArg _ (funext hψ)
  rw [e, hc]
  exact isSignedPerm_basis W c

/-- **Every bit of a `Z`-basis outcome is a `±1` diagonal.** -/
theorem isZBit_pauliOp_Z (β : Register F m → Bool) :
    IsZBit (pauliOp (F := F) (m := m) .Z) β := by
  have h := isSignedPerm_encObs_zProj (F := F) (n := Fin m → Bool) (k := 1)
    (fun e _ => β e) 0
  have e : (pauliOp (F := F) (m := m) .Z) = zProj := funext fun c => proj_wZ c
  unfold IsZBit
  rw [e]
  exact h

theorem isXBit_pauliLift (W : Bas) (β : Register F m → Bool)
    (hβ : ∀ x y, β (x + y) = xor (β x) (β y)) :
    IsXBit (QLD.Honest.pauliLift (F := F) (m := m) W) β :=
  (isXBit_pauliOp W β hβ).kronecker_one

theorem isZBit_pauliLift_Z (β : Register F m → Bool) :
    IsZBit (QLD.Honest.pauliLift (F := F) (m := m) .Z) β :=
  (isZBit_pauliOp_Z β).kronecker_one

/-- The probe label is additive in the outcome. -/
theorem probeLabel_add (ω : Omega F m) (W : Bas) (h h' : Register F m) :
    probeLabel ω W (h + h') = probeLabel ω W h + probeLabel ω W h' := by
  rw [← probeVector_trace, ← probeVector_trace, ← probeVector_trace]
  simp [trDot, Finset.sum_add_distrib, mul_add, map_add]

/-- **Any bit of the probe's outcome is a signed permutation**: a binary outcome's bit is
constant or affine, and the probe reads an `F₂`-linear functional of a Pauli outcome. -/
theorem isXBit_probeLift (ω : Omega F m) (W : Bas) (g : ZMod 2 → Bool) :
    IsXBit (probeLift ω W) g := by
  unfold probeLift
  refine IsXBit.kronecker_one ?_
  unfold probeOp
  rw [fibSum_eq_merge, isXBit_merge_iff]
  have hc : ∀ b : ZMod 2, g b = xor (g 0) (xor (g 0) (g 1) && decide (b = 1)) := by
    intro b
    fin_cases b
    · show g 0 = xor (g 0) (xor (g 0) (g 1) && false)
      simp
    · show g 1 = xor (g 0) (xor (g 0) (g 1) && true)
      cases g 0 <;> cases g 1 <;> rfl
  have e : (g ∘ probeLabel ω W) =
      fun h => xor (g 0) (xor (g 0) (g 1) && decide (probeLabel ω W h = 1)) :=
    funext fun h => hc _
  rw [e]
  refine IsXBit.xor (pauliOp_isPVM W).toIn
    (isZBit_const (pauliOp_isPVM W).toIn (g 0)).isXBit (isXBit_pauliOp W _ fun x y => ?_)
  rw [probeLabel_add]
  generalize probeLabel ω W x = a
  generalize probeLabel ω W y = b
  generalize xor (g 0) (g 1) = c
  revert a b c
  decide

theorem ldEnc_add (h h' : Register F m) :
    LowDegree.ldEnc (h + h') = LowDegree.ldEnc h + LowDegree.ldEnc h' := by
  simp [LowDegree.ldEnc, Finset.sum_add_distrib, add_mul]

theorem lineAnswer_add (n : ℕ) (u v : LIDT.Point F m) (h h' : Register F m) :
    lineAnswer n u v (h + h') = lineAnswer n u v h + lineAnswer n u v h' := by
  funext i
  simp [lineAnswer, ldEnc_add, LowDegree.lineRestrict, map_add]

end Pauli

/-! ## Binary measurements and the Magic Square -/

section Square

variable {Ω A B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype A] [Fintype B]

theorem sum_observableToProjector (O : Matrix Ω Ω ℂ) :
    ∑ b : ZMod 2, LCS.observableToProjector O b = 1 := by
  rw [univ_zmod_two, Finset.sum_pair (by decide)]
  simp only [LCS.observableToProjector, LCS.observableSign]
  simp only [↓reduceIte, one_ne_zero]
  module

theorem isXBit_mul_fst {P : A → Matrix Ω Ω ℂ} {Q : B → Matrix Ω Ω ℂ} (hQ : ∑ b, Q b = 1)
    {f : A → Bool} (h : IsXBit P f) :
    IsXBit (fun ab : A × B => P ab.1 * Q ab.2) fun ab => f ab.1 := by
  unfold IsXBit at *
  rwa [bitObs_mul_fst P Q hQ]

theorem isXBit_mul_snd {P : A → Matrix Ω Ω ℂ} {Q : B → Matrix Ω Ω ℂ} (hP : ∑ a, P a = 1)
    {f : B → Bool} (h : IsXBit Q f) :
    IsXBit (fun ab : A × B => P ab.1 * Q ab.2) fun ab => f ab.2 := by
  unfold IsXBit at *
  rwa [bitObs_mul_snd P Q hP]

/-- A bit of a binary outcome is constant or affine. -/
theorem bool_affine (g : ZMod 2 → Bool) (b : ZMod 2) :
    g b = xor (g 0) (decide (b = 1) && xor (g 0) (g 1)) := by
  fin_cases b
  · show g 0 = xor (g 0) (false && xor (g 0) (g 1))
    simp
  · show g 1 = xor (g 0) (true && xor (g 0) (g 1))
    cases g 0 <;> cases g 1 <;> rfl

/-- **Any bit of the binary measurement `½(1 ± O)` of a signed permutation is one.** -/
theorem isXBit_observableToProjector {O : Matrix Ω Ω ℂ} (hO : IsSignedPerm O)
    (g : ZMod 2 → Bool) : IsXBit (LCS.observableToProjector O) g := by
  unfold IsXBit
  rw [show bitObs (LCS.observableToProjector O) g =
    encObs (LCS.observableToProjector O) (fun b (_ : Fin 1) => g b) 0 from rfl]
  cases h : xor (g 0) (g 1)
  · rw [encObs_observableToProjector_const _ _ 0 (g 0) fun b => by
      rw [bool_affine g b, h]; simp]
    exact isSignedPerm_bitSign_smul_one _
  · rw [encObs_observableToProjector _ _ 0 (g 0) fun b => by
      rw [bool_affine g b, h]; simp]
    cases g 0
    · simpa [bitSign] using hO
    · simpa [bitSign] using hO.neg

end Square

/-! ## The answers -/

section Answers

variable {k : ℕ} (hk : 1 ≤ k) {m d : ℕ} [NeZero m]
variable [Algebra (ZMod 2) (SAT.shoupBinField k hk).carrier]

/-- The `i`-th bit of the encoded answer. -/
noncomputable def answerBit (i : ℕ) (a : Answer (SAT.shoupBinField k hk).carrier m d) : Bool :=
  (PauliAnswerProgram.answerBits (SAT.shoupBinField k hk) a).getD i false

/-- A bit of an answer whose encoding is that of a vector additive in the outcome is
additive. -/
theorem answerBit_add_of {n : ℕ} (a : Register (SAT.shoupBinField k hk).carrier m →
    Answer (SAT.shoupBinField k hk).carrier m d)
    (v : Register (SAT.shoupBinField k hk).carrier m → Fin n → (SAT.shoupBinField k hk).carrier)
    (hav : ∀ h, PauliAnswerProgram.answerBits (SAT.shoupBinField k hk) (a h) =
      ((SAT.shoupBinField k hk).vecBits (v h)).flatten)
    (hv : ∀ h h', v (h + h') = v h + v h') (i : ℕ) (h h' : Register _ m) :
    answerBit hk i (a (h + h')) = xor (answerBit hk i (a h)) (answerBit hk i (a h')) := by
  unfold answerBit
  rw [hav, hav, hav, hv, getD_flatten_vecBits_add]

theorem isXBit_pauliLift_answer {n : ℕ} (W : Bas)
    (a : Register (SAT.shoupBinField k hk).carrier m → Answer (SAT.shoupBinField k hk).carrier m d)
    (v : Register (SAT.shoupBinField k hk).carrier m → Fin n → (SAT.shoupBinField k hk).carrier)
    (hav : ∀ h, PauliAnswerProgram.answerBits (SAT.shoupBinField k hk) (a h) =
      ((SAT.shoupBinField k hk).vecBits (v h)).flatten)
    (hv : ∀ h h', v (h + h') = v h + v h') (i : ℕ) :
    IsXBit (fibSum (QLD.Honest.pauliLift W) a) (answerBit hk i) := by
  rw [fibSum_eq_merge, isXBit_merge_iff]
  exact isXBit_pauliLift W _ (answerBit_add_of hk a v hav hv i)

/-- **Every answer bit of the honest Pauli basis test measurement is a signed permutation.** -/
theorem isXBit_answerOp (hm : m ∣ Fintype.card (SAT.shoupBinField k hk).carrier)
    (q : Question (SAT.shoupBinField k hk).carrier m) (i : ℕ) :
    IsXBit (answerOp (d := d) hm q) (answerBit hk i) := by
  cases q with
  | point W u =>
    refine isXBit_pauliLift_answer hk (n := 1) W _
      (fun h (_ : Fin 1) => MvPolynomial.eval u (LowDegree.ldEnc h)) (fun h => ?_)
      (fun h h' => ?_) i
    · simp [PauliAnswerProgram.answerBits, PauliAnswerProgram.answerRows,
        SAT.BinField.vecBits]
    · funext j
      simp [ldEnc_add]
  | aline W u s =>
    exact isXBit_pauliLift_answer hk W _ _ (fun h => rfl)
      (fun h h' => lineAnswer_add _ _ _ h h') i
  | dline W u s v =>
    exact isXBit_pauliLift_answer hk W _ _ (fun h => rfl)
      (fun h h' => lineAnswer_add _ _ _ h h') i
  | pauli W =>
    exact isXBit_pauliLift_answer hk W _ _ (fun h => rfl) (fun h h' => rfl) i
  | pairB W ω =>
    change IsXBit (fibSum (pairBBranch ω W) Answer.bit) _
    rw [fibSum_eq_merge, isXBit_merge_iff]
    unfold pairBBranch
    split_ifs
    · exact isXBit_probeLift ω W _
    · exact (isZBit_readout _ _).isXBit
  | pair ω =>
    change IsXBit (fibSum (pairBranch ω) Answer.bitPair) _
    rw [fibSum_eq_merge, isXBit_merge_iff]
    unfold pairBranch
    split_ifs
    · rw [fibSum_eq_merge, isXBit_merge_iff]
      have hX := (probeLift_isPVM ω .X).sum_eq_one
      have hZ := (probeLift_isPVM ω .Z).sum_eq_one
      by_cases hi : i = 1
      · subst hi
        have e : ((answerBit hk 1 ∘ Answer.bitPair (F := (SAT.shoupBinField k hk).carrier)
            (m := m) (d := d)) ∘ pairLabel) = fun p => LowDegree.BinaryLinear.bit p.2 := by
          funext p
          simp [answerBit, PauliAnswerProgram.answerBits, PauliAnswerProgram.answerRows,
            pairLabel]
        rw [e]
        exact isXBit_mul_snd hX (isXBit_probeLift ω .Z _)
      · have e : ((answerBit hk i ∘ Answer.bitPair (F := (SAT.shoupBinField k hk).carrier)
            (m := m) (d := d)) ∘ pairLabel) =
            fun p => [LowDegree.BinaryLinear.bit p.1, false].getD i false := by
          funext p
          rcases i with _ | _ | i
          · simp [answerBit, PauliAnswerProgram.answerBits, PauliAnswerProgram.answerRows,
              pairLabel]
          · exact absurd rfl hi
          · simp [answerBit, PauliAnswerProgram.answerBits, PauliAnswerProgram.answerRows]
        rw [e]
        exact isXBit_mul_fst hZ
          (isXBit_probeLift ω .X fun b => [LowDegree.BinaryLinear.bit b, false].getD i false)
    · exact (isZBit_readout _ _).isXBit
  | con c ω =>
    change IsXBit (fibSum (constraintBranch ω c) Answer.bitTriple) _
    rw [fibSum_eq_merge, isXBit_merge_iff]
    unfold constraintBranch
    split_ifs with hg
    · exact (isZBit_readout _ _).isXBit
    · set A := basis .X (probeVector ω .X)
      set B := basis .Z (probeVector ω .Z)
      have hA : IsSignedPerm A := isSignedPerm_basis _ _
      have hB : IsSignedPerm B := isSignedPerm_basis _ _
      set V := fun j : Fin 3 =>
        Introspection.HonestMagicSquare.variableOp A B
          (Introspection.HonestMagicSquare.cellIndex c j)
      have hV : ∀ j, ∑ b, V j b = 1 := fun j => sum_observableToProjector _
      have hVX : ∀ j g, IsXBit (V j) g := fun j g =>
        isXBit_observableToProjector (isSignedPerm_grid hA hB _) g
      set G := answerBit hk i ∘ Answer.bitTriple (F := (SAT.shoupBinField k hk).carrier)
        (m := m) (d := d)
      let J : (ZMod 2 × ZMod 2) × ZMod 2 → Matrix _ _ ℂ := fun p => V 0 p.1.1 * V 1 p.1.2 * V 2 p.2
      have hJ : (Introspection.HonestMagicSquare.constraintOp A B c) =
          fun a => J (Introspection.HonestMagicSquare.tripleEquiv a) := rfl
      have hG : G = (G ∘ Introspection.HonestMagicSquare.tripleEquiv.symm) ∘
          Introspection.HonestMagicSquare.tripleEquiv := by
        funext a
        simp
      unfold IsXBit
      rw [hJ, hG, bitObs_comp_equiv]
      have hG' : G ∘ Introspection.HonestMagicSquare.tripleEquiv.symm =
          fun p => (List.ofFn fun j : Fin 3 =>
            [LowDegree.BinaryLinear.bit (![p.1.1, p.1.2, p.2] j)]).flatten.getD i false := by
        funext p
        rfl
      rw [hG']
      have h01 : ∑ p : ZMod 2 × ZMod 2, V 0 p.1 * V 1 p.2 = 1 := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, hV, mul_one]
        exact hV 0
      rcases i with _ | _ | _ | i
      · refine (isXBit_mul_fst (hV 2) (isXBit_mul_fst (hV 1)
          (hVX 0 LowDegree.BinaryLinear.bit))).congr fun p _ => ?_
        simp [List.ofFn_succ]
      · refine (isXBit_mul_fst (hV 2) (isXBit_mul_snd (hV 0)
          (hVX 1 LowDegree.BinaryLinear.bit))).congr fun p _ => ?_
        simp [List.ofFn_succ]
      · refine (isXBit_mul_snd h01 (hVX 2 LowDegree.BinaryLinear.bit)).congr fun p _ => ?_
        simp [List.ofFn_succ]
      · refine (isXBit_mul_snd h01 (hVX 2 fun _ => false)).congr fun p _ => ?_
        simp [List.ofFn_succ]
  | var j ω =>
    change IsXBit (fibSum (variableBranch ω j) Answer.bit) _
    rw [fibSum_eq_merge, isXBit_merge_iff]
    unfold variableBranch
    split_ifs
    · exact (isZBit_readout _ _).isXBit
    · exact isXBit_observableToProjector (isSignedPerm_grid (isSignedPerm_basis _ _)
        (isSignedPerm_basis _ _) _) _

/-- **Every answer bit of the honest `(Pauli, Z)` measurement is a `±1` diagonal.** -/
theorem isZBit_answerOp_pauliZ (hm : m ∣ Fintype.card (SAT.shoupBinField k hk).carrier)
    (i : ℕ) : IsZBit (answerOp (d := d) hm (.pauli .Z)) (answerBit hk i) := by
  change IsZBit (fibSum (QLD.Honest.pauliLift .Z) Answer.pauliAns) _
  rw [fibSum_eq_merge, isZBit_merge_iff]
  exact isZBit_pauliLift_Z _

end Answers

end MIPRE.Tailored.Intro

end
