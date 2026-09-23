/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliBooleanPrograms
import MIPRE.Background.QLD.PauliQuestionPrograms

/-! # Correctness of the uniform Pauli decision program -/

noncomputable section
namespace MIPRE.QLD.PauliBooleanProgram
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryLinear PauliCL
  PauliAnswerProgram PauliQuestionProgram PauliArithmeticProgram

def encodedInput {k m : ℕ} (E : BinField k) (j : ℕ) (T U : Ty)
    (x y : Coord m → E.carrier) (a b : Answer E.carrier m 1) : Input :=
  ((unary k, unary j, unary m),
    (T, fieldEncoding E x, answerBits E a), (U, fieldEncoding E y, answerBits E b))

@[simp] theorem explicitDecode_ty {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} (π : F ≃ F) (T : Ty) (x : Coord m → F) :
    (ExplicitSeed.decode π T x).ty = T := by cases T <;> rfl

theorem parser_for_type {k m : ℕ} (E : BinField k) (hk : 0 < k)
    (π : E.carrier ≃ E.carrier) (T : Ty) (x : Coord m → E.carrier)
    (a : Answer E.carrier m 1) (ha : (ExplicitSeed.decode π T x).fmtOk a = true) :
    PauliAnswerProgram.parser (T, unary m, unary k, unary 1, answerBits E a) =
      (true, answerRows E a) := by
  simpa using parser_answerBits E hk (ExplicitSeed.decode π T x) a ha

@[simp] theorem route_encodedInput {k m : ℕ} (E : BinField k) (j : ℕ) (T U : Ty)
    (x y : Coord m → E.carrier) (a b : Answer E.carrier m 1) :
    route (encodedInput E j T U x y a b) = PauliBranchProgram.route T U := rfl

theorem leftParser_encodedInput {k m : ℕ} (E : BinField k) (hk : 0 < k) (j : ℕ)
    (π : E.carrier ≃ E.carrier) (T U : Ty) (x y : Coord m → E.carrier)
    (a b : Answer E.carrier m 1)
    (ha : (ExplicitSeed.decode π T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode π U y).fmtOk b = true) :
    (leftParser (encodedInput E j T U x y a b)).1 = true := by
  have hpa := parser_for_type E hk π T x a ha
  have hpb := parser_for_type E hk π U y b hb
  cases hs : (PauliBranchProgram.route T U).2.1 <;>
    simp [leftParser, leftBits, left, oriented, PauliBranchProgram.orientProg_apply,
      encodedInput, endpoints, dim, width, params, route, endpointTypes, hs, hpa, hpb]

theorem rightParser_encodedInput {k m : ℕ} (E : BinField k) (hk : 0 < k) (j : ℕ)
    (π : E.carrier ≃ E.carrier) (T U : Ty) (x y : Coord m → E.carrier)
    (a b : Answer E.carrier m 1)
    (ha : (ExplicitSeed.decode π T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode π U y).fmtOk b = true) :
    (rightParser (encodedInput E j T U x y a b)).1 = true := by
  have hpa := parser_for_type E hk π T x a ha
  have hpb := parser_for_type E hk π U y b hb
  cases hs : (PauliBranchProgram.route T U).2.1 <;>
    simp [rightParser, rightBits, right, oriented, PauliBranchProgram.orientProg_apply,
      encodedInput, endpoints, dim, width, params, route, endpointTypes, hs, hpa, hpb]

theorem program_of_formatted {k m : ℕ} (E : BinField k) (hk : 0 < k) (j : ℕ)
    (π : E.carrier ≃ E.carrier) (T U : Ty) (x y : Coord m → E.carrier)
    (a b : Answer E.carrier m 1)
    (ha : (ExplicitSeed.decode π T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode π U y).fmtOk b = true) :
    let input := encodedInput E j T U x y a b
    program input = [consistency input, axisCheck input, diagonalCheck input,
      tableCheck input, pairCheck input, probeCheck input, magicCheck input,
      magicProbeCheck input].getD (PauliBranchProgram.route T U).1 true := by
  dsimp only
  rw [program_apply, leftParser_encodedInput E hk j π T U x y a b ha hb,
    rightParser_encodedInput E hk j π T U x y a b ha hb, route_encodedInput]
  simp only [Bool.true_and]

theorem explicitDecode_format_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m d : ℕ} (π : F ≃ F) (T : Ty) (x y : Coord m → F) (a : Answer F m d) :
    (ExplicitSeed.decode π T x).fmtOk a = (ExplicitSeed.decode π T y).fmtOk a := by
  cases T <;> cases a <;> rfl

theorem program_same_type {k m : ℕ} (E : BinField k) (hk : 0 < k) (j : ℕ)
    (π : E.carrier ≃ E.carrier) (T : Ty) (x y : Coord m → E.carrier)
    (a b : Answer E.carrier m 1)
    (ha : (ExplicitSeed.decode π T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode π T y).fmtOk b = true) :
    program (encodedInput E j T T x y a b) = decide (a = b) := by
  rw [program_of_formatted E hk j π T T x y a b ha hb]
  have hb' : (ExplicitSeed.decode π T x).fmtOk b = true := by
    rwa [explicitDecode_format_eq π T x y]
  simp only [PauliBranchProgram.route, ↓reduceIte, List.getD_cons_zero]
  simp only [consistency, ap₂_apply, ArrayProg.eqBits_apply, leftBits, rightBits,
    left, right, oriented, comp_apply, pair_apply, fst_apply, snd_apply,
    route, endpointTypes, PauliBranchProgram.routeProg_apply, PauliBranchProgram.route, ↓reduceIte,
    PauliBranchProgram.orientProg_apply, endpoints, encodedInput]
  apply Bool.eq_iff_iff.mpr
  simpa using
    answerBits_injective_of_format E hk (ExplicitSeed.decode π T x) a b ha hb'

private theorem seed_fieldEncoding {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    Introspection.PauliStageProgram.seed (fieldEncoding E x) = E.toBits (x .seed) := rfl

private theorem direction_fieldEncoding {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    Introspection.PauliStageProgram.direction (fieldEncoding E x) =
      E.vecBits (fun i => x (.direction i)) := rfl

theorem program_axis (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (W : Bas)
    (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) (f : LIDT.LinePoly (shoupBinField k hk).carrier 1) :
    program (encodedInput (shoupBinField k hk) j (.point W) (.aline W) x y (.val a) (.apoly f)) =
      lowDeg (fun i => y (.point W i))
        (Pi.single (LIDT.CL.chi hm (ExplicitSeed.seedPermutation (shoupBinField k hk) (y .seed))) 1)
        (fun i => x (.point W i)) f a := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.point W) x (.val a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.aline W) y (.apoly f) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.point W) (.aline W) x y (.val a) (.apoly f) rfl rfl]
  have hr : PauliBranchProgram.route (.point W) (.aline W) =
      (1, false, PauliBranchProgram.basisIndex W, 0) := by
    simp [PauliBranchProgram.route, PauliBranchProgram.pairRoute]
  rw [hr]
  change axisCheck _ = _
  simp only [axisCheck, comp_apply, pair_apply, width, params, origin, point, axis,
    leftValue, leftRows, rightRows, leftParser, rightParser, leftBits, rightBits,
    leftFields, rightFields, left, right, oriented, basis, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, hr, PauliBranchProgram.orientProg_apply,
    Bool.false_eq_true, ↓reduceIte, hpa, hpb, nthD_apply,
    PauliAnswerProgram.answerRows, List.getD_cons_zero,
    selectedPoint_fieldEncoding, seed_fieldEncoding, axisDirectionProg_legacy k hk j hj hm,
    lineCheckProg_eq_lowDeg k hk]

theorem program_diagonal (k : ℕ) (hk : 1 ≤ k) (j m : ℕ) (W : Bas)
    (x y : Coord m → (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) (f : LIDT.LinePoly (shoupBinField k hk).carrier (m * 1)) :
    program (encodedInput (shoupBinField k hk) j (.point W) (.dline W) x y (.val a) (.dpoly f)) =
      lowDeg (fun i => y (.point W i)) (fun i => y (.direction i))
        (fun i => x (.point W i)) f a := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.point W) x (.val a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.dline W) y (.dpoly f) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.point W) (.dline W) x y (.val a) (.dpoly f) rfl rfl]
  have hr : PauliBranchProgram.route (.point W) (.dline W) =
      (2, false, PauliBranchProgram.basisIndex W, 0) := by
    simp [PauliBranchProgram.route, PauliBranchProgram.pairRoute]
  rw [hr]
  change diagonalCheck _ = _
  simp only [diagonalCheck, comp_apply, pair_apply, width, params, origin, point,
    leftValue, leftRows, rightRows, leftParser, rightParser, leftBits, rightBits,
    leftFields, rightFields, left, right, oriented, basis, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, hr, PauliBranchProgram.orientProg_apply,
    Bool.false_eq_true, ↓reduceIte, hpa, hpb, nthD_apply,
    PauliAnswerProgram.answerRows, List.getD_cons_zero,
    selectedPoint_fieldEncoding, direction_fieldEncoding, lineCheckProg_eq_lowDeg k hk]

theorem program_table (k : ℕ) (hk : 1 ≤ k) (j m : ℕ) (W : Bas)
    (x y : Coord m → (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) (h : (Fin m → Bool) → (shoupBinField k hk).carrier) :
    program (encodedInput (shoupBinField k hk) j (.point W) (.pauli W) x y (.val a) (.pauliAns h)) =
      decide (MvPolynomial.eval (fun i => x (.point W i)) (ldEnc h) = a) := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.point W) x (.val a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.pauli W) y (.pauliAns h) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.point W) (.pauli W) x y (.val a) (.pauliAns h) rfl rfl]
  have hr : PauliBranchProgram.route (.point W) (.pauli W) =
      (3, false, PauliBranchProgram.basisIndex W, 0) := by
    simp [PauliBranchProgram.route, PauliBranchProgram.pairRoute]
  rw [hr]
  change tableCheck _ = _
  simp only [tableCheck, comp_apply, pair_apply, width, params, point,
    leftValue, leftRows, rightRows, leftParser, rightParser, leftBits, rightBits,
    leftFields, left, right, oriented, basis, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, hr, PauliBranchProgram.orientProg_apply,
    Bool.false_eq_true, ↓reduceIte, hpa, hpb, nthD_apply,
    PauliAnswerProgram.answerRows, List.getD_cons_zero, selectedPoint_fieldEncoding]
  exact fullAnswerCheckProg_correct k hk (fun i => x (.point W i)) h a

private theorem bit_ne_zero (b : ZMod 2) : bit b = decide (b ≠ 0) := by
  revert b
  decide

private theorem boolEq_bits (a b : ZMod 2) : boolEq (bit a, bit b) = decide (a = b) := by
  revert a b
  decide

theorem program_pair (k : ℕ) (hk : 1 ≤ k) (j m : ℕ) (W : Bas)
    (x y : Coord m → (shoupBinField k hk).carrier) (a : ZMod 2) (b : Bas → ZMod 2) :
    program (encodedInput (shoupBinField k hk) j (.pairB W) .pair x y (.bit a) (.bitPair b)) =
      (decide (gam (vectorContent y).omega ≠ 0) || decide (a = b W)) := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.pairB W) x (.bit a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) .pair y (.bitPair b) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.pairB W) .pair x y (.bit a) (.bitPair b) rfl rfl]
  have hr : PauliBranchProgram.route (.pairB W) .pair =
      (4, false, PauliBranchProgram.basisIndex W, 0) := by
    simp [PauliBranchProgram.route, PauliBranchProgram.pairRoute]
  rw [hr]
  change pairCheck _ = _
  simp only [pairCheck, ap₂_apply, comp_apply, pair_apply, width, params, gamma,
    leftBit, bitAt, leftRows, rightRows, leftParser, rightParser, leftBits, rightBits,
    rightFields, left, right, oriented, basis, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, hr, PauliBranchProgram.orientProg_apply,
    Bool.false_eq_true, ↓reduceIte, hpa, hpb, nthD_apply, SAT.ArrayProg.getD_apply,
    PauliAnswerProgram.answerRows, List.getD_cons_zero, zip_apply,
    gammaProg_fieldEncoding k hk]
  cases W <;> simp only [PauliBranchProgram.basisIndex, List.getD_cons_zero,
    List.getD_cons_succ, boolEq_bits, boolOr, finiteFunction_apply]
  all_goals rw [bit_ne_zero]

theorem program_probe (k : ℕ) (hk : 1 ≤ k) (j m : ℕ) (W : Bas)
    (x y : Coord m → (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier)
    (b : ZMod 2) :
    program (encodedInput (shoupBinField k hk) j (.point W) (.pairB W) x y (.val a) (.bit b)) =
      (decide (gam (vectorContent y).omega ≠ 0) || decide (prb a (y (.scalar W)) = b)) := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.point W) x (.val a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.pairB W) y (.bit b) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.point W) (.pairB W) x y (.val a) (.bit b) rfl rfl]
  have hr : PauliBranchProgram.route (.point W) (.pairB W) =
      (5, false, PauliBranchProgram.basisIndex W, 0) := by
    simp [PauliBranchProgram.route, PauliBranchProgram.pairRoute]
  rw [hr]
  change probeCheck _ = _
  simp only [probeCheck, ap₂_apply, comp_apply, pair_apply, width, params, gamma, probe, scalar,
    leftValue, rightBit, bitAt, leftRows, rightRows, leftParser, rightParser, leftBits, rightBits,
    rightFields, left, right, oriented, basis, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, hr, PauliBranchProgram.orientProg_apply,
    Bool.false_eq_true, ↓reduceIte, hpa, hpb, nthD_apply, SAT.ArrayProg.getD_apply,
    PauliAnswerProgram.answerRows, List.getD_cons_zero, zip_apply,
    gammaProg_fieldEncoding k hk, selectedScalar_fieldEncoding,
    probeProg_eq_prb k hk, boolEq_bits, boolOr, finiteFunction_apply]
  rw [bit_ne_zero]

private theorem boolNot_bit (a : ZMod 2) : boolNot (bit a) = decide (a = 0) := by
  revert a
  decide

private theorem bitAt_ofFn {n : ℕ} (a : Fin n → ZMod 2) (i : Fin n) :
    bitAt (i.val, List.ofFn fun j => [bit (a j)]) = bit (a i) := by
  simp [bitAt, List.getD_eq_getElem?_getD]

private theorem parity_bits (a : Fin 3 → ZMod 2) :
    parityProg (bit (a 0), bit (a 1), bit (a 2)) = bit (∑ i, a i) := by
  simp [parityProg, Fin.sum_univ_succ, add_assoc]

theorem program_magic (k : ℕ) (hk : 1 ≤ k) (j m : ℕ)
    (i : Fin LCS.MagicSquare.layout.r) (v : Fin LCS.MagicSquare.layout.s)
    (x y : Coord m → (shoupBinField k hk).carrier) (a : Fin 3 → ZMod 2) (b : ZMod 2) :
    program (encodedInput (shoupBinField k hk) j (.con i) (.var v) x y (.bitTriple a) (.bit b)) =
      (decide (gam (vectorContent y).omega = 0) ||
        (decide (v ∈ LCS.MagicSquare.layout.V i) &&
          decide (∑ z, a z = LCS.MagicSquare.game.b i) &&
            decide (a (LCS.MagicSquare.cellIdx i v) = b))) := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.con i) x (.bitTriple a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.var v) y (.bit b) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.con i) (.var v) x y (.bitTriple a) (.bit b) rfl rfl, PauliBranchProgram.route_con_var]
  change magicCheck _ = _
  simp only [magicCheck, ap₂_apply, comp_apply, pair_apply, width, params, gamma,
    magicMetadata, magicTypes, magicInfo, leftParity, rightBit,
    leftRows, rightRows, leftParser, rightParser, leftBits, rightBits,
    rightFields, left, right, oriented, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, PauliBranchProgram.route_con_var,
    PauliBranchProgram.orientProg_apply, Bool.false_eq_true, ↓reduceIte,
    hpa, hpb, PauliAnswerProgram.answerRows, zip_apply, gammaProg_fieldEncoding k hk,
    finiteFunction_apply, bitAt_ofFn, boolNot_bit]
  simp only [bitAt, comp_apply, nthD_apply, SAT.ArrayProg.getD_apply,
    List.getD_cons_zero, boolEq_bits, boolOr, boolAnd, finiteFunction_apply, Bool.and_assoc]
  simp [parity_bits, boolEq_bits]

theorem program_magicProbe (k : ℕ) (hk : 1 ≤ k) (j m : ℕ) (W : Bas)
    (v : Fin LCS.MagicSquare.layout.s)
    (x y : Coord m → (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) (b : ZMod 2) :
    program (encodedInput (shoupBinField k hk) j (.point W) (.var v) x y (.val a) (.bit b)) =
      (decide (gam (vectorContent y).omega = 0) ||
        (PauliBooleanProgram.probeEligible (.point W, .var v) && decide (prb a (y (.scalar W)) = b))) := by
  have hpa := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.point W) x (.val a) rfl
  have hpb := parser_for_type (shoupBinField k hk) hk (Equiv.refl _) (.var v) y (.bit b) rfl
  rw [program_of_formatted (shoupBinField k hk) hk j (Equiv.refl _)
    (.point W) (.var v) x y (.val a) (.bit b) rfl rfl]
  have hr : PauliBranchProgram.route (.point W) (.var v) =
      (7, false, PauliBranchProgram.basisIndex W, v.val) := by
    simp [PauliBranchProgram.route, PauliBranchProgram.pairRoute]
  rw [hr]
  change magicProbeCheck _ = _
  simp only [magicProbeCheck, ap₂_apply, comp_apply, pair_apply, width, params, gamma, probe, scalar,
    magicTypes, leftValue, rightBit, bitAt, leftRows, rightRows, leftParser, rightParser,
    leftBits, rightBits, rightFields, left, right, oriented, basis, route, endpointTypes,
    endpoints, encodedInput, fst_apply, snd_apply, dim, const_apply,
    PauliBranchProgram.routeProg_apply, hr, PauliBranchProgram.orientProg_apply,
    Bool.false_eq_true, ↓reduceIte, hpa, hpb, nthD_apply, SAT.ArrayProg.getD_apply,
    PauliAnswerProgram.answerRows, List.getD_cons_zero, zip_apply,
    gammaProg_fieldEncoding k hk, selectedScalar_fieldEncoding, probeProg_eq_prb k hk,
    boolNot_bit, boolEq_bits, boolOr, boolAnd, finiteFunction_apply]

end MIPRE.QLD.PauliBooleanProgram
end
