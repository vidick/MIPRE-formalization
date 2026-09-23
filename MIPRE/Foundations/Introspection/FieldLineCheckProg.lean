/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.FieldPolynomialProg
import MIPRE.Foundations.Introspection.LineRepresentativeProg
import MIPRE.Foundations.CL.DetypingProgParse

/-! # Executable line-versus-point arithmetic

The program finds the first nonzero direction coordinate, checks membership
in the affine line, and evaluates the supplied polynomial at that parameter.
The zero direction denotes a singleton line and has parameter zero.
-/

noncomputable section
namespace MIPRE.Introspection.FieldLineCheck
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryPolynomial
  LineProgram FieldPolynomialProgram CL.Detyping.Program

private theorem firstPair_zero {F : Type*} [Zero F] [DecidableEq F]
    (l : List (F × F)) (h : ∀ p ∈ l, p.2 = 0) : firstPair l = (0, 0) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (by simp)
    have hl : ∀ p ∈ l, p.2 = 0 := fun p hp => h p (by simp [hp])
    simpa [firstPair, ha] using ih hl

/-- The canonical scalar parameter, including singleton lines. -/
def parameter {F : Type*} [Field F] [DecidableEq F] {m : ℕ}
    (origin direction point : Fin m → F) : F :=
  coefficient (List.ofFn fun i => (point i - origin i, direction i))

theorem parameter_eq {F : Type*} [Field F] [DecidableEq F] {m : ℕ}
    (origin direction point : Fin m → F) :
    parameter origin direction point =
      if h : ∃ j, direction j ≠ 0 then
        (point (Fin.find (fun j => direction j ≠ 0) h) -
          origin (Fin.find (fun j => direction j ≠ 0) h)) /
          direction (Fin.find (fun j => direction j ≠ 0) h)
      else 0 := by
  unfold parameter coefficient
  split
  · rename_i h
    rw [firstPair_ofFn (fun i => point i - origin i) direction h,
      if_pos (Fin.find_spec h), div_eq_mul_inv]
  · rename_i h
    have hz : ∀ i, direction i = 0 := by simpa using h
    rw [firstPair_zero _ (by
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hz i)]
    simp

theorem membership_iff {F : Type*} [Field F] [DecidableEq F] {m : ℕ}
    (origin direction point : Fin m → F) :
    point = origin + parameter origin direction point • direction ↔
      ∃ t : F, point = origin + t • direction := by
  constructor
  · exact fun h => ⟨_, h⟩
  · rintro ⟨t, ht⟩
    by_cases hd : ∃ j, direction j ≠ 0
    · have hp : parameter origin direction point = t := by
        rw [parameter_eq, dif_pos hd, ht]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
        exact mul_div_cancel_right₀ t (Fin.find_spec hd)
      rw [hp]
      exact ht
    · have hz : direction = 0 := by ext i; simpa using (not_exists.mp hd i)
      simpa [hz] using ht

def subtractProg : PolyTimeFun (List BitStr × List BitStr) (List BitStr) :=
  (map xorBitsProg).comp zip

theorem subtractProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x y : Fin m → (shoupBinField k hk).carrier) :
    subtractProg ((shoupBinField k hk).vecBits x, (shoupBinField k hk).vecBits y) =
      (shoupBinField k hk).vecBits (x - y) := by
  have hz : ((shoupBinField k hk).vecBits x).zip ((shoupBinField k hk).vecBits y) =
      List.ofFn (fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (y i))) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  change List.map xorBitsProg _ = _
  rw [zip_apply, hz]
  simp only [List.map_ofFn, Function.comp_def, xorBitsProg_apply,
    shoupXorBits_correct, BinField.vecBits, Pi.sub_apply, CharTwo.sub_eq_add]

/-- Width, origin, direction, and point. -/
def parameterProg : PolyTimeFun (Unary × List BitStr × List BitStr × List BitStr) BitStr :=
  let origin := fst.comp snd
  let direction := fst.comp (snd.comp snd)
  let point := snd.comp (snd.comp snd)
  let differences := subtractProg.comp (point.pair origin)
  coefficientBitsProg.comp (fst.pair (zip.comp (differences.pair direction)))

theorem parameterProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier) :
    parameterProg (unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point) =
      (shoupBinField k hk).toBits (parameter origin direction point) := by
  have hz : ((shoupBinField k hk).vecBits (point - origin)).zip
      ((shoupBinField k hk).vecBits direction) =
      (List.ofFn (fun i => (point i - origin i, direction i))).map
        (fun p => ((shoupBinField k hk).toBits p.1, (shoupBinField k hk).toBits p.2)) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  simp only [parameterProg, comp_apply, pair_apply, fst_apply, snd_apply,
    subtractProg_correct, zip_apply, hz, coefficientBitsProg_correct, parameter]

private def affineEntryProg : PolyTimeFun ((BitStr × BitStr) × Unary × BitStr) BitStr :=
  xorBitsProg.comp ((fst.comp fst).pair
    (shoupMulProg.comp ((fst.comp snd).pair ((snd.comp snd).pair (snd.comp fst)))))

def affineProg : PolyTimeFun (Unary × BitStr × List BitStr × List BitStr) (List BitStr) :=
  (mapWith affineEntryProg).comp
    ((zip.comp (snd.comp snd)).pair (fst.pair (fst.comp snd)))

theorem affineProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (t : (shoupBinField k hk).carrier)
    (origin direction : Fin m → (shoupBinField k hk).carrier) :
    affineProg (unary k, (shoupBinField k hk).toBits t,
      (shoupBinField k hk).vecBits origin, (shoupBinField k hk).vecBits direction) =
      (shoupBinField k hk).vecBits (origin + t • direction) := by
  have hz : ((shoupBinField k hk).vecBits origin).zip ((shoupBinField k hk).vecBits direction) =
      List.ofFn (fun i => ((shoupBinField k hk).toBits (origin i),
        (shoupBinField k hk).toBits (direction i))) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  simp only [affineProg, comp_apply, pair_apply, fst_apply, snd_apply,
    zip_apply, hz, mapWith_apply, List.map_ofFn, Function.comp_def]
  simp only [BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change xorBits ((shoupBinField k hk).toBits (origin i))
    (shoupMulProg (unary k, (shoupBinField k hk).toBits t,
      (shoupBinField k hk).toBits (direction i))) = _
  rw [shoupMulProg_encoding, shoupXorBits_correct]
  rfl

private theorem vecBits_injective {k m : ℕ} (E : BinField k) :
    Function.Injective (E.vecBits : (Fin m → E.carrier) → List BitStr) := by
  intro x y h
  simp only [BinField.vecBits, List.map_ofFn] at h
  have he := List.ofFn_injective h
  funext i
  have hi := congrArg (fun f => E.ofBits (f i)) he
  simpa only [Function.comp_apply, E.ofBits_toBits] using hi

def memberProg : PolyTimeFun (Unary × List BitStr × List BitStr × List BitStr) Bool :=
  let expected := affineProg.comp
    (fst.pair (parameterProg.pair ((fst.comp snd).pair (fst.comp (snd.comp snd)))))
  treeEq.comp ((encoded.comp (snd.comp (snd.comp snd))).pair (encoded.comp expected))

theorem memberProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier) :
    memberProg (unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point) = true ↔
      ∃ t : (shoupBinField k hk).carrier, point = origin + t • direction := by
  simp only [memberProg, comp_apply, pair_apply, fst_apply, snd_apply,
    parameterProg_correct, affineProg_correct, encoded_apply, treeEq_apply,
    decide_eq_true_eq, encode_injective.eq_iff, (vecBits_injective (shoupBinField k hk)).eq_iff,
    membership_iff]

/-- The geometric line input, polynomial coefficients, and claimed point value. -/
def lineCheckProg : PolyTimeFun
    ((Unary × List BitStr × List BitStr × List BitStr) × List BitStr × BitStr) Bool :=
  let evaluated := shoupHornerProg.comp
    ((fst.comp fst).pair ((parameterProg.comp fst).pair (fst.comp snd)))
  ite (memberProg.comp fst)
    (ArrayProg.eqBits.comp (evaluated.pair (snd.comp snd))) (const false)

theorem lineCheckProg_correct (k : ℕ) (hk : 1 ≤ k) {m n : ℕ}
    (origin direction point : Fin m → (shoupBinField k hk).carrier)
    (f : Fin n → (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) :
    lineCheckProg ((unary k, (shoupBinField k hk).vecBits origin,
      (shoupBinField k hk).vecBits direction, (shoupBinField k hk).vecBits point),
      (shoupBinField k hk).vecBits f, (shoupBinField k hk).toBits a) = true ↔
      (∃ t : (shoupBinField k hk).carrier, point = origin + t • direction) ∧
        (∑ i, f i * parameter origin direction point ^ (i : ℕ)) = a := by
  have hi : Function.Injective (shoupBinField k hk).toBits := by
    intro x y h
    simpa only [(shoupBinField k hk).ofBits_toBits] using congrArg (shoupBinField k hk).ofBits h
  simp only [lineCheckProg, PolyTimeFun.ite_apply, comp_apply, pair_apply, fst_apply, snd_apply,
    parameterProg_correct, shoupHornerProg_ofFn, ArrayProg.eqBits_apply,
    const_apply, Bool.ite_eq_true_distrib, Bool.false_eq_true,
    decide_eq_true_eq, hi.eq_iff, memberProg_correct]
  split <;> simp_all

theorem lineCheckProg_runs (input :
    (Unary × List BitStr × List BitStr × List BitStr) × List BitStr × BitStr) :
    ∃ t ≤ lineCheckProg.timeBound.eval (esize input),
      lineCheckProg.code.Runs (encode input) (encode (lineCheckProg input)) t :=
  lineCheckProg.computes input

end MIPRE.Introspection.FieldLineCheck
end
