/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestFirstHide
import MIPRE.Foundations.Introspection.RegisterTransport

/-! # The adaptive honest Read and Hide measurements

The recursion follows the CL presentation itself. At a `cons` node the joint
Z/linear and X/dual-linear measurement is made on the current register. Its Z
outcome selects the continuation on the complementary register. These are
actual projective measurements; no commutation assumption on different
continuations is needed.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

section AdaptiveTensor

variable {I J A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

/-- Measure one register and use its outcome to select a measurement of the other. -/
def adaptiveTensor (P : A → Matrix I I ℂ) (Q : A → B → Matrix J J ℂ)
    (ab : A × B) : Matrix (I × J) (I × J) ℂ := P ab.1 ⊗ₖ Q ab.1 ab.2

theorem adaptiveTensor_isPVM (P : A → Matrix I I ℂ) (Q : A → B → Matrix J J ℂ)
    (hP : IsPVM P) (hQ : ∀ a, IsPVM (Q a)) : IsPVM (adaptiveTensor P Q) where
  isSelfAdjoint ab := by
    simp only [adaptiveTensor, Matrix.conjTranspose_kronecker,
      hP.isSelfAdjoint, (hQ _).isSelfAdjoint]
  idem ab := by
    simp only [adaptiveTensor, ← Matrix.mul_kronecker_mul, hP.idem, (hQ _).idem]
  sum_eq_one := by
    simp only [adaptiveTensor, Fintype.sum_prod_type]
    simp_rw [← kronecker_sum_right, (hQ _).sum_eq_one]
    rw [← sum_kronecker_left, hP.sum_eq_one, Matrix.one_kronecker_one]

end AdaptiveTensor

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι]

abbrev ReadLabel (F ι : Type*) := (ι → F) × (ι → F)
abbrev HideLabel (F ι : Type*) := (ι → F) × (ι → F) × (ι → F)

/-- Extend an assignment on an active register by zero to the ambient space. -/
def insertRegister (V : Finset ι) (x : V → F) : ι → F :=
  fun i => if h : i ∈ V then x ⟨i, h⟩ else 0

/-- The honest commuting local Z/linear and X/dual-linear measurement. -/
def localRead {S : Finset ι} (L : CL.RegLinear F S)
    (ab : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) :
    Matrix (Fin (Fintype.card S) → F) (Fin (Fintype.card S) → F) ℂ :=
  synOf wZ (coordinateLinear L) ab.1 * synOf wX (CL.lperp (coordinateLinear L)) ab.2

theorem localRead_isPVM {S : Finset ι} (L : CL.RegLinear F S) : IsPVM (localRead L) := by
  apply sampling_hiding_isPVM
  simp only [CL.ker_lperp, CL.perp_perp]
  exact le_rfl

def joinRead (S : Finset ι)
    (a : ((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) × ReadLabel F ι) :
    ReadLabel F ι :=
  (coordinateInsert S a.1.1 + a.2.1, coordinateInsert S a.1.2 + a.2.2)

def joinHide (S : Finset ι)
    (a : ((Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F)) × HideLabel F ι) :
    HideLabel F ι :=
  (coordinateInsert S a.1.1 + a.2.1, coordinateInsert S a.1.2 + a.2.2.1, a.2.2.2)

/-- The register part of the honest Read measurement, including all adaptive stages. -/
def readRegister : {ℓ : ℕ} → (P : CL.CLFun F ι ℓ) → (V : Finset ι) →
    P.SupportedOn V → ReadLabel F ι → Matrix (V → F) (V → F) ℂ
  | _, .zero, _, _, a => if a = (0, 0) then 1 else 0
  | _, .cons S L next, V, h, a =>
      registerOp (coordinateSplit S V h.1)
        (∑ q ∈ Finset.univ.filter (fun q => joinRead S q = a),
          adaptiveTensor (localRead L)
            (fun z => readRegister (next (coordinateInsert S z.1)) (V \ S)
              (h.2 (coordinateInsert S z.1))) q)

/-- Every adaptive Read family is a PVM, even for zero-probability branch labels. -/
theorem readRegister_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) : IsPVM (readRegister P V h) := by
  induction P generalizing V with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro a; simp only [readRegister]; split <;> simp
      · intro a; simp only [readRegister]; split <;> simp
      · simp [readRegister]
  | cons S L next ih =>
      exact registerOp_isPVM (coordinateSplit S V h.1)
        ((adaptiveTensor_isPVM (localRead L) _ (localRead_isPVM L)
          (fun z => ih _ _ (h.2 _))).coarse (joinRead S))

/-- At a stopping node, retain the full X tail and the first dual value, without reading Z. -/
def stopHideAnswer {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι) (x : V → F) :
    HideLabel F ι := firstHideAnswer P (insertRegister V x)

def stopHide {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι) :
    HideLabel F ι → Matrix (V → F) (V → F) ℂ := synOf wX (stopHideAnswer P V)

theorem stopHide_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (V : Finset ι) :
    IsPVM (stopHide P V) := by
  have hX : IsPVM (proj (wX (F := F) (n := V))) :=
    ⟨proj_conjTranspose isWeylFamily_wX,
      fun x => by rw [proj_mul_proj isWeylFamily_wX, if_pos rfl], sum_proj isWeylFamily_wX⟩
  exact hX.coarse (stopHideAnswer P V)

/-- The honest Hide measurement at zero-based stage `k`. Earlier stages read joint
Z/linear and X/dual-linear outcomes; the current stage and remaining tail use X only. -/
def hideRegister : {ℓ : ℕ} → (P : CL.CLFun F ι ℓ) → (k : ℕ) → (V : Finset ι) →
    P.SupportedOn V → HideLabel F ι → Matrix (V → F) (V → F) ℂ
  | _, P, 0, V, _, a => stopHide P V a
  | _, .zero, _ + 1, V, _, a => stopHide .zero V a
  | _, .cons S L next, k + 1, V, h, a =>
      registerOp (coordinateSplit S V h.1)
        (∑ q ∈ Finset.univ.filter (fun q => joinHide S q = a),
          adaptiveTensor (localRead L)
            (fun z => hideRegister (next (coordinateInsert S z.1)) k (V \ S)
              (h.2 (coordinateInsert S z.1))) q)

@[simp] theorem hideRegister_zero {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) (a : HideLabel F ι) :
    hideRegister P 0 V h a = stopHide P V a := by
  cases P <;> rfl

theorem hideRegister_zero_fun {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (V : Finset ι) (h : P.SupportedOn V) : hideRegister P 0 V h = stopHide P V := by
  funext a
  exact hideRegister_zero P V h a

/-- Projectivity of every honest hiding level, including the branch-dependent later levels. -/
theorem hideRegister_isPVM {ℓ : ℕ} (P : CL.CLFun F ι ℓ) (k : ℕ)
    (V : Finset ι) (h : P.SupportedOn V) : IsPVM (hideRegister P k V h) := by
  induction P generalizing V k with
  | zero => cases k <;> exact stopHide_isPVM _ _
  | cons S L next ih =>
      cases k with
      | zero => exact stopHide_isPVM _ _
      | succ k =>
          exact registerOp_isPVM (coordinateSplit S V h.1)
            ((adaptiveTensor_isPVM (localRead L) _ (localRead_isPVM L)
              (fun z => ih _ _ _ (h.2 _))).coarse (joinHide S))

end MIPRE.Introspection.Honest
