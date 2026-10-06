/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Bits
public import MIPRE.Foundations.Introspection.HonestCompleteAux
public import MIPRE.Tailored.Intro.Transport

@[expose] public section

/-!
# The bits of the honest auxiliary measurements

The honest strategy of the introspection verifier answers its auxiliary questions with the
measurements of `MIPRE.Introspection.Honest.auxOp`, on a register of `F₂`-valued coordinates
tensor the input's space: Introspect and Sample read the register in the computational basis and
measure the input's strategy at the question read (`coreOp`); Read measures the adaptive
`Z`-linear and `X`-dual-linear registers (`readOp`) and the input's strategy at the `Z`-outcome
(`fullReadOp`); Hide measures the adaptive hiding registers (`hideOp`). This file computes the
observables of their answer bits:

* `isXBit_readRegister`, `isXBit_hideRegister`: an `F₂`-linear bit of the dual outcome `y'` of
  Read, or of the dual outcome and the `X` tail `(y', x)` of Hide, is a signed permutation. By
  induction along the CL presentation: at each level the measurement is `Z`-syndrome ⊗ `X`-syndrome
  followed by a continuation selected by the `Z`-syndrome, so the bit's observable is a controlled
  sum of the continuation's, times the `X`-syndrome's linear bit, which is a shift `wX c`
  (linear data processing, `exists_encObs_proj_linear`);
* `isZBit_readOp_fst`, `isZBit_hideOp_fst`: any bit of the `Z` outcome `y` is a `±1` diagonal, the
  marginal on `y` being a read-out;
* `auxOp_*`: the bits of the four auxiliary measurements, the input's answer bits entering
  controlled on the register read.
-/

namespace MIPRE.Tailored.Intro

open Finset Matrix MIPRE.Weyl MIPRE.Introspection MIPRE.Introspection.Honest
open scoped Kronecker

set_option linter.unusedSectionVars false

/-! ## Generic shapes -/

section Shapes

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem bitObs_indicator {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (a₀ : Λ) (f : Λ → Bool) :
    bitObs (fun a => if a = a₀ then (1 : Matrix I I ℂ) else 0) f = bitSign (f a₀) • 1 := by
  unfold bitObs pvmObs
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem isXBit_indicator {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (a₀ : Λ) (f : Λ → Bool) :
    IsXBit (fun a => if a = a₀ then (1 : Matrix I I ℂ) else 0) f := by
  unfold IsXBit
  rw [bitObs_indicator]
  exact isSignedPerm_bitSign_smul_one _

/-- **A bit of an adaptive tensor of a joint measurement**: if the outcome `((z, z'), b)` has
measurement `(P z * P' z') ⊗ Q z b`, the bit `g z' ⊕ h z b` has observable
`(∑_z P z ⊗ (bit h z of Q z)) (bit g of P' ⊗ 1)`. -/
theorem bitObs_adaptive_xor {K K' B : Type*} [Fintype K] [Fintype K'] [Fintype B]
    (P : K → Matrix I I ℂ) (P' : K' → Matrix I I ℂ) (Q : K → B → Matrix J J ℂ) (g : K' → Bool)
    (h : K → B → Bool) :
    bitObs (fun zb : (K × K') × B => (P zb.1.1 * P' zb.1.2) ⊗ₖ Q zb.1.1 zb.2)
        (fun zb => xor (g zb.1.2) (h zb.1.1 zb.2)) =
      (∑ z, P z ⊗ₖ bitObs (Q z) (h z)) * (bitObs P' g ⊗ₖ (1 : Matrix J J ℂ)) := by
  rw [Finset.sum_mul]
  unfold bitObs pvmObs
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← mul_kronecker_mul, mul_one, Finset.mul_sum]
  ext ⟨u, u'⟩ ⟨v, v'⟩
  simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.smul_apply, Matrix.mul_apply,
    smul_eq_mul, bitSign_xor, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem sum_filter_fst {A B M : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [AddCommMonoid M] (P : A × B → M) (a : A) :
    ∑ ab ∈ univ.filter (fun ab : A × B => ab.1 = a), P ab = ∑ b, P (a, b) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end Shapes

/-! ## The binary register -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `decide (a + b = 1)` is the exclusive or of the two bits. -/
theorem decide_add_eq_one_xor (a b : ZMod 2) :
    decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  revert a b
  decide

/-- The `X`-syndrome measurement's linear bits are shifts. -/
theorem isXBit_synOf_wX {n : Type*} [Fintype n] [DecidableEq n] {C : Type*} [Fintype C]
    [DecidableEq C] (ψ : (n → ZMod 2) → C) (φ : Module.Dual (ZMod 2) (n → ZMod 2))
    (g : C → Bool) (hg : ∀ e, g (ψ e) = decide (φ e = 1)) :
    IsSignedPerm (bitObs (synOf (wX (F := ZMod 2) (n := n)) ψ) g) := by
  have h1 : bitObs (synOf (wX (F := ZMod 2) (n := n)) ψ) g =
      encObs (proj wX) (fun e (j : Fin 1) => decide ((fun _ => φ) j e = 1)) 0 := by
    rw [encObs_eq_bitObs]
    exact (bitObs_merge (proj wX) ψ g).trans (congrArg _ (funext hg))
  obtain ⟨c, hc⟩ := exists_encObs_proj_linear (wX (F := ZMod 2) (n := n)) (k := 1) (fun _ => φ) 0
  rw [h1, hc]
  exact isSignedPerm_wX c

/-- The inclusion of a register, as a linear map. -/
def insertRegisterL (V : Finset ι) : (V → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun := insertRegister V
  map_add' x y := by
    funext i
    by_cases h : i ∈ V <;> simp [insertRegister, h]
  map_smul' c x := by
    funext i
    by_cases h : i ∈ V <;> simp [insertRegister, h]

@[simp] theorem insertRegisterL_apply (V : Finset ι) (x : V → ZMod 2) :
    insertRegisterL V x = insertRegister V x := rfl

/-! ## Read -/

/-- **A linear bit of the dual outcome of the adaptive Read measurement is a signed
permutation.** -/
theorem isXBit_readRegister {ℓ : ℕ} (P : CL.CLFun (ZMod 2) ι ℓ) (V : Finset ι)
    (h : P.SupportedOn V) (φ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    IsXBit (readRegister P V h) fun a => decide (φ a.2 = 1) := by
  induction P generalizing V with
  | zero =>
    exact isXBit_indicator (0, 0) _
  | cons S L next ih =>
    change IsXBit (fun a => (∑ q ∈ Finset.univ.filter (fun q => joinRead S q = a),
      adaptiveTensor (localRead L) (fun z => readRegister (next (coordinateInsert S z.1)) (V \ S)
        (h.2 (coordinateInsert S z.1))) q).submatrix (coordinateSplit S V h.1)
          (coordinateSplit S V h.1)) _
    refine IsXBit.submatrix_equiv ?_ (coordinateSplit S V h.1)
    rw [isXBit_merge_iff]
    unfold IsXBit
    have e : ((fun a : ReadLabel (ZMod 2) ι => decide (φ a.2 = 1)) ∘ joinRead S) =
        fun zb => xor (decide (φ (coordinateInsert S zb.1.2) = 1)) (decide (φ zb.2.2 = 1)) := by
      funext zb
      simp only [Function.comp_apply, joinRead, map_add, decide_add_eq_one_xor]
    rw [e]
    have e2 := bitObs_adaptive_xor (synOf wZ (coordinateLinear L))
      (synOf wX (CL.lperp (coordinateLinear L)))
      (fun z => readRegister (next (coordinateInsert S z)) (V \ S) (h.2 (coordinateInsert S z)))
      (fun z' => decide (φ (coordinateInsert S z') = 1)) (fun _ q => decide (φ q.2 = 1))
    refine (congrArg IsSignedPerm e2).mpr ?_
    refine IsSignedPerm.mul ?_ (IsSignedPerm.kronecker_one ?_)
    · simp_rw [← readout_eq_synOf]
      exact isSignedPerm_controlled _ _ fun z => ih _ _ _
    · exact isXBit_synOf_wX _ (φ ∘ₗ coordinateInsert S ∘ₗ CL.lperp (coordinateLinear L)) _
        fun e => rfl

/-! ## Hide -/

/-- The dual value and the `X` tail of the stopping Hide answer are linear in the `X`
outcome. -/
theorem exists_dual_stopHideAnswer {ℓ : ℕ} (P : CL.CLFun (ZMod 2) ι ℓ) (V : Finset ι)
    (φ χ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    ∃ ψ : Module.Dual (ZMod 2) (V → ZMod 2), ∀ e,
      φ (stopHideAnswer P V e).2.1 + χ (stopHideAnswer P V e).2.2 = ψ e := by
  cases P with
  | zero =>
    refine ⟨χ ∘ₗ CL.proj ((CL.CLFun.zero : CL.CLFun (ZMod 2) ι 0).factorOfPrefix 0 0)ᶜ ∘ₗ
      insertRegisterL V, fun e => ?_⟩
    simp [stopHideAnswer, firstHideAnswer, CLChecks.dualReadout]
  | cons S L next =>
    refine ⟨φ ∘ₗ coordinateInsert S ∘ₗ CL.lperp (coordinateLinear L) ∘ₗ coordinateRestrict S ∘ₗ
      insertRegisterL V + χ ∘ₗ CL.proj ((CL.CLFun.cons S L next).factorOfPrefix 0 0)ᶜ ∘ₗ
      insertRegisterL V, fun e => ?_⟩
    simp [stopHideAnswer, firstHideAnswer, CLChecks.dualReadout]

theorem isXBit_stopHide {ℓ : ℕ} (P : CL.CLFun (ZMod 2) ι ℓ) (V : Finset ι)
    (φ χ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    IsXBit (stopHide P V) fun a => decide (φ a.2.1 + χ a.2.2 = 1) := by
  obtain ⟨ψ, hψ⟩ := exists_dual_stopHideAnswer P V φ χ
  exact isXBit_synOf_wX _ ψ _ fun e => by rw [hψ]

/-- **A linear bit of the dual outcome and the `X` tail of the adaptive Hide measurement is a
signed permutation.** -/
theorem isXBit_hideRegister (k : ℕ) {ℓ : ℕ} (P : CL.CLFun (ZMod 2) ι ℓ) (V : Finset ι)
    (h : P.SupportedOn V) (φ χ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    IsXBit (hideRegister P k V h) fun a => decide (φ a.2.1 + χ a.2.2 = 1) := by
  induction k generalizing ℓ P V with
  | zero =>
    rw [hideRegister_zero_fun]
    exact isXBit_stopHide P V φ χ
  | succ k ih =>
    cases P with
    | zero => exact isXBit_stopHide _ V φ χ
    | cons S L next =>
      change IsXBit (fun a => (∑ q ∈ Finset.univ.filter (fun q => joinHide S q = a),
        adaptiveTensor (localRead L) (fun z => hideRegister (next (coordinateInsert S z.1)) k
          (V \ S) (h.2 (coordinateInsert S z.1))) q).submatrix (coordinateSplit S V h.1)
            (coordinateSplit S V h.1)) _
      refine IsXBit.submatrix_equiv ?_ (coordinateSplit S V h.1)
      rw [isXBit_merge_iff]
      unfold IsXBit
      have e : ((fun a : HideLabel (ZMod 2) ι => decide (φ a.2.1 + χ a.2.2 = 1)) ∘
          joinHide S) = fun zb => xor (decide (φ (coordinateInsert S zb.1.2) = 1))
            (decide (φ zb.2.2.1 + χ zb.2.2.2 = 1)) := by
        funext zb
        simp only [Function.comp_apply, joinHide, map_add, decide_add_eq_one_xor,
          Bool.xor_assoc]
        all_goals rfl
      rw [e]
      have e2 := bitObs_adaptive_xor (synOf wZ (coordinateLinear L))
        (synOf wX (CL.lperp (coordinateLinear L)))
        (fun z => hideRegister (next (coordinateInsert S z)) k (V \ S)
          (h.2 (coordinateInsert S z)))
        (fun z' => decide (φ (coordinateInsert S z') = 1))
        (fun _ q => decide (φ q.2.1 + χ q.2.2 = 1))
      refine (congrArg IsSignedPerm e2).mpr ?_
      refine IsSignedPerm.mul ?_ (IsSignedPerm.kronecker_one ?_)
      · simp_rw [← readout_eq_synOf]
        exact isSignedPerm_controlled _ _ fun z => ih _ _ _
      · exact isXBit_synOf_wX _ (φ ∘ₗ coordinateInsert S ∘ₗ CL.lperp (coordinateLinear L)) _
          fun e => rfl

/-! ## The ambient registers -/

theorem isXBit_readOp {ℓ : ℕ} (P : CL.CLFun (ZMod 2) ι ℓ) (h : P.SupportedOn Finset.univ)
    (φ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    IsXBit (readOp P h) fun a => decide (φ a.2 = 1) :=
  (isXBit_readRegister P _ h φ).submatrix_equiv univRestriction

theorem isXBit_hideOp {ℓ : ℕ} (P : CL.CLFun (ZMod 2) ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (φ χ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    IsXBit (hideOp P k h) fun a => decide (φ a.2.1 + χ a.2.2 = 1) :=
  (isXBit_hideRegister k P _ h φ χ).submatrix_equiv univRestriction

/-- **Any bit of the `Z` outcome of Hide is a `±1` diagonal**: the marginal is a read-out. -/
theorem isZBit_hideOp_fst {ℓ : ℕ} (P : CL.CLFun (ZMod 2) ι ℓ) (k : ℕ)
    (h : P.SupportedOn Finset.univ) (g : (ι → ZMod 2) → Bool) :
    IsZBit (hideOp P k h) fun a => g a.1 := by
  have e : (fun y => ∑ a ∈ univ.filter (fun a : HideLabel (ZMod 2) ι => a.1 = y),
      hideOp P k h a) = readout (P.truncate k).eval := by
    funext y
    rw [sum_filter_fst (fun a : HideLabel (ZMod 2) ι => hideOp P k h a) y]
    exact hideOp_marginal P k h y
  have := isZBit_readout (P.truncate k).eval g
  rw [← e, isZBit_merge_iff] at this
  exact this

/-! ## The four auxiliary measurements -/

section Aux

variable {A PA : Type*} [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun (ZMod 2) ι ℓ) (D : (ι → ZMod 2) → (ι → ZMod 2) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

theorem parsedCoreOp_eq_extend (t : CoreType) :
    parsedCoreOp (PA := PA) L D R t =
      Function.extend (fun ya : (ι → ZMod 2) × A => ParsedAnswer.pair ya.1 ya.2)
        (coreOp L D R t) 0 := by
  have hinj : Function.Injective (fun ya : (ι → ZMod 2) × A =>
      (ParsedAnswer.pair ya.1 ya.2 : ParsedAnswer (ι → ZMod 2) A PA)) := by
    rintro ⟨y, a⟩ ⟨y', a'⟩ h
    simp only [ParsedAnswer.pair.injEq] at h
    rw [h.1, h.2]
  funext a
  cases a with
  | pair y α => exact (hinj.extend_apply (coreOp L D R t) 0 (y, α)).symm
  | _ =>
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
    rfl

theorem parsedReadOp_eq_extend (w : Bool) (h : (L w).SupportedOn Finset.univ) :
    parsedReadOp (PA := PA) L D R w h =
      Function.extend (fun a : ReadLabel (ZMod 2) ι × A => ParsedAnswer.read a.1.1 a.1.2 a.2)
        (fullReadOp L D R w h) 0 := by
  have hinj : Function.Injective (fun a : ReadLabel (ZMod 2) ι × A =>
      (ParsedAnswer.read a.1.1 a.1.2 a.2 : ParsedAnswer (ι → ZMod 2) A PA)) := by
    rintro ⟨⟨y, yp⟩, a⟩ ⟨⟨y', yp'⟩, a'⟩ h
    simp only [ParsedAnswer.read.injEq] at h
    rw [h.1, h.2.1, h.2.2]
  funext a
  cases a with
  | read y yp α => exact (hinj.extend_apply (fullReadOp L D R w h) 0 ((y, yp), α)).symm
  | _ =>
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
    rfl

theorem parsedHideOp_eq_extend (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ) :
    parsedHideOp (PA := PA) L D R w k h =
      Function.extend (fun a : HideLabel (ZMod 2) ι => ParsedAnswer.hide a.1 a.2.1 a.2.2)
        (fun a => hideOp (L w) k h a ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ)) 0 := by
  have hinj : Function.Injective (fun a : HideLabel (ZMod 2) ι =>
      (ParsedAnswer.hide a.1 a.2.1 a.2.2 : ParsedAnswer (ι → ZMod 2) A PA)) := by
    rintro ⟨y, yp, x⟩ ⟨y', yp', x'⟩ h
    simp only [ParsedAnswer.hide.injEq] at h
    rw [h.1, h.2.1, h.2.2]
  funext a
  cases a with
  | hide y yp x =>
    exact (hinj.extend_apply (fun a => hideOp (L w) k h a ⊗ₖ
      (1 : Matrix (Fin R.d) (Fin R.d) ℂ)) 0 (y, yp, x)).symm
  | _ =>
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
    rfl

/-- **The bits of Introspect and Sample**: controlled by the register read, the input's bits at
the question read. -/
theorem isXBit_parsedCoreOp (t : CoreType) (f : ParsedAnswer (ι → ZMod 2) A PA → Bool)
    (hf : ∀ y, IsXBit (R.P.M (t.2, originalQuestion L t y)) fun α => f (.pair y α)) :
    IsXBit (parsedCoreOp L D R t) f := by
  unfold IsXBit
  rw [parsedCoreOp_eq_extend, bitObs_extend _ (by
    rintro ⟨y, a⟩ ⟨y', a'⟩ h
    simp only [ParsedAnswer.pair.injEq] at h
    rw [h.1, h.2])]
  exact isXBit_controlled (displayed L t) (fun y => R.P.M (t.2, originalQuestion L t y)) _ hf

theorem isZBit_parsedCoreOp (t : CoreType) (f : ParsedAnswer (ι → ZMod 2) A PA → Bool)
    (hf : ∀ y, IsZBit (R.P.M (t.2, originalQuestion L t y)) fun α => f (.pair y α)) :
    IsZBit (parsedCoreOp L D R t) f := by
  unfold IsZBit
  rw [parsedCoreOp_eq_extend, bitObs_extend _ (by
    rintro ⟨y, a⟩ ⟨y', a'⟩ h
    simp only [ParsedAnswer.pair.injEq] at h
    rw [h.1, h.2])]
  exact isZBit_controlled (displayed L t) (fun y => R.P.M (t.2, originalQuestion L t y)) _ hf

theorem readOp_merge (w : Bool) (h : (L w).SupportedOn Finset.univ) :
    (fun ya : (ι → ZMod 2) × A => ∑ a ∈ univ.filter
      (fun a : ReadLabel (ZMod 2) ι × A => (a.1.1, a.2) = ya), fullReadOp L D R w h a) =
      fun ya => readout (L w).eval ya.1 ⊗ₖ R.P.M (w, ya.1) ya.2 := by
  funext ⟨y, α⟩
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single y (fun y' _ hy' => by simp [hy']) (by simp)]
  simp only [true_and]
  rw [Finset.sum_comm, Finset.sum_eq_single α (fun α' _ hα' => by simp [hα']) (by simp)]
  simp only [↓reduceIte]
  rw [← readOp_marginal (L w) h y]
  simp only [fullReadOp]
  rw [MIPRE.sum_kronecker_left]

/-- **The bits of Read that depend on the register and the input's answer**: controlled by the
register. -/
theorem isXBit_parsedReadOp_fst (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (f : ParsedAnswer (ι → ZMod 2) A PA → Bool) (F' : (ι → ZMod 2) × A → Bool)
    (hF : ∀ y yp α, f (.read y yp α) = F' (y, α))
    (hf : ∀ y, IsXBit (R.P.M (w, y)) fun α => F' (y, α)) :
    IsXBit (parsedReadOp L D R w h) f := by
  unfold IsXBit
  rw [parsedReadOp_eq_extend, bitObs_extend _ (by
    rintro ⟨⟨y, yp⟩, a⟩ ⟨⟨y', yp'⟩, a'⟩ h
    simp only [ParsedAnswer.read.injEq] at h
    rw [h.1, h.2.1, h.2.2])]
  have e : (f ∘ fun a : ReadLabel (ZMod 2) ι × A => ParsedAnswer.read a.1.1 a.1.2 a.2) =
      F' ∘ fun a => (a.1.1, a.2) := by
    funext a
    exact hF _ _ _
  rw [e, ← bitObs_merge, readOp_merge]
  exact isXBit_controlled (L w).eval (fun y => R.P.M (w, y)) F' hf

theorem isZBit_parsedReadOp_fst (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (f : ParsedAnswer (ι → ZMod 2) A PA → Bool) (F' : (ι → ZMod 2) × A → Bool)
    (hF : ∀ y yp α, f (.read y yp α) = F' (y, α))
    (hf : ∀ y, IsZBit (R.P.M (w, y)) fun α => F' (y, α)) :
    IsZBit (parsedReadOp L D R w h) f := by
  unfold IsZBit
  rw [parsedReadOp_eq_extend, bitObs_extend _ (by
    rintro ⟨⟨y, yp⟩, a⟩ ⟨⟨y', yp'⟩, a'⟩ h
    simp only [ParsedAnswer.read.injEq] at h
    rw [h.1, h.2.1, h.2.2])]
  have e : (f ∘ fun a : ReadLabel (ZMod 2) ι × A => ParsedAnswer.read a.1.1 a.1.2 a.2) =
      F' ∘ fun a => (a.1.1, a.2) := by
    funext a
    exact hF _ _ _
  rw [e, ← bitObs_merge, readOp_merge]
  exact isZBit_controlled (L w).eval (fun y => R.P.M (w, y)) F' hf

/-- **A linear bit of the dual outcome of Read is a signed permutation.** -/
theorem isXBit_parsedReadOp_dual (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (f : ParsedAnswer (ι → ZMod 2) A PA → Bool) (φ : Module.Dual (ZMod 2) (ι → ZMod 2))
    (hF : ∀ y yp α, f (.read y yp α) = decide (φ yp = 1)) :
    IsXBit (parsedReadOp L D R w h) f := by
  unfold IsXBit
  rw [parsedReadOp_eq_extend, bitObs_extend _ (by
    rintro ⟨⟨y, yp⟩, a⟩ ⟨⟨y', yp'⟩, a'⟩ h
    simp only [ParsedAnswer.read.injEq] at h
    rw [h.1, h.2.1, h.2.2])]
  have e : bitObs (fullReadOp L D R w h)
      (f ∘ fun a : ReadLabel (ZMod 2) ι × A => ParsedAnswer.read a.1.1 a.1.2 a.2) =
      bitObs (readOp (L w) h) (fun a => decide (φ a.2 = 1)) ⊗ₖ 1 := by
    have h1 := bitObs_add_kronecker (readOp (L w) h) (fun a => R.P.M (w, a.1))
      (f ∘ fun a : ReadLabel (ZMod 2) ι × A => ParsedAnswer.read a.1.1 a.1.2 a.2)
    refine h1.trans ?_
    simp only [Function.comp_apply, hF]
    rw [bitObs, pvmObs, MIPRE.sum_kronecker_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [bitObs_const (R.isPVMIn _), Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [e]
  exact IsSignedPerm.kronecker_one (isXBit_readOp (L w) h φ)

theorem hide_injective :
    Function.Injective (fun a : HideLabel (ZMod 2) ι =>
      (ParsedAnswer.hide a.1 a.2.1 a.2.2 : ParsedAnswer (ι → ZMod 2) A PA)) := by
  rintro ⟨y, yp, x⟩ ⟨y', yp', x'⟩ h
  simp only [ParsedAnswer.hide.injEq] at h
  rw [h.1, h.2.1, h.2.2]

/-- **Any bit of the `Z` outcome of Hide is a `±1` diagonal.** -/
theorem isZBit_parsedHideOp_fst (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ)
    (f : ParsedAnswer (ι → ZMod 2) A PA → Bool) (g : (ι → ZMod 2) → Bool)
    (hF : ∀ y yp x, f (.hide y yp x) = g y) :
    IsZBit (parsedHideOp L D R w k h) f := by
  unfold IsZBit
  rw [parsedHideOp_eq_extend, bitObs_extend _ hide_injective]
  have e : (f ∘ fun a : HideLabel (ZMod 2) ι => ParsedAnswer.hide a.1 a.2.1 a.2.2) =
      fun a => g a.1 := by
    funext a
    exact hF _ _ _
  rw [e]
  exact (isZBit_hideOp_fst (L w) k h g).kronecker_one

/-- **A linear bit of the dual outcome and the `X` tail of Hide is a signed permutation.** -/
theorem isXBit_parsedHideOp_lin (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ)
    (f : ParsedAnswer (ι → ZMod 2) A PA → Bool) (φ χ : Module.Dual (ZMod 2) (ι → ZMod 2))
    (hF : ∀ y yp x, f (.hide y yp x) = decide (φ yp + χ x = 1)) :
    IsXBit (parsedHideOp L D R w k h) f := by
  unfold IsXBit
  rw [parsedHideOp_eq_extend, bitObs_extend _ hide_injective]
  have e : (f ∘ fun a : HideLabel (ZMod 2) ι => ParsedAnswer.hide a.1 a.2.1 a.2.2) =
      fun a => decide (φ a.2.1 + χ a.2.2 = 1) := by
    funext a
    exact hF _ _ _
  rw [e]
  exact (isXBit_hideOp (L w) k h φ χ).kronecker_one

end Aux

end MIPRE.Tailored.Intro

end
