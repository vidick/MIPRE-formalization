/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestXCoordinates
import MIPRE.Foundations.Introspection.HidingPrefix

/-! # Exact Pauli-X readouts under adaptive coordinate splits -/

noncomputable section
namespace MIPRE.Introspection.Honest
open Finset Matrix Classical Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F I J K Y : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype Y] [DecidableEq Y]

private theorem matrix_ite_entry {I J : Type*} (p : Prop) [Decidable p]
    (M N : Matrix I J ℂ) (i : I) (j : J) :
    (if p then M else N) i j = if p then M i j else N i j := by
  by_cases h : p <;> simp [h]

/-- A spectral readout depending only on the second coordinate factor acts
as identity on the first one. The split of each X projector is explicit. -/
theorem synX_split_second
    (e : (I → F) ≃ (J → F) × (K → F))
    (he : ∀ z, proj wX z = registerOp e (proj wX (e z).1 ⊗ₖ proj wX (e z).2))
    (f : (K → F) → Y) (y : Y) :
    synOf wX (fun z => f (e z).2) y = registerOp e
      ((1 : Matrix (J → F) (J → F) ℂ) ⊗ₖ synOf wX f y) := by
  ext x x'
  simp only [synOf, Matrix.sum_apply, Finset.sum_filter, registerOp_apply,
    Matrix.kroneckerMap_apply, matrix_ite_entry, Matrix.zero_apply]
  calc
    _ = ∑ p : (J → F) × (K → F),
        if f p.2 = y then proj wX p.1 (e x).1 (e x').1 * proj wX p.2 (e x).2 (e x').2 else 0 := by
      apply Fintype.sum_equiv e
      intro z
      rw [he z]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      have ht (a : J → F) (b : K → F) :
          (if f b = y then proj wX a (e x).1 (e x').1 * proj wX b (e x).2 (e x').2 else 0) =
          proj wX a (e x).1 (e x').1 * (if f b = y then proj wX b (e x).2 (e x').2 else 0) := by
        by_cases h : f b = y <;> simp [h]
      simp_rw [ht, ← Finset.mul_sum, ← Finset.sum_mul]
      have hs := congrArg (fun M : Matrix (J → F) (J → F) ℂ => M (e x).1 (e x').1)
        (sum_proj (w := wX) isWeylFamily_wX)
      simp only [Matrix.sum_apply] at hs
      rw [hs]

theorem synX_split_first
    (e : (I → F) ≃ (J → F) × (K → F))
    (he : ∀ z, proj wX z = registerOp e (proj wX (e z).1 ⊗ₖ proj wX (e z).2))
    (f : (J → F) → Y) (y : Y) :
    synOf wX (fun z => f (e z).1) y = registerOp e
      (synOf wX f y ⊗ₖ (1 : Matrix (K → F) (K → F) ℂ)) := by
  let e' := e.trans (Equiv.prodComm (J → F) (K → F))
  have he' (z : I → F) : proj wX z =
      registerOp e' (proj wX (e' z).1 ⊗ₖ proj wX (e' z).2) := by
    rw [he z]
    ext x x'
    simp only [registerOp_apply, Matrix.kroneckerMap_apply, e', Equiv.trans_apply,
      Equiv.prodComm_apply]
    exact mul_comm _ _
  have hh : synOf wX (fun z => f (e z).1) y = registerOp e'
      ((1 : Matrix (K → F) (K → F) ℂ) ⊗ₖ synOf wX f y) :=
    synX_split_second e' he' f y
  rw [hh]
  ext x x'
  simp only [registerOp_apply, Matrix.kroneckerMap_apply, e', Equiv.trans_apply,
    Equiv.prodComm_apply]
  exact mul_comm _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ambientIndexSplit (V : Finset ι) : ι ≃ V ⊕ ↥(Vᶜ) where
  toFun i := if hi : i ∈ V then .inl ⟨i,hi⟩ else .inr ⟨i,mem_compl.mpr hi⟩
  invFun z := match z with | .inl i => i | .inr i => i
  left_inv i := by by_cases hi : i ∈ V <;> simp [hi]
  right_inv z := by
    cases z with
    | inl i => simp only [dif_pos i.property]
    | inr i => simp only [dif_neg (mem_compl.mp i.property)]

theorem trDot_ambientSplit (V : Finset ι) (x y : ι → F) :
    trDot x y = trDot (ambientSplit V x).1 (ambientSplit V y).1 +
      trDot (ambientSplit V x).2 (ambientSplit V y).2 := by
  unfold trDot
  rw [← map_add]
  congr 1
  have he := Equiv.sum_comp (ambientIndexSplit V).symm (fun i : ι => x i * y i)
  rw [Fintype.sum_sum_type] at he
  exact he.symm

theorem pauliX_ambientSplit (V : Finset ι) (x : ι → F) :
    proj wX x = registerOp (ambientSplit V)
      (proj wX (ambientSplit V x).1 ⊗ₖ proj wX (ambientSplit V x).2) :=
  pauliX_split (ambientSplit V) (fun _ _ => rfl) (trDot_ambientSplit V) x

theorem insertRegister_ambientSplit_snd (V : Finset ι) (x : ι → F) :
    insertRegister Vᶜ (ambientSplit V x).2 = CL.proj Vᶜ x := by
  ext i
  simp [insertRegister, ambientSplit, CL.proj_apply]

/-- The selected dual readout has no action on preceding prefix registers. -/
theorem dualReadout_prefix_split {ℓ : ℕ} (P : CL.CLFun F ι ℓ)
    (h : P.SupportedOn univ) (k : ℕ) (y yp : ι → F) :
    synOf wX (CLChecks.dualReadout P k y) yp =
      registerOp (ambientSplit (CLChecks.prefixRegister P k y))
        ((1 : Matrix (CLChecks.prefixRegister P k y → F) _ ℂ) ⊗ₖ
          synOf wX (fun x : ↥((CLChecks.prefixRegister P k y)ᶜ) → F =>
            CLChecks.dualReadout P k y (insertRegister (CLChecks.prefixRegister P k y)ᶜ x)) yp) := by
  have hf (x : ι → F) : CLChecks.dualReadout P k y x =
      CLChecks.dualReadout P k y (insertRegister (CLChecks.prefixRegister P k y)ᶜ
        (ambientSplit (CLChecks.prefixRegister P k y) x).2) := by
    rw [insertRegister_ambientSplit_snd, CLChecks.dualReadout_proj_compl_prefix h]
  conv_lhs => arg 2; ext x; rw [hf x]
  exact synX_split_second (ambientSplit (CLChecks.prefixRegister P k y))
    (pauliX_ambientSplit (F := F) (CLChecks.prefixRegister P k y))
    (fun x => CLChecks.dualReadout P k y (insertRegister (CLChecks.prefixRegister P k y)ᶜ x)) yp

/-- The dual readout at any later stage ignores the first register. -/
theorem dualReadout_tail_split {ℓ : ℕ} {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ) (y yp : ι → F) :
    synOf wX (fun x : V → F => CLChecks.dualReadout (.cons S L next) (k+1) y
      (insertRegister V x)) yp =
      registerOp (coordinateSplit S V h.1)
        ((1 : Matrix (Fin (Fintype.card S) → F) _ ℂ) ⊗ₖ
          synOf wX (fun x : ↥(V \ S) → F =>
            CLChecks.dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y)
              (insertRegister (V \ S) x)) yp) := by
  have hf (x : V → F) : CLChecks.dualReadout (.cons S L next) (k+1) y
      (insertRegister V x) =
      CLChecks.dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y)
        (insertRegister (V \ S) (coordinateSplit S V h.1 x).2) := by
    simp only [CLChecks.dualReadout, ← tail_insertRegister S V h.1]
    apply CLChecks.dualReadout_congr (h.2 _)
    intro i hi
    have hiS := (mem_sdiff.mp hi).2
    simp [CL.proj_apply, hiS]
  simp_rw [hf]
  exact synX_split_second (coordinateSplit S V h.1) (pauliX_coordinateSplit (F := F) S V h.1)
    (fun x => CLChecks.dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y)
      (insertRegister (V \ S) x)) yp

end MIPRE.Introspection.Honest
