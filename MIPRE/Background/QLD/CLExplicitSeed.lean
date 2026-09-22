/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.CLBinary
import MIPRE.Foundations.Introspection.SeedSelectorProg

/-! # Pauli sampling with the explicit binary seed enumeration

The sampler retains its canonical binary seed and uses the efficient high-bit
selector. Only the mathematical decoder permutes that seed to the enumeration
used in `qldGame`. A permutation of the common random content proves equality
with the existing QLD question law, including the line seeds in the questions.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL.ExplicitSeed
open Finset Classical
open MIPRE.Introspection.SeedProgram
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

def secondMap (χ : F → Fin m) (t : Ty) (s : F) :
    CL.RegLinear F (directionSet m) :=
  match t with
  | .dline _ => directionMap (χ s)
  | _ => 0

def finalMap (χ : F → Fin m) (t : Ty) (s : F) (v : Fin m → F) :
    CL.RegLinear F (finalSet m) :=
  match t with
  | .point W => pointMap W LinearMap.id
  | .aline W => pointMap W (CL.canonLin (Submodule.span F {Pi.single (χ s) 1}))
  | .dline W => pointMap W (CL.canonLin (Submodule.span F {v}))
  | .pauli _ => 0
  | _ => CL.RegLinear.id _

/-- The concrete three-stage presentation with a specified seed selector. -/
def presentation (χ : F → Fin m) (t : Ty) : CL.CLFun F (Coord m) 3 :=
  .cons (seedSet m) (seedMap t) fun y =>
    .cons (directionSet m) (secondMap χ t (y .seed)) fun z =>
      .cons (finalSet m) (finalMap χ t (y .seed) (fun i => z (.direction i)))
        fun _ => .zero

theorem presentation_exactlyOn (χ : F → Fin m) (t : Ty) :
    (presentation χ t).ExactlyOn univ := by
  refine ⟨subset_univ _, fun _ => ⟨?_, fun _ => ?_⟩⟩
  · intro c hc
    cases c <;> simp_all [seedSet, directionSet]
  · have he : (univ \ seedSet m) \ directionSet m = finalSet m := by
      ext c
      simp [finalSet]
    rw [he]
    exact ⟨Subset.rfl, fun _ => by simp⟩

theorem presentation_pauli_eval (χ : F → Fin m) (W : Bas) (x : Coord m → F) :
    (presentation χ (.pauli W)).eval x = 0 := by
  simp [presentation, seedMap, secondMap, finalMap]

/-- Permute just the shared seed; all other random content stays fixed. -/
def contentPermutation (π : F ≃ F) : Content F m ≃ Content F m where
  toFun c := ⟨c.uX, c.uZ, π c.s, c.v, c.rX, c.rZ⟩
  invFun c := ⟨c.uX, c.uZ, π.symm c.s, c.v, c.rX, c.rZ⟩
  left_inv c := by cases c; simp
  right_inv c := by cases c; simp

/-- Decode the explicit seed into the fixed enumeration used by the legacy
QLD question type. No program needs to evaluate this mathematical relabelling. -/
def decode (π : F ≃ F) (t : Ty) (x : Coord m → F) : Question F m :=
  let c := contentPermutation π (vectorContent x)
  match t with
  | .point W => .point W (c.pt W)
  | .aline W => .aline W (c.pt W) c.s
  | .dline W => .dline W (c.pt W) c.s c.v
  | .pauli W => .pauli W
  | .pairB W => .pairB W c.omega
  | .pair => .pair c.omega
  | .con i => .con i c.omega
  | .var j => .var j c.omega

variable [NeZero m]

/-- Literal equality of the full decoded questions, not merely equality of
the chosen direction index. -/
theorem decode_presentation (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) (t : Ty) (c : Content F m) :
    decode π t ((presentation χ t).eval (contentVector c)) =
      (contentPermutation π c).question hm t := by
  cases t <;> (try cases ‹Bas›) <;>
    simp only [decode, presentation, seedMap, secondMap, finalMap,
      CL.CLFun.eval, CL.RegLinear.zero_apply, CL.RegLinear.id_apply,
      pointMap_apply, directionMap_apply, Pi.add_apply, Pi.zero_apply,
      vectorContent, contentPermutation, Equiv.coe_fn_mk,
      Content.question, Content.pt, Content.omega, LIDT.CL.rep, hχ]
  all_goals
    simp [CL.proj_apply, seedSet, directionSet, finalSet, contentVector]
  all_goals constructor <;> rfl

def samplePermutation (π : F ≃ F) : Sample F m ≃ (TyEdge × (Coord m → F)) :=
  Equiv.prodCongr (Equiv.refl _) ((contentPermutation π).symm.trans contentEquiv)

/-- Exact legacy QLD question law under the content permutation. -/
theorem qldGame_mu_presentation [Algebra (ZMod 2) F] {d : ℕ}
    (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y =
      SampledGame.dist
        (fun p : TyEdge × (Coord m → F) =>
          decode π p.1.val.1 ((presentation χ p.1.val.1).eval p.2))
        (fun p : TyEdge × (Coord m → F) =>
          decode π p.1.val.2 ((presentation χ p.1.val.2).eval p.2)) x y := by
  change (∑ p : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
    if (p.2.question hm p.1.val.1, p.2.question hm p.1.val.2) = (x, y)
      then 1 else 0) = _
  unfold SampledGame.dist
  rw [← Finset.mul_sum, Fintype.card_congr (samplePermutation (m := m) π)]
  congr 1
  refine Fintype.sum_equiv (samplePermutation π) _ _ fun p => ?_
  simp only [samplePermutation, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    Equiv.trans_apply, contentEquiv, Equiv.coe_fn_mk, decode_presentation hm χ π hχ,
    Equiv.apply_symm_apply]

section Binary
variable [Algebra (ZMod 2) F] {t : ℕ}

def binaryPresentation (χ : F → Fin m) (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) :
    CL.CLFun (ZMod 2) (Fin ((3 * m + 3) * t)) 3 :=
  ((presentation χ T).downsize b).reindex (binaryCoordEquiv m t)

theorem binaryPresentation_exactlyOn (χ : F → Fin m)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) :
    (binaryPresentation χ b T).ExactlyOn univ := by
  have h := ((presentation_exactlyOn χ T).downsize b).reindex (binaryCoordEquiv m t)
  simpa only [binaryPresentation, Finset.univ_product_univ, Finset.map_univ_equiv] using h

theorem binaryPresentation_eval (χ : F → Fin m)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Coord m → F) :
    (binaryPresentation χ b T).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((presentation χ T).eval x) := by
  change (((presentation χ T).downsize b).reindex (binaryCoordEquiv m t)).eval
    (CL.reindexEquiv (binaryCoordEquiv m t) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.eval_reindex, CL.CLFun.eval_downsize]
  rfl

theorem binaryPresentation_pauli_eval (χ : F → Fin m)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : Bas)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) :
    (binaryPresentation χ b (.pauli W)).eval x = 0 := by
  obtain ⟨z, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective x
  rw [binaryPresentation_eval, presentation_pauli_eval, map_zero]

def binaryDecode (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (T : Ty) (x : Fin ((3 * m + 3) * t) → ZMod 2) : Question F m :=
  decode π T ((binaryVectorEquiv b).symm x)

theorem binaryDecode_presentation (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (c : Content F m) :
    binaryDecode π b T ((binaryPresentation χ b T).eval
      (binaryVectorEquiv b (contentVector c))) = (contentPermutation π c).question hm T := by
  rw [binaryPresentation_eval]
  unfold binaryDecode
  rw [LinearEquiv.symm_apply_apply, decode_presentation hm χ π hχ]

def binarySamplePermutation (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    Sample F m ≃ (TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2)) :=
  (samplePermutation π).trans (Equiv.prodCongr (Equiv.refl _) (binaryVectorEquiv b).toEquiv)

theorem qldGame_mu_binaryPresentation {d : ℕ}
    (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (b : Module.Basis (Fin t) (ZMod 2) F) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y =
      SampledGame.dist
        (fun p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2) =>
          binaryDecode π b p.1.val.1 ((binaryPresentation χ b p.1.val.1).eval p.2))
        (fun p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2) =>
          binaryDecode π b p.1.val.2 ((binaryPresentation χ b p.1.val.2).eval p.2)) x y := by
  change (∑ p : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
    if (p.2.question hm p.1.val.1, p.2.question hm p.1.val.2) = (x, y)
      then 1 else 0) = _
  unfold SampledGame.dist
  rw [← Finset.mul_sum, Fintype.card_congr (binarySamplePermutation (m := m) π b)]
  congr 1
  refine Fintype.sum_equiv (binarySamplePermutation π b) _ _ fun p => ?_
  simp only [binarySamplePermutation, samplePermutation, Equiv.prodCongr_apply,
    Prod.map, Equiv.refl_apply, Equiv.trans_apply, contentEquiv, Equiv.coe_fn_mk,
    LinearEquiv.coe_toEquiv, binaryDecode_presentation hm χ π hχ,
    Equiv.apply_symm_apply]
end Binary

/-- The concrete permutation from canonical bit rank to the legacy numbering. -/
def seedPermutation {k : ℕ} (E : SAT.BinField k) : E.carrier ≃ E.carrier :=
  ((fieldEnumeration E).trans (finCongr E.card_carrier.symm)).trans
    (Fintype.equivFin E.carrier).symm

theorem seedPermutation_rank {k : ℕ} (E : SAT.BinField k) (s : E.carrier) :
    (Fintype.equivFin E.carrier (seedPermutation E s)).val = (fieldIndex E s).val := by
  simp [seedPermutation, fieldEnumeration]

/-- The arbitrary legacy enumeration appears only in the seed relabelling.
The branch chosen by the actual presentation is computed by `selectorProg`. -/
theorem chi_seedPermutation {k : ℕ} (E : SAT.BinField k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card E.carrier) (s : E.carrier) :
    LIDT.CL.chi hm (seedPermutation E s) = selector E j hj s := by
  apply Fin.ext
  change (Fintype.equivFin E.carrier (seedPermutation E s)).val /
    (Fintype.card E.carrier / 2 ^ j) = (fieldIndex E s).val / 2 ^ (k - j)
  rw [seedPermutation_rank, E.card_carrier]
  have he : 2 ^ k / 2 ^ j = 2 ^ (k - j) := by
    conv_lhs => rw [show k = j + (k - j) by omega, pow_add]
    simp
  rw [he]

theorem dyadic_divides {k : ℕ} (E : SAT.BinField k) (j : ℕ) (hj : j ≤ k) :
    2 ^ j ∣ Fintype.card E.carrier := by
  rw [E.card_carrier]
  refine ⟨2 ^ (k - j), ?_⟩
  rw [← pow_add, Nat.add_sub_of_le hj]

/-- The instantiated explicit sampler has the actual legacy QLD law. The
selector correspondence has been proved, rather than supplied as a premise. -/
theorem qldGame_mu_selector_binary {k j : ℕ} (E : SAT.BinField k) (hj : j ≤ k)
    [Algebra (ZMod 2) E.carrier] {t d : ℕ}
    (b : Module.Basis (Fin t) (ZMod 2) E.carrier)
    (x y : Question E.carrier (2 ^ j)) :
    (qldGame (d := d) (dyadic_divides E j hj)).μ x y =
      SampledGame.dist
        (fun p : TyEdge × (Fin ((3 * 2 ^ j + 3) * t) → ZMod 2) =>
          binaryDecode (seedPermutation E) b p.1.val.1
            ((binaryPresentation (selector E j hj) b p.1.val.1).eval p.2))
        (fun p : TyEdge × (Fin ((3 * 2 ^ j + 3) * t) → ZMod 2) =>
          binaryDecode (seedPermutation E) b p.1.val.2
            ((binaryPresentation (selector E j hj) b p.1.val.2).eval p.2)) x y :=
  qldGame_mu_binaryPresentation (dyadic_divides E j hj) (selector E j hj)
    (seedPermutation E) (chi_seedPermutation E j hj _) b x y

end MIPRE.QLD.PauliCL.ExplicitSeed
end
