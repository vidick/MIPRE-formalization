/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.Game
import MIPRE.Foundations.CL.Basic
import MIPRE.Foundations.SampledGame

/-! # The actual three-level Pauli question presentations

The ambient coordinates are precisely the two points, the seed, the raw
direction, and the two scalars in `Content`. The presentation reads the seed,
then the selected direction, then the point and scalar registers. Its full
evaluation is the question map of the existing twenty-six-type Pauli game.
These are concrete field-valued presentations; uniform binary execution is
a separate layer.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false

/-- The `3m+3` field coordinates in the actual Pauli sample. -/
inductive Coord (m : ℕ)
  | point (W : Bas) (i : Fin m)
  | seed
  | direction (i : Fin m)
  | scalar (W : Bas)
  deriving DecidableEq, Fintype

def coordEquiv (m : ℕ) : Coord m ≃ ((Bas × Fin m) ⊕ (Unit ⊕ (Fin m ⊕ Bas))) where
  toFun
    | .point W i => .inl (W, i)
    | .seed => .inr (.inl ())
    | .direction i => .inr (.inr (.inl i))
    | .scalar W => .inr (.inr (.inr W))
  invFun
    | .inl (W, i) => .point W i
    | .inr (.inl _) => .seed
    | .inr (.inr (.inl i)) => .direction i
    | .inr (.inr (.inr W)) => .scalar W
  left_inv c := by cases c <;> rfl
  right_inv c := by rcases c with ⟨W, i⟩ | (u | (i | W)) <;> rfl

theorem card_coord (m : ℕ) : Fintype.card (Coord m) = 3 * m + 3 := by
  rw [Fintype.card_congr (coordEquiv m)]
  have hB : Fintype.card Bas = 2 := by decide
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit, hB]
  omega

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

def contentVector (c : Content F m) : Coord m → F
  | .point .X i => c.uX i
  | .point .Z i => c.uZ i
  | .seed => c.s
  | .direction i => c.v i
  | .scalar .X => c.rX
  | .scalar .Z => c.rZ

def vectorContent (x : Coord m → F) : Content F m :=
  ⟨fun i => x (.point .X i), fun i => x (.point .Z i), x .seed,
    fun i => x (.direction i), x (.scalar .X), x (.scalar .Z)⟩

def contentEquiv : Content F m ≃ (Coord m → F) where
  toFun := contentVector
  invFun := vectorContent
  left_inv c := by cases c; rfl
  right_inv x := by
    funext i
    cases i with
    | point W i => cases W <;> rfl
    | scalar W => cases W <;> rfl
    | seed => rfl
    | direction i => rfl

def seedSet (m : ℕ) : Finset (Coord m) := {.seed}

def directionSet (m : ℕ) : Finset (Coord m) :=
  univ.filter fun c => match c with | .direction _ => True | _ => False

def finalSet (m : ℕ) : Finset (Coord m) := (seedSet m ∪ directionSet m)ᶜ

private theorem direction_subset (m : ℕ) : directionSet m ⊆ univ \ seedSet m := by
  intro c hc
  cases c <;> simp_all [seedSet, directionSet]

private theorem remainder_eq (m : ℕ) :
    (univ \ seedSet m) \ directionSet m = finalSet m := by
  ext c
  simp [finalSet]

/-- A point-register linear map, zero on all other content coordinates. -/
def pointMap (W : Bas) (L : (Fin m → F) →ₗ[F] (Fin m → F)) :
    CL.RegLinear F (finalSet m) where
  toLinearMap :=
    { toFun := fun x c => match c with
        | .point W' i => if W' = W then L (fun j => x (.point W j)) i else 0
        | _ => 0
      map_add' x y := by
        funext c
        cases c with
        | point W' i =>
          by_cases h : W' = W
          · simp only [if_pos h, Pi.add_apply]
            exact congrFun (L.map_add (fun j => x (.point W j))
              (fun j => y (.point W j))) i
          · simp only [if_neg h, Pi.add_apply, add_zero]
        | seed => simp
        | direction i => simp
        | scalar W => simp
      map_smul' a x := by
        funext c
        cases c with
        | point W' i =>
          by_cases h : W' = W
          · simp only [if_pos h, Pi.smul_apply]
            exact congrFun (L.map_smul a (fun j => x (.point W j))) i
          · simp only [if_neg h, Pi.smul_apply, smul_zero]
        | seed => simp
        | direction i => simp
        | scalar W => simp }
  proj_comp_proj' x := by
    funext c
    cases c with
    | point W' i =>
      simp [CL.proj_apply, finalSet, seedSet, directionSet]
    | seed => simp [CL.proj_apply, finalSet, seedSet, directionSet]
    | direction i => simp [CL.proj_apply, finalSet, seedSet, directionSet]
    | scalar W => simp [CL.proj_apply, finalSet, seedSet, directionSet]

def directionMap (i : Fin m) : CL.RegLinear F (directionSet m) where
  toLinearMap :=
    { toFun := fun x c => match c with
        | .direction j => if j < i then 0 else x (.direction j)
        | _ => 0
      map_add' x y := by
        funext c
        cases c with
        | direction j => by_cases h : j < i <;> simp [h]
        | point W j => simp
        | seed => simp
        | scalar W => simp
      map_smul' a x := by
        funext c
        cases c with
        | direction j => by_cases h : j < i <;> simp [h]
        | point W j => simp
        | seed => simp
        | scalar W => simp }
  proj_comp_proj' x := by
    funext c
    cases c <;> simp [CL.proj_apply, directionSet]

def seedMap : Ty → CL.RegLinear F (seedSet m)
  | .aline _ | .dline _ => CL.RegLinear.id _
  | _ => 0

@[simp] theorem pointMap_apply (W : Bas)
    (L : (Fin m → F) →ₗ[F] (Fin m → F)) (x : Coord m → F) (c : Coord m) :
    pointMap W L x c = (match c with
      | .point W' i => if W' = W then L (fun j => x (.point W j)) i else 0
      | _ => 0) := rfl

@[simp] theorem directionMap_apply (i : Fin m) (x : Coord m → F) (c : Coord m) :
    directionMap i x c = (match c with
      | .direction j => if j < i then 0 else x (.direction j)
      | _ => 0) := rfl

variable [NeZero m]

def secondMap (hm : m ∣ Fintype.card F) (t : Ty) (s : F) :
    CL.RegLinear F (directionSet m) :=
  match t with
  | .dline _ => directionMap (LIDT.CL.chi hm s)
  | _ => 0

def finalMap (hm : m ∣ Fintype.card F) (t : Ty) (s : F) (v : Fin m → F) :
    CL.RegLinear F (finalSet m) :=
  match t with
  | .point W => pointMap W LinearMap.id
  | .aline W => pointMap W
      (CL.canonLin (Submodule.span F {Pi.single (LIDT.CL.chi hm s) 1}))
  | .dline W => pointMap W (CL.canonLin (Submodule.span F {v}))
  | .pauli _ => 0
  | _ => CL.RegLinear.id _

/-- All twenty-six full question maps, with an explicit three-stage register
partition. Trivial stages are retained for the lower-level question types. -/
def presentation (hm : m ∣ Fintype.card F) (t : Ty) : CL.CLFun F (Coord m) 3 :=
  .cons (seedSet m) (seedMap t) fun y =>
    .cons (directionSet m) (secondMap hm t (y .seed)) fun z =>
      .cons (finalSet m) (finalMap hm t (y .seed) (fun i => z (.direction i)))
        fun _ => .zero

theorem presentation_exactlyOn (hm : m ∣ Fintype.card F) (t : Ty) :
    (presentation hm t).ExactlyOn univ := by
  refine ⟨subset_univ _, fun _ => ⟨direction_subset m, fun _ => ?_⟩⟩
  rw [remainder_eq]
  exact ⟨Subset.rfl, fun _ => by simp⟩

/-- Decode the actual content carried by a question of the specified type. -/
def questionOfVector (t : Ty) (x : Coord m → F) : Question F m :=
  let c := vectorContent x
  match t with
  | .point W => .point W (c.pt W)
  | .aline W => .aline W (c.pt W) c.s
  | .dline W => .dline W (c.pt W) c.s c.v
  | .pauli W => .pauli W
  | .pairB W => .pairB W c.omega
  | .pair => .pair c.omega
  | .con i => .con i c.omega
  | .var j => .var j c.omega

/-- Full evaluation produces exactly the seeded question in `QLD.Game`,
including its seed-dependent diagonal direction and canonical base point. -/
theorem questionOfVector_presentation (hm : m ∣ Fintype.card F)
    (t : Ty) (c : Content F m) :
    questionOfVector t ((presentation hm t).eval (contentVector c)) = c.question hm t := by
  cases t <;> (try cases ‹Bas›) <;>
    simp only [questionOfVector, presentation, seedMap, secondMap, finalMap,
      CL.CLFun.eval, CL.RegLinear.zero_apply, CL.RegLinear.id_apply,
      pointMap_apply, directionMap_apply, Pi.add_apply, Pi.zero_apply,
      vectorContent, Content.question, Content.pt, Content.omega,
      LIDT.CL.rep]
  all_goals
    simp [CL.proj_apply, seedSet, directionSet, finalSet, contentVector]
  all_goals constructor <;> rfl

/-- Full Pauli questions have the literal zero content needed by the
introspection sampling and first-hiding edges. -/
theorem presentation_pauli_eval (hm : m ∣ Fintype.card F)
    (W : Bas) (x : Coord m → F) : (presentation hm (.pauli W)).eval x = 0 := by
  simp [presentation, seedMap, secondMap, finalMap]

/-- Numbering the existing random content preserves its uniform law. -/
def sampleEquiv : Sample F m ≃ (TyEdge × (Coord m → F)) :=
  Equiv.prodCongr (Equiv.refl _) contentEquiv

/-- The actual Pauli game's question law is generated by the constructed CL
family, using a uniformly chosen graph edge and a common ambient vector. -/
theorem qldGame_mu_presentation [Algebra (ZMod 2) F] {d : ℕ}
    (hm : m ∣ Fintype.card F) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y =
      SampledGame.dist
        (fun p : TyEdge × (Coord m → F) =>
          questionOfVector p.1.val.1 ((presentation hm p.1.val.1).eval p.2))
        (fun p : TyEdge × (Coord m → F) =>
          questionOfVector p.1.val.2 ((presentation hm p.1.val.2).eval p.2)) x y := by
  change (∑ p : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
    if (p.2.question hm p.1.val.1, p.2.question hm p.1.val.2) = (x, y)
      then 1 else 0) = _
  unfold SampledGame.dist
  rw [← Finset.mul_sum, Fintype.card_congr (sampleEquiv (F := F) (m := m))]
  congr 1
  refine Fintype.sum_equiv sampleEquiv _ _ fun p => ?_
  simp only [sampleEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    contentEquiv, Equiv.coe_fn_mk, questionOfVector_presentation]

end MIPRE.QLD.PauliCL
end
