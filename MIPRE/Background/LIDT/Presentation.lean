/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.CLGame
import MIPRE.Foundations.CL.Basic

/-!
# The seeded low-degree questions as CL functions, on any registers

The paper's typed CL functions `L_Point`, `L_ALine`, `L_DLine` (`ldt.tex`, `eq:cl-ptf` to
`eq:cl-dlnf`) act on three registers of an ambient space: a point register `V_pt ≅ F^n`, a
coordinate (seed) register `V_coord ≅ F` and a direction register `V_dir ≅ F^n`. The answer-reduced
sampler (`sec:ar-verifier`) uses six copies of them on *overlapping* registers of one ambient
space, so the registers are data here: `Regs ι n` places them in the coordinates `ι` of the
ambient space by two injections and a coordinate.

Every type gets a three-level presentation (`pres`), the levels being the seed, then the
direction, then everything else; the paper's one- and two-level functions are the same with
trivial levels, as in `QLD.PauliCL.presentation`. The presentations are exact on the whole space
(`pres_exactlyOn`), and their full evaluation, read back through the registers (`questionOf`), is
the seeded test's question `LIDT.CL.Sample.question` for the sample the registers carry
(`questionOf_eval`).
-/

noncomputable section

namespace MIPRE.CL

open Finset

/-- **Summing over vectors through an injection of coordinates**: `x ↦ x ∘ e` has fibres of
size `q^{|ι| - |κ|}`. -/
theorem sum_comp_injective {κ ι F M : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [AddCommMonoid M] (e : κ → ι)
    (he : Function.Injective e) (g : (κ → F) → M) :
    ∑ x : ι → F, g (x ∘ e)
      = (Fintype.card F ^ (Fintype.card ι - Fintype.card κ)) • ∑ y : κ → F, g y := by
  classical
  rw [← Finset.sum_fiberwise (univ : Finset (ι → F)) (fun x => x ∘ e) (fun x => g (x ∘ e)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const]
  congr 1
  have hc : (univ.filter fun x : ι → F => x ∘ e = y).card
      = Fintype.card ({c : ι // c ∉ Set.range e} → F) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun x c => x.1 c.1
        invFun := fun z => ⟨fun c => if h : ∃ k, e k = c then y h.choose
          else z ⟨c, fun ⟨k, hk⟩ => h ⟨k, hk⟩⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · funext k
      have h : ∃ k', e k' = e k := ⟨k, rfl⟩
      simp only [Function.comp_apply, dif_pos h]
      rw [he h.choose_spec]
    · rintro ⟨x, hx⟩
      apply Subtype.ext
      funext c
      simp only
      split_ifs with h
      · rw [← hx, Function.comp_apply, h.choose_spec]
      · rfl
    · intro z
      funext c
      simp only
      rw [dif_neg fun ⟨k, hk⟩ => c.2 ⟨k, hk⟩]
  rw [hc, Fintype.card_fun, Fintype.card_subtype_compl, Set.card_range_of_injective he]

end MIPRE.CL

namespace MIPRE.LIDT.CL

open Finset MIPRE.CL

/-- The three registers of a copy of the low-degree test in an ambient space with coordinates
`ι`: the point and direction registers, each `n` coordinates, and the seed coordinate. -/
structure Regs (ι : Type*) (n : ℕ) where
  /-- The point register. -/
  pt : Fin n → ι
  /-- The direction register. -/
  dir : Fin n → ι
  /-- The coordinate (seed) register. -/
  coord : ι
  pt_injective : Function.Injective pt
  dir_injective : Function.Injective dir
  pt_ne_dir : ∀ i j, pt i ≠ dir j
  pt_ne_coord : ∀ i, pt i ≠ coord
  dir_ne_coord : ∀ j, dir j ≠ coord

namespace Regs

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]

/-! ## Reading and writing registers -/

/-- The point a vector carries. -/
def ptOf (x : ι → F) : Point F n := fun i => x (R.pt i)

/-- The direction a vector carries. -/
def dirOf (x : ι → F) : Point F n := fun i => x (R.dir i)

/-- Write a point into the point register, zero elsewhere. -/
def putPt : Point F n →ₗ[F] (ι → F) := Function.ExtendByZero.linearMap F R.pt

/-- Write a direction into the direction register, zero elsewhere. -/
def putDir : Point F n →ₗ[F] (ι → F) := Function.ExtendByZero.linearMap F R.dir

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putPt_pt (w : Point F n) (i : Fin n) : R.putPt w (R.pt i) = w i := by
  simp [putPt, R.pt_injective.extend_apply]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putDir_dir (w : Point F n) (i : Fin n) : R.putDir w (R.dir i) = w i := by
  simp [putDir, R.dir_injective.extend_apply]

omit [DecidableEq ι] [Fintype ι] in
theorem putPt_of_not {c : ι} (h : ∀ i, R.pt i ≠ c) (w : Point F n) : R.putPt w c = 0 := by
  simp only [putPt, Function.ExtendByZero.linearMap_apply]
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => h i hi]
  rfl

omit [DecidableEq ι] [Fintype ι] in
theorem putDir_of_not {c : ι} (h : ∀ i, R.dir i ≠ c) (w : Point F n) : R.putDir w c = 0 := by
  simp only [putDir, Function.ExtendByZero.linearMap_apply]
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => h i hi]
  rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem ptOf_putPt (w : Point F n) : R.ptOf (R.putPt w) = w := by
  funext i; simp [ptOf]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem dirOf_putDir (w : Point F n) : R.dirOf (R.putDir w) = w := by
  funext i; simp [dirOf]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem dirOf_putPt (w : Point F n) : R.dirOf (R.putPt w) = 0 := by
  funext j; exact R.putPt_of_not (fun i => R.pt_ne_dir i j) w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem ptOf_putDir (w : Point F n) : R.ptOf (R.putDir w) = 0 := by
  funext i; exact R.putDir_of_not (fun j h => R.pt_ne_dir i j h.symm) w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putPt_coord (w : Point F n) : R.putPt w R.coord = 0 :=
  R.putPt_of_not R.pt_ne_coord w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putDir_coord (w : Point F n) : R.putDir w R.coord = 0 :=
  R.putDir_of_not R.dir_ne_coord w

/-! ## The register sets -/

/-- The seed register. -/
def coordSet : Finset ι := {R.coord}

/-- The direction register. -/
def dirSet : Finset ι := univ.image R.dir

/-- Everything else: the point register and the coordinates no copy of the test reads. -/
def finalSet : Finset ι := (univ \ R.coordSet) \ R.dirSet

theorem dirSet_subset : R.dirSet ⊆ univ \ R.coordSet := by
  intro c hc
  obtain ⟨j, -, rfl⟩ := mem_image.mp hc
  simp [coordSet, R.dir_ne_coord j]

theorem pt_mem_finalSet (i : Fin n) : R.pt i ∈ R.finalSet := by
  simp only [finalSet, coordSet, dirSet, mem_sdiff, mem_univ, mem_singleton, mem_image,
    true_and, not_exists]
  exact ⟨R.pt_ne_coord i, fun j h => R.pt_ne_dir i j h.symm⟩

omit [Fintype ι] in
theorem dir_mem_dirSet (j : Fin n) : R.dir j ∈ R.dirSet := mem_image_of_mem _ (mem_univ j)

theorem proj_finalSet_putPt (w : Point F n) : proj R.finalSet (R.putPt w) = R.putPt w := by
  refine proj_eq_self_iff.mpr fun c hc =>
    R.putPt_of_not (fun i h => hc (by subst h; exact R.pt_mem_finalSet i)) w

omit [Fintype ι] in
theorem proj_dirSet_putDir (w : Point F n) : proj R.dirSet (R.putDir w) = R.putDir w := by
  refine proj_eq_self_iff.mpr fun c hc =>
    R.putDir_of_not (fun j h => hc (by subst h; exact R.dir_mem_dirSet j)) w

theorem ptOf_proj_finalSet (x : ι → F) : R.ptOf (proj R.finalSet x) = R.ptOf x := by
  funext i; simp [ptOf, proj_apply_of_mem (R.pt_mem_finalSet i)]

omit [Fintype ι] in
theorem dirOf_proj_dirSet (x : ι → F) : R.dirOf (proj R.dirSet x) = R.dirOf x := by
  funext j; simp [dirOf, proj_apply_of_mem (R.dir_mem_dirSet j)]

/-! ## The stage maps -/

/-- `π_i`, zeroing the first `i` coordinates, as a linear map. -/
def zeroBelowLin (i : Fin n) : Point F n →ₗ[F] Point F n where
  toFun := zeroBelow i
  map_add' x y := by funext k; simp only [zeroBelow, Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by funext k; simp only [zeroBelow, Pi.smul_apply]; split_ifs <;> simp

/-- A linear map of the point register, as a map on the final register. -/
def ptLin (A : Point F n →ₗ[F] Point F n) : RegLinear F R.finalSet :=
  RegLinear.ofLinearMap R.finalSet (R.putPt ∘ₗ A ∘ₗ LinearMap.funLeft F F R.pt)

theorem ptLin_apply (A : Point F n →ₗ[F] Point F n) (x : ι → F) :
    R.ptLin A x = R.putPt (A (R.ptOf x)) := by
  simp only [ptLin, RegLinear.ofLinearMap_apply, LinearMap.comp_apply]
  rw [show (LinearMap.funLeft F F R.pt) (proj R.finalSet x) = R.ptOf (proj R.finalSet x) from rfl,
    R.ptOf_proj_finalSet, R.proj_finalSet_putPt]

/-- `π_i` of the direction register. -/
def dirLin (i : Fin n) : RegLinear F R.dirSet :=
  RegLinear.ofLinearMap R.dirSet (R.putDir ∘ₗ zeroBelowLin i ∘ₗ LinearMap.funLeft F F R.dir)

omit [Fintype ι] in
theorem dirLin_apply (i : Fin n) (x : ι → F) :
    R.dirLin i x = R.putDir (zeroBelow i (R.dirOf x)) := by
  simp only [dirLin, RegLinear.ofLinearMap_apply, LinearMap.comp_apply]
  rw [show (LinearMap.funLeft F F R.dir) (proj R.dirSet x) = R.dirOf (proj R.dirSet x) from rfl,
    R.dirOf_proj_dirSet]
  exact R.proj_dirSet_putDir _

variable [Fintype F] [DecidableEq F] [NeZero n] (hn : n ∣ Fintype.card F)

/-- The first stage: the seed, for the two line types. -/
def seedLin : Ty → RegLinear F R.coordSet
  | .point => 0
  | _ => RegLinear.id _

/-- The second stage: `π_{χ(s)}` of the direction, for the diagonal type. -/
def secondLin : Ty → F → RegLinear F R.dirSet
  | .dline, s => R.dirLin (chi hn s)
  | _, _ => 0

/-- The third stage: the canonical base point of the line through the point. -/
def finalLin : Ty → F → Point F n → RegLinear F R.finalSet
  | .point, _, _ => R.ptLin LinearMap.id
  | .aline, s, _ => R.ptLin (MIPRE.CL.canonLin (Submodule.span F {Pi.single (chi hn s) 1}))
  | .dline, _, v => R.ptLin (MIPRE.CL.canonLin (Submodule.span F {v}))

/-- **The three-level presentation** of the question of type `t`: seed, then direction, then
the point register and everything else. -/
def pres (t : Ty) : CLFun F ι 3 :=
  .cons R.coordSet (R.seedLin t) fun y =>
    .cons R.dirSet (R.secondLin hn t (y R.coord)) fun z =>
      .cons R.finalSet (R.finalLin hn t (y R.coord) (R.dirOf z)) fun _ => .zero

omit [DecidableEq F] in
theorem pres_exactlyOn (t : Ty) : (R.pres hn t).ExactlyOn univ :=
  ⟨subset_univ _, fun _ => ⟨R.dirSet_subset, fun _ => ⟨Subset.rfl, fun _ => Finset.sdiff_self _⟩⟩⟩

/-- Read the question of type `t` off a vector. -/
def questionOf (t : Ty) (x : ι → F) : Question F n :=
  match t with
  | .point => .point (R.ptOf x)
  | .aline => .aline (R.ptOf x) (x R.coord)
  | .dline => .dline (R.ptOf x) (x R.coord) (R.dirOf x)

/-- The sample a vector carries, with both types `t`. -/
def sampleOf (t : Ty) (x : ι → F) : Sample F n := ⟨t, t, R.ptOf x, x R.coord, R.dirOf x⟩

omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem not_mem_coordSet_pt (i : Fin n) : R.pt i ∉ R.coordSet := by
  simp [coordSet, R.pt_ne_coord i]

omit [Fintype ι] [NeZero n] in
theorem not_mem_dirSet_pt (i : Fin n) : R.pt i ∉ R.dirSet := by
  simp only [dirSet, mem_image, mem_univ, true_and, not_exists]
  exact fun j h => R.pt_ne_dir i j h.symm

omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem not_mem_coordSet_dir (j : Fin n) : R.dir j ∉ R.coordSet := by
  simp [coordSet, R.dir_ne_coord j]

omit [DecidableEq ι] [Fintype ι] [NeZero n] in
theorem coord_mem_coordSet : R.coord ∈ R.coordSet := mem_singleton_self _

omit [DecidableEq F] in
/-- **The presentation computes the seeded question** of the sample the registers carry. -/
theorem questionOf_eval (t : Ty) (x : ι → F) :
    R.questionOf t ((R.pres hn t).eval x) = (R.sampleOf t x).question hn t := by
  have hpt : ∀ i, (proj R.dirSetᶜ (proj R.coordSetᶜ x)) (R.pt i) = x (R.pt i) := fun i => by
    rw [proj_apply_of_mem (by simpa using R.not_mem_dirSet_pt i),
      proj_apply_of_mem (by simpa using R.not_mem_coordSet_pt i)]
  have hptOf : R.ptOf (proj R.dirSetᶜ (proj R.coordSetᶜ x)) = R.ptOf x := funext hpt
  have hdirOf : R.dirOf (proj R.coordSetᶜ x) = R.dirOf x := by
    funext j
    simp only [dirOf]
    rw [proj_apply_of_mem (by simpa using R.not_mem_coordSet_dir j)]
  have hcoord : (proj R.coordSet x) R.coord = x R.coord := proj_apply_of_mem R.coord_mem_coordSet x
  cases t with
  | point =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.zero_apply, zero_add, add_zero, ptLin_apply, LinearMap.id_apply, hptOf]
    simp [questionOf, sampleOf, Sample.question]
  | aline =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.zero_apply, RegLinear.id_apply, zero_add, add_zero, ptLin_apply, hptOf, hcoord]
    simp only [questionOf, sampleOf, Sample.question, rep]
    congr 1
    · funext i
      simp only [ptOf, Pi.add_apply]
      rw [proj_apply_of_not_mem (R.not_mem_coordSet_pt i), zero_add, R.putPt_pt]
    · simp [hcoord]
  | dline =>
    simp only [pres, CLFun.eval_cons, CLFun.eval_zero, seedLin, secondLin, finalLin,
      RegLinear.id_apply, add_zero, ptLin_apply, dirLin_apply, hptOf, hcoord, hdirOf]
    simp only [dirOf_putDir]
    simp only [questionOf, sampleOf, Sample.question, rep]
    congr 1
    · funext i
      simp only [ptOf, Pi.add_apply]
      rw [proj_apply_of_not_mem (R.not_mem_coordSet_pt i), R.putDir_of_not
        (fun j h => R.pt_ne_dir i j h.symm), R.putPt_pt]
      simp
    · simp [hcoord]
    · funext j
      simp only [dirOf, Pi.add_apply]
      rw [proj_apply_of_not_mem (R.not_mem_coordSet_dir j), R.putDir_dir,
        R.putPt_of_not (fun i => R.pt_ne_dir i j)]
      simp

/-! ## The law of the sample -/

omit [DecidableEq ι] [Fintype ι] [DecidableEq F] [NeZero n] in
/-- The registers, as one injection of `Fin n ⊕ (Unit ⊕ Fin n)`. -/
theorem embed_injective :
    Function.Injective (Sum.elim R.pt (Sum.elim (fun _ : Unit => R.coord) R.dir)) := by
  rintro (i | _ | j) (i' | _ | j') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · rw [R.pt_injective h]
  · exact absurd h (R.pt_ne_coord i)
  · exact absurd h (R.pt_ne_dir i j')
  · exact absurd h.symm (R.pt_ne_coord i')
  · rfl
  · exact absurd h.symm (R.dir_ne_coord j')
  · exact absurd h.symm (R.pt_ne_dir i' j)
  · exact absurd h (R.dir_ne_coord j)
  · rw [R.dir_injective h]

omit [Field F] [DecidableEq F] [NeZero n] in
/-- **Uniform content gives a uniform sample**: summing a function of the sample the registers
carry over all vectors is summing it over all samples, `q^{|ι| - (2n+1)}` times. -/
theorem sum_sampleOf {M : Type*} [AddCommMonoid M] (t : Ty) (g : Sample F n → M) :
    ∑ x : ι → F, g (R.sampleOf t x)
      = (Fintype.card F ^ (Fintype.card ι - (2 * n + 1))) •
          ∑ u : Point F n, ∑ s : F, ∑ v : Point F n, g ⟨t, t, u, s, v⟩ := by
  classical
  set e := Sum.elim R.pt (Sum.elim (fun _ : Unit => R.coord) R.dir)
  let G : (Fin n ⊕ (Unit ⊕ Fin n) → F) → M := fun y =>
    g ⟨t, t, fun i => y (.inl i), y (.inr (.inl ())), fun j => y (.inr (.inr j))⟩
  rw [show (∑ x : ι → F, g (R.sampleOf t x)) = ∑ x : ι → F, G (x ∘ e) from rfl,
    MIPRE.CL.sum_comp_injective e R.embed_injective G]
  congr 1
  · simp [Fintype.card_sum]; ring_nf
  · rw [← (Equiv.sumArrowEquivProdArrow _ _ F).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← (Equiv.sumArrowEquivProdArrow _ _ F).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    rw [← (Equiv.funUnique Unit F).symm.sum_comp]
    rfl

end Regs

end MIPRE.LIDT.CL

end
