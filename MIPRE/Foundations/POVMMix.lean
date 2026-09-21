/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Pasting

/-!
# Mixtures and extensions of POVMs, and the agreement triangle

Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4
needs, and one inequality.

* `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with
  certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy
  that must be a *function of the question* while the analysis controls it *sample by sample* is
  a mixture over the samples producing the question, and the Born rule's linearity
  (`bornProb_mix_left`, `bornProb_mix_right`) turns a bound on the mixture into the average of the
  per-sample bounds.
* `agreeSum_triangle` is the paper's triangle-like inequality for the consistency relation
  (`fact:triangle-for-simeq`, item 1): if Alice's `A` agrees with Bob's `B`, Alice's `C` agrees
  with Bob's `B`, and Alice's `C` agrees with Bob's `D`, each with probability at least `1 - δ`,
  then Alice's `A` agrees with Bob's `D` with probability at least `1 - 11 δ`. No projectivity is
  assumed: for POVMs the agreement is not a squared distance, and the argument goes through the
  vectors `(R_a ⊗ I)|ψ⟩`, whose weighted squared norms are at most one and, by Cauchy--Schwarz
  against a partner they agree with, at least `1 - 2δ`. The paper pads these vectors to unit
  vectors and gets `9 δ`; the unpadded argument here costs the extra `2 δ` and needs no auxiliary
  space.
-/

noncomputable section

namespace MIPRE

open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

/-! ## Extension by the identity, and the deterministic POVM -/

section Lift

variable {A : Type*} [Fintype A] {d E : Type*} [Fintype d] [DecidableEq d] [Fintype E]
  [DecidableEq E]

/-- A POVM on `d`, extended by the identity to `d × E`. -/
def POVM.aOp (M : POVM A d) : POVM A (d × E) where
  mats a := ⟨MIPRE.aOp (M.mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, aOp_conjTranspose,
      ← Matrix.star_eq_conjTranspose, selfAdjoint.mem_iff.mp (M.mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      ((M.posSemidef a).kronecker Matrix.PosSemidef.one))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, MIPRE.aOp (M.mats a).val = 1
    rw [← aOp_sum, POVM.sum_val, aOp_one]

@[simp] theorem POVM.aOp_mats (M : POVM A d) (a : A) :
    ((M.aOp (E := E)).mats a).val = MIPRE.aOp (M.mats a).val := rfl

/-- Extending by the identity commutes with relabelling the outcomes. -/
theorem POVM.map_aOp {B : Type*} [Fintype B] [DecidableEq B] (f : A → B) (M : POVM A d) :
    (M.map f).aOp (E := E) = (M.aOp (E := E)).map f :=
  POVM.ext' fun b => by
    rw [POVM.aOp_mats, POVM.map_mats, POVM.map_mats, aOp_sum]
    rfl

variable [DecidableEq A]

/-- The deterministic POVM answering `a₀`. -/
def POVM.dirac (a₀ : A) : POVM A d where
  mats a := ⟨if a = a₀ then 1 else 0, by
    rw [selfAdjoint.mem_iff]
    split_ifs <;> simp⟩
  nonneg a := by
    refine Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
    show (if a = a₀ then (1 : Matrix d d ℂ) else 0).PosSemidef
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, (if a = a₀ then (1 : Matrix d d ℂ) else 0) = 1
    rw [Finset.sum_ite_eq' univ a₀]
    simp

end Lift

/-! ## Mixtures -/

section Mix

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d] {ι : Type*} [Fintype ι]

/-- **A convex combination of POVMs** with the same outcomes, with real weights `w` summing to
one. -/
def POVM.mix (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Q : ι → POVM A d) :
    POVM A d where
  mats a := ⟨∑ i, w i • ((Q i).mats a).val, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, star_trivial, ← Matrix.star_eq_conjTranspose,
      selfAdjoint.mem_iff.mp ((Q i).mats a).prop]⟩
  nonneg a :=
    Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_sum _ fun i _ => ((Q i).posSemidef a).smul (hw i)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, ∑ i, w i • ((Q i).mats a).val = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, POVM.sum_val]
    rw [← Finset.sum_smul, hw1, one_smul]

@[simp] theorem POVM.mix_mats (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (Q : ι → POVM A d) (a : A) :
    ((POVM.mix w hw hw1 Q).mats a).val = ∑ i, w i • ((Q i).mats a).val := rfl

variable {dA dB : Type*} [Fintype dA] [Fintype dB]

/-- The Born probability is linear in a real multiple of Alice's operator. -/
theorem bornProb_smul_left (ψ : dA × dB → ℂ) (r : ℝ) (EA : Matrix dA dA ℂ)
    (EB : Matrix dB dB ℂ) : bornProb ψ (r • EA) EB = r * bornProb ψ EA EB := by
  rw [bornProb, bornProb, Matrix.smul_kronecker, Matrix.smul_mulVec, dotProduct_smul,
    Complex.real_smul, Complex.re_ofReal_mul]

/-- The Born probability is linear in a real multiple of Bob's operator. -/
theorem bornProb_smul_right (ψ : dA × dB → ℂ) (r : ℝ) (EA : Matrix dA dA ℂ)
    (EB : Matrix dB dB ℂ) : bornProb ψ EA (r • EB) = r * bornProb ψ EA EB := by
  rw [bornProb, bornProb, Matrix.kronecker_smul, Matrix.smul_mulVec, dotProduct_smul,
    Complex.real_smul, Complex.re_ofReal_mul]

variable [DecidableEq dA] [DecidableEq dB]

/-- **The Born probability of a mixture is the mixture of the Born probabilities**, on Alice's
side. -/
theorem bornProb_mix_left (ψ : dA × dB → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (Q : ι → POVM A dA) (a : A) (EB : Matrix dB dB ℂ) :
    bornProb ψ (((POVM.mix w hw hw1 Q).mats a).val) EB
      = ∑ i, w i * bornProb ψ (((Q i).mats a).val) EB := by
  rw [POVM.mix_mats, bornProb_sum_left]
  exact Finset.sum_congr rfl fun i _ => bornProb_smul_left ψ (w i) _ _

/-- The same, on Bob's side. -/
theorem bornProb_mix_right (ψ : dA × dB → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (EA : Matrix dA dA ℂ) (Q : ι → POVM A dB) (a : A) :
    bornProb ψ EA (((POVM.mix w hw hw1 Q).mats a).val)
      = ∑ i, w i * bornProb ψ EA (((Q i).mats a).val) := by
  rw [POVM.mix_mats, bornProb_sum_right]
  exact Finset.sum_congr rfl fun i _ => bornProb_smul_right ψ (w i) _ _

end Mix

/-! ## A POVM from a positive family, and uniform averages -/

section Of

variable {A : Type*} [Fintype A] {d : Type*} [Fintype d] [DecidableEq d]

/-- A POVM from a family of positive semidefinite matrices summing to the identity. -/
def POVM.ofPosSemidef (E : A → Matrix d d ℂ) (hpos : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) : POVM A d where
  mats a := ⟨E a, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (hpos a).isHermitian.eq⟩
  nonneg a := Subtype.coe_le_coe.mp (Matrix.nonneg_iff_posSemidef.mpr (hpos a))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hsum

@[simp] theorem POVM.ofPosSemidef_mats (E : A → Matrix d d ℂ) (hpos : ∀ a, (E a).PosSemidef)
    (hsum : ∑ a, E a = 1) (a : A) : ((POVM.ofPosSemidef E hpos hsum).mats a).val = E a := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform weights on a finset. -/
def unifOn (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then (S.card : ℝ)⁻¹ else 0

omit [Fintype ι] in
theorem unifOn_nonneg (S : Finset ι) (i : ι) : 0 ≤ unifOn S i := by
  unfold unifOn
  split_ifs <;> positivity

theorem sum_unifOn (S : Finset ι) (hS : S.Nonempty) : ∑ i, unifOn S i = 1 := by
  unfold unifOn
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hS).ne')

variable [DecidableEq A]

/-- **The uniform average of POVMs over a finset**, defaulting to the deterministic answer `a₀`
when the finset is empty. -/
def POVM.avgOn (S : Finset ι) (Q : ι → POVM A d) (a₀ : A) : POVM A d :=
  if hS : S.Nonempty then POVM.mix (unifOn S) (unifOn_nonneg S) (sum_unifOn S hS) Q
  else POVM.dirac a₀

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem bornProb_avgOn_left (ψ : dA × dB → ℂ) {S : Finset ι} (hS : S.Nonempty)
    (Q : ι → POVM A dA) (a₀ : A) (a : A) (EB : Matrix dB dB ℂ) :
    bornProb ψ (((POVM.avgOn S Q a₀).mats a).val) EB
      = (S.card : ℝ)⁻¹ * ∑ i ∈ S, bornProb ψ (((Q i).mats a).val) EB := by
  rw [POVM.avgOn, dif_pos hS, bornProb_mix_left]
  simp only [unifOn, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

theorem bornProb_avgOn_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) {S : Finset ι}
    (hS : S.Nonempty) (Q : ι → POVM A dB) (a₀ : A) (a : A) :
    bornProb ψ EA (((POVM.avgOn S Q a₀).mats a).val)
      = (S.card : ℝ)⁻¹ * ∑ i ∈ S, bornProb ψ EA (((Q i).mats a).val) := by
  rw [POVM.avgOn, dif_pos hS, bornProb_mix_right]
  simp only [unifOn, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

end Of

/-! ## Averages and relabelling -/

section AvgMap

variable {A : Type*} [Fintype A] [DecidableEq A] {d : Type*} [Fintype d] [DecidableEq d]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operators of a uniform average over a nonempty finset. -/
theorem POVM.avgOn_mats {S : Finset ι} (hS : S.Nonempty) (Q : ι → POVM A d) (a₀ : A) (a : A) :
    ((POVM.avgOn S Q a₀).mats a).val = (S.card : ℝ)⁻¹ • ∑ i ∈ S, ((Q i).mats a).val := by
  rw [POVM.avgOn, dif_pos hS, POVM.mix_mats, Finset.smul_sum]
  simp only [unifOn, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

omit [DecidableEq A] [DecidableEq ι] in
/-- Relabelling commutes with mixing. -/
theorem POVM.map_mix {B : Type*} [Fintype B] [DecidableEq B] (g : A → B) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (Q : ι → POVM A d) :
    (POVM.mix w hw hw1 Q).map g = POVM.mix w hw hw1 fun i => (Q i).map g :=
  POVM.ext' fun b => by
    simp only [POVM.map_mats, POVM.mix_mats, Finset.smul_sum]
    exact Finset.sum_comm

/-- Relabelling the deterministic POVM. -/
theorem POVM.map_dirac {B : Type*} [Fintype B] [DecidableEq B] (g : A → B) (a₀ : A) :
    (POVM.dirac (d := d) a₀).map g = POVM.dirac (g a₀) :=
  POVM.ext' fun b => by
    rw [POVM.map_mats]
    show (∑ a ∈ univ.filter fun a => g a = b, if a = a₀ then (1 : Matrix d d ℂ) else 0)
      = if b = g a₀ then 1 else 0
    rw [Finset.sum_ite_eq' (univ.filter fun a => g a = b) a₀ fun _ => (1 : Matrix d d ℂ)]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact if_congr eq_comm rfl rfl

/-- Relabelling commutes with the uniform average. -/
theorem POVM.map_avgOn {B : Type*} [Fintype B] [DecidableEq B] (g : A → B) (S : Finset ι)
    (Q : ι → POVM A d) (a₀ : A) :
    (POVM.avgOn S Q a₀).map g = POVM.avgOn S (fun i => (Q i).map g) (g a₀) := by
  by_cases hS : S.Nonempty
  · rw [POVM.avgOn, POVM.avgOn, dif_pos hS, dif_pos hS, POVM.map_mix]
  · rw [POVM.avgOn, POVM.avgOn, dif_neg hS, dif_neg hS, POVM.map_dirac]

/-- Relabelling along the identity does nothing. -/
theorem POVM.map_id (M : POVM A d) : M.map (fun a => a) = M :=
  POVM.ext' fun b => by
    rw [POVM.map_mats, Finset.sum_filter, Finset.sum_ite_eq' univ b fun a => (M.mats a).val]
    simp

omit [DecidableEq A] in
/-- An outcome outside the range of the relabelling carries the zero operator. -/
theorem POVM.map_mats_eq_zero_of_forall_ne {B : Type*} [Fintype B] [DecidableEq B] (f : A → B)
    (M : POVM A d) {b : B} (h : ∀ a, f a ≠ b) : ((M.map f).mats b).val = 0 := by
  rw [POVM.map_mats]
  exact Finset.sum_eq_zero fun a ha => absurd (Finset.mem_filter.mp ha).2 (h a)

omit [DecidableEq A] in
/-- Two relabellings that agree on the support of a POVM relabel it the same way. -/
theorem POVM.map_congr_of_support {B : Type*} [Fintype B] [DecidableEq B] {f g : A → B}
    (M : POVM A d) (h : ∀ a, (M.mats a).val ≠ 0 → f a = g a) : M.map f = M.map g :=
  POVM.ext' fun b => by
    rw [POVM.map_mats, POVM.map_mats, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : (M.mats a).val = 0
    · rw [ha]
      simp
    · rw [h a ha]

end AvgMap

/-! ## Acceptance on the support, and the conditional failure -/

section Fail

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_zero_left (ψ : dA × dB → ℂ) (EB : Matrix dB dB ℂ) : bornProb ψ 0 EB = 0 := by
  rw [bornProb, Matrix.zero_kronecker, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]

omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_zero_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) : bornProb ψ EA 0 = 0 := by
  rw [bornProb, Matrix.kronecker_zero, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]

variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}

/-- **Agreement on the support implies acceptance bounds the conditional failure by the
disagreement of the relabelled POVMs.** Only outcomes both parties can produce are asked to be
accepted, which is what a strategy answering every question in its own format needs. -/
theorem condFail_le_one_sub_sum_bornProb_map {G : Game X Y A B} {MA : X → POVM A dA}
    {MB : Y → POVM B dB} (f : A → C) (g : B → C)
    (hD : ∀ a b, ((MA x).mats a).val ≠ 0 → ((MB y).mats b).val ≠ 0 → f a = g b →
      G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val) := by
  classical
  rw [sum_bornProb_map, condFail]
  have hle : ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
      * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) ≤ condWin G ψ MA MB x y := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hfg : f a = g b
    · rw [if_pos hfg]
      by_cases hA : ((MA x).mats a).val = 0
      · rw [hA, bornProb_zero_left, mul_zero, mul_zero]
      by_cases hB : ((MB y).mats b).val = 0
      · rw [hB, bornProb_zero_right, mul_zero, mul_zero]
      rw [if_pos (hD a b hA hB hfg)]
    · rw [if_neg hfg, zero_mul]
      exact mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b))
  linarith

/-- The same with both parties' outcomes read as they are: acceptance of every diagonal pair
on the support bounds the conditional failure by the diagonal disagreement. -/
theorem condFail_le_one_sub_sum_bornProb_diag {G : Game X Y A A} {MA : X → POVM A dA}
    {MB : Y → POVM A dB}
    (hD : ∀ a, ((MA x).mats a).val ≠ 0 → ((MB y).mats a).val ≠ 0 → G.D x y a a = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ a, bornProb ψ (((MA x).mats a).val) (((MB y).mats a).val) := by
  classical
  rw [condFail]
  have hle : ∑ a, bornProb ψ (((MA x).mats a).val) (((MB y).mats a).val)
      ≤ condWin G ψ MA MB x y := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun b => (if G.D x y a b then (1 : ℝ) else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val))
      (fun b _ => mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b))) (Finset.mem_univ a))
    by_cases hA : ((MA x).mats a).val = 0
    · rw [hA, bornProb_zero_left, mul_zero]
    by_cases hB : ((MB y).mats a).val = 0
    · rw [hB, bornProb_zero_right, mul_zero]
    rw [if_pos (hD a hA hB), one_mul]
  linarith

/-- `sum_bornProb_map` for two bare POVMs. -/
theorem sum_bornProb_map' {A B : Type*} [Fintype A] [Fintype B] (P : POVM A dA) (Q : POVM B dB)
    (f : A → C) (g : B → C) :
    ∑ c, bornProb ψ (((P.map f).mats c).val) (((Q.map g).mats c).val)
      = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ ((P.mats a).val) ((Q.mats b).val) :=
  sum_bornProb_map (MA := fun _ : Unit => P) (MB := fun _ : Unit => Q) (x := ()) (y := ()) f g

/-- Forgetting the outcome altogether gives the identity operator. -/
theorem POVM.map_const_mats {A : Type*} [Fintype A] (P : POVM A dA) :
    ((P.map fun _ => ()).mats ()).val = 1 := by
  rw [POVM.map_mats, Finset.filter_true_of_mem fun _ _ => rfl, POVM.sum_val]

theorem bornProb_one_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    bornProb ψ (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) = 1 := by
  rw [bornProb, Matrix.one_kronecker_one, Matrix.one_mulVec, hψ, Complex.one_re]

end Fail

/-! ## The agreement triangle -/

section Triangle

variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

/-- The agreement probability of two families of POVMs, one per party, on the same questions,
averaged over the question distribution `μ`: the paper's `p(R, S)`. -/
def agreeSum (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)

/-- The weighted squared norm of Alice's measurement vectors, `∑_x μ_x ∑_a ‖(M^x_a ⊗ I)ψ‖²`. -/
def weightA (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) : ℝ :=
  ∑ x, μ x * ∑ a, stateSqNorm ψ (((M x).mats a).val)

/-- Bob's version. -/
def weightB (μ : X → ℝ) (ψ : dA × dB → ℂ) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, ‖stateVecB ψ (((N x).mats a).val)‖ ^ 2

/-- The weighted cross-party deviation of two families. -/
def xDev (μ : X → ℝ) (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) : ℝ :=
  ∑ x, μ x * ∑ a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val)

variable {μ : X → ℝ} {ψ : dA × dB → ℂ}

theorem weightA_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) : weightA μ ψ M ≤ 1 := by
  calc weightA μ ψ M ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNorm_le_one hψ (M x)) (hμ x)
    _ = 1 := by simp [hμ1]

theorem weightB_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (N : X → POVM Λ dB) : weightB μ ψ N ≤ 1 := by
  calc weightB μ ψ N ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNormB_le_one hψ (N x)) (hμ x)
    _ = 1 := by simp [hμ1]

theorem weightA_nonneg (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) : 0 ≤ weightA μ ψ M :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => by
    rw [stateSqNorm]; positivity)

theorem weightB_nonneg (hμ : ∀ x, 0 ≤ μ x) (N : X → POVM Λ dB) : 0 ≤ weightB μ ψ N :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => by positivity)

/-- **The cross deviation expands**: `xDev = weightA + weightB - 2 agreeSum`. -/
theorem xDev_eq (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N = weightA μ ψ M + weightB μ ψ N - 2 * agreeSum μ ψ M N := by
  unfold xDev weightA weightB agreeSum
  have hexp : ∀ x a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val)
      = stateSqNorm ψ (((M x).mats a).val) + ‖stateVecB ψ (((N x).mats a).val)‖ ^ 2
        - 2 * bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := fun x a =>
    xSqNorm_eq_expand ψ (by
      rw [← Matrix.star_eq_conjTranspose]; exact selfAdjoint.mem_iff.mp ((M x).mats a).prop) _
  have hx : ∀ x, μ x * ∑ a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val)
      = μ x * ∑ a, stateSqNorm ψ (((M x).mats a).val)
        + μ x * ∑ a, ‖stateVecB ψ (((N x).mats a).val)‖ ^ 2
        - 2 * (μ x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)) := by
    intro x
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  simp only [hx, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- A Born probability is at most the product of the two state norms (Cauchy--Schwarz). -/
theorem bornProb_le_norm_mul_norm (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} (hEA : EAᴴ = EA)
    (EB : Matrix dB dB ℂ) :
    bornProb ψ EA EB ≤ ‖stateVec ψ EA‖ * ‖stateVecB ψ EB‖ := by
  have h : bornProb ψ EA EB = (inner ℂ (stateVec ψ EA) (stateVecB ψ EB)).re := by
    rw [inner_stateVec_stateVecB ψ hEA, bornProb]
  rw [h]
  exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)

/-- **Cauchy--Schwarz for the agreement**: `agreeSum ≤ √weightA · √weightB`. -/
theorem agreeSum_le_sqrt_mul_sqrt (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    agreeSum μ ψ M N ≤ Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N) := by
  classical
  have hpt : ∀ x a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)
      ≤ ‖stateVec ψ (((M x).mats a).val)‖ * ‖stateVecB ψ (((N x).mats a).val)‖ := fun x a =>
    bornProb_le_norm_mul_norm ψ (by
      rw [← Matrix.star_eq_conjTranspose]; exact selfAdjoint.mem_iff.mp ((M x).mats a).prop) _
  have h1 : agreeSum μ ψ M N ≤ ∑ p : X × Λ, μ p.1
      * (‖stateVec ψ (((M p.1).mats p.2).val)‖ * ‖stateVecB ψ (((N p.1).mats p.2).val)‖) := by
    rw [agreeSum, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun x _ => ?_
    dsimp only
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hpt x a) (hμ x)
  refine le_trans h1 (le_of_le_of_eq (sum_weighted_mul_le_sqrt (fun p : X × Λ => μ p.1)
    (fun p => ‖stateVec ψ (((M p.1).mats p.2).val)‖)
    (fun p => ‖stateVecB ψ (((N p.1).mats p.2).val)‖) fun p => hμ p.1) ?_)
  congr 1 <;> congr 1
  · rw [weightA, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [stateSqNorm, stateNorm]
  · rw [weightB, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]

/-- A family that agrees with some partner with probability at least `1 - δ` has weight at least
`1 - 2δ`. -/
theorem weightA_ge (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) {δ : ℝ} (h : 1 - agreeSum μ ψ M N ≤ δ) :
    1 - 2 * δ ≤ weightA μ ψ M := by
  have hcs := agreeSum_le_sqrt_mul_sqrt (ψ := ψ) hμ M N
  have hB : Real.sqrt (weightB μ ψ N) ≤ 1 :=
    Real.sqrt_le_one.mpr (weightB_le_one hμ hμ1 hψ N)
  have hA0 : 0 ≤ weightA μ ψ M := weightA_nonneg hμ M
  have hsA : agreeSum μ ψ M N ≤ Real.sqrt (weightA μ ψ M) :=
    le_trans hcs (by
      calc Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N)
          ≤ Real.sqrt (weightA μ ψ M) * 1 :=
            mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)
        _ = Real.sqrt (weightA μ ψ M) := mul_one _)
  by_cases hδ : 1 - δ ≤ 0
  · nlinarith
  · have h1 : 1 - δ ≤ Real.sqrt (weightA μ ψ M) := by linarith
    have h2 : (1 - δ) ^ 2 ≤ weightA μ ψ M := by
      have := Real.sq_sqrt hA0
      nlinarith [Real.sqrt_nonneg (weightA μ ψ M)]
    have hsq : 1 - 2 * δ ≤ (1 - δ) ^ 2 := by nlinarith [sq_nonneg δ]
    linarith

/-- Bob's version. -/
theorem weightB_ge (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) {δ : ℝ} (h : 1 - agreeSum μ ψ M N ≤ δ) :
    1 - 2 * δ ≤ weightB μ ψ N := by
  have hcs := agreeSum_le_sqrt_mul_sqrt (ψ := ψ) hμ M N
  have hA : Real.sqrt (weightA μ ψ M) ≤ 1 :=
    Real.sqrt_le_one.mpr (weightA_le_one hμ hμ1 hψ M)
  have hB0 : 0 ≤ weightB μ ψ N := weightB_nonneg hμ N
  have hsB : agreeSum μ ψ M N ≤ Real.sqrt (weightB μ ψ N) :=
    le_trans hcs (by
      calc Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N)
          ≤ 1 * Real.sqrt (weightB μ ψ N) :=
            mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)
        _ = Real.sqrt (weightB μ ψ N) := one_mul _)
  by_cases hδ : 1 - δ ≤ 0
  · nlinarith
  · have h1 : 1 - δ ≤ Real.sqrt (weightB μ ψ N) := by linarith
    have h2 : (1 - δ) ^ 2 ≤ weightB μ ψ N := by
      have := Real.sq_sqrt hB0
      nlinarith [Real.sqrt_nonneg (weightB μ ψ N)]
    have hsq : 1 - 2 * δ ≤ (1 - δ) ^ 2 := by nlinarith [sq_nonneg δ]
    linarith

/-- The cross deviation is at most twice the disagreement. -/
theorem xDev_le (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N ≤ 2 * (1 - agreeSum μ ψ M N) := by
  rw [xDev_eq]
  have := weightA_le_one hμ hμ1 hψ M
  have := weightB_le_one hμ hμ1 hψ N
  linarith

/-- **The weighted triangle inequality for cross deviations**: Alice's `A` against Bob's `D`,
through Bob's `B` and Alice's `C`. -/
theorem xDev_triangle (hμ : ∀ x, 0 ≤ μ x) (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) :
    xDev μ ψ A D ≤ 3 * xDev μ ψ A B + 3 * xDev μ ψ C B + 3 * xDev μ ψ C D := by
  have h := sum_weighted_snorm_sq_triangle3 ψ hμ (univ : Finset X)
    (fun x a => (aOp (((A x).mats a).val) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun x a => bOp (((B x).mats a).val)) (fun x a => aOp (((C x).mats a).val))
    (fun x a => bOp (((D x).mats a).val))
  have hmid : ∀ x a, snorm ψ ((bOp (((B x).mats a).val) : Matrix (dA × dB) (dA × dB) ℂ)
      - aOp (((C x).mats a).val)) ^ 2
      = xSqNorm ψ (((C x).mats a).val) (((B x).mats a).val) := fun x a => by
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  simp only [← xSqNorm_eq_snorm_sq, hmid] at h
  exact h

/-- **The agreement triangle** (`fact:triangle-for-simeq`, item 1, with `11 δ` in place of the
paper's `9 δ`): agreement is transitive across the two parties, for POVMs. -/
theorem agreeSum_triangle (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) {δ : ℝ}
    (hAB : 1 - agreeSum μ ψ A B ≤ δ) (hCB : 1 - agreeSum μ ψ C B ≤ δ)
    (hCD : 1 - agreeSum μ ψ C D ≤ δ) :
    1 - agreeSum μ ψ A D ≤ 11 * δ := by
  have hAD := xDev_eq (μ := μ) (ψ := ψ) A D
  have htri := xDev_triangle (μ := μ) (ψ := ψ) hμ A C B D
  have h1 := xDev_le hμ hμ1 hψ A B
  have h2 := xDev_le hμ hμ1 hψ C B
  have h3 := xDev_le hμ hμ1 hψ C D
  have hwA := weightA_ge hμ hμ1 hψ A B hAB
  have hwD := weightB_ge hμ hμ1 hψ C D hCD
  linarith

end Triangle

end MIPRE

end
