/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.RegisterEPR
public import MIPRE.Foundations.Introspection.ValueStability
public import MIPRE.Foundations.AncillaDilation

@[expose] public section

/-! # Projectivizing a conditional residual measurement

One fixed ancilla is added on the residual side of every prefix. The prefix
projectors are unchanged. Squared distance to the old projective measurement
costs `2 sqrt(delta)`; a dilation does not in general preserve that distance.

In a bipartite model (Phase 4 of `planning/mipco-track.md`): the ancilla is the first player's
one-sided extension `Ψ.expandA t₀` (`MIPRE/Foundations/AncillaDilation.lean`), an old operator
`m` becomes `m ⊗ 1`, and the dilation of the residual POVMs is `MIPRE.exists_pvm_dilation`, in
the first player's algebra and against the fixed basis vector `t₀ = inl (a₀, 0)` of the ancilla
`DilationAncilla A K`, the number `K` of Kraus terms depending on the POVMs.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical

set_option linter.unusedSectionVars false

section Distance

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
  {A T : Type*} [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]

/-- Extending an old operator by identity preserves its state norm exactly. -/
theorem stateSqNorm_expandA_diagonal (t₀ : T) (m : 𝒜) :
    (Ψ.expandA t₀).stateSqNorm (diagonal fun _ => m) = Ψ.stateSqNorm m :=
  BipartiteModel.LocalIsometry.stateSqNorm_of_W_ψ (Ψ.inertA_W_ψ t₀) m

/-- The first player's quadratic form on the one-sided extension is that of the `(t₀, t₀)`
entry. -/
theorem qform_πA_expandA (t₀ : T) (X : Matrix T T 𝒜) :
    (Ψ.expandA t₀).qform ((Ψ.expandA t₀).πA X) = Ψ.qform (Ψ.πA (X t₀ t₀)) := by
  rw [BipartiteModel.qform_expandA, BipartiteModel.expandA_πA, map_apply]

/-- A fixed-state projective dilation remains close to an old PVM. The bound
is uniform over every dilation with the displayed compression identity. -/
theorem dilated_pvm_distance (hΨ : ‖Ψ.ψ‖ = 1) (t₀ : T)
    (M R : A → 𝒜) (P : A → Matrix T T 𝒜) (hM : IsPVMIn M) (hP : IsPVMIn P)
    (hk : ∀ a, P a t₀ t₀ = R a)
    {δ : ℝ} (hd : ∑ a, Ψ.stateSqNorm (M a - R a) ≤ δ) :
    (∑ a, (Ψ.expandA t₀).stateSqNorm ((diagonal fun _ => M a) - P a)) ≤ 2 * Real.sqrt δ := by
  let q : 𝒜 → ℝ := fun x => Ψ.qform (Ψ.πA x)
  have hq_sub (x y : 𝒜) : q (x - y) = q x - q y := by
    simp only [q, map_sub, Ψ.qform_sub]
  have hq_add (x y : 𝒜) : q (x + y) = q x + q y := by
    simp only [q, map_add, Ψ.qform_add]
  have hq_sum (f : A → 𝒜) : q (∑ a, f a) = ∑ a, q (f a) := by
    simp only [q, map_sum, Ψ.qform_sum]
  have hsumR : ∑ a, R a = 1 := by
    have h := congrFun (congrFun hP.sum_eq_one t₀) t₀
    rw [Matrix.sum_apply, one_apply_eq] at h
    simpa only [hk] using h
  have hRsa a : star (R a) = R a := by
    rw [← hk, ← Matrix.star_apply, hP.star_eq]
  have hexp a : (Ψ.expandA t₀).stateSqNorm ((diagonal fun _ => M a) - P a) =
      q (M a) + q (R a) - 2 * q (M a * R a) := by
    have hsym : q (R a * M a) = q (M a * R a) := by
      simp only [q]
      rw [← Ψ.qform_star, ← map_star, star_mul, hM.star_eq, hRsa]
    have hD : star (diagonal fun _ : T => M a) = diagonal fun _ => M a := by
      rw [star_eq_conjTranspose, diagonal_conjTranspose, Pi.star_def]
      simp only [hM.star_eq]
    rw [BipartiteModel.stateSqNorm_eq, qform_πA_expandA, star_sub, hD, hP.star_eq, sub_mul,
      mul_sub, mul_sub, hP.idem]
    have e1 : ((diagonal fun _ : T => M a) * (diagonal fun _ : T => M a) : Matrix T T 𝒜) t₀ t₀ =
        M a := by
      rw [diagonal_mul_diagonal, diagonal_apply_eq, hM.idem]
    have e2 : ((diagonal fun _ : T => M a) * P a : Matrix T T 𝒜) t₀ t₀ = M a * R a := by
      rw [diagonal_mul, hk]
    have e3 : (P a * (diagonal fun _ : T => M a) : Matrix T T 𝒜) t₀ t₀ = R a * M a := by
      rw [mul_diagonal, hk]
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, e1, e2, e3, hk]
    show q (M a - M a * R a - (R a * M a - R a)) = _
    rw [hq_sub, hq_sub, hq_sub, hsym]
    ring
  have hsum : (∑ a, (Ψ.expandA t₀).stateSqNorm ((diagonal fun _ => M a) - P a)) =
      2 * ∑ a, q (M a * (M a - R a)) := by
    simp_rw [hexp, mul_sub, hM.idem, hq_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← hq_sum, ← hq_sum, hM.sum_eq_one, hsumR]
    ring
  have hmass : (∑ a, Ψ.snorm (Ψ.πA (M a)) ^ 2) = 1 := by
    simp_rw [Ψ.snorm_sq_eq_qform, ← map_star, ← map_mul, hM.star_eq, hM.idem]
    rw [← Ψ.qform_sum, ← map_sum, hM.sum_eq_one, map_one, Ψ.qform_one hΨ]
  have hcs := abs_sum_qform_mul_le Ψ.toStateModel univ
    (fun a => Ψ.πA (M a)) (fun a => Ψ.πA (M a - R a))
    (fun a => by rw [← map_star, hM.star_eq])
  rw [hmass, Real.sqrt_one, one_mul] at hcs
  simp only [← map_mul] at hcs
  have hδ : (∑ a, Ψ.snorm (Ψ.πA (M a - R a)) ^ 2) ≤ δ := hd
  rw [hsum]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hcs.trans (Real.sqrt_le_sqrt hδ))) (by norm_num)

end Distance

section Conditional

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
  {I Y A T : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]

/-- The joint operator: the prefix projector of the register times the dilated residual
operator, with the fresh ancilla outermost, as the one-sided extension carries it. -/
def conditionalDilationOp (Z : Y → Matrix I I ℂ) (P : Y → A → Matrix T T 𝒜) (p : Y × A) :
    Matrix T T (Matrix I I 𝒜) :=
  (P p.1 p.2).map fun x => smulKron x (Z p.1)

/-- Conditional projective residual measurements keep the joint measurement
projective while leaving every prefix projector untouched. -/
theorem conditionalDilationOp_isPVM (Z : Y → Matrix I I ℂ) (hZ : IsPVM Z)
    (P : Y → A → Matrix T T 𝒜) (hP : ∀ y, IsPVMIn (P y)) :
    IsPVMIn (conditionalDilationOp Z P) := by
  have hmul (y : Y) (X X' : Matrix T T 𝒜) :
      (X * X').map (fun x => smulKron x (Z y)) =
        X.map (fun x => smulKron x (Z y)) * X'.map (fun x => smulKron x (Z y)) := by
    ext t t'
    simp only [map_apply, Matrix.mul_apply, smulKron_mul, hZ.idem, ← smulKron_sum_left]
  have hmul' {y y' : Y} (hy : y ≠ y') (X X' : Matrix T T 𝒜) :
      X.map (fun x => smulKron x (Z y)) * X'.map (fun x => smulKron x (Z y')) = 0 := by
    ext t t'
    simp only [map_apply, Matrix.mul_apply, smulKron_mul, hZ.toIn.orthogonal hy,
      smulKron_zero_right, Finset.sum_const_zero, Matrix.zero_apply]
  refine ⟨fun p => ?_, fun p => ?_, ?_, fun {p p'} hpp' => ?_⟩
  · have hf (x : 𝒜) : smulKron (star x) (Z p.1) = star (smulKron x (Z p.1)) := by
      rw [star_smulKron, ← star_eq_conjTranspose, hZ.toIn.star_eq]
    show star ((P p.1 p.2).map fun x => smulKron x (Z p.1)) =
      (P p.1 p.2).map fun x => smulKron x (Z p.1)
    rw [star_eq_conjTranspose, ← conjTranspose_map (fun x => smulKron x (Z p.1)) hf,
      ← star_eq_conjTranspose,
      (hP p.1).star_eq]
  · rw [conditionalDilationOp, ← hmul, (hP p.1).idem]
  · rw [Fintype.sum_prod_type]
    have h1 (y : Y) : ∑ a, conditionalDilationOp Z P (y, a) =
        (1 : Matrix T T 𝒜).map fun x => smulKron x (Z y) := by
      rw [← (hP y).sum_eq_one]
      ext t t' : 2
      simp only [conditionalDilationOp, Matrix.sum_apply, map_apply, smulKron_sum_left]
    simp_rw [h1]
    ext t t' : 2
    rw [Matrix.sum_apply]
    simp only [map_apply]
    by_cases h : t = t'
    · subst h
      simp only [one_apply_eq]
      rw [← smulKron_sum_right, hZ.sum_eq_one, smulKron_one_one]
    · simp only [one_apply_ne h, smulKron_zero_left, Finset.sum_const_zero]
  · by_cases hy : p.1 = p'.1
    · have ha : p.2 ≠ p'.2 := fun ha => hpp' (Prod.ext hy ha)
      rw [conditionalDilationOp, conditionalDilationOp, ← hy, ← hmul, (hP p.1).orthogonal ha]
      ext t t'
      simp only [map_apply, Matrix.zero_apply, smulKron_zero_left]
    · exact hmul' hy _ _

/-- The full conditional dilation compresses to the desired prefix times residual POVM, using the
same fixed vector for every prefix and outcome. -/
theorem conditionalDilationOp_compress (t₀ : T) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix T T 𝒜) (R : Y → A → 𝒜) (hk : ∀ y a, P y a t₀ t₀ = R y a)
    (p : Y × A) : conditionalDilationOp Z P p t₀ t₀ = smulKron (R p.1 p.2) (Z p.1) := by
  rw [conditionalDilationOp, map_apply, hk]

variable {𝒞 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The conditional product form has exactly the original outcome
probabilities against every measurement on the other party. -/
theorem conditionalDilationOp_born (Ψ : BipartiteModel 𝒞 (Matrix I I 𝒜) ℬ) (t₀ : T)
    (Z : Y → Matrix I I ℂ) (P : Y → A → Matrix T T 𝒜) (R : Y → A → 𝒜)
    (hk : ∀ y a, P y a t₀ t₀ = R y a) (p : Y × A) (b : ℬ) :
    (Ψ.expandA t₀).bornProb (conditionalDilationOp Z P p) b =
      Ψ.bornProb (smulKron (R p.1 p.2) (Z p.1)) b := by
  rw [BipartiteModel.bornProb_expandA, conditionalDilationOp_compress t₀ Z P R hk]

variable {J : Type*} [Fintype J] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- **Common-ancilla conditional projectivization.** All residual POVMs in a
question/prefix family are dilated with one fixed ancilla state. The resulting
joint PVMs retain the displayed prefix projectors and are quantitatively close
to the old projective family on the one extended state. -/
theorem exists_conditional_projective_dilation
    (Ψ : BipartiteModel 𝒞 (Matrix I I 𝒜) ℬ) (hΨ : ‖Ψ.ψ‖ = 1) (a₀ : A)
    (D : J → ℝ) (hD0 : ∀ j, 0 ≤ D j) (hD1 : ∑ j, D j = 1)
    (Z : J → Y → Matrix I I ℂ) (hZ : ∀ j, IsPVM (Z j))
    (Q : J → Y → POVMIn A 𝒜)
    (M : J → Y × A → Matrix I I 𝒜) (hM : ∀ j, IsPVMIn (M j))
    {δ : ℝ} (hd : ∑ j, D j * ∑ p : Y × A,
      Ψ.stateSqNorm (M j p - smulKron ((Q j p.1).op p.2) (Z j p.1)) ≤ δ) :
    ∃ K : ℕ, ∃ P : J → Y → A → Matrix (DilationAncilla A K) (DilationAncilla A K) 𝒜,
      (∀ j y, IsPVMIn (P j y)) ∧
      (∀ j y a, P j y a (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) = (Q j y).op a) ∧
      (∀ j, IsPVMIn (conditionalDilationOp (Z j) (P j))) ∧
      (∀ j p, conditionalDilationOp (Z j) (P j) p (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) =
        smulKron ((Q j p.1).op p.2) (Z j p.1)) ∧
      (∑ j, D j * ∑ p : Y × A, (Ψ.expandA (Sum.inl (a₀, 0) : DilationAncilla A K)).stateSqNorm
        ((diagonal fun _ => M j p) - conditionalDilationOp (Z j) (P j) p)) ≤
          2 * Real.sqrt δ := by
  obtain ⟨K, P, hP, hk⟩ := exists_pvm_dilation (fun jy : J × Y => Q jy.1 jy.2) a₀
  let P' j y a := P (j, y) a
  have hP' j y : IsPVMIn (P' j y) := hP (j, y)
  have hjoint j := conditionalDilationOp_isPVM (Z j) (hZ j) (P' j) (hP' j)
  have hcompress j p := conditionalDilationOp_compress (Sum.inl (a₀, 0)) (Z j) (P' j)
    (fun y a => (Q j y).op a) (fun y a => hk (j, y) a) p
  refine ⟨K, P', hP', fun j y a => hk (j, y) a, hjoint, hcompress, ?_⟩
  let err j := ∑ p : Y × A, Ψ.stateSqNorm (M j p - smulKron ((Q j p.1).op p.2) (Z j p.1))
  have herr j : 0 ≤ err j := Finset.sum_nonneg fun _ _ => Ψ.stateSqNorm_nonneg _
  have hpoint j := dilated_pvm_distance Ψ hΨ (Sum.inl (a₀, 0) : DilationAncilla A K) (M j)
    (fun p => smulKron ((Q j p.1).op p.2) (Z j p.1)) (conditionalDilationOp (Z j) (P' j))
    (hM j) (hjoint j) (hcompress j) (δ := err j) le_rfl
  calc
    _ ≤ ∑ j, D j * (2 * Real.sqrt (err j)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (hD0 j)
    _ = 2 * ∑ j, D j * Real.sqrt (err j) := by
      simp only [mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum]
    _ ≤ 2 * Real.sqrt δ := mul_le_mul_of_nonneg_left
      ((sum_weighted_sqrt_le D err hD0 hD1 herr).trans (Real.sqrt_le_sqrt hd)) (by norm_num)

end Conditional

section Varying

variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq A]
  {I Y : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]
  {𝒞 𝒜 ℬ : J → Type*} [∀ j, Ring (𝒞 j)] [∀ j, StarRing (𝒞 j)] [∀ j, Algebra ℂ (𝒞 j)]
  [∀ j, Ring (𝒜 j)] [∀ j, StarRing (𝒜 j)] [∀ j, Algebra ℂ (𝒜 j)] [∀ j, StarModule ℂ (𝒜 j)]
  [∀ j, PartialOrder (𝒜 j)] [∀ j, StarOrderedRing (𝒜 j)] [∀ j, StarProper (𝒜 j)]
  [∀ j, Ring (ℬ j)] [∀ j, StarRing (ℬ j)] [∀ j, Algebra ℂ (ℬ j)]

/-- **Conditional projectivization with varying local registers.** The prefix,
residual and other-party carriers may all depend on the conditioned question, and so may the
models. Each question gets one fixed ancilla state, common to all its prefixes; its number of
Kraus terms depends on the question. -/
theorem exists_varying_conditional_projective_dilation
    (Ψ : (j : J) → BipartiteModel (𝒞 j) (Matrix (I j) (I j) (𝒜 j)) (ℬ j))
    (hΨ : ∀ j, ‖(Ψ j).ψ‖ = 1) (a₀ : A)
    (D : J → ℝ) (hD0 : ∀ j, 0 ≤ D j) (hD1 : ∑ j, D j = 1)
    (Z : (j : J) → Y j → Matrix (I j) (I j) ℂ) (hZ : ∀ j, IsPVM (Z j))
    (Q : (j : J) → Y j → POVMIn A (𝒜 j))
    (M : (j : J) → Y j × A → Matrix (I j) (I j) (𝒜 j)) (hM : ∀ j, IsPVMIn (M j))
    {δ : ℝ} (hd : ∑ j, D j * ∑ p : Y j × A,
      (Ψ j).stateSqNorm (M j p - smulKron ((Q j p.1).op p.2) (Z j p.1)) ≤ δ) :
    ∃ K : J → ℕ, ∃ P : (j : J) → Y j → A →
        Matrix (DilationAncilla A (K j)) (DilationAncilla A (K j)) (𝒜 j),
      (∀ j y, IsPVMIn (P j y)) ∧
      (∀ j y a, P j y a (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) = (Q j y).op a) ∧
      (∀ j, IsPVMIn (conditionalDilationOp (Z j) (P j))) ∧
      (∀ j p, conditionalDilationOp (Z j) (P j) p (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) =
        smulKron ((Q j p.1).op p.2) (Z j p.1)) ∧
      (∑ j, D j * ∑ p : Y j × A,
        ((Ψ j).expandA (Sum.inl (a₀, 0) : DilationAncilla A (K j))).stateSqNorm
          ((diagonal fun _ => M j p) - conditionalDilationOp (Z j) (P j) p)) ≤
        2 * Real.sqrt δ := by
  let err j := ∑ p : Y j × A,
    (Ψ j).stateSqNorm (M j p - smulKron ((Q j p.1).op p.2) (Z j p.1))
  have herr j : 0 ≤ err j := Finset.sum_nonneg fun _ _ => (Ψ j).stateSqNorm_nonneg _
  have hlocal j : ∃ K : ℕ, ∃ P : Y j → A →
      Matrix (DilationAncilla A K) (DilationAncilla A K) (𝒜 j),
      (∀ y, IsPVMIn (P y)) ∧
      (∀ y a, P y a (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) = (Q j y).op a) ∧
      IsPVMIn (conditionalDilationOp (Z j) P) ∧
      (∀ p, conditionalDilationOp (Z j) P p (Sum.inl (a₀, 0)) (Sum.inl (a₀, 0)) =
        smulKron ((Q j p.1).op p.2) (Z j p.1)) ∧
      (∑ p : Y j × A, ((Ψ j).expandA (Sum.inl (a₀, 0) : DilationAncilla A K)).stateSqNorm
        ((diagonal fun _ => M j p) - conditionalDilationOp (Z j) P p)) ≤
          2 * Real.sqrt (err j) := by
    obtain ⟨K, P, hp, hk, hjoint, hfull, hdist⟩ :=
      exists_conditional_projective_dilation (J := Unit) (Ψ j) (hΨ j) a₀
        (fun _ => 1) (fun _ => zero_le_one) (by simp)
        (fun _ => Z j) (fun _ => hZ j) (fun _ => Q j)
        (fun _ => M j) (fun _ => hM j) (δ := err j) (by simp [err])
    refine ⟨K, P (), hp (), hk (), hjoint (), hfull (), ?_⟩
    simpa only [Fintype.sum_unique, one_mul] using hdist
  choose K P hp hk hjoint hfull hdist using hlocal
  refine ⟨K, P, hp, hk, hjoint, hfull, ?_⟩
  calc
    _ ≤ ∑ j, D j * (2 * Real.sqrt (err j)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdist j) (hD0 j)
    _ = 2 * ∑ j, D j * Real.sqrt (err j) := by
      simp only [mul_left_comm (b := (2 : ℝ)), ← Finset.mul_sum]
    _ ≤ 2 * Real.sqrt δ := mul_le_mul_of_nonneg_left
      ((sum_weighted_sqrt_le D err hD0 hD1 herr).trans (Real.sqrt_le_sqrt hd)) (by norm_num)

end Varying

end MIPRE.Introspection

end

end
