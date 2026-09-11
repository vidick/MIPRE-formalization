/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/BlockArena.lean
-/
/-
# The block resolver arena (node 1.2.5, proof layer)

An exact finite construction of a `ResolverArena` inside the matrix
amplification `amplify M d` of `VN/Amplify.lean`, driven by the interface's
sums-of-squares positivity (D13): writing each refinement piece as
`F_i^a = ∑_k x_{i,a,k}* x_{i,a,k}`, the Alice column of `i` stacks the factors
`x_{i,a,k}` (rows indexed by `(i, a, k)`), the Bob row of `j` lays out the
adjoints of the factors of `G_j^b` (columns indexed by `(j, b, l)`), the
POVMs are the diagonal 0/1 projections onto the answer blocks (with the
fallback answer collecting every index outside the block, as in
04_resolver_corner.tex eqs alice-corner-povm/bob-corner-povm), and the branch
is `√d · ι(c_i (σ e₀₀) d_j)` (eq joint-rectangular-branch with the
`t_Q = d` normalization of eq resolver-corner-normalization-unitary). The two
exact pairing identities (eqs joint-branch-norm, joint-branch-answer-weight)
are the trace computation eq branch-norm-computation /
branch-weight-computation with the columns' square and refinement identities
(eqs resolver-square-identities, resolver-refinement-identities) now
tautological in the factor indices. Nothing here is a manuscript statement;
the manuscript's resolver-integral columns (needed for the entropy budget of
node 1.2.6) are not used.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.ArenaDef
import MIPRE.Background.Repetition.CommutingRepetition.VN.Amplify

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

namespace BlockArena

variable {M : StdTracialAlgebra.{0}}
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
variable (kA : I → A → ℕ) (kB : J → B → ℕ)

/-- Alice's factor rows `(i, a, k)`. -/
abbrev RowA : Type := Σ i : I, Σ a : A, Fin (kA i a)

/-- Bob's factor columns `(j, b, l)`. -/
abbrev ColB : Type := Σ j : J, Σ b : B, Fin (kB j b)

/-- The block index set: the source `e₀`, Alice's rows, Bob's columns. -/
abbrev Idx : Type := Unit ⊕ RowA kA ⊕ ColB kB

variable (xA : RowA kA → M.A) (yB : ColB kB → M.A)

/-- The Alice column of `i` as a vector: the factors of `i`, zero elsewhere. -/
def colVec (i : I) : Idx kA kB → M.A
  | Sum.inr (Sum.inl r) => if r.1 = i then xA r else 0
  | _ => 0

/-- The Bob row of `j` as a vector: the adjoint factors of `j`, zero elsewhere. -/
def rowVec (j : J) : Idx kA kB → M.A
  | Sum.inr (Sum.inr s) => if s.1 = j then star (yB s) else 0
  | _ => 0

/-- The answer label of an index for Alice's POVM at `i`: the factor's answer
on the rows of `i`, the fallback `a₀` everywhere else. -/
def labelA (a₀ : A) (i : I) : Idx kA kB → A
  | Sum.inr (Sum.inl r) => if r.1 = i then r.2.1 else a₀
  | _ => a₀

def labelB (b₀ : B) (j : J) : Idx kA kB → B
  | Sum.inr (Sum.inr s) => if s.1 = j then s.2.1 else b₀
  | _ => b₀

/-- A rank-one block `a σ bᵀ`. -/
def rankOne (a b : Idx kA kB → M.A) (σ : M.A) : Matrix (Idx kA kB) (Idx kA kB) M.A :=
  Matrix.of fun p q => a p * σ * b q

/-- The rank-one block `c_i (σ e₀₀) d_j`: entries `x_r σ y_s*`. -/
def branchMat (σ : M.A) (i : I) (j : J) : Matrix (Idx kA kB) (Idx kA kB) M.A :=
  rankOne kA kB (colVec kA kB xA i) (rowVec kA kB yB j) σ

/-- A 0/1 diagonal projection. -/
def proj (P : Idx kA kB → Prop) [DecidablePred P] : Matrix (Idx kA kB) (Idx kA kB) M.A :=
  Matrix.diagonal fun p => if P p then (1 : M.A) else 0

/-! ### The trace computation -/

/-- The core computation (eqs branch-norm-computation,
branch-weight-computation): the diagonal trace of
`X* (P X P')` for the rank-one block `X = a σ bᵀ`. -/
theorem sum_diag_trace (σ : M.A) (a b : Idx kA kB → M.A) (PA PB : Idx kA kB → Prop)
    [DecidablePred PA] [DecidablePred PB] :
    (∑ q : Idx kA kB, M.τ ((star (rankOne kA kB a b σ) *
        (proj kA kB PA * rankOne kA kB a b σ * proj kA kB PB) :
          Matrix (Idx kA kB) (Idx kA kB) M.A) q q))
      = M.τ (star σ * ((∑ p : Idx kA kB, if PA p then star (a p) * a p else 0) * σ *
          ∑ q : Idx kA kB, if PB q then b q * star (b q) else 0)) := by
  have hentry : ∀ q : Idx kA kB,
      (star (rankOne kA kB a b σ) *
        (proj kA kB PA * rankOne kA kB a b σ * proj kA kB PB) :
          Matrix (Idx kA kB) (Idx kA kB) M.A) q q
      = ∑ p : Idx kA kB, if PA p ∧ PB q then
          star (b q) * (star σ * (star (a p) * (a p * (σ * b q)))) else 0 := by
    intro q
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold proj rankOne
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]
    simp only [Matrix.of_apply]
    by_cases hP : PA p
    · by_cases hQ : PB q
      · simp only [if_pos hP, if_pos hQ, if_pos (And.intro hP hQ), one_mul, mul_one, star_mul,
          mul_assoc]
      · simp only [if_pos hP, if_neg hQ, if_neg (fun h : _ ∧ _ => hQ h.2), mul_zero]
    · simp only [if_neg hP, if_neg (fun h : _ ∧ _ => hP h.1), zero_mul, mul_zero]
  simp only [hentry]
  have hterm : ∀ p q : Idx kA kB,
      M.τ (if PA p ∧ PB q then
        star (b q) * (star σ * (star (a p) * (a p * (σ * b q)))) else 0)
      = M.τ (star σ * ((if PA p then star (a p) * a p else 0) * σ *
          (if PB q then b q * star (b q) else 0))) := by
    intro p q
    by_cases hP : PA p
    · by_cases hQ : PB q
      · simp only [if_pos hP, if_pos hQ, if_pos (And.intro hP hQ)]
        rw [M.τ_mul_comm]
        congr 1
        simp only [mul_assoc]
      · simp only [if_pos hP, if_neg hQ, if_neg (fun h : _ ∧ _ => hQ h.2), mul_zero, map_zero]
    · simp only [if_neg hP, if_neg (fun h : _ ∧ _ => hP h.1), zero_mul, mul_zero, map_zero]
  simp only [map_sum, hterm]
  rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, map_sum]

/-! ### The block sums -/

variable (F : I → A → M.A) (G : J → B → M.A)

/-- The Alice column square, restricted to an answer predicate on the block
labels. -/
theorem sum_colVec (a₀ : A) (i : I) (P : A → Prop) [DecidablePred P]
    (hxA : ∀ (i : I) (a : A), F i a = ∑ k : Fin (kA i a), star (xA ⟨i, a, k⟩) * xA ⟨i, a, k⟩) :
    (∑ p : Idx kA kB, if P (labelA kA kB a₀ i p) then
        star (colVec kA kB xA i p) * colVec kA kB xA i p else 0)
      = ∑ a : A, if P a then F i a else 0 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h0 : (∑ _u : Unit, if P (labelA kA kB a₀ i (Sum.inl _u)) then
      star (colVec kA kB xA i (Sum.inl _u)) * colVec kA kB xA i (Sum.inl _u) else 0) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    simp [colVec]
  have hB : (∑ s : ColB kB, if P (labelA kA kB a₀ i (Sum.inr (Sum.inr s))) then
      star (colVec kA kB xA i (Sum.inr (Sum.inr s))) * colVec kA kB xA i (Sum.inr (Sum.inr s))
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [colVec]
  rw [h0, hB, zero_add, add_zero, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [labelA, colVec, if_true]
    split_ifs with hPa
    · rw [hxA i a]
    · exact Finset.sum_eq_zero fun k _ => rfl
  · intro i' _ hne
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [labelA, colVec, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The Bob row square, restricted to an answer predicate. -/
theorem sum_rowVec (b₀ : B) (j : J) (P : B → Prop) [DecidablePred P]
    (hyB : ∀ (j : J) (b : B), G j b = ∑ l : Fin (kB j b), star (yB ⟨j, b, l⟩) * yB ⟨j, b, l⟩) :
    (∑ q : Idx kA kB, if P (labelB kA kB b₀ j q) then
        rowVec kA kB yB j q * star (rowVec kA kB yB j q) else 0)
      = ∑ b : B, if P b then G j b else 0 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h0 : (∑ _u : Unit, if P (labelB kA kB b₀ j (Sum.inl _u)) then
      rowVec kA kB yB j (Sum.inl _u) * star (rowVec kA kB yB j (Sum.inl _u)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    simp [rowVec]
  have hA : (∑ r : RowA kA, if P (labelB kA kB b₀ j (Sum.inr (Sum.inl r))) then
      rowVec kA kB yB j (Sum.inr (Sum.inl r)) * star (rowVec kA kB yB j (Sum.inr (Sum.inl r)))
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    simp [rowVec]
  rw [h0, hA, zero_add, zero_add, Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [labelB, rowVec, if_true, star_star]
    split_ifs with hPb
    · rw [hyB j b]
    · exact Finset.sum_eq_zero fun l _ => rfl
  · intro j' _ hne
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [labelB, rowVec, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The 0/1 projections onto the labels of `i` form a partition of unity. -/
theorem sum_proj_labelA (a₀ : A) (i : I) :
    (∑ a : A, proj kA kB (fun p => labelA kA kB a₀ i p = a)) = (1 : Matrix (Idx kA kB) (Idx kA kB) M.A) := by
  ext p q
  rw [Matrix.sum_apply]
  unfold proj
  simp only [Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, Matrix.one_apply_eq]
    rw [Finset.sum_ite_eq]
    simp
  · simp [hpq, Matrix.one_apply_ne hpq]

theorem sum_proj_labelB (b₀ : B) (j : J) :
    (∑ b : B, proj kA kB (fun q => labelB kA kB b₀ j q = b)) = (1 : Matrix (Idx kA kB) (Idx kA kB) M.A) := by
  ext p q
  rw [Matrix.sum_apply]
  unfold proj
  simp only [Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, Matrix.one_apply_eq]
    rw [Finset.sum_ite_eq]
    simp
  · simp [hpq, Matrix.one_apply_ne hpq]

/-- A 0/1 projection is a hermitian square of itself. -/
theorem proj_star_mul_self (P : Idx kA kB → Prop) [DecidablePred P] :
    star (proj kA kB (M := M) P) * proj kA kB P = proj kA kB P := by
  unfold proj
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases hp : P p <;> simp [hp]

theorem proj_true : proj kA kB (M := M) (fun _ => True) = 1 := by
  simp [proj, Matrix.diagonal_one]

/-! ### The arena -/

/-- The amplification dimension. -/
abbrev dim : ℕ := Fintype.card (Idx kA kB)

instance : NeZero (dim kA kB) := ⟨Fintype.card_ne_zero⟩

/-- The block algebra `N = M_d(M)`. -/
noncomputable abbrev N : StdTracialAlgebra.{0} := StdTracialAlgebra.amplify M (dim kA kB)

/-- The reindexing of block matrices into `N`. -/
noncomputable def emb (X : Matrix (Idx kA kB) (Idx kA kB) M.A) : (N (M := M) kA kB).A :=
  Matrix.reindex (Fintype.equivFin (Idx kA kB)) (Fintype.equivFin (Idx kA kB)) X

theorem emb_mul (X Y : Matrix (Idx kA kB) (Idx kA kB) M.A) :
    emb kA kB (X * Y) = emb kA kB X * emb kA kB Y := by
  unfold emb
  exact (Matrix.reindexAlgEquiv ℂ M.A (Fintype.equivFin (Idx kA kB))).map_mul X Y

theorem emb_star (X : Matrix (Idx kA kB) (Idx kA kB) M.A) :
    emb kA kB (star X) = star (emb kA kB X) :=
  (Matrix.conjTranspose_reindex _ _ X).symm

theorem emb_one : emb kA kB (M := M) 1 = 1 := by
  unfold emb
  show (Matrix.reindex (Fintype.equivFin (Idx kA kB)) (Fintype.equivFin (Idx kA kB))
    (1 : Matrix (Idx kA kB) (Idx kA kB) M.A) : Matrix (Fin (dim kA kB)) (Fin (dim kA kB)) M.A) = 1
  ext p q
  simp [Matrix.reindex_apply, Matrix.one_apply]

theorem emb_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Idx kA kB) (Idx kA kB) M.A) :
    emb kA kB (∑ x ∈ s, f x) = ∑ x ∈ s, emb kA kB (f x) := by
  unfold emb
  exact map_sum (Matrix.reindexAlgEquiv ℂ M.A (Fintype.equivFin (Idx kA kB))) f s

/-- The trace of `N` on an embedded block matrix: `d⁻¹ ∑_p τ(X p p)`. -/
theorem τ_emb (X : Matrix (Idx kA kB) (Idx kA kB) M.A) :
    (N (M := M) kA kB).τ (emb kA kB X)
      = ((dim kA kB : ℂ))⁻¹ * ∑ p : Idx kA kB, M.τ (X p p) := by
  unfold emb
  show StdTracialAlgebra.ampτ M (dim kA kB)
    (Matrix.reindex (Fintype.equivFin (Idx kA kB)) (Fintype.equivFin (Idx kA kB)) X) = _
  rw [StdTracialAlgebra.ampτ_apply]
  congr 1
  rw [← Equiv.sum_comp (Fintype.equivFin (Idx kA kB))]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Matrix.reindex_apply]

variable (a₀ : A) (b₀ : B)

/-- The block arena. -/
noncomputable def arena
    (hxA : ∀ (i : I) (a : A), F i a = ∑ k : Fin (kA i a), star (xA ⟨i, a, k⟩) * xA ⟨i, a, k⟩)
    (hyB : ∀ (j : J) (b : B), G j b = ∑ l : Fin (kB j b), star (yB ⟨j, b, l⟩) * yB ⟨j, b, l⟩) :
    ResolverArena M F G where
  N := N kA kB
  Ameas i a := emb kA kB (proj kA kB fun p => labelA kA kB a₀ i p = a)
  Bmeas j b := emb kA kB (proj kA kB fun q => labelB kA kB b₀ j q = b)
  Ameas_pos i a := by
    refine ⟨1, fun _ => emb kA kB (proj kA kB fun p => labelA kA kB a₀ i p = a), ?_⟩
    rw [Fin.sum_univ_one]
    exact (congrArg (emb kA kB) (proj_star_mul_self kA kB _).symm).trans
      ((emb_mul kA kB _ _).trans (by rw [emb_star]))
  Bmeas_pos j b := by
    refine ⟨1, fun _ => emb kA kB (proj kA kB fun q => labelB kA kB b₀ j q = b), ?_⟩
    rw [Fin.sum_univ_one]
    exact (congrArg (emb kA kB) (proj_star_mul_self kA kB _).symm).trans
      ((emb_mul kA kB _ _).trans (by rw [emb_star]))
  Ameas_sum i :=
    (emb_sum kA kB Finset.univ _).symm.trans (by rw [sum_proj_labelA, emb_one])
  Bmeas_sum j :=
    (emb_sum kA kB Finset.univ _).symm.trans (by rw [sum_proj_labelB, emb_one])
  branch σ i j :=
    ((Real.sqrt (dim kA kB) : ℝ) : ℂ) • (N kA kB).ι (emb kA kB (branchMat kA kB xA yB σ i j))
  branch_norm σ i j := by
    rw [inner_smul_left, inner_smul_right, StdTracialAlgebra.ι_inner, ← emb_star, ← emb_mul,
      τ_emb]
    have hX : star (branchMat kA kB xA yB σ i j) * branchMat kA kB xA yB σ i j
        = star (branchMat kA kB xA yB σ i j) *
          (proj kA kB (fun _ => True) * branchMat kA kB xA yB σ i j *
            proj kA kB (fun _ => True)) := by
      rw [proj_true, Matrix.one_mul, Matrix.mul_one]
    rw [hX]
    unfold branchMat
    rw [sum_diag_trace]
    have hA := sum_colVec kA kB xA F a₀ i (fun _ => True) hxA
    have hB := sum_rowVec kA kB yB G b₀ j (fun _ => True) hyB
    simp only [if_true] at hA hB ⊢
    rw [hA, hB]
    have hd : (0 : ℝ) < dim kA kB := by exact_mod_cast Fintype.card_pos
    rw [Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hd.le, ← mul_assoc]
    rw [show ((dim kA kB : ℝ) : ℂ) * ((dim kA kB : ℂ))⁻¹ = 1 from by
      rw [Complex.ofReal_natCast]
      exact mul_inv_cancel₀ (by exact_mod_cast hd.ne')]
    rw [one_mul]
  branch_answer σ i j a b := by
    rw [inner_smul_left, map_smul, map_smul, inner_smul_right, StdTracialAlgebra.inner_L_R,
      ← emb_star, ← emb_mul, ← emb_mul, ← emb_mul, τ_emb]
    unfold branchMat
    rw [sum_diag_trace]
    have hA := sum_colVec kA kB xA F a₀ i (fun a' => a' = a) hxA
    have hB := sum_rowVec kA kB yB G b₀ j (fun b' => b' = b) hyB
    rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ _)] at hA
    rw [Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ _)] at hB
    rw [hA, hB]
    have hd : (0 : ℝ) < dim kA kB := by exact_mod_cast Fintype.card_pos
    rw [Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hd.le, ← mul_assoc]
    rw [show ((dim kA kB : ℝ) : ℂ) * ((dim kA kB : ℂ))⁻¹ = 1 from by
      rw [Complex.ofReal_natCast]
      exact mul_inv_cancel₀ (by exact_mod_cast hd.ne')]
    rw [one_mul]

end BlockArena

end CommutingRepetition
