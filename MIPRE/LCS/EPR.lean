/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Strategy.Equivalence
import MIPRE.LCS.WinningCondition
import MIPRE.LCS.MatrixSOS

/-!
# EPR Extraction for LCS Relation Terms

This module contains the EPR/vectorization algebra and SOS extraction lemmas
used to turn perfect local LCS play into local matrix identities.  The EPR
vector is intentionally unnormalized:
$$
  \Omega = \sum_a e_a \otimes e_a,
$$
since the arguments only use annihilation and injectivity.

The basic EPR identities are:

* `kronecker_mulVec_epr`, computing the action of a two-sided Kronecker product:
  $$
    ((M \otimes N)\Omega)_{a,b} = \sum_k M_{a,k}N_{b,k}.
  $$
* `kronecker_mulVec_epr_eq_zero_iff`, converting EPR annihilation into the local
  matrix equation
  $$
    (M \otimes N)\Omega = 0 \quad\Longleftrightarrow\quad MN^T = 0.
  $$
* `bipartiteAliceLift_mulVec_epr_eq_zero_iff`,
  `one_sub_kronecker_mulVec_epr_eq_zero_iff`,
  `bipartiteAliceLift_one_sub_smul_mulVec_epr_eq_zero_iff`, and
  `one_sub_smul_kronecker_mulVec_epr_eq_zero_iff`, which are the specialized
  injectivity forms used for bipartite Alice/Bob lifts.

The LCS-specific part defines the three SOS relation terms
`sosConsistencyTerm`, `sosRowTerm`, and `sosProductTerm`, together with their
square-sum `sosSquareSum`.  The extraction pipeline is:

* `local_loss_kills_epr_sos_sum`: a local loss operator killing $\Omega$ rewrites
  to the scaled SOS square-sum killing $\Omega$.
* `sos_sum_kills_epr_implies_terms_kill_epr`: positivity for self-adjoint
  squares gives the three individual relation annihilations.
* `consistency_of_epr_annihilates`, `row_relation_of_epr_annihilates`, and
  `product_relation_of_epr_annihilates`: the EPR identities remove $\Omega$ and
  produce the corresponding local matrix equations.
* `local_matrix_identities_of_local_loss_annihilate_epr`: the final bundled
  theorem, extracting all three local matrix identities directly from local-loss
  annihilation on $\Omega$.
-/

namespace MIPRE.LCS


open Matrix
open scoped Kronecker

section EPRVector
/-!
## The Unnormalized EPR Vector

The vector `eprVec n` is the coordinate function of
$\Omega = \sum_{a : n} e_a \otimes e_a$.
-/

/-- The unnormalized EPR vector $\Omega = \sum_a e_a \otimes e_a$, as a
function on pairs. -/
noncomputable def eprVec
    (n : Type*) [Fintype n] [DecidableEq n] : (n × n) → ℂ :=
  fun ab ↦ if ab.1 = ab.2 then 1 else 0

/-- Summing a function over the diagonal of `n × n` is the same as summing it
over `n`.

This private helper is the finite-support calculation behind the formula
$$
  (M \otimes N)\Omega = \sum_k M_{\_,k} N_{\_,k}.
$$
-/
private lemma sum_pair_diag
    {n : Type*} [Fintype n] [DecidableEq n] (f : n → n → ℂ) :
    (∑ x : n × n, if x.1 = x.2 then f x.1 x.2 else 0) = ∑ k : n, f k k := by
  classical
  rw [← Finset.sum_filter]
  have hdiag :
      (Finset.univ.filter fun x : n × n ↦ x.1 = x.2) =
        (Finset.univ : Finset n).diag := by
    ext x
    simp [Finset.mem_diag]
  rw [hdiag]
  simp only [
    (Finset.sum_diag (s := Finset.univ) (f := fun x : n × n ↦ f x.1 x.2))
  ]

end EPRVector

section KroneckerEPR
/-!
## Kronecker Products Acting on EPR

This section proves the two core matrix identities.  The first computes the
action of a two-sided Kronecker product on $\Omega$.  The second converts
annihilation of $\Omega$ into the local matrix equation $M N^T = 0$.
-/

/-- Action of a two-sided Kronecker product on the unnormalized EPR vector:
$$
  ((M \otimes N)\Omega)_{a,b} =
    \sum_k M_{a,k} N_{b,k}.
$$
-/
lemma kronecker_mulVec_epr
    (n : Type*) [Fintype n] [DecidableEq n]
    (M N : Matrix n n ℂ) :
    (M ⊗ₖ N) *ᵥ (eprVec n)
      =
    fun ab ↦ ∑ k : n, M ab.1 k * N ab.2 k := by
  ext ab
  simpa [Matrix.mulVec, dotProduct, eprVec, mul_assoc] using
    sum_pair_diag (n := n) (fun k l ↦ M ab.1 k * N ab.2 l)

/-- The EPR vector turns two-sided annihilation into a local matrix identity:
$$
  (M \otimes N)\Omega = 0 \quad\Longleftrightarrow\quad M N^T = 0.
$$
-/
lemma kronecker_mulVec_epr_eq_zero_iff
    (n : Type*) [Fintype n] [DecidableEq n]
    (M N : Matrix n n ℂ) :
    (M ⊗ₖ N) *ᵥ (eprVec n) = 0 ↔
      M * Nᵀ = 0 := by
  constructor
  · intro h
    ext a b
    have h_ab := congrFun h (a, b)
    simpa [kronecker_mulVec_epr, Matrix.mul_apply, Matrix.transpose_apply] using h_ab
  · intro h
    ext ab
    have h_ab := congrFun (congrFun h ab.1) ab.2
    simpa [kronecker_mulVec_epr, Matrix.mul_apply, Matrix.transpose_apply] using h_ab

/-- A matrix acting on Alice's side annihilates EPR iff the matrix is zero:
$$
  (M \otimes I)\Omega = 0 \quad\Longleftrightarrow\quad M = 0.
$$
-/
lemma bipartiteAliceLift_mulVec_epr_eq_zero_iff
    (n : Type*) [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) :
    (bipartiteAliceLift M) *ᵥ (eprVec n) = 0 ↔ M = 0 := by
  rw [bipartiteAliceLift, kronecker_mulVec_epr_eq_zero_iff]
  simp

/-- The relation term $1 - M \otimes N$ annihilates EPR precisely when
$$
  M N^T = I.
$$
-/
lemma one_sub_kronecker_mulVec_epr_eq_zero_iff
    (n : Type*) [Fintype n] [DecidableEq n]
    (M N : Matrix n n ℂ) :
    (1 - M ⊗ₖ N) *ᵥ (eprVec n) = 0 ↔
      M * Nᵀ = 1 := by
  constructor
  · intro h
    ext a b
    have h_ab := congrFun h (a, b)
    have h_eq :
        eprVec n (a, b) - (∑ x, M a x * N b x) = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec, kronecker_mulVec_epr] using h_ab
    have h_sum : (∑ x, M a x * N b x) = eprVec n (a, b) :=
      (sub_eq_zero.mp h_eq).symm
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, eprVec] using h_sum
  · intro h
    ext ab
    have h_ab := congrFun (congrFun h ab.1) ab.2
    have h_eq :
        eprVec n ab - (∑ x, M ab.1 x * N ab.2 x) = 0 := by
      apply sub_eq_zero.mpr
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, eprVec] using h_ab.symm
    simpa [Matrix.sub_mulVec, Matrix.one_mulVec, kronecker_mulVec_epr] using h_eq

end KroneckerEPR

section BipartiteLiftAlgebra
/-!
## Algebra of Bipartite Lifts

The observable strategy files define Alice and Bob lifts as $A \otimes I$ and
$I \otimes B$.  This section records the small collection of rewrite lemmas
needed to turn global bipartite relation terms into local matrix equations.
-/

/-- Multiplying Bob's lift by Alice's lift gives the two-sided Kronecker product:
$$
  (I \otimes B)(A \otimes I) = A \otimes B.
$$
-/
lemma bipartiteBobLift_mul_bipartiteAliceLift
    (n : Type*) [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    bipartiteBobLift B * bipartiteAliceLift A = A ⊗ₖ B := by
  change ((1 : Matrix n n ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix n n ℂ)) = A ⊗ₖ B
  rw [← mul_kronecker_mul, one_mul, mul_one]

/-- Alice lifts preserve multiplication:
$$
  (A \otimes I)(B \otimes I) = (AB) \otimes I.
$$
-/
lemma bipartiteAliceLift_mul
    (n : Type*) [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    bipartiteAliceLift A * bipartiteAliceLift B = bipartiteAliceLift (A * B) := by
  change (A ⊗ₖ (1 : Matrix n n ℂ)) * (B ⊗ₖ (1 : Matrix n n ℂ)) =
    (A * B) ⊗ₖ (1 : Matrix n n ℂ)
  rw [← mul_kronecker_mul, mul_one]

/-- Multiplying Alice's lift by Bob's lift gives the two-sided Kronecker product:
$$
  (A \otimes I)(I \otimes B) = A \otimes B.
$$
-/
lemma bipartiteAliceLift_mul_bipartiteBobLift
    (n : Type*) [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    bipartiteAliceLift A * bipartiteBobLift B = A ⊗ₖ B := by
  change (A ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B) = A ⊗ₖ B
  rw [← mul_kronecker_mul, mul_one, one_mul]

/-- Alice lifting commutes with the affine expression $1 - cM$:
$$
  (1 - cM) \otimes I = 1 - c (M \otimes I).
$$
-/
lemma bipartiteAliceLift_one_sub_smul
    (n : Type*) [Fintype n] [DecidableEq n]
    (c : ℂ) (M : Matrix n n ℂ) :
    bipartiteAliceLift (1 - c • M) =
      1 - c • bipartiteAliceLift M := by
  ext ab cd
  rcases ab with ⟨a₁, a₂⟩
  rcases cd with ⟨d₁, d₂⟩
  by_cases h₁ : a₁ = d₁ <;> by_cases h₂ : a₂ = d₂ <;>
    simp [bipartiteAliceLift, h₁, h₂, Prod.ext_iff]

/-- EPR injectivity for an affine Alice-side relation:
$$
  (1 - c(M \otimes I))\Omega = 0
    \quad\Longleftrightarrow\quad
  1 - cM = 0.
$$
-/
lemma bipartiteAliceLift_one_sub_smul_mulVec_epr_eq_zero_iff
    (n : Type*) [Fintype n] [DecidableEq n]
    (c : ℂ) (M : Matrix n n ℂ) :
    (1 - c • bipartiteAliceLift M) *ᵥ (eprVec n) = 0 ↔
      1 - c • M = 0 := by
  rw [← bipartiteAliceLift_one_sub_smul]
  exact bipartiteAliceLift_mulVec_epr_eq_zero_iff n (1 - c • M)

/-- EPR injectivity for a scalar multiple of a two-sided Kronecker product:
$$
  (1 - c(M \otimes N))\Omega = 0
    \quad\Longleftrightarrow\quad
  c(MN^T) = I.
$$
-/
lemma one_sub_smul_kronecker_mulVec_epr_eq_zero_iff
    (n : Type*) [Fintype n] [DecidableEq n]
    (c : ℂ) (M N : Matrix n n ℂ) :
    (1 - c • (M ⊗ₖ N)) *ᵥ (eprVec n) = 0 ↔
      c • (M * Nᵀ) = 1 := by
  rw [← Matrix.smul_kronecker c M N, one_sub_kronecker_mulVec_epr_eq_zero_iff]
  simp

end BipartiteLiftAlgebra


section LCSSOSTerms
/-!
## SOS Relation Terms and Main EPR Pipeline

This section packages the three relation terms from `localLossOperator_sos`, their
square-sum, and the three extraction stages: loss kills `Ω`, the SOS terms kill
`Ω`, and the local matrix identities follow.
-/

variable {G : Layout}
variable (game : Game G)
variable (n : Type*) [Fintype n] [DecidableEq n]
variable (strat : ProjectorStrategy (Matrix (n × n) (n × n) ℂ) G)

local notation "Ω" => eprVec n
local notation "A[" i ", " j "]" => ProjectorStrategy.aliceObs strat i j
local notation "B[" j "]" => ProjectorStrategy.bobObs strat j
local notation "b[" i "]" => game.b i

/-- Paper-style notation for `ProjectorStrategy.aliceRowProd strat i`. -/
local notation "∏ₐ[" i "]" => ProjectorStrategy.aliceRowProd strat i

/-- The consistency SOS relation term. -/
noncomputable def sosConsistencyTerm
    (i : Fin G.r) (j : G.V i) : Matrix (n × n) (n × n) ℂ :=
  1 - B[↑j] * A[i, j]

/-- The row-product SOS relation term. -/
noncomputable def sosRowTerm
    (i : Fin G.r) : Matrix (n × n) (n × n) ℂ :=
  1 - (-1 : ℂ) ^ b[i].val • ∏ₐ[i]

/-- The product SOS relation term. -/
noncomputable def sosProductTerm
    (i : Fin G.r) (j : G.V i) : Matrix (n × n) (n × n) ℂ :=
  1 - (-1 : ℂ) ^ b[i].val • (∏ₐ[i] * A[i, j] * B[↑j])

/-- The sum of squares appearing in the local-loss SOS decomposition. -/
noncomputable def sosSquareSum
    (i : Fin G.r) (j : G.V i) : Matrix (n × n) (n × n) ℂ :=
  (sosConsistencyTerm n strat i j) ^ 2 +
    (sosRowTerm game n strat i) ^ 2 +
    (sosProductTerm game n strat i j) ^ 2

section Stage1
/-!
### Stage 1: Local Loss ⇒ Scaled SOS Square-Sum
-/

/-- The part of the SOS pipeline that is purely a rewrite: if the local loss annihilates EPR,
then the SOS expression from `localLossOperator_sos` annihilates EPR.  Extracting each individual
square term from this sum requires a positivity/norm argument.

In symbols, this is the formal rewrite step
$$
  L_{ij}\Omega = 0
    \quad\Longrightarrow\quad
  \frac18\,(T_1^2 + T_2^2 + T_3^2)\Omega = 0,
$$
where the three $T_k$ are the SOS relation terms from `localLossOperator_sos`.
-/
lemma local_loss_kills_epr_sos_sum
    (i : Fin G.r) (j : G.V i)
    (hLoss :
      localLossOperator game strat i j *ᵥ Ω = 0) :
    ((1 / 8 : ℂ) • sosSquareSum game n strat i j) *ᵥ Ω = 0 := by
  simpa [localLossOperator_sos, sosSquareSum, sosConsistencyTerm, sosRowTerm,
    sosProductTerm] using hLoss

end Stage1

section Stage2
/-!
### Stage 2: Scaled SOS Square-Sum ⇒ Individual SOS-Term Annihilation
-/

/-- A noncommutative product of pairwise commuting self-adjoint matrices is self-adjoint:
if every factor satisfies $f_x^* = f_x$, then
$$
  \left(\prod_{x \in s} f_x\right)^* = \prod_{x \in s} f_x .
$$
This is the generic finite-product input used below to show that Alice's row product is
self-adjoint, which is needed before the SOS square-sum can be split into individual
annihilation relations.
-/
private lemma noncommProd_conjTranspose_eq_self
    {ι m : Type*} [Fintype m] [DecidableEq m]
    (s : Finset ι) (f : ι → Matrix m m ℂ)
    (comm : (s : Set ι).Pairwise fun x y ↦ Commute (f x) (f y))
    (hself : ∀ x ∈ s, (f x)ᴴ = f x) :
    (s.noncommProd f comm)ᴴ = s.noncommProd f comm := by
  classical
  induction s using Finset.cons_induction_on with
  | empty =>
      simp [Finset.noncommProd_empty]
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons]
      rw [Matrix.conjTranspose_mul]
      rw [hself a (Finset.mem_cons_self a s)]
      have ih' :
          (s.noncommProd f (comm.mono fun _ hx ↦ Finset.mem_cons.2 (.inr hx)))ᴴ =
            s.noncommProd f (comm.mono fun _ hx ↦ Finset.mem_cons.2 (.inr hx)) := by
        exact ih _ (fun x hx ↦ hself x (Finset.mem_cons.2 (.inr hx)))
      rw [ih']
      have hcomm :
          Commute (f a)
            (s.noncommProd f (comm.mono fun _ hx ↦ Finset.mem_cons.2 (.inr hx))) := by
        apply Finset.noncommProd_commute
        intro y hy
        exact comm (Finset.mem_cons_self a s) (Finset.mem_cons.2 (.inr hy)) (by
          intro h
          exact ha (by simpa [h] using hy))
      exact hcomm.symm.eq

/-- Alice's row product is self-adjoint:
$$
  \operatorname{Row}_i(A)^* = \operatorname{Row}_i(A).
$$
It packages the observable self-adjointness of the individual row entries and their
within-row commutativity.  This is useful for proving that the row SOS term
$1 - (-1)^{b_i}\operatorname{Row}_i(A)$ is self-adjoint.
-/
private lemma alice_row_prod_conjTranspose_eq_self
    (i : Fin G.r) :
    (∏ₐ[i])ᴴ = ∏ₐ[i] := by
  unfold ProjectorStrategy.aliceRowProd
  apply noncommProd_conjTranspose_eq_self
  intro j _
  simpa [star_eq_conjTranspose] using
    (ProjectorStrategy.isObservable_aliceObs strat i j).self_adjoint

/-- The LCS sign attached to row $i$ is real:
$$
  \overline{(-1)^{b_i}} = (-1)^{b_i}.
$$
This small scalar fact is used when taking adjoints of signed relation terms such as
$1 - (-1)^{b_i}T$ in the Stage 2 self-adjointness checks.
-/
private lemma sign_star_eq_self {G : Layout} (game : Game G) (i : Fin G.r) :
    star ((-1 : ℂ) ^ (game.b i).val) = (-1 : ℂ) ^ (game.b i).val := by
  rcases zmod_two_eq_zero_or_one (game.b i) with hb | hb <;> simp [hb]

/-- If $c$ is real and $T$ is self-adjoint, then the affine relation
$1 - cT$ is self-adjoint:
$$
  (1 - cT)^* = 1 - cT .
$$
This avoids repeating the adjoint calculation for both signed SOS relation terms in
Stage 2.
-/
private lemma one_sub_smul_conjTranspose_eq_self
    {m : Type*} [DecidableEq m]
    (c : ℂ) (T : Matrix m m ℂ)
    (hc : star c = c) (hT : Tᴴ = T) :
    (1 - c • T)ᴴ = 1 - c • T := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, hc, hT]

/-- The consistency SOS relation term is self-adjoint:
$$
  (1 - B_jA_{ij})^* = 1 - B_jA_{ij}.
$$
The proof uses that Alice and Bob observables are self-adjoint and commute.  This is one
of the three self-adjointness hypotheses required to turn
$(T_1^2 + T_2^2 + T_3^2)\Omega = 0$ into $T_1\Omega = 0$.
-/
private lemma sos_consistency_term_conjTranspose_eq_self
    (i : Fin G.r) (j : G.V i) :
    (sosConsistencyTerm n strat i j)ᴴ =
      sosConsistencyTerm n strat i j := by
  have hA : A[i, j]ᴴ = A[i, j] := by
    simpa [star_eq_conjTranspose] using
      (ProjectorStrategy.isObservable_aliceObs strat i j).self_adjoint
  have hB : B[↑j]ᴴ = B[↑j] := by
    simpa [star_eq_conjTranspose] using
      (ProjectorStrategy.isObservable_bobObs strat ↑j).self_adjoint
  unfold sosConsistencyTerm
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hA, hB]
  rw [(ProjectorStrategy.aliceObs_commute_bobObs strat i j ↑j).eq]

/-- The product inside the third SOS relation is self-adjoint:
$$
  \bigl(\operatorname{Row}_i(A) A_{ij} B_j\bigr)^*
    = \operatorname{Row}_i(A) A_{ij} B_j .
$$
It combines self-adjointness of the row product, Alice entry, and Bob entry with the local
commutation rules.  This is the key input for showing that the signed product SOS term
$1 - (-1)^{b_i}\operatorname{Row}_i(A)A_{ij}B_j$ is self-adjoint.
-/
private lemma sos_product_core_conjTranspose_eq_self
    (i : Fin G.r) (j : G.V i) :
    (∏ₐ[i] * A[i, j] * B[↑j])ᴴ = ∏ₐ[i] * A[i, j] * B[↑j] := by
  have hRow : (∏ₐ[i])ᴴ = ∏ₐ[i] := alice_row_prod_conjTranspose_eq_self n strat i
  have hA : A[i, j]ᴴ = A[i, j] := by
    simpa [star_eq_conjTranspose] using
      (ProjectorStrategy.isObservable_aliceObs strat i j).self_adjoint
  have hB : B[↑j]ᴴ = B[↑j] := by
    simpa [star_eq_conjTranspose] using
      (ProjectorStrategy.isObservable_bobObs strat ↑j).self_adjoint
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRow, hA, hB]
  calc
    B[↑j] * (A[i, j] * ∏ₐ[i]) = B[↑j] * (∏ₐ[i] * A[i, j]) := by
          rw [(ProjectorStrategy.aliceObs_commute_aliceRowProd strat i j).eq]
    _ = (B[↑j] * ∏ₐ[i]) * A[i, j] := by
          rw [Matrix.mul_assoc]
    _ = (∏ₐ[i] * B[↑j]) * A[i, j] := by
          rw [(ProjectorStrategy.bobObs_commute_aliceRowProd strat i j).eq]
    _ = ∏ₐ[i] * (B[↑j] * A[i, j]) := by
          rw [Matrix.mul_assoc]
    _ = ∏ₐ[i] * (A[i, j] * B[↑j]) := by
          rw [(ProjectorStrategy.aliceObs_commute_bobObs strat i j ↑j).eq]
    _ = ∏ₐ[i] * A[i, j] * B[↑j] := by
          rw [Matrix.mul_assoc]

/-- If the scaled SOS square-sum annihilates EPR, then each individual SOS relation term
annihilates EPR:
$$
  \frac18(T_1^2 + T_2^2 + T_3^2)\Omega = 0
    \quad\Longrightarrow\quad
  T_1\Omega = T_2\Omega = T_3\Omega = 0 .
$$
Here $T_1 = 1 - B_jA_{ij}$, $T_2 = 1 - (-1)^{b_i}\operatorname{Row}_i(A)$, and
$T_3 = 1 - (-1)^{b_i}\operatorname{Row}_i(A)A_{ij}B_j$.  This is the positivity step
that bridges the rewritten local-loss SOS identity from Stage 1 to the concrete local
matrix identities extracted in Stage 3.
-/
lemma sos_sum_kills_epr_implies_terms_kill_epr
    (i : Fin G.r) (j : G.V i)
    (h :
      ((1 / 8 : ℂ) • sosSquareSum game n strat i j) *ᵥ Ω = 0) :
    sosConsistencyTerm n strat i j *ᵥ Ω = 0 ∧
      sosRowTerm game n strat i *ᵥ Ω = 0 ∧
      sosProductTerm game n strat i j *ᵥ Ω = 0 := by
  let T₁ : Matrix (n × n) (n × n) ℂ := sosConsistencyTerm n strat i j
  let T₂ : Matrix (n × n) (n × n) ℂ := sosRowTerm game n strat i
  let T₃ : Matrix (n × n) (n × n) ℂ := sosProductTerm game n strat i j
  have hsum : (T₁ ^ 2 + T₂ ^ 2 + T₃ ^ 2) *ᵥ Ω = 0 := by
    have hscaled :
        (1 / 8 : ℂ) • (sosSquareSum game n strat i j *ᵥ Ω) = 0 := by
      simpa only [Matrix.smul_mulVec] using h
    rcases smul_eq_zero.mp hscaled with hcoef | hzero
    · norm_num at hcoef
    · simpa [T₁, T₂, T₃, sosSquareSum] using hzero
  have hT₁ : T₁ᴴ = T₁ := by
    simpa [T₁] using sos_consistency_term_conjTranspose_eq_self n strat i j
  have hT₂ : T₂ᴴ = T₂ := by
    simpa [T₂, sosRowTerm] using one_sub_smul_conjTranspose_eq_self
      ((-1 : ℂ) ^ b[i].val)
      ∏ₐ[i]
      (sign_star_eq_self game i)
      (alice_row_prod_conjTranspose_eq_self n strat i)
  have hT₃ : T₃ᴴ = T₃ := by
    simpa [T₃, sosProductTerm] using one_sub_smul_conjTranspose_eq_self
      ((-1 : ℂ) ^ b[i].val)
      (∏ₐ[i] * A[i, j] * B[↑j])
      (sign_star_eq_self game i)
      (sos_product_core_conjTranspose_eq_self n strat i j)
  simpa [T₁, T₂, T₃] using
    three_selfAdjoint_squares_mulVec_eq_zero T₁ T₂ T₃ Ω hT₁ hT₂ hT₃ hsum

end Stage2

section Stage3
/-!
### Stage 3: Individual SOS-Term Annihilation ⇒ Local Matrix Identities

The sum-of-squares decomposition produces three relation terms.  Once a
positivity argument shows that each term annihilates the EPR vector, the lemmas
in this section remove $\Omega$ and produce the local matrix identities needed
for the solution-group representation.
-/

/-- If the consistency SOS relation annihilates EPR, the local Alice and Bob matrices agree
up to transpose:
$$
  A_{ij} = B_j^T.
$$
-/
lemma consistency_of_epr_annihilates
    (i : Fin G.r) (j : G.V i)
    (A B : Matrix n n ℂ)
    (hCons :
      sosConsistencyTerm n strat i j *ᵥ Ω = 0)
    (hAlice : A[i, j] = bipartiteAliceLift A)
    (hBob : B[↑j] = bipartiteBobLift B)
    (hBobs : IsObservable B) :
    A = Bᵀ := by
  have hCons' :
      (1 - A ⊗ₖ B) *ᵥ Ω = 0 := by
    simpa [hAlice, hBob, sosConsistencyTerm, bipartiteBobLift_mul_bipartiteAliceLift] using hCons
  have hAB : A * Bᵀ = 1 :=
    (one_sub_kronecker_mulVec_epr_eq_zero_iff n A B).mp hCons'
  have hBT : Bᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBobs.involutive, Matrix.transpose_one]
  calc
    A = A * 1 := (Matrix.mul_one A).symm
    _ = A * (Bᵀ * Bᵀ) := by rw [hBT]
    _ = (A * Bᵀ) * Bᵀ := by rw [Matrix.mul_assoc]
    _ = Bᵀ := by rw [hAB, Matrix.one_mul]

/-- If the row SOS relation annihilates EPR, the corresponding local row product satisfies
the LCS row equation:
$$
  R_i = (-1)^{b_i} I.
$$
-/
lemma row_relation_of_epr_annihilates
    (i : Fin G.r)
    (Row : Matrix n n ℂ)
    (hRow :
      sosRowTerm game n strat i *ᵥ Ω = 0)
    (hRowLift : ∏ₐ[i] = bipartiteAliceLift Row) :
    Row = (-1 : ℂ) ^ b[i].val • 1 := by
  let c : ℂ := (-1 : ℂ) ^ b[i].val
  have hLocal : 1 - c • Row = 0 := by
    have hRow' :
        (1 - c • bipartiteAliceLift Row) *ᵥ Ω = 0 := by
      simpa [c, hRowLift, sosRowTerm] using hRow
    exact (bipartiteAliceLift_one_sub_smul_mulVec_epr_eq_zero_iff n c Row).mp hRow'
  have hcRow : c • Row = 1 := (sub_eq_zero.mp hLocal).symm
  have hc : c * c = 1 := by
    simpa [c] using sign_sq (game.b i)
  calc
    Row = (1 : ℂ) • Row := (one_smul ℂ Row).symm
    _ = (c * c) • Row := by rw [hc]
    _ = c • (c • Row) := by rw [smul_smul]
    _ = c • (1 : Matrix n n ℂ) := by rw [hcRow]

/-- If the third SOS relation annihilates EPR, the corresponding local product identity holds:
$$
  (-1)^{b_i} R_i A_{ij} B_j^T = I.
$$
-/
lemma product_relation_of_epr_annihilates
    (i : Fin G.r) (j : G.V i)
    (A B Row : Matrix n n ℂ)
    (hProd :
      sosProductTerm game n strat i j *ᵥ Ω = 0)
    (hAlice : A[i, j] = bipartiteAliceLift A)
    (hBob : B[↑j] = bipartiteBobLift B)
    (hRowLift : ∏ₐ[i] = bipartiteAliceLift Row) :
    (-1 : ℂ) ^ b[i].val • (Row * A * Bᵀ) = 1 := by
  let c : ℂ := (-1 : ℂ) ^ b[i].val
  have hProd' :
      (1 - c • ((Row * A) ⊗ₖ B)) *ᵥ Ω = 0 := by
    simpa [c, hAlice, hBob, hRowLift, sosProductTerm, bipartiteAliceLift_mul,
      bipartiteAliceLift_mul_bipartiteBobLift, Matrix.mul_assoc] using hProd
  have hLocal :
      c • ((Row * A) * Bᵀ) = 1 :=
    (one_sub_smul_kronecker_mulVec_epr_eq_zero_iff n c (Row * A) B).mp hProd'
  simpa [Matrix.mul_assoc] using hLocal

/-- Bundled extraction of the local matrix identities from the individual SOS relation terms
annihilating EPR.

Given annihilation of the consistency, row, and product SOS terms, this returns
the three local identities
$$
  A_{ij} = B_j^T,\qquad
  R_i = (-1)^{b_i} I,\qquad
  (-1)^{b_i} R_i A_{ij} B_j^T = I.
$$
-/
lemma local_matrix_identities_of_sos_terms_annihilate_epr
    (i : Fin G.r) (j : G.V i)
    (A B Row : Matrix n n ℂ)
    (hCons :
      sosConsistencyTerm n strat i j *ᵥ Ω = 0)
    (hRow :
      sosRowTerm game n strat i *ᵥ Ω = 0)
    (hProd :
      sosProductTerm game n strat i j *ᵥ Ω = 0)
    (hAlice : A[i, j] = bipartiteAliceLift A)
    (hBob : B[↑j] = bipartiteBobLift B)
    (hRowLift : ∏ₐ[i] = bipartiteAliceLift Row)
    (hBobs : IsObservable B) :
    A = Bᵀ ∧
      Row = (-1 : ℂ) ^ (game.b i).val • 1 ∧
      (-1 : ℂ) ^ (game.b i).val • (Row * A * Bᵀ) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact consistency_of_epr_annihilates n strat i j A B hCons hAlice hBob hBobs
  · exact row_relation_of_epr_annihilates game n strat i Row hRow hRowLift
  · exact product_relation_of_epr_annihilates game n strat i j A B Row hProd hAlice hBob hRowLift

end Stage3

/-- Final bundled extraction from local-loss annihilation on EPR to the local matrix
identities.

This packages the three stages:
1. local loss annihilates `Ω`, so the scaled SOS square-sum annihilates `Ω`;
2. the positivity argument extracts annihilation of each SOS relation term;
3. EPR injectivity converts those annihilations into local matrix identities.
-/
lemma local_matrix_identities_of_local_loss_annihilate_epr
    (i : Fin G.r) (j : G.V i)
    (A B Row : Matrix n n ℂ)
    (hLoss :
      localLossOperator game strat i j *ᵥ Ω = 0)
    (hAlice : A[i, j] = bipartiteAliceLift A)
    (hBob : B[↑j] = bipartiteBobLift B)
    (hRowLift : ∏ₐ[i] = bipartiteAliceLift Row)
    (hBobs : IsObservable B) :
    A = Bᵀ ∧
      Row = (-1 : ℂ) ^ (game.b i).val • 1 ∧
      (-1 : ℂ) ^ (game.b i).val • (Row * A * Bᵀ) = 1 := by
  have hSos :
      ((1 / 8 : ℂ) • sosSquareSum game n strat i j) *ᵥ Ω = 0 :=
    local_loss_kills_epr_sos_sum game n strat i j hLoss
  rcases sos_sum_kills_epr_implies_terms_kill_epr game n strat i j hSos with
    ⟨hCons, hRow, hProd⟩
  exact local_matrix_identities_of_sos_terms_annihilate_epr
    game n strat i j A B Row hCons hRow hProd hAlice hBob hRowLift hBobs

end LCSSOSTerms

end MIPRE.LCS
