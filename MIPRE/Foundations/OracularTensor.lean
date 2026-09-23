/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularSound
import MIPRE.Foundations.POVMMix
import MIPRE.Foundations.GameAdapt
import MIPRE.Foundations.RegisterReindex

/-!
# Soundness of oracularization, for bipartite strategies

Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of
games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for
`MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so
`val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`.

`MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That
is not the statement a verifier-level consumer can use: `Verifier.valStar` is a supremum over
`TensorProductStrategy`, and so is the detyping transport (`restrictAmbient_value_ge`), while the
only bridge from synchronous to bipartite values, `thm:almost-sync`, is off the critical path.
The paper's `thm:oracle-soundness` is bipartite; this is its game-level form.

## The argument

Every `TensorProductStrategy` is projective, so no Naimark dilation is needed. Fix a seed `z` and
write, on the joint space, `O` for the first player's oracle measurement at `(oracle, z)`,
`O^𝖠`, `O^𝖡` for its two component marginals (`OAns.aliceView`, `OAns.bobView`), `C` for the
first player's isolated-Alice measurement at `L^𝖠 z`, and `P`, `Q` for the second player's
isolated-Alice and isolated-Bob measurements at `L^𝖠 z` and `L^𝖡 z`. Then

`C_u ⊗ Q_v - O^𝖠_u O^𝖡_v ⊗ Id = (Id ⊗ Q_v)(C_u ⊗ Id - Id ⊗ P_u)`
  `+ (Id ⊗ Q_v)(Id ⊗ P_u - O^𝖠_u ⊗ Id) + (O^𝖠_u ⊗ Id)(Id ⊗ Q_v - O^𝖡_v ⊗ Id)`

(`sum_snorm_sq_chain`). Each front factor is a projective measurement, so it costs nothing summed
over its outcome (`sum_snorm_sq_mul_le`), and each of the three deviations is the cross-party
consistency of one role pair --- `(alice, alice)`, `(oracle, alice)`, `(oracle, bob)` --- hence at
most twice that pair's conditional failure (`xSqNorm_sum_le_condFail`). So the product strategy is
within `6` times three conditional failures of the oracle's joint marginal, linearly in `ε`.

The single square root of repair 1 of `rem:oracularization-repairs` is spent once, in
`sum_snorm_sq_ge_of_close`: the paper's `fact:approx-implies-close-value` (NW19's Fact 4.31) at
the level of vectors, which compares the mass two families with total mass at most one put on the
set of outcome pairs the input decider accepts. The oracle's joint marginal puts mass at least the
oracle's own acceptance probability at `(oracle, oracle)` there.

Averaging, the four role pairs used are distinct and each carries a ninth of the question weight,
so their conditional failures average to at most `9ε` in total (`sum_failAt_four_le`), and
`val ≥ 1 - 9ε - 2√(54ε) ≥ 1 - 24√ε`: the synchronous constant. Neither the paper's
marginalization step nor its commutation step is needed, because the oracle's measurement enters
only through its joint marginal and the second player's two isolated measurements are multiplied
in one order only.

The extracted strategy (`tensorSound`) is the adapter `TensorProductStrategy.adapt`: the first
player's isolated-Alice measurement and the second player's isolated-Bob measurement, relabelled
along `OAns.singlePart` so that an oracle-shaped answer is grouped into one distinguished outcome.
-/

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

/-! ## Reading an oracle's answer one component at a time -/

section Views

variable {A : Type*}

/-- An oracularized answer read as the answer meant for the original Alice: an oracle's pair is
read as its first component; an isolated player's answer is left as it is (for an oracle it is
rejected by the shape check anyway). -/
def OAns.aliceView : OAns A → OAns A
  | .pair a _ => .single a
  | .single a => .single a

/-- An oracularized answer read as the answer meant for the original Bob. -/
def OAns.bobView : OAns A → OAns A
  | .pair _ b => .single b
  | .single b => .single b

end Views

/-! ## Close measurements have close values -/

section CloseValues

variable {N : Type*} [Fintype N] {ι : Type*} [Fintype ι]

/-- **Close measurements have close values**, at the level of vectors (the paper's
`fact:approx-implies-close-value`, NW19's Fact 4.31): two families of operators whose total
squared mass on `v` is at most one put masses within `2√δ` of each other on any set of outcomes,
`δ` their summed squared deviation. For projections the squared mass is the Born probability. -/
theorem sum_snorm_sq_ge_of_close (v : N → ℂ) (R O : ι → Matrix N N ℂ)
    (hR : ∑ i, snorm v (R i) ^ 2 ≤ 1) (hO : ∑ i, snorm v (O i) ^ 2 ≤ 1) (acc : Finset ι) :
    ∑ i ∈ acc, snorm v (O i) ^ 2 - 2 * √(∑ i, snorm v (R i - O i) ^ 2)
      ≤ ∑ i ∈ acc, snorm v (R i) ^ 2 := by
  set D : ι → ℝ := fun i => snorm v (R i - O i) with hD
  set s : ι → ℝ := fun i => snorm v (O i) + snorm v (R i) with hs
  have hterm : ∀ i, snorm v (O i) ^ 2 - snorm v (R i) ^ 2 ≤ D i * s i := by
    intro i
    have h1 : snorm v (O i) ≤ snorm v (R i) + D i := by
      have h := snorm_sub_le v (R i) (R i - O i)
      rwa [sub_sub_cancel] at h
    have h0 := snorm_nonneg v (O i)
    have h0' := snorm_nonneg v (R i)
    have hk : 0 ≤ (D i - (snorm v (O i) - snorm v (R i))) * s i :=
      mul_nonneg (by linarith) (by simp only [hs]; linarith)
    simp only [hs] at hk ⊢
    nlinarith [hk]
  have hD0 : ∀ i, 0 ≤ D i * s i := fun i =>
    mul_nonneg (snorm_nonneg v _) (add_nonneg (snorm_nonneg v _) (snorm_nonneg v _))
  have hsum : ∑ i ∈ acc, snorm v (O i) ^ 2 - ∑ i ∈ acc, snorm v (R i) ^ 2
      ≤ ∑ i, D i * s i := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ i ∈ acc, (snorm v (O i) ^ 2 - snorm v (R i) ^ 2) ≤ ∑ i ∈ acc, D i * s i :=
          Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ∑ i, D i * s i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hD0 i
  have hs2 : ∑ i, s i ^ 2 ≤ 4 := by
    have hle : ∀ i, s i ^ 2 ≤ 2 * snorm v (O i) ^ 2 + 2 * snorm v (R i) ^ 2 := fun i => by
      simp only [hs]
      nlinarith [sq_nonneg (snorm v (O i) - snorm v (R i))]
    calc ∑ i, s i ^ 2 ≤ ∑ i, (2 * snorm v (O i) ^ 2 + 2 * snorm v (R i) ^ 2) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = 2 * ∑ i, snorm v (O i) ^ 2 + 2 * ∑ i, snorm v (R i) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 4 := by linarith
  have hsq : √(∑ i, s i ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
    exact Real.sqrt_le_sqrt hs2
  have hcs : ∑ i, D i * s i ≤ 2 * √(∑ i, D i ^ 2) :=
    calc ∑ i, D i * s i ≤ √(∑ i, D i ^ 2) * √(∑ i, s i ^ 2) := sum_mul_le_sqrt D s
      _ ≤ √(∑ i, D i ^ 2) * 2 := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ = 2 * √(∑ i, D i ^ 2) := by ring
  have hDsq : ∑ i, D i ^ 2 = ∑ i, snorm v (R i - O i) ^ 2 := rfl
  rw [hDsq] at hcs
  linarith

/-- A projective measurement has total squared mass one on a unit vector. -/
theorem sum_snorm_sq_eq_one_of_isPVM [DecidableEq N] {v : N → ℂ} (hv : ‖evec v‖ = 1)
    {M : ι → Matrix N N ℂ} (hM : IsPVM M) : ∑ i, snorm v (M i) ^ 2 = 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by
      rw [snorm_sq_eq_qform, hM.isSelfAdjoint i, hM.idem i],
    ← qform_sum, hM.sum_eq_one, qform_one v hv]

end CloseValues

/-! ## Fibres of a projective measurement -/

section Fibres

variable {n : Type*} [Fintype n] [DecidableEq n] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The product of two fibre sums is the fibre sum over the intersection**: distinct outcomes of
a projective measurement are orthogonal. -/
theorem IsPVM.sum_mul_sum {P : Λ → Matrix n n ℂ} (hP : IsPVM P) (s t : Finset Λ) :
    (∑ a ∈ s, P a) * (∑ b ∈ t, P b) = ∑ a ∈ s ∩ t, P a := by
  rw [Finset.sum_mul_sum, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ t
  · rw [if_pos ha, Finset.sum_eq_single_of_mem a ha fun b _ hba => hP.orthogonal (Ne.symm hba),
      hP.idem a]
  · rw [if_neg ha]
    exact Finset.sum_eq_zero fun b hb => hP.orthogonal fun hab => ha (hab ▸ hb)

/-- **A projective measurement, coarse-grained, is projective.** -/
theorem IsPVM.fibre {P : Λ → Matrix n n ℂ} (hP : IsPVM P) {C : Type*} [Fintype C] [DecidableEq C]
    (f : Λ → C) : IsPVM fun c => ∑ a ∈ univ.filter fun a => f a = c, P a where
  isSelfAdjoint c := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun a _ => hP.isSelfAdjoint a
  idem c := by rw [hP.sum_mul_sum, Finset.inter_self]
  sum_eq_one := by
    rw [Finset.sum_fiberwise_of_maps_to (fun a _ => mem_univ (f a))]
    exact hP.sum_eq_one

end Fibres

/-- The operators of a projective measurement at one question form a PVM. -/
theorem ProjectiveMeasurement.isPVM_at {X A : Type*} [Fintype A] {n : Type*} [Fintype n]
    [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) :
    IsPVM (P.M x) where
  isSelfAdjoint a := by rw [← Matrix.star_eq_conjTranspose]; exact P.selfAdjoint x a
  idem a := P.projective x a
  sum_eq_one := P.normalized x

@[simp] theorem ProjectiveMeasurement.toPOVM_mats_val {X A : Type*} [Fintype A] {n : Type*}
    [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) (a : A) :
    ((P.toPOVM x).mats a).val = P.M x a := rfl

/-! ## The chain of three deviations -/

section Chain

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- **The per-seed algebra.** `C_u ⊗ Q_v - O^𝖠_u O^𝖡_v ⊗ Id` splits into three cross-party
deviations, each behind a front factor that is a projective measurement and so costs nothing
summed over its outcome. -/
theorem sum_snorm_sq_chain (ψ : HA × HB → ℂ) {K : Type*} [Fintype K] [DecidableEq K]
    (C OA OB : K → Matrix HA HA ℂ) (P Q : K → Matrix HB HB ℂ) (hQ : IsPVM Q) (hOA : IsPVM OA) :
    ∑ o : K × K,
        snorm ψ ((aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
          - aOp (OA o.1 * OB o.2)) ^ 2
      ≤ 3 * ∑ u, snorm ψ ((aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ u, snorm ψ ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ v, snorm ψ ((aOp (OB v) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (Q v)) ^ 2 := by
  have hQF : ∑ v, ((bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ))ᴴ * bOp (Q v)
      ≤ (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
    le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hQ)
  have hOF : ∑ u, ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ))ᴴ * aOp (OA u)
      ≤ (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
    le_of_eq (sum_aOp_conjTranspose_mul_self_of_isPVM hOA)
  refine le_trans (sum_snorm_sq_triangle3 ψ
    (fun o : K × K => (aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2))
    (fun o => (bOp (Q o.2) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (P o.1))
    (fun o => (aOp (OA o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2))
    (fun o => (aOp (OA o.1 * OB o.2) : Matrix (HA × HB) (HA × HB) ℂ))) ?_
  -- the first deviation: `(Id ⊗ Q_v)(C_u ⊗ Id - Id ⊗ P_u)`
  have h1 : ∑ o : K × K, snorm ψ ((aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
        - bOp (Q o.2) * bOp (P o.1)) ^ 2
      ≤ ∑ u, snorm ψ ((aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    have heq : ∀ v, (aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q v)
        - bOp (Q v) * bOp (P u) = bOp (Q v) * (aOp (C u) - bOp (P u)) := fun v => by
      rw [aOp_mul_bOp, Matrix.mul_sub]
    simp only [heq]
    exact sum_snorm_sq_mul_le ψ (fun v => (bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ)) hQF _
  -- the second: `(Id ⊗ Q_v)(Id ⊗ P_u - O^𝖠_u ⊗ Id)`
  have h2 : ∑ o : K × K, snorm ψ ((bOp (Q o.2) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (P o.1)
        - aOp (OA o.1) * bOp (Q o.2)) ^ 2
      ≤ ∑ u, snorm ψ ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    have heq : ∀ v, (bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (P u)
        - aOp (OA u) * bOp (Q v) = bOp (Q v) * (bOp (P u) - aOp (OA u)) := fun v => by
      rw [aOp_mul_bOp, Matrix.mul_sub]
    simp only [heq]
    rw [snorm_sub_comm]
    exact sum_snorm_sq_mul_le ψ (fun v => (bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ)) hQF _
  -- the third: `(O^𝖠_u ⊗ Id)(Id ⊗ Q_v - O^𝖡_v ⊗ Id)`
  have h3 : ∑ o : K × K, snorm ψ ((aOp (OA o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
        - aOp (OA o.1 * OB o.2)) ^ 2
      ≤ ∑ v, snorm ψ ((aOp (OB v) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (Q v)) ^ 2 := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_le_sum fun v _ => ?_
    have heq : ∀ u, (aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q v)
        - aOp (OA u * OB v) = aOp (OA u) * (bOp (Q v) - aOp (OB v)) := fun u => by
      rw [aOp_mul, Matrix.mul_sub]
    simp only [heq]
    rw [snorm_sub_comm]
    exact sum_snorm_sq_mul_le ψ (fun u => (aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ)) hOF _
  linarith

end Chain

/-! ## Born probabilities of a bipartite strategy, on the joint space -/

section Proj

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- For projections `X`, `Y`, the squared mass of `X ⊗ Y` is its quadratic form. -/
theorem snorm_sq_aOp_mul_bOp_of_proj (ψ : HA × HB → ℂ) {X : Matrix HA HA ℂ} {Y : Matrix HB HB ℂ}
    (hX : Xᴴ = X) (hXX : X * X = X) (hY : Yᴴ = Y) (hYY : Y * Y = Y) :
    snorm ψ ((aOp X : Matrix (HA × HB) (HA × HB) ℂ) * bOp Y) ^ 2
      = qform ψ ((aOp X : Matrix (HA × HB) (HA × HB) ℂ) * bOp Y) := by
  rw [snorm_sq_eq_qform]
  congr 1
  rw [Matrix.conjTranspose_mul, bOp_conjTranspose, aOp_conjTranspose, hX, hY]
  calc (bOp Y : Matrix (HA × HB) (HA × HB) ℂ) * aOp X * (aOp X * bOp Y)
      = aOp X * bOp Y * (aOp X * bOp Y) := by rw [← aOp_mul_bOp]
    _ = aOp X * (aOp X * bOp Y * bOp Y) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bOp Y), ← aOp_mul_bOp]
    _ = aOp X * bOp Y := by
        rw [Matrix.mul_assoc (aOp X), ← bOp_mul, hYY, ← Matrix.mul_assoc, ← aOp_mul, hXX]

/-- For a projection `X`, the squared mass of `X ⊗ Id` is its quadratic form. -/
theorem snorm_sq_aOp (ψ : HA × HB → ℂ) {X : Matrix HA HA ℂ} (hX : Xᴴ = X) (hXX : X * X = X) :
    snorm ψ (aOp X : Matrix (HA × HB) (HA × HB) ℂ) ^ 2
      = qform ψ (aOp X : Matrix (HA × HB) (HA × HB) ℂ) := by
  rw [snorm_sq_eq_qform, aOp_conjTranspose, ← aOp_mul, hX, hXX]

end Proj

section Born

variable {X Y A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A'] [Fintype B']
variable {G : Game X Y A' B'}

namespace TensorProductStrategy

/-- The Born probability, as the quadratic form of `A^x_a ⊗ B^y_b` on the joint space. -/
theorem born_eq_qform (N : TensorProductStrategy G) (x : X) (y : Y) (a : A') (b : B') :
    N.born x y a b
      = qform N.ψ ((aOp (N.PA.M x a) : Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          * bOp (N.PB.M y b)) :=
  bornProb_eq_qform N.ψ (N.PA.M x a) (N.PB.M y b)

/-- Summing out the second player's outcome leaves the first player's marginal. -/
theorem sum_born_right (N : TensorProductStrategy G) (x : X) (y : Y) (a : A') :
    ∑ b, N.born x y a b
      = qform N.ψ (aOp (N.PA.M x a) : Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := by
  simp_rw [N.born_eq_qform]
  rw [← qform_sum, ← Finset.mul_sum, ← bOp_sum, N.PB.normalized y, bOp_one, Matrix.mul_one]

/-- The Born probability is the squared mass of `A^x_a ⊗ B^y_b`, the operators being
projections. -/
theorem snorm_sq_eq_born (N : TensorProductStrategy G) (x : X) (y : Y) (a : A') (b : B') :
    snorm N.ψ ((aOp (N.PA.M x a) : Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
        * bOp (N.PB.M y b)) ^ 2 = N.born x y a b := by
  rw [snorm_sq_aOp_mul_bOp_of_proj N.ψ ((N.PA.isPVM_at x).isSelfAdjoint a) ((N.PA.isPVM_at x).idem a)
    ((N.PB.isPVM_at y).isSelfAdjoint b) ((N.PB.isPVM_at y).idem b), N.born_eq_qform]

/-- The conditional failure of `povmValue`, read on the strategy's own measurements. -/
theorem condFail_eq_failAt (N : TensorProductStrategy G) (x : X) (y : Y) :
    condFail G N.ψ (fun x => N.PA.toPOVM x) (fun y => N.PB.toPOVM y) x y = N.failAt x y := rfl

/-- **Accept implies agree**, for a bipartite strategy: if acceptance at `(x, y)` forces two
post-processings of the answers to agree, the cross-party deviation of the post-processed
measurements is at most twice the conditional failure there. -/
theorem sum_snorm_sq_fibre_le (N : TensorProductStrategy G) (x : X) (y : Y)
    {C : Type*} [Fintype C] [DecidableEq C] (f : A' → C) (g : B' → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    ∑ c, snorm N.ψ
        ((aOp (∑ a ∈ univ.filter fun a => f a = c, N.PA.M x a) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          - bOp (∑ b ∈ univ.filter fun b => g b = c, N.PB.M y b)) ^ 2
      ≤ 2 * N.failAt x y := by
  have h := xSqNorm_sum_le_condFail (G := G) (ψ := N.ψ) (MA := fun x => N.PA.toPOVM x)
    (MB := fun y => N.PB.toPOVM y) N.ψ_unit f g hD
  rw [N.condFail_eq_failAt] at h
  simpa only [xSqNorm_eq_snorm_sq, POVM.map_mats, ProjectiveMeasurement.toPOVM_mats_val] using h

end TensorProductStrategy

end Born

/-! ## The three roles -/

/-- A sum over the three roles. -/
theorem Role.sum_eq {M : Type*} [AddCommMonoid M] (f : Role → M) :
    ∑ r, f r = f .oracle + f .alice + f .bob := by
  change ∑ r ∈ ({Role.oracle, Role.alice, Role.bob} : Finset Role), f r = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

namespace SeededGame

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)

/-! ## What acceptance forces -/

/-- The oracle's own answer passes the game check: it is a pair, which the input decider accepts
at the question pair the seed determines. -/
def oracleGood (z : V) : OAns A → Bool
  | .pair a b => S.D (S.LA z) (S.LB z) a b
  | .single _ => false

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem oracleGood_of_oaccepts {z : V} {q : Role × V} {w u : OAns A}
    (h : S.oaccepts (Role.oracle, z) q w u = true) : S.oracleGood z w = true := by
  cases w <;> simp_all [oaccepts, shapeOk, gameCheck, oracleGood]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem aliceView_of_oaccepts {z x : V} {w u : OAns A}
    (h : S.oaccepts (Role.oracle, z) (Role.alice, x) w u = true) : w.aliceView = u := by
  cases w <;> cases u <;> simp_all [oaccepts, shapeOk, gameCheck, oracleVsPlayer, OAns.aliceView]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem bobView_of_oaccepts {z y : V} {w v : OAns A}
    (h : S.oaccepts (Role.oracle, z) (Role.bob, y) w v = true) : w.bobView = v := by
  cases w <;> cases v <;> simp_all [oaccepts, shapeOk, gameCheck, oracleVsPlayer, OAns.bobView]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem eq_of_oaccepts_self {p : Role × V} {u v : OAns A} (h : S.oaccepts p p u v = true) :
    u = v := by
  by_contra hne
  rw [S.oaccepts_eq_false_of_ne hne] at h
  exact Bool.false_ne_true h

/-! ## The extracted strategy -/

/-- **The strategy extracted from a bipartite strategy for the oracularization**: Alice plays the
first player's isolated-Alice measurement, Bob the second player's isolated-Bob measurement, both
relabelled along `OAns.singlePart`, so that an oracle-shaped answer is grouped into one
distinguished outcome. Same state, same Hilbert spaces. -/
noncomputable def tensorSound (N : TensorProductStrategy S.oracular.toGame) :
    TensorProductStrategy S.toGame :=
  N.adapt S.toGame (fun x => (Role.alice, x)) (fun y => (Role.bob, y))
    (fun _ => OAns.singlePart) (fun _ => OAns.singlePart)

omit [Inhabited A] in
theorem tensorSound_ψ (N : TensorProductStrategy S.oracular.toGame) [Inhabited A] :
    (S.tensorSound N).ψ = N.ψ := rfl

/-- The answer pairs the input decider accepts at the question pair the seed determines. -/
def accPairs (z : V) : Finset (A × A) :=
  univ.filter fun p => S.D (S.LA z) (S.LB z) p.1 p.2 = true

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
/-- Pairs of isolated answers. -/
def singlePairEmb : A × A ↪ OAns A × OAns A :=
  ⟨fun p => (OAns.single p.1, OAns.single p.2), fun p q h => by
    simp only [Prod.mk.injEq, OAns.single.injEq] at h
    exact Prod.ext h.1 h.2⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
@[simp] theorem singlePairEmb_apply (p : A × A) :
    singlePairEmb p = (OAns.single p.1, OAns.single p.2) := rfl

variable {S}

/-- The oracle's measurement at `(oracle, z)`, coarse-grained along a view of its answer. -/
noncomputable def oracleView (N : TensorProductStrategy S.oracular.toGame) (z : V)
    (f : OAns A → OAns A) (u : OAns A) : Matrix (Fin N.dA) (Fin N.dA) ℂ :=
  ∑ w ∈ univ.filter fun w => f w = u, N.PA.M (Role.oracle, z) w

omit [Inhabited A] in
theorem isPVM_oracleView (N : TensorProductStrategy S.oracular.toGame) (z : V)
    (f : OAns A → OAns A) : IsPVM (oracleView N z f) :=
  (N.PA.isPVM_at (Role.oracle, z)).fibre f

omit [Inhabited A] in
/-- The two component marginals multiply to the joint marginal. -/
theorem oracleView_mul (N : TensorProductStrategy S.oracular.toGame) (z : V) (u v : OAns A) :
    oracleView N z OAns.aliceView u * oracleView N z OAns.bobView v
      = ∑ w ∈ univ.filter fun w => (w.aliceView, w.bobView) = (u, v),
          N.PA.M (Role.oracle, z) w := by
  rw [oracleView, oracleView, (N.PA.isPVM_at _).sum_mul_sum, ← Finset.filter_and]
  refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun _ _ => rfl
  simp [Prod.ext_iff]

omit [Inhabited A] in
/-- **The oracle's joint marginal is a projective measurement.** -/
theorem isPVM_oracleJoint (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    IsPVM fun o : OAns A × OAns A =>
      oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2 := by
  have h := (N.PA.isPVM_at (Role.oracle, z)).fibre fun w : OAns A => (w.aliceView, w.bobView)
  convert h using 1
  funext o
  exact oracleView_mul N z o.1 o.2

/-! ## The estimate at one seed -/

omit [Inhabited A] in
/-- **The three cross-party deviations**, each bounded by its role pair's conditional failure, and
chained: the product of the two isolated measurements is within `6` times three conditional
failures of the oracle's joint marginal. Linear in the failures; no square root yet. -/
theorem sum_snorm_sq_joint_le (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    ∑ o : OAns A × OAns A,
        snorm N.ψ ((aOp (N.PA.M (Role.alice, S.LA z) o.1) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
              * bOp (N.PB.M (Role.bob, S.LB z) o.2)
          - aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2)) ^ 2
      ≤ 6 * (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
        + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
        + N.failAt (Role.oracle, z) (Role.bob, S.LB z)) := by
  have hchain := sum_snorm_sq_chain N.ψ (fun u => N.PA.M (Role.alice, S.LA z) u)
    (oracleView N z OAns.aliceView) (oracleView N z OAns.bobView)
    (fun u => N.PB.M (Role.alice, S.LA z) u) (fun v => N.PB.M (Role.bob, S.LB z) v)
    (N.PB.isPVM_at _) (isPVM_oracleView N z _)
  -- `(alice, alice)`: equal questions force equal answers
  have h1 := N.sum_snorm_sq_fibre_le (Role.alice, S.LA z) (Role.alice, S.LA z)
    (fun u : OAns A => u) (fun u => u) fun a b h => S.eq_of_oaccepts_self h
  -- `(oracle, alice)`: the oracle's Alice component matches the isolated Alice
  have h2 := N.sum_snorm_sq_fibre_le (Role.oracle, z) (Role.alice, S.LA z)
    OAns.aliceView (fun u => u) fun a b h => S.aliceView_of_oaccepts h
  -- `(oracle, bob)`: the oracle's Bob component matches the isolated Bob
  have h3 := N.sum_snorm_sq_fibre_le (Role.oracle, z) (Role.bob, S.LB z)
    OAns.bobView (fun u => u) fun a b h => S.bobView_of_oaccepts h
  simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton] at h1 h2 h3
  have e2 : ∀ c, (∑ a ∈ univ.filter fun a => a.aliceView = c, N.PA.M (Role.oracle, z) a)
      = oracleView N z OAns.aliceView c := fun c => rfl
  have e3 : ∀ c, (∑ a ∈ univ.filter fun a => a.bobView = c, N.PA.M (Role.oracle, z) a)
      = oracleView N z OAns.bobView c := fun c => rfl
  simp only [e2, e3] at h2 h3
  linarith

omit [Inhabited A] in
/-- The product of the two isolated measurements has total mass one. -/
theorem sum_snorm_sq_isolated (N : TensorProductStrategy S.oracular.toGame) (x y : V) :
    ∑ o : OAns A × OAns A,
        snorm N.ψ ((aOp (N.PA.M (Role.alice, x) o.1) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          * bOp (N.PB.M (Role.bob, y) o.2)) ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [N.snorm_sq_eq_born]
  exact N.sum_born _ _

omit [Inhabited A] in
/-- The oracle's joint marginal has total mass one. -/
theorem sum_snorm_sq_oracleJoint (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    ∑ o : OAns A × OAns A,
        snorm N.ψ (aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2 = 1 :=
  sum_snorm_sq_eq_one_of_isPVM (norm_evec_eq_one_of_unit N.ψ_unit) (isPVM_oracleJoint N z).aOp

omit [Inhabited A] in
/-- **The oracle's joint marginal carries the oracle's acceptance.** On the accepted pairs of
isolated answers it has at least the mass with which the oracle passes its own game check at
`(oracle, oracle)`. -/
theorem succAt_oracle_le (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    N.succAt (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ o ∈ (S.accPairs z).map singlePairEmb,
          snorm N.ψ (aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2 := by
  have hproj : ∀ w, snorm N.ψ (aOp (N.PA.M (Role.oracle, z) w) :
      Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2
        = qform N.ψ (aOp (N.PA.M (Role.oracle, z) w) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := fun w =>
    snorm_sq_aOp N.ψ ((N.PA.isPVM_at _).isSelfAdjoint w) ((N.PA.isPVM_at _).idem w)
  -- the oracle's acceptance is at most the mass of its good answers
  have hgood : N.succAt (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ u, (if S.oracleGood z u then 1 else 0) *
          qform N.ψ (aOp (N.PA.M (Role.oracle, z) u) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := by
    unfold TensorProductStrategy.succAt
    refine Finset.sum_le_sum fun u _ => ?_
    rw [← N.sum_born_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (N.born_nonneg _ _ _ _)
    by_cases h : S.oracular.toGame.D (Role.oracle, z) (Role.oracle, z) u w = true
    · rw [if_pos h, if_pos (S.oracleGood_of_oaccepts h)]
    · rw [if_neg h]
      split_ifs <;> norm_num
  -- the good answers are the accepted pairs
  have hpairs : ∑ u, (if S.oracleGood z u then 1 else 0) *
        qform N.ψ (aOp (N.PA.M (Role.oracle, z) u) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
      = ∑ p ∈ S.accPairs z, qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.pair p.1 p.2)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := by
    rw [OAns.sum_eq, accPairs, Finset.sum_filter]
    have hsingle : ∑ a : A, (if S.oracleGood z (OAns.single a) = true then (1 : ℝ) else 0) *
        qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.single a)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) = 0 :=
      Finset.sum_eq_zero fun a _ => by
        show (if false = true then (1 : ℝ) else 0) * _ = 0
        simp
    rw [hsingle, add_zero]
    refine Finset.sum_congr rfl fun p _ => ?_
    show (if S.D (S.LA z) (S.LB z) p.1 p.2 = true then (1 : ℝ) else 0) * _ = _
    split_ifs <;> simp
  -- and each accepted pair lies in its fibre of the joint marginal
  have hfibre : ∀ p ∈ S.accPairs z,
      qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.pair p.1 p.2)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
        ≤ snorm N.ψ (aOp (oracleView N z OAns.aliceView (OAns.single p.1)
            * oracleView N z OAns.bobView (OAns.single p.2)) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) ^ 2 := by
    intro p _
    have hJ := isPVM_oracleJoint N z
    rw [snorm_sq_aOp N.ψ (hJ.isSelfAdjoint (OAns.single p.1, OAns.single p.2))
      (hJ.idem (OAns.single p.1, OAns.single p.2)), oracleView_mul, aOp_sum, qform_sum]
    refine Finset.single_le_sum (f := fun w => qform N.ψ (aOp (N.PA.M (Role.oracle, z) w) :
      Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)) (fun w _ => ?_) ?_
    · rw [← hproj w]
      exact sq_nonneg _
    · simp [OAns.aliceView, OAns.bobView]
  calc N.succAt (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ p ∈ S.accPairs z, qform N.ψ (aOp (N.PA.M (Role.oracle, z) (OAns.pair p.1 p.2)) :
          Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) := hgood.trans (le_of_eq hpairs)
    _ ≤ _ := by
        rw [Finset.sum_map]
        exact Finset.sum_le_sum hfibre

/-- **The extracted strategy wins at least the accepted isolated answer pairs.** -/
theorem succAt_tensorSound_ge_sum (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    ∑ o ∈ (S.accPairs z).map singlePairEmb,
        snorm N.ψ ((aOp (N.PA.M (Role.alice, S.LA z) o.1) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
          * bOp (N.PB.M (Role.bob, S.LB z) o.2)) ^ 2
      ≤ (S.tensorSound N).succAt (S.LA z) (S.LB z) := by
  rw [tensorSound, TensorProductStrategy.succAt_adapt_eq, ← Fintype.sum_prod_type']
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ
    ((S.accPairs z).map singlePairEmb)) fun o _ _ =>
      mul_nonneg (by split_ifs <;> norm_num) (N.born_nonneg _ _ _ _))
  refine Finset.sum_congr rfl fun o ho => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp ho
  have hD : S.D (S.LA z) (S.LB z) p.1 p.2 = true := (Finset.mem_filter.mp hp).2
  rw [N.snorm_sq_eq_born]
  simp only [singlePairEmb_apply, OAns.singlePart, toGame_D, hD, if_true, one_mul]

/-- **Soundness at one seed**, where the square root is spent. -/
theorem succAt_tensorSound_ge (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    1 - N.failAt (Role.oracle, z) (Role.oracle, z)
        - 2 * √(6 * (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z)))
      ≤ (S.tensorSound N).succAt (S.LA z) (S.LB z) := by
  have hclose := sum_snorm_sq_ge_of_close N.ψ
    (fun o : OAns A × OAns A => (aOp (N.PA.M (Role.alice, S.LA z) o.1) :
      Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ) * bOp (N.PB.M (Role.bob, S.LB z) o.2))
    (fun o => aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2))
    (le_of_eq (sum_snorm_sq_isolated N _ _)) (le_of_eq (sum_snorm_sq_oracleJoint N z))
    ((S.accPairs z).map singlePairEmb)
  have hroot := Real.sqrt_le_sqrt (sum_snorm_sq_joint_le N z)
  have hsucc := succAt_oracle_le N z
  have hwin := succAt_tensorSound_ge_sum N z
  have hfail : N.failAt (Role.oracle, z) (Role.oracle, z)
      = 1 - N.succAt (Role.oracle, z) (Role.oracle, z) := rfl
  linarith

/-! ## Averaging over the seed -/

omit [Inhabited A] in
/-- **The budget.** The four role pairs the argument uses are distinct, and each carries a ninth
of the question weight, so their conditional failures, averaged over the seed, add up to at most
nine times the failure probability. -/
theorem sum_failAt_four_le (N : TensorProductStrategy S.oracular.toGame) :
    (Fintype.card V : ℝ)⁻¹ * ∑ z, (N.failAt (Role.oracle, z) (Role.oracle, z)
        + (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z)))
      ≤ 9 * (1 - N.value) := by
  set g : Role × Role × V → ℝ :=
    fun s => N.failAt (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => N.failAt_nonneg _ _
  have htot : 1 - N.value = (Fintype.card (Role × Role × V) : ℝ)⁻¹ * ∑ s, g s := by
    rw [N.one_sub_value_eq_sum_failAt]
    exact S.sum_oDist_mul N.failAt
  have hsplit : ∑ s, g s = ∑ r₁ : Role, ∑ r₂ : Role, ∑ z : V, g (r₁, r₂, z) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r₁ _ => Fintype.sum_prod_type _
  have hpos : ∀ r₁ r₂ : Role, 0 ≤ ∑ z : V, g (r₁, r₂, z) := fun r₁ r₂ =>
    Finset.sum_nonneg fun z _ => hg0 _
  have hfour : ∑ z, (N.failAt (Role.oracle, z) (Role.oracle, z)
        + (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z)))
      = ∑ z, g (.oracle, .oracle, z) + (∑ z, g (.alice, .alice, z)
          + ∑ z, g (.oracle, .alice, z) + ∑ z, g (.oracle, .bob, z)) := by
    simp only [← Finset.sum_add_distrib]
    rfl
  have hle : ∑ z, (N.failAt (Role.oracle, z) (Role.oracle, z)
        + (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z))) ≤ ∑ s, g s := by
    rw [hfour, hsplit]
    simp only [Role.sum_eq]
    linarith [hpos .alice .oracle, hpos .alice .bob, hpos .bob .oracle, hpos .bob .alice,
      hpos .bob .bob]
  have hcard : (Fintype.card V : ℝ)⁻¹ = 9 * (Fintype.card (Role × Role × V) : ℝ)⁻¹ := by
    have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    rw [card_role_prod_prod (V := V)]
    field_simp
  rw [htot, hcard, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hle (by positivity)) (by norm_num)

/-- The value of the extracted strategy is the average over the seed of its conditional success
at the question pair the seed determines. -/
theorem tensorSound_value_eq (N : TensorProductStrategy S.oracular.toGame) :
    (S.tensorSound N).value
      = (Fintype.card V : ℝ)⁻¹ * ∑ z, (S.tensorSound N).succAt (S.LA z) (S.LB z) := by
  rw [TensorProductStrategy.value_eq_sum_succAt]
  exact S.sum_dist_mul _

/-! ## Soundness -/

/-- **Soundness of oracularization, for bipartite strategies** (item 2 of blueprint
`thm:oracularization`, `lem:oracular-soundness-tensor`): a tensor-product strategy of value at
least `1 - ε` for the oracularized game yields one of value at least `1 - 24√ε` for the input
game, on the same state. The loss carries the *single* square root of repair 1 of
`rem:oracularization-repairs`, spent in exactly one place, `sum_snorm_sq_ge_of_close`. -/
theorem tensorSound_value_ge (N : TensorProductStrategy S.oracular.toGame) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hval : 1 - ε ≤ N.value) :
    1 - 24 * √ε ≤ (S.tensorSound N).value := by
  have hcardV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hW : (0 : ℝ) < (Fintype.card V : ℝ)⁻¹ := by positivity
  set F : V → ℝ := fun z => N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
    + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
    + N.failAt (Role.oracle, z) (Role.bob, S.LB z) with hF
  set Gm : V → ℝ := fun z => N.failAt (Role.oracle, z) (Role.oracle, z) with hGm
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    add_nonneg (add_nonneg (N.failAt_nonneg _ _) (N.failAt_nonneg _ _)) (N.failAt_nonneg _ _)
  have hG0 : ∀ z, 0 ≤ Gm z := fun z => N.failAt_nonneg _ _
  -- the budget, split between the game check and the three consistencies
  have hbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z + (Fintype.card V : ℝ)⁻¹ * ∑ z, F z
      ≤ 9 * ε := by
    have h := sum_failAt_four_le N
    rw [← mul_add, ← Finset.sum_add_distrib]
    linarith
  have hGbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z ≤ 9 * ε := by
    have : 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, F z :=
      mul_nonneg hW.le (Finset.sum_nonneg fun z _ => hF0 z)
    linarith
  have hFbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, F z ≤ 9 * ε := by
    have : 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z :=
      mul_nonneg hW.le (Finset.sum_nonneg fun z _ => hG0 z)
    linarith
  -- the averaging step: `𝔼 √(6 F) ≤ √(54 ε)`
  have hjensen : (Fintype.card V : ℝ)⁻¹ * ∑ z, √(6 * F z) ≤ √(54 * ε) := by
    have hj0 := sum_mul_sqrt_le (univ : Finset V) (fun _ => (Fintype.card V : ℝ)⁻¹)
      (fun z => 6 * F z) (fun _ => hW.le) fun z => mul_nonneg (by norm_num) (hF0 z)
    have hj1 : (∑ _z : V, (Fintype.card V : ℝ)⁻¹) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [hj1, Real.sqrt_one, one_mul, ← Finset.mul_sum, ← Finset.mul_sum] at hj0
    refine hj0.trans (Real.sqrt_le_sqrt ?_)
    have h6 : (Fintype.card V : ℝ)⁻¹ * ∑ z, 6 * F z
        = 6 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, F z) := by
      rw [← Finset.mul_sum]
      ring
    rw [h6]
    linarith
  -- put the seeds together
  rw [tensorSound_value_eq]
  have hmono : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - Gm z - 2 * √(6 * F z))
      ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, (S.tensorSound N).succAt (S.LA z) (S.LB z) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => succAt_tensorSound_ge N z) hW.le
  refine le_trans ?_ hmono
  have hexp : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - Gm z - 2 * √(6 * F z))
      = 1 - (Fintype.card V : ℝ)⁻¹ * (∑ z, Gm z)
        - 2 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, √(6 * F z)) := by
    rw [show (∑ z : V, (1 - Gm z - 2 * √(6 * F z)))
        = ((∑ _z : V, (1 : ℝ)) - ∑ z, Gm z) - 2 * ∑ z, √(6 * F z) from by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub, mul_sub,
      inv_mul_cancel₀ hcardV.ne']
    ring
  rw [hexp]
  -- and the final arithmetic
  have heps : ε ≤ √ε := by
    have h1 : √(ε ^ 2) ≤ √ε := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq hε0] at h1
  have hs54 : √(54 * ε) ≤ (7.35 : ℝ) * √ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 54)]
    have h54 : √(54 : ℝ) ≤ 7.35 := by
      rw [show (7.35 : ℝ) = √(7.35 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact mul_le_mul_of_nonneg_right h54 (Real.sqrt_nonneg ε)
  nlinarith [hjensen, hGbud, heps, hs54, Real.sqrt_nonneg ε]

variable (S)

/-- **Soundness of oracularization, in quantum values**: `val*` of the oracularized game above
`1 - ε` puts `val*` of the input game at least `1 - 24√ε`. This is the form a verifier-level
statement consumes, `Verifier.valStar` being a quantum value. -/
theorem quantumValue_ge_of_oracular {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue S.oracular.toGame) :
    1 - 24 * √ε ≤ quantumValue S.toGame := by
  by_cases hε1 : ε ≤ 1
  · by_contra hcon
    rw [not_le] at hcon
    have hall : ∀ N : TensorProductStrategy S.oracular.toGame, N.value ≤ 1 - ε := by
      intro N
      by_contra hN
      rw [not_le] at hN
      have h1 := tensorSound_value_ge N hε.le hε1 hN.le
      have h2 : (S.tensorSound N).value ≤ quantumValue S.toGame :=
        le_ciSup (TensorProductStrategy.bddAbove_range_value _) (S.tensorSound N)
      linarith
    have h3 : quantumValue S.oracular.toGame ≤ 1 - ε := Real.iSup_le hall (by linarith)
    linarith
  · rw [not_le] at hε1
    have h1 : 1 < √ε := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt zero_le_one hε1
    have h2 := quantumValue_nonneg S.toGame
    linarith

end SeededGame

end MIPRE
