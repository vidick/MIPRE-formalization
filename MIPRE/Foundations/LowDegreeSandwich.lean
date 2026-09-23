/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Pasting

/-!
# The low-degree sandwich

Blueprint `lem:ar-sandwich-support`, the paper's `lem:ld-sandwich` (NW19's Fact 4.34 with the
measurements depending on an index). Alice holds a projective measurement `A^x` whose outcome is a
tuple `(g_1, ..., g_k)` of functions; Bob holds, for each coordinate, a projective measurement
`G^{i,x}` of that coordinate alone. If each coordinate of `A`, *evaluated at a random point*, agrees
with the evaluated `G^{i,x}`, then the whole tuple, evaluated, agrees with Bob's **sandwich**

`C^x_{g_1, ..., g_k} = G^{k,x}_{g_k} ⋯ G^{2,x}_{g_2} G^{1,x}_{g_1} G^{2,x}_{g_2} ⋯ G^{k,x}_{g_k}`,

which is a POVM because each layer is conjugation by a projective measurement. It is the step that
lets answer reduction replace a measurement of a whole proof tuple by the product of measurements of
its pieces.

## The chain

The proof has three parts, and only the middle one is about sandwiches.

* **From evaluations to outcomes.** Two distinct functions of the family agree at a random point
  with probability at most `ε`. So when the evaluations disagree with probability `δ`, the
  outcomes themselves disagree with probability `η` satisfying `η (1 - ε) ≤ δ`, and since `η ≤ 1`
  this is `η ≤ δ + ε` with no case split (`one_sub_sum_bornProb_le_eval`). The only use of the
  independence of the point from the index is here: the Born probabilities do not see the point,
  so its average acts on the collision indicator alone.
* **One more layer of the sandwich** (`sqrt_sum_xSqNorm_sandStep_le`). Alice's joint element is
  the palindrome `A_g A_o A_g` of her two marginals, and three replacements move it to Bob's
  `G_g C_o G_g`: the right `A_g`, then `A_o`, then the left `A_g`. Each replacement multiplies a
  known deviation by a family whose squares sum to at most the identity, so it costs exactly that
  deviation (the paper's `fact:add-a-proj`). The three costs are added **as square roots**, by
  Minkowski's inequality in `ℓ²` over the index and the outcomes, and that is what keeps the error
  linear in `k`: the cruder `(a + b + c)² ≤ 3 (a² + b² + c²)` would multiply by three at every
  layer.
* **From a squared distance back to agreement.** When Alice's measurement is projective,
  `1 - ∑_g ⟨A_g ⊗ C_g⟩ ≤ (∑_g ‖(A_g ⊗ 1 - 1 ⊗ C_g) ψ‖²)^{1/2}`, whatever `C` is
  (`one_sub_sum_bornProb_le_sqrt`), and coarse-graining both sides by the evaluation map can only
  increase agreement (`sum_bornProb_le_fibSum_of_nonneg`).

## The constant

The paper states `k (δ + ε)^{1/2}` with an implicit constant. The one here is
`2 √2 k (δ + ε)^{1/2}`: the `2 √2` is the factor `2` of each layer (the new coordinate is replaced
twice) times the `√2` of passing from agreement to squared distance for a single coordinate.

## What the statement does not assume

The paper's outcome set for `A` is `𝒢_1 × ⋯ × 𝒢_k`; its consumer's measurement has function-valued
outcomes outside those families, and the paper's proof uses `A` only through its coordinate
coarse-grainings. The blueprint's answer is to extend each `G^{i,x}` by zero projectors to the full
alphabet, so here the outcome set of `A` is literally the product, and the families are arbitrary
finite types with an evaluation map. The point is drawn from an arbitrary distribution `ν`, not
necessarily uniform, and the collision bound is stated against it.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Minkowski's inequality for weighted sums of squares -/

section Minkowski

variable {J : Type*} [Fintype J]

/-- **Minkowski's inequality** for a weighted `ℓ²` sum: the square root of a weighted sum of squares
is a norm, so it satisfies the triangle inequality. -/
theorem sqrt_sum_weighted_sq_add_le (w f g : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Real.sqrt (∑ j, w j * (f j + g j) ^ 2)
      ≤ Real.sqrt (∑ j, w j * f j ^ 2) + Real.sqrt (∑ j, w j * g j ^ 2) := by
  have hF : 0 ≤ ∑ j, w j * f j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hG : 0 ≤ ∑ j, w j * g j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hcs := sum_weighted_mul_le_sqrt w f g hw
  have hexp : ∑ j, w j * (f j + g j) ^ 2
      = ∑ j, w j * f j ^ 2 + 2 * ∑ j, w j * (f j * g j) + ∑ j, w j * g j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Real.sqrt_le_left (by positivity), hexp, add_sq, Real.sq_sqrt hF, Real.sq_sqrt hG]
  linarith

/-- The three-term form, for a pointwise bound `d ≤ a + b + c` of a nonnegative `d`. -/
theorem sqrt_sum_weighted_sq_le_add3 {w d a b c : J → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hd : ∀ j, 0 ≤ d j) (hdabc : ∀ j, d j ≤ a j + b j + c j) :
    Real.sqrt (∑ j, w j * d j ^ 2)
      ≤ Real.sqrt (∑ j, w j * a j ^ 2) + Real.sqrt (∑ j, w j * b j ^ 2)
        + Real.sqrt (∑ j, w j * c j ^ 2) := by
  have hmono : ∑ j, w j * d j ^ 2 ≤ ∑ j, w j * ((a j + b j) + c j) ^ 2 :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hd j) (hdabc j) 2) (hw j)
  have h1 := sqrt_sum_weighted_sq_add_le w (fun j => a j + b j) c hw
  have h2 := sqrt_sum_weighted_sq_add_le w a b hw
  calc Real.sqrt (∑ j, w j * d j ^ 2)
      ≤ Real.sqrt (∑ j, w j * ((a j + b j) + c j) ^ 2) := Real.sqrt_le_sqrt hmono
    _ ≤ _ := by linarith

/-- A weighted sum of inner sums is a weighted sum over the pairs. -/
theorem sum_mul_sum_eq_sum_prod {X P : Type*} [Fintype X] [Fintype P] (μ : X → ℝ)
    (f : X → P → ℝ) : ∑ x, μ x * ∑ p, f x p = ∑ q : X × P, μ q.1 * f q.1 q.2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _

/-- The three-term form for a weight on an index and an unweighted inner sum: the shape of every
average over questions of a sum over outcomes. -/
theorem sqrt_wsum_le_add3 {X P : Type*} [Fintype X] [Fintype P] {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    {d a b c : X → P → ℝ} (hd : ∀ x p, 0 ≤ d x p)
    (hdabc : ∀ x p, d x p ≤ a x p + b x p + c x p) :
    Real.sqrt (∑ x, μ x * ∑ p, d x p ^ 2)
      ≤ Real.sqrt (∑ x, μ x * ∑ p, a x p ^ 2) + Real.sqrt (∑ x, μ x * ∑ p, b x p ^ 2)
        + Real.sqrt (∑ x, μ x * ∑ p, c x p ^ 2) := by
  rw [sum_mul_sum_eq_sum_prod μ fun x p => d x p ^ 2,
    sum_mul_sum_eq_sum_prod μ fun x p => a x p ^ 2,
    sum_mul_sum_eq_sum_prod μ fun x p => b x p ^ 2,
    sum_mul_sum_eq_sum_prod μ fun x p => c x p ^ 2]
  exact sqrt_sum_weighted_sq_le_add3 (w := fun q : X × P => μ q.1) (d := fun q => d q.1 q.2)
    (a := fun q => a q.1 q.2) (b := fun q => b q.1 q.2) (c := fun q => c q.1 q.2)
    (fun q => hμ q.1) (fun q => hd q.1 q.2) fun q => hdabc q.1 q.2

end Minkowski

/-! ## One layer of the sandwich -/

section Step

/-- **The algebra of one layer.** In any ring, if `a2 a1 = a`, `a a2 = a`, and Bob's `q`, `c`
commute with Alice's `a1`, `a2` as needed, then `a - q c q` is the sum of the three
replacements. -/
theorem sandStep_identity {R : Type*} [Ring R] {a a1 a2 q c : R} (h1 : a * a2 = a)
    (h2 : a2 * a1 = a) (hq1 : q * a1 = a1 * q) (hca : c * a2 = a2 * c) (hq2 : q * a2 = a2 * q) :
    a - q * c * q = a * (a2 - q) + a2 * q * (a1 - c) + q * c * (a2 - q) := by
  have e2 : a2 * q * a1 = a * q := by rw [mul_assoc, hq1, ← mul_assoc, h2]
  have e3 : q * c * a2 = a2 * q * c := by rw [mul_assoc, hca, ← mul_assoc, hq2]
  have hexp : a * (a2 - q) + a2 * q * (a1 - c) + q * c * (a2 - q)
      = a * a2 - a * q + (a2 * q * a1 - a2 * q * c) + (q * c * a2 - q * c * q) := by
    noncomm_ring
  rw [hexp, h1, e2, e3]
  abel

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {O K : Type*} [Fintype O] [DecidableEq O] [Fintype K] [DecidableEq K]

/-- A projective family's element is below the identity. -/
theorem IsPVM.le_one {ι N : Type*} [Fintype ι] [Fintype N] [DecidableEq N]
    {P : ι → Matrix N N ℂ} (h : IsPVM P) (i : ι) : P i ≤ 1 := by
  classical
  rw [← h.sum_eq_one]
  exact Finset.single_le_sum (fun j _ => h.nonneg j) (mem_univ i)

/-- A projective element, on either factor, is a contraction. -/
theorem IsPVM.aOp_contraction {ι : Type*} [Fintype ι] {P : ι → Matrix dA dA ℂ} (h : IsPVM P)
    (i : ι) : ((MIPRE.aOp (P i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * MIPRE.aOp (P i) ≤ 1 := by
  rw [aOp_conjTranspose, h.isSelfAdjoint, ← aOp_mul, h.idem, ← aOp_one (HA := dA) (HB := dB)]
  exact aOp_mono (h.le_one i)

theorem IsPVM.bOp_contraction {ι : Type*} [Fintype ι] {P : ι → Matrix dB dB ℂ} (h : IsPVM P)
    (i : ι) : ((MIPRE.bOp (P i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * MIPRE.bOp (P i) ≤ 1 := by
  rw [bOp_conjTranspose, h.isSelfAdjoint, ← bOp_mul, h.idem, ← bOp_one (HA := dA) (HB := dB)]
  exact bOp_mono (h.le_one i)

/-- A positive family on Bob's factor summing to the identity satisfies the hypothesis of
`sum_snorm_sq_mul_le`: `C† C = C² ≤ C`. -/
theorem sum_bOp_conjTranspose_mul_self_le_one_of_nonneg {C : O → Matrix dB dB ℂ}
    (hC0 : ∀ o, 0 ≤ C o) (hC1 : ∑ o, C o = 1) :
    ∑ o, ((bOp (C o) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * bOp (C o) ≤ 1 := by
  have hsa : ∀ o, (C o)ᴴ = C o := fun o => (Matrix.nonneg_iff_posSemidef.mp (hC0 o)).isHermitian
  rw [Finset.sum_congr rfl fun o (_ : o ∈ univ) => by rw [bOp_conjTranspose, hsa o, ← bOp_mul],
    ← bOp_sum, ← bOp_one (HA := dA) (HB := dB)]
  exact bOp_mono (sum_sq_le_one_of_sum_eq_one hC0 hC1)

/-- **One layer, at a single index.** The three families of squared deviations, each bounded by the
deviation it multiplies. -/
theorem sum_snorm_sq_sandStep_le (ψ : dA × dB → ℂ) {A : O × K → Matrix dA dA ℂ}
    {C : O → Matrix dB dB ℂ} {Q : K → Matrix dB dB ℂ} (hA : IsPVM A) (hC0 : ∀ o, 0 ≤ C o)
    (hC1 : ∑ o, C o = 1) (hQ : IsPVM Q) :
    (∑ p : O × K, snorm ψ ((aOp (A p) : Matrix (dA × dB) _ ℂ)
        * (aOp (∑ o', A (o', p.2)) - bOp (Q p.2))) ^ 2
      ≤ ∑ g, xSqNorm ψ (∑ o, A (o, g)) (Q g)) ∧
    (∑ p : O × K, snorm ψ ((aOp (∑ o', A (o', p.2)) : Matrix (dA × dB) _ ℂ) * bOp (Q p.2)
        * (aOp (∑ g', A (p.1, g')) - bOp (C p.1))) ^ 2
      ≤ ∑ o, xSqNorm ψ (∑ g, A (o, g)) (C o)) ∧
    (∑ p : O × K, snorm ψ ((bOp (Q p.2 * C p.1) : Matrix (dA × dB) _ ℂ)
        * (aOp (∑ o', A (o', p.2)) - bOp (Q p.2))) ^ 2
      ≤ ∑ g, xSqNorm ψ (∑ o, A (o, g)) (Q g)) := by
  classical
  have hA2 : IsPVM fun g => ∑ o, A (o, g) := hA.marg_right
  refine ⟨?_, ?_, ?_⟩
  · -- the family `aOp (A (o, g))` over `o`, at each `g`: a sub-family of a projective measurement
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_le_sum fun g _ => ?_
    rw [xSqNorm_eq_snorm_sq]
    have hall := sum_snorm_sq_mul_le ψ (fun p : O × K => (aOp (A p) : Matrix (dA × dB) _ ℂ))
      (le_of_eq (sum_aOp_conjTranspose_mul_self_of_isPVM hA))
      ((aOp (∑ o', A (o', g)) : Matrix (dA × dB) _ ℂ) - bOp (Q g))
    refine le_trans ?_ hall
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun g' => ∑ o, snorm ψ ((aOp (A (o, g')) :
        Matrix (dA × dB) _ ℂ) * (aOp (∑ o', A (o', g)) - bOp (Q g))) ^ 2)
      (fun g' _ => Finset.sum_nonneg fun o _ => sq_nonneg _) (mem_univ g)
  · -- the family `aOp (A_g) bOp (Q_g)` over `g`, at each `o`: a contraction, then a projective
    -- measurement
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun o _ => ?_
    rw [xSqNorm_eq_snorm_sq]
    set M : Matrix (dA × dB) (dA × dB) ℂ := aOp (∑ g', A (o, g')) - bOp (C o) with hM
    calc ∑ g, snorm ψ ((aOp (∑ o', A (o', g)) : Matrix (dA × dB) _ ℂ) * bOp (Q g) * M) ^ 2
        ≤ ∑ g, snorm ψ ((bOp (Q g) : Matrix (dA × dB) _ ℂ) * M) ^ 2 :=
          Finset.sum_le_sum fun g _ => by
            rw [Matrix.mul_assoc]
            exact snorm_sq_mul_le_of_contraction ψ (hA2.aOp_contraction g) _
      _ ≤ snorm ψ M ^ 2 :=
          sum_snorm_sq_mul_le ψ _ (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hQ)) M
  · -- the family `bOp (Q_g C_o)` over `o`, at each `g`: a contraction, then a POVM
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_le_sum fun g _ => ?_
    rw [xSqNorm_eq_snorm_sq]
    set M : Matrix (dA × dB) (dA × dB) ℂ := aOp (∑ o', A (o', g)) - bOp (Q g) with hM
    calc ∑ o, snorm ψ ((bOp (Q g * C o) : Matrix (dA × dB) _ ℂ) * M) ^ 2
        ≤ ∑ o, snorm ψ ((bOp (C o) : Matrix (dA × dB) _ ℂ) * M) ^ 2 :=
          Finset.sum_le_sum fun o _ => by
            rw [bOp_mul, Matrix.mul_assoc]
            exact snorm_sq_mul_le_of_contraction ψ (hQ.bOp_contraction g) _
      _ ≤ snorm ψ M ^ 2 :=
          sum_snorm_sq_mul_le ψ _ (sum_bOp_conjTranspose_mul_self_le_one_of_nonneg hC0 hC1) M

theorem snorm_add3_le {N : Type*} [Fintype N] (v : N → ℂ) (X Y Z : Matrix N N ℂ) :
    snorm v (X + Y + Z) ≤ snorm v X + snorm v Y + snorm v Z := by
  have h1 := snorm_add_le v (X + Y) Z
  have h2 := snorm_add_le v X Y
  linarith

/-- **The pointwise triangle inequality of one layer.** -/
theorem snorm_sandStep_le (ψ : dA × dB → ℂ) {A : O × K → Matrix dA dA ℂ}
    (C : O → Matrix dB dB ℂ) (Q : K → Matrix dB dB ℂ) (hA : IsPVM A) (o : O) (g : K) :
    snorm ψ ((aOp (A (o, g)) : Matrix (dA × dB) _ ℂ) - bOp (Q g * C o * Q g))
      ≤ snorm ψ ((aOp (A (o, g)) : Matrix (dA × dB) _ ℂ)
            * (aOp (∑ o', A (o', g)) - bOp (Q g)))
        + snorm ψ ((aOp (∑ o', A (o', g)) : Matrix (dA × dB) _ ℂ) * bOp (Q g)
            * (aOp (∑ g', A (o, g')) - bOp (C o)))
        + snorm ψ ((bOp (Q g * C o) : Matrix (dA × dB) _ ℂ)
            * (aOp (∑ o', A (o', g)) - bOp (Q g))) := by
  classical
  have hid := sandStep_identity (a := (aOp (A (o, g)) : Matrix (dA × dB) _ ℂ))
    (a1 := aOp (∑ g', A (o, g'))) (a2 := aOp (∑ o', A (o', g))) (q := bOp (Q g))
    (c := bOp (C o))
    (by
      rw [← aOp_mul]
      congr 1
      rw [Finset.mul_sum, Finset.sum_eq_single o (fun o' _ ho' => hA.orthogonal fun he =>
        ho' (Prod.mk.injEq .. ▸ he).1.symm) fun hmem => absurd (mem_univ o) hmem, hA.idem])
    (by rw [← aOp_mul, hA.marg_mul_marg])
    (aOp_mul_bOp _ _).symm (aOp_mul_bOp _ _).symm (aOp_mul_bOp _ _).symm
  rw [bOp_mul, bOp_mul, hid]
  exact snorm_add3_le ψ _ _ _

/-- **One layer of the sandwich**, averaged over an index. Alice's joint projective measurement
`A_{(o, g)}` is compared with Bob's `Q_g C_o Q_g`, where `C` is any POVM and `Q` is projective. The
error is the marginal's distance to `C` plus twice the other marginal's distance to `Q`, *added as
square roots*. -/
theorem sqrt_sum_xSqNorm_sandStep_le {X : Type*} [Fintype X] {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (ψ : dA × dB → ℂ) {A : X → O × K → Matrix dA dA ℂ} {C : X → O → Matrix dB dB ℂ}
    {Q : X → K → Matrix dB dB ℂ} (hA : ∀ x, IsPVM (A x)) (hC0 : ∀ x o, 0 ≤ C x o)
    (hC1 : ∀ x, ∑ o, C x o = 1) (hQ : ∀ x, IsPVM (Q x)) :
    Real.sqrt (∑ x, μ x * ∑ p : O × K, xSqNorm ψ (A x p) (Q x p.2 * C x p.1 * Q x p.2))
      ≤ Real.sqrt (∑ x, μ x * ∑ o, xSqNorm ψ (∑ g, A x (o, g)) (C x o))
        + 2 * Real.sqrt (∑ x, μ x * ∑ g, xSqNorm ψ (∑ o, A x (o, g)) (Q x g)) := by
  classical
  have hmink := sqrt_wsum_le_add3 hμ
    (d := fun x (p : O × K) => snorm ψ ((aOp (A x p) : Matrix (dA × dB) _ ℂ)
      - bOp (Q x p.2 * C x p.1 * Q x p.2)))
    (a := fun x p => snorm ψ ((aOp (A x p) : Matrix (dA × dB) _ ℂ)
      * (aOp (∑ o', A x (o', p.2)) - bOp (Q x p.2))))
    (b := fun x p => snorm ψ ((aOp (∑ o', A x (o', p.2)) : Matrix (dA × dB) _ ℂ) * bOp (Q x p.2)
      * (aOp (∑ g', A x (p.1, g')) - bOp (C x p.1))))
    (c := fun x p => snorm ψ ((bOp (Q x p.2 * C x p.1) : Matrix (dA × dB) _ ℂ)
      * (aOp (∑ o', A x (o', p.2)) - bOp (Q x p.2))))
    (fun x p => snorm_nonneg _ _) fun x p => snorm_sandStep_le ψ (C x) (Q x) (hA x) p.1 p.2
  have hlhs : ∑ x, μ x * ∑ p : O × K, xSqNorm ψ (A x p) (Q x p.2 * C x p.1 * Q x p.2)
      = ∑ x, μ x * ∑ p : O × K, snorm ψ ((aOp (A x p) : Matrix (dA × dB) _ ℂ)
          - bOp (Q x p.2 * C x p.1 * Q x p.2)) ^ 2 :=
    Finset.sum_congr rfl fun x _ => congrArg (μ x * ·)
      (Finset.sum_congr rfl fun p _ => xSqNorm_eq_snorm_sq _ _ _)
  have hb := fun x => sum_snorm_sq_sandStep_le ψ (hA x) (hC0 x) (hC1 x) (hQ x)
  have hwmono : ∀ {f g : X → ℝ}, (∀ x, f x ≤ g x) → ∑ x, μ x * f x ≤ ∑ x, μ x * g x :=
    fun h => Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x)
  have ha := Real.sqrt_le_sqrt (hwmono fun x => (hb x).1)
  have hb' := Real.sqrt_le_sqrt (hwmono fun x => (hb x).2.1)
  have hc := Real.sqrt_le_sqrt (hwmono fun x => (hb x).2.2)
  rw [hlhs]
  linarith

end Step

/-! ## The sandwich of `k` measurements -/

section KFold

universe u

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The sandwich of `k` measurements**,
`M^{k}_{g_k} ⋯ M^{2}_{g_2} M^{1}_{g_1} M^{2}_{g_2} ⋯ M^{k}_{g_k}`, with the last index outermost
as in the paper. The empty sandwich is the identity: the one-outcome POVM. -/
def sandK : {k : ℕ} → {G : Fin k → Type u} → ((i : Fin k) → G i → Matrix n n ℂ) →
    ((i : Fin k) → G i) → Matrix n n ℂ
  | 0, _, _, _ => 1
  | k + 1, _, M, g => M (Fin.last k) (g (Fin.last k))
      * sandK (fun i : Fin k => M i.castSucc) (Fin.init g) * M (Fin.last k) (g (Fin.last k))

theorem sandK_zero {G : Fin 0 → Type u} (M : (i : Fin 0) → G i → Matrix n n ℂ)
    (g : (i : Fin 0) → G i) : sandK M g = 1 := rfl

theorem sandK_succ {k : ℕ} {G : Fin (k + 1) → Type u} (M : (i : Fin (k + 1)) → G i → Matrix n n ℂ)
    (g : (i : Fin (k + 1)) → G i) :
    sandK M g = M (Fin.last k) (g (Fin.last k))
      * sandK (fun i : Fin k => M i.castSucc) (Fin.init g) * M (Fin.last k) (g (Fin.last k)) :=
  rfl

/-- The sandwich at a `snoc`: the new layer outside the old sandwich. -/
theorem sandK_snoc {k : ℕ} {G : Fin (k + 1) → Type u} (M : (i : Fin (k + 1)) → G i → Matrix n n ℂ)
    (o : (i : Fin k) → G i.castSucc) (c : G (Fin.last k)) :
    sandK M (Fin.snoc o c)
      = M (Fin.last k) c * sandK (fun i : Fin k => M i.castSucc) o * M (Fin.last k) c := by
  rw [sandK_succ, Fin.init_snoc, Fin.snoc_last]

/-- **A sandwich of projective measurements is positive.** Each layer is a conjugation by a
self-adjoint operator. -/
theorem sandK_nonneg : ∀ {k : ℕ} {G : Fin k → Type u} [∀ i, Fintype (G i)]
    {M : (i : Fin k) → G i → Matrix n n ℂ}, (∀ i, IsPVM (M i)) →
    ∀ g, (0 : Matrix n n ℂ) ≤ sandK M g
  | 0, _, _, _, _, _ => Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one
  | k + 1, _, _, M, hM, g => by
      rw [sandK_succ]
      have hS := Matrix.nonneg_iff_posSemidef.mp
        (sandK_nonneg (fun i : Fin k => hM i.castSucc) (Fin.init g))
      have h := hS.conjTranspose_mul_mul_same (M (Fin.last k) (g (Fin.last k)))
      rw [(hM (Fin.last k)).isSelfAdjoint] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h

/-- **A sandwich of projective measurements sums to the identity**: summing the outermost layer
first, `∑_c M_c S M_c = ∑_c M_c² = 1` once the inner sandwich `S` has summed to the identity. -/
theorem sum_sandK : ∀ {k : ℕ} {G : Fin k → Type u} [∀ i, Fintype (G i)]
    {M : (i : Fin k) → G i → Matrix n n ℂ}, (∀ i, IsPVM (M i)) → ∑ g, sandK M g = 1
  | 0, _, _, M, _ => by
      rw [Fintype.sum_subsingleton _ (fun i => Fin.elim0 i)]
      rfl
  | k + 1, G, _, M, hM => by
      have hS := sum_sandK (fun i : Fin k => hM i.castSucc)
      calc ∑ g, sandK M g
          = ∑ p : G (Fin.last k) × ((i : Fin k) → G i.castSucc), sandK M (Fin.snoc p.2 p.1) :=
            (Fintype.sum_equiv (Fin.snocEquiv G) _ _ fun p => rfl).symm
        _ = ∑ c, ∑ o, M (Fin.last k) c * sandK (fun i : Fin k => M i.castSucc) o
              * M (Fin.last k) c := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun o _ => sandK_snoc M o c
        _ = ∑ c, M (Fin.last k) c * M (Fin.last k) c := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← Finset.sum_mul, ← Finset.mul_sum, hS, Matrix.mul_one]
        _ = 1 := by
            rw [Finset.sum_congr rfl fun c _ => (hM (Fin.last k)).idem c]
            exact (hM (Fin.last k)).sum_eq_one

end KFold

/-! ## Coarse-graining along a bijection, a marginal, and a composite -/

section FibSum

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Coarse-graining does not see a relabelling of the outcomes by a bijection. -/
theorem fibSum_comp_equiv {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (G : β → Matrix N N ℂ) (e : α ≃ β) (f : β → γ) (c : γ) :
    fibSum (fun a => G (e a)) (fun a => f (e a)) c = fibSum G f c := by
  unfold fibSum
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Fintype.sum_equiv e _ _ fun a => rfl

/-- Coarse-graining a marginal is coarse-graining the joint family. -/
theorem fibSum_marg_left {O K γ : Type*} [Fintype O] [Fintype K] [DecidableEq γ]
    (A : O × K → Matrix N N ℂ) (h : O → γ) (c : γ) :
    fibSum (fun o => ∑ k, A (o, k)) h c = fibSum A (fun p => h p.1) c := by
  unfold fibSum
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hc : h o = c
  · simp only [hc, if_true]
  · simp only [hc, if_false, Finset.sum_const_zero]

/-- The coarse-graining along the second projection is the marginal. -/
theorem fibSum_snd {O K : Type*} [Fintype O] [Fintype K] [DecidableEq K]
    (A : O × K → Matrix N N ℂ) (c : K) : fibSum A (fun p => p.2) c = ∑ o, A (o, c) := by
  unfold fibSum
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp

/-- Coarse-graining twice is coarse-graining along the composite. -/
theorem fibSum_fibSum {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (G : α → Matrix N N ℂ) (f : α → β) (h : β → γ) (c : γ) :
    fibSum (fibSum G f) h c = fibSum G (fun a => h (f a)) c := by
  unfold fibSum
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_fiberwise (univ : Finset α) f (fun a => if h (f a) = c then G a else 0)]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : h b = c
  · rw [if_pos hb]
    exact Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2, if_pos hb]
  · rw [if_neg hb]
    exact (Finset.sum_eq_zero fun a ha => by rw [(Finset.mem_filter.mp ha).2, if_neg hb]).symm

end FibSum

/-! ## The `k`-fold sandwich, at the level of outcomes -/

section KFoldBound

universe u

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {X : Type*} [Fintype X]

/-- **The `k`-fold sandwich, at the level of outcomes** (NW19's Fact 4.33, averaged over an index,
in the squared-distance form). Alice's projective measurement of a `k`-tuple is compared with Bob's
sandwich of his `k` projective measurements: the error, as a square root, is at most twice the sum
of the square roots of the `k` coordinate errors. Induction on `k`, peeling the outermost layer with
`sqrt_sum_xSqNorm_sandStep_le`. -/
theorem sqrt_sum_xSqNorm_sandK_le {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ) :
    ∀ {k : ℕ} {G : Fin k → Type u} [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]
      {A : X → ((i : Fin k) → G i) → Matrix dA dA ℂ}
      {M : (i : Fin k) → X → G i → Matrix dB dB ℂ},
      (∀ x, IsPVM (A x)) → (∀ i x, IsPVM (M i x)) →
      Real.sqrt (∑ x, μ x * ∑ g, xSqNorm ψ (A x g) (sandK (fun i => M i x) g))
        ≤ 2 * ∑ i, Real.sqrt (∑ x, μ x * ∑ c,
          xSqNorm ψ (fibSum (A x) (fun g => g i) c) (M i x c))
  | 0, _, _, _, A, M, hA, _ => by
      have hA1 : ∀ x g, A x g = 1 := fun x g => by
        have h := (hA x).sum_eq_one
        rwa [Fintype.sum_subsingleton _ g] at h
      have hzero : ∀ x g, xSqNorm ψ (A x g) (sandK (fun i => M i x) g) = 0 := fun x g => by
        rw [hA1 x g, sandK_zero, xSqNorm_eq_snorm_sq, aOp_one, bOp_one, sub_self]
        simp [snorm]
      simp [hzero]
  | k + 1, G, _, _, A, M, hA, hM => by
      classical
      -- split the outcome as (inner tuple, last coordinate)
      let e : ((i : Fin k) → G i.castSucc) × G (Fin.last k) ≃ ((i : Fin (k + 1)) → G i) :=
        (Equiv.prodComm _ _).trans (Fin.snocEquiv G)
      have hA' : ∀ x, IsPVM fun p => A x (e p) := fun x => (hA x).comp_equiv e
      have hA1 : ∀ x, IsPVM fun o => ∑ c, A x (e (o, c)) := fun x => (hA' x).marg_left
      -- the induction hypothesis, for the marginal on the inner tuple
      have hIH := sqrt_sum_xSqNorm_sandK_le hμ ψ (G := fun i : Fin k => G i.castSucc)
        (A := fun x o => ∑ c, A x (e (o, c))) (M := fun i => M i.castSucc) hA1
        (fun i x => hM i.castSucc x)
      -- one more layer
      have hstep := sqrt_sum_xSqNorm_sandStep_le hμ ψ (A := fun x p => A x (e p))
        (C := fun x o => sandK (fun i : Fin k => M i.castSucc x) o)
        (Q := fun x => M (Fin.last k) x) hA'
        (fun x o => sandK_nonneg (fun i : Fin k => hM i.castSucc x) o)
        (fun x => sum_sandK (fun i : Fin k => hM i.castSucc x)) (fun x => hM (Fin.last k) x)
      -- the left side is the step's left side
      have hlhs : ∀ x, ∑ g, xSqNorm ψ (A x g) (sandK (fun i => M i x) g)
          = ∑ p : ((i : Fin k) → G i.castSucc) × G (Fin.last k),
              xSqNorm ψ (A x (e p)) (M (Fin.last k) x p.2
                * sandK (fun i : Fin k => M i.castSucc x) p.1 * M (Fin.last k) x p.2) := by
        intro x
        refine (Fintype.sum_equiv e _ _ fun p => ?_).symm
        rw [show e p = Fin.snoc p.1 p.2 from rfl, sandK_snoc]
      -- the two marginals, in terms of the coordinates of `A`
      have hlast : ∀ x c, ∑ o, A x (e (o, c)) = fibSum (A x) (fun g => g (Fin.last k)) c := by
        intro x c
        rw [← fibSum_snd (fun p => A x (e p)) c,
          ← fibSum_comp_equiv (A x) e (fun g => g (Fin.last k)) c]
        congr 1
        funext p
        exact (Fin.snoc_last (α := G) p.2 p.1).symm
      have hinit : ∀ x (i : Fin k) c, fibSum (fun o => ∑ c', A x (e (o, c'))) (fun o => o i) c
          = fibSum (A x) (fun g => g i.castSucc) c := by
        intro x i c
        rw [fibSum_marg_left (fun p => A x (e p)) (fun o => o i) c,
          ← fibSum_comp_equiv (A x) e (fun g => g i.castSucc) c]
        congr 1
        funext p
        exact (Fin.snoc_castSucc (α := G) p.2 p.1 i).symm
      simp only [hlhs] at *
      simp only [hlast, hinit] at hstep hIH
      rw [Fin.sum_univ_castSucc, mul_add]
      linarith

end KFoldBound

/-! ## From agreement to squared distance and back -/

section Agreement

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The Born probabilities of two families that each sum to the identity add up to one. -/
theorem sum_sum_bornProb_eq_one {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {Λ' : Type*}
    [Fintype Λ'] {P : Λ → Matrix dA dA ℂ} {Q : Λ' → Matrix dB dB ℂ} (hP : ∑ a, P a = 1)
    (hQ : ∑ b, Q b = 1) : ∑ a, ∑ b, bornProb ψ (P a) (Q b) = 1 := by
  have h : bornProb ψ (∑ a, P a) (∑ b, Q b) = ∑ a, ∑ b, bornProb ψ (P a) (Q b) := by
    rw [bornProb_sum_left]
    exact Finset.sum_congr rfl fun a _ => bornProb_sum_right ψ univ (P a) Q
  rw [← h, hP, hQ, bornProb_eq_qform, aOp_one, bOp_one, Matrix.mul_one, qform_one _ hψ]

/-- **A squared distance to a projective measurement bounds the disagreement**, whatever the other
family is (NW19's Fact 4.14, item 3, with constant one). The mass `1 = ∑_a ‖(P_a ⊗ 1) ψ‖²` minus
the agreement is a sum of cross terms `⟨(P_a ⊗ 1) ψ, (P_a ⊗ 1 - 1 ⊗ C_a) ψ⟩`, and one
Cauchy--Schwarz over the outcomes bounds it. -/
theorem one_sub_sum_bornProb_le_sqrt {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {P : Λ → Matrix dA dA ℂ} (hP : IsPVM P) (C : Λ → Matrix dB dB ℂ) :
    1 - ∑ a, bornProb ψ (P a) (C a) ≤ Real.sqrt (∑ a, xSqNorm ψ (P a) (C a)) := by
  have hmass : ∑ a, snorm ψ (aOp (P a) : Matrix (dA × dB) _ ℂ) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [snorm_sq_eq_qform, aOp_conjTranspose, hP.isSelfAdjoint, ← aOp_mul, hP.idem],
      ← qform_sum, ← aOp_sum, hP.sum_eq_one, aOp_one, qform_one _ hψ]
  have hterm : ∀ a, snorm ψ (aOp (P a) : Matrix (dA × dB) _ ℂ) ^ 2 - bornProb ψ (P a) (C a)
      = qform ψ (((aOp (P a) : Matrix (dA × dB) _ ℂ))ᴴ * (aOp (P a) - bOp (C a))) := by
    intro a
    rw [snorm_sq_eq_qform, bornProb_eq_qform, Matrix.mul_sub, qform_sub, aOp_conjTranspose,
      hP.isSelfAdjoint]
  have hsum : 1 - ∑ a, bornProb ψ (P a) (C a)
      = ∑ a, qform ψ (((aOp (P a) : Matrix (dA × dB) _ ℂ))ᴴ * (aOp (P a) - bOp (C a))) := by
    rw [← hmass, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => hterm a
  rw [hsum]
  calc ∑ a, qform ψ (((aOp (P a) : Matrix (dA × dB) _ ℂ))ᴴ * (aOp (P a) - bOp (C a)))
      ≤ ∑ a, snorm ψ (aOp (P a) : Matrix (dA × dB) _ ℂ)
          * snorm ψ ((aOp (P a) : Matrix (dA × dB) _ ℂ) - bOp (C a)) :=
        Finset.sum_le_sum fun a _ =>
          le_trans (le_abs_self _) (abs_qform_conjTranspose_mul_le ψ _ _)
    _ ≤ Real.sqrt (∑ a, snorm ψ (aOp (P a) : Matrix (dA × dB) _ ℂ) ^ 2)
          * Real.sqrt (∑ a, snorm ψ ((aOp (P a) : Matrix (dA × dB) _ ℂ) - bOp (C a)) ^ 2) :=
        sum_mul_le_sqrt _ _
    _ = Real.sqrt (∑ a, xSqNorm ψ (P a) (C a)) := by
        rw [hmass, Real.sqrt_one, one_mul]
        congr 1
        exact Finset.sum_congr rfl fun a _ => (xSqNorm_eq_snorm_sq ψ (P a) (C a)).symm

/-- **Coarse-graining two positive families the same way only adds agreement.** The added terms are
Born probabilities of positive operators; no projectivity is needed, unlike
`sum_bornProb_le_fibSum`. -/
theorem sum_bornProb_le_fibSum_of_nonneg (ψ : dA × dB → ℂ) {β : Type*} [Fintype β] [DecidableEq β]
    {P : Λ → Matrix dA dA ℂ} {Q : Λ → Matrix dB dB ℂ} (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a)
    (e : Λ → β) :
    ∑ a, bornProb ψ (P a) (Q a) ≤ ∑ b, bornProb ψ (fibSum P e b) (fibSum Q e b) := by
  have hfib : ∀ b : β, bornProb ψ (fibSum P e b) (fibSum Q e b)
      = ∑ a ∈ univ.filter fun a => e a = b, ∑ a' ∈ univ.filter fun a' => e a' = b,
          bornProb ψ (P a) (Q a') := fun b => by rw [fibSum, fibSum, bornProb_sum_sum]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hfib b]
  have hdiag : ∀ b : β, ∑ a ∈ univ.filter fun a => e a = b, bornProb ψ (P a) (Q a)
      ≤ ∑ a ∈ univ.filter fun a => e a = b, ∑ a' ∈ univ.filter fun a' => e a' = b,
          bornProb ψ (P a) (Q a') := fun b =>
    Finset.sum_le_sum fun a ha => Finset.single_le_sum
      (fun a' _ => bornProb_nonneg ψ (Matrix.nonneg_iff_posSemidef.mp (hP a))
        (Matrix.nonneg_iff_posSemidef.mp (hQ a'))) ha
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun b (_ : b ∈ univ) => hdiag b)
  exact (Finset.sum_fiberwise (univ : Finset Λ) e fun a => bornProb ψ (P a) (Q a)).symm

/-- **From evaluations to outcomes.** Two projective measurements with the same outcome set, whose
outcomes are separated by an evaluation map at a point drawn from `ν` (distinct outcomes collide
with probability at most `ε`): their disagreement is at most the average disagreement of the
evaluated measurements, plus `ε`.

With `η` the disagreement of the outcomes, the evaluated disagreement is at least `(1 - ε) η`,
because the Born probabilities do not depend on the point and every disagreeing pair of outcomes is
separated with probability at least `1 - ε`. Since `η ≤ 1`, this gives `η ≤ δ + ε`. -/
theorem one_sub_sum_bornProb_le_eval {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {Y R : Type*} [Fintype Y] [Fintype R] [DecidableEq R]
    {P : Λ → Matrix dA dA ℂ} {Q : Λ → Matrix dB dB ℂ} (hP : IsPVM P) (hQ : IsPVM Q)
    {ν : Y → ℝ} (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (ev : Y → Λ → R) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsep : ∀ g g' : Λ, g ≠ g' → ∑ y, ν y * (if ev y g = ev y g' then 1 else 0) ≤ ε) :
    1 - ∑ g, bornProb ψ (P g) (Q g)
      ≤ ∑ y, ν y * (1 - ∑ r, bornProb ψ (fibSum P (ev y) r) (fibSum Q (ev y) r)) + ε := by
  have hβ0 : ∀ g g', 0 ≤ bornProb ψ (P g) (Q g') := fun g g' =>
    bornProb_nonneg ψ (hP.posSemidef g) (hQ.posSemidef g')
  have hβ1 : ∑ g, ∑ g', bornProb ψ (P g) (Q g') = 1 :=
    sum_sum_bornProb_eq_one hψ hP.sum_eq_one hQ.sum_eq_one
  -- the evaluated disagreement at one point, as a sum over pairs of outcomes
  have hfib : ∀ y, 1 - ∑ r, bornProb ψ (fibSum P (ev y) r) (fibSum Q (ev y) r)
      = ∑ g, ∑ g', (if ev y g = ev y g' then 0 else 1) * bornProb ψ (P g) (Q g') := by
    intro y
    have hagree : ∑ r, bornProb ψ (fibSum P (ev y) r) (fibSum Q (ev y) r)
        = ∑ g, ∑ g', (if ev y g = ev y g' then 1 else 0) * bornProb ψ (P g) (Q g') := by
      rw [Finset.sum_congr rfl fun r (_ : r ∈ univ) => by rw [fibSum, fibSum, bornProb_sum_sum],
        ← sum_fiber (ev y) fun r g =>
          ∑ g' ∈ univ.filter fun g' => ev y g' = r, bornProb ψ (P g) (Q g')]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun g' _ => ?_
      by_cases h : ev y g' = ev y g
      · rw [if_pos h, if_pos h.symm, one_mul]
      · rw [if_neg h, if_neg (Ne.symm h), zero_mul]
    have hpt : ∀ g g', (if ev y g = ev y g' then (0 : ℝ) else 1) * bornProb ψ (P g) (Q g')
        = bornProb ψ (P g) (Q g')
          - (if ev y g = ev y g' then 1 else 0) * bornProb ψ (P g) (Q g') := by
      intro g g'
      split_ifs <;> ring
    rw [hagree]
    simp only [hpt, Finset.sum_sub_distrib, hβ1]
  -- the disagreement of the outcomes
  have hdiag : 1 - ∑ g, bornProb ψ (P g) (Q g)
      = ∑ g, ∑ g', (if g = g' then 0 else 1) * bornProb ψ (P g) (Q g') := by
    have h1 : ∀ g, ∑ g', (if g = g' then (0 : ℝ) else 1) * bornProb ψ (P g) (Q g')
        = ∑ g', bornProb ψ (P g) (Q g') - bornProb ψ (P g) (Q g) := by
      intro g
      have hsplit : ∀ g', (if g = g' then (0 : ℝ) else 1) * bornProb ψ (P g) (Q g')
          = bornProb ψ (P g) (Q g') - (if g = g' then bornProb ψ (P g) (Q g') else 0) := by
        intro g'
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun g' _ => hsplit g', Finset.sum_sub_distrib, Finset.sum_ite_eq,
        if_pos (mem_univ g)]
    rw [Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_sub_distrib, hβ1]
  -- average over the point
  have havg : ∑ y, ν y * (1 - ∑ r, bornProb ψ (fibSum P (ev y) r) (fibSum Q (ev y) r))
      = ∑ g, ∑ g', (∑ y, ν y * (if ev y g = ev y g' then 0 else 1))
          * bornProb ψ (P g) (Q g') := by
    simp only [hfib, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  -- every disagreeing pair of outcomes is separated with probability at least `1 - ε`
  have hcoef : ∀ g g' : Λ, (if g = g' then (0 : ℝ) else 1) * (1 - ε)
      ≤ ∑ y, ν y * (if ev y g = ev y g' then 0 else 1) := by
    intro g g'
    by_cases h : g = g'
    · rw [if_pos h, zero_mul]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (hν0 y) (by split_ifs <;> norm_num)
    · rw [if_neg h, one_mul]
      have hs := hsep g g' h
      have hpt : ∀ y, ν y * (if ev y g = ev y g' then (0 : ℝ) else 1)
          = ν y - ν y * (if ev y g = ev y g' then 1 else 0) := by
        intro y
        split_ifs <;> ring
      have hcompl : ∑ y, ν y * (if ev y g = ev y g' then (0 : ℝ) else 1)
          = 1 - ∑ y, ν y * (if ev y g = ev y g' then 1 else 0) := by
        simp only [hpt, Finset.sum_sub_distrib, hν1]
      linarith
  have hlow : (1 - ε) * (∑ g, ∑ g', (if g = g' then (0 : ℝ) else 1) * bornProb ψ (P g) (Q g'))
      ≤ ∑ y, ν y * (1 - ∑ r, bornProb ψ (fibSum P (ev y) r) (fibSum Q (ev y) r)) := by
    rw [havg, Finset.mul_sum]
    refine Finset.sum_le_sum fun g _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun g' _ => ?_
    have h := mul_le_mul_of_nonneg_right (hcoef g g') (hβ0 g g')
    linarith
  have hη1 : ∑ g, ∑ g', (if g = g' then (0 : ℝ) else 1) * bornProb ψ (P g) (Q g') ≤ 1 := by
    calc ∑ g, ∑ g', (if g = g' then (0 : ℝ) else 1) * bornProb ψ (P g) (Q g')
        ≤ ∑ g, ∑ g', bornProb ψ (P g) (Q g') :=
          Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun g' _ => by
            have := hβ0 g g'
            split_ifs <;> linarith
      _ = 1 := hβ1
  rw [hdiag]
  have hprod := mul_nonneg hε (sub_nonneg.mpr hη1)
  nlinarith

end Agreement

/-! ## The low-degree sandwich -/

section Main

universe u

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The low-degree sandwich** (blueprint `lem:ar-sandwich-support`; the paper's `lem:ld-sandwich`;
NW19's Fact 4.34 with an index).

An index `x` is drawn from `μ` and a point `y` from `ν`, independently. Alice measures `A^x`,
projective, with outcome a tuple `g` whose `i`-th coordinate lies in a finite family `G i`; Bob has,
for each `i`, a projective measurement `M i x` of the `i`-th coordinate. The families are separated
by their evaluation maps `ev i y`: distinct members collide at `y ∼ ν` with probability at most `ε`.
If, for every coordinate, Alice's evaluated coordinate disagrees with Bob's evaluated measurement
with probability at most `δ`, then Alice's evaluated tuple disagrees with the evaluated sandwich
`sandK (M · x)` with probability at most `2 √2 k (δ + ε)^{1/2}`. -/
theorem one_sub_sum_bornProb_ldSandwich_le {X Y : Type*} [Fintype X] [Fintype Y]
    {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    {ν : Y → ℝ} (hν0 : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1)
    {k : ℕ} {G : Fin k → Type u} {R : Fin k → Type*} [∀ i, Fintype (G i)]
    [∀ i, DecidableEq (G i)] [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    (ev : (i : Fin k) → Y → G i → R i) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hsep : ∀ i (g g' : G i), g ≠ g' →
      ∑ y, ν y * (if ev i y g = ev i y g' then 1 else 0) ≤ ε)
    {A : X → ((i : Fin k) → G i) → Matrix dA dA ℂ}
    {M : (i : Fin k) → X → G i → Matrix dB dB ℂ}
    (hA : ∀ x, IsPVM (A x)) (hM : ∀ i x, IsPVM (M i x))
    (hcons : ∀ i, ∑ x, μ x * ∑ y, ν y * (1 - ∑ r,
      bornProb ψ (fibSum (A x) (fun g => ev i y (g i)) r) (fibSum (M i x) (ev i y) r)) ≤ δ) :
    ∑ x, μ x * ∑ y, ν y * (1 - ∑ a,
      bornProb ψ (fibSum (A x) (fun g i => ev i y (g i)) a)
        (fibSum (sandK fun i => M i x) (fun g i => ev i y (g i)) a))
      ≤ 2 * Real.sqrt 2 * k * Real.sqrt (δ + ε) := by
  classical
  -- the coordinate marginals of `A`, projective
  have hAi : ∀ i x, IsPVM (fibSum (A x) fun g => g i) := fun i x => isPVM_fibSum (hA x) _
  -- each coordinate: outcome-level disagreement from the evaluated one
  have hη : ∀ i, ∑ x, μ x * (1 - ∑ c, bornProb ψ (fibSum (A x) (fun g => g i) c) (M i x c))
      ≤ δ + ε := by
    intro i
    have hx : ∀ x, 1 - ∑ c, bornProb ψ (fibSum (A x) (fun g => g i) c) (M i x c)
        ≤ ∑ y, ν y * (1 - ∑ r, bornProb ψ (fibSum (A x) (fun g => ev i y (g i)) r)
            (fibSum (M i x) (ev i y) r)) + ε := by
      intro x
      have h := one_sub_sum_bornProb_le_eval hψ (hAi i x) (hM i x) hν0 hν1 (ev i) hε (hsep i)
      simp only [fibSum_fibSum] at h
      exact h
    calc ∑ x, μ x * (1 - ∑ c, bornProb ψ (fibSum (A x) (fun g => g i) c) (M i x c))
        ≤ ∑ x, μ x * (∑ y, ν y * (1 - ∑ r, bornProb ψ (fibSum (A x) (fun g => ev i y (g i)) r)
            (fibSum (M i x) (ev i y) r)) + ε) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hx x) (hμ0 x)
      _ = ∑ x, μ x * ∑ y, ν y * (1 - ∑ r, bornProb ψ (fibSum (A x) (fun g => ev i y (g i)) r)
            (fibSum (M i x) (ev i y) r)) + ε := by
          rw [Finset.sum_congr rfl fun x _ => mul_add (μ x) _ ε, Finset.sum_add_distrib,
            ← Finset.sum_mul, hμ1, one_mul]
      _ ≤ δ + ε := by linarith [hcons i]
  -- each coordinate: squared distance twice the disagreement
  have he : ∀ i, ∑ x, μ x * ∑ c, xSqNorm ψ (fibSum (A x) (fun g => g i) c) (M i x c)
      ≤ 2 * (δ + ε) := by
    intro i
    have hx : ∀ x, ∑ c, xSqNorm ψ (fibSum (A x) (fun g => g i) c) (M i x c)
        = 2 * (1 - ∑ c, bornProb ψ (fibSum (A x) (fun g => g i) c) (M i x c)) := by
      intro x
      rw [one_sub_sum_bornProb_eq hψ (hAi i x) (hM i x)]
      ring
    rw [Finset.sum_congr rfl fun x _ => by rw [hx x], ]
    calc ∑ x, μ x * (2 * (1 - ∑ c, bornProb ψ (fibSum (A x) (fun g => g i) c) (M i x c)))
        = 2 * ∑ x, μ x * (1 - ∑ c, bornProb ψ (fibSum (A x) (fun g => g i) c) (M i x c)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ 2 * (δ + ε) := by linarith [hη i]
  -- the `k`-fold sandwich at the level of outcomes
  have hKbound : Real.sqrt (∑ x, μ x * ∑ g, xSqNorm ψ (A x g) (sandK (fun i => M i x) g))
      ≤ 2 * Real.sqrt 2 * k * Real.sqrt (δ + ε) := by
    refine le_trans (sqrt_sum_xSqNorm_sandK_le hμ0 ψ hA hM) ?_
    have hsum : ∑ i : Fin k, Real.sqrt (∑ x, μ x * ∑ c,
          xSqNorm ψ (fibSum (A x) (fun g => g i) c) (M i x c))
        ≤ ∑ _i : Fin k, Real.sqrt 2 * Real.sqrt (δ + ε) :=
      Finset.sum_le_sum fun i _ => by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (he i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    linarith
  -- outcome-level agreement, at each index, then averaged by Jensen
  have hout : ∑ x, μ x * (1 - ∑ g, bornProb ψ (A x g) (sandK (fun i => M i x) g))
      ≤ Real.sqrt (∑ x, μ x * ∑ g, xSqNorm ψ (A x g) (sandK (fun i => M i x) g)) := by
    calc ∑ x, μ x * (1 - ∑ g, bornProb ψ (A x g) (sandK (fun i => M i x) g))
        ≤ ∑ x, μ x * Real.sqrt (∑ g, xSqNorm ψ (A x g) (sandK (fun i => M i x) g)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (one_sub_sum_bornProb_le_sqrt hψ (hA x) _) (hμ0 x)
      _ ≤ _ := sum_weighted_sqrt_le μ _ hμ0 hμ1 fun x =>
          Finset.sum_nonneg fun g _ => xSqNorm_nonneg _ _ _
  -- evaluating both sides only adds agreement
  have heval : ∀ x y, 1 - ∑ a, bornProb ψ (fibSum (A x) (fun g i => ev i y (g i)) a)
        (fibSum (sandK fun i => M i x) (fun g i => ev i y (g i)) a)
      ≤ 1 - ∑ g, bornProb ψ (A x g) (sandK (fun i => M i x) g) := by
    intro x y
    have h := sum_bornProb_le_fibSum_of_nonneg ψ (fun g => (hA x).nonneg g)
      (fun g => sandK_nonneg (fun i => hM i x) g) (fun g i => ev i y (g i))
    linarith
  calc ∑ x, μ x * ∑ y, ν y * (1 - ∑ a,
        bornProb ψ (fibSum (A x) (fun g i => ev i y (g i)) a)
          (fibSum (sandK fun i => M i x) (fun g i => ev i y (g i)) a))
      ≤ ∑ x, μ x * ∑ y, ν y * (1 - ∑ g, bornProb ψ (A x g) (sandK (fun i => M i x) g)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (heval x y) (hν0 y)) (hμ0 x)
    _ = ∑ x, μ x * (1 - ∑ g, bornProb ψ (A x g) (sandK (fun i => M i x) g)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_mul, hν1, one_mul]
    _ ≤ 2 * Real.sqrt 2 * k * Real.sqrt (δ + ε) := le_trans hout hKbound

end Main

end MIPRE
