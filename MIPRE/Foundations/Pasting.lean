/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Sandwich

/-!
# Pasting two measurements into one

The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's
`lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds
two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with
`A`'s two marginals. The conclusion is that `A` agrees with the **sandwich**
`J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes.

Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are
proved first.

* **A sub-measurement close to a projective measurement carries almost all the mass**
  (`qform_sum_ge_of_close`, NW19's Fact 4.31). Two Cauchy--Schwarz steps against the same
  deviation, and the loss is `2 sqrt(delta)`.
* **Multiplying by the projector of the same outcome costs nothing** (`sum_snorm_sq_cool`, the
  paper's `lem:cool-closeness-fact` in its partition form). The cross terms vanish by mutual
  orthogonality and each diagonal term loses only `A_a <= Id`. The partition form is what matters:
  the consumers apply it to the `q` fibres of an outcome map at once, and the single-subset form
  would cost a factor `q` there.

The sandwich is where a **collision probability** enters. `G_2^{g_2} G_1 G_2^{g_2}` summed over a
fibre of `g_2 |-> g_2(y)` is a *pinching* of `G_1` by that fibre, not a conjugation by the fibre's
projector, and the difference is the cross terms `g_2 \ne g_2'` with `g_2(y) = g_2'(y)`. Those are
rare exactly when the outcome map separates the family, which for line polynomials is
Schwartz--Zippel.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Two small facts about the quadratic form -/

section QF

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem dotProduct_star_comm (u w : N → ℂ) : star u ⬝ᵥ w = star (star w ⬝ᵥ u) := by
  rw [dotProduct, dotProduct, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul']
  simp [Pi.star_apply, mul_comm]

/-- The quadratic form does not see the adjoint: it is a real part, and the adjoint conjugates. -/
theorem qform_conjTranspose (v : N → ℂ) (M : Matrix N N ℂ) : qform v (Mᴴ) = qform v M := by
  have h0 := star_mulVec_dotProduct M (1 : Matrix N N ℂ) v
  rw [Matrix.mul_one, Matrix.one_mulVec] at h0
  rw [qform, qform, ← h0, dotProduct_star_comm (M *ᵥ v) v, RCLike.star_def, Complex.conj_re,
    dotProduct_star_comm v (M *ᵥ v), RCLike.star_def, Complex.conj_re]

/-- A positive operator below the identity has `M^2 <= M`, so a family of positive operators
summing to the identity has its squares summing to at most the identity. -/
theorem sum_sq_le_one_of_sum_eq_one {C : Type*} [Fintype C] {P : C → Matrix N N ℂ}
    (hP0 : ∀ c, (0 : Matrix N N ℂ) ≤ P c) (hPsum : ∑ c, P c = 1) :
    ∑ c, (P c) * (P c) ≤ (1 : Matrix N N ℂ) := by
  classical
  have hP1 : ∀ c, P c ≤ (1 : Matrix N N ℂ) := fun c =>
    le_trans (Finset.single_le_sum (fun c' _ => hP0 c') (mem_univ c)) (le_of_eq hPsum)
  calc ∑ c, (P c) * (P c) ≤ ∑ c, P c :=
        Finset.sum_le_sum fun c _ => mul_self_le_of_le_one (hP0 c) (hP1 c)
    _ = 1 := hPsum

end QF

section Mass

variable {N : Type*} [Fintype N] [DecidableEq N] {C : Type*} [Fintype C] [DecidableEq C]

/-! ## A sub-measurement close to a projective measurement -/

/-- **NW19's Fact 4.31.** A family of positive operators summing to at most the identity, which is
`delta`-close to a projective measurement on a state, carries all but `2 sqrt(delta)` of the mass.
Two Cauchy--Schwarz steps against the same deviation: one moves from `1` to `sum <M_c P_c>`, the
other from there to `sum <P_c^2>`, and `P_c^2 <= P_c`. -/
theorem qform_sum_ge_of_close {v : N → ℂ} (hv : ‖evec v‖ = 1) {M P : C → Matrix N N ℂ}
    (hM : IsPVM M) (hP0 : ∀ c, (0 : Matrix N N ℂ) ≤ P c)
    (hPsum : ∑ c, P c ≤ (1 : Matrix N N ℂ))
    {δ : ℝ} (hclose : ∑ c, snorm v (M c - P c) ^ 2 ≤ δ) :
    1 - 2 * Real.sqrt δ ≤ ∑ c, qform v (P c) := by
  classical
  have hPsa : ∀ c, (P c)ᴴ = P c := fun c =>
    (Matrix.nonneg_iff_posSemidef.mp (hP0 c)).isHermitian
  have hP1 : ∀ c, P c ≤ (1 : Matrix N N ℂ) := fun c =>
    le_trans (Finset.single_le_sum (fun c' _ => hP0 c') (mem_univ c)) hPsum
  have hδ0 : 0 ≤ δ := le_trans (Finset.sum_nonneg fun c _ => sq_nonneg _) hclose
  -- the three mass sums
  have hMmass : ∑ c, snorm v (M c) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [snorm_sq_eq_qform, hM.isSelfAdjoint c, hM.idem c], ← qform_sum, hM.sum_eq_one,
      qform_one v hv]
  have hPtotal : ∑ c, qform v (P c) ≤ 1 := by
    rw [← qform_sum, ← qform_one v hv]
    exact qform_le_of_le v hPsum
  have hPmass : ∑ c, snorm v (P c) ^ 2 ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) hPtotal
    rw [snorm_sq_eq_qform, hPsa c]
    exact qform_le_of_le v (mul_self_le_of_le_one (hP0 c) (hP1 c))
  -- the two Cauchy--Schwarz steps
  have hcs : ∀ (G : C → Matrix N N ℂ) (hG : ∀ c, (G c)ᴴ = G c) (K : C → Matrix N N ℂ),
      |∑ c, qform v (G c * K c)|
        ≤ Real.sqrt (∑ c, snorm v (G c) ^ 2) * Real.sqrt (∑ c, snorm v (K c) ^ 2) := by
    intro G hG K
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun c _ => ?_)
      (sum_mul_le_sqrt (fun c => snorm v (G c)) (fun c => snorm v (K c)))
    have h := abs_qform_conjTranspose_mul_le v (G c) (K c)
    rwa [hG c] at h
  have hstep1 : |∑ c, qform v (M c * (M c - P c))| ≤ Real.sqrt δ := by
    refine le_trans (hcs M hM.isSelfAdjoint (fun c => M c - P c)) ?_
    rw [hMmass, Real.sqrt_one, one_mul]
    exact Real.sqrt_le_sqrt hclose
  have hstep2 : |∑ c, qform v ((M c - P c) * P c)| ≤ Real.sqrt δ := by
    refine le_trans (hcs (fun c => M c - P c)
      (fun c => by rw [Matrix.conjTranspose_sub, hM.isSelfAdjoint c, hPsa c]) P) ?_
    calc Real.sqrt (∑ c, snorm v (M c - P c) ^ 2) * Real.sqrt (∑ c, snorm v (P c) ^ 2)
        ≤ Real.sqrt δ * Real.sqrt 1 :=
          mul_le_mul (Real.sqrt_le_sqrt hclose) (Real.sqrt_le_sqrt hPmass)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt δ := by rw [Real.sqrt_one, mul_one]
  -- unwinding the two identities
  have heq1 : ∑ c, qform v (M c * (M c - P c)) = 1 - ∑ c, qform v (M c * P c) := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [show M c * (M c - P c) = M c - M c * P c from by rw [Matrix.mul_sub, hM.idem c],
        qform_sub], Finset.sum_sub_distrib, ← qform_sum, hM.sum_eq_one, qform_one v hv]
  have heq2 : ∑ c, qform v ((M c - P c) * P c)
      = (∑ c, qform v (M c * P c)) - ∑ c, qform v (P c * P c) := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [Matrix.sub_mul, qform_sub], Finset.sum_sub_distrib]
  have hlow : 1 - 2 * Real.sqrt δ ≤ ∑ c, qform v (P c * P c) := by
    have h1 := (abs_le.mp hstep1).2
    have h2 := (abs_le.mp hstep2).2
    rw [heq1] at h1
    rw [heq2] at h2
    linarith
  refine le_trans hlow (Finset.sum_le_sum fun c _ => ?_)
  exact qform_le_of_le v (mul_self_le_of_le_one (hP0 c) (hP1 c))

end Mass

/-! ## The coarse-graining of a family, and the product question distribution -/

section Setup

/-- The fibre sum of a family of operators along an outcome map --- its coarse-graining. -/
def fibSum {α β N : Type*} [Fintype α] [DecidableEq β] (G : α → Matrix N N ℂ) (e : α → β)
    (b : β) : Matrix N N ℂ :=
  ∑ g ∈ univ.filter fun g => e g = b, G g

variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e

/-- The question distribution of the pasting lemma: a weight on the part both measurements see,
times the uniform distribution on the probe that separates the second family's outcomes. -/
theorem sum_prod_uniform {Z Y : Type*} [Fintype Z] [Fintype Y] [Nonempty Y] (ν : Z → ℝ)
    (f : Z → ℝ) :
    ∑ i : Z × Y, (ν i.1 * (Fintype.card Y : ℝ)⁻¹) * f i.1 = ∑ z : Z, ν z * f z := by
  classical
  have hY : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The product question distribution is a distribution. -/
theorem sum_prod_uniform_one {Z Y : Type*} [Fintype Z] [Fintype Y] [Nonempty Y] {ν : Z → ℝ}
    (hν : ∑ z, ν z = 1) :
    ∑ i : Z × Y, ν i.1 * (Fintype.card Y : ℝ)⁻¹ = 1 := by
  have h := sum_prod_uniform (Y := Y) ν fun _ => 1
  simp only [mul_one] at h
  rw [h, hν]

end Setup

/-! ## Regrouping along the fibres of an outcome map -/

section Fibre

theorem sum_prod_eq {M : Type*} [AddCommMonoid M] {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → M) : ∑ a, ∑ b, f a b = ∑ p : α × β, f p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- A sum whose summand depends on the index only through its image splits into the fibres. -/
theorem sum_fiber {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (e : α → β) (f : β → α → M) :
    ∑ g : α, f (e g) g = ∑ b : β, ∑ g ∈ univ.filter fun g => e g = b, f b g := by
  classical
  conv_lhs => rw [← Finset.sum_fiberwise (univ : Finset α) e fun g => f (e g) g]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g hg => by
    rw [(Finset.mem_filter.mp hg).2]

/-- Moving the outermost sum of four inwards. -/
theorem sum_comm4 {α β γ κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ]
    (T : α → β → γ → κ → ℝ) :
    ∑ y : α, ∑ a : β, ∑ g : γ, ∑ g' : κ, T y a g g'
      = ∑ a : β, ∑ g : γ, ∑ g' : κ, ∑ y : α, T y a g g' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_comm

/-- **Cauchy--Schwarz for a double sum**, in the shape the steps use: each term is dominated by a
product, and the two factors separate. -/
theorem abs_sum_sum_le_sqrt {α β : Type*} [Fintype α] [Fintype β] (f u v : α → β → ℝ)
    (hf : ∀ a b, |f a b| ≤ u a b * v a b) :
    |∑ a, ∑ b, f a b| ≤ Real.sqrt (∑ a, ∑ b, u a b ^ 2) * Real.sqrt (∑ a, ∑ b, v a b ^ 2) := by
  rw [sum_prod_eq f, sum_prod_eq fun a b => u a b ^ 2, sum_prod_eq fun a b => v a b ^ 2]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact le_trans (Finset.sum_le_sum fun p _ => hf p.1 p.2)
    (sum_mul_le_sqrt (fun p : α × β => u p.1 p.2) fun p : α × β => v p.1 p.2)

/-! ### Weighted sums -/

section Weighted

variable {ι : Type*} [Fintype ι]

theorem sum_weighted_add (w f g : ι → ℝ) :
    ∑ i, w i * (f i + g i) = (∑ i, w i * f i) + ∑ i, w i * g i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => mul_add _ _ _

theorem sum_weighted_const_mul (c : ℝ) (w f : ι → ℝ) :
    ∑ i, w i * (c * f i) = c * ∑ i, w i * f i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_weighted_div (w f : ι → ℝ) (c : ℝ) :
    ∑ i, w i * (f i / c) = (∑ i, w i * f i) / c := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

end Weighted

end Fibre

/-! ## Two ways for a family of squared state norms to sum to at most one -/

section Mass2

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **Mutually orthogonal projections**: the sum is a projection, hence bounded by the identity. -/
theorem sum_snorm_sq_orth_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {v : N → ℂ}
    (hv : ‖evec v‖ = 1) (P : ι → Matrix N N ℂ) (hsa : ∀ i, (P i)ᴴ = P i)
    (hidem : ∀ i, P i * P i = P i) (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    ∑ i, snorm v (P i) ^ 2 ≤ 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by
      rw [snorm_sq_eq_qform, hsa i, hidem i], ← qform_sum, ← qform_one v hv]
  exact qform_le_of_le v
    (proj_le_one (conjTranspose_sum_of_orth hsa) (mul_self_sum_of_orth hidem horth))

/-- **A POVM**: each square is below the element, and the elements sum to the identity. -/
theorem sum_snorm_sq_povm_le_one {ι : Type*} [Fintype ι] {v : N → ℂ} (hv : ‖evec v‖ = 1)
    {P : ι → Matrix N N ℂ} (hP0 : ∀ i, (0 : Matrix N N ℂ) ≤ P i) (hPsum : ∑ i, P i = 1) :
    ∑ i, snorm v (P i) ^ 2 ≤ 1 := by
  have hsa : ∀ i, (P i)ᴴ = P i := fun i => (Matrix.nonneg_iff_posSemidef.mp (hP0 i)).isHermitian
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by rw [snorm_sq_eq_qform, hsa i],
    ← qform_sum, ← qform_one v hv]
  exact qform_le_of_le v (sum_sq_le_one_of_sum_eq_one hP0 hPsum)

end Mass2

section Nonneg

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem aOp_zero : (aOp (0 : Matrix dA dA ℂ) : Matrix (dA × dB) (dA × dB) ℂ) = 0 := by
  rw [aOp, Matrix.zero_kronecker]

theorem bOp_zero : (bOp (0 : Matrix dB dB ℂ) : Matrix (dA × dB) (dA × dB) ℂ) = 0 := by
  rw [bOp, Matrix.kronecker_zero]

theorem sum_aOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι]
    {P : ι → Matrix dA dA ℂ} (h : IsPVM P) :
    ∑ i, ((aOp (P i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * aOp (P i) = 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by
      rw [aOp_conjTranspose, h.isSelfAdjoint, ← aOp_mul, h.idem],
    ← aOp_sum, h.sum_eq_one, aOp_one]

theorem bornProb_sub_right (ψ : dA × dB → ℂ) (X : Matrix dA dA ℂ) (M N : Matrix dB dB ℂ) :
    bornProb ψ X (M - N) = bornProb ψ X M - bornProb ψ X N := by
  rw [bornProb_eq_qform, bornProb_eq_qform, bornProb_eq_qform, bOp_sub, Matrix.mul_sub, qform_sub]

/-- A product of two commuting projections is a projection, so its squared state norm is its
quadratic form --- a Born probability. -/
theorem snorm_sq_prod_proj (ψ : dA × dB → ℂ) {P : Matrix dA dA ℂ} {Q : Matrix dB dB ℂ}
    (hPsa : Pᴴ = P) (hPi : P * P = P) (hQsa : Qᴴ = Q) (hQi : Q * Q = Q) :
    snorm ψ ((aOp P : Matrix (dA × dB) _ ℂ) * bOp Q) ^ 2
      = bornProb ψ P Q := by
  rw [snorm_sq_eq_qform, aOp_bOp_conjTranspose, hPsa, hQsa, aOp_bOp_mul_aOp_bOp, hPi, hQi,
    bornProb_eq_qform]

theorem bornProb_sum_left {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, bornProb ψ (A i) B := by
  rw [bornProb_eq_qform, aOp_sum, Finset.sum_mul, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ (A i) B).symm

theorem bornProb_sum_right {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ A (∑ i ∈ s, B i) = ∑ i ∈ s, bornProb ψ A (B i) := by
  rw [bornProb_eq_qform, bOp_sum, Finset.mul_sum, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ A (B i)).symm

end Nonneg

/-! ## Coarse-graining a pair of projective families, on the two parties -/

section Coarse2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Coarse-graining adds the off-diagonal Born probabilities, which are nonnegative. -/
theorem sum_bornProb_le_fibSum (ψ : dA × dB → ℂ) {X : α → Matrix dA dA ℂ}
    {X' : α → Matrix dB dB ℂ} (hX : IsPVM X) (hX' : IsPVM X') (e : α → β) :
    ∑ a, bornProb ψ (X a) (X' a) ≤ ∑ b, bornProb ψ (fibSum X e b) (fibSum X' e b) := by
  classical
  have hfib : ∀ b : β, bornProb ψ (fibSum X e b) (fibSum X' e b)
      = ∑ a ∈ univ.filter fun a => e a = b, ∑ a' ∈ univ.filter fun a' => e a' = b,
          bornProb ψ (X a) (X' a') := fun b => by rw [fibSum, fibSum, bornProb_sum_sum]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hfib b]
  have hdiag : ∀ b : β, ∑ a ∈ univ.filter fun a => e a = b, bornProb ψ (X a) (X' a)
      ≤ ∑ a ∈ univ.filter fun a => e a = b, ∑ a' ∈ univ.filter fun a' => e a' = b,
          bornProb ψ (X a) (X' a') := fun b =>
    Finset.sum_le_sum fun a ha => Finset.single_le_sum
      (fun a' _ => bornProb_nonneg ψ (hX.posSemidef a) (hX'.posSemidef a')) ha
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun b (_ : b ∈ univ) => hdiag b)
  exact (Finset.sum_fiberwise (univ : Finset α) e fun a => bornProb ψ (X a) (X' a)).symm

/-- **Coarse-graining two projective families the same way costs nothing**, in the `fibSum` form
that the pasting lemma needs. -/
theorem sum_xSqNorm_fibSum_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {X : α → Matrix dA dA ℂ}
    {X' : α → Matrix dB dB ℂ} (hX : IsPVM X) (hX' : IsPVM X') (e : α → β) :
    ∑ b, xSqNorm ψ (fibSum X e b) (fibSum X' e b) ≤ ∑ a, xSqNorm ψ (X a) (X' a) := by
  have e1 := one_sub_sum_bornProb_eq hψ (isPVM_fibSum hX e) (isPVM_fibSum hX' e)
  have e2 := one_sub_sum_bornProb_eq hψ hX hX'
  have e3 := sum_bornProb_le_fibSum ψ hX hX' e
  linarith

end Coarse2

/-! ## The fine-grained commutator against the coarse-grained one -/

section Fine

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Z Y G2 R1 R2 : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype G2] [DecidableEq G2] [Fintype R1] [DecidableEq R1]
  [Fintype R2] [DecidableEq R2]

/-- The commutator sum of two projective families on Bob's factor, written as the deficit of one
overlap. Both the fine-grained and the coarse-grained commutators have this shape, and it is what
lets them be compared. -/
theorem sum_snorm_sq_comm_eq {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 → Matrix dB dB ℂ} {B : G2 → Matrix dB dB ℂ} (hA : IsPVM A) (hB : IsPVM B) :
    ∑ a : R1, ∑ g : G2, snorm ψ (bOp (A a * B g - B g * A a) : Matrix (dA × dB) _ ℂ) ^ 2
      = 2 - 2 * ∑ a : R1, ∑ g : G2,
          qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ) := by
  classical
  -- the expansion of one squared deviation
  have hterm : ∀ (a : R1) (g : G2),
      snorm ψ (bOp (A a * B g - B g * A a) : Matrix (dA × dB) _ ℂ) ^ 2
        = qform ψ (bOp (A a * B g * A a) : Matrix (dA × dB) _ ℂ)
          + qform ψ (bOp (B g * A a * B g) : Matrix (dA × dB) _ ℂ)
          - qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ)
          - qform ψ (bOp (B g * A a * B g * A a) : Matrix (dA × dB) _ ℂ) := by
    intro a g
    rw [snorm_sq_eq_qform, bOp_conjTranspose, ← bOp_mul,
      show (A a * B g - B g * A a)ᴴ * (A a * B g - B g * A a)
          = A a * B g * A a + B g * A a * B g
            - A a * B g * A a * B g - B g * A a * B g * A a from by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hA.isSelfAdjoint, hB.isSelfAdjoint]
        calc (B g * A a - A a * B g) * (A a * B g - B g * A a)
            = B g * (A a * A a) * B g + A a * (B g * B g) * A a
              - B g * A a * B g * A a - A a * B g * A a * B g := by noncomm_ring
          _ = _ := by rw [hA.idem, hB.idem]; abel,
      bOp_sub, bOp_sub, bOp_add, qform_sub, qform_sub, qform_add]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun g (_ : g ∈ univ) => hterm a g]
  -- the two diagonal sums are exactly one, and the two off-diagonal sums are equal
  have h1 : ∑ a : R1, ∑ g : G2,
      qform ψ (bOp (A a * B g * A a) : Matrix (dA × dB) _ ℂ) = 1 := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
        rw [← qform_sum, ← bOp_sum,
          show (∑ g : G2, A a * B g * A a) = A a * A a from by
            rw [show (∑ g : G2, A a * B g * A a) = A a * (∑ g : G2, B g) * A a from by
              rw [Matrix.mul_sum, Finset.sum_mul], hB.sum_eq_one, Matrix.mul_one], hA.idem],
      ← qform_sum, ← bOp_sum, hA.sum_eq_one, bOp_one, qform_one _ hψ]
  have h2 : ∑ a : R1, ∑ g : G2,
      qform ψ (bOp (B g * A a * B g) : Matrix (dA × dB) _ ℂ) = 1 := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun g (_ : g ∈ univ) => by
        rw [← qform_sum, ← bOp_sum,
          show (∑ a : R1, B g * A a * B g) = B g * B g from by
            rw [show (∑ a : R1, B g * A a * B g) = B g * (∑ a : R1, A a) * B g from by
              rw [Matrix.mul_sum, Finset.sum_mul], hA.sum_eq_one, Matrix.mul_one], hB.idem],
      ← qform_sum, ← bOp_sum, hB.sum_eq_one, bOp_one, qform_one _ hψ]
  have h3 : ∑ a : R1, ∑ g : G2,
      qform ψ (bOp (B g * A a * B g * A a) : Matrix (dA × dB) _ ℂ)
        = ∑ a : R1, ∑ g : G2,
          qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g _ => ?_
    have hadj : (A a * B g * A a * B g)ᴴ = B g * A a * B g * A a := by
      simp only [Matrix.conjTranspose_mul, hA.isSelfAdjoint, hB.isSelfAdjoint]
      noncomm_ring
    rw [← qform_conjTranspose ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ),
      bOp_conjTranspose, hadj]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1, h2, h3]
  ring

end Fine

/-! ## The sandwich family of the pasting lemma -/

section Sand2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]

/-- **The pasted POVM**: the paper's `J_{[eval = (a_1, a_2)]}`. `R` is already the coarse-graining
of the paper's `G_1` along its own outcome map --- only `R`'s projectivity is used, so it enters
as a single projective family, and the inner coarse-graining is the consumer's business. -/
def pasteJ (R : R1 → Matrix dB dB ℂ) (G : K → Matrix dB dB ℂ) (e : K → R2)
    (p : R1 × R2) : Matrix dB dB ℂ :=
  ∑ g ∈ univ.filter fun g => e g = p.2, G g * R p.1 * G g

variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}

/-- Each term of the pasting sandwich is a Gram operator, hence positive. -/
theorem sandOp_posSemidef (hR : IsPVM R) (hG : IsPVM G) (a : R1) (g : K) :
    (R a * G g * R a).PosSemidef := by
  have h : R a * G g * R a = (G g * R a)ᴴ * (G g * R a) := by
    calc R a * G g * R a = R a * (G g * G g) * R a := by rw [hG.idem]
      _ = (G g * R a)ᴴ * (G g * R a) := by
          rw [Matrix.conjTranspose_mul, hR.isSelfAdjoint, hG.isSelfAdjoint]; noncomm_ring
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The pasting sandwich is a POVM: the inner family sums away against `R`'s projectivity. -/
theorem sum_sandOp (hR : IsPVM R) (hG : IsPVM G) :
    ∑ p : R1 × K, R p.1 * G p.2 * R p.1 = 1 := by
  rw [← sum_prod_eq fun (a : R1) (g : K) => R a * G g * R a]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => show
      (∑ g : K, R a * G g * R a) = R a from by
        rw [show (∑ g : K, R a * G g * R a) = R a * (∑ g : K, G g) * R a from by
          rw [Matrix.mul_sum, Finset.sum_mul], hG.sum_eq_one, Matrix.mul_one, hR.idem],
    hR.sum_eq_one]

/-- The squared state norms of the pasting sandwich sum to at most one. -/
theorem sum_snorm_sq_sandOp_le_one {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) (hR : IsPVM R)
    (hG : IsPVM G) :
    ∑ a : R1, ∑ g : K,
        snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2 ≤ 1 := by
  rw [sum_prod_eq fun (a : R1) (g : K) =>
    snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2]
  refine sum_snorm_sq_povm_le_one hψ
    (fun p => bOp_nonneg (Matrix.nonneg_iff_posSemidef.mpr (sandOp_posSemidef hR hG p.1 p.2))) ?_
  rw [← bOp_sum, sum_sandOp hR hG, bOp_one]

/-- **The cloud step.** Replacing Bob's outer factor by Alice's copy of it costs the square root of
their cross-party deviation --- and nothing depending on the size of `K`, because one factor `R a`
stays in front of the deviation, so the sum over `a` is absorbed rather than repeated. -/
theorem abs_sigma_sub_cloud_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {Ga : K → Matrix dA dA ℂ}
    (hR : IsPVM R) (hG : IsPVM G) :
    |(∑ a : R1, ∑ g : K, qform ψ (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)|
      ≤ Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) := by
  classical
  have hsa : ∀ (a : R1) (g : K),
      ((bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))ᴴ = bOp (R a * G g * R a) := by
    intro a g
    rw [bOp_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hR.isSelfAdjoint, hG.isSelfAdjoint, Matrix.mul_assoc]
  -- the one matrix identity: an `R a` in front of the deviation is free, because the sandwich
  -- already ends in `R a`
  have hM : ∀ (a : R1) (g : K), (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ)
        * ((bOp (R a) : Matrix (dA × dB) _ ℂ)
          * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g)))
      = (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ)
        - aOp (Ga g) * bOp (R a * G g * R a) := by
    intro a g
    have hRR : R a * G g * R a * R a = R a * G g * R a := by
      rw [show R a * G g * R a * R a = R a * G g * (R a * R a) from by noncomm_ring, hR.idem]
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← bOp_mul,
      ← bOp_mul, hRR, ← aOp_mul_bOp]
  have hterm : ∀ (a : R1) (g : K),
      qform ψ (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ)
          - bornProb ψ (Ga g) (R a * G g * R a)
        = qform ψ (((bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))ᴴ
            * ((bOp (R a) : Matrix (dA × dB) _ ℂ)
              * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g)))) := by
    intro a g
    rw [hsa a g, hM a g, qform_sub, bornProb_eq_qform]
  have hsum : (∑ a : R1, ∑ g : K,
        qform ψ (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)
      = ∑ a : R1, ∑ g : K, qform ψ (((bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))ᴴ
          * ((bOp (R a) : Matrix (dA × dB) _ ℂ)
            * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hterm a g
  rw [hsum]
  -- the two mass bounds, then Cauchy--Schwarz
  have hmass1 := sum_snorm_sq_sandOp_le_one (dA := dA) hψ hR hG
  have hmass2 : ∑ a : R1, ∑ g : K, snorm ψ ((bOp (R a) : Matrix (dA × dB) _ ℂ)
        * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))) ^ 2
      ≤ ∑ g : K, xSqNorm ψ (Ga g) (G g) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun g _ => ?_
    refine le_trans (sum_snorm_sq_mul_le ψ (fun a => (bOp (R a) : Matrix (dA × dB) _ ℂ))
      (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hR))
      ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))) ?_
    refine le_of_eq ?_
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  refine le_trans (abs_sum_sum_le_sqrt _
    (fun a g => snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))
    (fun a g => snorm ψ ((bOp (R a) : Matrix (dA × dB) _ ℂ)
      * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))))
    fun a g => abs_qform_conjTranspose_mul_le ψ _ _) ?_
  calc Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2)
        * Real.sqrt (∑ a : R1, ∑ g : K, snorm ψ ((bOp (R a) : Matrix (dA × dB) _ ℂ)
          * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))) ^ 2)
      ≤ Real.sqrt 1 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) :=
        mul_le_mul (Real.sqrt_le_sqrt hmass1) (Real.sqrt_le_sqrt hmass2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) := by rw [Real.sqrt_one, one_mul]

/-! ## Alice's operator against Bob's projection -/

/-- **A mutually orthogonal family of products of commuting projections** has its squared state
norms summing to at most one. Alice's factor need not be a measurement in its own right: only
self-adjointness, idempotence and orthogonality along the first index are used. -/
theorem sum_snorm_sq_prod_le_one {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) (P : ι → κ → Matrix dA dA ℂ)
    (Q : κ → Matrix dB dB ℂ) (hPsa : ∀ i k, (P i k)ᴴ = P i k)
    (hPidem : ∀ i k, P i k * P i k = P i k)
    (hPorth : ∀ (i j : ι) (k : κ), i ≠ j → P i k * P j k = 0) (hQ : IsPVM Q) :
    ∑ i, ∑ k, snorm ψ ((aOp (P i k) : Matrix (dA × dB) _ ℂ) * bOp (Q k)) ^ 2 ≤ 1 := by
  classical
  have hsa : ∀ p : ι × κ, ((aOp (P p.1 p.2) : Matrix (dA × dB) _ ℂ) * bOp (Q p.2))ᴴ
      = (aOp (P p.1 p.2) : Matrix (dA × dB) _ ℂ) * bOp (Q p.2) := by
    intro p
    rw [aOp_bOp_conjTranspose, hPsa, hQ.isSelfAdjoint]
  have hidem : ∀ p : ι × κ, ((aOp (P p.1 p.2) : Matrix (dA × dB) _ ℂ) * bOp (Q p.2))
        * ((aOp (P p.1 p.2) : Matrix (dA × dB) _ ℂ) * bOp (Q p.2))
      = (aOp (P p.1 p.2) : Matrix (dA × dB) _ ℂ) * bOp (Q p.2) := by
    intro p
    rw [aOp_bOp_mul_aOp_bOp, hPidem, hQ.idem]
  have horth : ∀ p p' : ι × κ, p ≠ p' →
      ((aOp (P p.1 p.2) : Matrix (dA × dB) _ ℂ) * bOp (Q p.2))
        * ((aOp (P p'.1 p'.2) : Matrix (dA × dB) _ ℂ) * bOp (Q p'.2)) = 0 := by
    intro p p' hne
    rw [aOp_bOp_mul_aOp_bOp]
    by_cases h2 : p.2 = p'.2
    · have h1 : p.1 ≠ p'.1 := fun h => hne (Prod.ext h h2)
      rw [← h2, hPorth p.1 p'.1 p.2 h1, aOp_zero, Matrix.zero_mul]
    · rw [hQ.orthogonal h2, bOp_zero, Matrix.mul_zero]
  rw [sum_prod_eq fun (i : ι) (k : κ) =>
    snorm ψ ((aOp (P i k) : Matrix (dA × dB) _ ℂ) * bOp (Q k)) ^ 2]
  exact sum_snorm_sq_orth_le_one hψ _ hsa hidem horth

/-- **From the sandwich to the ordered product.** The difference is Alice's operator against Bob's
commutator; Alice's projection times Bob's is a mutually orthogonal family, so the Cauchy--Schwarz
costs only the commutator. -/
theorem abs_sand_sub_ord_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hG : IsPVM G) (e : K → R2) :
    |(∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a)|
      ≤ Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) := by
  classical
  have hterm : ∀ (a : R1) (g : K),
      bornProb ψ (A (a, e g)) (G g * R a * G g) - bornProb ψ (A (a, e g)) (G g * R a)
        = qform ψ (((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g))ᴴ
            * bOp (R a * G g - G g * R a)) := by
    intro a g
    have hM : ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g))ᴴ
          * bOp (R a * G g - G g * R a)
        = (aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g * R a * G g)
          - (aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g * R a) := by
      rw [aOp_bOp_conjTranspose, hA.isSelfAdjoint, hG.isSelfAdjoint,
        Matrix.mul_assoc (aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ), ← bOp_mul,
        show G g * (R a * G g - G g * R a) = G g * R a * G g - G g * R a from by
          rw [Matrix.mul_sub, show G g * (G g * R a) = G g * G g * R a from by noncomm_ring,
            hG.idem, Matrix.mul_assoc],
        bOp_sub, Matrix.mul_sub]
    rw [hM, qform_sub, bornProb_eq_qform, bornProb_eq_qform]
  have hsum : (∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a)
      = ∑ a : R1, ∑ g : K, qform ψ (((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g))ᴴ
          * bOp (R a * G g - G g * R a)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hterm a g
  rw [hsum]
  have hmass : ∑ a : R1, ∑ g : K,
      snorm ψ ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g)) ^ 2 ≤ 1 :=
    sum_snorm_sq_prod_le_one hψ (fun a g => A (a, e g)) G
      (fun a g => hA.isSelfAdjoint _) (fun a g => hA.idem _)
      (fun a a' g hne => hA.orthogonal fun h => hne (Prod.ext_iff.mp h).1) hG
  refine le_trans (abs_sum_sum_le_sqrt _
    (fun a g => snorm ψ ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g)))
    (fun a g => snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ))
    fun a g => abs_qform_conjTranspose_mul_le ψ _ _) ?_
  calc Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g)) ^ 2)
        * Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ Real.sqrt 1 * Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_one, one_mul]

/-! ## The ordered product carries almost all the mass -/

/-- **Step (i) of the pasting lemma.** Bob's two projections in the order `G_g R_a`, paired with
Alice's joint outcome, already agree with the state at `1 - delta/2 - sqrt(delta/2)`: the outer
factor sums away against Alice's marginal, and what is left is the `R`-consistency, whose square
root is the only one in the whole argument that is not a commutator. -/
theorem sum_bornProb_ord_ge {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    1 - (∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b)) / 2
        - Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2)
      ≤ ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a) := by
  classical
  -- the split `G_g R_a = G_g - G_g (Id - R_a)`
  have hsplit : ∀ (a : R1) (g : K), bornProb ψ (A (a, e g)) (G g * R a)
      = bornProb ψ (A (a, e g)) (G g)
        - bornProb ψ (A (a, e g)) (G g * ((1 : Matrix dB dB ℂ) - R a)) := by
    intro a g
    rw [← bornProb_sub_right,
      show G g - G g * ((1 : Matrix dB dB ℂ) - R a) = G g * R a from by
        rw [Matrix.mul_sub, Matrix.mul_one]; abel]
  -- the first term is the `G`-consistency of Alice's second marginal
  have hterm1 : ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g)
      = 1 - (∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b)) / 2 := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun g (_ : g ∈ univ) => (bornProb_sum_left ψ univ
        (fun a => A (a, e g)) (G g)).symm,
      sum_fiber e fun b g => bornProb ψ (∑ a : R1, A (a, b)) (G g),
      Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
        (∑ g ∈ univ.filter fun g => e g = b, bornProb ψ (∑ a : R1, A (a, b)) (G g))
          = bornProb ψ (∑ a : R1, A (a, b)) (fibSum G e b) from
        (bornProb_sum_right ψ (univ.filter fun g => e g = b) (∑ a : R1, A (a, b)) G).symm]
    have h := one_sub_sum_bornProb_eq (dA := dA) (dB := dB) hψ hA.marg_right (isPVM_fibSum hG e)
    linarith
  -- the second term is bounded by the square root of the `R`-consistency
  have hbar : ((1 : Matrix dB dB ℂ) - R ·) = fun a => (1 : Matrix dB dB ℂ) - R a := rfl
  have hbarsa : ∀ a : R1, ((1 : Matrix dB dB ℂ) - R a)ᴴ = (1 : Matrix dB dB ℂ) - R a := by
    intro a
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hR.isSelfAdjoint]
  have hbari : ∀ a : R1, ((1 : Matrix dB dB ℂ) - R a) * ((1 : Matrix dB dB ℂ) - R a)
      = (1 : Matrix dB dB ℂ) - R a := by
    intro a
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hR.idem]
    abel
  -- regrouping the second term along the fibres of `e`
  have hterm2eq : ∀ a : R1, ∑ g : K, bornProb ψ (A (a, e g))
        (G g * ((1 : Matrix dB dB ℂ) - R a))
      = ∑ b : R2, bornProb ψ (A (a, b)) (fibSum G e b * ((1 : Matrix dB dB ℂ) - R a)) := by
    intro a
    rw [sum_fiber e fun b g => bornProb ψ (A (a, b)) (G g * ((1 : Matrix dB dB ℂ) - R a))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [fibSum, Finset.sum_mul, bornProb_sum_right]
  have hCS : ∀ (a : R1) (b : R2),
      |bornProb ψ (A (a, b)) (fibSum G e b * ((1 : Matrix dB dB ℂ) - R a))|
        ≤ snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b))
          * snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
            * bOp ((1 : Matrix dB dB ℂ) - R a)) := by
    intro a b
    have hM : ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b))ᴴ
          * ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp ((1 : Matrix dB dB ℂ) - R a))
        = (aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
          * bOp (fibSum G e b * ((1 : Matrix dB dB ℂ) - R a)) := by
      rw [aOp_bOp_conjTranspose, hA.isSelfAdjoint,
        (isPVM_fibSum hG e).isSelfAdjoint, aOp_bOp_mul_aOp_bOp, hA.idem]
    have h := abs_qform_conjTranspose_mul_le ψ
      ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b))
      ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp ((1 : Matrix dB dB ℂ) - R a))
    rw [hM, ← bornProb_eq_qform] at h
    exact h
  have hmass1 : ∑ a : R1, ∑ b : R2,
      snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b)) ^ 2 ≤ 1 :=
    sum_snorm_sq_prod_le_one hψ (fun a b => A (a, b)) (fibSum G e)
      (fun a b => hA.isSelfAdjoint _) (fun a b => hA.idem _)
      (fun a a' b hne => hA.orthogonal fun h => hne (Prod.ext_iff.mp h).1) (isPVM_fibSum hG e)
  have hmass2 : ∑ a : R1, ∑ b : R2, snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
        * bOp ((1 : Matrix dB dB ℂ) - R a)) ^ 2
      = (∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2 := by
    have hone : ∑ a : R1, bornProb ψ (∑ b : R2, A (a, b)) (1 : Matrix dB dB ℂ) = 1 := by
      have hsum : ∑ a : R1, (∑ b : R2, A (a, b)) = 1 := hA.sum_marg_left
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => bornProb_eq_qform ψ _ _, ← qform_sum]
      rw [show (∑ a : R1, (aOp (∑ b : R2, A (a, b)) : Matrix (dA × dB) _ ℂ)
            * bOp (1 : Matrix dB dB ℂ))
          = (1 : Matrix (dA × dB) (dA × dB) ℂ) from by
        simp only [bOp_one, Matrix.mul_one]
        rw [← aOp_sum, hsum, aOp_one], qform_one _ hψ]
    have hsq : ∀ (a : R1) (b : R2), snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
          * bOp ((1 : Matrix dB dB ℂ) - R a)) ^ 2
        = bornProb ψ (A (a, b)) ((1 : Matrix dB dB ℂ) - R a) := fun a b =>
      snorm_sq_prod_proj ψ (hA.isSelfAdjoint _) (hA.idem _) (hbarsa a) (hbari a)
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun b (_ : b ∈ univ) => hsq a b]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      (bornProb_sum_left ψ univ (fun b => A (a, b)) ((1 : Matrix dB dB ℂ) - R a)).symm]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      bornProb_sub_right ψ (∑ b : R2, A (a, b)) 1 (R a), Finset.sum_sub_distrib, hone]
    have h := one_sub_sum_bornProb_eq (dA := dA) (dB := dB) hψ hA.marg_left hR
    linarith
  -- assembling
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun g (_ : g ∈ univ) => hsplit a g]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_sub_distrib _ _,
    Finset.sum_sub_distrib, hterm1]
  have hbound : ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g))
        (G g * ((1 : Matrix dB dB ℂ) - R a))
      ≤ Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2) := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hterm2eq a]
    refine le_trans (le_abs_self _) (le_trans (abs_sum_sum_le_sqrt _
      (fun a b => snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b)))
      (fun a b => snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
        * bOp ((1 : Matrix dB dB ℂ) - R a))) fun a b => hCS a b) ?_)
    rw [hmass2]
    calc Real.sqrt (∑ a : R1, ∑ b : R2,
            snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b)) ^ 2)
          * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2)
        ≤ Real.sqrt 1 * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmass1) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, one_mul]
  linarith

/-! ## The pasted POVM -/

/-- The other sandwich --- the one the pasted POVM is built from --- is also a Gram operator. -/
theorem sandOpG_posSemidef (hR : IsPVM R) (hG : IsPVM G) (a : R1) (g : K) :
    (G g * R a * G g).PosSemidef := by
  have h : G g * R a * G g = (R a * G g)ᴴ * (R a * G g) := by
    calc G g * R a * G g = G g * (R a * R a) * G g := by rw [hR.idem]
      _ = (R a * G g)ᴴ * (R a * G g) := by
          rw [Matrix.conjTranspose_mul, hR.isSelfAdjoint, hG.isSelfAdjoint]; noncomm_ring
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sum_sandOpG (hR : IsPVM R) (hG : IsPVM G) :
    ∑ p : R1 × K, G p.2 * R p.1 * G p.2 = 1 := by
  rw [← sum_prod_eq fun (a : R1) (g : K) => G g * R a * G g, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun g (_ : g ∈ univ) => show
      (∑ a : R1, G g * R a * G g) = G g from by
        rw [show (∑ a : R1, G g * R a * G g) = G g * (∑ a : R1, R a) * G g from by
          rw [Matrix.mul_sum, Finset.sum_mul], hR.sum_eq_one, Matrix.mul_one, hG.idem],
    hG.sum_eq_one]

theorem pasteJ_posSemidef (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) (p : R1 × R2) :
    (pasteJ R G e p).PosSemidef := by
  rw [pasteJ]
  exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) (Matrix.PosSemidef.zero)
    fun g _ => sandOpG_posSemidef hR hG p.1 g

theorem sum_pasteJ (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    ∑ p : R1 × R2, pasteJ R G e p = 1 := by
  classical
  have h : ∀ a : R1, ∑ b : R2, pasteJ R G e (a, b) = ∑ g : K, G g * R a * G g := by
    intro a
    rw [sum_fiber e fun b g => G g * R a * G g]
    exact Finset.sum_congr rfl fun b _ => rfl
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a (_ : a ∈ univ) => h a,
    sum_prod_eq fun (a : R1) (g : K) => G g * R a * G g, sum_sandOpG hR hG]

/-- **From the Born rule to the state-dependent distance**: Alice's family is projective and the
pasted family is a POVM, so the summed deviation is at most twice the disagreement. -/
theorem sum_xSqNorm_pasteJ_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    ∑ p : R1 × R2, xSqNorm ψ (A p) (pasteJ R G e p)
      ≤ 2 * (1 - ∑ p : R1 × R2, bornProb ψ (A p) (pasteJ R G e p)) := by
  classical
  have hAmass : ∑ p : R1 × R2, stateSqNorm ψ (A p) = 1 := by
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => by
        rw [stateSqNorm_eq_qform (dB := dB) ψ (A p), hA.isSelfAdjoint p, hA.idem p],
      ← qform_sum, ← aOp_sum, hA.sum_eq_one, aOp_one, qform_one _ hψ]
  have hJmass : ∑ p : R1 × R2, ‖stateVecB ψ (pasteJ R G e p)‖ ^ 2 ≤ 1 := by
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => show
      ‖stateVecB ψ (pasteJ R G e p)‖ ^ 2
        = snorm ψ (bOp (pasteJ R G e p) : Matrix (dA × dB) _ ℂ) ^ 2 from by
      rw [norm_stateVecB_eq_snorm]]
    exact sum_snorm_sq_povm_le_one hψ
      (fun p => bOp_nonneg (Matrix.nonneg_iff_posSemidef.mpr (pasteJ_posSemidef hR hG e p)))
      (by rw [← bOp_sum, sum_pasteJ hR hG e, bOp_one])
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) =>
    xSqNorm_eq_expand ψ (hA.isSelfAdjoint p) (pasteJ R G e p), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hAmass, ← Finset.mul_sum]
  linarith

/-! ## The coarse-grained commutator, and the collision term -/

/-- **The coarse-grained commutator is small**: this is the commutation analysis, with both
families on Bob's factor and Alice's joint measurement supplying the operator both products
reach. -/
theorem sum_snorm_sq_comm_coarse_le {ψ : dA × dB → ℂ} {A : R1 × R2 → Matrix dA dA ℂ}
    {Gf : R2 → Matrix dB dB ℂ} (hA : IsPVM A) (hR : IsPVM R) (hGf : IsPVM Gf) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a) ≤ δ₁)
    (h2 : ∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (Gf b) ≤ δ₂) :
    ∑ a : R1, ∑ b : R2, snorm ψ (bOp (R a * Gf b - Gf b * R a) : Matrix (dA × dB) _ ℂ) ^ 2
      ≤ 16 * (δ₁ + δ₂) := by
  classical
  have hδ₂0 : 0 ≤ δ₂ := le_trans (Finset.sum_nonneg fun b _ => xSqNorm_nonneg _ _ _) h2
  have hδ₁0 : 0 ≤ δ₁ := le_trans (Finset.sum_nonneg fun a _ => xSqNorm_nonneg _ _ _) h1
  have hdev : ∀ (X : Matrix dA dA ℂ) (Y : Matrix dB dB ℂ),
      snorm ψ ((bOp Y : Matrix (dA × dB) _ ℂ) - aOp X) ^ 2 = xSqNorm ψ X Y := by
    intro X Y
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  have key := commutation_analysis_abstract (N := dA × dB) (B := R1) (C := R2) (δ := δ₁ + δ₂) ψ
    (fun a => (bOp (R a) : Matrix (dA × dB) _ ℂ))
    (fun b => (bOp (Gf b) : Matrix (dA × dB) _ ℂ))
    (fun a => (aOp (∑ b : R2, A (a, b)) : Matrix (dA × dB) _ ℂ))
    (fun b => (aOp (∑ a : R1, A (a, b)) : Matrix (dA × dB) _ ℂ))
    (fun p => (aOp (A p) : Matrix (dA × dB) _ ℂ))
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hR))
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hGf))
    (le_of_eq (sum_aOp_conjTranspose_mul_self_of_isPVM hA.marg_left))
    (le_of_eq (sum_aOp_conjTranspose_mul_self_of_isPVM hA.marg_right))
    (fun a b => (aOp_mul_bOp _ _).symm) (fun b a => (aOp_mul_bOp _ _).symm)
    (fun a b => by rw [← aOp_mul, hA.marg_mul_marg a b])
    (fun a b => by rw [← aOp_mul, hA.marg_mul_marg' a b])
    (by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hdev (∑ b : R2, A (a, b)) (R a)]
      linarith)
    (by
      rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hdev (∑ a : R1, A (a, b)) (Gf b)]
      linarith)
  rw [sum_prod_eq fun (a : R1) (b : R2) =>
    snorm ψ (bOp (R a * Gf b - Gf b * R a) : Matrix (dA × dB) _ ℂ) ^ 2]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) key
  rw [bOp_sub, bOp_mul, bOp_mul]

/-- **The collision term**: the pairs of `G`-outcomes that the outcome map cannot tell apart. It
is exactly what the coarse-grained cloud has beyond the fine-grained one, and the only place where
the separating property of the outcome map is needed. -/
def collisionTerm (ψ : dA × dB → ℂ) (R : R1 → Matrix dB dB ℂ) (G : K → Matrix dB dB ℂ)
    (Ga : K → Matrix dA dA ℂ) (e : K → R2) : ℝ :=
  ∑ a : R1, ∑ g : K, ∑ g' ∈ univ.filter fun g' => g' ≠ g ∧ e g' = e g,
    bornProb ψ (Ga g') (R a * G g * R a)

theorem collisionTerm_nonneg (ψ : dA × dB → ℂ) {Ga : K → Matrix dA dA ℂ}
    (hR : IsPVM R) (hG : IsPVM G) (hGa : IsPVM Ga) (e : K → R2) :
    0 ≤ collisionTerm ψ R G Ga e :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun g' _ =>
    bornProb_nonneg ψ (hGa.posSemidef g') (sandOp_posSemidef hR hG a g)

/-- **The strife minus the cloud is exactly the collision term.** Both are sums of the same Born
probabilities; coarse-graining pairs each `G`-outcome with every other one the map identifies
with it. -/
theorem strife_sub_cloud_eq {ψ : dA × dB → ℂ} {Ga : K → Matrix dA dA ℂ} (e : K → R2) :
    (∑ a : R1, ∑ b : R2,
        bornProb ψ (fibSum Ga e b) (R a * fibSum G e b * R a))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)
      = collisionTerm ψ R G Ga e := by
  classical
  have key : ∀ a : R1, ∑ b : R2, bornProb ψ (fibSum Ga e b) (R a * fibSum G e b * R a)
      = ∑ g : K, ∑ g' ∈ univ.filter fun g' => e g' = e g,
          bornProb ψ (Ga g') (R a * G g * R a) := by
    intro a
    rw [sum_fiber e fun b g => ∑ g' ∈ univ.filter fun g' => e g' = b,
      bornProb ψ (Ga g') (R a * G g * R a)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show R a * fibSum G e b * R a
        = ∑ g ∈ univ.filter fun g => e g = b, R a * G g * R a from by
      rw [fibSum, Finset.mul_sum, Finset.sum_mul], fibSum, bornProb_sum_sum]
    exact Finset.sum_comm
  have hsplit : ∀ (a : R1) (g : K),
      (∑ g' ∈ univ.filter fun g' => e g' = e g, bornProb ψ (Ga g') (R a * G g * R a))
        = bornProb ψ (Ga g) (R a * G g * R a)
          + ∑ g' ∈ univ.filter fun g' => g' ≠ g ∧ e g' = e g,
              bornProb ψ (Ga g') (R a * G g * R a) := by
    intro a g
    rw [show (univ.filter fun g' => g' ≠ g ∧ e g' = e g)
        = (univ.filter fun g' => e g' = e g).erase g from by
      ext g'
      simp [Finset.mem_erase, and_comm]]
    exact (Finset.add_sum_erase (univ.filter fun g' => e g' = e g)
      (fun g' => bornProb ψ (Ga g') (R a * G g * R a))
      (Finset.mem_filter.mpr ⟨mem_univ g, rfl⟩)).symm
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => key a,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun g (_ : g ∈ univ) => hsplit a g,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_add_distrib,
    Finset.sum_add_distrib, collisionTerm]
  ring

/-! ## The two halves of the pasting lemma, at one question -/

/-- **The fine-grained commutator against the coarse-grained one.** The coarse-grained one is
small by the commutation analysis; the two differ by the cloud, the strife and the collision term,
and the cloud--strife comparison is the only place Alice's copy of `G` is used. -/
theorem sum_snorm_sq_comm_fine_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} {Ga : K → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R)
    (hG : IsPVM G) (hGa : IsPVM Ga) (e : K → R2) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a) ≤ δ₁)
    (h2 : ∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b) ≤ δ₂) :
    (∑ a : R1, ∑ g : K, snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ 16 * (δ₁ + δ₂) + 4 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g))
        + 2 * collisionTerm ψ R G Ga e := by
  have hfine := sum_snorm_sq_comm_eq (dA := dA) hψ hR hG
  have hcoarse := sum_snorm_sq_comm_eq (dA := dA) hψ hR (isPVM_fibSum hG e)
  have hcc := sum_snorm_sq_comm_coarse_le (ψ := ψ) hA hR (isPVM_fibSum hG e) h1 h2
  have hc1 := abs_le.mp (abs_sigma_sub_cloud_le (Ga := Ga) hψ hR hG)
  have hc2 := abs_le.mp (abs_sigma_sub_cloud_le (K := R2) (G := fibSum G e)
    (Ga := fibSum Ga e) hψ hR (isPVM_fibSum hG e))
  have hcol := strife_sub_cloud_eq (ψ := ψ) (R := R) (G := G) (Ga := Ga) e
  have hmono : Real.sqrt (∑ b : R2, xSqNorm ψ (fibSum Ga e b) (fibSum G e b))
      ≤ Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) :=
    Real.sqrt_le_sqrt (sum_xSqNorm_fibSum_le hψ hGa hG e)
  linarith [hc1.1, hc1.2, hc2.1, hc2.2]

/-- **The pasted POVM agrees with Alice's joint measurement, at one question.** Step (i) reaches
the ordered product and step (ii) the sandwich. -/
theorem one_sub_sum_bornProb_pasteJ_le' {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    1 - (∑ p : R1 × R2, bornProb ψ (A p) (pasteJ R G e p))
      ≤ (∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b)) / 2
        + Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2)
        + Real.sqrt (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) := by
  classical
  have hD : ∑ p : R1 × R2, bornProb ψ (A p) (pasteJ R G e p)
      = ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a * G g) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fiber e fun b g => bornProb ψ (A (a, b)) (G g * R a * G g)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show pasteJ R G e (a, b)
        = ∑ g ∈ univ.filter fun g => e g = b, G g * R a * G g from rfl, bornProb_sum_right]
  have hstepi := sum_bornProb_ord_ge hψ hA hR hG e
  have hstepii := abs_le.mp (abs_sand_sub_ord_le hψ hA hG (R := R) e)
  rw [hD]
  linarith [hstepii.1, hstepii.2]

end Sand2

/-! ## The marginal of a joint measurement against the other party's product

The step `lem:qld-pairs-of-lines` needs before the pasting lemma applies: a *joint* measurement
consistent with the ordered product of the other party's two families is consistent, after summing
out one outcome, with that party's single family. Two facts do it: `sum_snorm_sq_cool`, to replace
the marginal by the same marginal with the other party's projection attached, and then the
orthogonality of that projection's fibres, which is what makes the sum over the summed-out outcome
free rather than a factor `|R2|`. -/

section Marginal

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]

/-- A projective family stays projective on the product space. -/
theorem IsPVM.aOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dA dA ℂ} (h : IsPVM Q) :
    IsPVM fun i => (aOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [aOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← aOp_mul, h.idem]
  sum_eq_one := by rw [← aOp_sum, h.sum_eq_one, aOp_one]

theorem IsPVM.bOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    IsPVM fun i => (bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [bOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← bOp_mul, h.idem]
  sum_eq_one := by rw [← bOp_sum, h.sum_eq_one, bOp_one]

theorem sum_fibre_fst {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [AddCommMonoid M]
    (i : ι) (g : ι × κ → M) :
    ∑ p ∈ univ.filter fun p : ι × κ => p.1 = i, g p = ∑ k : κ, g (i, k) := by
  classical
  rw [show (univ.filter fun p : ι × κ => p.1 = i) = ({i} : Finset ι) ×ˢ (univ : Finset κ) from by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true], Finset.sum_product, Finset.sum_singleton]

/-- `sum_snorm_sq_cool` at the fibres of the first projection of a product outcome set. -/
theorem sum_snorm_sq_cool_prod {N : Type*} [Fintype N] [DecidableEq N] (v : N → ℂ)
    {A : R1 × R2 → Matrix N N ℂ} (hA : IsPVM A) (B : R1 × R2 → Matrix N N ℂ) :
    ∑ a : R1, snorm v (∑ b : R2, (A (a, b) - A (a, b) * B (a, b))) ^ 2
      ≤ ∑ p : R1 × R2, snorm v (A p - B p) ^ 2 := by
  classical
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    (sum_snorm_sq_cool v hA B Prod.fst)
  exact congrArg (fun M => snorm v M ^ 2)
    (sum_fibre_fst a fun p => A p - A p * B p).symm

/-- **The marginal step.** Alice's joint projective measurement, consistent with Bob's ordered
product `Z_b X_a`, has its `R2`-marginal consistent with `X_a` alone. -/
theorem sum_xSqNorm_marg_le {ψ : dA × dB → ℂ} {Q : R1 × R2 → Matrix dA dA ℂ}
    {Z : R2 → Matrix dB dB ℂ} (X : R1 → Matrix dB dB ℂ) (hQ : IsPVM Q) (hZ : IsPVM Z) :
    ∑ a : R1, xSqNorm ψ (∑ b : R2, Q (a, b)) (X a)
      ≤ 2 * (∑ p : R1 × R2, snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
              - aOp (Q p)) ^ 2)
        + 2 * ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
  classical
  -- the intermediate operator: the marginal with Bob's projection attached
  have hcool : ∑ a : R1, snorm ψ ((aOp (∑ b : R2, Q (a, b)) : Matrix (dA × dB) _ ℂ)
        - ∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b)) ^ 2
      ≤ ∑ p : R1 × R2, snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
          - aOp (Q p)) ^ 2 := by
    have h := sum_snorm_sq_cool_prod (ψ) hQ.aOp
      (fun p => (aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2))
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (le_trans h
      (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)))
    · refine congrArg (fun M => snorm ψ M ^ 2) ?_
      rw [aOp_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ)
          * ((aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b))
          = (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b) from by
        rw [← Matrix.mul_assoc, ← aOp_mul, hQ.idem]]
    · rw [snorm_sub_comm]
  -- the orthogonal insertion
  have horth : ∑ a : R1, snorm ψ ((∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b))
        - bOp (X a)) ^ 2
      ≤ ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
    have hsplit : ∀ a : R1, (∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b))
          - bOp (X a)
        = ∑ b : R2, (bOp (Z b) : Matrix (dA × dB) _ ℂ)
            * ((aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) - bOp (Z b * X a)) := by
      intro a
      rw [show (bOp (X a) : Matrix (dA × dB) _ ℂ) = ∑ b : R2, (bOp (Z b * X a)) from by
        rw [← bOp_sum, ← Finset.sum_mul, hZ.sum_eq_one, Matrix.one_mul],
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_sub, ← aOp_mul_bOp, ← bOp_mul,
        show Z b * (Z b * X a) = Z b * X a from by
          rw [show Z b * (Z b * X a) = Z b * Z b * X a from by noncomm_ring, hZ.idem]]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      congrArg (fun M => snorm ψ M ^ 2) (hsplit a)]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      snorm_sq_sum_proj_mul ψ (fun b => hZ.bOp.isSelfAdjoint b)
        (fun b b' hbb' => hZ.bOp.orthogonal hbb') _ univ]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    rw [xSqNorm_eq_snorm_sq]
    refine snorm_sq_mul_le_of_contraction ψ ?_ _
    rw [hZ.bOp.isSelfAdjoint, hZ.bOp.idem]
    exact proj_le_one (hZ.bOp.isSelfAdjoint b) (hZ.bOp.idem b)
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    xSqNorm_eq_snorm_sq ψ (∑ b : R2, Q (a, b)) (X a)]
  refine le_trans (sum_snorm_sq_triangle' ψ _
    (fun a => ∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b)) _) ?_
  linarith

/-- **A projective family stays projective under a relabelling of its outcomes by a bijection.** -/
theorem IsPVM.comp_equiv {N ι κ : Type*} [Fintype N] [DecidableEq N] [Fintype ι] [Fintype κ]
    {P : ι → Matrix N N ℂ} (h : IsPVM P) (e : κ ≃ ι) : IsPVM fun k => P (e k) where
  isSelfAdjoint k := h.isSelfAdjoint (e k)
  idem k := h.idem (e k)
  sum_eq_one := by
    rw [← h.sum_eq_one]
    exact Fintype.sum_bijective e e.bijective _ _ fun k => rfl

/-- **Bob's own deviation, through Alice's operator.** The three-term triangle inequality in the
one shape the consumer needs: a same-side deviation bounded by two cross-party ones. -/
theorem normSq_stateVecB_sub_le (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B₁ B₂ : Matrix dB dB ℂ) :
    ‖stateVecB ψ (B₁ - B₂)‖ ^ 2 ≤ 2 * xSqNorm ψ A B₁ + 2 * xSqNorm ψ A B₂ := by
  have htri : ‖stateVecB ψ (B₁ - B₂)‖ ≤ xNorm ψ A B₁ + xNorm ψ A B₂ := by
    rw [stateVecB_sub', xNorm, xNorm,
      show stateVecB ψ B₁ - stateVecB ψ B₂
          = (stateVecB ψ B₁ - stateVec ψ A) + (stateVec ψ A - stateVecB ψ B₂) from by abel]
    refine le_trans (norm_add_le _ _) (add_le_add (le_of_eq ?_) (le_of_eq rfl))
    rw [norm_sub_rev]
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq]
  nlinarith [norm_nonneg (stateVecB ψ (B₁ - B₂)), xNorm_nonneg ψ A B₁, xNorm_nonneg ψ A B₂,
    sq_nonneg (xNorm ψ A B₁ - xNorm ψ A B₂)]

/-- **Attaching the other party's projection to a consistent joint measurement costs nothing.**
The relation the marginal step's first term needs, from the consistency with the ordered product
alone. -/
theorem sum_snorm_sq_mul_proj_le {ψ : dA × dB → ℂ} (Q : R1 × R2 → Matrix dA dA ℂ)
    {Z : R2 → Matrix dB dB ℂ} (X : R1 → Matrix dB dB ℂ) (hZ : IsPVM Z) :
    ∑ p : R1 × R2, snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
        - aOp (Q p)) ^ 2
      ≤ 4 * ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 : snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
      - bOp (Z p.2 * X p.1)) ^ 2 ≤ xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
    rw [xSqNorm_eq_snorm_sq]
    have hcon : ((bOp (Z p.2) : Matrix (dA × dB) _ ℂ))ᴴ * bOp (Z p.2)
        ≤ (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
      rw [hZ.bOp.isSelfAdjoint, hZ.bOp.idem]
      exact proj_le_one (hZ.bOp.isSelfAdjoint p.2) (hZ.bOp.idem p.2)
    refine le_trans (le_of_eq (congrArg (fun M => snorm ψ M ^ 2) ?_))
      (snorm_sq_mul_le_of_contraction ψ hcon _)
    rw [Matrix.mul_sub, ← bOp_mul,
      show Z p.2 * (Z p.2 * X p.1) = Z p.2 * X p.1 from by
        rw [show Z p.2 * (Z p.2 * X p.1) = Z p.2 * Z p.2 * X p.1 from by noncomm_ring, hZ.idem],
      ← aOp_mul_bOp]
  have h2 : snorm ψ ((bOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) - aOp (Q p)) ^ 2
      = xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  have htri : snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2) - aOp (Q p))
      ≤ snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2) - bOp (Z p.2 * X p.1))
        + snorm ψ ((bOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) - aOp (Q p)) := by
    refine le_trans (le_of_eq (congrArg (snorm ψ) ?_)) (snorm_add_le ψ _ _)
    abel
  nlinarith [snorm_nonneg ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2) - aOp (Q p)),
    snorm_nonneg ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2) - bOp (Z p.2 * X p.1)),
    snorm_nonneg ψ ((bOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) - aOp (Q p)),
    sq_nonneg (snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2) - bOp (Z p.2 * X p.1))
      - snorm ψ ((bOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) - aOp (Q p)))]

/-- **The marginal step, packaged.** A joint projective measurement consistent with the other
party's ordered product `Z_b X_a` has its `R2`-marginal consistent with `X_a` alone, at ten times
the input. -/
theorem sum_xSqNorm_marg_le' {ψ : dA × dB → ℂ} {Q : R1 × R2 → Matrix dA dA ℂ}
    {Z : R2 → Matrix dB dB ℂ} (X : R1 → Matrix dB dB ℂ) (hQ : IsPVM Q) (hZ : IsPVM Z) :
    ∑ a : R1, xSqNorm ψ (∑ b : R2, Q (a, b)) (X a)
      ≤ 10 * ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
  have h1 := sum_xSqNorm_marg_le (ψ := ψ) X hQ hZ
  have h2 := sum_snorm_sq_mul_proj_le (ψ := ψ) Q X hZ
  linarith

end Marginal

/-! ## Transport to a twice-extended state

The consumer's two inputs live on different spaces: the joint measurement on each party's space
enlarged by one register (the Naimark dilation of `lem:qld-combined-points`), the line measurements
on the unenlarged ones. An operator with an inert ancilla has the same cross-party deviation on the
extended state as the operator itself. -/

section Transport

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

theorem xSqNorm_extVec2_aOp (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc) {P : Matrix dA dA ℂ}
    (hP : Pᴴ = P) (Q : Matrix dB dB ℂ) :
    xSqNorm (extVec2 ψ a₀ b₀) (aOp P : Matrix (dA × Anc) _ ℂ) (aOp Q : Matrix (dB × Bnc) _ ℂ)
      = xSqNorm ψ P Q := by
  rw [xSqNorm_eq_expand _ (by rw [aOp_conjTranspose, hP] :
      (aOp P : Matrix (dA × Anc) _ ℂ)ᴴ = aOp P) _,
    xSqNorm_eq_expand ψ hP Q, normSq_stateVecB_extVec2_aOp,
    show stateSqNorm (extVec2 ψ a₀ b₀) (aOp P : Matrix (dA × Anc) _ ℂ) = stateSqNorm ψ P from by
      rw [stateSqNorm_eq_qform, aOp_conjTranspose, ← aOp_mul, qform_aOp_extVec2, compress_aOp,
        ← stateSqNorm_eq_qform],
    show bornProb (extVec2 ψ a₀ b₀) (aOp P : Matrix (dA × Anc) _ ℂ)
          (aOp Q : Matrix (dB × Bnc) _ ℂ) = bornProb ψ P Q from by
      rw [bornProb_extVec2, compress_aOp, compress_aOp]]

end Transport


/-! ## The pasting lemma

The averaged statement. `A` is Alice's joint projective measurement, `R` Bob's first family --- in
the application already the coarse-graining of his answer measurement along its own outcome map ---
and `G` his second, with `Ga` Alice's copy of it. The four hypotheses are the two marginal
consistencies, the cross-party self-consistency of `G` at the *fine* level, and the collision term.

Two hypotheses of the paper's statement are absent, and both are absences rather than gaps.
`G_1` is assumed projective (in the paper it may be a POVM for `i = 1`), which makes the two
diagonal sums of the commutator expansion exactly one and removes the need for NW19's Fact 4.31.
And the cross-party self-consistency of `G` is a hypothesis here rather than derived from the
backwards consistency and Alice's self-consistency, because the consumer has it directly, at the
fine level and with no collision cost. -/

section Average

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ι R1 R2 K : Type*} [Fintype ι] [Fintype R1] [DecidableEq R1] [Fintype R2]
  [DecidableEq R2] [Fintype K] [DecidableEq K]

/-- **The pasting lemma, `k = 2`** (NW19's Fact 4.35, the paper's `lem:pasting-updated`), in Born
probability form: Alice's joint measurement agrees with the pasted sandwich up to
`delta/2 + sqrt(delta/2) + sqrt(32 delta + 4 sqrt(eta) + 2 eps)`. -/
theorem one_sub_sum_bornProb_pasteJ_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {A : ι → R1 × R2 → Matrix dA dA ℂ} {R : ι → R1 → Matrix dB dB ℂ}
    {G : ι → K → Matrix dB dB ℂ} {Ga : ι → K → Matrix dA dA ℂ} (e : ι → K → R2)
    (hA : ∀ i, IsPVM (A i)) (hR : ∀ i, IsPVM (R i)) (hG : ∀ i, IsPVM (G i))
    (hGa : ∀ i, IsPVM (Ga i)) {δ η ε : ℝ}
    (hP1 : ∑ i, w i * ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a) ≤ δ)
    (hP2 : ∑ i, w i * ∑ b : R2,
      xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b) ≤ δ)
    (hP4 : ∑ i, w i * ∑ g : K, xSqNorm ψ (Ga i g) (G i g) ≤ η)
    (hcoll : ∑ i, w i * collisionTerm ψ (R i) (G i) (Ga i) (e i) ≤ ε) :
    1 - ∑ i, w i * ∑ p : R1 × R2, bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) := by
  classical
  have hX1nn : ∀ i, 0 ≤ ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a) := fun i =>
    Finset.sum_nonneg fun a _ => xSqNorm_nonneg _ _ _
  have hEnn : ∀ i, 0 ≤ ∑ g : K, xSqNorm ψ (Ga i g) (G i g) := fun i =>
    Finset.sum_nonneg fun g _ => xSqNorm_nonneg _ _ _
  have hCnn : ∀ i, 0 ≤ ∑ a : R1, ∑ g : K,
      snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2 := fun i =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => sq_nonneg _
  -- the average of the fine-grained commutators
  have hCfavg : ∑ i, w i * (∑ a : R1, ∑ g : K,
        snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ 32 * δ + 4 * Real.sqrt η + 2 * ε := by
    have hper : ∀ i, (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
        ≤ 16 * ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a))
            + ∑ b : R2, xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b))
          + 4 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g))
          + 2 * collisionTerm ψ (R i) (G i) (Ga i) (e i) := fun i =>
      sum_snorm_sq_comm_fine_le hψ (hA i) (hR i) (hG i) (hGa i) (e i) le_rfl le_rfl
    have hjensen : ∑ i, w i * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g))
        ≤ Real.sqrt η :=
      le_trans (sum_weighted_sqrt_le w (fun i => ∑ g : K, xSqNorm ψ (Ga i g) (G i g)) hw0 hw1 hEnn)
        (Real.sqrt_le_sqrt hP4)
    calc ∑ i, w i * (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
        ≤ ∑ i, w i * (16 * ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a))
              + ∑ b : R2, xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b))
            + 4 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g))
            + 2 * collisionTerm ψ (R i) (G i) (Ga i) (e i)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hper i) (hw0 i)
      _ = 16 * (∑ i, w i * ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a))
            + 16 * (∑ i, w i * ∑ b : R2,
              xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b))
            + 4 * (∑ i, w i * Real.sqrt (∑ g : K, xSqNorm ψ (Ga i g) (G i g)))
            + 2 * ∑ i, w i * collisionTerm ψ (R i) (G i) (Ga i) (e i) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 32 * δ + 4 * Real.sqrt η + 2 * ε := by linarith
  -- the deficit splits off the weight
  have hsplit : ∑ i, w i * (1 - (∑ p : R1 × R2,
        bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p)))
      = 1 - ∑ i, w i * ∑ p : R1 × R2, bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_sub (w i) 1 _, Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_one (w i), hw1]
  rw [← hsplit]
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (one_sub_sum_bornProb_pasteJ_le' hψ (hA i) (hR i) (hG i) (e i)) (hw0 i)) ?_
  have hdist : ∑ i, w i * ((∑ b : R2,
          xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b)) / 2
        + Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2)
        + Real.sqrt (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2))
      = (∑ i, w i * ∑ b : R2,
            xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b)) / 2
        + (∑ i, w i * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2))
        + ∑ i, w i * Real.sqrt (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdist]
  have h2 : ∑ i, w i * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2)
      ≤ Real.sqrt (δ / 2) := by
    refine le_trans (sum_weighted_sqrt_le w
      (fun i => (∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) / 2) hw0 hw1
      fun i => by linarith [hX1nn i]) (Real.sqrt_le_sqrt ?_)
    rw [sum_weighted_div w (fun i => ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a)) 2]
    linarith
  have h3 : ∑ i, w i * Real.sqrt (∑ a : R1, ∑ g : K,
        snorm ψ (bOp (R i a * G i g - G i g * R i a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) :=
    le_trans (sum_weighted_sqrt_le w _ hw0 hw1 hCnn) (Real.sqrt_le_sqrt hCfavg)
  linarith

end Average

/-! ## The collision term under a product question distribution -/

section Collision

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Z Y R1 R2 K : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]

/-- **The collision term is at most the average collision probability.** The question is a pair: a
part `z` that all the measurements see, and a probe `y`, uniform and independent of `z`, that only
the outcome map sees. The Born probabilities do not depend on `y`, so the probe average acts on the
indicator alone; what is left is a POVM's total mass, which is one.

The collision probability is allowed to depend on `z`, and the conclusion is its average. The
consumer needs that: for a degenerate line the outcome map separates nothing, and what makes the
average small is that such lines are rare rather than that the bound holds everywhere. -/
theorem sum_collisionTerm_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {ν : Z → ℝ}
    (hν0 : ∀ z, 0 ≤ ν z)
    {R : Z → R1 → Matrix dB dB ℂ} {G : Z → K → Matrix dB dB ℂ} {Ga : Z → K → Matrix dA dA ℂ}
    (hR : ∀ z, IsPVM (R z)) (hG : ∀ z, IsPVM (G z)) (hGa : ∀ z, IsPVM (Ga z))
    (e : Z → Y → K → R2) {εz : Z → ℝ} (hε : ∀ z, 0 ≤ εz z)
    (hsep : ∀ (z : Z) (g g' : K), g' ≠ g →
      ((univ.filter fun y : Y => e z y g' = e z y g).card : ℝ) ≤ εz z * (Fintype.card Y : ℝ)) :
    ∑ i : Z × Y, (ν i.1 * (Fintype.card Y : ℝ)⁻¹)
        * collisionTerm ψ (R i.1) (G i.1) (Ga i.1) (e i.1 i.2) ≤ ∑ z : Z, ν z * εz z := by
  classical
  have hcardpos : (0 : ℝ) < (Fintype.card Y : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hFnn : ∀ (z : Z) (a : R1) (g g' : K),
      0 ≤ bornProb ψ (Ga z g') (R z a * G z g * R z a) := fun z a g g' =>
    bornProb_nonneg ψ ((hGa z).posSemidef g') (sandOp_posSemidef (hR z) (hG z) a g)
  -- the total mass of the cloud's Born probabilities is one
  have hmass : ∀ z : Z, ∑ a : R1, ∑ g : K, ∑ g' : K,
      bornProb ψ (Ga z g') (R z a * G z g * R z a) = 1 := by
    intro z
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        show (∑ g' : K, bornProb ψ (Ga z g') (R z a * G z g * R z a))
            = bornProb ψ 1 (R z a * G z g * R z a) from by
          rw [← (hGa z).sum_eq_one, bornProb_sum_left],
      sum_prod_eq fun (a : R1) (g : K) => bornProb ψ 1 (R z a * G z g * R z a),
      ← bornProb_sum_right, sum_sandOp (hR z) (hG z), bornProb_eq_qform, aOp_one, bOp_one,
      Matrix.one_mul, qform_one _ hψ]
  -- the probe average of the collision term, at one `z`
  have hstep : ∀ z : Z, ∑ y : Y, collisionTerm ψ (R z) (G z) (Ga z) (e z y)
      ≤ εz z * (Fintype.card Y : ℝ) := by
    intro z
    have hcol : ∀ y : Y, collisionTerm ψ (R z) (G z) (Ga z) (e z y)
        = ∑ a : R1, ∑ g : K, ∑ g' : K,
            (if g' ≠ g ∧ e z y g' = e z y g then
              bornProb ψ (Ga z g') (R z a * G z g * R z a) else 0) := by
      intro y
      rw [collisionTerm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g _ =>
        Finset.sum_filter _ _
    have hinner : ∀ (a : R1) (g g' : K),
        (∑ y : Y, (if g' ≠ g ∧ e z y g' = e z y g then
            bornProb ψ (Ga z g') (R z a * G z g * R z a) else 0))
          ≤ (εz z * (Fintype.card Y : ℝ)) * bornProb ψ (Ga z g') (R z a * G z g * R z a) := by
      intro a g g'
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      by_cases hne : g' = g
      · rw [show (univ.filter fun y : Y => g' ≠ g ∧ e z y g' = e z y g) = ∅ from by
          ext y; simp [hne], Finset.card_empty, Nat.cast_zero, zero_mul]
        exact mul_nonneg (mul_nonneg (hε z) (le_of_lt hcardpos)) (hFnn z a g g')
      · rw [show (univ.filter fun y : Y => g' ≠ g ∧ e z y g' = e z y g)
            = univ.filter fun y : Y => e z y g' = e z y g from by ext y; simp [hne]]
        exact mul_le_mul_of_nonneg_right (hsep z g g' hne) (hFnn z a g g')
    rw [Finset.sum_congr rfl fun y (_ : y ∈ univ) => hcol y, sum_comm4]
    calc ∑ a : R1, ∑ g : K, ∑ g' : K, ∑ y : Y,
            (if g' ≠ g ∧ e z y g' = e z y g then
              bornProb ψ (Ga z g') (R z a * G z g * R z a) else 0)
        ≤ ∑ a : R1, ∑ g : K, ∑ g' : K,
            (εz z * (Fintype.card Y : ℝ)) * bornProb ψ (Ga z g') (R z a * G z g * R z a) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun g _ =>
            Finset.sum_le_sum fun g' _ => hinner a g g'
      _ = (εz z * (Fintype.card Y : ℝ)) * ∑ a : R1, ∑ g : K, ∑ g' : K,
            bornProb ψ (Ga z g') (R z a * G z g * R z a) := by
          simp only [Finset.mul_sum]
      _ = εz z * (Fintype.card Y : ℝ) := by rw [hmass z, mul_one]
  -- the weighted sum over the product
  rw [← sum_prod_eq fun (z : Z) (y : Y) => (ν z * (Fintype.card Y : ℝ)⁻¹)
    * collisionTerm ψ (R z) (G z) (Ga z) (e z y)]
  refine Finset.sum_le_sum fun z _ => ?_
  have hne : (Fintype.card Y : ℝ) ≠ 0 := ne_of_gt hcardpos
  rw [← Finset.mul_sum]
  calc (ν z * (Fintype.card Y : ℝ)⁻¹) * ∑ y : Y, collisionTerm ψ (R z) (G z) (Ga z) (e z y)
      ≤ (ν z * (Fintype.card Y : ℝ)⁻¹) * (εz z * (Fintype.card Y : ℝ)) :=
        mul_le_mul_of_nonneg_left (hstep z)
          (mul_nonneg (hν0 z) (le_of_lt (inv_pos.mpr hcardpos)))
    _ = ν z * εz z := by field_simp

end Collision

end MIPRE

end
