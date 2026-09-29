/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Sandwich

@[expose] public section

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

The argument is proved once, for a bipartite model (`MIPRE/Foundations/BipartiteModel.lean`) with
the first player's joint measurement in `𝒜` and the second player's two families in `ℬ`: the pasting
lemma is `BipartiteModel.one_sub_sum_bornProb_pasteJ_le`, and NW19's Fact 4.31 is
`StateModel.qform_sum_ge_of_close`. The coarse-graining `fibSumIn` (of which the matrix `fibSum` is
the instance) and the pasted family `pasteJ` are defined in any ring, and the sandwich identities
they rest on are those of projective measurements in a `⋆`-ring (`IsPVMIn.conj_eq_gram`,
`IsPVMIn.sum_pasteJ`). The matrix statements are the instances in the tensor-product model
`BipartiteModel.tensor ψ`. Where the square of a positive contraction is bounded (`P² ≤ P` for
`0 ≤ P ≤ 1`), the hypothesis is on the operators represented on the Hilbert space, where the
functional calculus proves it, and the matrix instances discharge it from matrix positivity; the
matrix inequality `sum_sq_le_one_of_sum_eq_one` is itself the instance of
`sum_mul_self_le_one_of_sum_le_one`, stated in any ordered algebra with a functional calculus. Only
the transport to a twice-extended state (`xSqNorm_extVec2_aOp`) is about matrices alone.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## The coarse-graining of a family, and the product question distribution -/

section Setup

/-- The fibre sum of a family along an outcome map --- its coarse-graining --- in any additive
monoid, so that the family may be matrices or elements of a player's algebra. -/
def fibSumIn {α β M : Type*} [Fintype α] [DecidableEq β] [AddCommMonoid M] (G : α → M)
    (e : α → β) (b : β) : M :=
  ∑ g ∈ univ.filter fun g => e g = b, G g

/-- The coarse-graining of a projective measurement in a `⋆`-ring is projective. -/
theorem isPVMIn_fibSumIn {S α β : Type*} [Ring S] [StarRing S] [Fintype α] [Fintype β]
    [DecidableEq β] {G : α → S} (h : IsPVMIn G) (e : α → β) : IsPVMIn (fibSumIn G e) :=
  h.coarse e

/-- The fibre sum of a family of operators along an outcome map --- its coarse-graining. It is
`fibSumIn` in a matrix algebra (`fibSum_eq_fibSumIn`); the square matrix type stays in the
signature, because consumers let it fix the dimension. -/
def fibSum {α β N : Type*} [Fintype α] [DecidableEq β] (G : α → Matrix N N ℂ) (e : α → β)
    (b : β) : Matrix N N ℂ :=
  ∑ g ∈ univ.filter fun g => e g = b, G g

theorem fibSum_eq_fibSumIn {α β N : Type*} [Fintype α] [DecidableEq β] (G : α → Matrix N N ℂ)
    (e : α → β) (b : β) : fibSum G e b = fibSumIn G e b :=
  rfl

variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  (isPVMIn_fibSumIn h.toIn e).toIsPVM

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

/-! ## The pasted family, and sandwiches of projective measurements in a `⋆`-ring

The algebra of the pasting sandwich uses only that the families are projective measurements, so
it is stated in any `⋆`-ring (`MIPRE/Foundations/Measurement.lean`): a player's algebra, or a
matrix algebra. Unlike `sand` of `MIPRE/Foundations/Sandwich.lean`, the two families here have
different outcome sets. -/

/-- **The pasted POVM**: the paper's `J_{[eval = (a_1, a_2)]}`. `R` is already the coarse-graining
of the paper's `G_1` along its own outcome map --- only `R`'s projectivity is used, so it enters
as a single projective family, and the inner coarse-graining is the consumer's business. It is
defined in any semiring, so that the two families may be matrices or elements of the second
player's algebra. -/
def pasteJ {S R1 R2 K : Type*} [NonUnitalNonAssocSemiring S] [DecidableEq R2] [Fintype K]
    (R : R1 → S) (G : K → S) (e : K → R2) (p : R1 × R2) : S :=
  ∑ g ∈ univ.filter fun g => e g = p.2, G g * R p.1 * G g

namespace IsPVMIn

variable {S : Type*} [Ring S] [StarRing S] {A B : Type*} [Fintype A] [Fintype B]
  {X : A → S} {Z : B → S}

/-- The elements of a projective measurement satisfy `∑ P* P = 1`. -/
theorem sum_star_mul_self (hX : IsPVMIn X) : ∑ a, star (X a) * X a = 1 := by
  simp only [hX.star_eq, hX.idem]
  exact hX.sum_eq_one

/-- **A projective measurement stays projective under a relabelling of its outcomes by a
bijection.** -/
theorem comp_equiv (hX : IsPVMIn X) (e : B ≃ A) : IsPVMIn fun b => X (e b) where
  star_eq b := hX.star_eq (e b)
  idem b := hX.idem (e b)
  sum_eq_one := by
    rw [← hX.sum_eq_one]
    exact Fintype.sum_bijective e e.bijective _ _ fun b => rfl
  orthogonal {b b'} hbb' := hX.orthogonal fun h => hbb' (e.injective h)

/-- **One projective measurement's element conjugated by another's is a Gram element**:
`Z_b X_a Z_b = (X_a Z_b)* (X_a Z_b)`, the two families on any outcome sets. This is where the
positivity of both pasting sandwiches comes from. -/
theorem conj_eq_gram (hX : IsPVMIn X) (hZ : IsPVMIn Z) (a : A) (b : B) :
    Z b * X a * Z b = star (X a * Z b) * (X a * Z b) := by
  rw [star_mul, hX.star_eq, hZ.star_eq]
  calc Z b * X a * Z b = Z b * (X a * X a) * Z b := by rw [hX.idem]
    _ = Z b * X a * (X a * Z b) := by noncomm_ring

/-- The conjugates `Z_b X_a Z_b` sum to one, the conjugating index second: the inner family sums
away against the outer one's projectivity. -/
theorem sum_conj (hX : IsPVMIn X) (hZ : IsPVMIn Z) : ∑ p : A × B, Z p.2 * X p.1 * Z p.2 = 1 := by
  rw [Fintype.sum_prod_type_right]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
      (∑ a : A, Z b * X a * Z b) = Z b from by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hX.sum_eq_one, mul_one, hZ.idem]]
  exact hZ.sum_eq_one

/-- The conjugates `Z_b X_a Z_b` sum to one, the conjugating index first. -/
theorem sum_conj' (hX : IsPVMIn X) (hZ : IsPVMIn Z) :
    ∑ p : B × A, Z p.1 * X p.2 * Z p.1 = 1 := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
      (∑ a : A, Z b * X a * Z b) = Z b from by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hX.sum_eq_one, mul_one, hZ.idem]]
  exact hZ.sum_eq_one

variable {R1 R2 K : Type*} [Fintype R1] [Fintype R2] [DecidableEq R2] [Fintype K]
  {R : R1 → S} {G : K → S}

/-- **The pasted family sums to one.** -/
theorem sum_pasteJ (hR : IsPVMIn R) (hG : IsPVMIn G) (e : K → R2) :
    ∑ p : R1 × R2, pasteJ R G e p = 1 := by
  classical
  have h : ∀ a : R1, ∑ b : R2, pasteJ R G e (a, b) = ∑ g : K, G g * R a * G g := by
    intro a
    rw [← Finset.sum_fiberwise (univ : Finset K) e fun g => G g * R a * G g]
    rfl
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a (_ : a ∈ univ) => h a,
    sum_prod_eq fun (a : R1) (g : K) => G g * R a * G g, hR.sum_conj hG]

/-- **The pasted family is a POVM** in a star-ordered ring: each of its terms is a Gram
element. -/
theorem pasteJ_nonneg [PartialOrder S] [StarOrderedRing S] (hR : IsPVMIn R) (hG : IsPVMIn G)
    (e : K → R2) (p : R1 × R2) : 0 ≤ pasteJ R G e p :=
  Finset.sum_nonneg fun g _ => by
    rw [hR.conj_eq_gram hG p.1 g]
    exact star_mul_self_nonneg _

end IsPVMIn

/-! ## Positive contractions -/

/-- **A family of positive elements summing to at most one has its squares summing to at most
one**, in any ordered algebra with a continuous functional calculus --- the matrices and the
operators on a Hilbert space alike: `P² ≤ P` for each, because `P (1 - P)` is a product of
commuting positive elements. -/
theorem sum_mul_self_le_one_of_sum_le_one {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A] {C : Type*} [Fintype C] {P : C → A} (hP0 : ∀ c, 0 ≤ P c)
    (hPsum : ∑ c, P c ≤ 1) : ∑ c, P c * P c ≤ 1 := by
  classical
  have hsq : ∀ c, P c * P c ≤ P c := fun c => by
    have hP1 : P c ≤ 1 := (Finset.single_le_sum (fun c' _ => hP0 c') (mem_univ c)).trans hPsum
    have hprod : 0 ≤ P c * (1 - P c) :=
      ((Commute.one_right (P c)).sub_right (Commute.refl (P c))).mul_nonneg (hP0 c)
        (sub_nonneg.2 hP1)
    rw [mul_sub, mul_one] at hprod
    exact sub_nonneg.1 hprod
  exact (Finset.sum_le_sum fun c _ => hsq c).trans hPsum

/-! ## In a model

The estimates are proved once. Those about a single represented algebra --- NW19's Fact 4.31, the
two mass bounds, the commutator expansion --- are stated for a state model
(`MIPRE/Foundations/StateModel.lean`); the pasting argument itself for a bipartite model, with the
first player's joint measurement `A` and copy `Ga` of `G` in `𝒜`, and the second player's families
`R` and `G` in `ℬ`. The matrix statements further down are the instances in the tensor-product
model. -/

namespace StateModel

open scoped InnerProductSpace

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (M : StateModel 𝒞)

/-- **The quadratic form does not see the adjoint**: it is a real part, and the adjoint
conjugates. -/
theorem qform_star (T : 𝒞) : M.qform (star T) = M.qform T := by
  show (⟪M.ψ, M.π (star T) M.ψ⟫_ℂ).re = (⟪M.ψ, M.π T M.ψ⟫_ℂ).re
  rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, Complex.conj_re]

/-- A Gram element is represented by a positive operator. -/
theorem π_star_mul_self_nonneg (x : 𝒞) : 0 ≤ M.π (star x * x) := by
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

/-- An element represented between `0` and `1` has `‖π T ψ‖² ≤ ⟨ψ, π T ψ⟩`, because `t² ≤ t`
there. -/
theorem snorm_sq_le_qform {T : 𝒞} (h0 : 0 ≤ M.π T) (h1 : M.π T ≤ 1) :
    M.snorm T ^ 2 ≤ M.qform T := by
  rw [M.snorm_sq_eq_qform]
  show Op.qform M.ψ (M.π (star T * T)) ≤ Op.qform M.ψ (M.π T)
  rw [map_mul, map_star, (IsSelfAdjoint.of_nonneg h0).star_eq]
  exact Op.qform_mono _ (Op.mul_self_le_self h0 h1)

/-- An element represented between `0` and `1` has `⟨ψ, π(T²) ψ⟩ ≤ ⟨ψ, π T ψ⟩`. -/
theorem qform_mul_self_le {T : 𝒞} (h0 : 0 ≤ M.π T) (h1 : M.π T ≤ 1) :
    M.qform (T * T) ≤ M.qform T := by
  show Op.qform M.ψ (M.π (T * T)) ≤ Op.qform M.ψ (M.π T)
  rw [map_mul]
  exact Op.qform_mono _ (Op.mul_self_le_self h0 h1)

/-! ### Two ways for a family of squared state norms to sum to at most one -/

/-- **Mutually orthogonal projections**: the sum is a projection, hence a contraction. -/
theorem sum_snorm_sq_orth_le_one (hψ : ‖M.ψ‖ = 1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → 𝒞) (hsa : ∀ i, star (P i) = P i) (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    ∑ i, M.snorm (P i) ^ 2 ≤ 1 := by
  have h := M.snorm_sq_sum_proj_mul hsa horth (fun _ => 1) univ
  simp only [mul_one] at h
  rw [← h]
  have h1 := M.snorm_le_one_of_isStarProjection hψ
    (isStarProjection_sum_of_orth (fun i => ⟨hidem i, hsa i⟩) horth)
  nlinarith [M.snorm_nonneg (∑ i, P i)]

/-- **A POVM**, positive on the Hilbert space: each square is below the element, and the elements
sum to at most the identity. -/
theorem sum_snorm_sq_povm_le_one (hψ : ‖M.ψ‖ = 1) {ι : Type*} [Fintype ι] {P : ι → 𝒞}
    (hP0 : ∀ i, 0 ≤ M.π (P i)) (hPsum : ∑ i, M.π (P i) ≤ 1) :
    ∑ i, M.snorm (P i) ^ 2 ≤ 1 := by
  classical
  have hP1 : ∀ i, M.π (P i) ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => hP0 j) (mem_univ i)).trans hPsum
  calc ∑ i, M.snorm (P i) ^ 2 ≤ ∑ i, M.qform (P i) :=
        Finset.sum_le_sum fun i _ => M.snorm_sq_le_qform (hP0 i) (hP1 i)
    _ = Op.qform M.ψ (∑ i, M.π (P i)) := by rw [Op.qform_sum]; rfl
    _ ≤ Op.qform M.ψ 1 := Op.qform_mono _ hPsum
    _ = 1 := Op.qform_one _ hψ

/-! ### A sub-measurement close to a projective measurement -/

/-- **NW19's Fact 4.31.** A family represented by positive operators summing to at most the
identity, which is `delta`-close to a projective measurement on the state, carries all but
`2 sqrt(delta)` of the mass. Two Cauchy--Schwarz steps against the same deviation: one moves from
`1` to `sum <Q_c P_c>`, the other from there to `sum <P_c^2>`, and `P_c^2 <= P_c` on the Hilbert
space. -/
theorem qform_sum_ge_of_close (hψ : ‖M.ψ‖ = 1) {C : Type*} [Fintype C] {Q P : C → 𝒞}
    (hQ : IsPVMIn Q) (hP0 : ∀ c, 0 ≤ M.π (P c)) (hPsum : ∑ c, M.π (P c) ≤ 1) {δ : ℝ}
    (hclose : ∑ c, M.snorm (Q c - P c) ^ 2 ≤ δ) :
    1 - 2 * Real.sqrt δ ≤ ∑ c, M.qform (P c) := by
  classical
  have hPsa : ∀ c, M.π (star (P c)) = M.π (P c) := fun c => by
    rw [map_star, (IsSelfAdjoint.of_nonneg (hP0 c)).star_eq]
  have hP1 : ∀ c, M.π (P c) ≤ 1 := fun c =>
    (Finset.single_le_sum (fun c' _ => hP0 c') (mem_univ c)).trans hPsum
  -- the two mass sums
  have hQmass : ∑ c, M.snorm (Q c) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [M.snorm_sq_eq_qform, hQ.star_eq c, hQ.idem c], ← M.qform_sum, hQ.sum_eq_one,
      M.qform_one hψ]
  have hPmass : ∑ c, M.snorm (P c) ^ 2 ≤ 1 := M.sum_snorm_sq_povm_le_one hψ hP0 hPsum
  -- the two Cauchy--Schwarz steps
  have hcs : ∀ (G K : C → 𝒞), (∀ c, M.π (star (G c)) = M.π (G c)) →
      |∑ c, M.qform (G c * K c)|
        ≤ Real.sqrt (∑ c, M.snorm (G c) ^ 2) * Real.sqrt (∑ c, M.snorm (K c) ^ 2) := by
    intro G K hG
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun c _ => ?_)
      (sum_mul_le_sqrt (fun c => M.snorm (G c)) (fun c => M.snorm (K c)))
    have h := M.abs_qform_star_mul_le (G c) (K c)
    have he : M.qform (star (G c) * K c) = M.qform (G c * K c) := by
      show Op.qform M.ψ (M.π (star (G c) * K c)) = Op.qform M.ψ (M.π (G c * K c))
      rw [map_mul, map_mul, hG c]
    rwa [he] at h
  have hstep1 : |∑ c, M.qform (Q c * (Q c - P c))| ≤ Real.sqrt δ := by
    refine le_trans (hcs Q (fun c => Q c - P c) fun c => by rw [hQ.star_eq]) ?_
    rw [hQmass, Real.sqrt_one, one_mul]
    exact Real.sqrt_le_sqrt hclose
  have hstep2 : |∑ c, M.qform ((Q c - P c) * P c)| ≤ Real.sqrt δ := by
    refine le_trans (hcs (fun c => Q c - P c) P fun c => by
      rw [star_sub, map_sub, map_sub, hQ.star_eq, hPsa]) ?_
    calc Real.sqrt (∑ c, M.snorm (Q c - P c) ^ 2) * Real.sqrt (∑ c, M.snorm (P c) ^ 2)
        ≤ Real.sqrt δ * Real.sqrt 1 :=
          mul_le_mul (Real.sqrt_le_sqrt hclose) (Real.sqrt_le_sqrt hPmass)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt δ := by rw [Real.sqrt_one, mul_one]
  -- unwinding the two identities
  have heq1 : ∑ c, M.qform (Q c * (Q c - P c)) = 1 - ∑ c, M.qform (Q c * P c) := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [show Q c * (Q c - P c) = Q c - Q c * P c from by rw [mul_sub, hQ.idem c],
        M.qform_sub], Finset.sum_sub_distrib, ← M.qform_sum, hQ.sum_eq_one, M.qform_one hψ]
  have heq2 : ∑ c, M.qform ((Q c - P c) * P c)
      = (∑ c, M.qform (Q c * P c)) - ∑ c, M.qform (P c * P c) := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [sub_mul, M.qform_sub], Finset.sum_sub_distrib]
  have hlow : 1 - 2 * Real.sqrt δ ≤ ∑ c, M.qform (P c * P c) := by
    have h1 := (abs_le.mp hstep1).2
    have h2 := (abs_le.mp hstep2).2
    rw [heq1] at h1
    rw [heq2] at h2
    linarith
  exact le_trans hlow (Finset.sum_le_sum fun c _ => M.qform_mul_self_le (hP0 c) (hP1 c))

/-- `sum_snorm_sq_cool` at the fibres of the first projection of a product outcome set. -/
theorem sum_snorm_sq_cool_prod {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2]
    [DecidableEq R2] {A : R1 × R2 → 𝒞} (hA : IsPVMIn A) (B : R1 × R2 → 𝒞) :
    ∑ a : R1, M.snorm (∑ b : R2, (A (a, b) - A (a, b) * B (a, b))) ^ 2
      ≤ ∑ p : R1 × R2, M.snorm (A p - B p) ^ 2 := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    (M.sum_snorm_sq_cool hA B Prod.fst)
  refine congrArg (fun T => M.snorm T ^ 2) ?_
  rw [Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_eq_single_of_mem a (mem_univ a) fun a' _ ha' =>
      Finset.sum_eq_zero fun b _ => ite_eq_right ha']
  exact Finset.sum_congr rfl fun b _ => (ite_eq_left rfl).symm

/-- **The commutator sum of two projective families, as the deficit of one overlap.** Both the
fine-grained and the coarse-grained commutators of the pasting lemma have this shape, and it is
what lets them be compared. -/
theorem sum_snorm_sq_comm_eq (hψ : ‖M.ψ‖ = 1) {R1 G2 : Type*} [Fintype R1] [Fintype G2]
    {A : R1 → 𝒞} {B : G2 → 𝒞} (hA : IsPVMIn A) (hB : IsPVMIn B) :
    ∑ a : R1, ∑ g : G2, M.snorm (A a * B g - B g * A a) ^ 2
      = 2 - 2 * ∑ a : R1, ∑ g : G2, M.qform (A a * B g * A a * B g) := by
  -- the expansion of one squared deviation
  have hterm : ∀ (a : R1) (g : G2), M.snorm (A a * B g - B g * A a) ^ 2
      = M.qform (A a * B g * A a) + M.qform (B g * A a * B g)
        - M.qform (A a * B g * A a * B g) - M.qform (B g * A a * B g * A a) := by
    intro a g
    rw [M.snorm_sq_eq_qform,
      show star (A a * B g - B g * A a) * (A a * B g - B g * A a)
          = A a * B g * A a + B g * A a * B g
            - A a * B g * A a * B g - B g * A a * B g * A a from by
        rw [star_sub, star_mul, star_mul, hA.star_eq, hB.star_eq]
        calc (B g * A a - A a * B g) * (A a * B g - B g * A a)
            = B g * (A a * A a) * B g + A a * (B g * B g) * A a
              - B g * A a * B g * A a - A a * B g * A a * B g := by noncomm_ring
          _ = _ := by rw [hA.idem, hB.idem]; abel,
      M.qform_sub, M.qform_sub, M.qform_add]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun g (_ : g ∈ univ) => hterm a g]
  -- the two diagonal sums are exactly one, and the two off-diagonal sums are equal
  have h1 : ∑ a : R1, ∑ g : G2, M.qform (A a * B g * A a) = 1 := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
        rw [← M.qform_sum, ← Finset.sum_mul, ← Finset.mul_sum, hB.sum_eq_one, mul_one,
          hA.idem],
      ← M.qform_sum, hA.sum_eq_one, M.qform_one hψ]
  have h2 : ∑ a : R1, ∑ g : G2, M.qform (B g * A a * B g) = 1 := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun g (_ : g ∈ univ) => by
        rw [← M.qform_sum, ← Finset.sum_mul, ← Finset.mul_sum, hA.sum_eq_one, mul_one,
          hB.idem],
      ← M.qform_sum, hB.sum_eq_one, M.qform_one hψ]
  have h3 : ∑ a : R1, ∑ g : G2, M.qform (B g * A a * B g * A a)
      = ∑ a : R1, ∑ g : G2, M.qform (A a * B g * A a * B g) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g _ => ?_
    rw [← M.qform_star (A a * B g * A a * B g)]
    congr 1
    simp only [star_mul, hA.star_eq, hB.star_eq]
    noncomm_ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1, h2, h3]
  ring

end StateModel

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-! ### Born probabilities of projections -/

theorem bornProb_sub_right (a : 𝒜) (b b' : ℬ) :
    M.bornProb a (b - b') = M.bornProb a b - M.bornProb a b' := by
  unfold bornProb
  rw [map_sub, mul_sub, M.qform_sub]

/-- A projection of the first player against a Gram element of the second: the Born probability
is the squared norm of a product. -/
theorem snorm_sq_πA_mul_πB {p : 𝒜} (hp : IsStarProjection p) (y : ℬ) :
    M.snorm (M.πA p * M.πB y) ^ 2 = M.bornProb p (star y * y) := by
  rw [M.snorm_sq_eq_qform, M.star_πA_mul_πB, M.πA_mul_πB_mul, hp.isSelfAdjoint.star_eq,
    hp.isIdempotentElem.eq]
  rfl

theorem bornProb_gram_nonneg {p : 𝒜} (hp : IsStarProjection p) (y : ℬ) :
    0 ≤ M.bornProb p (star y * y) := by
  rw [← M.snorm_sq_πA_mul_πB hp y]
  exact sq_nonneg _

/-- A product of two commuting projections is a projection, so its squared state norm is its
quadratic form --- a Born probability. -/
theorem snorm_sq_prod_proj {p : 𝒜} {q : ℬ} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : M.snorm (M.πA p * M.πB q) ^ 2 = M.bornProb p q := by
  rw [M.snorm_sq_πA_mul_πB hp, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq]

theorem bornProb_proj_nonneg {p : 𝒜} {q : ℬ} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : 0 ≤ M.bornProb p q := by
  rw [← M.snorm_sq_prod_proj hp hq]
  exact sq_nonneg _

/-! ### Coarse-graining a pair of projective families, on the two players -/

section Coarse

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- Coarse-graining adds the off-diagonal Born probabilities, which are nonnegative. -/
theorem sum_bornProb_le_fibSum {X : α → 𝒜} {X' : α → ℬ} (hX : IsPVMIn X) (hX' : IsPVMIn X')
    (e : α → β) :
    ∑ a, M.bornProb (X a) (X' a) ≤ ∑ b, M.bornProb (fibSumIn X e b) (fibSumIn X' e b) := by
  have hfib : ∀ b : β, M.bornProb (fibSumIn X e b) (fibSumIn X' e b)
      = ∑ a ∈ univ.filter fun a => e a = b, ∑ a' ∈ univ.filter fun a' => e a' = b,
          M.bornProb (X a) (X' a') := fun b => by rw [fibSumIn, fibSumIn, M.bornProb_sum_sum]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hfib b]
  have hdiag : ∀ b : β, ∑ a ∈ univ.filter fun a => e a = b, M.bornProb (X a) (X' a)
      ≤ ∑ a ∈ univ.filter fun a => e a = b, ∑ a' ∈ univ.filter fun a' => e a' = b,
          M.bornProb (X a) (X' a') := fun b =>
    Finset.sum_le_sum fun a ha => Finset.single_le_sum
      (fun a' _ => M.bornProb_proj_nonneg (hX.isStarProjection a) (hX'.isStarProjection a')) ha
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun b (_ : b ∈ univ) => hdiag b)
  exact (Finset.sum_fiberwise (univ : Finset α) e fun a => M.bornProb (X a) (X' a)).symm

/-- **Coarse-graining two projective families the same way costs nothing**, in the `fibSumIn` form
that the pasting lemma needs. -/
theorem sum_xSqNorm_fibSum_le (hψ : ‖M.ψ‖ = 1) {X : α → 𝒜} {X' : α → ℬ} (hX : IsPVMIn X)
    (hX' : IsPVMIn X') (e : α → β) :
    ∑ b, M.xSqNorm (fibSumIn X e b) (fibSumIn X' e b) ≤ ∑ a, M.xSqNorm (X a) (X' a) := by
  have e1 := M.one_sub_sum_bornProb_eq hψ (isPVMIn_fibSumIn hX e) (isPVMIn_fibSumIn hX' e)
  have e2 := M.one_sub_sum_bornProb_eq hψ hX hX'
  have e3 := M.sum_bornProb_le_fibSum hX hX' e
  linarith

end Coarse

/-- **The commutator sum of two projective families of the second player**, as the deficit of
one overlap. -/
theorem sum_snorm_sq_comm_eq (hψ : ‖M.ψ‖ = 1) {R1 G2 : Type*} [Fintype R1] [Fintype G2]
    {A : R1 → ℬ} {B : G2 → ℬ} (hA : IsPVMIn A) (hB : IsPVMIn B) :
    ∑ a : R1, ∑ g : G2, M.swap.stateSqNorm (A a * B g - B g * A a)
      = 2 - 2 * ∑ a : R1, ∑ g : G2, M.qform (M.πB (A a * B g * A a * B g)) := by
  have h := M.toStateModel.sum_snorm_sq_comm_eq hψ (hA.map M.πB) (hB.map M.πB)
  simp only [← map_mul, ← map_sub] at h
  exact h

/-! ### The sandwich family of the pasting lemma -/

section Sand2

variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K] {R : R1 → ℬ} {G : K → ℬ}

/-- The squared state norms of the pasting sandwich sum to at most one: it is a POVM of Gram
elements, positive on the Hilbert space whatever the order of `ℬ`. -/
theorem sum_snorm_sq_sandOp_le_one (hψ : ‖M.ψ‖ = 1) (hR : IsPVMIn R) (hG : IsPVMIn G) :
    ∑ a : R1, ∑ g : K, M.swap.stateSqNorm (R a * G g * R a) ≤ 1 := by
  have hpos : ∀ p : R1 × K, 0 ≤ M.π (M.πB (R p.1 * G p.2 * R p.1)) := fun p => by
    rw [hG.conj_eq_gram hR p.2 p.1, map_mul M.πB, map_star M.πB]
    exact M.toStateModel.π_star_mul_self_nonneg _
  have hsum : ∑ p : R1 × K, M.π (M.πB (R p.1 * G p.2 * R p.1)) ≤ 1 := by
    rw [← map_sum, ← map_sum, hG.sum_conj' hR, map_one, map_one]
  rw [sum_prod_eq fun (a : R1) (g : K) => M.swap.stateSqNorm (R a * G g * R a)]
  exact M.toStateModel.sum_snorm_sq_povm_le_one hψ hpos hsum

/-- **The cloud step.** Replacing the second player's outer factor by the first player's copy of
it costs the square root of their cross-party deviation --- and nothing depending on the size of
`K`, because one factor `R a` stays in front of the deviation, so the sum over `a` is absorbed
rather than repeated. -/
theorem abs_sigma_sub_cloud_le (hψ : ‖M.ψ‖ = 1) {Ga : K → 𝒜} (hR : IsPVMIn R)
    (hG : IsPVMIn G) :
    |(∑ a : R1, ∑ g : K, M.qform (M.πB (R a * G g * R a * G g)))
        - ∑ a : R1, ∑ g : K, M.bornProb (Ga g) (R a * G g * R a)|
      ≤ Real.sqrt (∑ g : K, M.xSqNorm (Ga g) (G g)) := by
  have hsa : ∀ (a : R1) (g : K), star (M.πB (R a * G g * R a)) = M.πB (R a * G g * R a) := by
    intro a g
    rw [← map_star, star_mul, star_mul, hR.star_eq, hG.star_eq, mul_assoc]
  -- the one identity: an `R a` in front of the deviation is free, because the sandwich already
  -- ends in `R a`
  have hM : ∀ (a : R1) (g : K),
      M.πB (R a * G g * R a) * (M.πB (R a) * (M.πB (G g) - M.πA (Ga g)))
        = M.πB (R a * G g * R a * G g) - M.πA (Ga g) * M.πB (R a * G g * R a) := by
    intro a g
    have hRR : R a * G g * R a * R a = R a * G g * R a := by
      rw [mul_assoc (R a * G g), hR.idem]
    rw [mul_sub, mul_sub, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, hRR,
      ← (M.commute (Ga g) (R a * G g * R a)).eq]
  have hterm : ∀ (a : R1) (g : K),
      M.qform (M.πB (R a * G g * R a * G g)) - M.bornProb (Ga g) (R a * G g * R a)
        = M.qform (star (M.πB (R a * G g * R a))
            * (M.πB (R a) * (M.πB (G g) - M.πA (Ga g)))) := by
    intro a g
    rw [hsa a g, hM a g, M.qform_sub]
    rfl
  have hsum : (∑ a : R1, ∑ g : K, M.qform (M.πB (R a * G g * R a * G g)))
        - ∑ a : R1, ∑ g : K, M.bornProb (Ga g) (R a * G g * R a)
      = ∑ a : R1, ∑ g : K, M.qform (star (M.πB (R a * G g * R a))
          * (M.πB (R a) * (M.πB (G g) - M.πA (Ga g)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hterm a g
  rw [hsum]
  -- the two mass bounds, then Cauchy--Schwarz
  have hmass1 : ∑ a : R1, ∑ g : K, M.snorm (M.πB (R a * G g * R a)) ^ 2 ≤ 1 :=
    M.sum_snorm_sq_sandOp_le_one hψ hR hG
  have hmass2 : ∑ a : R1, ∑ g : K, M.snorm (M.πB (R a) * (M.πB (G g) - M.πA (Ga g))) ^ 2
      ≤ ∑ g : K, M.xSqNorm (Ga g) (G g) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun g _ => ?_
    refine le_trans (M.sum_snorm_sq_mul_le (fun a => M.πB (R a))
      (M.isColContraction_of_isPVMIn (hR.map M.πB)) (M.πB (G g) - M.πA (Ga g))) (le_of_eq ?_)
    rw [M.snorm_sub_comm]
    rfl
  refine le_trans (abs_sum_sum_le_sqrt _
    (fun a g => M.snorm (M.πB (R a * G g * R a)))
    (fun a g => M.snorm (M.πB (R a) * (M.πB (G g) - M.πA (Ga g))))
    fun a g => M.abs_qform_star_mul_le _ _) ?_
  calc Real.sqrt (∑ a : R1, ∑ g : K, M.snorm (M.πB (R a * G g * R a)) ^ 2)
        * Real.sqrt (∑ a : R1, ∑ g : K, M.snorm (M.πB (R a) * (M.πB (G g) - M.πA (Ga g))) ^ 2)
      ≤ Real.sqrt 1 * Real.sqrt (∑ g : K, M.xSqNorm (Ga g) (G g)) :=
        mul_le_mul (Real.sqrt_le_sqrt hmass1) (Real.sqrt_le_sqrt hmass2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ g : K, M.xSqNorm (Ga g) (G g)) := by rw [Real.sqrt_one, one_mul]

/-- **A mutually orthogonal family of products of commuting projections** has its squared state
norms summing to at most one. The first player's factor need not be a measurement in its own
right: only self-adjointness, idempotence and orthogonality along the first index are used. -/
theorem sum_snorm_sq_prod_le_one (hψ : ‖M.ψ‖ = 1) {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (P : ι → κ → 𝒜) (Q : κ → ℬ)
    (hPsa : ∀ i k, star (P i k) = P i k) (hPidem : ∀ i k, P i k * P i k = P i k)
    (hPorth : ∀ (i j : ι) (k : κ), i ≠ j → P i k * P j k = 0) (hQ : IsPVMIn Q) :
    ∑ i, ∑ k, M.snorm (M.πA (P i k) * M.πB (Q k)) ^ 2 ≤ 1 := by
  have hsa : ∀ p : ι × κ, star (M.πA (P p.1 p.2) * M.πB (Q p.2))
      = M.πA (P p.1 p.2) * M.πB (Q p.2) := by
    intro p
    rw [M.star_πA_mul_πB, hPsa, hQ.star_eq]
  have hidem : ∀ p : ι × κ, M.πA (P p.1 p.2) * M.πB (Q p.2) * (M.πA (P p.1 p.2) * M.πB (Q p.2))
      = M.πA (P p.1 p.2) * M.πB (Q p.2) := by
    intro p
    rw [M.πA_mul_πB_mul, hPidem, hQ.idem]
  have horth : ∀ p p' : ι × κ, p ≠ p' →
      M.πA (P p.1 p.2) * M.πB (Q p.2) * (M.πA (P p'.1 p'.2) * M.πB (Q p'.2)) = 0 := by
    intro p p' hne
    rw [M.πA_mul_πB_mul]
    by_cases h2 : p.2 = p'.2
    · have h1 : p.1 ≠ p'.1 := fun h => hne (Prod.ext h h2)
      rw [← h2, hPorth p.1 p'.1 p.2 h1, map_zero, zero_mul]
    · rw [hQ.orthogonal h2, map_zero, mul_zero]
  rw [sum_prod_eq fun (i : ι) (k : κ) => M.snorm (M.πA (P i k) * M.πB (Q k)) ^ 2]
  exact M.toStateModel.sum_snorm_sq_orth_le_one hψ _ hsa hidem horth

/-- **From the sandwich to the ordered product.** The difference is the first player's operator
against the second player's commutator; the first player's projection times the second's is a
mutually orthogonal family, so the Cauchy--Schwarz costs only the commutator. -/
theorem abs_sand_sub_ord_le (hψ : ‖M.ψ‖ = 1) {A : R1 × R2 → 𝒜} (hA : IsPVMIn A)
    (hG : IsPVMIn G) (e : K → R2) :
    |(∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * R a)|
      ≤ Real.sqrt (∑ a : R1, ∑ g : K, M.swap.stateSqNorm (R a * G g - G g * R a)) := by
  show _ ≤ Real.sqrt (∑ a : R1, ∑ g : K, M.snorm (M.πB (R a * G g - G g * R a)) ^ 2)
  have hterm : ∀ (a : R1) (g : K),
      M.bornProb (A (a, e g)) (G g * R a * G g) - M.bornProb (A (a, e g)) (G g * R a)
        = M.qform (star (M.πA (A (a, e g)) * M.πB (G g)) * M.πB (R a * G g - G g * R a)) := by
    intro a g
    have hM : star (M.πA (A (a, e g)) * M.πB (G g)) * M.πB (R a * G g - G g * R a)
        = M.πA (A (a, e g)) * M.πB (G g * R a * G g) - M.πA (A (a, e g)) * M.πB (G g * R a) := by
      rw [M.star_πA_mul_πB, hA.star_eq, hG.star_eq, mul_assoc, ← map_mul M.πB,
        show G g * (R a * G g - G g * R a) = G g * R a * G g - G g * R a from by
          rw [mul_sub, ← mul_assoc (G g) (G g), hG.idem, mul_assoc],
        map_sub, mul_sub]
    rw [hM, M.qform_sub]
    rfl
  have hsum : (∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * R a)
      = ∑ a : R1, ∑ g : K, M.qform (star (M.πA (A (a, e g)) * M.πB (G g))
          * M.πB (R a * G g - G g * R a)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hterm a g
  rw [hsum]
  have hmass : ∑ a : R1, ∑ g : K, M.snorm (M.πA (A (a, e g)) * M.πB (G g)) ^ 2 ≤ 1 :=
    M.sum_snorm_sq_prod_le_one hψ (fun a g => A (a, e g)) G
      (fun a g => hA.star_eq _) (fun a g => hA.idem _)
      (fun a a' g hne => hA.orthogonal fun h => hne (Prod.ext_iff.mp h).1) hG
  refine le_trans (abs_sum_sum_le_sqrt _
    (fun a g => M.snorm (M.πA (A (a, e g)) * M.πB (G g)))
    (fun a g => M.snorm (M.πB (R a * G g - G g * R a)))
    fun a g => M.abs_qform_star_mul_le _ _) ?_
  calc Real.sqrt (∑ a : R1, ∑ g : K, M.snorm (M.πA (A (a, e g)) * M.πB (G g)) ^ 2)
        * Real.sqrt (∑ a : R1, ∑ g : K, M.snorm (M.πB (R a * G g - G g * R a)) ^ 2)
      ≤ Real.sqrt 1
          * Real.sqrt (∑ a : R1, ∑ g : K, M.snorm (M.πB (R a * G g - G g * R a)) ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_one, one_mul]

/-- **Step (i) of the pasting lemma.** The second player's two projections in the order
`G_g R_a`, paired with the first player's joint outcome, already agree with the state at
`1 - delta/2 - sqrt(delta/2)`: the outer factor sums away against the first player's marginal, and
what is left is the `R`-consistency, whose square root is the only one in the whole argument that
is not a commutator. -/
theorem sum_bornProb_ord_ge (hψ : ‖M.ψ‖ = 1) {A : R1 × R2 → 𝒜} (hA : IsPVMIn A)
    (hR : IsPVMIn R) (hG : IsPVMIn G) (e : K → R2) :
    1 - (∑ b : R2, M.xSqNorm (∑ a : R1, A (a, b)) (fibSumIn G e b)) / 2
        - Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a)) / 2)
      ≤ ∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * R a) := by
  -- the split `G_g R_a = G_g - G_g (1 - R_a)`
  have hsplit : ∀ (a : R1) (g : K), M.bornProb (A (a, e g)) (G g * R a)
      = M.bornProb (A (a, e g)) (G g) - M.bornProb (A (a, e g)) (G g * (1 - R a)) := by
    intro a g
    rw [← M.bornProb_sub_right, show G g - G g * (1 - R a) = G g * R a from by
      rw [mul_sub, mul_one]; abel]
  -- the first term is the `G`-consistency of the first player's second marginal
  have hterm1 : ∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g)
      = 1 - (∑ b : R2, M.xSqNorm (∑ a : R1, A (a, b)) (fibSumIn G e b)) / 2 := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        (M.bornProb_sum_left univ (fun a => A (a, e g)) (G g)).symm,
      sum_fiber e fun b g => M.bornProb (∑ a : R1, A (a, b)) (G g),
      Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
        (∑ g ∈ univ.filter fun g => e g = b, M.bornProb (∑ a : R1, A (a, b)) (G g))
          = M.bornProb (∑ a : R1, A (a, b)) (fibSumIn G e b) from
        (M.bornProb_sum_right (∑ a : R1, A (a, b)) (univ.filter fun g => e g = b) G).symm]
    have h := M.one_sub_sum_bornProb_eq hψ hA.marg_right (isPVMIn_fibSumIn hG e)
    linarith
  -- the second term is bounded by the square root of the `R`-consistency
  have hbar : ∀ a : R1, IsStarProjection (1 - R a) := fun a => (hR.isStarProjection a).one_sub
  -- regrouping the second term along the fibres of `e`
  have hterm2eq : ∀ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * (1 - R a))
      = ∑ b : R2, M.bornProb (A (a, b)) (fibSumIn G e b * (1 - R a)) := by
    intro a
    rw [sum_fiber e fun b g => M.bornProb (A (a, b)) (G g * (1 - R a))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [fibSumIn, Finset.sum_mul, M.bornProb_sum_right]
  have hCS : ∀ (a : R1) (b : R2),
      |M.bornProb (A (a, b)) (fibSumIn G e b * (1 - R a))|
        ≤ M.snorm (M.πA (A (a, b)) * M.πB (fibSumIn G e b))
          * M.snorm (M.πA (A (a, b)) * M.πB (1 - R a)) := by
    intro a b
    have hM : star (M.πA (A (a, b)) * M.πB (fibSumIn G e b)) * (M.πA (A (a, b)) * M.πB (1 - R a))
        = M.πA (A (a, b)) * M.πB (fibSumIn G e b * (1 - R a)) := by
      rw [M.star_πA_mul_πB, hA.star_eq, (isPVMIn_fibSumIn hG e).star_eq, M.πA_mul_πB_mul,
        hA.idem]
    have h := M.abs_qform_star_mul_le (M.πA (A (a, b)) * M.πB (fibSumIn G e b))
      (M.πA (A (a, b)) * M.πB (1 - R a))
    rw [hM] at h
    exact h
  have hmass1 : ∑ a : R1, ∑ b : R2, M.snorm (M.πA (A (a, b)) * M.πB (fibSumIn G e b)) ^ 2 ≤ 1 :=
    M.sum_snorm_sq_prod_le_one hψ (fun a b => A (a, b)) (fibSumIn G e)
      (fun a b => hA.star_eq _) (fun a b => hA.idem _)
      (fun a a' b hne => hA.orthogonal fun h => hne (Prod.ext_iff.mp h).1)
      (isPVMIn_fibSumIn hG e)
  have hmass2 : ∑ a : R1, ∑ b : R2, M.snorm (M.πA (A (a, b)) * M.πB (1 - R a)) ^ 2
      = (∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a)) / 2 := by
    have hone : ∑ a : R1, M.bornProb (∑ b : R2, A (a, b)) 1 = 1 := by
      rw [← M.bornProb_sum_left, hA.sum_marg_left]
      show M.qform (M.πA 1 * M.πB 1) = 1
      rw [map_one, map_one, mul_one, M.qform_one hψ]
    have hsq : ∀ (a : R1) (b : R2), M.snorm (M.πA (A (a, b)) * M.πB (1 - R a)) ^ 2
        = M.bornProb (A (a, b)) (1 - R a) := fun a b =>
      M.snorm_sq_prod_proj (hA.isStarProjection _) (hbar a)
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun b (_ : b ∈ univ) => hsq a b]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      (M.bornProb_sum_left univ (fun b => A (a, b)) (1 - R a)).symm]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      M.bornProb_sub_right (∑ b : R2, A (a, b)) 1 (R a), Finset.sum_sub_distrib, hone]
    have h := M.one_sub_sum_bornProb_eq hψ hA.marg_left hR
    linarith
  -- assembling
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun g (_ : g ∈ univ) => hsplit a g]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_sub_distrib _ _,
    Finset.sum_sub_distrib, hterm1]
  have hbound : ∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * (1 - R a))
      ≤ Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a)) / 2) := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hterm2eq a]
    refine le_trans (le_abs_self _) (le_trans (abs_sum_sum_le_sqrt _
      (fun a b => M.snorm (M.πA (A (a, b)) * M.πB (fibSumIn G e b)))
      (fun a b => M.snorm (M.πA (A (a, b)) * M.πB (1 - R a))) fun a b => hCS a b) ?_)
    rw [hmass2]
    calc Real.sqrt (∑ a : R1, ∑ b : R2, M.snorm (M.πA (A (a, b)) * M.πB (fibSumIn G e b)) ^ 2)
          * Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a)) / 2)
        ≤ Real.sqrt 1 * Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a)) / 2) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmass1) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, one_mul]
  linarith

/-- **From the Born rule to the state-dependent distance**: the first player's family is
projective and the pasted family a POVM positive on the Hilbert space, so the summed deviation is
at most twice the disagreement. -/
theorem sum_xSqNorm_pasteJ_le (hψ : ‖M.ψ‖ = 1) {A : R1 × R2 → 𝒜} (hA : IsPVMIn A)
    (hR : IsPVMIn R) (hG : IsPVMIn G) (e : K → R2) :
    ∑ p : R1 × R2, M.xSqNorm (A p) (pasteJ R G e p)
      ≤ 2 * (1 - ∑ p : R1 × R2, M.bornProb (A p) (pasteJ R G e p)) := by
  have hAmass := M.sum_stateSqNorm_of_isPVMIn hψ hA
  have hpos : ∀ p : R1 × R2, 0 ≤ M.π (M.πB (pasteJ R G e p)) := fun p => by
    rw [pasteJ, map_sum, map_sum]
    refine Finset.sum_nonneg fun g _ => ?_
    rw [hR.conj_eq_gram hG p.1 g, map_mul M.πB, map_star M.πB]
    exact M.toStateModel.π_star_mul_self_nonneg _
  have hsum : ∑ p : R1 × R2, M.π (M.πB (pasteJ R G e p)) ≤ 1 := by
    rw [← map_sum, ← map_sum, hR.sum_pasteJ hG e, map_one, map_one]
  have hJmass : ∑ p : R1 × R2, M.swap.stateSqNorm (pasteJ R G e p) ≤ 1 :=
    M.toStateModel.sum_snorm_sq_povm_le_one hψ hpos hsum
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => M.xSqNorm_eq (hA.star_eq p) (pasteJ R G e p),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hAmass, ← Finset.mul_sum]
  linarith

/-- **The coarse-grained commutator is small**: this is the commutation analysis, with both
families on the second player's side and the first player's joint measurement supplying the
operator both products reach. -/
theorem sum_snorm_sq_comm_coarse_le {A : R1 × R2 → 𝒜} {Gf : R2 → ℬ} (hA : IsPVMIn A)
    (hR : IsPVMIn R) (hGf : IsPVMIn Gf) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a) ≤ δ₁)
    (h2 : ∑ b : R2, M.xSqNorm (∑ a : R1, A (a, b)) (Gf b) ≤ δ₂) :
    ∑ a : R1, ∑ b : R2, M.swap.stateSqNorm (R a * Gf b - Gf b * R a) ≤ 16 * (δ₁ + δ₂) := by
  have hδ₂0 : 0 ≤ δ₂ := le_trans (Finset.sum_nonneg fun b _ => M.xSqNorm_nonneg _ _) h2
  have hδ₁0 : 0 ≤ δ₁ := le_trans (Finset.sum_nonneg fun a _ => M.xSqNorm_nonneg _ _) h1
  have hdev : ∀ (x : 𝒜) (y : ℬ), M.snorm (M.πB y - M.πA x) ^ 2 = M.xSqNorm x y := fun x y => by
    rw [M.snorm_sub_comm]
    rfl
  have key := M.commutation_analysis_abstract (δ := δ₁ + δ₂)
    (fun a => M.πB (R a)) (fun b => M.πB (Gf b))
    (fun a => M.πA (∑ b : R2, A (a, b))) (fun b => M.πA (∑ a : R1, A (a, b)))
    (fun p => M.πA (A p))
    (M.isColContraction_of_isPVMIn (hR.map M.πB))
    (M.isColContraction_of_isPVMIn (hGf.map M.πB))
    (M.isColContraction_of_isPVMIn (hA.marg_left.map M.πA))
    (M.isColContraction_of_isPVMIn (hA.marg_right.map M.πA))
    (fun a b => (M.commute _ _).eq.symm) (fun b a => (M.commute _ _).eq.symm)
    (fun a b => by rw [← map_mul, hA.marg_mul_marg a b])
    (fun a b => by rw [← map_mul, hA.marg_mul_marg' a b])
    (by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hdev (∑ b : R2, A (a, b)) (R a)]
      linarith)
    (by
      rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hdev (∑ a : R1, A (a, b)) (Gf b)]
      linarith)
  rw [sum_prod_eq fun (a : R1) (b : R2) => M.swap.stateSqNorm (R a * Gf b - Gf b * R a)]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) key
  show M.snorm (M.πB (R p.1 * Gf p.2 - Gf p.2 * R p.1)) ^ 2 = _
  rw [map_sub, map_mul, map_mul]

/-- **The collision term**: the pairs of `G`-outcomes that the outcome map cannot tell apart. It
is exactly what the coarse-grained cloud has beyond the fine-grained one, and the only place where
the separating property of the outcome map is needed. -/
def collisionTerm (R : R1 → ℬ) (G : K → ℬ) (Ga : K → 𝒜) (e : K → R2) : ℝ :=
  ∑ a : R1, ∑ g : K, ∑ g' ∈ univ.filter fun g' => g' ≠ g ∧ e g' = e g,
    M.bornProb (Ga g') (R a * G g * R a)

theorem collisionTerm_nonneg {Ga : K → 𝒜} (hR : IsPVMIn R) (hG : IsPVMIn G)
    (hGa : IsPVMIn Ga) (e : K → R2) : 0 ≤ M.collisionTerm R G Ga e :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun g' _ => by
    rw [hG.conj_eq_gram hR g a]
    exact M.bornProb_gram_nonneg (hGa.isStarProjection g') _

/-- **The strife minus the cloud is exactly the collision term.** Both are sums of the same Born
probabilities; coarse-graining pairs each `G`-outcome with every other one the map identifies
with it. -/
theorem strife_sub_cloud_eq {Ga : K → 𝒜} (e : K → R2) :
    (∑ a : R1, ∑ b : R2, M.bornProb (fibSumIn Ga e b) (R a * fibSumIn G e b * R a))
        - ∑ a : R1, ∑ g : K, M.bornProb (Ga g) (R a * G g * R a)
      = M.collisionTerm R G Ga e := by
  have key : ∀ a : R1, ∑ b : R2, M.bornProb (fibSumIn Ga e b) (R a * fibSumIn G e b * R a)
      = ∑ g : K, ∑ g' ∈ univ.filter fun g' => e g' = e g,
          M.bornProb (Ga g') (R a * G g * R a) := by
    intro a
    rw [sum_fiber e fun b g => ∑ g' ∈ univ.filter fun g' => e g' = b,
      M.bornProb (Ga g') (R a * G g * R a)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show R a * fibSumIn G e b * R a
        = ∑ g ∈ univ.filter fun g => e g = b, R a * G g * R a from by
      rw [fibSumIn, Finset.mul_sum, Finset.sum_mul], fibSumIn, M.bornProb_sum_sum]
    exact Finset.sum_comm
  have hsplit : ∀ (a : R1) (g : K),
      (∑ g' ∈ univ.filter fun g' => e g' = e g, M.bornProb (Ga g') (R a * G g * R a))
        = M.bornProb (Ga g) (R a * G g * R a)
          + ∑ g' ∈ univ.filter fun g' => g' ≠ g ∧ e g' = e g,
              M.bornProb (Ga g') (R a * G g * R a) := by
    intro a g
    rw [show (univ.filter fun g' => g' ≠ g ∧ e g' = e g)
        = (univ.filter fun g' => e g' = e g).erase g from by
      ext g'
      simp [Finset.mem_erase, and_comm]]
    exact (Finset.add_sum_erase (univ.filter fun g' => e g' = e g)
      (fun g' => M.bornProb (Ga g') (R a * G g * R a))
      (Finset.mem_filter.mpr ⟨mem_univ g, rfl⟩)).symm
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => key a,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun g (_ : g ∈ univ) => hsplit a g,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_add_distrib,
    Finset.sum_add_distrib, collisionTerm]
  ring

/-- **The fine-grained commutator against the coarse-grained one.** The coarse-grained one is
small by the commutation analysis; the two differ by the cloud, the strife and the collision term,
and the cloud--strife comparison is the only place the first player's copy of `G` is used. -/
theorem sum_snorm_sq_comm_fine_le (hψ : ‖M.ψ‖ = 1) {A : R1 × R2 → 𝒜} {Ga : K → 𝒜}
    (hA : IsPVMIn A) (hR : IsPVMIn R) (hG : IsPVMIn G) (hGa : IsPVMIn Ga) (e : K → R2)
    {δ₁ δ₂ : ℝ} (h1 : ∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a) ≤ δ₁)
    (h2 : ∑ b : R2, M.xSqNorm (∑ a : R1, A (a, b)) (fibSumIn G e b) ≤ δ₂) :
    (∑ a : R1, ∑ g : K, M.swap.stateSqNorm (R a * G g - G g * R a))
      ≤ 16 * (δ₁ + δ₂) + 4 * Real.sqrt (∑ g : K, M.xSqNorm (Ga g) (G g))
        + 2 * M.collisionTerm R G Ga e := by
  have hfine := M.sum_snorm_sq_comm_eq hψ hR hG
  have hcoarse := M.sum_snorm_sq_comm_eq hψ hR (isPVMIn_fibSumIn hG e)
  have hcc := M.sum_snorm_sq_comm_coarse_le hA hR (isPVMIn_fibSumIn hG e) h1 h2
  have hc1 := abs_le.mp (M.abs_sigma_sub_cloud_le hψ (Ga := Ga) hR hG)
  have hc2 := abs_le.mp (M.abs_sigma_sub_cloud_le hψ (K := R2) (G := fibSumIn G e)
    (Ga := fibSumIn Ga e) hR (isPVMIn_fibSumIn hG e))
  have hcol := M.strife_sub_cloud_eq (R := R) (G := G) (Ga := Ga) e
  have hmono : Real.sqrt (∑ b : R2, M.xSqNorm (fibSumIn Ga e b) (fibSumIn G e b))
      ≤ Real.sqrt (∑ g : K, M.xSqNorm (Ga g) (G g)) :=
    Real.sqrt_le_sqrt (M.sum_xSqNorm_fibSum_le hψ hGa hG e)
  linarith [hc1.1, hc1.2, hc2.1, hc2.2]

/-- **The pasted POVM agrees with the first player's joint measurement, at one question.** Step
(i) reaches the ordered product and step (ii) the sandwich. -/
theorem one_sub_sum_bornProb_pasteJ_le' (hψ : ‖M.ψ‖ = 1) {A : R1 × R2 → 𝒜} (hA : IsPVMIn A)
    (hR : IsPVMIn R) (hG : IsPVMIn G) (e : K → R2) :
    1 - (∑ p : R1 × R2, M.bornProb (A p) (pasteJ R G e p))
      ≤ (∑ b : R2, M.xSqNorm (∑ a : R1, A (a, b)) (fibSumIn G e b)) / 2
        + Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A (a, b)) (R a)) / 2)
        + Real.sqrt (∑ a : R1, ∑ g : K, M.swap.stateSqNorm (R a * G g - G g * R a)) := by
  have hD : ∑ p : R1 × R2, M.bornProb (A p) (pasteJ R G e p)
      = ∑ a : R1, ∑ g : K, M.bornProb (A (a, e g)) (G g * R a * G g) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_fiber e fun b g => M.bornProb (A (a, b)) (G g * R a * G g)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show pasteJ R G e (a, b)
        = ∑ g ∈ univ.filter fun g => e g = b, G g * R a * G g from rfl, M.bornProb_sum_right]
  have hstepi := M.sum_bornProb_ord_ge hψ hA hR hG e
  have hstepii := abs_le.mp (M.abs_sand_sub_ord_le hψ hA hG (R := R) e)
  rw [hD]
  linarith [hstepii.1, hstepii.2]

end Sand2

/-! ### The marginal of a joint measurement against the other player's product -/

section Marginal

variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]

/-- **The marginal step.** The first player's joint projective measurement, consistent with the
second player's ordered product `Z_b X_a`, has its `R2`-marginal consistent with `X_a` alone. -/
theorem sum_xSqNorm_marg_le {Q : R1 × R2 → 𝒜} {Z : R2 → ℬ} (X : R1 → ℬ) (hQ : IsPVMIn Q)
    (hZ : IsPVMIn Z) :
    ∑ a : R1, M.xSqNorm (∑ b : R2, Q (a, b)) (X a)
      ≤ 2 * (∑ p : R1 × R2, M.snorm (M.πA (Q p) * M.πB (Z p.2) - M.πA (Q p)) ^ 2)
        + 2 * ∑ p : R1 × R2, M.xSqNorm (Q p) (Z p.2 * X p.1) := by
  -- the intermediate operator: the marginal with the second player's projection attached
  have hcool : ∑ a : R1, M.snorm (M.πA (∑ b : R2, Q (a, b))
        - ∑ b : R2, M.πA (Q (a, b)) * M.πB (Z b)) ^ 2
      ≤ ∑ p : R1 × R2, M.snorm (M.πA (Q p) * M.πB (Z p.2) - M.πA (Q p)) ^ 2 := by
    have h := M.sum_snorm_sq_cool_prod (hQ.map M.πA) (fun p => M.πA (Q p) * M.πB (Z p.2))
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (le_trans h
      (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)))
    · refine congrArg (fun T => M.snorm T ^ 2) ?_
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_assoc, ← map_mul, hQ.idem]
    · rw [M.snorm_sub_comm]
  -- the orthogonal insertion
  have horth : ∑ a : R1, M.snorm ((∑ b : R2, M.πA (Q (a, b)) * M.πB (Z b)) - M.πB (X a)) ^ 2
      ≤ ∑ p : R1 × R2, M.xSqNorm (Q p) (Z p.2 * X p.1) := by
    have hsplit : ∀ a : R1, (∑ b : R2, M.πA (Q (a, b)) * M.πB (Z b)) - M.πB (X a)
        = ∑ b : R2, M.πB (Z b) * (M.πA (Q (a, b)) - M.πB (Z b * X a)) := by
      intro a
      rw [show M.πB (X a) = ∑ b : R2, M.πB (Z b * X a) from by
        rw [← map_sum, ← Finset.sum_mul, hZ.sum_eq_one, one_mul], ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_sub, ← (M.commute _ _).eq, ← map_mul M.πB, ← mul_assoc, hZ.idem]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      congrArg (fun T => M.snorm T ^ 2) (hsplit a)]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      M.snorm_sq_sum_proj_mul (fun b => (hZ.map M.πB).star_eq b)
        (fun b b' hbb' => (hZ.map M.πB).orthogonal hbb') _ univ]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have h := M.snorm_mul_le (M.bnd_πB_of_isStarProjection (hZ.isStarProjection b))
      (M.πA (Q (a, b)) - M.πB (Z b * X a))
    rw [one_mul] at h
    exact pow_le_pow_left₀ (M.snorm_nonneg _) h 2
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => show M.xSqNorm (∑ b : R2, Q (a, b)) (X a)
      = M.snorm (M.πA (∑ b : R2, Q (a, b)) - M.πB (X a)) ^ 2 from rfl]
  refine le_trans (M.sum_snorm_sq_triangle univ (fun a => M.πA (∑ b : R2, Q (a, b)))
    (fun a => ∑ b : R2, M.πA (Q (a, b)) * M.πB (Z b)) (fun a => M.πB (X a))) ?_
  linarith

/-- **The second player's own deviation, through the first player's operator.** The three-term
triangle inequality in the one shape the consumer needs: a same-side deviation bounded by two
cross-party ones. -/
theorem swap_stateSqNorm_sub_le (a : 𝒜) (b₁ b₂ : ℬ) :
    M.swap.stateSqNorm (b₁ - b₂) ≤ 2 * M.xSqNorm a b₁ + 2 * M.xSqNorm a b₂ := by
  have htri : M.swap.stateNorm (b₁ - b₂) ≤ M.xNorm a b₁ + M.xNorm a b₂ := by
    show M.snorm (M.πB (b₁ - b₂)) ≤ M.snorm (M.πA a - M.πB b₁) + M.snorm (M.πA a - M.πB b₂)
    rw [map_sub, show M.πB b₁ - M.πB b₂ = (M.πA a - M.πB b₂) - (M.πA a - M.πB b₁) from by
      abel]
    exact le_trans (M.snorm_sub_le _ _) (le_of_eq (add_comm _ _))
  have h0 := M.swap.stateNorm_nonneg (b₁ - b₂)
  rw [M.xSqNorm_eq_sq, M.xSqNorm_eq_sq]
  show M.swap.stateNorm (b₁ - b₂) ^ 2 ≤ _
  nlinarith [M.xNorm_nonneg a b₁, M.xNorm_nonneg a b₂, sq_nonneg (M.xNorm a b₁ - M.xNorm a b₂)]

/-- **Attaching the other player's projection to a consistent joint measurement costs
nothing.** -/
theorem sum_snorm_sq_mul_proj_le (Q : R1 × R2 → 𝒜) {Z : R2 → ℬ} (X : R1 → ℬ)
    (hZ : IsPVMIn Z) :
    ∑ p : R1 × R2, M.snorm (M.πA (Q p) * M.πB (Z p.2) - M.πA (Q p)) ^ 2
      ≤ 4 * ∑ p : R1 × R2, M.xSqNorm (Q p) (Z p.2 * X p.1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 : M.snorm (M.πA (Q p) * M.πB (Z p.2) - M.πB (Z p.2 * X p.1)) ^ 2
      ≤ M.xSqNorm (Q p) (Z p.2 * X p.1) := by
    have h := M.snorm_mul_le (M.bnd_πB_of_isStarProjection (hZ.isStarProjection p.2))
      (M.πA (Q p) - M.πB (Z p.2 * X p.1))
    rw [one_mul, mul_sub, ← (M.commute _ _).eq, ← map_mul M.πB, ← mul_assoc, hZ.idem] at h
    exact pow_le_pow_left₀ (M.snorm_nonneg _) h 2
  have h2 : M.snorm (M.πB (Z p.2 * X p.1) - M.πA (Q p)) ^ 2
      = M.xSqNorm (Q p) (Z p.2 * X p.1) := by
    rw [M.snorm_sub_comm]
    rfl
  have htri : M.snorm (M.πA (Q p) * M.πB (Z p.2) - M.πA (Q p))
      ≤ M.snorm (M.πA (Q p) * M.πB (Z p.2) - M.πB (Z p.2 * X p.1))
        + M.snorm (M.πB (Z p.2 * X p.1) - M.πA (Q p)) := by
    refine le_trans (le_of_eq (congrArg M.snorm ?_)) (M.snorm_add_le _ _)
    abel
  nlinarith [M.snorm_nonneg (M.πA (Q p) * M.πB (Z p.2) - M.πA (Q p)),
    M.snorm_nonneg (M.πA (Q p) * M.πB (Z p.2) - M.πB (Z p.2 * X p.1)),
    M.snorm_nonneg (M.πB (Z p.2 * X p.1) - M.πA (Q p)),
    sq_nonneg (M.snorm (M.πA (Q p) * M.πB (Z p.2) - M.πB (Z p.2 * X p.1))
      - M.snorm (M.πB (Z p.2 * X p.1) - M.πA (Q p)))]

/-- **The marginal step, packaged**, at ten times the input. -/
theorem sum_xSqNorm_marg_le' {Q : R1 × R2 → 𝒜} {Z : R2 → ℬ} (X : R1 → ℬ) (hQ : IsPVMIn Q)
    (hZ : IsPVMIn Z) :
    ∑ a : R1, M.xSqNorm (∑ b : R2, Q (a, b)) (X a)
      ≤ 10 * ∑ p : R1 × R2, M.xSqNorm (Q p) (Z p.2 * X p.1) := by
  have h1 := M.sum_xSqNorm_marg_le X hQ hZ
  have h2 := M.sum_snorm_sq_mul_proj_le Q X hZ
  linarith

end Marginal

/-! ### The pasting lemma -/

section Average

variable {ι R1 R2 K : Type*} [Fintype ι] [Fintype R1] [DecidableEq R1] [Fintype R2]
  [DecidableEq R2] [Fintype K] [DecidableEq K]

/-- **The pasting lemma, `k = 2`** (NW19's Fact 4.35, the paper's `lem:pasting-updated`), in a
bipartite model: the first player's joint measurement agrees with the pasted sandwich up to
`delta/2 + sqrt(delta/2) + sqrt(32 delta + 4 sqrt(eta) + 2 eps)`. -/
theorem one_sub_sum_bornProb_pasteJ_le (hψ : ‖M.ψ‖ = 1) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {A : ι → R1 × R2 → 𝒜} {R : ι → R1 → ℬ} {G : ι → K → ℬ}
    {Ga : ι → K → 𝒜} (e : ι → K → R2) (hA : ∀ i, IsPVMIn (A i)) (hR : ∀ i, IsPVMIn (R i))
    (hG : ∀ i, IsPVMIn (G i)) (hGa : ∀ i, IsPVMIn (Ga i)) {δ η ε : ℝ}
    (hP1 : ∑ i, w i * ∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a) ≤ δ)
    (hP2 : ∑ i, w i * ∑ b : R2,
      M.xSqNorm (∑ a : R1, A i (a, b)) (fibSumIn (G i) (e i) b) ≤ δ)
    (hP4 : ∑ i, w i * ∑ g : K, M.xSqNorm (Ga i g) (G i g) ≤ η)
    (hcoll : ∑ i, w i * M.collisionTerm (R i) (G i) (Ga i) (e i) ≤ ε) :
    1 - ∑ i, w i * ∑ p : R1 × R2, M.bornProb (A i p) (pasteJ (R i) (G i) (e i) p)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) := by
  have hX1nn : ∀ i, 0 ≤ ∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a) := fun i =>
    Finset.sum_nonneg fun a _ => M.xSqNorm_nonneg _ _
  have hEnn : ∀ i, 0 ≤ ∑ g : K, M.xSqNorm (Ga i g) (G i g) := fun i =>
    Finset.sum_nonneg fun g _ => M.xSqNorm_nonneg _ _
  have hCnn : ∀ i, 0 ≤ ∑ a : R1, ∑ g : K,
      M.swap.stateSqNorm (R i a * G i g - G i g * R i a) := fun i =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => M.swap.stateSqNorm_nonneg _
  -- the average of the fine-grained commutators
  have hCfavg : ∑ i, w i * (∑ a : R1, ∑ g : K,
        M.swap.stateSqNorm (R i a * G i g - G i g * R i a))
      ≤ 32 * δ + 4 * Real.sqrt η + 2 * ε := by
    have hper : ∀ i, (∑ a : R1, ∑ g : K, M.swap.stateSqNorm (R i a * G i g - G i g * R i a))
        ≤ 16 * ((∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a))
            + ∑ b : R2, M.xSqNorm (∑ a : R1, A i (a, b)) (fibSumIn (G i) (e i) b))
          + 4 * Real.sqrt (∑ g : K, M.xSqNorm (Ga i g) (G i g))
          + 2 * M.collisionTerm (R i) (G i) (Ga i) (e i) := fun i =>
      M.sum_snorm_sq_comm_fine_le hψ (hA i) (hR i) (hG i) (hGa i) (e i) le_rfl le_rfl
    have hjensen : ∑ i, w i * Real.sqrt (∑ g : K, M.xSqNorm (Ga i g) (G i g))
        ≤ Real.sqrt η :=
      le_trans (sum_weighted_sqrt_le w (fun i => ∑ g : K, M.xSqNorm (Ga i g) (G i g)) hw0 hw1
        hEnn) (Real.sqrt_le_sqrt hP4)
    calc ∑ i, w i * (∑ a : R1, ∑ g : K, M.swap.stateSqNorm (R i a * G i g - G i g * R i a))
        ≤ ∑ i, w i * (16 * ((∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a))
              + ∑ b : R2, M.xSqNorm (∑ a : R1, A i (a, b)) (fibSumIn (G i) (e i) b))
            + 4 * Real.sqrt (∑ g : K, M.xSqNorm (Ga i g) (G i g))
            + 2 * M.collisionTerm (R i) (G i) (Ga i) (e i)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hper i) (hw0 i)
      _ = 16 * (∑ i, w i * ∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a))
            + 16 * (∑ i, w i * ∑ b : R2,
              M.xSqNorm (∑ a : R1, A i (a, b)) (fibSumIn (G i) (e i) b))
            + 4 * (∑ i, w i * Real.sqrt (∑ g : K, M.xSqNorm (Ga i g) (G i g)))
            + 2 * ∑ i, w i * M.collisionTerm (R i) (G i) (Ga i) (e i) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 32 * δ + 4 * Real.sqrt η + 2 * ε := by linarith
  -- the deficit splits off the weight
  have hsplit : ∑ i, w i * (1 - (∑ p : R1 × R2,
        M.bornProb (A i p) (pasteJ (R i) (G i) (e i) p)))
      = 1 - ∑ i, w i * ∑ p : R1 × R2, M.bornProb (A i p) (pasteJ (R i) (G i) (e i) p) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_sub (w i) 1 _, Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_one (w i), hw1]
  rw [← hsplit]
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (M.one_sub_sum_bornProb_pasteJ_le' hψ (hA i) (hR i) (hG i) (e i)) (hw0 i)) ?_
  have hdist : ∑ i, w i * ((∑ b : R2,
          M.xSqNorm (∑ a : R1, A i (a, b)) (fibSumIn (G i) (e i) b)) / 2
        + Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a)) / 2)
        + Real.sqrt (∑ a : R1, ∑ g : K, M.swap.stateSqNorm (R i a * G i g - G i g * R i a)))
      = (∑ i, w i * ∑ b : R2,
            M.xSqNorm (∑ a : R1, A i (a, b)) (fibSumIn (G i) (e i) b)) / 2
        + (∑ i, w i * Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a)) / 2))
        + ∑ i, w i * Real.sqrt (∑ a : R1, ∑ g : K,
            M.swap.stateSqNorm (R i a * G i g - G i g * R i a)) := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdist]
  have h2 : ∑ i, w i * Real.sqrt ((∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a)) / 2)
      ≤ Real.sqrt (δ / 2) := by
    refine le_trans (sum_weighted_sqrt_le w
      (fun i => (∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a)) / 2) hw0 hw1
      fun i => by linarith [hX1nn i]) (Real.sqrt_le_sqrt ?_)
    rw [sum_weighted_div w (fun i => ∑ a : R1, M.xSqNorm (∑ b : R2, A i (a, b)) (R i a)) 2]
    linarith
  have h3 : ∑ i, w i * Real.sqrt (∑ a : R1, ∑ g : K,
        M.swap.stateSqNorm (R i a * G i g - G i g * R i a))
      ≤ Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) :=
    le_trans (sum_weighted_sqrt_le w _ hw0 hw1 hCnn) (Real.sqrt_le_sqrt hCfavg)
  linarith

end Average

/-! ### The collision term under a product question distribution -/

section Collision

variable {Z Y R1 R2 K : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]

/-- **The collision term is at most the average collision probability**, in a bipartite model:
the Born probabilities do not depend on the probe, so the probe average acts on the indicator
alone, and what is left is a POVM's total mass, which is one. -/
theorem sum_collisionTerm_le (hψ : ‖M.ψ‖ = 1) {ν : Z → ℝ} (hν0 : ∀ z, 0 ≤ ν z)
    {R : Z → R1 → ℬ} {G : Z → K → ℬ} {Ga : Z → K → 𝒜}
    (hR : ∀ z, IsPVMIn (R z)) (hG : ∀ z, IsPVMIn (G z)) (hGa : ∀ z, IsPVMIn (Ga z))
    (e : Z → Y → K → R2) {εz : Z → ℝ} (hε : ∀ z, 0 ≤ εz z)
    (hsep : ∀ (z : Z) (g g' : K), g' ≠ g →
      ((univ.filter fun y : Y => e z y g' = e z y g).card : ℝ) ≤ εz z * (Fintype.card Y : ℝ)) :
    ∑ i : Z × Y, (ν i.1 * (Fintype.card Y : ℝ)⁻¹)
        * M.collisionTerm (R i.1) (G i.1) (Ga i.1) (e i.1 i.2) ≤ ∑ z : Z, ν z * εz z := by
  have hcardpos : (0 : ℝ) < (Fintype.card Y : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hFnn : ∀ (z : Z) (a : R1) (g g' : K),
      0 ≤ M.bornProb (Ga z g') (R z a * G z g * R z a) := fun z a g g' => by
    rw [(hG z).conj_eq_gram (hR z) g a]
    exact M.bornProb_gram_nonneg ((hGa z).isStarProjection g') _
  -- the total mass of the cloud's Born probabilities is one
  have hmass : ∀ z : Z, ∑ a : R1, ∑ g : K, ∑ g' : K,
      M.bornProb (Ga z g') (R z a * G z g * R z a) = 1 := by
    intro z
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        show (∑ g' : K, M.bornProb (Ga z g') (R z a * G z g * R z a))
            = M.bornProb 1 (R z a * G z g * R z a) from by
          rw [← (hGa z).sum_eq_one, M.bornProb_sum_left],
      sum_prod_eq fun (a : R1) (g : K) => M.bornProb 1 (R z a * G z g * R z a),
      ← M.bornProb_sum_right, (hG z).sum_conj' (hR z)]
    show M.qform (M.πA 1 * M.πB 1) = 1
    rw [map_one, map_one, mul_one, M.qform_one hψ]
  -- the probe average of the collision term, at one `z`
  have hstep : ∀ z : Z, ∑ y : Y, M.collisionTerm (R z) (G z) (Ga z) (e z y)
      ≤ εz z * (Fintype.card Y : ℝ) := by
    intro z
    have hcol : ∀ y : Y, M.collisionTerm (R z) (G z) (Ga z) (e z y)
        = ∑ a : R1, ∑ g : K, ∑ g' : K,
            (if g' ≠ g ∧ e z y g' = e z y g then
              M.bornProb (Ga z g') (R z a * G z g * R z a) else 0) := by
      intro y
      rw [collisionTerm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g _ =>
        Finset.sum_filter _ _
    have hinner : ∀ (a : R1) (g g' : K),
        (∑ y : Y, (if g' ≠ g ∧ e z y g' = e z y g then
            M.bornProb (Ga z g') (R z a * G z g * R z a) else 0))
          ≤ (εz z * (Fintype.card Y : ℝ)) * M.bornProb (Ga z g') (R z a * G z g * R z a) := by
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
              M.bornProb (Ga z g') (R z a * G z g * R z a) else 0)
        ≤ ∑ a : R1, ∑ g : K, ∑ g' : K,
            (εz z * (Fintype.card Y : ℝ)) * M.bornProb (Ga z g') (R z a * G z g * R z a) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun g _ =>
            Finset.sum_le_sum fun g' _ => hinner a g g'
      _ = (εz z * (Fintype.card Y : ℝ)) * ∑ a : R1, ∑ g : K, ∑ g' : K,
            M.bornProb (Ga z g') (R z a * G z g * R z a) := by
          simp only [Finset.mul_sum]
      _ = εz z * (Fintype.card Y : ℝ) := by rw [hmass z, mul_one]
  -- the weighted sum over the product
  rw [← sum_prod_eq fun (z : Z) (y : Y) => (ν z * (Fintype.card Y : ℝ)⁻¹)
    * M.collisionTerm (R z) (G z) (Ga z) (e z y)]
  refine Finset.sum_le_sum fun z _ => ?_
  have hne : (Fintype.card Y : ℝ) ≠ 0 := ne_of_gt hcardpos
  rw [← Finset.mul_sum]
  calc (ν z * (Fintype.card Y : ℝ)⁻¹) * ∑ y : Y, M.collisionTerm (R z) (G z) (Ga z) (e z y)
      ≤ (ν z * (Fintype.card Y : ℝ)⁻¹) * (εz z * (Fintype.card Y : ℝ)) :=
        mul_le_mul_of_nonneg_left (hstep z)
          (mul_nonneg (hν0 z) (le_of_lt (inv_pos.mpr hcardpos)))
    _ = ν z * εz z := by field_simp

end Collision

end BipartiteModel

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
  rw [qform_eq_mat, qform_eq_mat]
  exact (StateModel.mat v).qform_star M

/-- A positive operator below the identity has `M^2 <= M`, so a family of positive operators
summing to the identity has its squares summing to at most the identity. -/
theorem sum_sq_le_one_of_sum_eq_one {C : Type*} [Fintype C] {P : C → Matrix N N ℂ}
    (hP0 : ∀ c, (0 : Matrix N N ℂ) ≤ P c) (hPsum : ∑ c, P c = 1) :
    ∑ c, (P c) * (P c) ≤ (1 : Matrix N N ℂ) :=
  sum_mul_self_le_one_of_sum_le_one hP0 hPsum.le

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
  simp only [qform_eq_mat]
  refine (StateModel.mat v).qform_sum_ge_of_close hv hM.toIn
    (fun c => (StateModel.mat v).π_nonneg (hP0 c)) ?_ hclose
  have h := OrderHomClass.mono (StateModel.mat v).π hPsum
  rwa [map_sum, map_one] at h

end Mass

/-! ## Two ways for a family of squared state norms to sum to at most one -/

section Mass2

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **Mutually orthogonal projections**: the sum is a projection, hence bounded by the identity. -/
theorem sum_snorm_sq_orth_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {v : N → ℂ}
    (hv : ‖evec v‖ = 1) (P : ι → Matrix N N ℂ) (hsa : ∀ i, (P i)ᴴ = P i)
    (hidem : ∀ i, P i * P i = P i) (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    ∑ i, snorm v (P i) ^ 2 ≤ 1 :=
  (StateModel.mat v).sum_snorm_sq_orth_le_one hv P hsa hidem horth

/-- **A POVM**: each square is below the element, and the elements sum to the identity. -/
theorem sum_snorm_sq_povm_le_one {ι : Type*} [Fintype ι] {v : N → ℂ} (hv : ‖evec v‖ = 1)
    {P : ι → Matrix N N ℂ} (hP0 : ∀ i, (0 : Matrix N N ℂ) ≤ P i) (hPsum : ∑ i, P i = 1) :
    ∑ i, snorm v (P i) ^ 2 ≤ 1 :=
  (StateModel.mat v).sum_snorm_sq_povm_le_one hv (fun i => (StateModel.mat v).π_nonneg (hP0 i))
    (le_of_eq (by rw [← map_sum, hPsum, map_one]))

end Mass2

section Nonneg

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem aOp_zero : (aOp (0 : Matrix dA dA ℂ) : Matrix (dA × dB) (dA × dB) ℂ) = 0 := by
  rw [aOp, Matrix.zero_kronecker]

theorem bOp_zero : (bOp (0 : Matrix dB dB ℂ) : Matrix (dA × dB) (dA × dB) ℂ) = 0 := by
  rw [bOp, Matrix.kronecker_zero]

/-- Bob's squared state norm is the second player's in the tensor-product model. -/
theorem snorm_bOp_sq_eq_tensor (ψ : dA × dB → ℂ) (Y : Matrix dB dB ℂ) :
    snorm ψ (bOp Y : Matrix (dA × dB) _ ℂ) ^ 2 = (BipartiteModel.tensor ψ).swap.stateSqNorm Y :=
  rfl

theorem sum_aOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι]
    {P : ι → Matrix dA dA ℂ} (h : IsPVM P) :
    ∑ i, ((aOp (P i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * aOp (P i) = 1 := by
  classical
  exact (h.toIn.map (BipartiteModel.aOpStarAlgHom (dB := dB))).sum_star_mul_self

theorem bornProb_sub_right (ψ : dA × dB → ℂ) (X : Matrix dA dA ℂ) (M N : Matrix dB dB ℂ) :
    bornProb ψ X (M - N) = bornProb ψ X M - bornProb ψ X N := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_sub_right X M N

/-- A product of two commuting projections is a projection, so its squared state norm is its
quadratic form --- a Born probability. -/
theorem snorm_sq_prod_proj (ψ : dA × dB → ℂ) {P : Matrix dA dA ℂ} {Q : Matrix dB dB ℂ}
    (hPsa : Pᴴ = P) (hPi : P * P = P) (hQsa : Qᴴ = Q) (hQi : Q * Q = Q) :
    snorm ψ ((aOp P : Matrix (dA × dB) _ ℂ) * bOp Q) ^ 2
      = bornProb ψ P Q := by
  rw [← BipartiteModel.snorm_tensor, bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).snorm_sq_prod_proj ⟨hPi, hPsa⟩ ⟨hQi, hQsa⟩

theorem bornProb_sum_left {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, bornProb ψ (A i) B := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_sum_left s A B

theorem bornProb_sum_right {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ A (∑ i ∈ s, B i) = ∑ i ∈ s, bornProb ψ A (B i) := by
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).bornProb_sum_right A s B

end Nonneg

/-! ## Coarse-graining a pair of projective families, on the two parties -/

section Coarse2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Coarse-graining adds the off-diagonal Born probabilities, which are nonnegative. -/
theorem sum_bornProb_le_fibSum (ψ : dA × dB → ℂ) {X : α → Matrix dA dA ℂ}
    {X' : α → Matrix dB dB ℂ} (hX : IsPVM X) (hX' : IsPVM X') (e : α → β) :
    ∑ a, bornProb ψ (X a) (X' a) ≤ ∑ b, bornProb ψ (fibSum X e b) (fibSum X' e b) := by
  simp only [bornProb_eq_tensor, fibSum_eq_fibSumIn]
  exact (BipartiteModel.tensor ψ).sum_bornProb_le_fibSum hX.toIn hX'.toIn e

/-- **Coarse-graining two projective families the same way costs nothing**, in the `fibSum` form
that the pasting lemma needs. -/
theorem sum_xSqNorm_fibSum_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {X : α → Matrix dA dA ℂ}
    {X' : α → Matrix dB dB ℂ} (hX : IsPVM X) (hX' : IsPVM X') (e : α → β) :
    ∑ b, xSqNorm ψ (fibSum X e b) (fibSum X' e b) ≤ ∑ a, xSqNorm ψ (X a) (X' a) := by
  simp only [xSqNorm_eq_tensor, fibSum_eq_fibSumIn]
  exact (BipartiteModel.tensor ψ).sum_xSqNorm_fibSum_le hψ hX.toIn hX'.toIn e

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
  simp only [snorm_bOp_sq_eq_tensor, ← BipartiteModel.qform_tensor]
  exact (BipartiteModel.tensor ψ).sum_snorm_sq_comm_eq hψ hA.toIn hB.toIn

end Fine

/-! ## The sandwich family of the pasting lemma -/

section Sand2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]

variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}

/-- Each term of the pasting sandwich is a Gram operator, hence positive. -/
theorem sandOp_posSemidef (hR : IsPVM R) (hG : IsPVM G) (a : R1) (g : K) :
    (R a * G g * R a).PosSemidef := by
  rw [hG.toIn.conj_eq_gram hR.toIn g a]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The pasting sandwich is a POVM: the inner family sums away against `R`'s projectivity. -/
theorem sum_sandOp (hR : IsPVM R) (hG : IsPVM G) :
    ∑ p : R1 × K, R p.1 * G p.2 * R p.1 = 1 :=
  hG.toIn.sum_conj' hR.toIn

/-- The squared state norms of the pasting sandwich sum to at most one. -/
theorem sum_snorm_sq_sandOp_le_one {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) (hR : IsPVM R)
    (hG : IsPVM G) :
    ∑ a : R1, ∑ g : K,
        snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2 ≤ 1 := by
  simp only [snorm_bOp_sq_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_snorm_sq_sandOp_le_one hψ hR.toIn hG.toIn

/-- **The cloud step.** Replacing Bob's outer factor by Alice's copy of it costs the square root of
their cross-party deviation --- and nothing depending on the size of `K`, because one factor `R a`
stays in front of the deviation, so the sum over `a` is absorbed rather than repeated. -/
theorem abs_sigma_sub_cloud_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {Ga : K → Matrix dA dA ℂ}
    (hR : IsPVM R) (hG : IsPVM G) :
    |(∑ a : R1, ∑ g : K, qform ψ (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)|
      ≤ Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) := by
  simp only [← BipartiteModel.qform_tensor, bornProb_eq_tensor, xSqNorm_eq_tensor]
  exact (BipartiteModel.tensor ψ).abs_sigma_sub_cloud_le hψ hR.toIn hG.toIn

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
  simp only [← BipartiteModel.snorm_tensor]
  exact (BipartiteModel.tensor ψ).sum_snorm_sq_prod_le_one hψ P Q hPsa hPidem hPorth hQ.toIn

/-- **From the sandwich to the ordered product.** The difference is Alice's operator against Bob's
commutator; Alice's projection times Bob's is a mutually orthogonal family, so the Cauchy--Schwarz
costs only the commutator. -/
theorem abs_sand_sub_ord_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hG : IsPVM G) (e : K → R2) :
    |(∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a)|
      ≤ Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) := by
  simp only [bornProb_eq_tensor, snorm_bOp_sq_eq_tensor]
  exact (BipartiteModel.tensor ψ).abs_sand_sub_ord_le hψ hA.toIn hG.toIn e

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
  simp only [xSqNorm_eq_tensor, bornProb_eq_tensor, fibSum_eq_fibSumIn]
  exact (BipartiteModel.tensor ψ).sum_bornProb_ord_ge hψ hA.toIn hR.toIn hG.toIn e

/-! ## The pasted POVM -/

/-- The other sandwich --- the one the pasted POVM is built from --- is also a Gram operator. -/
theorem sandOpG_posSemidef (hR : IsPVM R) (hG : IsPVM G) (a : R1) (g : K) :
    (G g * R a * G g).PosSemidef := by
  rw [hR.toIn.conj_eq_gram hG.toIn a g]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sum_sandOpG (hR : IsPVM R) (hG : IsPVM G) :
    ∑ p : R1 × K, G p.2 * R p.1 * G p.2 = 1 :=
  hR.toIn.sum_conj hG.toIn

theorem pasteJ_posSemidef (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) (p : R1 × R2) :
    (pasteJ R G e p).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (hR.toIn.pasteJ_nonneg hG.toIn e p)

theorem sum_pasteJ (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    ∑ p : R1 × R2, pasteJ R G e p = 1 :=
  hR.toIn.sum_pasteJ hG.toIn e

/-- **From the Born rule to the state-dependent distance**: Alice's family is projective and the
pasted family is a POVM, so the summed deviation is at most twice the disagreement. -/
theorem sum_xSqNorm_pasteJ_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    ∑ p : R1 × R2, xSqNorm ψ (A p) (pasteJ R G e p)
      ≤ 2 * (1 - ∑ p : R1 × R2, bornProb ψ (A p) (pasteJ R G e p)) := by
  simp only [xSqNorm_eq_tensor, bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_xSqNorm_pasteJ_le hψ hA.toIn hR.toIn hG.toIn e

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
  simp only [xSqNorm_eq_tensor] at h1 h2
  simp only [snorm_bOp_sq_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_snorm_sq_comm_coarse_le hA.toIn hR.toIn hGf.toIn h1 h2

/-- **The collision term**: the pairs of `G`-outcomes that the outcome map cannot tell apart. It
is exactly what the coarse-grained cloud has beyond the fine-grained one, and the only place where
the separating property of the outcome map is needed. -/
def collisionTerm (ψ : dA × dB → ℂ) (R : R1 → Matrix dB dB ℂ) (G : K → Matrix dB dB ℂ)
    (Ga : K → Matrix dA dA ℂ) (e : K → R2) : ℝ :=
  ∑ a : R1, ∑ g : K, ∑ g' ∈ univ.filter fun g' => g' ≠ g ∧ e g' = e g,
    bornProb ψ (Ga g') (R a * G g * R a)

/-- **The collision term is that of the tensor-product model.** -/
theorem collisionTerm_eq_tensor (ψ : dA × dB → ℂ) (R : R1 → Matrix dB dB ℂ)
    (G : K → Matrix dB dB ℂ) (Ga : K → Matrix dA dA ℂ) (e : K → R2) :
    collisionTerm ψ R G Ga e = (BipartiteModel.tensor ψ).collisionTerm R G Ga e := by
  simp only [collisionTerm, BipartiteModel.collisionTerm, bornProb_eq_tensor]

theorem collisionTerm_nonneg (ψ : dA × dB → ℂ) {Ga : K → Matrix dA dA ℂ}
    (hR : IsPVM R) (hG : IsPVM G) (hGa : IsPVM Ga) (e : K → R2) :
    0 ≤ collisionTerm ψ R G Ga e := by
  rw [collisionTerm_eq_tensor]
  exact (BipartiteModel.tensor ψ).collisionTerm_nonneg hR.toIn hG.toIn hGa.toIn e

/-- **The strife minus the cloud is exactly the collision term.** Both are sums of the same Born
probabilities; coarse-graining pairs each `G`-outcome with every other one the map identifies
with it. -/
theorem strife_sub_cloud_eq {ψ : dA × dB → ℂ} {Ga : K → Matrix dA dA ℂ} (e : K → R2) :
    (∑ a : R1, ∑ b : R2,
        bornProb ψ (fibSum Ga e b) (R a * fibSum G e b * R a))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)
      = collisionTerm ψ R G Ga e := by
  rw [collisionTerm_eq_tensor]
  simp only [bornProb_eq_tensor, fibSum_eq_fibSumIn]
  exact (BipartiteModel.tensor ψ).strife_sub_cloud_eq e

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
  simp only [xSqNorm_eq_tensor, fibSum_eq_fibSumIn] at h1 h2
  simp only [snorm_bOp_sq_eq_tensor, xSqNorm_eq_tensor, collisionTerm_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_snorm_sq_comm_fine_le hψ hA.toIn hR.toIn hG.toIn hGa.toIn e
    h1 h2

/-- **The pasted POVM agrees with Alice's joint measurement, at one question.** Step (i) reaches
the ordered product and step (ii) the sandwich. -/
theorem one_sub_sum_bornProb_pasteJ_le' {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    1 - (∑ p : R1 × R2, bornProb ψ (A p) (pasteJ R G e p))
      ≤ (∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b)) / 2
        + Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2)
        + Real.sqrt (∑ a : R1, ∑ g : K,
            snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) := by
  simp only [bornProb_eq_tensor, xSqNorm_eq_tensor, snorm_bOp_sq_eq_tensor, fibSum_eq_fibSumIn]
  exact (BipartiteModel.tensor ψ).one_sub_sum_bornProb_pasteJ_le' hψ hA.toIn hR.toIn hG.toIn e

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
    IsPVM fun i => (aOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) := by
  classical
  exact (h.toIn.map (BipartiteModel.aOpStarAlgHom (dB := dB))).toIsPVM

theorem IsPVM.bOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    IsPVM fun i => (bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) := by
  classical
  exact (h.toIn.map (BipartiteModel.bOpStarAlgHom (dA := dA))).toIsPVM

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
      ≤ ∑ p : R1 × R2, snorm v (A p - B p) ^ 2 :=
  (StateModel.mat v).sum_snorm_sq_cool_prod hA.toIn B

/-- **The marginal step.** Alice's joint projective measurement, consistent with Bob's ordered
product `Z_b X_a`, has its `R2`-marginal consistent with `X_a` alone. -/
theorem sum_xSqNorm_marg_le {ψ : dA × dB → ℂ} {Q : R1 × R2 → Matrix dA dA ℂ}
    {Z : R2 → Matrix dB dB ℂ} (X : R1 → Matrix dB dB ℂ) (hQ : IsPVM Q) (hZ : IsPVM Z) :
    ∑ a : R1, xSqNorm ψ (∑ b : R2, Q (a, b)) (X a)
      ≤ 2 * (∑ p : R1 × R2, snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
              - aOp (Q p)) ^ 2)
        + 2 * ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
  simp only [xSqNorm_eq_tensor, ← BipartiteModel.snorm_tensor]
  exact (BipartiteModel.tensor ψ).sum_xSqNorm_marg_le X hQ.toIn hZ.toIn

/-- **A projective family stays projective under a relabelling of its outcomes by a bijection.** -/
theorem IsPVM.comp_equiv {N ι κ : Type*} [Fintype N] [DecidableEq N] [Fintype ι] [Fintype κ]
    {P : ι → Matrix N N ℂ} (h : IsPVM P) (e : κ ≃ ι) : IsPVM fun k => P (e k) := by
  classical
  exact (h.toIn.comp_equiv e).toIsPVM

/-- **Bob's own deviation, through Alice's operator.** The three-term triangle inequality in the
one shape the consumer needs: a same-side deviation bounded by two cross-party ones. -/
theorem normSq_stateVecB_sub_le (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B₁ B₂ : Matrix dB dB ℂ) :
    ‖stateVecB ψ (B₁ - B₂)‖ ^ 2 ≤ 2 * xSqNorm ψ A B₁ + 2 * xSqNorm ψ A B₂ := by
  rw [normSq_stateVecB_eq_tensor, xSqNorm_eq_tensor, xSqNorm_eq_tensor]
  exact (BipartiteModel.tensor ψ).swap_stateSqNorm_sub_le A B₁ B₂

/-- **Attaching the other party's projection to a consistent joint measurement costs nothing.**
The relation the marginal step's first term needs, from the consistency with the ordered product
alone. -/
theorem sum_snorm_sq_mul_proj_le {ψ : dA × dB → ℂ} (Q : R1 × R2 → Matrix dA dA ℂ)
    {Z : R2 → Matrix dB dB ℂ} (X : R1 → Matrix dB dB ℂ) (hZ : IsPVM Z) :
    ∑ p : R1 × R2, snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
        - aOp (Q p)) ^ 2
      ≤ 4 * ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
  simp only [xSqNorm_eq_tensor, ← BipartiteModel.snorm_tensor]
  exact (BipartiteModel.tensor ψ).sum_snorm_sq_mul_proj_le Q X hZ.toIn

/-- **The marginal step, packaged.** A joint projective measurement consistent with the other
party's ordered product `Z_b X_a` has its `R2`-marginal consistent with `X_a` alone, at ten times
the input. -/
theorem sum_xSqNorm_marg_le' {ψ : dA × dB → ℂ} {Q : R1 × R2 → Matrix dA dA ℂ}
    {Z : R2 → Matrix dB dB ℂ} (X : R1 → Matrix dB dB ℂ) (hQ : IsPVM Q) (hZ : IsPVM Z) :
    ∑ a : R1, xSqNorm ψ (∑ b : R2, Q (a, b)) (X a)
      ≤ 10 * ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
  simp only [xSqNorm_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_xSqNorm_marg_le' X hQ.toIn hZ.toIn

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
  simp only [xSqNorm_eq_tensor, fibSum_eq_fibSumIn] at hP1 hP2 hP4
  simp only [collisionTerm_eq_tensor] at hcoll
  simp only [bornProb_eq_tensor]
  exact (BipartiteModel.tensor ψ).one_sub_sum_bornProb_pasteJ_le hψ hw0 hw1 e
    (fun i => (hA i).toIn) (fun i => (hR i).toIn) (fun i => (hG i).toIn) (fun i => (hGa i).toIn)
    hP1 hP2 hP4 hcoll

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
  simp only [collisionTerm_eq_tensor]
  exact (BipartiteModel.tensor ψ).sum_collisionTerm_le hψ hν0 (fun z => (hR z).toIn)
    (fun z => (hG z).toIn) (fun z => (hGa z).toIn) e hε hsep

end Collision

end MIPRE

end

end
