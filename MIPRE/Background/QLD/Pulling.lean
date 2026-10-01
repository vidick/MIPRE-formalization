/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.MTilde
public import MIPRE.Background.QLD.AncTransport
public import MIPRE.Foundations.Introspection.ValueStability

@[expose] public section

/-!
# The estimates of `lem:qld-pauli-selfcons`, by polynomial outcome

`MIPRE/Background/QLD/AncTransport.lean` closes the identities of the paper's pulling chain. Its
estimates --- displays `eq:qld-pulling-7` and `eq:qld-pulling-11` --- consume the second item of
`lem:qld-helper`, but not in the form that lemma is stated in. The helper is stated at an outcome
`a` in `F_q`, which is what the expansion stage produces; the chain sums over the *polynomial*
outcomes `g` of the simultaneous measurement, because the label `coded(g) . u-tilde` it carries is
a function of `g` and not of `g(u)`.

The two sums are equal, not merely comparable. Within a fibre of the evaluation the pair
measurement's outcomes are orthogonal projectors, so every cross term of the squared norm
vanishes, and the fibres partition the outcomes. That is `StateModel.snorm_sq_sum_orthogonal` of
`MIPRE/Foundations/ModelCalculus.lean`, and the helper in the chain's own indexing is its
corollary.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The estimates about a single
vector `v` and matrices on its index set are stated in a state model `M : StateModel 𝒞`
(`snorm v T` is `M.snorm T`, `qform v T` is `M.qform T`, the adjoint is `star`), and the positivity
of a sandwich is that of the represented operator. The estimates about two parties are stated in a
bipartite model: `aOp A * bOp B` is `M.πA A * M.πB B`, and the agreement operator is an element of
the model's algebra. In `fact:add-a-proj` the register factor is a matrix of scalars on a register
of the second player, `B ⊗ T` being `smulKron B T` in the matrices over the second player's
algebra, ordered as they are (`MatrixStar`). The helper in the chain's indexing is stated for any
`SimulPair M S K ι δ`. The matrix `snorm_sq_sum_orthogonal` of this file is
`StateModel.snorm_sq_sum_orthogonal`, and is used from `ModelCalculus.lean`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The agreement operator, and inserting it as a near-identity

Display `eq:qld-pulling-1` right-multiplies by
`sum_g (S-hat^W_g)_{A A'} (x) (M-hat^{(Point,W),u}_{g(u)})_{B A''}`, which the first item of
`lem:qld-helper` says is close to the identity on the state. What makes the step cheap is that this
operator is a *projection*: the outcomes of the pair measurement are orthogonal, so the cross terms
vanish, and the opposite party's factors are projectors. Its deficit from the identity is then
exactly one minus the agreement, with no Cauchy--Schwarz anywhere. -/

section Agree

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {G : Type*} [Fintype G]

/-- **The agreement operator** `sum_g S_g (x) B_g` of a family on one party against a family on the
other, indexed by the same outcome. -/
def agreeOp (M : BipartiteModel 𝒞 𝒜 ℬ) (S : G → 𝒜) (B : G → ℬ) : 𝒞 :=
  ∑ g, M.πA (S g) * M.πB (B g)

theorem agreeOp_conjTranspose (M : BipartiteModel 𝒞 𝒜 ℬ) {S : G → 𝒜} {B : G → ℬ}
    (hS : ∀ g, star (S g) = S g) (hB : ∀ g, star (B g) = B g) :
    star (agreeOp M S B) = agreeOp M S B := by
  rw [agreeOp, star_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [M.star_πA_mul_πB, hS, hB]

/-- **It is idempotent**, because the first party's outcomes are orthogonal and the second party's
factors are projectors. -/
theorem agreeOp_mul_self [DecidableEq G] (M : BipartiteModel 𝒞 𝒜 ℬ) {S : G → 𝒜}
    (hS : IsPVMIn S) {B : G → ℬ} (hB : ∀ g, B g * B g = B g) :
    agreeOp M S B * agreeOp M S B = agreeOp M S B := by
  rw [agreeOp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single g (fun g' _ hg' => by
      rw [M.πA_mul_πB_mul, hS.orthogonal (Ne.symm hg'), map_zero, zero_mul])
    fun hmem => absurd (Finset.mem_univ g) hmem,
    M.πA_mul_πB_mul, hS.idem, hB]

theorem qform_agreeOp (M : BipartiteModel 𝒞 𝒜 ℬ) (S : G → 𝒜) (B : G → ℬ) :
    M.qform (agreeOp M S B) = ∑ g, M.bornProb (S g) (B g) := by
  rw [agreeOp, M.qform_sum]
  rfl

/-- **The deficit of the agreement operator from the identity is one minus the agreement.** No
Cauchy--Schwarz: the operator is a projection, so its squared deviation is linear in it. -/
theorem snorm_sq_one_sub_agreeOp [DecidableEq G] {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1)
    {S : G → 𝒜} (hS : IsPVMIn S) {B : G → ℬ} (hBsa : ∀ g, star (B g) = B g)
    (hB : ∀ g, B g * B g = B g) :
    M.snorm (1 - agreeOp M S B) ^ 2 = 1 - ∑ g, M.bornProb (S g) (B g) := by
  have hsa := agreeOp_conjTranspose M hS.star_eq hBsa
  have hid := agreeOp_mul_self M hS hB
  have hkey : star ((1 : 𝒞) - agreeOp M S B) * (1 - agreeOp M S B) = 1 - agreeOp M S B := by
    rw [star_sub, star_one, hsa]
    calc (1 - agreeOp M S B) * (1 - agreeOp M S B)
        = 1 - agreeOp M S B - agreeOp M S B + agreeOp M S B * agreeOp M S B := by noncomm_ring
      _ = 1 - agreeOp M S B := by rw [hid]; abel
  rw [M.snorm_sq_eq_qform, hkey, M.qform_sub, M.qform_one hM, qform_agreeOp]

/-- **Inserting the near-identity costs at most its own deficit.** A contraction on the left cannot
amplify it, which is the whole of display `eq:qld-pulling-1`. -/
theorem snorm_sub_mul_agreeOp_le (M : BipartiteModel 𝒞 𝒜 ℬ) {X : 𝒞} (hX : M.Bnd X 1)
    (S : G → 𝒜) (B : G → ℬ) :
    M.snorm (X - X * agreeOp M S B) ≤ M.snorm (1 - agreeOp M S B) := by
  rw [show X - X * agreeOp M S B = X * (1 - agreeOp M S B) by rw [mul_sub, mul_one]]
  exact le_trans (M.snorm_mul_le hX _) (le_of_eq (one_mul _))

end Agree

/-! ## The paper's `fact:add-a-proj`, in the shape the chain uses it -/

section AddAProj

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R] {anc X : Type*} [Fintype anc] [DecidableEq anc]
  [Fintype X]

/-- **A family of projections tensored with a projective measurement of a register sums to at most
the identity.** The complement is `∑_x (1 - B_x) ⊗ T_x`, a sum of nonnegative terms. This is what
displays `eq:qld-pulling-8` and `eq:qld-pulling-10` use to discard the index the sandwich runs
over. -/
theorem sum_kron_le_one {B : X → R} (hBsa : ∀ x, star (B x) = B x)
    (hB : ∀ x, B x * B x = B x) {T : X → Matrix anc anc ℂ} (hT : IsPVM T) :
    (∑ x, smulKron (B x) (T x)) ≤ (1 : Matrix anc anc R) := by
  have hrw : (1 : Matrix anc anc R) - ∑ x, smulKron (B x) (T x)
      = ∑ x, smulKron (1 - B x) (T x) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => (smulKron_sub_left 1 (B x) (T x)).symm,
      Finset.sum_sub_distrib, ← smulKron_sum_right, hT.sum_eq_one, smulKron_one_one]
  refine sub_nonneg.mp ?_
  rw [hrw]
  refine Finset.sum_nonneg fun x _ => smulKron_nonneg_of_proj ?_ ?_
  · refine posSemidef_of_proj ?_ ?_
    · rw [star_sub, star_one, hBsa]
    · calc (1 - B x) * (1 - B x) = 1 - B x - B x + B x * B x := by noncomm_ring
        _ = 1 - B x := by rw [hB]; abel
  · rw [hT.isSelfAdjoint, hT.idem]

/-- **Discarding that index.** Against a nonnegative operator on the other party, the family's
total contribution is at most the operator's own weight. The second player's algebra is the
matrices over `R` on the register. -/
theorem sum_bornProb_kron_le {𝒞 𝒜 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜]
    [StarRing 𝒜] [Algebra ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (M : BipartiteModel 𝒞 𝒜 (Matrix anc anc R)) {A : 𝒜} (hA : 0 ≤ A) {B : X → R}
    (hBsa : ∀ x, star (B x) = B x) (hB : ∀ x, B x * B x = B x) {T : X → Matrix anc anc ℂ}
    (hT : IsPVM T) :
    ∑ x, M.bornProb A (smulKron (B x) (T x)) ≤ M.bornProb A 1 := by
  rw [← M.bornProb_sum_right]
  exact bornProb_mono_right M hA (sum_kron_le_one hBsa hB hT)

end AddAProj

/-! ## The middle of `eq:qld-pulling-10`'s justification

Between `fact:add-a-proj` at the top and the helper at the bottom, the estimate does two things.
It expands a squared norm over the orthogonal outcomes of a projective family into a sum of
sandwiches, one per outcome, and it then *moves* the measurement being sandwiched from one party
to the other. The move is the only place in the chain where Cauchy--Schwarz is used, and it is
where the `O(sqrt(eps))` of display `eq:qld-pulling-13` comes from: the two placements of the
point measurement differ by `eps` in summed squared state distance, and substituting one for the
other costs twice its square root.

Nothing here knows about the chain's indices. The projective family, the operators beside it and
the two placements are arbitrary; what is used of the geometry is that the measurement being
moved is a projection commuting with what it sandwiches, which in the chain holds because the two
act on different parties. -/

section Substitute

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] {ι : Type*}

/-- **A projection is represented by a positive operator.** -/
theorem π_nonneg_of_isStarProjection (M : StateModel 𝒞) {P : 𝒞} (hP : IsStarProjection P) :
    0 ≤ M.π P := by
  have h : P = star P * P := by rw [hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
  rw [h]
  exact M.π_star_mul_self_nonneg P

/-- **A projector's sandwich is the squared norm of half of it.** The `sqrt(1)` factors of the
chain's Cauchy--Schwarz are read off a sandwich this way. -/
theorem snorm_sq_proj_mul_eq_qform (M : StateModel 𝒞) {S Y : 𝒞} (hSsa : star S = S)
    (hSidem : S * S = S) (hYsa : star Y = Y) :
    M.snorm (S * Y) ^ 2 = M.qform (Y * S * Y) := by
  rw [M.snorm_sq_eq_qform, star_mul, hSsa, hYsa]
  congr 1
  rw [mul_assoc, ← mul_assoc S S Y, hSidem, ← mul_assoc]

/-- **A sandwiched positive operator is a nonnegative form.** -/
theorem qform_sandwich_nonneg (M : StateModel 𝒞) {P : 𝒞} (hP : 0 ≤ M.π P) (W : 𝒞) :
    0 ≤ M.qform (star W * P * W) := by
  refine M.qform_nonneg ?_
  rw [map_mul, map_mul, map_star]
  exact star_left_conjugate_nonneg hP _

/-- **The squared norm of a sum over orthogonal outcomes is a sum of sandwiches.** One term per
outcome, with the operator beside it on both sides; the cross terms vanish because the outcomes
annihilate each other. -/
theorem snorm_sq_sum_proj_sandwich [Fintype ι] [DecidableEq ι] (M : StateModel 𝒞)
    {P : ι → 𝒞} (hP : IsPVMIn P) (W : ι → 𝒞) (s : Finset ι) :
    M.snorm (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, M.qform (star (W i) * P i * W i) := by
  rw [M.snorm_sq_sum_proj_mul hP.star_eq (fun i j hij => hP.orthogonal hij) W s]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (W i) * star (P i) * (P i * W i) = star (W i) * P i * W i := by
    rw [hP.star_eq, mul_assoc, ← mul_assoc (P i) (P i) (W i), hP.idem, ← mul_assoc]
  rw [M.snorm_sq_eq_qform, star_mul, h]

/-- **Dropping a constraint on the outcomes.** Every sandwich is nonnegative, so enlarging the set
summed over only increases the total. -/
theorem sum_qform_sandwich_le_of_subset [Fintype ι] (M : StateModel 𝒞) {P : ι → 𝒞}
    (hP : IsPVMIn P) (W : ι → 𝒞) {s t : Finset ι} (hst : s ⊆ t) :
    ∑ i ∈ s, M.qform (star (W i) * P i * W i) ≤ ∑ i ∈ t, M.qform (star (W i) * P i * W i) :=
  Finset.sum_le_sum_of_subset_of_nonneg hst fun i _ _ =>
    qform_sandwich_nonneg M (π_nonneg_of_isStarProjection M (hP.isStarProjection i)) (W i)

/-- **Cauchy--Schwarz across an index, with the first family not self-adjoint.**
With `A` self-adjoint, `A * R` is already `star A * R`; the projector form of the chain's swap
needs the general one. -/
theorem abs_sum_qform_conjTranspose_mul_le (M : StateModel 𝒞) (s : Finset ι)
    (A R : ι → 𝒞) :
    |∑ i ∈ s, M.qform (star (A i) * R i)|
      ≤ Real.sqrt (∑ i ∈ s, M.snorm (A i) ^ 2) * Real.sqrt (∑ i ∈ s, M.snorm (R i) ^ 2) := by
  have hpt : ∀ i ∈ s, |M.qform (star (A i) * R i)| ≤ M.snorm (A i) * M.snorm (R i) :=
    fun i _ => M.abs_qform_star_mul_le (A i) (R i)
  refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hpt)) ?_
  have hsq := sum_mul_sq_le_sq_mul_sq s (fun i => M.snorm (A i)) (fun i => M.snorm (R i))
  have hn : (0 : ℝ) ≤ ∑ i ∈ s, M.snorm (A i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ i ∈ s, M.snorm (A i) * M.snorm (R i))
      ≤ |∑ i ∈ s, M.snorm (A i) * M.snorm (R i)| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ s, M.snorm (A i) * M.snorm (R i)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i ∈ s, M.snorm (A i) ^ 2) * ∑ i ∈ s, M.snorm (R i) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_mul hn _

/-- **Display `eq:qld-pulling-13`, with the deviation read through the projector.** The chain's
second remaining estimate sandwiches a *projector* with the measurement it swaps, and what bounds
the cost is the deviation read through that projector --- summing the projector away is what makes
the bound `eps` rather than `eps` times the number of pair outcomes, which is what the bare form
below would give. Otherwise the two are the same argument. -/
theorem abs_sum_qform_swap_proj_le (M : StateModel 𝒞) (s : Finset ι) {X Y S : ι → 𝒞}
    {ε : ℝ} (hXsa : ∀ i, star (X i) = X i) (hXidem : ∀ i, X i * X i = X i)
    (hYsa : ∀ i, star (Y i) = Y i) (hSsa : ∀ i, star (S i) = S i)
    (hSidem : ∀ i, S i * S i = S i) (hcomm : ∀ i, X i * S i = S i * X i)
    (hε : ∑ i ∈ s, M.snorm (S i * (X i - Y i)) ^ 2 ≤ ε)
    (hY : ∑ i ∈ s, M.snorm (S i * Y i) ^ 2 ≤ 1)
    (hX : ∑ i ∈ s, M.snorm (S i * X i) ^ 2 ≤ 1) :
    |(∑ i ∈ s, M.qform (X i * S i)) - ∑ i ∈ s, M.qform (Y i * S i * Y i)|
      ≤ 2 * Real.sqrt ε := by
  have hdev : ∀ i, star (X i - Y i) = X i - Y i := fun i => by
    rw [star_sub, hXsa, hYsa]
  have hterm : ∀ i ∈ s, M.qform (X i * S i) - M.qform (Y i * S i * Y i)
      = M.qform ((X i - Y i) * (S i * Y i)) + M.qform ((X i - Y i) * (S i * X i)) := by
    intro i _
    have hXSX : X i * S i * X i = X i * S i := by
      rw [mul_assoc, ← hcomm i, ← mul_assoc, hXidem]
    have hflip : M.qform (Y i * S i * (X i - Y i))
        = M.qform ((X i - Y i) * (S i * Y i)) := by
      rw [← M.qform_star (Y i * S i * (X i - Y i))]
      congr 1
      rw [star_mul, star_mul, hdev, hSsa, hYsa]
    rw [← hXSX, ← M.qform_sub, ← hflip, ← M.qform_add]
    congr 1
    noncomm_ring
  have hsplit : (∑ i ∈ s, M.qform (X i * S i)) - ∑ i ∈ s, M.qform (Y i * S i * Y i)
      = (∑ i ∈ s, M.qform ((X i - Y i) * (S i * Y i)))
        + ∑ i ∈ s, M.qform ((X i - Y i) * (S i * X i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  have hb : ∀ Z : ι → 𝒞, (∑ i ∈ s, M.snorm (S i * Z i) ^ 2) ≤ 1 →
      |∑ i ∈ s, M.qform ((X i - Y i) * (S i * Z i))| ≤ Real.sqrt ε := by
    intro Z hZ
    have hcong : ∀ i ∈ s, M.qform ((X i - Y i) * (S i * Z i))
        = M.qform (star (S i * (X i - Y i)) * (S i * Z i)) := by
      intro i _
      congr 1
      rw [star_mul, hSsa, hdev i, mul_assoc, ← mul_assoc (S i) (S i), hSidem]
    rw [Finset.sum_congr rfl hcong]
    refine le_trans (abs_sum_qform_conjTranspose_mul_le M s
      (fun i => S i * (X i - Y i)) (fun i => S i * Z i)) ?_
    have h1 : Real.sqrt (∑ i ∈ s, M.snorm (S i * Z i) ^ 2) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hZ
    calc Real.sqrt (∑ i ∈ s, M.snorm (S i * (X i - Y i)) ^ 2)
          * Real.sqrt (∑ i ∈ s, M.snorm (S i * Z i) ^ 2)
        ≤ Real.sqrt (∑ i ∈ s, M.snorm (S i * (X i - Y i)) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ε := by rw [mul_one]; exact Real.sqrt_le_sqrt hε
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have := hb Y hY
  have := hb X hX
  linarith

/-- **Display `eq:qld-pulling-13`: moving the sandwiched measurement across costs
`2 sqrt(eps)`.** `X` and `Y` are the two placements of one projective measurement, `X` the one
that commutes with the projector `S` it sandwiches; `eps` bounds the summed squared state
distance between them. Writing the difference of the two sandwiches as a sum of two terms, each
with the deviation `X - Y` on one side, and applying Cauchy--Schwarz across the index to each,
leaves `sqrt(eps)` twice --- the other factor of each product being a mass at most one.

The sandwich on the `X` side has collapsed: `X S X = X S` there, since `X` is a projection
commuting with `S`. That is why only the `Y` side is written with both halves. -/
theorem abs_sum_qform_swap_le (M : StateModel 𝒞) (s : Finset ι) {X Y S : ι → 𝒞} {ε : ℝ}
    (hXsa : ∀ i, star (X i) = X i) (hXidem : ∀ i, X i * X i = X i)
    (hYsa : ∀ i, star (Y i) = Y i) (hSsa : ∀ i, star (S i) = S i)
    (hcomm : ∀ i, X i * S i = S i * X i)
    (hε : ∑ i ∈ s, M.snorm (X i - Y i) ^ 2 ≤ ε)
    (hY : ∑ i ∈ s, M.snorm (S i * Y i) ^ 2 ≤ 1)
    (hX : ∑ i ∈ s, M.snorm (S i * X i) ^ 2 ≤ 1) :
    |(∑ i ∈ s, M.qform (X i * S i)) - ∑ i ∈ s, M.qform (Y i * S i * Y i)|
      ≤ 2 * Real.sqrt ε := by
  have hdev : ∀ i, star (X i - Y i) = X i - Y i := fun i => by
    rw [star_sub, hXsa, hYsa]
  have hterm : ∀ i ∈ s, M.qform (X i * S i) - M.qform (Y i * S i * Y i)
      = M.qform ((X i - Y i) * (S i * Y i)) + M.qform ((X i - Y i) * (S i * X i)) := by
    intro i _
    have hXSX : X i * S i * X i = X i * S i := by
      rw [mul_assoc, ← hcomm i, ← mul_assoc, hXidem]
    have hflip : M.qform (Y i * S i * (X i - Y i))
        = M.qform ((X i - Y i) * (S i * Y i)) := by
      rw [← M.qform_star (Y i * S i * (X i - Y i))]
      congr 1
      rw [star_mul, star_mul, hdev, hSsa, hYsa]
    rw [← hXSX, ← M.qform_sub, ← hflip, ← M.qform_add]
    congr 1
    noncomm_ring
  have hsplit : (∑ i ∈ s, M.qform (X i * S i)) - ∑ i ∈ s, M.qform (Y i * S i * Y i)
      = (∑ i ∈ s, M.qform ((X i - Y i) * (S i * Y i)))
        + ∑ i ∈ s, M.qform ((X i - Y i) * (S i * X i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  have hdevε : Real.sqrt (∑ i ∈ s, M.snorm (X i - Y i) ^ 2) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hε
  have hb : ∀ Z : ι → 𝒞, (∑ i ∈ s, M.snorm (S i * Z i) ^ 2) ≤ 1 →
      |∑ i ∈ s, M.qform ((X i - Y i) * (S i * Z i))| ≤ Real.sqrt ε := by
    intro Z hZ
    have hcs := abs_sum_qform_conjTranspose_mul_le M s (fun i => X i - Y i)
      (fun i => S i * Z i)
    simp only [hdev] at hcs
    refine le_trans hcs ?_
    have h1 : Real.sqrt (∑ i ∈ s, M.snorm (S i * Z i) ^ 2) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hZ
    calc Real.sqrt (∑ i ∈ s, M.snorm (X i - Y i) ^ 2)
          * Real.sqrt (∑ i ∈ s, M.snorm (S i * Z i) ^ 2)
        ≤ Real.sqrt (∑ i ∈ s, M.snorm (X i - Y i) ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ε := by rw [mul_one]; exact hdevε
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have := hb Y hY
  have := hb X hX
  linarith

end Substitute

/-! ## Display `eq:qld-pulling-3`: inserting the other party's outcome

The expansion stage leaves one party's projector beside the *other* party's point measurement.
The chain then inserts a copy of that measurement on the first party's side, which is where the
self-consistency of `lem:qld-win` is spent. Two things make the step cost exactly that and no
more. The deficit of the insertion is the cross-party deviation itself, because the outcome being
inserted beside is a projection and the two parties commute; and the projective family in front
is indexed through a map to the measurement's own outcomes, so the fibres of that map --- and not
the whole index --- are what the sum sees. -/

section Insert

section Fibre

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] {ι κ : Type*} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **A projective family in front, indexed through a map to the operators' own index.** Each
fibre of the map contributes at most the operator it names, because the projectors in a fibre sum
to a projection and a projection is a contraction. Without the fibres this would be false: the
index `i` can be far larger than `k`, and summing one operator once per `i` would multiply the
bound by the size of a fibre. -/
theorem sum_snorm_sq_proj_comp_le (M : StateModel 𝒞) {P : ι → 𝒞} (hP : IsPVMIn P)
    (c : ι → κ) (Z : κ → 𝒞) :
    ∑ i, M.snorm (P i * Z (c i)) ^ 2 ≤ ∑ k, M.snorm (Z k) ^ 2 := by
  have hsplit : ∑ i, M.snorm (P i * Z (c i)) ^ 2
      = ∑ k, ∑ i ∈ univ.filter fun i => c i = k, M.snorm (P i * Z (c i)) ^ 2 :=
    (Finset.sum_fiberwise (univ : Finset ι) c fun i => M.snorm (P i * Z (c i)) ^ 2).symm
  rw [hsplit]
  refine Finset.sum_le_sum fun k _ => ?_
  have hfib : ∑ i ∈ univ.filter fun i => c i = k, M.snorm (P i * Z (c i)) ^ 2
      = ∑ i ∈ univ.filter fun i => c i = k, M.snorm (P i * Z k) ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [hfib, ← M.snorm_sq_sum_orthogonal hP (Z k) (univ.filter fun i => c i = k)]
  have h := M.snorm_mul_le (M.bnd_one_of_isStarProjection ((hP.coarse c).isStarProjection k))
    (Z k)
  rw [one_mul] at h
  exact pow_le_pow_left₀ (M.snorm_nonneg _) h 2

end Fibre

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The deficit of the insertion is the cross-party deviation.** Inserting one party's outcome
in front of the other party's costs `(1 - A) B`, which is `B (B - A)` because `B` is a projection
and the two parties commute --- and a projection in front costs nothing. -/
theorem snorm_one_sub_aOp_mul_bOp_le (M : BipartiteModel 𝒞 𝒜 ℬ) (A : 𝒜) {B : ℬ}
    (hBsa : star B = B) (hBidem : B * B = B) :
    M.snorm ((1 - M.πA A) * M.πB B) ≤ M.snorm (M.πA A - M.πB B) := by
  have hrw : (1 - M.πA A) * M.πB B = M.πB B * (M.πB B - M.πA A) := by
    rw [sub_mul, mul_sub, one_mul, ← map_mul M.πB B B, hBidem, (M.commute A B).eq]
  have hbnd : M.Bnd (M.πB B) 1 := M.bnd_πB_of_isStarProjection ⟨hBidem, hBsa⟩
  rw [hrw, M.snorm_sub_comm (M.πA A) (M.πB B)]
  simpa using M.snorm_mul_le hbnd (M.πB B - M.πA A)

/-- **Display `eq:qld-pulling-3`.** Inserting the other party's outcome beside each term of a
projective family, the family being indexed through the measurement's own outcomes, costs the
measurement's summed cross-consistency and nothing else. -/
theorem sum_snorm_sq_insert_le (M : BipartiteModel 𝒞 𝒜 ℬ) {P : ι → 𝒞} (hP : IsPVMIn P)
    (c : ι → κ) (A : κ → 𝒜) {B : κ → ℬ} (hBsa : ∀ k, star (B k) = B k)
    (hBidem : ∀ k, B k * B k = B k) {ε : ℝ} (hcons : ∑ k, M.xSqNorm (A k) (B k) ≤ ε) :
    ∑ i, M.snorm (P i * ((1 - M.πA (A (c i))) * M.πB (B (c i)))) ^ 2 ≤ ε := by
  refine le_trans (sum_snorm_sq_proj_comp_le M.toStateModel hP c
    fun k => (1 - M.πA (A k)) * M.πB (B k)) ?_
  refine le_trans (Finset.sum_le_sum fun k (_ : k ∈ univ) => ?_) hcons
  rw [M.xSqNorm_eq_sq]
  exact pow_le_pow_left₀ (M.snorm_nonneg _)
    (snorm_one_sub_aOp_mul_bOp_le M (A k) (hBsa k) (hBidem k)) 2

end Insert

/-! ## The final passage: coarse-graining the self-consistency

What the chain establishes is that the whole family of exact Pauli outcomes agrees across the
parties. What `lem:qld-swap` consumes is one binary observable, read off that family by a
function of the outcome. The passage between the two is the paper's `fact:agreement`,
`fact:data-processing` and `fact:agreement` again, and for *projective* families it is free: the
summed deviation and the agreement probability determine each other exactly, and agreement can
only increase under a relabelling. Foundations has that as `BipartiteModel.sum_xSqNorm_map_le`, on
POVMs; a projective family is one (`IsPVMIn.toPOVMIn`). -/

section Coarse

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]
  {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']

/-- **Coarse-graining a cross-party consistency costs nothing.** Two projective measurements
relabelled the same way stay as close as they were --- with no factor for the size of a fibre,
which a per-fibre triangle inequality would have cost. -/
theorem sum_xSqNorm_fibre_le {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1) {A : Λ → 𝒜}
    {B : Λ → ℬ} (hA : IsPVMIn A) (hB : IsPVMIn B) (f : Λ → Λ') :
    ∑ c, M.xSqNorm (∑ a ∈ univ.filter fun a => f a = c, A a)
        (∑ a ∈ univ.filter fun a => f a = c, B a)
      ≤ ∑ a, M.xSqNorm (A a) (B a) := by
  have h := M.sum_xSqNorm_map_le hM hA.toPOVMIn hB.toPOVMIn hA hB f
  simpa only [POVMIn.map_op, IsPVMIn.toPOVMIn_op] using h

end Coarse

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

section Helper

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']

namespace SimulPair

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

variable (P : SimulPair M S K ι δ)

/-- **The evaluated marginal's same-party product, split by polynomial outcome.** The evaluated
marginal at `a` is the sum of the polynomial-indexed outcomes over the fibre `g(u) = a`, and those
are orthogonal projections, so the squared norms add. -/
theorem snorm_sq_evalMarg_eq_sum_polyMarg (W : Bas) (u : Point F m) (a : F) :
    K.snorm (K.πA ((evalMarg P.SA W u).op a * (1 - ι.ΦA (hatMats S.PA W u a)))) ^ 2
      = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          K.snorm (K.πA ((polyMarg P.SA W).op g * (1 - ι.ΦA (hatMats S.PA W u a)))) ^ 2 := by
  have hsplit : (evalMarg P.SA W u).op a
      = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          (polyMarg P.SA W).op g := by
    rw [evalMarg_eq_map_polyMarg]
    exact POVMIn.map_op _ _ _
  rw [hsplit, map_mul, map_sum,
    K.snorm_sq_sum_orthogonal ((isPVM_polyMarg P.SA_proj W).map K.πA)]
  exact Finset.sum_congr rfl fun g _ => by rw [map_mul]

/-- **Item 2 of `lem:qld-helper`, in the chain's own indexing**: the same-party product of the
*polynomial-indexed* marginal with the complement of Alice's point measurement at that outcome's
own value. This is the form displays `eq:qld-pulling-7` and `eq:qld-pulling-11` consume. -/
theorem sum_snorm_sq_polyMarg_one_sub_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas) :
    ∑ u, uniform (Point F m) u
        * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          K.snorm (K.πA ((polyMarg P.SA W).op g
            * (1 - ι.ΦA (hatMats S.PA W u (g.eval u))))) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  have h := P.sum_snorm_sq_evalMarg_one_sub_le hfail W
  have hu : ∀ u : Point F m,
      (∑ a : F, K.snorm (K.πA ((evalMarg P.SA W u).op a
          * (1 - ι.ΦA (hatMats S.PA W u a)))) ^ 2)
        = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          K.snorm (K.πA ((polyMarg P.SA W).op g
            * (1 - ι.ΦA (hatMats S.PA W u (g.eval u))))) ^ 2 :=
    fun u => by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        P.snorm_sq_evalMarg_eq_sum_polyMarg W u a]
      rw [← Finset.sum_fiberwise (univ : Finset (LowIndDegPoly (F := F) (m := m) (d := d)))
        (fun g => g.eval u) fun g => K.snorm (K.πA ((polyMarg P.SA W).op g
          * (1 - ι.ΦA (hatMats S.PA W u (g.eval u))))) ^ 2]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g hg => by
        rw [(Finset.mem_filter.mp hg).2]
  rwa [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hu u]] at h

/-- **Display `eq:qld-pulling-14`**: the complement of the helper's agreement, read by polynomial
outcome. The sub-chain that justifies `eq:qld-pulling-10` terminates here, and the bound is the
helper's own `delta_S`: the marginal's outcomes sum to the identity, so the complementary mass is
one minus the agreement. -/
theorem sum_bornProb_polyMarg_one_sub_le (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
        K.bornProb ((polyMarg P.SA W).op g) (1 - ι.ΦB (hatMats S.PB W u (g.eval u)))
      ≤ δ := by
  have hlow := P.sum_bornProb_polyMarg_ge W
  have hsplit : ∀ u : Point F m,
      (∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          K.bornProb ((polyMarg P.SA W).op g) (1 - ι.ΦB (hatMats S.PB W u (g.eval u))))
        = 1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u (g.eval u))) := by
    intro u
    rw [Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        K.bornProb_sub_right ((polyMarg P.SA W).op g) 1 (ι.ΦB (hatMats S.PB W u (g.eval u))),
      Finset.sum_sub_distrib, ← K.bornProb_sum_left, (polyMarg P.SA W).sum_op,
      K.bornProb_one_one P.ψ_unit]
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hsplit u],
    Finset.sum_congr rfl fun u (_ : u ∈ univ) =>
      show uniform (Point F m) u * (1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u (g.eval u))))
          = uniform (Point F m) u - uniform (Point F m) u
              * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
                K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u (g.eval u)))
        from by ring,
    Finset.sum_sub_distrib, sum_uniform_eq_one]
  linarith

end SimulPair

end Helper

/-! ## Passing from pointwise agreement to equality of polynomials -/

section Agree

open MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

omit [NeZero m] in
/-- **Schwartz--Zippel for two low-individual-degree outcomes.** Distinct polynomials of individual
degree at most `d` agree at a uniform point with probability at most `md/q`. No lower bound on `d`
is needed: both polynomials carry the same degree bound, so the hypothesis
`prob_agree_le_individualDegree` wants is already met. -/
theorem sum_uniform_agree_le
    {p q : LowIndDegPoly (F := F) (m := m) (d := d)} (hne : p.toMv ≠ q.toMv) :
    ∑ u, uniform (Point F m) u * (if p.eval u = q.eval u then (1 : ℝ) else 0)
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  have hsz := prob_agree_le_individualDegree hne (LowIndDegPoly.degreeOf_toMv_le p)
    (LowIndDegPoly.degreeOf_toMv_le q)
  have hset : (univ.filter fun u : Point F m => p.eval u = q.eval u) = agree p.toMv q.toMv := by
    ext u
    rw [mem_filter, mem_agree, LowIndDegPoly.eval_toMv, LowIndDegPoly.eval_toMv]
    simp only [mem_univ, true_and]
  simp only [uniform]
  rw [← Finset.mul_sum, Finset.sum_boole, hset, Fintype.card_fun, Fintype.card_fin]
  push_cast at hsz ⊢
  rw [inv_mul_eq_div]
  exact hsz

omit [NeZero m] in
/-- **Restricting a weighted sum to pointwise agreement costs `md/q`**, at every index whose
weight is nonzero and whose two polynomials are distinct. This is display `eq:qld-pulling-12`: the
chain's sum is constrained by an equality of polynomial *values* at the sampled point, and passing
to equality of the polynomials themselves discards only the tuples where distinct polynomials
happen to agree there. The weights are the Born probabilities of a projective family, hence
nonnegative and summing to at most one.

The hypothesis is asked only where the weight is nonzero, which is what lets the same packaging
serve `eq:qld-unitary-8` of `lem:qld-swap` item 2: there the index is a *pair* and the diagonal,
where the two polynomials coincide, is excluded by the weight rather than by the index set. -/
theorem sum_uniform_agree_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ι → LowIndDegPoly (F := F) (m := m) (d := d)} (w : ι → ℝ)
    (hne : ∀ i, w i ≠ 0 → (p i).toMv ≠ (q i).toMv) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i ≤ 1) :
    ∑ u, uniform (Point F m) u
        * ∑ i ∈ univ.filter fun i => (p i).eval u = (q i).eval u, w i
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  have hmd : (0 : ℝ) ≤ (m : ℝ) * d / Fintype.card F := by positivity
  have hswap : (∑ u, uniform (Point F m) u
        * ∑ i ∈ univ.filter fun i => (p i).eval u = (q i).eval u, w i)
      = ∑ i, w i * ∑ u, uniform (Point F m) u
          * (if (p i).eval u = (q i).eval u then (1 : ℝ) else 0) := by
    simp only [Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
  rw [hswap]
  calc ∑ i, w i * ∑ u, uniform (Point F m) u
          * (if (p i).eval u = (q i).eval u then (1 : ℝ) else 0)
      ≤ ∑ i, w i * ((m : ℝ) * d / Fintype.card F) :=
        Finset.sum_le_sum fun i _ => by
          rcases eq_or_ne (w i) 0 with h0 | h0
          · rw [h0, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (sum_uniform_agree_le (hne i h0)) (hw0 i)
    _ = (∑ i, w i) * ((m : ℝ) * d / Fintype.card F) := by rw [Finset.sum_mul]
    _ ≤ 1 * ((m : ℝ) * d / Fintype.card F) := mul_le_mul_of_nonneg_right hw hmd
    _ = (m : ℝ) * d / Fintype.card F := one_mul _

end Agree

end MIPRE.QLD

end

end
