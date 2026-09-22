/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.MTilde
import MIPRE.Background.QLD.AncTransport
import MIPRE.Foundations.Introspection.ValueStability

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
vanishes, and the fibres partition the outcomes. That is `snorm_sq_sum_orthogonal` below, and the
helper in the chain's own indexing is its corollary.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## A squared norm over orthogonal outcomes -/

section Orthogonal

variable {N : Type*} [Fintype N] [DecidableEq N] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **A sum of orthogonal blocks has no cross terms.** If `S` is a projective family then, for any
`R`, the squared state norm of `(∑ g ∈ s, S g) R` is the sum of those of the `S g · R`. -/
theorem snorm_sq_sum_orthogonal (v : N → ℂ) {S : Λ → Matrix N N ℂ} (hS : IsPVM S)
    (R : Matrix N N ℂ) (s : Finset Λ) :
    snorm v ((∑ g ∈ s, S g) * R) ^ 2 = ∑ g ∈ s, snorm v (S g * R) ^ 2 := by
  classical
  rw [snorm_sq_eq_qform, Finset.sum_mul, Matrix.conjTranspose_sum, Finset.sum_mul]
  have hterm : ∀ g ∈ s, ((S g * R)ᴴ * ∑ g' ∈ s, S g' * R) = (S g * R)ᴴ * (S g * R) := by
    intro g hg
    rw [Finset.mul_sum, Finset.sum_eq_single_of_mem g hg fun g' _ hg' => ?_]
    rw [Matrix.conjTranspose_mul, hS.isSelfAdjoint, Matrix.mul_assoc,
      ← Matrix.mul_assoc (S g) (S g') R, hS.orthogonal (Ne.symm hg'), Matrix.zero_mul,
      Matrix.mul_zero]
  rw [Finset.sum_congr rfl hterm, qform_sum]
  exact Finset.sum_congr rfl fun g _ => (snorm_sq_eq_qform v (S g * R)).symm

end Orthogonal

/-! ## The agreement operator, and inserting it as a near-identity

Display `eq:qld-pulling-1` right-multiplies by
`sum_g (S-hat^W_g)_{A A'} (x) (M-hat^{(Point,W),u}_{g(u)})_{B A''}`, which the first item of
`lem:qld-helper` says is close to the identity on the state. What makes the step cheap is that this
operator is a *projection*: the outcomes of the pair measurement are orthogonal, so the cross terms
vanish, and the opposite party's factors are projectors. Its deficit from the identity is then
exactly one minus the agreement, with no Cauchy--Schwarz anywhere. -/

section Agree

variable {dA dB G : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype G] [DecidableEq G]

/-- **The agreement operator** `sum_g S_g (x) B_g` of a family on one party against a family on the
other, indexed by the same outcome. -/
def agreeOp (S : G → Matrix dA dA ℂ) (B : G → Matrix dB dB ℂ) :
    Matrix (dA × dB) (dA × dB) ℂ :=
  ∑ g, (aOp (S g) : Matrix (dA × dB) _ ℂ) * bOp (B g)

omit [DecidableEq G] in
theorem agreeOp_conjTranspose {S : G → Matrix dA dA ℂ} {B : G → Matrix dB dB ℂ}
    (hS : ∀ g, (S g)ᴴ = S g) (hB : ∀ g, (B g)ᴴ = B g) :
    (agreeOp S B)ᴴ = agreeOp S B := by
  rw [agreeOp, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [aOp_bOp_conjTranspose, hS, hB]

/-- **It is idempotent**, because the first party's outcomes are orthogonal and the second party's
factors are projectors. -/
theorem agreeOp_mul_self {S : G → Matrix dA dA ℂ} (hS : IsPVM S) {B : G → Matrix dB dB ℂ}
    (hB : ∀ g, B g * B g = B g) : agreeOp S B * agreeOp S B = agreeOp S B := by
  classical
  rw [agreeOp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single g (fun g' _ hg' => by
      rw [aOp_bOp_mul_aOp_bOp, hS.orthogonal (Ne.symm hg'), aOp_zero, Matrix.zero_mul])
    fun hmem => absurd (Finset.mem_univ g) hmem,
    aOp_bOp_mul_aOp_bOp, hS.idem, hB]

omit [DecidableEq G] in
theorem qform_agreeOp (ψ : dA × dB → ℂ) (S : G → Matrix dA dA ℂ) (B : G → Matrix dB dB ℂ) :
    qform ψ (agreeOp S B) = ∑ g, bornProb ψ (S g) (B g) := by
  rw [agreeOp, qform_sum]
  exact Finset.sum_congr rfl fun g _ => (bornProb_eq_qform ψ (S g) (B g)).symm

/-- **The deficit of the agreement operator from the identity is one minus the agreement.** No
Cauchy--Schwarz: the operator is a projection, so its squared deviation is linear in it. -/
theorem snorm_sq_one_sub_agreeOp {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {S : G → Matrix dA dA ℂ} (hS : IsPVM S) {B : G → Matrix dB dB ℂ}
    (hBsa : ∀ g, (B g)ᴴ = B g) (hB : ∀ g, B g * B g = B g) :
    snorm ψ (1 - agreeOp S B) ^ 2 = 1 - ∑ g, bornProb ψ (S g) (B g) := by
  have hsa := agreeOp_conjTranspose hS.isSelfAdjoint hBsa
  have hid := agreeOp_mul_self hS hB
  have hkey : ((1 : Matrix (dA × dB) (dA × dB) ℂ) - agreeOp S B)ᴴ * (1 - agreeOp S B)
      = 1 - agreeOp S B := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hid]
    abel
  rw [snorm_sq_eq_qform, hkey, qform_sub, qform_one ψ hψ, qform_agreeOp]

omit [DecidableEq G] in
/-- **Inserting the near-identity costs at most its own deficit.** A contraction on the left cannot
amplify it, which is the whole of display `eq:qld-pulling-1`. -/
theorem snorm_sub_mul_agreeOp_le (ψ : dA × dB → ℂ) {X : Matrix (dA × dB) (dA × dB) ℂ}
    (hX : Bnd X 1) (S : G → Matrix dA dA ℂ) (B : G → Matrix dB dB ℂ) :
    snorm ψ (X - X * agreeOp S B) ≤ snorm ψ (1 - agreeOp S B) := by
  rw [show X - X * agreeOp S B = X * (1 - agreeOp S B) from by
    rw [Matrix.mul_sub, Matrix.mul_one]]
  exact le_trans (snorm_mul_le ψ hX _) (le_of_eq (one_mul _))

end Agree

/-! ## The paper's `fact:add-a-proj`, in the shape the chain uses it -/

section AddAProj

variable {dB anc X : Type*} [Fintype dB] [DecidableEq dB] [Fintype anc] [DecidableEq anc]
  [Fintype X]

/-- **A family of projectors tensored with a projective measurement sums to at most the
identity.** The complement is `∑_x (1 - B_x) ⊗ T_x`, a sum of positive semidefinite terms. This is
what displays `eq:qld-pulling-8` and `eq:qld-pulling-10` use to discard the index the sandwich
runs over. -/
theorem sum_kron_le_one {B : X → Matrix dB dB ℂ} (hBsa : ∀ x, (B x)ᴴ = B x)
    (hB : ∀ x, B x * B x = B x) {T : X → Matrix anc anc ℂ} (hT : IsPVM T) :
    (∑ x, B x ⊗ₖ T x) ≤ (1 : Matrix (dB × anc) (dB × anc) ℂ) := by
  have hrw : (1 : Matrix (dB × anc) (dB × anc) ℂ) - ∑ x, B x ⊗ₖ T x
      = ∑ x, ((1 : Matrix dB dB ℂ) - B x) ⊗ₖ T x := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) =>
        sub_kronecker_right (1 : Matrix dB dB ℂ) (B x) (T x),
      Finset.sum_sub_distrib, ← kronecker_sum_right, hT.sum_eq_one, Matrix.one_kronecker_one]
  refine sub_nonneg.mp ?_
  rw [hrw]
  refine Finset.sum_nonneg fun x _ => Matrix.nonneg_iff_posSemidef.mpr ?_
  refine Matrix.PosSemidef.kronecker ?_ (hT.posSemidef x)
  refine posSemidef_of_proj ?_ ?_
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hBsa]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hB]
    abel

/-- **Discarding that index.** Against a positive semidefinite operator on the other party, the
family's total contribution is at most the operator's own weight. -/
theorem sum_bornProb_kron_le {dA : Type*} [Fintype dA] [DecidableEq dA] (ψ : dA × (dB × anc) → ℂ)
    {A : Matrix dA dA ℂ} (hA : A.PosSemidef) {B : X → Matrix dB dB ℂ}
    (hBsa : ∀ x, (B x)ᴴ = B x) (hB : ∀ x, B x * B x = B x) {T : X → Matrix anc anc ℂ}
    (hT : IsPVM T) :
    ∑ x, bornProb ψ A (B x ⊗ₖ T x) ≤ bornProb ψ A 1 := by
  rw [← bornProb_sum_right]
  exact bornProb_mono_right ψ hA (sum_kron_le_one hBsa hB hT)

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

variable {N : Type*} [Fintype N] [DecidableEq N] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq N] in
/-- **A projector's sandwich is the squared norm of half of it.** The `sqrt(1)` factors of the
chain's Cauchy--Schwarz are read off a sandwich this way. -/
theorem snorm_sq_proj_mul_eq_qform (v : N → ℂ) {S Y : Matrix N N ℂ} (hSsa : Sᴴ = S)
    (hSidem : S * S = S) (hYsa : Yᴴ = Y) :
    snorm v (S * Y) ^ 2 = qform v (Y * S * Y) := by
  rw [snorm_sq_eq_qform, Matrix.conjTranspose_mul, hSsa, hYsa]
  congr 1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc S S Y, hSidem, ← Matrix.mul_assoc]

/-- **A sandwiched positive operator is a nonnegative form.** -/
theorem qform_sandwich_nonneg (v : N → ℂ) {P : Matrix N N ℂ} (hP : P.PosSemidef)
    (W : Matrix N N ℂ) : 0 ≤ qform v (Wᴴ * P * W) :=
  qform_nonneg_of_nonneg v (Matrix.nonneg_iff_posSemidef.mpr (hP.conjTranspose_mul_mul_same W))

/-- **The squared norm of a sum over orthogonal outcomes is a sum of sandwiches.** One term per
outcome, with the operator beside it on both sides; the cross terms vanish because the outcomes
annihilate each other. -/
theorem snorm_sq_sum_proj_sandwich (v : N → ℂ) {P : ι → Matrix N N ℂ} (hP : IsPVM P)
    (W : ι → Matrix N N ℂ) (s : Finset ι) :
    snorm v (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, qform v ((W i)ᴴ * P i * W i) := by
  rw [snorm_sq_sum_proj_mul v hP.isSelfAdjoint (fun i j hij => hP.orthogonal hij) W s]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (W i)ᴴ * (P i)ᴴ * (P i * W i) = (W i)ᴴ * P i * W i := by
    rw [hP.isSelfAdjoint, Matrix.mul_assoc, ← Matrix.mul_assoc (P i) (P i) (W i), hP.idem,
      ← Matrix.mul_assoc]
  rw [snorm_sq_eq_qform, Matrix.conjTranspose_mul, h]

omit [DecidableEq ι] in
/-- **Dropping a constraint on the outcomes.** Every sandwich is nonnegative, so enlarging the set
summed over only increases the total. -/
theorem sum_qform_sandwich_le_of_subset (v : N → ℂ) {P : ι → Matrix N N ℂ} (hP : IsPVM P)
    (W : ι → Matrix N N ℂ) {s t : Finset ι} (hst : s ⊆ t) :
    ∑ i ∈ s, qform v ((W i)ᴴ * P i * W i) ≤ ∑ i ∈ t, qform v ((W i)ᴴ * P i * W i) :=
  Finset.sum_le_sum_of_subset_of_nonneg hst fun i _ _ =>
    qform_sandwich_nonneg v (hP.posSemidef i) (W i)

/-- **Display `eq:qld-pulling-13`: moving the sandwiched measurement across costs
`2 sqrt(eps)`.** `X` and `Y` are the two placements of one projective measurement, `X` the one
that commutes with the projector `S` it sandwiches; `eps` bounds the summed squared state
distance between them. Writing the difference of the two sandwiches as a sum of two terms, each
with the deviation `X - Y` on one side, and applying Cauchy--Schwarz across the index to each,
leaves `sqrt(eps)` twice --- the other factor of each product being a mass at most one.

The sandwich on the `X` side has collapsed: `X S X = X S` there, since `X` is a projection
commuting with `S`. That is why only the `Y` side is written with both halves. -/
theorem abs_sum_qform_swap_le (v : N → ℂ) (s : Finset ι) {X Y S : ι → Matrix N N ℂ} {ε : ℝ}
    (hXsa : ∀ i, (X i)ᴴ = X i) (hXidem : ∀ i, X i * X i = X i) (hYsa : ∀ i, (Y i)ᴴ = Y i)
    (hSsa : ∀ i, (S i)ᴴ = S i) (hcomm : ∀ i, X i * S i = S i * X i)
    (hε : ∑ i ∈ s, snorm v (X i - Y i) ^ 2 ≤ ε)
    (hY : ∑ i ∈ s, snorm v (S i * Y i) ^ 2 ≤ 1)
    (hX : ∑ i ∈ s, snorm v (S i * X i) ^ 2 ≤ 1) :
    |(∑ i ∈ s, qform v (X i * S i)) - ∑ i ∈ s, qform v (Y i * S i * Y i)|
      ≤ 2 * Real.sqrt ε := by
  have hdev : ∀ i, (X i - Y i)ᴴ = X i - Y i := fun i => by
    rw [Matrix.conjTranspose_sub, hXsa, hYsa]
  have hterm : ∀ i ∈ s, qform v (X i * S i) - qform v (Y i * S i * Y i)
      = qform v ((X i - Y i) * (S i * Y i)) + qform v ((X i - Y i) * (S i * X i)) := by
    intro i _
    have hXSX : X i * S i * X i = X i * S i := by
      rw [Matrix.mul_assoc, ← hcomm i, ← Matrix.mul_assoc, hXidem]
    have hflip : qform v (Y i * S i * (X i - Y i)) = qform v ((X i - Y i) * (S i * Y i)) := by
      rw [← qform_conjTranspose v (Y i * S i * (X i - Y i))]
      congr 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hdev, hSsa, hYsa]
    rw [← hXSX, ← qform_sub, ← hflip, ← qform_add]
    congr 1
    noncomm_ring
  have hsplit : (∑ i ∈ s, qform v (X i * S i)) - ∑ i ∈ s, qform v (Y i * S i * Y i)
      = (∑ i ∈ s, qform v ((X i - Y i) * (S i * Y i)))
        + ∑ i ∈ s, qform v ((X i - Y i) * (S i * X i)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  have hdevε : Real.sqrt (∑ i ∈ s, snorm v (X i - Y i) ^ 2) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hε
  have hb : ∀ Z : ι → Matrix N N ℂ, (∑ i ∈ s, snorm v (S i * Z i) ^ 2) ≤ 1 →
      |∑ i ∈ s, qform v ((X i - Y i) * (S i * Z i))| ≤ Real.sqrt ε := by
    intro Z hZ
    refine le_trans (Introspection.abs_sum_qform_mul_le v s (fun i => X i - Y i)
      (fun i => S i * Z i) hdev) ?_
    have h1 : Real.sqrt (∑ i ∈ s, snorm v (S i * Z i) ^ 2) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hZ
    calc Real.sqrt (∑ i ∈ s, snorm v (X i - Y i) ^ 2)
          * Real.sqrt (∑ i ∈ s, snorm v (S i * Z i) ^ 2)
        ≤ Real.sqrt (∑ i ∈ s, snorm v (X i - Y i) ^ 2) * 1 :=
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

variable {N : Type*} [Fintype N] [DecidableEq N] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- **A projective family in front, indexed through a map to the operators' own index.** Each
fibre of the map contributes at most the operator it names, because the projectors in a fibre sum
to a projection and a projection is a contraction. Without the fibres this would be false: the
index `i` can be far larger than `k`, and summing one operator once per `i` would multiply the
bound by the size of a fibre. -/
theorem sum_snorm_sq_proj_comp_le (v : N → ℂ) {P : ι → Matrix N N ℂ} (hP : IsPVM P)
    (c : ι → κ) (Z : κ → Matrix N N ℂ) :
    ∑ i, snorm v (P i * Z (c i)) ^ 2 ≤ ∑ k, snorm v (Z k) ^ 2 := by
  classical
  have hsplit : ∑ i, snorm v (P i * Z (c i)) ^ 2
      = ∑ k, ∑ i ∈ univ.filter fun i => c i = k, snorm v (P i * Z (c i)) ^ 2 :=
    (Finset.sum_fiberwise (univ : Finset ι) c fun i => snorm v (P i * Z (c i)) ^ 2).symm
  rw [hsplit]
  refine Finset.sum_le_sum fun k _ => ?_
  have hfib : ∑ i ∈ univ.filter fun i => c i = k, snorm v (P i * Z (c i)) ^ 2
      = ∑ i ∈ univ.filter fun i => c i = k, snorm v (P i * Z k) ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [hfib, ← snorm_sq_sum_orthogonal v hP (Z k) (univ.filter fun i => c i = k)]
  refine snorm_sq_mul_le_of_contraction v ?_ (Z k)
  have hsa : (∑ i ∈ univ.filter fun i => c i = k, P i)ᴴ
      = ∑ i ∈ univ.filter fun i => c i = k, P i := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => hP.isSelfAdjoint i
  have hidem : (∑ i ∈ univ.filter fun i => c i = k, P i)
      * (∑ i ∈ univ.filter fun i => c i = k, P i)
      = ∑ i ∈ univ.filter fun i => c i = k, P i := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Matrix.mul_sum,
      Finset.sum_eq_single_of_mem i hi fun j _ hji => hP.orthogonal (Ne.symm hji), hP.idem]
  rw [hsa, hidem]
  exact proj_le_one hsa hidem

end Fibre

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The deficit of the insertion is the cross-party deviation.** Inserting one party's outcome
in front of the other party's costs `(1 - A) B`, which is `B (B - A)` because `B` is a projection
and the two parties commute --- and a projection in front costs nothing. -/
theorem snorm_one_sub_aOp_mul_bOp_le (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) {B : Matrix dB dB ℂ}
    (hBsa : Bᴴ = B) (hBidem : B * B = B) :
    snorm ψ (((1 : Matrix (dA × dB) (dA × dB) ℂ) - aOp A) * bOp B)
      ≤ snorm ψ ((aOp A : Matrix (dA × dB) (dA × dB) ℂ) - bOp B) := by
  have hrw : ((1 : Matrix (dA × dB) (dA × dB) ℂ) - aOp A) * bOp B
      = bOp B * ((bOp B : Matrix (dA × dB) (dA × dB) ℂ) - aOp A) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, ← bOp_mul, hBidem,
      ← aOp_mul_bOp]
  have hbnd : Bnd (bOp B : Matrix (dA × dB) (dA × dB) ℂ) 1 := by
    refine bnd_bOp ?_
    rw [hBsa, hBidem]
    exact proj_le_one hBsa hBidem
  rw [hrw, snorm_sub_comm ψ (aOp A) (bOp B)]
  simpa using snorm_mul_le ψ hbnd ((bOp B : Matrix (dA × dB) (dA × dB) ℂ) - aOp A)

/-- **Display `eq:qld-pulling-3`.** Inserting the other party's outcome beside each term of a
projective family, the family being indexed through the measurement's own outcomes, costs the
measurement's summed cross-consistency and nothing else. -/
theorem sum_snorm_sq_insert_le (ψ : dA × dB → ℂ)
    {P : ι → Matrix (dA × dB) (dA × dB) ℂ} (hP : IsPVM P) (c : ι → κ) (A : κ → Matrix dA dA ℂ)
    {B : κ → Matrix dB dB ℂ} (hBsa : ∀ k, (B k)ᴴ = B k) (hBidem : ∀ k, B k * B k = B k)
    {ε : ℝ} (hcons : ∑ k, xSqNorm ψ (A k) (B k) ≤ ε) :
    ∑ i, snorm ψ (P i
        * (((1 : Matrix (dA × dB) (dA × dB) ℂ) - aOp (A (c i))) * bOp (B (c i)))) ^ 2 ≤ ε := by
  refine le_trans (sum_snorm_sq_proj_comp_le ψ hP c
    fun k => ((1 : Matrix (dA × dB) (dA × dB) ℂ) - aOp (A k)) * bOp (B k)) ?_
  refine le_trans (Finset.sum_le_sum fun k (_ : k ∈ univ) => ?_) hcons
  rw [xSqNorm_eq_snorm_sq]
  have h := snorm_one_sub_aOp_mul_bOp_le ψ (A k) (hBsa k) (hBidem k)
  have h0 := snorm_nonneg ψ (((1 : Matrix (dA × dB) (dA × dB) ℂ) - aOp (A k)) * bOp (B k))
  nlinarith [h, h0]

end Insert

/-! ## The final passage: coarse-graining the self-consistency

What the chain establishes is that the whole family of exact Pauli outcomes agrees across the
parties. What `lem:qld-swap` consumes is one binary observable, read off that family by a
function of the outcome. The passage between the two is the paper's `fact:agreement`,
`fact:data-processing` and `fact:agreement` again, and for *projective* families it is free: the
summed deviation and the agreement probability determine each other exactly, and agreement can
only increase under a relabelling. Foundations has that as `sum_xSqNorm_map_le`, on bundled
POVMs; what the chain speaks is `IsPVM`, and `IsPVM.toPOVM` bridges the two. -/

section Coarse

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']

/-- **Coarse-graining a cross-party consistency costs nothing.** Two projective measurements
relabelled the same way stay as close as they were --- with no factor for the size of a fibre,
which a per-fibre triangle inequality would have cost. -/
theorem sum_xSqNorm_fibre_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {A : Λ → Matrix dA dA ℂ} {B : Λ → Matrix dB dB ℂ} (hA : IsPVM A) (hB : IsPVM B)
    (f : Λ → Λ') :
    ∑ c, xSqNorm ψ (∑ a ∈ univ.filter fun a => f a = c, A a)
        (∑ a ∈ univ.filter fun a => f a = c, B a)
      ≤ ∑ a, xSqNorm ψ (A a) (B a) := by
  have h := sum_xSqNorm_map_le hψ hA.toPOVM hB.toPOVM hA hB f
  simpa only [POVM.map_mats, IsPVM.toPOVM_mats] using h

end Coarse

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

section Helper

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- The pair space is a four-fold product whose `DecidableEq` runs past the default instance-size
bound; raised as in `MIPRE/Background/QLD/MTilde.lean`. -/
set_option synthInstance.maxSize 1000

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **The evaluated marginal's same-party product, split by polynomial outcome.** The evaluated
marginal at `a` is the sum of the polynomial-indexed outcomes over the fibre `g(u) = a`, and those
are orthogonal projectors, so the squared norms add. -/
theorem snorm_sq_evalMarg_eq_sum_polyMarg (W : Bas) (u : Point F m) (a : F) :
    snorm P.Φ (aOp ((((evalMarg P.SA W u).mats a).val)
          * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2
      = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          snorm P.Φ (aOp (((polyMarg P.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2 := by
  classical
  have hsplit : (((evalMarg P.SA W u).mats a).val)
      = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          ((polyMarg P.SA W).mats g).val := by
    rw [evalMarg_eq_map_polyMarg]
    exact POVM.map_mats _ _ _
  rw [hsplit, Finset.sum_mul, aOp_sum]
  rw [show (∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
      (aOp (((polyMarg P.SA W).mats g).val
        * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))
        : Matrix (((dA × Anc F m) × P.EA) × ((dB × Anc F m) × P.EB)) _ ℂ))
      = (∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          (aOp (((polyMarg P.SA W).mats g).val)
            : Matrix (((dA × Anc F m) × P.EA) × ((dB × Anc F m) × P.EB)) _ ℂ))
        * aOp (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)) from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun g _ => aOp_mul _ _]
  rw [snorm_sq_sum_orthogonal P.Φ (isPVM_polyMarg P.SA_proj W).aOp _ _]
  exact Finset.sum_congr rfl fun g _ => by rw [aOp_mul]

/-- **Item 2 of `lem:qld-helper`, in the chain's own indexing**: the same-party product of the
*polynomial-indexed* marginal with the complement of Alice's point measurement at that outcome's
own value. This is the form displays `eq:qld-pulling-7` and `eq:qld-pulling-11` consume. -/
theorem sum_snorm_sq_polyMarg_one_sub_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) :
    ∑ u, uniform (Point F m) u
        * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), snorm P.Φ
          (aOp (((polyMarg P.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  classical
  have h := P.sum_snorm_sq_evalMarg_one_sub_le (hm := hm) hψ hfail hprojB W
  have hu : ∀ u : Point F m,
      (∑ a : F, snorm P.Φ (aOp ((((evalMarg P.SA W u).mats a).val)
          * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2)
        = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), snorm P.Φ
          (aOp (((polyMarg P.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2 :=
    fun u => by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        P.snorm_sq_evalMarg_eq_sum_polyMarg W u a]
      rw [← Finset.sum_fiberwise (univ : Finset (LowIndDegPoly (F := F) (m := m) (d := d)))
        (fun g => g.eval u) fun g => snorm P.Φ (aOp (((polyMarg P.SA W).mats g).val
          * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g hg => by
        rw [(Finset.mem_filter.mp hg).2]
  rwa [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hu u]] at h

/-- **Display `eq:qld-pulling-14`**: the complement of the helper's agreement, read by polynomial
outcome. The sub-chain that justifies `eq:qld-pulling-10` terminates here, and the bound is the
helper's own `delta_S`: the marginal's outcomes sum to the identity, so the complementary mass is
one minus the agreement. -/
theorem sum_bornProb_polyMarg_one_sub_le (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
        bornProb P.Φ (((polyMarg P.SA W).mats g).val)
          (1 - (aOp (hatMats MB W u (g.eval u)) : Matrix ((dB × Anc F m) × P.EB) _ ℂ))
      ≤ δ := by
  classical
  have hlow := P.sum_bornProb_polyMarg_ge (MB := MB) W
  have hsplit : ∀ u : Point F m,
      (∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          bornProb P.Φ (((polyMarg P.SA W).mats g).val)
            (1 - (aOp (hatMats MB W u (g.eval u)) : Matrix ((dB × Anc F m) × P.EB) _ ℂ)))
        = 1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            bornProb P.Φ (((polyMarg P.SA W).mats g).val)
              (aOp (hatMats MB W u (g.eval u))) := by
    intro u
    rw [Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        bornProb_sub_right P.Φ (((polyMarg P.SA W).mats g).val) 1
          (aOp (hatMats MB W u (g.eval u))),
      Finset.sum_sub_distrib, ← bornProb_sum_left,
      (isPVM_polyMarg P.SA_proj W).sum_eq_one, bornProb_one_one P.Φ_unit]
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hsplit u],
    Finset.sum_congr rfl fun u (_ : u ∈ univ) =>
      show uniform (Point F m) u * (1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            bornProb P.Φ (((polyMarg P.SA W).mats g).val)
              (aOp (hatMats MB W u (g.eval u))))
          = uniform (Point F m) u - uniform (Point F m) u
              * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
                bornProb P.Φ (((polyMarg P.SA W).mats g).val)
                  (aOp (hatMats MB W u (g.eval u))) from by ring,
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
