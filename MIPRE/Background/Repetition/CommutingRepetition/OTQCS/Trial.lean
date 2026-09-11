/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/Trial.lean
-/
/-
# OTQCS: the one-trial resource (node 1.3.5)

Anchors: 06_otqcs.tex, eqs N1-Z, omega0, PQ, one-trial-probabilities,
erasers, polar-initial, common-branch.

Encoding: the trial register is indexed by `Fin (m + 1)` with the
distinguished symbol `★ = Fin.last m` and the retained bins enumerated
by `Fin.castSucc` — an abstract *band family* `B : Fin m → Set ℝ` of
pairwise disjoint measurable subsets of `(0, ∞)` with band values
`t : Fin m → ℝ` (at consumption, node 1.3.9: the bins `I_j^{θ₀} ∩
[L, H]` of the common shift with `t j` the upper endpoints, and the
band masses below rewrite to the grid functionals of OTQCS/Grid.lean).
The one-trial algebra is the matrix amplification `M_{m+1}(N')` of
WP-B3 over the modulus family's algebra; everything is an algebra
element, so left/right actions and the trial state come from the
amplified standard form.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.JointMeasure
import MIPRE.Background.Repetition.CommutingRepetition.VN.Amplify

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open MeasureTheory
open scoped BigOperators InnerProductSpace

universe u v w

/-- A band family for the trial construction: `m` pairwise disjoint
measurable subsets of `(0, ∞)` with positive band values. At
consumption these are the retained shifted bins `I_j^{θ₀} ∩ [L, H]`
and their upper endpoints `t_j` (06_otqcs.tex, eq N1-Z "the finite
retained bin set"). -/
structure IsBandFamily {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ) :
    Prop where
  meas : ∀ j, MeasurableSet (B j)
  disj : Pairwise (Function.onFun Disjoint B)
  pos : ∀ j, B j ⊆ Set.Ioi 0
  tpos : ∀ j, 0 < t j

/-- `Z = ∑_{j ∈ J} t_j²` (06_otqcs.tex, eq N1-Z). -/
noncomputable def bandZ {m : ℕ} (t : Fin m → ℝ) : ℝ := ∑ j, t j ^ 2

/-- Alice's band mass `a_s = ∑_j t_j² τ(p_j(h_s))` in finite band
form (06_otqcs.tex, eq abcGamma via eq one-trial-probabilities). -/
noncomputable def bandMassA {N : StdTracialAlgebra.{u}} {S : Type v}
    {T : Type w} {x : S → N.H} {y : T → N.H} (F : ModulusFamily N x y)
    {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ) (s : S) : ℝ :=
  ∑ j, t j ^ 2 * ((F.dataA s).μ (B j)).toReal

/-- Bob's band mass `b_t = ∑_j t_j² τ(p_j(k_t))`. -/
noncomputable def bandMassB {N : StdTracialAlgebra.{u}} {S : Type v}
    {T : Type w} {x : S → N.H} {y : T → N.H} (F : ModulusFamily N x y)
    {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ) (t' : T) : ℝ :=
  ∑ j, t j ^ 2 * ((F.dataB t').μ (B j)).toReal

/-- The joint band mass `c_{st} = ∑_j t_j² τ(p_j(h_s) p_j(k_t))`, read
through the joint spectral coupling (06_otqcs.tex, eqs abcGamma +
joint-measure). -/
noncomputable def bandCross {N : StdTracialAlgebra.{u}} {S : Type v}
    {T : Type w} {x : S → N.H} {y : T → N.H} (F : ModulusFamily N x y)
    {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ) (s : S) (t' : T) : ℝ :=
  ∑ j, t j ^ 2 * ((F.joint s t').ν (B j ×ˢ B j)).toReal

/-- Core `w`-norm computation (06_otqcs.tex, eq w-norm):
`τ(w* w) = ∑_j t_j² τ(p_j(h) p_j(k)) = c`, where
`w = ∑_j t_j p_j(h) p_j(k) v`. -/
theorem wnorm_core {N : StdTracialAlgebra.{u}} {x y : N.H}
    (dA : SpectralData N x) (dB : SpectralData N y)
    (Jd : JointSpectralData dA dB) {m : ℕ} (B : Fin m → Set ℝ)
    (t : Fin m → ℝ) (hB : IsBandFamily B t) :
    N.τ (star (∑ j, (t j : ℂ) • (dA.proj (B j) * dB.proj (B j) * dB.v)) *
        (∑ j, (t j : ℂ) • (dA.proj (B j) * dB.proj (B j) * dB.v))) =
      ((∑ j, t j ^ 2 * (Jd.ν (B j ×ˢ B j)).toReal : ℝ) : ℂ) := by
  classical
  set pA : Fin m → N.A := fun j => dA.proj (B j) with hpA
  set pB : Fin m → N.A := fun j => dB.proj (B j) with hpB
  -- projection algebra
  have hidemA : ∀ j, pA j * pA j = pA j := by
    intro j
    simp only [hpA]
    rw [dA.proj_inter (B j) (B j) (hB.meas j) (hB.meas j), Set.inter_self]
  have hidemB : ∀ j, pB j * pB j = pB j := by
    intro j
    simp only [hpB]
    rw [dB.proj_inter (B j) (B j) (hB.meas j) (hB.meas j), Set.inter_self]
  have horthA : ∀ a b : Fin m, a ≠ b → pA a * pA b = 0 := by
    intro a b hab
    simp only [hpA]
    rw [dA.proj_inter (B a) (B b) (hB.meas a) (hB.meas b),
      Set.disjoint_iff_inter_eq_empty.mp (hB.disj hab), dA.proj_empty]
  have hstarA : ∀ j, star (pA j) = pA j := by
    intro j; simp only [hpA]; exact dA.proj_star (B j)
  have hstarB : ∀ j, star (pB j) = pB j := by
    intro j; simp only [hpB]; exact dB.proj_star (B j)
  -- right support absorption for B: pB j * (v v*) = pB j
  have hrab : ∀ j, pB j * (dB.v * star dB.v) = pB j := by
    intro j
    simp only [hpB]
    have h := dB.absorb (B j) (hB.meas j) (hB.pos j)
    have hs := congrArg star h
    rw [star_mul, star_mul, star_star, dB.proj_star] at hs
    exact hs
  -- abbreviate a_j = pA j * pB j * v
  set a : Fin m → N.A := fun j => pA j * pB j * dB.v with ha
  -- star of a_j
  have hstara : ∀ j, star (a j) = star dB.v * pB j * pA j := by
    intro j
    simp only [ha]
    rw [star_mul, star_mul, hstarA j, hstarB j, mul_assoc]
  -- diagonal product: star (a j) * a j = star v * pB j * pA j * pB j * v
  have hdiag : ∀ j, star (a j) * a j = star dB.v * pB j * pA j * pB j * dB.v := by
    intro j
    rw [hstara j]
    simp only [ha]
    rw [show star dB.v * pB j * pA j * (pA j * pB j * dB.v)
        = star dB.v * pB j * (pA j * pA j) * pB j * dB.v by noncomm_ring,
      hidemA j]
  -- off-diagonal product vanishes
  have hoff : ∀ i j, i ≠ j → star (a i) * a j = 0 := by
    intro i j hij
    rw [hstara i]
    simp only [ha]
    rw [show star dB.v * pB i * pA i * (pA j * pB j * dB.v)
        = star dB.v * pB i * (pA i * pA j) * pB j * dB.v by noncomm_ring,
      horthA i j hij]
    simp
  -- τ of diagonal term reduces to τ(pA j * pB j)
  have htau : ∀ j, N.τ (star (a j) * a j) = N.τ (pA j * pB j) := by
    intro j
    rw [hdiag j]
    rw [show star dB.v * pB j * pA j * pB j * dB.v
        = star dB.v * (pB j * pA j * pB j * dB.v) by noncomm_ring]
    rw [N.τ_mul_comm (star dB.v) (pB j * pA j * pB j * dB.v)]
    rw [show pB j * pA j * pB j * dB.v * star dB.v
        = (pB j * pA j) * (pB j * (dB.v * star dB.v)) by noncomm_ring, hrab j]
    rw [N.τ_mul_comm (pB j * pA j) (pB j),
      show pB j * (pB j * pA j) = (pB j * pB j) * pA j by noncomm_ring,
      hidemB j, N.τ_mul_comm (pB j) (pA j)]
  -- expand the product of sums
  have hexpand : star (∑ j, (t j : ℂ) • a j) * (∑ j, (t j : ℂ) • a j) =
      ∑ i, ∑ j, ((t i : ℂ) * (t j : ℂ)) • (star (a i) * a j) := by
    rw [star_sum]
    have hss : ∀ i, star ((t i : ℂ) • a i) = (t i : ℂ) • star (a i) := by
      intro i
      rw [star_smul, Complex.star_def, Complex.conj_ofReal]
    rw [Finset.sum_congr rfl fun i _ => hss i]
    rw [Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  -- reduce double sum to diagonal
  have hcollapse : ∑ i, ∑ j, ((t i : ℂ) * (t j : ℂ)) • (star (a i) * a j) =
      ∑ j, ((t j : ℂ) * (t j : ℂ)) • (star (a j) * a j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [hoff i j (Ne.symm hji), smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- assemble
  rw [show (∑ j, (t j : ℂ) • (dA.proj (B j) * dB.proj (B j) * dB.v))
      = ∑ j, (t j : ℂ) • a j from rfl]
  rw [hexpand, hcollapse, map_sum]
  have hterm : ∀ j, N.τ (((t j : ℂ) * (t j : ℂ)) • (star (a j) * a j)) =
      ((t j ^ 2 * (Jd.ν (B j ×ˢ B j)).toReal : ℝ) : ℂ) := by
    intro j
    rw [map_smul, smul_eq_mul, htau j,
      Jd.cross (B j) (B j) (hB.meas j) (hB.meas j)]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Complex.ofReal_sum]

section Trial

variable (N : StdTracialAlgebra.{u}) {S : Type v} {T : Type w}
variable {x : S → N.H} {y : T → N.H}

/-- The one-trial resource matrix: `√((m+1)/Z) ∑_{j} t_j e_jj ⊗ 1`,
zero at the distinguished diagonal entry `★★` (06_otqcs.tex, eq
omega0, as an element of `M_{m+1}(N)` before the GNS embedding). -/
noncomputable def trialUnitMat (m : ℕ) (t : Fin m → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.diagonal (Fin.lastCases 0 fun j =>
    ((Real.sqrt ((m + 1) / bandZ t) * t j : ℝ) : ℂ) • (1 : N.A))

/-- The one-trial resource vector `ω₀ ∈ L²(M_{m+1}(N))`
(06_otqcs.tex, eq omega0). -/
noncomputable def trialState (m : ℕ) (t : Fin m → ℝ) :
    (StdTracialAlgebra.amplify N (m + 1)).H :=
  (StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t)

variable (F : ModulusFamily N x y) {m : ℕ} (B : Fin m → Set ℝ)
  (t : Fin m → ℝ)

/-- Alice's one-trial success projection
`P_s = ∑_j e_jj ⊗ p_j(h_s)` (06_otqcs.tex, eq PQ). -/
noncomputable def trialPA (s : S) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.diagonal (Fin.lastCases 0 fun j => (F.dataA s).proj (B j))

/-- Bob's one-trial success projection
`Q_t = ∑_j e_jj ⊗ p_j(k_t)` (06_otqcs.tex, eq PQ). -/
noncomputable def trialQB (t' : T) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.diagonal (Fin.lastCases 0 fun j => (F.dataB t').proj (B j))

/-- Alice's bin-erasing partial isometry
`V_s = ∑_j e_{★j} ⊗ p_j(h_s)` (06_otqcs.tex, eq erasers). -/
noncomputable def trialVA (s : S) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.of fun i i' =>
    if i = Fin.last m
    then Fin.lastCases 0 (fun j => (F.dataA s).proj (B j)) i' else 0

/-- Bob's bin-erasing partial isometry
`W_t = ∑_j e_{j★} ⊗ p_j(k_t)` (06_otqcs.tex, eq erasers). -/
noncomputable def trialWB (t' : T) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.of fun i i' =>
    if i' = Fin.last m
    then Fin.lastCases 0 (fun j => (F.dataB t').proj (B j)) i else 0

/-- The polar corrector `v̄_t = e_{★★} ⊗ v_t` (06_otqcs.tex, above eq
polar-initial). -/
noncomputable def trialVbar (t' : T) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.single (Fin.last m) (Fin.last m) (F.dataB t').v

/-- The erased, polar-corrected common branch
`ζ_{st} = V_s ω₀ W_t v̄_t` — Alice's eraser on the left, Bob's on the
right (06_otqcs.tex, eq common-branch). -/
noncomputable def trialZeta (s : S) (t' : T) :
    (StdTracialAlgebra.amplify N (m + 1)).H :=
  (StdTracialAlgebra.amplify N (m + 1)).L (trialVA N F B s)
    ((StdTracialAlgebra.amplify N (m + 1)).Rop
      (trialWB N F B t' * trialVbar N F t') (trialState N m t))

/-- The one-trial resource is a unit vector (06_otqcs.tex, below eq
omega0). -/
theorem trialState_norm (m : ℕ) (t : Fin m → ℝ) (hZ : 0 < bandZ t) :
    ‖trialState N m t‖ = 1 := by
  classical
  set c : Fin m → ℝ := fun j => Real.sqrt ((m + 1) / bandZ t) * t j with hc
  set d : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => ((c j : ℝ) : ℂ) • (1 : N.A)) with hd
  -- the amplified inner product of the resource with itself
  have hinner : ⟪trialState N m t, trialState N m t⟫_ℂ = 1 := by
    have hii := (StdTracialAlgebra.amplify N (m + 1)).ι_inner
      (trialUnitMat N m t) (trialUnitMat N m t)
    rw [trialState, hii]
    show StdTracialAlgebra.ampτ N (m + 1)
      (star (trialUnitMat N m t) * trialUnitMat N m t) = 1
    have hU : star (trialUnitMat N m t) * trialUnitMat N m t =
        Matrix.diagonal (fun i => star (d i) * d i) := by
      rw [trialUnitMat, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      rfl
    rw [hU, StdTracialAlgebra.ampτ_apply]
    -- compute the diagonal traces
    have hterm : ∀ j : Fin m,
        N.τ ((Matrix.diagonal (fun i => star (d i) * d i))
          (Fin.castSucc j) (Fin.castSucc j)) = ((c j ^ 2 : ℝ) : ℂ) := by
      intro j
      simp only [Matrix.diagonal_apply_eq, hd, Fin.lastCases_castSucc]
      rw [star_smul, star_one, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, mul_one, smul_smul, Complex.star_def,
        Complex.conj_ofReal, ← Complex.ofReal_mul, map_smul, N.τ_one,
        smul_eq_mul, mul_one, ← pow_two]
    have hlast :
        N.τ ((Matrix.diagonal (fun i => star (d i) * d i))
          (Fin.last m) (Fin.last m)) = 0 := by
      simp only [Matrix.diagonal_apply_eq, hd, Fin.lastCases_last,
        star_zero, zero_mul, map_zero]
    rw [Fin.sum_univ_castSucc,
      Finset.sum_congr rfl (fun j _ => hterm j), hlast, add_zero]
    -- ∑ c_j² = (m+1)/Z · Z = m+1
    have hcsq : ∑ j, ((c j ^ 2 : ℝ) : ℂ) = ((m : ℂ) + 1) := by
      rw [← Complex.ofReal_sum]
      have : ∑ j, c j ^ 2 = (m + 1 : ℝ) := by
        have hcexp : ∀ j, c j ^ 2 = (m + 1) / bandZ t * t j ^ 2 := by
          intro j
          rw [hc]
          rw [mul_pow, Real.sq_sqrt (by positivity)]
        rw [Finset.sum_congr rfl (fun j _ => hcexp j), ← Finset.mul_sum,
          ← bandZ, div_mul_cancel₀]
        exact ne_of_gt hZ
      rw [this]
      push_cast
      ring
    rw [hcsq]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  -- conclude the norm
  have hnn : (0 : ℝ) ≤ ‖trialState N m t‖ := norm_nonneg _
  have hsq : ‖trialState N m t‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (trialState N m t), hinner]
    simp
  nlinarith [hsq, hnn]

/-- Alice's one-trial success probability is `a_s / Z` (06_otqcs.tex,
eq one-trial-probabilities, first entry). -/
theorem trial_success_A (hB : IsBandFamily B t) (s : S) :
    ⟪trialState N m t,
        (StdTracialAlgebra.amplify N (m + 1)).L (trialPA N F B s)
          (trialState N m t)⟫_ℂ =
      ((bandMassA F B t s / bandZ t : ℝ) : ℂ) := by
  classical
  set D := F.dataA s with hDdef
  have hbz : 0 ≤ bandZ t := by rw [bandZ]; positivity
  set c : Fin m → ℝ := fun j => Real.sqrt ((m + 1) / bandZ t) * t j with hc
  set d : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => ((c j : ℝ) : ℂ) • (1 : N.A)) with hd
  set p : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => D.proj (B j)) with hp
  -- L(P)ω₀ = ι(P U); pair against ω₀ = ι U
  rw [trialState]
  rw [show (StdTracialAlgebra.amplify N (m + 1)).L (trialPA N F B s)
        ((StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t)) =
      (StdTracialAlgebra.amplify N (m + 1)).ι
        (trialPA N F B s * trialUnitMat N m t) from
    (StdTracialAlgebra.amplify N (m + 1)).L_apply _ _]
  rw [(StdTracialAlgebra.amplify N (m + 1)).ι_inner
    (trialUnitMat N m t) (trialPA N F B s * trialUnitMat N m t)]
  show StdTracialAlgebra.ampτ N (m + 1)
    (star (trialUnitMat N m t) *
      (trialPA N F B s * trialUnitMat N m t)) = _
  have hU : star (trialUnitMat N m t) *
      (trialPA N F B s * trialUnitMat N m t) =
      Matrix.diagonal (fun i => star (d i) * (p i * d i)) := by
    rw [trialUnitMat, trialPA, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    rfl
  rw [hU, StdTracialAlgebra.ampτ_apply]
  have hterm : ∀ j : Fin m,
      N.τ ((Matrix.diagonal (fun i => star (d i) * (p i * d i)))
        (Fin.castSucc j) (Fin.castSucc j)) =
        ((c j ^ 2 * (D.μ (B j)).toReal : ℝ) : ℂ) := by
    intro j
    simp only [Matrix.diagonal_apply_eq, hd, hp, Fin.lastCases_castSucc]
    rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, one_mul,
      mul_one, smul_smul, map_smul, smul_eq_mul,
      D.proj_trace (B j) (hB.meas j), ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← pow_two]
  have hlast :
      N.τ ((Matrix.diagonal (fun i => star (d i) * (p i * d i)))
        (Fin.last m) (Fin.last m)) = 0 := by
    simp only [Matrix.diagonal_apply_eq, hd, hp, Fin.lastCases_last,
      star_zero, zero_mul, map_zero]
  rw [Fin.sum_univ_castSucc,
    Finset.sum_congr rfl (fun j _ => hterm j), hlast, add_zero]
  rw [← Complex.ofReal_sum]
  have hreal : ∑ j, c j ^ 2 * (D.μ (B j)).toReal =
      (m + 1) / bandZ t * bandMassA F B t s := by
    have hcexp : ∀ j, c j ^ 2 * (D.μ (B j)).toReal =
        (m + 1) / bandZ t * (t j ^ 2 * (D.μ (B j)).toReal) := by
      intro j
      rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hcexp j), ← Finset.mul_sum]
    rfl
  rw [hreal]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hfin : ((m : ℝ) + 1)⁻¹ * ((m + 1) / bandZ t * bandMassA F B t s) =
      bandMassA F B t s / bandZ t := by
    rw [div_mul_eq_mul_div, mul_div_assoc, ← mul_assoc,
      inv_mul_cancel₀ hm1, one_mul]
  have hcast : (↑(m + 1) : ℂ) = (((m : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, hfin]

/-- Bob's one-trial success probability is `b_t / Z` (06_otqcs.tex, eq
one-trial-probabilities, second entry). -/
theorem trial_success_B (hB : IsBandFamily B t) (t' : T) :
    ⟪trialState N m t,
        (StdTracialAlgebra.amplify N (m + 1)).Rop (trialQB N F B t')
          (trialState N m t)⟫_ℂ =
      ((bandMassB F B t t' / bandZ t : ℝ) : ℂ) := by
  classical
  set D := F.dataB t' with hDdef
  have hbz : 0 ≤ bandZ t := by rw [bandZ]; positivity
  set c : Fin m → ℝ := fun j => Real.sqrt ((m + 1) / bandZ t) * t j with hc
  set d : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => ((c j : ℝ) : ℂ) • (1 : N.A)) with hd
  set q : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => D.proj (B j)) with hq
  -- Rop(Q)ω₀ = ι(U Q); pair against ω₀ = ι U
  rw [trialState]
  have hRop : (StdTracialAlgebra.amplify N (m + 1)).Rop (trialQB N F B t')
      ((StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t)) =
      (StdTracialAlgebra.amplify N (m + 1)).ι
        (trialUnitMat N m t * trialQB N F B t') :=
    (StdTracialAlgebra.amplify N (m + 1)).R_apply
      (trialQB N F B t') (trialUnitMat N m t)
  rw [hRop,
    (StdTracialAlgebra.amplify N (m + 1)).ι_inner
      (trialUnitMat N m t) (trialUnitMat N m t * trialQB N F B t')]
  show StdTracialAlgebra.ampτ N (m + 1)
    (star (trialUnitMat N m t) *
      (trialUnitMat N m t * trialQB N F B t')) = _
  have hU : star (trialUnitMat N m t) *
      (trialUnitMat N m t * trialQB N F B t') =
      Matrix.diagonal (fun i => star (d i) * (d i * q i)) := by
    rw [trialUnitMat, trialQB, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    rfl
  rw [hU, StdTracialAlgebra.ampτ_apply]
  have hterm : ∀ j : Fin m,
      N.τ ((Matrix.diagonal (fun i => star (d i) * (d i * q i)))
        (Fin.castSucc j) (Fin.castSucc j)) =
        ((c j ^ 2 * (D.μ (B j)).toReal : ℝ) : ℂ) := by
    intro j
    simp only [Matrix.diagonal_apply_eq, hd, hq, Fin.lastCases_castSucc]
    rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal,
      Algebra.smul_mul_assoc, one_mul, Algebra.smul_mul_assoc, one_mul,
      smul_smul, map_smul, smul_eq_mul,
      D.proj_trace (B j) (hB.meas j), ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← pow_two]
  have hlast :
      N.τ ((Matrix.diagonal (fun i => star (d i) * (d i * q i)))
        (Fin.last m) (Fin.last m)) = 0 := by
    simp only [Matrix.diagonal_apply_eq, hd, hq, Fin.lastCases_last,
      star_zero, zero_mul, map_zero]
  rw [Fin.sum_univ_castSucc,
    Finset.sum_congr rfl (fun j _ => hterm j), hlast, add_zero]
  rw [← Complex.ofReal_sum]
  have hreal : ∑ j, c j ^ 2 * (D.μ (B j)).toReal =
      (m + 1) / bandZ t * bandMassB F B t t' := by
    have hcexp : ∀ j, c j ^ 2 * (D.μ (B j)).toReal =
        (m + 1) / bandZ t * (t j ^ 2 * (D.μ (B j)).toReal) := by
      intro j
      rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hcexp j), ← Finset.mul_sum]
    rfl
  rw [hreal]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hfin : ((m : ℝ) + 1)⁻¹ * ((m + 1) / bandZ t * bandMassB F B t t') =
      bandMassB F B t t' / bandZ t := by
    rw [div_mul_eq_mul_div, mul_div_assoc, ← mul_assoc,
      inv_mul_cancel₀ hm1, one_mul]
  have hcast : (↑(m + 1) : ℂ) = (((m : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, hfin]

/-- The joint one-trial success probability is `c_{st} / Z`
(06_otqcs.tex, eq one-trial-probabilities, third entry). -/
theorem trial_success_joint (hB : IsBandFamily B t) (s : S) (t' : T) :
    ⟪trialState N m t,
        (StdTracialAlgebra.amplify N (m + 1)).L (trialPA N F B s)
          ((StdTracialAlgebra.amplify N (m + 1)).Rop (trialQB N F B t')
            (trialState N m t))⟫_ℂ =
      ((bandCross F B t s t' / bandZ t : ℝ) : ℂ) := by
  classical
  set DA := F.dataA s with hDAdef
  set DB := F.dataB t' with hDBdef
  set J := F.joint s t' with hJdef
  have hbz : 0 ≤ bandZ t := by rw [bandZ]; positivity
  set c : Fin m → ℝ := fun j => Real.sqrt ((m + 1) / bandZ t) * t j with hc
  set d : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => ((c j : ℝ) : ℂ) • (1 : N.A)) with hd
  set p : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => DA.proj (B j)) with hp
  set q : Fin (m + 1) → N.A :=
    Fin.lastCases (0 : N.A) (fun j => DB.proj (B j)) with hq
  rw [trialState]
  have hRop : (StdTracialAlgebra.amplify N (m + 1)).Rop (trialQB N F B t')
      ((StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t)) =
      (StdTracialAlgebra.amplify N (m + 1)).ι
        (trialUnitMat N m t * trialQB N F B t') :=
    (StdTracialAlgebra.amplify N (m + 1)).R_apply
      (trialQB N F B t') (trialUnitMat N m t)
  rw [hRop, show (StdTracialAlgebra.amplify N (m + 1)).L (trialPA N F B s)
        ((StdTracialAlgebra.amplify N (m + 1)).ι
          (trialUnitMat N m t * trialQB N F B t')) =
      (StdTracialAlgebra.amplify N (m + 1)).ι
        (trialPA N F B s * (trialUnitMat N m t * trialQB N F B t')) from
    (StdTracialAlgebra.amplify N (m + 1)).L_apply _ _]
  rw [(StdTracialAlgebra.amplify N (m + 1)).ι_inner
    (trialUnitMat N m t)
    (trialPA N F B s * (trialUnitMat N m t * trialQB N F B t'))]
  show StdTracialAlgebra.ampτ N (m + 1)
    (star (trialUnitMat N m t) *
      (trialPA N F B s *
        (trialUnitMat N m t * trialQB N F B t'))) = _
  have hU : star (trialUnitMat N m t) *
      (trialPA N F B s * (trialUnitMat N m t * trialQB N F B t')) =
      Matrix.diagonal (fun i => star (d i) * (p i * (d i * q i))) := by
    rw [trialUnitMat, trialPA, trialQB, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rfl
  rw [hU, StdTracialAlgebra.ampτ_apply]
  have hterm : ∀ j : Fin m,
      N.τ ((Matrix.diagonal (fun i => star (d i) * (p i * (d i * q i))))
        (Fin.castSucc j) (Fin.castSucc j)) =
        ((c j ^ 2 * (J.ν (B j ×ˢ B j)).toReal : ℝ) : ℂ) := by
    intro j
    simp only [Matrix.diagonal_apply_eq, hd, hp, hq,
      Fin.lastCases_castSucc]
    rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal,
      Algebra.smul_mul_assoc, one_mul, Algebra.smul_mul_assoc, one_mul,
      Algebra.mul_smul_comm, smul_smul, map_smul, smul_eq_mul,
      J.cross (B j) (B j) (hB.meas j) (hB.meas j), ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, ← pow_two]
  have hlast :
      N.τ ((Matrix.diagonal (fun i => star (d i) * (p i * (d i * q i))))
        (Fin.last m) (Fin.last m)) = 0 := by
    simp only [Matrix.diagonal_apply_eq, hd, hp, hq, Fin.lastCases_last,
      star_zero, zero_mul, map_zero]
  rw [Fin.sum_univ_castSucc,
    Finset.sum_congr rfl (fun j _ => hterm j), hlast, add_zero]
  rw [← Complex.ofReal_sum]
  have hreal : ∑ j, c j ^ 2 * (J.ν (B j ×ˢ B j)).toReal =
      (m + 1) / bandZ t * bandCross F B t s t' := by
    have hcexp : ∀ j, c j ^ 2 * (J.ν (B j ×ˢ B j)).toReal =
        (m + 1) / bandZ t * (t j ^ 2 * (J.ν (B j ×ˢ B j)).toReal) := by
      intro j
      rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hcexp j), ← Finset.mul_sum]
    rfl
  rw [hreal]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hfin : ((m : ℝ) + 1)⁻¹ *
      ((m + 1) / bandZ t * bandCross F B t s t') =
      bandCross F B t s t' / bandZ t := by
    rw [div_mul_eq_mul_div, mul_div_assoc, ← mul_assoc,
      inv_mul_cancel₀ hm1, one_mul]
  have hcast : (↑(m + 1) : ℂ) = (((m : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, hfin]

/-- `V_s* V_s = P_s` (06_otqcs.tex, below eq erasers). -/
theorem trialVA_star_mul (hB : IsBandFamily B t) (s : S) :
    star (trialVA N F B s) * trialVA N F B s = trialPA N F B s := by
  classical
  set D := F.dataA s with hDdef
  -- projection algebra of the band spectral projections
  have hidem : ∀ j, D.proj (B j) * D.proj (B j) = D.proj (B j) := by
    intro j
    rw [D.proj_inter (B j) (B j) (hB.meas j) (hB.meas j), Set.inter_self]
  have horth : ∀ a b : Fin m, a ≠ b →
      D.proj (B a) * D.proj (B b) = 0 := by
    intro a b hab
    rw [D.proj_inter (B a) (B b) (hB.meas a) (hB.meas b),
      Set.disjoint_iff_inter_eq_empty.mp (hB.disj hab), D.proj_empty]
  ext i k
  rw [Matrix.mul_apply]
  have hsum : (∑ l, (star (trialVA N F B s)) i l * trialVA N F B s l k) =
      star (Fin.lastCases (0 : N.A) (fun j => D.proj (B j)) i) *
        Fin.lastCases (0 : N.A) (fun j => D.proj (B j)) k := by
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp only [Matrix.star_apply, trialVA, Matrix.of_apply, if_true,
        ← hDdef]
    · intro l _ hl
      simp only [trialVA, Matrix.of_apply, if_neg hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, trialPA, Matrix.diagonal_apply, ← hDdef]
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.lastCases_last]
    simp
  | cast a =>
    rw [Fin.lastCases_castSucc]
    rw [D.proj_star]
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.lastCases_last, mul_zero]
      rw [if_neg (by exact (Fin.castSucc_lt_last a).ne)]
    | cast b =>
      rw [Fin.lastCases_castSucc]
      by_cases hab : a = b
      · subst hab
        rw [hidem a, if_pos rfl]
      · rw [horth a b hab, if_neg (by simpa using hab)]

/-- `W_t W_t* = Q_t` (06_otqcs.tex, below eq erasers). -/
theorem trialWB_mul_star (hB : IsBandFamily B t) (t' : T) :
    trialWB N F B t' * star (trialWB N F B t') = trialQB N F B t' := by
  classical
  set D := F.dataB t' with hDdef
  have hidem : ∀ j, D.proj (B j) * D.proj (B j) = D.proj (B j) := by
    intro j
    rw [D.proj_inter (B j) (B j) (hB.meas j) (hB.meas j), Set.inter_self]
  have horth : ∀ a b : Fin m, a ≠ b →
      D.proj (B a) * D.proj (B b) = 0 := by
    intro a b hab
    rw [D.proj_inter (B a) (B b) (hB.meas a) (hB.meas b),
      Set.disjoint_iff_inter_eq_empty.mp (hB.disj hab), D.proj_empty]
  ext i k
  rw [Matrix.mul_apply]
  have hsum : (∑ l, trialWB N F B t' i l * (star (trialWB N F B t')) l k) =
      Fin.lastCases (0 : N.A) (fun j => D.proj (B j)) i *
        star (Fin.lastCases (0 : N.A) (fun j => D.proj (B j)) k) := by
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp only [Matrix.star_apply, trialWB, Matrix.of_apply, if_true,
        ← hDdef]
    · intro l _ hl
      simp only [trialWB, Matrix.of_apply, if_neg hl, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, trialQB, Matrix.diagonal_apply, ← hDdef]
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.lastCases_last]
    simp
  | cast a =>
    rw [Fin.lastCases_castSucc]
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.lastCases_last, star_zero, mul_zero,
        if_neg (by exact (Fin.castSucc_lt_last a).ne)]
    | cast b =>
      rw [Fin.lastCases_castSucc, D.proj_star]
      by_cases hab : a = b
      · subst hab
        rw [hidem a, if_pos rfl]
      · rw [horth a b hab, if_neg (by simpa using hab)]

/-- `W_t v̄_t v̄_t* W_t* = Q_t`: every retained spectral projection of
`k_t` lies below the left support `v_t v_t*` (06_otqcs.tex, eq
polar-initial). -/
theorem trialWB_vbar_initial (hB : IsBandFamily B t) (t' : T) :
    trialWB N F B t' * trialVbar N F t' * star (trialVbar N F t') *
        star (trialWB N F B t') = trialQB N F B t' := by
  classical
  set D := F.dataB t' with hDdef
  -- right-support absorption: `p_j(k_t) · (v v*) = p_j(k_t)`
  have hrab : ∀ j : Fin m, D.proj (B j) * (D.v * star D.v) = D.proj (B j) := by
    intro j
    have h := D.absorb (B j) (hB.meas j) (hB.pos j)
    have hs := congrArg star h
    rw [star_mul, star_mul, star_star, D.proj_star] at hs
    exact hs
  -- `v̄* = e_{★★} ⊗ v*`
  have hstarV : star (trialVbar N F t') =
      Matrix.single (Fin.last m) (Fin.last m) (star D.v) := by
    rw [trialVbar, Matrix.star_eq_conjTranspose]
    ext p q
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply, ← hDdef]
    by_cases h : Fin.last m = q ∧ Fin.last m = p
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩), star_zero]
  -- `v̄ v̄* = e_{★★} ⊗ (v v*)`
  have hM : trialVbar N F t' * star (trialVbar N F t') =
      Matrix.single (Fin.last m) (Fin.last m) (D.v * star D.v) := by
    rw [hstarV, trialVbar, ← hDdef, Matrix.single_mul_single_same]
  -- `W_t · (e_{★★} ⊗ v v*) = W_t`, because each retained `p_j(k_t) ≤ v v*`
  have hWM : trialWB N F B t' *
      Matrix.single (Fin.last m) (Fin.last m) (D.v * star D.v) =
      trialWB N F B t' := by
    ext i k
    by_cases hk : k = Fin.last m
    · subst hk
      rw [Matrix.mul_single_apply_same]
      have hWlast : (trialWB N F B t') i (Fin.last m) =
          Fin.lastCases (0 : N.A) (fun j => D.proj (B j)) i := by
        simp only [trialWB, Matrix.of_apply, ← hDdef, if_true]
      rw [hWlast]
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last, zero_mul]
      | cast j => rw [Fin.lastCases_castSucc]; exact hrab j
    · have hrhs : trialWB N F B t' i k = 0 := by
        simp only [trialWB, Matrix.of_apply, if_neg hk]
      rw [hrhs, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [Matrix.single_apply, if_neg (fun h => hk h.2.symm), mul_zero]
  calc trialWB N F B t' * trialVbar N F t' * star (trialVbar N F t') *
        star (trialWB N F B t')
      = trialWB N F B t' * (trialVbar N F t' * star (trialVbar N F t')) *
          star (trialWB N F B t') := by
        rw [mul_assoc (trialWB N F B t') (trialVbar N F t')
          (star (trialVbar N F t'))]
    _ = trialWB N F B t' *
          Matrix.single (Fin.last m) (Fin.last m) (D.v * star D.v) *
          star (trialWB N F B t') := by rw [hM]
    _ = trialWB N F B t' * star (trialWB N F B t') := by rw [hWM]
    _ = trialQB N F B t' := trialWB_mul_star N F B t hB t'

/-- The erased, polar-corrected common branch as a matrix (eq common-branch before the
GNS map): `V_s ω₀ (W_t v̄_t) = e_{★★} ⊗ √((m+1)/Z) w_{st}`. -/
theorem trialVA_mul_state_mul_WVbar (s : S) (t' : T) :
    (trialVA N F B s * (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t')) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) =
      Matrix.single (Fin.last m) (Fin.last m)
        (((Real.sqrt ((m + 1) / bandZ t) : ℝ) : ℂ) •
          ∑ j, (t j : ℂ) •
            ((F.dataA s).proj (B j) * (F.dataB t').proj (B j) * (F.dataB t').v)) := by
  classical
  set DA := F.dataA s with hDAdef
  set DB := F.dataB t' with hDBdef
  -- entrywise: `W_t v̄_t` has column `★` equal to `p_j(k_t) v_t`
  have hWV : ∀ l k : Fin (m + 1),
      (trialWB N F B t' * trialVbar N F t' :
        Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) l k =
      if k = Fin.last m then
        Fin.lastCases (0 : N.A) (fun j => DB.proj (B j)) l * DB.v else 0 := by
    intro l k
    rw [trialVbar, ← hDBdef]
    by_cases hk : k = Fin.last m
    · subst hk
      rw [Matrix.mul_single_apply_same, if_pos rfl]
      congr 1
      simp only [trialWB, Matrix.of_apply, ← hDBdef, if_true]
    · rw [if_neg hk, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro p _
      rw [Matrix.single_apply, if_neg (fun h => hk h.2.symm), mul_zero]
  -- fold the diagonal `U` into the column
  have hM2 : ∀ l k : Fin (m + 1), (trialUnitMat N m t *
      (trialWB N F B t' * trialVbar N F t') :
        Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) l k =
      if k = Fin.last m then
        (Fin.lastCases (0 : N.A)
          (fun j => ((Real.sqrt ((m + 1) / bandZ t) * t j : ℝ) : ℂ) •
            (1 : N.A)) l) *
          (Fin.lastCases (0 : N.A) (fun j => DB.proj (B j)) l * DB.v)
      else 0 := by
    intro l k
    rw [Matrix.mul_apply, Finset.sum_eq_single l]
    · rw [hWV l k, trialUnitMat, Matrix.diagonal_apply_eq, mul_ite, mul_zero]
    · intro p _ hp
      rw [trialUnitMat, Matrix.diagonal_apply_ne _ (Ne.symm hp), zero_mul]
    · intro h; exact absurd (Finset.mem_univ l) h
  -- the surviving summand on the `★` row
  have hsummand : ∀ l : Fin (m + 1), (trialVA N F B s) (Fin.last m) l *
      (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t') :
        Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) l (Fin.last m) =
      (Fin.lastCases (0 : N.A) (fun j => DA.proj (B j)) l) *
        ((Fin.lastCases (0 : N.A)
          (fun j => ((Real.sqrt ((m + 1) / bandZ t) * t j : ℝ) : ℂ) •
            (1 : N.A)) l) *
          (Fin.lastCases (0 : N.A) (fun j => DB.proj (B j)) l * DB.v)) := by
    intro l
    rw [hM2 l (Fin.last m), if_pos rfl]
    congr 1
    simp only [trialVA, Matrix.of_apply, ← hDAdef, if_true]
  -- scalar/associativity normalization of each retained term
  have hterm : ∀ j : Fin m,
      (Fin.lastCases (0 : N.A) (fun j => DA.proj (B j)) (Fin.castSucc j)) *
        ((Fin.lastCases (0 : N.A)
          (fun j => ((Real.sqrt ((m + 1) / bandZ t) * t j : ℝ) : ℂ) •
            (1 : N.A)) (Fin.castSucc j)) *
          (Fin.lastCases (0 : N.A) (fun j => DB.proj (B j)) (Fin.castSucc j)
            * DB.v)) =
      ((Real.sqrt ((m + 1) / bandZ t) : ℝ) : ℂ) •
        ((t j : ℂ) • (DA.proj (B j) * DB.proj (B j) * DB.v)) := by
    intro j
    simp only [Fin.lastCases_castSucc]
    rw [Algebra.smul_mul_assoc, one_mul, Algebra.mul_smul_comm,
      Complex.ofReal_mul, mul_smul, ← mul_assoc]
  ext i k
  rw [Matrix.mul_apply]
  by_cases hi : i = Fin.last m
  · subst hi
    by_cases hk : k = Fin.last m
    · subst hk
      rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
      rw [Finset.sum_congr rfl (fun l _ => hsummand l),
        Fin.sum_univ_castSucc, Fin.lastCases_last, zero_mul, add_zero,
        Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.smul_sum]
    · rw [Matrix.single_apply, if_neg (fun h => hk h.2.symm)]
      apply Finset.sum_eq_zero
      intro l _
      rw [hM2 l k, if_neg hk, mul_zero]
  · rw [Matrix.single_apply, if_neg (fun h => hi h.1.symm)]
    apply Finset.sum_eq_zero
    intro l _
    have hva : (trialVA N F B s) i l = 0 := by
      simp only [trialVA, Matrix.of_apply, if_neg hi]
    rw [hva, zero_mul]

/-- The common branch in closed form:
`ζ_{st} = √((m+1)/Z) · ι(e_{★★} ⊗ ∑_j t_j p_j(h_s) p_j(k_t) v_t)`
(06_otqcs.tex, eq common-branch, second line). -/
theorem trialZeta_eq (hB : IsBandFamily B t) (s : S) (t' : T) :
    trialZeta N F B t s t' =
      (StdTracialAlgebra.amplify N (m + 1)).ι
        (Matrix.single (Fin.last m) (Fin.last m)
          (((Real.sqrt ((m + 1) / bandZ t) : ℝ) : ℂ) •
            ∑ j, (t j : ℂ) •
              ((F.dataA s).proj (B j) * (F.dataB t').proj (B j) *
                (F.dataB t').v))) := by
  classical
  -- ζ = ι(V_s · U · W_t v̄_t) via the amplified left/right actions
  rw [trialZeta, trialState]
  have hRop : (StdTracialAlgebra.amplify N (m + 1)).Rop
      (trialWB N F B t' * trialVbar N F t')
      ((StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t)) =
      (StdTracialAlgebra.amplify N (m + 1)).ι
        (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t')) :=
    (StdTracialAlgebra.amplify N (m + 1)).R_apply
      (trialWB N F B t' * trialVbar N F t') (trialUnitMat N m t)
  rw [hRop]
  have hL : (StdTracialAlgebra.amplify N (m + 1)).L (trialVA N F B s)
      ((StdTracialAlgebra.amplify N (m + 1)).ι
        (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t'))) =
      (StdTracialAlgebra.amplify N (m + 1)).ι
        (trialVA N F B s *
          (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t'))) :=
    (StdTracialAlgebra.amplify N (m + 1)).L_apply (trialVA N F B s)
      (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t'))
  rw [hL]
  congr 1
  exact trialVA_mul_state_mul_WVbar N F B t s t'

/-- `‖ζ_{st}‖² = c_{st} / Z` (06_otqcs.tex, below eq common-branch). -/
theorem trialZeta_normSq (hB : IsBandFamily B t) (s : S) (t' : T) :
    ‖trialZeta N F B t s t'‖ ^ 2 = bandCross F B t s t' / bandZ t := by
  classical
  rw [trialZeta_eq N F B t hB s t']
  set dA := F.dataA s with hdA
  set dB := F.dataB t' with hdB
  set sc : ℂ := ((Real.sqrt (((m : ℝ) + 1) / bandZ t) : ℝ) : ℂ) with hsc
  set w : N.A := ∑ j, (t j : ℂ) • (dA.proj (B j) * dB.proj (B j) * dB.v) with hw
  set X : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
    Matrix.single (Fin.last m) (Fin.last m) (sc • w) with hX
  set c : ℝ := ∑ j, t j ^ 2 * ((F.joint s t').ν (B j ×ˢ B j)).toReal with hc
  have hbz : (0 : ℝ) ≤ bandZ t := by unfold bandZ; positivity
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hsc_star : star sc = sc := by
    rw [hsc, Complex.star_def, Complex.conj_ofReal]
  have hscsq : sc * sc = (((((m : ℝ) + 1) / bandZ t) : ℝ) : ℂ) := by
    rw [hsc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (div_nonneg (by positivity) hbz)]
  -- the amplified inner product equals c/Z
  have hip : ⟪(StdTracialAlgebra.amplify N (m + 1)).ι X,
        (StdTracialAlgebra.amplify N (m + 1)).ι X⟫_ℂ
      = ((c / bandZ t : ℝ) : ℂ) := by
    rw [(StdTracialAlgebra.amplify N (m + 1)).ι_inner X X]
    show StdTracialAlgebra.ampτ N (m + 1) (star X * X) = ((c / bandZ t : ℝ) : ℂ)
    -- star X * X = single ★★ ((sc*sc) • (star w * w))
    have hstarX : star X * X =
        Matrix.single (Fin.last m) (Fin.last m) ((sc * sc) • (star w * w)) := by
      have hstarX0 : star X =
          Matrix.single (Fin.last m) (Fin.last m) (star (sc • w)) := by
        rw [hX, Matrix.star_eq_conjTranspose]
        ext p q
        simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
        by_cases h : (Fin.last m = q ∧ Fin.last m = p)
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
        · rw [if_neg h, if_neg (fun hc' => h ⟨hc'.2, hc'.1⟩), star_zero]
      rw [hstarX0, hX, Matrix.single_mul_single_same]
      congr 1
      rw [star_smul, hsc_star, smul_mul_smul_comm]
    rw [hstarX, StdTracialAlgebra.ampτ_apply]
    -- diagonal sum picks out ★
    have hsum : (∑ i : Fin (m + 1),
        N.τ ((Matrix.single (Fin.last m) (Fin.last m)
          ((sc * sc) • (star w * w)) : Matrix _ _ N.A) i i))
        = N.τ ((sc * sc) • (star w * w)) := by
      rw [Finset.sum_eq_single (Fin.last m)]
      · rw [Matrix.single_apply_same]
      · intro i _ hi
        rw [Matrix.single_apply, if_neg (by rintro ⟨h1, _⟩; exact hi h1.symm),
          map_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, map_smul, smul_eq_mul,
      show N.τ (star w * w) = ((c : ℝ) : ℂ) from
        wnorm_core dA dB (F.joint s t') B t hB, hscsq]
    -- (↑(m+1))⁻¹ * ((((m+1)/Z:ℝ):ℂ) * (c:ℂ)) = ((c/Z:ℝ):ℂ)
    rw [(by push_cast; ring : (↑(m + 1) : ℂ) = (((m : ℝ) + 1 : ℝ) : ℂ)),
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [div_eq_mul_inv ((m : ℝ) + 1) (bandZ t),
      show ((m : ℝ) + 1)⁻¹ * (((m : ℝ) + 1) * (bandZ t)⁻¹ * c)
        = (((m : ℝ) + 1)⁻¹ * ((m : ℝ) + 1)) * ((bandZ t)⁻¹ * c) by ring,
      inv_mul_cancel₀ hm1, one_mul, mul_comm, ← div_eq_mul_inv]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hip, RCLike.re_to_complex,
    Complex.ofReal_re, hc, bandCross]

/-! ### One-trial traces and the corner trace (proof-side helpers for OTQCS/Compile) -/

/-- `τ₁(ω₀* ω₀) = 1` (the unit-norm resource, in trace form). -/
theorem trialUnitMat_trace_one (hZ : 0 < bandZ t) :
    (StdTracialAlgebra.amplify N (m + 1)).τ
      (star (trialUnitMat N m t) * trialUnitMat N m t) = 1 := by
  have hω := trialState_norm N m t hZ
  rw [trialState] at hω
  have hi := (StdTracialAlgebra.amplify N (m + 1)).ι_inner (trialUnitMat N m t)
    (trialUnitMat N m t)
  rw [inner_self_eq_norm_sq_to_K, hω] at hi
  have hi' : (StdTracialAlgebra.amplify N (m + 1)).τ
      (star (trialUnitMat N m t) * trialUnitMat N m t) = ((1 : ℝ) : ℂ) ^ 2 := hi.symm
  rw [hi']
  norm_num

/-- `τ₁(ω₀* P_s ω₀) = a_s/Z` (eq one-trial-probabilities, trace form). -/
theorem trialUnitMat_trace_PA (hB : IsBandFamily B t) (s : S) :
    (StdTracialAlgebra.amplify N (m + 1)).τ
        (star (trialUnitMat N m t) * (trialPA N F B s * trialUnitMat N m t))
      = ((bandMassA F B t s / bandZ t : ℝ) : ℂ) := by
  have h := trial_success_A N F B t hB s
  have hL : (StdTracialAlgebra.amplify N (m + 1)).L (trialPA N F B s)
      ((StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t))
      = (StdTracialAlgebra.amplify N (m + 1)).ι (trialPA N F B s * trialUnitMat N m t) :=
    (StdTracialAlgebra.amplify N (m + 1)).L_apply _ _
  have hi := (StdTracialAlgebra.amplify N (m + 1)).ι_inner (trialUnitMat N m t)
    (trialPA N F B s * trialUnitMat N m t)
  rw [trialState, hL, hi] at h
  exact h

/-- `τ₁(ω₀* ω₀ Q_t) = b_t/Z`. -/
theorem trialUnitMat_trace_QB (hB : IsBandFamily B t) (t' : T) :
    (StdTracialAlgebra.amplify N (m + 1)).τ
        (star (trialUnitMat N m t) * (trialUnitMat N m t * trialQB N F B t'))
      = ((bandMassB F B t t' / bandZ t : ℝ) : ℂ) := by
  have h := trial_success_B N F B t hB t'
  have hR : (StdTracialAlgebra.amplify N (m + 1)).Rop (trialQB N F B t')
      ((StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t))
      = (StdTracialAlgebra.amplify N (m + 1)).ι (trialUnitMat N m t * trialQB N F B t') :=
    (StdTracialAlgebra.amplify N (m + 1)).R_apply _ _
  have hi := (StdTracialAlgebra.amplify N (m + 1)).ι_inner (trialUnitMat N m t)
    (trialUnitMat N m t * trialQB N F B t')
  rw [trialState, hR, hi] at h
  exact h

/-- `τ₁(ω₀* P_s ω₀ Q_t) = c_{st}/Z`. -/
theorem trialUnitMat_trace_joint (hB : IsBandFamily B t) (s : S) (t' : T) :
    (StdTracialAlgebra.amplify N (m + 1)).τ
        (star (trialUnitMat N m t) * (trialPA N F B s * trialUnitMat N m t * trialQB N F B t'))
      = ((bandCross F B t s t' / bandZ t : ℝ) : ℂ) := by
  have h := trial_success_joint N F B t hB s t'
  have hi := (StdTracialAlgebra.amplify N (m + 1)).inner_L_R (trialUnitMat N m t)
    (trialPA N F B s) (trialUnitMat N m t) (trialQB N F B t')
  rw [trialState, hi] at h
  exact h

/-- The normalized matrix trace of a `★★`-corner matrix. -/
theorem ampτ_single (z : N.A) :
    (StdTracialAlgebra.amplify N (m + 1)).τ (Matrix.single (Fin.last m) (Fin.last m) z) =
      ((m : ℂ) + 1)⁻¹ * N.τ z := by
  show StdTracialAlgebra.ampτ N (m + 1) (Matrix.single (Fin.last m) (Fin.last m) z) = _
  rw [StdTracialAlgebra.ampτ_apply]
  have hsum : (∑ i : Fin (m + 1),
      N.τ ((Matrix.single (Fin.last m) (Fin.last m) z : Matrix _ _ N.A) i i)) = N.τ z := by
    rw [Finset.sum_eq_single (Fin.last m)]
    · rw [Matrix.single_apply_same]
    · intro i _ hi
      rw [Matrix.single_apply, if_neg (by rintro ⟨h1, _⟩; exact hi h1.symm), map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, Nat.cast_succ]

end Trial

/-! ### First-success arithmetic (node 1.3.6)

Scalar consumed form of lem otqcs-first-success: the per-trial success
probabilities are `a/Z, b/Z, c/Z` (eq one-trial-probabilities), and
independence across trials reduces the first-success analysis to the
three scalar facts below (exact geometric mass of the equal-index
event, the mismatch bound, and the exhaustion tail). -/

/-- Exact equal-index probability (06_otqcs.tex, proof of lem
otqcs-first-success, the geometric sum): with per-trial progress
`w = (a + b − c)/Z`, the total mass of "both first successes at the
same trial" is `∑_{j≥0} (1 − w)^j (c/Z) = c/(a + b − c)`. -/
theorem equal_index_probability (a b c Z : ℝ) (hZ : 0 < Z)
    (hw : 0 < a + b - c) (hle : a + b - c ≤ Z) :
    (∑' j : ℕ, (1 - (a + b - c) / Z) ^ j * (c / Z)) =
      c / (a + b - c) := by
  set w := (a + b - c) / Z with hwdef
  have hw0 : 0 < w := div_pos hw hZ
  have hw1 : w ≤ 1 := by rw [hwdef, div_le_one hZ]; exact hle
  have hr0 : 0 ≤ 1 - w := by linarith
  have hr1 : 1 - w < 1 := by linarith
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
  rw [sub_sub_cancel]
  rw [hwdef]
  field_simp

/-- **First-success mismatch** (node 1.3.6; 06_otqcs.tex, eq
first-index-mismatch): when `a, b ≥ 1/2` (eq ab-mass under the
standing condition `ρ + L² ≤ 1/4`) and `c ≤ min{a, b}` (eq c-min),
the index-mismatch probability `(a + b − 2c)/(a + b − c)` is at most
`2 Γ = 2 (a + b − 2c)`. -/
theorem first_success_mismatch (a b c : ℝ) (ha : 1 / 2 ≤ a)
    (hb : 1 / 2 ≤ b) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
    (a + b - 2 * c) / (a + b - c) ≤ 2 * (a + b - 2 * c) := by
  have hd : 0 < a + b - c := by linarith
  have hΓ : 0 ≤ a + b - 2 * c := by linarith
  rw [div_le_iff₀ hd]
  nlinarith [mul_nonneg hΓ (by linarith : (0:ℝ) ≤ 2 * (a + b - c) - 1)]

/-- Exhaustion tail (06_otqcs.tex, eq finite-bad): a player with
per-trial success probability `a/Z ≥ 1/(2Z)` fails all `R` retained
trials with probability at most `e^{−R/(2Z)}`. -/
theorem all_fail_bound (a Z : ℝ) (R : ℕ) (hZ : 0 < Z) (ha : 1 / 2 ≤ a)
    (haZ : a ≤ Z) :
    (1 - a / Z) ^ R ≤ Real.exp (-(R : ℝ) / (2 * Z)) := by
  have haZ1 : a / Z ≤ 1 := (div_le_one hZ).mpr haZ
  have hnn : 0 ≤ 1 - a / Z := by linarith
  -- pointwise 1 - a/Z ≤ exp(-a/Z)
  have hpt : 1 - a / Z ≤ Real.exp (-(a / Z)) := by
    have := Real.add_one_le_exp (-(a / Z))
    linarith
  calc (1 - a / Z) ^ R ≤ (Real.exp (-(a / Z))) ^ R :=
        pow_le_pow_left₀ hnn hpt R
    _ = Real.exp ((R : ℝ) * -(a / Z)) := by
        rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (-(R : ℝ) / (2 * Z)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        have hle : (R : ℝ) / (2 * Z) ≤ (R : ℝ) * (a / Z) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Z)]
          have hRnn : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
          have : (R : ℝ) * (a / Z) * (2 * Z) = (R : ℝ) * a * 2 := by
            field_simp
          rw [this]
          nlinarith [hRnn, ha]
        linarith

end CommutingRepetition
