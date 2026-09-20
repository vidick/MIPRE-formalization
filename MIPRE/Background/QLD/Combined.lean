/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Expanded
import MIPRE.Foundations.Linearity
import MIPRE.Foundations.Sandwich
import MIPRE.Background.QLD.Swap

/-!
# Combining the two bases: the joint point measurement

Blueprint `lem:qld-combined-points`, the paper's `lem:qld-4-10`. The expansion stage left two
measurements per content --- one in each basis --- that *approximately commute*
(`lem:qld-expanded-points`). This stage turns them into a single projective measurement returning
both values at once.

## The route, and how it differs from the paper's

The paper builds the sandwich `R^w_{a,b} = M^Z_b M^X_a M^Z_b`, proves it approximately
self-consistent and approximately linear in the two probes, *orthonormalizes* it
(`cor:ortho-from-consistency`), and then applies the quantum linearity test
(`thm:linearity`) to the resulting observables. Three of those four steps are unnecessary here,
and the reason is that the strategy may be taken **projective** --- which is without loss of
generality by Naimark dilation, and which the paper also assumes:

* the sandwich is then already a POVM, and its terms are already projections;
* the joint measurement is its **Naimark dilation**, which is projective by construction --- no
  orthonormalization, and no `thm:linearity`;
* the compression identity of the dilation carries every estimate about the sandwich to the
  dilated measurement unchanged, so the estimates are proved once, about `R`.

What remains is the analytic content: the sandwich is close to the ordered product
(`hatSand_close`, one commutation), the ordered products are cross-party consistent, and the
sandwich is therefore self-consistent. The commutation input arrives at the level of the
**observables**, and Parseval is what moves it to the level of the measurement elements
(`sum_stateSqNorm_hatComm_le`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

set_option linter.unusedSectionVars false

section Combined

/-! ## The hatted point measurement, indexed by the point

`hatPOVM` is indexed by a content, but it depends on it only through the point of the relevant
basis --- not through the probes, the seed or the diagonal direction. Saying so once, by
re-indexing, is what lets the probe average be separated from the point average later. -/

/-- **The hatted point measurement at a point**: the strategy's point measurement at `u`,
convolved with the ancilla's syndrome measurement there. -/
def hatPtPOVM {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) :
    POVM F (d' × Anc F m) :=
  ((((M (.point W u)).map rdVal).kron (synPOVM W u)).map fun p => p.1 + p.2)

theorem hatPOVM_eq {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) :
    hatPOVM hm M W c = hatPtPOVM M W (c.pt W) := by
  rw [hatPOVM, ptValPOVM, Content.omega_pt, hatPtPOVM]
  rfl

/-- The elements of the hatted point measurement, as matrices. -/
def hatMats {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (a : F) :
    Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  (((hatPtPOVM M W u).mats a).val)

/-! ## The hatted observable at an arbitrary probe

`hatObs` is the hatted point observable at the probe the content itself carries. The transform
needs the whole family, one observable for each `r in F_q`, and `hatObsAt_self` is the
identification at the content's own probe. -/

/-- The hatted point measurement's binary observable at the probe `r`. -/
def hatObsAt {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (r : F) :
    Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  trObs (hatMats M W u) r

/-- **The measurement is the transform of its observables.** -/
theorem trFourier_hatObsAt {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (a : F) :
    trFourier (hatObsAt M W u) a = hatMats M W u a :=
  trFourier_trObs _ a

/-- A product family's transform splits: the hatted observable is the strategy's observable
tensored with the ancilla's. -/
theorem hatObsAt_eq {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (r : F) :
    hatObsAt M W u r
      = (trObs (fun a : F => ((((M (.point W u)).map rdVal).mats a).val)) r)
        ⊗ₖ (trObs (fun a : F => (((synPOVM W u).mats a).val)) r) := by
  classical
  rw [hatObsAt, show hatMats M W u = fun a : F => ((((hatPtPOVM M W u).mats a).val)) from rfl,
    hatPtPOVM, trObs_map]
  rw [Fintype.sum_prod_type, trObs, trObs, sum_kronecker_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.smul_kronecker, kronecker_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.kronecker_smul, smul_smul, POVM.kron_mats, ← sgn_add, ← map_add, ← add_mul]

/-- The strategy's factor, at the content's own probe, is `ptObs`. -/
theorem trObs_ptVal {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) :
    trObs (fun a : F => ((((M (.point W (c.pt W))).map rdVal).mats a).val)) (c.omega.r W)
      = ptObs hm M W c := by
  classical
  rw [trObs_map, ptObs, obs2_map]
  refine Finset.sum_congr rfl fun ans _ => ?_
  congr 1
  cases ans <;> simp [rdVal, rdProbeAt, rdProbe, prb]

/-- The ancilla's factor is the Weyl operator at `r . ind_m(u)`: the syndrome projectors are the
spectral projectors of the Weyl family, so their signed sum is the operator itself. -/
theorem trObs_synPOVM (W : Bas) (u : Point F m) (r : F) :
    trObs (fun a : F => (((synPOVM (F := F) (m := m) W u).mats a).val)) r
      = weylOf W (r • indVec u) := by
  classical
  rw [trObs, eq_sum_proj (w := weylOf (F := F) (m := m) W) (r • indVec u),
    ← Finset.sum_fiberwise (univ : Finset (Anc F m)) (fun e => dotF e (indVec u))
      (fun e => sgn (trDot (r • indVec u) e) • proj (weylOf (F := F) (m := m) W) e)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [synPOVM_mats, syn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  rw [trDot, ← (Finset.mem_filter.mp he).2, dotF]
  congr 2
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

/-- **At the content's own probe, the transform is `hatObs`.** -/
theorem hatObsAt_self (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) dA) (W : Bas) (c : Content F m) :
    hatObsAt M W (c.pt W) (c.omega.r W) = hatObs hm M W c := by
  rw [hatObsAt_eq, trObs_ptVal hm, trObs_synPOVM, hatObs, ancVec, Content.omega_pt]

/-! ## Parseval: from the observables' commutator to the elements'

The commutation input of `lem:qld-expanded-points` is about the *observables*, one pair for each
`(r, s)`. What the sandwich needs is the commutator of the measurement *elements*, one pair for
each `(a, b)`. Parseval exchanges the two at no cost: the sum over outcomes of the one is the
average over probes of the other. -/

/-- The commutator of the two bases' hatted measurement elements. -/
def hatComm {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (x z : Point F m) (a b : F) :
    Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  hatMats M .X x a * hatMats M .Z z b - hatMats M .Z z b * hatMats M .X x a

/-- The commutator of the two bases' hatted observables. -/
def hatObsComm {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (x z : Point F m) (r s : F) :
    Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  hatObsAt M .X x r * hatObsAt M .Z z s - hatObsAt M .Z z s * hatObsAt M .X x r

/-- **The elements' commutator is the transform of the observables'.** -/
theorem hatComm_eq_fourierOf {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (x z : Point F m) (a b : F) :
    hatComm M x z a b
      = fourierOf (fun v : Fin 2 → F => hatObsComm M x z (v 0) (v 1)) (pairVec a b) := by
  rw [show (fun v : Fin 2 → F => hatObsComm M x z (v 0) (v 1))
      = fun v : Fin 2 → F => hatObsAt M .X x (v 0) * hatObsAt M .Z z (v 1)
        - hatObsAt M .Z z (v 1) * hatObsAt M .X x (v 0) from rfl,
    fourierOf_sub, fourierOf_pair_mul, fourierOf_pair_mul', trFourier_hatObsAt,
    trFourier_hatObsAt, hatComm]

/-- **Parseval, for the commutator.** -/
theorem sum_stateSqNorm_hatComm (ψ : dA × dB → ℂ)
    (M : Question F m → POVM (Answer F m d) dA) (x z : Point F m) :
    ∑ p : F × F, stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm M x z p.1 p.2)
      = ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹)
        * ∑ p : F × F, stateSqNorm (hatVec (F := F) (m := m) ψ) (hatObsComm M x z p.1 p.2) := by
  classical
  have hcardR : ((Fintype.card (Fin 2 → F) : ℝ))⁻¹
      = (Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [pow_two, mul_inv]
  have hpar := sum_stateSqNorm_fourierOf (hatVec (F := F) (m := m) ψ)
    (fun v : Fin 2 → F => hatObsComm M x z (v 0) (v 1))
  rw [hcardR] at hpar
  rw [show (∑ p : F × F, stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm M x z p.1 p.2))
      = ∑ e : Fin 2 → F, stateSqNorm (hatVec (F := F) (m := m) ψ)
          (fourierOf (fun v : Fin 2 → F => hatObsComm M x z (v 0) (v 1)) e) from by
    rw [sum_prod_eq_sum_pairVec (fun a b => stateSqNorm (hatVec (F := F) (m := m) ψ)
      (hatComm M x z a b))]
    exact Finset.sum_congr rfl fun v _ => by rw [hatComm_eq_fourierOf, show pairVec (v 0) (v 1) = v
      from by funext i; fin_cases i <;> simp [pairVec]], hpar,
    sum_prod_eq_sum_pairVec (fun a b => stateSqNorm (hatVec (F := F) (m := m) ψ)
      (hatObsComm M x z a b))]

/-! ## Projectivity

The sandwich is a POVM only because the `Z`-side hatted measurement is *projective*, so the
strategy has to be. That is without loss of generality --- it is what `def:tensor-strategy`
already asks for, and Naimark dilation supplies it in general --- and the hypothesis is carried
explicitly. Projectivity passes through the convolution: a product of projective measurements is
projective, and so is a coarse-graining of one. -/

theorem isPVM_synPOVM (W : Bas) (u : Point F m) :
    IsPVM fun a : F => (((synPOVM (F := F) (m := m) W u).mats a).val) :=
  isPVM_synOfPOVM W _

/-- **The hatted point measurement is projective** when the strategy is. -/
theorem isPVM_hatMats {d' : Type} [Fintype d'] [DecidableEq d']
    {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (W : Bas) (u : Point F m) :
    IsPVM (hatMats M W u) :=
  isPVM_povm_map _ (isPVM_povm_kron _ _ (isPVM_povm_map _ (hM (.point W u)) rdVal)
    (isPVM_synPOVM W u)) _

/-! ## Splitting the content

The content average includes the uniform average over the two probes `(r_X, r_Z)`, independently
of everything else it carries. That is exactly what Parseval needs: the sum over *outcomes* of the
elements' commutator is the *average over probes* of the observables' (`sum_stateSqNorm_hatComm`),
and the content average of the second is the content average of the commutator at the content's
own probes --- which is what `lem:qld-expanded-points` bounds. -/

/-- The content, split into what the measurements see and the two probes. -/
def contentEquiv : Content F m ≃ ((Point F m × Point F m × F × Point F m) × (F × F)) where
  toFun c := ((c.uX, c.uZ, c.s, c.v), (c.rX, c.rZ))
  invFun p := ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_content_split {M : Type*} [AddCommMonoid M] (f : Content F m → M) :
    ∑ c : Content F m, f c
      = ∑ k : Point F m × Point F m × F × Point F m, ∑ p : F × F,
          f ⟨k.1, k.2.1, k.2.2.1, k.2.2.2, p.1, p.2⟩ := by
  classical
  rw [Fintype.sum_equiv contentEquiv f (fun q => f (contentEquiv.symm q)) fun c => rfl,
    ← Finset.univ_product_univ, Finset.sum_product]
  rfl

/-- The same, with the content's fields as separate arguments: the form the consumers use. -/
theorem sum_content_split' {M : Type*} [AddCommMonoid M]
    (f : Point F m → Point F m → F → Point F m → F → F → M) :
    ∑ c : Content F m, f c.uX c.uZ c.s c.v c.rX c.rZ
      = ∑ k : Point F m × Point F m × F × Point F m, ∑ p : F × F,
          f k.1 k.2.1 k.2.2.1 k.2.2.2 p.1 p.2 :=
  sum_content_split fun c => f c.uX c.uZ c.s c.v c.rX c.rZ

/-- **The probe average is free.** Averaging a probe-independent quantity over the content's own
probes changes nothing, so a bound stated at the content's probes is a bound on the average over
all probes --- which is the form Parseval produces. -/
theorem sum_content_avg_probe (g : Point F m → Point F m → F → F → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ * ∑ p : F × F, g c.uX c.uZ p.1 p.2)
      = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * g c.uX c.uZ c.rX c.rZ := by
  classical
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_content_split' (F := F) (m := m) fun x z _ _ _ _ =>
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹ * ∑ p : F × F, g x z p.1 p.2),
    sum_content_split' (F := F) (m := m) fun x z _ _ r t =>
      (Fintype.card (Content F m) : ℝ)⁻¹ * g x z r t]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  field_simp

/-! ## The element-level commutator bound -/

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

set_option maxHeartbeats 1600000 in
/-- **The elements of the two bases' hatted point measurements commute on the expanded state**, on
average over the content, at the constant of `lem:qld-obs-commutation`. This is
`hatObs_commutation` moved from the observables to the measurement elements by Parseval, which
costs nothing --- the probe average the transform introduces is the one the content already
carries. -/
theorem sum_content_hatComm_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm MA c.uX c.uZ p.1 p.2)
      ≤ 57676416 * ε := by
  classical
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
    rw [sum_stateSqNorm_hatComm (F := F) (m := m) ψ MA c.uX c.uZ],
    sum_content_avg_probe fun x z r s =>
      stateSqNorm (hatVec (F := F) (m := m) ψ) (hatObsComm MA x z r s)]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c (_ : c ∈ univ) => ?_))
    (hatObs_commutation (MB := MB) hψ hfail)
  congr 1
  show stateSqNorm (hatVec (F := F) (m := m) ψ) (hatObsComm MA c.uX c.uZ c.rX c.rZ)
    = ‖stateVec (hatVec (F := F) (m := m) ψ) (hatObs hm MA .X c * hatObs hm MA .Z c
        - hatObs hm MA .Z c * hatObs hm MA .X c)‖ ^ 2
  rw [stateSqNorm, stateNorm, hatObsComm,
    show hatObsAt MA .X c.uX c.rX = hatObs hm MA .X c from hatObsAt_self hm MA .X c,
    show hatObsAt MA .Z c.uZ c.rZ = hatObs hm MA .Z c from hatObsAt_self hm MA .Z c]

/-- The same for the other player, by the game's symmetry in the two players. -/
theorem sum_content_hatComm_le_B (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
        ‖stateVecB (hatVec (F := F) (m := m) ψ) (hatComm MB c.uX c.uZ p.1 p.2)‖ ^ 2
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le (hm := hm) (MA := MB) (MB := MA) (ψ := swapVec ψ)
    (swapVec_unit hψ) (povmValue_swapped_le hfail)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) h
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [norm_stateVecB, hatVec_swapVec]
  rfl

/-! ## The cross-party consistency, at the points -/

/-- `lem:qld-expanded-points`'s first item, re-indexed by the point. -/
theorem hatPOVM_mats_eq {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) (a : F) :
    (((hatPOVM hm M W c).mats a).val) = hatMats M W (c.pt W) a := by
  rw [hatPOVM_eq hm M W c]
  rfl

theorem sum_content_hatMats_consistency (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
          (hatMats MB W (c.pt W) a)
      ≤ 172 * ε := by
  have h := hatPOVM_consistency (MB := MB) hψ hfail W
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) =>
    congrArg (fun t : ℝ => (Fintype.card (Content F m) : ℝ)⁻¹ * t)
      (Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
        rw [hatPOVM_mats_eq hm MA W c a, hatPOVM_mats_eq hm MB W c a])] at h
  exact h

/-! ## The lemma -/

/-- **The error of `lem:qld-combined-points`**, the paper's `delta_Q(eps) = poly(eps)`. The square
roots are the three Cauchy--Schwarz steps of the sandwich's self-consistency chain; the linear term
is the `Z`-consistency, which enters without one. -/
def deltaQ (ε : ℝ) : ℝ :=
  2 * Real.sqrt (57676416 * ε) + Real.sqrt (86 * ε) + 86 * ε

theorem sum_uniform_content : ∑ _c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ = 1 := by
  have hpos : 0 < Fintype.card (Content F m) :=
    Fintype.card_pos_iff.mpr ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne')

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-combined-points`.** For each pair of points `(x, z)` there is a *projective*
measurement on each party's expanded space, enlarged by one `F_q x F_q` ancilla register, which
returns the `X`-value at `x` and the `Z`-value at `z` at once; it is self-consistent across the two
parties on average over the content, and consistent with **both** ordered products of the expanded
point measurements. Every error is `poly(eps)` and none depends on `q`.

The measurement is the Naimark dilation of the sandwich `M-hat^{Z,z}_b M-hat^{X,x}_a
M-hat^{Z,z}_b`, and the third and fourth conclusions record the compression identity, which is
what carries the estimates. -/
theorem combined_points (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) :
    ∃ (QA : Content F m → F × F →
        Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ)
      (QB : Content F m → F × F →
        Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ),
      (∀ c, IsPVM (QA c)) ∧ (∀ c, IsPVM (QB c))
      ∧ (∀ c p, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QA c p * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MA .X c.uX) (hatMats MA .Z c.uZ) p)
      ∧ (∀ c p, (ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QB c p * ancillaEmbed (dB × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MB .X c.uX) (hatMats MB .Z c.uZ) p)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
            xSqNorm (extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F)) ((0 : F), (0 : F)))
              (QA c p) (QB c p)
          ≤ 2 * deltaQ ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
            xSqNorm (extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F)) ((0 : F), (0 : F)))
              (QA c p) (aOp (hatMats MB .Z c.uZ p.2 * hatMats MB .X c.uX p.1))
          ≤ 4 * deltaQ ε + 115352832 * ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ p : F × F,
            xSqNorm (extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F)) ((0 : F), (0 : F)))
              (QA c p) (aOp (hatMats MB .X c.uX p.1 * hatMats MB .Z c.uZ p.2))
          ≤ 4 * deltaQ ε + 461411328 * ε) := by
  classical
  have hΓ : Real.sqrt (57676416 * ε) + Real.sqrt (57676416 * ε) + Real.sqrt (172 * ε / 2)
      + 172 * ε / 2 = deltaQ ε := by
    rw [deltaQ, show (172 : ℝ) * ε / 2 = 86 * ε from by ring]
    ring
  obtain ⟨QA, QB, hPA, hPB, hkA, hkB, h1, h2, h3⟩ :=
    exists_projective_joint (A := F) (ι := Content F m)
      (w := fun _ : Content F m => (Fintype.card (Content F m) : ℝ)⁻¹)
      (fun _ => by positivity) sum_uniform_content (hatVec_unit hψ) ((0 : F), (0 : F))
      (X := fun c : Content F m => hatMats MA .X c.uX)
      (Z := fun c : Content F m => hatMats MA .Z c.uZ)
      (X' := fun c : Content F m => hatMats MB .X c.uX)
      (Z' := fun c : Content F m => hatMats MB .Z c.uZ)
      (fun c => isPVM_hatMats hprojA .X c.uX) (fun c => isPVM_hatMats hprojA .Z c.uZ)
      (fun c => isPVM_hatMats hprojB .X c.uX) (fun c => isPVM_hatMats hprojB .Z c.uZ)
      (cA := 57676416 * ε) (cB := 57676416 * ε) (α := 172 * ε) (β := 172 * ε)
      (sum_content_hatComm_le (MB := MB) hψ hfail)
      (sum_content_hatComm_le_B (MA := MA) hψ hfail)
      (sum_content_hatMats_consistency (MB := MB) hψ hfail .X)
      (sum_content_hatMats_consistency (MB := MB) hψ hfail .Z)
  refine ⟨QA, QB, hPA, hPB, hkA, hkB, ?_, ?_, ?_⟩
  · rw [← hΓ]; exact h1
  · rw [← hΓ, show (115352832 : ℝ) * ε = 2 * (57676416 * ε) from by ring]; exact h2
  · rw [← hΓ, show (461411328 : ℝ) * ε = 8 * (57676416 * ε) from by ring]; exact h3

/-! ## The padded point measurement

Blueprint `lem:qld-padded-points`. A point of the padded space `F_q^{4m}` is
`u = (x, z, alpha, beta, w)`, and the measurement returns the *combined* value
`alpha g_X(x) + beta g_Z(z)`: the combined point measurement of
`lem:qld-combined-points`, coarse-grained along the linear form `(a, b) |-> alpha a + beta b`.
It depends on `u` only through `(x, z, alpha, beta)`, which is what ``independent of the dummy
coordinates'' means, and it is indexed by those here.

The two conclusions are free for opposite reasons. Self-consistency survives the coarse-graining
at no cost because both families are *projective*, so the deviation and the agreement determine
each other and agreement only increases (`sum_xSqNorm_map_le`). Consistency with the ordered
products does *not* survive it unaided --- the fibres have `q` elements and a triangle inequality
would cost exactly that factor --- and what saves it is Parseval over `F_q`
(`sum_avg_norm_fibre_sq`), whose zero-probe term vanishes because the deviation family sums to
zero: both `sum_{a,b} Q-hat_{a,b}` and `sum_{a,b} M-hat^Z_b M-hat^X_a` are the identity. -/

/-- Bob's ordered product, `Z` then `X`. -/
def hatOrdZX {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (x z : Point F m) (p : F × F) :
    Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  hatMats M .Z z p.2 * hatMats M .X x p.1

/-- Bob's ordered product, `X` then `Z`. -/
def hatOrdXZ {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (x z : Point F m) (p : F × F) :
    Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  hatMats M .X x p.1 * hatMats M .Z z p.2

theorem sum_hatOrdZX {d' : Type} [Fintype d'] [DecidableEq d']
    {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (x z : Point F m) :
    ∑ p : F × F, hatOrdZX M x z p = 1 := by
  classical
  rw [sum_prod_swap (fun p : F × F => hatOrdZX M x z p)]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
      (∑ a : F, hatOrdZX M x z (a, b)) = hatMats M .Z z b from by
    rw [show (∑ a : F, hatOrdZX M x z (a, b))
        = hatMats M .Z z b * ∑ a : F, hatMats M .X x a from by
      rw [Matrix.mul_sum]
      rfl, (isPVM_hatMats hM .X x).sum_eq_one, Matrix.mul_one]]
  exact (isPVM_hatMats hM .Z z).sum_eq_one

theorem sum_hatOrdXZ {d' : Type} [Fintype d'] [DecidableEq d']
    {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (x z : Point F m) :
    ∑ p : F × F, hatOrdXZ M x z p = 1 := by
  classical
  rw [sum_prod_id (fun p : F × F => hatOrdXZ M x z p)]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => show
      (∑ b : F, hatOrdXZ M x z (a, b)) = hatMats M .X x a from by
    rw [show (∑ b : F, hatOrdXZ M x z (a, b))
        = hatMats M .X x a * ∑ b : F, hatMats M .Z z b from by
      rw [Matrix.mul_sum]
      rfl, (isPVM_hatMats hM .Z z).sum_eq_one, Matrix.mul_one]]
  exact (isPVM_hatMats hM .X x).sum_eq_one

/-- **Parseval for the padded coarse-graining.** On average over `(alpha, beta)` the summed
deviation of the two families coarse-grained along `(a, b) |-> alpha a + beta b` is `1 - 1/q`
times the families' own --- in particular no worse, although the fibres have `q` elements. The
two normalizations are what make the zero probe drop out. -/
theorem sum_avg_xSqNorm_fibre_eq {d1 d2 : Type*} [Fintype d1] [DecidableEq d1]
    [Fintype d2] [DecidableEq d2] (Ψ : d1 × d2 → ℂ)
    {Q : F × F → Matrix d1 d1 ℂ} {B : F × F → Matrix d2 d2 ℂ}
    (hQ : ∑ p : F × F, Q p = 1) (hB : ∑ p : F × F, B p = 1) :
    ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
        ∑ v : F, xSqNorm Ψ
          (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, Q p)
          (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, B p)
      = (1 - (Fintype.card F : ℝ)⁻¹) * ∑ p : F × F, xSqNorm Ψ (Q p) (B p) := by
  classical
  set U : F × F → ((d1 × d2) → ℂ) := fun p =>
    ((aOp (Q p) : Matrix (d1 × d2) _ ℂ) - bOp (B p)) *ᵥ Ψ with hUdef
  have hU0 : ∑ p : F × F, U p = 0 := by
    rw [hUdef,
      show (∑ p : F × F, (((aOp (Q p) : Matrix (d1 × d2) _ ℂ) - bOp (B p)) *ᵥ Ψ))
        = ((aOp (∑ p : F × F, Q p) : Matrix (d1 × d2) _ ℂ) - bOp (∑ p : F × F, B p)) *ᵥ Ψ from
        sum_fibre_dev Ψ univ Q B, hQ, hB, aOp_one, bOp_one, sub_self, Matrix.zero_mulVec]
  have hfib := sum_avg_norm_fibre_sq U hU0
  have hcoarse : ∀ (ab : F × F) (v : F),
      ‖evec (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, U p)‖ ^ 2
        = xSqNorm Ψ (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, Q p)
            (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, B p) := by
    intro ab v
    rw [xSqNorm_eq_norm_evec_sq, hUdef]
    exact congrArg (fun w => ‖evec w‖ ^ 2) (sum_fibre_dev Ψ _ Q B)
  have hfine : ∀ p : F × F, ‖evec (U p)‖ ^ 2 = xSqNorm Ψ (Q p) (B p) := fun p => by
    rw [xSqNorm_eq_norm_evec_sq, hUdef]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hfine p,
    Finset.sum_congr rfl fun ab (_ : ab ∈ univ) =>
      congrArg (fun t : ℝ => ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) * t)
        (Finset.sum_congr rfl fun v (_ : v ∈ univ) => hcoarse ab v)] at hfib
  exact hfib

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-padded-points`.** The padded space's point measurement: the combined `XZ`
measurement coarse-grained along `(a, b) |-> alpha a + beta b`, so that it returns the single
field element `alpha g_X(x) + beta g_Z(z)`. It is indexed by `(x, z, alpha, beta)` --- which is
what ``independent of the dummy coordinates'' means --- projective, self-consistent, and
consistent with both ordered products of the expanded point measurements, coarse-grained the same
way. -/
theorem padded_points (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) :
    ∃ (QA : Content F m → F × F → F →
        Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ)
      (QB : Content F m → F × F → F →
        Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ),
      (∀ c ab, IsPVM (QA c ab)) ∧ (∀ c ab, IsPVM (QB c ab))
      ∧ (∀ ab : F × F, ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
            ∑ v : F, xSqNorm (extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F))
              ((0 : F), (0 : F))) (QA c ab v) (QB c ab v)
          ≤ 2 * deltaQ ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
            ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
              ∑ v : F, xSqNorm (extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F))
                  ((0 : F), (0 : F))) (QA c ab v)
                (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v,
                  aOp (hatOrdZX MB c.uX c.uZ p))
          ≤ 4 * deltaQ ε + 115352832 * ε)
      ∧ (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
            ∑ ab : F × F, ((Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ)⁻¹) *
              ∑ v : F, xSqNorm (extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F))
                  ((0 : F), (0 : F))) (QA c ab v)
                (∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v,
                  aOp (hatOrdXZ MB c.uX c.uZ p))
          ≤ 4 * deltaQ ε + 461411328 * ε) := by
  classical
  obtain ⟨QA0, QB0, hPA, hPB, hkA, hkB, h1, h2, h3⟩ :=
    combined_points (MB := MB) hψ hfail hprojA hprojB
  set Φ := extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F)) ((0 : F), (0 : F)) with hΦ
  have hΦ1 : star Φ ⬝ᵥ Φ = 1 := extVec2_unit (hatVec_unit hψ) _ _
  have hq1 : (0 : ℝ) ≤ 1 - (Fintype.card F : ℝ)⁻¹ := by
    have h : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
      have : 1 ≤ Fintype.card F := Fintype.card_pos
      exact_mod_cast this
    have h0 : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
    rw [sub_nonneg, inv_le_one_iff₀]
    right
    exact h
  have hq2 : (1 : ℝ) - (Fintype.card F : ℝ)⁻¹ ≤ 1 := by
    have : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := by positivity
    linarith
  -- Bob's ordered products sum to the identity, which is what kills the zero probe
  have hZX : ∀ c : Content F m, ∑ p : F × F,
      (aOp (hatOrdZX MB c.uX c.uZ p) : Matrix ((dB × Anc F m) × (F × F)) _ ℂ) = 1 := by
    intro c
    rw [← aOp_sum, sum_hatOrdZX hprojB, aOp_one]
  have hXZ : ∀ c : Content F m, ∑ p : F × F,
      (aOp (hatOrdXZ MB c.uX c.uZ p) : Matrix ((dB × Anc F m) × (F × F)) _ ℂ) = 1 := by
    intro c
    rw [← aOp_sum, sum_hatOrdXZ hprojB, aOp_one]
  refine ⟨fun c ab v => ∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, QA0 c p,
    fun c ab v => ∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, QB0 c p,
    fun c ab => (hPA c).coarse _, fun c ab => (hPB c).coarse _, ?_, ?_, ?_⟩
  · -- item 1: coarse-graining costs nothing, both families being projective
    intro ab
    refine le_trans (Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) h1
    have hmap := sum_xSqNorm_map_le (A := F × F) (C := F) hΦ1
      (hPA c).toPOVM (hPB c).toPOVM (by simpa using hPA c) (by simpa using hPB c)
      (fun p : F × F => ab.1 * p.1 + ab.2 * p.2)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun v _ => ?_)) hmap
    rw [show (((((hPA c).toPOVM).map fun p : F × F => ab.1 * p.1 + ab.2 * p.2).mats v).val)
        = ∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, QA0 c p from
      AddSubmonoidClass.coe_finsetSum _ _,
      show (((((hPB c).toPOVM).map fun p : F × F => ab.1 * p.1 + ab.2 * p.2).mats v).val)
        = ∑ p ∈ univ.filter fun p : F × F => ab.1 * p.1 + ab.2 * p.2 = v, QB0 c p from
      AddSubmonoidClass.coe_finsetSum _ _]
  · -- item 2: Parseval, and the zero probe drops out
    refine le_trans (Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) h2
    rw [sum_avg_xSqNorm_fibre_eq Φ (hPA c).sum_eq_one (hZX c)]
    refine le_trans (mul_le_mul_of_nonneg_right hq2 (Finset.sum_nonneg fun p _ =>
      xSqNorm_nonneg _ _ _)) (le_of_eq (one_mul _))
  · -- item 3: the same, at the other order
    refine le_trans (Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left ?_ (by positivity)) h3
    rw [sum_avg_xSqNorm_fibre_eq Φ (hPA c).sum_eq_one (hXZ c)]
    refine le_trans (mul_le_mul_of_nonneg_right hq2 (Finset.sum_nonneg fun p _ =>
      xSqNorm_nonneg _ _ _)) (le_of_eq (one_mul _))

end Combined

end MIPRE.QLD

end
