/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import MIPRE.Foundations.FinitePairExpand
public import MIPRE.Foundations.MatUnits
public import MIPRE.Tactics

@[expose] public section

/-!
# Dyadic pairs: finite pairs with no abelian projections

The orthonormalization step of the C6b port (`povm_orthogonalization_finitePair`, in
`MIPRE/Background/Orthonormalization/FinitePairOrtho.lean`) applies in the first algebra of a
finite pair whose operators contain no nonzero abelian projection: no projection `r` with
`(r x r)(r y r) = (r y r)(r x r)` for all of the algebra's `x, y`. This file gives a class of finite
pairs in which that holds on both sides, by a trace estimate and no comparison theory
(`reports/c6b-paper-proofs.md`, §3, Theorems K, K′ and Cl).

* **Cauchy–Schwarz in a commutative corner** (`mul_star_le_mul_of_commute`): for operators `x, y`
  with `α = x⋆x`, `β = y⋆y`, `γ = x⋆y`, if `α` commutes with `β` and `β` with `γ`, then
  `γ γ⋆ ≤ α β`. The proof writes `(β + ε)(α (β + ε) − γ γ⋆)` as `z⋆z + ε γ γ⋆` and lets `ε → 0`.
* **The trace estimate** (`VecTrace.card_mul_re_tr_le_one`, Theorem K1): in a set `s` of operators
  closed under products and adjoints, with a faithful tracial vector functional `tr` and unital
  `ι × ι` matrix units `f`, an abelian projection `p` has `|ι| · Re tr p ≤ 1`. With
  `wᵢ = f_{i₀ i} p` and `X = ∑ᵢ wᵢ wᵢ⋆`: `tr X = tr p`, `Re tr X² ≤ Re tr p` by the corner
  Cauchy–Schwarz applied to the commuting `p fᵢⱼ p`, and `X` lives under `f_{i₀ i₀}`, whose trace
  is `1/|ι|`; positivity of `tr (X − c f_{i₀ i₀})²` at `c = |ι| tr p` gives the bound.
* **No abelian projections** (`VecTrace.eq_zero_of_dyadicUnits`, Theorem K2): with units of every
  size `2ⁿ`, an abelian projection has trace `0`, so vanishes, the trace being faithful.
* **Finite pairs** (`IsFinitePair.eq_zero_of_abelianA`, `.eq_zero_of_abelianB`, Theorem K′): in a
  finite pair whose first algebra has unital dyadic matrix units, the first player's operators
  contain no nonzero abelian projection, in the form of the hypothesis `hII` of
  `povm_orthogonalization_finitePair`; and likewise for the second.
* **The class** (`BipartiteModel.IsDyadicPair`): finite pairs whose two algebras have unital
  dyadic matrix units (`MIPRE/Foundations/MatUnits.lean`). It is closed under the exchange of the
  players (`IsDyadicPair.swap`) and ancilla extensions (`IsDyadicPair.expand`), the two model
  operations at the boundary of `LIDT.Simul.SoundFin`.
* **Values** (`CommutingFinitePairApprox`): below `ω_co(G)`, and above `0`, lies the value of a
  projective strategy for `G` in a dyadic pair on a Hilbert space of `Type`. It is the statement
  `LIDT.Simul.SoundFin` is used through; the proof, on the `Background` side
  (`MIPRE.Repetition.commutingFinitePairApprox`), amplifies the finite pairs of Lin's tracial
  density by the twisted Pauli algebra.
-/

namespace MIPRE

open scoped InnerProductSpace

/-! ## Cauchy–Schwarz in a commutative corner -/

section CauchySchwarz

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `ε`-regularized corner Cauchy–Schwarz inequality: `0 ≤ α (β + ε) − γ γ⋆`. -/
private theorem sub_mul_star_nonneg_of_commute {x y α β γ : H →L[ℂ] H} (hα : star x * x = α)
    (hβ : star y * y = β) (hγ : star x * y = γ) (h1 : Commute α β) (h2 : Commute β γ) {ε : ℝ}
    (hε : 0 < ε) : 0 ≤ α * (β + algebraMap ℝ _ ε) - γ * star γ := by
  have hγs : star y * x = star γ := by rw [← hγ, star_mul, star_star]
  have hβsa : star β = β := by rw [← hβ, star_mul, star_star]
  have hβ0 : 0 ≤ β := hβ ▸ star_mul_self_nonneg y
  set e : H →L[ℂ] H := algebraMap ℝ (H →L[ℂ] H) ε with he
  have hc : ∀ c : H →L[ℂ] H, Commute e c := fun c => Algebra.commutes' ε c
  have hesa : star e = e := (isStrictlyPositive_algebraMap hε).isSelfAdjoint.star_eq
  have hbpos : IsStrictlyPositive (β + e) := by
    rw [add_comm]; exact (isStrictlyPositive_algebraMap hε).add_nonneg hβ0
  have hβγs : Commute β (star γ) := by
    have := h2.star_star; rwa [hβsa] at this
  have hbα : Commute (β + e) α := h1.symm.add_left (hc α)
  have hbγ : Commute (β + e) γ := h2.add_left (hc γ)
  have hbγs : Commute (β + e) (star γ) := hβγs.add_left (hc _)
  have hbsa : star (β + e) = β + e := by rw [star_add, hβsa, hesa]
  -- the identity `b D = z⋆ z + ε γ γ⋆`, with `b = β + ε` and `z = x b − y γ⋆`
  have key : (β + e) * (α * (β + e) - γ * star γ) =
      star (x * (β + e) - y * star γ) * (x * (β + e) - y * star γ) + e * (γ * star γ) := by
    rw [star_sub, star_mul, star_mul, hbsa, star_star]
    have e1 : (β + e) * star x * (x * (β + e)) = (β + e) * α * (β + e) := by
      rw [← hα]; noncomm_ring
    have e2 : (β + e) * star x * (y * star γ) = (β + e) * (γ * star γ) := by
      rw [← hγ]; noncomm_ring
    have e3 : γ * star y * (x * (β + e)) = γ * star γ * (β + e) := by
      rw [← hγs]; noncomm_ring
    have e4 : γ * star y * (y * star γ) = γ * β * star γ := by
      rw [← hβ]; noncomm_ring
    simp only [sub_mul, mul_sub]
    rw [e1, e2, e3, e4]
    have f1 : (β + e) * α * (β + e) = (β + e) * (α * (β + e)) := by
      rw [mul_assoc]
    have f2 : γ * star γ * (β + e) = (β + e) * (γ * star γ) :=
      ((hbγ.mul_right hbγs).eq).symm
    have f3 : γ * β * star γ = β * (γ * star γ) := by
      rw [← h2.eq]; noncomm_ring
    rw [f1, f2, f3]; noncomm_ring
  have hpos :
      0 ≤ star (x * (β + e) - y * star γ) * (x * (β + e) - y * star γ) + e * (γ * star γ) :=
    add_nonneg (star_mul_self_nonneg _)
      (Commute.mul_nonneg (isStrictlyPositive_algebraMap hε).nonneg (mul_star_self_nonneg γ)
        (hc _))
  rw [← key] at hpos
  have hbD : Commute (β + e) (α * (β + e) - γ * star γ) :=
    (hbα.mul_right (Commute.refl _)).sub_right (hbγ.mul_right hbγs)
  have hcomm : Commute (Ring.inverse (β + e)) ((β + e) * (α * (β + e) - γ * star γ)) := by
    obtain ⟨u, hu⟩ := hbpos.isUnit
    have h := (Commute.refl (β + e)).mul_right hbD
    rw [← hu] at h ⊢
    rw [Ring.inverse_unit]
    exact h.units_inv_left
  have := Commute.mul_nonneg hbpos.ringInverse.nonneg hpos hcomm
  rwa [← mul_assoc, Ring.inverse_mul_cancel _ hbpos.isUnit, one_mul] at this

/-- **Cauchy–Schwarz in a commutative corner** (`thm:no-abelian-dyadic`, the tool of its proof): for
operators `x, y` with `α = x⋆x`, `β = y⋆y` and `γ = x⋆y`, if `α` commutes with `β` and `β` with `γ`,
then `γ γ⋆ ≤ α β`. -/
theorem mul_star_le_mul_of_commute {x y α β γ : H →L[ℂ] H} (hα : star x * x = α)
    (hβ : star y * y = β) (hγ : star x * y = γ) (h1 : Commute α β) (h2 : Commute β γ) :
    γ * star γ ≤ α * β := by
  rw [← sub_nonneg]
  let f : ℝ → (H →L[ℂ] H) := fun ε => α * (β + algebraMap ℝ _ ε) - γ * star γ
  have hf : Continuous f :=
    (continuous_const.mul (continuous_const.add (by
      have : (⇑(algebraMap ℝ (H →L[ℂ] H))) = fun ε => ε • (1 : H →L[ℂ] H) :=
        funext fun ε => Algebra.algebraMap_eq_smul_one ε
      rw [this]; exact continuous_id.smul continuous_const))).sub
      continuous_const
  have hcl : IsClosed (f ⁻¹' {a | 0 ≤ a}) := CStarAlgebra.isClosed_nonneg.preimage hf
  have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by simp
  have : (0 : ℝ) ∈ f ⁻¹' {a | 0 ≤ a} :=
    closure_minimal (fun ε (hε : 0 < ε) => sub_mul_star_nonneg_of_commute hα hβ hγ h1 h2 hε)
      hcl h0
  simpa [f] using this

end CauchySchwarz

/-! ## The trace functional of a vector trace -/

namespace VecTrace

section Tr

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {s : Set (H →L[ℂ] H)}
  (τ : VecTrace s)

/-- **The functional of a vector trace**, on all operators: `tr T = ∑ₖ ⟪gₖ, T gₖ⟫`, a linear
functional. -/
noncomputable def tr : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun T := ∑ k, ⟪τ.g k, T (τ.g k)⟫_ℂ
  map_add' T S := by simp [Finset.sum_add_distrib]
  map_smul' c T := by simp [Finset.mul_sum]

/-- The functional is normalized. -/
theorem tr_one : τ.tr 1 = 1 := by
  have h := τ.norm_sq_sum
  simp only [tr, LinearMap.coe_mk, AddHom.coe_mk, one_apply_eq_self, inner_self_eq_norm_sq_to_K]
  rw [← Complex.ofReal_one, ← h]; push_cast; rfl

/-- The functional is tracial on the set. -/
theorem tr_mul_comm {T S : H →L[ℂ] H} (hT : T ∈ s) (hS : S ∈ s) :
    τ.tr (T * S) = τ.tr (S * T) :=
  τ.trace_mul_comm T hT S hS

/-- The functional is positive. -/
theorem re_tr_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) : 0 ≤ (τ.tr T).re := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT
  simp only [tr, LinearMap.coe_mk, AddHom.coe_mk, Complex.re_sum]
  exact Finset.sum_nonneg fun k _ => hT.re_inner_nonneg_right _

/-- The real part of the functional is monotone. -/
theorem re_tr_mono {T S : H →L[ℂ] H} (h : T ≤ S) : (τ.tr T).re ≤ (τ.tr S).re := by
  have := τ.re_tr_nonneg (sub_nonneg.mpr h)
  rw [map_sub, Complex.sub_re] at this; linarith

variable [CompleteSpace H]

/-- `tr (T⋆T) = ∑ₖ ‖T gₖ‖²`. -/
theorem tr_star_mul_self (T : H →L[ℂ] H) :
    τ.tr (star T * T) = ((∑ k, ‖T (τ.g k)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [tr, LinearMap.coe_mk, AddHom.coe_mk, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, Complex.ofReal_sum, Complex.ofReal_pow]
  rfl

end Tr

/-! ## The trace estimate, and no abelian projections -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {s : Set (H →L[ℂ] H)}

/-- **An abelian projection has trace at most `1/|ι|`** (`thm:no-abelian-dyadic`, item K1; Theorem
K1 of `reports/c6b-paper-proofs.md`, §3): in a set `s` of operators closed under products and
adjoints, with a faithful tracial vector functional `τ` and unital `ι × ι` matrix units in `s`, a
projection `p ∈ s` with `(p x p)(p y p) = (p y p)(p x p)` for all `x, y ∈ s` has
`|ι| · Re tr p ≤ 1`. -/
theorem card_mul_re_tr_le_one (τ : VecTrace s) (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s)
    (hstar : ∀ x ∈ s, star x ∈ s) {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    {f : ι → ι → H →L[ℂ] H} (hf : IsMatUnits f) (hfs : ∀ i j, f i j ∈ s) {p : H →L[ℂ] H}
    (hpP : IsStarProjection p) (hps : p ∈ s)
    (hab : ∀ x ∈ s, ∀ y ∈ s, p * x * p * (p * y * p) = p * y * p * (p * x * p)) :
    (Fintype.card ι : ℝ) * (τ.tr p).re ≤ 1 := by
  have hpsa : star p = p := hpP.isSelfAdjoint.star_eq
  have hpp : p * p = p := hpP.isIdempotentElem.eq
  have hmulij : ∀ i j m, f i j * f j m = f i m := hf.mul_cancel
  let w : ι → H →L[ℂ] H := fun i => f i0 i * p
  let a : ι → ι → H →L[ℂ] H := fun i j => p * f i j * p
  have hws : ∀ i, w i ∈ s := fun i => hmul _ (hfs _ _) _ hps
  have hwss : ∀ i, star (w i) ∈ s := fun i => hstar _ (hws i)
  have hsw : ∀ i, star (w i) = p * f i i0 := fun i => by
    simp only [w, star_mul, hpsa, hf.star_eq]
  have hww : ∀ i j, star (w i) * w j = a i j := fun i j => by
    rw [hsw]; simp only [w, a]; rw [← hmulij i i0 j]; noncomm_ring
  have hcomm : ∀ i j l m, Commute (a i j) (a l m) := fun i j l m =>
    hab _ (hfs i j) _ (hfs l m)
  have hsa : ∀ i j, star (a i j) = a j i := fun i j => by
    simp only [a, star_mul, hpsa, hf.star_eq, mul_assoc]
  have hdiag : ∑ i, a i i = p := by
    simp only [a]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hf.sum_diag, mul_one, hpp]
  have hcs : ∀ i j, a i j * star (a i j) ≤ a i i * a j j := fun i j =>
    mul_star_le_mul_of_commute (hww i i) (hww j j) (hww i j) (hcomm _ _ _ _) (hcomm _ _ _ _)
  set X : H →L[ℂ] H := ∑ i, w i * star (w i) with hX
  have hXsa : star X = X := by
    simp only [hX, star_sum, star_mul, star_star]
  have htrX : τ.tr X = τ.tr p := by
    rw [hX, map_sum, ← hdiag, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [τ.tr_mul_comm (hws i) (hwss i), hww]
  have htrXX : (τ.tr (X * X)).re ≤ (τ.tr p).re := by
    have h1 : τ.tr (X * X) = ∑ i, ∑ j, τ.tr (a i j * star (a i j)) := by
      rw [hX, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hY : star (w i) * (w j * star (w j)) ∈ s :=
        hmul _ (hwss i) _ (hmul _ (hws j) _ (hwss j))
      rw [mul_assoc, τ.tr_mul_comm (hws i) hY]
      congr 1
      rw [hsa, ← hww j i, ← hww i j]; noncomm_ring
    have h2 : τ.tr p = ∑ i, ∑ j, τ.tr (a i i * a j j) := by
      rw [← hpp, ← hdiag, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, map_sum]
    rw [h1, h2, Complex.re_sum, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Complex.re_sum, Complex.re_sum]
    exact Finset.sum_le_sum fun j _ => τ.re_tr_mono (hcs i j)
  have heX : f i0 i0 * X = X := by
    simp only [hX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show f i0 i0 * (f i0 i * p * star (w i)) = f i0 i * p * star (w i)
    rw [← mul_assoc, ← mul_assoc, hmulij]
  have hXe : X * f i0 i0 = X := by
    simp only [hX, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w i * star (w i) * f i0 i0 = w i * star (w i)
    rw [hsw, mul_assoc (w i), mul_assoc p, hmulij]
  have hes : star (f i0 i0) = f i0 i0 := hf.star_eq _ _
  have hee : f i0 i0 * f i0 i0 = f i0 i0 := hmulij _ _ _
  have htre : (Fintype.card ι : ℂ) * τ.tr (f i0 i0) = 1 := by
    have hii : ∀ i, τ.tr (f i i) = τ.tr (f i0 i0) := fun i => by
      rw [← hmulij i i0 i, τ.tr_mul_comm (hfs _ _) (hfs _ _), hmulij]
    have := congrArg τ.tr hf.sum_diag
    rw [map_sum, tr_one] at this
    simp only [hii, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact this
  set t := (τ.tr p).re with ht
  have hpos : ∀ c : ℝ, 0 ≤ (τ.tr (X * X)).re - 2 * c * t + c ^ 2 * (τ.tr (f i0 i0)).re := by
    intro c
    have h0 := τ.re_tr_nonneg (star_mul_self_nonneg (X - (c : ℂ) • f i0 i0))
    have hexp : star (X - (c : ℂ) • f i0 i0) * (X - (c : ℂ) • f i0 i0) =
        X * X - (2 * (c : ℂ)) • X + ((c : ℂ) ^ 2) • f i0 i0 := by
      rw [star_sub, star_smul, hXsa, hes, Complex.star_def, Complex.conj_ofReal]
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hXe, heX, hee]
      module
    rw [hexp, map_add, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, htrX] at h0
    have e1 : ((2 * (c : ℂ)) * τ.tr p).re = 2 * c * t := by
      rw [ht]; simp [Complex.mul_re]
    have e2 : (((c : ℂ) ^ 2) * τ.tr (f i0 i0)).re = c ^ 2 * (τ.tr (f i0 i0)).re := by
      rw [show ((c : ℂ) ^ 2) = ((c ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    rw [Complex.add_re, Complex.sub_re, e1, e2] at h0
    exact h0
  set k := Fintype.card ι with hkdef
  have hk : 0 < k := Fintype.card_pos_iff.mpr ⟨i0⟩
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have htre' : (τ.tr (f i0 i0)).re = 1 / k := by
    have := congrArg Complex.re htre
    simp [Complex.mul_re] at this
    field_simp; linarith
  have ht0 : 0 ≤ t := τ.re_tr_nonneg hpP.nonneg
  have := hpos (k * t)
  rw [htre'] at this
  have h3 : t * (1 - k * t) ≥ 0 := by
    have : 0 ≤ t - 2 * (k * t) * t + (k * t) ^ 2 * (1 / k) := le_trans this (by linarith [htrXX])
    field_simp at this ⊢
    nlinarith [this]
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simp
  · nlinarith [h3, h]

/-- **No nonzero abelian projection** (`thm:no-abelian-dyadic`, item K2; Theorem K2 of
`reports/c6b-paper-proofs.md`, §3): in a set `s` of operators closed under products and adjoints,
with a faithful tracial vector functional `τ` and unital matrix units in `s` of every size `2ⁿ`, a
projection `p ∈ s` with `(p x p)(p y p) = (p y p)(p x p)` for all `x, y ∈ s` is `0`. -/
theorem eq_zero_of_dyadicUnits (τ : VecTrace s) (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s)
    (hstar : ∀ x ∈ s, star x ∈ s)
    (hunits : ∀ n : ℕ, ∃ f : (Fin n → Fin 2) → (Fin n → Fin 2) → H →L[ℂ] H,
      IsMatUnits f ∧ ∀ i j, f i j ∈ s)
    {p : H →L[ℂ] H} (hpP : IsStarProjection p) (hps : p ∈ s)
    (hab : ∀ x ∈ s, ∀ y ∈ s, p * x * p * (p * y * p) = p * y * p * (p * x * p)) : p = 0 := by
  have hbound : ∀ n : ℕ, (2 : ℝ) ^ n * (τ.tr p).re ≤ 1 := fun n => by
    obtain ⟨f, hf, hfs⟩ := hunits n
    have := τ.card_mul_re_tr_le_one hmul hstar (fun _ => 0) hf hfs hpP hps hab
    simpa [Fintype.card_fun, Fintype.card_fin] using this
  have ht0 : 0 ≤ (τ.tr p).re := τ.re_tr_nonneg hpP.nonneg
  have ht : (τ.tr p).re = 0 := by
    refine le_antisymm (not_lt.mp fun h => ?_) ht0
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (τ.tr p).re) (by norm_num : (1 : ℝ) < 2)
    have := hbound n
    rw [div_lt_iff₀ h] at hn
    linarith
  have hsq : τ.tr p = ((∑ k, ‖p (τ.g k)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← tr_star_mul_self, hpP.isSelfAdjoint.star_eq, hpP.isIdempotentElem.eq]
  rw [hsq, Complex.ofReal_re] at ht
  refine τ.separating p hps fun k => ?_
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖p (τ.g k)‖)).mp ht k
    (Finset.mem_univ k)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

end VecTrace

/-! ## Finite pairs with dyadic matrix units -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-- The first player's operators are closed under products. -/
theorem mul_mem_opsA {x y : M.H →L[ℂ] M.H} (hx : x ∈ M.opsA) (hy : y ∈ M.opsA) :
    x * y ∈ M.opsA := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

/-- The first player's operators are closed under adjoints. -/
theorem star_mem_opsA {x : M.H →L[ℂ] M.H} (hx : x ∈ M.opsA) : star x ∈ M.opsA := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨star a, by simp only [map_star]⟩

/-- **No nonzero abelian projection among the first player's operators** (`thm:no-abelian-dyadic`,
item K′; Theorem K′ of `reports/c6b-paper-proofs.md`, §3): in a finite pair whose first algebra has
unital dyadic matrix units, a projection `r` of the first player's operators with
`(r x r)(r y r) = (r y r)(r x r)` for all of them is `0`. The hypothesis `hII` of
`povm_orthogonalization_finitePair` is `fun r hr => hM.eq_zero_of_abelianA hU hr`. -/
theorem IsFinitePair.eq_zero_of_abelianA (hM : M.IsFinitePair) (hU : HasDyadicUnits 𝒜)
    {r : M.H →L[ℂ] M.H} (hr : r ∈ M.opsA) (hrP : IsStarProjection r)
    (hab : ∀ x ∈ M.opsA, ∀ y ∈ M.opsA, r * x * r * (r * y * r) = r * y * r * (r * x * r)) :
    r = 0 := by
  obtain ⟨τ⟩ := hM.traceA
  refine τ.eq_zero_of_dyadicUnits (fun _ hx _ hy => mul_mem_opsA hx hy)
    (fun _ hx => star_mem_opsA hx) (fun n => ?_) hrP hr hab
  obtain ⟨e, he⟩ := hU n
  exact ⟨_, he.map (M.π.comp M.πA), fun i j => ⟨e i j, rfl⟩⟩

/-- **No nonzero abelian projection among the second player's operators** (`thm:no-abelian-dyadic`,
item K′): the same for the second algebra, through the exchange of the players. -/
theorem IsFinitePair.eq_zero_of_abelianB (hM : M.IsFinitePair) (hU : HasDyadicUnits ℬ)
    {r : M.H →L[ℂ] M.H} (hr : r ∈ M.opsB) (hrP : IsStarProjection r)
    (hab : ∀ x ∈ M.opsB, ∀ y ∈ M.opsB, r * x * r * (r * y * r) = r * y * r * (r * x * r)) :
    r = 0 :=
  hM.swap.eq_zero_of_abelianA (M := M.swap) hU hr hrP hab

/-- **A dyadic pair** (`def:dyadic-pair`): a finite pair whose two algebras have unital matrix units
of every size `2ⁿ`. Neither player's operators contain a nonzero abelian projection
(`IsDyadicPair.eq_zero_of_abelianA`, `.eq_zero_of_abelianB`). -/
structure IsDyadicPair (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop where
  /-- The model is a finite pair. -/
  isFinitePair : M.IsFinitePair
  /-- The first player's algebra has unital dyadic matrix units. -/
  unitsA : HasDyadicUnits 𝒜
  /-- The second player's algebra has unital dyadic matrix units. -/
  unitsB : HasDyadicUnits ℬ

namespace IsDyadicPair

/-- **A dyadic pair with the players exchanged is a dyadic pair** (`lem:dyadic-pair-closure`). -/
theorem swap (h : M.IsDyadicPair) : M.swap.IsDyadicPair :=
  ⟨h.isFinitePair.swap, h.unitsB, h.unitsA⟩

/-- **An ancilla extension of a dyadic pair is a dyadic pair** (`lem:dyadic-pair-closure`), for
nonempty registers: the units of the extension's algebras are the scalar diagonals of those of the
model. -/
theorem expand (h : M.IsDyadicPair) {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Nonempty α] [Nonempty β] (e : α × β → ℂ) : (M.expand e).IsDyadicPair :=
  ⟨h.isFinitePair.expand e, h.unitsA.matrix α, h.unitsB.matrix β⟩

/-- **No nonzero abelian projection among the first player's operators of a dyadic pair**
(`lem:dyadic-pair-closure`), in the form of the hypothesis `hII` of
`povm_orthogonalization_finitePair`. -/
theorem eq_zero_of_abelianA (h : M.IsDyadicPair) {r : M.H →L[ℂ] M.H} (hr : r ∈ M.opsA)
    (hrP : IsStarProjection r)
    (hab : ∀ x ∈ M.opsA, ∀ y ∈ M.opsA, r * x * r * (r * y * r) = r * y * r * (r * x * r)) :
    r = 0 :=
  h.isFinitePair.eq_zero_of_abelianA h.unitsA hr hrP hab

/-- **No nonzero abelian projection among the second player's operators of a dyadic pair**
(`lem:dyadic-pair-closure`). -/
theorem eq_zero_of_abelianB (h : M.IsDyadicPair) {r : M.H →L[ℂ] M.H} (hr : r ∈ M.opsB)
    (hrP : IsStarProjection r)
    (hab : ∀ x ∈ M.opsB, ∀ y ∈ M.opsB, r * x * r * (r * y * r) = r * y * r * (r * x * r)) :
    r = 0 :=
  h.isFinitePair.eq_zero_of_abelianB h.unitsB hr hrP hab

end IsDyadicPair

end BipartiteModel

/-! ## Values in dyadic pairs -/

/-- **`ω_co` is approached by projective strategies in dyadic pairs** (`def:dyadic-pair`; proved as
`lem:co-value-finite-pair`): below `ω_co(G)`, and above `0`, lies the value of a projective strategy
for `G` in a dyadic pair (`BipartiteModel.IsDyadicPair`) on a Hilbert space of `Type`. Proved from
Lin's tracial density and an amplification by the twisted Pauli algebra
(`MIPRE.Repetition.commutingFinitePairApprox`). -/
def CommutingFinitePairApprox : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G : Game X Y A B) {t : ℝ},
    0 ≤ t → t < commutingOperatorValue G →
      ∃ (𝒞 𝒜 ℬ : Type) (_ : Ring 𝒞) (_ : StarRing 𝒞) (_ : Algebra ℂ 𝒞) (_ : Ring 𝒜)
        (_ : StarRing 𝒜) (_ : Algebra ℂ 𝒜) (_ : Ring ℬ) (_ : StarRing ℬ) (_ : Algebra ℂ ℬ)
        (_ : PartialOrder 𝒜) (_ : StarOrderedRing 𝒜) (_ : PartialOrder ℬ)
        (_ : StarOrderedRing ℬ) (_ : StarModule ℂ 𝒜) (_ : StarProper 𝒜) (_ : StarModule ℂ ℬ)
        (_ : StarProper ℬ) (M : BipartiteModel.{0} 𝒞 𝒜 ℬ),
        M.IsDyadicPair ∧ ∃ S : M.ProjStrat G, t < S.value

end MIPRE

end
