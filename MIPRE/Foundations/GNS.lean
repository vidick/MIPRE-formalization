/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.LinearMapCompletion
import MIPRE.Foundations.CommutingOperator

/-!
# The GNS construction: from a state on a `⋆`-algebra to a commuting-operator strategy

The Gelfand–Naimark–Segal construction, in the form the Tsirelson campaign needs
(`planning/tsirelson-campaign.md`, §3.2): a state `L` on a complex `⋆`-algebra `P`, together
with elements `e x a`, `f y b` of `P` satisfying the defining relations of a pair of
commuting POVM families *under `L`*, yields a `MIPRE.CommutingOperatorStrategy` whose
correlation is `Re L (e x a * f y b)`. The module is generic in `P`; it is instantiated at
the free `⋆`-algebra on the generators of a game elsewhere.

The construction has three layers.

**Abstract GNS.** A positive semidefinite Hermitian sesquilinear form `β` on a complex
vector space `V` (`PSDForm`) makes the type synonym `Pre β` of `V` a pre-inner-product space
(`PreInnerProductSpace.Core`, `InnerProductSpace.ofCore`). Its null vectors have norm zero
but need not vanish, so `Pre β` is not `T0`; its completion `H β` is a Hilbert space, into
which `ι : V → H β` maps with dense range (`denseRange_ι`), killing every null vector
(`ι_eq_zero_of_null`). A linear map `T` of `V` that is bounded for the seminorm of `β`
(`Bdd`) lifts to a continuous operator `lift β T` on `H β`, with `lift β T (ι v) = ι (T v)`
(`lift_ι`). Identities between lifts are checked on the dense image of `ι`, where it suffices
that they hold up to null vectors: `lift_eq_of_null`, `sum_lift_eq_one`, `commute_lift`.
A lift is positive as soon as `T` is symmetric and positive for `β` (`lift_isPositive`).

**States.** A state on `P` (`State`) is a `ℂ`-linear `L : P → ℂ` with `L 1 = 1`,
`L (a⋆) = conj (L a)` and `0 ≤ Re L (a⋆ a)`. Its GNS form is `⟨a, b⟩ = L (a⋆ b)`
(`State.form`). Left multiplication by `g` is a contraction as soon as
`Re L (s⋆ (1 - g⋆ g) s) ≥ 0` for every `s` (`State.bdd_mulLeft`), and for an effect `g` of a
family that is positive under `L` and sums to one under `L`, this holds by
`1 - g² = (1 - g) + g (1 - g) g + (1 - g) g (1 - g)` (`State.contraction_of_povm`).
A relation `ρ` with `L (u ρ v) = 0` for all `u, v` makes every `ρ s` null
(`State.null_of_ideal`), which turns the POVM and commutation relations in `P` into the
corresponding operator identities on `H` (`State.sum_lift_mulLeft`,
`State.commute_lift_mulLeft`). The cyclic vector `ι 1` is a unit vector (`State.norm_ι_one`).

**The strategy.** `GenData` records the families `e`, `f` and the conditions on them;
`GenData.strategy` is the resulting commuting-operator strategy on `H`, with state `ι 1` and
operators the lifts of left multiplication by `e x a` and `f y b`, and
`GenData.strategy_correlation` computes its correlation to be `Re L (e x a * f y b)`.

All carriers live in `Type`, since the Hilbert space of a `CommutingOperatorStrategy` does.

## Main declarations

* `PSDForm`, `Pre`, `H`, `ι`, `denseRange_ι`, `ι_eq_zero_of_null`;
* `Bdd`, `lift`, `lift_ι`, `lift_eq_of_null`, `sum_lift_eq_one`, `commute_lift`,
  `lift_isPositive`;
* `State`, `State.form`, `State.bdd_mulLeft`, `State.contraction_of_povm`,
  `State.null_of_ideal`, `State.sum_lift_mulLeft`, `State.commute_lift_mulLeft`,
  `State.norm_ι_one`;
* `GenData`, `GenData.strategy`, `GenData.strategy_correlation`.
-/

open scoped InnerProductSpace ComplexConjugate
open UniformSpace Completion

namespace MIPRE.GNS

/-! ## Abstract GNS on a positive semidefinite form -/

/-- A positive semidefinite Hermitian sesquilinear form on a complex vector space `V`,
conjugate-linear in the first argument. -/
structure PSDForm (V : Type) [AddCommGroup V] [Module ℂ V] where
  /-- The form. -/
  B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ
  /-- The form is Hermitian. -/
  conj_symm : ∀ u v, conj (B v u) = B u v
  /-- The form is positive semidefinite. -/
  re_nonneg : ∀ v, 0 ≤ (B v v).re

variable {V : Type} [AddCommGroup V] [Module ℂ V] (β : PSDForm V)

/-- The type synonym of `V` carrying the pre-inner product and the seminorm of `β`. -/
@[nolint unusedArguments]
def Pre (_β : PSDForm V) : Type := V

/-- The additive group of `V`. -/
instance : AddCommGroup (Pre β) := inferInstanceAs (AddCommGroup V)

/-- The complex vector space structure of `V`. -/
instance : Module ℂ (Pre β) := inferInstanceAs (Module ℂ V)

/-- The identity `V ≃ Pre β`. -/
def toPre : V ≃ₗ[ℂ] Pre β := LinearEquiv.refl ℂ V

/-- The identity `Pre β ≃ V`. -/
def ofPre : Pre β ≃ₗ[ℂ] V := (toPre β).symm

/-- `toPre` inverts `ofPre`. -/
@[simp] theorem toPre_ofPre (a : Pre β) : toPre β (ofPre β a) = a := rfl

/-- `ofPre` inverts `toPre`. -/
@[simp] theorem ofPre_toPre (a : V) : ofPre β (toPre β a) = a := rfl

/-- The pre-inner-product core of `β` on `Pre β`. -/
noncomputable abbrev core : PreInnerProductSpace.Core ℂ (Pre β) where
  inner a b := β.B (ofPre β a) (ofPre β b)
  conj_inner_symm a b := β.conj_symm _ _
  re_inner_nonneg a := β.re_nonneg _
  add_left a b c := by simp only [map_add, LinearMap.add_apply]
  smul_left a b r := by
    rw [LinearEquiv.map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

/-- The seminorm of `β`, `‖a‖ = √(Re β a a)`. -/
noncomputable instance : SeminormedAddCommGroup (Pre β) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core β)

/-- The pre-inner product `⟪a, b⟫ = β a b`. -/
noncomputable instance : InnerProductSpace ℂ (Pre β) :=
  InnerProductSpace.ofCore (core β)

/-- The inner product of `Pre β` is the form `β`. -/
theorem pre_inner_def (a b : Pre β) : ⟪a, b⟫_ℂ = β.B (ofPre β a) (ofPre β b) := rfl

/-- The seminorm of `Pre β` is `√(Re β a a)`. -/
theorem pre_norm_def (a : Pre β) : ‖a‖ = √(β.B (ofPre β a) (ofPre β a)).re := rfl

/-- The GNS Hilbert space of `β`: the completion of `Pre β`. -/
abbrev H := Completion (Pre β)

/-- The canonical map `V → H β`. -/
noncomputable def ι (v : V) : H β := ((toPre β v : Pre β) : H β)

/-- The inner product of two images of `ι` is the form `β`. -/
theorem inner_ι (u v : V) : ⟪ι β u, ι β v⟫_ℂ = β.B u v := by
  rw [ι, ι, inner_coe, pre_inner_def, ofPre_toPre, ofPre_toPre]

/-- The norm of an image of `ι` is `√(Re β v v)`. -/
theorem norm_ι (v : V) : ‖ι β v‖ = √(β.B v v).re := by
  rw [ι, norm_coe, pre_norm_def, ofPre_toPre]

/-- `ι` is additive. -/
theorem ι_add (u v : V) : ι β (u + v) = ι β u + ι β v := by
  rw [ι, ι, ι, map_add, Completion.coe_add]

/-- `ι` is `ℂ`-linear. -/
theorem ι_smul (c : ℂ) (v : V) : ι β (c • v) = c • ι β v := by
  rw [ι, ι, LinearEquiv.map_smul, Completion.coe_smul]

/-- `ι` commutes with subtraction. -/
theorem ι_sub (u v : V) : ι β (u - v) = ι β u - ι β v := by
  rw [ι, ι, ι, map_sub, Completion.coe_sub]

/-- The image of `V` is dense in `H β`. -/
theorem denseRange_ι : DenseRange (ι β) := by
  have : Set.range (ι β) = Set.range ((↑) : Pre β → H β) := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨ofPre β x, rfl⟩
  rw [DenseRange, this]
  exact denseRange_coe

/-- A null vector of `β` maps to `0`. -/
theorem ι_eq_zero_of_null {v : V} (hv : β.B v v = 0) : ι β v = 0 := by
  rw [← norm_eq_zero, norm_ι, hv, Complex.zero_re, Real.sqrt_zero]

/-- Density induction on `H β`: a closed property that holds on the image of `ι` holds
everywhere. -/
theorem ι_induction {p : H β → Prop} (hp : IsClosed {x | p x}) (h : ∀ v, p (ι β v)) (x : H β) :
    p x :=
  induction_on x hp fun a => h (ofPre β a)

/-! ### Lifting operators -/

/-- A linear map of `V` bounded for the seminorm of `β`. -/
def Bdd (T : V →ₗ[ℂ] V) : Prop :=
  ∃ C : ℝ, ∀ v, (β.B (T v) (T v)).re ≤ C * (β.B v v).re

/-- A bounded linear map of `V`, as a continuous operator on `Pre β`. -/
noncomputable def liftPre (T : V →ₗ[ℂ] V) (hT : Bdd β T) : Pre β →L[ℂ] Pre β :=
  ((toPre β).toLinearMap ∘ₗ T ∘ₗ (ofPre β).toLinearMap).mkContinuousOfExistsBound <| by
    obtain ⟨C, hC⟩ := hT
    refine ⟨√(max C 0), fun x => ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, pre_norm_def,
      ofPre_toPre]
    rw [← Real.sqrt_mul (le_max_right _ _)]
    apply Real.sqrt_le_sqrt
    exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (β.re_nonneg _))

/-- A bounded linear map of `V`, as a continuous operator on the Hilbert space `H β`. -/
noncomputable def lift (T : V →ₗ[ℂ] V) (hT : Bdd β T) : H β →L[ℂ] H β :=
  (liftPre β T hT).completion

/-- The lift of `T` extends `T`: `lift β T (ι v) = ι (T v)`. -/
@[simp] theorem lift_ι (T : V →ₗ[ℂ] V) (hT : Bdd β T) (v : V) :
    lift β T hT (ι β v) = ι β (T v) := by
  rw [lift, ι, ContinuousLinearMap.completion_apply_coe]
  rfl

/-- Contractions for `β` are bounded. -/
theorem bdd_of_contraction (T : V →ₗ[ℂ] V) (hT : ∀ v, (β.B (T v) (T v)).re ≤ (β.B v v).re) :
    Bdd β T :=
  ⟨1, fun v => by simpa using hT v⟩

/-- The identity is bounded. -/
theorem bdd_id : Bdd β LinearMap.id := bdd_of_contraction β _ fun _ => le_rfl

/-- Two operators on `H β` that agree on the image of `ι` are equal. -/
theorem ext_ι {S S' : H β →L[ℂ] H β} (h : ∀ v, S (ι β v) = S' (ι β v)) : S = S' := by
  ext x
  refine ι_induction β (p := fun x => S x = S' x) ?_ h x
  exact isClosed_eq S.continuous S'.continuous

/-- The lift of the identity is the identity. -/
theorem lift_id : lift β LinearMap.id (bdd_id β) = 1 :=
  ext_ι β fun v => by
    rw [lift_ι]
    rfl

/-- Two bounded maps that agree up to null vectors have equal lifts. -/
theorem lift_eq_of_null (T T' : V →ₗ[ℂ] V) (hT : Bdd β T) (hT' : Bdd β T')
    (h : ∀ v, β.B ((T - T') v) ((T - T') v) = 0) : lift β T hT = lift β T' hT' :=
  ext_ι β fun v => by
    rw [lift_ι, lift_ι, ← sub_eq_zero, ← ι_sub, ← LinearMap.sub_apply]
    exact ι_eq_zero_of_null β (h v)

/-- Boundedness, restated through the seminorm of `Pre β`. -/
theorem bdd_iff_norm (T : V →ₗ[ℂ] V) :
    Bdd β T ↔ ∃ C : ℝ, ∀ v, ‖toPre β (T v)‖ ≤ C * ‖toPre β v‖ := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨√(max C 0), fun v => ?_⟩
    rw [pre_norm_def, pre_norm_def, ofPre_toPre, ofPre_toPre,
      ← Real.sqrt_mul (le_max_right _ _)]
    apply Real.sqrt_le_sqrt
    exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (β.re_nonneg _))
  · rintro ⟨C, hC⟩
    refine ⟨C ^ 2, fun v => ?_⟩
    have h0 : 0 ≤ ‖toPre β (T v)‖ := norm_nonneg _
    have hsq : ‖toPre β (T v)‖ ^ 2 ≤ (C * ‖toPre β v‖) ^ 2 := pow_le_pow_left₀ h0 (hC v) 2
    rw [mul_pow, pre_norm_def, pre_norm_def, ofPre_toPre, ofPre_toPre,
      Real.sq_sqrt (β.re_nonneg _), Real.sq_sqrt (β.re_nonneg _)] at hsq
    exact hsq

/-- Sums of bounded maps are bounded. -/
theorem Bdd.add {T T' : V →ₗ[ℂ] V} (hT : Bdd β T) (hT' : Bdd β T') : Bdd β (T + T') := by
  rw [bdd_iff_norm] at *
  obtain ⟨C, hC⟩ := hT
  obtain ⟨C', hC'⟩ := hT'
  refine ⟨C + C', fun v => ?_⟩
  rw [LinearMap.add_apply, map_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC v) (hC' v))

/-- Composites of bounded maps are bounded. -/
theorem Bdd.comp {T T' : V →ₗ[ℂ] V} (hT : Bdd β T) (hT' : Bdd β T') : Bdd β (T ∘ₗ T') := by
  obtain ⟨C, hC⟩ := hT
  obtain ⟨C', hC'⟩ := hT'
  refine ⟨max C 0 * C', fun v => ?_⟩
  rw [LinearMap.comp_apply, mul_assoc]
  exact (hC _).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (β.re_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (hC' v) (le_max_right _ _)))

/-- The lift of a sum is the sum of the lifts. -/
theorem lift_add {T T' : V →ₗ[ℂ] V} (hT : Bdd β T) (hT' : Bdd β T') :
    lift β (T + T') (hT.add β hT') = lift β T hT + lift β T' hT' :=
  ext_ι β fun v => by
    rw [_root_.add_apply, lift_ι, lift_ι, lift_ι, LinearMap.add_apply, ι_add]

/-- The lift of a composite is the product of the lifts. -/
theorem lift_comp {T T' : V →ₗ[ℂ] V} (hT : Bdd β T) (hT' : Bdd β T') :
    lift β (T ∘ₗ T') (hT.comp β hT') = lift β T hT * lift β T' hT' :=
  ext_ι β fun v => by
    rw [mul_apply_eq_comp, lift_ι, lift_ι, lift_ι, LinearMap.comp_apply]

/-- A finite sum of lifts, evaluated on the image of `ι`. -/
theorem sum_lift_ι {ι' : Type*} (s : Finset ι') (T : ι' → V →ₗ[ℂ] V) (hT : ∀ i, Bdd β (T i))
    (v : V) : (∑ i ∈ s, lift β (T i) (hT i)) (ι β v) = ι β ((∑ i ∈ s, T i) v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, _root_.zero_apply,
      LinearMap.zero_apply, ι, map_zero, Completion.coe_zero]
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, _root_.add_apply, ih,
      lift_ι, LinearMap.add_apply, ι_add]

/-- A family of bounded maps summing to the identity up to null vectors lifts to a family
summing to `1`. -/
theorem sum_lift_eq_one {ι' : Type*} [Fintype ι'] (T : ι' → V →ₗ[ℂ] V) (hT : ∀ i, Bdd β (T i))
    (h : ∀ v, β.B ((∑ i, T i) v - v) ((∑ i, T i) v - v) = 0) :
    ∑ i, lift β (T i) (hT i) = 1 :=
  ext_ι β fun v => by
    rw [sum_lift_ι, one_apply_eq_self, ← sub_eq_zero, ← ι_sub]
    exact ι_eq_zero_of_null β (h v)

/-- Two bounded maps commuting up to null vectors have commuting lifts. -/
theorem commute_lift {T T' : V →ₗ[ℂ] V} (hT : Bdd β T) (hT' : Bdd β T')
    (h : ∀ v, β.B (T (T' v) - T' (T v)) (T (T' v) - T' (T v)) = 0) :
    Commute (lift β T hT) (lift β T' hT') := by
  change lift β T hT * lift β T' hT' = lift β T' hT' * lift β T hT
  refine ext_ι β fun v => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, lift_ι, lift_ι, lift_ι,
    lift_ι, ← sub_eq_zero, ← ι_sub]
  exact ι_eq_zero_of_null β (h v)

/-- The lift of a map that is symmetric and positive for `β` is a positive operator. -/
theorem lift_isPositive (T : V →ₗ[ℂ] V) (hT : Bdd β T)
    (hsymm : ∀ u v, β.B (T u) v = β.B u (T v)) (hpos : ∀ v, 0 ≤ (β.B v (T v)).re) :
    (lift β T hT).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · change ⟪lift β T hT x, y⟫_ℂ = ⟪x, lift β T hT y⟫_ℂ
    induction x, y using induction_on₂ with
    | hp =>
      exact isClosed_eq (((lift β T hT).continuous.comp continuous_fst).inner continuous_snd)
        (continuous_fst.inner ((lift β T hT).continuous.comp continuous_snd))
    | ih a b =>
      change ⟪lift β T hT (ι β (ofPre β a)), ι β (ofPre β b)⟫_ℂ =
        ⟪ι β (ofPre β a), lift β T hT (ι β (ofPre β b))⟫_ℂ
      rw [lift_ι, lift_ι, inner_ι, inner_ι, hsymm]
  · change 0 ≤ RCLike.re ⟪lift β T hT x, x⟫_ℂ
    refine ι_induction β (p := fun x => 0 ≤ RCLike.re ⟪lift β T hT x, x⟫_ℂ) ?_ (fun v => ?_) x
    · exact isClosed_le continuous_const
        (RCLike.continuous_re.comp ((lift β T hT).continuous.inner continuous_id))
    · rw [lift_ι, inner_ι, hsymm]
      exact hpos v

/-- A vector of `β`-norm one maps to a unit vector. -/
theorem norm_ι_eq_one {v₀ : V} (h : β.B v₀ v₀ = 1) : ‖ι β v₀‖ = 1 := by
  rw [norm_ι, h, Complex.one_re, Real.sqrt_one]

/-! ## States on a `⋆`-algebra -/

section StarAlg

variable {P : Type} [Ring P] [StarRing P] [Algebra ℂ P] [StarModule ℂ P]

/-- A state on a complex `⋆`-algebra: a normalized, Hermitian, positive linear functional.
Positivity is required on the squares `a⋆ a` only; the positivity of the generators is a
separate hypothesis (`GenData`). -/
structure State (P : Type) [Ring P] [StarRing P] [Algebra ℂ P] [StarModule ℂ P] where
  /-- The functional. -/
  L : P →ₗ[ℂ] ℂ
  /-- `L 1 = 1`. -/
  map_one : L 1 = 1
  /-- `L` is Hermitian. -/
  map_star : ∀ a, L (star a) = conj (L a)
  /-- `L` is positive on squares. -/
  nonneg : ∀ a, 0 ≤ (L (star a * a)).re

variable (φ : State P)

/-- The GNS form `⟨a, b⟩ = L (a⋆ b)` of a state. -/
noncomputable def State.form : PSDForm P where
  B := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun a b => φ.L (star a * b))
    (fun a a' b => by rw [star_add, add_mul, map_add])
    (fun c a b => by rw [star_smul, smul_mul_assoc, LinearMap.map_smul, starRingEnd_apply])
    (fun a b b' => by rw [mul_add, map_add])
    (fun c a b => by rw [mul_smul_comm, LinearMap.map_smul, RingHom.id_apply])
  conj_symm u v := by
    change conj (φ.L (star v * u)) = φ.L (star u * v)
    rw [← φ.map_star, star_mul, star_star]
  re_nonneg := φ.nonneg

/-- The GNS form of a state, applied. -/
@[simp] theorem State.form_B (a b : P) : φ.form.B a b = φ.L (star a * b) := rfl

/-- Left multiplication by `g` is bounded for the GNS form as soon as `1 - g⋆ g` is positive
under `L` after conjugation by every `s`. -/
theorem State.bdd_mulLeft (g : P) (hg : ∀ s, 0 ≤ (φ.L (star s * (1 - star g * g) * s)).re) :
    Bdd φ.form (LinearMap.mulLeft ℂ g) := by
  refine bdd_of_contraction _ _ fun v => ?_
  have h := hg v
  simp only [State.form_B, LinearMap.mulLeft_apply, star_mul]
  rw [mul_sub, sub_mul, mul_one, map_sub, Complex.sub_re, sub_nonneg] at h
  simpa only [mul_assoc] using h

/-- The lift of left multiplication by a self-adjoint `g`, positive under `L` after
conjugation, is a positive operator. -/
theorem State.lift_mulLeft_isPositive (g : P) (hg : Bdd φ.form (LinearMap.mulLeft ℂ g))
    (hsa : star g = g) (hpos : ∀ s, 0 ≤ (φ.L (star s * g * s)).re) :
    (lift φ.form (LinearMap.mulLeft ℂ g) hg).IsPositive := by
  refine lift_isPositive _ _ _ (fun u v => ?_) (fun v => ?_)
  · simp only [State.form_B, LinearMap.mulLeft_apply, star_mul, hsa, mul_assoc]
  · simpa only [State.form_B, LinearMap.mulLeft_apply, mul_assoc] using hpos v

/-- If `L (u ρ v) = 0` for all `u, v`, then every `ρ s` is a null vector of the GNS form. -/
theorem State.null_of_ideal (ρ : P) (hρ : ∀ u v, φ.L (u * ρ * v) = 0) (s : P) :
    φ.form.B (ρ * s) (ρ * s) = 0 := by
  rw [State.form_B, ← mul_assoc]
  exact hρ _ _

omit [StarRing P] [StarModule ℂ P] in
/-- A finite sum of left multiplications is left multiplication by the sum. -/
theorem sum_mulLeft_apply {ι' : Type*} (t : Finset ι') (g : ι' → P) (v : P) :
    (∑ i ∈ t, LinearMap.mulLeft ℂ (g i)) v = (∑ i ∈ t, g i) * v := by
  rw [LinearMap.sum_apply, Finset.sum_mul]
  rfl

/-- A family summing to one under `L` (`L (u (Σ g - 1) v) = 0`) lifts to operators summing
to `1`. -/
theorem State.sum_lift_mulLeft {ι' : Type*} [Fintype ι'] (g : ι' → P)
    (hg : ∀ i, Bdd φ.form (LinearMap.mulLeft ℂ (g i)))
    (hsum : ∀ u v, φ.L (u * (∑ i, g i - 1) * v) = 0) :
    ∑ i, lift φ.form (LinearMap.mulLeft ℂ (g i)) (hg i) = 1 := by
  refine sum_lift_eq_one _ _ hg fun v => ?_
  have hv : (∑ i, g i) * v - v = (∑ i, g i - 1) * v := by rw [sub_mul, one_mul]
  rw [sum_mulLeft_apply, hv]
  exact φ.null_of_ideal _ hsum v

/-- Two elements commuting under `L` (`L (u [g, g'] v) = 0`) lift to commuting operators. -/
theorem State.commute_lift_mulLeft (g g' : P) (hg : Bdd φ.form (LinearMap.mulLeft ℂ g))
    (hg' : Bdd φ.form (LinearMap.mulLeft ℂ g'))
    (hc : ∀ u v, φ.L (u * (g * g' - g' * g) * v) = 0) :
    Commute (lift φ.form _ hg) (lift φ.form _ hg') := by
  refine commute_lift _ hg hg' fun v => ?_
  simp only [LinearMap.mulLeft_apply]
  rw [← mul_assoc, ← mul_assoc, ← sub_mul]
  exact φ.null_of_ideal _ hc v

/-- The inner product of the images of `a` and `b` in the GNS space is `L (a⋆ b)`. -/
theorem State.inner_ι (a b : P) : ⟪ι φ.form a, ι φ.form b⟫_ℂ = φ.L (star a * b) :=
  GNS.inner_ι _ a b

/-- The cyclic vector `ι 1` is a unit vector. -/
theorem State.norm_ι_one : ‖ι φ.form (1 : P)‖ = 1 :=
  norm_ι_eq_one _ (by rw [State.form_B, star_one, one_mul, φ.map_one])

/-- The contraction condition for one effect of a family that is positive under `L` and sums
to one under `L`: `1 - g² = (1 - g) + g (1 - g) g + (1 - g) g (1 - g)`, and
`1 - g_i = Σ_{j ≠ i} g_j - (Σ g - 1)`. -/
theorem State.contraction_of_povm {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (g : ι' → P)
    (hsa : ∀ i, star (g i) = g i) (hpos : ∀ i s, 0 ≤ (φ.L (star s * g i * s)).re)
    (hsum : ∀ u v, φ.L (u * (∑ i, g i - 1) * v) = 0) (i : ι') (s : P) :
    0 ≤ (φ.L (star s * (1 - star (g i) * g i) * s)).re := by
  have h1 : ∀ t : P, 0 ≤ (φ.L (star t * (1 - g i) * t)).re := by
    intro t
    have hdecomp : (1 : P) - g i = (∑ j ∈ Finset.univ.erase i, g j) - (∑ j, g j - 1) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      abel
    rw [hdecomp, mul_sub, sub_mul, map_sub, hsum, sub_zero, Finset.mul_sum, Finset.sum_mul,
      map_sum, Complex.re_sum]
    exact Finset.sum_nonneg fun j _ => hpos j t
  have key : star s * (1 - star (g i) * g i) * s =
      star s * (1 - g i) * s + star (g i * s) * (1 - g i) * (g i * s) +
        star ((1 - g i) * s) * g i * ((1 - g i) * s) := by
    simp only [star_mul, star_sub, star_one, hsa]
    noncomm_ring
  rw [key, map_add, map_add, Complex.add_re, Complex.add_re]
  exact add_nonneg (add_nonneg (h1 s) (h1 _)) (hpos i _)

end StarAlg

/-! ## A commuting-operator strategy from a state -/

section Strategy

variable {P : Type} [Ring P] [StarRing P] [Algebra ℂ P] [StarModule ℂ P]
variable {X Y A B : Type} [Fintype A] [Fintype B]

/-- Elements `e x a`, `f y b` of `P` satisfying, under the state `φ`, the relations of two
commuting families of POVMs: self-adjoint, positive under `φ` after conjugation, summing to
one and commuting inside `φ (u · v)`. -/
structure GenData (P : Type) [Ring P] [StarRing P] [Algebra ℂ P] [StarModule ℂ P]
    (X Y A B : Type) [Fintype A] [Fintype B] (φ : State P) where
  /-- The first player's effects. -/
  e : X → A → P
  /-- The second player's effects. -/
  f : Y → B → P
  /-- The first player's effects are self-adjoint. -/
  e_sa : ∀ x a, star (e x a) = e x a
  /-- The second player's effects are self-adjoint. -/
  f_sa : ∀ y b, star (f y b) = f y b
  /-- The first player's effects are positive under `φ`. -/
  e_pos : ∀ x a s, 0 ≤ (φ.L (star s * e x a * s)).re
  /-- The second player's effects are positive under `φ`. -/
  f_pos : ∀ y b s, 0 ≤ (φ.L (star s * f y b * s)).re
  /-- The first player's effects sum to one under `φ`. -/
  e_sum : ∀ x u v, φ.L (u * (∑ a, e x a - 1) * v) = 0
  /-- The second player's effects sum to one under `φ`. -/
  f_sum : ∀ y u v, φ.L (u * (∑ b, f y b - 1) * v) = 0
  /-- The two players' effects commute under `φ`. -/
  comm : ∀ x y a b u v, φ.L (u * (e x a * f y b - f y b * e x a) * v) = 0

variable {φ : State P} (d : GenData P X Y A B φ)

/-- Left multiplication by a first-player effect is bounded. -/
theorem GenData.e_bdd (x : X) (a : A) : Bdd φ.form (LinearMap.mulLeft ℂ (d.e x a)) := by
  classical
  exact φ.bdd_mulLeft _ (φ.contraction_of_povm (d.e x) (d.e_sa x) (d.e_pos x) (d.e_sum x) a)

/-- Left multiplication by a second-player effect is bounded. -/
theorem GenData.f_bdd (y : Y) (b : B) : Bdd φ.form (LinearMap.mulLeft ℂ (d.f y b)) := by
  classical
  exact φ.bdd_mulLeft _ (φ.contraction_of_povm (d.f y) (d.f_sa y) (d.f_pos y) (d.f_sum y) b)

variable [Fintype X] [Fintype Y]

/-- **GNS**: the commuting-operator strategy of a state, on the GNS space of `φ`, with state
the cyclic vector `ι 1` and operators the lifts of left multiplication by the effects. -/
noncomputable def GenData.strategy : CommutingOperatorStrategy X Y A B where
  H := H φ.form
  ψ := ι φ.form 1
  ψ_norm := φ.norm_ι_one
  E x a := lift φ.form _ (d.e_bdd x a)
  F y b := lift φ.form _ (d.f_bdd y b)
  E_pos x a := φ.lift_mulLeft_isPositive _ _ (d.e_sa x a) (d.e_pos x a)
  F_pos y b := φ.lift_mulLeft_isPositive _ _ (d.f_sa y b) (d.f_pos y b)
  E_sum x := φ.sum_lift_mulLeft (d.e x) (d.e_bdd x) (d.e_sum x)
  F_sum y := φ.sum_lift_mulLeft (d.f y) (d.f_bdd y) (d.f_sum y)
  commutes x y a b := φ.commute_lift_mulLeft _ _ _ _ (fun u v => d.comm x y a b u v)

/-- **GNS**: the correlation of the strategy of a state is `Re L (e x a * f y b)`. -/
theorem GenData.strategy_correlation (x : X) (y : Y) (a : A) (b : B) :
    d.strategy.correlation x y a b = (φ.L (d.e x a * d.f y b)).re := by
  change (⟪ι φ.form 1, lift φ.form _ (d.e_bdd x a) (lift φ.form _ (d.f_bdd y b)
    (ι φ.form 1))⟫_ℂ).re = _
  rw [lift_ι, lift_ι, State.inner_ι]
  simp only [LinearMap.mulLeft_apply, star_one, one_mul, mul_one]

end Strategy

end MIPRE.GNS
