/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/GraphModulus.lean
-/
/-
# The graph of left multiplication by an `L²` vector (Stage D of `PLAN-modulus-family.md`)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

For a vector `x ∈ H = L²(M, τ)`, left multiplication by `x` is the (unbounded)
operator `ι a ↦ x·a = Rop a x` on the dense domain `ι(A)`. Its graph closure
`Γₓ ⊆ H ⊕ H` (in the block space `BH M (Fin 2)` of `VN/BlockOperators.lean`) is a
genuine graph (closability: `(0, η) ∈ Γₓ → η = 0`, from the adjoint identity
`⟪x·a, ι b⟫ = ⟪ι a, (Jx)·b⟫`). The orthogonal projection `P` onto `Γₓ` commutes
with the block-diagonal right action, so its four entries lie in `R(M)′ = vnAlg`.
The two entries we use are
`E := P₁₁ = TT*(1+TT*)⁻¹` (a positive contraction) and `C := P₀₁ = T*(1+TT*)⁻¹`,
with the three graph relations
`‖Cη‖² + ‖Eη‖² = ⟪η, Eη⟫`, `C*(ι a) = (1−E)(x·a)`, `C*C = E(1−E)`,
injectivity of `1 − E`, and the key formula for the Borel calculus of `E`:
`C g(E) Ω = J ((1−t)g)(E) x` (`Cop_bfc_traceVector`). Nothing here is a
manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.BlockOperators
import MIPRE.Background.Repetition.CommutingRepetition.VN.Commutation
import MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralProjection

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace GraphMod

open scoped InnerProductSpace Topology
open Filter Block

set_option linter.unusedSectionVars false

universe u

variable (M : StdTracialAlgebra.{u})

/-! ### Pairs in the block space `H ⊕ H` -/

/-- The pair `(v, v')` in `H²`. -/
noncomputable def pair (v v' : M.H) : BH M (Fin 2) :=
  embed M (Fin 2) 0 v + embed M (Fin 2) 1 v'

theorem pair_apply_zero (v v' : M.H) : pair M v v' 0 = v := by
  simp [pair, embed_apply]

theorem pair_apply_one (v v' : M.H) : pair M v v' 1 = v' := by
  simp [pair, embed_apply]

theorem pair_zero_left (v' : M.H) : pair M 0 v' = embed M (Fin 2) 1 v' := by
  rw [pair, map_zero, zero_add]

theorem decomp (w : BH M (Fin 2)) : w = pair M (w 0) (w 1) := by
  conv_lhs => rw [← sum_embed_proj_apply M (Fin 2) w]
  rw [Fin.sum_univ_two]
  rfl

theorem inner_pair_left (v v' : M.H) (w : BH M (Fin 2)) :
    ⟪pair M v v', w⟫_ℂ = ⟪v, w 0⟫_ℂ + ⟪v', w 1⟫_ℂ := by
  rw [pair, inner_add_left, inner_embed_left, inner_embed_left]

theorem inner_pair (v v' w w' : M.H) :
    ⟪pair M v v', pair M w w'⟫_ℂ = ⟪v, w⟫_ℂ + ⟪v', w'⟫_ℂ := by
  rw [inner_pair_left, pair_apply_zero, pair_apply_one]

theorem norm_pair_sq (v v' : M.H) : ‖pair M v v'‖ ^ 2 = ‖v‖ ^ 2 + ‖v'‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
    ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_pair, map_add]

/-- A block operator on a pair, through its four entries. -/
theorem apply_pair (T : BH M (Fin 2) →L[ℂ] BH M (Fin 2)) (v v' : M.H) :
    T (pair M v v') = pair M (entry M (Fin 2) T 0 0 v + entry M (Fin 2) T 0 1 v')
      (entry M (Fin 2) T 1 0 v + entry M (Fin 2) T 1 1 v') := by
  rw [decomp M (T (pair M v v'))]
  congr 1
  · show T (embed M (Fin 2) 0 v + embed M (Fin 2) 1 v') 0 = _
    rw [map_add, PiLp.add_apply]
    rfl
  · show T (embed M (Fin 2) 0 v + embed M (Fin 2) 1 v') 1 = _
    rw [map_add, PiLp.add_apply]
    rfl

theorem Rop_Rop (a b : M.A) (v : M.H) : M.Rop b (M.Rop a v) = M.Rop (a * b) v := by
  show (M.R (MulOpposite.op b) * M.R (MulOpposite.op a)) v = M.R (MulOpposite.op (a * b)) v
  rw [← map_mul, ← MulOpposite.op_mul]

theorem Rt_pair (b : M.A) (v v' : M.H) :
    Rt M (Fin 2) b (pair M v v') = pair M (M.Rop b v) (M.Rop b v') := by
  rw [apply_pair]
  simp [entry_Rt]

/-! ### The graph of left multiplication by `x` -/

variable (x : M.H)

/-- The generator `(ι a, x·a)` of the graph. -/
noncomputable def gen (a : M.A) : BH M (Fin 2) := pair M (M.ι a) (M.Rop a x)

/-- The closed graph `Γₓ`. -/
noncomputable def Γ : Submodule ℂ (BH M (Fin 2)) :=
  (Submodule.span ℂ (Set.range (gen M x))).topologicalClosure

theorem gen_mem (a : M.A) : gen M x a ∈ Γ M x :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)

theorem isClosed_Γ : IsClosed (Γ M x : Set (BH M (Fin 2))) :=
  Submodule.isClosed_topologicalClosure _

theorem Γ_le {N : Submodule ℂ (BH M (Fin 2))} (hN : IsClosed (N : Set (BH M (Fin 2))))
    (h : ∀ a, gen M x a ∈ N) : Γ M x ≤ N :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact h a)) hN

instance : CompleteSpace (Γ M x) := (isClosed_Γ M x).completeSpace_coe

instance : (Γ M x).HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The orthogonal projection onto the graph. -/
noncomputable def P : BH M (Fin 2) →L[ℂ] BH M (Fin 2) := (Γ M x).starProjection

theorem P_sa : IsSelfAdjoint (P M x) := isSelfAdjoint_starProjection _

theorem P_idem : P M x * P M x = P M x := Submodule.isIdempotentElem_starProjection _

theorem P_eq_self {w : BH M (Fin 2)} (hw : w ∈ Γ M x) : P M x w = w :=
  Submodule.starProjection_eq_self_iff.mpr hw

theorem mem_of_P_eq {w : BH M (Fin 2)} (hw : P M x w = w) : w ∈ Γ M x :=
  Submodule.starProjection_eq_self_iff.mp hw

theorem P_gen (a : M.A) : P M x (gen M x a) = gen M x a := P_eq_self M x (gen_mem M x a)

/-! ### Closability -/

/-- The adjoint identity on generators: `⟪x·a, ι b⟫ = ⟪ι a, (Jx)·b⟫`. -/
theorem inner_gen_key (a b : M.A) : ⟪M.Rop a x, M.ι b⟫_ℂ = ⟪M.ι a, M.Rop b (M.J x)⟫_ℂ := by
  have h1 : ⟪M.Rop a x, M.ι b⟫_ℂ = ⟪x, M.ι (b * star a)⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      M.star_Rop, show M.Rop (star a) (M.ι b) = M.ι (b * star a) from M.R_apply (star a) b]
  have h2 : ⟪M.ι a, M.Rop b (M.J x)⟫_ℂ = ⟪x, M.ι (b * star a)⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      M.star_Rop, show M.Rop (star b) (M.ι a) = M.ι (a * star b) from M.R_apply (star b) a,
      ← inner_conj_symm, M.inner_J_left, M.J_ι, inner_conj_symm, star_mul, star_star]
  rw [h1, h2]

/-- The vectors `(−(Jx)·b, ι b)` are orthogonal to the graph. -/
noncomputable def orthGen (b : M.A) : BH M (Fin 2) := pair M (-(M.Rop b (M.J x))) (M.ι b)

theorem inner_gen_orthGen (a b : M.A) : ⟪gen M x a, orthGen M x b⟫_ℂ = 0 := by
  rw [gen, orthGen, inner_pair, inner_neg_right, inner_gen_key]
  ring

theorem orthGen_mem (b : M.A) : orthGen M x b ∈ (Γ M x)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have : Γ M x ≤ (ℂ ∙ orthGen M x b)ᗮ :=
    Γ_le M x (Submodule.isClosed_orthogonal _) fun a =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (inner_gen_orthGen M x a b)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (this hw)

/-- **Closability**: the graph closure is a graph. -/
theorem closable {η : M.H} (h : embed M (Fin 2) 1 η ∈ Γ M x) : η = 0 := by
  refine M.ext_of_inner_ι fun b => ?_
  have := (Submodule.mem_orthogonal _ _).mp (orthGen_mem M x b) _ h
  rw [← pair_zero_left, orthGen, inner_pair, inner_zero_left, zero_add] at this
  rw [this, inner_zero_left]

/-! ### Right-action invariance and the entries of `P` -/

theorem Rt_gen (b a : M.A) : Rt M (Fin 2) b (gen M x a) = gen M x (a * b) := by
  rw [gen, gen, Rt_pair, Rop_Rop, show M.Rop b (M.ι a) = M.ι (a * b) from M.R_apply b a]

theorem Γ_invariant (b : M.A) {w : BH M (Fin 2)} (hw : w ∈ Γ M x) :
    Rt M (Fin 2) b w ∈ Γ M x := by
  have hcl : IsClosed ((Γ M x).comap (Rt M (Fin 2) b : BH M (Fin 2) →ₗ[ℂ] BH M (Fin 2)) :
      Set (BH M (Fin 2))) := by
    rw [Submodule.comap_coe, ContinuousLinearMap.coe_coe]
    exact (isClosed_Γ M x).preimage (Rt M (Fin 2) b).continuous
  have : Γ M x ≤ (Γ M x).comap (Rt M (Fin 2) b : BH M (Fin 2) →ₗ[ℂ] BH M (Fin 2)) :=
    Γ_le M x hcl fun a => by
      rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, Rt_gen]
      exact gen_mem M x _
  exact this hw

/-- An operator leaving a closed subspace and its orthogonal complement invariant commutes with
the orthogonal projection. -/
theorem starProjection_comm {K : Submodule ℂ (BH M (Fin 2))} [K.HasOrthogonalProjection]
    {A : BH M (Fin 2) →L[ℂ] BH M (Fin 2)} (hA : ∀ w ∈ K, A w ∈ K)
    (hA' : ∀ w ∈ K, star A w ∈ K) : A * K.starProjection = K.starProjection * A := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [Resolver.Douglas.mulA, Resolver.Douglas.mulA]
  symm
  have h1 : K.starProjection (A (K.starProjection w)) = A (K.starProjection w) :=
    Submodule.starProjection_eq_self_iff.mpr (hA _ (Submodule.starProjection_apply_mem _ _))
  have h2 : K.starProjection (A (w - K.starProjection w)) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
    exact (Submodule.mem_orthogonal _ _).mp (Submodule.sub_starProjection_mem_orthogonal w) _
      (hA' u hu)
  calc K.starProjection (A w)
      = K.starProjection (A (K.starProjection w) + A (w - K.starProjection w)) := by
        rw [← map_add, add_sub_cancel]
    _ = A (K.starProjection w) := by rw [map_add, h1, h2, add_zero]

theorem P_comm_Rt (b : M.A) : Rt M (Fin 2) b * P M x = P M x * Rt M (Fin 2) b :=
  starProjection_comm M (fun _ hw => Γ_invariant M x b hw) fun _ hw => by
    rw [star_Rt]; exact Γ_invariant M x (star b) hw

theorem P_mem_blockAlg : P M x ∈ blockAlg M (Fin 2) :=
  (mem_blockAlg_iff_comm M (Fin 2)).mpr (P_comm_Rt M x)

/-- `E = P₁₁ = TT*(1+TT*)⁻¹`. -/
noncomputable def Eop : M.H →L[ℂ] M.H := entry M (Fin 2) (P M x) 1 1

/-- `C = P₀₁ = T*(1+TT*)⁻¹`. -/
noncomputable def Cop : M.H →L[ℂ] M.H := entry M (Fin 2) (P M x) 0 1

theorem Eop_mem : Eop M x ∈ M.vnAlg := (mem_blockAlg_iff M (Fin 2)).mp (P_mem_blockAlg M x) 1 1

theorem Cop_mem : Cop M x ∈ M.vnAlg := (mem_blockAlg_iff M (Fin 2)).mp (P_mem_blockAlg M x) 0 1

theorem star_Cop_mem : star (Cop M x) ∈ M.vnAlg := star_mem (Cop_mem M x)

theorem entry_P_one_zero : entry M (Fin 2) (P M x) 1 0 = star (Cop M x) := by
  rw [Cop, ← entry_star, (P_sa M x).star_eq]

theorem Eop_sa : IsSelfAdjoint (Eop M x) := by
  rw [Eop, IsSelfAdjoint, ← entry_star, (P_sa M x).star_eq]

theorem P_embed_one (η : M.H) :
    P M x (embed M (Fin 2) 1 η) = pair M (Cop M x η) (Eop M x η) := by
  rw [← pair_zero_left, apply_pair]
  simp only [map_zero, zero_add]
  rfl

/-! ### The graph relations -/

/-- (R1) `‖Cη‖² + ‖Eη‖² = ⟪η, Eη⟫`. -/
theorem norm_Cop_sq_add (η : M.H) :
    ‖Cop M x η‖ ^ 2 + ‖Eop M x η‖ ^ 2 = (⟪η, Eop M x η⟫_ℂ).re := by
  have h1 : ‖P M x (embed M (Fin 2) 1 η)‖ ^ 2 = ‖Cop M x η‖ ^ 2 + ‖Eop M x η‖ ^ 2 := by
    rw [P_embed_one, norm_pair_sq]
  have h2 : (⟪embed M (Fin 2) 1 η, P M x (embed M (Fin 2) 1 η)⟫_ℂ).re
      = ‖P M x (embed M (Fin 2) 1 η)‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← BorelCalc.inner_sa (P_sa M x),
      ← Resolver.Douglas.mulA, P_idem]
    rfl
  have h3 : ⟪embed M (Fin 2) 1 η, P M x (embed M (Fin 2) 1 η)⟫_ℂ = ⟪η, Eop M x η⟫_ℂ := by
    rw [P_embed_one, ← pair_zero_left, inner_pair, inner_zero_left, zero_add]
  rw [← h1, ← h2, h3]

/-- (R2) `C*(ι a) = (1 − E)(x·a)`. -/
theorem star_Cop_ι (a : M.A) : star (Cop M x) (M.ι a) = (1 - Eop M x) (M.Rop a x) := by
  have h := P_gen M x a
  rw [gen, apply_pair] at h
  have h1 := congrArg (fun w => w 1) h
  simp only [pair_apply_one] at h1
  rw [entry_P_one_zero] at h1
  rw [ContinuousLinearMap.sub_apply, Resolver.Douglas.oneA]
  exact eq_sub_of_add_eq h1

/-- (R3) `C*C = E(1 − E)`. -/
theorem star_Cop_mul_Cop : star (Cop M x) * Cop M x = Eop M x * (1 - Eop M x) := by
  have h := congrArg (fun T => entry M (Fin 2) T 1 1) (P_idem M x)
  simp only [entry_mul, Fin.sum_univ_two, entry_P_one_zero] at h
  change star (Cop M x) * Cop M x + Eop M x * Eop M x = Eop M x at h
  rw [mul_sub, mul_one]
  exact eq_sub_of_add_eq h

theorem norm_Cop_apply_sq (η : M.H) :
    ‖Cop M x η‖ ^ 2 = (⟪η, (Eop M x * (1 - Eop M x)) η⟫_ℂ).re := by
  rw [← star_Cop_mul_Cop, Resolver.Douglas.mulA, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/-- Injectivity of `1 − E`. -/
theorem eq_zero_of_Eop_eq {ζ : M.H} (h : Eop M x ζ = ζ) : ζ = 0 := by
  have h1 := norm_Cop_sq_add M x ζ
  have h2 : (⟪ζ, ζ⟫_ℂ).re = ‖ζ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ζ
  rw [h, h2] at h1
  have hC : Cop M x ζ = 0 := by
    have : ‖Cop M x ζ‖ ^ 2 = 0 := by linarith
    simpa using this
  apply closable M x
  refine mem_of_P_eq M x ?_
  rw [P_embed_one, hC, h, pair_zero_left]

theorem Eop_nonneg : 0 ≤ Eop M x :=
  Resolver.Douglas.nonneg_of_re_inner (Eop_sa M x) fun ζ => by
    rw [← BorelCalc.inner_sa (Eop_sa M x), ← norm_Cop_sq_add]
    positivity

theorem norm_Eop_apply_le (ζ : M.H) : ‖Eop M x ζ‖ ≤ ‖ζ‖ := by
  have h1 := norm_Cop_sq_add M x ζ
  have h2 : (⟪ζ, Eop M x ζ⟫_ℂ).re ≤ ‖ζ‖ * ‖Eop M x ζ‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h3 : ‖Eop M x ζ‖ ^ 2 ≤ ‖ζ‖ * ‖Eop M x ζ‖ := by nlinarith [sq_nonneg ‖Cop M x ζ‖]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ‖Eop M x ζ‖ := (norm_nonneg _).trans_lt hlt
  nlinarith

theorem Eop_le_one : Eop M x ≤ 1 := by
  rw [← sub_nonneg]
  have hsa : IsSelfAdjoint (1 - Eop M x) := by
    rw [IsSelfAdjoint, star_sub, star_one, (Eop_sa M x).star_eq]
  refine Resolver.Douglas.nonneg_of_re_inner hsa fun ζ => ?_
  rw [ContinuousLinearMap.sub_apply, Resolver.Douglas.oneA, inner_sub_left, Complex.sub_re,
    ← BorelCalc.inner_sa (Eop_sa M x)]
  have h2 : (⟪ζ, Eop M x ζ⟫_ℂ).re ≤ ‖ζ‖ * ‖Eop M x ζ‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h3 : ‖ζ‖ * ‖Eop M x ζ‖ ≤ ‖ζ‖ * ‖ζ‖ :=
    mul_le_mul_of_nonneg_left (norm_Eop_apply_le M x ζ) (norm_nonneg _)
  have h4 : (⟪ζ, ζ⟫_ℂ).re = ‖ζ‖ * ‖ζ‖ := by
    rw [← sq]; exact inner_self_eq_norm_sq (𝕜 := ℂ) ζ
  linarith

theorem norm_Eop_le_one : ‖Eop M x‖ ≤ 1 :=
  StrongLimit.norm_le_one_of_nonneg_le_one (Eop_nonneg M x) (Eop_le_one M x)

/-- The spectrum of `E` lies in `[0, 1]`. -/
theorem spectrum_Eop_subset : spectrum ℝ (Eop M x) ⊆ Set.Icc 0 1 := by
  intro t ht
  refine ⟨spectrum_nonneg_of_nonneg (Eop_nonneg M x) ht, ?_⟩
  have hmem : (1 : ℝ) - t ∈ spectrum ℝ (algebraMap ℝ (M.H →L[ℂ] M.H) 1 - Eop M x) := by
    rw [← spectrum.singleton_sub_eq]
    exact ⟨1, Set.mem_singleton 1, t, ht, rfl⟩
  rw [map_one] at hmem
  linarith [spectrum_nonneg_of_nonneg (sub_nonneg.mpr (Eop_le_one M x)) hmem]

/-! ### The Borel calculus of `E` -/

/-- `t ↦ max 0 (min 1 t)`: a bounded continuous function equal to the identity on `[0, 1]`. -/
noncomputable def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp_continuous : Continuous clamp := by unfold clamp; fun_prop

theorem clamp_nonneg (t : ℝ) : 0 ≤ clamp t := le_max_left _ _

theorem clamp_le_one (t : ℝ) : clamp t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp_bdd : BorelCalc.Bdd clamp :=
  BorelCalc.Bdd.of_continuous clamp_continuous (C := 1) fun t =>
    abs_le.mpr ⟨by linarith [clamp_nonneg t], clamp_le_one t⟩

theorem one_sub_clamp_bdd : BorelCalc.Bdd fun t => 1 - clamp t :=
  (BorelCalc.Bdd.const 1).sub clamp_bdd

theorem clamp_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp t = t := by
  unfold clamp
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem clamp_zero : clamp 0 = 0 := clamp_of_mem ⟨le_rfl, zero_le_one⟩

theorem clamp_one : clamp 1 = 1 := clamp_of_mem ⟨zero_le_one, le_rfl⟩

/-- Local notation for the Borel calculus, spectral projections and spectral measures of `E`. -/
local notation "bE" => BorelCalc.bfc (Eop M x) (Eop_sa M x)
local notation "PE" => BorelCalc.P (Eop M x) (Eop_sa M x)

theorem vnAlg_strong_closed :
    ∀ (T : ℕ → M.H →L[ℂ] M.H) (L : M.H →L[ℂ] M.H), (∀ n, T n ∈ M.vnAlg) →
      (∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (L ξ))) → L ∈ M.vnAlg :=
  fun _ _ hT hL => M.mem_vnAlg_of_tendsto hT hL

theorem bE_mem {g : ℝ → ℝ} (hg : BorelCalc.Bdd g) : bE g ∈ M.vnAlg :=
  BorelCalc.bfc_mem_of_bdd _ _ M.vnAlg (vnAlg_strong_closed M) (Eop_mem M x) hg

theorem PE_mem (I : Set ℝ) : PE I ∈ M.vnAlg :=
  BorelCalc.P_mem _ _ M.vnAlg (vnAlg_strong_closed M) (Eop_mem M x) I

/-- `E = clamp(E)`. -/
theorem bE_clamp : bE clamp = Eop M x := by
  rw [BorelCalc.bfc_cfc _ _ clamp_bdd clamp_continuous,
    cfc_congr (fun t ht => clamp_of_mem (spectrum_Eop_subset M x ht)),
    cfc_id' ℝ (Eop M x) (Eop_sa M x)]

theorem one_sub_Eop_sa : IsSelfAdjoint (1 - Eop M x) := by
  rw [IsSelfAdjoint, star_sub, star_one, (Eop_sa M x).star_eq]

theorem one_sub_Eop_eq : 1 - Eop M x = bE fun t => 1 - clamp t := by
  have h : (fun t => 1 - clamp t) = (fun _ => (1 : ℝ)) - clamp := rfl
  rw [h, BorelCalc.bfc_sub _ _ (BorelCalc.Bdd.const 1) clamp_bdd, bE_clamp,
    BorelCalc.bfc_const, Complex.ofReal_one, one_smul]

theorem Eop_mul_bE {g : ℝ → ℝ} (hg : BorelCalc.Bdd g) :
    Eop M x * bE g = bE fun t => clamp t * g t := by
  calc Eop M x * bE g = bE clamp * bE g := by rw [bE_clamp]
    _ = bE fun t => clamp t * g t := (BorelCalc.bfc_mul _ _ clamp_bdd hg).symm

theorem bE_mul_Eop {g : ℝ → ℝ} (hg : BorelCalc.Bdd g) :
    bE g * Eop M x = bE fun t => g t * clamp t := by
  calc bE g * Eop M x = bE g * bE clamp := by rw [bE_clamp]
    _ = bE fun t => g t * clamp t := (BorelCalc.bfc_mul _ _ hg clamp_bdd).symm

theorem one_sub_Eop_mul_bE {g : ℝ → ℝ} (hg : BorelCalc.Bdd g) :
    (1 - Eop M x) * bE g = bE fun t => (1 - clamp t) * g t := by
  rw [one_sub_Eop_eq]
  exact (BorelCalc.bfc_mul _ _ one_sub_clamp_bdd hg).symm

theorem bE_mul_one_sub_Eop {g : ℝ → ℝ} (hg : BorelCalc.Bdd g) :
    bE g * (1 - Eop M x) = bE fun t => g t * (1 - clamp t) := by
  rw [one_sub_Eop_eq]
  exact (BorelCalc.bfc_mul _ _ hg one_sub_clamp_bdd).symm

/-- The spectral projection at `{1}` vanishes (`1 − E` is injective). -/
theorem PE_singleton_one : PE {1} = 0 := by
  ext ζ
  rw [ContinuousLinearMap.zero_apply]
  apply eq_zero_of_Eop_eq M x
  have h : Eop M x * PE {1} = PE {1} := by
    rw [BorelCalc.P, Eop_mul_bE M x (BorelCalc.Bdd.indicator (measurableSet_singleton 1))]
    congr 1
    funext t
    by_cases ht : t = 1
    · subst ht; simp [clamp_one]
    · simp [Set.indicator, ht]
  rw [← Resolver.Douglas.mulA, h]

/-- **The key formula**: `C g(E) Ω = J ((1 − t) g)(E) x` for bounded Borel `g`. -/
theorem Cop_bfc_traceVector {g : ℝ → ℝ} (hg : BorelCalc.Bdd g) :
    Cop M x (bE g M.traceVector) = M.J (bE (fun t => (1 - clamp t) * g t) x) := by
  have hg' : BorelCalc.Bdd fun t => (1 - clamp t) * g t := one_sub_clamp_bdd.mul hg
  refine M.ext_of_inner_ι fun b => ?_
  have h1 : ⟪Cop M x (bE g M.traceVector), M.ι b⟫_ℂ
      = ⟪bE g M.traceVector, (1 - Eop M x) (M.Rop b x)⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      star_Cop_ι]
  have hmem := bE_mem M x hg'
  rw [h1, BorelCalc.inner_sa (one_sub_Eop_sa M x), ← Resolver.Douglas.mulA,
    one_sub_Eop_mul_bE M x hg, ← BorelCalc.inner_sa (BorelCalc.bfc_isSelfAdjoint _ _ hg'),
    ← Resolver.Douglas.mulA, ← (M.mem_vnAlg_iff.mp hmem b), Resolver.Douglas.mulA,
    ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, M.star_Rop,
    M.Rop_traceVector, ← M.inner_J_J, M.J_ι, star_star]

/-- `x` has no mass at `{0}` (it lies in the closure of the range of `T`). -/
theorem PE_singleton_zero_apply : PE {0} x = 0 := by
  have hind := BorelCalc.Bdd.indicator (measurableSet_singleton (0 : ℝ))
  have hEP : Eop M x * PE {0} = 0 := by
    rw [BorelCalc.P, Eop_mul_bE M x hind]
    have hfun : (fun t => clamp t * ({0} : Set ℝ).indicator (1 : ℝ → ℝ) t) = 0 := by
      funext t
      by_cases ht : t = 0
      · subst ht; simp [clamp_zero]
      · simp [Set.indicator, ht]
    rw [hfun]
    exact BorelCalc.bfc_zero _ _
  have hCP : Cop M x * PE {0} = 0 := by
    ext ζ
    rw [ContinuousLinearMap.zero_apply, Resolver.Douglas.mulA]
    have hz : Eop M x (PE {0} ζ) = 0 := by
      rw [← Resolver.Douglas.mulA, hEP, ContinuousLinearMap.zero_apply]
    have h := norm_Cop_apply_sq M x (PE {0} ζ)
    rw [Resolver.Douglas.mulA, ContinuousLinearMap.sub_apply, Resolver.Douglas.oneA, hz,
      sub_zero, hz, inner_zero_right, Complex.zero_re] at h
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
  have hPC : PE {0} * star (Cop M x) = 0 := by
    have := congrArg star hCP
    rwa [star_mul, BorelCalc.star_P, star_zero] at this
  have hP1 : PE {0} * (1 - Eop M x) = PE {0} := by
    rw [BorelCalc.P, bE_mul_one_sub_Eop M x hind]
    congr 1
    funext t
    by_cases ht : t = 0
    · subst ht; simp [clamp_zero]
    · simp [Set.indicator, ht]
  have hRop1 : M.Rop 1 x = x := by
    show M.R (MulOpposite.op 1) x = x
    rw [MulOpposite.op_one, map_one, Resolver.Douglas.oneA]
  have hx : (1 - Eop M x) x = star (Cop M x) M.traceVector := by
    have h1 := star_Cop_ι M x 1
    rw [hRop1] at h1
    exact h1.symm
  calc PE {0} x = (PE {0} * (1 - Eop M x)) x := by rw [hP1]
    _ = (PE {0} * star (Cop M x)) M.traceVector := by
        rw [Resolver.Douglas.mulA, Resolver.Douglas.mulA, hx]
    _ = 0 := by rw [hPC, ContinuousLinearMap.zero_apply]

end GraphMod

end CommutingRepetition
