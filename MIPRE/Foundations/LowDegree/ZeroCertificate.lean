/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.LowDegree.ZeroBasis
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Projection
public import MIPRE.Tactics

@[expose] public section

/-!
# Linear certificates for vanishing on the Boolean cube

`exists_zero_basis` (`prop:zero-basis`) gives, for a polynomial of individual degree at most `d`
vanishing on the Boolean cube, certificates `c_i` of individual degree at most `d` with
`f = Σ_i c_i · X_i (1 - X_i)`. Paper II's answer reduction needs them to be chosen *linearly*
in `f` (the proof of prop:completeness_and_soundness_of_PCP_for_V_n, II:9156, with the explicit
`Div` and `Mod`): the honest PCP's linear part must be `F₂`-linear in the linear answers. Any
linear right inverse of `c ↦ Σ_i c_i X_i (1 - X_i)` on the vanishing polynomials, composed with
a linear projection onto them, serves (`cert`): `cert_sum` on vanishing polynomials,
`degreeOf_cert_le` everywhere.
-/

namespace MIPRE.LowDegree

open MvPolynomial Finset

variable {F : Type*} [Field F] {m : ℕ}

theorem mem_restrictDegree_iff_degreeOf {p : MvPolynomial (Fin m) F} {d : ℕ} :
    p ∈ restrictDegree (Fin m) F d ↔ ∀ i, p.degreeOf i ≤ d := by
  rw [mem_restrictDegree]
  simp only [degreeOf_le_iff]
  exact ⟨fun h i s hs => h s hs i, fun h s hs i => h i s hs⟩

/-- The polynomials of individual degree at most `d` that vanish on the Boolean cube. -/
noncomputable def cubeVanishing (m d : ℕ) : Submodule F (MvPolynomial (Fin m) F) :=
  restrictDegree (Fin m) F d ⊓
    ⨅ y : Fin m → Bool, LinearMap.ker (aeval (pt y : Fin m → F)).toLinearMap

theorem mem_cubeVanishing {d : ℕ} {f : MvPolynomial (Fin m) F} :
    f ∈ cubeVanishing m d ↔ (∀ i, f.degreeOf i ≤ d) ∧ ∀ y : Fin m → Bool, eval (pt y) f = 0 := by
  simp [cubeVanishing, mem_restrictDegree_iff_degreeOf, Submodule.mem_iInf]

/-- `c ↦ Σ_i c_i · X_i (1 - X_i)`, on tuples of polynomials of individual degree at most `d`. -/
noncomputable def certSum (m d : ℕ) :
    (Fin m → restrictDegree (Fin m) F d) →ₗ[F] MvPolynomial (Fin m) F :=
  ∑ i : Fin m, (LinearMap.mulRight F (cubeZero i : MvPolynomial (Fin m) F)).comp
    ((restrictDegree (Fin m) F d).subtype.comp (LinearMap.proj i))

theorem certSum_apply {d : ℕ} (c : Fin m → restrictDegree (Fin m) F d) :
    certSum m d c = ∑ i, (c i : MvPolynomial (Fin m) F) * cubeZero i := by
  simp [certSum]

/-- The tuples whose certificate sum vanishes on the cube. -/
noncomputable def certDomain (m d : ℕ) : Submodule F (Fin m → restrictDegree (Fin m) F d) :=
  (cubeVanishing m d).comap (certSum m d)

/-- The certificate sum, onto the vanishing polynomials. -/
noncomputable def certSum' (m d : ℕ) : certDomain (F := F) m d →ₗ[F] cubeVanishing (F := F) m d :=
  (certSum m d).restrict fun _ h => h

theorem certSum'_surjective (d : ℕ) : (certSum' (F := F) m d).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  rintro ⟨f, hf⟩
  obtain ⟨hd, hv⟩ := mem_cubeVanishing.1 hf
  obtain ⟨c, hc, hcd⟩ := exists_zero_basis f hd hv
  let c' : Fin m → restrictDegree (Fin m) F d :=
    fun i => ⟨c i, mem_restrictDegree_iff_degreeOf.2 (hcd i)⟩
  have hsum : certSum m d c' = f := by rw [certSum_apply, hc]
  refine ⟨⟨c', ?_⟩, ?_⟩
  · change certSum m d c' ∈ cubeVanishing m d
    rw [hsum]; exact hf
  · apply Subtype.ext
    exact hsum

/-- **The linear certificate map**: on a polynomial of individual degree at most `d` that vanishes
on the Boolean cube, certificates of individual degree at most `d` (`cert_sum`), chosen linearly in
the polynomial. -/
noncomputable def cert (m d : ℕ) : MvPolynomial (Fin m) F →ₗ[F] (Fin m → MvPolynomial (Fin m) F) :=
  let Ψ := Classical.choose
    (LinearMap.exists_rightInverse_of_surjective (certSum' (F := F) m d) (certSum'_surjective d))
  let hq := Classical.choose_spec (Submodule.exists_isCompl (cubeVanishing (F := F) m d))
  let π := (cubeVanishing (F := F) m d).projectionOnto _ hq
  LinearMap.pi (fun i => (restrictDegree (Fin m) F d).subtype.comp (LinearMap.proj i)) ∘ₗ
    (certDomain (F := F) m d).subtype ∘ₗ Ψ ∘ₗ π

theorem degreeOf_cert_le {d : ℕ} (f : MvPolynomial (Fin m) F) (i j : Fin m) :
    (cert m d f i).degreeOf j ≤ d := by
  unfold cert
  dsimp only
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, Submodule.coe_subtype,
    LinearMap.coe_proj, Function.eval]
  exact mem_restrictDegree_iff_degreeOf.1 (Subtype.property _) j

theorem cert_sum {d : ℕ} {f : MvPolynomial (Fin m) F} (hf : f ∈ cubeVanishing m d) :
    ∑ i, cert m d f i * cubeZero i = f := by
  unfold cert
  dsimp only
  set Ψ := Classical.choose
    (LinearMap.exists_rightInverse_of_surjective (certSum' (F := F) m d) (certSum'_surjective d))
    with hΨ
  have hspec := Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective (certSum' (F := F) m d) (certSum'_surjective d))
  rw [← hΨ] at hspec
  set hq := Classical.choose_spec (Submodule.exists_isCompl (cubeVanishing (F := F) m d))
  have hπ : (cubeVanishing (F := F) m d).projectionOnto _ hq f = ⟨f, hf⟩ :=
    Submodule.projectionOnto_apply_left hq ⟨f, hf⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, Submodule.coe_subtype,
    LinearMap.coe_proj, Function.eval, hπ]
  have h := congrArg (fun g => ((g ⟨f, hf⟩ : cubeVanishing (F := F) m d) :
    MvPolynomial (Fin m) F)) hspec
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h
  refine Eq.trans ?_ h
  change _ = certSum m d (Ψ ⟨f, hf⟩ : Fin m → restrictDegree (Fin m) F d)
  rw [certSum_apply]

end MIPRE.LowDegree

end
