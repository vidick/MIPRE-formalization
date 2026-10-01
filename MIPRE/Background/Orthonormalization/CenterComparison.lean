/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Orthonormalization.CenterTraceClauses
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.Comparison
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.MatrixFactor
public import MIPRE.Background.Orthonormalization.Orthogonalization.MvN.PolarDecomp

@[expose] public section

/-!
# Comparison of projections, and the centre-valued trace of a von Neumann algebra with a vector trace

Two projections with the same centre-valued trace are Murray–von Neumann equivalent, in a von
Neumann algebra `M` with a faithful tracial vector functional and in the matrix algebras
`M_n(M)` (the comparison clauses `equiv_of_eq` and `equiv_of_eq_matrix` of the vendored
`IsCenterValuedTrace`). With `MIPRE/Background/Orthonormalization/CenterTrace.lean` this gives
field H3 of the structure-theory interface at the projection `1`
(`exists_isCenterValuedTrace`), for every such `M`, with no factor hypothesis.

* **Generalized comparison** (`mvNEquiv_of_map_eq`): for a von Neumann algebra `N` with a faithful
  positive tracial functional, and a linear map `Φ` that is tracial on `N`, compatible with left
  multiplication by central projections and faithful on projections, projections with the same
  image under `Φ` are equivalent. The vendored proof for factors (`MvN/Comparison.lean`,
  `mvNEquiv_of_trace_eq`) builds a maximal partial isometry `W` from `p` into `q` by a greedy
  chain; its factor hypothesis enters only to show that the complements `p - W* W` and
  `q - W W*` cannot both be nonzero. Here maximality gives `(q - W W*) y (p - W* W) = 0` for every
  `y ∈ N` (`exists_maximal_isPartialBetween`, through `exists_extension_of_mul_ne_zero`), so the
  central support `c` of `p - W* W` (`exists_centralSupport`) kills `q - W W*`, and applying `Φ`
  to `c (p - W* W) = p - W* W` and `c (q - W W*) = 0` shows that both complements have `Φ = 0`.
  The three vendored blocks that use the factor hypothesis are copied without it; the rest of
  `MvN/Comparison.lean` (partial isometries, the greedy step, strong limits of chains) is reused.
* **The instances**: `N = M` with `Φ = E`, and `N = M_n(M)` with `Φ X = ∑ᵢ E(Xᵢᵢ)` and the
  diagonal trace of `τ`, whose central projections are amplifications of central projections of
  `M` (`exists_eq_amplify_of_commute`, the first half of the vendored `matrixAlgebra_factor`).
-/

namespace MIPRE.Orthonormalization

open scoped ComplexOrder InnerProductSpace
open Orthogonalization Orthogonalization.MvN

universe u

/-! ### The three factor-dependent steps of the vendored comparison theorem, without a factor -/

section Comparison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The central support of a projection** `f ∈ N`: the projection `c` onto the closed span of
the vectors `y (f ξ)`, `y ∈ N`, is a central projection of `N` with `c f = f`, and every operator
`e` with `e y f = 0` for all `y ∈ N` vanishes on its range. This is the vendored corner lemma
`exists_mul_mul_ne_zero_of_factor` (`MvN/Comparison.lean`) without its factor step, which
identifies `c` with `1` there; the construction of `c` is copied from it. -/
theorem exists_centralSupport (N : VonNeumannAlgebra K) {f : K →L[ℂ] K} (hfN : f ∈ N) :
    ∃ c : K →L[ℂ] K, IsStarProjection c ∧ c ∈ N ∧ (∀ y ∈ N, Commute c y) ∧ c * f = f ∧
      ∀ e : K →L[ℂ] K, (∀ y ∈ N, e * y * f = 0) → e * c = 0 := by
  /- The closed subspace `S` spanned by the vectors `y (f ξ)`, `y ∈ N`. -/
  set G : Set K := {v | ∃ y ∈ N, ∃ ξ, v = y (f ξ)}
  set S₀ : Submodule ℂ K := Submodule.span ℂ G
  set S : Submodule ℂ K := S₀.topologicalClosure
  have hgen : ∀ y ∈ N, ∀ ξ, y (f ξ) ∈ S := fun y hy ξ =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, hy, ξ, rfl⟩)
  -- an operator mapping the generators into `S₀` leaves `S` invariant
  have hinv : ∀ T : K →L[ℂ] K, (∀ v ∈ G, T v ∈ S₀) → ∀ v ∈ S, T v ∈ S := by
    intro T hT v hv
    have h1 : S₀ ≤ S₀.comap (T : K →ₗ[ℂ] K) := Submodule.span_le.mpr fun v hv => hT v hv
    have h2 : v ∈ closure (S₀ : Set K) := by rwa [← Submodule.topologicalClosure_coe]
    have h3 : T v ∈ closure (S₀ : Set K) :=
      map_mem_closure T.continuous h2 fun x hx => h1 hx
    rwa [← Submodule.topologicalClosure_coe] at h3
  have hinvN : ∀ y ∈ N, ∀ v ∈ S, y v ∈ S := fun y hy => hinv y (by
    rintro _ ⟨y', hy', ξ, rfl⟩
    exact Submodule.subset_span ⟨y * y', mul_mem hy hy', ξ, by rw [mul_apply_eq_comp]⟩)
  have hinvC : ∀ y ∈ N.commutant, ∀ v ∈ S, y v ∈ S := fun y hy => hinv y (by
    rintro _ ⟨y', hy', ξ, rfl⟩
    refine Submodule.subset_span ⟨y', hy', y ξ, ?_⟩
    rw [← mul_apply_eq_comp, CommutingRepetition.VN.commutant_mul_of_mem hy' hy,
      mul_apply_eq_comp, ← mul_apply_eq_comp y f,
      CommutingRepetition.VN.commutant_mul_of_mem hfN hy, mul_apply_eq_comp])
  /- Its projection `c` commutes with `N` and `N'`, so it is a central projection of `N`. -/
  set c : K →L[ℂ] K := S.starProjection
  have hcN : ∀ y ∈ N, Commute y c := fun y hy =>
    Blocks.starProjection_commute_of_invariant' S (hinvN y hy) (hinvN _ (star_mem hy))
  have hcC : ∀ y ∈ N.commutant, Commute y c := fun y hy =>
    Blocks.starProjection_commute_of_invariant' S (hinvC y hy) (hinvC _ (star_mem hy))
  refine ⟨c, isStarProjection_starProjection,
    CommutingRepetition.VN.mem_of_commute_commutant N fun y hy => (hcC y hy).eq,
    fun y hy => (hcN y hy).symm, ?_, fun e he => ?_⟩
  · -- `c` fixes every vector `f ξ`
    refine ContinuousLinearMap.ext fun ξ => ?_
    rw [mul_apply_eq_comp]
    exact Submodule.starProjection_eq_self_iff.mpr (by simpa using hgen 1 (one_mem N) ξ)
  · -- `e` vanishes on the generators, hence on `S`, which contains the range of `c`
    have hker : S ≤ LinearMap.ker (e : K →ₗ[ℂ] K) := by
      refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker e)
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨y, hy, ξ, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp,
        ← mul_apply_eq_comp, he y hy, zero_apply]
    refine ContinuousLinearMap.ext fun v => ?_
    have := LinearMap.mem_ker.mp (hker (S.starProjection_apply_mem v))
    rw [ContinuousLinearMap.coe_coe] at this
    rw [mul_apply_eq_comp, this, zero_apply]

/-- **Extension from a nonzero corner**: if `(q - w w*) y (p - w* w) ≠ 0` for some `y ∈ N`, the
partial isometry `w` extends by a partial isometry `u` between the complements `p - w* w`,
`q - w w*`, whose initial projection has positive trace when `τ` is faithful. This is the vendored
`exists_extension_of_ne` (`MvN/Comparison.lean`), copied with the nonzero corner as a hypothesis:
there it comes from the factor hypothesis. -/
theorem exists_extension_of_mul_ne_zero (N : VonNeumannAlgebra K) (τ : (K →L[ℂ] K) →ₗ[ℂ] ℂ)
    (hτ0 : ∀ x ∈ N, 0 ≤ τ (star x * x)) (hτf : ∀ x ∈ N, τ (star x * x) = 0 → x = 0)
    {p q w y : K →L[ℂ] K} (hp : IsStarProjection p) (hpN : p ∈ N) (hq : IsStarProjection q)
    (hqN : q ∈ N) (hw : IsPartialBetween N p q w) (hyN : y ∈ N)
    (hx0 : (q - w * star w) * y * (p - star w * w) ≠ 0) :
    ∃ u, IsPartialBetween N (p - star w * w) (q - w * star w) u ∧ 0 < (τ (star u * u)).re := by
  have hrP := hw.proj
  have hlP := hw.isStarProjection_mul_star
  have hpr : IsStarProjection (p - star w * w) := isStarProjection_sub_of_le hp hrP hw.init_le
    (Blocks.proj_mul_left_of_mul_right hrP hp hw.init_le)
  have hql : IsStarProjection (q - w * star w) := isStarProjection_sub_of_le hq hlP hw.final_le
    (Blocks.proj_mul_left_of_mul_right hlP hq hw.final_le)
  set x := (q - w * star w) * y * (p - star w * w) with hx
  have hxN : x ∈ N := mul_mem (mul_mem (sub_mem hqN hw.final_mem) hyN) (sub_mem hpN hw.init_mem)
  /- The polar decomposition `x = u |x|` gives the extension. -/
  obtain ⟨u, huN, hu1, hu2, hxu⟩ := exists_polar N x hxN
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hxu
    exact hx0 hxu
  have hxp : x * (p - star w * w) = x := by rw [hx, mul_assoc, hpr.isIdempotentElem.eq]
  have hqx : (q - w * star w) * x = x := by
    rw [hx, ← mul_assoc, ← mul_assoc, hql.isIdempotentElem.eq]
  refine ⟨u, ⟨huN, by rw [hu1]; exact isStarProjection_rightSupport x,
    by rw [hu1]; exact rightSupport_mul_eq_self_of hxp,
    by rw [hu2]; exact leftSupport_mul_eq_self_of hql hqx⟩, ?_⟩
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hτ0 u huN)
  rcases hre.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    refine hu0 (hτf u huN (Complex.ext ?_ ?_))
    · rw [Complex.zero_re]; exact heq.symm
    · rw [Complex.zero_im]; exact him.symm

/-- **A maximal partial isometry between two projections**: in a von Neumann algebra `N` with a
faithful positive functional `τ`, some partial isometry `W ∈ N` from below `p` to below `q` leaves
complements with no corner between them, `(q - W W*) y (p - W* W) = 0` for every `y ∈ N`. The
greedy chain is that of the vendored `mvNEquiv_of_trace_eq` (`MvN/Comparison.lean`), copied
because that theorem hard-codes its factor hypothesis, through which maximality makes one of the
two complements vanish. -/
theorem exists_maximal_isPartialBetween (N : VonNeumannAlgebra K) (τ : (K →L[ℂ] K) →ₗ[ℂ] ℂ)
    (hτ0 : ∀ x ∈ N, 0 ≤ τ (star x * x)) (hτf : ∀ x ∈ N, τ (star x * x) = 0 → x = 0)
    {p q : K →L[ℂ] K} (hp : IsStarProjection p) (hpN : p ∈ N) (hq : IsStarProjection q)
    (hqN : q ∈ N) :
    ∃ W, IsPartialBetween N p q W ∧ ∀ y ∈ N, (q - W * star W) * y * (p - star W * W) = 0 := by
  classical
  /- The greedy step, as a function of the current partial isometry. -/
  have hstep : ∀ w, IsPartialBetween N p q w →
      ∃ u, IsPartialBetween N (p - star w * w) (q - w * star w) u ∧
        ∀ u', IsPartialBetween N (p - star w * w) (q - w * star w) u' →
          (τ (star u' * u')).re ≤ 2 * (τ (star u * u)).re :=
    fun w hw => exists_good_extension N τ hτ0 hp hpN hw
  choose! U hU using hstep
  /- The greedy sequence `w₀ = 0`, `wₙ₊₁ = wₙ + U wₙ`. -/
  obtain ⟨w, hw0, hwsucc⟩ : ∃ w : ℕ → K →L[ℂ] K, w 0 = 0 ∧ ∀ n, w (n + 1) = w n + U (w n) :=
    ⟨fun n => Nat.rec 0 (fun _ w => w + U w) n, rfl, fun _ => rfl⟩
  have hw : ∀ n, IsPartialBetween N p q (w n) := by
    intro n
    induction n with
    | zero => rw [hw0]; exact zero_isPartialBetween N p q
    | succ n ih => rw [hwsucc]; exact (IsPartialBetween.add hp hq ih (hU _ ih).1).1
  have hchain : IsChain N p q w (fun n => U (w n)) := ⟨hw, fun n => (hU _ (hw n)).1, hwsucc⟩
  /- The strong limit `W`, with its initial projection `W* W` and final projection `W W*`. -/
  obtain ⟨W, hWN, hWlim, hRP, hRp, hrR⟩ := hchain.exists_limit hp hq
  obtain ⟨V, -, hVlim, hLP, hLq, hlL⟩ := hchain.adjoint.exists_limit hq hp
  have hVW : V = star W := eq_star_of_tendsto hWlim hVlim
  simp only [hVW, star_star] at hLP hLq hlL
  have hWpart : IsPartialBetween N p q W := ⟨hWN, hRP, hRp, hLq⟩
  refine ⟨W, hWpart, fun y hyN => ?_⟩
  /- Maximality. Otherwise an extension `u'` of `W` of trace `δ > 0` extends every `wₙ`, so
  `δ ≤ 2 (tₙ₊₁ − tₙ)` for the sequence `tₙ = τ(wₙ* wₙ)`, which is bounded by `τ(p)`: absurd. -/
  by_contra hx0
  obtain ⟨u', hu', hδ⟩ := exists_extension_of_mul_ne_zero N τ hτ0 hτf hp hpN hq hqN hWpart hyN hx0
  have hu'n : ∀ n, IsPartialBetween N (p - star (w n) * w n) (q - w n * star (w n)) u' :=
    fun n => hu'.mono (sub_mul_sub_of_le (hw n).proj hRP hp (hrR n) hRp)
      (sub_mul_sub_of_le (hw n).isStarProjection_mul_star hLP hq (hlL n) hLq)
  have hbound : ∀ n, (τ (star u' * u')).re ≤ 2 * (τ (star (U (w n)) * U (w n))).re :=
    fun n => (hU _ (hw n)).2 u' (hu'n n)
  have ht_succ : ∀ n, (τ (star (w (n + 1)) * w (n + 1))).re =
      (τ (star (w n) * w n)).re + (τ (star (U (w n)) * U (w n))).re := fun n => by
    rw [hchain.init_succ hp hq n, map_add, Complex.add_re]
  have ht_le : ∀ n, (τ (star (w n) * w n)).re ≤ (τ p).re := fun n =>
    Blocks.re_map_le_of_mem hτ0 (hw n).init_mem hpN ((hw n).init_le_loewner hp)
  have ht_ge : ∀ n : ℕ, n * ((τ (star u' * u')).re / 2) ≤ (τ (star (w n) * w n)).re := by
    intro n
    induction n with
    | zero => simp [hw0]
    | succ n ih =>
      rw [ht_succ n]
      push_cast
      linarith [hbound n]
  obtain ⟨n, hn⟩ := exists_nat_gt ((τ p).re / ((τ (star u' * u')).re / 2))
  rw [div_lt_iff₀ (half_pos hδ)] at hn
  linarith [ht_le n, ht_ge n]

end Comparison

/- `hτtr` belongs to the statement's shape, that of the vendored `mvNEquiv_of_trace_eq`; the proof
does not use it, since the traciality of `Φ` takes its place in the endgame. -/
set_option linter.unusedVariables false in
/-- **Generalized comparison of projections**: in a von Neumann algebra `N` with a faithful
positive tracial functional `τ`, two projections with the same image under a linear map `Φ` that
is tracial on `N`, compatible with left multiplication by central projections, and faithful on
projections, are Murray–von Neumann equivalent. -/
theorem mvNEquiv_of_map_eq {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (N : VonNeumannAlgebra K) (τ : (K →L[ℂ] K) →ₗ[ℂ] ℂ)
    (hτ0 : ∀ x ∈ N, 0 ≤ τ (star x * x)) (hτtr : ∀ x ∈ N, ∀ y ∈ N, τ (x * y) = τ (y * x))
    (hτf : ∀ x ∈ N, τ (star x * x) = 0 → x = 0)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (Φ : (K →L[ℂ] K) →ₗ[ℂ] V)
    (hΦtr : ∀ x ∈ N, ∀ y ∈ N, Φ (x * y) = Φ (y * x))
    (hΦc : ∀ c, IsStarProjection c → c ∈ N → (∀ y ∈ N, Commute c y) →
      ∃ L : V → V, ∀ x ∈ N, Φ (c * x) = L (Φ x))
    (hΦf : ∀ e, IsStarProjection e → e ∈ N → Φ e = 0 → e = 0)
    {p q : K →L[ℂ] K} (hp : IsStarProjection p) (hpN : p ∈ N) (hq : IsStarProjection q)
    (hqN : q ∈ N) (hpq : Φ p = Φ q) : MvNEquiv N p q := by
  obtain ⟨W, hW, hmax⟩ := exists_maximal_isPartialBetween N τ hτ0 hτf hp hpN hq hqN
  have hpW : IsStarProjection (p - star W * W) := isStarProjection_sub_of_le hp hW.proj hW.init_le
    (Blocks.proj_mul_left_of_mul_right hW.proj hp hW.init_le)
  have hqW : IsStarProjection (q - W * star W) :=
    isStarProjection_sub_of_le hq hW.isStarProjection_mul_star hW.final_le
      (Blocks.proj_mul_left_of_mul_right hW.isStarProjection_mul_star hq hW.final_le)
  have hpWN : p - star W * W ∈ N := sub_mem hpN hW.init_mem
  have hqWN : q - W * star W ∈ N := sub_mem hqN hW.final_mem
  /- The central support `c` of `p - W* W` kills `q - W W*`, by maximality. -/
  obtain ⟨c, hc, hcN, hcc, hcp, hce⟩ := exists_centralSupport N hpWN
  have hcq : c * (q - W * star W) = 0 := (hcc _ hqWN).eq.trans (hce _ hmax)
  /- The complements have the same image under `Φ`, by traciality, and `Φ (c x) = L (Φ x)`
  makes it vanish: `Φ (p - W* W) = L (Φ (p - W* W)) = L (Φ (q - W W*)) = Φ (c (q - W W*)) = 0`. -/
  obtain ⟨L, hL⟩ := hΦc c hc hcN hcc
  have hΦW : Φ (p - star W * W) = Φ (q - W * star W) := by
    rw [map_sub, map_sub, hpq, hΦtr _ (star_mem hW.mem) _ hW.mem]
  have hΦp : Φ (p - star W * W) = 0 :=
    calc Φ (p - star W * W) = L (Φ (p - star W * W)) := by rw [← hL _ hpWN, hcp]
      _ = L (Φ (q - W * star W)) := by rw [hΦW]
      _ = 0 := by rw [← hL _ hqWN, hcq, map_zero]
  exact ⟨W, hW.mem, (sub_eq_zero.mp (hΦf _ hpW hpWN hΦp)).symm,
    (sub_eq_zero.mp (hΦf _ hqW hqWN (hΦW.symm.trans hΦp))).symm⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The centre of `M_n(M)` is the amplified centre of `M`**: an element of `M_n(M)` commuting
with `M_n(M)` is the amplification of a central element of `M`. -/
theorem exists_eq_amplify_of_commute (M : VonNeumannAlgebra H) {n : ℕ}
    {X : FinDim.BlockSpace H (Fin n) →L[ℂ] FinDim.BlockSpace H (Fin n)}
    (hX : X ∈ matrixAlgebra M n) (hXc : ∀ Y ∈ matrixAlgebra M n, Commute X Y) :
    ∃ c, IsCentralIn M 1 c ∧ X = amplify n c := by
  /- The first half of the vendored `matrixAlgebra_factor` (`MvN/MatrixFactor.lean`), which
  stops short of its factor hypothesis. -/
  obtain _ | n := n
  · exact ⟨0, ⟨zero_mem M, by rw [mul_zero, zero_mul], fun y _ _ => Commute.zero_left y⟩,
      ext_entry fun i _ => i.elim0⟩
  -- commuting with `e_{ij}`: `X_{ki} = δ_{ki} X_{jj}`
  have key : ∀ k i j : Fin (n + 1), entry X k i = if k = i then entry X j j else 0 := by
    intro k i j
    have h := congrArg (fun Y => entry Y k j) (hXc _ (matrixUnit_mem M i j)).eq
    simpa only [entry_mul_matrixUnit, entry_matrixUnit_mul, eq_self_iff_true, ite_true] using h
  have hXz : X = amplify (n + 1) (entry X 0 0) :=
    ext_entry fun k i => by rw [entry_amplify, key k i 0]
  refine ⟨entry X 0 0, ⟨entry_mem hX 0 0, by rw [one_mul, mul_one], fun y hy _ => ?_⟩, hXz⟩
  -- commuting with `y ⊕ ⋯ ⊕ y`, `y ∈ M`: `X_{00}` commutes with `y`
  have h := congrArg (fun Y => entry Y 0 0) (hXc _ (amplify_mem hy)).eq
  rw [hXz] at h
  simp only [entry_mul_amplify, entry_amplify, ite_true] at h
  exact h

/-! ### The vector functional as the trace of the comparison theorem -/

section VecFunctional

variable {M : VonNeumannAlgebra H} {d : ℕ} {g : Fin d → H}

/-- `τ(x* x) = ∑ₖ ‖x gₖ‖²` for the vector functional `τ` of `g`. -/
theorem vecFunctional_star_mul_self_eq_sum (g : Fin d → H) (x : H →L[ℂ] H) :
    vecFunctional g (star x * x) = ((∑ k, ‖x (g k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [vecFunctional_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The vector functional is positive. -/
theorem vecFunctional_star_mul_self_nonneg (g : Fin d → H) (x : H →L[ℂ] H) :
    0 ≤ vecFunctional g (star x * x) := by
  rw [vecFunctional_star_mul_self_eq_sum]
  exact Complex.zero_le_real.mpr (Finset.sum_nonneg fun k _ => sq_nonneg _)

/-- The vector functional of a family separating `M` is faithful on `M`. -/
theorem eq_zero_of_vecFunctional_star_mul_self_eq_zero
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) {x : H →L[ℂ] H} (hx : x ∈ M)
    (h : vecFunctional g (star x * x) = 0) : x = 0 := by
  rw [vecFunctional_star_mul_self_eq_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _] at h
  exact hsep x hx fun k => norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (h k (by simp)))

end VecFunctional

namespace IsCenterExpectation

variable {M : VonNeumannAlgebra H} {d : ℕ} {g : Fin d → H}
  {E : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} (hE : IsCenterExpectation M g E)
include hE

/-- **Comparison in `M`**: projections with the same centre-valued trace are equivalent. -/
theorem equiv_of_eq (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∀ q q', IsStarProjection q → q ∈ M → IsStarProjection q' → q' ∈ M → E q = E q' →
      MvNEquiv M q q' := by
  intro q q' hq hqM hq' hq'M h
  refine mvNEquiv_of_map_eq M (vecFunctional g) (fun x _ => vecFunctional_star_mul_self_nonneg g x)
    htr (fun x hx => eq_zero_of_vecFunctional_star_mul_self_eq_zero hsep hx) E
    (hE.trace htr hsep) (fun c _ hcM hcc => ⟨(c * ·), fun x hx => ?_⟩) (fun e he heM h0 => ?_)
    hq hqM hq' hq'M h
  · -- a central projection is central in `M`, and `E` is linear over the centre
    exact hE.center_mul hsep c ⟨hcM, by rw [one_mul, mul_one], fun y hy _ => hcc y hy⟩ x hx
  · -- `τ(e* e) = τ(e) = τ(E e) = 0`
    refine eq_zero_of_vecFunctional_star_mul_self_eq_zero hsep heM ?_
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq, ← hE.vecFunctional_eq e heM, h0,
      map_zero]

/-- **Comparison in `M_n(M)`**: projections with the same diagonal centre-valued trace
`∑ᵢ E(Xᵢᵢ)` are equivalent. -/
theorem equiv_of_eq_matrix
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) (n : ℕ)
    (P Q : FinDim.BlockSpace H (Fin n) →L[ℂ] FinDim.BlockSpace H (Fin n)) :
    P ∈ matrixAlgebra M n → IsStarProjection P → Q ∈ matrixAlgebra M n → IsStarProjection Q →
      ∑ i, E (entry P i i) = ∑ i, E (entry Q i i) → MvNEquiv (matrixAlgebra M n) P Q := by
  intro hPM hP hQM hQ h
  have hτ0 : ∀ x ∈ M, 0 ≤ vecFunctional g (star x * x) := fun x _ =>
    vecFunctional_star_mul_self_nonneg g x
  have hτf : ∀ x ∈ M, vecFunctional g (star x * x) = 0 → x = 0 := fun x hx =>
    eq_zero_of_vecFunctional_star_mul_self_eq_zero hsep hx
  /- `Φ X = ∑ᵢ E(Xᵢᵢ)`, with the diagonal trace of `τ` as the trace of `M_n(M)`. -/
  set Φ : (FinDim.BlockSpace H (Fin n) →L[ℂ] FinDim.BlockSpace H (Fin n)) →ₗ[ℂ] (H →L[ℂ] H) :=
    ∑ i, E ∘ₗ entryₗ i i with hΦdef
  have hΦ : ∀ X, Φ X = ∑ i, E (entry X i i) := fun X => by
    rw [hΦdef, LinearMap.sum_apply]
    rfl
  refine mvNEquiv_of_map_eq (matrixAlgebra M n) (diagTrace (vecFunctional g) n)
    (diagTrace_nonneg M _ hτ0 n) (diagTrace_trace M _ htr n) (diagTrace_faithful M _ hτ0 hτf n) Φ
    (fun X hX Y hY => by
      rw [hΦ, hΦ]
      exact sum_entry_mul_eq E (hE.trace htr hsep) (entry_mem hX) (entry_mem hY))
    (fun C _ hCM hCc => ?_) (fun e he heM h0 => ?_) hP hPM hQ hQM (by rw [hΦ, hΦ, h])
  · -- a central projection of `M_n(M)` is `c ⊕ ⋯ ⊕ c` with `c` central in `M`
    obtain ⟨c, hc, rfl⟩ := exists_eq_amplify_of_commute M hCM hCc
    refine ⟨(c * ·), fun X hX => ?_⟩
    simp only [hΦ, entry_amplify_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hE.center_mul hsep c hc _ (entry_mem hX i i)
  · -- `∑ᵢ τ((e* e)ᵢᵢ) = ∑ᵢ τ(eᵢᵢ) = ∑ᵢ τ(E eᵢᵢ) = τ(Φ e) = 0`
    refine diagTrace_faithful M _ hτ0 hτf n e heM ?_
    rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq, diagTrace_apply]
    calc ∑ i, vecFunctional g (entry e i i) = ∑ i, vecFunctional g (E (entry e i i)) :=
          Finset.sum_congr rfl fun i _ => (hE.vecFunctional_eq _ (entry_mem heM i i)).symm
      _ = vecFunctional g (Φ e) := by rw [hΦ, map_sum]
      _ = 0 := by rw [h0, map_zero]

/-- **A centre-valued expectation is a centre-valued trace** (field H3 at the projection `1`). -/
theorem isCenterValuedTrace
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) : IsCenterValuedTrace M 1 E where
  mem_center x hx _ := hE.mem_center x hx
  nonneg x hx _ := hE.nonneg x hx
  trace x hx _ y hy _ := hE.trace htr hsep x hx y hy
  center_fixed := hE.center_fixed hsep
  center_mul c hc x hx _ := hE.center_mul hsep c hc x hx
  faithful x hx _ := hE.faithful hsep x hx
  normal l T L hT hL _ := hE.normal hsep l T L (fun k => (hT k).1) hL
  equiv_of_eq q q' hq hqM _ hq' hq'M _ := hE.equiv_of_eq htr hsep q q' hq hqM hq' hq'M
  div r hr hrM _ := hE.div hsep r hr hrM
  equiv_of_eq_matrix n P Q hPM hP _ hQM hQ _ := hE.equiv_of_eq_matrix htr hsep n P Q hPM hP hQM hQ

end IsCenterExpectation

/-- **Field H3 at the projection `1`** for a von Neumann algebra with a faithful tracial vector
functional: it has a centre-valued trace. No factor, type or separability hypothesis. -/
theorem exists_isCenterValuedTrace (M : VonNeumannAlgebra H) {d : ℕ} (g : Fin d → H)
    (htr : ∀ x ∈ M, ∀ y ∈ M, vecFunctional g (x * y) = vecFunctional g (y * x))
    (hsep : ∀ x ∈ M, (∀ k, x (g k) = 0) → x = 0) :
    ∃ E, IsCenterValuedTrace M 1 E := by
  obtain ⟨E, hE⟩ := exists_isCenterExpectation M g htr hsep
  exact ⟨E, hE.isCenterValuedTrace htr hsep⟩

end MIPRE.Orthonormalization

end
