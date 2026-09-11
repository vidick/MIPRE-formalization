/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Haagerup/Reduction.lean
-/
/-
# Haagerup's reduction: the periodic modular groups (density stage E6.4a)

In the crossed product `ℛ = M ⋊_σ ℚ` with the cyclic separating vector `Ω̂` we put, for each
`n`, `u_n := λ(2^{-n})`, `a_n := 2^n·(−i log u_n)` (a self-adjoint element of the centralizer
of `ψ̂`), and `ξ_n := e^{−a_n/2}Ω̂`. The modular group of `ξ_n` is
`σ^{ξ_n}_t = Ad(e^{−ita_n}) ∘ σ̂_t` on `ℛ`, and it is **`2^{-n}`-periodic**: at `t = 2^{-n}`
one has `e^{−i2^{-n}a_n} = u_n*` while `σ̂_{2^{-n}} = Ad(u_n)`, so the two cancel.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.Crossed.Modular
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.Perturb
import MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.UnitaryLog

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace VN

namespace Haagerup

open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology MeasureTheory BorelCalc ClosedSubmodule
open CommutingRepetition.VN.Modular CommutingRepetition.VN.Crossed

set_option linter.unusedSectionVars false

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-! ## The generating unitaries `λ(2^{-n})` -/

/-- The rational `2^{-n}`. -/
noncomputable def qn (n : ℕ) : ℚ := 1 / 2 ^ n

theorem qn_cast (n : ℕ) : ((qn n : ℚ) : ℝ) = 1 / 2 ^ n := by
  rw [qn]; push_cast; ring

theorem qn_pos (n : ℕ) : 0 < qn n := by
  rw [qn]; positivity

/-- `u_n = λ(2^{-n})`. -/
noncomputable def un (n : ℕ) : L2Q K →L[ℂ] L2Q K := shift (qn n)

theorem star_un (n : ℕ) : star (un (K := K) n) = shift (-(qn n)) := shift_star _

theorem star_un_mul (n : ℕ) : star (un (K := K) n) * un (K := K) n = 1 := by
  rw [star_un, un, ← shift_add, neg_add_cancel, shift_zero]

theorem un_mul_star (n : ℕ) : un (K := K) n * star (un (K := K) n) = 1 := by
  rw [star_un, un, ← shift_add, add_neg_cancel, shift_zero]

theorem un_mem (M : VonNeumannAlgebra K) (Ω : K) (n : ℕ) : un (K := K) n ∈ crossed M Ω :=
  shift_mem M Ω _

theorem commute_un_amp (n : ℕ) (y : K →L[ℂ] K) : Commute (un (K := K) n) (amp y) :=
  shift_amp _ y

theorem commute_star_un_amp (n : ℕ) (y : K →L[ℂ] K) :
    Commute (star (un (K := K) n)) (amp y) := by
  rw [star_un]; exact shift_amp _ y

/-! ## The logarithms `a_n` -/

/-- `a_n = 2^n·(−i log λ(2^{-n}))`: self-adjoint, in `ℛ`, and in the centralizer of `ψ̂`. -/
noncomputable def an (n : ℕ) : L2Q K →L[ℂ] L2Q K :=
  ((2 ^ n : ℝ) : ℂ) • ulog (un (K := K) n) (star_un_mul n) (un_mul_star n)

theorem isSelfAdjoint_an (n : ℕ) : IsSelfAdjoint (an (K := K) n) := by
  have h := isSelfAdjoint_ulog (un (K := K) n) (star_un_mul n) (un_mul_star n)
  rw [an, IsSelfAdjoint, star_smul, h.star_eq, Complex.star_def, Complex.conj_ofReal]

theorem an_mem (M : VonNeumannAlgebra K) (Ω : K) (n : ℕ) : an (K := K) n ∈ crossed M Ω :=
  VN.smul_mem_vn _ _ (ulog_mem _ (star_un_mul n) (un_mul_star n) (un_mem M Ω n))

theorem commute_an_amp (n : ℕ) (y : K →L[ℂ] K) : Commute (an (K := K) n) (amp y) :=
  (commute_ulog _ (star_un_mul n) (un_mul_star n) (commute_un_amp n y)
    (commute_star_un_amp n y)).smul_left _

theorem commute_an_R (M : VonNeumannAlgebra K) (Ω : K)
    (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)
    (n : ℕ) : Commute (an (K := K) n) (R (crossed M Ω) (Ωh Ω)) := by
  rw [R_crossed M Ω hs hc]
  exact commute_an_amp n _

/-! ## The exponentials of `a_n` -/

theorem eit_an (n : ℕ) (t : ℝ) :
    eit (an (K := K) n) (isSelfAdjoint_an n) t =
      eit (ulog (un (K := K) n) (star_un_mul n) (un_mul_star n))
        (isSelfAdjoint_ulog _ _ _) (t * 2 ^ n) := by
  exact eit_ulog_smul (un (K := K) n) (star_un_mul n) (un_mul_star n) ((2 : ℝ) ^ n) t
    (isSelfAdjoint_an n)

theorem eit_an_qn (n : ℕ) : eit (an (K := K) n) (isSelfAdjoint_an n) (1 / 2 ^ n) = un n := by
  rw [eit_an]
  have e : (1 : ℝ) / 2 ^ n * 2 ^ n = 1 := by
    field_simp
  rw [e]
  exact eit_ulog _ (star_un_mul n) (un_mul_star n)

theorem eit_an_neg_qn (n : ℕ) :
    eit (an (K := K) n) (isSelfAdjoint_an n) (-(1 / 2 ^ n)) = star (un (K := K) n) := by
  have h := eit_star (isSelfAdjoint_an (K := K) n) (1 / 2 ^ n)
  rw [eit_an_qn] at h
  exact h.symm

/-! ## The perturbed vectors and their modular groups -/

section Dyn

variable (M : VonNeumannAlgebra K) (Ω : K)
variable (hs : IsSeparating (M : Set (K →L[ℂ] K)) Ω) (hc : IsCyclic (M : Set (K →L[ℂ] K)) Ω)

/-- `ξ_n = e^{−a_n/2}Ω̂`. -/
noncomputable def xin (n : ℕ) : L2Q K := pvec (Ωh Ω) (an n)

include hs hc in
theorem isSeparating_xin (n : ℕ) :
    IsSeparating (crossed M Ω : Set (L2Q K →L[ℂ] L2Q K)) (xin Ω n) :=
  isSeparating_pvec (crossed M Ω) (Ωh Ω) (isSeparating_Ωh M Ω hs hc) (an_mem M Ω n)
    (isSelfAdjoint_an n)

include hs hc in
theorem isCyclic_xin (n : ℕ) :
    IsCyclic (crossed M Ω : Set (L2Q K →L[ℂ] L2Q K)) (xin Ω n) :=
  isCyclic_pvec (crossed M Ω) (Ωh Ω) (isCyclic_Ωh M Ω hc) (an_mem M Ω n) (isSelfAdjoint_an n)

include hs hc in
theorem Δit_xin (n : ℕ) (t : ℝ) :
    Δit (crossed M Ω) (xin Ω n) t =
      eit (Bp (crossed M Ω) (Ωh Ω) (an n))
        (isSelfAdjoint_Bp (crossed M Ω) (Ωh Ω) (isSeparating_Ωh M Ω hs hc) (isCyclic_Ωh M Ω hc)
          (an n) (isSelfAdjoint_an n)) t * Δit (crossed M Ω) (Ωh Ω) t :=
  Δit_pvec (crossed M Ω) (Ωh Ω) (isSeparating_Ωh M Ω hs hc) (isCyclic_Ωh M Ω hc) (an n)
    (an_mem M Ω n) (isSelfAdjoint_an n) (commute_an_R M Ω hs hc n) t

include hs hc in
set_option maxHeartbeats 2000000 in
/-- **The modular group of `ξ_n`**: `σ^{ξ_n}_t = Ad(e^{−ita_n}) ∘ σ̂_t` on `ℛ`. -/
theorem σ_xin (n : ℕ) (t : ℝ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    σ (crossed M Ω) (xin Ω n) t x =
      eit (an (K := K) n) (isSelfAdjoint_an n) (-t) * σ (crossed M Ω) (Ωh Ω) t x *
        eit (an (K := K) n) (isSelfAdjoint_an n) t := by
  have hsΩ := isSeparating_Ωh M Ω hs hc
  have hcΩ := isCyclic_Ωh M Ω hc
  have ha := an_mem M Ω n
  have hsa := isSelfAdjoint_an (K := K) n
  have haR := commute_an_R M Ω hs hc n
  have hsa' : IsSelfAdjoint (conjJm (crossed M Ω) (Ωh Ω) (an n)) :=
    conjJm_isSelfAdjoint (crossed M Ω) (Ωh Ω) hsΩ hcΩ hsa
  have hab : Commute (an (K := K) n) (conjJm (crossed M Ω) (Ωh Ω) (an n)) :=
    commute_a_conjJm (crossed M Ω) (Ωh Ω) hsΩ hcΩ (an n) ha
  have ha'mem : conjJm (crossed M Ω) (Ωh Ω) (an n) ∈ (crossed M Ω).commutant :=
    conjJm_mem_commutant (crossed M Ω) (Ωh Ω) hsΩ hcΩ ha
  have ha'R : Commute (conjJm (crossed M Ω) (Ωh Ω) (an n)) (R (crossed M Ω) (Ωh Ω)) :=
    commute_conjJm_R (crossed M Ω) (Ωh Ω) hsΩ hcΩ haR
  -- the expansion of the two modular unitaries
  have hΔ : Δit (crossed M Ω) (xin Ω n) t =
      eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' t * eit (an (K := K) n) hsa (-t) *
        Δit (crossed M Ω) (Ωh Ω) t := by
    rw [Δit_xin M Ω hs hc n t]
    congr 1
    exact eit_sub hsa hsa' hab t
  have hΔ' : Δit (crossed M Ω) (xin Ω n) (-t) =
      eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' (-t) * eit (an (K := K) n) hsa t *
        Δit (crossed M Ω) (Ωh Ω) (-t) := by
    rw [Δit_xin M Ω hs hc n (-t)]
    congr 1
    have h := eit_sub hsa hsa' hab (-t)
    rw [neg_neg] at h
    exact h
  -- the commutations
  have hA'x : Commute (eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' (-t)) x :=
    (VonNeumannAlgebra.mem_commutant_iff.mp
      (eit_mem hsa' (crossed M Ω).commutant ha'mem (-t)) x hx).symm
  have hA'B : Commute (eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' (-t))
      (eit (an (K := K) n) hsa (-t)) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp
      (eit_mem hsa' (crossed M Ω).commutant ha'mem (-t)) _ (eit_mem hsa _ ha (-t))).symm
  have hA'D : Commute (eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' (-t))
      (Δit (crossed M Ω) (Ωh Ω) t) :=
    commute_eit hsa' (commute_cbfc _ _ ha'R.symm (cbdd_gDel t)).symm (-t)
  have hBD : Commute (eit (an (K := K) n) hsa t) (Δit (crossed M Ω) (Ωh Ω) (-t)) :=
    commute_eit hsa (commute_cbfc _ _ haR.symm (cbdd_gDel (-t))).symm t
  have hAA' : eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' t *
      eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' (-t) = 1 := eit_mul_neg hsa' t
  simp only [σ]
  rw [hΔ, hΔ']
  set A := eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' t
  set A' := eit (conjJm (crossed M Ω) (Ωh Ω) (an n)) hsa' (-t)
  set B₁ := eit (an (K := K) n) hsa (-t)
  set B₂ := eit (an (K := K) n) hsa t
  set D := Δit (crossed M Ω) (Ωh Ω) t
  set D' := Δit (crossed M Ω) (Ωh Ω) (-t)
  have h1 : Commute A' (B₁ * D * x) := (hA'B.mul_right hA'D).mul_right hA'x
  calc A * B₁ * D * x * (A' * B₂ * D')
      = A * (B₁ * D * x * A') * (B₂ * D') := by simp only [mul_assoc]
    _ = A * (A' * (B₁ * D * x)) * (B₂ * D') := by rw [← h1.eq]
    _ = A * A' * (B₁ * D * x * (B₂ * D')) := by simp only [mul_assoc]
    _ = B₁ * D * x * (B₂ * D') := by rw [hAA', one_mul]
    _ = B₁ * D * x * (D' * B₂) := by rw [hBD.eq]
    _ = B₁ * (D * x * D') * B₂ := by simp only [mul_assoc]

include hs hc in
/-- **Periodicity**: `σ^{ξ_n}` is `2^{-n}`-periodic on `ℛ`, i.e. trivial at `t = 2^{-n}`. -/
theorem σ_xin_period (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    σ (crossed M Ω) (xin Ω n) (1 / 2 ^ n) x = x := by
  have hσ : σ (crossed M Ω) (Ωh Ω) (1 / 2 ^ n : ℝ) x =
      un (K := K) n * x * star (un (K := K) n) := by
    have e : ((qn n : ℚ) : ℝ) = 1 / 2 ^ n := qn_cast n
    rw [← e, σ_crossed_rat M Ω hs hc (qn n) hx, star_un, un]
  rw [σ_xin M Ω hs hc n _ hx, hσ, eit_an_neg_qn, eit_an_qn]
  calc star (un (K := K) n) * (un (K := K) n * x * star (un (K := K) n)) * un (K := K) n
      = star (un (K := K) n) * un (K := K) n *
          (x * (star (un (K := K) n) * un (K := K) n)) := by simp only [mul_assoc]
    _ = x := by rw [star_un_mul, one_mul, mul_one]

/-! ## The centralizer algebra `ℛ_n` -/

theorem isClosed_vn (N : VonNeumannAlgebra (L2Q K)) :
    IsClosed (N : Set (L2Q K →L[ℂ] L2Q K)) := by
  have h : (N : Set (L2Q K →L[ℂ] L2Q K)) =
      Set.centralizer (Set.centralizer (N : Set (L2Q K →L[ℂ] L2Q K))) :=
    (N.centralizer_centralizer').symm
  rw [h]
  exact Set.isClosed_centralizer _

theorem commute_star_of_isSelfAdjoint {A x : L2Q K →L[ℂ] L2Q K} (hA : IsSelfAdjoint A)
    (h : Commute x A) : Commute (star x) A := by
  have := congrArg star h.eq
  rw [star_mul, star_mul, hA.star_eq] at this
  exact this.symm

/-- **The centralizer `ℛ_n`** of the perturbed state: the elements of `ℛ` commuting with
`R(ℛ, ξ_n)`, equivalently the fixed points of `σ^{ξ_n}`. -/
noncomputable def Rn (n : ℕ) : StarSubalgebra ℂ (L2Q K →L[ℂ] L2Q K) where
  carrier := {x | x ∈ crossed M Ω ∧ Commute x (R (crossed M Ω) (xin Ω n))}
  mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul_left hy.2⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add_left hy.2⟩
  algebraMap_mem' := fun c => by
    refine ⟨?_, ?_⟩
    · rw [Algebra.algebraMap_eq_smul_one]
      exact VN.smul_mem_vn _ c (one_mem _)
    · rw [Algebra.algebraMap_eq_smul_one]
      exact (Commute.one_left _).smul_left c
  star_mem' := fun hx =>
    ⟨star_mem hx.1, commute_star_of_isSelfAdjoint (R_isSelfAdjoint _ _) hx.2⟩

theorem mem_Rn_iff {n : ℕ} {x : L2Q K →L[ℂ] L2Q K} :
    x ∈ Rn M Ω n ↔ x ∈ crossed M Ω ∧ Commute x (R (crossed M Ω) (xin Ω n)) := Iff.rfl

theorem isCentral_of_mem_Rn {n : ℕ} {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ Rn M Ω n) :
    IsCentral (crossed M Ω) (xin Ω n) x := hx

include hs hc in
/-- `ℛ_n` is exactly the fixed-point algebra of `σ^{ξ_n}`. -/
theorem mem_Rn_iff_σ {n : ℕ} {x : L2Q K →L[ℂ] L2Q K} :
    x ∈ Rn M Ω n ↔
      x ∈ crossed M Ω ∧ ∀ t : ℝ, σ (crossed M Ω) (xin Ω n) t x = x := by
  refine ⟨fun hx => ⟨hx.1, fun t =>
    σ_eq_self_of_commute_R (crossed M Ω) (xin Ω n) hx.2 t⟩, fun hx => ⟨hx.1, ?_⟩⟩
  refine commute_R_of_commute_Δit (crossed M Ω) (xin Ω n) (isSeparating_xin M Ω hs hc n)
    (isCyclic_xin M Ω hs hc n) fun t => ?_
  exact ((σ_eq_self_iff (crossed M Ω) (xin Ω n) t x).mp (hx.2 t)).symm

include hs hc in
theorem isClosed_Rn (n : ℕ) : IsClosed ((Rn M Ω n : StarSubalgebra ℂ _) :
    Set (L2Q K →L[ℂ] L2Q K)) := by
  have h1 : ((Rn M Ω n : StarSubalgebra ℂ _) : Set (L2Q K →L[ℂ] L2Q K)) =
      (crossed M Ω : Set (L2Q K →L[ℂ] L2Q K)) ∩
        {x | x * R (crossed M Ω) (xin Ω n) - R (crossed M Ω) (xin Ω n) * x = 0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sub_eq_zero]
    exact Iff.rfl
  rw [h1]
  refine (isClosed_vn _).inter ?_
  have hcont : Continuous fun x : L2Q K →L[ℂ] L2Q K =>
      x * R (crossed M Ω) (xin Ω n) - R (crossed M Ω) (xin Ω n) * x :=
    (continuous_id.mul continuous_const).sub (continuous_const.mul continuous_id)
  exact isClosed_eq hcont continuous_const

/-! ## Traciality and the Radon–Nikodym element -/

include hs hc in
/-- **The perturbed state is tracial on `ℛ_n`** (`IsCentral.tracial`). -/
theorem tracial_Rn (n : ℕ) {x y : L2Q K →L[ℂ] L2Q K} (hx : x ∈ Rn M Ω n)
    (hy : y ∈ crossed M Ω) :
    ⟪xin Ω n, (x * y) (xin Ω n)⟫_ℂ = ⟪xin Ω n, (y * x) (xin Ω n)⟫_ℂ :=
  IsCentral.tracial (isSeparating_xin M Ω hs hc n) (isCyclic_xin M Ω hs hc n)
    (isCentral_of_mem_Rn M Ω hx) hy

/-- `d_n = e^{a_n}`, the Radon–Nikodym derivative of `ψ̂` with respect to `ψ_{ξ_n}`. -/
noncomputable def dn (n : ℕ) : L2Q K →L[ℂ] L2Q K := expA (an n) 1

theorem dn_mem (n : ℕ) : dn (K := K) n ∈ crossed M Ω := expA_mem _ (an_mem M Ω n) 1

theorem isSelfAdjoint_dn (n : ℕ) : IsSelfAdjoint (dn (K := K) n) := expA_isSelfAdjoint 1

include hs hc in
theorem isCentral_expA_an (n : ℕ) (r : ℝ) :
    IsCentral (crossed M Ω) (Ωh Ω) (expA (an (K := K) n) r) :=
  ⟨expA_mem _ (an_mem M Ω n) r, commute_expA (commute_an_R M Ω hs hc n) r⟩

include hs hc in
/-- **`ψ̂ = ψ_{ξ_n}(d_n ·)` on `ℛ`**: the state of `Ω̂` is the `d_n`-perturbation of the state
of `ξ_n`. -/
theorem inner_Ωh_eq_inner_xin_dn (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    ⟪Ωh Ω, x (Ωh Ω)⟫_ℂ = ⟪xin Ω n, (dn (K := K) n * x) (xin Ω n)⟫_ℂ := by
  have hsa := isSelfAdjoint_an (K := K) n
  have hsh : IsSelfAdjoint (expA (an (K := K) n) (-(1 / 2))) := expA_isSelfAdjoint _
  have hcen := isCentral_expA_an M Ω hs hc n (1 / 2)
  have e : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
  have e0 : (-(1 / 2 : ℝ)) + 1 / 2 = 0 := by norm_num
  have hop : expA (an (K := K) n) (-(1 / 2)) * (dn n * x) * expA (an (K := K) n) (-(1 / 2)) =
      expA (an (K := K) n) (1 / 2) * (x * expA (an (K := K) n) (-(1 / 2))) := by
    rw [dn]
    simp only [mul_assoc]
    rw [← mul_assoc (expA (an (K := K) n) (-(1 / 2))), expA_mul hsa, e]
  have hop2 : x * expA (an (K := K) n) (-(1 / 2)) * expA (an (K := K) n) (1 / 2) = x := by
    rw [mul_assoc, expA_mul hsa, e0, expA_zero hsa, mul_one]
  have h1 : ⟪xin Ω n, (dn (K := K) n * x) (xin Ω n)⟫_ℂ =
      ⟪Ωh Ω, (expA (an (K := K) n) (1 / 2) *
        (x * expA (an (K := K) n) (-(1 / 2)))) (Ωh Ω)⟫_ℂ := by
    rw [xin, pvec, ← BorelCalc.inner_sa hsh, ← mul_apply_eq_comp, ← mul_apply_eq_comp, hop]
  rw [h1, IsCentral.tracial (isSeparating_Ωh M Ω hs hc) (isCyclic_Ωh M Ω hc) hcen
    (mul_mem hx (expA_mem _ (an_mem M Ω n) _)), hop2]


/-! ## The averaging weight `2^n·1_{(0,2^{-n}]}` -/

/-- The period `T_n = 2^{-n}` of `σ^{ξ_n}`. -/
noncomputable def Tn (n : ℕ) : ℝ := 1 / 2 ^ n

theorem Tn_eq (n : ℕ) : Tn n = 1 / 2 ^ n := rfl

theorem Tn_pos (n : ℕ) : 0 < Tn n := by rw [Tn]; positivity

theorem two_pow_mul_Tn (n : ℕ) : (2 : ℝ) ^ n * Tn n = 1 := by
  rw [Tn]; field_simp

/-- The real averaging weight `2^n·1_{(0,2^{-n}]}`: a probability density. -/
noncomputable def wtR (n : ℕ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc 0 (Tn n)) fun _ => (2 : ℝ) ^ n

/-- The averaging weight as a complex-valued function. -/
noncomputable def wt (n : ℕ) (t : ℝ) : ℂ := (wtR n t : ℂ)

theorem wtR_nonneg (n : ℕ) (t : ℝ) : 0 ≤ wtR n t :=
  Set.indicator_nonneg (fun _ _ => by positivity) t

theorem wtR_of_mem {n : ℕ} {t : ℝ} (h : t ∈ Set.Ioc (0 : ℝ) (Tn n)) : wtR n t = (2 : ℝ) ^ n :=
  Set.indicator_of_mem h _

theorem wtR_of_notMem {n : ℕ} {t : ℝ} (h : t ∉ Set.Ioc (0 : ℝ) (Tn n)) : wtR n t = 0 :=
  Set.indicator_of_notMem h _

theorem conj_wt (n : ℕ) (t : ℝ) : (starRingEnd ℂ) (wt n t) = wt n t :=
  Complex.conj_ofReal _

theorem norm_wt (n : ℕ) (t : ℝ) : ‖wt n t‖ = wtR n t := by
  rw [wt, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wtR_nonneg n t)]

theorem wt_eq_indicator (n : ℕ) :
    wt n = Set.indicator (Set.Ioc 0 (Tn n)) fun _ => (((2 : ℝ) ^ n : ℝ) : ℂ) := by
  funext t
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) (Tn n)
  · rw [Set.indicator_of_mem ht, wt, wtR_of_mem ht]
  · rw [Set.indicator_of_notMem ht, wt, wtR_of_notMem ht, Complex.ofReal_zero]

theorem integrable_wtR (n : ℕ) : Integrable (wtR n) :=
  ((continuous_const.integrableOn_Ioc (a := (0 : ℝ)) (b := Tn n))).integrable_indicator
    measurableSet_Ioc

theorem integrable_wt (n : ℕ) : Integrable (wt n) := by
  rw [wt_eq_indicator]
  exact ((continuous_const.integrableOn_Ioc (a := (0 : ℝ)) (b := Tn n))).integrable_indicator
    measurableSet_Ioc

theorem integral_wtR (n : ℕ) : ∫ t, wtR n t = 1 := by
  rw [wtR, integral_indicator measurableSet_Ioc, setIntegral_const,
    Real.volume_real_Ioc_of_le (Tn_pos n).le, sub_zero, smul_eq_mul, mul_comm]
  exact two_pow_mul_Tn n

theorem integral_wt (n : ℕ) : ∫ t, wt n t = 1 := by
  rw [wt_eq_indicator, integral_indicator measurableSet_Ioc, setIntegral_const,
    Real.volume_real_Ioc_of_le (Tn_pos n).le, sub_zero, Complex.real_smul,
    ← Complex.ofReal_mul, mul_comm, two_pow_mul_Tn, Complex.ofReal_one]

theorem integral_norm_wt (n : ℕ) : ∫ t, ‖wt n t‖ = 1 := by
  simp only [norm_wt]; exact integral_wtR n

/-- Integrating against `wt n` is averaging over one period. -/
theorem integral_wt_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (n : ℕ) (g : ℝ → E) :
    ∫ t, wt n t • g t = (((2 : ℝ) ^ n : ℝ) : ℂ) • ∫ t in (0 : ℝ)..Tn n, g t := by
  have h : (fun t => wt n t • g t) =
      Set.indicator (Set.Ioc 0 (Tn n)) fun t => (((2 : ℝ) ^ n : ℝ) : ℂ) • g t := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) (Tn n)
    · rw [Set.indicator_of_mem ht, wt, wtR_of_mem ht]
    · rw [Set.indicator_of_notMem ht, wt, wtR_of_notMem ht, Complex.ofReal_zero, zero_smul]
  rw [h, integral_indicator measurableSet_Ioc, integral_smul,
    intervalIntegral.integral_of_le (Tn_pos n).le]

theorem integrable_wt_mul {n : ℕ} {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable fun t => wt n t * g t := by
  have h : (fun t => wt n t * g t) =
      Set.indicator (Set.Ioc 0 (Tn n)) fun t => (((2 : ℝ) ^ n : ℝ) : ℂ) * g t := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) (Tn n)
    · rw [Set.indicator_of_mem ht, wt, wtR_of_mem ht]
    · rw [Set.indicator_of_notMem ht, wt, wtR_of_notMem ht, Complex.ofReal_zero, zero_mul]
  rw [h]
  exact ((continuous_const.mul hg).integrableOn_Ioc).integrable_indicator measurableSet_Ioc

/-! ## The conditional expectation `Φ_n` -/

/-- **Haagerup's conditional expectation** `Φ_n(x) = 2^n ∫_0^{2^{-n}} σ^{ξ_n}_t(x) dt`,
realized as a weak (vectorwise) integral. -/
noncomputable def Phi (n : ℕ) (x : L2Q K →L[ℂ] L2Q K) : L2Q K →L[ℂ] L2Q K :=
  smear (wt n) (integrable_wt n) (fun t => σ (crossed M Ω) (xin Ω n) t x)
    (fun v => continuous_σ_apply (crossed M Ω) (xin Ω n) x v)
    (fun t => norm_σ_le (crossed M Ω) (xin Ω n) t x)

theorem intervalIntegrable_σ (n : ℕ) (x : L2Q K →L[ℂ] L2Q K) (ζ : L2Q K) (a b : ℝ) :
    IntervalIntegrable (fun t => σ (crossed M Ω) (xin Ω n) t x ζ) volume a b :=
  (continuous_σ_apply (crossed M Ω) (xin Ω n) x ζ).intervalIntegrable a b

theorem Phi_apply (n : ℕ) (x : L2Q K →L[ℂ] L2Q K) (ζ : L2Q K) :
    Phi M Ω n x ζ =
      (((2 : ℝ) ^ n : ℝ) : ℂ) • ∫ t in (0 : ℝ)..Tn n, σ (crossed M Ω) (xin Ω n) t x ζ := by
  rw [Phi, smear_apply, integral_wt_smul]
  rfl

theorem norm_Phi_le (n : ℕ) (x : L2Q K →L[ℂ] L2Q K) : ‖Phi M Ω n x‖ ≤ ‖x‖ := by
  have h := norm_smear_le (wt n) (integrable_wt n) (fun t => σ (crossed M Ω) (xin Ω n) t x)
    (fun v => continuous_σ_apply (crossed M Ω) (xin Ω n) x v)
    (fun t => norm_σ_le (crossed M Ω) (xin Ω n) t x)
  rwa [integral_norm_wt, one_mul] at h

include hs hc in
/-- `Φ_n` maps `ℛ` into `ℛ`. -/
theorem Phi_mem (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    Phi M Ω n x ∈ crossed M Ω :=
  smear_mem _ _ _ _ _ (crossed M Ω) fun t =>
    σ_mem (crossed M Ω) (xin Ω n) (isSeparating_xin M Ω hs hc n) (isCyclic_xin M Ω hs hc n) hx t

/-- `Φ_n` is unital. -/
theorem Phi_one (n : ℕ) : Phi M Ω n (1 : L2Q K →L[ℂ] L2Q K) = 1 := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  rw [Phi, smear_apply]
  simp only [σ_one, ContinuousLinearMap.one_apply]
  rw [integral_smul_const, integral_wt, one_smul]

theorem Phi_add (n : ℕ) (x y : L2Q K →L[ℂ] L2Q K) :
    Phi M Ω n (x + y) = Phi M Ω n x + Phi M Ω n y := by
  ext ζ
  have h : ∀ t : ℝ, σ (crossed M Ω) (xin Ω n) t (x + y) ζ =
      σ (crossed M Ω) (xin Ω n) t x ζ + σ (crossed M Ω) (xin Ω n) t y ζ := fun t => by
    rw [σ_add_op, ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.add_apply, Phi_apply, Phi_apply, Phi_apply]
  simp only [h]
  rw [intervalIntegral.integral_add (intervalIntegrable_σ M Ω n x ζ 0 (Tn n))
    (intervalIntegrable_σ M Ω n y ζ 0 (Tn n)), smul_add]

theorem Phi_smul (n : ℕ) (c : ℂ) (x : L2Q K →L[ℂ] L2Q K) :
    Phi M Ω n (c • x) = c • Phi M Ω n x := by
  ext ζ
  have h : ∀ t : ℝ, σ (crossed M Ω) (xin Ω n) t (c • x) ζ =
      c • σ (crossed M Ω) (xin Ω n) t x ζ := fun t => by
    rw [σ_smul, ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.smul_apply, Phi_apply, Phi_apply]
  simp only [h]
  rw [intervalIntegral.integral_smul, smul_comm]

/-! ## `Φ_n` lands in `ℛ_n` -/

include hs hc in
theorem periodic_σ_xin (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) (ζ : L2Q K) :
    Function.Periodic (fun t => σ (crossed M Ω) (xin Ω n) t x ζ) (Tn n) := fun t => by
  show σ (crossed M Ω) (xin Ω n) (t + Tn n) x ζ = σ (crossed M Ω) (xin Ω n) t x ζ
  rw [σ_add, Tn_eq, σ_xin_period M Ω hs hc n hx]

include hs hc in
/-- **`σ^{ξ_n}` fixes the range of `Φ_n`**: the average over one full period is invariant. -/
theorem σ_Phi (n : ℕ) (s : ℝ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    σ (crossed M Ω) (xin Ω n) s (Phi M Ω n x) = Phi M Ω n x := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  have hper := periodic_σ_xin M Ω hs hc n hx ζ
  have hint : ∀ t : ℝ, Δit (crossed M Ω) (xin Ω n) s
      (σ (crossed M Ω) (xin Ω n) t x (Δit (crossed M Ω) (xin Ω n) (-s) ζ)) =
      σ (crossed M Ω) (xin Ω n) (s + t) x ζ := fun t => by
    rw [σ_add]
    simp only [σ_apply]
  have htr := intervalIntegral.integral_comp_add_left
    (f := fun u => σ (crossed M Ω) (xin Ω n) u x ζ) (a := (0 : ℝ)) (b := Tn n) s
  rw [σ_apply, Phi_apply, Phi_apply, map_smul]
  congr 1
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
    (intervalIntegrable_σ M Ω n x (Δit (crossed M Ω) (xin Ω n) (-s) ζ) 0 (Tn n))]
  simp only [hint]
  rw [htr, add_zero, hper.intervalIntegral_add_eq s 0, zero_add]

include hs hc in
/-- **`Φ_n` maps `ℛ` into the centralizer `ℛ_n`.** -/
theorem Phi_mem_Rn (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ crossed M Ω) :
    Phi M Ω n x ∈ Rn M Ω n :=
  (mem_Rn_iff_σ M Ω hs hc).mpr
    ⟨Phi_mem M Ω hs hc n hx, fun s => σ_Phi M Ω hs hc n s hx⟩

/-- **`Φ_n` is the identity on `ℛ_n`**, so it is a projection onto `ℛ_n`. -/
theorem Phi_eq_self (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : x ∈ Rn M Ω n) :
    Phi M Ω n x = x := by
  refine ContinuousLinearMap.ext fun ζ => ?_
  have hfix : ∀ t : ℝ, σ (crossed M Ω) (xin Ω n) t x = x := fun t =>
    σ_eq_self_of_commute_R (crossed M Ω) (xin Ω n) (isCentral_of_mem_Rn M Ω hx).2 t
  rw [Phi, smear_apply]
  simp only [hfix]
  rw [integral_smul_const, integral_wt, one_smul]

/-! ## `Φ_n` preserves the state, positivity and self-adjointness -/

/-- **`ψ_{ξ_n} ∘ Φ_n = ψ_{ξ_n}`.** -/
theorem inner_xin_Phi (n : ℕ) (x : L2Q K →L[ℂ] L2Q K) :
    ⟪xin Ω n, Phi M Ω n x (xin Ω n)⟫_ℂ = ⟪xin Ω n, x (xin Ω n)⟫_ℂ := by
  rw [Phi, inner_smear]
  simp only [inner_Ω_σ]
  rw [integral_mul_const, integral_wt, one_mul]

theorem isSelfAdjoint_σ (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : IsSelfAdjoint x) (t : ℝ) :
    IsSelfAdjoint (σ (crossed M Ω) (xin Ω n) t x) := by
  show star (σ (crossed M Ω) (xin Ω n) t x) = σ (crossed M Ω) (xin Ω n) t x
  rw [← σ_star, hx.star_eq]

theorem isSelfAdjoint_Phi (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (Phi M Ω n x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro ζ η
  have hsym : ∀ t : ℝ, ⟪σ (crossed M Ω) (xin Ω n) t x ζ, η⟫_ℂ =
      ⟪ζ, σ (crossed M Ω) (xin Ω n) t x η⟫_ℂ := fun t =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_σ M Ω n hx t) ζ η
  show ⟪Phi M Ω n x ζ, η⟫_ℂ = ⟪ζ, Phi M Ω n x η⟫_ℂ
  rw [← inner_conj_symm (Phi M Ω n x ζ) η, Phi, inner_smear, inner_smear, ← integral_conj]
  congr 1
  funext t
  rw [map_mul, conj_wt, inner_conj_symm, hsym]

theorem nonneg_σ (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : 0 ≤ x) (t : ℝ) :
    0 ≤ σ (crossed M Ω) (xin Ω n) t x := by
  have hxp := (ContinuousLinearMap.nonneg_iff_isPositive x).mp hx
  refine Resolver.Douglas.nonneg_of_re_inner
    (isSelfAdjoint_σ M Ω n hxp.isSelfAdjoint t) fun ζ => ?_
  have h : ⟪σ (crossed M Ω) (xin Ω n) t x ζ, ζ⟫_ℂ =
      ⟪x (Δit (crossed M Ω) (xin Ω n) (-t) ζ),
        Δit (crossed M Ω) (xin Ω n) (-t) ζ⟫_ℂ := by
    rw [σ_apply, ← ContinuousLinearMap.adjoint_inner_right
      (Δit (crossed M Ω) (xin Ω n) t), ← ContinuousLinearMap.star_eq_adjoint, Δit_star]
  rw [h]
  have h2 := hxp.2 (Δit (crossed M Ω) (xin Ω n) (-t) ζ)
  rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at h2

/-- **`Φ_n` is positive.** -/
theorem Phi_nonneg (n : ℕ) {x : L2Q K →L[ℂ] L2Q K} (hx : 0 ≤ x) : 0 ≤ Phi M Ω n x := by
  have hxp := (ContinuousLinearMap.nonneg_iff_isPositive x).mp hx
  refine Resolver.Douglas.nonneg_of_re_inner
    (isSelfAdjoint_Phi M Ω n hxp.isSelfAdjoint) fun ζ => ?_
  have hcont : Continuous fun t => ⟪ζ, σ (crossed M Ω) (xin Ω n) t x ζ⟫_ℂ :=
    continuous_const.inner (continuous_σ_apply (crossed M Ω) (xin Ω n) x ζ)
  rw [← inner_conj_symm (Phi M Ω n x ζ) ζ, Complex.conj_re, Phi, inner_smear,
    ← RCLike.re_to_complex, ← integral_re (integrable_wt_mul hcont)]
  refine integral_nonneg fun t => ?_
  rw [RCLike.re_to_complex, wt, Complex.re_ofReal_mul]
  exact mul_nonneg (wtR_nonneg n t)
    (Resolver.Douglas.re_inner_nonneg_of_nonneg (nonneg_σ M Ω n hx t) ζ)

end Dyn

end Haagerup

end VN

end CommutingRepetition
