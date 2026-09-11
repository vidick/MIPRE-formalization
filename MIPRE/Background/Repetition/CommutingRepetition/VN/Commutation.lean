/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Commutation.lean
-/
/-
# Tracial commutation, strong closure and the extension datum (WP-B7, stage A)

Three elementary facts about the commutant `R(N)′ = vnAlg N` of the right
action (`VN/ConcreteVN.lean`), all proved with the antiunitary `J` and the
identity `J x Ω = x* Ω` on `R(N)′`:

* **commutation**: `R(N)′` commutes with `J R(N)′ J = L(N)′` — the tracial
  commutation theorem in the form the joint spectral measure of node 1.3.2
  needs (strong commutation of a left PVM with a right PVM), with no
  bicommutant theorem;
* **strong closure**: pointwise limits of sequences in `R(N)′` stay in `R(N)′`;
* **the right action of `vnModel N` is `T ↦ J T* J`**.

`vnExtension N` is the tracial extension of `exists_modulusFamily`: the
concrete von Neumann model on the same Hilbert space (`U = id`).
Infrastructure only; no manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Tracial.CommutantPullback
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Modulus

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped InnerProductSpace Topology
open Filter

universe u

variable (M : StdTracialAlgebra.{u})

/-- Two operators agreeing on `ι(M.A)` are equal. -/
theorem ext_of_eq_on_ι {F G : M.H →L[ℂ] M.H} (h : ∀ a, F (M.ι a) = G (M.ι a)) : F = G := by
  ext v
  exact M.ι_induction (p := fun v => F v = G v) (isClosed_eq F.continuous G.continuous) h v

theorem J_ι_traceVector (a : M.A) : M.J (M.ι a) = M.L (star a) M.traceVector := by
  rw [M.J_ι]
  unfold traceVector
  rw [M.L_apply, mul_one]

/-- **Tracial commutation**: `R(M)′` commutes with `J R(M)′ J`. -/
theorem vnAlg_comm_conjJ {T T' : M.H →L[ℂ] M.H} (hT : T ∈ M.vnAlg) (hT' : T' ∈ M.vnAlg) :
    T * M.conjJ T' = M.conjJ T' * T := by
  refine M.ext_of_eq_on_ι fun a => ?_
  have hLa : M.L a ∈ M.vnAlg := M.L_mem_vnAlg a
  have hLa' : M.L (star a) ∈ M.vnAlg := M.L_mem_vnAlg _
  have hι : M.ι a = M.L a M.traceVector := by
    unfold traceVector; rw [M.L_apply, mul_one]
  rw [mulA, mulA, conjJ_apply, conjJ_apply, M.J_ι_traceVector, hι]
  -- LHS: T (J (T' (L a* Ω))) = T (L a (T'* Ω))
  have e1 : M.J (T' (M.L (star a) M.traceVector)) = (M.L a * star T') M.traceVector := by
    rw [← mulA, M.J_apply_traceVector (mul_mem hT' hLa'), star_mul, map_star, star_star]
  -- RHS: J (T' (J (T (L a Ω)))) = J (T' ((L a* * T*) Ω)) = (T * L a * T'*) Ω
  have e2 : M.J (T (M.L a M.traceVector)) = (M.L (star a) * star T) M.traceVector := by
    rw [← mulA, M.J_apply_traceVector (mul_mem hT hLa), star_mul, map_star]
  rw [e1, e2, ← mulA M T (M.L a * star T') M.traceVector,
    ← mulA M T' (M.L (star a) * star T) M.traceVector,
    M.J_apply_traceVector (mul_mem hT' (mul_mem hLa' (star_mem hT)))]
  congr 1
  rw [star_mul, star_mul, star_star, mul_assoc, ← map_star, star_star]

/-- `R(M)′` is closed under pointwise limits of sequences. -/
theorem mem_vnAlg_of_tendsto {T : ℕ → M.H →L[ℂ] M.H} {L : M.H →L[ℂ] M.H}
    (hT : ∀ n, T n ∈ M.vnAlg) (h : ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (L ξ))) :
    L ∈ M.vnAlg := by
  rw [M.mem_vnAlg_iff]
  intro a
  ext ξ
  rw [mulA, mulA]
  have h1 : Tendsto (fun n => M.Rop a (T n ξ)) atTop (𝓝 (M.Rop a (L ξ))) :=
    ((M.Rop a).continuous.tendsto _).comp (h ξ)
  have h2 : Tendsto (fun n => M.Rop a (T n ξ)) atTop (𝓝 (L (M.Rop a ξ))) := by
    refine (h (M.Rop a ξ)).congr fun n => ?_
    rw [← mulA, ← M.mem_vnAlg_iff.mp (hT n) a, mulA]
  exact tendsto_nhds_unique h1 h2

/-- The right action of the concrete model is conjugation by `J` of the adjoint. -/
theorem vnModel_Rop_eq (T : ↥M.vnAlg) : M.vnModel.Rop T = M.conjJ (star T.1) := by
  refine M.vnData.eq_of_eq_on_orbit fun P hP => ?_
  show M.vnData.right T (P M.traceVector) = _
  rw [M.vnData.right_apply T hP, conjJ_apply, M.J_apply_traceVector hP, ← mulA,
    M.J_apply_traceVector (mul_mem (star_mem T.2) (star_mem hP)), star_mul, star_star, star_star]

/-- `Lv` as a unital star algebra homomorphism `M.A →⋆ₐ[ℂ] vnAlg M`. -/
noncomputable def LvHom : M.A →⋆ₐ[ℂ] ↥M.vnAlg where
  toFun := M.Lv
  map_one' := M.Lv_one
  map_mul' := M.Lv_mul
  map_zero' := Subtype.ext (map_zero M.L)
  map_add' := fun a b => Subtype.ext (map_add M.L a b)
  commutes' := fun c => Subtype.ext (by
    show M.L (algebraMap ℂ M.A c) = (algebraMap ℂ ↥M.vnAlg c).1
    rw [AlgHomClass.commutes]
    rfl)
  map_star' := M.Lv_star

/-- **The tracial extension of WP-B7**: the concrete von Neumann model on the same L². -/
noncomputable def vnExtension : TracialExtension M where
  N' := M.vnModel
  emb := M.LvHom
  U := LinearIsometryEquiv.refl ℂ M.H
  U_ι := fun a => by
    show M.ι a = M.L a M.traceVector
    unfold traceVector; rw [M.L_apply, mul_one]
  L_emb := fun a ξ => rfl
  R_emb := fun a ξ => by
    have h : M.conjJ (star (M.L a)) ξ = M.Rop a ξ := by
      rw [conjJ_apply, ← map_star, M.J_L_J, star_star]
    show M.vnModel.Rop (M.Lv a) ξ = M.Rop a ξ
    rw [M.vnModel_Rop_eq]
    exact h

end StdTracialAlgebra

end CommutingRepetition
