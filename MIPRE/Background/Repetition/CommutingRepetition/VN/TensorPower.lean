/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/TensorPower.lean
-/
/-
# Iterated tensor powers of a standard tracial algebra (Stage B, WP-B3b)

Iterates the binary tensor step (VN/TensorStep.lean) into `R`-fold
powers with factor ∗-embeddings, commuting images, and the
ordered-product trace law — the ingredients of the Section 6 tensor
interface (`TensorPowerData`, OTQCS/Compile.lean, eq
amplified-resource). The witness assembly for the sorried root
`exists_tensorPowerData` is deferred to the batch-#20 review per the
fidelity protocol's standing rule 1.

Convention: `tensorPow N 0 = N` (a junk value — the interface at
`R = 0` has no factors and any algebra serves), and
`tensorPow N (k+1) = tensorStep (tensorPow N k) N`, so factor `k` of
`R+1` factors is the right slot of the outermost step and factors
`< k` embed through the left slot.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.TensorStep

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace StdTracialAlgebra

open scoped TensorProduct InnerProductSpace

universe u

variable (M₁ M₂ : StdTracialAlgebra.{u})

/-! ### Factor embeddings of the binary step -/

/-- The left factor embedding `a ↦ a ⊗ 1` as a ∗-algebra hom. -/
noncomputable def stepInclLeft : M₁.A →⋆ₐ[ℂ] (M₁.A ⊗[ℂ] M₂.A) :=
  { (Algebra.TensorProduct.includeLeft :
      M₁.A →ₐ[ℂ] (M₁.A ⊗[ℂ] M₂.A)) with
    map_star' := fun a => by
      show (star a) ⊗ₜ[ℂ] (1 : M₂.A) = star (a ⊗ₜ[ℂ] (1 : M₂.A))
      rw [TensorProduct.star_tmul, star_one] }

@[simp] theorem stepInclLeft_apply (a : M₁.A) :
    stepInclLeft M₁ M₂ a = a ⊗ₜ[ℂ] (1 : M₂.A) := rfl

/-- The right factor embedding `b ↦ 1 ⊗ b` as a ∗-algebra hom. -/
noncomputable def stepInclRight : M₂.A →⋆ₐ[ℂ] (M₁.A ⊗[ℂ] M₂.A) :=
  { (Algebra.TensorProduct.includeRight :
      M₂.A →ₐ[ℂ] (M₁.A ⊗[ℂ] M₂.A)) with
    map_star' := fun b => by
      show (1 : M₁.A) ⊗ₜ[ℂ] (star b) = star ((1 : M₁.A) ⊗ₜ[ℂ] b)
      rw [TensorProduct.star_tmul, star_one] }

@[simp] theorem stepInclRight_apply (b : M₂.A) :
    stepInclRight M₁ M₂ b = (1 : M₁.A) ⊗ₜ[ℂ] b := rfl

theorem stepIncl_commute (a : M₁.A) (b : M₂.A) :
    Commute (stepInclLeft M₁ M₂ a) (stepInclRight M₁ M₂ b) := by
  show (a ⊗ₜ[ℂ] (1 : M₂.A)) * ((1 : M₁.A) ⊗ₜ[ℂ] b) =
    ((1 : M₁.A) ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] (1 : M₂.A))
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul,
    mul_one]

theorem stepτ_inclLeft_mul_inclRight (a : M₁.A) (b : M₂.A) :
    stepτ M₁ M₂ (stepInclLeft M₁ M₂ a * stepInclRight M₁ M₂ b) =
      M₁.τ a * M₂.τ b := by
  rw [stepInclLeft_apply, stepInclRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, stepτ_tmul]

/-! ### Iterated powers -/

variable (N : StdTracialAlgebra.{u})

/-- The `R`-fold tensor power, by iterating the binary step on the
right (junk value `N` itself at `R = 0`). -/
noncomputable def tensorPow : ℕ → StdTracialAlgebra.{u}
  | 0 => N
  | (k + 1) => tensorStep (tensorPow k) N

/-- The factor embeddings of the iterated power: factor `k` of `R+1`
factors is the right slot of the outermost step, earlier factors embed
through the left slot. -/
noncomputable def tensorPowIncl : (R : ℕ) → Fin R →
    (N.A →⋆ₐ[ℂ] (tensorPow N R).A)
  | 0 => Fin.elim0
  | (k + 1) =>
    Fin.snoc
      (fun i => (stepInclLeft (tensorPow N k) N).comp
        (tensorPowIncl k i))
      (stepInclRight (tensorPow N k) N)

@[simp] theorem tensorPowIncl_last (k : ℕ) :
    tensorPowIncl N (k + 1) (Fin.last k) =
      stepInclRight (tensorPow N k) N := by
  simp only [tensorPowIncl]
  exact Fin.snoc_last _ _

@[simp] theorem tensorPowIncl_castSucc (k : ℕ) (i : Fin k) :
    tensorPowIncl N (k + 1) i.castSucc =
      (stepInclLeft (tensorPow N k) N).comp (tensorPowIncl N k i) := by
  simp only [tensorPowIncl]
  exact Fin.snoc_castSucc _ _ _

/-- Images of distinct factors commute. -/
theorem tensorPowIncl_commute : ∀ (R : ℕ) ⦃i j : Fin R⦄, i ≠ j →
    ∀ a b : N.A,
      Commute (tensorPowIncl N R i a) (tensorPowIncl N R j b)
  | (k + 1), i, j, hij, a, b => by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hij' : i' ≠ j' := fun h => hij (by rw [h])
        rw [tensorPowIncl_castSucc, tensorPowIncl_castSucc]
        show Commute
          (stepInclLeft (tensorPow N k) N (tensorPowIncl N k i' a))
          (stepInclLeft (tensorPow N k) N (tensorPowIncl N k j' b))
        exact (tensorPowIncl_commute k hij' a b).map _
      · rw [tensorPowIncl_castSucc, tensorPowIncl_last]
        exact stepIncl_commute (tensorPow N k) N _ _
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [tensorPowIncl_castSucc, tensorPowIncl_last]
        exact (stepIncl_commute (tensorPow N k) N _ _).symm
      · exact absurd rfl hij

/-- The ordered-product trace law: the trace of the ordered product of
one element per factor is the product of the factor traces
(06_otqcs.tex, eq amplified-resource, in the consumed form of
`TensorPowerData.trace_prod`). -/
theorem tensorPow_trace_prod : ∀ (R : ℕ) (f : Fin R → N.A),
    (tensorPow N R).τ
        (List.ofFn fun j => tensorPowIncl N R j (f j)).prod =
      ∏ j, N.τ (f j)
  | 0, _ => by
    rw [List.ofFn_zero, List.prod_nil]
    show N.τ 1 = _
    rw [N.τ_one, Fin.prod_univ_zero]
  | (k + 1), f => by
    have hsplit : (List.ofFn fun j : Fin (k + 1) =>
        tensorPowIncl N (k + 1) j (f j)).prod =
      stepInclLeft (tensorPow N k) N
          ((List.ofFn fun i : Fin k =>
            tensorPowIncl N k i (f i.castSucc)).prod) *
        stepInclRight (tensorPow N k) N (f (Fin.last k)) := by
      rw [List.ofFn_succ_last, List.prod_append, List.prod_singleton,
        tensorPowIncl_last]
      congr 1
      rw [map_list_prod, List.map_ofFn]
      congr 1
      congr 1
      funext i
      rw [Function.comp_apply, tensorPowIncl_castSucc]
      rfl
    rw [hsplit]
    show stepτ (tensorPow N k) N _ = _
    rw [stepInclLeft_apply, stepInclRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      stepτ_tmul, tensorPow_trace_prod k, Fin.prod_univ_castSucc]

end StdTracialAlgebra

end CommutingRepetition
