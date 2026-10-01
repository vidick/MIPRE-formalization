/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.CL.DetypingSoundness
public import MIPRE.Foundations.CommutingModel

@[expose] public section

/-! # Same-state soundness of finite-game detyping, in a bipartite model

The detyping restriction of `MIPRE/Foundations/CL/DetypingSoundness.lean` (the finite-game core
of `lem:detyping-verifiers`) uses nothing of a tensor-product strategy but its conditional
failures, their nonnegativity and the averaging identity of a sampled game. It is restated here
for POVM families in a bipartite model (Phase 2 of `planning/mipco-track.md`): the families of a
strategy for the detyped game, read at the fixed graph views, are a strategy for the typed game in
the same model, and it fails at most `16^{|T|}` times as often
(`CL.Detyping.restrict_povmValue_ge`). Its readings in the two values —
`CL.Detyping.quantumValue_typedGame_ge` and `CL.Detyping.commutingOperatorValue_typedGame_ge` —
bound the typed game's value below by the detyped game's, through a supremum
(`one_sub_mul_one_sub_iSup_le`).
-/

noncomputable section

namespace MIPRE

open Finset Classical

/-- **An affine transfer of values survives the supremum.** If every value `v i` gives
`1 - c (1 - v i) ≤ Q`, with `c ≥ 1` and `Q ≥ 0`, then so does their supremum. -/
theorem one_sub_mul_one_sub_iSup_le {ι : Sort*} (v : ι → ℝ) {c Q : ℝ} (hc : 1 ≤ c) (hQ : 0 ≤ Q)
    (h : ∀ i, 1 - c * (1 - v i) ≤ Q) :
    1 - c * (1 - ⨆ i, v i) ≤ Q := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Real.iSup_of_isEmpty]
    nlinarith
  · by_contra hcon
    rw [not_le] at hcon
    have hc0 : 0 < c := by linarith
    have hlt : 1 - (1 - Q) / c < ⨆ i, v i := by
      have h1 : (1 - ⨆ i, v i) < (1 - Q) / c := by
        rw [lt_div_iff₀ hc0]
        linarith
      linarith
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hlt
    have h2 : c * (1 - v i) < 1 - Q := by
      have h3 : 1 - v i < (1 - Q) / c := by linarith
      calc c * (1 - v i) < c * ((1 - Q) / c) := mul_lt_mul_of_pos_left h3 hc0
        _ = 1 - Q := by field_simp
    linarith [h i]

namespace SampledGame

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

/-- **The failure probability of a strategy in a model is the uniform average of its conditional
failures** — `one_sub_value` for POVM families in a bipartite model. -/
theorem one_sub_povmValue [Nonempty S] {A B : Type*} [Fintype A] [Fintype B]
    (qA : S → X) (qB : S → Y) (D : X → Y → A → B → Bool) {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞]
    [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
    [PartialOrder 𝒜] [PartialOrder ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ) (MA : X → POVMIn A 𝒜)
    (MB : Y → POVMIn B ℬ) :
    1 - M.povmValue (game qA qB D) MA MB
      = (∑ s, M.condFail (game qA qB D) MA MB (qA s) (qB s)) / Fintype.card S := by
  rw [M.one_sub_povmValue_eq]
  exact sum_dist_mul qA qB (M.condFail (game qA qB D) MA MB)

end SampledGame

namespace CL.Detyping

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]
  (M : BipartiteModel 𝒞 𝒜 ℬ)

set_option linter.unusedSectionVars false

/-- Conditional failure agrees on every edge: the restricted families, at a typed question pair
on an edge, fail exactly as the original ones at the embedded questions. -/
theorem restrict_condFail_eq {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (D : Question T ι → Question T ι → A → B → Bool)
    (MA : (Coord T ι → ZMod 2) → POVMIn A 𝒜) (MB : (Coord T ι → ZMod 2) → POVMIn B ℬ)
    (x y : Question T ι) (h : E x.1 y.1) :
    M.condFail (typedGame E hne P D) (fun x => MA (question E false x))
        (fun y => MB (question E true y)) x y
      = M.condFail (game E P D) MA MB (question E false x) (question E true y) := by
  unfold BipartiteModel.condFail BipartiteModel.condWin
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change (if D x y a b then (1 : ℝ) else 0) * _ =
    (if accepts E D (question E false x) (question E true y) a b then 1 else 0) * _
  rw [accepts_question E D x y h]

/-- The typed failure is the uniform edge-and-content average of the conditional failures. -/
theorem typed_failure_povm {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (D : Question T ι → Question T ι → A → B → Bool)
    (MA : Question T ι → POVMIn A 𝒜) (MB : Question T ι → POVMIn B ℬ) :
    1 - M.povmValue (typedGame E hne P D) MA MB =
      (∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
        M.condFail (typedGame E hne P D) MA MB (uv.1, (P false uv.1).eval v)
          (uv.2, (P true uv.2).eval v)) /
      ((Graph.edges E).card * Fintype.card (ι → ZMod 2)) := by
  let _ : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine (SampledGame.one_sub_povmValue (typedQuestion (E := E) P false) (typedQuestion P true) D
    M MA MB).trans ?_
  simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, Fintype.sum_prod_type,
    typedQuestion, Bool.false_eq_true, ↓reduceIte]
  congr 1
  exact Finset.sum_coe_sort (Graph.edges E) (fun uv => ∑ v : ι → ZMod 2,
    M.condFail (typedGame E hne P D) MA MB (uv.1, (P false uv.1).eval v)
      (uv.2, (P true uv.2).eval v))

/-- The detyped failure is the uniform average over its independent graph and content seeds. -/
theorem failure_povm {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (MA : (Coord T ι → ZMod 2) → POVMIn A 𝒜) (MB : (Coord T ι → ZMod 2) → POVMIn B ℬ) :
    1 - M.povmValue (game E P D) MA MB =
      (∑ g : Graph.Coord T → ZMod 2, ∑ v : ι → ZMod 2,
        M.condFail (game E P D) MA MB ((presentation E false (P false)).eval (Sum.elim g v))
          ((presentation E true (P true)).eval (Sum.elim g v))) /
      ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2)) := by
  refine (SampledGame.one_sub_povmValue _ _ _ M MA MB).trans ?_
  let e := Equiv.sumArrowEquivProdArrow (Graph.Coord T) ι (ZMod 2)
  have hc := Fintype.card_congr e
  rw [hc, Fintype.card_prod, Graph.card_seeds, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  rw [← Fintype.sum_prod_type']
  exact (e.symm.sum_comp (fun z => M.condFail (game E P D) MA MB
    ((presentation E false (P false)).eval z) ((presentation E true (P true)).eval z))).symm

/-- The restricted families' failure is the detyped failure conditioned on valid graph seeds. -/
theorem restrict_failure_eq_povm {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (MA : (Coord T ι → ZMod 2) → POVMIn A 𝒜) (MB : (Coord T ι → ZMod 2) → POVMIn B ℬ) :
    1 - M.povmValue (typedGame E hne P D) (fun x => MA (question E false x))
        (fun y => MB (question E true y)) =
      (∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
        M.condFail (game E P D) MA MB ((presentation E false (P false)).eval (Sum.elim g v))
          ((presentation E true (P true)).eval (Sum.elim g v))) /
        ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) := by
  rw [typed_failure_povm, conditional_average E hE P hP hℓ]
  congr 1
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro v _
  exact restrict_condFail_eq M E hne P D MA MB _ _ (Finset.mem_filter.mp huv).2

variable [StarOrderedRing 𝒜] [StarOrderedRing ℬ]

/-- **The finite-game detyping reduction, in a bipartite model**, with the source's soundness
factor `16^{|T|}`. -/
theorem restrict_failure_le_povm {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (hψ : ‖M.ψ‖ = 1) (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (MA : (Coord T ι → ZMod 2) → POVMIn A 𝒜) (MB : (Coord T ι → ZMod 2) → POVMIn B ℬ) :
    1 - M.povmValue (typedGame E hne P D) (fun x => MA (question E false x))
        (fun y => MB (question E true y))
      ≤ (16 : ℝ) ^ Fintype.card T * (1 - M.povmValue (game E P D) MA MB) := by
  rw [restrict_failure_eq_povm M E hE hne P hP hℓ D MA MB, failure_povm M E P D MA MB]
  exact valid_average_le E hne _ (fun _ _ => M.condFail_nonneg hψ _ _)

/-- **Same-state soundness of detyping, in a bipartite model** (`lem:transports-model`): families of
value at least `1 - ε` for the detyped game, read at the fixed graph views, have value at least
`1 - 16^{|T|} ε` for the typed game, in the same model. -/
theorem restrict_povmValue_ge {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (hψ : ‖M.ψ‖ = 1) (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool)
    (MA : (Coord T ι → ZMod 2) → POVMIn A 𝒜) (MB : (Coord T ι → ZMod 2) → POVMIn B ℬ)
    {ε : ℝ} (hS : 1 - ε ≤ M.povmValue (game E P D) MA MB) :
    1 - (16 : ℝ) ^ Fintype.card T * ε ≤ M.povmValue (typedGame E hne P D)
      (fun x => MA (question E false x)) (fun y => MB (question E true y)) := by
  have h := restrict_failure_le_povm M hψ E hE hne P hP hℓ D MA MB
  have hp : 0 ≤ (16 : ℝ) ^ Fintype.card T := pow_nonneg (by norm_num) _
  nlinarith

/-! ## The two values -/

/-- **Detyping in quantum values**: the typed game's `val*` is at least
`1 - 16^{|T|}(1 - val*)` of the detyped game's. -/
theorem quantumValue_typedGame_ge {A B : Type*} [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) :
    1 - (16 : ℝ) ^ Fintype.card T * (1 - quantumValue (game E P D))
      ≤ quantumValue (typedGame E hne P D) :=
  one_sub_mul_one_sub_iSup_le _ (one_le_pow₀ (by norm_num)) (quantumValue_nonneg _)
    fun S =>
      (restrict_value_ge E hE hne P hP hℓ D S (by linarith)).trans
        (le_ciSup (TensorProductStrategy.bddAbove_range_value _) _)

/-- **Detyping in commuting-operator values**: the typed game's `ω_co` is at least
`1 - 16^{|T|}(1 - ω_co)` of the detyped game's. A commuting-operator strategy for the detyped game
is restricted in its own model (`restrict_povmValue_ge`), and the restriction is a
commuting-operator strategy (`BipartiteModel.povmValue_le_commutingOperatorValue`). -/
theorem commutingOperatorValue_typedGame_ge {T ι A B : Type} [Fintype T] [DecidableEq T]
    [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] {ℓ : ℕ}
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → B → Bool) :
    1 - (16 : ℝ) ^ Fintype.card T * (1 - commutingOperatorValue (game E P D))
      ≤ commutingOperatorValue (typedGame E hne P D) :=
  one_sub_mul_one_sub_iSup_le _ (one_le_pow₀ (by norm_num)) (commutingOperatorValue_nonneg _)
    fun S =>
      (restrict_povmValue_ge S.toModel S.toModel_ψ_norm E hE hne P hP hℓ D S.aliceMeas S.bobMeas
        (ε := 1 - S.value (game E P D)) (by rw [S.value_eq_povmValue]; linarith)).trans
        (S.toModel.povmValue_le_commutingOperatorValue S.toModel_ψ_norm _ _ _)

end CL.Detyping

end MIPRE

end
