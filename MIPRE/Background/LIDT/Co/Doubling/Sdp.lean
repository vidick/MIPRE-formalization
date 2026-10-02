/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Doubling.FinitePair
public import MIPRE.Background.Orthonormalization.SdpMaximizer

@[expose] public section

/-!
# The summed semidefinite form in the doubled model

Corollary 12 and Lemma 13 of `reports/c6b-paper-proofs.md`, §5.5–5.6 (item M9 of
`planning/c6b-plan.md`). Theorem 10 (`MIPRE.Orthonormalization.exists_isSummedSdp_finitePairA`,
`_finitePairB`) solves the summed semidefinite program `IsSummedSdp A T Z` (a measurement `T`, a
self-adjoint `Z ≥ Aᵢ`, `Tᵢ Z = Tᵢ Aᵢ`) in each commutant of a finite pair `M`. This file solves it
in the doubled model's local algebra and carries the solution to the placements and to the
players' abstract algebras.

* **Componentwise** (`isSummedSdp_prod_iff`): in a product of ordered `⋆`-rings, with the
  componentwise order, the summed form holds exactly when it holds in each factor.
* **Corollary 12** (`exists_isSummedSdp_loc`): for self-adjoint `Aᵢ` of the doubled local algebra
  `Loc M = LocA M × LocB M`, the solutions of Theorem 10 in `LocA M` and in `LocB M`, paired, solve
  the program in `Loc M`, with `Z = ∑ᵢ Tᵢ Aᵢ`; and so do their images under both placements of the
  doubled model (`isSummedSdp_L_iff`, `isSummedSdp_R_iff`, `exists_isSummedSdp_model`). Neither the
  property (S) of the doubled algebra nor a doubled trace is used.
* **Lemma 13** (`isSummedSdp_equivA_iff`, `isSummedSdp_equiv_iff`): the summed form pulls back
  along the `⋆`-isomorphisms `IsFinitePair.equivA : 𝒜 ≃⋆ₐ LocA M` and
  `Doubling.equiv : 𝒜 × ℬ ≃⋆ₐ Loc M` of a finite pair with star-ordered algebras, and pushes
  forward. The order agreement it rests on is `IsFinitePair.nonneg_iff_A`
  (`MIPRE/Foundations/FinitePairOrder.lean`), not re-proved here; a measurement pulls back by
  `POVMIn.mapHom hM.equivA.symm`. So Theorem 10 holds in `𝒜` itself (`exists_isSummedSdp_A`,
  `exists_isSummedSdp_B`), and Corollary 12 in the report's local algebra `𝒩 = 𝒜 × ℬ`
  (`exists_isSummedSdp_prod`), with the images under the placements of the translation.

The order transport is one lemma (`isSummedSdp_map_iff_of_nonneg_iff`): a `⋆`-ring homomorphism
between star-ordered rings that reflects nonnegativity is an order embedding, injective, and
carries the summed form both ways.
-/

namespace MIPRE.LIDT.Co.Doubling

open MIPRE.SummedSdp MIPRE.OperatorMatrix

/-! ## Transport of the summed form -/

section Transport

variable {R S : Type*} [Ring R] [StarRing R] [PartialOrder R] [Ring S] [StarRing S]
  [PartialOrder S] {G : Type*} [Fintype G]

/-- **The summed form in a product** is the summed form in each factor: the operations, the star
and the order of `R × S` are componentwise. -/
theorem isSummedSdp_prod_iff {A T : G → R × S} {Z : R × S} :
    IsSummedSdp A T Z ↔ IsSummedSdp (fun i => (A i).1) (fun i => (T i).1) Z.1 ∧
      IsSummedSdp (fun i => (A i).2) (fun i => (T i).2) Z.2 := by
  constructor
  · intro h
    exact ⟨⟨fun i => (h.nonneg i).1, by rw [← Prod.fst_sum, h.total, Prod.fst_one],
        congrArg Prod.fst h.isSelfAdjoint.star_eq, fun i => (h.dualFeasible i).1,
        fun i => congrArg Prod.fst (h.complementarySlackness i)⟩,
      ⟨fun i => (h.nonneg i).2, by rw [← Prod.snd_sum, h.total, Prod.snd_one],
        congrArg Prod.snd h.isSelfAdjoint.star_eq, fun i => (h.dualFeasible i).2,
        fun i => congrArg Prod.snd (h.complementarySlackness i)⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun i => ⟨h₁.nonneg i, h₂.nonneg i⟩,
      Prod.ext (by rw [Prod.fst_sum, h₁.total, Prod.fst_one])
        (by rw [Prod.snd_sum, h₂.total, Prod.snd_one]),
      Prod.ext h₁.isSelfAdjoint.star_eq h₂.isSelfAdjoint.star_eq,
      fun i => ⟨h₁.dualFeasible i, h₂.dualFeasible i⟩,
      fun i => Prod.ext (h₁.complementarySlackness i) (h₂.complementarySlackness i)⟩

variable [StarOrderedRing R] [StarOrderedRing S]

/-- **The summed form along a homomorphism that reflects nonnegativity**: a `⋆`-ring homomorphism
`f` between star-ordered rings with `0 ≤ f x ↔ 0 ≤ x` preserves and reflects the order, is
injective, and so carries the summed form both ways. -/
theorem isSummedSdp_map_iff_of_nonneg_iff {F : Type*} [FunLike F R S] [RingHomClass F R S]
    [StarHomClass F R S] (f : F) (hf : ∀ x, 0 ≤ f x ↔ 0 ≤ x) {A T : G → R} {Z : R} :
    IsSummedSdp (fun i => f (A i)) (fun i => f (T i)) (f Z) ↔ IsSummedSdp A T Z := by
  have hle : ∀ x y, f x ≤ f y ↔ x ≤ y := fun x y => by
    rw [← sub_nonneg, ← map_sub, hf, sub_nonneg]
  refine isSummedSdp_map_iff (f : R →+* S) (fun x y hxy => le_antisymm ?_ ?_)
    (fun x => map_star f x) hle
  · exact (hle x y).1 (le_of_eq hxy)
  · exact (hle y x).1 (le_of_eq hxy.symm)

end Transport

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1) {G : Type*} [Fintype G]

/-! ## Corollary 12: the doubled model's local algebra -/

include hM in
/-- **Corollary 12** (`reports/c6b-paper-proofs.md`, §5.5): in the doubled local algebra
`Loc M = LocA M × LocB M` of a finite pair, for finitely many self-adjoint `Aᵢ` there is a
measurement `T` with `Z = ∑ᵢ Tᵢ Aᵢ` self-adjoint, `Aᵢ ≤ Z` and `Tᵢ Z = Tᵢ Aᵢ`. It is solved
componentwise, by Theorem 10 in `LocA M` and in `LocB M`. -/
theorem exists_isSummedSdp_loc [Nonempty G] (A : G → Loc M) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → Loc M, IsSummedSdp A T (∑ i, T i * A i) := by
  obtain ⟨T₁, h₁⟩ := Orthonormalization.exists_isSummedSdp_finitePairA M hM (fun i => (A i).1)
    fun i => congrArg Prod.fst (hA i).star_eq
  obtain ⟨T₂, h₂⟩ := Orthonormalization.exists_isSummedSdp_finitePairB M hM (fun i => (A i).2)
    fun i => congrArg Prod.snd (hA i).star_eq
  refine ⟨fun i => (T₁ i, T₂ i), isSummedSdp_prod_iff.2 ⟨?_, ?_⟩⟩
  · simpa only [Prod.fst_sum, Prod.fst_mul] using h₁
  · simpa only [Prod.snd_sum, Prod.snd_mul] using h₂

/-- **The summed form under the first placement** of the doubled model: `L` preserves and reflects
the order (`L_nonneg_iff`), so it carries the summed form both ways. -/
theorem isSummedSdp_L_iff {A T : G → Loc M} {Z : Loc M} :
    IsSummedSdp (fun i => (model hM hψ).L (A i)) (fun i => (model hM hψ).L (T i))
      ((model hM hψ).L Z) ↔ IsSummedSdp A T Z :=
  isSummedSdp_map_iff_of_nonneg_iff (model hM hψ).L (L_nonneg_iff hM hψ)

/-- **The summed form under the second placement** of the doubled model: `R` preserves and
reflects the order (`R_nonneg_iff`), so it carries the summed form both ways. -/
theorem isSummedSdp_R_iff {A T : G → Loc M} {Z : Loc M} :
    IsSummedSdp (fun i => (model hM hψ).R (A i)) (fun i => (model hM hψ).R (T i))
      ((model hM hψ).R Z) ↔ IsSummedSdp A T Z :=
  isSummedSdp_map_iff_of_nonneg_iff (model hM hψ).R (R_nonneg_iff hM hψ)

/-- **Corollary 12 with the placements** (`reports/c6b-paper-proofs.md`, §5.5): for finitely many
self-adjoint `Aᵢ` of the doubled local algebra there is a measurement `T` that, with
`Z = ∑ᵢ Tᵢ Aᵢ`, solves the summed form in `Loc M` and under both placements `L` and `R`. -/
theorem exists_isSummedSdp_model [Nonempty G] (A : G → Loc M) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → Loc M, IsSummedSdp A T (∑ i, T i * A i) ∧
      IsSummedSdp (fun i => (model hM hψ).L (A i)) (fun i => (model hM hψ).L (T i))
        ((model hM hψ).L (∑ i, T i * A i)) ∧
      IsSummedSdp (fun i => (model hM hψ).R (A i)) (fun i => (model hM hψ).R (T i))
        ((model hM hψ).R (∑ i, T i * A i)) := by
  obtain ⟨T, h⟩ := exists_isSummedSdp_loc hM A hA
  exact ⟨T, h, (isSummedSdp_L_iff hM hψ).2 h, (isSummedSdp_R_iff hM hψ).2 h⟩

/-! ## Lemma 13: pull-back to the players' algebras -/

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **Lemma 13, first player** (`reports/c6b-paper-proofs.md`, §5.6): the summed form pulls back
along `IsFinitePair.equivA : 𝒜 ≃⋆ₐ LocA M` and pushes forward, by the order agreement
`IsFinitePair.nonneg_iff_A`. -/
theorem isSummedSdp_equivA_iff {A T : G → 𝒜} {Z : 𝒜} :
    IsSummedSdp (fun i => hM.equivA (A i)) (fun i => hM.equivA (T i)) (hM.equivA Z) ↔
      IsSummedSdp A T Z :=
  isSummedSdp_map_iff_of_nonneg_iff hM.equivA fun _ => hM.nonneg_iff_A

include hM in
/-- **Theorem 10 in the first player's algebra** of a finite pair (Theorem 10 in `LocA M`, pulled
back by Lemma 13): for finitely many self-adjoint `Aᵢ ∈ 𝒜` there is a measurement `T` of `𝒜` with
`Z = ∑ᵢ Tᵢ Aᵢ` self-adjoint, `Aᵢ ≤ Z` and `Tᵢ Z = Tᵢ Aᵢ`. -/
theorem exists_isSummedSdp_A [Nonempty G] (A : G → 𝒜) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → 𝒜, IsSummedSdp A T (∑ i, T i * A i) := by
  obtain ⟨T, h⟩ := Orthonormalization.exists_isSummedSdp_finitePairA M hM
    (fun i => hM.equivA (A i)) fun i => (hA i).map hM.equivA
  refine ⟨fun i => hM.equivA.symm (T i), (isSummedSdp_equivA_iff hM).1 ?_⟩
  simpa only [map_sum, map_mul, StarAlgEquiv.apply_symm_apply] using h

variable [PartialOrder ℬ] [StarOrderedRing ℬ]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- **Lemma 13, second player**: the summed form pulls back along
`IsFinitePair.equivB : ℬ ≃⋆ₐ LocB M` and pushes forward, by `IsFinitePair.nonneg_iff_B`. -/
theorem isSummedSdp_equivB_iff {A T : G → ℬ} {Z : ℬ} :
    IsSummedSdp (fun i => hM.equivB (A i)) (fun i => hM.equivB (T i)) (hM.equivB Z) ↔
      IsSummedSdp A T Z :=
  isSummedSdp_map_iff_of_nonneg_iff hM.equivB fun _ => hM.nonneg_iff_B

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
include hM in
/-- **Theorem 10 in the second player's algebra** of a finite pair (Theorem 10 in `LocB M`, pulled
back by Lemma 13). -/
theorem exists_isSummedSdp_B [Nonempty G] (A : G → ℬ) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → ℬ, IsSummedSdp A T (∑ i, T i * A i) :=
  exists_isSummedSdp_A hM.swap A hA

/-- **Lemma 13 for the report's local algebra** `𝒩 = 𝒜 × ℬ`: the summed form pulls back along the
translation `Doubling.equiv : 𝒜 × ℬ ≃⋆ₐ Loc M` and pushes forward (`equiv_nonneg_iff`). -/
theorem isSummedSdp_equiv_iff {A T : G → 𝒜 × ℬ} {Z : 𝒜 × ℬ} :
    IsSummedSdp (fun i => equiv hM (A i)) (fun i => equiv hM (T i)) (equiv hM Z) ↔
      IsSummedSdp A T Z :=
  isSummedSdp_map_iff_of_nonneg_iff (equiv hM) (equiv_nonneg_iff hM)

/-- **Corollary 12 in the report's local algebra** `𝒩 = 𝒜 × ℬ` (`reports/c6b-paper-proofs.md`,
§5.5–5.6): for finitely many self-adjoint `Aᵢ ∈ 𝒜 × ℬ` there is a measurement `T` of `𝒜 × ℬ`
that, with `Z = ∑ᵢ Tᵢ Aᵢ`, solves the summed form in `𝒜 × ℬ`, and whose translation solves it under
both placements of the doubled model. -/
theorem exists_isSummedSdp_prod [Nonempty G] (A : G → 𝒜 × ℬ) (hA : ∀ i, IsSelfAdjoint (A i)) :
    ∃ T : G → 𝒜 × ℬ, IsSummedSdp A T (∑ i, T i * A i) ∧
      IsSummedSdp (fun i => (model hM hψ).L (equiv hM (A i)))
        (fun i => (model hM hψ).L (equiv hM (T i))) ((model hM hψ).L (equiv hM (∑ i, T i * A i))) ∧
      IsSummedSdp (fun i => (model hM hψ).R (equiv hM (A i)))
        (fun i => (model hM hψ).R (equiv hM (T i)))
        ((model hM hψ).R (equiv hM (∑ i, T i * A i))) := by
  obtain ⟨T₁, h₁⟩ := exists_isSummedSdp_A hM (fun i => (A i).1)
    fun i => congrArg Prod.fst (hA i).star_eq
  obtain ⟨T₂, h₂⟩ := exists_isSummedSdp_B hM (fun i => (A i).2)
    fun i => congrArg Prod.snd (hA i).star_eq
  have h : IsSummedSdp A (fun i => (T₁ i, T₂ i)) (∑ i, (T₁ i, T₂ i) * A i) :=
    isSummedSdp_prod_iff.2 ⟨by simpa only [Prod.fst_sum, Prod.fst_mul] using h₁,
      by simpa only [Prod.snd_sum, Prod.snd_mul] using h₂⟩
  have he := (isSummedSdp_equiv_iff hM).2 h
  exact ⟨_, h, (isSummedSdp_L_iff hM hψ).2 he, (isSummedSdp_R_iff hM hψ).2 he⟩

end Order

end MIPRE.LIDT.Co.Doubling

end
