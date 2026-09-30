/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.ExplicitGame
public import MIPRE.Background.Introspection.BinaryGame

@[expose] public section

/-! # Explicit-selector completeness and actual QLD restriction

These constructions consume the complete typed game equivalence. Completeness
retains the honest PCC dimension. Soundness restriction produces an actual
QLD strategy on the original state and preserves every valid Pauli effect.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): soundness restriction takes a
projective strategy of a model `M`, restricts it to the relabelled questions
(`BipartiteModel.ProjStrat.restrict`) and then to the QLD game (`PauliRestriction.strategy`), all in
the same model, so the state is unchanged by construction and the former state and dimension
equalities have no content. The valid Pauli effects are preserved as `.op` equalities. Completeness
stays on synchronous matrix strategies.
-/

noncomputable section
namespace MIPRE.Introspection.ExplicitGame
open Finset Classical
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 60000

section GenericRestriction
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  {G : Game (Question m t ℓ) (Question m t ℓ)
    (ParsedAnswer (ι → F₀) A (QLD.Answer F m d))
    (ParsedAnswer (ι → F₀) A (QLD.Answer F m d))}
  (S : M.ProjStrat G) (e : Question m t ℓ → Question m t ℓ)

/-- Ask an arbitrary source game's measurements at relabelled questions, in the same model,
before applying the checked QLD restriction. -/
abbrev restrictionOfRelabel : M.ProjStrat (QLD.qldGame (d := d) hm) :=
  PauliRestriction.strategy hm b L project D
    (S.restrict (PauliRestriction.fullGame hm b L project D) e e) (.val 0) (.val 0)

/-- Exact equality of a valid Alice Pauli effect after restriction. -/
def RestrictionPauliAEq (W : QLD.Bas) (a : (Fin m → Bool) → F) : Prop :=
  ((restrictionOfRelabel hm b L project D S e).PA (.pauli W)).op (.pauliAns a) =
    (S.PA (QuestionType.pauli (.pauli W),0)).op (.pauli (.pauliAns a))

/-- Fixing the distinguished Pauli question preserves its Alice effects. -/
theorem restrictionPauliAEq (W : QLD.Bas) (a : (Fin m → Bool) → F)
    (he : e (QuestionType.pauli (.pauli W),0) = (QuestionType.pauli (.pauli W),0)) :
    RestrictionPauliAEq hm b L project D S e W a := by
  unfold RestrictionPauliAEq restrictionOfRelabel
  rw [PauliRestriction.strategy_pauliAns_A]
  show (S.PA (e (QuestionType.pauli (.pauli W),0))).op _ = _
  rw [he]

/-- Exact equality of a valid Bob Pauli effect after restriction. -/
def RestrictionPauliBEq (W : QLD.Bas) (a : (Fin m → Bool) → F) : Prop :=
  ((restrictionOfRelabel hm b L project D S e).PB (.pauli W)).op (.pauliAns a) =
    (S.PB (QuestionType.pauli (.pauli W),0)).op (.pauli (.pauliAns a))

/-- Fixing the distinguished Pauli question preserves its Bob effects. -/
theorem restrictionPauliBEq (W : QLD.Bas) (a : (Fin m → Bool) → F)
    (he : e (QuestionType.pauli (.pauli W),0) = (QuestionType.pauli (.pauli W),0)) :
    RestrictionPauliBEq hm b L project D S e W a := by
  unfold RestrictionPauliBEq restrictionOfRelabel
  rw [PauliRestriction.strategy_pauliAns_B]
  show (S.PB (e (QuestionType.pauli (.pauli W),0))).op _ = _
  rw [he]
end GenericRestriction

section Restriction
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : M.ProjStrat (game hm χ π b L project D))

/-- Full explicit introspection restricted to the actual QLD game, in the same model. -/
abbrev qldStrategy : M.ProjStrat (QLD.qldGame (d := d) hm) :=
  restrictionOfRelabel hm b L project D S (questionEquiv π b).symm

include hχ in
/-- Restriction loses at most the full type graph's ordered-edge factor. -/
theorem qldStrategy_failure_le {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (qldStrategy hm χ π b L project D S).value ≤
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε := by
  apply PauliRestriction.strategy_failure_le
  rwa [← toLegacy_eq_restrict hm χ π b L project D S, toLegacy_value hm χ π hχ b L project D]

/-- Every valid Alice Pauli-answer effect is preserved literally. -/
theorem qldStrategy_pauliAns_A (W : QLD.Bas) (a : (Fin m → Bool) → F) :
    RestrictionPauliAEq hm b L project D S (questionEquiv π b).symm W a :=
  restrictionPauliAEq hm b L project D S (questionEquiv π b).symm W a
    (questionEquiv_symm_pauli π b W 0)

/-- Every valid Bob Pauli-answer effect is preserved literally. -/
theorem qldStrategy_pauliAns_B (W : QLD.Bas) (a : (Fin m → Bool) → F) :
    RestrictionPauliBEq hm b L project D S (questionEquiv π b).symm W a :=
  restrictionPauliBEq hm b L project D S (questionEquiv π b).symm W a
    (questionEquiv_symm_pauli π b W 0)
end Restriction

section Completeness
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m t d ℓ : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ)
  (D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)

/-- The explicit-selector full typed game has the same concrete honest PCC dimension. -/
theorem exists_perfectPCC (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
    (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (b : Module.Basis (Fin t) (ZMod 2) F) (hb : LowDegree.IsSelfDualBasis b)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (game hm χ π b L (BinaryComplete.project (d := d) b) D).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (BinaryComplete.Seed m t) * R.d := by
  obtain ⟨Q,hQ,hvQ,hdQ⟩ := BinaryComplete.exists_perfectPCC L D R hm b hb hd hL hR hv
  refine ⟨pccToExplicit hm χ π b L _ D Q,
    pccToExplicit_isPCC hm χ π hχ b L _ D Q hQ, ?_, ?_⟩
  · exact (pccToExplicit_value hm χ π hχ b L _ D Q).trans hvQ
  · exact (pccToExplicit_dimension hm χ π b L _ D Q).trans hdQ
end Completeness

section Selector
variable {k j t d ℓ : ℕ} (E : SAT.BinField k) (hj : j ≤ k)
  [Algebra (ZMod 2) E.carrier]
  {F₀ ι A : Type*} [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A]
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (b : Module.Basis (Fin t) (ZMod 2) E.carrier)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer E.carrier (2^j) d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)

/-- Concrete finite game using the implemented high-bit selector. -/
def selectorGame := game (dyadic_divides E j hj) (SeedProgram.selector E j hj)
  (seedPermutation E) b L project D

/-- Concrete selector transport: the enumeration correspondence is proved internally. -/
theorem selector_toLegacy_value
    (S : M.ProjStrat (selectorGame E hj b L project D)) :
    (toLegacy (dyadic_divides E j hj) (SeedProgram.selector E j hj)
      (seedPermutation E) b L project D S).value = S.value :=
  toLegacy_value _ _ _ (chi_seedPermutation E j hj _) b L project D S

/-- The implemented selector restricts to QLD with the same ordered-edge loss. -/
theorem selector_qldStrategy_failure_le
    (S : M.ProjStrat (selectorGame E hj b L project D))
    {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (qldStrategy (dyadic_divides E j hj) (SeedProgram.selector E j hj)
      (seedPermutation E) b L project D S).value ≤
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε :=
  qldStrategy_failure_le _ _ _ (chi_seedPermutation E j hj _) b L project D S hS

end Selector

/-- Honest completeness instantiated with the implemented selector, with no
enumeration-compatibility premise. -/
theorem selector_exists_perfectPCC {k j t d ℓ : ℕ} (E : SAT.BinField k) (hj : j ≤ k)
    [Algebra (ZMod 2) E.carrier] {A : Type*} [Fintype A] [DecidableEq A]
    (b : Module.Basis (Fin t) (ZMod 2) E.carrier) (hb : LowDegree.IsSelfDualBasis b)
    (L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord (2^j) t) ℓ)
    (D : BinaryComplete.Seed (2^j) t → BinaryComplete.Seed (2^j) t → A → A → Bool)
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (selectorGame E hj b L (BinaryComplete.project (d := d) b) D).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (BinaryComplete.Seed (2^j) t) * R.d :=
  exists_perfectPCC L D R _ _ _ (chi_seedPermutation E j hj _) b hb hd hL hR hv

end MIPRE.Introspection.ExplicitGame

end
