/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.CLExplicitTransport
import MIPRE.Background.Introspection.PauliRestriction
import MIPRE.Foundations.GameDouble
import MIPRE.Foundations.GameTransportProjection

/-! # Full typed introspection under an explicit Pauli seed enumeration

The equivalence acts on all raw questions, preserves the type, and fixes the
auxiliary questions and both distinguished Pauli measurements. A permutation
of the common random content proves equality of the full question-pair law,
including mixed Pauli/auxiliary edges. The parsed predicate is intertwined on
every question and every answer, including malformed answers and loops.
-/

noncomputable section
namespace MIPRE.Introspection.ExplicitGame
open Finset Classical
open QLD.PauliCL
open QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]

/-- Raw questions consist of an introspection type and its full binary content. -/
abbrev Question (m t ℓ : ℕ) :=
  CL.Detyping.Question (QuestionType QLD.Ty ℓ) (Fin ((3*m+3)*t))

/-- Change only the Pauli contents whose decoding retains the seed. -/
def contentPermutation (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    QuestionType QLD.Ty ℓ →
      ((Fin ((3*m+3)*t) → ZMod 2) ≃ (Fin ((3*m+3)*t) → ZMod 2))
  | .inl p => binaryOutputPermutation π b p
  | .inr _ => Equiv.refl _

/-- A total equivalence of full raw typed questions, not only sampled outputs. -/
def questionEquiv (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    Question m t ℓ ≃ Question m t ℓ where
  toFun q := (q.1, contentPermutation π b q.1 q.2)
  invFun q := (q.1, (contentPermutation π b q.1).symm q.2)
  left_inv q := by simp
  right_inv q := by simp

/-- The question equivalence fixes every auxiliary question. -/
@[simp] theorem questionEquiv_aux (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (u : AuxType ℓ) (w : Bool)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    questionEquiv π b (.inr (u,w),x) = (.inr (u,w),x) := rfl

/-- The question equivalence fixes both distinguished Pauli questions. -/
@[simp] theorem questionEquiv_pauli (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : QLD.Bas)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    questionEquiv (ℓ := ℓ) π b (.inl (.pauli W),x) = (.inl (.pauli W),x) := by
  simp [questionEquiv, contentPermutation]

/-- The inverse equivalence also fixes both distinguished Pauli questions. -/
@[simp] theorem questionEquiv_symm_pauli (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : QLD.Bas)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    (questionEquiv (ℓ := ℓ) π b).symm (.inl (.pauli W),x) = (.inl (.pauli W),x) :=
  (Equiv.symm_apply_eq _).mpr (questionEquiv_pauli π b W x).symm

/-- The Pauli decision predicate with the explicit seed decoder. -/
def pauliCheck (hm : m ∣ Fintype.card F) (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QLD.Ty) (x y : Fin ((3*m+3)*t) → ZMod 2) :
    QLD.Answer F m d → QLD.Answer F m d → Bool :=
  QLD.accepts hm (binaryDecode π b p x) (binaryDecode π b q y)

/-- The actual explicit-selector typed game, with the same source predicate. -/
def game (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
    (D : (ι → F₀) → (ι → F₀) → A → A → Bool) :
    Game (Question m t ℓ) (Question m t ℓ)
      (ParsedAnswer (ι → F₀) A (QLD.Answer F m d))
      (ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :=
  TypedEstimates.parsedGame QLD.adj (.pauli .X) (.pauli .Z)
    (ExplicitSeed.binaryPresentation χ b) L project D (pauliCheck hm π b)

variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)

include hχ in
/-- The raw question equivalence intertwines every sampled typed question. -/
theorem questionEquiv_family (u : QuestionType QLD.Ty ℓ)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    questionEquiv π b (u,(TypedPresentation.family (ExplicitSeed.binaryPresentation χ b) u).eval x) =
      (u,(TypedPresentation.family (QLD.PauliCL.binaryPresentation hm b) u).eval
        (binarySeedPermutation π b x)) := by
  cases u with
  | inl p =>
    exact congrArg (fun y => (Sum.inl p,y))
      (binaryOutputPermutation_presentation hm χ π hχ b p x)
  | inr u => rcases u with ⟨u,w⟩; simp

/-- Simultaneous seed and output equivalences preserve the joint sampling law. -/
private theorem dist_equiv {S X : Type*} [Fintype S] [Fintype X]
    (a b c d : S → X) (e : S ≃ S) (f : X ≃ X)
    (ha : ∀ s, f (a s) = c (e s)) (hb : ∀ s, f (b s) = d (e s)) (x y : X) :
    SampledGame.dist a b x y = SampledGame.dist c d (f x) (f y) := by
  unfold SampledGame.dist
  congr 1
  refine Fintype.sum_equiv e _ _ fun s => ?_
  rw [← ha, ← hb]
  simp only [Prod.mk.injEq, Equiv.apply_eq_iff_eq]

include hχ in
/-- Equality of the complete typed law, including every auxiliary and mixed edge. -/
theorem game_mu (q r : Question m t ℓ) :
    (game hm χ π b L project D).μ q r =
      (PauliRestriction.fullGame hm b L project D).μ
        (questionEquiv π b q) (questionEquiv π b r) := by
  apply dist_equiv _ _ _ _
    (Equiv.prodCongr (Equiv.refl _) (binarySeedPermutation π b)) (questionEquiv π b)
  · intro s
    exact questionEquiv_family hm χ π hχ b s.1.val.1 s.2
  · intro s
    exact questionEquiv_family hm χ π hχ b s.1.val.2 s.2

/-- Exact decision equality on all raw questions and all parsed answers. -/
theorem game_D (q r : Question m t ℓ)
    (a a' : ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :
    (game hm χ π b L project D).D q r a a' =
      (PauliRestriction.fullGame hm b L project D).D
        (questionEquiv π b q) (questionEquiv π b r) a a' := by
  rcases q with ⟨p,x⟩
  rcases r with ⟨s,y⟩
  change TypedPredicate.check L (.pauli .X) (.pauli .Z) project D
    (fun p s => pauliCheck hm π b p s x y) p s a a' =
    TypedPredicate.check L (.pauli .X) (.pauli .Z) project D
      (fun p' s' => PauliRestriction.pauliCheck hm b p' s'
        (contentPermutation π b p x) (contentPermutation π b s y)) p s a a'
  unfold TypedPredicate.check
  congr 3
  cases p <;> cases s <;> cases a <;> cases a' <;>
    simp only [pauliCheck, PauliRestriction.pauliCheck, contentPermutation,
      binaryQuestion_outputPermutation]

set_option backward.isDefEq.respectTransparency true

/-- Transport any legacy tensor strategy to the explicit full game. -/
def toExplicit (S : TensorProductStrategy (PauliRestriction.fullGame hm b L project D)) :
    TensorProductStrategy (game hm χ π b L project D) :=
  S.relabel _ (questionEquiv π b) (questionEquiv π b) (.refl _) (.refl _)

include hχ in
/-- Transport to the explicit game preserves the strategy value. -/
theorem toExplicit_value (S : TensorProductStrategy (PauliRestriction.fullGame hm b L project D)) :
    (toExplicit hm χ π b L project D S).value = S.value :=
  S.value_relabel _ (questionEquiv π b) (questionEquiv π b) (.refl _) (.refl _)
    (game_mu hm χ π hχ b L project D) (game_D hm χ π b L project D)

/-- Transport an explicit strategy back to the legacy full game, with its literal state. -/
abbrev toLegacy (S : TensorProductStrategy (game hm χ π b L project D)) :
    TensorProductStrategy (PauliRestriction.fullGame hm b L project D) :=
  S.relabel _ (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)

include hχ in
/-- Transport to the legacy game preserves the strategy value. -/
theorem toLegacy_value (S : TensorProductStrategy (game hm χ π b L project D)) :
    (toLegacy hm χ π b L project D S).value = S.value := by
  apply S.value_relabel _ (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
  · intro q r
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply] using
      (game_mu hm χ π hχ b L project D ((questionEquiv π b).symm q)
        ((questionEquiv π b).symm r)).symm
  · intro q r a a'
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply] using
      (game_D hm χ π b L project D ((questionEquiv π b).symm q)
        ((questionEquiv π b).symm r) a a').symm

/-- Legacy transport preserves the literal shared state. -/
theorem toLegacy_state (S : TensorProductStrategy (game hm χ π b L project D)) :
    S.RelabelStateEq (PauliRestriction.fullGame hm b L project D)
      (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _) :=
  S.relabelStateEq (PauliRestriction.fullGame hm b L project D)
    (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)

set_option linter.defProp false in
/-- Legacy transport preserves both register dimensions. The proof's inferred
type avoids reducing the concrete games when comparing strategy projections. -/
def toLegacy_dimensions (S : TensorProductStrategy (game hm χ π b L project D)) :=
  And.intro
    (S.relabel_dA (PauliRestriction.fullGame hm b L project D)
      (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _))
    (S.relabel_dB (PauliRestriction.fullGame hm b L project D)
      (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _))

include hχ in
/-- The two full typed presentations have the same quantum value. -/
theorem quantumValue_eq : quantumValue (game hm χ π b L project D) =
    quantumValue (PauliRestriction.fullGame hm b L project D) :=
  quantumValue_eq_of_equiv _ _ (questionEquiv π b) (questionEquiv π b) (.refl _) (.refl _)
    (game_mu hm χ π hχ b L project D) (game_D hm χ π b L project D)

/-- Legacy transport preserves Alice's distinguished Pauli effects. -/
theorem toLegacy_pauli_A (S : TensorProductStrategy (game hm χ π b L project D))
    (W : QLD.Bas) (a : ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :
    S.RelabelPAEq (PauliRestriction.fullGame hm b L project D)
      (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
      (.inl (.pauli W),0) a (.inl (.pauli W),0) a :=
  S.relabelPAEq (PauliRestriction.fullGame hm b L project D)
    (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
    (.inl (.pauli W),0) a (.inl (.pauli W),0) a
    (questionEquiv_symm_pauli π b W 0) rfl

/-- Legacy transport preserves Bob's distinguished Pauli effects. -/
theorem toLegacy_pauli_B (S : TensorProductStrategy (game hm χ π b L project D))
    (W : QLD.Bas) (a : ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :
    S.RelabelPBEq (PauliRestriction.fullGame hm b L project D)
      (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
      (.inl (.pauli W),0) a (.inl (.pauli W),0) a :=
  S.relabelPBEq (PauliRestriction.fullGame hm b L project D)
    (questionEquiv π b).symm (questionEquiv π b).symm (.refl _) (.refl _)
    (.inl (.pauli W),0) a (.inl (.pauli W),0) a
    (questionEquiv_symm_pauli π b W 0) rfl

variable [DecidableEq A]

/-- The same relabeling on the doubled questions used by PCC completeness. -/
abbrev pccToExplicit (S : SyncStrategy (PauliRestriction.fullGame hm b L project D).doubled) :
    SyncStrategy (game hm χ π b L project D).doubled :=
  S.relabel _ (Equiv.prodCongr (.refl Bool) (questionEquiv π b)) (.refl _)

include hχ in
/-- Relabeling the doubled game preserves the PCC property. -/
theorem pccToExplicit_isPCC
    (S : SyncStrategy (PauliRestriction.fullGame hm b L project D).doubled) (hS : S.IsPCC) :
    (pccToExplicit hm χ π b L project D S).IsPCC := by
  apply SyncStrategy.isPCC_relabel hS
  intro q r
  simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    game_mu hm χ π hχ b L project D]

include hχ in
/-- Relabeling the doubled game preserves the strategy value. -/
theorem pccToExplicit_value
    (S : SyncStrategy (PauliRestriction.fullGame hm b L project D).doubled) :
    (pccToExplicit hm χ π b L project D S).value = S.value := by
  apply S.value_relabel _ (Equiv.prodCongr (.refl Bool) (questionEquiv π b)) (.refl _)
  · intro q r
    simp only [Game.doubled_μ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      game_mu hm χ π hχ b L project D]
  · intro q r a a'
    simp only [Game.doubled_D, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      game_D hm χ π b L project D]

set_option linter.defProp false in
/-- Relabeling the doubled game preserves the honest strategy dimension.
The inferred proof type keeps the concrete game parameters opaque. -/
def pccToExplicit_dimension
    (S : SyncStrategy (PauliRestriction.fullGame hm b L project D).doubled) :=
  S.relabel_d (game hm χ π b L project D).doubled
    (Equiv.prodCongr (.refl Bool) (questionEquiv π b)) (.refl _)

end MIPRE.Introspection.ExplicitGame
