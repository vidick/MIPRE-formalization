/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryQuotientChecks
import MIPRE.Foundations.Introspection.TypedPredicate

/-! # Quotient hiding comparisons in the complete typed predicate

The quotient comparisons accept every legacy accepted tuple. Deterministic
answer decoding restores legacy acceptance on every raw question and answer,
including consistency loops and both orientations of auxiliary edges.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryQuotient
open Classical
set_option backward.isDefEq.respectTransparency false
variable {PauliType PauliAnswer F A : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Decode only dual coordinates, with the CL function selected by question side. -/
def decodeAnswer (L : Bool → CL.CLFun F (ι) ℓ) :
    QuestionType PauliType ℓ → ParsedAnswer (ι → F) A PauliAnswer →
      ParsedAnswer (ι → F) A PauliAnswer
  | .inr (_, w), .read y yp a => .read y (AuxiliaryDual.decodeDual (L w) y yp) a
  | .inr (_, w), .hide y yp x => .hide y (AuxiliaryDual.decodeDual (L w) y yp) x
  | _, a => a

/-- Decoding preserves the answer constructor and hence the format check. -/
@[simp] theorem fits_decodeAnswer (L : Bool → CL.CLFun F (ι) ℓ)
    (t : QuestionType PauliType ℓ) (a : ParsedAnswer (ι → F) A PauliAnswer) :
    TypedPredicate.fits t (decodeAnswer L t a) = TypedPredicate.fits t a := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> rfl

/-- The directed tests with the two exact dual comparisons replaced by quotient comparisons. -/
def directed (L : Bool → CL.CLFun F (ι) ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → (ι) → F)
    (D : ((ι) → F) → ((ι) → F) → A → A → Bool) :
    QuestionType PauliType ℓ → QuestionType PauliType ℓ →
      ParsedAnswer ((ι) → F) A PauliAnswer → ParsedAnswer ((ι) → F) A PauliAnswer → Bool
  | .inl p, .inr (.sample, _), .pauli a, .pair z _ =>
      if p = Z then decide (projectPauli a = z) else true
  | .inr (.introspect, w), .inr (.sample, v), .pair y a, .pair z b =>
      if w = v then decide (CLChecks.sampling (L w) (y, a) (z, b)) else true
  | .inr (.introspect, w), .inr (.read, v), .pair y a, .read z zp b =>
      if w = v then decide (CLChecks.reading (y, a) (z, zp, b)) else true
  | .inr (.hide k, w), .inr (.read, v), .hide y yp x, .read z zp a =>
      if w = v ∧ k.val + 1 = ℓ then decide (CLChecks.hidingRead (L w) (y, yp, x) (z, zp, a))
      else true
  | .inr (.hide k, w), .inr (.hide j, v), .hide y yp x, .hide z zp t =>
      if w = v ∧ k.val + 1 = j.val then
        decide (hidingNext (L w) k.val (y, yp, x) (z, zp, t)) else true
  | .inl p, .inr (.hide k, w), .pauli a, .hide y yp x =>
      if p = X ∧ k.val = 0 then decide (hidingPauli (L w) (projectPauli a) (y, yp, x))
      else true
  | .inr (.introspect, false), .inr (.introspect, true), .pair x a, .pair y b => D x y a b
  | _, _, _, _ => true

variable (L : Bool → CL.CLFun F (ι) ℓ) (X Z : PauliType)
  (project : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)

/-- Every legacy directed comparison implies the quotient comparison. -/
theorem directed_of_legacy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t u : QuestionType PauliType ℓ) (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : TypedPredicate.directed L X Z project D t u a b = true) :
    directed L X Z project D t u a b = true := by
  fun_cases directed L X Z project D t u a b <;>
    simp_all only [TypedPredicate.directed, ↓reduceIte, and_self, decide_eq_true_eq]
  · exact hidingNext_of_legacy (hL _) _ _ _ h
  · exact hidingPauli_of_legacy (hL _) _ _ h

/-- Every quotient directed comparison becomes a legacy comparison after decoding. -/
theorem directed_sound (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t u : QuestionType PauliType ℓ) (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : directed L X Z project D t u a b = true) :
    TypedPredicate.directed L X Z project D t u (decodeAnswer L t a) (decodeAnswer L u b) =
      true := by
  fun_cases directed L X Z project D t u a b <;>
    simp_all only [directed, TypedPredicate.directed, decodeAnswer, CLChecks.reading,
      ↓reduceIte, and_self, decide_eq_true_eq]
  case case7 => exact hidingRead_sound (hL _) _ _ h
  case case9 =>
    apply hidingNext_sound (hL _) _ _ _ h
    omega
  case case11 =>
    apply hidingPauli_sound (hL _) _ _ _ h
    omega
  case case14 =>
    split <;> try rfl
    all_goals cases a <;> cases b <;> simp_all [-Bool.forall_bool]
    all_goals
      rename_i hbad
      exfalso
      apply hbad <;> rfl

/-- Complete typed predicate with quotient hiding comparisons. All format,
consistency, Pauli and source-game checks are unchanged. -/
def check (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (t u : QuestionType PauliType ℓ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) : Bool :=
  TypedPredicate.fits t a && TypedPredicate.fits u b &&
    (if t = u then decide (a = b) else true) &&
    (match t, u, a, b with
      | .inl p, .inl q, .pauli x, .pauli y => DP p q x y
      | _, _, _, _ => true) &&
    directed L X Z project D t u a b && directed L X Z project D u t b a

/-- Legacy acceptance always implies quotient acceptance, including both orientations. -/
theorem check_of_legacy (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (t u : QuestionType PauliType ℓ) (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : TypedPredicate.check L X Z project D DP t u a b = true) :
    check L X Z project D DP t u a b = true := by
  simp only [check, TypedPredicate.check, Bool.and_eq_true] at h ⊢
  refine ⟨⟨⟨h.1.1.1, ?_⟩, directed_of_legacy L X Z project D hL t u a b h.1.2⟩,
    directed_of_legacy L X Z project D hL u t b a h.2⟩
  rcases t with p | ⟨t,w⟩ <;> rcases u with q | ⟨u,v⟩ <;> cases a <;> cases b <;>
    exact h.1.1.2

/-- Every accepted quotient tuple is accepted by the legacy predicate after decoding.
This statement covers every raw answer, rather than only sampler outputs. -/
theorem check_sound (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (t u : QuestionType PauliType ℓ) (a b : ParsedAnswer (ι → F) A PauliAnswer)
    (h : check L X Z project D DP t u a b = true) :
    TypedPredicate.check L X Z project D DP t u (decodeAnswer L t a) (decodeAnswer L u b) =
      true := by
  simp only [check, TypedPredicate.check, Bool.and_eq_true, fits_decodeAnswer] at h ⊢
  refine ⟨⟨⟨⟨h.1.1.1.1, ?_⟩, ?_⟩,
    directed_sound L X Z project D hL t u a b h.1.2⟩,
    directed_sound L X Z project D hL u t b a h.2⟩
  · by_cases htu : t = u
    · subst u
      have hab : a = b := of_decide_eq_true (by simpa only [↓reduceIte] using h.1.1.1.2)
      subst b
      simp
    · simp [htu]
  · rcases t with p | ⟨t,w⟩ <;> rcases u with q | ⟨u,v⟩ <;> cases a <;> cases b <;>
      exact h.1.1.2

end MIPRE.Introspection.AuxiliaryQuotient
