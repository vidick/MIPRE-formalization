/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedQuotientPredicate

/-! # Changing only the Pauli payload in a parsed answer

The map may depend on the question label. Auxiliary registers and source
answers are unchanged. Endpoint-local projection agreements suffice for all
mixed checks, and equality consistency survives every deterministic map.
-/

noncomputable section
namespace MIPRE.Introspection
open Classical
set_option backward.isDefEq.respectTransparency false

namespace ParsedAnswer
variable {V A P B T : Type*} {ℓ : ℕ}

def mapPauli (f : QuestionType T ℓ → P → B) (t : QuestionType T ℓ) :
    ParsedAnswer V A P → ParsedAnswer V A B
  | .pauli a => .pauli (f t a)
  | .pair y a => .pair y a
  | .read y yp a => .read y yp a
  | .hide y yp x => .hide y yp x

@[simp] theorem fits_mapPauli {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (f : QuestionType T ℓ → P → B) (t : QuestionType T ℓ)
    (a : ParsedAnswer (ι → F) A P) :
    TypedPredicate.fits t (mapPauli f t a) = TypedPredicate.fits t a := by
  rcases t with p | ⟨u,w⟩
  · cases a <;> rfl
  · cases u <;> cases a <;> rfl

end ParsedAnswer

namespace AuxiliaryQuotient
variable {F ι A PA PB P : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (X Z : P)
  (π : PA → ι → F) (π' : PB → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (f : QuestionType P ℓ → PA → PB)

/-- Only the distinguished Pauli endpoints require projection compatibility. -/
theorem directed_mapPauli (t u : QuestionType P ℓ)
    (a b : ParsedAnswer (ι → F) A PA)
    (hp : ∀ p c, (p = X ∨ p = Z) → t = .inl p → a = .pauli c →
      π' (f (.inl p) c) = π c)
    (h : directed L X Z π D t u a b = true) :
    directed L X Z π' D t u (ParsedAnswer.mapPauli f t a)
      (ParsedAnswer.mapPauli f u b) = true := by
  fun_cases directed L X Z π D t u a b
  all_goals try simp_all only [ParsedAnswer.mapPauli, directed, ↓reduceIte]
  case case1 w a z b =>
    simpa only [ParsedAnswer.mapPauli, directed, ↓reduceIte,
      hp Z a (Or.inr rfl) rfl rfl] using h
  case case11 p k w a y yp x hw =>
    simpa only [hp X a (Or.inl rfl) rfl rfl] using h
  case case14 =>
    split <;> try rfl
    all_goals cases a <;> cases b <;> simp_all [-Bool.forall_bool]
    all_goals
      rename_i hbad
      exfalso
      apply hbad <;> rfl

/-- A type-dependent Pauli encoding or decoding preserves accepted tuples. -/
theorem check_mapPauli
    (DP : P → P → PA → PA → Bool) (DP' : P → P → PB → PB → Bool)
    (t u : QuestionType P ℓ) (a b : ParsedAnswer (ι → F) A PA)
    (hpa : ∀ p c, (p = X ∨ p = Z) → t = .inl p → a = .pauli c →
      π' (f (.inl p) c) = π c)
    (hpb : ∀ p c, (p = X ∨ p = Z) → u = .inl p → b = .pauli c →
      π' (f (.inl p) c) = π c)
    (hDP : ∀ p q x y, t = .inl p → u = .inl q → a = .pauli x → b = .pauli y →
      DP p q x y = true → DP' p q (f (.inl p) x) (f (.inl q) y) = true)
    (h : check L X Z π D DP t u a b = true) :
    check L X Z π' D DP' t u (ParsedAnswer.mapPauli f t a)
      (ParsedAnswer.mapPauli f u b) = true := by
  have hd := directed_mapPauli L X Z π π' D f t u a b hpa
  have hr := directed_mapPauli L X Z π π' D f u t b a hpb
  simp only [check, Bool.and_eq_true, ParsedAnswer.fits_mapPauli] at h ⊢
  refine ⟨⟨⟨⟨⟨h.1.1.1.1.1,h.1.1.1.1.2⟩,?_⟩,?_⟩,hd h.1.2⟩,hr h.2⟩
  · by_cases htu : t = u
    · subst u
      have hab : a = b := of_decide_eq_true (by simpa only [↓reduceIte] using h.1.1.1.2)
      subst b
      simp
    · simp [htu]
  · rcases t with p | ⟨t,w⟩ <;> rcases u with q | ⟨u,v⟩ <;>
      cases a <;> cases b <;> try rfl
    exact hDP p q _ _ rfl rfl rfl rfl h.1.1.2

end AuxiliaryQuotient

namespace ParsedAnswer
variable {V A B PA P : Type*} {ℓ : ℕ}

/-- Map the original answer in the pair and Read formats. -/
def mapAnswer (g : A → B) : ParsedAnswer V A PA → ParsedAnswer V B PA
  | .pauli a => .pauli a
  | .pair y a => .pair y (g a)
  | .read y yp a => .read y yp (g a)
  | .hide y yp x => .hide y yp x

@[simp] theorem fits_mapAnswer {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (g : A → B) (t : QuestionType P ℓ) (a : ParsedAnswer (ι → F) A PA) :
    TypedPredicate.fits t (mapAnswer g a) = TypedPredicate.fits t a := by
  rcases t with p | ⟨u,w⟩
  · cases a <;> rfl
  · cases u <;> cases a <;> rfl

end ParsedAnswer

namespace AuxiliaryQuotient
variable {F ι A B PA P : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (X Z : P) (π : PA → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (D' : (ι → F) → (ι → F) → B → B → Bool) (g : A → B)

/-- Source-predicate compatibility is required only for the actual endpoint payloads. -/
theorem directed_mapAnswer (t u : QuestionType P ℓ)
    (a b : ParsedAnswer (ι → F) A PA)
    (hD : ∀ x y c d, a = .pair x c → b = .pair y d →
      D x y c d = true → D' x y (g c) (g d) = true)
    (h : directed L X Z π D t u a b = true) :
    directed L X Z π D' t u (ParsedAnswer.mapAnswer g a)
      (ParsedAnswer.mapAnswer g b) = true := by
  fun_cases directed L X Z π D t u a b
  all_goals try (solve
    | simpa only [ParsedAnswer.mapAnswer, directed, CLChecks.hidingRead] using h
    | simp_all only [ParsedAnswer.mapAnswer, directed, CLChecks.hidingRead, ↓reduceIte])
  case case3 w y a z b =>
    have he : y = (L w).eval z ∧ a = b := by
      simpa [directed, CLChecks.sampling] using h
    simp [ParsedAnswer.mapAnswer, directed, CLChecks.sampling, he.1, he.2]
  case case5 w y a z zp b =>
    have he : y = z ∧ a = b := by simpa [directed, CLChecks.reading] using h
    simp [ParsedAnswer.mapAnswer, directed, CLChecks.reading, he.1, he.2]
  case case14 =>
    simp only [ParsedAnswer.mapAnswer, directed]
    split <;> try rfl
    all_goals cases a <;> cases b <;> simp_all [-Bool.forall_bool]
    all_goals
      rename_i hbad
      exfalso
      apply hbad <;> rfl

/-- In particular, bounded decoding of source answers preserves all accepted checks. -/
theorem check_mapAnswer (DP : P → P → PA → PA → Bool)
    (t u : QuestionType P ℓ) (a b : ParsedAnswer (ι → F) A PA)
    (hD : ∀ x y c d, a = .pair x c → b = .pair y d →
      D x y c d = true → D' x y (g c) (g d) = true)
    (hDr : ∀ x y c d, b = .pair x c → a = .pair y d →
      D x y c d = true → D' x y (g c) (g d) = true)
    (h : check L X Z π D DP t u a b = true) :
    check L X Z π D' DP t u (ParsedAnswer.mapAnswer g a)
      (ParsedAnswer.mapAnswer g b) = true := by
  have hd := directed_mapAnswer L X Z π D D' g t u a b hD
  have hr := directed_mapAnswer L X Z π D D' g u t b a hDr
  simp only [check, Bool.and_eq_true, ParsedAnswer.fits_mapAnswer] at h ⊢
  refine ⟨⟨⟨⟨⟨h.1.1.1.1.1,h.1.1.1.1.2⟩,?_⟩,?_⟩,hd h.1.2⟩,hr h.2⟩
  · by_cases htu : t = u
    · subst u
      have hab : a = b := of_decide_eq_true (by simpa only [↓reduceIte] using h.1.1.1.2)
      subst b
      simp
    · simp [htu]
  · rcases t with p | ⟨t,w⟩ <;> rcases u with q | ⟨u,v⟩ <;>
      cases a <;> cases b <;> exact h.1.1.2

end AuxiliaryQuotient
end MIPRE.Introspection
end
