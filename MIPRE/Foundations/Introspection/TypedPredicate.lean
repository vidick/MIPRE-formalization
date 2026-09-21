/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryChecks

/-! # The parsed typed introspection predicate

This supplies the actual finite decision predicate, including both orientations
of every auxiliary test and the original game test. The Pauli predicate and
its X/Z answer projection are supplied by the Pauli test. This semantic layer
does not assert the remaining byte parser, answer clock, or program compiler.
-/

namespace MIPRE.Introspection

/-- The four parsed answer formats. Sample and Introspect share the pair format. -/
inductive ParsedAnswer (V A P : Type*)
  | pauli (a : P)
  | pair (y : V) (a : A)
  | read (y yp : V) (a : A)
  | hide (y yp x : V)
  deriving DecidableEq, Fintype

noncomputable section

namespace TypedPredicate

open Classical

variable {PauliType PauliAnswer F ι A : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Check the parsed answer constructor against the question type. -/
def fits : QuestionType PauliType ℓ → ParsedAnswer (ι → F) A PauliAnswer → Bool
  | .inl _, .pauli _ => true
  | .inr (.introspect, _), .pair _ _ => true
  | .inr (.sample, _), .pair _ _ => true
  | .inr (.read, _), .read _ _ _ => true
  | .inr (.hide _, _), .hide _ _ _ => true
  | _, _ => false

/-- One orientation of all sampling/hiding/game comparisons.
The caller checks both orientations, as required by the symmetric type graph. -/
def directed (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool) :
    QuestionType PauliType ℓ → QuestionType PauliType ℓ →
      ParsedAnswer (ι → F) A PauliAnswer → ParsedAnswer (ι → F) A PauliAnswer → Bool
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
        decide (CLChecks.hidingNext (L w) k.val (y, yp, x) (z, zp, t)) else true
  | .inl p, .inr (.hide k, w), .pauli a, .hide y yp x =>
      if p = X ∧ k.val = 0 then decide (CLChecks.hidingPauli (L w) (projectPauli a) (y, yp, x))
      else true
  | .inr (.introspect, false), .inr (.introspect, true), .pair x a, .pair y b => D x y a b
  | _, _, _, _ => true

/-- The actual parsed predicate: format, consistency, Pauli, and both auxiliary orientations. -/
def check (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (t u : QuestionType PauliType ℓ)
    (a b : ParsedAnswer (ι → F) A PauliAnswer) : Bool :=
  fits t a && fits u b && (if t = u then decide (a = b) else true) &&
    (match t, u, a, b with | .inl p, .inl q, .pauli x, .pauli y => DP p q x y | _, _, _, _ => true) &&
    directed L X Z projectPauli D t u a b && directed L X Z projectPauli D u t b a

variable (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)

/-- Accepted answers have the correct constructors on both sides. -/
theorem check_formats {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) : fits t a = true ∧ fits u b = true := by
  simp only [check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩

/-- Accepted equal-type questions have exactly equal parsed answers. -/
theorem check_consistency {t : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t t a b = true) : a = b := by
  simp only [check, Bool.and_eq_true, ↓reduceIte, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- Accepted introspection/sample answers satisfy the original full CL relation. -/
theorem check_sampling (w : Bool) {y z : ι → F} {a b : A}
    (h : check L X Z projectPauli D DP (.inr (.introspect, w)) (.inr (.sample, w))
      (.pair y a) (.pair z b) = true) : y = (L w).eval z ∧ a = b := by
  simp [check, fits, directed, CLChecks.sampling] at h
  exact @of_decide_eq_true _ (Classical.propDecidable _) h

/-- Therefore acceptance enforces every marginal check on the complete answer alphabet. -/
theorem check_sampling_prefix (w : Bool) (hL : (L w).SupportedOn Finset.univ)
    {y z : ι → F} {a b : A}
    (h : check L X Z projectPauli D DP (.inr (.introspect, w)) (.inr (.sample, w))
      (.pair y a) (.pair z b) = true) (k : ℕ) :
    ((L w).outputPrefix k y, a) = (((L w).truncate k).eval z, b) :=
  CLChecks.sampling_prefix (u := (y, a)) (v := (z, b)) hL
    (check_sampling L X Z projectPauli D DP w h) k

/-- The reading edge preserves the introspected question and answer. -/
theorem check_reading (w : Bool) {y z zp : ι → F} {a b : A}
    (h : check L X Z projectPauli D DP (.inr (.introspect, w)) (.inr (.read, w))
      (.pair y a) (.read z zp b) = true) : y = z ∧ a = b := by
  simp [check, fits, directed, CLChecks.reading] at h
  exact @of_decide_eq_true _ (Classical.propDecidable _) h

/-- The cross-introspection edge runs precisely the original decision predicate. -/
theorem check_game (x y : ι → F) (a b : A) :
    check L X Z projectPauli D DP (.inr (.introspect, false)) (.inr (.introspect, true))
      (.pair x a) (.pair y b) = D x y a b := by
  simp [check, fits, directed]

/-- Reversing the players on that edge retains the original Alice/Bob argument order. -/
theorem check_game_reversed (x y : ι → F) (a b : A) :
    check L X Z projectPauli D DP (.inr (.introspect, true)) (.inr (.introspect, false))
      (.pair y b) (.pair x a) = D x y a b := by
  simp [check, fits, directed]

/-- Acceptance includes the auxiliary check in the displayed player order. -/
theorem check_directed {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) :
    directed L X Z projectPauli D t u a b = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.2

/-- Acceptance also includes the auxiliary check with the players reversed. -/
theorem check_directed_reversed {t u : QuestionType PauliType ℓ}
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : check L X Z projectPauli D DP t u a b = true) :
    directed L X Z projectPauli D u t b a = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.2

/-- The last hiding level and Read have the tested common prefix and full dual answer. -/
theorem check_hiding_read (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ)
    {y yp x z zp : ι → F} {a : A}
    (h : check L X Z projectPauli D DP (.inr (.hide k, w)) (.inr (.read, w))
      (.hide y yp x) (.read z zp a) = true) :
    CLChecks.hidingRead (L w) (y, yp, x) (z, zp, a) := by
  have hd := check_directed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd

/-- The reversed Read/hiding edge retains the same earlier-prefix convention. -/
theorem check_hiding_read_reversed (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ)
    {y yp x z zp : ι → F} {a : A}
    (h : check L X Z projectPauli D DP (.inr (.read, w)) (.inr (.hide k, w))
      (.read z zp a) (.hide y yp x) = true) :
    CLChecks.hidingRead (L w) (y, yp, x) (z, zp, a) := by
  have hd := check_directed_reversed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd

/-- Accepted consecutive hiding answers satisfy all four source comparisons. -/
theorem check_hiding_next (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    {y yp x z zp t : ι → F}
    (h : check L X Z projectPauli D DP (.inr (.hide k, w)) (.inr (.hide j, w))
      (.hide y yp x) (.hide z zp t) = true) :
    CLChecks.hidingNext (L w) k.val (y, yp, x) (z, zp, t) := by
  have hd := check_directed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd

/-- Reversing the players does not change which hiding answer fixes the later register. -/
theorem check_hiding_next_reversed (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    {y yp x z zp t : ι → F}
    (h : check L X Z projectPauli D DP (.inr (.hide j, w)) (.inr (.hide k, w))
      (.hide z zp t) (.hide y yp x) = true) :
    CLChecks.hidingNext (L w) k.val (y, yp, x) (z, zp, t) := by
  have hd := check_directed_reversed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd

/-- The Pauli-X/hiding-first edge checks the dual first register and the untouched tail. -/
theorem check_hiding_pauli (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    {a : PauliAnswer} {y yp x : ι → F}
    (h : check L X Z projectPauli D DP (.inl X) (.inr (.hide k, w))
      (.pauli a) (.hide y yp x) = true) :
    CLChecks.hidingPauli (L w) (projectPauli a) (y, yp, x) := by
  have hd := check_directed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd

/-- The reversed first hiding edge has the same dual-map and tail comparisons. -/
theorem check_hiding_pauli_reversed (w : Bool) (k : Fin ℓ) (hk : k.val = 0)
    {a : PauliAnswer} {y yp x : ι → F}
    (h : check L X Z projectPauli D DP (.inr (.hide k, w)) (.inl X)
      (.hide y yp x) (.pauli a) = true) :
    CLChecks.hidingPauli (L w) (projectPauli a) (y, yp, x) := by
  have hd := check_directed_reversed L X Z projectPauli D DP h
  simp only [directed, hk, and_self, ↓reduceIte] at hd
  exact @of_decide_eq_true _ (Classical.propDecidable _) hd

end TypedPredicate
end
end MIPRE.Introspection
