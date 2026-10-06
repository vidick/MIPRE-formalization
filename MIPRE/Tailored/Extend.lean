/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Data.Presents
public import MIPRE.Tailored.Repeat.Strategy
public import MIPRE.Foundations.GameRestrict
public import MIPRE.Foundations.VerifierValue

@[expose] public section

/-!
# Extending a tailored game along an embedding of its questions

A tailored game `G'` on `X'` *extends* a tailored game `G` on `X` along an embedding
`e : X ↪ X'` (`TailoredGame.Extends`) when it has the weights, the lengths and the constraints
of `G` on the image of `e`, and no weight off it. This is how the game of a polynomial-time
tailored verifier on an input, whose questions are the strings of length at most `B`, relates to
the game of the tailored verifier it simulates, whose questions are the vectors of `𝔽₂^s`
(`MIPRE/Tailored/ClassVerifier.lean`).

* `Extends.valStar_eq`: the two games have the same quantum value. Restricting `G'` to the
  image changes nothing, the distribution being supported there
  (`quantumValue_restrictQuestions`); the answers of length at most `G.maxLen` then sit inside
  those of length at most `G'.maxLen`, and the canonical decider rejects the longer ones
  (`quantumValue_extendAnswers`).
* `Extends.hasPerfectZPC`: a perfect ZPC strategy of `G` gives one of `G'`, with its observables
  on the image and identities off it, where no question is asked: the strategy pulled back along
  the inverse of `e` (`PermStrategy.comap`, `Tailored/Repeat/Strategy.lean`).
* `Extends.doubled`: the doubled games extend each other along `Bool × e`, so the completeness
  clause of `TMIP*`, read on the doubled game, transfers too.
-/

namespace MIPRE.Tailored

open Cost Verifier

namespace TailoredGame

variable {X X' : Type*} [Fintype X] [Fintype X']

/-- **`G'` extends `G` along `e`**: the weights, the lengths and the constraints of `G` on the
image of `e`, and no weight off it. -/
structure Extends (G' : TailoredGame X') (G : TailoredGame X) (e : X ↪ X') : Prop where
  μ_eq : ∀ x y, G'.μ (e x) (e y) = G.μ x y
  support : ∀ x' y', G'.μ x' y' ≠ 0 → (∃ x, e x = x') ∧ ∃ y, e y = y'
  lenR_eq : ∀ x, G'.lenR (e x) = G.lenR x
  lenL_eq : ∀ x, G'.lenL (e x) = G.lenL x
  cons_eq : ∀ x y, G'.cons (e x) (e y) = G.cons x y

/-- A tailored game has a question: its weights sum to `1`. -/
theorem nonempty (G : TailoredGame X) : Nonempty X := by
  by_contra hX
  rw [not_nonempty_iff] at hX
  have h := G.μ_sum_one
  simp at h

namespace Extends

variable {G' : TailoredGame X'} {G : TailoredGame X} {e : X ↪ X'}

theorem len_eq (h : G'.Extends G e) (x : X) : G'.len (e x) = G.len x := by
  unfold TailoredGame.len
  rw [h.lenR_eq, h.lenL_eq]

/-- The canonical deciders agree on the image. -/
theorem accepts_iff (h : G'.Extends G e) (x y : X) (a b : BitStr) :
    G'.Accepts (e x) (e y) a b ↔ G.Accepts x y a b := by
  unfold TailoredGame.Accepts
  rw [h.len_eq, h.len_eq, h.lenR_eq, h.lenR_eq, h.cons_eq]

theorem maxLen_le (h : G'.Extends G e) : G.maxLen ≤ G'.maxLen :=
  Finset.sup_le fun x _ => (h.len_eq x).symm.trans_le (Finset.le_sup (Finset.mem_univ (e x)))

/-! ## The quantum value -/

/-- **The quantum value is that of `G`.** -/
theorem valStar_eq (h : G'.Extends G e) : G'.valStar = G.valStar := by
  classical
  haveI := G.nonempty
  have hsum : ∑ x, ∑ y, G'.toGame.μ (e x) (e y) = 1 := by
    show ∑ x, ∑ y, G'.μ (e x) (e y) = 1
    simp_rw [h.μ_eq]
    exact G.μ_sum_one
  set Gmid := G'.toGame.restrict e e hsum with hGmid
  have h1 : quantumValue Gmid = quantumValue G'.toGame :=
    quantumValue_restrictQuestions G'.toGame Gmid e e (fun _ _ => rfl) h.support
      (fun _ _ _ _ => rfl)
  have h2 : quantumValue Gmid = quantumValue G.toGame := by
    refine quantumValue_extendAnswers G.toGame Gmid (Answers.castLE h.maxLen_le)
      (Answers.castLE h.maxLen_le) h.μ_eq (fun x y a b => ?_) (fun x y a' b' hab => ?_)
    · show decide (G'.Accepts (e x) (e y) a.1 b.1) = decide (G.Accepts x y a.1 b.1)
      rw [decide_eq_decide]
      exact h.accepts_iff x y a.1 b.1
    · have hacc : G'.Accepts (e x) (e y) a'.1 b'.1 := of_decide_eq_true hab
      rw [h.accepts_iff] at hacc
      have ha : a'.1.length ≤ G.maxLen :=
        hacc.1.trans_le (Finset.le_sup (f := G.len) (Finset.mem_univ x))
      have hb : b'.1.length ≤ G.maxLen :=
        hacc.2.1.trans_le (Finset.le_sup (f := G.len) (Finset.mem_univ y))
      exact ⟨⟨⟨a'.1, ha⟩, Subtype.ext rfl⟩, ⟨⟨b'.1, hb⟩, Subtype.ext rfl⟩⟩
  rw [valStar, valStar, ← h1, h2]

/-! ## Perfect ZPC strategies -/

/-- **A perfect ZPC strategy of `G` gives one of `G'`**: the strategy pulled back along the
inverse of `e` (`PermStrategy.comap`), with its observables at the questions of the image and
identities elsewhere. -/
theorem hasPerfectZPC (h : G'.Extends G e) (hG : G.HasPerfectZPC) : G'.HasPerfectZPC := by
  obtain ⟨S, hS⟩ := hG
  haveI := G.nonempty
  have hφ : ∀ x, Function.invFun e (e x) = x := Function.leftInverse_invFun e.injective
  have hedge : ∀ y₁ y₂, 0 < G'.μ y₁ y₂ →
      SameLens G G' (Function.invFun e) y₁ ∧ SameLens G G' (Function.invFun e) y₂ ∧
        0 < G.μ (Function.invFun e y₁) (Function.invFun e y₂) := by
    intro y₁ y₂ hpos
    obtain ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩ := h.support _ _ hpos.ne'
    simp only [SameLens, hφ, h.lenR_eq, h.lenL_eq, and_self, true_and]
    rwa [← h.μ_eq]
  refine ⟨S.comap G' (Function.invFun e) hedge,
    S.value_comap_eq_one hS (Function.invFun e) hedge fun y₁ y₂ hpos a b hacc => ?_⟩
  obtain ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩ := h.support _ _ hpos.ne'
  rw [hφ, hφ] at hacc
  exact (h.accepts_iff x₁ x₂ a b).2 hacc

/-! ## The doubled games -/

/-- **The doubled games extend each other** along `Bool × e`. -/
theorem doubled (h : G'.Extends G e) :
    G'.doubled.Extends G.doubled ((Function.Embedding.refl Bool).prodMap e) where
  μ_eq p q := by
    show (if p.1 = false ∧ q.1 = true then G'.μ (e p.2) (e q.2) else 0) =
      if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0
    rw [h.μ_eq]
  support p q hpq := by
    have hpq' : (if p.1 = false ∧ q.1 = true then G'.μ p.2 q.2 else 0) ≠ 0 := hpq
    have hμ : G'.μ p.2 q.2 ≠ 0 := by
      intro h0
      exact hpq' (by split_ifs <;> simp [h0])
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h.support _ _ hμ
    exact ⟨⟨(p.1, x), Prod.ext rfl hx⟩, ⟨(q.1, y), Prod.ext rfl hy⟩⟩
  lenR_eq p := h.lenR_eq p.2
  lenL_eq p := h.lenL_eq p.2
  cons_eq p q := h.cons_eq p.2 q.2

end Extends

end TailoredGame

end MIPRE.Tailored

end
