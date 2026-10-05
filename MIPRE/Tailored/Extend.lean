/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Data.Presents
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
  on the image and identities off it, where no question is asked (`Extends.strategy`).
* `Extends.doubled`: the doubled games extend each other along `Bool × e`, so the completeness
  clause of `TMIP*`, read on the doubled game, transfers too.
-/

namespace MIPRE.Tailored

open Cost Verifier

/-- Casting the answer vector of a Fourier transform along an equality of lengths. -/
theorem fourierProj_cast {R : Type*} [Ring R] [Algebra ℂ R] {n m : ℕ} (hnm : n = m)
    (U : Fin m → R) (a : Fin n → Bool) :
    fourierProj (fun i => U (Fin.cast hnm i)) a =
      fourierProj U fun j => a (Fin.cast hnm.symm j) := by
  subst hnm
  rfl

/-- A strategy's observables at equal questions, read along equal lengths. -/
theorem PermStrategy.U_congr {X : Type*} [Fintype X] {G : TailoredGame X} (S : PermStrategy G)
    {x y : X} (hxy : x = y) {n : ℕ} (p : n = G.len x) (q : n = G.len y) (i : Fin n) :
    S.U x (Fin.cast p i) = S.U y (Fin.cast q i) := by
  subst hxy
  rfl

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
theorem valStar_eq [Nonempty X] (h : G'.Extends G e) : G'.valStar = G.valStar := by
  classical
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

/-- A question of the image has the length of its preimage. -/
theorem len_choose (h : G'.Extends G e) {x' : X'} (hx : ∃ x, e x = x') :
    G'.len x' = G.len hx.choose :=
  (congrArg G'.len hx.choose_spec).symm.trans (h.len_eq _)

open Classical in
/-- **The extended strategy**: the strategy's observables at the questions of the image, and
identities elsewhere. -/
noncomputable def strategy (h : G'.Extends G e) (S : PermStrategy G) : PermStrategy G' where
  m := S.m
  m_pos := S.m_pos
  U x' i := if hx : ∃ x, e x = x' then S.U hx.choose (Fin.cast (h.len_choose hx) i) else 1
  signedPerm x' i := by
    by_cases hx : ∃ x, e x = x'
    · obtain ⟨σ, s, hσ⟩ := S.signedPerm hx.choose (Fin.cast (h.len_choose hx) i)
      exact ⟨σ, s, by rw [dite_eq_left hx, hσ]⟩
    · exact ⟨1, fun _ => false, by rw [dite_eq_right hx, signedPermMatrix_one_one]⟩
  invol x' i := by
    by_cases hx : ∃ x, e x = x'
    · rw [dite_eq_left hx]; exact S.invol _ _
    · rw [dite_eq_right hx, one_mul]
  comm x' i j := by
    by_cases hx : ∃ x, e x = x'
    · simp only [dite_eq_left hx]; exact S.comm _ _ _
    · simp only [dite_eq_right hx]
  zAligned x' i hi := by
    by_cases hx : ∃ x, e x = x'
    · rw [dite_eq_left hx]
      refine S.zAligned _ _ ?_
      have hR : G'.lenR x' = G.lenR hx.choose :=
        (congrArg G'.lenR hx.choose_spec).symm.trans (h.lenR_eq _)
      simpa [hR] using hi
    · rw [dite_eq_right hx]; exact Matrix.isDiag_one
  commEdges x' y' hxy i j := by
    obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h.support _ _ hxy.ne'
    have hx : ∃ x₀, e x₀ = e x := ⟨x, rfl⟩
    have hy : ∃ y₀, e y₀ = e y := ⟨y, rfl⟩
    simp only [dite_eq_left hx, dite_eq_left hy]
    refine S.commEdges _ _ ?_ _ _
    rw [e.injective hx.choose_spec, e.injective hy.choose_spec, ← h.μ_eq]
    exact hxy

/-- The extended strategy's measurement at a question of the image is the strategy's. -/
theorem proj_strategy (h : G'.Extends G e) (S : PermStrategy G) (x : X)
    (a : Fin (G.len x) → Bool) :
    (h.strategy S).proj (e x) (fun i => a (Fin.cast (h.len_eq x) i)) = S.proj x a := by
  classical
  have hx : ∃ x₀, e x₀ = e x := ⟨x, rfl⟩
  have hU : (h.strategy S).U (e x) = fun i => S.U x (Fin.cast (h.len_eq x) i) := by
    funext i
    show (if hx : ∃ x₀, e x₀ = e x then S.U hx.choose (Fin.cast (h.len_choose hx) i)
      else 1) = _
    rw [dite_eq_left hx]
    exact S.U_congr (e.injective hx.choose_spec) _ _ i
  unfold PermStrategy.proj
  rw [hU]
  exact fourierProj_cast (h.len_eq x) (S.U x) _

/-- Reindexing a sum over answer vectors along an equality of lengths. -/
theorem sum_cast {M : Type*} [AddCommMonoid M] {n m : ℕ} (hnm : n = m)
    (f : (Fin m → Bool) → M) :
    ∑ a : Fin m → Bool, f a = ∑ a : Fin n → Bool, f fun i => a (Fin.cast hnm.symm i) := by
  subst hnm
  rfl

/-- **The extended strategy has the strategy's value.** -/
theorem value_strategy (h : G'.Extends G e) (S : PermStrategy G) :
    (h.strategy S).value = S.value := by
  unfold PermStrategy.value
  symm
  refine Fintype.sum_of_injective e e.injective _ _ (fun x' hx' => ?_) fun x => ?_
  · refine Finset.sum_eq_zero fun y' _ => Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => ?_
    have h0 : G'.μ x' y' = 0 := by
      by_contra hne
      obtain ⟨⟨x, hx⟩, -⟩ := h.support _ _ hne
      exact hx' ⟨x, hx⟩
    rw [h0, zero_mul, zero_mul]
  refine Fintype.sum_of_injective e e.injective _ _ (fun y' hy' => ?_) fun y => ?_
  · refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    have h0 : G'.μ (e x) y' = 0 := by
      by_contra hne
      obtain ⟨-, ⟨y, hy⟩⟩ := h.support _ _ hne
      exact hy' ⟨y, hy⟩
    rw [h0, zero_mul, zero_mul]
  rw [sum_cast (h.len_eq x).symm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_cast (h.len_eq y).symm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hA : List.ofFn (fun i => a (Fin.cast (h.len_eq x).symm.symm i)) = List.ofFn a :=
    (List.ofFn_congr (h.len_eq x).symm a).symm
  have hB : List.ofFn (fun i => b (Fin.cast (h.len_eq y).symm.symm i)) = List.ofFn b :=
    (List.ofFn_congr (h.len_eq y).symm b).symm
  rw [hA, hB, h.μ_eq, proj_strategy, proj_strategy]
  by_cases hacc : G.Accepts x y (List.ofFn a) (List.ofFn b)
  · rw [ite_eq_left hacc, ite_eq_left ((h.accepts_iff x y _ _).2 hacc)]
    rfl
  · rw [ite_eq_right hacc, ite_eq_right (mt (h.accepts_iff x y _ _).1 hacc)]
    rfl

/-- **A perfect ZPC strategy of `G` gives one of `G'`.** -/
theorem hasPerfectZPC (h : G'.Extends G e) (hG : G.HasPerfectZPC) : G'.HasPerfectZPC := by
  obtain ⟨S, hS⟩ := hG
  exact ⟨h.strategy S, (h.value_strategy S).trans hS⟩

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
