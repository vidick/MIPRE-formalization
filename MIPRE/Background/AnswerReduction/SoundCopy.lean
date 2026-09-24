/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Honest
import MIPRE.Background.LIDT.PresentationEmbed

/-!
# Soundness of answer reduction: the low-degree test inside the predicate

Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`): on the nine type
pairs of one copy of the low-degree test, at a role pair where the answer-reduced predicate runs
that copy's test, acceptance of the predicate implies acceptance of the seeded CL test on the
questions the copy's presentation computes (`cl_accepts_of_accepts`, `cl_accepts_of_accepts6`).
The copies tested are copy `v` for the isolated player `v` (step 3), copies `3`, `4`, `5` and the
sixth for two oracles (step 4); an oracle's copies `1` and `2` are tested only through the
isolated players.

The CL test's equality subtest on equal types is the predicate's step 1, its format check is the
preamble, and its point-against-line subtests are steps 3 and 4, in either order of the players
(`CL.accepts_comm`).
-/

noncomputable section

namespace MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)

theorem subtests_comm (x y : Question F m) (a b : Answer F m d ldc) :
    subtests hm x y a b = subtests hm y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;> simp only [subtests] <;>
    first | rfl | exact decide_eq_decide.mpr eq_comm

/-- **The seeded test is symmetric in the two players.** -/
theorem accepts_comm (x y : Question F m) (a b : Answer F m d ldc) :
    accepts hm x y a b = accepts hm y x b a := by
  simp only [accepts, subtests_comm hm x y a b]
  cases x.fmtOk a <;> cases y.fmtOk b <;> rfl

end MIPRE.LIDT.CL

namespace MIPRE.AnswerReduction

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp

variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm') {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)

/-- The role pairs and copies at which the predicate runs a copy's low-degree test: copy `v` for
the isolated player `v`, copies `3`, `4`, `5` for two oracles. -/
def LDStep (r : Role) (i : Fin 5) : Prop := roleIdx r = some i ∨ (r = .oracle ∧ 2 ≤ (i : ℕ))

theorem fmtOk_of_ansFmt {i : Fin 5} {τ : Ty} {u : Ans P F} (h : ansFmt (i.castSucc, τ) u = true)
    (y : Coord P → F) : (q1 S i τ y).fmtOk (ans1 u) = true := by
  rcases u with a | a
  · cases τ <;> rcases a with _ | _ | _ <;>
      simp_all [ansFmt, tyFmt, q1, Regs.sampleOf, Sample.question, ans1, Question.fmtOk]
  · simp [ansFmt] at h
    omega

omit [NeZero P.m] in
theorem fmtOk_of_ansFmt6 {i : Fin 6} (hi : (i : ℕ) = 5) {τ : Ty} {u : Ans P F}
    (h : ansFmt (i, τ) u = true) (y : Coord P → F) : (q6 S' τ y).fmtOk (ans6 u) = true := by
  rcases u with a | a
  · simp [ansFmt, hi] at h
  · cases τ <;> rcases a with _ | _ | _ <;>
      simp_all [ansFmt, tyFmt, q6, Regs.sampleOf, Sample.question, ans6, Question.fmtOk]

/-- Step 3 or step 4(b), read off one side: a point answer of copy `i` against a line answer of
the same copy, at a role pair where the copy is tested. -/
theorem cl_accepts_of_side {r : Role} {i : Fin 5} (hr : LDStep r i) {τ' : Ty}
    (hτ' : τ' ≠ .point) {x x' : X} {y y' : Coord P → F} {u v : Ans P F}
    (h : side S S' check ((r, (i.castSucc, .point)), x, y) ((r, (i.castSucc, τ')), x', y') u v
      = true) :
    CL.accepts hm (q1 S i .point y) (q1 S i τ' y') (ans1 u) (ans1 v) = true := by
  simp only [side, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, h3⟩, h4⟩, -⟩ := h
  rcases hr with hr | ⟨rfl, h2⟩
  · rw [hr] at h3
    simp only at h3
    rw [if_pos ⟨trivial, by simp, by simp, trivial, hτ'⟩] at h3
    exact h3
  · simp only [true_and, if_true, Bool.and_eq_true] at h4
    obtain ⟨⟨-, h4b⟩, -⟩ := h4
    rw [dif_pos ⟨by simpa using h2, by simp, hτ'⟩] at h4b
    exact h4b

/-- **The copy's test inside the predicate**: on the nine type pairs of copy `i ≤ 5`, at a role pair
where the copy is tested, acceptance of the answer-reduced predicate implies acceptance of the
seeded CL test on the questions the copy's registers carry. -/
theorem cl_accepts_of_accepts {r : Role} {i : Fin 5} (hr : LDStep r i) (τ τ' : Ty) {x x' : X}
    {y y' : Coord P → F} {u v : Ans P F}
    (h : accepts S S' check ((r, (i.castSucc, τ)), x, y) ((r, (i.castSucc, τ')), x', y') u v
      = true) :
    CL.accepts hm (q1 S i τ y) (q1 S i τ' y') (ans1 u) (ans1 v) = true := by
  have h' := h
  simp only [accepts, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨hfu, hfv⟩, heq⟩, hs⟩, hs'⟩ := h'
  have fu := fmtOk_of_ansFmt S hfu y
  have fv := fmtOk_of_ansFmt S hfv y'
  by_cases hττ : τ = τ'
  · subst hττ
    rw [if_pos rfl, decide_eq_true_eq] at heq
    subst heq
    simp only [CL.accepts, fu, fv, Bool.true_and]
    cases τ <;> rcases hua : ans1 u with _ | _ | _ <;>
      simp_all [q1, Regs.sampleOf, Sample.question, subtests, Question.fmtOk]
  · by_cases hp : τ = .point
    · subst hp
      exact cl_accepts_of_side S S' check hr (Ne.symm hττ) hs
    · by_cases hp' : τ' = .point
      · subst hp'
        rw [CL.accepts_comm]
        exact cl_accepts_of_side S S' check hr hp hs'
      · simp only [CL.accepts, fu, fv, Bool.true_and]
        cases τ <;> cases τ' <;> simp_all [q1, Regs.sampleOf, Sample.question, subtests]

/-- Step 4(c), read off one side: the sixth copy's point answer against its line answer, for two
oracles. -/
theorem cl_accepts_of_side6 {i : Fin 6} (hi : (i : ℕ) = 5) {τ' : Ty} (hτ' : τ' ≠ .point)
    {x x' : X} {y y' : Coord P → F} {u v : Ans P F}
    (h : side S S' check ((.oracle, (i, .point)), x, y) ((.oracle, (i, τ')), x', y') u v
      = true) :
    CL.accepts hm' (q6 S' .point y) (q6 S' τ' y') (ans6 u) (ans6 v) = true := by
  simp only [side, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, h4⟩, -⟩ := h
  simp only [true_and, if_true, Bool.and_eq_true] at h4
  obtain ⟨-, h4c⟩ := h4
  rw [if_pos ⟨hi, hi, hτ'⟩] at h4c
  exact h4c

/-- **The sixth copy's test inside the predicate**, for two oracles. -/
theorem cl_accepts_of_accepts6 {i : Fin 6} (hi : (i : ℕ) = 5) (τ τ' : Ty) {x x' : X}
    {y y' : Coord P → F} {u v : Ans P F}
    (h : accepts S S' check ((.oracle, (i, τ)), x, y) ((.oracle, (i, τ')), x', y') u v = true) :
    CL.accepts hm' (q6 S' τ y) (q6 S' τ' y') (ans6 u) (ans6 v) = true := by
  have h' := h
  simp only [accepts, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨hfu, hfv⟩, heq⟩, hs⟩, hs'⟩ := h'
  have fu := fmtOk_of_ansFmt6 S' hi hfu y
  have fv := fmtOk_of_ansFmt6 S' hi hfv y'
  by_cases hττ : τ = τ'
  · subst hττ
    rw [if_pos rfl, decide_eq_true_eq] at heq
    subst heq
    simp only [CL.accepts, fu, fv, Bool.true_and]
    cases τ <;> rcases hua : ans6 u with _ | _ | _ <;>
      simp_all [q6, Regs.sampleOf, Sample.question, subtests, Question.fmtOk]
  · by_cases hp : τ = .point
    · subst hp
      exact cl_accepts_of_side6 S S' check hi (Ne.symm hττ) hs
    · by_cases hp' : τ' = .point
      · subst hp'
        rw [CL.accepts_comm]
        exact cl_accepts_of_side6 S S' check hi hp hs'
      · simp only [CL.accepts, fu, fv, Bool.true_and]
        cases τ <;> cases τ' <;> simp_all [q6, Regs.sampleOf, Sample.question, subtests]

end MIPRE.AnswerReduction

end
