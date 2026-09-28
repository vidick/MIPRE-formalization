/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ClassMIPStar
import MIPRE.Foundations.GameDouble
import MIPRE.Foundations.Halting.Enumerate

/-!
# The class `MIP*_{1,1/2}(2,1)` as the paper defines it

Blueprint `def:mipstar`, the paper's form (`games.tex`, Definition "`def:mipstar`"): a language
`L` is in the class if there are two machines, a sampler `𝒮` and a decider `𝒟`, such that for
every string `z` there is a finite game `G_z` with

* **efficiency**: `𝒮` on input `z` runs in time `poly(|z|)` and returns a question pair
  distributed as `μ_z`; `𝒟` on input `(z, x, y, a, b)` runs in time `poly(|z|)` and returns
  `D_z(x, y, a, b)`, returning `0` whenever `x, y, a, b` are too long (the paper's footnote);
* **completeness**: `z ∈ L → val*(G_z) = 1`;
* **soundness**: `z ∉ L → val*(G_z) ≤ 1/2`.

`MIPRE.MIPStar` (`ClassMIPStar.lean`) is the *computable* version of this, with `G_z` an explicit
`GameData` computed from `z` with no time bound; `planning/polytime-halting.md` has why the two
are different and what it takes to prove `RE ⊆` the class below. This file is the class itself.

## The reading

A `PolyVerifier` is a closed sampler program, a closed decider program and one polynomial `P`;
write `B z = P.eval |z|`.

* A randomized machine is a deterministic program with an explicit uniform seed of the length
  of its time bound: the sampler runs on `encode (z, r)` for a seed `r` of length `B z`. The
  question distribution `μ_z` is the pushforward of the uniform seed.
* The decider's time is polynomial in the **total** input length `|z| + |x| + |y| + |a| + |b|`,
  not in `|z|` alone: a program of the ambient model reads a list only by walking it (blueprint,
  the discussion under `def:decider`), so the paper's "`poly(|z|)` even for long inputs" is not
  expressible here. The paper's own device, the footnote's rejection of overlong messages, is
  a separate clause (`Efficient.rejects_long`), and the game `G_z` lives on the strings of
  length at most `B z`, which makes it the paper's finite game.
* The output of the sampler is read as a pair of strings of length at most `B z`; on an
  efficient verifier it always is one (`Efficient.sampler_runs`), and the fallback `([], [])`
  of `PolyVerifier.questions` is never taken. It is there so that `game` is total.

`MIPStarPoly.toMIPStar` (`ClassMIPStarPolyTab.lean`) is the inclusion in the computable class,
by tabulation, which gives `MIPStarPoly ⊆ RE` from `MIPStar.isRE`.
-/

namespace MIPRE

open MIPRE.Cost Verifier

/-- **A polynomial-time verifier** (`def:mipstar`, the paper's form): a sampler, a decider and
one polynomial time bound. -/
structure PolyVerifier where
  /-- The sampler program; its input is `encode (z, r)` for the input `z` and a seed `r`. -/
  sampler : Prog
  /-- It is closed. -/
  sampler_closed : sampler.WellScoped 1
  /-- The decider program; its input is `encode (z, x, y, a, b)`. -/
  decider : Prog
  /-- It is closed. -/
  decider_closed : decider.WellScoped 1
  /-- The polynomial `P` of the time bounds. -/
  bound : Polynomial ℕ

namespace PolyVerifier

variable (V : PolyVerifier)

/-- The bound `B z = P(|z|)`: the seed length, the sampler's time on `z`, and the length of the
questions and answers of `G_z`. -/
def B (z : BitStr) : ℕ := V.bound.eval z.length

/-- The decider **accepts** `(z, x, y, a, b)`: it halts with output `1`. -/
def Accepts (z x y a b : BitStr) : Prop :=
  ∃ t, V.decider.Runs (encode (z, x, y, a, b)) (encode true) t

open Classical in
/-- The sampler's output on `(z, r)`, if it halts with (the encoding of) a pair of strings. -/
noncomputable def sample? (z r : BitStr) : Option (BitStr × BitStr) :=
  if h : ∃ (p : BitStr × BitStr) (t : ℕ), V.sampler.Runs (encode (z, r)) (encode p) t
  then some h.choose else none

theorem sample?_eq_some_iff (z r : BitStr) (p : BitStr × BitStr) :
    V.sample? z r = some p ↔ ∃ t, V.sampler.Runs (encode (z, r)) (encode p) t := by
  unfold sample?
  split_ifs with h
  · obtain ⟨t, ht⟩ := h.choose_spec
    constructor
    · rintro ⟨rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t', ht'⟩
      obtain ⟨he, -⟩ := ht.deterministic ht'
      have := SizedEncoding.decode_encode (α := BitStr × BitStr) h.choose
      rw [he, SizedEncoding.decode_encode] at this
      rw [Option.some.injEq] at this
      rw [this]
  · simp only [false_iff, not_exists]
    exact fun t ht => h ⟨p, t, ht⟩

/-- The empty answer, in the alphabet of length at most `T`. -/
def emptyAnswer (T : ℕ) : Answers T := ⟨[], by simp⟩

/-- The question pair a seed produces: the sampler's output, when it is a pair of strings of
length at most `B z`, and `([], [])` otherwise. -/
noncomputable def questions (z r : BitStr) : Answers (V.B z) × Answers (V.B z) :=
  match V.sample? z r with
  | some p =>
      if h : p.1.length ≤ V.B z ∧ p.2.length ≤ V.B z then (⟨p.1, h.1⟩, ⟨p.2, h.2⟩)
      else (emptyAnswer _, emptyAnswer _)
  | none => (emptyAnswer _, emptyAnswer _)

/-- **Efficiency** on the input `z` (`def:mipstar`, item 1). -/
structure Efficient (z : BitStr) : Prop where
  /-- The sampler, on every seed of length `B z`, halts within cost `P(|z| + |r|)` with a pair
  of strings of length at most `B z`. The bound is in the total input length, as the decider's:
  a program reads its seed only by walking it, so `B z` itself would leave no time to read a
  seed of length `B z`; with `|r| = B z` polynomial in `|z|` the bound is still `poly(|z|)`. -/
  sampler_runs : ∀ r : BitStr, r.length = V.B z →
    ∃ (x y : BitStr) (t : ℕ), t ≤ V.bound.eval (z.length + r.length) ∧
      x.length ≤ V.B z ∧ y.length ≤ V.B z ∧
      V.sampler.Runs (encode (z, r)) (encode (x, y)) t
  /-- The decider halts within cost `P(|z| + |x| + |y| + |a| + |b|)` on every input. -/
  decider_time : ∀ x y a b : BitStr,
    HaltsWithin V.decider (encode (z, x, y, a, b))
      (V.bound.eval (z.length + x.length + y.length + a.length + b.length))
  /-- The decider rejects whenever one of the four strings is longer than `B z`. -/
  rejects_long : ∀ x y a b : BitStr,
    V.B z < x.length ∨ V.B z < y.length ∨ V.B z < a.length ∨ V.B z < b.length →
      ¬ V.Accepts z x y a b

/-- On an efficient verifier the sampler's output on a seed of the right length is the
question pair, with no fallback. -/
theorem questions_eq_of_efficient {z : BitStr} (h : V.Efficient z) {r : BitStr}
    (hr : r.length = V.B z) :
    ∃ (x y : BitStr) (t : ℕ), t ≤ V.bound.eval (z.length + r.length) ∧
      V.sampler.Runs (encode (z, r)) (encode (x, y)) t ∧
      (V.questions z r).1.1 = x ∧ (V.questions z r).2.1 = y := by
  obtain ⟨x, y, t, ht, hx, hy, hrun⟩ := h.sampler_runs r hr
  refine ⟨x, y, t, ht, hrun, ?_⟩
  have hs : V.sample? z r = some (x, y) := (V.sample?_eq_some_iff z r (x, y)).2 ⟨t, hrun⟩
  simp only [questions, hs, hx, hy, and_self, dite_true]

/-! ## The game `G_z` -/

/-- The number of seeds of length `B z` producing the question pair `(x, y)`. -/
noncomputable def seedCount (z : BitStr) (x y : Answers (V.B z)) : ℕ :=
  ((Data.bitStrsOfLen (V.B z)).filter fun r => decide (V.questions z r = (x, y))).length

/-- Summing a list's fibres over a finite codomain counts the list. -/
theorem sum_length_filter_eq {A : Type*} [Fintype A] [DecidableEq A] (f : BitStr → A × A)
    (l : List BitStr) :
    ∑ x : A, ∑ y : A, (l.filter fun r => decide (f r = (x, y))).length = l.length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    have hstep : ∀ x y : A,
        ((r :: l).filter fun w => decide (f w = (x, y))).length =
          (if f r = (x, y) then 1 else 0) + (l.filter fun w => decide (f w = (x, y))).length := by
      intro x y
      rw [List.filter_cons]
      by_cases h : f r = (x, y)
      · rw [if_pos (by simpa using h), List.length_cons, if_pos h]; omega
      · rw [if_neg (by simpa using h), if_neg h]; omega
    simp only [hstep, Finset.sum_add_distrib, ih, List.length_cons]
    have hone : ∑ x : A, ∑ y : A, (if f r = (x, y) then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single (f r).1]
      · rw [Finset.sum_eq_single (f r).2]
        · simp
        · intro b _ hb
          exact if_neg fun h => hb (by rw [h])
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · intro a _ ha
        exact Finset.sum_eq_zero fun b _ => if_neg fun h => ha (by rw [h])
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    omega

open Classical in
/-- **The game `G_z`** of the verifier on the input `z`: questions and answers are the strings of
length at most `B z`, the question pair is the sampler's output on a uniform seed, and the
decision is the decider's. -/
noncomputable def game (z : BitStr) :
    Game (Answers (V.B z)) (Answers (V.B z)) (Answers (V.B z)) (Answers (V.B z)) where
  μ x y := (V.seedCount z x y : ℝ) / 2 ^ V.B z
  μ_nonneg _ _ := by positivity
  μ_sum_one := by
    simp only [seedCount, ← Finset.sum_div]
    rw [div_eq_one_iff_eq (by positivity)]
    have := sum_length_filter_eq (fun r => V.questions z r) (Data.bitStrsOfLen (V.B z))
    rw [Data.length_bitStrsOfLen] at this
    exact_mod_cast this
  D x y a b := decide (V.Accepts z x.1 y.1 a.1 b.1)

theorem game_μ (z : BitStr) (x y : Answers (V.B z)) :
    (V.game z).μ x y = (V.seedCount z x y : ℝ) / 2 ^ V.B z := rfl

open Classical in
theorem game_D (z : BitStr) (x y a b : Answers (V.B z)) :
    (V.game z).D x y a b = decide (V.Accepts z x.1 y.1 a.1 b.1) := rfl

end PolyVerifier

/-- **`def:mipstar`, the paper's class `MIP*_{1,1/2}(2,1)`.** A language `L` is in it if some
polynomial-time verifier is efficient on every input, and its game has quantum value `1` on
the members of `L` and at most `1/2` off them. -/
def MIPStarPoly (L : Set BitStr) : Prop :=
  ∃ V : PolyVerifier, (∀ z, V.Efficient z) ∧
    ∀ z, (z ∈ L → quantumValue (V.game z) = 1) ∧
      (z ∉ L → quantumValue (V.game z) ≤ 1 / 2)

end MIPRE
