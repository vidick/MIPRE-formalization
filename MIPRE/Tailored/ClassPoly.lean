/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ClassMIPStar
public import MIPRE.Tailored.Verifier

@[expose] public section

/-!
# The class `TMIP*` as the paper defines it: polynomial-time tailored verifiers

Paper II, II:787 and II:1505 (clause (1) of `thm:tailored_MIP*=RE`): a language is in `TMIP*` when
a polynomial-time procedure presents, on every input `z`, a tailored game `G_z`, sampling a
question pair and evaluating the canonical decider in time `poly(|z|)`, with a perfect ZPC strategy
on the members and value at most `1/2` off them. `MIPRE.Tailored.TMIPStarComputable`
(`Tailored/Class.lean`) is the computable version, with `G_z` an explicit description computed
with no time bound; this file is the class itself, as `Foundations/ClassMIPStar.lean` is for
`MIP*`.

## The reading

A `TPolyVerifier` is three closed programs and one polynomial `P`; write `B z = P(|z|)`.

* **The sampler** is `MIP*`'s (`PolyVerifier`, through `toPoly`): on `(z, r)`, for a uniform seed
  `r` of length `B z`, a question pair of strings of length at most `B z`. The question
  distribution of `G_z` is the pushforward of the seed (`PolyVerifier.game`).
* **The answer-length calculator**, on `(z, x, κ)`, outputs the number of readable (`κ = false`)
  or linear variables at the question `x`, read in unary, as `MIPRE.Tailored.LenIs` reads the
  calculator of a tailored normal form verifier.
* **The linear-constraints processor**, on `(z, x, y, a^R, b^R)`, outputs the constraints
  `L_xy(a^R b^R)`, read by `Data.bitsListD`, as `MIPRE.Tailored.LpIs` does.

`tgame z` is the tailored game on the strings of length at most `B z`, with the constraint list
that rejects everything where a program does not halt (`consOf`), as `TailoredVerifier.tgame`.
**Efficiency** (`Efficient`) bounds the three programs by `P` of the total input length, as
`PolyVerifier.Efficient` bounds the sampler and the decider; the canonical decider itself is
then a polynomial-time check on what they output (`Tailored/Canonical.lean`), whose cost the plan
deferred because no statement needs it.

`TMIPStar L`: some polynomial-time tailored verifier is efficient on every input, its doubled game
has a perfect ZPC strategy on the members of `L`, and its game has value at most `1/2` off them.
The completeness clause is read on the doubled game, as `TailoredVerifier.HasPerfectZPC` reads
the paper's for tailored normal form verifiers and `TailoredGapCompression.completeness`
transports it.
-/

namespace MIPRE.Tailored

open Cost Verifier

/-- **A polynomial-time tailored verifier** (II:1505): a sampler, an answer-length calculator, a
linear-constraints processor and one polynomial time bound. -/
structure TPolyVerifier where
  /-- The sampler program; its input is `encode (z, r)` for the input `z` and a seed `r`. -/
  sampler : Prog
  sampler_closed : sampler.WellScoped 1
  /-- The answer-length calculator; its input is `encode (z, x, κ)`. -/
  len : Prog
  len_closed : len.WellScoped 1
  /-- The linear-constraints processor; its input is `encode (z, x, y, a^R, b^R)`. -/
  lp : Prog
  lp_closed : lp.WellScoped 1
  /-- The polynomial `P` of the time bounds. -/
  bound : Polynomial ℕ

namespace TPolyVerifier

variable (V : TPolyVerifier)

/-- The sampler and the bound, as a `PolyVerifier` whose decider is never used: its seeds, its
question pairs and its question distribution are the tailored verifier's. -/
def toPoly : PolyVerifier where
  sampler := V.sampler
  sampler_closed := V.sampler_closed
  decider := V.sampler
  decider_closed := V.sampler_closed
  bound := V.bound

/-- The bound `B z = P(|z|)`: the seed length, and the length of the questions. -/
abbrev B (z : BitStr) : ℕ := V.toPoly.B z

/-- The answer-length calculator outputs `k` on `(z, x, κ)`, read in unary. -/
def LenIs (z x : BitStr) (κ : Bool) (k : ℕ) : Prop :=
  ∃ t d, V.len.Runs (encode (z, x, κ)) d t ∧ (Data.spineList d).length = k

/-- The linear-constraints processor outputs `cs` on `(z, x, y, a^R, b^R)`. -/
def LpIs (z x y aR bR : BitStr) (cs : List BitStr) : Prop :=
  ∃ t d, V.lp.Runs (encode (z, x, y, aR, bR)) d t ∧ Data.bitsListD d = cs

open Classical in
/-- The length the calculator outputs on `(z, x, κ)`, and `0` when it does not halt. -/
noncomputable def lenOf (z x : BitStr) (κ : Bool) : ℕ :=
  if h : ∃ k, V.LenIs z x κ k then h.choose else 0

/-- The calculator halts at the question `x`, for both kinds of variables. -/
def LenDefined (z x : BitStr) : Prop := ∀ κ, ∃ k, V.LenIs z x κ k

open Classical in
/-- The constraints at `(x, y)`: what the processor outputs when the calculator halts at both
questions and the processor halts; otherwise the list that rejects everything. -/
noncomputable def consOf (z x y aR bR : BitStr) : List BitStr :=
  if h : V.LenDefined z x ∧ V.LenDefined z y ∧ ∃ cs, V.LpIs z x y aR bR cs then
    h.2.2.choose
  else
    [rejectConstraint (V.lenOf z x false + V.lenOf z x true + V.lenOf z y false +
      V.lenOf z y true)]

/-- **The game `G_z`**: questions the strings of length at most `B z`, distributed as the
sampler's output on a uniform seed, lengths and constraints as the calculator and the processor
compute them. -/
noncomputable def tgame (z : BitStr) : TailoredGame (Answers (V.B z)) where
  μ := (V.toPoly.game z).μ
  μ_nonneg := (V.toPoly.game z).μ_nonneg
  μ_sum_one := (V.toPoly.game z).μ_sum_one
  lenR x := V.lenOf z x.1 false
  lenL x := V.lenOf z x.1 true
  cons x y := V.consOf z x.1 y.1

/-- **Efficiency** on the input `z` (II:1505, clause (1)): the sampler's clause of
`PolyVerifier.Efficient`, and the calculator and the processor halting within `P` of the total
input length on every input. -/
structure Efficient (z : BitStr) : Prop where
  sampler_runs : V.toPoly.SamplerRuns z
  len_time : ∀ (x : BitStr) (κ : Bool),
    HaltsWithin V.len (encode (z, x, κ)) (V.bound.eval (z.length + x.length))
  lp_time : ∀ x y aR bR : BitStr,
    HaltsWithin V.lp (encode (z, x, y, aR, bR))
      (V.bound.eval (z.length + x.length + y.length + aR.length + bR.length))

/-! ## The outputs are determined -/

theorem LenIs.unique {z x : BitStr} {κ : Bool} {k k' : ℕ} (h : V.LenIs z x κ k)
    (h' : V.LenIs z x κ k') : k = k' := by
  obtain ⟨t, d, hd, rfl⟩ := h
  obtain ⟨t', d', hd', rfl⟩ := h'
  obtain ⟨rfl, -⟩ := Eval.deterministic hd hd'
  rfl

theorem LpIs.unique {z x y aR bR : BitStr} {cs cs' : List BitStr} (h : V.LpIs z x y aR bR cs)
    (h' : V.LpIs z x y aR bR cs') : cs = cs' := by
  obtain ⟨t, d, hd, rfl⟩ := h
  obtain ⟨t', d', hd', rfl⟩ := h'
  obtain ⟨rfl, -⟩ := Eval.deterministic hd hd'
  rfl

theorem lenOf_eq {z x : BitStr} {κ : Bool} {k : ℕ} (h : V.LenIs z x κ k) : V.lenOf z x κ = k := by
  have hex : ∃ m, V.LenIs z x κ m := ⟨k, h⟩
  unfold lenOf
  rw [dite_eq_left hex]
  exact LenIs.unique V hex.choose_spec h

theorem consOf_eq {z x y aR bR : BitStr} (hx : V.LenDefined z x) (hy : V.LenDefined z y)
    {cs : List BitStr} (h : V.LpIs z x y aR bR cs) : V.consOf z x y aR bR = cs := by
  have hex : V.LenDefined z x ∧ V.LenDefined z y ∧ ∃ cs, V.LpIs z x y aR bR cs :=
    ⟨hx, hy, cs, h⟩
  unfold consOf
  rw [dite_eq_left hex]
  exact LpIs.unique V hex.2.2.choose_spec h

end TPolyVerifier

/-- **`TMIP*`, the paper's class** (II:787). A language `L` is in it if some polynomial-time
tailored verifier is efficient on every input, its doubled game has a perfect ZPC strategy on the
members of `L`, and its game has value at most `1/2` off them. -/
def TMIPStar (L : Set BitStr) : Prop :=
  ∃ V : TPolyVerifier, (∀ z, V.Efficient z) ∧
    ∀ z, (z ∈ L → (V.tgame z).doubled.HasPerfectZPC) ∧ (z ∉ L → (V.tgame z).valStar ≤ 1 / 2)

end MIPRE.Tailored

end
