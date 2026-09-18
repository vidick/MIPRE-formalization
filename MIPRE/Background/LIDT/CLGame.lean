/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game
import MIPRE.Foundations.CL.Canonical

/-!
# The seeded CL low individual degree test

Blueprint `def:lidt-cl`, the paper's typed low-degree game `game^ld` (`ldt.tex`,
`sec:ld-game` and `fig:ld-decider`), with parameters `(q, m, d, ldc)`, `q = #F` admissible
and `m ∣ q`. This is the test the paper's padded and simultaneous Pauli uses, and it is *not*
the canonical-line test `MIPRE.LIDT.lidtGame` whose soundness is formalized: the two differ in
which lines they sample and in how they label answers, which is the whole content of
`lem:lidt-reduction-setup`.

## What makes it "seeded"

A question of type `ALine` is a pair `(u₀, s) ∈ F^m × F`, not a line. The seed `s` selects the
direction `e_{χ(s)}`, where `χ(s)` reads off which of the `m` equal blocks of `F` (there are
`q/m` elements each, using `m ∣ q`) the element `s` falls into. So `q/m` seeds describe the
same geometric line, **and they remain different questions**: a strategy is free to answer
differently on two descriptions of one line, which is exactly why the reduction to the
canonical-line test needs a choice or averaging argument.

`DLine` questions are triples `(u₀, s, v')` where `v'` is `v` with its first `χ(s)` coordinates
zeroed. Base points are the canonical representatives `u₀ = L^Ln_w(u)` of
`MIPRE.CL.canonLin` (blueprint `def:cl-canonical`), `w` being the direction.

## The distribution

The verifier samples the ordered type pair uniformly from the nine possibilities and
`(u, s, v)` uniformly from `F^m × F × F^m`, then hands each player the content its type
prescribes. Every sample has the same weight, so normalization is one division rather than the
subtest bookkeeping the canonical-line game needs.

## The decision predicate

`fig:ld-decider` is a format check and then three numbered subtests. The check is the table at
the top of the figure, and the text around it is explicit that it *rejects*: "If the answers
returned by the players do not fit this format the decision procedure rejects." The subtests
are: equal types, accept iff the answers agree; a line type against `Point`, accept iff every
one of the `ldc` polynomials evaluated at the parameter of the point gives the corresponding
coordinate of the point answer; and "in all cases where no action is indicated, accept".

`Question.fmtOk` is the check and `subtests` the rest, with `accepts` their conjunction. The
separation matters because the two clauses that look alike are not: an answer of the wrong
format for its question type is *rejected*, while a well-formatted answer to one of the two
cross type pairs `(ALine, DLine)` and `(DLine, ALine)` is *accepted* --- that is the `2/9` of
the question mass on which this test checks nothing.

Leaving the format check out makes the test vacuous, and an earlier version of this file did
leave it out. The constant strategy answering `values 0` to *every* question, the two line
types included, then passes every subtest through the catch-all, so the game has a value-`1`
strategy whose point measurements are an arbitrary function of the point --- and
`thm:lidt-cl-soundness`, which concludes that those measurements are consistent with
evaluations of a low-individual-degree polynomial measurement, is false for it.
`accepts_aline_values_eq_false` and `accepts_point_apolys_eq_false` pin the two rejections, and
`accepts_aline_dline` pins the acceptance that must survive.

## The one place this file is stricter than the paper

Where the paper writes "`t ∈ F` is such that `x = u₀ + t w`", the point may fail to lie on the
line, and the condition is then vacuous. This file requires membership, as
`MIPRE.LIDT.lidtGame` already does for the canonical-line test: the two agree on the support of
the question distribution, where the point is always on the line, and keeping the convention of
the test whose soundness is proved is what makes the two comparable at all.
-/

noncomputable section

namespace MIPRE.LIDT.CL

open Finset MIPRE.LIDT

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d ldc : ℕ)

/-! ## The seed function -/

variable {F m}

/-- `χ(s)`: which of the `m` blocks of `q/m` field elements the seed `s` falls into, under the
fixed bijection `F ≃ Fin q`. The paper's `eq:chi-func`, `0`-indexed. Needs `m ∣ q`. -/
def chi [NeZero m] (hm : m ∣ Fintype.card F) (s : F) : Fin m :=
  ⟨(Fintype.equivFin F s).val / (Fintype.card F / m), by
    obtain ⟨c, hc⟩ := hm
    have hq : 0 < Fintype.card F := Fintype.card_pos
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · simp [hc] at hq
      · exact h
    have hdiv : Fintype.card F / m = c := by
      rw [hc]; exact Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero (NeZero.ne m))
    rw [hdiv]
    exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; simpa [hc, mul_comm] using
      (Fintype.equivFin F s).isLt)⟩

omit [DecidableEq F] in
/-- The block size `q / m`, positive and with `m * (q/m) = q`. -/
theorem card_div_pos [NeZero m] (hm : m ∣ Fintype.card F) : 0 < Fintype.card F / m := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  exact Nat.div_pos (Nat.le_of_dvd hq hm) (Nat.pos_of_ne_zero (NeZero.ne m))

omit [DecidableEq F] in
theorem chi_val [NeZero m] (hm : m ∣ Fintype.card F) (s : F) :
    (chi hm s : ℕ) = (Fintype.equivFin F s).val / (Fintype.card F / m) := rfl

omit [DecidableEq F] in
/-- **Each seed block has exactly `q / m` elements.** This is what makes the axis-parallel
line distribution the seeded test induces uniform over lines, and it is the input
`lem:lidt-test-transfer` consumes: `q/m` seeds describe each line, so a uniform seed gives a
uniform direction index. It is where `m ∣ q` earns its place among the hypotheses. -/
theorem card_chi_fiber [NeZero m] (hm : m ∣ Fintype.card F) (i : Fin m) :
    #{s : F | chi hm s = i} = Fintype.card F / m := by
  classical
  have hc0 : 0 < Fintype.card F / m := card_div_pos hm
  have hmc : m * (Fintype.card F / m) = Fintype.card F := Nat.mul_div_cancel' hm
  rw [← Fintype.card_subtype]
  refine (Fintype.card_congr ?_).trans (Fintype.card_fin _)
  refine
    { toFun := fun s => ⟨(Fintype.equivFin F s).val % (Fintype.card F / m),
        Nat.mod_lt _ hc0⟩
      invFun := fun r => ⟨(Fintype.equivFin F).symm
        ⟨(i : ℕ) * (Fintype.card F / m) + (r : ℕ), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- the index is below `q`
    have : (i : ℕ) + 1 ≤ m := i.isLt
    calc (i : ℕ) * (Fintype.card F / m) + (r : ℕ)
        < (i : ℕ) * (Fintype.card F / m) + (Fintype.card F / m) := by omega
      _ = ((i : ℕ) + 1) * (Fintype.card F / m) := by ring
      _ ≤ m * (Fintype.card F / m) := Nat.mul_le_mul_right _ this
      _ = Fintype.card F := hmc
  · -- it lands in the `i`-th block
    apply Fin.ext
    rw [chi_val]
    simp only [Equiv.apply_symm_apply]
    rw [mul_comm ((i : ℕ)) (Fintype.card F / m), Nat.mul_add_div hc0,
      Nat.div_eq_of_lt r.isLt, add_zero]
  · -- left inverse
    intro s
    obtain ⟨s, hs⟩ := s
    apply Subtype.ext
    apply (Fintype.equivFin F).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    have hdiv : (Fintype.equivFin F s).val / (Fintype.card F / m) = (i : ℕ) := by
      rw [← chi_val hm s, hs]
    have hdam := Nat.div_add_mod (Fintype.equivFin F s).val (Fintype.card F / m)
    rw [hdiv, mul_comm] at hdam
    exact hdam
  · -- right inverse
    intro r
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    rw [mul_comm ((i : ℕ)) (Fintype.card F / m), Nat.mul_add_mod,
      Nat.mod_eq_of_lt r.isLt]

/-- `π_i(v)`: `v` with its first `i` coordinates zeroed (the paper's `π_{i-1}` at a `0`-indexed
`i`). -/
def zeroBelow (i : Fin m) (v : Point F m) : Point F m :=
  fun k => if (k : ℕ) < (i : ℕ) then 0 else v k

/-- The canonical representative of the line through `u` in direction `w`: the paper's
`L^Ln_w(u)`, the canonical linear map with kernel `span{w}` applied to `u`. -/
def rep (w u : Point F m) : Point F m :=
  MIPRE.CL.canonLin (Submodule.span F {w}) u

/-- The parameter of `x` on the line `u₀ + t · w`: with `j` the first nonzero coordinate of
`w`, the unique `t` with `x j = u₀ j + t · w j`; `0` for a singleton line. Unlike
`MIPRE.LIDT.Line.param` this does not assume the direction normalized, the seeded test's
diagonal directions being arbitrary. -/
def lineParam (u₀ w x : Point F m) : F :=
  if h : ∃ j, w j ≠ 0 then
    (x (Fin.find (fun j => w j ≠ 0) h) - u₀ (Fin.find (fun j => w j ≠ 0) h))
      / w (Fin.find (fun j => w j ≠ 0) h)
  else 0

/-! ## Questions, answers, and samples -/

variable (F m)

/-- The three question types. -/
inductive Ty
  | point
  | aline
  | dline
  deriving DecidableEq

instance : Fintype Ty where
  elems := {Ty.point, Ty.aline, Ty.dline}
  complete t := by cases t <;> simp

/-- Questions: a point, a seeded axis-parallel line, or a seeded diagonal line. -/
inductive Question
  | point (u : Point F m)
  | aline (u₀ : Point F m) (s : F)
  | dline (u₀ : Point F m) (s : F) (v : Point F m)
  deriving DecidableEq, Fintype

/-- Answers: `ldc` field elements, or `ldc` polynomials of degree `≤ d` or `≤ m·d`. -/
inductive Answer
  | values (a : Fin ldc → F)
  | apolys (f : Fin ldc → LinePoly F d)
  | dpolys (f : Fin ldc → LinePoly F (m * d))
  deriving DecidableEq, Fintype

/-- The verifier's random choices: the ordered pair of types, and the ambient
`(u, s, v) ∈ F^m × F × F^m`. -/
structure Sample where
  /-- Alice's type. -/
  tyA : Ty
  /-- Bob's type. -/
  tyB : Ty
  /-- The point. -/
  u : Point F m
  /-- The seed. -/
  s : F
  /-- The raw diagonal direction. -/
  v : Point F m
  deriving DecidableEq, Fintype

variable {F m d ldc}

/-- The question a player of type `t` receives. The paper's typed CL functions `L_Point`,
`L_ALine`, `L_DLine` of `eq:cl-ptf`–`eq:cl-dlnf`, read off the ambient sample. -/
def Sample.question [NeZero m] (hm : m ∣ Fintype.card F) (sm : Sample F m) :
    Ty → Question F m
  | .point => .point sm.u
  | .aline => .aline (rep (Pi.single (chi hm sm.s) 1) sm.u) sm.s
  | .dline =>
      let v' := zeroBelow (chi hm sm.s) sm.v
      .dline (rep v' sm.u) sm.s v'

/-- The direction a line question describes. -/
def Question.dir [NeZero m] (hm : m ∣ Fintype.card F) : Question F m → Point F m
  | .point _ => 0
  | .aline _ s => Pi.single (chi hm s) 1
  | .dline _ _ v => v

/-- The base point a question carries. -/
def Question.base : Question F m → Point F m
  | .point u => u
  | .aline u₀ _ => u₀
  | .dline u₀ _ _ => u₀

omit [DecidableEq F] in
/-- Two seeds in the same block of `q/m` describe the *same* geometric line --- the base point
and the direction agree --- but are *different questions*. This is the "seeded" in the test's
name, and the reason `lem:lidt-reduction-setup` needs a choice or averaging argument to convert
a seeded strategy into one for the canonical-line test: a strategy may answer differently on
two descriptions of one line. -/
theorem aline_question_ne [NeZero m] (hm : m ∣ Fintype.card F) (sm : Sample F m) (s' : F)
    (hs : chi hm s' = chi hm sm.s) (hne : s' ≠ sm.s) :
    ({sm with s := s'} : Sample F m).question hm .aline ≠ sm.question hm .aline := by
  simp [Sample.question, hs, hne]

/-! ## The decision predicate -/

/-- A line answer against a point answer: the point lies on the line, and each of the `ldc`
polynomials evaluated at the parameter of the point gives the corresponding coordinate. -/
def lineVsPoint (u₀ w x : Point F m) {n : ℕ} (f : Fin ldc → LinePoly F n)
    (a : Fin ldc → F) : Bool :=
  decide ((∃ t : F, x = u₀ + t • w) ∧ ∀ j, (f j).eval (lineParam u₀ w x) = a j)

/-- Whether an answer has the format the question's type prescribes, which is the table at the
top of `fig:ld-decider`: a `Point` question is answered by `ldc` field elements, an `ALine`
question by `ldc` polynomials of degree `≤ d`, a `DLine` question by `ldc` polynomials of
degree `≤ m·d`. The decider's first step checks this and **rejects** if it fails ("If the
answers returned by the players do not fit this format the decision procedure rejects"). -/
def Question.fmtOk : Question F m → Answer F m d ldc → Bool
  | .point _, .values _ => true
  | .aline _ _, .apolys _ => true
  | .dline _ _ _, .dpolys _ => true
  | _, _ => false

/-- The three numbered subtests of `fig:ld-decider`, on correctly formatted answers: equal
types accept iff the answers agree, a line type against `Point` accepts iff each polynomial
evaluated at the parameter of the point gives the corresponding coordinate, and "in all cases
where no action is indicated, accept" --- which after the format check of `accepts` means
exactly the two cross type pairs `(ALine, DLine)` and `(DLine, ALine)`. -/
def subtests [NeZero m] (hm : m ∣ Fintype.card F) :
    Question F m → Question F m → Answer F m d ldc → Answer F m d ldc → Bool
  | .point _, .point _, .values a, .values b => decide (a = b)
  | .aline _ _, .aline _ _, .apolys f, .apolys g => decide (f = g)
  | .dline _ _ _, .dline _ _ _, .dpolys f, .dpolys g => decide (f = g)
  | .aline u₀ s, .point x, .apolys f, .values a =>
      lineVsPoint u₀ (Pi.single (chi hm s) 1) x f a
  | .point x, .aline u₀ s, .values a, .apolys f =>
      lineVsPoint u₀ (Pi.single (chi hm s) 1) x f a
  | .dline u₀ _ v, .point x, .dpolys f, .values a => lineVsPoint u₀ v x f a
  | .point x, .dline u₀ _ v, .values a, .dpolys f => lineVsPoint u₀ v x f a
  | _, _, _, _ => true

/-- The decision predicate of `fig:ld-decider`: the format check, then the subtests. -/
def accepts [NeZero m] (hm : m ∣ Fintype.card F)
    (x y : Question F m) (a b : Answer F m d ldc) : Bool :=
  x.fmtOk a && y.fmtOk b && subtests hm x y a b

/-! ### The format check rejects

These are the cases the catch-all of `subtests` would otherwise accept, and they are why the
check cannot be left out: without it the constant strategy answering `values 0` to *every*
question --- including the two line types, for which that is the wrong format --- passes every
subtest, so the test has a value-`1` strategy whose point measurements are an arbitrary
function of the point, and `thm:lidt-cl-soundness` is false for the game. -/

@[simp] theorem accepts_eq_false_left [NeZero m] (hm : m ∣ Fintype.card F)
    {x y : Question F m} {a b : Answer F m d ldc} (h : x.fmtOk a = false) :
    accepts hm x y a b = false := by
  simp [accepts, h]

@[simp] theorem accepts_eq_false_right [NeZero m] (hm : m ∣ Fintype.card F)
    {x y : Question F m} {a b : Answer F m d ldc} (h : y.fmtOk b = false) :
    accepts hm x y a b = false := by
  simp [accepts, h]

/-- A line question answered in the point format is rejected --- the case that made the test
vacuous before the format check was added. -/
theorem accepts_aline_values_eq_false [NeZero m] (hm : m ∣ Fintype.card F)
    (u₀ : Point F m) (s : F) (y : Question F m) (a : Fin ldc → F) (b : Answer F m d ldc) :
    accepts hm (.aline u₀ s) y (.values a) b = false :=
  accepts_eq_false_left hm rfl

/-- A point question answered in a line format is rejected. -/
theorem accepts_point_apolys_eq_false [NeZero m] (hm : m ∣ Fintype.card F)
    (u : Point F m) (y : Question F m) (f : Fin ldc → LinePoly F d)
    (b : Answer F m d ldc) :
    accepts hm (.point u) y (.apolys f) b = false :=
  accepts_eq_false_left hm rfl

/-- The two cross type pairs are still accepted on well-formatted answers, as
`fig:ld-decider`'s "in all cases where no action is indicated, accept" prescribes. This is the
`2/9` of the question mass on which the test checks nothing. -/
theorem accepts_aline_dline [NeZero m] (hm : m ∣ Fintype.card F)
    (u₀ : Point F m) (s : F) (u₀' : Point F m) (s' : F) (v : Point F m)
    (f : Fin ldc → LinePoly F d) (g : Fin ldc → LinePoly F (m * d)) :
    accepts hm (.aline u₀ s) (.dline u₀' s' v) (.apolys f) (.dpolys g) = true := rfl

/-! ## The game -/

/-- The **seeded CL low individual degree test** as a game (blueprint `def:lidt-cl`). -/
def clGame [NeZero m] (hm : m ∣ Fintype.card F) :
    Game (Question F m) (Question F m) (Answer F m d ldc) (Answer F m d ldc) where
  μ x y := ∑ sm : Sample F m,
    (Fintype.card (Sample F m) : ℝ)⁻¹ *
      if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0
  μ_nonneg _ _ := Finset.sum_nonneg fun _ _ =>
    mul_nonneg (by positivity) (by split_ifs <;> norm_num)
  μ_sum_one := by
    rw [← Fintype.sum_prod_type', Finset.sum_comm]
    simp only [← Finset.mul_sum, Prod.mk.eta, Fintype.sum_ite_eq, mul_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by
      simpa using (Fintype.card_pos_iff.mpr ⟨⟨.point, .point, 0, 0, 0⟩⟩ :
        0 < Fintype.card (Sample F m)).ne')
  D := accepts hm

end MIPRE.LIDT.CL

end
