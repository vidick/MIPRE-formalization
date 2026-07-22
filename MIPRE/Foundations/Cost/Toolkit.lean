/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.PolyTime

/-!
# The efficient computability toolkit

The efficient versions of the universal machine, the s-m-n theorem, and Kleene's
recursion theorem, in the ambient cost model — blueprint Section
`sec:rr-computability` (`lem:universal-tm`, `lem:smn`, `lem:kleene`), following
[MNY, Lemmas 2.1–2.3]. Mathlib has the computability halves
(`Nat.Partrec.Code.smn`, `eval_part`, `fixed_point`); everything with a time bound
is new.

Contents:

* `Code.size`, `Code.encodeList`: program size, and the length-faithful
  serialization of programs as machine words (7 tags, preorder; length = size).
  This — not any numeric Gödel numbering — is how programs occur as *data*.
* `pushList`/`hardcode`: the **efficient s-m-n**. `hardcode c l` prepends the
  literal `l` to the input and runs `c`. The witness makes [MNY, Lemma 2.2]
  quantitative and stronger than stated there: program-size and time overheads are
  *linear* in `vsize l` (paper: polynomial), with a universal constant.
* `exists_efficient_universal` (`lem:universal-tm`): a fixed program `univ` with
  `univ.eval (⌜c⌝ ++ SEP :: v) = c.eval v` and polynomial time overhead.
* `exists_clocked_universal`: the time-bounded variant ("run `c` on `v` for `k`
  steps"), used by the recursive compression argument and by the pipeline's
  deciders (introspection and repetition simulate other deciders under a budget).
* `efficient_fixed_point` (`lem:kleene`): Kleene's recursion theorem with
  polynomially-equivalent runtimes, for a polynomial-time map on programs.

Effort notes (matching the blueprint's `\effortHard` on this section): the s-m-n
lemmas are elementary once `TimedEval` has its API. The two universal-machine
theorems are the hard core — an in-model self-interpreter with polynomial (in
fact, the aim should be linear-times-polylog) overhead; this is the same kind of
artifact as the interpreter underlying the succinct Cook–Levin gateway
(`thm:succinct-sat`), and the two developments should share design.
-/

/-! ## Programs as data -/

namespace Turing.ToPartrec.Code

/-- Structural size of a program (constructor count). -/
def size : Code → ℕ
  | .zero' => 1
  | .succ => 1
  | .tail => 1
  | .cons f g => f.size + g.size + 1
  | .comp f g => f.size + g.size + 1
  | .case f g => f.size + g.size + 1
  | .fix f => f.size + 1

/-- Length-faithful serialization of programs: preorder traversal, one tag cell
per constructor (arities are determined by tags, so this is a prefix code).
`(encodeList c).length = c.size`, in contrast with numeric Gödel numberings
(`Nat.Partrec.Code.encodeCode`), whose bit-length is exponential in nesting
depth. -/
def encodeList : Code → List ℕ
  | .zero' => [0]
  | .succ => [1]
  | .tail => [2]
  | .cons f g => 3 :: (f.encodeList ++ g.encodeList)
  | .comp f g => 4 :: (f.encodeList ++ g.encodeList)
  | .case f g => 5 :: (f.encodeList ++ g.encodeList)
  | .fix f => 6 :: f.encodeList

theorem encodeList_length (c : Code) : c.encodeList.length = c.size := by
  sorry -- routine induction

/-- Tag-based deserialization. -/
def decodeList (l : List ℕ) : Option Code := by
  sorry -- structural; routine

end Turing.ToPartrec.Code

namespace MIPRE.Cost

open Turing.ToPartrec Polynomial

instance : SizedEncoding Code where
  encode := Code.encodeList
  decode := Code.decodeList
  decode_encode c := by sorry -- prefix-code round trip; routine
  bound := 6
  cells_le_bound c := by sorry -- routine induction

@[simp] theorem esize_code (c : Code) : esize c = c.size := by
  show c.encodeList.length = c.size
  exact c.encodeList_length

/-! ## Efficient s-m-n (blueprint `lem:smn`; [MNY, Lemma 2.2])

The s-m-n program transformation is `hardcode c l := c.comp (pushList l)`: prepend
the literal word `l`, then run `c`. On the pairing convention of
`Cost.Encoding` (`encode (a, x) = encode a ++ sep :: encode x`), hardcoding the
first component of a pair is `hardcode c (encode a ++ [sep])`. -/

/-- `constNum n` outputs `[n]` on any input; size `Θ(n)` — used only for *cells*,
which the encodings keep bounded, so this never costs more than a constant. -/
def constNum : ℕ → Code
  | 0 => Code.zero
  | n + 1 => Code.succ.comp (constNum n)

@[simp] theorem constNum_eval (n : ℕ) (v : List ℕ) :
    (constNum n).eval v = pure [n] := by
  induction n with
  | zero => simp [constNum]
  | succ n ih => simp [constNum, ih]

/-- `push n` prepends the cell `n` to the input: `push n v = n :: v`. -/
def push (n : ℕ) : Code := Code.cons (constNum n) Code.id

@[simp] theorem push_eval (n : ℕ) (v : List ℕ) : (push n).eval v = pure (n :: v) := by
  simp [push]

/-- `pushList l` prepends the literal word `l`: `pushList l v = l ++ v`. -/
def pushList : List ℕ → Code
  | [] => Code.id
  | n :: l => (push n).comp (pushList l)

@[simp] theorem pushList_eval (l v : List ℕ) : (pushList l).eval v = pure (l ++ v) := by
  induction l with
  | nil => simp [pushList]
  | cons n l ih => simp [pushList, ih]

/-- The s-m-n transformation: `hardcode c l` runs `c` on `l ++ ·`. -/
def hardcode (c : Code) (l : List ℕ) : Code := c.comp (pushList l)

/-- Efficient s-m-n, functional equation ([MNY, Lemma 2.2], first clause). -/
@[simp] theorem hardcode_eval (c : Code) (l v : List ℕ) :
    (hardcode c l).eval v = c.eval (l ++ v) := by
  simp [hardcode]

/-- Efficient s-m-n, size bound: hardcoding costs *linear* program size.
(The constant is generous and provisional.) -/
theorem hardcode_size (c : Code) (l : List ℕ) :
    (hardcode c l).size ≤ c.size + 12 * (vsize l + 1) := by
  sorry -- routine induction on `l`

/-- Efficient s-m-n, forward time transfer: a run of `c` on `l ++ v` yields a run
of `hardcode c l` on `v` with *additive, linear* overhead. -/
theorem hardcode_time (c : Code) (l v w : List ℕ) (t : ℕ)
    (h : TimedEval c (l ++ v) w t) :
    ∃ t' ≤ t + 12 * (vsize l + 1), TimedEval (hardcode c l) v w t' := by
  sorry -- run `pushList l` (linear), then `h`

/-- Efficient s-m-n, backward time transfer: runs of `hardcode c l` restrict to
runs of `c`. -/
theorem hardcode_time_rev (c : Code) (l v w : List ℕ) (t : ℕ)
    (h : TimedEval (hardcode c l) v w t) :
    ∃ t' ≤ t, TimedEval c (l ++ v) w t' := by
  sorry -- invert the `comp` rule

/-- The s-m-n map itself is polynomial-time computable *in the model* — the clause
of [MNY, Lemma 2.2] that the recursive compression argument uses at runtime (the
self-referential decider builds hardcoded programs while executing). Requires the
closure library. -/
theorem smn_polyTime :
    ∃ S : PolyTimeFun (Code × BitStr) Code,
      ∀ c : Code, ∀ x : BitStr, S (c, x) = hardcode c (encode x) := by
  sorry

/-! ## The efficient universal machine (blueprint `lem:universal-tm`; [MNY, Lemma 2.1]) -/

/-- Separator cell for `⌜program⌝ ++ SEP :: input` layouts (program tags are `≤ 6`). -/
def SEP : ℕ := 7

/-- **Efficient universal machine.** A fixed program `univ` simulating any `c` on
any `v` — with the same divergence behavior — at polynomial time overhead.

This is the hard artifact of the toolkit (compare the self-interpreters of the
Coq call-by-value λ-calculus line of work). The overhead polynomial is
existential here; the eventual development should expose it as data, like
`PolyTimeFun.timeBound`. -/
theorem exists_efficient_universal :
    ∃ (univ : Code) (p : Polynomial ℕ),
      ∀ (c : Code) (v : List ℕ),
        univ.eval (encode c ++ SEP :: v) = c.eval v ∧
        ∀ w t, TimedEval c v w t →
          ∃ t' ≤ p.eval (c.size + vsize v + t),
            TimedEval univ (encode c ++ SEP :: v) w t' := by
  sorry

open Classical in
/-- The result of running `c` on `v` for at most `k` cost, if it halts within the
budget (well-defined by `TimedEval.deterministic`). -/
noncomputable def evalWithin (c : Code) (v : List ℕ) (k : ℕ) : Option (List ℕ) :=
  if h : ∃ w t, t ≤ k ∧ TimedEval c v w t then some h.choose else none

/-- **Clocked universal machine**: total simulation under a step budget `k`
(supplied as a single unary-priced cell), returning `1 :: w` on in-budget halting
and `[0]` on budget exhaustion, in time polynomial in the budget. This is the
primitive with which deciders of the pipeline run other deciders, and with which
the recursive compression argument runs "`e` for `log n` steps". -/
theorem exists_clocked_universal :
    ∃ (univT : Code) (p : Polynomial ℕ),
      ∀ (c : Code) (v : List ℕ) (k : ℕ),
        ∃ t ≤ p.eval (k + c.size + vsize v),
          TimedEval univT (k :: (encode c ++ SEP :: v))
            (match evalWithin c v k with
              | some w => 1 :: w
              | none => [0]) t := by
  sorry

/-! ## Efficient Kleene recursion (blueprint `lem:kleene`; [MNY, Lemma 2.3]) -/

/-- **Efficient Kleene fixed point**: for a polynomial-time map on programs, a
program `e` with `e.eval = (F e).eval` and polynomially-equivalent runtimes. The
proof is the classical construction through `hardcode` and `univ`, tracking the
overheads; the polynomial `p` depends on `F.timeBound` and should eventually be
exposed as data (the λ-boundedness bookkeeping of [JNVWY, §12.2] chooses λ above
it). -/
theorem efficient_fixed_point (F : PolyTimeFun Code Code) :
    ∃ (e : Code) (p : Polynomial ℕ),
      e.eval = (F e).eval ∧
      (∀ v w t, TimedEval (F e) v w t →
        ∃ t' ≤ p.eval (vsize v + t), TimedEval e v w t') ∧
      (∀ v w t, TimedEval e v w t →
        ∃ t' ≤ p.eval (vsize v + t), TimedEval (F e) v w t') := by
  sorry

end MIPRE.Cost
