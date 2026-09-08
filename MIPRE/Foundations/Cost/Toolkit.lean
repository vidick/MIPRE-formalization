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
  `smn_polyTime` is the runtime version — the map is itself polynomial-time
  computable in the model — generic in the type of the hardcoded value.
* `UniversalMachine` / `exists_efficient_universal` (`lem:universal-tm`): a fixed
  program `univ` with `univ.eval (⌜c⌝ ++ SEP :: v) = c.eval v` and polynomial time
  overhead, packaged as data (the program and its overhead polynomial) whose
  existence is the sorried node.
* `ClockedUniversalMachine` / `exists_clocked_universal`: the time-bounded variant
  ("run `c` on `v` for `k` steps"), used by the recursive compression argument and
  by the pipeline's deciders (introspection and repetition simulate other deciders
  under a budget).
* `efficient_fixed_point` (`lem:kleene`): Kleene's recursion theorem for a
  polynomial-time map on programs, with the runs of the fixed point bounded by
  those of its image at polynomial overhead.

The statement shapes were audited against the proof of the recursive compression
lemma (`planning/compression-track.md`, K0): the universal machines are structures so
that downstream definitions can name the program and its polynomial without any
sorried `def`; the runtime s-m-n is generic in the hardcoded type; Kleene is stated
in the one direction the argument uses (see its docstring).

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
  induction c with
  | zero' => rfl
  | succ => rfl
  | tail => rfl
  | cons f g ihf ihg => simp only [encodeList, size, List.length_cons, List.length_append, ihf, ihg]
  | comp f g ihf ihg => simp only [encodeList, size, List.length_cons, List.length_append, ihf, ihg]
  | case f g ihf ihg => simp only [encodeList, size, List.length_cons, List.length_append, ihf, ihg]
  | fix f ih => simp only [encodeList, size, List.length_cons, ih]

/-- Every cell of a serialized program is a tag `≤ 6`. -/
theorem encodeList_cells_le (c : Code) : ∀ x ∈ c.encodeList, x ≤ 6 := by
  induction c with
  | zero' => simp [encodeList]
  | succ => simp [encodeList]
  | tail => simp [encodeList]
  | cons f g ihf ihg =>
    simp only [encodeList, List.forall_mem_cons, List.forall_mem_append]
    exact ⟨by omega, ihf, ihg⟩
  | comp f g ihf ihg =>
    simp only [encodeList, List.forall_mem_cons, List.forall_mem_append]
    exact ⟨by omega, ihf, ihg⟩
  | case f g ihf ihg =>
    simp only [encodeList, List.forall_mem_cons, List.forall_mem_append]
    exact ⟨by omega, ihf, ihg⟩
  | fix f ih =>
    simp only [encodeList, List.forall_mem_cons]
    exact ⟨by omega, ih⟩

/-- Tag-directed parser with fuel: `parseCode fuel l = some (c, rest)` when `l` starts
with the serialization of a program `c` of size at most `fuel`, followed by `rest`
(`parseCode_encodeList`). The fuel bounds the recursion structurally, so the parser is
kernel-evaluable. -/
def parseCode : ℕ → List ℕ → Option (Code × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, 0 :: l => some (.zero', l)
  | _ + 1, 1 :: l => some (.succ, l)
  | _ + 1, 2 :: l => some (.tail, l)
  | fuel + 1, 3 :: l =>
    match parseCode fuel l with
    | some (f, l) =>
      match parseCode fuel l with
      | some (g, l) => some (.cons f g, l)
      | none => none
    | none => none
  | fuel + 1, 4 :: l =>
    match parseCode fuel l with
    | some (f, l) =>
      match parseCode fuel l with
      | some (g, l) => some (.comp f g, l)
      | none => none
    | none => none
  | fuel + 1, 5 :: l =>
    match parseCode fuel l with
    | some (f, l) =>
      match parseCode fuel l with
      | some (g, l) => some (.case f g, l)
      | none => none
    | none => none
  | fuel + 1, 6 :: l =>
    match parseCode fuel l with
    | some (f, l) => some (.fix f, l)
    | none => none
  | _ + 1, _ :: _ => none

/-- Tag-based deserialization: inverts `encodeList` (`decodeList_encodeList`); `none` on
malformed or non-exhausted input. -/
def decodeList (l : List ℕ) : Option Code :=
  match parseCode l.length l with
  | some (c, []) => some c
  | _ => none

/-- The parser reads back a serialized program, given enough fuel. -/
theorem parseCode_encodeList (c : Code) :
    ∀ (fuel : ℕ) (rest : List ℕ), c.size ≤ fuel →
      parseCode fuel (c.encodeList ++ rest) = some (c, rest) := by
  induction c with
  | zero' =>
    intro fuel rest h
    cases fuel with
    | zero => simp [size] at h
    | succ fuel => simp [encodeList, parseCode]
  | succ =>
    intro fuel rest h
    cases fuel with
    | zero => simp [size] at h
    | succ fuel => simp [encodeList, parseCode]
  | tail =>
    intro fuel rest h
    cases fuel with
    | zero => simp [size] at h
    | succ fuel => simp [encodeList, parseCode]
  | cons f g ihf ihg =>
    intro fuel rest h
    cases fuel with
    | zero => simp [size] at h
    | succ fuel =>
      simp only [size] at h
      simp only [encodeList, List.cons_append, List.append_assoc, parseCode,
        ihf fuel (g.encodeList ++ rest) (by omega), ihg fuel rest (by omega)]
  | comp f g ihf ihg =>
    intro fuel rest h
    cases fuel with
    | zero => simp [size] at h
    | succ fuel =>
      simp only [size] at h
      simp only [encodeList, List.cons_append, List.append_assoc, parseCode,
        ihf fuel (g.encodeList ++ rest) (by omega), ihg fuel rest (by omega)]
  | case f g ihf ihg =>
    intro fuel rest h
    cases fuel with
    | zero => simp [size] at h
    | succ fuel =>
      simp only [size] at h
      simp only [encodeList, List.cons_append, List.append_assoc, parseCode,
        ihf fuel (g.encodeList ++ rest) (by omega), ihg fuel rest (by omega)]
  | fix f ih =>
    intro fuel rest h
    cases fuel with
    | zero => simp [size] at h
    | succ fuel =>
      simp only [size] at h
      simp only [encodeList, List.cons_append, parseCode, ih fuel rest (by omega)]

/-- `decodeList` inverts `encodeList`. -/
theorem decodeList_encodeList (c : Code) : decodeList c.encodeList = some c := by
  have h := parseCode_encodeList c c.size [] le_rfl
  rw [List.append_nil] at h
  simp only [decodeList, encodeList_length, h]

end Turing.ToPartrec.Code

namespace MIPRE.Cost

open Turing.ToPartrec Polynomial

instance : SizedEncoding Code where
  encode := Code.encodeList
  decode := Code.decodeList
  decode_encode := Code.decodeList_encodeList
  bound := 6
  cells_le_bound := Code.encodeList_cells_le

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

theorem constNum_size (n : ℕ) : (constNum n).size = 2 * n + 5 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [constNum, Code.size, ih]; omega

theorem push_size (n : ℕ) : (push n).size = 2 * n + 9 := by
  simp only [push, Code.size, constNum_size, Code.id]

theorem pushList_size (l : List ℕ) : (pushList l).size ≤ 10 * vsize l + 3 := by
  induction l with
  | nil => simp [pushList, Code.id, Code.size]
  | cons n l ih => simp only [pushList, Code.size, push_size, vsize_cons]; omega

/-- Efficient s-m-n, size bound: hardcoding costs *linear* program size.
(The constant is generous and provisional.) -/
theorem hardcode_size (c : Code) (l : List ℕ) :
    (hardcode c l).size ≤ c.size + 12 * (vsize l + 1) := by
  have := pushList_size l
  simp only [hardcode, Code.size]
  omega

/-- The run of `constNum n`: `2n + 5` steps. -/
theorem constNum_timedEval (n : ℕ) (v : List ℕ) :
    TimedEval (constNum n) v [n] (2 * n + 5) := by
  induction n with
  | zero => exact TimedEval.code_zero v
  | succ n ih => exact (TimedEval.comp ih (.succ [n])).cast_cost (by omega)

/-- The run of `push n`: `2n + 9` steps. -/
theorem push_timedEval (n : ℕ) (v : List ℕ) : TimedEval (push n) v (n :: v) (2 * n + 9) :=
  (TimedEval.cons (constNum_timedEval n v) (TimedEval.code_id v)).cast_cost (by omega)

/-- The run of `pushList l`: linear in `vsize l`. -/
theorem pushList_timedEval (l v : List ℕ) :
    ∃ t ≤ 10 * vsize l + 3, TimedEval (pushList l) v (l ++ v) t := by
  induction l generalizing v with
  | nil => exact ⟨3, by simp, TimedEval.code_id v⟩
  | cons n l ih =>
    obtain ⟨t, ht, h⟩ := ih v
    refine ⟨t + (2 * n + 9) + 1, ?_, TimedEval.comp h (push_timedEval n (l ++ v))⟩
    simp only [vsize_cons]
    omega

/-- Efficient s-m-n, forward time transfer: a run of `c` on `l ++ v` yields a run
of `hardcode c l` on `v` with *additive, linear* overhead. -/
theorem hardcode_time (c : Code) (l v w : List ℕ) (t : ℕ)
    (h : TimedEval c (l ++ v) w t) :
    ∃ t' ≤ t + 12 * (vsize l + 1), TimedEval (hardcode c l) v w t' := by
  obtain ⟨s, hs, hp⟩ := pushList_timedEval l v
  exact ⟨s + t + 1, by omega, TimedEval.comp hp h⟩

/-- Efficient s-m-n, backward time transfer: runs of `hardcode c l` restrict to
runs of `c`. -/
theorem hardcode_time_rev (c : Code) (l v w : List ℕ) (t : ℕ)
    (h : TimedEval (hardcode c l) v w t) :
    ∃ t' ≤ t, TimedEval c (l ++ v) w t' := by
  change TimedEval (c.comp (pushList l)) v w t at h
  cases h with
  | comp hp hc =>
    obtain ⟨s, -, hp'⟩ := pushList_timedEval l v
    obtain ⟨rfl, -⟩ := hp.deterministic hp'
    exact ⟨_, by omega, hc⟩

/-- Hardcoding the first component of a pair: with the separator of the pairing
convention, `hardcode c (encode a ++ [pairSep α β])` run on `encode b` is `c` run on
`encode (a, b)`. -/
theorem hardcode_pair_eval {α β : Type*} [SizedEncoding α] [SizedEncoding β]
    (c : Code) (a : α) (b : β) :
    (hardcode c (encode a ++ [pairSep α β])).eval (encode b) = c.eval (encode (a, b)) := by
  rw [hardcode_eval, encode_prod, List.append_assoc, List.singleton_append]

/-- The s-m-n map itself is polynomial-time computable *in the model* — the clause
of [MNY, Lemma 2.2] that the recursive compression argument uses at runtime (the
self-referential decider builds hardcoded programs while executing). The argument
hardcodes encoded programs and tuples, not only bit strings, hence the statement is
generic in the hardcoded type `α`; the trailing separator `sep` lets the hardcoded
value be the first component of a pair (`sep = pairSep α β`, `hardcode_pair_eval`).
Requires the closure library. -/
theorem smn_polyTime (α : Type*) [SizedEncoding α] (sep : ℕ) :
    ∃ S : PolyTimeFun (Code × α) Code,
      ∀ (c : Code) (a : α), S (c, a) = hardcode c (encode a ++ [sep]) := by
  sorry

/-! ## The efficient universal machine (blueprint `lem:universal-tm`; [MNY, Lemma 2.1])

The two universal machines are *structures*: the program and its overhead polynomial
are fields, so that downstream definitions (deciders simulating other deciders under a
budget; the λ-bookkeeping of [JNVWY, §12.2], which chooses λ above the concrete
overhead polynomials) can refer to them as data. Their existence is the sorried node;
no `def` is sorried. This is the hard artifact of the toolkit (compare the
self-interpreters of the Coq call-by-value λ-calculus line of work). -/

/-- Separator cell for `⌜program⌝ ++ SEP :: input` layouts (program tags are `≤ 6`). -/
def SEP : ℕ := 7

/-- **Efficient universal machine.** A fixed program `univ` simulating any `c` on
any `v` — with the same divergence behavior — at polynomial time overhead in
`c.size + vsize v + runtime`. -/
structure UniversalMachine where
  /-- The universal program; it takes `encode c ++ SEP :: v`. -/
  univ : Code
  /-- The overhead polynomial. -/
  bound : Polynomial ℕ
  /-- Same input/output behavior — including divergence — as the simulated program. -/
  eval_eq : ∀ (c : Code) (v : List ℕ), univ.eval (encode c ++ SEP :: v) = c.eval v
  /-- A run of `c` yields a run of the simulation at polynomial overhead. -/
  time_le : ∀ (c : Code) (v w : List ℕ) (t : ℕ), TimedEval c v w t →
    ∃ t' ≤ bound.eval (c.size + vsize v + t), TimedEval univ (encode c ++ SEP :: v) w t'

/-- Existence of an efficient universal machine (blueprint `lem:universal-tm`). -/
theorem exists_efficient_universal : Nonempty UniversalMachine := by
  sorry

open Classical in
/-- The result of running `c` on `v` for at most `k` cost, if it halts within the
budget (well-defined by `TimedEval.deterministic`). -/
noncomputable def evalWithin (c : Code) (v : List ℕ) (k : ℕ) : Option (List ℕ) :=
  if h : ∃ w t, t ≤ k ∧ TimedEval c v w t then some h.choose else none

/-- The word a clocked simulation returns: `1 :: w` on in-budget halting with output
`w`, and `[0]` on budget exhaustion. -/
noncomputable def clockedResult (c : Code) (v : List ℕ) (k : ℕ) : List ℕ :=
  match evalWithin c v k with
  | some w => 1 :: w
  | none => [0]

/-- **Clocked universal machine**: total simulation under a step budget `k`
(supplied as a single unary-priced cell), returning `clockedResult c v k` in time
polynomial in the budget, the program size and the input size. This is the
primitive with which deciders of the pipeline run other deciders, and with which
the recursive compression argument runs "`e` for `log n` steps". -/
structure ClockedUniversalMachine where
  /-- The clocked universal program; it takes `k :: (encode c ++ SEP :: v)`. -/
  univT : Code
  /-- The overhead polynomial. -/
  bound : Polynomial ℕ
  /-- Total, budget-bounded simulation. -/
  run : ∀ (c : Code) (v : List ℕ) (k : ℕ),
    ∃ t ≤ bound.eval (k + c.size + vsize v),
      TimedEval univT (k :: (encode c ++ SEP :: v)) (clockedResult c v k) t

/-- Existence of a clocked universal machine (blueprint `lem:universal-tm`). -/
theorem exists_clocked_universal : Nonempty ClockedUniversalMachine := by
  sorry

/-! ## Efficient Kleene recursion (blueprint `lem:kleene`; [MNY, Lemma 2.3]) -/

/-- **Efficient Kleene fixed point**: for a polynomial-time map on programs, a
program `e` with `e.eval = (F e).eval` whose runs are bounded by the runs of `F e`
at polynomial overhead. The proof is the classical construction through `hardcode`
and a `UniversalMachine`, tracking the overheads; the polynomial `p` depends on
`F.timeBound` and on the machine's `bound`.

Departure from [MNY, Lemma 2.3], which states the runtimes of `e` and `F e` as
*polynomially equivalent*: only the direction "runs of `F e` bound runs of `e`" is
used by the recursive compression argument (it is what makes the fixed point
polynomial-time), and only that direction follows from `UniversalMachine.time_le`.
The converse would need a lower-bound clause on the universal machine ("a simulation
is never faster than the simulated run"); it is omitted to keep the universal-machine
obligation minimal and can be restored with such a clause if a consumer needs it. -/
theorem efficient_fixed_point (F : PolyTimeFun Code Code) :
    ∃ (e : Code) (p : Polynomial ℕ),
      e.eval = (F e).eval ∧
      ∀ v w t, TimedEval (F e) v w t →
        ∃ t' ≤ p.eval (vsize v + t), TimedEval e v w t' := by
  sorry

end MIPRE.Cost
