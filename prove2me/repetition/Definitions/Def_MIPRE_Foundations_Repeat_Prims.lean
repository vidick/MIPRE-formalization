/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-!
# Primitives of the repeated sampler and decider

Three loops of the ambient model that the programs of `thm:parallel-repetition` share
(`planning/repetition-verifier.md`, R3(a)–(b)):

* `powBody`: on the state `(e, bl, bn, acc)` — `e` a unary counter, `bl` and `bn` the bit
  lists of `λ` and `n`, `acc` a list — prepend `|bl| + |bn|` copies of `nil` to `acc`, `e`
  times (`powLoop_runs`). With `acc = []` the result is the unary numeral
  `e · (|λ| + |n|)`; with `acc` the numeral `1` it is the binary numeral `2^{e(|λ| + |n|)}`,
  the repetition count `k(n)` and the parse length `B(n)` of `MIPRE.Repetition`; with `acc`
  the bits of `s ≠ 0` it is `2^{e(|λ| + |n|)} · s`, the dimension of the repeated sampler.
* `dblBody`: on `(m, acc)`, `m` a unary counter and `acc` a unary numeral, double `acc` `m`
  times (`dblLoop_runs`): the unary numeral `2^m` from the unary numeral `m`.
* `takeBody` and `chunkBody`: cut a list into pieces of `s` elements (`Data.chunks`), `s`
  given in unary (`chunkLoop_runs`): the blocks of a vector of `𝔽₂^{k s}`.
-/

namespace MIPRE.Cost

open Data

namespace Data

/-- The elements of a datum read as a list: every datum is a `cons`-chain ending in `nil`. -/
def toList : Data → List Data
  | nil => []
  | cons a b => a :: toList b

@[simp] theorem list_toList : ∀ d : Data, list (toList d) = d
  | nil => rfl
  | cons a b => by simp [toList, list_toList b]

@[simp] theorem toList_list : ∀ l : List Data, toList (list l) = l
  | [] => rfl
  | a :: l => by simp [toList, toList_list l]

/-- The `i`-th piece of `s` elements of a list. -/
def chunk {α : Type*} (s i : ℕ) (l : List α) : List α := (l.drop (i * s)).take s

/-- The pieces of `s` elements of two lists, in lockstep: as many as the first list has, the
second one's possibly shorter or empty. -/
def chunkPairs (s : ℕ) (hs : 0 < s) : List Data → List Data → List (List Data × List Data)
  | [], _ => []
  | h :: l, y => ((h :: l).take s, y.take s) :: chunkPairs s hs ((h :: l).drop s) (y.drop s)
termination_by l => l.length
decreasing_by simp; omega

end Data

namespace Prog

/-! ## Prepending `e · (|bl| + |bn|)` copies of `nil` -/

/-- Body of the power walk: on the state `cons u (cons bl (cons bn acc))`, stop with `acc` if
the counter `u` is empty, and otherwise walk `bn` then `bl`, prepending a `nil` to `acc` per
element, and decrement `u`. -/
def powBody : Prog :=
  .elim 0 .nil
    (.elim 0
      (.elim 1 .nil (.elim 1 .nil (.cons .nil (.var 1))))
      (.elim 3 .nil (.elim 1 .nil
        (.let_ (.let_ (.cons (.var 0) (.var 1)) (.loop lenBody))
          (.let_ (.let_ (.cons (.var 3) (.var 0)) (.loop lenBody))
            (.cons (.cons .nil .nil)
              (.cons (.var 7) (.cons (.var 4) (.cons (.var 2) (.var 0))))))))))

/-- The state of the power walk. -/
def powState (e : ℕ) (bl bn acc : List Data) : Data :=
  .cons (ofNat e) (.cons (.list bl) (.cons (.list bn) (.list acc)))

/-- The cost of the power walk with counter `e` on lists of total length `L` and total size
`Σ`: `(e + 1)` rounds, each polynomial in the sizes. -/
def powCost (e L sz : ℕ) : ℕ := (e + 1) * (8 * (L + 1) * (sz + 2 * e * L + e + 14))

/-! ## Doubling a unary numeral -/

/-- Body of the doubling loop: on the state `cons u acc`, stop with `acc` if the counter `u` is
empty, and otherwise replace `acc` by `acc ++ acc` (reversal onto itself, `acc` being a list of
`nil`s) and decrement `u`. -/
def dblBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.let_ (.let_ (.cons (.var 3) (.var 3)) revOntoProg)
        (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))))

/-- The cost of the doubling loop: `m` rounds from the numeral `a`, the last on `2^m a`. -/
def dblCost (m a : ℕ) : ℕ := (m + 1) * ((2 ^ m * a + 1) * (4 * 2 ^ m * a + 14) + 10 * 2 ^ m * a + 2 * m + 32)

/-! ## Taking a prefix of given unary length -/

/-- Body of the take loop: on the state `cons u (cons rem cur)`, stop with `cons rem cur` if the
counter `u` is empty or `rem` is; otherwise move the head of `rem` onto `cur` and decrement. -/
def takeBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 3 .nil
        (.elim 0 (.cons .nil (.cons .nil (.var 1)))
          (.cons (.cons .nil .nil)
            (.cons (.var 5) (.cons (.var 1) (.cons (.var 0) (.var 3))))))))

/-- The state of the take loop. -/
def takeState (c : ℕ) (rem cur : List Data) : Data :=
  .cons (ofNat c) (.cons (.list rem) (.list cur))

end Prog

end MIPRE.Cost
