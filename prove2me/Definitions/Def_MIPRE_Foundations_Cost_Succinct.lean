/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Succinct.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

/-!
# Succinct descriptions and the bit-query program

`IsSuccinctDesc c n x` is [MNY, Definition 2.4] (blueprint `def:succinct`), with the time
bound adapted to the ambient model (see the module docstring of
`MIPRE.Foundations.Compression`). The **bit-query program** `bitQueryProg univ` of the
recursive compression argument answers bit-queries about a string that is only given
*implicitly*, as the output of a program `c'` on an input `(e, n)`: on
`encode (((c', e), n), m)` it simulates `c'` on `encode (e, n)` through the universal machine
and indexes the result with `bitAtProg`. Its correctness is conditional on the run of `c'`
(`bitQueryProg_runs`), and hardcoding `((c', e), n)` into it gives a succinct description of
that output whenever the run is fast enough for the budget (`isSuccinctDesc_hardcode`).
-/

namespace MIPRE.Cost

open Polynomial

/-! ## Succinct descriptions ([MNY, Definition 2.4]; blueprint `def:succinct`) -/

/-- `(c, n)` **succinctly describes** the bit string `x`: `c` is a closed program, `x` has
length at most `2 ^ n`, and `c` answers every bit-query `m` (presented in binary; the
answer is `bitQueryAnswer x m`) within cost `(n + 1) * (|m| + 1) ^ 2`.

[MNY, Definition 2.4], with the time bound adapted as discussed in the module docstring of
`MIPRE.Foundations.Compression`. The pair `(c, n)` is exponentially smaller than `x` itself;
a compression procedure's guarantees are only required on genuine succinct descriptions,
but it must *run* (in polynomial time) on all inputs. -/
def IsSuccinctDesc (c : Prog) (n : ℕ) (x : BitStr) : Prop :=
  c.WellScoped 1 ∧ x.length ≤ 2 ^ n ∧
    ∀ m : ℕ, ∃ t ≤ (n + 1) * (Nat.size m + 1) ^ 2, c.Runs (encode m) (bitQueryAnswer x m) t

namespace Prog

/-- The bit-query program: on `encode (((c', e), n), m)`, run `univ` on
`cons (encode c') (encode (e, n))` to obtain the string `y`, then answer the bit-query `m`
about `y` with `bitAtProg`. -/
def bitQueryProg (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil
    (.let_ (.cons (.var 0) (.cons (.var 1) (.var 3)))
      (.let_ (callVar 0 univ)
        (.let_ (.cons (.var 0) (.var 7))
          (callVar 0 bitAtProg))))))

end Prog

/-- The cost of the bit-query program, as a polynomial in
`s = esize c' + esize e + esize n + t` (with `t` the cost of the run of `c'`), per
`(|m| + 1) ^ 2`. -/
noncomputable def bitQueryBound (U : UniversalMachine) : Polynomial ℕ :=
  U.bound.comp (X + C 1) + (X + C 1) * (X + C 534) + C 2 * X + C 29

end MIPRE.Cost
