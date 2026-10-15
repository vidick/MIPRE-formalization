/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Toolkit.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Toolkit does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

/-!
# The efficient computability toolkit

The efficient versions of the universal machine, the s-m-n theorem, and Kleene's
recursion theorem, in the ambient cost model — blueprint Section
`sec:rr-computability` (`lem:universal-tm`, `lem:smn`, `lem:kleene`), following
[MNY, Lemmas 2.1–2.3]. Mathlib has the computability halves for `Nat.Partrec.Code`
(`Nat.Partrec.Code.smn`, `eval_part`, `fixed_point`); everything with a time bound
is new.

Contents:

* `hardcode`: the **efficient s-m-n**. `hardcode p d = let_ (cons (const d) (var 0)) p`
  binds the pair `(d, input)` as the input of `p`. The witness makes [MNY, Lemma 2.2]
  quantitative and stronger than stated there: the time overhead is *additive and linear*
  in the sizes of `d` and of the input, and the description grows by exactly `d.size + 35`
  nodes (paper: polynomial). `smn_polyTime` is the runtime version — the map is itself
  polynomial-time computable in the model (`smnProg`, linear time) — generic in the type of
  the hardcoded value.
* `UniversalMachine` / `exists_efficient_universal` (`lem:universal-tm`): a fixed closed
  program `univ` that, on the pair `(encode c, v)`, halts exactly when `c` halts on `v`,
  with the same result and polynomial time overhead — packaged as data (the program and its
  overhead polynomial); its existence is proved in `Cost/Universal.lean` by a
  self-interpreter.
* `ClockedUniversalMachine` / `exists_clocked_universal`: the time-bounded variant ("run
  `c` on `v` for `k` steps"), used by the recursive compression argument and by the
  pipeline's deciders (introspection and repetition simulate other deciders under a budget).
* `efficient_fixed_point` (`lem:kleene`, in `Cost/Kleene.lean`): Kleene's recursion theorem
  for a polynomial-time map on programs, with the runs of the fixed point bounded by those
  of its image at polynomial overhead — proved from the universal machine and `hardcode`.

The statement shapes were audited against the proof of the recursive compression lemma
(`planning/compression-track.md`, K0): the universal machines are structures so that
downstream definitions can name the program and its polynomial without any sorried `def`;
the runtime s-m-n is generic in the hardcoded type; Kleene is stated in the one direction
the argument uses (see its docstring).

Effort notes (matching the blueprint's `\effortHard` on this section): the s-m-n lemmas
are elementary. The two universal-machine theorems are the hard core — a self-interpreter
of `Prog` written in `Prog` with polynomial overhead (`Cost/Interpreter.lean`,
`Cost/MachineBound.lean`, `Cost/Universal.lean`); this is the same kind of artifact as the
interpreter underlying the succinct Cook–Levin gateway (`thm:succinct-sat`), and the two
developments should share design.
-/

namespace MIPRE.Cost

open Polynomial

/-! ## The efficient s-m-n (blueprint `lem:smn`; [MNY, Lemma 2.2]) -/

/-- The description of a hardcoded program, spelled out. -/
theorem toData_hardcode (p : Prog) (d : Data) :
    (hardcode p d).toData = .cons (.ofNat 4) (.cons (.cons (.ofNat 2)
      (.cons (.cons (.ofNat 6) d) (.cons .nil .nil))) p.toData) := rfl

/-! ## The efficient universal machine (blueprint `lem:universal-tm`; [MNY, Lemma 2.1])

The two universal machines are *structures*: the program and its overhead polynomial are
fields, so that downstream definitions (deciders simulating other deciders under a budget;
the λ-bookkeeping of [JNVWY, §12.2], which chooses λ above the concrete overhead
polynomials) can refer to them as data. Their existence is proved in `Cost/Universal.lean`
(`selfUniversal`, `selfClockedUniversal`). -/

/-! `exists_efficient_universal : Nonempty UniversalMachine` (blueprint `lem:universal-tm`)
is proved in `Cost/Universal.lean` by the self-interpreter. -/

/-! `exists_clocked_universal : Nonempty ClockedUniversalMachine` (blueprint
`lem:universal-tm`) is proved in `Cost/Universal.lean` by the clocked self-interpreter. -/

/-! ## Efficient Kleene recursion

`efficient_fixed_point` (blueprint `lem:kleene`; [MNY, Lemma 2.3]) is proved in
`Cost/Kleene.lean` from `hardcode`, `smnProg` and a `UniversalMachine`. -/

end MIPRE.Cost
