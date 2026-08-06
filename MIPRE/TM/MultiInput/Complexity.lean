/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.MultiInput.TapeLemmas

/-!
# Time and space bounds for multi-input machines

The exact-run relation `MultiInputTM.ComputesInTimeAndSpace` mirrors the vendored CSLib
`Turing.MultiTapeTM.ComputesInTimeAndSpace` clause for clause (the machine has halted by
step `t`, has emitted exactly `output`, and has visited exactly `s` work-tape cells); the
equivalence with the one-input model is proved in `MIPRE.TM.MultiInput.OneInputEquiv`.

The packaged form `MultiInputTM.ComputesFunWithBounds` bounds time and space by arbitrary
functions of the *tuple of input lengths*. Deliberately, no convention such as "time as a
function of `∑ⱼ |xⱼ|`" or "of `maxⱼ |xⱼ|`" is baked in at this level: the paper states
verifier runtimes primarily as functions of a single index `n` with separate caps on the
other inputs (blueprint `def:lambda-bounded`), and any such shape instantiates the length
tuple directly. See `planning/tm-infrastructure.md`, decision D4.
-/

namespace Turing.MultiInputTM

variable {i w : ℕ} {State Symbol : Type*}

/-- A proof that the Turing machine `tm` on input tuple `input` outputs `output` in at
most `t` steps and uses exactly `s` space. Neither the alphabet nor the state set is
required to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiInputTM i w Symbol State)
    (input : Fin i → List Symbol) (output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.configs (tm.initCfg input) t).state = none ∧
  tm.outputString (tm.initCfg input) t = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A proof that the Turing machine `tm` computes the function `f` on `i`-tuples of
strings over an input/output alphabet embedded into the machine alphabet, within time
`timeBound` and space `spaceBound` — both arbitrary functions of the tuple of input
lengths. -/
def ComputesFunWithBounds
    (tm : MultiInputTM i w Symbol State)
    {IOSymbol : Type*}
    (f : (Fin i → List IOSymbol) → List IOSymbol)
    (emb : IOSymbol ↪ Symbol)
    (timeBound spaceBound : (Fin i → ℕ) → ℕ) : Prop :=
  ∀ x : Fin i → List IOSymbol,
    ∃ t ≤ timeBound (fun j => (x j).length), ∃ s ≤ spaceBound (fun j => (x j).length),
      tm.ComputesInTimeAndSpace (fun j => (x j).map emb) ((f x).map emb) t s

end Turing.MultiInputTM
