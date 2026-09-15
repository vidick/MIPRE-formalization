/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ValueApprox.RawComplete
import MIPRE.Foundations.ValueApprox.RawPrimrec
import Mathlib.Computability.RE

/-!
# The quantum value is approximable from below: the `val*` half of `lem:value-lower-approx`

`MIPRE.ValueApprox.rePred_lt_quantumValue`: the set of pairs `(g, p / q)` of a game
description and a nonnegative rational threshold with `val*(G_g) > p / q` is recursively
enumerable, in Mathlib's sense (`REPred`, the domain of a partial computable function).

The procedure is the one of statement (S) in the paper's proof of `cor:mip-re`, with exact
candidates: dovetail over the raw candidates `r` (`RawStrategy`, a `Primcodable` type) and halt
on the first that passes the primitive recursive check `Check g p q r`. Some candidate passes
iff `p / q < val*(G_g)` (`exists_check_iff`), so the search halts exactly on the members of the
set; the boundary case `val* = p / q` is correctly non-halting.

Thresholds are nonnegative rationals given as fractions `p / q` of naturals, as in the paper's
(S) (`t ∈ [0, 1]`); a negative threshold is trivial, since `val* ≥ 0`. For `q = 0` the real
number `p / q` is `0`, and the check tests `0 < val*` accordingly.
-/

namespace MIPRE.ValueApprox

open HaltingGameValue (GameData)

/-- A predicate of the form `∃ b, p a b` with `p` primitive recursive is recursively enumerable:
search over the codes of `b`. -/
theorem REPred.of_primrecRel_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → β → Prop} (hp : PrimrecRel p) : REPred fun a => ∃ b, p a b := by
  obtain ⟨inst, hp⟩ := hp
  -- the search predicate: decode `n` and test
  let q : α × ℕ → Bool := fun x =>
    ((Encodable.decode x.2 : Option β).map fun b => @decide (p x.1 b) (inst (x.1, b))).getD false
  have hq : Primrec q :=
    Primrec.option_getD.comp
      (Primrec.option_map (Primrec.decode.comp Primrec.snd)
        (hp.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)
      (Primrec.const false)
  have hpart : Partrec fun a : α => Nat.rfind fun n => (Part.some (q (a, n)) : Part Bool) :=
    Partrec.rfind (p := fun a n => (Part.some (q (a, n)) : Part Bool)) hq.to_comp.partrec
  refine hpart.dom_re.of_eq fun a => ?_
  refine (Nat.rfind_dom' (p := fun n => (Part.some (q (a, n)) : Part Bool))).trans ?_
  constructor
  · rintro ⟨n, hn, -⟩
    rw [Part.mem_some_iff] at hn
    revert hn
    simp only [q]
    cases h : (Encodable.decode n : Option β) with
    | none => simp
    | some b =>
      intro hb
      simp only [Option.map_some, Option.getD_some, Bool.true_eq, decide_eq_true_eq] at hb
      exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    refine ⟨Encodable.encode b, ?_, fun _ => trivial⟩
    rw [Part.mem_some_iff]
    simp [q, Encodable.encodek, hb]

/-- **The quantum value from below** (the `val*` half of `lem:value-lower-approx`): the pairs
`(g, (p, q))` with `p / q < val*(G_g)` form a recursively enumerable set. -/
theorem rePred_lt_quantumValue :
    REPred fun x : GameData × ℕ × ℕ => (x.2.1 : ℝ) / x.2.2 < quantumValue x.1.game := by
  have h : PrimrecRel fun (x : GameData × ℕ × ℕ) (r : RawStrategy) => Check x.1 x.2.1 x.2.2 r :=
    primrecPred_check
  exact (REPred.of_primrecRel_exists h).of_eq fun x => exists_check_iff x.1 x.2.1 x.2.2

end MIPRE.ValueApprox
