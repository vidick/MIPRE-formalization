/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Pcp
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Admissible fields exist

`MIPRE.SAT.BinField k` is what `thm:pcp-decider` takes as a parameter: a field of size `2^k`
with a fixed `k`-bit representation of its elements. This file inhabits it, for every `k ≥ 1`.

The field is Mathlib's `GaloisField 2 k` and the representation is the coordinate vector in an
arbitrary basis. That is enough for `BinField` as stated -- the structure asks for the
cardinality and a representation with a left inverse, and nothing more -- so it is enough to
remove `thm:pcp-decider`'s field parameter from the list of things this project assumes.

**What this does not do.** It is *not* `lem:self-dual-basis`. The basis here is whatever
`Module.finBasisOfFinrankEq` returns; it is not normal, not self-dual, and carries no
multiplication tables, so the `\downsize` maps of `lem:downsize-field` are not computed by the
trace form and there is no `poly(k)` bound on anything. Consumers that need those --- the
downsized samplers of `lem:cl-downsize` past field size `2` --- need the self-dual normal
basis, and `MIPRE.SAT.BinField` will have to grow fields for it before they can be served.
The point of this file is the narrower one: nothing in the pipeline should be blocked on an
*existence* question that Mathlib already answers.
-/

noncomputable section

namespace MIPRE.SAT

open Finset

/-- The coordinate representation of a `ZMod 2`-vector as bits. -/
private def bitOf (z : ZMod 2) : Bool := z = 1

private theorem ite_bitOf (z : ZMod 2) : (if bitOf z then (1 : ZMod 2) else 0) = z := by
  revert z
  decide

/-- **An admissible field of size `2^k` with a bit representation**, for every `k ≥ 1`:
Mathlib's `GaloisField 2 k` with coordinates in a basis. See the module docstring for what this
is *not*. -/
def binFieldGalois (k : ℕ) (hk : k ≠ 0) : BinField k :=
  letI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  letI : DecidableEq (GaloisField 2 k) := Classical.decEq _
  let b : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k) :=
    Module.finBasisOfFinrankEq (ZMod 2) (GaloisField 2 k) (GaloisField.finrank 2 hk)
  { carrier := GaloisField 2 k
    instField := inferInstance
    instFintype := inferInstance
    instDecidableEq := inferInstance
    card_carrier := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 k hk
    toBits := fun x => List.ofFn fun i => bitOf (b.repr x i)
    ofBits := fun l => ∑ i : Fin k, (if l.getD i false then (1 : ZMod 2) else 0) • b i
    length_toBits := fun _ => List.length_ofFn
    ofBits_toBits := fun x => by
      refine (Finset.sum_congr rfl fun i _ => ?_).trans (b.sum_repr x)
      congr 1
      rw [show (List.ofFn fun i => bitOf ((b.repr x) i)).getD (i : ℕ) false = bitOf (b.repr x i)
        from by simp, ite_bitOf] }

theorem nonempty_binField (k : ℕ) (hk : k ≠ 0) : Nonempty (BinField k) :=
  ⟨binFieldGalois k hk⟩

end MIPRE.SAT

end
