/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.CompressorProgram
import MIPRE.Foundations.ClassMIPStar

/-!
# The consequences of the halting reduction, conditionally on compression

Blueprint chapter 7 after `thm:main`, and `thm:halting-undecidable` of chapter 3, each proved
from a `GapCompression` (the hypothesis structure of `thm:compression`) and a universal machine:

* `halting_undecidable`, `halting_re`: Turing's theorem, from Mathlib's
  `ComputablePred.halting_problem` and `halting_problem_re` at the empty input.
* `gameValue_uncomputable_of`, `quantumValue_uncomputable_of` (`cor:value-uncomputable`): no
  computable predicate decides, under the promise that the value is `1` or at most `1/2`, which
  it is — in either value.
* `re_subset_mipstar_of` and `mipstar_eq_re_of` (`thm:mipstar-eq-re`): `RE ⊆ MIP*` by
  reducing membership in an r.e. language to halting on the empty input (`Nat.Partrec.Code.curry`)
  and composing with the reduction; with `MIPStar.isRE`, `MIP* = RE`.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)
open Nat.Partrec (Code)

/-! ## Turing's theorem -/

/-- **The halting problem is not decidable** (blueprint `thm:halting-undecidable`): Mathlib's
`ComputablePred.halting_problem` at the empty input. -/
theorem halting_undecidable : ¬ ComputablePred fun c : Code => HaltingGameValue.HaltsOnEmptyInput c :=
  ComputablePred.halting_problem 0

/-- **The halting problem is r.e.** -/
theorem halting_re : REPred fun c : Code => HaltingGameValue.HaltsOnEmptyInput c :=
  ComputablePred.halting_problem_re 0

namespace Halting

variable (G : GapCompression) (U : UniversalMachine)

/-! ## Uncomputability of the value -/

/-- A computable predicate separating the two sides of a promise problem decides every problem
that reduces to it: the shape both halves of `cor:value-uncomputable` use. -/
private theorem not_decidable_of_reduction {P : GameData → Prop}
    (h : ∃ g : Code → GameData, Computable g ∧
      ∀ pc, (HaltingGameValue.HaltsOnEmptyInput pc → P (g pc)) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc → ¬ P (g pc))) :
    ¬ ∃ f : GameData → Bool, Computable f ∧ ∀ d, P d ↔ f d = true := by
  rintro ⟨f, hf, hfP⟩
  obtain ⟨g, hg, hgap⟩ := h
  refine halting_undecidable (ComputablePred.computable_iff.2 ⟨fun pc => f (g pc), hf.comp hg, ?_⟩)
  funext pc
  apply propext
  constructor
  · intro hd; exact (hfP _).1 ((hgap pc).1 hd)
  · intro hb; by_contra hd; exact (hgap pc).2 hd ((hfP _).2 hb)

include G U in
/-- **Uncomputability of the synchronous value** (blueprint `cor:value-uncomputable`),
conditionally on compression: no computable `f` answers `true` on every description of
synchronous value `1` and `false` on every description of synchronous value at most `1/2`. -/
theorem gameValue_uncomputable_of :
    ¬ ∃ f : GameData → Bool, Computable f ∧
      (∀ d, HaltingGameValue.gameValue d.toGame = 1 → f d = true) ∧
      (∀ d, HaltingGameValue.gameValue d.toGame ≤ 1 / 2 → f d = false) := by
  rintro ⟨f, hf, h1, h2⟩
  obtain ⟨g, hg, hgap⟩ := halting_reduces_to_gameValue_of G U
  refine not_decidable_of_reduction (P := fun d => f d = true) ⟨g, hg, fun pc => ?_⟩ ⟨f, hf, fun _ => Iff.rfl⟩
  exact ⟨fun hd => h1 _ ((hgap pc).1 hd), fun hd => by rw [h2 _ ((hgap pc).2 hd)]; decide⟩

include G U in
/-- **Uncomputability of the quantum value** (blueprint `cor:value-uncomputable`, second
clause), conditionally on compression. -/
theorem quantumValue_uncomputable_of :
    ¬ ∃ f : GameData → Bool, Computable f ∧
      (∀ d, quantumValue d.game = 1 → f d = true) ∧
      (∀ d, quantumValue d.game ≤ 1 / 2 → f d = false) := by
  rintro ⟨f, hf, h1, h2⟩
  obtain ⟨g, hg, hgap⟩ := halting_reduction_quantum_of G U
  refine not_decidable_of_reduction (P := fun d => f d = true) ⟨g, hg, fun pc => ?_⟩ ⟨f, hf, fun _ => Iff.rfl⟩
  exact ⟨fun hd => h1 _ ((hgap pc).1 hd), fun hd => by rw [h2 _ ((hgap pc).2 hd)]; decide⟩

/-! ## `RE ⊆ MIP*`, hence `MIP* = RE` -/

/-- **Every r.e. language many-one reduces to the halting problem**: a computable map from
strings to codes, halting on the empty input exactly on the members. Mathlib's
`Nat.Partrec.Code.curry` fixes the string into the code. -/
theorem exists_code_halts_of_isRE {L : Set BitStr} (h : IsRE L) :
    ∃ r : BitStr → Code, Computable r ∧ ∀ x, HaltingGameValue.HaltsOnEmptyInput (r x) ↔ x ∈ L := by
  -- the r.e. predicate as a partial recursive function on naturals, then a code for it
  have hF : Nat.Partrec fun m : ℕ =>
      Part.bind (↑(Encodable.decode (α := BitStr) m.unpair.1)) fun x =>
        (Part.assert (x ∈ L) fun _ => Part.some ()).map Encodable.encode := by
    have hp : Partrec fun m : ℕ => Part.bind (↑(Encodable.decode (α := BitStr) m.unpair.1))
        fun x => (Part.assert (x ∈ L) fun _ => Part.some ()).map Encodable.encode :=
      (Partrec.nat_iff.2 h).comp (Primrec.fst.comp Primrec.unpair).to_comp
    exact Partrec.nat_iff.1 hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hF
  refine ⟨fun x => Code.curry c (Encodable.encode x),
    Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.encode, fun x => ?_⟩
  show (Code.eval (Code.curry c (Encodable.encode x)) 0).Dom ↔ x ∈ L
  rw [Code.eval_curry, hc]
  simp [Part.assert]

include G U in
/-- **`RE ⊆ MIP*`**, conditionally on compression: compose the many-one reduction of an r.e.
language to the halting problem with the halting reduction of `cor:main-quantum`. -/
theorem re_subset_mipstar_of {L : Set BitStr} (h : IsRE L) : MIPStar L := by
  obtain ⟨r, hr, hrL⟩ := exists_code_halts_of_isRE h
  obtain ⟨g, hg, hgap⟩ := halting_reduction_quantum_of G U
  refine ⟨fun x => g (r x), hg.comp hr, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact (hgap (r x)).1 ((hrL x).2 hx)
  · exact (hgap (r x)).2 fun hd => hx ((hrL x).1 hd)

include G U in
/-- **`MIP* = RE`** (blueprint `thm:mipstar-eq-re`), conditionally on compression: the two
classes coincide, as predicates on languages. -/
theorem mipstar_eq_re_of : MIPStar = IsRE :=
  funext fun _ => propext ⟨MIPStar.isRE, re_subset_mipstar_of G U⟩

end Halting

end MIPRE
