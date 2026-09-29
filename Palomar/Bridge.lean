/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.MainTheorem
public import MIPRE.Foundations.ClassMIPStar
public import MIPRE.Foundations.GameDescription

@[expose] public section

/-!
# The library, in the vocabulary of the Palomar Challenge

`Palomar/Challenge.lean` states `MIP* = RE` on top of Mathlib alone, and `Palomar/Solution.lean`
proves it by transport from this library. This file holds the library-side half of that
transport: each result of the library is restated here in the shape the Challenge gives it, so
that the Solution only has to identify the Challenge's own types with the library's.

Nothing here mentions the Challenge's declarations, which the Solution declares (Palomar's
comparator matches them by name, so the Solution declares them itself and imports no file that
does); everything is stated in the library's vocabulary and proved from the library's theorems.

* `halting_reduction_both`: the halting reduction, unconditional, on one computable map and in
  both values (`MIPRE.Halting.halting_reduction_both_of` at the compression of
  `MIPRE/MainTheorem.lean`).
* `isRE_iff_exists_code`: `MIPRE.IsRE` (Mathlib's `REPred`) is the halting-set form the
  Challenge uses, through `Nat.Partrec.Code.exists_code`.
* `PolyVerifier.seedCount_eq`: on an efficient verifier, the seed count of the library's game
  `G_z` is a count of seeds `List.Vector Bool B` on which the sampler outputs the question pair.
* `mipstar_iff`: `MIPRE.MIPStar` with the verifier's game characterized (distribution and
  decision predicate pinned) rather than constructed.
-/

namespace MIPRE.Palomar.Bridge

open MIPRE MIPRE.Cost HaltingGameValue Verifier

/-! ## The halting reduction, in both values -/

/-- **The halting reduction** (Theorem 12.2 of "MIP* = RE"), unconditional, on one computable
map and in both the synchronous and the quantum value: the instance of
`MIPRE.Halting.halting_reduction_both_of` at the gap-preserving compression of
`MIPRE/MainTheorem.lean`, whose two halves are `HaltingGameValue.halting_reduces_to_gameValue`
and `MIPRE.Halting.halting_reduction_quantum`. -/
theorem halting_reduction_both :
    ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
      ∀ c : Nat.Partrec.Code,
        (HaltsOnEmptyInput c →
          gameValue (g c).toGame = 1 ∧ quantumValue (g c).game = 1) ∧
        (¬ HaltsOnEmptyInput c →
          gameValue (g c).toGame ≤ 1 / 2 ∧ quantumValue (g c).game ≤ 1 / 2) :=
  MIPRE.Halting.halting_reduction_both_of MIPRE.gapCompression Cost.selfUniversal

/-! ## Recursive enumerability through Gödel numbers -/

/-- A language is recursively enumerable (`MIPRE.IsRE`, Mathlib's `REPred`) iff it is the
halting set, on Gödel numbers of strings, of some partial recursive function
`c : Nat.Partrec.Code`. -/
theorem isRE_iff_exists_code (L : Set BitStr) :
    MIPRE.IsRE L ↔
      ∃ c : Nat.Partrec.Code, ∀ z : BitStr, z ∈ L ↔ (c.eval (Encodable.encode z)).Dom := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 h
    refine ⟨c, fun z => ?_⟩
    rw [hc, Part.dom_iff_mem]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.mem_map_iff,
      Part.mem_assert_iff, Part.mem_some_iff, exists_prop]
    exact ⟨fun hz => ⟨Encodable.encode (), (), ⟨hz, trivial⟩, rfl⟩,
      fun ⟨_, _, ⟨hz, _⟩, _⟩ => hz⟩
  · rintro ⟨c, hc⟩
    have h1 : Partrec fun z : BitStr => c.eval (Encodable.encode z) :=
      (Partrec.nat_iff.2 (Nat.Partrec.Code.exists_code.2 ⟨c, rfl⟩)).comp Computable.encode
    refine (h1.map (Computable.const ()).to₂).of_eq fun z => ?_
    ext u
    rw [Part.mem_map_iff, Part.mem_assert_iff]
    constructor
    · rintro ⟨n, hn, -⟩
      exact ⟨(hc z).2 (Part.dom_iff_mem.2 ⟨n, hn⟩),
        Part.mem_some_iff.2 (Subsingleton.elim _ _)⟩
    · rintro ⟨hz, -⟩
      obtain ⟨n, hn⟩ := Part.dom_iff_mem.1 ((hc z).1 hz)
      exact ⟨n, hn, Subsingleton.elim _ _⟩

/-! ## The game of a verifier, characterized -/

namespace PolyVerifier

variable (V : MIPRE.PolyVerifier)

/-- On an efficient verifier, a seed of length `B z` produces the question pair `(x, y)` exactly
when the sampler halts on it with (the encoding of) `(x, y)`. -/
theorem questions_eq_iff {z : BitStr} (hV : V.Efficient z) {r : BitStr}
    (hr : r.length = V.B z) (x y : Answers (V.B z)) :
    V.questions z r = (x, y) ↔
      ∃ t, V.sampler.Runs (encode (z, r)) (encode (x.1, y.1)) t := by
  obtain ⟨x', y', t, -, hrun, hx, hy⟩ := V.questions_eq_of_efficient hV hr
  constructor
  · intro hq
    have hx1 : x.1 = x' := by rw [← hx, hq]
    have hy1 : y.1 = y' := by rw [← hy, hq]
    exact ⟨t, by rw [hx1, hy1]; exact hrun⟩
  · rintro ⟨t', hrun'⟩
    obtain ⟨he, -⟩ := hrun.deterministic hrun'
    have h := encode_injective he
    rw [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext (hx.trans h.1)) (Subtype.ext (hy.trans h.2))

open Classical in
/-- On an efficient verifier, the seed count of the library's game `G_z`
(`MIPRE.PolyVerifier.seedCount`, a count over the list `Data.bitStrsOfLen (B z)`) is the number
of seeds `r : List.Vector Bool (B z)` on which the sampler outputs `(x, y)`. -/
theorem seedCount_eq {z : BitStr} (hV : V.Efficient z) (x y : Answers (V.B z)) :
    V.seedCount z x y =
      (Finset.univ.filter fun r : List.Vector Bool (V.B z) =>
        ∃ t, V.sampler.Runs (encode (z, r.1)) (encode (x.1, y.1)) t).card := by
  have h1 : V.seedCount z x y =
      ((Data.bitStrsOfLen (V.B z)).toFinset.filter fun r => V.questions z r = (x, y)).card := by
    rw [List.Nodup.card_eq_countP (Data.nodup_bitStrsOfLen _), List.countP_eq_length_filter]
    rfl
  rw [h1]
  refine Finset.card_bij'
    (fun r hr =>
      ⟨r, (Data.mem_bitStrsOfLen _ _).1 (List.mem_toFinset.1 (Finset.mem_filter.1 hr).1)⟩)
    (fun v _ => v.1) (fun r hr => ?_) (fun v hv => ?_) (fun r hr => rfl) (fun v hv => rfl)
  · obtain ⟨hmem, hq⟩ := Finset.mem_filter.1 hr
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (questions_eq_iff V hV ((Data.mem_bitStrsOfLen _ _).1 (List.mem_toFinset.1 hmem)) x y).1 hq⟩
  · refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 ((Data.mem_bitStrsOfLen _ _).2 v.2), ?_⟩
    exact (questions_eq_iff V hV v.2 x y).2 (Finset.mem_filter.1 hv).2

open Classical in
/-- The distribution of the library's game `G_z`, on an efficient verifier: the law of the
sampler's output on a uniform seed of length `B z`. -/
theorem game_μ_eq {z : BitStr} (hV : V.Efficient z) (x y : Answers (V.B z)) :
    (V.game z).μ x y =
      ((Finset.univ.filter fun r : List.Vector Bool (V.B z) =>
        ∃ t, V.sampler.Runs (encode (z, r.1)) (encode (x.1, y.1)) t).card : ℝ) / 2 ^ V.B z := by
  rw [MIPRE.PolyVerifier.game_μ, seedCount_eq V hV]

open Classical in
/-- A game on the alphabet of `G_z` with the distribution and the decision predicate of `G_z` has
the quantum value of `G_z`. -/
theorem quantumValue_eq_game {z : BitStr} (hV : V.Efficient z)
    (G : Game (Answers (V.B z)) (Answers (V.B z)) (Answers (V.B z)) (Answers (V.B z)))
    (hμ : ∀ x y, G.μ x y =
      ((Finset.univ.filter fun r : List.Vector Bool (V.B z) =>
        ∃ t, V.sampler.Runs (encode (z, r.1)) (encode (x.1, y.1)) t).card : ℝ) / 2 ^ V.B z)
    (hD : ∀ x y a b, G.D x y a b = decide (V.Accepts z x.1 y.1 a.1 b.1)) :
    quantumValue G = quantumValue (V.game z) :=
  quantumValue_eq_of_equiv (V.game z) G (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    (Equiv.refl _) (fun x y => by rw [hμ, game_μ_eq V hV]; rfl)
    (fun x y a b => by rw [hD, MIPRE.PolyVerifier.game_D]; rfl)

end PolyVerifier

open Classical in
/-- **The class `MIP*_{1,1/2}(2,1)`, with the game characterized.** `MIPRE.MIPStar L` holds iff
some polynomial-time verifier is efficient on every input `z` and some game on the strings of
length at most `B z` — whose question distribution is the law of the sampler's output on a
uniform seed of length `B z`, and whose decision predicate is the decider's verdict — has
quantum value `1` when `z ∈ L` and at most `1/2` when `z ∉ L`. The library constructs that game
(`MIPRE.PolyVerifier.game`); under efficiency it is the only one. -/
theorem mipstar_iff (L : Set BitStr) :
    MIPRE.MIPStar L ↔
      ∃ V : MIPRE.PolyVerifier, ∀ z : BitStr, V.Efficient z ∧
        ∃ G : Game (Answers (V.B z)) (Answers (V.B z)) (Answers (V.B z)) (Answers (V.B z)),
          (∀ x y, G.μ x y =
            ((Finset.univ.filter fun r : List.Vector Bool (V.B z) =>
              ∃ t, V.sampler.Runs (encode (z, r.1)) (encode (x.1, y.1)) t).card : ℝ)
                / 2 ^ V.B z) ∧
          (∀ x y a b, G.D x y a b = decide (V.Accepts z x.1 y.1 a.1 b.1)) ∧
          (z ∈ L → quantumValue G = 1) ∧
          (z ∉ L → quantumValue G ≤ 1 / 2) := by
  constructor
  · rintro ⟨V, hE, hval⟩
    exact ⟨V, fun z => ⟨hE z, V.game z, fun x y => PolyVerifier.game_μ_eq V (hE z) x y,
      fun x y a b => MIPRE.PolyVerifier.game_D V z x y a b, (hval z).1, (hval z).2⟩⟩
  · rintro ⟨V, h⟩
    refine ⟨V, fun z => (h z).1, fun z => ?_⟩
    obtain ⟨hE, G, hμ, hD, h1, h2⟩ := h z
    rw [← PolyVerifier.quantumValue_eq_game V hE G hμ hD]
    exact ⟨h1, h2⟩

end MIPRE.Palomar.Bridge

end
