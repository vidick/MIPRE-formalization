/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LiehrTsirelson.Bridge
import MIPRE.Background.LiehrTsirelson.Upstream.MainStatement
import MIPRE.Tsirelson

/-!
# The three terminal propositions of `lukasliehr/MIPRE`, proved

The vendored `MainStatement.lean` states three propositions in its own vocabulary and proves
none of them: `QuantitativeSeparationStatement` (a game with `valStar ≤ 1/2` and `valCo = 1`),
`NegativeTsirelsonStatement` (`C_qa(n,k) ⊂ C_qc(n,k)` for some `n, k ≥ 1`) and
`GameValueSeparationStatement` (a square game with `valStar < valCo = 1`). This file proves all
three from `MIPRE.separation` through the bridge of `Bridge.lean`.

The separating game is the one of `MIPRE.separation`, read as a vendored square game on
`Fin (nX + 1)` questions and `Fin (nA + 1)` answers; its vendored finite-dimensional value is
at most this repository's quantum value (`valStar_toLiehr_le`), which is at most `1/2`, and its
vendored commuting value is this repository's commuting-operator value (`valCo_toLiehr`), which
is `1`. The correlation of `MIPRE.separation` that lies in `C_qc` but not in `C_qa` does so
for the vendored sets too, since the vendored `C_qc` is this repository's and the vendored
`C_qa` is contained in this repository's.
-/

namespace MIPRE.Liehr

/-- The separating game of `MIPRE.separation`, as a vendored square game: `valStar ≤ 1/2`
and `valCo = 1`. -/
theorem exists_liehr_game :
    ∃ (n k : ℕ) (G : Tsirelson.Game (n + 1) (k + 1)),
      Tsirelson.valStar G ≤ 1 / 2 ∧ Tsirelson.valCo G = 1 := by
  obtain ⟨d, hq, hco, -⟩ := MIPRE.separation
  refine ⟨d.nX, d.nA, toLiehr d.game, (valStar_toLiehr_le d.game).trans hq, ?_⟩
  rw [valCo_toLiehr]
  exact hco

/-- **B28 of `lukasliehr/MIPRE`**: the quantitative separation. -/
theorem quantitativeSeparation : Tsirelson.QuantitativeSeparationStatement := by
  obtain ⟨n, k, G, h1, h2⟩ := exists_liehr_game
  exact ⟨Tsirelson.GameSig.ofGame G, h1, h2⟩

/-- **B30 of `lukasliehr/MIPRE`, second clause**: a square game with `valStar < valCo = 1`. -/
theorem gameValueSeparation : Tsirelson.GameValueSeparationStatement := by
  obtain ⟨n, k, G, h1, h2⟩ := exists_liehr_game
  refine ⟨n + 1, k + 1, G, Nat.succ_le_succ (Nat.zero_le n), Nat.succ_le_succ (Nat.zero_le k),
    ?_, h2⟩
  rw [h2]
  linarith

/-- **B30 of `lukasliehr/MIPRE`, first clause**: the negative answer to Tsirelson's problem,
`C_qa(n,k) ⊂ C_qc(n,k)` for some `n, k ≥ 1`. -/
theorem negativeTsirelson : Tsirelson.NegativeTsirelsonStatement := by
  obtain ⟨d, -, -, p, hp, -, hnot⟩ := MIPRE.separation
  refine ⟨d.nX + 1, d.nA + 1, Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_succ (Nat.zero_le _),
    ?_⟩
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨?_, fun h => ?_⟩
  · calc Tsirelson.Cqa (d.nX + 1) (d.nA + 1)
        ⊆ Cqa (Fin (d.nX + 1)) (Fin (d.nX + 1)) (Fin (d.nA + 1)) (Fin (d.nA + 1)) :=
          tensorCorrelationClosure_subset_Cqa
      _ ⊆ Cqc (Fin (d.nX + 1)) (Fin (d.nX + 1)) (Fin (d.nA + 1)) (Fin (d.nA + 1)) :=
          Cqa_subset_Cqc
      _ = Tsirelson.Cqc (d.nX + 1) (d.nA + 1) := commutingCorrelations_eq_Cqc.symm
  · have hp' : p ∈ Tsirelson.Cqc (d.nX + 1) (d.nA + 1) := by
      show p ∈ Tsirelson.CommutingCorrelations _ _ _ _
      rw [commutingCorrelations_eq_Cqc]
      exact hp
    rw [← h] at hp'
    exact hnot (tensorCorrelationClosure_subset_Cqa hp')

end MIPRE.Liehr
