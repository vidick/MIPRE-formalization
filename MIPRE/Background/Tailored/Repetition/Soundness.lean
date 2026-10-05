/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.Verifier
public import MIPRE.Background.Repetition.Soundness
public import MIPRE.Tactics

@[expose] public section

/-!
# Soundness of repeated tailored verifiers

The soundness half of paper II's `thm:repetition` (II:11103) in the direct form of the plan
(`planning/aldous-lyons-track.md`, Phase 2): the repeated verifier's game accepts, through the
coordinates of its answers, only what the direct repetition of `𝒱_n`'s bipartite game accepts
(`MIPRE.Tailored.TailoredVerifier.RepSpec.accepts_of_accepts`), so its value is at most that
game's (`MIPRE.quantumValue_le_of_coarse`), which the vendored direct repetition theorem bounds
(`MIPRE.Repetition.quantumValue_repeat_le_soundBound`). The answers of `𝒱_n`'s bipartite game
have length at most `2B` when the input's lengths are at most `B`, and the factor `2` is
absorbed into the constant: `soundBound c ε k (2B) ≤ soundBound (c / 2) ε k B`.
-/

namespace MIPRE

namespace Repetition

/-- The soundness bound grows with the answer length. -/
theorem soundBound_mono {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (k : ℕ) {B B' : ℕ} (hB : B ≤ B') :
    soundBound c ε k B ≤ soundBound c ε k B' := by
  unfold soundBound
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hX : 0 ≤ c * ε ^ 13 * (k : ℝ) := by positivity
  exact div_le_div_of_nonneg_left hX (by positivity) (by exact_mod_cast Nat.add_le_add_right hB 1)

/-- Doubling the answer length halves the constant. -/
theorem soundBound_two_mul {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε) (k B : ℕ) :
    soundBound c ε k (2 * B) ≤ soundBound (c / 2) ε k B := by
  unfold soundBound
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hX : 0 ≤ c * ε ^ 13 * (k : ℝ) := by positivity
  have hB : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  push_cast
  rw [show c / 2 * ε ^ 13 * (k : ℝ) / ((B : ℝ) + 1) = c * ε ^ 13 * (k : ℝ) / (2 * ((B : ℝ) + 1))
    by field_simp]
  exact div_le_div_of_nonneg_left hX (by positivity) (by linarith)

end Repetition

namespace Tailored

open Cost CL

namespace TailoredVerifier

variable {ℓ : ℕ} {V : TailoredVerifier ℓ}

/-- The answers of `𝒱_n`'s bipartite game have length at most `2B` when the answer-length
calculator's outputs are at most `B`. -/
theorem maxLen_le_of_lenBound {n B : ℕ} (hB : LenBound V.len n B) :
    (V.tgame n).maxLen ≤ 2 * B := by
  have hlen : ∀ (x : BitStr) κ, V.lenOf n x κ ≤ B := by
    intro x κ
    unfold lenOf
    split_ifs with h
    · exact hB _ _ _ h.choose_spec
    · exact Nat.zero_le _
  refine Finset.sup_le fun x _ => ?_
  change V.lenOf n _ false + V.lenOf n _ true ≤ 2 * B
  have := hlen (toBits x) false
  have := hlen (toBits x) true
  omega

variable {lam tau : ℕ} {L P : Decider} {n : ℕ}

/-- **The repeated verifier's value is at most that of the direct repetition of `𝒱_n`.** -/
theorem RepSpec.valStar_le_repeat (h : RepSpec V lam tau L P n) :
    (repTV V lam tau L P).valStar n ≤
      quantumValue ((V.tgame n).toGame.repeat (K lam tau n)) := by
  classical
  refine quantumValue_le_of_coarse ((repTV V lam tau L P).tgame n).toGame
    ((V.tgame n).toGame.repeat (K lam tau n)) (qEquiv V lam tau n)
    (fun x a i => ⟨(V.tgame n).coord (qEquiv V lam tau n x) a.1 i, by
      rw [TailoredGame.length_coord]; exact (V.tgame n).len_le_maxLen _⟩)
    (fun x y => repTV_μ x y) (fun x y a b hD => ?_)
  have hacc := h.accepts_of_accepts (of_decide_eq_true hD)
  obtain ⟨-, -, hall⟩ := ((V.tgame n).repeat_accepts_iff _ _ _ _).1 hacc
  exact decide_eq_true fun i => decide_eq_true (hall i)

/-- **Soundness of the repeated verifier**: for an input whose lengths are at most `B`,
`val*(𝒱_n) ≤ 1 - ε` gives `val*(𝒱^rep_n) ≤ exp(-(c/2) ε^13 k(n) / (B + 1))`, with `c` the
constant of the direct repetition theorem for answers of bounded length. -/
theorem RepSpec.valStar_le (h : RepSpec V lam tau L P n) {B : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hB : LenBound V.len n B) (hV : V.valStar n ≤ 1 - ε) :
    (repTV V lam tau L P).valStar n ≤
      Repetition.soundBound (Repetition.repConst / 2) ε (K lam tau n) B := by
  have hc := Repetition.repConst_pos.le
  calc (repTV V lam tau L P).valStar n
      ≤ quantumValue ((V.tgame n).toGame.repeat (K lam tau n)) := h.valStar_le_repeat
    _ ≤ Repetition.soundBound Repetition.repConst ε (K lam tau n) (V.tgame n).maxLen :=
        Repetition.quantumValue_repeat_le_soundBound _ hε hV (Nat.two_pow_pos _)
    _ ≤ Repetition.soundBound Repetition.repConst ε (K lam tau n) (2 * B) :=
        Repetition.soundBound_mono hc hε.le _ (maxLen_le_of_lenBound hB)
    _ ≤ Repetition.soundBound (Repetition.repConst / 2) ε (K lam tau n) B :=
        Repetition.soundBound_two_mul hc hε.le _ _

end TailoredVerifier

end Tailored

end MIPRE

end
