/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourcePaddingQueryCorrect
import MIPRE.Foundations.Introspection.AuxiliaryScanCorrect

/-! # The actual bounded source supplies every hiding-scan query

The seven source levels have three-bit indices. The common source clock
therefore covers all matrix and factor queries at every attained prefix.
This instantiates the generic scan interface with the executable padded
source programs, without assuming any source-query oracle.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliarySourceScan
open Cost SourcePadding SourcePadding.Program AuxiliaryProgram

theorem level_size_le {lam n j : ℕ} (hlam : 2 ≤ lam) (hn : 1 ≤ n) (hj : j < 7) :
    Nat.size (j + 1) ≤ (2 ^ n) ^ lam := by
  have hs : Nat.size (j + 1) ≤ 3 := Nat.size_le.mpr (by norm_num; omega)
  have htwo : 2 ≤ 2 ^ n := (two_le_exp_index_iff n).mpr hn
  have hfour : 4 ≤ (2 ^ n) ^ lam := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left htwo 2
      _ ≤ (2 ^ n) ^ lam := Nat.pow_le_pow_right (by omega) hlam
  omega

/-- Any initial context prefix and level are replaced before the queried
stage. Only its fixed source, clock, index and player matter. -/
theorem queriesCorrectAt (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (initialLevel : ℕ) (initial : Fin Q → CL.𝔽₂) (j : ℕ) (hj : j < 7) :
    AuxiliaryScan.QueriesCorrectAt (factorFromContext U) (matrixFromContext U)
      (queryContext V lam n w initialLevel initial)
      (depthFamily (firstEmbedding hQ) (sourceFamily V n) w) j := by
  intro u hu
  have ha : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x := by
    obtain ⟨x, hx⟩ := hu
    exact ⟨x, hx.symm⟩
  have hjR := level_size_le hV.two_le hn hj
  change factorFromContext U (queryContext V lam n w j u) = _ ∧
    matrixFromContext U (queryContext V lam n w j u) = _
  exact ⟨factorFromContext_legal U V hV hn hQ w j hj hjR u ha,
    matrixFromContext_legal U V hV hn hQ w j hj hjR u ha⟩

theorem queriesCorrectBelow (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (initialLevel : ℕ) (initial : Fin Q → CL.𝔽₂) (k : ℕ) (hk : k ≤ 7) :
    ∀ j < k, AuxiliaryScan.QueriesCorrectAt (factorFromContext U) (matrixFromContext U)
      (queryContext V lam n w initialLevel initial)
      (depthFamily (firstEmbedding hQ) (sourceFamily V n) w) j := by
  intro j hj
  exact queriesCorrectAt U V hV hn hQ w initialLevel initial j (by omega)

end MIPRE.Introspection.AuxiliarySourceScan
end
