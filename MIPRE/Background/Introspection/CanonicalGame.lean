/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.PauliSamplerTotal
import MIPRE.Background.Introspection.NumberedComplete
import MIPRE.Foundations.Introspection.VerifierSourceGame

/-! # The finite game at the compiler's canonical parameters

These definitions use the executable field, basis, selector, and register
numbering. The original answers retain their bounded finite alphabet.
-/

noncomputable section
namespace MIPRE.Introspection.CanonicalGame
open CL SourceCompiler PauliSamplerParameters QLD.PauliCL.ExplicitSeed

local instance power_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨by have := registerPower_pos c lam n; omega⟩

abbrev field (c lam n : ℕ) := SAT.shoupBinField (fieldBits c lam n) (fieldBits_pos c lam n)

abbrev basis (c : ℕ) (he : Even c) (lam n : ℕ) :=
  SAT.shoupSelfDualNormalBasis (fieldBits c lam n) (fieldBits_pos c lam n) (fieldBits_odd he lam n)

abbrev selector (c : ℕ) (hc : 1 ≤ c) (lam n : ℕ) :=
  SeedProgram.selector (field c lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits hc lam n)

abbrev permutation (c lam n : ℕ) := seedPermutation (field c lam n)

theorem divides (c : ℕ) (hc : 1 ≤ c) (lam n : ℕ) :
    registerPower c lam n ∣ Fintype.card (field c lam n).carrier :=
  dyadic_divides (field c lam n) (selectorBits c lam n) (selectorBits_le_fieldBits hc lam n)

theorem selector_eq (c : ℕ) (hc : 1 ≤ c) (lam n : ℕ) (s : (field c lam n).carrier) :
    LIDT.CL.chi (divides c hc lam n) (permutation c lam n s) = selector c hc lam n s :=
  chi_seedPermutation (field c lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits hc lam n) (divides c hc lam n) s

abbrev numbering (c lam n : ℕ) :=
  (QLD.PauliFullAnswerProgram.registerNumbering (registerPower c lam n) (fieldBits c lam n)).symm

abbrev quotient (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ)
    (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n) :=
  NumberedComplete.game (d := 1) (numbering c lam n) (AuxiliaryDecision.padded V hs)
    (VerifierSource.paddedPredicate V hs ((2^n)^lam)) (divides c hc lam n)
    (basis c he lam n) (selector c hc lam n) (permutation c lam n)

abbrev guarded (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ)
    (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n) :=
  PrefixGuard.game (AuxiliaryDecision.padded V hs) Prod.fst (quotient c hc he lam n V hs)

/-- The finite honest strategy has every support certificate used by the
executable prefix and source-output guards. -/
theorem exists_perfectPCC (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ)
    (V : Verifier 7) (hs : V.sampler.dim (2^n) ≤ registerBits c lam n)
    (hV : V.HasPerfectPCC (2^n) ((2^n)^lam)) :
    ∃ S : SyncStrategy (guarded c hc he lam n V hs).doubled,
      S.IsPCC ∧ S.value = 1 ∧
      (∀ q a, S.P.M q a ≠ 0 → PrefixGuard.holds (AuxiliaryDecision.padded V hs) q.2.1 a) ∧
      (∀ side w payload y a,
        S.P.M (side,.inr (.introspect,w),payload) (.pair y a) ≠ 0 →
        ∃ x, (AuxiliaryDecision.padded V hs w).eval x = y) ∧
      (∀ side t payload a,
        S.P.M (side,.inl t,payload) (.pauli a) ≠ 0 →
        (binaryDecode (permutation c lam n) (basis c he lam n) t payload).fmtOk a = true) := by
  obtain ⟨R,hR,hv⟩ := VerifierSource.padded_hasPerfectPCC V hs hV
  obtain ⟨S,hS,hvS,_,hg,hi,hp⟩ := NumberedComplete.exists_perfectPCC_with_format (d := 1)
    (numbering c lam n) (AuxiliaryDecision.padded V hs)
    (VerifierSource.paddedPredicate V hs ((2^n)^lam)) (divides c hc lam n)
    (basis c he lam n) (selector c hc lam n) (permutation c lam n) R
    (SAT.shoupSelfDualNormalBasis_selfDual _ _ _) (selector_eq c hc lam n)
    (by decide) (AuxiliaryDecision.padded_supported V hs) hR hv
  exact ⟨S,hS,hvS,hg,hi,hp⟩

end MIPRE.Introspection.CanonicalGame
