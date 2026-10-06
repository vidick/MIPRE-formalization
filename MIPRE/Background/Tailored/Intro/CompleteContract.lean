/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Output
public import MIPRE.Background.Tailored.Intro.HonestZPC

@[expose] public section

/-!
# Completeness of the output tailored verifier, in the contract's form

Phase 3c of `planning/aldous-lyons-track.md` (issue #281), the counterpart of
`Output.soundness_contract`. For a `λ`-bounded tailored verifier `T` with a perfect ZPC strategy
at index `2^n`, whose normal form verifier `T.ofTNFVT U0` is `Cλ`-bounded (`C ≥ 2`), the output
tailored verifier at `Cλ` has a perfect ZPC strategy at index `n` as soon as its programs meet
the specification `IntroSpec`.

The strategy is the honest strategy of the reference verifier's typed game
(`HonestChain.honest_zpc_ofTNFVT`), which meets the three conditions of
`Complete.hasPerfectZPC_tpresented`; `Output.hasPerfectZPC_outTV` carries it to the output. The
input's answers fit the cutoff `(2^n)^(Cλ)` by the length bound of a `λ`-bounded verifier
(`Output.maxLen_le_of_isBounded`).
-/

namespace MIPRE.Tailored.Intro.Output

open Cost CL MIPRE.SAT MIPRE.Introspection MIPRE.QLD SourceCompiler PauliSamplerParameters
open DecisionCompiler CL.Detyping.DeciderProgram

/-- **Completeness of the output, in the contract's form**: for a `λ`-bounded input `T` with a
perfect ZPC strategy at index `2^n`, whose normal form verifier is `Cλ`-bounded (`C ≥ 2`), when
the output's programs meet the specification at `Cλ`, the output's `n`-th game has a perfect
ZPC strategy. -/
theorem completeness_contract (T : TailoredVerifier 7) (U0 : UniversalMachine) {C lam n : ℕ}
    (hC : 2 ≤ C) (hl : 1 ≤ lam) (hn : 1 ≤ n) (hT : T.IsBounded lam)
    (hV : (T.ofTNFVT U0).IsBounded (C * lam))
    {hs : (T.ofTNFVT U0).sampler.dim (2 ^ n) ≤ registerBits sevenConstant (C * lam) n}
    {kg : ∀ S : Finset (Fin (registerBits sevenConstant (C * lam) n)), CL.RegLinear 𝔽₂ S →
      List (Fin (registerBits sevenConstant (C * lam) n) → 𝔽₂)} {L P : Decider}
    (hkg : KerGens (registerBits sevenConstant (C * lam) n) kg)
    {hl' : 1 ≤ C * lam}
    (h : IntroSpec sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
      selfClockedUniversal (T.ofTNFVT U0) hl' hn
      (presented graph (Sound.H sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
        (C * lam) n selfClockedUniversal (T.ofTNFVT U0))
        (Sound.tdata sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 (C * lam) n T
          (T.ofTNFVT U0) hs kg)) L P)
    (hZ : T.HasPerfectZPC (2 ^ n)) :
    (outTV sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 (C * lam)
      L P).HasPerfectZPC n := by
  have hm : 2 ≤ 2 ^ n := (two_le_exp_index_iff n).mpr hn
  have hlen : (T.tgame (2 ^ n)).maxLen ≤ (2 ^ n) ^ (C * lam) :=
    (maxLen_le_of_isBounded hT hm).trans (Nat.pow_le_pow_right (by omega) (by nlinarith))
  obtain ⟨R, hR, hval, hsupp, hperm, hdiag⟩ :=
    HonestChain.honest_zpc_ofTNFVT sevenConstant sevenConstant_spec.1 sevenConstant_spec.2.1
      selfClockedUniversal T U0 (C * lam) n hV hn hlen hZ
  exact hasPerfectZPC_outTV T sevenConstant_spec.1 hkg (acceptsAsInput_ofTNFVT T U0 n) hV h
    R hR hval hsupp hperm hdiag

end MIPRE.Tailored.Intro.Output

end
