/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Introspection.CanonicalComplete

@[expose] public section

/-!
# The honest strategy of the introspection verifier, explicitly

The completeness of the introspection compiler `MIPRE.Introspection.seven`
(`CanonicalComplete.output_hasPerfectPCC`) is proved through a chain of existential statements:
the input's strategy is carried to the padded source game (`VerifierSource.padded_hasPerfectPCC`),
the honest binary strategy is built on it and carried back to the canonical coordinates
(`NumberedComplete.exists_perfectPCC_with_format`), its answers are encoded
(`CanonicalComplete.exists_raw_perfectPCC`), and the typed strategy is detyped
(`DeciderProgram.exists_ambientPerfectPCC`). Phase 3c of `planning/aldous-lyons-track.md` needs
the measurement at each question as an explicit formula, so this file restates the chain as
definitions, each the construction the existential statement wraps, with its PCC property and
its value:

* `source`, `padded`: the input's strategy on the source game and on the padded source game;
* `canonical`: the honest strategy of the guarded game at the canonical parameters;
* `raw`: its answers encoded, a strategy of the typed game `rawGame`;
* `honest`: the detyped strategy, of the game `H` whose predicate is `Detyping.accepts` of
  `rawPredicate`.

The input is any perfect PCC strategy of the input verifier's game at index `2^n`.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.HonestChain

open Cost MIPRE.CL MIPRE.Introspection MIPRE.Introspection.CanonicalGame
open MIPRE.Introspection.DecisionCompiler MIPRE.Introspection.SourceCompiler
open MIPRE.Introspection.PauliSamplerParameters

local instance power_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨by have := registerPower_pos c lam n; omega⟩

variable {c : ℕ} (W : Verifier 7) {lam n : ℕ}
  (RW : SyncStrategy (W.game (2 ^ n) ((2 ^ n) ^ lam)).doubled)

/-- The register bound of the input. -/
theorem dim_le (c : ℕ) (hc : 2 ≤ c) (hW : W.IsBounded lam) (hn : 1 ≤ n) :
    W.sampler.dim (2 ^ n) ≤ registerBits c lam n :=
  VerifierSource.dimension_le_registerBits hc W hW hn

/-! ## The input on the source games -/

/-- The input's strategy, on the source game (the same game, presented by its CL family). -/
def source : SyncStrategy (Honest.sourceGame (SourcePadding.Program.sourceFamily W n)
    (VerifierSource.predicate W n ((2 ^ n) ^ lam))).doubled :=
  RW.copy _

theorem source_isPCC (hRW : RW.IsPCC) : (source W RW).IsPCC :=
  SyncStrategy.isPCC_copy hRW _ fun x y => by rw [VerifierSource.sourceGame_eq]

theorem source_value (hv : RW.value = 1) : (source W RW).value = 1 := by
  refine (RW.value_copy _ (fun x y => by rw [VerifierSource.sourceGame_eq])
    (fun x y a b => by rw [VerifierSource.sourceGame_eq])).trans hv

/-- The input's strategy on the padded source game, measuring at the unpadded question. -/
def padded (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n) :
    SyncStrategy (Honest.sourceGame (AuxiliaryDecision.padded W hs)
      (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam))).doubled :=
  (SourcePadding.strategy (AuxiliaryProgram.firstEmbedding hs) (SourcePadding.Program.sourceFamily W n)
    (VerifierSource.predicate W n ((2 ^ n) ^ lam)) (source W RW)).copy _

theorem padded_game_eq (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n) :
    Honest.sourceGame (AuxiliaryDecision.padded W hs)
      (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam)) =
    Honest.sourceGame (SourcePadding.family (AuxiliaryProgram.firstEmbedding hs)
        (SourcePadding.Program.sourceFamily W n))
      (SourcePadding.decider (AuxiliaryProgram.firstEmbedding hs)
        (VerifierSource.predicate W n ((2 ^ n) ^ lam))) :=
  SourcePadding.sourceGame_depthFamily (AuxiliaryProgram.firstEmbedding hs) (SourcePadding.Program.sourceFamily W n)
    (VerifierSource.predicate W n ((2 ^ n) ^ lam)) (by decide)
    (fun w => (W.sampler.cl_exactlyOn _ _).supportedOn)

theorem padded_isPCC (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n) (hRW : RW.IsPCC) :
    (padded W RW hs).IsPCC :=
  SyncStrategy.isPCC_copy (SourcePadding.strategy_isPCC _ _ _ _ (source_isPCC W RW hRW))
    _ fun x y => by rw [padded_game_eq]

theorem padded_value (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n) (hRW : RW.IsPCC)
    (hv : RW.value = 1) : (padded W RW hs).value = 1 :=
  ((SourcePadding.strategy _ _ _ _).value_copy _ (fun x y => by rw [padded_game_eq])
    (fun x y a b => by rw [padded_game_eq])).trans
    (SourcePadding.strategy_value _ _ _ _ (source_isPCC W RW hRW)
      (source_value W RW hv))

/-! ## The honest strategy of the guarded game -/

section Canonical

variable (hc1 : 1 ≤ c) (he : Even c) (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n)

/-- The source family in the binary Weyl coordinates. -/
abbrev family : Bool → CLFun 𝔽₂ (BinaryComplete.Coord (registerPower c lam n) (fieldBits c lam n))
    7 :=
  SourceReindex.family (numbering c lam n) (AuxiliaryDecision.padded W hs)

/-- The source predicate in the binary Weyl coordinates. -/
abbrev decider := SourceReindex.decider (numbering c lam n)
  (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam))

/-- The input's strategy in the binary Weyl coordinates. -/
abbrev reindexed := SourceReindex.strategy (numbering c lam n) (AuxiliaryDecision.padded W hs)
  (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam)) (padded W RW hs)

theorem family_supported (w : Bool) : (family W hs w).SupportedOn Finset.univ := by
  exact ((AuxiliaryDecision.padded_supported W hs w).reindex (numbering c lam n)).mono
    (Finset.subset_univ _)

/-- **The honest binary strategy** (`BinaryComplete.strategy`), at the canonical parameters. -/
abbrev binary :=
  BinaryComplete.strategy (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
    (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)

/-- The honest strategy of the quotient game in the binary Weyl coordinates. -/
abbrev quotient :=
  (BinaryComplete.quotientHonest (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
    (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
    (selector c hc1 lam n) (permutation c lam n)).copy
    (AuxiliaryQuotient.reindexedGame (numbering c lam n) QLD.adj (.pauli .X) (.pauli .Z)
      (QLD.PauliCL.ExplicitSeed.binaryPresentation (selector c hc1 lam n) (basis c he lam n))
      (AuxiliaryDecision.padded W hs) (NumberedComplete.project (d := 1) (numbering c lam n)
        (basis c he lam n))
      (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam))
      (ExplicitGame.pauliCheck (divides c hc1 lam n) (permutation c lam n)
        (basis c he lam n))).doubled

/-- **The honest strategy of the guarded game**, the strategy of
`CanonicalGame.exists_perfectPCC`. -/
def canonical : SyncStrategy (guarded c hc1 he lam n W hs).doubled :=
  (AuxiliaryQuotient.originalPCC (numbering c lam n) QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation (selector c hc1 lam n) (basis c he lam n))
    (AuxiliaryDecision.padded W hs)
    (NumberedComplete.project (d := 1) (numbering c lam n) (basis c he lam n))
    (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam))
    (ExplicitGame.pauliCheck (divides c hc1 lam n) (permutation c lam n) (basis c he lam n))
    (quotient W RW hc1 he hs)).copy _

theorem quotient_game_eq :
    AuxiliaryQuotient.reindexedGame (numbering c lam n) QLD.adj (.pauli .X) (.pauli .Z)
      (QLD.PauliCL.ExplicitSeed.binaryPresentation (selector c hc1 lam n) (basis c he lam n))
      (AuxiliaryDecision.padded W hs) (NumberedComplete.project (d := 1) (numbering c lam n)
        (basis c he lam n))
      (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam))
      (ExplicitGame.pauliCheck (divides c hc1 lam n) (permutation c lam n)
        (basis c he lam n)) =
    BinaryComplete.explicitQuotientGame (d := 1) (family W hs) (decider W hs)
      (divides c hc1 lam n) (basis c he lam n) (selector c hc1 lam n) (permutation c lam n) := by
  have hproj : (fun a : QLD.Answer (field c lam n).carrier (registerPower c lam n) 1 =>
      reindexEquiv (numbering c lam n) (NumberedComplete.project (numbering c lam n)
        (basis c he lam n) a)) = BinaryComplete.project (basis c he lam n) := by
    funext a
    exact (reindexEquiv (numbering c lam n)).apply_symm_apply _
  change AuxiliaryQuotient.game _ _ _ _ _ _ _ _ = _
  rw [hproj]
  rfl

theorem quotient_isPCC (hRW : RW.IsPCC) : (quotient W RW hc1 he hs).IsPCC :=
  SyncStrategy.isPCC_copy
    (BinaryComplete.quotientHonest_isPCC _ _ _ _ _ _ _ _
      (SAT.shoupSelfDualNormalBasis_selfDual _ _ _) (selector_eq c hc1 lam n)
      (SourceReindex.strategy_isPCC _ _ _ _ (padded_isPCC W RW hs hRW))) _
    fun x y => by rw [quotient_game_eq]; rfl

theorem quotient_value (hRW : RW.IsPCC) (hv : RW.value = 1) :
    (quotient W RW hc1 he hs).value = 1 :=
  (SyncStrategy.value_copy _ _ (fun x y => by rw [quotient_game_eq]; rfl)
    (fun x y a b => by rw [quotient_game_eq]; rfl)).trans
    (BinaryComplete.quotientHonest_value _ _ _ _ _ _ _ _
      (SAT.shoupSelfDualNormalBasis_selfDual _ _ _) (selector_eq c hc1 lam n) le_rfl
      (SourceReindex.strategy_isPCC _ _ _ _ (padded_isPCC W RW hs hRW))
      ((SourceReindex.strategy_value _ _ _ _).trans (padded_value W RW hs hRW hv)))

theorem canonical_prefixGuard (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n)))
    (a : CanonicalComplete.Answer c lam n) (ha : (canonical W RW hc1 he hs).P.M q a ≠ 0) :
    PrefixGuard.holds (AuxiliaryDecision.padded W hs) q.2.1 a :=
  AuxiliaryQuotient.originalPCC_prefixGuard (numbering c lam n) QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation (selector c hc1 lam n) (basis c he lam n))
    (AuxiliaryDecision.padded W hs)
    (NumberedComplete.project (d := 1) (numbering c lam n) (basis c he lam n))
    (VerifierSource.paddedPredicate W hs ((2 ^ n) ^ lam))
    (ExplicitGame.pauliCheck (divides c hc1 lam n) (permutation c lam n) (basis c he lam n))
    (quotient W RW hc1 he hs)
    (fun q a ha => BinaryComplete.quotientHonest_prefixGuard (family W hs) (decider W hs)
      (reindexed W RW hs) (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
      (selector c hc1 lam n) (permutation c lam n) q a ha) q a ha

theorem canonical_isPCC (hRW : RW.IsPCC) : (canonical W RW hc1 he hs).IsPCC :=
  PrefixGuard.copied_isPCC _ _ _ _
    (AuxiliaryQuotient.originalPCC_isPCC _ _ _ _ _ _ _ _ _ _ (quotient_isPCC W RW hc1 he hs hRW))

theorem canonical_value (hRW : RW.IsPCC) (hv : RW.value = 1) :
    (canonical W RW hc1 he hs).value = 1 :=
  PrefixGuard.copied_value_eq_one _ _ _ _ (canonical_prefixGuard W RW hc1 he hs)
    ((AuxiliaryQuotient.originalPCC_value _ _ _ _ _ _ _ _ _ _).trans
      (quotient_value W RW hc1 he hs hRW hv))

theorem quotient_introspect (side w : Bool) (payload : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n))
    (a : Verifier.Answers ((2 ^ n) ^ lam))
    (ha : (quotient W RW hc1 he hs).P.M (side, .inr (.introspect, w), payload) (.pair y a) ≠ 0) :
    ∃ x, (family W hs w).eval x = y :=
  BinaryComplete.quotientHonest_introspect (d := 1) (family W hs) (decider W hs)
    (reindexed W RW hs) (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
    (selector c hc1 lam n) (permutation c lam n) side w payload _ a ha

set_option backward.isDefEq.respectTransparency false in
theorem canonical_introspect (side w : Bool) (payload : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (y : Fin (registerBits c lam n) → 𝔽₂) (a : Verifier.Answers ((2 ^ n) ^ lam))
    (ha : (canonical W RW hc1 he hs).P.M (side, .inr (.introspect, w), payload)
      (.pair y a) ≠ 0) :
    ∃ x, (AuxiliaryDecision.padded W hs w).eval x = y := by
  have ha' : (quotient W RW hc1 he hs).P.M (side, .inr (.introspect, w), payload)
      (.pair (reindexEquiv (numbering c lam n) y) a) ≠ 0 := ha
  obtain ⟨x, hx⟩ := quotient_introspect W RW hc1 he hs side w payload _ a ha'
  refine ⟨(reindexEquiv (numbering c lam n)).symm x, ?_⟩
  change ((AuxiliaryDecision.padded W hs w).reindex (numbering c lam n)).eval x =
    reindexEquiv (numbering c lam n) y at hx
  rw [CLFun.eval_reindex'] at hx
  exact (reindexEquiv (numbering c lam n)).injective hx

theorem quotient_pauli_format (side : Bool) (t : QLD.Ty)
    (payload : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (a : QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
    (ha : (quotient W RW hc1 he hs).P.M (side, .inl t, payload) (.pauli a) ≠ 0) :
    (QLD.PauliCL.ExplicitSeed.binaryDecode (permutation c lam n) (basis c he lam n) t
      payload).fmtOk a = true :=
  BinaryComplete.quotientHonest_pauli_format (d := 1) (family W hs) (decider W hs)
    (reindexed W RW hs) (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
    (selector c hc1 lam n) (permutation c lam n) side t payload a ha

theorem canonical_pauli_format (side : Bool) (t : QLD.Ty)
    (payload : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (a : QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
    (ha : (canonical W RW hc1 he hs).P.M (side, .inl t, payload) (.pauli a) ≠ 0) :
    (QLD.PauliCL.ExplicitSeed.binaryDecode (permutation c lam n) (basis c he lam n) t
      payload).fmtOk a = true := by
  have ha' : (quotient W RW hc1 he hs).P.M (side, .inl t, payload) (.pauli a) ≠ 0 := ha
  exact quotient_pauli_format W RW hc1 he hs side t payload a ha'

end Canonical

/-! ## The encoded and detyped strategies -/

section Raw

variable (hc : 2 ≤ c) (he : Even c) (U : ClockedUniversalMachine) (hW : W.IsBounded lam)
  (hn : 1 ≤ n)

theorem one_le_c (hc : 2 ≤ c) : 1 ≤ c := by omega

/-- **The honest strategy of the typed game**: the honest strategy of the guarded game, its
answers encoded as bit strings (`CanonicalComplete.encodeAnswer`). -/
def raw : SyncStrategy (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled :=
  (canonical W RW (one_le_c hc) he (dim_le W c hc hW hn)).mergeAnswersByQuestion
    (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled
    fun _ a => CanonicalComplete.encodeAnswer c hc lam n a

theorem raw_isPCC (hRW : RW.IsPCC) : (raw W RW hc he U hW hn).IsPCC :=
  SyncStrategy.isPCC_mergeAnswersByQuestion _ _ _ (fun _ _ => rfl)
    (canonical_isPCC W RW _ he _ hRW)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem raw_value (hRW : RW.IsPCC) (hv : RW.value = 1) : (raw W RW hc he U hW hn).value = 1 := by
  have hc1 := one_le_c hc
  have hs := dim_le W c hc hW hn
  unfold raw
  refine SyncStrategy.perfect_mergeAnswersByQuestion
    (canonical W RW (one_le_c hc) he (dim_le W c hc hW hn))
    (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled
    (fun _ a => CanonicalComplete.encodeAnswer c hc lam n a) (fun _ _ => rfl) ?_
    (canonical_value W RW _ he _ hRW hv)
  intro q r a b _ ha hb hd
  have hfa := CanonicalComplete.pauliFormatted_of_support c hc1 he lam n W hs _
    (canonical_pauli_format W RW hc1 he hs) q a ha
  have hfb := CanonicalComplete.pauliFormatted_of_support c hc1 he lam n W hs _
    (canonical_pauli_format W RW hc1 he hs) r b hb
  have hsa := CanonicalComplete.sourceOutput_of_support c hc1 he lam n W hs _
    (canonical_introspect W RW hc1 he hs) q a ha
  have hsb := CanonicalComplete.sourceOutput_of_support c hc1 he lam n W hs _
    (canonical_introspect W RW hc1 he hs) r b hb
  rw [Game.doubled_D] at hd ⊢
  split_ifs at hd ⊢ with hside
  · have hacc := (PrefixGuard.game_accepts_iff (AuxiliaryDecision.padded W hs)
      Prod.fst (CanonicalGame.quotient c hc1 he lam n W hs) q.2 r.2 a b).mp hd
    exact CanonicalComplete.encoded_accepts c hc he U W hW hn hs q.2 r.2 a b hfa hfb
      hacc.1 hacc.2.1 hsa hsb hacc.2.2

/-- The constant answer off the decodable views. -/
def answer₀ : Verifier.Answers (outerBound c lam n) := ⟨[], by simp⟩

/-- **The honest strategy of the detyped game** `H` of the introspection verifier
(`Detyping.complete` of `raw`, the constant answer `[]` off the decodable views). -/
def honest : SyncStrategy (Detyping.game graph
    (CL.Detyping.DeciderProgram.sourceFamily (extendedSampler c (one_le_c hc) he lam) n)
    (rawPredicate c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n)).doubled :=
  Detyping.complete graph (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (CL.Detyping.DeciderProgram.sourceFamily (extendedSampler c (one_le_c hc) he lam) n)
    (rawPredicate c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n)
    (raw W RW hc he U hW hn) answer₀

theorem honest_isPCC (hRW : RW.IsPCC) : (honest W RW hc he U hW hn).IsPCC :=
  Detyping.complete_isPCC _ (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z)) _ _
    (fun w t => (extendedSampler c (one_le_c hc) he lam).cl_exactlyOn n (Player.ofBool w) t)
    (by decide) _ _ (raw_isPCC W RW hc he U hW hn hRW) _

theorem honest_value (hRW : RW.IsPCC) (hv : RW.value = 1) :
    (honest W RW hc he U hW hn).value = 1 :=
  Detyping.complete_value _ (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z)) _ _
    (fun w t => (extendedSampler c (one_le_c hc) he lam).cl_exactlyOn n (Player.ofBool w) t)
    (by decide) _ _ (raw_value W RW hc he U hW hn hRW hv) _

end Raw

end MIPRE.Tailored.Intro.HonestChain

end
