/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.PaddedLIDT
public import MIPRE.Background.QLD.Mirror

@[expose] public section

/-!
# `MirrorSimul`, discharged

`Mirror.lean` introduces `MirrorSimul`: the two cuts of `lem:qld-4-7`, on one state. Everything
`lem:qld-pauli-selfcons` and `lem:qld-swap` say is stated against it, and this file constructs one,
so that whole run of results holds for every legal projective strategy of the Pauli basis test in
the regime, not only for strategies assumed to carry the structure.

The two cuts are two runs of the same construction: `exists_globalPair` at the strategy gives the
first, and `exists_globalPair_swap`, at the strategy with the players exchanged in the model with
the players exchanged, gives the second. Each run's simultaneous pair measurement
(`GlobalPair.toSimulPair`) lives in its padded model, and is carried to the first cut of its
physical model along the embedding `j₁` of the padded model (`SimulPair.transport`); composed with
the inert embedding of the register model, `j₁` is the embedding `ι₁` that `CutSimul` asks for, by
definition. Nothing relates the two runs' measurements, and the structure does not ask that.

## Why there is nothing to check about the states

Both cuts read one physical state by construction. The first cut of the physical model of `M.swap`
is a reading of that physical model, which has the space, the state and the representation of the
physical model of `M`, with the two players' algebras exchanged; the exchange of the two blocks of
registers (`blockSwapIso`, where the symmetry of the pair enters, `physE_symm`) carries every
statement about the one to the other (`Mirror.lean`). So `MirrorSimul` has no field relating the
two cuts' states, and all the two runs must share is the padding size `K`. Each run of stage 4
holds at every padding size beyond a threshold (`exists_globalPair`), so both hold at the larger of
the two thresholds.

What this does **not** do is relate the two cuts' pair measurements. The paper does not either:
`lem:qld-4-7` gives one measurement per player's space, and the chain's endpoint is symmetric in
them for a reason of its own (`swap_mem_coupledIdx`), not because the two measurements are the
same object.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The matrix construction filled
the matrix `MirrorSimul` field by field from the two runs' `SimulPair`s, each on its own
twice-padded state vector `padState`, and proved its field `hmirror` --- the two states, each with
the other cut's pair appended, are one state up to a regrouping --- by computing both states
pointwise (`padState_reindex_apply`, from `extVec2_apply` and the weight `padWeight` of the padding
registers) and swapping a pair's halves (`epr_symm`). Here the strategy is a projective strategy
`S` of a bipartite model `M`, the two runs are `GlobalPair`s of the padded models of `M` and of
`M.swap`, a `MirrorSimul` is the padding size and the two runs' simultaneous pair measurements
transported to the first cut, and the state computation is gone: the two cuts read one physical
model by construction. The seeded soundness theorem enters as the hypothesis `hL` of
`exists_globalPair`, and `4m | q` is derived from the regime (`four_mul_dvd_card_of_regime`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder

/-! ## The two runs, at one padding size -/

section Mirror

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : ℕ} {δ ε : ℝ}

/-- **`MirrorSimul`, discharged.** The two cuts are two runs of the same construction at one
padding size `K`: a `GlobalPair` of the padded model of `M` at the strategy, and one of the padded
model of `M.swap` at the strategy with the players exchanged, which fails with the same probability
(`povmValue_swapped_le`). Each run's simultaneous pair measurement (`GlobalPair.toSimulPair`, of
error `δ_S(q, δ, ε)`) is carried to the first cut of its physical model along `j₁`, which lands on
`ι₁` by definition. Nothing relates the two runs' measurements, and the structure does not ask
that. -/
noncomputable def mirrorOfGlobalPairs
    (P : GlobalPair M S (padModel (Anc F m) F m d M K)
      ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
        norm_basisVec) δ)
    (P' : GlobalPair M.swap (S.swap (qldGame (d := d) hm)) (padModel (Anc F m) F m d M.swap K)
      ((M.swap.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
        norm_basisVec) δ)
    (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    MirrorSimul M S (deltaS (Fintype.card F) δ ε) where
  K := K
  first := (P.toSimulPair hd hfail hq).transport (j₁ (Anc F m) F m d M K)
  second := (P'.toSimulPair hd (povmValue_swapped_le hfail) hq).transport
    (j₁ (Anc F m) F m d M.swap K)

end Mirror

/-! ## `MirrorSimul` exists -/

section Exists

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {hm : m ∣ Fintype.card F}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {M : BipartiteModel 𝒞 𝒜 ℬ} {ε : ℝ}

/-- **`MirrorSimul` exists**: for a legal projective strategy of the Pauli basis test of value
`1 - ε`, if the seeded test is sound in every extension of the model by a unit vector, then inside
the regime `48 m d ≤ q` both cuts' simultaneous pair measurements exist, on one physical state,
with error `δ_S(q, δ_ld, ε)`. Running `lem:qld-global-pvm` twice --- once at the strategy
(`exists_globalPair`) and once at the strategy with the players exchanged
(`exists_globalPair_swap`) --- at the larger of the two padding thresholds gives the two cuts at
one padding size. This is what makes `lem:qld-pauli-selfcons` and everything below it hold for
every such strategy. -/
theorem exists_mirrorSimul
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (S : M.ProjStrat (qldGame (d := d) hm)) (hε : 0 ≤ ε) (hfail : 1 - S.value ≤ ε)
    (hlegA : LegalSupport S.PA) (hlegB : LegalSupport S.PB) (hd : 1 ≤ d)
    (hq : 48 * m * d ≤ Fintype.card F) :
    Nonempty (MirrorSimul M S
      (deltaS (Fintype.card F) (deltaLD (Fintype.card F) m d ε) ε)) := by
  have hm4 : 4 * m ∣ Fintype.card F := four_mul_dvd_card_of_regime hm hd hq
  obtain ⟨K₀, hK₀⟩ := exists_globalPair hL hm4 S hε hfail hlegA hlegB hd
  obtain ⟨K₀', hK₀'⟩ := exists_globalPair_swap hL hm4 S hε hfail hlegA hlegB hd
  obtain ⟨P⟩ := hK₀ (max K₀ K₀') (le_max_left _ _)
  obtain ⟨P'⟩ := hK₀' (max K₀ K₀') (le_max_right _ _)
  exact ⟨mirrorOfGlobalPairs P P' hd hfail hq⟩

end Exists

end MIPRE.QLD

end

end
