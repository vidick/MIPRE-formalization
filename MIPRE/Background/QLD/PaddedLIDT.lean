/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.PaddedValue
public import MIPRE.Background.QLD.Simul
public import MIPRE.Background.QLD.Dummy
public import MIPRE.Background.QLD.Products
public import MIPRE.Background.QLD.Linear
public import MIPRE.Background.QLD.Separate
public import MIPRE.Background.QLD.Complete
public import MIPRE.Background.QLD.Regime

@[expose] public section

/-!
# The global polynomial measurements: applying the seeded soundness theorem

`lem:qld-global-pvm`. By `lem:qld-global-success` (`padStrat_value`), the padded strategy
`(padStrat hm hm4 S.projA, padStrat hm hm4 S.projB)` wins the seeded low individual degree test at
`(q, 4m, d, 1)` in the expanded model `M.reg (Anc F m)` with probability at least `1 - δ_GS`, where
`δ_GS = 5 m² δ_P(ε, md/q + 1/q) + 4 δ_Q(ε) + (md + 1)/q`. This file feeds it to the seeded
soundness theorem and reads the conclusion back in the form stages 4b and 4c consume.

## The dilation, and where the soundness theorem is applied

The padded strategy is a pair of families of POVMs (its point answers are sandwich combinations,
its line answers averages of pasted measurements), and the soundness theorem is about projective
strategies. So each player's family is Halmos-dilated (`exists_pvm_dilation_ge`) on the padding
register `PadAnc F m d K`, both at one common size `K` (`exists_padDilation`): the dilated families
are a projective strategy `D` of the padded model `padModel (Anc F m) F m d M K`, the register
model extended by each player's padding register in the product vector `|t₀⟩ ⊗ |t₀⟩`
(`MIPRE/Background/QLD/PhysModel.lean`), whose reference entries are the padded strategy's. A Born
probability of the padded model is the Born probability of the reference entries
(`BipartiteModel.bornProb_expand_basisVec`), so `D` has the padded strategy's value
(`BipartiteModel.povmValue_expand_basisVec`).

The soundness theorem enters as a hypothesis `hL` on the model: the seeded test is sound
(`LIDT.Simul.SoundIn`) in every extension `M.expand e` of `M` by a unit vector. The padded model is
such an extension up to associativity, so the test is sound in it (`soundIn_padModel`), and it is
applied to `D` at one codeword (`r = 1`). Its conclusion is read back along
`Fin 1 → F ≃ F` (`BipartiteModel.inconsistency_map_equiv`), and the dilated point measurements are
replaced by the padded point measurements extended by the identity on the padding register (their
pushforward along the inert embedding of the register model): both have the padded point
measurement as reference entry, so every inconsistency on the padded model is the same
(`BipartiteModel.inconsistency_expand_basisVec_congr`). The final form, `exists_globalPair`,
mentions no dilation.

## The interface `GlobalPair`

A `GlobalPair M S K ι δ` is the output of the lemma in any model `K` into which the register model
embeds along `ι` (`BipartiteModel.Embedding`): two projective low-degree measurements `GA`, `GB`
in `K`'s algebras, consistent with the opposite party's padded point measurements carried along
`ι`, and with each other. Stages 4b and 4c are theorems about a `GlobalPair`, and every expectation
of an operator carried along `ι` is its expectation in the register model, so the conclusions of
stages 2 and 3 transfer. `exists_globalPair` gives one at `K = padModel …`, `ι` the inert embedding,
for every padding size beyond a threshold, so that the two runs of stage 4 (at `S` and at the
strategy with the players exchanged) can share one padding size. `GlobalPair.toSimulPair` builds
the interface `SimulPair` in the same model, with no reindexing.

## The error

`δ_ld = deltaLD q m d ε = deltaSim q (4m) d 1 (deltaGS q m d ε)`: the seeded soundness theorem's
error at `(q, 4m, d, 1)`, one codeword, for a strategy of value `1 - δ_GS`. It is of the
blueprint's displayed form `A (md)^A ((δ_GS)^b + q^{-b} + 2^{-bmd})`, since
`(4md)^A = 4^A (md)^A` and `2^{-4bmd} ≤ 2^{-bmd}`.

The recovered polynomials live on `F^{4m}`, while the point measurements read only the `2m + 2`
coordinates `xBlk`, `zBlk`, `alph`, `bet`. The Schwartz--Zippel argument that the polynomials
mostly do not read the remaining dummy coordinates is `MIPRE/Background/QLD/Dummy.lean`;
`GlobalPair.sum_bad_mass_A_le` is `lem:qld-global-dummy` for the measurements produced here.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The matrix proof applied the
vendored seeded soundness theorem through `LIDT/Adapter/Registers.lean`, which Naimark-dilated the
padded POVM strategy on an answer ancilla, packaged it on `Fin (card)` and read the conclusion back
on the twice-padded state vector `padState ψ` along `Matrix.reindex`. Here the soundness theorem is
the hypothesis `hL`, the dilation is the Halmos dilation in the players' algebras, the twice-padded
state is the padded model `padModel` (with no `F × F` register: stage 3's joint measurement is
internal to the padded strategy), its compressions are the two-sided compression at
`|t₀⟩ ⊗ |t₀⟩`, the doubly extended operators of the matrix statements are operators carried along
an embedding (`liftOp`, `liftPt`), the swapped padded state is the model `K.swap`, and
`GlobalPair` is generic in its model, so that `toSimulPair` needs no register transport.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder

/-! ## The error -/

/-- **`δ_ld`**: the seeded soundness theorem's error at `(q, 4m, d, 1)`, at one codeword, for a
strategy of value `1 - δ_GS`. -/
def deltaLD (q m d : ℕ) (ε : ℝ) : ℝ := LIDT.Simul.deltaSim q (4 * m) d 1 (deltaGS q m d ε)

/-! ## The expanded point measurements, carried to another model -/

section Lift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {R R' : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R] [Ring R'] [StarRing R'] [Algebra ℂ R']

/-- A party's expanded point measurement, carried to another algebra along a `⋆`-homomorphism
(the first or the second player's map of an embedding): the matrix proof's double extension by the
identity. -/
def liftOp (f : Matrix (Anc F m) (Anc F m) R →⋆ₙₐ[ℂ] R')
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) (a : F) : R' :=
  f (hatMats P W u a)

theorem isPVM_liftOp {f : Matrix (Anc F m) (Anc F m) R →⋆ₙₐ[ℂ] R'} (hf : f 1 = 1)
    {P : Question F m → POVMIn (Answer F m d) R} (hP : ∀ q, IsPVMIn (P q).op) (W : Bas)
    (u : Point F m) : IsPVMIn (liftOp f P W u) :=
  (isPVM_hatMats hP W u).pushforward hf

/-- The sandwich combination of the carried measurements is the carried padded point
measurement. -/
theorem sandComb_liftOp (f : Matrix (Anc F m) (Anc F m) R →⋆ₙₐ[ℂ] R')
    (P : Question F m → POVMIn (Answer F m d) R) (u : Point F (4 * m)) (c : F) :
    sandComb (liftOp f P .X) (liftOp f P .Z) u c
      = f (ptComb (sand (hatMats P .X (xBlk u)) (hatMats P .Z (zBlk u))) (alph u) (bet u) c) := by
  simp only [sandComb, ptComb, sand, liftOp, map_sum, map_mul]

theorem comm_liftOp (f : Matrix (Anc F m) (Anc F m) R →⋆ₙₐ[ℂ] R')
    (P : Question F m → POVMIn (Answer F m d) R) (x z : Point F m) (p : F × F) :
    comm (liftOp f P .X x) (liftOp f P .Z z) p = f (hatComm P x z p.1 p.2) := by
  simp only [comm, liftOp, hatComm, map_sub, map_mul]

variable [PartialOrder R'] [StarOrderedRing R']

/-- The padded point measurement, carried to another algebra along a unital `⋆`-homomorphism: the
expanded sandwich combination, carried. -/
theorem padPt_aOp_mats (f : Matrix (Anc F m) (Anc F m) R →⋆ₙₐ[ℂ] R') (hf : f 1 = 1)
    {S : Question F m → POVMIn (Answer F m d) R} (hS : ∀ q, IsPVMIn (S q).op)
    (u : Point F (4 * m)) (a : F) :
    ((padPt hS u).pushforward f hf).op a
      = f (ptComb (sand (hatMats S .X (xBlk u)) (hatMats S .Z (zBlk u))) (alph u) (bet u) a) := by
  rw [POVMIn.pushforward_op, padPt_mats]

/-- The opposite party's expanded point measurement, carried to another algebra along a unital
`⋆`-homomorphism. -/
def liftPt (f : Matrix (Anc F m) (Anc F m) R →⋆ₙₐ[ℂ] R') (hf : f 1 = 1)
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) : POVMIn F R' :=
  (hatPtPOVM P W u).pushforward f hf

theorem liftPt_mats (f : Matrix (Anc F m) (Anc F m) R →⋆ₙₐ[ℂ] R') (hf : f 1 = 1)
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) (a : F) :
    (liftPt f hf P W u).op a = liftOp f P W u a := rfl

end Lift

/-! ## The commutator weights of the two strategies, carried to another model -/

section Comm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {hm : m ∣ Fintype.card F}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
variable {M : BipartiteModel 𝒞 𝒜 ℬ} {PA : Question F m → POVMIn (Answer F m d) 𝒜}
  {PB : Question F m → POVMIn (Answer F m d) ℬ} {ε : ℝ} {K : BipartiteModel 𝒞' 𝒜' ℬ'}

omit [StarModule ℂ 𝒜] [StarProper 𝒜] in
/-- Bob's commutator weight, from `lem:qld-combined-points`, carried along an embedding of the
register model. -/
theorem sum_comm_liftOp_B_le (hM : ‖M.ψ‖ = 1) (hPB : ∀ q, IsPVMIn (PB q).op)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (ι : (M.reg (Anc F m)).Embedding K) :
    ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z) * ∑ p : F × F,
        K.swap.stateSqNorm (comm (liftOp ι.ΦB PB .X x) (liftOp ι.ΦB PB .Z z) p)
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le_B (PA := PA) hM hPB hfail
  rw [sum_content_blocks (fun x z => ∑ p : F × F,
    (M.reg (Anc F m)).swap.stateSqNorm (hatComm PB x z p.1 p.2))] at h
  simpa only [comm_liftOp, ι.swap_stateSqNorm] using h

omit [StarModule ℂ ℬ] [StarProper ℬ] in
/-- Alice's commutator weight, carried along an embedding of the register model. -/
theorem sum_comm_liftOp_A_le (hM : ‖M.ψ‖ = 1) (hPA : ∀ q, IsPVMIn (PA q).op)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (ι : (M.reg (Anc F m)).Embedding K) :
    ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z) * ∑ p : F × F,
        K.stateSqNorm (comm (liftOp ι.ΦA PA .X x) (liftOp ι.ΦA PA .Z z) p)
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le (PB := PB) hM hPA hfail
  rw [sum_content_blocks (fun x z => ∑ p : F × F,
    (M.reg (Anc F m)).stateSqNorm (hatComm PA x z p.1 p.2))] at h
  simpa only [comm_liftOp, ι.stateSqNorm] using h

end Comm

/-! ## The output of the lemma, as a structure -/

section Global

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']

/-- **The output of `lem:qld-global-pvm`, as a structure**, for a projective strategy `S` of the
Pauli basis test in a bipartite model `M`, in a model `K` into which the expanded model
`M.reg (Anc F m)` embeds along `ι`: two projective low-degree measurements in `K`'s algebras, the
two point consistencies against the opposite party's padded point measurements carried along `ι`,
and their mutual consistency, all with error `δ`. Stages 4b and 4c are theorems about a
`GlobalPair`. -/
structure GlobalPair {hm : m ∣ Fintype.card F} (M : BipartiteModel 𝒞 𝒜 ℬ)
    (S : M.ProjStrat (qldGame (d := d) hm)) (K : BipartiteModel 𝒞' 𝒜' ℬ')
    (ι : (M.reg (Anc F m)).Embedding K) (δ : ℝ) where
  /-- Alice's global measurement. -/
  GA : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) 𝒜'
  /-- Bob's global measurement. -/
  GB : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d)) ℬ'
  GA_proj : IsPVMIn GA.op
  GB_proj : IsPVMIn GB.op
  /-- Alice's padded points against Bob's evaluated global measurement. -/
  consA : K.inconsistency (uniform (Point F (4 * m)))
    (fun u => (padPt S.projA u).pushforward ι.ΦA ι.ΦA_one) (evalPOVMIn GB) ≤ δ
  /-- Alice's evaluated global measurement against Bob's padded points. -/
  consB : K.inconsistency (uniform (Point F (4 * m))) (evalPOVMIn GA)
    (fun u => (padPt S.projB u).pushforward ι.ΦB ι.ΦB_one) ≤ δ
  /-- The two global measurements against each other. -/
  consAB : K.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB) ≤ δ

/-- The state of the model of a `GlobalPair` is a unit vector, the strategy's being one. -/
theorem GlobalPair.ψ_unit {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
    {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
    {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ} (_P : GlobalPair M S K ι δ) : ‖K.ψ‖ = 1 := by
  rw [ι.norm_ψ]
  exact hatVec_unit S.ψ_unit

end Global

/-! ## The lemma -/

section Exists

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {hm : m ∣ Fintype.card F}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {M : BipartiteModel 𝒞 𝒜 ℬ} {ε : ℝ}

/-- **The Halmos dilation of the padded strategy**, both players at one padding size: for every
padding size beyond a threshold, a projective strategy of the padded model for the seeded test
whose reference entries are the padded strategy's. -/
theorem exists_padDilation (hm4 : 4 * m ∣ Fintype.card F) (S : M.ProjStrat (qldGame (d := d) hm)) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K →
      ∃ D : (padModel (Anc F m) F m d M K).ProjStrat (CL.clGame (d := d) (ldc := 1) hm4),
        (∀ y a, (D.PA y).op a t₀ t₀ = (padStrat hm hm4 S.projA y).op a)
          ∧ ∀ y b, (D.PB y).op b t₀ t₀ = (padStrat hm hm4 S.projB y).op b := by
  obtain ⟨KA, hKA⟩ :=
    exists_pvm_dilation_ge (padStrat hm hm4 S.projA) (ansZero : CL.Answer F (4 * m) d 1)
  obtain ⟨KB, hKB⟩ :=
    exists_pvm_dilation_ge (padStrat hm hm4 S.projB) (ansZero : CL.Answer F (4 * m) d 1)
  refine ⟨max KA KB, fun K hK => ?_⟩
  obtain ⟨QA, hQA, hQA0⟩ := hKA K (le_of_max_le_left hK)
  obtain ⟨QB, hQB, hQB0⟩ := hKB K (le_of_max_le_right hK)
  exact ⟨⟨fun y => (hQA y).toPOVMIn, fun y => (hQB y).toPOVMIn, hQA, hQB,
    ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
      norm_basisVec).norm_ψ.trans (hatVec_unit S.ψ_unit)⟩, hQA0, hQB0⟩

/-- **`lem:qld-global-pvm`, as the soundness theorem returns it.** For a legal projective strategy
of the Pauli basis test of value `1 - ε`, if the seeded test is sound in every extension of the
model by a unit vector: for every padding size beyond a threshold, a projective dilation `D` of the
padded strategy in the padded model, whose point measurements have the padded point measurements
as reference entries, and projective low-degree measurements `GA`, `GB` in the padded model's
algebras, with the two point-consistency estimates against `D` and the full-polynomial
consistency, all with error `δ_ld`. -/
theorem exists_global_pvm
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (hm4 : 4 * m ∣ Fintype.card F) (S : M.ProjStrat (qldGame (d := d) hm)) (hε : 0 ≤ ε)
    (hfail : 1 - S.value ≤ ε) (hlegA : LegalSupport S.PA) (hlegB : LegalSupport S.PB)
    (hd : 1 ≤ d) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K →
      ∃ (D : (padModel (Anc F m) F m d M K).ProjStrat (CL.clGame (d := d) (ldc := 1) hm4))
        (GA : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadAnc F m d K) (PadAnc F m d K) (Matrix (Anc F m) (Anc F m) 𝒜)))
        (GB : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadAnc F m d K) (PadAnc F m d K) (Matrix (Anc F m) (Anc F m) ℬ))),
        (∀ u a, ((D.PA (.point u)).map CL.Answer.toValue).op a t₀ t₀ = (padPt S.projA u).op a)
        ∧ (∀ u b, ((D.PB (.point u)).map CL.Answer.toValue).op b t₀ t₀ = (padPt S.projB u).op b)
        ∧ IsPVMIn GA.op ∧ IsPVMIn GB.op
        ∧ (padModel (Anc F m) F m d M K).inconsistency (uniform (Point F (4 * m)))
            (fun u => (D.PA (.point u)).map CL.Answer.toValue) (evalPOVMIn GB)
            ≤ deltaLD (Fintype.card F) m d ε
        ∧ (padModel (Anc F m) F m d M K).inconsistency (uniform (Point F (4 * m)))
            (evalPOVMIn GA) (fun u => (D.PB (.point u)).map CL.Answer.toValue)
            ≤ deltaLD (Fintype.card F) m d ε
        ∧ (padModel (Anc F m) F m d M K).inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
            ≤ deltaLD (Fintype.card F) m d ε := by
  obtain ⟨K₀, hK₀⟩ := exists_padDilation hm4 S
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨D, hDA, hDB⟩ := hK₀ K hK
  -- the dilated strategy has the padded strategy's value
  have hval : 1 - deltaGS (Fintype.card F) m d ε ≤ D.value :=
    (padStrat_value hm hm4 S.ψ_unit hfail S.projA S.projB hε hlegA hlegB hd).trans_eq
      ((M.reg (Anc F m)).povmValue_expand_basisVec t₀ t₀ _ D.PA D.PB _ _ hDA hDB).symm
  -- the soundness of the seeded test in the padded model, at one codeword
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow (F := F)
  obtain ⟨GA, GB, hGA, hGB, h1, h2, h3⟩ :=
    soundIn_padModel (I := Anc F m) (F := F) (m := m) (d := d) hL K hk hm4 hd le_rfl D
      (deltaGS (Fintype.card F) m d ε) (deltaGS_nonneg hε) hval
  -- the reading of a one-codeword tuple
  have hval1 : ∀ a : CL.Answer F (4 * m) d 1,
      Equiv.funUnique (Fin 1) F (LIDT.Simul.valsOf a) = CL.Answer.toValue a := by
    intro a
    cases a <;> rfl
  have hptA : ∀ u, (LIDT.Simul.tuplePOVMAIn hm4 D u).map (Equiv.funUnique (Fin 1) F)
      = (D.PA (.point u)).map CL.Answer.toValue := fun u => by
    rw [LIDT.Simul.tuplePOVMAIn, POVMIn.map_map]
    simp only [hval1]
  have hptB : ∀ u, (LIDT.Simul.tuplePOVMBIn hm4 D u).map (Equiv.funUnique (Fin 1) F)
      = (D.PB (.point u)).map CL.Answer.toValue := fun u => by
    rw [LIDT.Simul.tuplePOVMBIn, POVMIn.map_map]
    simp only [hval1]
  have hevA : ∀ u, (LIDT.Simul.evalTuplePOVMIn GA u).map (Equiv.funUnique (Fin 1) F)
      = evalPOVMIn (GA.map (Equiv.funUnique (Fin 1) _)) u := fun u => by
    rw [LIDT.Simul.evalTuplePOVMIn, evalPOVMIn, POVMIn.map_map, POVMIn.map_map]
    rfl
  have hevB : ∀ u, (LIDT.Simul.evalTuplePOVMIn GB u).map (Equiv.funUnique (Fin 1) F)
      = evalPOVMIn (GB.map (Equiv.funUnique (Fin 1) _)) u := fun u => by
    rw [LIDT.Simul.evalTuplePOVMIn, evalPOVMIn, POVMIn.map_map, POVMIn.map_map]
    rfl
  refine ⟨D, GA.map (Equiv.funUnique (Fin 1) _), GB.map (Equiv.funUnique (Fin 1) _),
    fun u a => ?_, fun u b => ?_, POVMIn.isPVMIn_map hGA _, POVMIn.isPVMIn_map hGB _, ?_, ?_, ?_⟩
  · rw [POVMIn.map_op, Matrix.sum_apply]
    simp only [hDA]
    rw [← padStrat_point_map_toValue hm hm4 S.projA u, POVMIn.map_op]
  · rw [POVMIn.map_op, Matrix.sum_apply]
    simp only [hDB]
    rw [← padStrat_point_map_toValue hm hm4 S.projB u, POVMIn.map_op]
  · have h := (BipartiteModel.inconsistency_map_equiv _ (Equiv.funUnique (Fin 1) F) _
      (LIDT.Simul.tuplePOVMAIn hm4 D) (LIDT.Simul.evalTuplePOVMIn GB)).trans_le h1
    simp only [hptA, hevB] at h
    exact h
  · have h := (BipartiteModel.inconsistency_map_equiv _ (Equiv.funUnique (Fin 1) F) _
      (LIDT.Simul.evalTuplePOVMIn GA) (LIDT.Simul.tuplePOVMBIn hm4 D)).trans_le h2
    simp only [hptB, hevA] at h
    exact h
  · exact (BipartiteModel.inconsistency_map_equiv _ (Equiv.funUnique (Fin 1) _) _
      (fun _ => GA) (fun _ => GB)).trans_le h3

/-- **`lem:qld-global-pvm`, with the dilation's point measurements replaced.** As
`exists_global_pvm`, with the consistencies against the padded point measurements extended by the
identity on the padding register (carried along the inert embedding of the register model into the
padded model): no dilation appears in the statement. -/
theorem exists_global_pvm_hat
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (hm4 : 4 * m ∣ Fintype.card F) (S : M.ProjStrat (qldGame (d := d) hm)) (hε : 0 ≤ ε)
    (hfail : 1 - S.value ≤ ε) (hlegA : LegalSupport S.PA) (hlegB : LegalSupport S.PB)
    (hd : 1 ≤ d) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K →
      ∃ (GA : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadAnc F m d K) (PadAnc F m d K) (Matrix (Anc F m) (Anc F m) 𝒜)))
        (GB : POVMIn (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadAnc F m d K) (PadAnc F m d K) (Matrix (Anc F m) (Anc F m) ℬ))),
        IsPVMIn GA.op ∧ IsPVMIn GB.op
        ∧ (padModel (Anc F m) F m d M K).inconsistency (uniform (Point F (4 * m)))
            (fun u => (padPt S.projA u).pushforward
              ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
                norm_basisVec).ΦA
              ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
                norm_basisVec).ΦA_one)
            (evalPOVMIn GB) ≤ deltaLD (Fintype.card F) m d ε
        ∧ (padModel (Anc F m) F m d M K).inconsistency (uniform (Point F (4 * m)))
            (evalPOVMIn GA)
            (fun u => (padPt S.projB u).pushforward
              ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
                norm_basisVec).ΦB
              ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
                norm_basisVec).ΦB_one)
            ≤ deltaLD (Fintype.card F) m d ε
        ∧ (padModel (Anc F m) F m d M K).inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
            ≤ deltaLD (Fintype.card F) m d ε := by
  obtain ⟨K₀, hK₀⟩ := exists_global_pvm hL hm4 S hε hfail hlegA hlegB hd
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨D, GA, GB, hDA, hDB, hGA, hGB, h1, h2, h3⟩ := hK₀ K hK
  refine ⟨GA, GB, hGA, hGB, ?_, ?_, h3⟩
  · refine le_of_eq_of_le ((M.reg (Anc F m)).inconsistency_expand_basisVec_congr t₀ t₀ _
      (fun u a => ?_) (fun u b => rfl)) h1
    rw [POVMIn.pushforward_op, BipartiteModel.inertEmb_ΦA, diagonal_apply_eq, hDA u a]
  · refine le_of_eq_of_le ((M.reg (Anc F m)).inconsistency_expand_basisVec_congr t₀ t₀ _
      (fun u a => rfl) (fun u b => ?_)) h2
    rw [POVMIn.pushforward_op, BipartiteModel.inertEmb_ΦB, diagonal_apply_eq, hDB u b]

/-- **`lem:qld-global-pvm`**, packaged: for a legal projective strategy of value `1 - ε`, if the
seeded test is sound in every extension of the model by a unit vector, then for every padding size
beyond a threshold the padded model has a `GlobalPair` with error `δ_ld`, along the inert embedding
of the register model. The threshold lets the two runs of stage 4 share one padding size. -/
theorem exists_globalPair
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (hm4 : 4 * m ∣ Fintype.card F) (S : M.ProjStrat (qldGame (d := d) hm)) (hε : 0 ≤ ε)
    (hfail : 1 - S.value ≤ ε) (hlegA : LegalSupport S.PA) (hlegB : LegalSupport S.PB)
    (hd : 1 ≤ d) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → Nonempty (GlobalPair M S (padModel (Anc F m) F m d M K)
      ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
        norm_basisVec)
      (deltaLD (Fintype.card F) m d ε)) := by
  obtain ⟨K₀, hK₀⟩ := exists_global_pvm_hat hL hm4 S hε hfail hlegA hlegB hd
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨GA, GB, hGA, hGB, h1, h2, h3⟩ := hK₀ K hK
  exact ⟨⟨GA, GB, hGA, hGB, h1, h2, h3⟩⟩

/-- **`lem:qld-global-pvm` for the strategy with the players exchanged**: `exists_globalPair` for
`S.swap` in the model `M.swap`, from the soundness of the seeded test in the extensions of `M`
(the test is symmetric in the players, `LIDT.Simul.soundIn_swap_expand_of_norm`). This is the
second run of stage 4; with `exists_globalPair` it gives both runs at any common padding size
beyond the two thresholds. -/
theorem exists_globalPair_swap
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (hm4 : 4 * m ∣ Fintype.card F) (S : M.ProjStrat (qldGame (d := d) hm)) (hε : 0 ≤ ε)
    (hfail : 1 - S.value ≤ ε) (hlegA : LegalSupport S.PA) (hlegB : LegalSupport S.PB)
    (hd : 1 ≤ d) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → Nonempty (GlobalPair M.swap (S.swap (qldGame (d := d) hm))
      (padModel (Anc F m) F m d M.swap K)
      ((M.swap.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
        norm_basisVec)
      (deltaLD (Fintype.card F) m d ε)) :=
  exists_globalPair (M := M.swap) (fun e he => LIDT.Simul.soundIn_swap_expand_of_norm hL e he) hm4
    (S.swap (qldGame (d := d) hm)) hε (povmValue_swapped_le hfail) hlegB hlegA hd

end Exists

/-! ## Stage 4b, on a `GlobalPair` -/

namespace GlobalPair

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ} (P : GlobalPair M S K ι δ) {ε : ℝ}

/-- **`lem:qld-global-dummy` for Alice's global measurement**: under `16 m d ≤ q`, the outcomes
that read a dummy coordinate weigh at most `4δ`. -/
theorem sum_bad_mass_A_le (hq : 16 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ WIndep g), K.bornProb (P.GA.op g) 1 ≤ 4 * δ :=
  sum_bad_mass_le_of_le P.ψ_unit P.GA (fun u => (padPt S.projB u).pushforward ι.ΦB ι.ΦB_one)
    (fun u u' => by simp only [padPt_mix]) P.consB hq

/-- **`lem:qld-global-dummy` for Bob's global measurement.** -/
theorem sum_bad_mass_B_le (hq : 16 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ WIndep g), K.bornProb 1 (P.GB.op g) ≤ 4 * δ := by
  have h1 := P.consA
  rw [← BipartiteModel.inconsistency_swap] at h1
  have := sum_bad_mass_le_of_le (K := K.swap) P.ψ_unit P.GB
    (fun u => (padPt S.projA u).pushforward ι.ΦA ι.ΦA_one) (fun u u' => by simp only [padPt_mix])
    h1 hq
  simpa only [BipartiteModel.bornProb_swap] using this

/-- Alice's global measurement is consistent with the sandwich combination of Bob's carried point
measurements: the form `lem:qld-global-products` consumes. -/
theorem cons_sandComb_A :
    1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.bornProb (P.GA.op g)
      (sandComb (liftOp ι.ΦB S.PB .X) (liftOp ι.ΦB S.PB .Z) u (g.eval u)) := by
  have h := P.consB
  rw [inconsistency_evalPOVM_eq _ (sum_uniform_eq_one _) P.ψ_unit] at h
  have hmats : ∀ (u : Point F (4 * m)) (c : F),
      ((padPt S.projB u).pushforward ι.ΦB ι.ΦB_one).op c
        = sandComb (liftOp ι.ΦB S.PB .X) (liftOp ι.ΦB S.PB .Z) u c := fun u c => by
    rw [padPt_aOp_mats, sandComb_liftOp]
  simp only [hmats] at h
  linarith

/-- Bob's version, in the model with the players exchanged. -/
theorem cons_sandComb_B :
    1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.swap.bornProb (P.GB.op g)
      (sandComb (liftOp ι.ΦA S.PA .X) (liftOp ι.ΦA S.PA .Z) u (g.eval u)) := by
  have h := P.consA
  rw [← BipartiteModel.inconsistency_swap,
    inconsistency_evalPOVM_eq (K := K.swap) _ (sum_uniform_eq_one _) P.ψ_unit] at h
  have hmats : ∀ (u : Point F (4 * m)) (c : F),
      ((padPt S.projA u).pushforward ι.ΦA ι.ΦA_one).op c
        = sandComb (liftOp ι.ΦA S.PA .X) (liftOp ι.ΦA S.PA .Z) u c := fun u c => by
    rw [padPt_aOp_mats, sandComb_liftOp]
  simp only [hmats] at h
  linarith

/-- **`lem:qld-global-products`, Alice's measurement against Bob's `Z_b X_a`.** -/
theorem products_ZX_A (hfail : 1 - S.value ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm (K.πA (P.GA.op g)
        * K.πB (1 - ordComb ordZX (liftOp ι.ΦB S.PB .X) (liftOp ι.ΦB S.PB .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordZX_le P.ψ_unit P.GA P.GA_proj (isPVM_liftOp ι.ΦB_one S.projB .X)
    (isPVM_liftOp ι.ΦB_one S.projB .Z) P.cons_sandComb_A
    (sum_comm_liftOp_B_le S.ψ_unit S.projB hfail ι)

/-- **`lem:qld-global-products`, Alice's measurement against Bob's `X_a Z_b`.** -/
theorem products_XZ_A (hfail : 1 - S.value ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.snorm (K.πA (P.GA.op g)
        * K.πB (1 - ordComb ordXZ (liftOp ι.ΦB S.PB .X) (liftOp ι.ΦB S.PB .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordXZ_le P.ψ_unit P.GA P.GA_proj (isPVM_liftOp ι.ΦB_one S.projB .X)
    (isPVM_liftOp ι.ΦB_one S.projB .Z) P.cons_sandComb_A
    (sum_comm_liftOp_B_le S.ψ_unit S.projB hfail ι)

/-- **`lem:qld-global-products`, Bob's measurement against Alice's `Z_b X_a`**, in the model with
the players exchanged. -/
theorem products_ZX_B (hfail : 1 - S.value ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.swap.snorm (K.swap.πA (P.GB.op g)
        * K.swap.πB (1 - ordComb ordZX (liftOp ι.ΦA S.PA .X) (liftOp ι.ΦA S.PA .Z) u
          (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordZX_le (K := K.swap) P.ψ_unit P.GB P.GB_proj (isPVM_liftOp ι.ΦA_one S.projA .X)
    (isPVM_liftOp ι.ΦA_one S.projA .Z) P.cons_sandComb_B
    (sum_comm_liftOp_A_le S.ψ_unit S.projA hfail ι)

/-- **`lem:qld-global-products`, Bob's measurement against Alice's `X_a Z_b`.** -/
theorem products_XZ_B (hfail : 1 - S.value ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, K.swap.snorm (K.swap.πA (P.GB.op g)
        * K.swap.πB (1 - ordComb ordXZ (liftOp ι.ΦA S.PA .X) (liftOp ι.ΦA S.PA .Z) u
          (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordXZ_le (K := K.swap) P.ψ_unit P.GB P.GB_proj (isPVM_liftOp ι.ΦA_one S.projA .X)
    (isPVM_liftOp ι.ΦA_one S.projA .Z) P.cons_sandComb_B
    (sum_comm_liftOp_A_le S.ψ_unit S.projA hfail ι)

/-- **`lem:qld-global-linear` for Alice's global measurement**: the outcomes that are not linear
in the combining coordinates `(α, β)` weigh at most `2Δ / (1 - 2η)`, where
`Δ = 2δ + 2 · 57676416 ε` is the `X_a Z_b` products bound and `η = (1 + 2d + 4md)/q`. -/
theorem sum_bad_linear_mass_A_le (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε) :
    (1 - 2 * ((1 + 2 * d + 4 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g), K.bornProb (P.GA.op g) 1
      ≤ 2 * (2 * δ + 2 * (57676416 * ε)) :=
  sum_bad_linear_mass_le hd K P.GA P.GA_proj (isPVM_liftOp ι.ΦB_one S.projB .X)
    (isPVM_liftOp ι.ΦB_one S.projB .Z) (P.products_XZ_A hfail)

/-- **`lem:qld-global-linear` for Bob's global measurement.** -/
theorem sum_bad_linear_mass_B_le (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε) :
    (1 - 2 * ((1 + 2 * d + 4 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsLinAB g), K.bornProb 1 (P.GB.op g)
      ≤ 2 * (2 * δ + 2 * (57676416 * ε)) := by
  have h := sum_bad_linear_mass_le hd K.swap P.GB P.GB_proj (isPVM_liftOp ι.ΦA_one S.projA .X)
    (isPVM_liftOp ι.ΦA_one S.projA .Z) (P.products_XZ_B hfail)
  simpa only [BipartiteModel.bornProb_swap] using h

/-- **`lem:qld-global-separate` for Alice's global measurement**: the outcomes that are not of the
form `α g_X(x) + β g_Z(z)` weigh at most `4Δ / (1 - 2η)`, where `Δ = 2δ + 2 · 57676416 ε` is the
bound of `lem:qld-global-products` for either order and `η = (2 + 2d + 8md)/q`. -/
theorem sum_not_isGood_mass_A_le (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε) :
    (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (P.GA.op g) 1
      ≤ 4 * (2 * δ + 2 * (57676416 * ε)) := by
  have h := sum_not_isGood_mass_le hd K P.GA P.GA_proj (isPVM_liftOp ι.ΦB_one S.projB .X)
    (isPVM_liftOp ι.ΦB_one S.projB .Z) (P.products_XZ_A hfail) (P.products_ZX_A hfail)
  linarith

/-- **`lem:qld-global-separate` for Bob's global measurement.** -/
theorem sum_not_isGood_mass_B_le (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε) :
    (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb 1 (P.GB.op g)
      ≤ 4 * (2 * δ + 2 * (57676416 * ε)) := by
  have h := sum_not_isGood_mass_le hd K.swap P.GB P.GB_proj (isPVM_liftOp ι.ΦA_one S.projA .X)
    (isPVM_liftOp ι.ΦA_one S.projA .Z) (P.products_XZ_B hfail) (P.products_ZX_B hfail)
  simp only [BipartiteModel.bornProb_swap] at h
  linarith

end GlobalPair

/-! ## The errors of stage 4c -/

/-- **`Δ`**, the ordered-products bound of `lem:qld-global-products` for a `GlobalPair` of error
`δ` on a strategy of failure `ε`: `2 δ + 2 κ` with `κ = 57676416 ε`. -/
def deltaProd (δ ε : ℝ) : ℝ := 2 * δ + 2 * (57676416 * ε)

/-- **`δ_G`**, the weight of the outcomes that are not of the separated form
`α g_X(x) + β g_Z(z)`: `8 Δ`, from `lem:qld-global-separate` under `48 m d ≤ q`. -/
def deltaSep (δ ε : ℝ) : ℝ := 8 * deltaProd δ ε

/-- **`δ_S`**, the error of `lem:qld-simultaneous`: the marginal estimate
`2 √Δ + 2/q + δ_G`. -/
noncomputable def deltaS (q : ℕ) (δ ε : ℝ) : ℝ :=
  2 * Real.sqrt (deltaProd δ ε) + 2 / q + deltaSep δ ε

namespace GlobalPair

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ} (P : GlobalPair M S K ι δ) {ε : ℝ}

omit [DecidableEq F] [Algebra (ZMod 2) F] in
/-- Under `48 m d ≤ q` the factor `1 - 2η` of `lem:qld-global-separate` is at least `1/2`. -/
theorem one_sub_two_eta_ge (hd : 1 ≤ d) (hq : 48 * m * d ≤ Fintype.card F) :
    (1 : ℝ) / 2 ≤ 1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F) := by
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos
  have hqc : (48 : ℝ) * m * d ≤ Fintype.card F := by exact_mod_cast hq
  have hkey : ((2 : ℝ) + 2 * d + 8 * m * d) / Fintype.card F ≤ 1 / 4 := by
    rw [div_le_iff₀ hq0]
    nlinarith
  linarith

/-- **`lem:qld-global-separate`, solved for the weight**: under `48 m d ≤ q` the outcomes of
Alice's global measurement that are not of the separated form weigh at most `δ_G`. -/
theorem sum_not_isGood_mass_A_le' (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε)
    (hq : 48 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (P.GA.op g) 1 ≤ deltaSep δ ε := by
  have h := P.sum_not_isGood_mass_A_le hd hfail
  have h2 := one_sub_two_eta_ge (F := F) (m := m) (d := d) hd hq
  have h0 : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb (P.GA.op g) 1 :=
    Finset.sum_nonneg fun g _ => K.bornProb_nonneg (P.GA_proj.nonneg g) zero_le_one
  rw [deltaSep, deltaProd]
  nlinarith

/-- **`lem:qld-global-separate`, solved for the weight**, for Bob's global measurement, in the
model with the players exchanged. -/
theorem sum_not_isGood_mass_B_le' (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε)
    (hq : 48 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.swap.bornProb (P.GB.op g) 1 ≤ deltaSep δ ε := by
  have h := P.sum_not_isGood_mass_B_le hd hfail
  simp only [BipartiteModel.bornProb_swap]
  have h2 := one_sub_two_eta_ge (F := F) (m := m) (d := d) hd hq
  have h0 : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ IsGood g), K.bornProb 1 (P.GB.op g) :=
    Finset.sum_nonneg fun g _ => K.bornProb_nonneg zero_le_one (P.GB_proj.nonneg g)
  rw [deltaSep, deltaProd]
  nlinarith

/-! ## The evaluated marginals of the completed pair measurement -/

/-- **`lem:qld-global-sandwich` for Alice's completed pair measurement**: its evaluated `W`
marginal is consistent with Bob's expanded `(Point, W)` measurement carried along `ι`, with error
`δ_S`. -/
theorem inconsistency_evalMarg_A_le (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε)
    (hq : 48 * m * d ≤ Fintype.card F) (W : Bas) :
    K.inconsistency (uniform (Point F m)) (fun u => evalMarg (pairMeas hd P.GA) W u)
        (fun u => liftPt ι.ΦB ι.ΦB_one S.PB W u)
      ≤ deltaS (Fintype.card F) δ ε := by
  have hbad := P.sum_not_isGood_mass_A_le' hd hfail hq
  cases W with
  | X =>
      refine inconsistency_evalMarg_X_le hd P.ψ_unit P.GA P.GA_proj
        (isPVM_liftOp ι.ΦB_one S.projB .X) (isPVM_liftOp ι.ΦB_one S.projB .Z)
        (fun u => liftPt ι.ΦB ι.ΦB_one S.PB .X u)
        (fun u a => liftPt_mats ι.ΦB ι.ΦB_one S.PB .X u a) ?_ hbad
      rw [deltaProd]
      exact P.products_ZX_A hfail
  | Z =>
      refine inconsistency_evalMarg_Z_le hd P.ψ_unit P.GA P.GA_proj
        (isPVM_liftOp ι.ΦB_one S.projB .X) (isPVM_liftOp ι.ΦB_one S.projB .Z)
        (fun u => liftPt ι.ΦB ι.ΦB_one S.PB .Z u)
        (fun u a => liftPt_mats ι.ΦB ι.ΦB_one S.PB .Z u a) ?_ hbad
      rw [deltaProd]
      exact P.products_XZ_A hfail

/-- **`lem:qld-global-sandwich` for Bob's completed pair measurement**, read in the model with the
players exchanged. -/
theorem inconsistency_evalMarg_B_le (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε)
    (hq : 48 * m * d ≤ Fintype.card F) (W : Bas) :
    K.inconsistency (uniform (Point F m)) (fun u => liftPt ι.ΦA ι.ΦA_one S.PA W u)
        (fun u => evalMarg (pairMeas hd P.GB) W u)
      ≤ deltaS (Fintype.card F) δ ε := by
  have hbad := P.sum_not_isGood_mass_B_le' hd hfail hq
  rw [← BipartiteModel.inconsistency_swap]
  cases W with
  | X =>
      refine inconsistency_evalMarg_X_le hd (K := K.swap) P.ψ_unit P.GB P.GB_proj
        (isPVM_liftOp ι.ΦA_one S.projA .X) (isPVM_liftOp ι.ΦA_one S.projA .Z)
        (fun u => liftPt ι.ΦA ι.ΦA_one S.PA .X u)
        (fun u a => liftPt_mats ι.ΦA ι.ΦA_one S.PA .X u a) ?_ hbad
      rw [deltaProd]
      exact P.products_ZX_B hfail
  | Z =>
      refine inconsistency_evalMarg_Z_le hd (K := K.swap) P.ψ_unit P.GB P.GB_proj
        (isPVM_liftOp ι.ΦA_one S.projA .X) (isPVM_liftOp ι.ΦA_one S.projA .Z)
        (fun u => liftPt ι.ΦA ι.ΦA_one S.PA .Z u)
        (fun u a => liftPt_mats ι.ΦA ι.ΦA_one S.PA .Z u a) ?_ hbad
      rw [deltaProd]
      exact P.products_XZ_B hfail

/-! ## The interface instance -/

/-- **`lem:qld-simultaneous`**: the completed pair measurements of a `GlobalPair` are a
`SimulPair` in the same model, along the same embedding, of error `δ_S = 2 √Δ + 2/q + δ_G`. -/
noncomputable def toSimulPair (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε)
    (hq : 48 * m * d ≤ Fintype.card F) : SimulPair M S K ι (deltaS (Fintype.card F) δ ε) where
  SA := pairMeas hd P.GA
  SA_proj := isPVM_pairMeas hd P.GA_proj
  SB := pairMeas hd P.GB
  SB_proj := isPVM_pairMeas hd P.GB_proj
  consA W := P.inconsistency_evalMarg_A_le hd hfail hq W
  consB W := P.inconsistency_evalMarg_B_le hd hfail hq W

@[simp]
theorem toSimulPair_SA (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε)
    (hq : 48 * m * d ≤ Fintype.card F) : (P.toSimulPair hd hfail hq).SA = pairMeas hd P.GA := rfl

@[simp]
theorem toSimulPair_SB (hd : 1 ≤ d) (hfail : 1 - S.value ≤ ε)
    (hq : 48 * m * d ≤ Fintype.card F) : (P.toSimulPair hd hfail hq).SB = pairMeas hd P.GB := rfl

end GlobalPair

/-! ## `lem:qld-simultaneous`, from the strategy -/

section ExistsSimul

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {hm : m ∣ Fintype.card F}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {M : BipartiteModel 𝒞 𝒜 ℬ} {ε : ℝ}

/-- **`lem:qld-simultaneous`**: for a legal projective strategy of the Pauli basis test of value
`1 - ε`, if the seeded test is sound in every extension of the model by a unit vector, then inside
the regime `48 m d ≤ q`, for every padding size beyond a threshold, the padded model has a
simultaneous pair measurement with error `δ_S(q, δ_ld, ε) = 2 √Δ + 2/q + 8 Δ`,
`Δ = 2 δ_ld + 2 · 57676416 ε`. -/
theorem exists_simulPair
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (M.expand e))
    (S : M.ProjStrat (qldGame (d := d) hm)) (hε : 0 ≤ ε) (hfail : 1 - S.value ≤ ε)
    (hlegA : LegalSupport S.PA) (hlegB : LegalSupport S.PB) (hd : 1 ≤ d)
    (hq : 48 * m * d ≤ Fintype.card F) :
    ∃ K₀ : ℕ, ∀ K, K₀ ≤ K → Nonempty (SimulPair M S (padModel (Anc F m) F m d M K)
      ((M.reg (Anc F m)).inertEmb (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))
        norm_basisVec)
      (deltaS (Fintype.card F) (deltaLD (Fintype.card F) m d ε) ε)) := by
  obtain ⟨K₀, hK₀⟩ := exists_globalPair hL (four_mul_dvd_card_of_regime hm hd hq) S hε hfail
    hlegA hlegB hd
  exact ⟨K₀, fun K hK => (hK₀ K hK).map fun P => P.toSimulPair hd hfail hq⟩

end ExistsSimul

end MIPRE.QLD

end

end
