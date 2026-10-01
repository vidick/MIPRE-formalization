/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.ChainProbe

@[expose] public section

/-!
# The second cut, and why it is a second `SimulPair`

`lem:qld-pauli-selfcons` and `lem:qld-swap` both compare *Alice's* exact Pauli object with *Bob's*.
Everything merged so far builds Alice's, from `SimulPair.SA`. This file supplies Bob's.

## Why `SB` is not it

The paper's `lem:qld-4-7` gives a pair measurement `S-hat` on `A A'` **and** one on `B B'`, with

* `(S-hat_{[eval_u = a]})_{A A'} ~ (M-hat^{(Point,W),u}_a)_{B A''}`,
* `(S-hat_{[eval_u = a]})_{B B'} ~ (M-hat^{(Point,W),u}_a)_{A B''}`,

and it is the second that Bob's swap unitary `V_B` conjugates by, because `V_B` acts on `B B' B''`.
`SimulPair.SB` is an operator of the second player of the first cut, whose registers are
`(A'', (B'', (Eb, B')))`, and its consistency is with Alice's expanded measurements carried along
the embedding of the register model, whose second half `A''` is the half of the pair that the
register model `M.reg (Anc F m)` gives Bob. So `SB` sits on `B A''`: it is the second party of the
*first* cut, a legitimate object (it is the symmetric equivalent `M-hat_{A A'} ~ S-hat_{B A''}` of
the first display) but not the one `V_B` is built from.

## What it is instead

`qld-commutation.tex` (`sec:expanding`, "Partitioning the registers, and symmetries") partitions
the six registers two ways --- `A A'` against `B A''`, and `B B'` against `A B''` --- and records
that every bipartite relation derived for one holds for the other with the registers changed. The
second partition is therefore not data of a new kind: it is the same kind as the first, so **the
mirror of a `SimulPair` is a `SimulPair`** --- at the exchanged players and the exchanged strategy,
over the other reading of one physical state.

`MirrorSimul` is that pair of readings, `first` and `second`. Every lemma already proved about
`SimulPair` and `CutSimul` --- `mTildeAnc`, `swapA`, `swapU_conj_mTildeAnc`,
`inconsistency_mTilde_pauli_le_of_win` --- then applies to Bob by instantiating it at `second`,
with no mirror lemma to prove. That is the whole point of the shape.

## The state, and where the second pair is

Both cuts read the **physical model** `phys (Anc F m) F m d M K`
(`MIPRE/Background/QLD/PhysModel.lean`): the strategy's model with each player's physical
registers, `(A'', (Ea, A'))` and `(B'', (Eb, B'))`, in the state that holds both pairs and the two
padding registers. The first cut `cut1 … M K` is a reading of its state model that hands `A''` to
Bob; the second cut is the first cut of the model with the players exchanged, `cut1 … M.swap K`, a
reading of the same state model --- the physical model of `M.swap` has the physical model's space,
state and representation, with the two players' algebras exchanged and the first player's
registers on the first block. So the two cuts read one state by construction, and the exchange of
the blocks of registers (`blockSwapIso`) carries every statement about the physical model of
`M.swap` to the physical model with the players exchanged.

`mTildeAnc`, which puts its Pauli register outermost, followed by `compHom`, lands on Alice's
**physical** registers `(A'', (Ea, A'))` with nothing to reindex --- and `second`'s lands on
Bob's, `(B'', (Eb, B'))`: `aliceMTilde` and `bobMTilde` are operators of the two players of the
physical model, so their cross-party deviation `selfConsGap` is well formed. It is not well formed
for any two objects built inside one `SimulPair`, which is the concrete reason both cuts are needed
at once.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The matrix structure carried
each cut's state on an explicit product of index sets (`Φ` and `Φ'`, with their padding types
`Ea`, `Eb`), the two cuts' data field by field, and a field `hmirror` saying that the two states,
each with the other cut's pair appended, are one state up to a regrouping (`mirrorVec`); the
appending and the regroupings onto the physical grouping were explicit (`sndExtVec`,
`sndPairEquiv`, `pairSwapVec`). Here the physical model holds both pairs and each cut is a reading
of it, so a `MirrorSimul` is the padding size `K` and the two pair measurements on the first cut
(`CutSimul`), of `M` at `S` and of `M.swap` at `S.swap`; it has no field saying that they read one
state, and the mirror exchanges them definitionally (`M.swap.swap` is `M` and the exchange of a
projective strategy is an involution, both by `rfl`). Bob's objects are `compHom` of the second
cut's, elements of the second player's algebra of `phys M K` as they stand, and a statement about
them proved on the physical model of `M.swap` reads on `phys M K` along `blockSwapIso`
(`phys_swap_bornProb`, `phys_swap_snorm_sum_mul`, `phys_swap_inconsistency`, ...).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The exchange of the blocks, as transfers

The physical model of the model with the players exchanged is the physical model with the players
exchanged, by the unitary exchanging the two blocks of registers (`blockSwapIso`), which is the
identity on the players' algebras. So an operator of the first player of `phys N.swap K` is an
operator of the second player of `phys N K`, and every quantity computed from the state is carried
over with the players exchanged. These are the transfers by which Bob's statements, proved at the
second cut, read on the physical model. -/

section BlockSwap

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {I : Type*} [Fintype I] [DecidableEq I] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {m d : ℕ} {N : BipartiteModel 𝒞 𝒜 ℬ} {K : ℕ}

/-- **A Born probability of the physical model of the exchanged players** is the Born probability
of the physical model with the two operators exchanged. -/
theorem phys_swap_bornProb (Y : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ)
    (X : Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜) :
    (phys I F m d N.swap K).bornProb Y X = (phys I F m d N K).bornProb X Y := by
  rw [← (blockSwapIso I F m d N K).bornProb_eq, blockSwapIso_ΦA, blockSwapIso_ΦB,
    BipartiteModel.bornProb_swap]

/-- **The first player's state norms of the physical model of the exchanged players** are the
second player's of the physical model. -/
theorem phys_swap_stateSqNorm (Y : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ) :
    (phys I F m d N.swap K).stateSqNorm Y = (phys I F m d N K).swap.stateSqNorm Y := by
  rw [← (blockSwapIso I F m d N K).stateSqNorm_eq, blockSwapIso_ΦA]

/-- **The second player's state norms of the physical model of the exchanged players** are the
first player's of the physical model. -/
theorem phys_swap_swap_stateSqNorm (X : Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜) :
    (phys I F m d N.swap K).swap.stateSqNorm X = (phys I F m d N K).stateSqNorm X := by
  rw [← (blockSwapIso I F m d N K).swap_stateSqNorm_eq, blockSwapIso_ΦB]
  rfl

/-- **The cross norms of the physical model of the exchanged players** are those of the physical
model, with the two operators exchanged. -/
theorem phys_swap_xSqNorm (Y : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ)
    (X : Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜) :
    (phys I F m d N.swap K).xSqNorm Y X = (phys I F m d N K).xSqNorm X Y := by
  rw [← (blockSwapIso I F m d N K).xSqNorm_eq, blockSwapIso_ΦA, blockSwapIso_ΦB,
    BipartiteModel.xSqNorm_swap]

/-- **A sum of products of the two players' operators of the physical model of the exchanged
players keeps its state norm** on the physical model, each product's factors exchanged. -/
theorem phys_swap_snorm_sum_mul {κ : Type*} (s : Finset κ)
    (Y : κ → Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ)
    (X : κ → Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜) :
    (phys I F m d N.swap K).snorm
        (∑ i ∈ s, (phys I F m d N.swap K).πA (Y i) * (phys I F m d N.swap K).πB (X i))
      = (phys I F m d N K).snorm
        (∑ i ∈ s, (phys I F m d N K).πA (X i) * (phys I F m d N K).πB (Y i)) := by
  have h := (blockSwapIso I F m d N K).toLocalIsometry.snorm_sum_mul_of_W_ψ
    (blockSwapIso I F m d N K).W_ψ s Y X
  rw [← h]
  show (phys I F m d N K).snorm
      (∑ i ∈ s, (phys I F m d N K).πB (Y i) * (phys I F m d N K).πA (X i)) = _
  exact congrArg (phys I F m d N K).snorm
    (Finset.sum_congr rfl fun i _ => ((phys I F m d N K).commute (X i) (Y i)).symm.eq)

/-- **The quadratic form of a sum of products of the two players' operators** is carried over in
the same way. -/
theorem phys_swap_qform_sum_mul {κ : Type*} (s : Finset κ)
    (Y : κ → Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ)
    (X : κ → Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜) :
    (phys I F m d N.swap K).qform
        (∑ i ∈ s, (phys I F m d N.swap K).πA (Y i) * (phys I F m d N.swap K).πB (X i))
      = (phys I F m d N K).qform
        (∑ i ∈ s, (phys I F m d N K).πA (X i) * (phys I F m d N K).πB (Y i)) := by
  have h := (blockSwapIso I F m d N K).toLocalIsometry.qform_sum_mul_of_W_ψ
    (blockSwapIso I F m d N K).W_ψ s Y X
  rw [← h]
  show (phys I F m d N K).qform
      (∑ i ∈ s, (phys I F m d N K).πB (Y i) * (phys I F m d N K).πA (X i)) = _
  exact congrArg (phys I F m d N K).qform
    (Finset.sum_congr rfl fun i _ => ((phys I F m d N K).commute (X i) (Y i)).symm.eq)

/-- **The inconsistency of two families of the physical model of the exchanged players** is that
of the physical model, with the two families exchanged. -/
theorem phys_swap_inconsistency [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ] {Λ X : Type*} [Fintype Λ]
    [DecidableEq Λ] [Fintype X] (μ : X → ℝ)
    (P : X → POVMIn Λ (Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ))
    (Q : X → POVMIn Λ (Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜)) :
    (phys I F m d N.swap K).inconsistency μ P Q = (phys I F m d N K).inconsistency μ Q P := by
  rw [← (blockSwapIso I F m d N K).inconsistency_eq μ (P' := P) (Q' := Q) (fun _ _ => rfl)
    (fun _ _ => rfl), BipartiteModel.inconsistency_swap]

end BlockSwap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]

/-- **One physical state, read along both of the paper's cuts.**

For a projective strategy `S` of the Pauli basis test in a bipartite model `M`, with error `δ`: a
size `K` of the padding registers, common to the two cuts, and two simultaneous pair measurements,
one on the first cut of the physical state, `A A' Ea | B A'' Eb (B' B'')`, and one on the first cut
of the physical state of the model with the players exchanged at the exchanged strategy, which is
the paper's second cut `B B' Eb | A B'' Ea (A' A'')`. The second is the first with the players
exchanged, which is what `sec:expanding`'s symmetry paragraph licenses; both read the physical
model `phys (Anc F m) F m d M K`, so no field says that they read one state. -/
structure MirrorSimul {hm : m ∣ Fintype.card F} (M : BipartiteModel 𝒞 𝒜 ℬ)
    (S : M.ProjStrat (qldGame (d := d) hm)) (δ : ℝ) where
  /-- The size of the padding registers `Ea` and `Eb`, common to the two cuts. -/
  K : ℕ
  /-- **The first cut**: Alice's pair measurement, on `(Ea, A')` --- exactly the data stages
  4a--4c deliver. -/
  first : CutSimul M S K δ
  /-- **The second cut**, the first cut at the exchanged players and strategy: Bob's pair
  measurement, on `(Eb, B')` --- the one `V_B` is built from. Its `SA` is Bob's, so every
  construction made from `SimulPair.SA` --- `mTildeAnc` and `swapA` above all --- is Bob's when
  instantiated here. -/
  second : CutSimul M.swap (S.swap (qldGame (d := d) hm)) K δ

namespace MirrorSimul

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ}

variable (Mi : MirrorSimul M S δ)

/-- **The mirror of a `MirrorSimul` is a `MirrorSimul`**, at the exchanged players and strategy,
with the two cuts exchanged. `first` and `second` give Bob's objects as a `SimulPair`, which is
enough for everything stated on one cut; this gives Bob's objects as the first player's of a
`MirrorSimul`, so every lemma about the physical model becomes Bob's by instantiating here, with
no mirror lemma to prove --- the same economy `second` buys one level down. It is definitional:
`M.swap.swap` is `M` and the exchange of a projective strategy is an involution, both by `rfl`. -/
def mirror : MirrorSimul M.swap (S.swap (qldGame (d := d) hm)) δ where
  K := Mi.K
  first := Mi.second
  second := Mi.first

@[simp] theorem mirror_K : Mi.mirror.K = Mi.K := rfl

@[simp] theorem mirror_toFirst : Mi.mirror.first = Mi.second := rfl

@[simp] theorem mirror_toSecond : Mi.mirror.second = Mi.first := rfl

theorem mirror_SA : Mi.mirror.first.SA = Mi.second.SA := rfl

/-- **The mirror is an involution, on the nose.** -/
theorem mirror_mirror : Mi.mirror.mirror = Mi := rfl

/-! ## The physical state -/

/-- **The physical state is a unit vector**: it is the state of the first cut. -/
theorem physVec_unit : ‖(phys (Anc F m) F m d M Mi.K).ψ‖ = 1 :=
  Mi.first.mVec_unit

/-- **The second cut lands on the same physical state.** The exchange of the two blocks of
registers carries the physical state of the model with the players exchanged, which the second
cut reads, to the physical state, which the first cut reads (`physE_symm`). It is what lets a
statement proved on one cut be combined with one proved on the other. -/
theorem physVec_mirror :
    (blockSwapIso (Anc F m) F m d M Mi.K).W (phys (Anc F m) F m d M.swap Mi.K).ψ
      = (phys (Anc F m) F m d M Mi.K).ψ :=
  (blockSwapIso (Anc F m) F m d M Mi.K).W_ψ

/-! ## Bob's objects, for free

Nothing below has a proof of its own: each is a lemma about `SimulPair` instantiated at `second`
and flattened onto the physical registers by `compHom`. They are stated because the typing is the
point --- each of Bob's objects is an operator of the second player of the physical model, where
Alice's is one of the first. -/

section Bob

/-- **Bob's exact Pauli measurement at an arbitrary probe**, on his physical registers
`(B'', (Eb, B'))`. -/
def bobMTilde (W : Bas) (v : Anc F m) (a : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  compHom (Mi.second.mTildeAnc W v a)

/-- It is projective, by the lemma that says Alice's is. -/
theorem isPVM_bobMTilde (W : Bas) (v : Anc F m) : IsPVMIn (Mi.bobMTilde W v) :=
  (Mi.second.isPVM_mTildeAnc W v).pushforward compHom_one

/-- **Bob's swap unitary** `V_B`, on the same registers. -/
def bobSwap : Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  compHom Mi.second.swapA

theorem bobSwap_mul_conjTranspose : Mi.bobSwap * star Mi.bobSwap = 1 := by
  rw [bobSwap, ← map_star, ← map_mul, Mi.second.swapA_mul_conjTranspose, compHom_one]

theorem bobSwap_conjTranspose_mul : star Mi.bobSwap * Mi.bobSwap = 1 := by
  rw [bobSwap, ← map_star, ← map_mul, Mi.second.swapA_conjTranspose_mul, compHom_one]

/-- **Display `eq:qld-unitary-6` for Bob**: his swap unitary strips the pair measurement off his
exact Pauli measurement, leaving the Weyl syndrome on `B''` alone. The paper says "an entirely
analogous calculation shows"; here it is the same calculation, at the other instance. -/
theorem bobSwap_conj_bobMTilde (W : Bas) (v : Anc F m) (a : F) :
    Mi.bobSwap * Mi.bobMTilde W v a * star Mi.bobSwap
      = compHom (smulKron 1 (syn (weylOf W) v a)) := by
  rw [bobSwap, bobMTilde, ← map_star, ← map_mul, ← map_mul, Mi.second.swapU_conj_mTildeAnc]

/-- **Alice's exact Pauli measurement at an arbitrary probe**, on her physical registers
`(A'', (Ea, A'))` --- named here only so that the two sit side by side. -/
def aliceMTilde (W : Bas) (v : Anc F m) (a : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  compHom (Mi.first.mTildeAnc W v a)

/-- It is projective. -/
theorem isPVM_aliceMTilde (W : Bas) (v : Anc F m) : IsPVMIn (Mi.aliceMTilde W v) :=
  (Mi.first.isPVM_mTildeAnc W v).pushforward compHom_one

/-- At the mirror, Alice's exact Pauli measurement is Bob's. -/
@[simp] theorem mirror_aliceMTilde : Mi.mirror.aliceMTilde = Mi.bobMTilde := rfl

/-- At the mirror, Bob's exact Pauli measurement is Alice's. -/
@[simp] theorem mirror_bobMTilde : Mi.mirror.bobMTilde = Mi.aliceMTilde := rfl

/-- **The two exact Pauli measurements lie on opposite sides of the physical cut.** The content is
the typing: this expression is well formed, and no expression comparing two objects built inside a
single `SimulPair` is. It is the left-hand side of `lem:qld-pauli-selfcons`. -/
def selfConsGap (W : Bas) (v : Anc F m) (a : F) : ℝ :=
  (phys (Anc F m) F m d M Mi.K).xSqNorm (Mi.aliceMTilde W v a) (Mi.bobMTilde W v a)

/-- **The gap is the same at the mirror**: the mirror's physical model is the physical model with
the players exchanged (`blockSwapIso`), and its two measurements are Bob's and Alice's. -/
theorem mirror_selfConsGap (W : Bas) (v : Anc F m) (a : F) :
    Mi.mirror.selfConsGap W v a = Mi.selfConsGap W v a :=
  phys_swap_xSqNorm (Mi.bobMTilde W v a) (Mi.aliceMTilde W v a)

end Bob

end MirrorSimul

end MIPRE.QLD

end

end
