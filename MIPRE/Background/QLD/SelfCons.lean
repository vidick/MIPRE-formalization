/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.ChainAssembly

@[expose] public section

/-!
# The self-consistency of the exact Pauli observables (`lem:qld-pauli-selfcons`)

`MIPRE/Background/QLD/ChainAssembly.lean` takes Alice's exact Pauli measurement at an arbitrary
probe to the endpoint of the pulling chain, on the physical state. This file closes the lemma:
Bob's exact Pauli measurement reaches the same endpoint (the same chain at the mirror, carried back
by the exchange of the blocks of registers), so the two measurements agree across the physical cut
(`sum_selfConsGap_le`); and the observables, the signed sums of the measurements' elements, agree
at a factor two (`snorm_sq_wTilde_le`), the family being coarse-grained along the character first.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The two exact Pauli
observables are operators of the two players of the physical model `phys (Anc F m) F m d M Mi.K`,
the first cut's and the second cut's `wTildeAt` flattened onto the players' physical registers by
`compHom`. The matrix route moved Bob's half of the chain to the physical state through the
exchange of the parties on the vector (`swapVec`, `snorm_swapVec_aOp_sub_kron_sum`); here the
mirror's physical model is the physical model of the exchanged players, and Bob's half is carried
over by the exchange of the blocks of registers (`MirrorSimul.snorm_sub_endOpMirror`, through
`blockSwapIso`). The passage from the measurements to the observables is the state-model form of
`lem:qld-povm-to-obs` (`StateModel.snorm_sq_obs_sub_le`). The constants are the matrix ones.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

section Generic

/-- **Regrouping a weighted sum by the fibres of a relabelling.** -/
theorem sum_fibre_smul {V : Type*} [AddCommMonoid V] [Module ℂ V] {Λ Λ' : Type*} [Fintype Λ]
    [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ'] (f : Λ → Λ') (α : Λ' → ℂ) (X : Λ → V) :
    (∑ c : Λ', α c • ∑ a ∈ univ.filter fun a => f a = c, X a)
      = ∑ a : Λ, α (f a) • X a := by
  classical
  rw [← Finset.sum_fiberwise (univ : Finset Λ) f fun a => α (f a) • X a]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]

end Generic

section Physical

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ}

set_option synthInstance.maxSize 1000

namespace MirrorSimul

variable (Mi : MirrorSimul M S δ)

/-- **Alice's exact Pauli observable**, the signed sum of her measurement's elements, on her
physical registers `(A'', (Ea, A'))`. -/
def aliceWTilde (W : Bas) (e : F) (v : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  compHom (Mi.first.wTildeAt W e v)

/-- **Bob's**, on his, `(B'', (Eb, B'))`: the second cut's. -/
def bobWTilde (W : Bas) (e : F) (v : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  compHom (Mi.second.wTildeAt W e v)

/-- At the mirror, Alice's exact Pauli observable is Bob's. -/
@[simp] theorem mirror_aliceWTilde : Mi.mirror.aliceWTilde = Mi.bobWTilde := rfl

/-- **Each observable is the signed sum of its measurement's elements**, flattened onto the
physical registers. -/
theorem aliceWTilde_eq_sum (W : Bas) (e : F) (v : Anc F m) :
    Mi.aliceWTilde W e v
      = ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a)) • Mi.aliceMTilde W v a := by
  rw [aliceWTilde, SimulPair.wTildeAt, wTilde, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

theorem bobWTilde_eq_sum (W : Bas) (e : F) (v : Anc F m) :
    Mi.bobWTilde W e v
      = ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a)) • Mi.bobMTilde W v a :=
  Mi.mirror.aliceWTilde_eq_sum W e v

set_option maxHeartbeats 4000000 in
/-- **Display `eq:qld-pulling-cons` for Alice**, with the average over the sampled point dropped:
neither side depends on it. -/
theorem sum_snorm_sq_aliceMTilde_endOp_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceMTilde W v a) - Mi.endOp W v a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  have h := Mi.sum_uniform_snorm_sq_mTildeAnc_endOp_le hfail hd W v
  rwa [← Finset.sum_mul, sum_uniform_eq_one, one_mul] at h

/-- **The same at the mirror, read on the physical state.** The mirror of a `MirrorSimul` is a
`MirrorSimul`, its physical model is the physical model of the exchanged players, and its endpoint
is this one read from the other side: the exchange of the blocks of registers carries the one to
the other (`snorm_sub_endOpMirror`). -/
theorem snorm_endOp_bobMTilde_eq (W : Bas) (v : Anc F m) (a : F) :
    (phys (Anc F m) F m d M.swap Mi.K).snorm
        ((phys (Anc F m) F m d M.swap Mi.K).πA (Mi.bobMTilde W v a) - Mi.endOpMirror W v a)
      = (phys (Anc F m) F m d M Mi.K).snorm
        (Mi.endOp W v a - (phys (Anc F m) F m d M Mi.K).πB (Mi.bobMTilde W v a)) :=
  (Mi.snorm_sub_endOpMirror W v a (Mi.bobMTilde W v a)).trans
    ((phys (Anc F m) F m d M Mi.K).snorm_sub_comm _ _)

set_option maxHeartbeats 4000000 in
/-- **Display `eq:qld-pulling-cons` for Bob.** -/
theorem sum_snorm_sq_endOp_bobMTilde_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (Mi.endOp W v a - (phys (Anc F m) F m d M Mi.K).πB (Mi.bobMTilde W v a)) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  have h := Mi.mirror.sum_snorm_sq_aliceMTilde_endOp_le (povmValue_swapped_le hfail) hd W v
  refine le_trans (le_of_eq ?_) h
  exact (Finset.sum_congr rfl fun a _ =>
    congrArg (· ^ 2) (Mi.snorm_endOp_bobMTilde_eq W v a)).symm

set_option maxHeartbeats 4000000 in
/-- **Lemma `lem:qld-pauli-selfcons` at the level of the two exact Pauli measurements**: they
agree on the physical state, at four times what each costs to reach the chain's endpoint. -/
theorem sum_selfConsGap_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, Mi.selfConsGap W v a)
      ≤ 4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F)) := by
  have h := sum_xSqNorm_le_of_endOp Mi W v
    (Mi.sum_snorm_sq_aliceMTilde_endOp_le hfail hd W v)
    (Mi.sum_snorm_sq_endOp_bobMTilde_le hfail hd W v)
  have hgap : (∑ a : F, Mi.selfConsGap W v a)
      = ∑ a : F, (phys (Anc F m) F m d M Mi.K).xSqNorm (Mi.aliceMTilde W v a)
          (Mi.bobMTilde W v a) := rfl
  rw [hgap]
  linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma `lem:qld-pauli-selfcons`**: the two parties' exact Pauli *observables* agree.

The passage from the measurements to the observable is the paper's, and it is not
Lemma `lem:qld-povm-to-obs` applied to the whole outcome set --- that would cost a factor the
size of the field. The family is coarse-grained first, along the character the observable reads
(`sum_xSqNorm_fibre_le`, which is free for projective families), and only the resulting
*two*-outcome family is turned into an observable. The factor is therefore two. -/
theorem snorm_sq_wTilde_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (e : F) (v : Anc F m) :
    (phys (Anc F m) F m d M Mi.K).snorm
        ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceWTilde W e v)
          - (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWTilde W e v)) ^ 2
      ≤ 2 * (4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F))) := by
  classical
  have hA : (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceWTilde W e v)
      = ∑ c : ZMod 2, sgn c • (phys (Anc F m) F m d M Mi.K).πA (∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, Mi.aliceMTilde W v a) := by
    rw [Mi.aliceWTilde_eq_sum W e v,
      ← sum_fibre_smul (fun a : F => Algebra.trace (ZMod 2) F (e * a)) sgn (Mi.aliceMTilde W v),
      map_sum]
    exact Finset.sum_congr rfl fun c _ => map_smul _ _ _
  have hB : (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWTilde W e v)
      = ∑ c : ZMod 2, sgn c • (phys (Anc F m) F m d M Mi.K).πB (∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, Mi.bobMTilde W v a) := by
    rw [Mi.bobWTilde_eq_sum W e v,
      ← sum_fibre_smul (fun a : F => Algebra.trace (ZMod 2) F (e * a)) sgn (Mi.bobMTilde W v),
      map_sum]
    exact Finset.sum_congr rfl fun c _ => map_smul _ _ _
  have hcoarse := sum_xSqNorm_fibre_le (M := phys (Anc F m) F m d M Mi.K) Mi.physVec_unit
    (Mi.isPVM_aliceMTilde W v) (Mi.isPVM_bobMTilde W v)
    fun a : F => Algebra.trace (ZMod 2) F (e * a)
  simp only [BipartiteModel.xSqNorm_eq_sq, BipartiteModel.xNorm] at hcoarse
  have hgap := Mi.sum_selfConsGap_le hfail hd W v
  simp only [selfConsGap, BipartiteModel.xSqNorm_eq_sq, BipartiteModel.xNorm] at hgap
  have hfib : (∑ c : ZMod 2, (phys (Anc F m) F m d M Mi.K).snorm
        ((phys (Anc F m) F m d M Mi.K).πA (∑ a ∈ univ.filter
            fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, Mi.aliceMTilde W v a)
          - (phys (Anc F m) F m d M Mi.K).πB (∑ a ∈ univ.filter
            fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, Mi.bobMTilde W v a)) ^ 2)
      ≤ 4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F)) :=
    le_trans hcoarse hgap
  rw [hA, hB]
  refine le_trans ((phys (Anc F m) F m d M Mi.K).snorm_sq_obs_sub_le sgn
    (fun c => le_of_eq (norm_sgn c)) _ _) ?_
  rw [show (Fintype.card (ZMod 2) : ℝ) = 2 from by norm_num]
  exact mul_le_mul_of_nonneg_left hfib (by norm_num)

end MirrorSimul

end Physical

end MIPRE.QLD

end
