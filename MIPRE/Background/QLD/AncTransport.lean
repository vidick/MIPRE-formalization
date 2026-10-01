/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Simul

@[expose] public section

/-!
# The ancilla transports across the padded state (`lem:qld-pauli-selfcons`, the exact steps)

The paper's chain for the self-consistency of the exact Pauli observables --- the step
`eq:qld-pulling-3a`, and again `eq:qld-pulling-4` --- moves a generalized Pauli from one party's
ancilla half to the other's, and calls the move `approx_0`: it is exact, because the two halves are
maximally entangled and the syndrome projectors are symmetric.

The register model has that (`BipartiteModel.reg_mirror`): a matrix `P` on the first player's
half acts on the state as `Pᵀ` on the second player's. The generalized Paulis over a field of
characteristic two are real symmetric matrices, and so are their spectral and syndrome projectors
(`proj_weylOf_transpose`, `syn_weylOf_transpose`), so the transpose costs nothing
(`stateVec_hatVec_syn`). What the chain needs is the same statement in the model `K` of a
`SimulPair`, which is not literally the register model --- the structure only provides an
embedding `ι` of the register model into it. That is enough: `ι` intertwines each player's
operators and carries the state to the state, so the vector identity is carried exactly
(`SimulPair.stateVec_ancSyn`), and so is the resolution of the identity by the matched pairs of
syndrome projectors (`SimulPair.sum_ancSyn_mulVec`).

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The matrix route read the
expanded state `hatVec ψ = expVec epr ψ` entry by entry (`stateVec_expVec_kron_one`) and carried
the transport to the padded state `Φ` as the vanishing of a squared norm, a quantity the padded
state reproduces. In the model the expanded state is the register model `M.reg (Anc F m)`, the
ancilla operator `1 ⊗ S` of the first player is `smulKron 1 S`, the transport on it is
`BipartiteModel.reg_mirror`, and the transport to `K` is the intertwining of the embedding, with no
detour through a norm.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-! ## The symmetric ancilla projectors -/

/-- **A spectral projector of a generalized Pauli family is symmetric**: the family is real
symmetric, and the projector is a real Fourier average of it. -/
theorem proj_weylOf_transpose (W : Bas) (h : Anc F m) :
    (proj (weylOf W) h)ᵀ = proj (weylOf W) h := by
  rw [proj_def, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [Matrix.transpose_smul, weylOf_transpose W a]

/-- **A syndrome projector of a generalized Pauli family is symmetric**, as a sum of spectral
projectors. -/
theorem syn_weylOf_transpose (W : Bas) (v : Anc F m) (a : F) :
    (syn (weylOf W) v a)ᵀ = syn (weylOf W) v a := by
  rw [syn_eq_synOf, synOf, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun e _ => proj_weylOf_transpose W e

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-! ## The transport, on the expanded state -/

/-- **The ancilla's syndrome projector transports across the expanded state, exactly.** The two
halves of the register model's EPR pair are maximally entangled and the syndrome projectors are
symmetric, so moving one from Alice's half to Bob's costs nothing. -/
theorem stateVec_hatVec_syn (M : BipartiteModel 𝒞 𝒜 ℬ) (W : Bas) (v : Anc F m) (a : F) :
    (M.reg (Anc F m)).π ((M.reg (Anc F m)).πA (smulKron 1 (syn (weylOf W) v a)))
        (M.reg (Anc F m)).ψ
      = (M.reg (Anc F m)).π ((M.reg (Anc F m)).πB (smulKron 1 (syn (weylOf W) v a)))
        (M.reg (Anc F m)).ψ := by
  rw [M.reg_mirror, syn_weylOf_transpose]

/-- The expanded state's transport, as the vanishing of a cross-party deviation. -/
theorem xSqNorm_hatVec_syn (M : BipartiteModel 𝒞 𝒜 ℬ) (W : Bas) (v : Anc F m) (a : F) :
    (M.reg (Anc F m)).xSqNorm (smulKron 1 (syn (weylOf W) v a))
        (smulKron 1 (syn (weylOf W) v a)) = 0 := by
  rw [BipartiteModel.xSqNorm, BipartiteModel.xNorm, StateModel.snorm, Op.snorm, map_sub,
    _root_.sub_apply, stateVec_hatVec_syn, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0)]

/-- **The two ancilla halves resolve the identity on the expanded state** (`eq:qld-pulling-4`):
by the transport each matched pair of syndrome projectors acts as the projector on one side alone,
and those sum to the identity. -/
theorem sum_hatVec_syn_mulVec (M : BipartiteModel 𝒞 𝒜 ℬ) (W : Bas) (v : Anc F m) :
    (M.reg (Anc F m)).π (∑ a : F, (M.reg (Anc F m)).πA (smulKron 1 (syn (weylOf W) v a))
        * (M.reg (Anc F m)).πB (smulKron 1 (syn (weylOf W) v a))) (M.reg (Anc F m)).ψ
      = (M.reg (Anc F m)).ψ := by
  have hsyn := isPVM_syn (isWeylFamily_weylOf (F := F) (m := m) W) v
  have hstep : ∀ a : F,
      (M.reg (Anc F m)).π ((M.reg (Anc F m)).πA (smulKron 1 (syn (weylOf W) v a))
          * (M.reg (Anc F m)).πB (smulKron 1 (syn (weylOf W) v a))) (M.reg (Anc F m)).ψ
        = (M.reg (Anc F m)).π ((M.reg (Anc F m)).πA (smulKron 1 (syn (weylOf W) v a)))
          (M.reg (Anc F m)).ψ := fun a => by
    rw [map_mul, mul_apply_eq_comp, ← stateVec_hatVec_syn,
      ← mul_apply_eq_comp, ← map_mul, ← map_mul, smulKron_mul, one_mul,
      hsyn.idem a]
  rw [map_sum, _root_.sum_apply, Finset.sum_congr rfl fun a _ => hstep a,
    ← _root_.sum_apply, ← map_sum, ← map_sum, ← smulKron_sum_right,
    hsyn.sum_eq_one, smulKron_one_one, map_one, map_one, one_apply_eq_self]

/-! ## The transport, in the model of a simultaneous pair measurement -/

namespace SimulPair

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

/-- **The ancilla's syndrome projector transports across the padded state, exactly.**

This is the `approx_0` step of the paper's pulling chain (`eq:qld-pulling-3a`, and again at
`eq:qld-pulling-4`), on the state the chain is actually run on. The model `K` is not the register
model, but the embedding `ι` intertwines each player's operators and carries the state to the
state, so the transport on the register model (`stateVec_hatVec_syn`) is carried exactly. -/
theorem stateVec_ancSyn (_P : SimulPair M S K ι δ) (W : Bas) (v : Anc F m) (a : F) :
    K.π (K.πA (ι.ΦA (smulKron 1 (syn (weylOf W) v a)))) K.ψ
      = K.π (K.πB (ι.ΦB (smulKron 1 (syn (weylOf W) v a)))) K.ψ := by
  rw [← ι.W_ψ, ι.intertwineA, ι.intertwineB, stateVec_hatVec_syn]

/-- **The two ancilla halves resolve the identity on the padded state** (`eq:qld-pulling-4`).
Summing the matched pairs of syndrome projectors, one on each party, leaves the state unchanged:
this is the resolution on the register model (`sum_hatVec_syn_mulVec`), carried along the
embedding. This is the step that lets the chain insert Bob's ancilla resolution. -/
theorem sum_ancSyn_mulVec (_P : SimulPair M S K ι δ) (W : Bas) (v : Anc F m) :
    K.π (∑ a : F, K.πA (ι.ΦA (smulKron 1 (syn (weylOf W) v a)))
        * K.πB (ι.ΦB (smulKron 1 (syn (weylOf W) v a)))) K.ψ = K.ψ := by
  rw [← ι.W_ψ, ι.toLocalIsometry.intertwine_sum, sum_hatVec_syn_mulVec]

end SimulPair

end MIPRE.QLD

end

end
