/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.SwapMeasure

@[expose] public section

/-!
# The exact Pauli measurement at an arbitrary probe

`lem:qld-exact-paulis` gives `M~^{W, ind_m(u)}`, the exact Pauli measurement at the low-degree
encoding of a *point*. `lem:qld-pauli-selfcons` --- the self-consistency the swap isometry's item 1
needs --- is stated at a **uniform** `u-tilde` in `F_q^M`, and that is not a point's encoding: the
encodings are a tiny subset of `F_q^M`. Getting the two confused is the omission that created that
node in the first place, so the two probes are kept apart here by name.

`mTildeAnc` is the measurement at an arbitrary probe. Nothing about it is new --- the generic
`mTilde` of `ExactPauli.lean` already takes the probe as an argument, and `mTildeAt` is its value
at `indVec u` --- but the chain of `lem:qld-pauli-selfcons` runs at a probe that is not of that
form, and every statement it makes has to be available there. `mTildeAt_eq_mTildeAnc` is the one
place the two meet.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The pair measurement is the
`SA` of a `SimulPair M S K ι δ`, a projective measurement in the first algebra `𝒜'` of the model
`K`, so `mTildeAnc` is, as `mTildeAt` is, a matrix over `𝒜'` on the register `Anc F m` (register
outer, `smulKron`): projective in the sense of `IsPVMIn`, and conjugated by the swap unitary
`swapA` and its adjoint `star swapA` to the bare syndrome projector `smulKron 1 (syn …)`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

section Probe

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
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

set_option linter.unusedSectionVars false

namespace SimulPair

variable (P : SimulPair M S K ι δ)

/-- **The paper's `M~^{W, u-tilde}_a` at an arbitrary probe**: a matrix over `K`'s first algebra on
the register. `mTildeAt` is this at `ind_m(u)`. -/
def mTildeAnc (W : Bas) (v : Anc F m) (a : F) : Matrix (Anc F m) (Anc F m) 𝒜' :=
  mTilde P.SA.op (PolyPair.proj W) cubeData (weylOf W) v a

/-- It is a projective measurement, at every probe. -/
theorem isPVM_mTildeAnc [StarModule ℂ 𝒜'] (W : Bas) (v : Anc F m) :
    IsPVMIn (P.mTildeAnc W v) :=
  isPVM_mTilde P.SA_proj (PolyPair.proj W) cubeData (isWeylFamily_weylOf W) v

/-- **At a point's encoding it is the measurement `lem:qld-exact-paulis` speaks of.** The only
place the two probes meet. -/
theorem mTildeAt_eq_mTildeAnc (W : Bas) (u : Point F m) :
    P.mTildeAt W u = P.mTildeAnc W (indVec u) := rfl

/-- **Display `eq:qld-unitary-6` at an arbitrary probe.** Conjugation by the swap unitary strips
the pair measurement off the exact Pauli measurement whatever the probe, since the cancellation is
between the outcome's shift and the conjugation's, and both are written with the same pairing. -/
theorem swapU_conj_mTildeAnc [StarModule ℂ 𝒜'] (W : Bas) (v : Anc F m) (a : F) :
    P.swapA * P.mTildeAnc W v a * star P.swapA = smulKron 1 (syn (weylOf W) v a) := by
  rw [SimulPair.swapA, SimulPair.mTildeAnc]
  cases W with
  | X => exact swapU_conj_mTilde_X P.SA_proj v a
  | Z => exact swapU_conj_mTilde_Z P.SA_proj v a

end SimulPair

end Probe

end MIPRE.QLD

end

end
