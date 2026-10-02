/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122),
MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Local.lean, to the symmetric model of
`planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Core

@[expose] public section

/-!
# Preliminary comparison theorems: bipartite self-consistency (local bridges)

The bridge from bipartite strong self-consistency of a local family to strong
self-consistency of its left lift: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Local.lean` in the
port of `planning/c6b-plan.md` (milestone M3, section "Port conventions").

`bipartiteSSC_implies_localSSC_liftLeft` takes a symmetric model `S : SymModel 𝔓 K` in place of
the state `ψ : QuantumState (ι × ι)` and drops the vendored hypothesis `hperm : PermInvState ψ`.
The bipartite overlap `∑ₐ ev(Aₐ ⊗ Aₐ)` and the local square `∑ₐ ev(Aₐ² ⊗ I)` are comparable
because `ev(M ⊗ I) = ev(I ⊗ M)`, the model's `S.ev_L_eq_ev_R`, which enters through
`ev_adjoint_self_leftTensor_sub_rightTensor` (`BipartiteSelfConsistency/Core.lean`). The
comparison is made outcome by outcome, where the vendored proof sums first.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Preliminaries

open MIPStarRE.LDT (Distribution avgOver_mono)

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Bridge lemma: bipartite strong self-consistency of a local family implies strong
self-consistency of its left lift, with the same constant.

Each overlap `ev(Aₐ ⊗ Aₐ)` is at most the local square `ev(Aₐ² ⊗ I)`, since
`0 ≤ ev((Aₐ ⊗ I − I ⊗ Aₐ)^* (Aₐ ⊗ I − I ⊗ Aₐ)) = 2 (ev(Aₐ² ⊗ I) − ev(Aₐ ⊗ Aₐ))` by swap symmetry.
The vendored lemma asks for a permutation-invariant state. -/
theorem bipartiteSSC_implies_localSSC_liftLeft {Question Outcome : Type*} [Fintype Outcome]
    (S : SymModel 𝔓 K) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome 𝔓) (δ : ℝ) :
    S.BipartiteSSCRel 𝒟 A δ →
    S.SSCRel 𝒟 (IdxSubMeas.liftLeft S A) δ := fun ⟨hssc⟩ =>
  ⟨(avgOver_mono 𝒟 _ _ fun q => by
    show max 0 (S.ev (S.L (A q).total) -
        ∑ a, S.ev (S.L ((A q).outcome a) * S.L ((A q).outcome a))) ≤
      max 0 (S.ev (S.L (A q).total) -
        ∑ a, S.ev (S.opTensor ((A q).outcome a) ((A q).outcome a)))
    refine max_le_max le_rfl (sub_le_sub_left (Finset.sum_le_sum fun a _ => ?_) _)
    have h := ev_adjoint_self_leftTensor_sub_rightTensor S (.of_nonneg ((A q).outcome_pos a))
    have h0 := S.ev_adjoint_self_nonneg (S.L ((A q).outcome a) - S.R ((A q).outcome a))
    rw [S.leftTensor_mul_leftTensor]
    linarith).trans hssc⟩

end MIPRE.LIDT.Co.Preliminaries

end
