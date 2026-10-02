/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/
Commutativity/ScalarApproximation/Core.lean, to the symmetric model of `planning/c6b-plan.md`;
not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Commutativity.Scaffold.Products
public import MIPRE.Background.LIDT.Co.Preliminaries.BipartiteSelfConsistency.Core

@[expose] public section

/-!
# Section 11 commutativity: scalar approximation core

Upstream scalar-approximation lemmas that do not depend on the later averaged commutation proof,
so they can be shared by both `ProcessedG` and `Pointwise` without creating import cycles: the
counterpart of `MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/Core.lean`
in the port of `planning/c6b-plan.md` (milestone M7, section "Port conventions").

`qBipartiteSSCDefect_eq_half_qSDD_of_proj` takes the symmetric model `S` as an explicit first
argument in place of the vendored state `ψ`, and drops the vendored hypothesis
`hperm : PermInvState ψ`: its one swap use is in
`Preliminaries.ev_adjoint_self_leftTensor_sub_rightTensor`, which applies `S.ev_L_eq_ev_R`. For
that lemma this file imports `Co/Preliminaries/BipartiteSelfConsistency/Core.lean` besides the
counterpart of the vendored import, rather than repeat its expansion inline. The
vendored proof shows the gap `ev L(P) − ∑_a ev(P_a ⊗ P_a)` nonnegative through the Kronecker
inequality `P_a ⊗ P_a ≤ P_a ⊗ I`; here the gap is half of `qSDD`, a sum of expectations
`ev(X^* X)`, so it is nonnegative without that inequality.

## Not ported

Every declaration of the vendored file has a counterpart here.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Commutativity

variable {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓] [StarOrderedRing 𝔓]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For a projective submeasurement on a symmetric model, the bipartite SSC defect is exactly
half of the left/right SDD defect. The vendored lemma asks for a permutation-invariant state. -/
lemma qBipartiteSSCDefect_eq_half_qSDD_of_proj
    {α : Type*} [Fintype α]
    (S : SymModel 𝔓 K)
    (P : ProjSubMeas α 𝔓) :
    S.qBipartiteSSCDefect P.toSubMeas =
      (1 / 2 : ℝ) * S.qSDD (P.toSubMeas.liftLeft S) (P.toSubMeas.liftRight S) := by
  have hq : S.qSDD (P.toSubMeas.liftLeft S) (P.toSubMeas.liftRight S) =
      2 * (S.ev (S.L P.toSubMeas.total) -
        ∑ a : α, S.ev (S.opTensor (P.outcome a) (P.outcome a))) := by
    refine (Finset.sum_congr rfl fun a _ =>
      Preliminaries.ev_adjoint_self_leftTensor_sub_rightTensor S
        (.of_nonneg (P.outcome_pos a))).trans ?_
    simp only [P.proj]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← S.ev_sum, S.leftTensor_finset_sum,
      P.sum_eq_total]
  have hgap : 0 ≤ S.ev (S.L P.toSubMeas.total) -
      ∑ a : α, S.ev (S.opTensor (P.outcome a) (P.outcome a)) := by
    have := S.qSDD_nonneg (P.toSubMeas.liftLeft S) (P.toSubMeas.liftRight S)
    linarith
  rw [SymModel.qBipartiteSSCDefect, max_eq_right hgap, hq]
  ring

end MIPRE.LIDT.Co.Commutativity

end
