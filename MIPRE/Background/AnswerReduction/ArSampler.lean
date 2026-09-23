/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Params
import MIPRE.Background.AnswerReduction.TypedGame
import MIPRE.Foundations.OracularSampler

/-!
# The typed answer-reduced sampler

Piece AR-3d of `planning/answer-reduction.md`, concluded: the sampler `Ŝ^ar` of the typed
answer-reduced verifier as a `CL.TypedSampler` over the types `Role × PcpTy`, at the level
`max (ℓ + 1) 3`.

It is the product (`CL.TypedSampler.prodDirect`) of the typed oracularized sampler of the input
sampler (`oracleSampler`, piece O3) and the PCP sampler, answered directly (`pcpDirect`) with the
parameters of `family` computed by `parProg`. Its typed CL functions are those of the typed
game (`typedSampler_cl`), and its program depends only on the input sampler's program and on
`(λ, μ, σ)` (`typedSampler_prog`): the structural half of `lem:ar-sampler-independence`.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open CL SAT Pcp

variable {ℓ : ℕ} (S : Sampler (ℓ + 1)) (PD : PcpDecider) (lam mu sigma : ℕ)

/-- The PCP half, directly answered. -/
def pcpDirect : DirectSampler 3 PcpTy :=
  (family PD lam mu sigma).directSampler (parProg PD lam mu sigma) (parProg_closed PD lam mu sigma)
    (parProg_runs PD lam mu sigma)

/-- **The typed answer-reduced sampler.** -/
def typedSampler : TypedSampler (level ℓ) ArTy :=
  TypedSampler.prodDirect (oracleSampler S) (pcpDirect PD lam mu sigma) (level ℓ) (by omega)
    (le_max_left _ _) (le_max_right _ _)

/-- The typed CL functions are those of the typed answer-reduced game. -/
theorem typedSampler_cl (V : Verifier (ℓ + 1)) (n : ℕ) (w : Player) (rt : ArTy) :
    (typedSampler V.sampler PD lam mu sigma).cl n w rt =
      cl V n ((family PD lam mu sigma).par n) ((family PD lam mu sigma).hk n)
        ((family PD lam mu sigma).sel n) ((family PD lam mu sigma).sel' n) rt := rfl

theorem typedSampler_dim (n : ℕ) :
    (typedSampler S PD lam mu sigma).dim n =
      S.dim n + Pcp.pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k := rfl

/-- **The program depends only on the input sampler's program** and on `(λ, μ, σ)`. -/
theorem typedSampler_prog :
    (typedSampler S PD lam mu sigma).prog =
      ProductSampler.prog answerProg dimProg (OracleSampler.prog S.prog) (ℓ + 1)
        (parProg PD lam mu sigma) := rfl

end MIPRE.AnswerReduction

end
