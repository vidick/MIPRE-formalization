/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/StatementBridge.lean
-/
/-
# Bridge: the development proves the standalone statement

`Statement.lean` (Mathlib only) restates the definitions of the development
in its own namespace `MainStatement` and states the main theorem as the
proposition `UniformParallelRepetition`. A re-declared structure is a new
type, so the root theorem `CommutingRepetition.uniform_parallel_repetition`
does not literally apply to it; the private declarations below identify
each copy with its original field by field — every identity is definitional,
the only non-trivial step being that the two suprema defining `ω^co` range
over the same set of real numbers — and `uniform_parallel_repetition` then
proves `UniformParallelRepetition` from the root theorem. Since the density
programme (stage E7) proves Lin's theorem, the transfer also runs in the
other direction: `tracialDensity` discharges the standalone file's own
`TracialDensityHypothesis`, which is why `UniformParallelRepetition` has no
hypothesis. The axiom gate (`scripts/AxiomGate.lean`) checks both theorems
here together with the roots. Nothing here is a manuscript statement.
-/
import MIPRE.Background.Repetition.CommutingRepetition.Statement
import MIPRE.Background.Repetition.CommutingRepetition.MainTheorem.Main

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace MainStatement

section Bridge

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def toGame (G : Game X Y A B) : CommutingRepetition.Game X Y A B where
  questionWeight := G.questionWeight
  weight_nonneg := G.weight_nonneg
  weight_normalized := G.weight_normalized
  payoff := G.payoff
  payoff_nonneg := G.payoff_nonneg
  payoff_le_one := G.payoff_le_one

private def toStrategy (S : CommutingStrategy.{0} X Y A B) :
    CommutingRepetition.CommutingStrategy.{0} X Y A B where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  E := S.E
  F := S.F
  E_pos := S.E_pos
  F_pos := S.F_pos
  E_sum := S.E_sum
  F_sum := S.F_sum
  commutes := S.commutes

private def ofStrategy (S : CommutingRepetition.CommutingStrategy.{0} X Y A B) :
    CommutingStrategy.{0} X Y A B where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  E := S.E
  F := S.F
  E_pos := S.E_pos
  F_pos := S.F_pos
  E_sum := S.E_sum
  F_sum := S.F_sum
  commutes := S.commutes

/-- The two suprema defining `ω^co` range over the same set. -/
private theorem omegaCO_eq (G : Game X Y A B) :
    G.omegaCO = (toGame G).omegaCO := by
  unfold Game.omegaCO CommutingRepetition.Game.omegaCO
  congr 1
  ext r
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨toStrategy S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨ofStrategy S, rfl⟩

private def ofAlgebra (M : CommutingRepetition.StdTracialAlgebra.{0}) :
    StdTracialAlgebra.{0} where
  A := M.A
  τ := M.τ
  τ_one := M.τ_one
  τ_mul_comm := M.τ_mul_comm
  τ_star := M.τ_star
  H := M.H
  ι := M.ι
  ι_dense := M.ι_dense
  ι_inner := M.ι_inner
  L := M.L
  R := M.R
  L_apply := M.L_apply
  R_apply := M.R_apply
  LR_commute := M.LR_commute

private def ofEmbeddable {Xc Ac : Type} [Fintype Xc] [Fintype Ac]
    (q : CommutingRepetition.TraciallyEmbeddableCorrelation Xc Ac) :
    TraciallyEmbeddableCorrelation Xc Ac where
  M := ofAlgebra q.M
  σ := q.σ
  σ_pos := q.σ_pos
  σ_normalized := q.σ_normalized
  E := q.E
  E_pos := q.E_pos
  E_sum := q.E_sum
  G := q.G
  G_pos := q.G_pos
  G_sum := q.G_sum
  G_commutant := q.G_commutant

end Bridge

/-- **Lin's density theorem in the vocabulary of `Statement.lean`**
(audit node 1.1.1): the standalone file's own `TracialDensityHypothesis` is
a theorem, transferred from `CommutingRepetition.Density.tracialDensity`
(stage E7 of the density programme) through the field-by-field identification
of the two copies of `StdTracialAlgebra` and
`TraciallyEmbeddableCorrelation`. This is why `UniformParallelRepetition`
below carries no hypothesis. -/
theorem tracialDensity : TracialDensityHypothesis := by
  intro Xc Ac _ _ _ _ p hp δ hδ
  obtain ⟨S, hS⟩ := hp
  obtain ⟨q, hq⟩ :=
    CommutingRepetition.Density.tracialDensity Xc Ac p ⟨toStrategy S, hS⟩ δ hδ
  exact ⟨ofEmbeddable q, hq⟩

/-- The development proves the standalone statement of `Statement.lean`. -/
theorem uniform_parallel_repetition : UniformParallelRepetition := by
  unfold UniformParallelRepetition
  obtain ⟨c, hc, h⟩ := CommutingRepetition.uniform_parallel_repetition
  refine ⟨c, hc, ?_⟩
  intro X Y A B _ _ _ _ _ _ _ _ G n hn
  rw [omegaCO_eq, omegaCO_eq]
  exact h X Y A B (toGame G) n hn

end MainStatement
