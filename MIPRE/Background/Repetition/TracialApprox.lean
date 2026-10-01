/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Repetition.Commuting
public import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Reduction
public import MIPRE.Background.Repetition.CommutingRepetition.VN.ConcreteVN
public import MIPRE.Background.QLD.PaddedLIDT
public import MIPRE.Foundations.FinitePairExpand
public import MIPRE.Foundations.KrausDilation

@[expose] public section

/-!
# `ω_co` is approached by projective strategies in finite pairs

Phase 6 of `planning/mipco-track.md` (`reports/lidt-co-audit.md`, §3.4): below `ω_co(G)`, and above
`0`, lies the value of a projective strategy for `G` in a finite pair
(`MIPRE.CommutingFinitePairApprox`, `lem:co-value-finite-pair`). The analytic content is Lin's
tracial density, in the form proved by the vendored development:

1. **Strict tracial reduction.** `ω_co(G)` is the commuting-operator value of the vendored
   development (`MIPRE.Repetition.commutingOperatorValue_eq_omegaCO`), and below it lies the
   winning probability of a tracially embeddable strategy `T`
   (`CommutingRepetition.strict_tracial_reduction`): a tracial algebra in standard form
   `L²(𝒜, τ)`, a density `σ`, the first player's POVMs acting on the left and the second player's
   on the right, in the state `ι σ`.
2. **The standard-form pair.** On `L²(𝒜, τ)`, the commutant of the right action
   (`StdTracialAlgebra.vnAlg`) and its commutant are a finite pair: the trace vector `ι 1` is
   tracial on the first (`StdTracialAlgebra.traceState_mul_comm_vn`) and, through the conjugation
   `J`, on the second, and it separates both, being cyclic for the left and for the right
   actions. The left action lies in the first, the right action in the second, so `T` is a POVM
   strategy of this model, of value its winning probability (`BipartiteModel.value_toCommuting`,
   `TracialStrategy.toCommutingStrategy_correlation`).
3. **Projectivity.** Each player's POVMs dilate to projective measurements in the matrices over the
   player's algebra against one fixed basis vector (`MIPRE.exists_pvm_dilation`); in the ancilla
   extension at that basis vector they form a projective strategy of the same value
   (`BipartiteModel.povmValue_expand_basisVec`), and the extension is a finite pair
   (`BipartiteModel.IsFinitePair.expand`).

An empty alphabet makes `ω_co(G) = 0`, below every admissible threshold; otherwise the alphabets
are those of the vendored theorem, which assumes them nonempty.
-/

namespace MIPRE.Repetition

/-- **`ω_co` is approached by projective strategies in finite pairs** (`lem:co-value-finite-pair`):
below `ω_co(G)`, and above `0`, lies the value of a projective strategy for `G` in a finite pair
on a Hilbert space of `Type`. -/
theorem commutingFinitePairApprox : CommutingFinitePairApprox := by
  sorry

end MIPRE.Repetition

end
