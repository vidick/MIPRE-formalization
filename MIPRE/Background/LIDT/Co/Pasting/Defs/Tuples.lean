/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Pasting/Defs/
Tuples.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.OpFamily
public import MIPStarRE.LDT.Pasting.Defs.Tuples

@[expose] public section

/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers: the counterpart of
`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Tuples.lean` in the port of
`planning/c6b-plan.md` (milestone M11, section "Port conventions").

The operator helpers of the vendored file take their operators in the matrix algebra `Op ι`.
None of them reads a state, so here they are generic over a ring `R` (the type monomials and
truncated type sums), a `ℂ`-algebra (the Bernoulli tail, with its binomial coefficients as
complex scalars) or an ordered `⋆`-ring (the two products with a total operator, which take
submeasurements): local operators take `R = 𝔓`, joint ones `R = K →L[ℂ] K`. The one placement
lemma, `bernoulliTailOperator_leftTensor`, takes the symmetric model `S` as its first explicit
argument, in place of the vendored named carrier `(ι₂ := ι)`.

The classical half of the vendored file (the distinct-tuple distribution with its support and
probability lemmas, the question and outcome type abbreviations, the type weights and patterns,
and the interpolation-eligibility predicate) is not ported: this file imports the vendored file,
and the ported files of `Pasting` name those declarations through explicit
`open MIPStarRE.LDT.Pasting (…)` lists.

## Not ported

- `distinctTuples`: classical, imported.
- `distinctTupleSupport`: classical, imported.
- `mem_distinctTupleSupport`: classical, imported.
- `distinctTupleSupport_card`: classical, imported.
- `distinctTupleSupport_nonempty_of_le`: classical, imported.
- `distinctTupleSupport_eq_empty_of_lt`: classical, imported.
- `distinctTupleDistribution`: classical, imported.
- `distinctTupleDistribution_support`: classical, imported.
- `distinctTupleDistribution_weight`: classical, imported.
- `distinctTupleDistribution_weight_sum_le_one`: classical, imported.
- `distinctTupleDistribution_isProbability_of_le`: classical, imported.
- `distinctTupleDistribution_toPMF_of_le`: classical, imported.
- `distinctTupleDistribution_weight_sum_eq_one_of_le`: classical, imported.
- `GHatOutcome`: classical, imported.
- `SliceQuestion`: classical, imported.
- `SlicePairQuestion`: classical, imported.
- `GHatTupleOutcome`: classical, imported.
- `GHatType`: classical, imported.
- `SandwichedLineQuestion`: classical, imported.
- `VerticalLineQuestion`: classical, imported.
- `gHatTypeWeight`: classical, imported.
- `prependTypeBit`: classical, imported.
- `gHatTupleType`: classical, imported.
- `gHatTupleSupport`: classical, imported.
- `gHatTupleHammingWeight`: classical, imported.
- `outcomesByType`: classical, imported.
- `InterpolationEligible`: classical, imported.

## References

In `LionSR/MIPStarRE` at commit 507e8122, not in this repository:
- `references/ldt-paper/ld-pasting.tex`
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co.Pasting

open MIPStarRE.LDT.Pasting (GHatType gHatTypeWeight)
open MIPRE.LIDT.Co (SymModel SubMeas OpFamily)

section Ring

variable {R : Type*} [Ring R]

/-- The operator monomial `G^{|τ|} (1 - G)^{k - |τ|}` associated with a type `τ`. -/
noncomputable def gHatTypeOperator (G : R) {k : ℕ} (τ : GHatType k) : R :=
  G ^ gHatTypeWeight τ * (1 - G) ^ (k - gHatTypeWeight τ)

/-- `def:truncated-type-sums`.

Fixing a tail type `τ_tail`, this sums the source-style monomials contributed by
all prefixes whose total Hamming weight can still reach the interpolation
threshold `d + 1`. The parameter `prefixLen` is the paper's `ℓ - 1`. -/
noncomputable def truncatedTypeSums (G : R) (d prefixLen : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) : R :=
  ∑ τprefix : GHatType prefixLen,
    if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail then
      gHatTypeOperator G τprefix
    else 0

variable [Algebra ℂ R]

/-- The Bernoulli tail operator from `lem:chernoff-bernoulli-matrix`:
`F(X) = ∑_{r=degree+1}^{k} C(k,r) · X^r · (I - X)^{k-r}`.
This is the operator-valued Bernoulli tail probability. -/
noncomputable def bernoulliTailOperator (k degree : ℕ) (X : R) : R :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r))

end Ring

/-- The Bernoulli-tail polynomial commutes with left tensor placement. -/
theorem bernoulliTailOperator_leftTensor {𝔓 : Type*} [CStarAlgebra 𝔓] [PartialOrder 𝔓]
    [StarOrderedRing 𝔓] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (S : SymModel 𝔓 K) (A : 𝔓) (k degree : ℕ) :
    bernoulliTailOperator k degree (S.L A) = S.L (bernoulliTailOperator k degree A) := by
  unfold bernoulliTailOperator
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, map_mul, map_pow, map_pow, map_sub, map_one]

section SubMeas

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- Multiply each outcome operator by a total operator on the right. -/
noncomputable def multiplyByTotalOnRight {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α R) (B : SubMeas β R) : OpFamily α R where
  outcome := fun a => A.outcome a * B.total
  total := A.total * B.total

/-- Multiply each outcome operator by a total operator on the left. -/
noncomputable def multiplyByTotalOnLeft {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α R) (B : SubMeas β R) : OpFamily β R where
  outcome := fun b => A.total * B.outcome b
  total := A.total * B.total

end SubMeas

end MIPRE.LIDT.Co.Pasting

end
