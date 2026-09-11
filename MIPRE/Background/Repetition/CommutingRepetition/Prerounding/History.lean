/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/History.lean
-/
/-
# Pre-rounding: the history relative-entropy bound (node 1.2.10)

The closeness half of node 1.2.10 (05_prerounding.tex, eqs J-A, J-B,
conditioning-divergence, question-answer-conditioning-budget, JA-chain-rule,
first-history-chain-term, bob-block-conditioning-budget, bob-block-chain-rule,
second-history-chain-term, history-relative-entropy): the flattened posterior
`ℚ` over (public history, live questions) is `(3t₀ + 2s₀)/m`-close in relative
entropy to each locally generated tuple law `J_A`, `J_B`.

The frozen statement `history_relative_entropy` was stated in
`Prerounding/Costs.lean` (review #15, hash `cac0d30d4663ab65`) and is moved
here verbatim so that its proof layer can consume the flattened laws
(`flatQ`, `condQA/B`, `flatJA/B`) defined at the end of `Costs.lean`. The
proof-side lemmas live in `Prerounding/HistoryKL.lean` (finite relative-entropy
inequalities), `Prerounding/HistoryCore.lean` (the collapse of the posterior
onto the core posterior law along the flattening fibers), and
`Prerounding/HistoryA.lean` / `HistoryB.lean` (the two conjuncts: log split,
tensorized first chain term, reverse-experiment second chain term).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Costs
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryCore
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryA
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.HistoryB

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-- **History closeness** (node 1.2.10; 05_prerounding.tex, eq
history-relative-entropy): `D(ℚ ‖ J_A), D(ℚ ‖ J_B) ≤ (3t₀ + 2s₀)/m`
with `t₀ = log(1/p)`, `s₀ = |D|·log(|A||B|)`, `m = n − |D|`. The proof
is the KL chain rule (eq JA-chain-rule), tensorization + data
processing for the first term (eq first-history-chain-term), and the
reverse-experiment chain rule with the uniform cut for the second (eqs
bob-block-conditioning-budget through second-history-chain-term),
using the conditioning budget eq question-answer-conditioning-budget
(itself from `D(ℚ‖ℙ) = t₀`, eq conditioning-divergence, and the
`s₀`-cost of adjoining the core word). Classical given the branch
masses: no entropy budget is consumed. -/
theorem history_relative_entropy
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p)
    (hm : D.card < n) :
    Pinsker.finiteRelativeEntropy (S.flatQ R D μ w p)
        (S.flatJA R D μ w p)
      ≤ (3 * Real.log p⁻¹ + 2 * ((D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))) /
        ((n : ℝ) - D.card) ∧
    Pinsker.finiteRelativeEntropy (S.flatQ R D μ w p)
        (S.flatJB R D μ w p)
      ≤ (3 * Real.log p⁻¹ + 2 * ((D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))) /
        ((n : ℝ) - D.card) := by
  -- Proof layer: Prerounding/HistoryKL.lean (finite relative-entropy
  -- inequalities), HistoryCore.lean (the collapse of the posterior onto the core
  -- posterior law along the flattening fibers), HistoryA.lean (Alice conjunct:
  -- log split, tensorized first term, Bob-reverse-experiment second term),
  -- HistoryB.lean (the Bob mirror).
  refine ⟨?_, ?_⟩
  · exact S.klA_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm
  · exact S.klB_le μ hμ hμsum R htotF htotG w hw0 hw1 hwD hp hppos hm

end TracialStrategy

end CommutingRepetition
