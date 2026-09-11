/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Costs.lean
-/
/-
# Prior alignment costs and the posterior branch law (node 1.2.9)

The alignment estimate of 05_prerounding.tex, "Resolver martingales and
state alignment" (eqs prior-alignment-costs, IA-size-bias-calculation,
prior-alignment-bound) and its posterior form (eqs posterior-branch-law,
posterior-branch-normalization, two-alignment-bounds), stated over a
resolver arena invoked on the *generalized label family* — one label per
(revealed set, reference words, answer word), with Alice's effect
`setEffectA D R₀ μ xref yref zA` (batch #14).

Encoding notes (for the fidelity review):

- **The generalized family.** The manuscript invokes thm
  common-resolver-arena on "the one family" containing every effective
  effect, bar average, and reveal-martingale value/conditional mean. In
  the batch-#14 encoding all of these are `setEffectA`/`setEffectB` at
  suitable revealed sets: `H_{r,x}` at `{i} ∪ C_X` (the rfl bridge),
  `H̄_{r,y}` at `C_X` (the cut wiring identity + `C_X = D ∪ L_X ∪
  π_Y^{≤k_Y}`), `F_{j,z}` at `D ∪ L_X ∪ π_Y[1..j]`. So the family is
  indexed by `ALabel`/`BLabel` = (revealed set) × (reference words) ×
  (answer word), and the statements here take an arena over ARBITRARY
  refinement families constrained only through their totals
  (`htotF`/`htotG`) — node 1.2.11 instantiates the refinements (the
  live refinements of eq live-refinements) for the answer laws, which
  the alignment estimate never consumes.
- **Core words.** The manuscript's `z ∈ A_D × B_D`. Labels carry full
  answer words, so core assignments enter through the canonical
  extension `extendCoreA/B` (fixed default off the core, the
  node-1.2.11 fallback-answer pattern); the core effects read only the
  `D`-restriction, so the choice of default is invisible to every
  branch vector.
- **Canonical labels.** `setEffectA` reads its `xref` only on `R₀` and
  its `yref` only off `R₀` (mirrored for Bob). All statements use the
  CANONICAL labels `aLabel`/`bLabel` (pinned side kept on `R₀`, weight
  side kept off, defaults elsewhere) — the representatives the
  reveal-martingale mean tower visits, so the entropy budgets apply
  directly. (Review #15, N1: the budgets themselves already force
  equal branches at behaviorally identical labels via constant-tower
  arguments, so canonicalization is the convenient encoding rather
  than a truth prerequisite.)
- **Weighted form.** Per 07_main_theorem.tex sec 7.4 (the run consumed
  by `weighted_tracial_prerounding`), the core acceptance indicator is
  the private-coin weight `w ∈ [0,1]`; the predicate case is the
  `{0,1}`-valued specialization. The weight is abstract here
  (`0 ≤ w ≤ 1`) and CORE-MEASURABLE (`hwD`: it reads only the
  `D`-restrictions of the question words, exactly the manuscript's
  `w_D(t, z)` — review #15's repair R1: without this the mass and
  entropy chains are false), and the core mass `p` is
  hypothesis-pinned to its explicit strategy expression.
- **The costs** (eq prior-alignment-costs) are the `𝔼_{ℙ⁰}`-weighted
  squared distances of adjacent branch vectors; by the family encoding
  the Alice cost's two labels `({i} ∪ C_X, …)` and `(C_X, …)` are
  exactly the reveal martingale's cut-adjacent labels, which is how the
  proof consumes the signed entropy budgets (batch #13) through the
  signed reverse experiments (batch #11).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Alignment
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.CostsLemmas
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.PriorAlignment
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.PriorAlignmentB
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Vector
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Entropy
import MIPRE.Background.Repetition.CommutingRepetition.Prelim.Information
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.EntropyBudget

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-- The generalized Alice label: a revealed set, the reference words,
and an answer word. The Alice effect at a label is
`setEffectA D R₀ μ xref yref zA`. -/
abbrev ALabel (n : ℕ) (X Y A : Type) : Type :=
  Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)

/-- The generalized Bob label. -/
abbrev BLabel (n : ℕ) (X Y B : Type) : Type :=
  Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)

/-- Canonical extension of a core answer assignment to a full word
(fixed default off the core — the node-1.2.11 fallback-answer pattern;
the core effects read only the `D`-restriction). -/
noncomputable def extendCoreA [Nonempty A] (D : Finset (Fin n))
    (zD : {j : Fin n // j ∈ D} → A) : Fin n → A :=
  fun j => if h : j ∈ D then zD ⟨j, h⟩ else Classical.arbitrary A

/-- Canonical extension of a core Bob assignment. -/
noncomputable def extendCoreB [Nonempty B] (D : Finset (Fin n))
    (zD : {j : Fin n // j ∈ D} → B) : Fin n → B :=
  fun j => if h : j ∈ D then zD ⟨j, h⟩ else Classical.arbitrary B

/-- Canonicalize a reference word to its values ON the revealed set
(fixed default elsewhere). Labels are canonicalized so that two labels
with the same effect coincide: `setEffectA` reads its `xref` only on
`R₀` and its `yref` only off `R₀`, so the Alice label at `R₀` keeps
`xref` on `R₀` and `yref` off `R₀`; without this, an arena could
assign unrelated branch vectors to behaviorally identical labels and
the alignment bound would be false. -/
noncomputable def keepOn {α : Type} [Nonempty α] (R₀ : Finset (Fin n))
    (wd : Fin n → α) : Fin n → α :=
  fun j => if j ∈ R₀ then wd j else Classical.arbitrary α

/-- Canonicalize a reference word to its values OFF the revealed set
(fixed default on it). -/
noncomputable def keepOff {α : Type} [Nonempty α] (R₀ : Finset (Fin n))
    (wd : Fin n → α) : Fin n → α :=
  fun j => if j ∈ R₀ then Classical.arbitrary α else wd j

/-- The canonical Alice label at a revealed set: pinned side kept on
`R₀`, weight side kept off `R₀`, core answers canonically extended. -/
noncomputable def aLabel [Nonempty X] [Nonempty Y] [Nonempty A]
    (D R₀ : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
    (zD : {j : Fin n // j ∈ D} → A) : ALabel n X Y A :=
  (R₀, keepOn R₀ xw, keepOff R₀ yw, extendCoreA D zD)

/-- The canonical Bob label: pinned side (`yref`) kept on `R₀`, weight
side (`xref`) kept off `R₀`. -/
noncomputable def bLabel [Nonempty X] [Nonempty Y] [Nonempty B]
    (D R₀ : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
    (zD : {j : Fin n // j ∈ D} → B) : BLabel n X Y B :=
  (R₀, keepOff R₀ xw, keepOn R₀ yw, extendCoreB D zD)

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-- **The weighted core mass** `p = 𝔼[w_D]` (05_prerounding.tex,
eq p-q-m, in the weighted run of 07 sec 7.4): questions from the
product prior, core answers from the strategy's core-effect
correlation, weighted by `w`. -/
noncomputable def coreMass (D : Finset (Fin n)) (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ) :
    ℝ :=
  ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
    (∏ j : Fin n, μ (xw j) (yw j)) *
      ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        w xw yw zD.1 zD.2 *
          (S.M.τ (star S.σ *
            (S.coreEffectA D xw (extendCoreA D zD.1) * S.σ *
              S.coreEffectB D yw (extendCoreB D zD.2)))).re

/-- **The prior Alice alignment cost** `I_A` (05_prerounding.tex, eq
prior-alignment-costs): the `ℙ⁰`-weighted, `w`-weighted squared
distances `‖φ_{r,x,y} − φ^B_{r,y}‖²` — branch vectors of the
generalized-family arena at the cut-adjacent Alice labels
`({i} ∪ C_X, …)` (the effective effect `H_{r,x}`) and `(C_X, …)` (the
bar `H̄_{r,Y_i}`), against the full Bob label `({i} ∪ C_Y, …)`. -/
noncomputable def alignCostA
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ) :
    ℝ :=
  ∑ r : RevealDatum n D, r.revealLaw *
    ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 *
            ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
                (bLabel D (insert r.i r.CY) xw yw zD.2)
              - R.branch S.σ (aLabel D r.CX xw yw zD.1)
                  (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2

/-- **The prior Bob alignment cost** `I_B` (eq prior-alignment-costs,
second display): distances `‖φ_{r,x,y} − φ^A_{r,x}‖²`, the bar on the
Bob side. -/
noncomputable def alignCostB
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ) :
    ℝ :=
  ∑ r : RevealDatum n D, r.revealLaw *
    ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 *
            ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
                (bLabel D (insert r.i r.CY) xw yw zD.2)
              - R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
                  (bLabel D r.CY xw yw zD.2)‖ ^ 2

/-- **Prior alignment bound** (node 1.2.9; 05_prerounding.tex, eqs
IA-size-bias-calculation, prior-alignment-bound):
`I_A, I_B ≤ 2p(t₀ + s₀)/m` with `t₀ = log(1/p)`,
`s₀ = |D|·log(|A||B|)`, `m = n − |D|` — for any generalized-family
arena satisfying both entropy budgets (batch #13), any `[0,1]`-weight,
and the hypothesis-pinned weighted core mass. The proof consumes the
signed reverse experiments (batch #11), the reveal-martingale tower
(batch #14), the budgets telescoped at the uniform cut, and the
weighted accepted-word entropy (`finite_weighted_entropy_le_of_weight_bound`). -/
theorem prior_alignment_bound
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (hcol : R.ColEntropyBudget) (hrow : R.RowEntropyBudget)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p)
    (hm : D.card < n) :
    S.alignCostA R D μ w
        ≤ 2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
            Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) /
          ((n : ℝ) - D.card) ∧
    S.alignCostB R D μ w
        ≤ 2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
            Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) /
          ((n : ℝ) - D.card) := by
  -- Proof layer: Prerounding/PriorAlignment.lean (the reverse datum as
  -- (base, uniform cut), the cut-sum telescoped into the column/row budget,
  -- and the size-bias entropy step `∑ w h = p`, `∑ w ≤ (|A||B|)^|D|`).
  refine ⟨?_, ?_⟩
  · exact S.alignSumA_le μ hμ hμsum R htotF htotG hcol w hw0 hw1 hwD hp hppos hm
  · exact S.alignSumB_le μ hμ hμsum R htotF htotG hrow w hw0 hw1 hwD hp hppos hm

/-- **The posterior branch law** `ℚ` (05_prerounding.tex, eq
posterior-branch-law): reveal randomness times prior questions times
the weight times the exact branch mass `‖φ_{r,x,y}‖²`, divided by `p`.
Junk-free consumption: every use divides by the hypothesis-pinned
positive `p`. -/
noncomputable def posteriorQ
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ)
    (t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B))) :
    ℝ :=
  t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
    w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
    ‖R.branch S.σ
        (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
        (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2 / p

/-- **Posterior normalization** (eq posterior-branch-normalization):
the branch-norm identity and the tower property make `ℚ` a probability
law — the branch mass at the full labels is exactly the conditional
core-word correlation, so the total mass is `p/p = 1`. -/
theorem posteriorQ_sum
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s : ALabel n X Y A,
      (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t : BLabel n X Y B,
      (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ} (hp : p = S.coreMass D μ w) (hppos : 0 < p)
    (hm : D.card < n) :
    (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
        (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t) = 1 := by
  classical
  -- Generic finite-sum reorderings.
  have hswap3 : ∀ (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ]
      (F : α → β → γ → ℝ),
      (∑ a : α, ∑ b : β, ∑ c : γ, F a b c)
        = ∑ c : γ, ∑ a : α, ∑ b : β, F a b c := by
    intro α β γ _ _ _ F
    calc (∑ a : α, ∑ b : β, ∑ c : γ, F a b c)
        = ∑ a : α, ∑ c : γ, ∑ b : β, F a b c :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c : γ, ∑ a : α, ∑ b : β, F a b c := Finset.sum_comm
  have hswap4 : ∀ (α β γ δ : Type) [Fintype α] [Fintype β] [Fintype γ]
      [Fintype δ] (F : α → β → γ → δ → ℝ),
      (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, F a b c d)
        = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, F a b c d := by
    intro α β γ δ _ _ _ _ F
    calc (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, F a b c d)
        = ∑ a : α, ∑ c : γ, ∑ b : β, ∑ d : δ, F a b c d :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c : γ, ∑ a : α, ∑ b : β, ∑ d : δ, F a b c d := Finset.sum_comm
      _ = ∑ c : γ, ∑ a : α, ∑ d : δ, ∑ b : β, F a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl
            fun a _ => Finset.sum_comm
      _ = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, F a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
  -- Scalar cancellation with a junk-guard at vanishing one-sided masses.
  have halg : ∀ m1 m2 pin w0 tt : ℝ, (m1 = 0 → tt = 0) → (m2 = 0 → tt = 0) →
      w0 * (pin * tt) = (pin * (m1 * m2)) * (w0 * ((m1⁻¹ * m2⁻¹) * tt)) := by
    intro m1 m2 pin w0 tt h1 h2
    by_cases hm1 : m1 = 0
    · rw [h1 hm1]; ring
    · by_cases hm2 : m2 = 0
      · rw [h2 hm2]; ring
      · rw [show (pin * (m1 * m2)) * (w0 * ((m1⁻¹ * m2⁻¹) * tt))
            = (m1 * m1⁻¹) * ((m2 * m2⁻¹) * (w0 * (pin * tt))) from by ring,
          mul_inv_cancel₀ hm1, mul_inv_cancel₀ hm2, one_mul, one_mul]
  -- Canonicalized labels read back to the raw reference words.
  have hcanA : ∀ (R₀ : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
      (zA : Fin n → A),
      S.setEffectA D R₀ μ (keepOn R₀ xw) (keepOff R₀ yw) zA
        = S.setEffectA D R₀ μ xw yw zA := by
    intro R₀ xw yw zA
    have hw : setWeightX R₀ μ (keepOn R₀ xw) (keepOff R₀ yw)
        = setWeightX R₀ μ xw yw := by
      funext u
      simp only [setWeightX]
      have hkeep : ∀ j ∈ R₀, keepOn R₀ xw j = xw j := fun j hj => by
        simp only [keepOn, if_pos hj]
      have hiff : agreesOn R₀ u (keepOn R₀ xw) ↔ agreesOn R₀ u xw :=
        ⟨fun h j hj => (h j hj).trans (hkeep j hj),
         fun h j hj => (h j hj).trans (hkeep j hj).symm⟩
      have hprod : (∏ j ∈ R₀ᶜ, μ (u j) (keepOff R₀ yw j))
          = ∏ j ∈ R₀ᶜ, μ (u j) (yw j) :=
        Finset.prod_congr rfl fun j hj => by
          simp only [keepOff, if_neg (Finset.mem_compl.mp hj)]
      rw [if_congr hiff hprod rfl]
    simp only [setEffectA]
    rw [hw]
  have hcanB : ∀ (R₀ : Finset (Fin n)) (xw : Fin n → X) (yw : Fin n → Y)
      (zB : Fin n → B),
      S.setEffectB D R₀ μ (keepOff R₀ xw) (keepOn R₀ yw) zB
        = S.setEffectB D R₀ μ xw yw zB := by
    intro R₀ xw yw zB
    have hw : setWeightY R₀ μ (keepOff R₀ xw) (keepOn R₀ yw)
        = setWeightY R₀ μ xw yw := by
      funext v
      simp only [setWeightY]
      have hkeep : ∀ j ∈ R₀, keepOn R₀ yw j = yw j := fun j hj => by
        simp only [keepOn, if_pos hj]
      have hiff : agreesOn R₀ v (keepOn R₀ yw) ↔ agreesOn R₀ v yw :=
        ⟨fun h j hj => (h j hj).trans (hkeep j hj),
         fun h j hj => (h j hj).trans (hkeep j hj).symm⟩
      have hprod : (∏ j ∈ R₀ᶜ, μ (keepOff R₀ xw j) (v j))
          = ∏ j ∈ R₀ᶜ, μ (xw j) (v j) :=
        Finset.prod_congr rfl fun j hj => by
          simp only [keepOff, if_neg (Finset.mem_compl.mp hj)]
      rw [if_congr hiff hprod rfl]
    simp only [setEffectB]
    rw [hw]
  -- Branch mass at the full canonical labels = effective-effect pairing.
  have hbranch : ∀ (r : RevealDatum n D) (xw : Fin n → X) (yw : Fin n → Y)
      (za : {j : Fin n // j ∈ D} → A) (zb : {j : Fin n // j ∈ D} → B),
      ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw za)
          (bLabel D (insert r.i r.CY) xw yw zb)‖ ^ 2
        = (S.M.τ (star S.σ *
            (S.effectiveH r μ xw yw (extendCoreA D za) * S.σ *
              S.effectiveK r μ xw yw (extendCoreB D zb)))).re := by
    intro r xw yw za zb
    have htF : (∑ a : Af, Ffam (aLabel D (insert r.i r.CX) xw yw za) a)
        = S.setEffectA D (insert r.i r.CX) μ (keepOn (insert r.i r.CX) xw)
            (keepOff (insert r.i r.CX) yw) (extendCoreA D za) :=
      htotF (aLabel D (insert r.i r.CX) xw yw za)
    have htG : (∑ b : Bf, Gfam (bLabel D (insert r.i r.CY) xw yw zb) b)
        = S.setEffectB D (insert r.i r.CY) μ (keepOff (insert r.i r.CY) xw)
            (keepOn (insert r.i r.CY) yw) (extendCoreB D zb) :=
      htotG (bLabel D (insert r.i r.CY) xw yw zb)
    have hb := R.branch_norm S.σ (aLabel D (insert r.i r.CX) xw yw za)
      (bLabel D (insert r.i r.CY) xw yw zb)
    rw [htF, htG, hcanA, hcanB,
      ← S.effectiveH_eq_setEffectA r μ xw yw (extendCoreA D za),
      ← S.effectiveK_eq_setEffectB r μ xw yw (extendCoreB D zb),
      inner_self_eq_norm_sq_to_K] at hb
    rw [← hb]
    norm_cast
  -- Per-datum collapse of the posterior inner sum to the core mass.
  have hcollapse : ∀ r : RevealDatum n D,
      (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          r.revealLaw * (∏ j : Fin n, μ (xw j) (yw j)) *
            w xw yw zD.1 zD.2 *
            ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
              (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 / p)
        = r.revealLaw * S.coreMass D μ w / p := by
    intro r
    have hDcx : D ⊆ insert r.i r.CX := fun j hj =>
      Finset.mem_insert_of_mem (Finset.mem_inter.mp (r.core_subset hj)).1
    have hDcy : D ⊆ insert r.i r.CY := fun j hj =>
      Finset.mem_insert_of_mem (Finset.mem_inter.mp (r.core_subset hj)).2
    have hcovX : ∀ j : Fin n, j ∉ insert r.i r.CX → j ∈ insert r.i r.CY := by
      intro j hj
      have hji : j ≠ r.i := by
        rintro rfl
        exact hj (Finset.mem_insert_self _ _)
      have hmem : j ∈ r.CX ∪ r.CY := by
        rw [r.union_eq_compl_singleton]
        simpa using hji
      rcases Finset.mem_union.mp hmem with h | h
      · exact absurd (Finset.mem_insert_of_mem h) hj
      · exact Finset.mem_insert_of_mem h
    have hcovY : ∀ j : Fin n, j ∉ insert r.i r.CY → j ∈ insert r.i r.CX := by
      intro j hj
      have hji : j ≠ r.i := by
        rintro rfl
        exact hj (Finset.mem_insert_self _ _)
      have hmem : j ∈ r.CX ∪ r.CY := by
        rw [r.union_eq_compl_singleton]
        simpa using hji
      rcases Finset.mem_union.mp hmem with h | h
      · exact Finset.mem_insert_of_mem h
      · exact absurd (Finset.mem_insert_of_mem h) hj
    -- One-sided weights read the reference pair only through its
    -- revealed values.
    have hxWeq : ∀ (x x₀ : Fin n → X) (y y₀ : Fin n → Y),
        agreesOn (insert r.i r.CX) x x₀ →
        agreesOn (insert r.i r.CY) y y₀ →
        r.xWeight μ x y = r.xWeight μ x₀ y₀ := by
      intro x x₀ y y₀ hx hy
      funext u
      simp only [RevealDatum.xWeight]
      have hiff : agreesOn (insert r.i r.CX) u x
          ↔ agreesOn (insert r.i r.CX) u x₀ :=
        ⟨fun h j hj => (h j hj).trans (hx j hj),
         fun h j hj => (h j hj).trans (hx j hj).symm⟩
      have hprod : (∏ j ∈ (insert r.i r.CX)ᶜ, μ (u j) (y j))
          = ∏ j ∈ (insert r.i r.CX)ᶜ, μ (u j) (y₀ j) :=
        Finset.prod_congr rfl fun j hj => by
          rw [hy j (hcovX j (Finset.mem_compl.mp hj))]
      rw [if_congr hiff hprod rfl]
    have hyWeq : ∀ (x x₀ : Fin n → X) (y y₀ : Fin n → Y),
        agreesOn (insert r.i r.CX) x x₀ →
        agreesOn (insert r.i r.CY) y y₀ →
        r.yWeight μ x y = r.yWeight μ x₀ y₀ := by
      intro x x₀ y y₀ hx hy
      funext v
      simp only [RevealDatum.yWeight]
      have hiff : agreesOn (insert r.i r.CY) v y
          ↔ agreesOn (insert r.i r.CY) v y₀ :=
        ⟨fun h j hj => (h j hj).trans (hy j hj),
         fun h j hj => (h j hj).trans (hy j hj).symm⟩
      have hprod : (∏ j ∈ (insert r.i r.CY)ᶜ, μ (x j) (v j))
          = ∏ j ∈ (insert r.i r.CY)ᶜ, μ (x₀ j) (v j) :=
        Finset.prod_congr rfl fun j hj => by
          rw [hx j (hcovY j (Finset.mem_compl.mp hj))]
      rw [if_congr hiff hprod rfl]
    -- The reference-pair fiber counts are constant.
    have hnuX : ∀ x : Fin n → X,
        (∑ x₀ : Fin n → X,
          if agreesOn (insert r.i r.CX) x x₀ then (1 : ℝ) else 0)
        = ∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
            (Fintype.card X : ℝ)) := by
      intro x
      have hterm : ∀ x₀ : Fin n → X,
          (if agreesOn (insert r.i r.CX) x x₀ then (1 : ℝ) else 0)
          = ∏ j : Fin n, (if j ∈ insert r.i r.CX then
              (if x j = x₀ j then (1 : ℝ) else 0) else 1) := by
        intro x₀
        by_cases hag : agreesOn (insert r.i r.CX) x x₀
        · rw [if_pos hag]
          exact (Finset.prod_eq_one fun j _ => by
            by_cases hj : j ∈ insert r.i r.CX
            · rw [if_pos hj, if_pos (hag j hj)]
            · rw [if_neg hj]).symm
        · rw [if_neg hag]
          have hex : ∃ j ∈ insert r.i r.CX, ¬x j = x₀ j := by
            by_contra hcon
            exact hag fun j hj => Classical.byContradiction fun hne =>
              hcon ⟨j, hj, hne⟩
          obtain ⟨j, hjI, hne⟩ := hex
          exact (Finset.prod_eq_zero (Finset.mem_univ j)
            (by rw [if_pos hjI, if_neg hne])).symm
      rw [Finset.sum_congr rfl fun x₀ _ => hterm x₀]
      have hps := Finset.prod_univ_sum
        (fun _ : Fin n => (Finset.univ : Finset X))
        (fun j v => if j ∈ insert r.i r.CX then
          (if x j = v then (1 : ℝ) else 0) else 1)
      rw [Fintype.piFinset_univ] at hps
      rw [← hps]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j ∈ insert r.i r.CX
      · simp only [if_pos hj]
        rw [Finset.sum_ite_eq Finset.univ (x j) (fun _ => (1 : ℝ)),
          if_pos (Finset.mem_univ _)]
      · simp only [if_neg hj]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hnuY : ∀ y : Fin n → Y,
        (∑ y₀ : Fin n → Y,
          if agreesOn (insert r.i r.CY) y y₀ then (1 : ℝ) else 0)
        = ∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
            (Fintype.card Y : ℝ)) := by
      intro y
      have hterm : ∀ y₀ : Fin n → Y,
          (if agreesOn (insert r.i r.CY) y y₀ then (1 : ℝ) else 0)
          = ∏ j : Fin n, (if j ∈ insert r.i r.CY then
              (if y j = y₀ j then (1 : ℝ) else 0) else 1) := by
        intro y₀
        by_cases hag : agreesOn (insert r.i r.CY) y y₀
        · rw [if_pos hag]
          exact (Finset.prod_eq_one fun j _ => by
            by_cases hj : j ∈ insert r.i r.CY
            · rw [if_pos hj, if_pos (hag j hj)]
            · rw [if_neg hj]).symm
        · rw [if_neg hag]
          have hex : ∃ j ∈ insert r.i r.CY, ¬y j = y₀ j := by
            by_contra hcon
            exact hag fun j hj => Classical.byContradiction fun hne =>
              hcon ⟨j, hj, hne⟩
          obtain ⟨j, hjI, hne⟩ := hex
          exact (Finset.prod_eq_zero (Finset.mem_univ j)
            (by rw [if_pos hjI, if_neg hne])).symm
      rw [Finset.sum_congr rfl fun y₀ _ => hterm y₀]
      have hps := Finset.prod_univ_sum
        (fun _ : Fin n => (Finset.univ : Finset Y))
        (fun j v => if j ∈ insert r.i r.CY then
          (if y j = v then (1 : ℝ) else 0) else 1)
      rw [Fintype.piFinset_univ] at hps
      rw [← hps]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j ∈ insert r.i r.CY
      · simp only [if_pos hj]
        rw [Finset.sum_ite_eq Finset.univ (y j) (fun _ => (1 : ℝ)),
          if_pos (Finset.mem_univ _)]
      · simp only [if_neg hj]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hcount : ∀ (x : Fin n → X) (y : Fin n → Y),
        (∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y, priorWeight r μ x₀ y₀ x y)
        = (∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
            (Fintype.card X : ℝ))) *
          ((∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
            (Fintype.card Y : ℝ))) * ∏ j : Fin n, μ (x j) (y j)) := by
      intro x y
      have hterm : ∀ (x₀ : Fin n → X) (y₀ : Fin n → Y),
          priorWeight r μ x₀ y₀ x y
          = (if agreesOn (insert r.i r.CX) x x₀ then (1 : ℝ) else 0) *
            ((if agreesOn (insert r.i r.CY) y y₀ then (1 : ℝ) else 0) *
              ∏ j : Fin n, μ (x j) (y j)) := by
        intro x₀ y₀
        simp only [priorWeight]
        by_cases hx : agreesOn (insert r.i r.CX) x x₀
        · by_cases hy : agreesOn (insert r.i r.CY) y y₀
          · rw [if_pos ⟨hx, hy⟩, if_pos hx, if_pos hy, one_mul, one_mul]
          · rw [if_neg fun h => hy h.2, if_pos hx, if_neg hy]
            ring
        · rw [if_neg fun h => hx h.1, if_neg hx]
          ring
      calc (∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y, priorWeight r μ x₀ y₀ x y)
          = ∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y,
              (if agreesOn (insert r.i r.CX) x x₀ then (1 : ℝ) else 0) *
              ((if agreesOn (insert r.i r.CY) y y₀ then (1 : ℝ) else 0) *
                ∏ j : Fin n, μ (x j) (y j)) :=
            Finset.sum_congr rfl fun x₀ _ => Finset.sum_congr rfl
              fun y₀ _ => hterm x₀ y₀
        _ = (∑ x₀ : Fin n → X,
              if agreesOn (insert r.i r.CX) x x₀ then (1 : ℝ) else 0) *
            ((∑ y₀ : Fin n → Y,
              if agreesOn (insert r.i r.CY) y y₀ then (1 : ℝ) else 0) *
              ∏ j : Fin n, μ (x j) (y j)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun x₀ _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
        _ = (∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
              (Fintype.card X : ℝ))) *
            ((∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
              (Fintype.card Y : ℝ))) * ∏ j : Fin n, μ (x j) (y j)) := by
            rw [hnuX x, hnuY y]
    have hνX0 : (∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
        (Fintype.card X : ℝ))) ≠ 0 :=
      ne_of_gt (Finset.prod_pos fun j _ => by
        by_cases hj : j ∈ insert r.i r.CX
        · rw [if_pos hj]; exact one_pos
        · rw [if_neg hj]; exact_mod_cast Fintype.card_pos)
    have hνY0 : (∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
        (Fintype.card Y : ℝ))) ≠ 0 :=
      ne_of_gt (Finset.prod_pos fun j _ => by
        by_cases hj : j ∈ insert r.i r.CY
        · rw [if_pos hj]; exact one_pos
        · rw [if_neg hj]; exact_mod_cast Fintype.card_pos)
    -- The tower collapse at a fixed core word for a core-measurable
    -- weight: conditional pairing integrates to the plain pairing.
    have hkey : ∀ (zAf : Fin n → A) (zBf : Fin n → B)
        (W : (Fin n → X) → (Fin n → Y) → ℝ),
        (∀ (x x₀ : Fin n → X) (y y₀ : Fin n → Y),
          agreesOn D x x₀ → agreesOn D y y₀ → W x y = W x₀ y₀) →
        (∑ x : Fin n → X, ∑ y : Fin n → Y,
          (∏ j : Fin n, μ (x j) (y j)) * (W x y *
            (S.M.τ (star S.σ * (S.effectiveH r μ x y zAf * S.σ *
              S.effectiveK r μ x y zBf))).re))
        = ∑ x : Fin n → X, ∑ y : Fin n → Y,
            (∏ j : Fin n, μ (x j) (y j)) * (W x y *
              (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                S.coreEffectB D y zBf))).re) := by
      intro zAf zBf W hW
      have hfiber : ∀ (x₀ : Fin n → X) (y₀ : Fin n → Y),
          (∑ x : Fin n → X, ∑ y : Fin n → Y,
            priorWeight r μ x₀ y₀ x y * (W x y *
              (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                S.coreEffectB D y zBf))).re))
          = ∑ x : Fin n → X, ∑ y : Fin n → Y,
              priorWeight r μ x₀ y₀ x y * (W x y *
                (S.M.τ (star S.σ * (S.effectiveH r μ x y zAf * S.σ *
                  S.effectiveK r μ x y zBf))).re) := by
        intro x₀ y₀
        have hsupL : (∑ x : Fin n → X, ∑ y : Fin n → Y,
            priorWeight r μ x₀ y₀ x y * (W x y *
              (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                S.coreEffectB D y zBf))).re))
            = W x₀ y₀ * ∑ x : Fin n → X, ∑ y : Fin n → Y,
                priorWeight r μ x₀ y₀ x y *
                  (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                    S.coreEffectB D y zBf))).re := by
          calc (∑ x : Fin n → X, ∑ y : Fin n → Y,
              priorWeight r μ x₀ y₀ x y * (W x y *
                (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                  S.coreEffectB D y zBf))).re))
              = ∑ x : Fin n → X, ∑ y : Fin n → Y,
                  priorWeight r μ x₀ y₀ x y * (W x₀ y₀ *
                    (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                      S.coreEffectB D y zBf))).re) := by
                refine Finset.sum_congr rfl fun x _ =>
                  Finset.sum_congr rfl fun y _ => ?_
                by_cases hsup : agreesOn (insert r.i r.CX) x x₀ ∧
                    agreesOn (insert r.i r.CY) y y₀
                · rw [hW x x₀ y y₀ (fun j hj => hsup.1 j (hDcx hj))
                    (fun j hj => hsup.2 j (hDcy hj))]
                · rw [show priorWeight r μ x₀ y₀ x y = 0 from by
                    simp only [priorWeight]
                    rw [if_neg hsup], zero_mul, zero_mul]
            _ = W x₀ y₀ * ∑ x : Fin n → X, ∑ y : Fin n → Y,
                  priorWeight r μ x₀ y₀ x y *
                    (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                      S.coreEffectB D y zBf))).re := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun x _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun y _ => ?_
                ring
        have hsupR : (∑ x : Fin n → X, ∑ y : Fin n → Y,
            priorWeight r μ x₀ y₀ x y * (W x y *
              (S.M.τ (star S.σ * (S.effectiveH r μ x y zAf * S.σ *
                S.effectiveK r μ x y zBf))).re))
            = (∑ x : Fin n → X, ∑ y : Fin n → Y,
                priorWeight r μ x₀ y₀ x y) *
              (W x₀ y₀ *
                (S.M.τ (star S.σ * (S.effectiveH r μ x₀ y₀ zAf * S.σ *
                  S.effectiveK r μ x₀ y₀ zBf))).re) := by
          calc (∑ x : Fin n → X, ∑ y : Fin n → Y,
              priorWeight r μ x₀ y₀ x y * (W x y *
                (S.M.τ (star S.σ * (S.effectiveH r μ x y zAf * S.σ *
                  S.effectiveK r μ x y zBf))).re))
              = ∑ x : Fin n → X, ∑ y : Fin n → Y,
                  priorWeight r μ x₀ y₀ x y * (W x₀ y₀ *
                    (S.M.τ (star S.σ * (S.effectiveH r μ x₀ y₀ zAf * S.σ *
                      S.effectiveK r μ x₀ y₀ zBf))).re) := by
                refine Finset.sum_congr rfl fun x _ =>
                  Finset.sum_congr rfl fun y _ => ?_
                by_cases hsup : agreesOn (insert r.i r.CX) x x₀ ∧
                    agreesOn (insert r.i r.CY) y y₀
                · rw [hW x x₀ y y₀ (fun j hj => hsup.1 j (hDcx hj))
                      (fun j hj => hsup.2 j (hDcy hj)),
                    show S.effectiveH r μ x y zAf
                        = S.effectiveH r μ x₀ y₀ zAf from by
                      simp only [effectiveH]
                      rw [hxWeq x x₀ y y₀ hsup.1 hsup.2],
                    show S.effectiveK r μ x y zBf
                        = S.effectiveK r μ x₀ y₀ zBf from by
                      simp only [effectiveK]
                      rw [hyWeq x x₀ y y₀ hsup.1 hsup.2]]
                · rw [show priorWeight r μ x₀ y₀ x y = 0 from by
                    simp only [priorWeight]
                    rw [if_neg hsup], zero_mul, zero_mul]
            _ = (∑ x : Fin n → X, ∑ y : Fin n → Y,
                  priorWeight r μ x₀ y₀ x y) *
                (W x₀ y₀ *
                  (S.M.τ (star S.σ * (S.effectiveH r μ x₀ y₀ zAf * S.σ *
                    S.effectiveK r μ x₀ y₀ zBf))).re) := by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun x _ => (Finset.sum_mul _ _ _).symm
        have hbp : (∑ x : Fin n → X, ∑ y : Fin n → Y,
            priorWeight r μ x₀ y₀ x y *
              (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                S.coreEffectB D y zBf))).re)
            = r.pinnedWeight μ x₀ y₀ *
              (S.M.τ (star S.σ *
                ((∑ x : Fin n → X, ((r.xWeight μ x₀ y₀ x : ℝ) : ℂ) •
                    S.coreEffectA D x zAf) * S.σ *
                  (∑ y : Fin n → Y, ((r.yWeight μ x₀ y₀ y : ℝ) : ℂ) •
                    S.coreEffectB D y zBf)))).re := by
          rw [← S.branch_probability_core r μ x₀ y₀ zAf zBf]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
            fun y _ => by rw [S.coreEffect_correlation D x y zAf zBf]
        have hmass := r.priorWeight_mass_eq μ x₀ y₀
        have hEexp : (S.M.τ (star S.σ * (S.effectiveH r μ x₀ y₀ zAf * S.σ *
              S.effectiveK r μ x₀ y₀ zBf))).re
            = ((∑ x : Fin n → X, r.xWeight μ x₀ y₀ x)⁻¹ *
               (∑ y : Fin n → Y, r.yWeight μ x₀ y₀ y)⁻¹) *
              (S.M.τ (star S.σ *
                ((∑ x : Fin n → X, ((r.xWeight μ x₀ y₀ x : ℝ) : ℂ) •
                    S.coreEffectA D x zAf) * S.σ *
                  (∑ y : Fin n → Y, ((r.yWeight μ x₀ y₀ y : ℝ) : ℂ) •
                    S.coreEffectB D y zBf)))).re := by
          simp only [effectiveH, effectiveK, weightedAvg]
          rw [← Complex.ofReal_inv, ← Complex.ofReal_inv,
            smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
            mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
            Complex.re_ofReal_mul, Complex.re_ofReal_mul]
          ring
        have hTT0x : (∑ x : Fin n → X, r.xWeight μ x₀ y₀ x) = 0 →
            (S.M.τ (star S.σ *
              ((∑ x : Fin n → X, ((r.xWeight μ x₀ y₀ x : ℝ) : ℂ) •
                  S.coreEffectA D x zAf) * S.σ *
                (∑ y : Fin n → Y, ((r.yWeight μ x₀ y₀ y : ℝ) : ℂ) •
                  S.coreEffectB D y zBf)))).re = 0 := by
          intro hMx
          have hz := (Finset.sum_eq_zero_iff_of_nonneg
            (fun x _ => r.xWeight_nonneg μ hμ x₀ y₀ x)).mp hMx
          have hSA : (∑ x : Fin n → X, ((r.xWeight μ x₀ y₀ x : ℝ) : ℂ) •
              S.coreEffectA D x zAf) = 0 :=
            Finset.sum_eq_zero fun x hx => by
              rw [hz x hx, Complex.ofReal_zero, zero_smul]
          rw [hSA, zero_mul, zero_mul, mul_zero, map_zero, Complex.zero_re]
        have hTT0y : (∑ y : Fin n → Y, r.yWeight μ x₀ y₀ y) = 0 →
            (S.M.τ (star S.σ *
              ((∑ x : Fin n → X, ((r.xWeight μ x₀ y₀ x : ℝ) : ℂ) •
                  S.coreEffectA D x zAf) * S.σ *
                (∑ y : Fin n → Y, ((r.yWeight μ x₀ y₀ y : ℝ) : ℂ) •
                  S.coreEffectB D y zBf)))).re = 0 := by
          intro hMy
          have hz := (Finset.sum_eq_zero_iff_of_nonneg
            (fun y _ => r.yWeight_nonneg μ hμ x₀ y₀ y)).mp hMy
          have hSB : (∑ y : Fin n → Y, ((r.yWeight μ x₀ y₀ y : ℝ) : ℂ) •
              S.coreEffectB D y zBf) = 0 :=
            Finset.sum_eq_zero fun y hy => by
              rw [hz y hy, Complex.ofReal_zero, zero_smul]
          rw [hSB, mul_zero, mul_zero, map_zero, Complex.zero_re]
        rw [hsupL, hsupR, hbp, hmass, hEexp]
        exact halg _ _ _ _ _ hTT0x hTT0y
      -- Aggregate the fiber identity over all reference pairs; the
      -- fiber count is a positive constant, so it cancels.
      have hside : ∀ Q : (Fin n → X) → (Fin n → Y) → ℝ,
          (∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y, ∑ x : Fin n → X,
            ∑ y : Fin n → Y,
              priorWeight r μ x₀ y₀ x y * (W x y * Q x y))
          = (∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
              (Fintype.card X : ℝ))) *
            ((∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
              (Fintype.card Y : ℝ))) *
              ∑ x : Fin n → X, ∑ y : Fin n → Y,
                (∏ j : Fin n, μ (x j) (y j)) * (W x y * Q x y)) := by
        intro Q
        calc (∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y, ∑ x : Fin n → X,
            ∑ y : Fin n → Y,
              priorWeight r μ x₀ y₀ x y * (W x y * Q x y))
            = ∑ x : Fin n → X, ∑ y : Fin n → Y, ∑ x₀ : Fin n → X,
                ∑ y₀ : Fin n → Y,
                  priorWeight r μ x₀ y₀ x y * (W x y * Q x y) :=
              hswap4 _ _ _ _ _
          _ = ∑ x : Fin n → X, ∑ y : Fin n → Y,
                (∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y,
                  priorWeight r μ x₀ y₀ x y) * (W x y * Q x y) := by
              refine Finset.sum_congr rfl fun x _ =>
                Finset.sum_congr rfl fun y _ => ?_
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun x₀ _ => (Finset.sum_mul _ _ _).symm
          _ = ∑ x : Fin n → X, ∑ y : Fin n → Y,
                ((∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
                    (Fintype.card X : ℝ))) *
                  ((∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
                    (Fintype.card Y : ℝ))) *
                    ∏ j : Fin n, μ (x j) (y j))) * (W x y * Q x y) :=
              Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
                fun y _ => by rw [hcount x y]
          _ = (∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
                (Fintype.card X : ℝ))) *
              ((∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
                (Fintype.card Y : ℝ))) *
                ∑ x : Fin n → X, ∑ y : Fin n → Y,
                  (∏ j : Fin n, μ (x j) (y j)) * (W x y * Q x y)) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              ring
      have hL : (∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y, ∑ x : Fin n → X,
          ∑ y : Fin n → Y,
            priorWeight r μ x₀ y₀ x y * (W x y *
              (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                S.coreEffectB D y zBf))).re))
          = (∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
              (Fintype.card X : ℝ))) *
            ((∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
              (Fintype.card Y : ℝ))) *
              ∑ x : Fin n → X, ∑ y : Fin n → Y,
                (∏ j : Fin n, μ (x j) (y j)) * (W x y *
                  (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
                    S.coreEffectB D y zBf))).re)) :=
        hside fun x y => (S.M.τ (star S.σ * (S.coreEffectA D x zAf * S.σ *
          S.coreEffectB D y zBf))).re
      have hR : (∑ x₀ : Fin n → X, ∑ y₀ : Fin n → Y, ∑ x : Fin n → X,
          ∑ y : Fin n → Y,
            priorWeight r μ x₀ y₀ x y * (W x y *
              (S.M.τ (star S.σ * (S.effectiveH r μ x y zAf * S.σ *
                S.effectiveK r μ x y zBf))).re))
          = (∏ j : Fin n, (if j ∈ insert r.i r.CX then (1 : ℝ) else
              (Fintype.card X : ℝ))) *
            ((∏ j : Fin n, (if j ∈ insert r.i r.CY then (1 : ℝ) else
              (Fintype.card Y : ℝ))) *
              ∑ x : Fin n → X, ∑ y : Fin n → Y,
                (∏ j : Fin n, μ (x j) (y j)) * (W x y *
                  (S.M.τ (star S.σ * (S.effectiveH r μ x y zAf * S.σ *
                    S.effectiveK r μ x y zBf))).re)) :=
        hside fun x y => (S.M.τ (star S.σ * (S.effectiveH r μ x y zAf * S.σ *
          S.effectiveK r μ x y zBf))).re
      exact (mul_left_cancel₀ hνY0 (mul_left_cancel₀ hνX0 (by
        rw [← hL, ← hR]
        exact Finset.sum_congr rfl fun x₀ _ => Finset.sum_congr rfl
          fun y₀ _ => hfiber x₀ y₀))).symm
    -- Assemble the per-datum collapse.
    calc (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          r.revealLaw * (∏ j : Fin n, μ (xw j) (yw j)) *
            w xw yw zD.1 zD.2 *
            ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
              (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 / p)
        = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              r.revealLaw / p * ((∏ j : Fin n, μ (xw j) (yw j)) *
                (w xw yw zD.1 zD.2 *
                  (S.M.τ (star S.σ *
                    (S.effectiveH r μ xw yw (extendCoreA D zD.1) * S.σ *
                      S.effectiveK r μ xw yw
                        (extendCoreB D zD.2)))).re)) :=
          Finset.sum_congr rfl fun xw _ => Finset.sum_congr rfl
            fun yw _ => Finset.sum_congr rfl fun zD _ => by
              rw [hbranch r xw yw zD.1 zD.2]; ring
      _ = r.revealLaw / p * ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              (∏ j : Fin n, μ (xw j) (yw j)) *
                (w xw yw zD.1 zD.2 *
                  (S.M.τ (star S.σ *
                    (S.effectiveH r μ xw yw (extendCoreA D zD.1) * S.σ *
                      S.effectiveK r μ xw yw (extendCoreB D zD.2)))).re) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun xw _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun yw _ => ?_
          rw [Finset.mul_sum]
      _ = r.revealLaw / p *
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
                (∏ j : Fin n, μ (xw j) (yw j)) *
                  (w xw yw zD.1 zD.2 *
                    (S.M.τ (star S.σ *
                      (S.effectiveH r μ xw yw (extendCoreA D zD.1) * S.σ *
                        S.effectiveK r μ xw yw
                          (extendCoreB D zD.2)))).re) :=
          congrArg (fun z => r.revealLaw / p * z) (hswap3 _ _ _ _)
      _ = r.revealLaw / p *
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
                (∏ j : Fin n, μ (xw j) (yw j)) *
                  (w xw yw zD.1 zD.2 *
                    (S.M.τ (star S.σ *
                      (S.coreEffectA D xw (extendCoreA D zD.1) * S.σ *
                        S.coreEffectB D yw
                          (extendCoreB D zD.2)))).re) :=
          congrArg (fun z => r.revealLaw / p * z)
            (Finset.sum_congr rfl fun zD _ =>
              hkey (extendCoreA D zD.1) (extendCoreB D zD.2)
                (fun x y => w x y zD.1 zD.2)
                (fun x x₀ y y₀ hx hy => hwD x x₀ y y₀ zD.1 zD.2 hx hy))
      _ = r.revealLaw / p * ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              (∏ j : Fin n, μ (xw j) (yw j)) *
                (w xw yw zD.1 zD.2 *
                  (S.M.τ (star S.σ *
                    (S.coreEffectA D xw (extendCoreA D zD.1) * S.σ *
                      S.coreEffectB D yw (extendCoreB D zD.2)))).re) :=
          congrArg (fun z => r.revealLaw / p * z) (hswap3 _ _ _ _).symm
      _ = r.revealLaw / p * S.coreMass D μ w :=
          congrArg (fun z => r.revealLaw / p * z) (by
            simp only [coreMass]
            refine Finset.sum_congr rfl fun xw _ =>
              Finset.sum_congr rfl fun yw _ => ?_
            rw [Finset.mul_sum])
      _ = r.revealLaw * S.coreMass D μ w / p := by ring
  -- Flatten, collapse per datum, and normalize by the reveal law.
  calc (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
        (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t)
      = ∑ r : RevealDatum n D, ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            r.revealLaw * (∏ j : Fin n, μ (xw j) (yw j)) *
              w xw yw zD.1 zD.2 *
              ‖R.branch S.σ (aLabel D (insert r.i r.CX) xw yw zD.1)
                (bLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 / p := by
        simp only [posteriorQ, Fintype.sum_prod_type]
    _ = ∑ r : RevealDatum n D, r.revealLaw * S.coreMass D μ w / p :=
        Finset.sum_congr rfl fun r _ => hcollapse r
    _ = 1 := by
        rw [← Finset.sum_div, ← Finset.sum_mul,
          RevealDatum.revealLaw_sum hm, one_mul, ← hp, div_self hppos.ne']

/-- **Posterior alignment, Bob-candidate side** (node 1.2.9;
05_prerounding.tex, eqs prerounding-normalization-inequality,
two-alignment-bounds): multiplying the normalization inequality by `ℚ`
cancels the ideal branch mass, so the posterior expected squared
distance between the normalized candidates `u_{st}` and `y_{i,r,y}` is
at most `4·I_A/p`. -/
theorem posterior_alignment_A
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    {p : ℝ} (hppos : 0 < p) :
    (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
        (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t *
        ‖R.candidate S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ
              (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2)
      ≤ 4 * S.alignCostA R D μ w / p := by
  have hcore : ∀ (v u : R.N.H),
      ‖v‖ ^ 2 * ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖u‖⁻¹ : ℝ) : ℂ) • u‖ ^ 2
        ≤ 4 * ‖v - u‖ ^ 2 := by
    intro v u
    by_cases hv : v = 0
    · subst hv
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, zero_sub]
      positivity
    by_cases hu : u = 0
    · subst hu
      have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp only [norm_zero, smul_zero, sub_zero]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        mul_pow, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hvn, one_pow, one_mul]
      nlinarith [sq_nonneg ‖v‖, norm_nonneg v, sq_abs ‖v‖]
    · have h := norm_normalize_sub_normalize_sq_le v u hv hu
      have hvpos : (0 : ℝ) < ‖v‖ ^ 2 := by
        have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        positivity
      calc ‖v‖ ^ 2 * ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖u‖⁻¹ : ℝ) : ℂ) • u‖ ^ 2
          ≤ ‖v‖ ^ 2 * (4 * ‖v - u‖ ^ 2 / ‖v‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h hvpos.le
        _ = 4 * ‖v - u‖ ^ 2 := by
            field_simp
  have hpoint : ∀ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t *
        ‖R.candidate S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ
              (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2
        ≤ 4 / p * (t.1.revealLaw *
            (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
            ‖R.branch S.σ
                (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
              - R.branch S.σ
                  (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
                  (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                    t.2.2.2.2)‖ ^ 2) := by
    intro t
    have hc0 : 0 ≤ t.1.revealLaw *
        (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
        w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 :=
      mul_nonneg (mul_nonneg t.1.revealLaw_nonneg
        (Finset.prod_nonneg fun j _ => hμ _ _)) (hw0 _ _ _ _)
    simp only [posteriorQ, ResolverArena.candidate]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hppos.le
    calc t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
          w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
          ‖R.branch S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2 * _
        = (t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) *
          (‖R.branch S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2 * _) := by ring
      _ ≤ (t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) *
          (4 * ‖R.branch S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
            - R.branch S.σ
                (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                  t.2.2.2.2)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hcore _ _) hc0
      _ = 4 * (t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
            ‖R.branch S.σ
                (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
              - R.branch S.σ
                  (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
                  (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                    t.2.2.2.2)‖ ^ 2) := by ring
  have hflat : (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
        w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
        ‖R.branch S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.branch S.σ
              (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2)
      = S.alignCostA R D μ w := by
    simp only [alignCostA, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl
      fun xw _ => Finset.sum_congr rfl fun yw _ =>
        Finset.sum_congr rfl fun zD _ => by ring
  calc (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t *
        ‖R.candidate S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ
              (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2)
      ≤ ∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
          (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
        4 / p * (t.1.revealLaw *
            (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
            ‖R.branch S.σ
                (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
              - R.branch S.σ
                  (aLabel D t.1.CX t.2.1 t.2.2.1 t.2.2.2.1)
                  (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                    t.2.2.2.2)‖ ^ 2) :=
        Finset.sum_le_sum fun t _ => hpoint t
    _ = 4 / p * S.alignCostA R D μ w := by
        rw [← Finset.mul_sum, hflat]
    _ = 4 * S.alignCostA R D μ w / p := by ring

/-- **Posterior alignment, Alice-candidate side** (mirror): distance to
`x_{i,r,x}` against `I_B`. -/
theorem posterior_alignment_B
    (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    {p : ℝ} (hppos : 0 < p) :
    (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
        (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t *
        ‖R.candidate S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2)
      ≤ 4 * S.alignCostB R D μ w / p := by
  have hcore : ∀ (v u : R.N.H),
      ‖v‖ ^ 2 * ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖u‖⁻¹ : ℝ) : ℂ) • u‖ ^ 2
        ≤ 4 * ‖v - u‖ ^ 2 := by
    intro v u
    by_cases hv : v = 0
    · subst hv
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, zero_sub]
      positivity
    by_cases hu : u = 0
    · subst hu
      have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp only [norm_zero, smul_zero, sub_zero]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        mul_pow, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hvn, one_pow, one_mul]
      nlinarith [sq_nonneg ‖v‖, norm_nonneg v, sq_abs ‖v‖]
    · have h := norm_normalize_sub_normalize_sq_le v u hv hu
      have hvpos : (0 : ℝ) < ‖v‖ ^ 2 := by
        have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        positivity
      calc ‖v‖ ^ 2 * ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ((‖u‖⁻¹ : ℝ) : ℂ) • u‖ ^ 2
          ≤ ‖v‖ ^ 2 * (4 * ‖v - u‖ ^ 2 / ‖v‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h hvpos.le
        _ = 4 * ‖v - u‖ ^ 2 := by
            field_simp
  have hpoint : ∀ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t *
        ‖R.candidate S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2
        ≤ 4 / p * (t.1.revealLaw *
            (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
            ‖R.branch S.σ
                (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
              - R.branch S.σ
                  (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                  (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2) := by
    intro t
    have hc0 : 0 ≤ t.1.revealLaw *
        (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
        w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 :=
      mul_nonneg (mul_nonneg t.1.revealLaw_nonneg
        (Finset.prod_nonneg fun j _ => hμ _ _)) (hw0 _ _ _ _)
    simp only [posteriorQ, ResolverArena.candidate]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hppos.le
    calc t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
          w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
          ‖R.branch S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2 * _
        = (t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) *
          (‖R.branch S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1
                t.2.2.2.2)‖ ^ 2 * _) := by ring
      _ ≤ (t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) *
          (4 * ‖R.branch S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
            - R.branch S.σ
                (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hcore _ _) hc0
      _ = 4 * (t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
            ‖R.branch S.σ
                (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
              - R.branch S.σ
                  (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                  (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2) := by ring
  have hflat : (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      t.1.revealLaw * (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
        w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
        ‖R.branch S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.branch S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2)
      = S.alignCostB R D μ w := by
    simp only [alignCostB, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl
      fun xw _ => Finset.sum_congr rfl fun yw _ =>
        Finset.sum_congr rfl fun zD _ => by ring
  calc (∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      S.posteriorQ R D μ w p t *
        ‖R.candidate S.σ
            (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
            (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
          - R.candidate S.σ
              (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
              (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2)
      ≤ ∑ t : RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
          (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
        4 / p * (t.1.revealLaw *
            (∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
            w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 *
            ‖R.branch S.σ
                (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                (bLabel D (insert t.1.i t.1.CY) t.2.1 t.2.2.1 t.2.2.2.2)
              - R.branch S.σ
                  (aLabel D (insert t.1.i t.1.CX) t.2.1 t.2.2.1 t.2.2.2.1)
                  (bLabel D t.1.CY t.2.1 t.2.2.1 t.2.2.2.2)‖ ^ 2) :=
        Finset.sum_le_sum fun t _ => hpoint t
    _ = 4 / p * S.alignCostB R D μ w := by
        rw [← Finset.mul_sum, hflat]
    _ = 4 * S.alignCostB R D μ w / p := by ring

end TracialStrategy

/-! ## Posterior histories (node 1.2.10, closeness half)

The flattened posterior over public histories and live questions, the
locally generated conditional laws, and the history relative-entropy
bound (05_prerounding.tex, eqs label-law-pi, J-A, J-B,
conditioning-divergence, question-answer-conditioning-budget,
JA-chain-rule, first-history-chain-term, bob-block-conditioning-budget,
bob-block-chain-rule, second-history-chain-term,
history-relative-entropy). The exact-seed half of node 1.2.10 is the
`Prelim/Seed.lean` sampler applied to the conditional laws below at
assembly time (node 1.2.11). The bound itself, `history_relative_entropy`,
is stated (verbatim, at its frozen hash) in `Prerounding/History.lean`,
which imports this file. -/

namespace TracialStrategy

variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-- The posterior tuple space: reveal datum, full reference words, core
word. -/
abbrev PostTuple (n : ℕ) (X Y A B : Type) (D : Finset (Fin n)) : Type :=
  RevealDatum n D × (Fin n → X) × (Fin n → Y) ×
    (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B))

/-- The public-history core of a posterior tuple (the manuscript's
`R = (i, T₀, Z)`, eq history-R): the reveal datum, the revealed
question values (kept on `C_X` resp. `C_Y` — the live values excluded,
since `i ∉ C_X ∪ C_Y`), and the core word. -/
noncomputable def histCore
    (t : PostTuple n X Y A B D) : PostTuple n X Y A B D :=
  (t.1, keepOn t.1.CX t.2.1, keepOn t.1.CY t.2.2.1, t.2.2.2)

/-- The flattening of a posterior tuple to (history, live questions)
(the tuple format of eqs J-A, J-B). -/
noncomputable def flattenPost (t : PostTuple n X Y A B D) :
    PostTuple n X Y A B D × X × Y :=
  (histCore t, t.2.1 t.1.i, t.2.2.1 t.1.i)

open Classical in
/-- The flattened posterior law `ℚ(R, x, y)` — the pushforward of
`posteriorQ` under `flattenPost` (classical decidability of tuple
equality is harmless: the law is noncomputable anyway). -/
noncomputable def flatQ
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (u : PostTuple n X Y A B D × X × Y) : ℝ :=
  ClassicalInformation.groupedMass (flattenPost (D := D)) (S.posteriorQ R D μ w p) u

/-- The conditional history law `ℚ(R = h ∣ i, X_i = x)` (eq J-A's
conditional): supported on histories whose datum has the given live
coordinate; junk value `0` at a vanishing posterior marginal
("Zero posterior marginals use one fixed default distribution" — the
default is chosen at assembly (node 1.2.11); the relative-entropy
statements below are unaffected because zero-marginal cells carry zero
`ℚ`-mass). -/
noncomputable def condQA
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (x : X) (h : PostTuple n X Y A B D) : ℝ :=
  if h.1.i = i₀ then
    (∑ y : Y, S.flatQ R D μ w p (h, x, y)) /
      (∑ h' : PostTuple n X Y A B D,
        if h'.1.i = i₀ then ∑ y : Y, S.flatQ R D μ w p (h', x, y) else 0)
  else 0

/-- The conditional history law `ℚ(R = h ∣ i, Y_i = y)` (eq J-B's
conditional, mirror). -/
noncomputable def condQB
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (i₀ : Fin n) (y : Y) (h : PostTuple n X Y A B D) : ℝ :=
  if h.1.i = i₀ then
    (∑ x : X, S.flatQ R D μ w p (h, x, y)) /
      (∑ h' : PostTuple n X Y A B D,
        if h'.1.i = i₀ then ∑ x : X, S.flatQ R D μ w p (h', x, y) else 0)
  else 0

/-- The locally generated Alice tuple law `J_A(R, x, y) = m⁻¹ μ(x,y)
ℚ(R ∣ i, X_i = x)` (eq J-A), in its defaultless form (zero at
zero-marginal cells; the assembly's fixed default redistributes only
mass that carries no `ℚ`-weight). -/
noncomputable def flatJA
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (u : PostTuple n X Y A B D × X × Y) : ℝ :=
  (((n - D.card : ℕ) : ℝ))⁻¹ * μ u.2.1 u.2.2 *
    S.condQA R D μ w p u.1.1.i u.2.1 u.1

/-- The locally generated Bob tuple law `J_B` (eq J-B, mirror). -/
noncomputable def flatJB
    {Ffam : ALabel n X Y A → Af → S.M.A}
    {Gfam : BLabel n X Y B → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (D : Finset (Fin n))
    (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (p : ℝ) (u : PostTuple n X Y A B D × X × Y) : ℝ :=
  (((n - D.card : ℕ) : ℝ))⁻¹ * μ u.2.1 u.2.2 *
    S.condQB R D μ w p u.1.1.i u.2.2 u.1

end TracialStrategy

end CommutingRepetition
