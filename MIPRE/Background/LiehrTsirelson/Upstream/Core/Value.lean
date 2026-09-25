/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core/Value.lean, from a snapshot of the `main` branch supplied on 2026-09-25 (archive,
no commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core.Strategy

/-!
# Payoff, the two game values, and their bounds

Sources: `Blueprint/Nodes/B23-Games/Parts/01-GamesAndStrategies.tex`,
`def:tensor-product-value`; `Blueprint/Nodes/B05-NPA-Core/Math.tex`, `def:n7b`
(the payoff `ω(G;ψ,A,B)`, the two suprema, and the game functional `ℓ_G`).

## The `sSup` carriers

`valStar G` is the supremum of `payoff G` over the **generic tensor correlation
set**, and `valCo G` over the **generic commuting correlation set**.  For a
square game these are `Cq n k` and `Cqc n k` definitionally, because the square
names are `abbrev` aliases.

`valStar` is deliberately **not** the supremum over the closure: that the closure
gives the same value is B30's topological bridge, which P00 must not pre-empt.

## Raw-array discipline

`Correlation X Y A B` is an arbitrary real array, so **no** unconditional
`[0,1]` payoff theorem is stated for it.  The two `payoff_mem_Icc_of_mem_*`
lemmas carry an explicit realization hypothesis; only realized strategy payoffs
and the two values are bounded unconditionally.
-/

namespace Tsirelson

noncomputable section

universe u v w z

variable {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The payoff of a correlation array against a game:
`∑_{x,y} μ(x,y) ∑_{a,b} D(x,y,a,b) p(a,b|x,y)`.

This is the game functional `ℓ_G` of `def:n7b`. -/
def payoff (G : NonlocalGame X Y A B) (p : Correlation X Y A B) : ℝ :=
  ∑ q : X × Y, G.questions.prob q * ∑ a, ∑ b, G.D q.1 q.2 a b * p q.1 q.2 a b

theorem payoff_eq_sum_sum (G : NonlocalGame X Y A B) (p : Correlation X Y A B) :
    payoff G p = ∑ x, ∑ y, G.questions.prob (x, y) * ∑ a, ∑ b, G.D x y a b * p x y a b := by
  rw [payoff, ← Finset.sum_product']
  rfl

/-- The inner decision sum of a *realized* correlation lies in `[0,1]`. -/
theorem inner_sum_mem_Icc (G : NonlocalGame X Y A B) {p : Correlation X Y A B}
    (hnn : ∀ x y a b, 0 ≤ p x y a b) (hsum : ∀ x y, ∑ a, ∑ b, p x y a b = 1) (x : X) (y : Y) :
    (∑ a, ∑ b, G.D x y a b * p x y a b) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (G.D_nonneg x y a b) (hnn x y a b)
  · rw [← hsum x y]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      mul_le_of_le_one_left (hnn x y a b) (G.D_le_one x y a b)

/-- **Realization-conditional payoff bound.**  A correlation array that is
pointwise nonnegative and normalized has payoff in `[0,1]`. -/
theorem payoff_mem_Icc_of_normalized (G : NonlocalGame X Y A B) {p : Correlation X Y A B}
    (hnn : ∀ x y a b, 0 ≤ p x y a b) (hsum : ∀ x y, ∑ a, ∑ b, p x y a b = 1) :
    payoff G p ∈ Set.Icc (0 : ℝ) 1 :=
  G.questions.sum_mul_mem_Icc
    (fun q => (inner_sum_mem_Icc G hnn hsum q.1 q.2).1)
    (fun q => (inner_sum_mem_Icc G hnn hsum q.1 q.2).2)

theorem payoff_mem_Icc_of_mem_tensorCorrelations (G : NonlocalGame X Y A B)
    {p : Correlation X Y A B} (hp : p ∈ TensorCorrelations X Y A B) :
    payoff G p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨S, rfl⟩ := hp
  exact payoff_mem_Icc_of_normalized G (fun x y a b => S.corr_nonneg x y a b)
    (fun x y => S.sum_corr x y)

theorem payoff_mem_Icc_of_mem_commutingCorrelations (G : NonlocalGame X Y A B)
    {p : Correlation X Y A B} (hp : p ∈ CommutingCorrelations X Y A B) :
    payoff G p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨S, rfl⟩ := hp
  exact payoff_mem_Icc_of_normalized G (fun x y a b => S.corr_nonneg x y a b)
    (fun x y => S.sum_corr x y)

/-! ## Strategy values -/

/-- The value of a tensor strategy: the payoff of its actual correlation. -/
def TensorStrategy.value (S : TensorStrategy X Y A B) (G : NonlocalGame X Y A B) : ℝ :=
  payoff G S.corr

/-- The value of a commuting strategy: the payoff of its actual correlation. -/
def CommutingStrategy.value (S : CommutingStrategy X Y A B) (G : NonlocalGame X Y A B) : ℝ :=
  payoff G S.corr

/-- A game has a value-one PCC strategy when an actual common-local-space
tensor strategy is PCC for the game and its canonical strategy value is
exactly one. -/
def NonlocalGame.HasValueOnePCC (G : NonlocalGame X Y A B) : Prop :=
  ∃ S : CommonTensorStrategy X Y A B,
    S.IsPCC G ∧ S.toTensorStrategy.value G = 1

/-- The dependently typed value-one PCC property for a bundled game
signature. -/
def GameSig.HasValueOnePCC (g : GameSig) : Prop :=
  g.game.HasValueOnePCC

theorem TensorStrategy.value_eq_payoff (S : TensorStrategy X Y A B)
    (G : NonlocalGame X Y A B) : S.value G = payoff G S.corr := rfl

theorem CommutingStrategy.value_eq_payoff (S : CommutingStrategy X Y A B)
    (G : NonlocalGame X Y A B) : S.value G = payoff G S.corr := rfl

theorem tensorStrategy_value_mem_Icc (S : TensorStrategy X Y A B)
    (G : NonlocalGame X Y A B) : S.value G ∈ Set.Icc (0 : ℝ) 1 :=
  payoff_mem_Icc_of_mem_tensorCorrelations G ⟨S, rfl⟩

theorem commutingStrategy_value_mem_Icc (S : CommutingStrategy X Y A B)
    (G : NonlocalGame X Y A B) : S.value G ∈ Set.Icc (0 : ℝ) 1 :=
  payoff_mem_Icc_of_mem_commutingCorrelations G ⟨S, rfl⟩

/-! ## The two game values -/

/-- The finite-dimensional (tensor-product) value: the supremum of the payoff over
the **generic tensor correlation set**.  Specializes to `Cq` for square games. -/
def valStar (G : NonlocalGame X Y A B) : ℝ :=
  sSup (payoff G '' TensorCorrelations X Y A B)

/-- The commuting-operator value: the supremum of the payoff over the **generic
commuting correlation set**.  Specializes to `Cqc` for square games. -/
def valCo (G : NonlocalGame X Y A B) : ℝ :=
  sSup (payoff G '' CommutingCorrelations X Y A B)

/-! ### Nonemptiness and boundedness, as required before any `csSup` reasoning -/

theorem tensorPayoffImage_nonempty (G : NonlocalGame X Y A B) :
    (payoff G '' TensorCorrelations X Y A B).Nonempty :=
  (tensorCorrelations_nonempty G.nonemptyA G.nonemptyB).image _

theorem commutingPayoffImage_nonempty (G : NonlocalGame X Y A B) :
    (payoff G '' CommutingCorrelations X Y A B).Nonempty :=
  (commutingCorrelations_nonempty G.nonemptyA G.nonemptyB).image _

theorem tensorPayoffImage_bddAbove (G : NonlocalGame X Y A B) :
    BddAbove (payoff G '' TensorCorrelations X Y A B) :=
  ⟨1, by rintro _ ⟨p, hp, rfl⟩; exact (payoff_mem_Icc_of_mem_tensorCorrelations G hp).2⟩

theorem commutingPayoffImage_bddAbove (G : NonlocalGame X Y A B) :
    BddAbove (payoff G '' CommutingCorrelations X Y A B) :=
  ⟨1, by rintro _ ⟨p, hp, rfl⟩; exact (payoff_mem_Icc_of_mem_commutingCorrelations G hp).2⟩

/-- Every realized tensor payoff is at most `valStar`. -/
theorem le_valStar_of_mem (G : NonlocalGame X Y A B) {p : Correlation X Y A B}
    (hp : p ∈ TensorCorrelations X Y A B) : payoff G p ≤ valStar G :=
  le_csSup (tensorPayoffImage_bddAbove G) ⟨p, hp, rfl⟩

/-- Every realized commuting payoff is at most `valCo`. -/
theorem le_valCo_of_mem (G : NonlocalGame X Y A B) {p : Correlation X Y A B}
    (hp : p ∈ CommutingCorrelations X Y A B) : payoff G p ≤ valCo G :=
  le_csSup (commutingPayoffImage_bddAbove G) ⟨p, hp, rfl⟩

theorem TensorStrategy.value_le_valStar (S : TensorStrategy X Y A B)
    (G : NonlocalGame X Y A B) : S.value G ≤ valStar G :=
  le_valStar_of_mem G ⟨S, rfl⟩

theorem CommutingStrategy.value_le_valCo (S : CommutingStrategy X Y A B)
    (G : NonlocalGame X Y A B) : S.value G ≤ valCo G :=
  le_valCo_of_mem G ⟨S, rfl⟩

theorem valStar_le_of_forall (G : NonlocalGame X Y A B) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ p ∈ TensorCorrelations X Y A B, payoff G p ≤ c) : valStar G ≤ c :=
  Real.sSup_le (by rintro _ ⟨p, hp, rfl⟩; exact h p hp) hc

theorem valCo_le_of_forall (G : NonlocalGame X Y A B) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ p ∈ CommutingCorrelations X Y A B, payoff G p ≤ c) : valCo G ≤ c :=
  Real.sSup_le (by rintro _ ⟨p, hp, rfl⟩; exact h p hp) hc

theorem valStar_mem_Icc (G : NonlocalGame X Y A B) : valStar G ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, valStar_le_of_forall G zero_le_one fun p hp =>
    (payoff_mem_Icc_of_mem_tensorCorrelations G hp).2⟩
  obtain ⟨v, hv⟩ := tensorPayoffImage_nonempty G
  obtain ⟨p, hp, rfl⟩ := hv
  exact le_trans (payoff_mem_Icc_of_mem_tensorCorrelations G hp).1 (le_valStar_of_mem G hp)

theorem valCo_mem_Icc (G : NonlocalGame X Y A B) : valCo G ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, valCo_le_of_forall G zero_le_one fun p hp =>
    (payoff_mem_Icc_of_mem_commutingCorrelations G hp).2⟩
  obtain ⟨v, hv⟩ := commutingPayoffImage_nonempty G
  obtain ⟨p, hp, rfl⟩ := hv
  exact le_trans (payoff_mem_Icc_of_mem_commutingCorrelations G hp).1 (le_valCo_of_mem G hp)

/-- For a square game the `valStar` carrier is literally `Cq n k`. -/
theorem valStar_square (n k : ℕ) (G : Game n k) :
    valStar G = sSup (payoff G '' Cq n k) := rfl

/-- For a square game the `valCo` carrier is literally `Cqc n k`. -/
theorem valCo_square (n k : ℕ) (G : Game n k) :
    valCo G = sSup (payoff G '' Cqc n k) := rfl

end

end Tsirelson
