/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import MIPRE.Foundations.Correlations
import MIPRE.Foundations.GNS
import MIPRE.Foundations.NCPoly.Cone

/-!
# The game algebra of Tsirelson's problem

The algebraic layer of the Tsirelson route (`planning/tsirelson-campaign.md`, §3.1–§3.2): the
free `⋆`-algebra of a two-player scenario with question sets `X`, `Y` and answer sets `A`, `B`,
its cone of positive elements, and the correspondence between commuting-operator strategies and
states on it.

**The algebra.** The letters are `Gen X Y A B = (X × A) ⊕ (Y × B)`, one self-adjoint letter
`eG x a` per effect of the first player and `fG y b` per effect of the second, and the algebra is
`NCPoly (Gen X Y A B)`. The relations `rels` are the two POVM normalisations `Σ_a e_xa - 1`,
`Σ_b f_yb - 1` and the cross commutators `e_xa f_yb - f_yb e_xa`; the cone `M = cone X Y A B` is
their quadratic module `NCPoly.qmod`. Every letter satisfies `1 - g ∈ M`
(`1 - e_xa = Σ_{a' ≠ a} e_xa' - (Σ_a' e_xa' - 1)`), hence `1 - g² ∈ M`
(`one_sub_gen_mul_gen_mem`), so `M` is Archimedean (`cone_archimedean`), and a polynomial
outside `M` is separated from it by a real functional (`exists_state_functional_of_not_mem`).

**Strategies.** A commuting-operator strategy `S` evaluates the letters at its effects
(`stratEval S`), which kills the relations, so every element of `M` has nonnegative expectation
in the strategy's state (`strategy_nonneg`). The correlation is the expectation of
`e_xa f_yb` (`correlation_eq`), and the value in a game `G` is the expectation of the game
polynomial `W_G = gamePoly G = Σ μ(x, y) [D x y a b] e_xa f_yb` (`value_eq`). Hence a cone
certificate `r·1 - W_G ∈ M` bounds every strategy's value, and the commuting-operator value, by
`r` (`value_le_of_mem`, `commutingOperatorValue_le_of_mem`). The latter is stated for `0 ≤ r`,
which lets it use `Real.iSup_le` without a nonemptiness hypothesis; it cannot be dropped: if `A`
is empty and `X` is not, then `-1 = Σ_a e_xa - 1` is a relation, the cone is the whole algebra,
and there is no strategy, so the value is `0`.
Every effect, and so every word, evaluates to a contraction (`norm_eval_single_one_le`).

**Cone states.** A *cone state* (`IsConeState`) is a `ℂ`-linear functional `L` with `L 1 = 1`
and `0 ≤ Re L m` for every `m ∈ M`. This single notion covers the three sources of states:

* the state `stateOf S : z ↦ ⟪ψ, π_S(z) ψ⟫` of a strategy is a cone state
  (`isConeState_stateOf`), bounded by `1` on words (`norm_stateOf_single_one_le`);
* the complexification `z ↦ L₀ z - i L₀ (i z)` of a real functional that is `1` at the unit and
  nonnegative on `M` is a cone state (`complexify`, `isConeState_complexify`), so a polynomial
  outside `M` is separated from it by a cone state (`exists_isConeState_of_not_mem`);
* a cone state is hermitian (`IsConeState.map_star`, since `z - z⋆` and `i (z + z⋆)` are
  anti-hermitian), vanishes on the relation ideal (`IsConeState.map_eq_zero_of_mem_relSpan`,
  since `±j, ±i j ∈ M`), and is positive on every `s⋆ g s`; so it is a `GNS.State` whose letters
  form `GNS.GenData`, and the GNS construction turns it into a commuting-operator strategy
  `stateStrategy hL` with correlation `Re L (e_xa f_yb)` and value `Re L (W_G)`
  (`stateStrategy_correlation`, `stateStrategy_value`).

Together: `C_qc` is exactly the set of the `Re L (e_xa f_yb)` over cone states `L`
(`mem_Cqc_iff`). The GNS part needs `X Y A B : Type`, since the Hilbert space of a
`CommutingOperatorStrategy` lives in `Type`.

Finally, the deterministic strategy on `ℂ` (`CommutingOperatorStrategy.deterministic`) makes the
type of strategies nonempty when both answer sets are
(`CommutingOperatorStrategy.instNonempty`), which uniform bounds over strategies need for
`ciSup_le`.

## Main declarations

* `Gen`, `eG`, `fG`, `rels`, `cone`, `one_sub_eG_mem`, `one_sub_fG_mem`,
  `one_sub_gen_mul_gen_mem`, `cone_archimedean`, `exists_state_functional_of_not_mem`;
* `stratEval`, `stratEval_rels`, `strategy_nonneg`, `correlation_eq`, `gamePoly`, `value_eq`,
  `value_le_of_mem`, `commutingOperatorValue_le_of_mem`;
* `stateOf`, `IsConeState`, `isConeState_stateOf`, `complexify`, `isConeState_complexify`,
  `exists_isConeState_of_not_mem`;
* `IsConeState.toState`, `IsConeState.genData`, `stateStrategy`, `stateStrategy_correlation`,
  `stateStrategy_value`, `re_gamePoly_le_commutingOperatorValue`, `mem_Cqc_iff`;
* `CommutingOperatorStrategy.deterministic`, `CommutingOperatorStrategy.norm_E_le_one`,
  `CommutingOperatorStrategy.norm_F_le_one`.
-/

noncomputable section

open ComplexConjugate
open scoped InnerProductSpace

namespace MIPRE

/-! ## The deterministic strategy, and contractions -/

namespace CommutingOperatorStrategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The deterministic strategy on `ℂ` that always answers `(a₀, b₀)`: every effect is `1` or
`0`. -/
def deterministic [DecidableEq A] [DecidableEq B] (a₀ : A) (b₀ : B) :
    CommutingOperatorStrategy X Y A B where
  H := ℂ
  ψ := 1
  ψ_norm := by simp
  E _ a := if a = a₀ then 1 else 0
  F _ b := if b = b₀ then 1 else 0
  E_pos _ a := by
    split_ifs
    · exact ContinuousLinearMap.isPositive_one
    · exact ContinuousLinearMap.isPositive_zero
  F_pos _ b := by
    split_ifs
    · exact ContinuousLinearMap.isPositive_one
    · exact ContinuousLinearMap.isPositive_zero
  E_sum _ := by simp
  F_sum _ := by simp
  commutes _ _ a b := by split_ifs <;> simp

/-- There is a commuting-operator strategy as soon as both answer sets are nonempty. -/
instance instNonempty [Nonempty A] [Nonempty B] :
    Nonempty (CommutingOperatorStrategy X Y A B) := by
  classical
  exact ⟨deterministic (Classical.arbitrary A) (Classical.arbitrary B)⟩

/-- Every effect of the first player is a contraction: `0 ≤ E x a ≤ 1`. -/
theorem norm_E_le_one (S : CommutingOperatorStrategy X Y A B) (x : X) (a : A) :
    ‖S.E x a‖ ≤ 1 := by
  have h0 : ∀ a', 0 ≤ S.E x a' := fun a' =>
    (ContinuousLinearMap.nonneg_iff_isPositive _).2 (S.E_pos x a')
  have hle : S.E x a ≤ 1 := by
    rw [← S.E_sum x]
    exact Finset.single_le_sum (fun a' _ => h0 a') (Finset.mem_univ a)
  calc ‖S.E x a‖ ≤ ‖(1 : S.H →L[ℂ] S.H)‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le (h0 a) hle
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

/-- Every effect of the second player is a contraction: `0 ≤ F y b ≤ 1`. -/
theorem norm_F_le_one (S : CommutingOperatorStrategy X Y A B) (y : Y) (b : B) :
    ‖S.F y b‖ ≤ 1 := by
  have h0 : ∀ b', 0 ≤ S.F y b' := fun b' =>
    (ContinuousLinearMap.nonneg_iff_isPositive _).2 (S.F_pos y b')
  have hle : S.F y b ≤ 1 := by
    rw [← S.F_sum y]
    exact Finset.single_le_sum (fun b' _ => h0 b') (Finset.mem_univ b)
  calc ‖S.F y b‖ ≤ ‖(1 : S.H →L[ℂ] S.H)‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le (h0 b) hle
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

end CommutingOperatorStrategy

namespace Tsirelson

/-! ## Letters, relations, and the cone -/

/-- The letters of the game algebra: one per effect `E x a` and one per effect `F y b`. -/
abbrev Gen (X Y A B : Type*) := (X × A) ⊕ (Y × B)

section Algebra

variable {X Y A B : Type*}

/-- The letter `e_xa`, standing for the first player's effect `E x a`. -/
def eG (x : X) (a : A) : NCPoly (Gen X Y A B) := NCPoly.gen (Sum.inl (x, a))

/-- The letter `f_yb`, standing for the second player's effect `F y b`. -/
def fG (y : Y) (b : B) : NCPoly (Gen X Y A B) := NCPoly.gen (Sum.inr (y, b))

/-- The letters `e_xa` are self-adjoint. -/
@[simp] theorem star_eG (x : X) (a : A) : star (eG (Y := Y) (B := B) x a) = eG x a :=
  NCPoly.star_gen _

/-- The letters `f_yb` are self-adjoint. -/
@[simp] theorem star_fG (y : Y) (b : B) : star (fG (X := X) (A := A) y b) = fG y b :=
  NCPoly.star_gen _

variable [Fintype A] [Fintype B]

variable (X Y A B) in
/-- The relations of the game algebra: both POVM normalisations `Σ_a e_xa - 1`,
`Σ_b f_yb - 1`, and the cross commutators `e_xa f_yb - f_yb e_xa`. -/
def rels : Set (NCPoly (Gen X Y A B)) :=
  Set.range (fun x : X => ∑ a, eG (Y := Y) (B := B) x a - 1) ∪
  Set.range (fun y : Y => ∑ b, fG (X := X) (A := A) y b - 1) ∪
  Set.range (fun p : X × Y × A × B =>
    eG p.1 p.2.2.1 * fG p.2.1 p.2.2.2 - fG p.2.1 p.2.2.2 * eG p.1 p.2.2.1)

variable (X Y A B) in
/-- The cone `M` of the game algebra: the quadratic module of `rels`. -/
abbrev cone : PointedCone ℝ (NCPoly (Gen X Y A B)) := NCPoly.qmod (rels X Y A B)

/-- The first player's normalisation lies in the relation ideal. -/
theorem sum_eG_sub_one_mem_relSpan (x : X) :
    ∑ a, eG (Y := Y) (B := B) x a - 1 ∈ NCPoly.relSpan (rels X Y A B) :=
  NCPoly.mem_relSpan_of_mem (Or.inl (Or.inl ⟨x, rfl⟩))

/-- The second player's normalisation lies in the relation ideal. -/
theorem sum_fG_sub_one_mem_relSpan (y : Y) :
    ∑ b, fG (X := X) (A := A) y b - 1 ∈ NCPoly.relSpan (rels X Y A B) :=
  NCPoly.mem_relSpan_of_mem (Or.inl (Or.inr ⟨y, rfl⟩))

/-- The cross commutators lie in the relation ideal. -/
theorem commutator_mem_relSpan (x : X) (y : Y) (a : A) (b : B) :
    eG x a * fG y b - fG y b * eG x a ∈ NCPoly.relSpan (rels X Y A B) :=
  NCPoly.mem_relSpan_of_mem (Or.inr ⟨(x, y, a, b), rfl⟩)

/-- `1 - e_xa ∈ M`: it is `Σ_{a' ≠ a} e_xa' - (Σ_a' e_xa' - 1)`. -/
theorem one_sub_eG_mem (x : X) (a : A) : 1 - eG (Y := Y) (B := B) x a ∈ cone X Y A B := by
  classical
  have hsum : ∑ a' ∈ Finset.univ.erase a, eG (Y := Y) (B := B) x a' ∈ cone X Y A B :=
    Submodule.sum_mem _ fun a' _ => NCPoly.gen_mem_qmod _
  have := Submodule.add_mem _ hsum
    (NCPoly.mem_qmod_of_mem_relSpan (Submodule.neg_mem _ (sum_eG_sub_one_mem_relSpan x)))
  convert this using 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  abel

/-- `1 - f_yb ∈ M`: it is `Σ_{b' ≠ b} f_yb' - (Σ_b' f_yb' - 1)`. -/
theorem one_sub_fG_mem (y : Y) (b : B) : 1 - fG (X := X) (A := A) y b ∈ cone X Y A B := by
  classical
  have hsum : ∑ b' ∈ Finset.univ.erase b, fG (X := X) (A := A) y b' ∈ cone X Y A B :=
    Submodule.sum_mem _ fun b' _ => NCPoly.gen_mem_qmod _
  have := Submodule.add_mem _ hsum
    (NCPoly.mem_qmod_of_mem_relSpan (Submodule.neg_mem _ (sum_fG_sub_one_mem_relSpan y)))
  convert this using 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  abel

/-- Every letter `g` of the game algebra satisfies `1 - g² ∈ M`. -/
theorem one_sub_gen_mul_gen_mem (g : Gen X Y A B) :
    1 - NCPoly.gen g * NCPoly.gen g ∈ cone X Y A B := by
  rcases g with ⟨x, a⟩ | ⟨y, b⟩
  · exact NCPoly.one_sub_gen_sq_mem (one_sub_eG_mem x a)
  · exact NCPoly.one_sub_gen_sq_mem (one_sub_fG_mem y b)

/-- **The Archimedean property of the game cone**: every polynomial is bounded by a multiple
of the unit. -/
theorem cone_archimedean (y : NCPoly (Gen X Y A B)) :
    ∃ N : ℝ, N • (1 : NCPoly (Gen X Y A B)) + y ∈ cone X Y A B :=
  NCPoly.archimedean_of_gen one_sub_gen_mul_gen_mem y

/-- **Separation from the game cone.** A polynomial outside `M` is separated from it by a real
linear functional that is nonnegative on `M`, takes the value `1` at the unit, and is `≤ 0` at
the polynomial. -/
theorem exists_state_functional_of_not_mem {h : NCPoly (Gen X Y A B)}
    (hh : h ∉ cone X Y A B) :
    ∃ L : NCPoly (Gen X Y A B) →ₗ[ℝ] ℝ,
      L 1 = 1 ∧ (∀ m ∈ cone X Y A B, 0 ≤ L m) ∧ L h ≤ 0 :=
  exists_separating_functional_of_archimedean _ 1 cone_archimedean NCPoly.one_mem_qmod h hh

end Algebra

/-! ## Evaluation in a strategy -/

section Strategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The letters evaluated in a commuting-operator strategy: `e_xa ↦ E x a`, `f_yb ↦ F y b`. -/
def stratEval (S : CommutingOperatorStrategy X Y A B) : Gen X Y A B → S.H →L[ℂ] S.H :=
  Sum.elim (fun p => S.E p.1 p.2) (fun p => S.F p.1 p.2)

variable (S : CommutingOperatorStrategy X Y A B)

/-- The letter `e_xa` evaluates to the effect `E x a`. -/
@[simp] theorem eval_eG (x : X) (a : A) : NCPoly.eval (stratEval S) (eG x a) = S.E x a := by
  simp [eG, stratEval]

/-- The letter `f_yb` evaluates to the effect `F y b`. -/
@[simp] theorem eval_fG (y : Y) (b : B) : NCPoly.eval (stratEval S) (fG y b) = S.F y b := by
  simp [fG, stratEval]

/-- The letters evaluate to positive operators. -/
theorem stratEval_isPositive (g : Gen X Y A B) : (stratEval S g).IsPositive := by
  rcases g with ⟨x, a⟩ | ⟨y, b⟩
  · exact S.E_pos x a
  · exact S.F_pos y b

/-- The letters evaluate to contractions. -/
theorem norm_stratEval_le_one (g : Gen X Y A B) : ‖stratEval S g‖ ≤ 1 := by
  rcases g with ⟨x, a⟩ | ⟨y, b⟩
  · exact S.norm_E_le_one x a
  · exact S.norm_F_le_one y b

/-- Every word evaluates to a contraction. -/
theorem norm_eval_single_one_le (w : FreeMonoid (Gen X Y A B)) :
    ‖NCPoly.eval (stratEval S) (NCPoly.single w 1)‖ ≤ 1 := by
  rw [NCPoly.eval_single, one_smul]
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact ContinuousLinearMap.norm_id_le
  | of_mul g w ih =>
    rw [map_mul, FreeMonoid.lift_eval_of]
    calc ‖stratEval S g * FreeMonoid.lift (stratEval S) w‖
        ≤ ‖stratEval S g‖ * ‖FreeMonoid.lift (stratEval S) w‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_stratEval_le_one S g) ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The strategy satisfies the relations. -/
theorem stratEval_rels : ∀ ρ ∈ rels X Y A B, NCPoly.eval (stratEval S) ρ = 0 := by
  rintro ρ ((⟨x, rfl⟩ | ⟨y, rfl⟩) | ⟨⟨x, y, a, b⟩, rfl⟩)
  · simp [S.E_sum]
  · simp [S.F_sum]
  · simp [(S.commutes x y a b).eq]

/-- **Positivity of the cone in every strategy**: every element of `M` has nonnegative
expectation in the strategy's state. -/
theorem strategy_nonneg {m : NCPoly (Gen X Y A B)} (hm : m ∈ cone X Y A B) :
    0 ≤ (⟪S.ψ, NCPoly.eval (stratEval S) m S.ψ⟫_ℂ).re :=
  NCPoly.re_inner_eval_nonneg _ (stratEval_isPositive S) (stratEval_rels S) S.ψ hm

/-- The correlation of a strategy is the expectation of `e_xa f_yb`. -/
theorem correlation_eq (x : X) (y : Y) (a : A) (b : B) :
    S.correlation x y a b =
      (⟪S.ψ, NCPoly.eval (stratEval S) (eG x a * fG y b) S.ψ⟫_ℂ).re := by
  simp [CommutingOperatorStrategy.correlation, mul_apply_eq_comp]

/-- The game polynomial `W_G = Σ μ(x, y) [D x y a b] e_xa f_yb`, with real coefficients. -/
def gamePoly (G : Game X Y A B) : NCPoly (Gen X Y A B) :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    ((G.μ x y * (if G.D x y a b then 1 else 0) : ℝ) : ℂ) • (eG x a * fG y b)

/-- The value of a strategy is the expectation of the game polynomial. -/
theorem value_eq (G : Game X Y A B) :
    S.value G = (⟪S.ψ, NCPoly.eval (stratEval S) (gamePoly G) S.ψ⟫_ℂ).re := by
  simp only [CommutingOperatorStrategy.value, gamePoly, map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul,
    correlation_eq]

/-- **Soundness of a cone certificate**: `r·1 - W_G ∈ M` bounds every strategy's value by
`r`. -/
theorem value_le_of_mem (G : Game X Y A B) {r : ℝ}
    (h : r • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B) : S.value G ≤ r := by
  have := strategy_nonneg S h
  have hr : r • (1 : NCPoly (Gen X Y A B)) = ((r : ℝ) : ℂ) • 1 := rfl
  rw [hr, map_sub, map_smul, map_one, sub_apply, _root_.smul_apply, one_apply_eq_self,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, S.ψ_norm, Complex.sub_re,
    ← value_eq] at this
  simpa using this

/-- **The commuting-operator value under a cone certificate**: `r·1 - W_G ∈ M` with `0 ≤ r`
bounds the commuting-operator value by `r`. The sign hypothesis replaces nonemptiness of the
type of strategies (`Real.iSup_le`); it cannot be dropped, since if `A` is empty and `X` is not,
every polynomial lies in the cone. -/
theorem commutingOperatorValue_le_of_mem (G : Game X Y A B) {r : ℝ} (hr : 0 ≤ r)
    (h : r • (1 : NCPoly (Gen X Y A B)) - gamePoly G ∈ cone X Y A B) :
    commutingOperatorValue G ≤ r :=
  Real.iSup_le (fun S => value_le_of_mem S G h) hr

end Strategy

/-! ## The state of a strategy -/

section StateOf

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable (S : CommutingOperatorStrategy X Y A B)

/-- The state of a strategy on the game algebra: `z ↦ ⟪ψ, π_S(z) ψ⟫`, with `π_S` the
evaluation of the letters in the strategy. -/
def stateOf : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ where
  toFun z := ⟪S.ψ, NCPoly.eval (stratEval S) z S.ψ⟫_ℂ
  map_add' z z' := by rw [map_add, add_apply, inner_add_right]
  map_smul' c z := by
    rw [map_smul, _root_.smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul]

/-- The state of a strategy, applied. -/
@[simp] theorem stateOf_apply (z : NCPoly (Gen X Y A B)) :
    stateOf S z = ⟪S.ψ, NCPoly.eval (stratEval S) z S.ψ⟫_ℂ := rfl

/-- The state of a strategy is bounded by `1` on every word. -/
theorem norm_stateOf_single_one_le (w : FreeMonoid (Gen X Y A B)) :
    ‖stateOf S (NCPoly.single w 1)‖ ≤ 1 := by
  rw [stateOf_apply]
  calc ‖⟪S.ψ, NCPoly.eval (stratEval S) (NCPoly.single w 1) S.ψ⟫_ℂ‖
      ≤ ‖S.ψ‖ * ‖NCPoly.eval (stratEval S) (NCPoly.single w 1) S.ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖S.ψ‖ * (‖NCPoly.eval (stratEval S) (NCPoly.single w 1)‖ * ‖S.ψ‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (1 * 1) := by rw [S.ψ_norm]; gcongr; exact norm_eval_single_one_le S w
    _ = 1 := by norm_num

/-- The state of a strategy recovers its correlation. -/
theorem re_stateOf_eG_mul_fG (x : X) (y : Y) (a : A) (b : B) :
    (stateOf S (eG x a * fG y b)).re = S.correlation x y a b :=
  (correlation_eq S x y a b).symm

/-- The state of a strategy recovers its value. -/
theorem re_stateOf_gamePoly (G : Game X Y A B) : (stateOf S (gamePoly G)).re = S.value G :=
  (value_eq S G).symm

end StateOf

/-! ## Cone states -/

section ConeState

variable {X Y A B : Type*} [Fintype A] [Fintype B]

/-- A **cone state** on the game algebra: a `ℂ`-linear functional that is `1` at the unit and
has nonnegative real part on the cone `M`. -/
structure IsConeState (L : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ) : Prop where
  /-- A cone state is normalized. -/
  map_one : L 1 = 1
  /-- A cone state has nonnegative real part on the cone. -/
  re_nonneg : ∀ m ∈ cone X Y A B, 0 ≤ (L m).re

namespace IsConeState

variable {L : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ} (hL : IsConeState L)
include hL

/-- A cone state has vanishing real part on `m` when both `m` and `-m` lie in the cone. -/
theorem re_eq_zero_of_neg_mem {m : NCPoly (Gen X Y A B)} (hm : m ∈ cone X Y A B)
    (hm' : -m ∈ cone X Y A B) : (L m).re = 0 := by
  have h1 := hL.re_nonneg m hm
  have h2 := hL.re_nonneg _ hm'
  rw [map_neg, Complex.neg_re] at h2
  linarith

/-- A cone state has vanishing real part on anti-hermitian elements. -/
theorem re_eq_zero_of_star_eq_neg {z : NCPoly (Gen X Y A B)} (hz : star z = -z) :
    (L z).re = 0 :=
  hL.re_eq_zero_of_neg_mem (NCPoly.mem_qmod_of_star_eq_neg hz)
    (NCPoly.mem_qmod_of_star_eq_neg (by rw [star_neg, hz]))

/-- A cone state is hermitian: `z - z⋆` and `i (z + z⋆)` are anti-hermitian. -/
theorem map_star (z : NCPoly (Gen X Y A B)) : L (star z) = conj (L z) := by
  have h1 : (L (z - star z)).re = 0 :=
    hL.re_eq_zero_of_star_eq_neg (by rw [star_sub, star_star, neg_sub])
  have h2 : (L (Complex.I • (z + star z))).re = 0 :=
    hL.re_eq_zero_of_star_eq_neg (by
      rw [star_smul, star_add, star_star, Complex.star_def, Complex.conj_I, neg_smul, add_comm])
  rw [map_sub, Complex.sub_re] at h1
  rw [map_smul, map_add, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.add_im] at h2
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

/-- A cone state vanishes on the relation ideal: `±j` and `±i j` lie in it. -/
theorem map_eq_zero_of_mem_relSpan {z : NCPoly (Gen X Y A B)}
    (hz : z ∈ NCPoly.relSpan (rels X Y A B)) : L z = 0 := by
  have hre : ∀ z ∈ NCPoly.relSpan (rels X Y A B), (L z).re = 0 := fun z hz =>
    hL.re_eq_zero_of_neg_mem (NCPoly.mem_qmod_of_mem_relSpan hz)
      (NCPoly.mem_qmod_of_mem_relSpan (Submodule.neg_mem _ hz))
  have h1 := hre z hz
  have h2 := hre _ (Submodule.smul_mem _ Complex.I hz)
  rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
  apply Complex.ext
  · simpa using h1
  · simp only [Complex.zero_im]; linarith

/-- A cone state vanishes on `u j v` for `j` in the relation ideal. -/
theorem map_mul_mul_eq_zero {j : NCPoly (Gen X Y A B)}
    (hj : j ∈ NCPoly.relSpan (rels X Y A B)) (u v : NCPoly (Gen X Y A B)) :
    L (u * j * v) = 0 :=
  hL.map_eq_zero_of_mem_relSpan (NCPoly.mul_mem_relSpan hj u v)

/-- A cone state is positive on hermitian squares. -/
theorem re_star_mul_self_nonneg (a : NCPoly (Gen X Y A B)) : 0 ≤ (L (star a * a)).re :=
  hL.re_nonneg _ (NCPoly.star_mul_self_mem_qmod a)

end IsConeState

/-- The state of a strategy is a cone state. -/
theorem isConeState_stateOf [Fintype X] [Fintype Y] (S : CommutingOperatorStrategy X Y A B) :
    IsConeState (stateOf S) where
  map_one := by simp [inner_self_eq_norm_sq_to_K, S.ψ_norm]
  re_nonneg _ hm := strategy_nonneg S hm

end ConeState

/-! ## Complexification of a real functional -/

section Complexify

variable {P : Type*} [AddCommGroup P] [Module ℂ P]

/-- The complexification `z ↦ L₀ z - i L₀ (i z)` of a real linear functional on a complex vector
space: the unique `ℂ`-linear functional with real part `L₀`. -/
def complexify (L₀ : P →ₗ[ℝ] ℝ) : P →ₗ[ℂ] ℂ where
  toFun z := (L₀ z : ℂ) - Complex.I * (L₀ (Complex.I • z) : ℂ)
  map_add' x y := by simp [smul_add]; ring
  map_smul' c z := by
    have hc : c • z = c.re • z + c.im • (Complex.I • z) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_comm, mul_smul, Complex.coe_smul, Complex.coe_smul,
        smul_comm Complex.I (c.im : ℝ)]
    have hIc : Complex.I • (c • z) = c.re • (Complex.I • z) - c.im • z := by
      rw [hc, smul_add, smul_comm Complex.I (c.re : ℝ), smul_comm Complex.I (c.im : ℝ),
        smul_smul, Complex.I_mul_I, neg_one_smul, smul_neg, sub_eq_add_neg]
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [hIc, hc, map_add, map_sub, L₀.map_smul, L₀.map_smul, L₀.map_smul, L₀.map_smul]
    apply Complex.ext
    · simp
    · simp; ring

/-- The complexification, applied. -/
theorem complexify_apply (L₀ : P →ₗ[ℝ] ℝ) (z : P) :
    complexify L₀ z = (L₀ z : ℂ) - Complex.I * (L₀ (Complex.I • z) : ℂ) := rfl

/-- The real part of the complexification is the original functional. -/
@[simp] theorem re_complexify (L₀ : P →ₗ[ℝ] ℝ) (z : P) : (complexify L₀ z).re = L₀ z := by
  simp [complexify_apply]

end Complexify

section ConeStateOfReal

variable {X Y A B : Type*} [Fintype A] [Fintype B]

/-- The complexification of a real functional that is `1` at the unit and nonnegative on the
cone is a cone state. -/
theorem isConeState_complexify {L₀ : NCPoly (Gen X Y A B) →ₗ[ℝ] ℝ} (h1 : L₀ 1 = 1)
    (hM : ∀ m ∈ cone X Y A B, 0 ≤ L₀ m) : IsConeState (complexify L₀) where
  map_one := by
    have hs : star (Complex.I • (1 : NCPoly (Gen X Y A B))) = -(Complex.I • 1) := by
      rw [star_smul, star_one, Complex.star_def, Complex.conj_I, neg_smul]
    have hs' : star (-(Complex.I • (1 : NCPoly (Gen X Y A B)))) = -(-(Complex.I • 1)) := by
      rw [star_neg, hs]
    have hpos := hM _ (NCPoly.mem_qmod_of_star_eq_neg hs)
    have hneg := hM _ (NCPoly.mem_qmod_of_star_eq_neg hs')
    rw [map_neg] at hneg
    have hI : L₀ (Complex.I • 1) = 0 := by linarith
    rw [complexify_apply, h1, hI]
    simp
  re_nonneg m hm := by rw [re_complexify]; exact hM m hm

/-- **Separation by a cone state.** A polynomial outside the cone is separated from it by a cone
state with nonpositive real part at the polynomial. -/
theorem exists_isConeState_of_not_mem {h : NCPoly (Gen X Y A B)} (hh : h ∉ cone X Y A B) :
    ∃ L : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ, IsConeState L ∧ (L h).re ≤ 0 := by
  obtain ⟨L₀, h1, hM, hLh⟩ := exists_state_functional_of_not_mem hh
  exact ⟨complexify L₀, isConeState_complexify h1 hM, by rw [re_complexify]; exact hLh⟩

end ConeStateOfReal

/-! ## The GNS strategy of a cone state -/

section GNS

variable {X Y A B : Type} [Fintype A] [Fintype B] {L : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ}

/-- A cone state as a `GNS.State` of the game algebra. -/
def IsConeState.toState (hL : IsConeState L) : GNS.State (NCPoly (Gen X Y A B)) where
  L := L
  map_one := hL.map_one
  map_star := hL.map_star
  nonneg := hL.re_star_mul_self_nonneg

/-- The functional of the `GNS.State` of a cone state is the cone state. -/
@[simp] theorem IsConeState.toState_L (hL : IsConeState L) : hL.toState.L = L := rfl

/-- The letters satisfy, under a cone state, the relations of two commuting families of
POVMs. -/
def IsConeState.genData (hL : IsConeState L) :
    GNS.GenData (NCPoly (Gen X Y A B)) X Y A B hL.toState where
  e := eG
  f := fG
  e_sa := star_eG
  f_sa := star_fG
  e_pos _ _ s := hL.re_nonneg _ (NCPoly.star_mul_mul_mem_qmod s _)
  f_pos _ _ s := hL.re_nonneg _ (NCPoly.star_mul_mul_mem_qmod s _)
  e_sum x u v := hL.map_mul_mul_eq_zero (sum_eG_sub_one_mem_relSpan x) u v
  f_sum y u v := hL.map_mul_mul_eq_zero (sum_fG_sub_one_mem_relSpan y) u v
  comm x y a b u v := hL.map_mul_mul_eq_zero (commutator_mem_relSpan x y a b) u v

variable [Fintype X] [Fintype Y]

/-- **The GNS strategy of a cone state.** -/
def stateStrategy (hL : IsConeState L) : CommutingOperatorStrategy X Y A B :=
  hL.genData.strategy

/-- The correlation of the GNS strategy of a cone state is `Re L (e_xa f_yb)`. -/
theorem stateStrategy_correlation (hL : IsConeState L) (x : X) (y : Y) (a : A) (b : B) :
    (stateStrategy hL).correlation x y a b = (L (eG x a * fG y b)).re :=
  hL.genData.strategy_correlation x y a b

/-- The value of the GNS strategy of a cone state is `Re L (W_G)`. -/
theorem stateStrategy_value (hL : IsConeState L) (G : Game X Y A B) :
    (stateStrategy hL).value G = (L (gamePoly G)).re := by
  simp only [CommutingOperatorStrategy.value, stateStrategy_correlation, gamePoly, map_sum,
    map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]

/-- A cone state is bounded on the game polynomial by the commuting-operator value. -/
theorem re_gamePoly_le_commutingOperatorValue (hL : IsConeState L) (G : Game X Y A B) :
    (L (gamePoly G)).re ≤ commutingOperatorValue G :=
  stateStrategy_value hL G ▸ (stateStrategy hL).value_le_commutingOperatorValue G

/-- **`C_qc` through cone states**: the commuting-operator correlations are exactly the
`Re L (e_xa f_yb)` for cone states `L`. -/
theorem mem_Cqc_iff {p : X → Y → A → B → ℝ} :
    p ∈ Cqc X Y A B ↔
      ∃ L : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ, IsConeState L ∧
        p = fun x y a b => (L (eG x a * fG y b)).re := by
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨stateOf S, isConeState_stateOf S, ?_⟩
    funext x y a b
    exact (re_stateOf_eG_mul_fG S x y a b).symm
  · rintro ⟨L, hL, rfl⟩
    refine ⟨stateStrategy hL, ?_⟩
    funext x y a b
    exact stateStrategy_correlation hL x y a b

end GNS

end Tsirelson

end MIPRE
