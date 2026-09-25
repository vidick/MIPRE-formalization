/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core/Strategy.lean, from a snapshot of the `main` branch supplied on 2026-09-25
(archive, no commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core.Measurement

/-!
# Strategies, the three generic correlation sets, and the B23 strategy predicates

Sources:

* `Blueprint/Nodes/B23-Games/Parts/01-GamesAndStrategies.tex`:
  `def:tensor-product-strategy`, `def:projective-strategy`,
  `rem:symmetric-games`, `def:comm-strategy`, `def:consistent-measurement`,
  `def:consistent-strategy`, `def:spcc`;
* `Blueprint/Nodes/B05-NPA-Core/Math.tex`, `def:n7b` (finite-dimensional
  tensor-product strategies and commuting-operator strategies);
* `Blueprint/Nodes/B30-Tsirelson-Consequence/Math.tex`,
  `def:terminal-correlation-sets` (`C_q`, `C_qa`, `C_qc`).

The three generic sets are *exactly* ranges of strategy correlations, and
`Cq`, `Cqa`, `Cqc` are `abbrev` aliases of them at square alphabets — never
second definitions.
-/

open scoped ComplexOrder

namespace Tsirelson

noncomputable section

universe u v w z

variable {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## Finite-dimensional tensor-product strategies -/

/-- A **finite-dimensional tensor-product strategy**: actual finite-dimensional
local Hilbert spaces, an actual bipartite unit vector, and actual local POVMs.

This is `def:tensor-product-strategy` = `def:n7b`. -/
structure TensorStrategy (X : Type u) (Y : Type v) (A : Type w) (B : Type z)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- Alice's local dimension. -/
  dA : ℕ
  /-- Bob's local dimension. -/
  dB : ℕ
  /-- The bipartite state, a vector of the concrete tensor product. -/
  ψ : EuclideanSpace ℂ (Fin dA × Fin dB)
  /-- The state is a unit vector. -/
  unit_ψ : ‖ψ‖ = 1
  /-- Alice's measurement family, one POVM per question. -/
  alice : X → POVM (FinH dA) A
  /-- Bob's measurement family, one POVM per question. -/
  bob : Y → POVM (FinH dB) B

namespace TensorStrategy

/-- The correlation of a tensor strategy, through the canonical Born value:
`p(a,b | x,y) = ⟨ψ| A^x_a ⊗ B^y_b |ψ⟩`. -/
def corr (S : TensorStrategy X Y A B) : Correlation X Y A B :=
  fun x y a b => born S.ψ (kronCLM ((S.alice x).effect a) ((S.bob y).effect b))

theorem corr_nonneg (S : TensorStrategy X Y A B) (x y a b) : 0 ≤ S.corr x y a b :=
  born_nonneg (kronCLM_isPositive ((S.alice x).positive a) ((S.bob y).positive b))

/-- The Born normalization: for every question pair the outcome distribution
sums to one.  This is *proved* from `sum_eq_one` of the two POVMs and the
unit-vector condition, not postulated. -/
theorem sum_corr (S : TensorStrategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.corr x y a b = 1 := by
  calc ∑ a, ∑ b, S.corr x y a b
      = ∑ a, born S.ψ (kronCLM ((S.alice x).effect a) 1) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [show (1 : FinH S.dB →L[ℂ] FinH S.dB) = ∑ b, (S.bob y).effect b from
          ((S.bob y).sum_eq_one).symm, kronCLM_sum_right, born_sum]
        rfl
    _ = born S.ψ (kronCLM (∑ a, (S.alice x).effect a) 1) := by
        rw [kronCLM_sum_left, born_sum]
    _ = born S.ψ 1 := by rw [(S.alice x).sum_eq_one, kronCLM_one_one]
    _ = 1 := by rw [born_one, S.unit_ψ]; norm_num

theorem corr_le_one (S : TensorStrategy X Y A B) (x y a b) : S.corr x y a b ≤ 1 := by
  have hsum := S.sum_corr x y
  have h1 : S.corr x y a b ≤ ∑ b', S.corr x y a b' :=
    Finset.single_le_sum (fun b' _ => S.corr_nonneg x y a b') (Finset.mem_univ b)
  have h2 : (∑ b', S.corr x y a b') ≤ ∑ a', ∑ b', S.corr x y a' b' :=
    Finset.single_le_sum
      (fun a' _ => Finset.sum_nonneg fun b' _ => S.corr_nonneg x y a' b')
      (Finset.mem_univ a)
  linarith

/-- **Projectivity** (`def:projective-strategy`): every local measurement is
projective. -/
def IsProjective (S : TensorStrategy X Y A B) : Prop :=
  (∀ x a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) ∧
  (∀ y b, (S.bob y).effect b * (S.bob y).effect b = (S.bob y).effect b)

end TensorStrategy

/-! ## Commuting-operator strategies -/

/-- A **commuting-operator strategy**: an actual complex Hilbert space (not
required finite-dimensional), an actual unit state, actual POVMs for both
players, and **global** cross-party commutation.

This is `def:n7b`'s commuting-operator strategy, with POVMs rather than
projective measurements — the version `ACCEPTANCE.md` and
`LEAN_CORE_AND_BRIDGE.md` §11.2 designate as the core `Cqc`.  Reconciling it with
B05's projective `def:n6-cqc` is `lem:n8`, a B05 obligation outside P00.

The carrier is taken in `Type`; see `API_REVIEW.md` §7 for the record. -/
structure CommutingStrategy (X : Type u) (Y : Type v) (A : Type w) (B : Type z)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- The ambient Hilbert space. -/
  H : Type
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  /-- The state. -/
  ψ : H
  /-- The state is a unit vector. -/
  unit_ψ : ‖ψ‖ = 1
  /-- Alice's measurement family. -/
  alice : X → POVM H A
  /-- Bob's measurement family. -/
  bob : Y → POVM H B
  /-- Global cross-party commutation, for **all** question pairs. -/
  commuting : ∀ x y a b,
    (alice x).effect a * (bob y).effect b = (bob y).effect b * (alice x).effect a

attribute [instance] CommutingStrategy.normedAddCommGroup CommutingStrategy.innerProductSpace
  CommutingStrategy.completeSpace

namespace CommutingStrategy

/-- The correlation of a commuting strategy, through the *same* canonical Born
value: `p(a,b | x,y) = ⟨ψ, A^x_a B^y_b ψ⟩`. -/
def corr (S : CommutingStrategy X Y A B) : Correlation X Y A B :=
  fun x y a b => born S.ψ ((S.alice x).effect a * (S.bob y).effect b)

theorem effect_mul_isPositive (S : CommutingStrategy X Y A B) (x y a b) :
    ((S.alice x).effect a * (S.bob y).effect b).IsPositive :=
  isPositive_mul_of_commute ((S.alice x).positive a) ((S.bob y).positive b)
    (S.commuting x y a b)

theorem corr_nonneg (S : CommutingStrategy X Y A B) (x y a b) : 0 ≤ S.corr x y a b :=
  born_nonneg (S.effect_mul_isPositive x y a b)

theorem sum_corr (S : CommutingStrategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.corr x y a b = 1 := by
  calc ∑ a, ∑ b, S.corr x y a b
      = ∑ a, born S.ψ ((S.alice x).effect a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [corr]
        rw [← born_sum, ← Finset.mul_sum, (S.bob y).sum_eq_one, mul_one]
    _ = born S.ψ 1 := by rw [← born_sum, (S.alice x).sum_eq_one]
    _ = 1 := by rw [born_one, S.unit_ψ]; norm_num

theorem corr_le_one (S : CommutingStrategy X Y A B) (x y a b) : S.corr x y a b ≤ 1 := by
  have hsum := S.sum_corr x y
  have h1 : S.corr x y a b ≤ ∑ b', S.corr x y a b' :=
    Finset.single_le_sum (fun b' _ => S.corr_nonneg x y a b') (Finset.mem_univ b)
  have h2 : (∑ b', S.corr x y a b') ≤ ∑ a', ∑ b', S.corr x y a' b' :=
    Finset.single_le_sum
      (fun a' _ => Finset.sum_nonneg fun b' _ => S.corr_nonneg x y a' b')
      (Finset.mem_univ a)
  linarith

/-- Projectivity for commuting-operator strategies.  Deliberately a *separate*
predicate from the tensor-strategy notion and from PCC. -/
def IsProjective (S : CommutingStrategy X Y A B) : Prop :=
  (∀ x a, (S.alice x).effect a * (S.alice x).effect a = (S.alice x).effect a) ∧
  (∀ y b, (S.bob y).effect b * (S.bob y).effect b = (S.bob y).effect b)

/-- Synchronicity for commuting-operator strategies on square alphabets
(`bp:b23-games:definition:011`). -/
def IsSynchronous (S : CommutingStrategy X X A A) : Prop :=
  ∀ x a b, a ≠ b → S.corr x x a b = 0

end CommutingStrategy

/-! ## The three generic correlation sets and their square aliases -/

variable (X Y A B)

/-- The **generic tensor correlation set**: exactly the range of
finite-dimensional tensor-strategy correlations. -/
def TensorCorrelations : Set (Correlation X Y A B) :=
  {p | ∃ S : TensorStrategy X Y A B, S.corr = p}

/-- The **generic commuting correlation set**: exactly the range of globally
commuting POVM-strategy correlations. -/
def CommutingCorrelations : Set (Correlation X Y A B) :=
  {p | ∃ S : CommutingStrategy X Y A B, S.corr = p}

/-- The **generic tensor-correlation closure**: definitionally the topological
closure of the generic tensor set, in the product/Euclidean topology of
`Core/Correlation.lean`. -/
def TensorCorrelationClosure : Set (Correlation X Y A B) :=
  closure (TensorCorrelations X Y A B)

variable {X Y A B}

/-- `C_q(n,k)` — the square alias, not a second definition. -/
abbrev Cq (n k : ℕ) : Set (Corr n k) :=
  TensorCorrelations (Fin n) (Fin n) (Fin k) (Fin k)

/-- `C_qa(n,k)` — the square alias of the generic tensor closure. -/
abbrev Cqa (n k : ℕ) : Set (Corr n k) :=
  TensorCorrelationClosure (Fin n) (Fin n) (Fin k) (Fin k)

/-- `C_qc(n,k)` — the square alias of the generic commuting set. -/
abbrev Cqc (n k : ℕ) : Set (Corr n k) :=
  CommutingCorrelations (Fin n) (Fin n) (Fin k) (Fin k)

theorem tensorCorrelationClosure_eq_closure :
    TensorCorrelationClosure X Y A B = closure (TensorCorrelations X Y A B) := rfl

/-- `C_qa = closure C_q`, by definition. -/
theorem cqa_eq_closure_cq (n k : ℕ) : Cqa n k = closure (Cq n k) := rfl

/-! ## Explicit witnesses: the one-dimensional deterministic strategies

`def:n7b` records that "both strategy classes are nonempty (use one-dimensional
deterministic measurements)".  These are those strategies, built explicitly. -/

section Trivial

/-- The deterministic POVM concentrated on a single outcome. -/
def detPOVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Type*) [Fintype A] (a₀ : A) : POVM H A := by
  classical
  exact
    { effect := fun a => if a = a₀ then 1 else 0
      positive := fun a => by
        by_cases h : a = a₀ <;> simp [h]
      sum_eq_one := by simp }

/-- The one-dimensional deterministic tensor strategy. -/
def trivialTensorStrategy (a₀ : A) (b₀ : B) : TensorStrategy X Y A B where
  dA := 1
  dB := 1
  ψ := EuclideanSpace.single ((0 : Fin 1), (0 : Fin 1)) (1 : ℂ)
  unit_ψ := by simp
  alice _ := detPOVM _ _ a₀
  bob _ := detPOVM _ _ b₀

/-- The one-dimensional deterministic commuting strategy. -/
def trivialCommutingStrategy (a₀ : A) (b₀ : B) : CommutingStrategy X Y A B where
  H := EuclideanSpace ℂ (Fin 1)
  ψ := EuclideanSpace.single (0 : Fin 1) (1 : ℂ)
  unit_ψ := by simp
  alice _ := detPOVM _ _ a₀
  bob _ := detPOVM _ _ b₀
  commuting := by
    classical
    intro x y a b
    by_cases ha : a = a₀ <;> by_cases hb : b = b₀ <;>
      simp [detPOVM, ha, hb]

theorem tensorCorrelations_nonempty (hA : Nonempty A) (hB : Nonempty B) :
    (TensorCorrelations X Y A B).Nonempty :=
  ⟨(trivialTensorStrategy (X := X) (Y := Y) hA.some hB.some).corr,
    ⟨trivialTensorStrategy hA.some hB.some, rfl⟩⟩

theorem commutingCorrelations_nonempty (hA : Nonempty A) (hB : Nonempty B) :
    (CommutingCorrelations X Y A B).Nonempty :=
  ⟨(trivialCommutingStrategy (X := X) (Y := Y) hA.some hB.some).corr,
    ⟨trivialCommutingStrategy hA.some hB.some, rfl⟩⟩

end Trivial

/-! ## The rigorously typed common-local-space view, and the B23 predicates

PCC compares an operator on one tensor leg with the *same* operator on the other
leg, so both legs must be literally the same space.  `CommonTensorStrategy` is
that view: one dimension `d`, one local space `FinH d`, state in
`EuclideanSpace ℂ (Fin d × Fin d)`. -/

/-- A tensor strategy whose two local Hilbert spaces have been identified with a
single finite-dimensional space.  This is the typing required by
`def:consistent-strategy` and `def:comm-strategy`. -/
structure CommonTensorStrategy (X : Type u) (Y : Type v) (A : Type w) (B : Type z)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- The common local dimension. -/
  d : ℕ
  /-- The bipartite state on `FinH d ⊗ FinH d`. -/
  ψ : EuclideanSpace ℂ (Fin d × Fin d)
  /-- The state is a unit vector. -/
  unit_ψ : ‖ψ‖ = 1
  /-- Alice's measurement family on the common local space. -/
  alice : X → POVM (FinH d) A
  /-- Bob's measurement family on the common local space. -/
  bob : Y → POVM (FinH d) B

namespace CommonTensorStrategy

/-- The underlying tensor strategy: a rigorous transport with `dA = dB = d`. -/
def toTensorStrategy (S : CommonTensorStrategy X Y A B) : TensorStrategy X Y A B where
  dA := S.d
  dB := S.d
  ψ := S.ψ
  unit_ψ := S.unit_ψ
  alice := S.alice
  bob := S.bob

@[simp] theorem toTensorStrategy_dA (S : CommonTensorStrategy X Y A B) :
    S.toTensorStrategy.dA = S.d := rfl

@[simp] theorem toTensorStrategy_dB (S : CommonTensorStrategy X Y A B) :
    S.toTensorStrategy.dB = S.d := rfl

/-- The correlation of the underlying tensor strategy. -/
def corr (S : CommonTensorStrategy X Y A B) : Correlation X Y A B := S.toTensorStrategy.corr

/-- **Consistency** (`def:consistent-strategy` via `def:consistent-measurement`).

Each Alice family is compared with **its own copy** on the opposite tensor leg,
and, *separately*, each Bob family with its own copy.  This is deliberately
**not** the cross-family equality `(A^x_a ⊗ I)ψ = (I ⊗ B^x_a)ψ`; see
`API_REVIEW.md` §9.4 for the recorded B04/B23 discrepancy. -/
def IsConsistent (S : CommonTensorStrategy X Y A B) : Prop :=
  (∀ x a, kronCLM ((S.alice x).effect a) 1 S.ψ = kronCLM 1 ((S.alice x).effect a) S.ψ) ∧
  (∀ y b, kronCLM ((S.bob y).effect b) 1 S.ψ = kronCLM 1 ((S.bob y).effect b) S.ψ)

/-- **Local commutation** (`def:comm-strategy`): commutation of Alice's and Bob's
operators on the *common local space*, restricted to the support of the game's
question distribution.

This is distinct from the global commutation defining `Cqc`, and it makes sense
for asymmetric alphabets. -/
def CommutesOn (G : NonlocalGame X Y A B) (S : CommonTensorStrategy X Y A B) : Prop :=
  ∀ x y, (x, y) ∈ G.questionSupport → ∀ a b,
    (S.alice x).effect a * (S.bob y).effect b = (S.bob y).effect b * (S.alice x).effect a

/-- **PCC** (`def:spcc`): projective, consistent, and locally commuting.  May have
asymmetric question and answer alphabets. -/
def IsPCC (G : NonlocalGame X Y A B) (S : CommonTensorStrategy X Y A B) : Prop :=
  S.toTensorStrategy.IsProjective ∧ S.IsConsistent ∧ S.CommutesOn G

/-- **Strategy symmetry** (`rem:symmetric-games`): the state is invariant under
exchanging the two tensor legs, **and** both players use identical measurement
families.  Equal dimensions alone are not enough. -/
def IsSymmetric (S : CommonTensorStrategy X X A A) : Prop :=
  (∀ i j : Fin S.d, WithLp.ofLp S.ψ (i, j) = WithLp.ofLp S.ψ (j, i)) ∧
  (∀ x, S.alice x = S.bob x)

/-- **SPCC** (`def:spcc`): PCC together with symmetry.  Only this predicate forces
square alphabets. -/
def IsSPCC (G : NonlocalGame X X A A) (S : CommonTensorStrategy X X A A) : Prop :=
  S.IsPCC G ∧ S.IsSymmetric

end CommonTensorStrategy

end

end Tsirelson
