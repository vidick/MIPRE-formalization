/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Disagreement
public import MIPRE.Foundations.OracularTensor
public import MIPRE.Foundations.ValueModel

@[expose] public section

/-!
# Projective strategies in a bipartite model

The soundness analysis of answer reduction is written for strategies: it restricts one to a copy
of the low-degree test, extracts polynomial measurements from the pieces, and decodes a strategy
for the input verifier's game from them. Phase 3 of `planning/mipco-track.md` writes it once, for
a **projective strategy in a bipartite model** (`BipartiteModel.ProjStrat`): for each question a
projective measurement in the player's algebra, on the model's state. It is `TensorProductStrategy`
with the tensor-product model replaced by any bipartite model, and carries the same operations —
the value, the conditional failures, playing a strategy on another game through maps of the
questions and the answers (`ProjStrat.adapt`), relabelling along equivalences
(`ProjStrat.relabel`) — each a single line over the model-level statements of
`MIPRE/Foundations/GameAdapt.lean`. The inconsistency of two families of measurements
(`BipartiteModel.inconsistency`), the error measure of the low-individual-degree test's
conclusions, is here too.

The two models the analysis is read in:

* **tensor-product**: a `TensorProductStrategy` is a projective strategy in its tensor-product
  model (`TensorProductStrategy.toModel`, of the same value), and conversely a projective
  strategy in the tensor-product model of a state on `Fin a × Fin b` is a
  `TensorProductStrategy` (`BipartiteModel.ProjStrat.toTensor`, of the same value);
* **commuting-operator**: `ω_co` is approached by projective strategies in the model of a
  commuting-operator strategy (`exists_projStrat_lt_commutingOperatorValue`), and the value of a
  projective strategy in a model on a Hilbert space is at most `ω_co`
  (`BipartiteModel.ProjStrat.value_le_commutingOperatorValue`).

`ValueModel.Dominates ω M` says that every projective strategy of `M` has value at most `ω`;
both models are dominated by their value (`ValueModel.tensor_dominates`,
`ValueModel.commuting_dominates`). So a model-level theorem — a projective strategy of value at
least `1 - ε` for one game gives a projective strategy of value at least `1 - f(ε)` for another,
in the same model — bounds the second game's value in both values.
-/

namespace MIPRE

open Finset
open scoped ComplexOrder MatrixOrder

/-! ## Coarse-grainings of POVMs in a `⋆`-algebra -/

namespace POVMIn

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R] {X : Type*}
  [Fintype X]

/-- **Relabelling twice is relabelling once**: the level sets of `g ∘ f` are the unions of the
level sets of `f` along the level sets of `g`. -/
theorem map_map {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (M : POVMIn X R) (f : X → Y) (g : Y → Z) : (M.map f).map g = M.map fun a => g (f a) := by
  refine ext' fun c => ?_
  simp only [map_op, Finset.sum_filter]
  have h : ∀ y, (if g y = c then ∑ x, (if f x = y then M.op x else 0) else 0)
      = ∑ x, if f x = y then (if g y = c then M.op x else 0) else 0 := fun y => by
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq univ (f x) (fun y => if g y = c then M.op x else 0),
    ite_eq_left (Finset.mem_univ _)]

/-- Relabelling along the identity changes nothing. -/
theorem map_id [DecidableEq X] (M : POVMIn X R) : M.map (fun a => a) = M := by
  refine ext' fun c => ?_
  rw [map_op, Finset.sum_filter, Finset.sum_ite_eq' univ c, ite_eq_left (Finset.mem_univ c)]

/-- **The coarse-graining of a projective measurement is projective.** -/
theorem isPVMIn_map {Y : Type*} [Fintype Y] [DecidableEq Y] {M : POVMIn X R}
    (h : IsPVMIn M.op) (f : X → Y) : IsPVMIn (M.map f).op := by
  rw [show (M.map f).op = _ from funext (map_op f M)]
  exact h.coarse f

end POVMIn

/-- A POVM in a matrix algebra is a matrix POVM: the same three fields. -/
def POVMIn.toPOVM {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVMIn A (Matrix d d ℂ)) : POVM A d :=
  ⟨M.mats, M.nonneg, M.normalized⟩

@[simp] theorem POVMIn.toPOVM_toIn {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVMIn A (Matrix d d ℂ)) : M.toPOVM.toIn = M := rfl

/-- Coarse-graining a matrix POVM is coarse-graining it in the matrix algebra. -/
theorem POVM.toIn_map {A B d : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Fintype d]
    [DecidableEq d] (M : POVM A d) (f : A → B) : (M.map f).toIn = M.toIn.map f :=
  POVMIn.ext' fun b => by
    rw [POVM.toIn_op, POVMIn.map_op, POVM.map_mats]
    rfl

/-! ## Projective strategies -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **A projective strategy in a bipartite model** for the game `G`: for each question a
projective measurement in the player's algebra, on the model's state, which is a unit vector.
`TensorProductStrategy` is the case of the tensor-product model
(`TensorProductStrategy.toModel`); a projective commuting-operator strategy is one in its own
model (`exists_projStrat_lt_commutingOperatorValue`). -/
structure ProjStrat (G : Game X Y A B) where
  /-- The first player's measurement at each question. -/
  PA : X → POVMIn A 𝒜
  /-- The second player's measurement at each question. -/
  PB : Y → POVMIn B ℬ
  /-- The first player's measurements are projective. -/
  projA : ∀ x, IsPVMIn (PA x).op
  /-- The second player's measurements are projective. -/
  projB : ∀ y, IsPVMIn (PB y).op
  /-- The model's state is a unit vector. -/
  ψ_unit : ‖M.ψ‖ = 1

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- Two games with the same distribution and the same decision predicate give every family of
measurements the same value. -/
theorem povmValue_congr_game {G G' : Game X Y A B} (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a b, G.D x y a b = G'.D x y a b) (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) :
    M.povmValue G MA MB = M.povmValue G' MA MB := by
  unfold povmValue condWin
  simp only [hμ, hD]

namespace ProjStrat

variable {M} {G : Game X Y A B} (S : M.ProjStrat G)

/-- **The value of a projective strategy**: the value of its measurements in the model. -/
def value : ℝ := M.povmValue G S.PA S.PB

/-- The probability that the strategy is rejected, given the question pair `(x, y)`. -/
def failAt (x : X) (y : Y) : ℝ := M.condFail G S.PA S.PB x y

theorem failAt_nonneg (x : X) (y : Y) : 0 ≤ S.failAt x y := M.condFail_nonneg S.ψ_unit x y

theorem failAt_le_one (x : X) (y : Y) : S.failAt x y ≤ 1 := by
  have := M.condWin_nonneg (G := G) (MA := S.PA) (MB := S.PB) x y
  unfold failAt condFail
  linarith

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **The failure probability, decomposed by question pair.** -/
theorem one_sub_value_eq_sum_failAt : 1 - S.value = ∑ x, ∑ y, G.μ x y * S.failAt x y :=
  M.one_sub_povmValue_eq

theorem value_le_one : S.value ≤ 1 := by
  have h := S.one_sub_value_eq_sum_failAt
  have : 0 ≤ ∑ x, ∑ y, G.μ x y * S.failAt x y := Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (G.μ_nonneg x y) (S.failAt_nonneg x y)
  linarith

theorem value_nonneg : 0 ≤ S.value :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (G.μ_nonneg x y) (M.condWin_nonneg x y)

/-! ### Playing a strategy on another game -/

section Adapt

variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
  [DecidableEq A'] [DecidableEq B']

/-- **Play `S` on `G'`**, through a map `qA`, `qB` of `G'`'s questions into `G`'s and a
coarse-graining `rA`, `rB` of `G`'s answers into `G'`'s that may depend on the question: the
measurement at a question `x'` of `G'` is the one `S` uses at `qA x'`, with its outcomes merged
along `rA x'`. A coarse-graining of a projective measurement is projective. -/
def adapt (G' : Game X' Y' A' B') (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A')
    (rB : Y' → B → B') : M.ProjStrat G' where
  PA x' := (S.PA (qA x')).map (rA x')
  PB y' := (S.PB (qB y')).map (rB y')
  projA x' := POVMIn.isPVMIn_map (S.projA (qA x')) (rA x')
  projB y' := POVMIn.isPVMIn_map (S.projB (qB y')) (rB y')
  ψ_unit := S.ψ_unit

/-- **The adapted strategy fails no more often**, at a question pair where every tuple `G`
accepts is still accepted after coarse-graining. -/
theorem failAt_adapt_le (G' : Game X' Y' A' B') (qA : X' → X) (qB : Y' → Y)
    (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (hD : ∀ a b, G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    (S.adapt G' qA qB rA rB).failAt x' y' ≤ S.failAt (qA x') (qB y') :=
  M.condFail_adapt_le S.PA S.PB G' qA qB rA rB x' y' hD

/-- **Relabel a strategy along equivalences** of the questions and the answers. -/
def relabel (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y) (eA : A' ≃ A) (eB : B' ≃ B) :
    M.ProjStrat G' :=
  S.adapt G' eX eY (fun _ => eA.symm) (fun _ => eB.symm)

/-- **Relabelling keeps the value**, when the equivalences carry `G'` onto `G`. -/
theorem value_relabel (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y) (eA : A' ≃ A)
    (eB : B' ≃ B) (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel G' eX eY eA eB).value = S.value :=
  M.povmValue_relabel S.PA S.PB G' eX eY eA eB hμ hD

end Adapt

/-- **Restrict a strategy to other questions**: the same measurements, asked at the images of the
new questions; the answers are kept. -/
def restrict {X' Y' : Type*} [Fintype X'] [Fintype Y'] (G' : Game X' Y' A B) (qA : X' → X)
    (qB : Y' → Y) : M.ProjStrat G' where
  PA x' := S.PA (qA x')
  PB y' := S.PB (qB y')
  projA x' := S.projA (qA x')
  projB y' := S.projB (qB y')
  ψ_unit := S.ψ_unit

end ProjStrat

/-! ## The inconsistency of two families of measurements -/

section Inconsistency

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {X : Type*} [Fintype X]

/-- **The inconsistency** of the first player's family `P` and the second player's `Q` on the
index weighted by `μ`: the weight of the outcome pairs that differ. The matrix `inconsistency`
is its tensor-product instance (`inconsistency_eq_tensor`). -/
def inconsistency (μ : X → ℝ) (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) : ℝ :=
  ∑ x, μ x * ∑ a, ∑ b, if a = b then 0 else M.bornProb ((P x).op a) ((Q x).op b)

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- The inconsistency is the weighted disagreement. -/
theorem inconsistency_eq_sum_dis (hψ : ‖M.ψ‖ = 1) (μ : X → ℝ) (P : X → POVMIn Λ 𝒜)
    (Q : X → POVMIn Λ ℬ) : M.inconsistency μ P Q = ∑ x, μ x * M.dis (P x) (Q x) := by
  unfold inconsistency
  simp only [M.dis_eq_sum_ne hψ]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- On a uniform index, the inconsistency is the average disagreement. -/
theorem inconsistency_uniform (hψ : ‖M.ψ‖ = 1) (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M.inconsistency (uniform X) P Q = (∑ x, M.dis (P x) (Q x)) / Fintype.card X := by
  rw [M.inconsistency_eq_sum_dis hψ]
  simp only [uniform, ← Finset.mul_sum]
  rw [inv_mul_eq_div]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **A bound on the inconsistency on a uniform index is a bound on the summed disagreement.** -/
theorem sum_dis_le_of_inconsistency (hψ : ‖M.ψ‖ = 1) (P : X → POVMIn Λ 𝒜)
    (Q : X → POVMIn Λ ℬ) {δ : ℝ} (h : M.inconsistency (uniform X) P Q ≤ δ) :
    ∑ x, M.dis (P x) (Q x) ≤ Fintype.card X * δ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [M.inconsistency_uniform hψ, div_le_iff₀ hc] at h
  linarith

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- On a one-point index, the inconsistency is the disagreement. -/
theorem inconsistency_uniform_unit (hψ : ‖M.ψ‖ = 1) (P : POVMIn Λ 𝒜) (Q : POVMIn Λ ℬ) :
    M.inconsistency (uniform Unit) (fun _ => P) (fun _ => Q) = M.dis P Q := by
  rw [M.inconsistency_uniform hψ]
  simp

end Inconsistency

end BipartiteModel

/-- **The matrix inconsistency is the inconsistency in the tensor-product model.** -/
theorem inconsistency_eq_tensor {X Λ : Type*} [Fintype X] [Fintype Λ] [DecidableEq Λ]
    {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] (μ : X → ℝ)
    (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    inconsistency μ ψ M N
      = (BipartiteModel.tensor ψ).inconsistency μ (fun x => (M x).toIn) (fun x => (N x).toIn) := by
  unfold inconsistency BipartiteModel.inconsistency
  simp only [POVM.toIn_op, ← bornProb_eq_tensor]
  rfl

/-! ## The tensor-product model -/

namespace TensorProductStrategy

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] {G : Game X Y A B}

/-- **A tensor-product strategy is a projective strategy in its tensor-product model**: its
measurements as POVMs in the two matrix algebras. -/
noncomputable def toModel (T : TensorProductStrategy G) :
    (BipartiteModel.tensor T.ψ).ProjStrat G where
  PA x := (T.PA.toPOVM x).toIn
  PB y := (T.PB.toPOVM y).toIn
  projA x := by classical exact (T.PA.isPVM_at x).toIn
  projB y := by classical exact (T.PB.isPVM_at y).toIn
  ψ_unit := norm_evec_eq_one T.ψ_unit

theorem value_toModel (T : TensorProductStrategy G) : T.toModel.value = T.value :=
  T.value_eq_tensor_povmValue.symm

theorem failAt_toModel (T : TensorProductStrategy G) (x : X) (y : Y) :
    T.toModel.failAt x y = T.failAt x y :=
  (T.failAt_eq_tensor_condFail x y).symm

end TensorProductStrategy

/-- A vector of `ℂ^N` whose `EuclideanSpace` norm is one is a unit vector. -/
theorem star_dotProduct_self_eq_one {N : Type*} [Fintype N] {ψ : N → ℂ} (h : ‖evec ψ‖ = 1) :
    star ψ ⬝ᵥ ψ = 1 := by
  have hre := norm_evec_sq ψ
  rw [h, one_pow] at hre
  have him : (star ψ ⬝ᵥ ψ).im = 0 := by
    simp only [dotProduct, Complex.im_sum, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  exact Complex.ext hre.symm him

namespace BipartiteModel.ProjStrat

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] {G : Game X Y A B}
  {a b : ℕ} {ψ : Fin a × Fin b → ℂ}

/-- **A projective strategy in the tensor-product model of a state on `Fin a × Fin b` is a
tensor-product strategy**, on the same state. -/
noncomputable def toTensor (S : (tensor ψ).ProjStrat G) : TensorProductStrategy G where
  dA := a
  dB := b
  ψ := ψ
  ψ_unit := star_dotProduct_self_eq_one S.ψ_unit
  PA := ProjectiveMeasurement.ofIsPVM (fun x => (S.PA x).toPOVM) fun x => (S.projA x).toIsPVM
  PB := ProjectiveMeasurement.ofIsPVM (fun y => (S.PB y).toPOVM) fun y => (S.projB y).toIsPVM

theorem value_toTensor (S : (tensor ψ).ProjStrat G) : S.toTensor.value = S.value := by
  rw [TensorProductStrategy.value_eq_tensor_povmValue]
  rfl

end BipartiteModel.ProjStrat

/-! ## The commuting-operator model -/

namespace BipartiteModel.ProjStrat

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel.{0} 𝒞 𝒜 ℬ}

/-- **The value of a projective strategy in a model on a Hilbert space is at most `ω_co`**: it is
a commuting-operator strategy (`BipartiteModel.toCommuting`). -/
theorem value_le_commutingOperatorValue {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] {G : Game X Y A B} (S : M.ProjStrat G) :
    S.value ≤ commutingOperatorValue G :=
  M.povmValue_le_commutingOperatorValue S.ψ_unit S.PA S.PB G

end BipartiteModel.ProjStrat

/-- **`ω_co` is approached by projective strategies in the models of commuting-operator
strategies** (`exists_isPVMIn_lt_povmValue`). -/
theorem exists_projStrat_lt_commutingOperatorValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] {G : Game X Y A B} {t : ℝ} (ht : 0 ≤ t)
    (h : t < commutingOperatorValue G) :
    ∃ S : CommutingOperatorStrategy X Y A B, ∃ R : S.toModel.ProjStrat G, t < R.value := by
  obtain ⟨S, hA, hB, hv⟩ := exists_isPVMIn_lt_povmValue ht h
  exact ⟨S, ⟨S.aliceMeas, S.bobMeas, hA, hB, S.toModel_ψ_norm⟩, hv⟩

/-! ## Value models dominating a bipartite model -/

namespace ValueModel

/-- **The value model dominates the projective strategies of a bipartite model**: each has value
at most the value of its game. -/
def Dominates {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
    [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    [PartialOrder ℬ] [StarOrderedRing ℬ] (ω : ValueModel) (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] (G : Game X Y A B)
    (S : M.ProjStrat G), S.value ≤ ω.val G

/-- **`val*` dominates the tensor-product model** of a state on `Fin a × Fin b`: a projective
strategy in it is a tensor-product strategy. -/
theorem tensor_dominates {a b : ℕ} (ψ : Fin a × Fin b → ℂ) :
    tensor.Dominates (BipartiteModel.tensor ψ) := fun G S => by
  rw [← S.value_toTensor]
  exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) _

/-- **`ω_co` dominates every bipartite model on a Hilbert space.** -/
theorem commuting_dominates {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜]
    [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] (M : BipartiteModel.{0} 𝒞 𝒜 ℬ) :
    commuting.Dominates M := fun _ S => S.value_le_commutingOperatorValue

end ValueModel

end MIPRE

end
