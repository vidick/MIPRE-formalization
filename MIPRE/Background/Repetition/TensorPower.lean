/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.Repetition.Direct
import MIPRE.Foundations.TensorFamily
import MIPRE.Foundations.GameDouble

/-!
# Tensor powers of synchronous strategies

The completeness half of `thm:parallel-repetition` at the level of games: the `k`-fold tensor
power of a PCC synchronous strategy of value `1` is a PCC synchronous strategy of value `1` for
the `k`-fold direct repetition (blueprint `def:direct-repetition`).

* `ProjectiveMeasurement.tensorPow P k`: the family `x⃗ ↦ a⃗ ↦ ⊗ᵢ M^{xᵢ}_{aᵢ}` on
  `ℂ^{Fin k → Fin d}` (`MIPRE.tensorFamily`), a projective measurement family on the repeated
  alphabets; `ProjectiveMeasurement.reindexMat` carries it to `ℂ^{d^k}`, the shape
  `SyncStrategy` asks for.
* `SyncStrategy.tensorPow S k : SyncStrategy (H.repeat k)`, with `value = S.value ^ k`
  (`value_tensorPow`) and PCC when `S` is (`isPCC_tensorPow`): the normalized trace on
  `ℂ^{d^k}` of a tensor product is the product of the normalized traces, and the direct
  repetition's distribution and predicate are products, so every summand of the value
  factorizes and the sum over `k`-tuples of questions and answers is the `k`-th power of the sum
  (`sum_pi_prod`).
* The doubled reading that `Verifier.HasPerfectPCC` uses: a strategy of `G.doubled` gives, by
  the tensor power read on the tag of the first coordinate, one of `(G.repeat k).doubled`
  (`SyncStrategy.tensorPowDoubled`), with the same value power and PCC, and
  `exists_perfectPCC_repeat_doubled` is the statement consumed downstream.
-/

namespace MIPRE

open Matrix

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

/-! ## Reindexing a measurement family along an equivalence of the index set -/

/-- The trace is invariant under reindexing along an equivalence. -/
theorem trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (M : Matrix ι ι ℂ) : (M.submatrix e.symm e.symm).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm fun i => M i i

namespace ProjectiveMeasurement

/-- Transport of a projective measurement family on `ℂ^ι` to `ℂ^κ` along `ι ≃ κ`. -/
def reindexMat {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (P : ProjectiveMeasurement X A (Matrix ι ι ℂ)) : ProjectiveMeasurement X A (Matrix κ κ ℂ) where
  M x a := (P.M x a).submatrix e.symm e.symm
  selfAdjoint x a := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      ← Matrix.star_eq_conjTranspose, P.selfAdjoint]
  projective x a := by rw [Matrix.submatrix_mul_equiv, P.projective]
  normalized x := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.submatrix_apply]
    rw [← Matrix.sum_apply, P.normalized]
    simp [Matrix.one_apply]

omit [Fintype X] [DecidableEq A] in
@[simp] theorem reindexMat_M {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (P : ProjectiveMeasurement X A (Matrix ι ι ℂ)) (x : X) (a : A) :
    (P.reindexMat e).M x a = (P.M x a).submatrix e.symm e.symm := rfl

omit [Fintype X] [DecidableEq A] in
theorem reindexMat_trace_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (e : ι ≃ κ) (P : ProjectiveMeasurement X A (Matrix ι ι ℂ)) (x y : X)
    (a b : A) :
    ((P.reindexMat e).M x a * (P.reindexMat e).M y b).trace = (P.M x a * P.M y b).trace := by
  rw [reindexMat_M, reindexMat_M, Matrix.submatrix_mul_equiv, trace_submatrix_equiv]

/-- The `k`-fold tensor power of a measurement family: `x⃗ ↦ a⃗ ↦ ⊗ᵢ M^{xᵢ}_{aᵢ}`. -/
def tensorPow {d : ℕ} (P : ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) :
    ProjectiveMeasurement (Fin k → X) (Fin k → A)
      (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) where
  M x a := tensorFamily fun i => P.M (x i) (a i)
  selfAdjoint x a := tensorFamily_star fun i => P.selfAdjoint _ _
  projective x a := tensorFamily_mul_self fun i => P.projective _ _
  normalized x := by
    rw [sum_tensorFamily]
    simp only [P.normalized]
    exact tensorFamily_one

omit [Fintype X] [DecidableEq A] in
@[simp] theorem tensorPow_M {d : ℕ} (P : ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ))
    (k : ℕ) (x : Fin k → X) (a : Fin k → A) :
    (P.tensorPow k).M x a = tensorFamily fun i => P.M (x i) (a i) := rfl

end ProjectiveMeasurement

/-- `(Fin k → Fin d) ≃ Fin (d ^ k)`. -/
noncomputable def equivFinPow (d k : ℕ) : (Fin k → Fin d) ≃ Fin (d ^ k) :=
  Fintype.equivFinOfCardEq (by simp)

/-! ## The trace of a product of two projections is real -/

/-- For self-adjoint idempotents `P`, `Q` on `ℂ^d` (`d > 0`), `Tr(PQ)` is real. -/
theorem trace_mul_im_eq_zero {d : ℕ} (hd : 0 < d) {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : star P = P) (hPP : P * P = P) (hQ : star Q = Q) (hQQ : Q * Q = Q) :
    (P * Q).trace.im = 0 := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have h := (normalizedTrace (Fin d)).nonneg_mul hP hPP hQ hQQ
  rw [normalizedTrace_apply, Complex.le_def] at h
  have him := h.2
  rw [Complex.zero_im, Complex.mul_im, Fintype.card_fin] at him
  have h1 : ((d : ℂ)⁻¹).im = 0 := by simp
  have h2 : ((d : ℂ)⁻¹).re = (d : ℝ)⁻¹ := by simp
  rw [h1, h2, zero_mul, add_zero] at him
  have hd' : (d : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
  exact (mul_eq_zero.1 him.symm).resolve_left hd'

/-- The normalized trace of a tensor product of pairs of projections is the product of the
normalized traces, in real parts. -/
theorem re_trace_tensorFamily_div {d k : ℕ} (hd : 0 < d)
    (P Q : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ i, star (P i) = P i) (hPP : ∀ i, P i * P i = P i)
    (hQ : ∀ i, star (Q i) = Q i) (hQQ : ∀ i, Q i * Q i = Q i) :
    (tensorFamily P * tensorFamily Q).trace.re / ((d ^ k : ℕ) : ℝ) =
      ∏ i, (P i * Q i).trace.re / (d : ℝ) := by
  rw [tensorFamily_mul, trace_tensorFamily]
  have hreal : ∀ i, (P i * Q i).trace = (((P i * Q i).trace.re : ℝ) : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [trace_mul_im_eq_zero hd (hP i) (hPP i) (hQ i) (hQQ i)])
  rw [Finset.prod_congr rfl fun i _ => hreal i, ← Complex.ofReal_prod, Complex.ofReal_re,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl

/-! ## Sums over tuples -/

/-- A sum over `k`-tuples of a product of per-coordinate terms is the `k`-th power of the
single-coordinate sum. -/
theorem sum_pi_prod {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (f : X → Y → A → B → ℝ) (k : ℕ) :
    (∑ x : Fin k → X, ∑ y : Fin k → Y, ∑ a : Fin k → A, ∑ b : Fin k → B,
        ∏ i, f (x i) (y i) (a i) (b i)) =
      (∑ x, ∑ y, ∑ a, ∑ b, f x y a b) ^ k := by
  -- the right-hand side as a product over `Fin k` of one sum over the product alphabet
  have hR : (∑ x, ∑ y, ∑ a, ∑ b, f x y a b) =
      ∑ q : X × Y × A × B, f q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  have hpow : (∑ q : X × Y × A × B, f q.1 q.2.1 q.2.2.1 q.2.2.2) ^ k =
      ∏ _i : Fin k, ∑ q : X × Y × A × B, f q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hR, hpow, Fintype.prod_sum]
  -- the left-hand side as one sum over the product of the tuple types
  have hL : (∑ x : Fin k → X, ∑ y : Fin k → Y, ∑ a : Fin k → A, ∑ b : Fin k → B,
        ∏ i, f (x i) (y i) (a i) (b i)) =
      ∑ p : (Fin k → X) × (Fin k → Y) × (Fin k → A) × (Fin k → B),
        ∏ i, f (p.1 i) (p.2.1 i) (p.2.2.1 i) (p.2.2.2 i) := by
    simp only [Fintype.sum_prod_type]
  rw [hL]
  refine Fintype.sum_equiv
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A) (fun _ => B)).symm)).trans
      ((Equiv.prodCongr (Equiv.refl _)
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Y) (fun _ => A × B)).symm).trans
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => X) (fun _ => Y × A × B)).symm))
    _ _ fun p => ?_
  rfl

/-! ## The tensor power of a synchronous strategy -/

namespace SyncStrategy

variable {H : SynchronousGame X A}

/-- The `k`-fold tensor power of a synchronous strategy, a strategy for the `k`-fold direct
repetition: dimension `d ^ k`, measurements `⊗ᵢ M^{xᵢ}_{aᵢ}`. -/
noncomputable def tensorPow (S : SyncStrategy H) (k : ℕ) : SyncStrategy (H.repeat k) where
  d := S.d ^ k
  d_pos := pow_pos S.d_pos k
  P := (S.P.tensorPow k).reindexMat (equivFinPow S.d k)

/-- The per-coordinate weight of a strategy: `μ(x, y) · [D(x, y, a, b)] · Tr(M^x_a M^y_b)/d`. -/
noncomputable def weight (S : SyncStrategy H) (x y : X) (a b : A) : ℝ :=
  H.μ x y * (if H.D x y a b then 1 else 0) * ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))

theorem value_eq_sum_weight (S : SyncStrategy H) :
    S.value = ∑ x, ∑ y, ∑ a, ∑ b, S.weight x y a b := S.value_eq

/-- The summand of the tensor power's value factorizes over the coordinates. -/
theorem weight_tensorPow (S : SyncStrategy H) (k : ℕ) (x y : Fin k → X) (a b : Fin k → A) :
    (S.tensorPow k).weight x y a b = ∏ i, S.weight (x i) (y i) (a i) (b i) := by
  unfold weight
  have htr : ((S.tensorPow k).P.M x a * (S.tensorPow k).P.M y b).trace.re /
      ((S.tensorPow k).d : ℝ) = ∏ i, (S.P.M (x i) (a i) * S.P.M (y i) (b i)).trace.re / (S.d : ℝ) := by
    change (((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M x a *
      ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M y b).trace.re / ((S.d ^ k : ℕ) : ℝ) = _
    rw [ProjectiveMeasurement.reindexMat_trace_mul, ProjectiveMeasurement.tensorPow_M,
      ProjectiveMeasurement.tensorPow_M]
    exact re_trace_tensorFamily_div S.d_pos _ _ (fun i => S.P.selfAdjoint _ _)
      (fun i => S.P.projective _ _) (fun i => S.P.selfAdjoint _ _) (fun i => S.P.projective _ _)
  rw [htr]
  have hμ : (H.repeat k).μ x y = ∏ i, H.μ (x i) (y i) := rfl
  have hD : (if (H.repeat k).D x y a b then (1 : ℝ) else 0) =
      ∏ i, if H.D (x i) (y i) (a i) (b i) then (1 : ℝ) else 0 := by
    show (if decide (∀ i, H.D (x i) (y i) (a i) (b i) = true) = true then (1 : ℝ) else 0) = _
    rw [Finset.prod_boole]
    simp
  rw [hμ, hD, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- **The value of the tensor power is the power of the value.** -/
theorem value_tensorPow (S : SyncStrategy H) (k : ℕ) : (S.tensorPow k).value = S.value ^ k := by
  rw [value_eq_sum_weight, value_eq_sum_weight, ← sum_pi_prod]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact weight_tensorPow S k x y a b

/-- A positive product weight has positive factors. -/
theorem μ_pos_of_repeat_pos {k : ℕ} {x y : Fin k → X} (h : 0 < (H.repeat k).μ x y) (i : Fin k) :
    0 < H.μ (x i) (y i) := by
  rcases (H.μ_nonneg (x i) (y i)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have : (H.repeat k).μ x y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) heq.symm
    rw [this] at h
    exact lt_irrefl 0 h

/-- **The tensor power of a PCC strategy is PCC.** -/
theorem isPCC_tensorPow {S : SyncStrategy H} (hS : S.IsPCC) (k : ℕ) : (S.tensorPow k).IsPCC := by
  intro x y hxy a b
  have hpos := μ_pos_of_repeat_pos hxy
  have h : ∀ i, S.P.M (x i) (a i) * S.P.M (y i) (b i) = S.P.M (y i) (b i) * S.P.M (x i) (a i) :=
    fun i => hS _ _ (hpos i) _ _
  change ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M x a *
      ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M y b =
    ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M y b *
      ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M x a
  rw [ProjectiveMeasurement.reindexMat_M, ProjectiveMeasurement.reindexMat_M,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ProjectiveMeasurement.tensorPow_M,
    ProjectiveMeasurement.tensorPow_M, tensorFamily_mul, tensorFamily_mul]
  congr 2
  funext i
  exact h i

end SyncStrategy

/-! ## The doubled reading -/

namespace SyncStrategy

variable {G : Game X X A A}

/-- The tensor power of a strategy of the doubled game, read on the doubled repeated game: the
tag is that of every coordinate. -/
noncomputable def tensorPowDoubled (S : SyncStrategy G.doubled) (k : ℕ) :
    SyncStrategy (G.repeat k).doubled :=
  (S.tensorPow k).relabel (G.repeat k).doubled (fun p i => (p.1, p.2 i)) (Equiv.refl _)

theorem value_tensorPowDoubled (S : SyncStrategy G.doubled) (k : ℕ) :
    (S.tensorPowDoubled k).value = S.value ^ k := by
  rw [value_eq, value_eq]
  rw [show (∑ p, ∑ q, ∑ a, ∑ b, (G.repeat k).doubled.μ p q *
      (if (G.repeat k).doubled.D p q a b then (1 : ℝ) else 0) *
      (((S.tensorPowDoubled k).P.M p a * (S.tensorPowDoubled k).P.M q b).trace.re /
        ((S.tensorPowDoubled k).d : ℝ))) = _ from Game.sum_doubled (G.repeat k) _]
  rw [show (∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q * (if G.doubled.D p q a b then (1 : ℝ) else 0) *
      ((S.P.M p a * S.P.M q b).trace.re / (S.d : ℝ))) = _ from Game.sum_doubled G _]
  rw [← sum_pi_prod]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  -- the summand of the doubled repeated game against the relabeled tensor power
  have htr : (((S.tensorPowDoubled k).P.M (false, x) a * (S.tensorPowDoubled k).P.M (true, y) b).trace.re /
      ((S.tensorPowDoubled k).d : ℝ)) =
      ∏ i, (S.P.M (false, x i) (a i) * S.P.M (true, y i) (b i)).trace.re / (S.d : ℝ) := by
    change (((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M (fun i => (false, x i)) a *
      ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M (fun i => (true, y i)) b).trace.re /
        ((S.d ^ k : ℕ) : ℝ) = _
    rw [ProjectiveMeasurement.reindexMat_trace_mul, ProjectiveMeasurement.tensorPow_M,
      ProjectiveMeasurement.tensorPow_M]
    exact re_trace_tensorFamily_div S.d_pos _ _ (fun i => S.P.selfAdjoint _ _)
      (fun i => S.P.projective _ _) (fun i => S.P.selfAdjoint _ _) (fun i => S.P.projective _ _)
  rw [htr]
  have hμ : (G.repeat k).μ x y = ∏ i, G.μ (x i) (y i) := rfl
  have hD : (if (G.repeat k).D x y a b then (1 : ℝ) else 0) =
      ∏ i, if G.D (x i) (y i) (a i) (b i) then (1 : ℝ) else 0 := by
    show (if decide (∀ i, G.D (x i) (y i) (a i) (b i) = true) = true then (1 : ℝ) else 0) = _
    rw [Finset.prod_boole]
    simp
  rw [hμ, hD, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

theorem isPCC_tensorPowDoubled {S : SyncStrategy G.doubled} (hS : S.IsPCC) (k : ℕ) :
    (S.tensorPowDoubled k).IsPCC := by
  refine isPCC_relabel_of_support (isPCC_tensorPow hS k) _ _ _ fun p q hpq => ?_
  rw [Game.doubled_μ] at hpq
  split_ifs at hpq with h
  · show 0 < ∏ i, G.doubled.μ (p.1, p.2 i) (q.1, q.2 i)
    have : ∀ i, G.doubled.μ (p.1, p.2 i) (q.1, q.2 i) = G.μ (p.2 i) (q.2 i) := fun i => by
      simp [Game.doubled_μ, h.1, h.2]
    simp only [this]
    exact hpq
  · exact absurd hpq (lt_irrefl 0)

end SyncStrategy

/-- **Game-level completeness of direct repetition**: a value-`1` PCC strategy of the doubled
game gives one of the doubled `k`-fold repetition, for every `k`. -/
theorem exists_perfectPCC_repeat_doubled {G : Game X X A A} (k : ℕ)
    (h : ∃ S : SyncStrategy G.doubled, S.IsPCC ∧ S.value = 1) :
    ∃ S' : SyncStrategy (G.repeat k).doubled, S'.IsPCC ∧ S'.value = 1 := by
  obtain ⟨S, hS, hv⟩ := h
  exact ⟨S.tensorPowDoubled k, SyncStrategy.isPCC_tensorPowDoubled hS k, by
    rw [SyncStrategy.value_tensorPowDoubled, hv, one_pow]⟩

end MIPRE
