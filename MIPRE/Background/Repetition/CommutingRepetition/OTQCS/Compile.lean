/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/OTQCS/Compile.lean
-/
/-
# OTQCS: compilation into full commuting POVMs (node 1.3.8)

Anchors: 06_otqcs.tex, eqs amplified-resource, Atilde, Btilde,
first-success-Kraus, all-fail, Ahat, Bhat, first-success-telescope,
common-index-mass; appendix_otqcs.tex, eqs one-trial-branch-norms,
common-index-vector, left-pullback, right-pullback (app:otqcs-povm).

Encoding decisions (DIFFERENCES.md D18):

* The tensor power `N̂ = N₁^{⊗R}` (eq amplified-resource) is consumed
  through `TensorPowerData`: some standard-form algebra with one
  ∗-embedding per tensor factor, commuting between distinct factors,
  whose trace multiplies over ordered products of single-factor
  elements. The sorried root `exists_tensorPowerData` is work package
  B3b (algebraic tensor powers, positivity of the product state, GNS).
  The resource state `Ω = ω₀^{⊗R}` is the GNS image of the ordered
  product of the embedded one-trial matrices (`tensorState`).
* The compiled effects follow eqs Ahat/Bhat verbatim: Alice pulls the
  target back as `K* Ã K` on the left, Bob as `K B̃ K*` on the right
  (the two orientations of eqs left-pullback/right-pullback).
* The branch content of the appendix (eqs one-trial-branch-norms +
  common-index-vector) is consumed as ONE decomposition statement:
  the compiled answer law equals `commonMass · (law of the selected
  state z_{st} under the original POVMs)` plus a nonnegative remainder
  of total mass `1 − commonMass` — the common-index branches versus
  everything else (mismatched indices, one-sided success, exhaustion,
  fallback corners). Eq finite-bad then bounds `1 − commonMass`
  by `2Γ + 2 e^{−R/(2Z)}` scalar-side.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.Selected
import MIPRE.Background.Repetition.CommutingRepetition.OTQCS.PairLaw
import MIPRE.Background.Repetition.CommutingRepetition.VN.TensorPower

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

universe u v w

/-- **Tensor power in consumed form** (06_otqcs.tex, eq
amplified-resource): a standard-form algebra `N̂` with one unital
∗-embedding per tensor factor, images at distinct factors commuting,
and the trace multiplicative over ordered products with one element
from each factor. Work package B3b provides the instance
(`exists_tensorPowerData`). -/
structure TensorPowerData (N₁ : StdTracialAlgebra.{u}) (R : ℕ) where
  Nhat : StdTracialAlgebra.{u}
  emb : Fin R → (N₁.A →⋆ₐ[ℂ] Nhat.A)
  emb_commute : ∀ ⦃i j : Fin R⦄, i ≠ j → ∀ a b : N₁.A,
    Commute (emb i a) (emb j b)
  trace_prod : ∀ f : Fin R → N₁.A,
    Nhat.τ (List.ofFn fun j => emb j (f j)).prod = ∏ j, N₁.τ (f j)

/-- Existence of tensor powers of a standard tracial algebra (work
package B3b; 06_otqcs.tex, thm otqcs item 1 "finitely many normalized
matrix amplifications and tensor powers"). -/
theorem exists_tensorPowerData (N₁ : StdTracialAlgebra.{u}) (R : ℕ) :
    Nonempty (TensorPowerData N₁ R) :=
  ⟨{ Nhat := StdTracialAlgebra.tensorPow N₁ R
     emb := StdTracialAlgebra.tensorPowIncl N₁ R
     emb_commute := StdTracialAlgebra.tensorPowIncl_commute N₁ R
     trace_prod := StdTracialAlgebra.tensorPow_trace_prod N₁ R }⟩

/-- The product state vector: the GNS image of the ordered product of
one copy of `u` per factor — `ω^{⊗R}` for `ω = ι(u)` (06_otqcs.tex, eq
amplified-resource, `Ω = ω₀^{⊗R}`). -/
noncomputable def tensorState {N₁ : StdTracialAlgebra.{u}} {R : ℕ}
    (D : TensorPowerData N₁ R) (u : N₁.A) : D.Nhat.H :=
  D.Nhat.ι (List.ofFn fun j => D.emb j u).prod

/-! ### Algebraic positivity helpers (for the compiled-effect positivity) -/

/-- A self-adjoint idempotent is algebraically positive: `a = (star a) * a`. -/
theorem isPosElem_of_projection {A : Type*} [Ring A] [StarRing A] {a : A}
    (hsa : star a = a) (hidem : a * a = a) : IsPosElem a := by
  have h : star a * a = a := by rw [hsa]; exact hidem
  exact h ▸ isPosElem_star_mul_self a

/-- Conjugation preserves algebraic positivity: `star k * x * k` for positive `x`. -/
theorem IsPosElem.conjug {A : Type*} [Ring A] [StarRing A] {x : A} (hx : IsPosElem x) (k : A) :
    IsPosElem (star k * x * k) := by
  obtain ⟨n, c, rfl⟩ := hx
  refine ⟨n, fun i => c i * k, ?_⟩
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul]; noncomm_ring

/-- Mirror conjugation `k * x * star k` for positive `x`. -/
theorem IsPosElem.conjug' {A : Type*} [Ring A] [StarRing A] {x : A} (hx : IsPosElem x) (k : A) :
    IsPosElem (k * x * star k) := by
  have := hx.conjug (star k); rwa [star_star] at this

/-- A `⋆`-algebra homomorphism maps positive elements to positive elements. -/
theorem IsPosElem.starAlgHom_map {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (f : A →⋆ₐ[ℂ] B) {x : A} (hx : IsPosElem x) : IsPosElem (f x) := by
  obtain ⟨n, c, rfl⟩ := hx
  refine ⟨n, fun i => f (c i), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_star]

/-- The diagonal matrix corner `single i i P` of a positive `P` is positive. -/
theorem single_isPosElem {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [Ring A] [StarRing A]
    (i : n) {P : A} (hP : IsPosElem P) : IsPosElem (Matrix.single i i P : Matrix n n A) := by
  obtain ⟨k, c, rfl⟩ := hP
  refine ⟨k, fun l => Matrix.single i i (c l), ?_⟩
  have hsum : (Matrix.single i i (∑ l, star (c l) * c l) : Matrix n n A)
      = ∑ l, Matrix.single i i (star (c l) * c l) := by
    rw [← Matrix.singleAddMonoidHom_apply, map_sum]
    simp only [Matrix.singleAddMonoidHom_apply]
  rw [hsum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, Matrix.single_mul_single_same]

/-- `noncommProd` of a pairwise-commuting family of self-adjoint idempotents is a
self-adjoint idempotent. -/
theorem noncommProd_proj {A : Type*} [Ring A] [StarRing A] {ι : Type*} [DecidableEq ι]
    (g : ι → A) (hsa : ∀ i, star (g i) = g i) (hidem : ∀ i, g i * g i = g i)
    (hcomm : ∀ i j, Commute (g i) (g j)) :
    ∀ (s : Finset ι) (comm), star (Finset.noncommProd s g comm) = Finset.noncommProd s g comm
      ∧ Finset.noncommProd s g comm * Finset.noncommProd s g comm
          = Finset.noncommProd s g comm := by
  intro s
  induction s using Finset.induction with
  | empty => intro comm; rw [Finset.noncommProd_empty]; refine ⟨?_, ?_⟩ <;> simp
  | insert a s' ha ih =>
    intro comm
    obtain ⟨ihsa, ihid⟩ := ih (comm.mono fun _ => Finset.mem_insert_of_mem)
    have hC : Commute (g a)
        (Finset.noncommProd s' g (comm.mono fun _ => Finset.mem_insert_of_mem)) :=
      Finset.noncommProd_commute s' g (comm.mono fun _ => Finset.mem_insert_of_mem) (g a)
        (fun i _ => hcomm a i)
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    generalize hQ : Finset.noncommProd s' g (comm.mono fun _ => Finset.mem_insert_of_mem) = Q at *
    refine ⟨?_, ?_⟩
    · rw [star_mul, hsa a, ihsa, hC.eq]
    · rw [show (g a * Q) * (g a * Q) = g a * (Q * g a) * Q by noncomm_ring, ← hC.eq,
        show g a * (g a * Q) * Q = (g a * g a) * (Q * Q) by noncomm_ring, hidem a, ihid]

/-- Hence such a `noncommProd` is algebraically positive. -/
theorem noncommProd_isPosElem {A : Type*} [Ring A] [StarRing A] {ι : Type*} [DecidableEq ι]
    (g : ι → A) (hsa : ∀ i, star (g i) = g i) (hidem : ∀ i, g i * g i = g i)
    (hcomm : ∀ i j, Commute (g i) (g j)) (s : Finset ι) (comm) :
    IsPosElem (Finset.noncommProd s g comm) := by
  obtain ⟨h1, h2⟩ := noncommProd_proj g hsa hidem hcomm s comm
  exact isPosElem_of_projection h1 h2

/-- **First-success telescope** for a pairwise-commuting family `q` (eq
first-success-telescope): `∑_j (∏_{ℓ<j} q_ℓ)(1 − q_j) + ∏_ℓ q_ℓ = 1`. -/
theorem noncommProd_prefix_telescope {A : Type*} [Ring A] {R : ℕ} (q : Fin R → A)
    (hcomm : ∀ i j, Commute (q i) (q j)) :
    (∑ j : Fin R,
        Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
          (fun a _ b _ _ => hcomm a b) * (1 - q j))
      + Finset.noncommProd Finset.univ q (fun a _ b _ _ => hcomm a b) = 1 := by
  classical
  have hcp : ∀ (s : Finset (Fin R)),
      (↑s : Set (Fin R)).Pairwise (Function.onFun Commute q) :=
    fun s a _ b _ _ => hcomm a b
  set P : ℕ → A := fun k =>
    Finset.noncommProd (Finset.univ.filter (fun ℓ : Fin R => (ℓ : ℕ) < k)) q
      (hcp _) with hPdef
  have hP0 : P 0 = 1 := by
    have hemp : (Finset.univ.filter (fun ℓ : Fin R => (ℓ : ℕ) < 0)) = ∅ :=
      Finset.filter_false_of_mem (fun ℓ _ => Nat.not_lt_zero (ℓ : ℕ))
    simp only [hPdef]
    rw [hemp, Finset.noncommProd_empty]
  have hPR : P R = Finset.noncommProd Finset.univ q (fun a _ b _ _ => hcomm a b) := by
    have hall : (Finset.univ.filter (fun ℓ : Fin R => (ℓ : ℕ) < R)) = Finset.univ :=
      Finset.filter_true_of_mem (fun ℓ _ => ℓ.is_lt)
    simp only [hPdef]
    rw [hall]
  have hpref : ∀ j : Fin R,
      Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q (fun a _ b _ _ => hcomm a b)
        = P (j : ℕ) := fun j => rfl
  have hstep : ∀ j : Fin R, P (j : ℕ) * q j = P ((j : ℕ) + 1) := by
    intro j
    have hfilter : Finset.univ.filter (fun ℓ : Fin R => (ℓ : ℕ) < (j : ℕ) + 1)
        = insert j (Finset.univ.filter (fun ℓ : Fin R => (ℓ : ℕ) < (j : ℕ))) := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
        · exact Or.inr h'
        · exact Or.inl (Fin.val_injective h')
      · rintro (rfl | h')
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt h'
    have hnotmem : j ∉ Finset.univ.filter (fun ℓ : Fin R => (ℓ : ℕ) < (j : ℕ)) := by simp
    simp only [hPdef]
    rw [hfilter, Finset.noncommProd_insert_of_notMem' _ _ _ _ hnotmem]
  have hterm : ∀ j : Fin R,
      P (j : ℕ) * (1 - q j) = P (j : ℕ) - P ((j : ℕ) + 1) := by
    intro j
    rw [mul_sub, mul_one, hstep j]
  calc (∑ j : Fin R,
          Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
            (fun a _ b _ _ => hcomm a b) * (1 - q j))
        + Finset.noncommProd Finset.univ q (fun a _ b _ _ => hcomm a b)
      = (∑ j : Fin R, (P (j : ℕ) - P ((j : ℕ) + 1))) + P R := by
        rw [hPR]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpref j, hterm j]
    _ = (∑ k ∈ Finset.range R, (P k - P (k + 1))) + P R := by
        rw [Fin.sum_univ_eq_sum_range (fun k => P k - P (k + 1)) R]
    _ = (P 0 - P R) + P R := by rw [Finset.sum_range_sub' P R]
    _ = 1 := by rw [hP0]; abel

/-- Ordered products of two families interleave factorwise when the factors at
distinct indices commute across the families. -/
theorem ofFn_prod_mul_ofFn_prod {A : Type*} [Monoid A] {R : ℕ} (p q : Fin R → A)
    (h : ∀ i j, i ≠ j → Commute (p i) (q j)) :
    (List.ofFn p).prod * (List.ofFn q).prod = (List.ofFn fun j => p j * q j).prod := by
  induction R with
  | zero => simp [List.ofFn_zero]
  | succ R ih =>
    have hc : Commute (List.ofFn fun i => p i.succ).prod (q 0) := by
      apply Commute.list_prod_left
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact h _ _ (Fin.succ_ne_zero i)
    have ih' := ih (fun i => p i.succ) (fun i => q i.succ)
      (fun i j hij => h _ _ (fun e => hij (Fin.succ_inj.mp e)))
    simp only [List.ofFn_succ, List.prod_cons, mul_assoc]
    rw [← ih', hc.left_comm]

/-- The star of an ordered product of a pairwise-commuting family is the ordered
product of the stars (the reversal is absorbed by the commutation). -/
theorem ofFn_prod_star {A : Type*} [Monoid A] [StarMul A] {R : ℕ} (p : Fin R → A)
    (h : ∀ i j, i ≠ j → Commute (p i) (p j)) :
    star (List.ofFn p).prod = (List.ofFn fun j => star (p j)).prod := by
  induction R with
  | zero => simp [List.ofFn_zero]
  | succ R ih =>
    have hc : Commute (List.ofFn fun i => star (p i.succ)).prod (star (p 0)) := by
      apply Commute.list_prod_left
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact (h _ _ (Fin.succ_ne_zero i)).star_star
    have ih' := ih (fun i => p i.succ)
      (fun i j hij => h _ _ (fun e => hij (Fin.succ_inj.mp e)))
    simp only [List.ofFn_succ, List.prod_cons, star_mul]
    rw [ih', hc.eq]

/-- Proof-side helper: the product state of a unit vector is a unit vector,
`‖ω^{⊗R}‖² = ∏_j τ(ω*ω) = 1`, from `trace_prod` after interleaving the two
ordered products through the cross-factor commutation. -/
theorem tensorState_norm {N₁ : StdTracialAlgebra.{u}} {R : ℕ} (D : TensorPowerData N₁ R)
    (u : N₁.A) (hu : ‖N₁.ι u‖ = 1) : ‖tensorState D u‖ = 1 := by
  have hτ : N₁.τ (star u * u) = 1 := by
    rw [← N₁.ι_inner u u, inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have hstar : star (List.ofFn fun j => D.emb j u).prod
      = (List.ofFn fun j => D.emb j (star u)).prod := by
    rw [ofFn_prod_star (fun j => D.emb j u) (fun i j hij => D.emb_commute hij _ _)]
    simp only [map_star]
  have hprod : star (List.ofFn fun j => D.emb j u).prod * (List.ofFn fun j => D.emb j u).prod
      = (List.ofFn fun j => D.emb j (star u * u)).prod := by
    rw [hstar, ofFn_prod_mul_ofFn_prod (fun j => D.emb j (star u)) (fun j => D.emb j u)
      (fun i j hij => D.emb_commute hij _ _)]
    simp only [map_mul]
  have hinner : ⟪tensorState D u, tensorState D u⟫_ℂ = 1 := by
    rw [tensorState, D.Nhat.ι_inner, hprod, D.trace_prod (fun _ => star u * u)]
    simp [hτ]
  have h2 : ‖tensorState D u‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (tensorState D u), hinner]
    simp
  rw [← Real.sqrt_sq (norm_nonneg (tensorState D u)), h2, Real.sqrt_one]

/-! ### Tensor words and the diagonal branch trace

Proof-side toolkit for the branch decomposition (`compile_decomposition`): ordered
products with one embedded element per tensor factor, the pairing algebra of a
standard tracial algebra, and the factorization of a Kraus-branch pairing over the
tensor factors (appendix eq common-index-vector). -/

/-! ### Ordered products with one entry per index -/

/-- A `List.ofFn` product whose entries are `1` except at `j` equals the entry at `j`. -/
theorem ofFn_prod_ite_eq {A : Type*} [Monoid A] {R : ℕ} (j : Fin R) (f : Fin R → A) :
    (List.ofFn fun ℓ : Fin R => if ℓ = j then f ℓ else 1).prod = f j := by
  induction R with
  | zero => exact j.elim0
  | succ R ih =>
    cases j using Fin.cases with
    | zero =>
      have htail : (List.ofFn fun i : Fin R =>
          if i.succ = (0 : Fin (R + 1)) then f i.succ else 1).prod = 1 := by
        simp only [Fin.succ_ne_zero, ite_false, List.ofFn_const, List.prod_replicate, one_pow]
      rw [List.ofFn_succ, List.prod_cons, if_pos rfl, htail, mul_one]
    | succ i =>
      have hfun : (fun i' : Fin R => if i'.succ = i.succ then f i'.succ else 1)
          = fun i' => if i' = i then (fun k : Fin R => f k.succ) i' else 1 := by
        funext i'
        simp only [Fin.succ_inj]
      rw [List.ofFn_succ, List.prod_cons, if_neg (Fin.succ_ne_zero i).symm, one_mul, hfun]
      exact ih i (fun k => f k.succ)

/-! ### Tensor words -/

/-- The ordered product of one embedded element per tensor factor. -/
noncomputable def tensorWord {N₁ : StdTracialAlgebra.{u}} {R : ℕ} (D : TensorPowerData N₁ R)
    (g : Fin R → N₁.A) : D.Nhat.A :=
  (List.ofFn fun ℓ => D.emb ℓ (g ℓ)).prod

section TensorWord

variable {N₁ : StdTracialAlgebra.{u}} {R : ℕ} (D : TensorPowerData N₁ R)

theorem tensorWord_mul (g g' : Fin R → N₁.A) :
    tensorWord D g * tensorWord D g' = tensorWord D fun ℓ => g ℓ * g' ℓ := by
  unfold tensorWord
  rw [ofFn_prod_mul_ofFn_prod (fun ℓ => D.emb ℓ (g ℓ)) (fun ℓ => D.emb ℓ (g' ℓ))
    (fun i j hij => D.emb_commute hij _ _)]
  simp only [map_mul]

theorem tensorWord_star (g : Fin R → N₁.A) :
    star (tensorWord D g) = tensorWord D fun ℓ => star (g ℓ) := by
  unfold tensorWord
  rw [ofFn_prod_star (fun ℓ => D.emb ℓ (g ℓ)) (fun i j hij => D.emb_commute hij _ _)]
  simp only [map_star]

theorem tensorWord_one : tensorWord D (fun _ => (1 : N₁.A)) = 1 := by
  unfold tensorWord
  simp only [map_one, List.ofFn_const, List.prod_replicate, one_pow]

theorem tensorWord_single (j : Fin R) (x : N₁.A) :
    D.emb j x = tensorWord D fun ℓ => if ℓ = j then x else 1 := by
  unfold tensorWord
  have h : (fun ℓ : Fin R => D.emb ℓ (if ℓ = j then x else 1))
      = fun ℓ => if ℓ = j then D.emb ℓ x else 1 := by
    funext ℓ
    split_ifs <;> simp
  rw [h]
  exact (ofFn_prod_ite_eq j (fun ℓ => D.emb ℓ x)).symm

theorem tensorWord_trace (g : Fin R → N₁.A) :
    D.Nhat.τ (tensorWord D g) = ∏ ℓ, N₁.τ (g ℓ) :=
  D.trace_prod g

theorem noncommProd_eq_tensorWord (s : Finset (Fin R)) (f : Fin R → N₁.A) (comm) :
    Finset.noncommProd s (fun ℓ => D.emb ℓ (f ℓ)) comm
      = tensorWord D fun ℓ => if ℓ ∈ s then f ℓ else 1 := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.noncommProd_empty]
    simp only [Finset.notMem_empty, ite_false]
    exact (tensorWord_one D).symm
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, ih, tensorWord_single D a (f a),
      tensorWord_mul]
    congr 1
    funext ℓ
    by_cases h : ℓ = a
    · subst h
      simp [ha]
    · simp [h]

end TensorWord

/-! ### Pairing algebra -/

namespace StdTracialAlgebra

variable (M : StdTracialAlgebra.{u})

theorem pairing_add_left (σ u₁ u₂ w : M.A) :
    M.τ (star σ * ((u₁ + u₂) * σ * w))
      = M.τ (star σ * (u₁ * σ * w)) + M.τ (star σ * (u₂ * σ * w)) := by
  rw [← map_add]; congr 1; noncomm_ring

theorem pairing_add_right (σ u w₁ w₂ : M.A) :
    M.τ (star σ * (u * σ * (w₁ + w₂)))
      = M.τ (star σ * (u * σ * w₁)) + M.τ (star σ * (u * σ * w₂)) := by
  rw [← map_add]; congr 1; noncomm_ring

theorem pairing_sum_left {ι : Type*} (s : Finset ι) (σ : M.A) (u : ι → M.A) (w : M.A) :
    M.τ (star σ * ((∑ i ∈ s, u i) * σ * w)) = ∑ i ∈ s, M.τ (star σ * (u i * σ * w)) := by
  rw [← map_sum]; congr 1; simp only [Finset.sum_mul, Finset.mul_sum]

theorem pairing_sum_right {ι : Type*} (s : Finset ι) (σ u : M.A) (w : ι → M.A) :
    M.τ (star σ * (u * σ * ∑ i ∈ s, w i)) = ∑ i ∈ s, M.τ (star σ * (u * σ * w i)) := by
  rw [← map_sum]; congr 1; simp only [Finset.mul_sum]

/-- Tracial cyclicity moves the common-branch pairing onto the branch vector
`ζ = V ω Wv`. -/
theorem pairing_cyc (ω V Wv At Bt : M.A) :
    M.τ (star ω * ((star V * At * V) * ω * (Wv * Bt * star Wv)))
      = M.τ (star (V * (ω * Wv)) * (At * (V * (ω * Wv)) * Bt)) := by
  rw [show star ω * ((star V * At * V) * ω * (Wv * Bt * star Wv))
      = (star ω * star V * At * V * ω * Wv * Bt) * star Wv by noncomm_ring,
    M.τ_mul_comm]
  congr 1
  simp only [star_mul, mul_assoc]

/-- The joint-failure pairing from the one-trial success traces
(appendix eq one-trial-branch-norms, first line). -/
theorem fail_both_trace (ω P Q : M.A) {a b c : ℂ}
    (h1 : M.τ (star ω * ω) = 1) (hP : M.τ (star ω * (P * ω)) = a)
    (hQ : M.τ (star ω * (ω * Q)) = b) (hPQ : M.τ (star ω * (P * ω * Q)) = c) :
    M.τ (star ω * ((1 - P) * ω * (1 - Q))) = 1 - a - b + c := by
  rw [show star ω * ((1 - P) * ω * (1 - Q))
      = star ω * ω - star ω * (P * ω) - star ω * (ω * Q) + star ω * (P * ω * Q) by
        noncomm_ring,
    map_add, map_sub, map_sub, h1, hP, hQ, hPQ]

end StdTracialAlgebra

/-- `1 - p` is idempotent when `p` is. -/
theorem one_sub_mul_one_sub_of_idem {A : Type*} [Ring A] {p : A} (hp : p * p = p) :
    (1 - p) * (1 - p) = 1 - p := by
  rw [sub_mul, one_mul, mul_sub, mul_one, hp, sub_self, sub_zero]

/-- The `x^j` bookkeeping: a product over `Fin R` that is `x` before `j`, `T` at `j`
and `1` after `j`. -/
theorem prod_ite_lt_eq_pow_mul {R : ℕ} (j : Fin R) (x T : ℂ) :
    (∏ ℓ : Fin R, (if ℓ < j then x else if ℓ = j then T else 1)) = x ^ (j : ℕ) * T := by
  classical
  have hsplit : ∀ ℓ : Fin R, (if ℓ < j then x else if ℓ = j then T else 1)
      = (if (ℓ : ℕ) < (j : ℕ) then x else 1) * (if ℓ = j then T else 1) := by
    intro ℓ
    by_cases hlt : ℓ < j
    · rw [if_pos hlt, if_pos (Fin.lt_def.mp hlt), if_neg (ne_of_lt hlt), mul_one]
    · rw [if_neg hlt, if_neg (fun h => hlt (Fin.lt_def.mpr h)), one_mul]
  rw [Finset.prod_congr rfl (fun ℓ _ => hsplit ℓ), Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ j (fun _ => T), if_pos (Finset.mem_univ j),
    ← Finset.prod_filter, Finset.prod_const, Fin.card_filter_val_lt,
    min_eq_right (le_of_lt j.isLt)]

/-- **Diagonal branch trace**: for a common first-success index `j`, the pairing of
the two compiled Kraus branches on the product state factorizes over the tensor
factors — joint failure (`x`) before `j`, the erased common branch (`T`) at `j`,
the untouched unit resource after `j` (appendix eq common-index-vector). -/
theorem diag_term_trace {M₁ : StdTracialAlgebra.{u}} {R : ℕ} (D : TensorPowerData M₁ R)
    (ω P Q V Wv At Bt : M₁.A) (hPsa : star P = P) (hPid : P * P = P)
    (hQsa : star Q = Q) (hQid : Q * Q = Q) {x T : ℂ}
    (h1 : M₁.τ (star ω * ω) = 1)
    (hx : M₁.τ (star ω * ((1 - P) * ω * (1 - Q))) = x)
    (hT : M₁.τ (star ω * ((star V * At * V) * ω * (Wv * Bt * star Wv))) = T)
    (j : Fin R)
    (commP : ((Finset.univ.filter fun ℓ : Fin R => ℓ < j) : Set (Fin R)).Pairwise
      (Function.onFun Commute fun ℓ => D.emb ℓ (1 - P)))
    (commQ : ((Finset.univ.filter fun ℓ : Fin R => ℓ < j) : Set (Fin R)).Pairwise
      (Function.onFun Commute fun ℓ => D.emb ℓ (1 - Q))) :
    D.Nhat.τ (star (tensorWord D fun _ => ω) *
      ((star (D.emb j V * Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
            (fun ℓ => D.emb ℓ (1 - P)) commP)
          * D.emb j At *
          (D.emb j V * Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
            (fun ℓ => D.emb ℓ (1 - P)) commP))
        * tensorWord D (fun _ => ω) *
        ((Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
            (fun ℓ => D.emb ℓ (1 - Q)) commQ * D.emb j Wv)
          * D.emb j Bt *
          star (Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
            (fun ℓ => D.emb ℓ (1 - Q)) commQ * D.emb j Wv))))
      = x ^ (j : ℕ) * T := by
  classical
  set kA : Fin R → M₁.A := fun ℓ => if ℓ < j then 1 - P else if ℓ = j then V else 1 with hkA
  set kB : Fin R → M₁.A := fun ℓ => if ℓ < j then 1 - Q else if ℓ = j then Wv else 1 with hkB
  have hKA : D.emb j V * Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
      (fun ℓ => D.emb ℓ (1 - P)) commP = tensorWord D kA := by
    rw [noncommProd_eq_tensorWord D _ (fun _ => 1 - P) commP, tensorWord_single D j V,
      tensorWord_mul]
    congr 1
    funext ℓ
    simp only [hkA, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : ℓ < j
    · simp only [if_pos hlt, if_neg (ne_of_lt hlt), one_mul]
    · simp only [if_neg hlt, mul_one]
  have hKB : Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
      (fun ℓ => D.emb ℓ (1 - Q)) commQ * D.emb j Wv
      = tensorWord D kB := by
    rw [noncommProd_eq_tensorWord D _ (fun _ => 1 - Q) commQ, tensorWord_single D j Wv,
      tensorWord_mul]
    congr 1
    funext ℓ
    simp only [hkB, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : ℓ < j
    · simp only [if_pos hlt, if_neg (ne_of_lt hlt), mul_one]
    · simp only [if_neg hlt, one_mul]
  have e1 : star (1 - P) * 1 * (1 - P) = 1 - P := by
    rw [star_sub, star_one, hPsa, mul_one, one_sub_mul_one_sub_of_idem hPid]
  have e2 : (1 - Q) * 1 * star (1 - Q) = 1 - Q := by
    rw [star_sub, star_one, hQsa, mul_one, one_sub_mul_one_sub_of_idem hQid]
  rw [hKA, hKB, tensorWord_single D j At, tensorWord_single D j Bt]
  simp only [tensorWord_star, tensorWord_mul, tensorWord_trace]
  rw [← prod_ite_lt_eq_pow_mul j x T]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  simp only [hkA, hkB]
  by_cases hlt : ℓ < j
  · have hne : ℓ ≠ j := ne_of_lt hlt
    simp only [if_pos hlt, if_neg hne]
    rw [e1, e2]
    exact hx
  · by_cases heq : ℓ = j
    · subst heq
      simp only [if_neg hlt, ite_true]
      exact hT
    · simp only [if_neg hlt, if_neg heq, star_one, mul_one, one_mul]
      exact h1

section Compile

variable {N : StdTracialAlgebra.{u}} {S : Type v} {T : Type w}
variable {x : S → N.H} {y : T → N.H} (F : ModulusFamily N x y)
variable {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ)
variable {R : ℕ}
  (D : TensorPowerData (StdTracialAlgebra.amplify N (m + 1)) R)
variable {Aa : Type*} {Bb : Type*}
variable (E : S → Aa → N.A) (G : T → Bb → N.A)

open Classical in
/-- Alice's extended target effect
`Ã_s^a = e_{★★} ⊗ A_s^a + 1_{a=a₀} (1 − e_{★★} ⊗ 1)`
(06_otqcs.tex, eq Atilde). -/
noncomputable def tildeA (a₀ : Aa) (s : S) (a : Aa) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.single (Fin.last m) (Fin.last m) (E s a) +
    if a = a₀ then
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) -
        Matrix.single (Fin.last m) (Fin.last m) (1 : N.A)
    else 0

open Classical in
/-- Bob's extended target effect
`B̃_t^b = e_{★★} ⊗ B_t^b + 1_{b=b₀} (1 − e_{★★} ⊗ 1)`
(06_otqcs.tex, eq Btilde). -/
noncomputable def tildeB (b₀ : Bb) (t' : T) (b : Bb) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) N.A :=
  Matrix.single (Fin.last m) (Fin.last m) (G t' b) +
    if b = b₀ then
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) -
        Matrix.single (Fin.last m) (Fin.last m) (1 : N.A)
    else 0

/-- Alice's first-success Kraus element
`K^A_{s,j} = V_{s,j} ∏_{ℓ<j} (1 − P_{s,ℓ})` (06_otqcs.tex, eq
first-success-Kraus). -/
noncomputable def krausA (s : S) (j : Fin R) : D.Nhat.A :=
  D.emb j (trialVA N F B s) *
    Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
      (fun ℓ => D.emb ℓ ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialPA N F B s))
      (fun _ _ _ _ h => D.emb_commute h _ _)

/-- Bob's first-success Kraus element
`K^B_{t,j} = (∏_{ℓ<j} (1 − Q_{t,ℓ})) W_{t,j} v̄_{t,j}` (06_otqcs.tex,
eq first-success-Kraus). -/
noncomputable def krausB (t' : T) (j : Fin R) : D.Nhat.A :=
  Finset.noncommProd (Finset.univ.filter fun ℓ => ℓ < j)
      (fun ℓ => D.emb ℓ ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialQB N F B t'))
      (fun _ _ _ _ h => D.emb_commute h _ _) *
    D.emb j (trialWB N F B t' * trialVbar N F t')

/-- Alice's all-fail projection `F_s^A = ∏_{j} (1 − P_{s,j})`
(06_otqcs.tex, eq all-fail). -/
noncomputable def allFailA (s : S) : D.Nhat.A :=
  Finset.noncommProd Finset.univ
    (fun ℓ => D.emb ℓ ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialPA N F B s))
    (fun _ _ _ _ h => D.emb_commute h _ _)

/-- Bob's all-fail projection `F_t^B = ∏_{j} (1 − Q_{t,j})`
(06_otqcs.tex, eq all-fail). -/
noncomputable def allFailB (t' : T) : D.Nhat.A :=
  Finset.noncommProd Finset.univ
    (fun ℓ => D.emb ℓ ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialQB N F B t'))
    (fun _ _ _ _ h => D.emb_commute h _ _)

open Classical in
/-- Alice's compiled effect
`Â_s^a = ∑_j (K^A_{s,j})* Ã_{s,j}^a K^A_{s,j} + 1_{a=a₀} F_s^A`
(06_otqcs.tex, eq Ahat). -/
noncomputable def hatA (a₀ : Aa) (s : S) (a : Aa) : D.Nhat.A :=
  (∑ j : Fin R,
    star (krausA F B D s j) * D.emb j (tildeA E a₀ s a) *
      krausA F B D s j) +
    if a = a₀ then allFailA F B D s else 0

open Classical in
/-- Bob's compiled effect
`B̂_t^b = ∑_j K^B_{t,j} B̃_{t,j}^b (K^B_{t,j})* + 1_{b=b₀} F_t^B`
(06_otqcs.tex, eq Bhat) — note the mirrored pullback orientation
(appendix eq right-pullback). -/
noncomputable def hatB (b₀ : Bb) (t' : T) (b : Bb) : D.Nhat.A :=
  (∑ j : Fin R,
    krausB F B D t' j * D.emb j (tildeB G b₀ t' b) *
      star (krausB F B D t' j)) +
    if b = b₀ then allFailB F B D t' else 0

/-- `P_s` is self-adjoint (its band spectral projections are self-adjoint). -/
theorem trialPA_sa (s : S) : star (trialPA N F B s) = trialPA N F B s := by
  rw [trialPA, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp [Pi.star_apply]
  | cast j => simp only [Pi.star_apply, Fin.lastCases_castSucc]; exact (F.dataA s).proj_star (B j)

/-- `P_s` is idempotent (the band spectral projections are, given measurability). -/
theorem trialPA_idem (hB : IsBandFamily B t) (s : S) :
    trialPA N F B s * trialPA N F B s = trialPA N F B s := by
  rw [trialPA, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j =>
    simp only [Fin.lastCases_castSucc]
    rw [(F.dataA s).proj_inter (B j) (B j) (hB.meas j) (hB.meas j), Set.inter_self]

/-- `Q_t` is self-adjoint. -/
theorem trialQB_sa (t' : T) : star (trialQB N F B t') = trialQB N F B t' := by
  rw [trialQB, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp [Pi.star_apply]
  | cast j => simp only [Pi.star_apply, Fin.lastCases_castSucc]; exact (F.dataB t').proj_star (B j)

/-- `Q_t` is idempotent. -/
theorem trialQB_idem (hB : IsBandFamily B t) (t' : T) :
    trialQB N F B t' * trialQB N F B t' = trialQB N F B t' := by
  rw [trialQB, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j =>
    simp only [Fin.lastCases_castSucc]
    rw [(F.dataB t').proj_inter (B j) (B j) (hB.meas j) (hB.meas j), Set.inter_self]

/-- For a `∗`-embedding `emb i` and a self-adjoint idempotent `p`, the image
`emb i (1 − p)` is a self-adjoint idempotent (the "bin ℓ failed" projection). -/
theorem emb_one_sub_proj {N₁ : StdTracialAlgebra.{u}} {R : ℕ}
    (D : TensorPowerData N₁ R) (i : Fin R) (p : N₁.A)
    (hsa : star p = p) (hidem : p * p = p) :
    star (D.emb i (1 - p)) = D.emb i (1 - p) ∧
      D.emb i (1 - p) * D.emb i (1 - p) = D.emb i (1 - p) := by
  refine ⟨?_, ?_⟩
  · rw [← map_star]; congr 1; rw [star_sub, star_one, hsa]
  · rw [← map_mul]; congr 1
    rw [mul_sub, mul_one, sub_mul, one_mul, hidem, sub_self, sub_zero]

/-- `Ã_s^a · e_{★★}⊗y = e_{★★} ⊗ (A_s^a y)`: the fallback part of `Ã` kills the corner. -/
theorem tildeA_mul_single (a₀ : Aa) (s : S) (a : Aa) (z : N.A) :
    (tildeA (m := m) E a₀ s a : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) *
        Matrix.single (Fin.last m) (Fin.last m) z
      = Matrix.single (Fin.last m) (Fin.last m) (E s a * z) := by
  classical
  rw [tildeA, add_mul, Matrix.single_mul_single_same]
  split_ifs with h
  · rw [sub_mul, one_mul, Matrix.single_mul_single_same, one_mul, sub_self, add_zero]
  · rw [zero_mul, add_zero]

/-- `e_{★★}⊗y · B̃_t^b = e_{★★} ⊗ (y B_t^b)`. -/
theorem single_mul_tildeB (b₀ : Bb) (t' : T) (b : Bb) (z : N.A) :
    Matrix.single (Fin.last m) (Fin.last m) z *
        (tildeB (m := m) G b₀ t' b : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A)
      = Matrix.single (Fin.last m) (Fin.last m) (z * G t' b) := by
  classical
  rw [tildeB, mul_add, Matrix.single_mul_single_same]
  split_ifs with h
  · rw [mul_sub, mul_one, Matrix.single_mul_single_same, mul_one, sub_self, add_zero]
  · rw [mul_zero, add_zero]

/-- The extended target effects are algebraically positive. -/
theorem tildeA_isPosElem (a₀ : Aa) (s : S) (hE : ∀ s a, IsPosElem (E s a)) (a : Aa) :
    IsPosElem (tildeA (m := m) E a₀ s a) := by
  classical
  rw [tildeA]
  apply IsPosElem.add
  · exact single_isPosElem (Fin.last m) (hE s a)
  · by_cases h : a = a₀
    · rw [if_pos h]
      apply isPosElem_of_projection
      · rw [star_sub, star_one]
        congr 1
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]
      · have he : (Matrix.single (Fin.last m) (Fin.last m) (1 : N.A) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) N.A)
            * Matrix.single (Fin.last m) (Fin.last m) (1 : N.A)
            = Matrix.single (Fin.last m) (Fin.last m) (1 : N.A) := by
          rw [Matrix.single_mul_single_same, one_mul]
        rw [mul_sub, mul_one, sub_mul, one_mul, he]
        abel
    · rw [if_neg h]; exact isPosElem_zero

theorem tildeB_isPosElem (b₀ : Bb) (t' : T) (hG : ∀ t' b, IsPosElem (G t' b)) (b : Bb) :
    IsPosElem (tildeB (m := m) G b₀ t' b) := by
  classical
  rw [tildeB]
  apply IsPosElem.add
  · exact single_isPosElem (Fin.last m) (hG t' b)
  · by_cases h : b = b₀
    · rw [if_pos h]
      apply isPosElem_of_projection
      · rw [star_sub, star_one]
        congr 1
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]
      · have he : (Matrix.single (Fin.last m) (Fin.last m) (1 : N.A) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) N.A)
            * Matrix.single (Fin.last m) (Fin.last m) (1 : N.A)
            = Matrix.single (Fin.last m) (Fin.last m) (1 : N.A) := by
          rw [Matrix.single_mul_single_same, one_mul]
        rw [mul_sub, mul_one, sub_mul, one_mul, he]
        abel
    · rw [if_neg h]; exact isPosElem_zero

/-- The all-fail projections are algebraically positive. -/
theorem allFailA_isPosElem (hB : IsBandFamily B t) (s : S) :
    IsPosElem (allFailA F B D s) := by
  rw [allFailA]
  apply noncommProd_isPosElem
  · intro i
    exact (emb_one_sub_proj D i (trialPA N F B s) (trialPA_sa F B s)
      (trialPA_idem F B t hB s)).1
  · intro i
    exact (emb_one_sub_proj D i (trialPA N F B s) (trialPA_sa F B s)
      (trialPA_idem F B t hB s)).2
  · intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact Commute.refl _
    · exact D.emb_commute hij _ _

theorem allFailB_isPosElem (hB : IsBandFamily B t) (t' : T) :
    IsPosElem (allFailB F B D t') := by
  rw [allFailB]
  apply noncommProd_isPosElem
  · intro i
    exact (emb_one_sub_proj D i (trialQB N F B t') (trialQB_sa F B t')
      (trialQB_idem F B t hB t')).1
  · intro i
    exact (emb_one_sub_proj D i (trialQB N F B t') (trialQB_sa F B t')
      (trialQB_idem F B t hB t')).2
  · intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact Commute.refl _
    · exact D.emb_commute hij _ _

/-- **The ★★-corner pairing**: on the erased common branch
`ζ = V ω₀ (W v̄) = e_{★★} ⊗ √((m+1)/Z) w_{st}`, the extended effects act through the
corner only: `τ₁(ζ* Ã ζ B̃) = Z⁻¹ τ(w* A w B)` (appendix eqs left-pullback and
right-pullback with the normalized corner identification). -/
theorem corner_pairing (s : S) (t' : T) (a₀ : Aa) (a : Aa) (b₀ : Bb) (b : Bb) :
    (StdTracialAlgebra.amplify N (m + 1)).τ
      ((star (trialVA N F B s * (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t'))) *
        (tildeA E a₀ s a *
          (trialVA N F B s * (trialUnitMat N m t * (trialWB N F B t' * trialVbar N F t'))) *
          tildeB G b₀ t' b) : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A))
      = ((bandZ t : ℝ) : ℂ)⁻¹ *
          N.τ (star (selWord (F.dataA s) (F.dataB t') B t) *
            (E s a * selWord (F.dataA s) (F.dataB t') B t * G t' b)) := by
  classical
  have hw : (∑ j, (t j : ℂ) •
      ((F.dataA s).proj (B j) * (F.dataB t').proj (B j) * (F.dataB t').v))
      = selWord (F.dataA s) (F.dataB t') B t := rfl
  rw [trialVA_mul_state_mul_WVbar N F B t s t', hw]
  set sc : ℂ := ((Real.sqrt ((m + 1) / bandZ t) : ℝ) : ℂ) with hsc
  set w : N.A := selWord (F.dataA s) (F.dataB t') B t with hw'
  have hbz : (0 : ℝ) ≤ bandZ t := by unfold bandZ; positivity
  have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have hsc_star : star sc = sc := by rw [hsc, Complex.star_def, Complex.conj_ofReal]
  have hscsq : sc * sc = ((((m : ℝ) + 1) / bandZ t : ℝ) : ℂ) := by
    rw [hsc, ← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg (by positivity) hbz)]
  rw [tildeA_mul_single, single_mul_tildeB, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single, Matrix.single_mul_single_same, ampτ_single]
  have hz : star (sc • w) * (E s a * (sc • w) * G t' b)
      = (sc * sc) • (star w * (E s a * w * G t' b)) := by
    rw [star_smul, hsc_star, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc sc (E s a * w) (G t' b), smul_mul_smul_comm]
  rw [hz, map_smul, smul_eq_mul, hscsq,
    show ((((m : ℝ) + 1) / bandZ t : ℝ) : ℂ) = ((m : ℂ) + 1) * ((bandZ t : ℝ) : ℂ)⁻¹ by
      push_cast; ring,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hm1, one_mul]

/-- The compiled Alice effects are algebraically positive
(06_otqcs.tex, "All effects in eqs Ahat–Bhat are positive"). -/
theorem hatA_isPosElem [Fintype Aa] (a₀ : Aa) (s : S)
    (hB : IsBandFamily B t)
    (hE : ∀ s a, IsPosElem (E s a)) (a : Aa) :
    IsPosElem (hatA F B D E a₀ s a) := by
  classical
  rw [hatA]
  apply IsPosElem.add
  · apply isPosElem_sum
    intro j _
    have htA := tildeA_isPosElem (m := m) E a₀ s hE a
    exact (htA.starAlgHom_map (D.emb j)).conjug (krausA F B D s j)
  · by_cases h : a = a₀
    · rw [if_pos h]; exact allFailA_isPosElem F B t D hB s
    · rw [if_neg h]; exact isPosElem_zero

/-- The compiled Bob effects are algebraically positive. -/
theorem hatB_isPosElem [Fintype Bb] (b₀ : Bb) (t' : T)
    (hB : IsBandFamily B t)
    (hG : ∀ t' b, IsPosElem (G t' b)) (b : Bb) :
    IsPosElem (hatB F B D G b₀ t' b) := by
  classical
  rw [hatB]
  apply IsPosElem.add
  · apply isPosElem_sum
    intro j _
    have htB := tildeB_isPosElem (m := m) G b₀ t' hG b
    exact (htB.starAlgHom_map (D.emb j)).conjug' (krausB F B D t' j)
  · by_cases h : b = b₀
    · rw [if_pos h]; exact allFailB_isPosElem F B t D hB t'
    · rw [if_neg h]; exact isPosElem_zero

/-- Alice's compiled family is a full POVM: the first-success
telescope (06_otqcs.tex, eq first-success-telescope, via
`V* V = P`). -/
theorem hatA_sum [Fintype Aa] (a₀ : Aa) (s : S) (hB : IsBandFamily B t)
    (hE1 : (∑ a, E s a) = 1) :
    (∑ a, hatA F B D E a₀ s a) = 1 := by
  classical
  set q : Fin R → D.Nhat.A :=
    fun ℓ => D.emb ℓ ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialPA N F B s) with hqdef
  have hqcomm : ∀ i j, Commute (q i) (q j) := by
    intro i j
    by_cases h : i = j
    · subst h; exact Commute.refl _
    · exact D.emb_commute h _ _
  have hqsa : ∀ ℓ, star (q ℓ) = q ℓ := by
    intro ℓ
    have hSA : star ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialPA N F B s)
        = 1 - trialPA N F B s := by rw [star_sub, star_one, trialPA_sa]
    exact (map_star (D.emb ℓ) _).symm.trans (congrArg (D.emb ℓ) hSA)
  have hqid : ∀ ℓ, q ℓ * q ℓ = q ℓ := by
    intro ℓ
    have hID : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialPA N F B s)
        * (1 - trialPA N F B s) = 1 - trialPA N F B s := by
      have := trialPA_idem F B t hB s
      rw [mul_sub, mul_one, sub_mul, one_mul, this]; abel
    exact (map_mul (D.emb ℓ) _ _).symm.trans (congrArg (D.emb ℓ) hID)
  -- q j = 1 - emb j (trialPA)
  have hqval : ∀ j : Fin R, q j = 1 - D.emb j (trialPA N F B s) := by
    intro j
    have he : D.emb j ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialPA N F B s)
        = D.emb j 1 - D.emb j (trialPA N F B s) := map_sub _ _ _
    show D.emb j ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialPA N F B s)
        = 1 - D.emb j (trialPA N F B s)
    rw [he, map_one]
  -- the star-Kraus-Kraus identity
  have hKK : ∀ j : Fin R, star (krausA F B D s j) * krausA F B D s j
      = Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
          (fun _ _ _ _ h => D.emb_commute h _ _) * (1 - q j) := by
    intro j
    set Pi := Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
      (fun _ _ _ _ h => D.emb_commute h _ _) with hPidef
    obtain ⟨hPisa, hPiid⟩ := noncommProd_proj q hqsa hqid hqcomm
      (Finset.univ.filter (fun ℓ => ℓ < j)) (fun _ _ _ _ h => D.emb_commute h _ _)
    have hVstar : star (D.emb j (trialVA N F B s)) = D.emb j (star (trialVA N F B s)) :=
      (map_star (D.emb j) _).symm
    have hVV : D.emb j (star (trialVA N F B s)) * D.emb j (trialVA N F B s)
        = D.emb j (trialPA N F B s) :=
      (map_mul (D.emb j) _ _).symm.trans (congrArg (D.emb j) (trialVA_star_mul N F B t hB s))
    have hcommP : Commute (D.emb j (trialPA N F B s)) Pi := by
      rw [hPidef]
      refine Finset.noncommProd_commute _ _ _ _ (fun ℓ hℓ => ?_)
      exact D.emb_commute ((Finset.mem_filter.mp hℓ).2).ne' _ _
    have hkA : krausA F B D s j = D.emb j (trialVA N F B s) * Pi := rfl
    calc star (krausA F B D s j) * krausA F B D s j
        = (Pi * D.emb j (star (trialVA N F B s)))
            * (D.emb j (trialVA N F B s) * Pi) := by
          rw [hkA, star_mul, hPisa, hVstar]
      _ = Pi * (D.emb j (star (trialVA N F B s)) * D.emb j (trialVA N F B s)) * Pi := by
          noncomm_ring
      _ = Pi * D.emb j (trialPA N F B s) * Pi := by rw [hVV]
      _ = (Pi * Pi) * D.emb j (trialPA N F B s) := by
          rw [mul_assoc, hcommP.eq, ← mul_assoc]
      _ = Pi * D.emb j (trialPA N F B s) := by rw [hPiid]
      _ = Pi * (1 - q j) := by rw [hqval j, sub_sub_cancel]
  -- sum of tildeA over answers is 1
  have hsumtilde : (∑ a, tildeA (m := m) E a₀ s a) = 1 := by
    simp only [tildeA]
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ a₀
        (fun _ => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A)
          - Matrix.single (Fin.last m) (Fin.last m) 1)]
    simp only [Finset.mem_univ, if_true]
    have hs : (∑ a, Matrix.single (Fin.last m) (Fin.last m) (E s a) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) N.A)
        = Matrix.single (Fin.last m) (Fin.last m) (∑ a, E s a) := by
      rw [← Matrix.singleAddMonoidHom_apply, map_sum]
      simp only [Matrix.singleAddMonoidHom_apply]
    rw [hs, hE1]
    abel
  -- reduce the answer sum
  have hreduce : (∑ a, hatA F B D E a₀ s a)
      = (∑ j : Fin R,
          Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
            (fun _ _ _ _ h => D.emb_commute h _ _) * (1 - q j))
        + Finset.noncommProd Finset.univ q (fun _ _ _ _ h => D.emb_commute h _ _) := by
    simp only [hatA]
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ a₀ (fun _ => allFailA F B D s)]
    simp only [Finset.mem_univ, if_true]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hKK j]
      have h1 : (∑ a, star (krausA F B D s j) * D.emb j (tildeA E a₀ s a) * krausA F B D s j)
          = star (krausA F B D s j) * (∑ a, D.emb j (tildeA E a₀ s a)) * krausA F B D s j := by
        rw [Finset.mul_sum, Finset.sum_mul]
      have h2 : (∑ a, D.emb j (tildeA E a₀ s a)) = 1 := by
        have hstep : D.emb j (∑ a, tildeA E a₀ s a) = ∑ a, D.emb j (tildeA E a₀ s a) :=
          map_sum _ _ _
        rw [← hstep]
        exact (congrArg (D.emb j) hsumtilde).trans (map_one _)
      rw [h1, h2, mul_one]
  rw [hreduce]
  exact noncommProd_prefix_telescope q hqcomm

/-- Bob's compiled family is a full POVM (mirror telescope via
`W W* = Q`). -/
theorem hatB_sum [Fintype Bb] (b₀ : Bb) (t' : T) (hB : IsBandFamily B t)
    (hG1 : (∑ b, G t' b) = 1) :
    (∑ b, hatB F B D G b₀ t' b) = 1 := by
  classical
  set q : Fin R → D.Nhat.A :=
    fun ℓ => D.emb ℓ ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialQB N F B t') with hqdef
  have hqcomm : ∀ i j, Commute (q i) (q j) := by
    intro i j
    by_cases h : i = j
    · subst h; exact Commute.refl _
    · exact D.emb_commute h _ _
  have hqsa : ∀ ℓ, star (q ℓ) = q ℓ := by
    intro ℓ
    have hSA : star ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialQB N F B t')
        = 1 - trialQB N F B t' := by rw [star_sub, star_one, trialQB_sa]
    exact (map_star (D.emb ℓ) _).symm.trans (congrArg (D.emb ℓ) hSA)
  have hqid : ∀ ℓ, q ℓ * q ℓ = q ℓ := by
    intro ℓ
    have hID : ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialQB N F B t')
        * (1 - trialQB N F B t') = 1 - trialQB N F B t' := by
      have := trialQB_idem F B t hB t'
      rw [mul_sub, mul_one, sub_mul, one_mul, this]; abel
    exact (map_mul (D.emb ℓ) _ _).symm.trans (congrArg (D.emb ℓ) hID)
  have hqval : ∀ j : Fin R, q j = 1 - D.emb j (trialQB N F B t') := by
    intro j
    have he : D.emb j ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialQB N F B t')
        = D.emb j 1 - D.emb j (trialQB N F B t') := map_sub _ _ _
    show D.emb j ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A) - trialQB N F B t')
        = 1 - D.emb j (trialQB N F B t')
    rw [he, map_one]
  have hKK : ∀ j : Fin R, krausB F B D t' j * star (krausB F B D t' j)
      = Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
          (fun _ _ _ _ h => D.emb_commute h _ _) * (1 - q j) := by
    intro j
    set Pi := Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
      (fun _ _ _ _ h => D.emb_commute h _ _) with hPidef
    obtain ⟨hPisa, hPiid⟩ := noncommProd_proj q hqsa hqid hqcomm
      (Finset.univ.filter (fun ℓ => ℓ < j)) (fun _ _ _ _ h => D.emb_commute h _ _)
    have hWstar : star (D.emb j (trialWB N F B t' * trialVbar N F t'))
        = D.emb j (star (trialWB N F B t' * trialVbar N F t')) := (map_star (D.emb j) _).symm
    have hmat : (trialWB N F B t' * trialVbar N F t')
        * star (trialWB N F B t' * trialVbar N F t') = trialQB N F B t' := by
      rw [star_mul, ← mul_assoc]
      exact trialWB_vbar_initial N F B t hB t'
    have hWW : D.emb j (trialWB N F B t' * trialVbar N F t')
        * D.emb j (star (trialWB N F B t' * trialVbar N F t')) = D.emb j (trialQB N F B t') :=
      (map_mul (D.emb j) _ _).symm.trans (congrArg (D.emb j) hmat)
    have hcommQ : Commute (D.emb j (trialQB N F B t')) Pi := by
      rw [hPidef]
      refine Finset.noncommProd_commute _ _ _ _ (fun ℓ hℓ => ?_)
      exact D.emb_commute ((Finset.mem_filter.mp hℓ).2).ne' _ _
    have hkB : krausB F B D t' j = Pi * D.emb j (trialWB N F B t' * trialVbar N F t') := rfl
    calc krausB F B D t' j * star (krausB F B D t' j)
        = Pi * (D.emb j (trialWB N F B t' * trialVbar N F t')
            * D.emb j (star (trialWB N F B t' * trialVbar N F t'))) * Pi := by
          rw [hkB, star_mul, hPisa, hWstar]; noncomm_ring
      _ = Pi * D.emb j (trialQB N F B t') * Pi := by rw [hWW]
      _ = (Pi * Pi) * D.emb j (trialQB N F B t') := by
          rw [mul_assoc, hcommQ.eq, ← mul_assoc]
      _ = Pi * D.emb j (trialQB N F B t') := by rw [hPiid]
      _ = Pi * (1 - q j) := by rw [hqval j, sub_sub_cancel]
  have hsumtilde : (∑ b, tildeB (m := m) G b₀ t' b) = 1 := by
    simp only [tildeB]
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ b₀
        (fun _ => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) N.A)
          - Matrix.single (Fin.last m) (Fin.last m) 1)]
    simp only [Finset.mem_univ, if_true]
    have hs : (∑ b, Matrix.single (Fin.last m) (Fin.last m) (G t' b) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) N.A)
        = Matrix.single (Fin.last m) (Fin.last m) (∑ b, G t' b) := by
      rw [← Matrix.singleAddMonoidHom_apply, map_sum]
      simp only [Matrix.singleAddMonoidHom_apply]
    rw [hs, hG1]
    abel
  have hreduce : (∑ b, hatB F B D G b₀ t' b)
      = (∑ j : Fin R,
          Finset.noncommProd (Finset.univ.filter (fun ℓ => ℓ < j)) q
            (fun _ _ _ _ h => D.emb_commute h _ _) * (1 - q j))
        + Finset.noncommProd Finset.univ q (fun _ _ _ _ h => D.emb_commute h _ _) := by
    simp only [hatB]
    rw [Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ b₀ (fun _ => allFailB F B D t')]
    simp only [Finset.mem_univ, if_true]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hKK j]
      have h1 : (∑ b, krausB F B D t' j * D.emb j (tildeB G b₀ t' b) * star (krausB F B D t' j))
          = krausB F B D t' j * (∑ b, D.emb j (tildeB G b₀ t' b)) * star (krausB F B D t' j) := by
        rw [Finset.mul_sum, Finset.sum_mul]
      have h2 : (∑ b, D.emb j (tildeB G b₀ t' b)) = 1 := by
        have hstep : D.emb j (∑ b, tildeB G b₀ t' b) = ∑ b, D.emb j (tildeB G b₀ t' b) :=
          map_sum _ _ _
        rw [← hstep]
        exact (congrArg (D.emb j) hsumtilde).trans (map_one _)
      rw [h1, h2, mul_one]
  rw [hreduce]
  exact noncommProd_prefix_telescope q hqcomm

end Compile

/-- Total mass of the common-index branches with `R` retained trials:
`∑_{j=1}^{R} (1 − (a+b−c)/Z)^{j−1} (c/Z)` (06_otqcs.tex, eq
common-index-mass, summed). -/
noncomputable def commonMass (a b c Z : ℝ) (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.range R, (1 - (a + b - c) / Z) ^ j * (c / Z)

/-- **Finite bad-event bound** (node 1.3.6; 06_otqcs.tex, eq
finite-bad): outside the common-index branches — mismatched indices or
exhaustion — the total mass is at most `2Γ + 2 e^{−R/(2Z)}` when
`a, b ≥ 1/2` and `c ≤ min{a,b}`. -/
theorem finite_bad_bound (a b c Z : ℝ) (R : ℕ) (hZ : 0 < Z)
    (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) (hc : 0 ≤ c) (hca : c ≤ a)
    (hcb : c ≤ b) (hle : a + b - c ≤ Z) :
    1 - commonMass a b c Z R ≤
      2 * (a + b - 2 * c) + 2 * Real.exp (-(R : ℝ) / (2 * Z)) := by
  set d := a + b - c with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hdhalf : 1 / 2 ≤ d := by rw [hd_def]; linarith
  have hcd : c ≤ d := by rw [hd_def]; linarith
  have hρpos : 0 < d / Z := div_pos hd hZ
  have hρle : d / Z ≤ 1 := (div_le_one hZ).mpr hle
  set x := 1 - d / Z with hx
  have hxnn : 0 ≤ x := by rw [hx]; linarith
  have hx1 : x ≠ 1 := by
    rw [hx]; intro h; apply ne_of_gt hρpos; linarith
  -- commonMass in closed form
  have hcm : commonMass a b c Z R = (c / d) * (1 - x ^ R) := by
    unfold commonMass
    rw [← hd_def, ← Finset.sum_mul, geom_sum_eq hx1 R]
    have hxm1 : x - 1 = -(d / Z) := by rw [hx]; ring
    rw [hxm1]
    field_simp
    ring
  -- exhaustion tail
  have htail : x ^ R ≤ Real.exp (-(R : ℝ) / (2 * Z)) := by
    have := all_fail_bound d Z R hZ hdhalf hle
    rwa [← hx] at this
  have htailnn : 0 ≤ x ^ R := pow_nonneg hxnn R
  -- mismatch
  have hmis : (a + b - 2 * c) / d ≤ 2 * (a + b - 2 * c) := by
    have := first_success_mismatch a b c ha hb hc hca hcb
    rwa [← hd_def] at this
  -- assemble
  have h1mc : 1 - commonMass a b c Z R = (a + b - 2 * c) / d + (c / d) * x ^ R := by
    rw [hcm]
    have : (a + b - 2 * c) / d = 1 - c / d := by
      rw [hd_def] at *
      field_simp
      ring
    rw [this]
    ring
  rw [h1mc]
  have hcdd : c / d ≤ 1 := (div_le_one hd).mpr hcd
  have hcd0 : 0 ≤ c / d := div_nonneg hc (le_of_lt hd)
  have hterm2 : (c / d) * x ^ R ≤ 2 * Real.exp (-(R : ℝ) / (2 * Z)) := by
    calc (c / d) * x ^ R ≤ 1 * x ^ R := by
          apply mul_le_mul_of_nonneg_right hcdd htailnn
      _ = x ^ R := one_mul _
      _ ≤ Real.exp (-(R : ℝ) / (2 * Z)) := htail
      _ ≤ 2 * Real.exp (-(R : ℝ) / (2 * Z)) := by
          have := Real.exp_pos (-(R : ℝ) / (2 * Z)); linarith
  linarith [hmis, hterm2]

/-- **Branch decomposition of the compiled answer law** (node 1.3.8;
06_otqcs.tex, eqs Ahat + Bhat realizing eq common-index-mass;
appendix_otqcs.tex, eqs one-trial-branch-norms, common-index-vector,
left-pullback, right-pullback): on each pair `(s,t)`, the compiled
resource's answer law equals `commonMass` times the answer law of the
selected state `z_{st}` under the original POVMs, plus a nonnegative
remainder — the mismatched-index, one-sided-success, exhaustion, and
fallback-corner branches — of total mass `1 − commonMass`. Stated at
universe 0 with the signed `tracialPairLaw`. -/
theorem compile_decomposition {N : StdTracialAlgebra.{0}}
    {S T Aa Bb : Type} [Fintype Aa] [Fintype Bb]
    {x : S → N.H} {y : T → N.H} (F : ModulusFamily N x y)
    {m : ℕ} (B : Fin m → Set ℝ) (t : Fin m → ℝ) {R : ℕ}
    (D : TensorPowerData (StdTracialAlgebra.amplify N (m + 1)) R)
    (E : S → Aa → N.A) (G : T → Bb → N.A) (a₀ : Aa) (b₀ : Bb)
    (hB : IsBandFamily B t) (hZ : 0 < bandZ t)
    (hE_pos : ∀ s a, IsPosElem (E s a))
    (hG_pos : ∀ t' b, IsPosElem (G t' b))
    (hE_sum : ∀ s, (∑ a, E s a) = 1)
    (hG_sum : ∀ t', (∑ b, G t' b) = 1) (s : S) (t' : T) :
    ∃ r : Aa → Bb → ℝ, (∀ a b, 0 ≤ r a b) ∧
      (∑ a, ∑ b, r a b) =
        1 - commonMass (bandMassA F B t s) (bandMassB F B t t')
          (bandCross F B t s t') (bandZ t) R ∧
      ∀ a b,
        tracialPairLaw D.Nhat
            (fun _ _ => tensorState D (trialUnitMat N m t))
            (fun s a => hatA F B D E a₀ s a)
            (fun t' b => hatB F B D G b₀ t' b) s t' a b =
          commonMass (bandMassA F B t s) (bandMassB F B t t')
              (bandCross F B t s t') (bandZ t) R *
            tracialPairLaw N
              (fun s t'' =>
                selState (F.dataA s) (F.dataB t'') (F.joint s t'') B t)
              E G s t' a b +
            r a b := by
  classical
  -- The remainder is forced by the law equation: `r = compiled law − commonMass · selected law`.
  refine ⟨fun a b =>
      tracialPairLaw D.Nhat (fun _ _ => tensorState D (trialUnitMat N m t))
          (fun s a => hatA F B D E a₀ s a) (fun t' b => hatB F B D G b₀ t' b) s t' a b
        - commonMass (bandMassA F B t s) (bandMassB F B t t') (bandCross F B t s t') (bandZ t) R
          * tracialPairLaw N
              (fun s t'' => selState (F.dataA s) (F.dataB t'') (F.joint s t'') B t) E G s t' a b,
    ?_, ?_, ?_⟩
  · -- (1) `0 ≤ r a b`: the appendix branch analysis. Expanding `Â`/`B̂` (eqs Ahat/Bhat)
    -- inside the pairing, every branch term is a pairing of algebraically positive
    -- elements (the pullbacks of eqs left-pullback/right-pullback), hence nonnegative;
    -- the diagonal terms `j = j'` factorize over the tensor factors (eq
    -- common-index-vector: joint failure before `j`, the erased common branch at `j`,
    -- the unit resource after) into `(1 − (a+b−c)/Z)^j · (c/Z) · (selected law)` through
    -- the `★★`-corner pairing, and sum to `commonMass · (selected law)` (eq
    -- common-index-mass).
    intro a b
    rw [sub_nonneg]
    set Pω : D.Nhat.A := tensorWord D (fun _ => trialUnitMat N m t) with hPω
    set X : Fin R → D.Nhat.A := fun j =>
      star (krausA F B D s j) * D.emb j (tildeA E a₀ s a) * krausA F B D s j with hX
    set Y : Fin R → D.Nhat.A := fun j =>
      krausB F B D t' j * D.emb j (tildeB G b₀ t' b) * star (krausB F B D t' j) with hY
    set FA : D.Nhat.A := if a = a₀ then allFailA F B D s else 0 with hFA
    set FB : D.Nhat.A := if b = b₀ then allFailB F B D t' else 0 with hFB
    -- the compiled law as a pairing on the product word
    have hcomp : tracialPairLaw D.Nhat (fun _ _ => tensorState D (trialUnitMat N m t))
        (fun s a => hatA F B D E a₀ s a) (fun t' b => hatB F B D G b₀ t' b) s t' a b
        = (D.Nhat.τ (star Pω * (((∑ j, X j) + FA) * Pω * ((∑ j, Y j) + FB)))).re := by
      rw [tracialPairLaw]
      exact congrArg Complex.re
        (D.Nhat.inner_L_R Pω (hatA F B D E a₀ s a) Pω (hatB F B D G b₀ t' b))
    -- positivity of the branch pieces
    have hXpos : ∀ j, IsPosElem (X j) := fun j =>
      ((tildeA_isPosElem E a₀ s hE_pos a).starAlgHom_map (D.emb j)).conjug _
    have hYpos : ∀ j, IsPosElem (Y j) := fun j =>
      ((tildeB_isPosElem G b₀ t' hG_pos b).starAlgHom_map (D.emb j)).conjug' _
    have hFApos : IsPosElem FA := by
      rw [hFA]; split_ifs
      · exact allFailA_isPosElem F B t D hB s
      · exact isPosElem_zero
    have hFBpos : IsPosElem FB := by
      rw [hFB]; split_ifs
      · exact allFailB_isPosElem F B t D hB t'
      · exact isPosElem_zero
    have hnn : ∀ u w : D.Nhat.A, IsPosElem u → IsPosElem w →
        0 ≤ (D.Nhat.τ (star Pω * (u * Pω * w))).re :=
      fun u w hu hw => D.Nhat.pairing_nonneg Pω hu hw
    -- bilinear expansion of the pairing
    have hexp : D.Nhat.τ (star Pω * (((∑ j, X j) + FA) * Pω * ((∑ j, Y j) + FB)))
        = (∑ j, ∑ j', D.Nhat.τ (star Pω * (X j * Pω * Y j')))
          + (∑ j, D.Nhat.τ (star Pω * (X j * Pω * FB)))
          + (∑ j', D.Nhat.τ (star Pω * (FA * Pω * Y j')))
          + D.Nhat.τ (star Pω * (FA * Pω * FB)) := by
      simp only [D.Nhat.pairing_add_left, D.Nhat.pairing_add_right, D.Nhat.pairing_sum_left,
        D.Nhat.pairing_sum_right]
      ring
    -- the diagonal terms
    have hdiag : ∀ j : Fin R, (D.Nhat.τ (star Pω * (X j * Pω * Y j))).re
        = (1 - (bandMassA F B t s + bandMassB F B t t' - bandCross F B t s t') / bandZ t) ^ (j : ℕ)
          * (bandCross F B t s t' / bandZ t)
          * tracialPairLaw N (fun s t'' => selState (F.dataA s) (F.dataB t'') (F.joint s t'') B t)
              E G s t' a b := by
      intro j
      have h1 := trialUnitMat_trace_one N t hZ
      have hx := (StdTracialAlgebra.amplify N (m + 1)).fail_both_trace (trialUnitMat N m t)
        (trialPA N F B s) (trialQB N F B t') h1 (trialUnitMat_trace_PA N F B t hB s)
        (trialUnitMat_trace_QB N F B t hB t') (trialUnitMat_trace_joint N F B t hB s t')
      have hcyc := (StdTracialAlgebra.amplify N (m + 1)).pairing_cyc (trialUnitMat N m t)
        (trialVA N F B s) (trialWB N F B t' * trialVbar N F t') (tildeA E a₀ s a)
        (tildeB G b₀ t' b)
      have hT := hcyc.trans (corner_pairing F B t E G s t' a₀ a b₀ b)
      have hd := diag_term_trace D (trialUnitMat N m t) (trialPA N F B s) (trialQB N F B t')
        (trialVA N F B s) (trialWB N F B t' * trialVbar N F t') (tildeA E a₀ s a)
        (tildeB G b₀ t' b) (trialPA_sa F B s) (trialPA_idem F B t hB s) (trialQB_sa F B t')
        (trialQB_idem F B t hB t') h1 hx hT j
        (fun _ _ _ _ h => D.emb_commute h _ _) (fun _ _ _ _ h => D.emb_commute h _ _)
      have hd' : D.Nhat.τ (star Pω * (X j * Pω * Y j))
          = (1 - ((bandMassA F B t s / bandZ t : ℝ) : ℂ) - ((bandMassB F B t t' / bandZ t : ℝ) : ℂ)
                + ((bandCross F B t s t' / bandZ t : ℝ) : ℂ)) ^ (j : ℕ)
            * (((bandZ t : ℝ) : ℂ)⁻¹ *
                N.τ (star (selWord (F.dataA s) (F.dataB t') B t) *
                  (E s a * selWord (F.dataA s) (F.dataB t') B t * G t' b))) := hd
      have hsel : (N.τ (star (selWord (F.dataA s) (F.dataB t') B t) *
            (E s a * selWord (F.dataA s) (F.dataB t') B t * G t' b))).re
          = bandCross F B t s t' *
            tracialPairLaw N (fun s t'' => selState (F.dataA s) (F.dataB t'') (F.joint s t'') B t)
              E G s t' a b :=
        (selState_pairing (F.dataA s) (F.dataB t') (F.joint s t') B t hB (E s a) (G t' b)).symm
      rw [hd',
        show (1 - ((bandMassA F B t s / bandZ t : ℝ) : ℂ) - ((bandMassB F B t t' / bandZ t : ℝ) : ℂ)
              + ((bandCross F B t s t' / bandZ t : ℝ) : ℂ))
            = (((1 - (bandMassA F B t s + bandMassB F B t t' - bandCross F B t s t') / bandZ t : ℝ))
                : ℂ) by push_cast; ring,
        ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
        hsel]
      ring
    -- assemble
    rw [hcomp, hexp]
    simp only [Complex.add_re, Complex.re_sum]
    have hmain : commonMass (bandMassA F B t s) (bandMassB F B t t') (bandCross F B t s t')
          (bandZ t) R
        * tracialPairLaw N (fun s t'' => selState (F.dataA s) (F.dataB t'') (F.joint s t'') B t)
            E G s t' a b
        = ∑ j : Fin R, (D.Nhat.τ (star Pω * (X j * Pω * Y j))).re := by
      rw [commonMass, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun j _ => (hdiag j).symm
    have h2 : 0 ≤ ∑ j, (D.Nhat.τ (star Pω * (X j * Pω * FB))).re :=
      Finset.sum_nonneg fun j _ => hnn _ _ (hXpos j) hFBpos
    have h3 : 0 ≤ ∑ j', (D.Nhat.τ (star Pω * (FA * Pω * Y j'))).re :=
      Finset.sum_nonneg fun j' _ => hnn _ _ hFApos (hYpos j')
    have h4 : 0 ≤ (D.Nhat.τ (star Pω * (FA * Pω * FB))).re := hnn _ _ hFApos hFBpos
    have h5 : ∑ j : Fin R, (D.Nhat.τ (star Pω * (X j * Pω * Y j))).re
        ≤ ∑ j : Fin R, ∑ j', (D.Nhat.τ (star Pω * (X j * Pω * Y j'))).re :=
      Finset.sum_le_sum fun j _ =>
        Finset.single_le_sum (fun j' _ => hnn _ _ (hXpos j) (hYpos j')) (Finset.mem_univ j)
    rw [hmain]
    linarith
  · -- (2) `∑_{a,b} r = 1 − commonMass`: both `tracialPairLaw`s are probability laws summing
    -- to `1` (`tracialPairLaw_sum` with the full POVMs `hatA_sum`/`hatB_sum`, `hE_sum`/`hG_sum`
    -- and the unit vectors `tensorState_norm`/`selState_norm`); then `∑ r = 1 − commonMass · 1`.
    have hΩ : ∀ (_ : S) (_ : T), ‖tensorState D (trialUnitMat N m t)‖ = 1 :=
      fun _ _ => tensorState_norm D (trialUnitMat N m t) (trialState_norm N m t hZ)
    have hz : ∀ (s : S) (t'' : T),
        ‖selState (F.dataA s) (F.dataB t'') (F.joint s t'') B t‖ = 1 :=
      fun s t'' => selState_norm (F.dataA s) (F.dataB t'') (F.joint s t'') B t hB
    have h1 := tracialPairLaw_sum D.Nhat (fun _ _ => tensorState D (trialUnitMat N m t))
      (fun s a => hatA F B D E a₀ s a) (fun t' b => hatB F B D G b₀ t' b) hΩ
      (fun s => hatA_sum F B t D E a₀ s hB (hE_sum s))
      (fun t' => hatB_sum F B t D G b₀ t' hB (hG_sum t')) s t'
    have h2 := tracialPairLaw_sum N
      (fun s t'' => selState (F.dataA s) (F.dataB t'') (F.joint s t'') B t) E G hz hE_sum
      hG_sum s t'
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h1, h2, mul_one]
  · intro a b; ring

end CommutingRepetition
