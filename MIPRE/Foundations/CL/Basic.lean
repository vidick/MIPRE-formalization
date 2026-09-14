/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Register
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Conditionally linear functions

Blueprint `def:cl-function` (paper `linear.tex`, Definition `def:cl-func`; ledger node
`1.1.2`). The question distribution of every game in the pipeline is *conditionally linear*:
linear maps applied in stages to complementary register subspaces of `V = F^ι`, the register
subspace and the linear map of each stage being allowed to depend on the outputs of the
previous stages.

## Presentations and functions

The paper defines the *set* of `ℓ`-level CL functions on `V` inductively: the `0`-level one is
the zero function, and an `ℓ`-level one is any `L` of the form
`L(x) = L₁(x^{V₁}) + L_{>1, L₁(x^{V₁})}(x^{V_{>1}})` for complementary register subspaces
`V₁ ⊕ V_{>1} = V`, a linear map `L₁` on `V₁`, and `(ℓ-1)`-level CL functions `L_{>1,v}` on
`V_{>1}`, one for each value `v` of `L₁`. Everything downstream — the structure lemma
`lem:cl-kth`, the query interface of a sampler, the hiding tests of introspection — works with
the *decomposition data*, which the function does not determine. So the Lean object is the
data:

* `MIPRE.CL.CLFun F ι ℓ` is the type of `ℓ`-level **presentations** on the ambient space
  `ι → F`. A presentation of level `ℓ + 1` is `cons S L₁ next`: the coordinates `S : Finset ι`
  of the first register subspace `V₁ = V_S`, the first linear map `L₁ : RegLinear F S`, and the
  continuation `next : (ι → F) → CLFun F ι ℓ`, indexed by the value of `L₁`.
* `CLFun.eval` is the function presented:
  `eval (cons S L₁ next) x = L₁ x + eval (next (L₁ x)) (x^{V_{Sᶜ}})`.
* `CLFun.SupportedOn P T` says that `P` is a presentation *on `V_T`* in the paper's sense:
  `S ⊆ T`, and every continuation is on `V_{T \ S}`. The paper's `V_{>1}` is `V_{T \ S}`; it is
  not stored, because the level-`0` presentation `zero` is "the zero function on `V_{T'}`" for
  every `T'` (exactly as in the paper), and this keeps every construction free of
  dependent-type transport.
* `MIPRE.CL.IsCLFun ℓ T f` is the paper's notion itself: some `ℓ`-level presentation on `V_T`
  evaluates to `f`.

Two departures from the letter of the paper, both harmless: continuations are indexed by *all*
vectors rather than by the values of `L₁` (the others are never evaluated), and there is one
ambient space `F^ι` throughout, register subspaces of it playing the role of the paper's
`V_{>1}`, `U ⊕ V`, and so on.

## The structure lemma (`lem:cl-kth`)

`lem:cl-kth` attaches to an `ℓ`-level CL function its marginals `L_{≤k}`, factor spaces
`V_{k,u}` and stage maps `L_{k,u}`, `u` being the prefix `L_{<k}(x)`. Here:

* `CLFun.truncate k P` presents the `k`-th marginal (`P.truncate ℓ = P`, `truncate_self`),
  padded with trivial levels when `k` exceeds the level (`CLFun.lift`, the paper's
  `rk:higher-level`);
* `CLFun.factorAt P k x` and `CLFun.mapAt P k x` are the register subspace and the linear map
  applied at stage `k + 1` on the input `x`. They depend on `x` only through the prefix
  `L_{≤k}(x)`: `CLFun.factorOfPrefix` and `CLFun.mapOfPrefix` compute them from that prefix
  alone (`SupportedOn.factorOfPrefix_eval`, `SupportedOn.mapOfPrefix_eval`), which is what the
  `factor` and `linear` queries of a sampler answer;
* `SupportedOn.eval_truncate_eq_sum` is the decomposition `L_{≤k}(x) = ∑_{i ≤ k} x^{L_i}`, and
  `SupportedOn.disjoint_factorAt`, `SupportedOn.factorAt_subset` say that the factor spaces
  along a run are disjoint register subspaces of `V_T`. `CLFun.ExactlyOn P T` is the
  strengthening under which they partition `T` (`ExactlyOn.biUnion_factorAt`) — item (2) of
  `lem:cl-kth`, which samplers are required to satisfy.
-/

namespace MIPRE.CL

universe u v

/-- Presentations of `ℓ`-level conditionally linear functions on the ambient space `ι → F`
(blueprint `def:cl-function`). `cons S L₁ next` presents `x ↦ L₁ x + next (L₁ x) (x^{V_{Sᶜ}})`. -/
inductive CLFun (F : Type u) [Semiring F] (ι : Type v) [DecidableEq ι] : ℕ → Type (max u v)
  /-- The `0`-level presentation: the zero function. -/
  | zero : CLFun F ι 0
  /-- One more level in front: the register subspace `V_S`, a linear map `L₁` on it, and the
  continuation, chosen according to the value of `L₁`. -/
  | cons {ℓ : ℕ} (S : Finset ι) (L₁ : RegLinear F S) (next : (ι → F) → CLFun F ι ℓ) :
      CLFun F ι (ℓ + 1)

namespace CLFun

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}

theorem eq_zero (P : CLFun F ι 0) : P = zero := by cases P; rfl

/-! ## Support -/
/-- `P.SupportedOn T`: `P` is a presentation on `V_T` — its first register subspace lies inside
`T`, and every continuation is a presentation on the complementary `V_{T \ S}`. -/
def SupportedOn : {ℓ : ℕ} → CLFun F ι ℓ → Finset ι → Prop
  | _, zero, _ => True
  | _, cons S _ next, T => S ⊆ T ∧ ∀ v, (next v).SupportedOn (T \ S)

@[simp] theorem supportedOn_zero (T : Finset ι) : (zero : CLFun F ι 0).SupportedOn T := trivial

@[simp] theorem supportedOn_cons {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (T : Finset ι) :
    (cons S L₁ next).SupportedOn T ↔ S ⊆ T ∧ ∀ v, (next v).SupportedOn (T \ S) := Iff.rfl

theorem SupportedOn.mono {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ T') : P.SupportedOn T' := by
  induction P generalizing T T' with
  | zero => trivial
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    exact ⟨hS.trans h, fun v => ih v (hnext v) (Finset.sdiff_subset_sdiff h (Finset.Subset.refl S))⟩

/-! ## Levels: padding and marginals -/
/-- One more level at the bottom, acting on the register subspace `V_T` by the zero map: the
paper's `rk:higher-level`, every `ℓ`-level CL function being `(ℓ + 1)`-level. Padding with
`T = ∅` preserves every support; padding with the coordinates not yet used preserves exactness
(`ExactlyOn.lift`). -/
def lift (T : Finset ι) : {ℓ : ℕ} → CLFun F ι ℓ → CLFun F ι (ℓ + 1)
  | _, zero => cons T 0 fun _ => zero
  | _, cons S L₁ next => cons S L₁ fun v => (next v).lift (T \ S)

theorem SupportedOn.lift {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T' ⊆ T) : (P.lift T').SupportedOn T := by
  induction P generalizing T T' with
  | zero => exact ⟨h, fun _ => trivial⟩
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    exact ⟨hS, fun v => ih v (hnext v) (Finset.sdiff_subset_sdiff h (Finset.Subset.refl S))⟩

/-- `n` trivial levels at the bottom. -/
def liftN (T : Finset ι) : (n : ℕ) → CLFun F ι ℓ → CLFun F ι (ℓ + n)
  | 0, P => P
  | n + 1, P => (P.liftN T n).lift T

theorem SupportedOn.liftN {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T' ⊆ T) (n : ℕ) : (P.liftN T' n).SupportedOn T := by
  induction n with
  | zero => exact hP
  | succ n ih => exact ih.lift h

/-- The first `k` levels of `P`: the `k`-th marginal `L_{≤k}` of `lem:cl-kth`. When `k` exceeds
the level of `P`, the missing levels are trivial. -/
def truncate : (k : ℕ) → {ℓ : ℕ} → CLFun F ι ℓ → CLFun F ι k
  | 0, _, _ => zero
  | k + 1, _, zero => (truncate k zero).lift ∅
  | k + 1, _, cons S L₁ next => cons S L₁ fun v => truncate k (next v)

@[simp] theorem truncate_zero (P : CLFun F ι ℓ) : P.truncate 0 = zero := by
  cases P <;> rfl

@[simp] theorem truncate_succ_cons {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) :
    (cons S L₁ next).truncate (k + 1) = cons S L₁ fun v => (next v).truncate k := rfl

theorem truncate_succ_zero (k : ℕ) :
    (zero : CLFun F ι 0).truncate (k + 1) = ((zero : CLFun F ι 0).truncate k).lift ∅ := rfl

/-- Item (4) of `lem:cl-kth`: `L = L_{≤ℓ}`. -/
@[simp] theorem truncate_self (P : CLFun F ι ℓ) : P.truncate ℓ = P := by
  induction P with
  | zero => rfl
  | cons S L₁ next ih =>
    rw [truncate_succ_cons]
    exact congrArg _ (funext ih)

/-- Item (1) of `lem:cl-kth`: the `k`-th marginal is a `k`-level CL function on the same space. -/
theorem SupportedOn.truncate {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) (k : ℕ) :
    (P.truncate k).SupportedOn T := by
  induction k generalizing ℓ P T with
  | zero => trivial
  | succ k ih =>
    cases P with
    | zero => exact (ih (supportedOn_zero T)).lift (Finset.empty_subset T)
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      exact ⟨hS, fun v => ih (hnext v)⟩

/-! ## Exact support -/

/-- `P.ExactlyOn T`: `P` is a presentation on `V_T` whose last level leaves nothing over, so
that the factor spaces along every run partition `T` (`ExactlyOn.biUnion_factorAt`). This is
item (2) of `lem:cl-kth`, `V = ⊕ᵢ V_{i, L_{<i}(x)}`. -/
def ExactlyOn : {ℓ : ℕ} → CLFun F ι ℓ → Finset ι → Prop
  | _, zero, T => T = ∅
  | _, cons S _ next, T => S ⊆ T ∧ ∀ v, (next v).ExactlyOn (T \ S)

@[simp] theorem exactlyOn_zero (T : Finset ι) : (zero : CLFun F ι 0).ExactlyOn T ↔ T = ∅ :=
  Iff.rfl

@[simp] theorem exactlyOn_cons {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (T : Finset ι) :
    (cons S L₁ next).ExactlyOn T ↔ S ⊆ T ∧ ∀ v, (next v).ExactlyOn (T \ S) := Iff.rfl

theorem ExactlyOn.supportedOn {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    P.SupportedOn T := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩

theorem ExactlyOn.lift {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    (P.lift T).ExactlyOn T := by
  induction P generalizing T with
  | zero => exact ⟨Finset.Subset.refl T, fun _ => Finset.sdiff_self T⟩
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩

theorem ExactlyOn.liftN {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (n : ℕ) :
    (P.liftN T n).ExactlyOn T := by
  induction n with
  | zero => exact hP
  | succ n ih => exact ih.lift

/-! ## Evaluation -/

variable [Fintype ι]

/-- The function presented: `L(x) = x^{L₁} + L_{>1, x^{L₁}}(x^{V_{>1}})`. -/
def eval : {ℓ : ℕ} → CLFun F ι ℓ → (ι → F) → (ι → F)
  | _, zero, _ => 0
  | _, cons S L₁ next, x => L₁ x + (next (L₁ x)).eval (proj Sᶜ x)

@[simp] theorem eval_zero (x : ι → F) : (zero : CLFun F ι 0).eval x = 0 := rfl

@[simp] theorem eval_cons {S : Finset ι} (L₁ : RegLinear F S) (next : (ι → F) → CLFun F ι ℓ)
    (x : ι → F) : (cons S L₁ next).eval x = L₁ x + (next (L₁ x)).eval (proj Sᶜ x) := rfl

@[simp] theorem eval_zero_vec (P : CLFun F ι ℓ) : P.eval 0 = 0 := by
  induction P with
  | zero => rfl
  | cons S L₁ next ih => simp [ih]

/-- A presentation on `V_T` reads only the coordinates in `T`. -/
theorem SupportedOn.eval_proj_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (hTU : T ⊆ U) (x : ι → F) : P.eval (proj U x) = P.eval x := by
  induction P generalizing T U x with
  | zero => rfl
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    have hsub : T \ S ⊆ Sᶜ := fun i hi => by
      simp only [Finset.mem_sdiff] at hi
      simpa using hi.2
    simp only [eval_cons, L₁.apply_proj_of_subset (hS.trans hTU), proj_proj]
    rw [ih _ (hnext _) (Finset.subset_inter hsub (Finset.sdiff_subset.trans hTU)) x,
      ih _ (hnext _) hsub x]

theorem SupportedOn.eval_proj {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (x : ι → F) : P.eval (proj T x) = P.eval x :=
  hP.eval_proj_of_subset (Finset.Subset.refl T) x

theorem SupportedOn.eval_proj_of_disjoint {P : CLFun F ι ℓ} {T U : Finset ι}
    (hP : P.SupportedOn T) (h : Disjoint T U) (x : ι → F) : P.eval (proj U x) = 0 := by
  rw [← hP.eval_proj (proj U x), proj_proj_of_disjoint h, eval_zero_vec]

/-- A presentation on `V_T` takes its values in `V_T`. -/
theorem SupportedOn.proj_eval {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (x : ι → F) : proj T (P.eval x) = P.eval x := by
  induction P generalizing T x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    simp only [eval_cons, map_add, L₁.proj_apply_of_subset hS]
    rw [← ih _ (hnext _) (proj Sᶜ x), proj_proj_of_subset' Finset.sdiff_subset]

theorem SupportedOn.proj_eval_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (x : ι → F) : proj U (P.eval x) = P.eval x := by
  rw [← hP.proj_eval x, proj_proj_of_subset' h, hP.proj_eval]

theorem SupportedOn.proj_eval_of_disjoint {P : CLFun F ι ℓ} {T U : Finset ι}
    (hP : P.SupportedOn T) (h : Disjoint U T) (x : ι → F) : proj U (P.eval x) = 0 := by
  rw [← hP.proj_eval x, proj_proj_of_disjoint h]

/-! ## Evaluation of padded and truncated presentations -/

@[simp] theorem eval_lift (T : Finset ι) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.lift T).eval x = P.eval x := by
  induction P generalizing T x with
  | zero => simp [lift]
  | cons S L₁ next ih => simp [lift, ih]

@[simp] theorem eval_liftN (T : Finset ι) (n : ℕ) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.liftN T n).eval x = P.eval x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [liftN, ih]

@[simp] theorem eval_truncate_zero (P : CLFun F ι 0) (k : ℕ) (x : ι → F) :
    (P.truncate k).eval x = 0 := by
  rw [P.eq_zero]
  induction k with
  | zero => rfl
  | succ k ih => rw [truncate_succ_zero, eval_lift, ih]

/-! ## The data of a stage -/

/-- The register subspace acted on at stage `k + 1` on the input `x`: the factor space
`V_{k+1,u}` of `lem:cl-kth`, `u = L_{≤k}(x)` the prefix. Beyond the level of `P` it is empty. -/
def factorAt : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → Finset ι
  | _, zero, _, _ => ∅
  | _, cons S _ _, 0, _ => S
  | _, cons S L₁ next, k + 1, x => (next (L₁ x)).factorAt k (proj Sᶜ x)

/-- The linear map applied at stage `k + 1` on the input `x`: the map `L_{k+1,u}` of
`lem:cl-kth`, `u = L_{≤k}(x)` the prefix, as an endomorphism of the ambient space. Beyond the
level of `P` it is zero. -/
def mapAt : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → ((ι → F) →ₗ[F] (ι → F))
  | _, zero, _, _ => 0
  | _, cons _ L₁ _, 0, _ => L₁.toLinearMap
  | _, cons S L₁ next, k + 1, x => (next (L₁ x)).mapAt k (proj Sᶜ x)

@[simp] theorem factorAt_zero (k : ℕ) (x : ι → F) : (zero : CLFun F ι 0).factorAt k x = ∅ := rfl

@[simp] theorem factorAt_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (x : ι → F) : (cons S L₁ next).factorAt 0 x = S := rfl

@[simp] theorem factorAt_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (x : ι → F) :
    (cons S L₁ next).factorAt (k + 1) x = (next (L₁ x)).factorAt k (proj Sᶜ x) := rfl

@[simp] theorem mapAt_zero (k : ℕ) (x : ι → F) : (zero : CLFun F ι 0).mapAt k x = 0 := rfl

@[simp] theorem mapAt_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (x : ι → F) :
    (cons S L₁ next).mapAt 0 x = L₁.toLinearMap := rfl

@[simp] theorem mapAt_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (x : ι → F) :
    (cons S L₁ next).mapAt (k + 1) x = (next (L₁ x)).mapAt k (proj Sᶜ x) := rfl

/-- The factor spaces along a run lie in `T`. -/
theorem SupportedOn.factorAt_subset {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : P.factorAt k x ⊆ T := by
  induction P generalizing T k x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    cases k with
    | zero => exact hS
    | succ k => exact (ih _ (hnext _) k _).trans Finset.sdiff_subset

/-- The factor spaces along a run are pairwise disjoint. -/
theorem SupportedOn.disjoint_factorAt {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    {i j : ℕ} (hij : i < j) (x : ι → F) : Disjoint (P.factorAt i x) (P.factorAt j x) := by
  induction P generalizing T i j x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    cases i with
    | zero =>
      rw [factorAt_cons_zero, factorAt_cons_succ]
      exact Finset.disjoint_of_subset_right ((hnext _).factorAt_subset j _) Finset.disjoint_sdiff
    | succ i =>
      rw [factorAt_cons_succ, factorAt_cons_succ]
      exact ih _ (hnext _) (by omega) _

/-- The stage maps of a presentation on `V_T` read only the coordinates in `T`. -/
theorem SupportedOn.mapAt_apply_proj {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (hTU : T ⊆ U) (k : ℕ) (x y : ι → F) : P.mapAt k x (proj U y) = P.mapAt k x y := by
  induction P generalizing T U k x y with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    cases k with
    | zero =>
      rw [mapAt_cons_zero, RegLinear.toLinearMap_apply, RegLinear.toLinearMap_apply]
      exact L₁.apply_proj_of_subset (hS.trans hTU) y
    | succ k =>
      rw [mapAt_cons_succ]
      exact ih _ (hnext _) (Finset.sdiff_subset.trans hTU) k _ y

/-- Item (3) of `lem:cl-kth`: `L_{≤k}(x) = ∑_{i ≤ k} x^{L_i}`, the marginal is the sum of the
stage maps applied to the input. -/
theorem SupportedOn.eval_truncate_eq_sum {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : (P.truncate k).eval x = ∑ i ∈ Finset.range k, P.mapAt i x x := by
  induction k generalizing ℓ P T x with
  | zero => simp
  | succ k ih =>
    cases P with
    | zero => simp
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      have hsub : T \ S ⊆ Sᶜ := fun i hi => by
        simp only [Finset.mem_sdiff] at hi
        simpa using hi.2
      rw [truncate_succ_cons, eval_cons, ih (hnext (L₁ x)) (proj Sᶜ x), Finset.sum_range_succ',
        mapAt_cons_zero, RegLinear.toLinearMap_apply, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mapAt_cons_succ, (hnext (L₁ x)).mapAt_apply_proj hsub i (proj Sᶜ x) x]

/-- Item (3) of `lem:cl-kth` at the top level: `L(x) = ∑_{i ≤ ℓ} x^{L_i}`. -/
theorem SupportedOn.eval_eq_sum {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (x : ι → F) : P.eval x = ∑ i ∈ Finset.range ℓ, P.mapAt i x x := by
  rw [← hP.eval_truncate_eq_sum ℓ x, truncate_self]

/-! ## Stage data from the prefix -/

/-- The factor space at stage `k + 1`, read off the prefix `u = L_{≤k}(x)` rather than the
input `x`: the paper's `V_{k+1,u}`. The prefix determines the branch taken at each earlier
stage — its `V_S`-component is the value of that stage's map — and this is how a sampler's
`factor` query is answered. -/
def factorOfPrefix : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → Finset ι
  | _, zero, _, _ => ∅
  | _, cons S _ _, 0, _ => S
  | _, cons S _ next, k + 1, u => (next (proj S u)).factorOfPrefix k (proj Sᶜ u)

/-- The linear map at stage `k + 1`, read off the prefix `u = L_{≤k}(x)`: the paper's
`L_{k+1,u}`; how a sampler's `linear` query is answered. -/
def mapOfPrefix : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → ((ι → F) →ₗ[F] (ι → F))
  | _, zero, _, _ => 0
  | _, cons _ L₁ _, 0, _ => L₁.toLinearMap
  | _, cons S _ next, k + 1, u => (next (proj S u)).mapOfPrefix k (proj Sᶜ u)

@[simp] theorem factorOfPrefix_zero (k : ℕ) (u : ι → F) :
    (zero : CLFun F ι 0).factorOfPrefix k u = ∅ := rfl

@[simp] theorem factorOfPrefix_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (u : ι → F) : (cons S L₁ next).factorOfPrefix 0 u = S := rfl

@[simp] theorem factorOfPrefix_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (cons S L₁ next).factorOfPrefix (k + 1) u =
      (next (proj S u)).factorOfPrefix k (proj Sᶜ u) := rfl

@[simp] theorem mapOfPrefix_zero (k : ℕ) (u : ι → F) :
    (zero : CLFun F ι 0).mapOfPrefix k u = 0 := rfl

@[simp] theorem mapOfPrefix_cons_zero {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (u : ι → F) :
    (cons S L₁ next).mapOfPrefix 0 u = L₁.toLinearMap := rfl

@[simp] theorem mapOfPrefix_cons_succ {S : Finset ι} (L₁ : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (cons S L₁ next).mapOfPrefix (k + 1) u =
      (next (proj S u)).mapOfPrefix k (proj Sᶜ u) := rfl

/-- The two components of the prefix `L_{≤(k+1)}(x) = L₁ x + r` of a presentation
`cons S L₁ next` on `V_T`: `L₁ x` on `V_S`, and `r`, the prefix of the continuation, on
`V_{T \ S}`. -/
theorem SupportedOn.proj_eval_truncate_succ {S : Finset ι} {L₁ : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} {T : Finset ι} (hP : (cons S L₁ next).SupportedOn T)
    (k : ℕ) (x : ι → F) :
    proj S (((cons S L₁ next).truncate (k + 1)).eval x) = L₁ x ∧
      proj Sᶜ (((cons S L₁ next).truncate (k + 1)).eval x) =
        ((next (L₁ x)).truncate k).eval (proj Sᶜ x) := by
  obtain ⟨hS, hnext⟩ := hP
  have hr := (hnext (L₁ x)).truncate k
  have hsub : T \ S ⊆ Sᶜ := fun i hi => by
    simp only [Finset.mem_sdiff] at hi
    simpa using hi.2
  rw [truncate_succ_cons, eval_cons]
  constructor
  · rw [map_add, L₁.proj_apply, hr.proj_eval_of_disjoint Finset.disjoint_sdiff, add_zero]
  · rw [map_add, L₁.proj_compl_apply, zero_add, hr.proj_eval_of_subset hsub]

/-- The factor space at a stage is determined by the prefix: `factorOfPrefix` computes
`factorAt`. This is what makes the paper's indexing `V_{k,u}` by `u ∈ L_{<k}(V)` well defined. -/
theorem SupportedOn.factorOfPrefix_eval {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : P.factorOfPrefix k ((P.truncate k).eval x) = P.factorAt k x := by
  induction P generalizing T k x with
  | zero => rfl
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨h₁, h₂⟩ := hP.proj_eval_truncate_succ k x
      rw [factorOfPrefix_cons_succ, h₁, h₂, factorAt_cons_succ]
      exact ih _ (hP.2 _) k _

/-- The linear map at a stage is determined by the prefix: `mapOfPrefix` computes `mapAt`. -/
theorem SupportedOn.mapOfPrefix_eval {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : P.mapOfPrefix k ((P.truncate k).eval x) = P.mapAt k x := by
  induction P generalizing T k x with
  | zero => rfl
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨h₁, h₂⟩ := hP.proj_eval_truncate_succ k x
      rw [mapOfPrefix_cons_succ, h₁, h₂, mapAt_cons_succ]
      exact ih _ (hP.2 _) k _

/-- Item (2) of `lem:cl-kth`: along every run, the factor spaces partition the coordinates. -/
theorem ExactlyOn.biUnion_factorAt {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T)
    (x : ι → F) : (Finset.range ℓ).biUnion (fun i => P.factorAt i x) = T := by
  induction P generalizing T x with
  | zero => simpa using hP.symm
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    have h := ih (L₁ x) (hnext (L₁ x)) (proj Sᶜ x)
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, hi⟩
      cases k with
      | zero => exact hS hi
      | succ k =>
        have : i ∈ T \ S := h ▸ Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hi⟩
        exact (Finset.mem_sdiff.mp this).1
    · intro hi
      by_cases hiS : i ∈ S
      · exact ⟨0, by omega, hiS⟩
      · obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp (h ▸ Finset.mem_sdiff.mpr ⟨hi, hiS⟩)
        exact ⟨k + 1, by simpa using Finset.mem_range.mp hk, hik⟩

end CLFun

/-! ## The paper's notion -/

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {ℓ : ℕ}

/-- Blueprint `def:cl-function`: `f` is an `ℓ`-level conditionally linear function on `V_T` if
some `ℓ`-level presentation on `V_T` evaluates to it. -/
def IsCLFun (ℓ : ℕ) (T : Finset ι) (f : (ι → F) → (ι → F)) : Prop :=
  ∃ P : CLFun F ι ℓ, P.SupportedOn T ∧ P.eval = f

theorem CLFun.SupportedOn.isCLFun {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) :
    IsCLFun ℓ T P.eval :=
  ⟨P, hP, rfl⟩

theorem isCLFun_zero_iff {T : Finset ι} {f : (ι → F) → (ι → F)} : IsCLFun 0 T f ↔ f = 0 := by
  constructor
  · rintro ⟨P, -, rfl⟩
    rw [P.eq_zero]
    rfl
  · rintro rfl
    exact ⟨.zero, trivial, rfl⟩

theorem IsCLFun.mono {T T' : Finset ι} {f : (ι → F) → (ι → F)} (h : IsCLFun ℓ T f)
    (hT : T ⊆ T') : IsCLFun ℓ T' f := by
  obtain ⟨P, hP, rfl⟩ := h
  exact ⟨P, hP.mono hT, rfl⟩

/-- The paper's `rk:higher-level`: an `ℓ`-level CL function is `(ℓ + 1)`-level. -/
theorem IsCLFun.succ {T : Finset ι} {f : (ι → F) → (ι → F)} (h : IsCLFun ℓ T f) :
    IsCLFun (ℓ + 1) T f := by
  obtain ⟨P, hP, rfl⟩ := h
  exact ⟨P.lift ∅, hP.lift (Finset.empty_subset T), funext fun x => P.eval_lift ∅ x⟩

theorem IsCLFun.of_le {ℓ' : ℕ} {T : Finset ι} {f : (ι → F) → (ι → F)} (h : IsCLFun ℓ T f)
    (hℓ : ℓ ≤ ℓ') : IsCLFun ℓ' T f := by
  induction hℓ with
  | refl => exact h
  | step _ ih => exact ih.succ

theorem IsCLFun.apply_zero {T : Finset ι} {f : (ι → F) → (ι → F)} (h : IsCLFun ℓ T f) :
    f 0 = 0 := by
  obtain ⟨P, -, rfl⟩ := h
  exact P.eval_zero_vec

/-- The paper's `rk:level-1-is-linear`, as an equivalence: the `1`-level CL functions on `V_T`
are exactly the linear maps on `V_T`. -/
theorem isCLFun_one_iff {T : Finset ι} {f : (ι → F) → (ι → F)} :
    IsCLFun 1 T f ↔ ∃ L : RegLinear F T, ⇑L = f := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    cases P with
    | cons S L₁ next =>
      refine ⟨L₁.castLE hP.1, funext fun x => ?_⟩
      rw [CLFun.eval_cons, (next (L₁ x)).eq_zero, CLFun.eval_zero, add_zero,
        RegLinear.castLE_apply]
  · rintro ⟨L, rfl⟩
    exact ⟨.cons T L fun _ => .zero, ⟨Finset.Subset.refl T, fun _ => trivial⟩,
      funext fun x => by simp⟩

end MIPRE.CL
