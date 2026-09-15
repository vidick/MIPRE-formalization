/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# Closure properties of conditionally linear functions, and CL distributions

Paper `linear.tex`: concatenation (`lem:cl-concat`) and direct sums (`lem:cl-func-prod`) of
conditionally linear functions, and the conditionally linear distribution of a pair of CL
functions (`def:cl-dist`); blueprint `def:cl-function` and `lem:cl-closure`, ledger node
`1.1.2`.

Both constructions are on presentations (`MIPRE.CL.CLFun`) and are hypothesis-free; the
hypotheses of the paper's lemmas — the pieces live on disjoint register subspaces — enter only
in the evaluation lemmas (`SupportedOn.eval_concat`, `SupportedOn.eval_directSum`), which say
that the constructions present the functions the paper writes down, and in the support
lemmas. The paper's statements about *functions* follow as `IsCLFun.concat` and
`IsCLFun.directSum`.

* `CLFun.concat L R`: run `L` (level `k`), then the `R_u` (level `ℓ`) selected by its output;
  level `ℓ + k` — the paper's `T(x) = L(x^U) + R_{L(x^U)}(x^V)` on `U ⊕ V`, here for `L` on
  `V_U`, the `R_u` on `V_W`, `U` and `W` disjoint.
* `CLFun.directSum P Q`: stage by stage, the register subspaces are joined and the two
  continuations run side by side, each selected by its own component of the joint output;
  the paper's `⊕ⱼ L⁽ʲ⁾`, two summands at a time (`liftN` pads to a common level, the paper's
  `ℓ = maxⱼ ℓⱼ`).
* `MIPRE.CL.clDist L R`: the law of `(L x, R x)` for `x` uniform, as a real-valued probability
  mass function on pairs, the format of `MIPRE.Game`.

The paper's third closure property, downsizing to `𝔽₂` (`lem:cl-downsize`), needs the self-dual
bases of blueprint `lem:self-dual-basis` and is not here.
-/

namespace MIPRE.CL

universe u v

namespace CLFun

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}

/-! ## Concatenation (`lem:cl-concat`) -/

/-- The concatenation of `L` (level `k`) with the family `R` (level `ℓ`): run `L`, then the
`R_u` selected by its output `u`. The paper's `T(x) = L(x^U) + R_{L(x^U)}(x^V)`; here `U` and
`V` are the supports of the two sides (`SupportedOn.eval_concat`). -/
def concat : {k : ℕ} → CLFun F ι k → ((ι → F) → CLFun F ι ℓ) → CLFun F ι (ℓ + k)
  | _, zero, R => R 0
  | _, cons S L₁ next, R => cons S L₁ fun v => (next v).concat fun w => R (v + w)

@[simp] theorem concat_zero (R : (ι → F) → CLFun F ι ℓ) :
    (zero : CLFun F ι 0).concat R = R 0 := rfl

@[simp] theorem concat_cons {S : Finset ι} (L₁ : RegLinear F S) (next : (ι → F) → CLFun F ι k)
    (R : (ι → F) → CLFun F ι ℓ) :
    (cons S L₁ next).concat R = cons S L₁ fun v => (next v).concat fun w => R (v + w) := rfl

theorem SupportedOn.concat {L : CLFun F ι k} {R : (ι → F) → CLFun F ι ℓ} {U W : Finset ι}
    (hL : L.SupportedOn U) (hR : ∀ u, (R u).SupportedOn W) (hUW : Disjoint U W) :
    (L.concat R).SupportedOn (U ∪ W) := by
  induction L generalizing R U with
  | zero => exact (hR 0).mono Finset.subset_union_right
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hL
    refine ⟨hS.trans Finset.subset_union_left, fun v => ?_⟩
    rw [Finset.union_sdiff_distrib,
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_of_subset_left hS hUW).symm]
    exact ih v (hnext v) (fun w => hR _) (Finset.disjoint_of_subset_left Finset.sdiff_subset hUW)

theorem ExactlyOn.concat {L : CLFun F ι k} {R : (ι → F) → CLFun F ι ℓ} {U W : Finset ι}
    (hL : L.ExactlyOn U) (hR : ∀ u, (R u).ExactlyOn W) (hUW : Disjoint U W) :
    (L.concat R).ExactlyOn (U ∪ W) := by
  induction L generalizing R U with
  | zero =>
    have hU : U = ∅ := hL
    rw [concat_zero, hU, Finset.empty_union]
    exact hR 0
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hL
    refine ⟨hS.trans Finset.subset_union_left, fun v => ?_⟩
    rw [Finset.union_sdiff_distrib,
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_of_subset_left hS hUW).symm]
    exact ih v (hnext v) (fun w => hR _) (Finset.disjoint_of_subset_left Finset.sdiff_subset hUW)

/-! ## Direct sums (`lem:cl-func-prod`) -/

/-- The direct sum of two presentations of the same level (`lem:cl-func-prod`, two summands;
`liftN` pads to a common level): stage by stage, the register subspaces are joined and the
continuations run side by side, each selected by its own component of the joint output. -/
def directSum : {ℓ : ℕ} → CLFun F ι ℓ → CLFun F ι ℓ → CLFun F ι ℓ
  | _, zero, zero => zero
  | _, cons S L₁ next, cons S' L₁' next' =>
    cons (S ∪ S') (L₁.directSum L₁') fun v => (next (proj S v)).directSum (next' (proj S' v))

@[simp] theorem directSum_zero : (zero : CLFun F ι 0).directSum zero = zero := rfl

@[simp] theorem directSum_cons {S S' : Finset ι} (L₁ : RegLinear F S) (L₁' : RegLinear F S')
    (next next' : (ι → F) → CLFun F ι ℓ) :
    (cons S L₁ next).directSum (cons S' L₁' next') =
      cons (S ∪ S') (L₁.directSum L₁') fun v =>
        (next (proj S v)).directSum (next' (proj S' v)) := rfl

/-- The remainders of a direct sum of presentations on disjoint `V_T`, `V_{T'}`. -/
private theorem union_sdiff_union {S S' T T' : Finset ι} (hS : S ⊆ T) (hS' : S' ⊆ T')
    (hTT' : Disjoint T T') : (T ∪ T') \ (S ∪ S') = (T \ S) ∪ (T' \ S') := by
  ext i
  have hTS' : i ∈ T → i ∉ S' := fun hi hi' => Finset.disjoint_left.mp hTT' hi (hS' hi')
  have hT'S : i ∈ T' → i ∉ S := fun hi hi' => Finset.disjoint_left.mp hTT' (hS hi') hi
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
  tauto

theorem SupportedOn.directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') : (P.directSum Q).SupportedOn (T ∪ T') := by
  induction P generalizing T T' with
  | zero =>
    rw [Q.eq_zero]
    trivial
  | cons S L₁ next ih =>
    cases Q with
    | cons S' L₁' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      refine ⟨Finset.union_subset_union hS hS', fun v => ?_⟩
      show ((next (proj S v)).directSum (next' (proj S' v))).SupportedOn ((T ∪ T') \ (S ∪ S'))
      rw [union_sdiff_union hS hS' hTT']
      exact ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT'))

theorem ExactlyOn.directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.ExactlyOn T)
    (hQ : Q.ExactlyOn T') (hTT' : Disjoint T T') : (P.directSum Q).ExactlyOn (T ∪ T') := by
  induction P generalizing T T' with
  | zero =>
    rw [Q.eq_zero] at hQ ⊢
    have hT : T = ∅ := hP
    have hT' : T' = ∅ := hQ
    show T ∪ T' = ∅
    rw [hT, hT', Finset.empty_union]
  | cons S L₁ next ih =>
    cases Q with
    | cons S' L₁' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      refine ⟨Finset.union_subset_union hS hS', fun v => ?_⟩
      show ((next (proj S v)).directSum (next' (proj S' v))).ExactlyOn ((T ∪ T') \ (S ∪ S'))
      rw [union_sdiff_union hS hS' hTT']
      exact ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT'))

/-! ## Evaluation -/

variable [Fintype ι]

/-- The concatenation presents `x ↦ L(x) + R_{L(x)}(x)`, when `L` is on `V_U`, the `R_u` on
`V_W`, and `U`, `W` are disjoint. -/
theorem SupportedOn.eval_concat {L : CLFun F ι k} {R : (ι → F) → CLFun F ι ℓ} {U W : Finset ι}
    (hL : L.SupportedOn U) (hR : ∀ u, (R u).SupportedOn W) (hUW : Disjoint U W) (x : ι → F) :
    (L.concat R).eval x = L.eval x + (R (L.eval x)).eval x := by
  induction L generalizing R U x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hL
    have hWS : W ⊆ Sᶜ := fun i hi =>
      Finset.mem_compl.mpr fun hiS => Finset.disjoint_left.mp hUW (hS hiS) hi
    rw [concat_cons, eval_cons, eval_cons,
      ih _ (hnext _) (fun w => hR _) (Finset.disjoint_of_subset_left Finset.sdiff_subset hUW)
        (proj Sᶜ x),
      (hR _).eval_proj_of_subset hWS, add_assoc]

/-- The direct sum presents the sum of the two functions, when they are on disjoint register
subspaces. -/
theorem SupportedOn.eval_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (x : ι → F) :
    (P.directSum Q).eval x = P.eval x + Q.eval x := by
  induction P generalizing T T' x with
  | zero =>
    rw [Q.eq_zero]
    simp
  | cons S L₁ next ih =>
    cases Q with
    | cons S' L₁' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      have hSS' : Disjoint S S' :=
        Finset.disjoint_of_subset_left hS (Finset.disjoint_of_subset_right hS' hTT')
      have h₁ : proj S (L₁.directSum L₁' x) = L₁ x := by
        rw [RegLinear.directSum_apply, map_add, L₁.proj_apply, L₁'.proj_apply_of_disjoint hSS',
          add_zero]
      have h₂ : proj S' (L₁.directSum L₁' x) = L₁' x := by
        rw [RegLinear.directSum_apply, map_add, L₁.proj_apply_of_disjoint hSS'.symm,
          L₁'.proj_apply, zero_add]
      have hsub : T \ S ⊆ (S ∪ S')ᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        rw [Finset.mem_compl, Finset.mem_union]
        exact fun h => h.elim hi.2 fun h' => Finset.disjoint_left.mp hTT' hi.1 (hS' h')
      have hsub' : T' \ S' ⊆ (S ∪ S')ᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        rw [Finset.mem_compl, Finset.mem_union]
        exact fun h => h.elim (fun h' => Finset.disjoint_left.mp hTT' (hS h') hi.1) hi.2
      have hS₁ : T \ S ⊆ Sᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_compl.mpr hi.2
      have hS₂ : T' \ S' ⊆ S'ᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_compl.mpr hi.2
      rw [directSum_cons, eval_cons, h₁, h₂,
        ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')) (proj (S ∪ S')ᶜ x),
        eval_cons, eval_cons, RegLinear.directSum_apply,
        (hnext _).eval_proj_of_subset hsub, (hnext' _).eval_proj_of_subset hsub',
        (hnext _).eval_proj_of_subset hS₁, (hnext' _).eval_proj_of_subset hS₂,
        add_add_add_comm]

end CLFun

/-! ## The paper's statements -/

section Statements

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {k ℓ : ℕ}

/-- `lem:cl-concat`: if `f` is a `k`-level CL function on `V_U` and each `g u` an `ℓ`-level
one on `V_W`, `U` and `W` disjoint, then `x ↦ f x + g (f x) x` is a `(k + ℓ)`-level CL
function on `V_{U ∪ W}`. -/
theorem IsCLFun.concat {U W : Finset ι} {f : (ι → F) → (ι → F)} {g : (ι → F) → (ι → F) → (ι → F)}
    (hf : IsCLFun k U f) (hg : ∀ u, IsCLFun ℓ W (g u)) (hUW : Disjoint U W) :
    IsCLFun (ℓ + k) (U ∪ W) fun x => f x + g (f x) x := by
  obtain ⟨L, hL, rfl⟩ := hf
  choose R hR hRg using hg
  refine ⟨L.concat R, hL.concat hR hUW, funext fun x => ?_⟩
  rw [hL.eval_concat hR hUW, hRg]

/-- `lem:cl-func-prod`, two summands of the same level: the sum of an `ℓ`-level CL function on
`V_T` and one on `V_{T'}`, `T` and `T'` disjoint, is an `ℓ`-level CL function on `V_{T ∪ T'}`. -/
theorem IsCLFun.directSum {T T' : Finset ι} {f g : (ι → F) → (ι → F)} (hf : IsCLFun ℓ T f)
    (hg : IsCLFun ℓ T' g) (hTT' : Disjoint T T') : IsCLFun ℓ (T ∪ T') (f + g) := by
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨Q, hQ, rfl⟩ := hg
  exact ⟨P.directSum Q, hP.directSum hQ hTT', funext fun x => hP.eval_directSum hQ hTT' x⟩

/-- `lem:cl-func-prod` with summands of different levels: the sum is CL of level the maximum. -/
theorem IsCLFun.directSum' {T T' : Finset ι} {f g : (ι → F) → (ι → F)} (hf : IsCLFun k T f)
    (hg : IsCLFun ℓ T' g) (hTT' : Disjoint T T') : IsCLFun (max k ℓ) (T ∪ T') (f + g) :=
  (hf.of_le (le_max_left k ℓ)).directSum (hg.of_le (le_max_right k ℓ)) hTT'

end Statements

/-! ## Conditionally linear distributions (`def:cl-dist`) -/

section Distribution

variable {F : Type u} [Fintype F] [DecidableEq F] {ι : Type v} [DecidableEq ι] [Fintype ι]

/-- The conditionally linear distribution of a pair of functions (`def:cl-dist`): the law of
`(L x, R x)` for `x` uniform in `F^ι`, as a real-valued probability mass function on pairs, the
format of the question distribution of a `MIPRE.Game`. -/
noncomputable def clDist (L R : (ι → F) → (ι → F)) (a b : ι → F) : ℝ :=
  ((Finset.univ.filter fun x => L x = a ∧ R x = b).card : ℝ) / Fintype.card (ι → F)

theorem clDist_nonneg (L R : (ι → F) → (ι → F)) (a b : ι → F) : 0 ≤ clDist L R a b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sum_clDist [Nonempty F] (L R : (ι → F) → (ι → F)) :
    ∑ a, ∑ b, clDist L R a b = 1 := by
  have hcard : (0 : ℝ) < Fintype.card (ι → F) := by exact_mod_cast Fintype.card_pos
  have key : ∑ p : (ι → F) × (ι → F),
      ((Finset.univ.filter fun x => L x = p.1 ∧ R x = p.2).card : ℝ) =
        Fintype.card (ι → F) := by
    rw [← Nat.cast_sum, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := fun x => (L x, R x)) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    ext x
    simp [Prod.ext_iff]
  rw [← Fintype.sum_prod_type' fun a b => clDist L R a b]
  simp only [clDist, div_eq_mul_inv, ← Finset.sum_mul, key, mul_inv_cancel₀ hcard.ne']

end Distribution

end MIPRE.CL
