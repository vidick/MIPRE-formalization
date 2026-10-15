/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Closure.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic

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

/-! ## Evaluation -/

variable [Fintype ι]

end CLFun

/-! ## The paper's statements -/

section Statements

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {k ℓ : ℕ}

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
