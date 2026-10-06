/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Forms
public import MIPRE.Foundations.Introspection.AuxiliaryDualKernel

@[expose] public section

/-!
# Constraints on registers read off windows

The introspection verifier's hiding checks compare registers `x : Fin s → 𝔽₂` — the duals and
tails of Read and Hide answers — through projections onto coordinate sets and through the dual
maps `registerDual L`, with the sets and the maps computed from the readable register. In the
padded layout a register is a window of an answer (`toBits x` at a known offset). This file
writes such comparisons as linear constraints:

* `dotL_toBits`: the inner product of two windows is the `𝔽₂` sum `∑ wᵢ xᵢ`;
* `projEqCons`, `projEqCons_iff`: the constraints `xᵢ = yᵢ` for `i ∈ S`, holding exactly when
  `proj S x = proj S y`;
* `dualCons`, `dualCons_iff`: for a list of vectors spanning the kernel of `L`, the constraints
  `∑ᵢ zᵢ (proj S (x - y))ᵢ = 0`, holding exactly when `registerDual L x = registerDual L y`
  (`AuxiliaryDual.registerDual_eq_iff_dot`).
-/

namespace MIPRE.Tailored.Intro

open Cost CL Finset MIPRE.Introspection

/-! ## Inner products of registers -/

theorem decide_add_eq_one (u v : 𝔽₂) :
    decide (u + v = 1) = xor (decide (u = 1)) (decide (v = 1)) := by
  fin_cases u <;> fin_cases v <;> decide

theorem decide_mul_eq_one (u v : 𝔽₂) :
    decide (u * v = 1) = (decide (u = 1) && decide (v = 1)) := by
  fin_cases u <;> fin_cases v <;> decide

/-- **The inner product of two windows is the `𝔽₂` sum.** -/
theorem dotL_toBits : ∀ {s : ℕ} (w x : Fin s → 𝔽₂),
    dotL (toBits w) (toBits x) = decide (∑ i, w i * x i = 1)
  | 0, w, x => by simp [toBits]
  | s + 1, w, x => by
    have e : ∀ v : Fin (s + 1) → 𝔽₂, toBits v = decide (v 0 = 1) :: toBits (fun i => v i.succ) :=
      fun v => by simp [toBits, List.ofFn_succ]
    rw [e w, e x, dotL_cons_cons, dotL_toBits, Fin.sum_univ_succ, decide_add_eq_one,
      decide_mul_eq_one]

/-- A register-level linear form, placed at an offset. -/
def regForm {s : ℕ} (n o : ℕ) (w : Fin s → 𝔽₂) : BitStr := place n o (toBits w)

theorem length_regForm {s n o : ℕ} (w : Fin s → 𝔽₂) (h : o + s ≤ n) :
    (regForm n o w).length = n :=
  length_place (by simp; omega)

theorem dotL_regForm {s n o : ℕ} {w x : Fin s → 𝔽₂} {a : BitStr} (h : o + s ≤ n)
    (ha : a.length = n) (hx : (a.drop o).take s = toBits x) :
    dotL (regForm n o w) a = decide (∑ i, w i * x i = 1) := by
  rw [regForm, dotL_place (by simp; omega) ha, length_toBits, hx, dotL_toBits]

variable {s la lb oa ob : ℕ}

/-- **A constraint between two registers**, read: `∑ wa·x + ∑ wb·y = γ`. -/
theorem satisfies_regForms_iff {a b : BitStr} (ha : a.length = la) (hb : b.length = lb)
    (hoa : oa + s ≤ la) (hob : ob + s ≤ lb) {x y wa wb : Fin s → 𝔽₂}
    (hx : (a.drop oa).take s = toBits x) (hy : (b.drop ob).take s = toBits y) (γ : Bool) :
    Satisfies (regForm la oa wa ++ regForm lb ob wb ++ [γ]) (a ++ b ++ [true]) ↔
      decide (∑ i, wa i * x i + ∑ i, wb i * y i = 1) = γ := by
  rw [satisfies_append_iff γ (by rw [length_regForm _ hoa, ha])
    (by rw [length_regForm _ hob, hb]), dotL_regForm hoa ha hx, dotL_regForm hob hb hy,
    decide_add_eq_one]

/-! ## Equality on a coordinate set -/

/-- The constraints `xᵢ = yᵢ` for `i ∈ S`, the registers at offsets `oa` of `a`, `ob` of `b`,
in increasing order of `i`. -/
def projEqCons (la lb oa ob : ℕ) (S : Finset (Fin s)) : List BitStr :=
  ((List.finRange s).filter (· ∈ S)).map fun i => regForm la oa (Pi.single i 1) ++ regForm lb ob (Pi.single i 1) ++ [false]

theorem sum_single_mul (i : Fin s) (x : Fin s → 𝔽₂) :
    ∑ j, (Pi.single i (1 : 𝔽₂) : _ → _) j * x j = x i := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **The coordinate-set equality constraints hold exactly when the projections agree.** -/
theorem projEqCons_iff {a b : BitStr} (ha : a.length = la) (hb : b.length = lb)
    (hoa : oa + s ≤ la) (hob : ob + s ≤ lb) {x y : Fin s → 𝔽₂}
    (hx : (a.drop oa).take s = toBits x) (hy : (b.drop ob).take s = toBits y)
    (S : Finset (Fin s)) :
    (∀ c ∈ projEqCons la lb oa ob S, Satisfies c (a ++ b ++ [true])) ↔ proj S x = proj S y := by
  have key : ∀ i, Satisfies (regForm la oa (Pi.single i 1) ++ regForm lb ob (Pi.single i 1) ++
      [false]) (a ++ b ++ [true]) ↔ x i = y i := by
    intro i
    rw [satisfies_regForms_iff ha hb hoa hob hx hy, sum_single_mul, sum_single_mul]
    generalize x i = u; generalize y i = v
    revert u v; decide
  simp only [projEqCons, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, key]
  constructor
  · intro h
    funext i
    simp only [proj_apply]
    split_ifs with hi
    · exact h i hi
    · rfl
  · intro h i hi
    have := congrFun h i
    simpa [proj_apply, hi] using this

/-! ## Equality of duals -/

/-- The constraints `∑ᵢ zᵢ (proj S (x - y))ᵢ = 0` for `z` in a list. -/
def dualCons (la lb oa ob : ℕ) (S : Finset (Fin s)) (gens : List (Fin s → 𝔽₂)) : List BitStr :=
  gens.map fun z => regForm la oa (proj S z) ++ regForm lb ob (proj S z) ++ [false]

theorem sum_proj_mul (S : Finset (Fin s)) (z x : Fin s → 𝔽₂) :
    ∑ i, proj S z i * x i = ∑ i, z i * proj S x i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [proj_apply]; split_ifs <;> simp

/-- **The dual equality constraints**, for a list of vectors of the kernel of `L` spanning it,
hold exactly when the duals agree. -/
theorem dualCons_iff {a b : BitStr} (ha : a.length = la) (hb : b.length = lb)
    (hoa : oa + s ≤ la) (hob : ob + s ≤ lb) {x y : Fin s → 𝔽₂}
    (hx : (a.drop oa).take s = toBits x) (hy : (b.drop ob).take s = toBits y)
    {S : Finset (Fin s)} (L : RegLinear 𝔽₂ S) (gens : List (Fin s → 𝔽₂))
    (hgens : ∀ g ∈ gens, L g = 0)
    (hspan : ∀ z, L z = 0 → z ∈ Submodule.span 𝔽₂ {g | g ∈ gens}) :
    (∀ c ∈ dualCons la lb oa ob S gens, Satisfies c (a ++ b ++ [true])) ↔
      AuxiliaryDual.registerDual L x = AuxiliaryDual.registerDual L y := by
  rw [AuxiliaryDual.registerDual_eq_iff_dot]
  have key : ∀ z, Satisfies (regForm la oa (proj S z) ++ regForm lb ob (proj S z) ++ [false])
      (a ++ b ++ [true]) ↔ ∑ i, z i * proj S (x - y) i = 0 := by
    intro z
    rw [satisfies_regForms_iff ha hb hoa hob hx hy, sum_proj_mul, sum_proj_mul,
      ← Finset.sum_add_distrib]
    have e : ∑ i, (z i * proj S x i + z i * proj S y i) = ∑ i, z i * proj S (x - y) i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, Pi.sub_apply, mul_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    rw [e]
    generalize ∑ i, z i * proj S (x - y) i = u
    revert u; decide
  simp only [dualCons, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, key]
  constructor
  · intro h z hz
    -- the functional `z ↦ ∑ zᵢ dᵢ` vanishes on the span of the generators
    let φ : (Fin s → 𝔽₂) →ₗ[𝔽₂] 𝔽₂ :=
      { toFun := fun z => ∑ i, z i * proj S (x - y) i
        map_add' := fun u v => by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun r u => by simp [mul_assoc, Finset.mul_sum] }
    have hker : Submodule.span 𝔽₂ {g | g ∈ gens} ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      intro g hg
      exact h g hg
    exact hker (hspan z hz)
  · intro h z hz
    exact h z (hgens z hz)

end MIPRE.Tailored.Intro

end
