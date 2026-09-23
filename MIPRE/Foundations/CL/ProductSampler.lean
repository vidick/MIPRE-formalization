/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Product
import MIPRE.Foundations.CL.Downsize
import MIPRE.Foundations.CL.TypedSampler
import Mathlib.Algebra.Field.ZMod

/-!
# The product of a typed sampler and a directly answered one: the presentations

The answer-reduced sampler (`sec:ar-verifier`, `ld_compiler.tex`) is the direct sum of the
oracularized sampler, whose queries are answered by a program, and the downsized PCP sampler,
whose queries a polynomial-time function answers outright. This file is the CL half of that
construction, for any two families of presentations on `𝔽₂^a` and `𝔽₂^b`:

* `prodCL L P Q` pads both to `L` levels and puts them side by side on `𝔽₂^{a + b}`, the first
  `a` coordinates for `P`;
* its three queries, in bits, are the two halves' queries concatenated (`toBits_eval_truncate_prodCL`,
  `toBits_mapOfPrefix_prodCL`, `indicatorBits_factorOfPrefix_prodCL`);
* beyond a presentation's own level its marginal is its full evaluation, its stage map zero and its
  factor space empty (`eval_truncate_of_le`, `mapOfPrefix_of_le`, `factorOfPrefix_of_le`).
-/

noncomputable section

namespace MIPRE.CL

open Finset Cost

namespace CLFun

variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ## Beyond the level -/

theorem eval_truncate_of_le {ℓ : ℕ} (P : CLFun F ι ℓ) {j : ℕ} (h : ℓ ≤ j)
    (x : ι → F) : (P.truncate j).eval x = P.eval x := by
  induction P generalizing j x with
  | zero => simp [eval_truncate_zero]
  | cons S L next ih =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [truncate_succ_cons, eval_cons]
    rw [ih _ (Nat.le_of_succ_le_succ h)]

theorem mapOfPrefix_of_le {ℓ : ℕ} (P : CLFun F ι ℓ) {k : ℕ} (h : ℓ ≤ k) (u : ι → F) :
    P.mapOfPrefix k u = 0 := by
  induction P generalizing k u with
  | zero => rfl
  | cons S L next ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ih _ (Nat.le_of_succ_le_succ h) _

theorem factorOfPrefix_of_le {ℓ : ℕ} (P : CLFun F ι ℓ) {k : ℕ} (h : ℓ ≤ k) (u : ι → F) :
    P.factorOfPrefix k u = ∅ := by
  induction P generalizing k u with
  | zero => rfl
  | cons S L next ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ih _ (Nat.le_of_succ_le_succ h) _

end CLFun

/-! ## Splitting vectors of `𝔽₂^{a + b}` -/

variable {a b : ℕ}

/-- The first `a` coordinates. -/
def leftPart (x : Fin (a + b) → 𝔽₂) : Fin a → 𝔽₂ := fun i => x (Fin.castAdd b i)

/-- The last `b` coordinates. -/
def rightPart (x : Fin (a + b) → 𝔽₂) : Fin b → 𝔽₂ := fun i => x (Fin.natAdd a i)

@[simp] theorem leftPart_append (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    leftPart (Fin.append v w) = v := by
  funext i; simp [leftPart]

@[simp] theorem rightPart_append (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    rightPart (Fin.append v w) = w := by
  funext i; simp [rightPart]

theorem toBits_append (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    toBits (Fin.append v w) = toBits v ++ toBits w := by
  simp only [toBits, List.ofFn_add, Fin.append_right]
  congr 2
  funext i
  rw [show Fin.castLE (Nat.le_add_right a b) i = Fin.castAdd b i from rfl, Fin.append_left]

theorem toBits_eq_append (x : Fin (a + b) → 𝔽₂) :
    toBits x = toBits (leftPart x) ++ toBits (rightPart x) := by
  simp only [toBits, List.ofFn_add, leftPart, rightPart]
  rfl

theorem indicatorBits_eq_append (S : Finset (Fin (a + b))) :
    indicatorBits S = indicatorBits (S.preimage (Fin.castAdd b) (Fin.castAdd_injective _ _).injOn)
      ++ indicatorBits (S.preimage (Fin.natAdd a) (Fin.natAdd_injective _ _).injOn) := by
  simp only [indicatorBits, List.ofFn_add, Finset.mem_preimage]
  rfl

theorem leftPart_ofBits (l : BitStr) :
    leftPart (ofBits (a + b) l) = ofBits a (l.take a) := by
  funext i
  simp only [leftPart, ofBits, Fin.val_castAdd, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt i.isLt]

theorem rightPart_ofBits (l : BitStr) :
    rightPart (ofBits (a + b) l) = ofBits b (l.drop a) := by
  funext i
  simp only [rightPart, ofBits, Fin.val_natAdd, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem take_toBits (x : Fin (a + b) → 𝔽₂) : (toBits x).take a = toBits (leftPart x) := by
  rw [toBits_eq_append, List.take_left' (length_toBits _)]

theorem drop_toBits (x : Fin (a + b) → 𝔽₂) : (toBits x).drop a = toBits (rightPart x) := by
  rw [toBits_eq_append, List.drop_left' (length_toBits _)]

/-! ## The product presentation -/

namespace CLFun

variable {ℓa ℓb : ℕ}

/-- `P` and `Q` padded to `L` levels, side by side on `𝔽₂^{a + b}`: `P` on the first `a`
coordinates. -/
def prodCL (L : ℕ) (P : CLFun 𝔽₂ (Fin a) ℓa) (Q : CLFun 𝔽₂ (Fin b) ℓb) (ha : ℓa ≤ L)
    (hb : ℓb ≤ L) : CLFun 𝔽₂ (Fin (a + b)) L :=
  ((P.liftTo univ L ha).prod (Q.liftTo univ L hb)).reindex finSumFinEquiv

variable (L : ℕ) {P : CLFun 𝔽₂ (Fin a) ℓa} {Q : CLFun 𝔽₂ (Fin b) ℓb} (hP : P.ExactlyOn univ)
  (hQ : Q.ExactlyOn univ) (ha : ℓa ≤ L) (hb : ℓb ≤ L)

include hP hQ in
theorem ExactlyOn.prodCL : (prodCL L P Q ha hb).ExactlyOn univ := by
  have h := (ExactlyOn.prod (hP.liftTo L ha) (hQ.liftTo L hb)).reindex finSumFinEquiv
  rwa [Finset.map_univ_equiv] at h

private theorem sumElim_reindex (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    reindexEquiv finSumFinEquiv (Sum.elim v w) = Fin.append v w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

private theorem split_symm (x : Fin (a + b) → 𝔽₂) :
    (reindexEquiv finSumFinEquiv).symm x = Sum.elim (leftPart x) (rightPart x) := by
  funext p
  rcases p with i | i <;> rfl

include hP hQ in
theorem eval_truncate_prodCL (j : ℕ) (x : Fin (a + b) → 𝔽₂) :
    ((prodCL L P Q ha hb).truncate j).eval x
      = Fin.append ((P.truncate j).eval (leftPart x)) ((Q.truncate j).eval (rightPart x)) := by
  rw [prodCL, truncate_reindex, eval_reindex', eval_truncate_prod _ _ (hP.liftTo L ha)
    (hQ.liftTo L hb), ← sumElim_reindex, split_symm]
  simp only [Sum.elim_inl, Sum.elim_inr, eval_truncate_liftTo]

include hP hQ in
theorem toBits_eval_truncate_prodCL (j : ℕ) (x : Fin (a + b) → 𝔽₂) :
    toBits (((prodCL L P Q ha hb).truncate j).eval x)
      = toBits ((P.truncate j).eval (leftPart x)) ++ toBits ((Q.truncate j).eval (rightPart x)) := by
  rw [eval_truncate_prodCL L hP hQ, toBits_append]

include hP hQ in
theorem mapOfPrefix_prodCL (k : ℕ) (u y : Fin (a + b) → 𝔽₂) :
    (prodCL L P Q ha hb).mapOfPrefix k u y
      = Fin.append (P.mapOfPrefix k (leftPart u) (leftPart y))
          (Q.mapOfPrefix k (rightPart u) (rightPart y)) := by
  have hu : u = reindexEquiv finSumFinEquiv (Sum.elim (leftPart u) (rightPart u)) := by
    rw [← split_symm, LinearEquiv.apply_symm_apply]
  rw [prodCL]
  conv_lhs => rw [hu, mapOfPrefix_reindex]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [mapOfPrefix_prod _ _ (hP.liftTo L ha) (hQ.liftTo L hb), split_symm, ← sumElim_reindex]
  simp only [Sum.elim_inl, Sum.elim_inr, mapOfPrefix_liftTo]

include hP hQ in
theorem toBits_mapOfPrefix_prodCL (k : ℕ) (u y : Fin (a + b) → 𝔽₂) :
    toBits ((prodCL L P Q ha hb).mapOfPrefix k u y)
      = toBits (P.mapOfPrefix k (leftPart u) (leftPart y))
          ++ toBits (Q.mapOfPrefix k (rightPart u) (rightPart y)) := by
  rw [mapOfPrefix_prodCL L hP hQ, toBits_append]

include hP hQ in
theorem factorOfPrefix_prodCL (k : ℕ) (u : Fin (a + b) → 𝔽₂) :
    (prodCL L P Q ha hb).factorOfPrefix k u
      = ((P.factorOfPrefix k (leftPart u)).map Function.Embedding.inl ∪
          (Q.factorOfPrefix k (rightPart u)).map Function.Embedding.inr).map
            finSumFinEquiv.toEmbedding := by
  have hu : u = reindexEquiv finSumFinEquiv (Sum.elim (leftPart u) (rightPart u)) := by
    rw [← split_symm, LinearEquiv.apply_symm_apply]
  rw [prodCL]
  conv_lhs => rw [hu, factorOfPrefix_reindex, factorOfPrefix_prod _ _ (hP.liftTo L ha)
    (hQ.liftTo L hb), factorOfPrefix_liftTo hP, factorOfPrefix_liftTo hQ]
  rfl

include hP hQ in
theorem indicatorBits_factorOfPrefix_prodCL (k : ℕ) (u : Fin (a + b) → 𝔽₂) :
    indicatorBits ((prodCL L P Q ha hb).factorOfPrefix k u)
      = indicatorBits (P.factorOfPrefix k (leftPart u))
          ++ indicatorBits (Q.factorOfPrefix k (rightPart u)) := by
  rw [factorOfPrefix_prodCL L hP hQ, indicatorBits_eq_append]
  congr 2
  · ext i
    simp only [Finset.mem_preimage, Finset.mem_map, Finset.mem_union, Equiv.toEmbedding_apply,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply]
    constructor
    · rintro ⟨p, hp, he⟩
      rcases hp with ⟨i', hi', rfl⟩ | ⟨i', hi', rfl⟩
      · rw [finSumFinEquiv_apply_left] at he
        rwa [← Fin.castAdd_injective _ _ he]
      · rw [finSumFinEquiv_apply_right] at he
        exact absurd he (Fin.ne_of_val_ne (by simp; omega))
    · intro hi
      exact ⟨.inl i, Or.inl ⟨i, hi, rfl⟩, finSumFinEquiv_apply_left i⟩
  · ext i
    simp only [Finset.mem_preimage, Finset.mem_map, Finset.mem_union, Equiv.toEmbedding_apply,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply]
    constructor
    · rintro ⟨p, hp, he⟩
      rcases hp with ⟨i', hi', rfl⟩ | ⟨i', hi', rfl⟩
      · rw [finSumFinEquiv_apply_left] at he
        exact absurd he (Fin.ne_of_val_ne (by simp; omega))
      · rw [finSumFinEquiv_apply_right] at he
        rwa [← Fin.natAdd_injective _ _ he]
    · intro hi
      exact ⟨.inr i, Or.inr ⟨i, hi, rfl⟩, finSumFinEquiv_apply_right i⟩

end CLFun

end MIPRE.CL

end
