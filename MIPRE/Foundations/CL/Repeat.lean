/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.Closure

/-!
# Direct sums of families of CL functions: the repeated sampler's functions

The `k`-fold direct sum of a family of `ℓ`-level CL presentations on `F^ι`, as an `ℓ`-level
presentation on `F^κ` for any `κ` in bijection with `Fin k × ι` (`CLFun.famSum`): stage by
stage, the register subspaces are the unions of the blocks' and the maps act blockwise. This is
`lem:cl-closure` (direct sums) iterated over `k` summands, in the form the repeated sampler of
`thm:parallel-repetition` needs: its CL function at index `n` is the direct sum of `k` copies
of the input sampler's on `𝔽₂^{k s(n)}`, `κ = Fin (k · s(n))` and `e = finProdFinEquiv`.

Everything the sampler's query interface asks is blockwise (the four `runs_*` clauses of
`MIPRE.CL.Sampler`), and everything the game needs is blockwise too, so the lemmas are stated
at the level of evaluation rather than as equalities of presentations:

* `eval_famSum`: `(⊕ᵢ Pᵢ)(x) = join (fun i => Pᵢ (block i x))`;
* `eval_truncate_famSum`, `factorOfPrefix_famSum`, `mapOfPrefix_famSum`: the marginals, factor
  spaces and stage maps read off a prefix are blockwise;
* `exactlyOn_famSum`: exactness is inherited (`lem:cl-kth`, item (2));
* `clDist_famSum`: the conditionally linear distribution of a direct sum is the product of the
  blocks' — the repeated game is the direct repetition.

The vocabulary: `block e i x` is the `i`-th block of `x : κ → F`, `join e v` assembles blocks,
and `blockSet e T` is the register subspace assembled from one per block.
-/

namespace MIPRE.CL

-- The block vocabulary is stated once for all the instances the file uses; the linter would
-- otherwise ask for an `omit` on every other lemma.
set_option linter.unusedSectionVars false

universe u v w

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}

/-! ## Blocks -/

section Blocks

variable (e : Fin k × ι ≃ κ)

/-- The `i`-th block of a vector on `κ ≃ Fin k × ι`. -/
def block (i : Fin k) (x : κ → F) : ι → F := fun j => x (e (i, j))

/-- The vector assembled from `k` blocks. -/
def join (v : Fin k → ι → F) : κ → F := fun p => v (e.symm p).1 (e.symm p).2

@[simp] theorem block_join (v : Fin k → ι → F) (i : Fin k) : block e i (join e v) = v i := by
  funext j; simp [block, join]

@[simp] theorem join_block (x : κ → F) : (join e fun i => block e i x) = x := by
  funext p; simp [block, join]

@[simp] theorem block_add (i : Fin k) (x y : κ → F) :
    block e i (x + y) = block e i x + block e i y := rfl

@[simp] theorem block_zero (i : Fin k) : block e i (0 : κ → F) = 0 := rfl

@[simp] theorem join_apply (v : Fin k → ι → F) (p : κ) :
    join e v p = v (e.symm p).1 (e.symm p).2 := rfl

@[simp] theorem join_apply_e (v : Fin k → ι → F) (i : Fin k) (j : ι) :
    join e v (e (i, j)) = v i j := by simp [join]

theorem join_eq_iff (v : Fin k → ι → F) (x : κ → F) : join e v = x ↔ ∀ i, v i = block e i x := by
  constructor
  · rintro rfl i; simp
  · intro h; rw [← join_block e x]; congr 1; funext i; exact h i

/-- The blocks of a vector, as an equivalence. -/
def blockEquiv : (κ → F) ≃ (Fin k → ι → F) where
  toFun x i := block e i x
  invFun := join e
  left_inv x := join_block e x
  right_inv v := funext fun i => block_join e v i

/-- The register subspace assembled from one register subspace per block. -/
def blockSet (T : Fin k → Finset ι) : Finset κ :=
  Finset.univ.filter fun p => (e.symm p).2 ∈ T (e.symm p).1

@[simp] theorem mem_blockSet (T : Fin k → Finset ι) (p : κ) :
    p ∈ blockSet e T ↔ (e.symm p).2 ∈ T (e.symm p).1 := by simp [blockSet]

theorem e_mem_blockSet (T : Fin k → Finset ι) (i : Fin k) (j : ι) :
    e (i, j) ∈ blockSet e T ↔ j ∈ T i := by simp

theorem blockSet_compl (T : Fin k → Finset ι) : (blockSet e T)ᶜ = blockSet e fun i => (T i)ᶜ := by
  ext p; simp

theorem blockSet_sdiff (T T' : Fin k → Finset ι) :
    blockSet e T \ blockSet e T' = blockSet e fun i => T i \ T' i := by
  ext p; simp

theorem blockSet_subset {T T' : Fin k → Finset ι} (h : ∀ i, T i ⊆ T' i) :
    blockSet e T ⊆ blockSet e T' := fun p hp => by
  rw [mem_blockSet] at hp ⊢; exact h _ hp

theorem blockSet_eq_empty_iff (T : Fin k → Finset ι) : blockSet e T = ∅ ↔ ∀ i, T i = ∅ := by
  constructor
  · intro h i
    ext j
    simp only [Finset.notMem_empty, iff_false]
    intro hj
    have : e (i, j) ∈ blockSet e T := (e_mem_blockSet e T i j).2 hj
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro h
    ext p
    simp [h]

@[simp] theorem blockSet_univ : blockSet e (fun _ => (Finset.univ : Finset ι)) = Finset.univ := by
  ext p; simp

theorem block_proj (T : Fin k → Finset ι) (i : Fin k) (x : κ → F) :
    block e i (proj (blockSet e T) x) = proj (T i) (block e i x) := by
  funext j
  simp [block, proj_apply]

end Blocks

/-! ## Direct sums of register-linear maps -/

namespace RegLinear

variable (e : Fin k × ι ≃ κ)

/-- The direct sum of a family of maps, one per block. -/
def blockSum {T : Fin k → Finset ι} (L : (i : Fin k) → RegLinear F (T i)) :
    RegLinear F (blockSet e T) where
  toLinearMap :=
    { toFun := fun x => join e fun i => L i (block e i x)
      map_add' := fun x y => by
        funext p
        simp only [join_apply, block_add, map_add, Pi.add_apply]
      map_smul' := fun c x => by
        funext p
        have : ∀ i, block e i (c • x) = c • block e i x := fun i => rfl
        simp only [join_apply, this, map_smul, RingHom.id_apply, Pi.smul_apply] }
  proj_comp_proj' := fun x => by
    funext p
    simp only [LinearMap.coe_mk, AddHom.coe_mk, join_apply, block_proj, RegLinear.apply_proj]
    rw [MIPRE.CL.proj_apply]
    by_cases h : p ∈ blockSet e T
    · rw [if_pos h]; rfl
    · rw [if_neg h]
      rw [mem_blockSet] at h
      have := congrFun ((L (e.symm p).1).proj_apply (block e (e.symm p).1 x)) (e.symm p).2
      rw [MIPRE.CL.proj_apply, if_neg h] at this
      exact this

@[simp] theorem blockSum_apply {T : Fin k → Finset ι} (L : (i : Fin k) → RegLinear F (T i))
    (x : κ → F) : blockSum e L x = join e fun i => L i (block e i x) := rfl

end RegLinear

/-! ## Direct sums of families of presentations -/

namespace CLFun

variable {ℓ : ℕ}

/-- The register subspace at the head of a presentation of positive level. -/
def hdS : CLFun F ι (ℓ + 1) → Finset ι
  | cons S _ _ => S

/-- The map at the head of a presentation of positive level. -/
def hdL : (P : CLFun F ι (ℓ + 1)) → RegLinear F P.hdS
  | cons _ L₁ _ => L₁

/-- The continuation of a presentation of positive level. -/
def tl : CLFun F ι (ℓ + 1) → (ι → F) → CLFun F ι ℓ
  | cons _ _ next => next

theorem eta (P : CLFun F ι (ℓ + 1)) : P = cons P.hdS P.hdL P.tl := by
  cases P; rfl

variable (e : Fin k × ι ≃ κ)

/-- The direct sum of a family of presentations, one per block, on `F^κ`, `κ ≃ Fin k × ι`. -/
def famSum : (ℓ : ℕ) → (Fin k → CLFun F ι ℓ) → CLFun F κ ℓ
  | 0, _ => zero
  | ℓ + 1, P =>
    cons (blockSet e fun i => (P i).hdS) (RegLinear.blockSum e fun i => (P i).hdL)
      fun v => famSum ℓ fun i => (P i).tl (block e i v)

@[simp] theorem famSum_zero (P : Fin k → CLFun F ι 0) : famSum e 0 P = zero := rfl

theorem famSum_succ (S : Fin k → Finset ι) (L : (i : Fin k) → RegLinear F (S i))
    (next : Fin k → (ι → F) → CLFun F ι ℓ) :
    famSum e (ℓ + 1) (fun i => cons (S i) (L i) (next i)) =
      cons (blockSet e S) (RegLinear.blockSum e L) fun v =>
        famSum e ℓ fun i => next i (block e i v) := rfl

/-- **Evaluation is blockwise.** -/
theorem eval_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (x : κ → F),
    (famSum e ℓ P).eval x = join e fun i => (P i).eval (block e i x)
  | 0, P, x => by
    funext p
    simp [(P _).eq_zero]
  | ℓ + 1, P, x => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP, famSum_succ, eval_cons, eval_famSum ℓ]
    funext p
    simp only [Pi.add_apply, RegLinear.blockSum_apply, join_apply, block_join, blockSet_compl,
      block_proj, eval_cons]

/-- **Support is blockwise.** -/
theorem supportedOn_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (T : Fin k → Finset ι),
    (∀ i, (P i).SupportedOn (T i)) → (famSum e ℓ P).SupportedOn (blockSet e T)
  | 0, _, _, _ => trivial
  | ℓ + 1, P, T, h => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP] at h ⊢
    rw [famSum_succ]
    refine ⟨blockSet_subset e fun i => (h i).1, fun v => ?_⟩
    rw [blockSet_sdiff]
    exact supportedOn_famSum ℓ _ _ fun i => (h i).2 _

/-- **Exactness is blockwise** (`lem:cl-kth`, item (2), for the direct sum). -/
theorem exactlyOn_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (T : Fin k → Finset ι),
    (∀ i, (P i).ExactlyOn (T i)) → (famSum e ℓ P).ExactlyOn (blockSet e T)
  | 0, P, T, h => by
    show blockSet e T = ∅
    rw [blockSet_eq_empty_iff]
    intro i
    have := h i
    rw [(P i).eq_zero] at this
    exact this
  | ℓ + 1, P, T, h => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP] at h ⊢
    rw [famSum_succ]
    refine ⟨blockSet_subset e fun i => (h i).1, fun v => ?_⟩
    rw [blockSet_sdiff]
    exact exactlyOn_famSum ℓ _ _ fun i => (h i).2 _

/-- **The marginals are blockwise.** -/
theorem eval_truncate_famSum : ∀ (j ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (x : κ → F),
    ((famSum e ℓ P).truncate j).eval x = join e fun i => ((P i).truncate j).eval (block e i x)
  | 0, _, P, x => by
    funext p
    simp
  | j + 1, 0, P, x => by
    funext p
    simp [eval_truncate_zero]
  | j + 1, ℓ + 1, P, x => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP, famSum_succ, truncate_succ_cons, eval_cons, eval_truncate_famSum j ℓ]
    funext p
    simp only [Pi.add_apply, RegLinear.blockSum_apply, join_apply, block_join, blockSet_compl,
      block_proj, truncate_succ_cons, eval_cons]

/-- **The factor spaces read off a prefix are blockwise.** -/
theorem factorOfPrefix_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (j : ℕ) (u : κ → F),
    (famSum e ℓ P).factorOfPrefix j u = blockSet e fun i => (P i).factorOfPrefix j (block e i u)
  | 0, P, j, u => by
    show (∅ : Finset κ) = _
    ext p
    simp [(P _).eq_zero]
  | ℓ + 1, P, j, u => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP, famSum_succ]
    cases j with
    | zero => rfl
    | succ j =>
      rw [factorOfPrefix_cons_succ, factorOfPrefix_famSum ℓ]
      congr 1
      funext i
      rw [factorOfPrefix_cons_succ, block_proj, blockSet_compl, block_proj]

/-- **The stage maps read off a prefix are blockwise.** -/
theorem mapOfPrefix_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (j : ℕ) (u y : κ → F),
    (famSum e ℓ P).mapOfPrefix j u y = join e fun i => (P i).mapOfPrefix j (block e i u) (block e i y)
  | 0, P, j, u, y => by
    funext p
    simp [(P _).eq_zero]
  | ℓ + 1, P, j, u, y => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP, famSum_succ]
    cases j with
    | zero => rfl
    | succ j =>
      rw [mapOfPrefix_cons_succ, mapOfPrefix_famSum ℓ]
      congr 1
      funext i
      rw [mapOfPrefix_cons_succ, block_proj, blockSet_compl, block_proj]

end CLFun

/-! ## The paper's statement, and the distribution -/

/-- `lem:cl-closure` (direct sums), `k` summands: the blockwise assembly of `ℓ`-level CL functions
on `V_{T i}` is an `ℓ`-level CL function on the assembled register subspace. -/
theorem IsCLFun.famSum (e : Fin k × ι ≃ κ) {ℓ : ℕ} {T : Fin k → Finset ι}
    {f : Fin k → (ι → F) → (ι → F)} (hf : ∀ i, IsCLFun ℓ (T i) (f i)) :
    IsCLFun ℓ (blockSet e T) fun x => join e fun i => f i (block e i x) := by
  choose P hP hPf using hf
  refine ⟨CLFun.famSum e ℓ P, CLFun.supportedOn_famSum e ℓ P T hP, funext fun x => ?_⟩
  rw [CLFun.eval_famSum]
  congr 1
  funext i
  rw [hPf]

/-- **The CL distribution of a direct sum is the product of the blocks' distributions.** -/
theorem clDist_famSum [Fintype F] [DecidableEq F] (e : Fin k × ι ≃ κ) {ℓ : ℕ}
    (L R : Fin k → CLFun F ι ℓ) (a b : κ → F) :
    clDist (CLFun.famSum e ℓ L).eval (CLFun.famSum e ℓ R).eval a b =
      ∏ i, clDist (L i).eval (R i).eval (block e i a) (block e i b) := by
  simp only [clDist]
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [← Nat.cast_prod, ← Fintype.card_piFinset]
    congr 1
    refine Finset.card_equiv (blockEquiv e) fun x => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      CLFun.eval_famSum, join_eq_iff, blockEquiv, Equiv.coe_fn_mk]
    exact forall_and.symm
  · rw [← Nat.cast_prod]
    congr 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Fintype.card_fun,
      ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

end MIPRE.CL
