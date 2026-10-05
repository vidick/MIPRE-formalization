/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.ZPC
public import Mathlib.Algebra.BigOperators.Fin
public import MIPRE.Tactics

@[expose] public section

/-!
# The `k`-fold tailored product of a tailored game

Paper II, §6.3 (II:11377–11396), in its direct form: the `k`-fold product of a tailored game
`G` is the tailored game `G.repeat k` on `k`-tuples of questions, with

* the product distribution `∏ᵢ μ(xᵢ, yᵢ)`;
* the variables at `x⃗` the disjoint union of the variables at the coordinates, the readable
  ones first, as a tailored answer must have them: the readable variables of `x₁, …, x_k`, in
  this order, then their linear variables (`varEquiv`), so that
  `lenR x⃗ = ∑ᵢ lenR xᵢ` and `lenL x⃗ = ∑ᵢ lenL xᵢ`;
* the constraints at `(x⃗, y⃗)` those of every coordinate, each written over all the variables
  by padding it with zeros (`padCons`): the paper's "zero-padded to the global length and
  concatenated" (II:11380). A constraint of the wrong length becomes the rejecting constraint,
  as the canonical decider rejects it in the coordinate.

`repeat_accepts_iff` is the acceptance law: the canonical decider accepts a pair of answers
exactly when they have the right lengths and every coordinate, read off by `coord`, is
accepted. It rests on `satisfies_padCons_iff`, the padded constraint being satisfied by the
whole answers exactly when the constraint is satisfied by the coordinate's.
-/

namespace MIPRE.Tailored

open Finset

variable {X : Type*} [Fintype X]

namespace TailoredGame

variable (G : TailoredGame X) {k : ℕ}

/-! ## The variables of a tuple of questions -/

/-- The readable variables of the coordinates, in order. -/
abbrev lenRSum (x : Fin k → X) : ℕ := ∑ i, G.lenR (x i)

/-- The linear variables of the coordinates, in order. -/
abbrev lenLSum (x : Fin k → X) : ℕ := ∑ i, G.lenL (x i)

/-- **The variables at `x⃗`**: the readable variables of the coordinates, then their linear
variables, matched with the pairs `(i, v)` of a coordinate and a variable `v` of the question
`xᵢ` (readable `v < lenR xᵢ` first, as in `G`). -/
def varEquiv (x : Fin k → X) :
    Fin (G.lenRSum x + G.lenLSum x) ≃ (i : Fin k) × Fin (G.len (x i)) :=
  finSumFinEquiv.symm.trans <|
    (Equiv.sumCongr finSigmaFinEquiv.symm finSigmaFinEquiv.symm).trans <|
      (Equiv.sigmaSumDistrib (fun i => Fin (G.lenR (x i))) fun i => Fin (G.lenL (x i))).symm.trans <|
        Equiv.sigmaCongrRight fun _ => finSumFinEquiv

/-- The readable variable `v` of the coordinate `i` is the readable variable
`∑_{j < i} lenR xⱼ + v` of the tuple. -/
theorem varEquiv_symm_castAdd (x : Fin k → X) (i : Fin k) (v : Fin (G.lenR (x i))) :
    (G.varEquiv x).symm ⟨i, Fin.castAdd (G.lenL (x i)) v⟩ =
      Fin.castAdd (G.lenLSum x) (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, v⟩) := by
  rw [Equiv.symm_apply_eq]
  simp [varEquiv, Equiv.sigmaSumDistrib, Equiv.sigmaCongrRight]
  rfl

/-- The linear variable `w` of the coordinate `i` is the linear variable
`∑_{j < i} lenL xⱼ + w` of the tuple, after all the readable ones. -/
theorem varEquiv_symm_natAdd (x : Fin k → X) (i : Fin k) (w : Fin (G.lenL (x i))) :
    (G.varEquiv x).symm ⟨i, Fin.natAdd (G.lenR (x i)) w⟩ =
      Fin.natAdd (G.lenRSum x) (finSigmaFinEquiv (n := fun j => G.lenL (x j)) ⟨i, w⟩) := by
  rw [Equiv.symm_apply_eq]
  simp [varEquiv, Equiv.sigmaSumDistrib, Equiv.sigmaCongrRight]
  rfl

/-- **Readable variables correspond**: a variable of the tuple is readable exactly when it is a
readable variable of its coordinate. -/
theorem lt_lenRSum_iff (x : Fin k → X) (g : Fin (G.lenRSum x + G.lenLSum x)) :
    g.val < G.lenRSum x ↔ ((G.varEquiv x) g).2.val < G.lenR (x ((G.varEquiv x) g).1) := by
  obtain ⟨⟨i, v⟩, rfl⟩ := (G.varEquiv x).symm.surjective g
  rw [Equiv.apply_symm_apply]
  refine Fin.addCases (fun r => ?_) (fun w => ?_) v
  · rw [varEquiv_symm_castAdd, Fin.val_castAdd]
    exact iff_of_true (finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, r⟩).isLt (by simp)
  · rw [varEquiv_symm_natAdd, Fin.val_natAdd]
    exact iff_of_false (by omega) (by simp)

/-! ## Coordinates of answers -/

/-- The answer to the coordinate `i` read off an answer `a` to the tuple `x⃗`. -/
def coord (x : Fin k → X) (a : Cost.BitStr) (i : Fin k) : Cost.BitStr :=
  List.ofFn fun v : Fin (G.len (x i)) => a.getD ((G.varEquiv x).symm ⟨i, v⟩) false

@[simp] theorem length_coord (x : Fin k → X) (a : Cost.BitStr) (i : Fin k) :
    (G.coord x a i).length = G.len (x i) := by simp [coord]

/-- The readable variables of the coordinates before `i`. -/
def preR (x : Fin k → X) (i : Fin k) : ℕ := ∑ j ∈ univ.filter (· < i), G.lenR (x j)

/-- The linear variables of the coordinates before `i`. -/
def preL (x : Fin k → X) (i : Fin k) : ℕ := ∑ j ∈ univ.filter (· < i), G.lenL (x j)

/-- The readable variables of the coordinates after `i`. -/
def sufR (x : Fin k → X) (i : Fin k) : ℕ := G.lenRSum x - (G.preR x i + G.lenR (x i))

/-- The linear variables of the coordinates after `i`. -/
def sufL (x : Fin k → X) (i : Fin k) : ℕ := G.lenLSum x - (G.preL x i + G.lenL (x i))

/-- A sum over the coordinates before `i`, written over `Fin i`. -/
theorem sum_castLE_eq_sum_filter (f : Fin k → ℕ) (i : Fin k) :
    ∑ j : Fin i, f (Fin.castLE i.isLt.le j) = ∑ j ∈ univ.filter (· < i), f j := by
  refine Finset.sum_bij (fun j _ => Fin.castLE i.isLt.le j) (fun j _ => ?_) (fun j _ j' _ h => ?_)
    (fun g hg => ?_) (fun _ _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.lt_def.2 j.isLt
  · exact Fin.castLE_injective _ h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact ⟨⟨g.val, hg⟩, Finset.mem_univ _, rfl⟩

/-- The position of a readable variable of the coordinate `i` among the readable variables. -/
theorem val_finSigmaFinEquiv_R (x : Fin k → X) (i : Fin k) (v : Fin (G.lenR (x i))) :
    ((finSigmaFinEquiv (n := fun j => G.lenR (x j)) ⟨i, v⟩ : Fin (G.lenRSum x)) : ℕ) =
      G.preR x i + v := by
  rw [finSigmaFinEquiv_apply, preR, ← sum_castLE_eq_sum_filter]

/-- The position of a linear variable of the coordinate `i` among the linear variables. -/
theorem val_finSigmaFinEquiv_L (x : Fin k → X) (i : Fin k) (w : Fin (G.lenL (x i))) :
    ((finSigmaFinEquiv (n := fun j => G.lenL (x j)) ⟨i, w⟩ : Fin (G.lenLSum x)) : ℕ) =
      G.preL x i + w := by
  rw [finSigmaFinEquiv_apply, preL, ← sum_castLE_eq_sum_filter]

theorem preR_add_le (x : Fin k → X) (i : Fin k) : G.preR x i + G.lenR (x i) ≤ G.lenRSum x := by
  rw [lenRSum, ← Finset.sum_filter_add_sum_filter_not univ (· < i), preR]
  refine Nat.add_le_add_left (Finset.single_le_sum (f := fun j => G.lenR (x j))
    (fun _ _ => Nat.zero_le _) ?_) _
  simp

theorem preL_add_le (x : Fin k → X) (i : Fin k) : G.preL x i + G.lenL (x i) ≤ G.lenLSum x := by
  rw [lenLSum, ← Finset.sum_filter_add_sum_filter_not univ (· < i), preL]
  refine Nat.add_le_add_left (Finset.single_le_sum (f := fun j => G.lenL (x j))
    (fun _ _ => Nat.zero_le _) ?_) _
  simp

/-- **A coordinate of an answer is two blocks of it**: its readable answers, at the coordinate's
place among the readable variables, then its linear answers, at its place among the linear
ones. -/
theorem coord_eq (x : Fin k → X) {a : Cost.BitStr} (ha : a.length = G.lenRSum x + G.lenLSum x)
    (i : Fin k) :
    G.coord x a i = (a.drop (G.preR x i)).take (G.lenR (x i)) ++
      (a.drop (G.lenRSum x + G.preL x i)).take (G.lenL (x i)) := by
  have hR := G.preR_add_le x i
  have hL := G.preL_add_le x i
  apply List.ext_getElem
  · simp only [length_coord, len, List.length_append, List.length_take, List.length_drop]; omega
  intro v h1 h2
  simp only [coord, List.getElem_ofFn]
  have hlen1 : ((a.drop (G.preR x i)).take (G.lenR (x i))).length = G.lenR (x i) := by
    simp; omega
  rcases Nat.lt_or_ge v (G.lenR (x i)) with hv | hv
  · have key : (((G.varEquiv x).symm ⟨i, ⟨v, by simpa using h1⟩⟩ : Fin _) : ℕ) =
        G.preR x i + v := by
      have hfin : (⟨v, by simpa using h1⟩ : Fin (G.len (x i))) =
          Fin.castAdd (G.lenL (x i)) ⟨v, hv⟩ := rfl
      rw [hfin, varEquiv_symm_castAdd, Fin.val_castAdd, val_finSigmaFinEquiv_R]
    rw [key, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
      List.getElem_append_left (by omega), List.getElem_take, List.getElem_drop]
  · have hw : v - G.lenR (x i) < G.lenL (x i) := by simp [len] at h1; omega
    have key : (((G.varEquiv x).symm ⟨i, ⟨v, by simpa using h1⟩⟩ : Fin _) : ℕ) =
        G.lenRSum x + (G.preL x i + (v - G.lenR (x i))) := by
      have hfin : (⟨v, by simpa using h1⟩ : Fin (G.len (x i))) =
          Fin.natAdd (G.lenR (x i)) ⟨v - G.lenR (x i), hw⟩ := by ext; simp; omega
      rw [hfin, varEquiv_symm_natAdd, Fin.val_natAdd, val_finSigmaFinEquiv_L]
    rw [key, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
      List.getElem_append_right (by omega)]
    simp only [List.getElem_take, List.getElem_drop, hlen1]
    congr 1
    omega

/-- The readable answer to the coordinate `i` read off the readable part `a^R` of an answer:
its block of `lenR xᵢ` bits after the readable variables of the coordinates before it. -/
def coordR (x : Fin k → X) (aR : Cost.BitStr) (i : Fin k) : Cost.BitStr :=
  (aR.drop (G.preR x i)).take (G.lenR (x i))

/-- The readable part of a coordinate of an answer is the coordinate of its readable part. -/
theorem coordR_take (x : Fin k → X) {a : Cost.BitStr} (ha : a.length = G.lenRSum x + G.lenLSum x)
    (i : Fin k) :
    G.coordR x (a.take (G.lenRSum x)) i = (G.coord x a i).take (G.lenR (x i)) := by
  have hR := G.preR_add_le x i
  rw [coord_eq G x ha, List.take_append_of_le_length (by simp; omega), List.take_take, coordR,
    List.drop_take, List.take_take]
  congr 1
  omega

/-! ## Padding a constraint of a coordinate -/

/-- `n` zero bits. -/
abbrev zeros (n : ℕ) : Cost.BitStr := List.replicate n false

/-- **A constraint of the coordinate `i`, written over all the variables** (II:11380): its
blocks of coefficients — readable at `xᵢ`, linear at `xᵢ`, readable at `yᵢ`, linear at `yᵢ`,
affine — each put at its coordinate's place among the variables of its kind, and zeros
everywhere else. The blocks are cut with `take` and `drop`, so that they partition the
constraint whatever its length: a constraint of the wrong length gives a padded vector of the
wrong length, which the canonical decider rejects, as it rejects the constraint in its
coordinate. -/
def padCons (x y : Fin k → X) (i : Fin k) (c : Cost.BitStr) : Cost.BitStr :=
  zeros (G.preR x i) ++ c.take (G.lenR (x i)) ++ zeros (G.sufR x i) ++
    zeros (G.preL x i) ++ (c.drop (G.lenR (x i))).take (G.lenL (x i)) ++ zeros (G.sufL x i) ++
    zeros (G.preR y i) ++ (c.drop (G.len (x i))).take (G.lenR (y i)) ++ zeros (G.sufR y i) ++
    zeros (G.preL y i) ++ (c.drop (G.len (x i) + G.lenR (y i))).take (G.lenL (y i)) ++
    zeros (G.sufL y i) ++ c.drop (G.len (x i) + G.len (y i))

/-! ## The product game -/

end TailoredGame

/-- **The `k`-fold tailored product** (II:11377): product distribution, the variables of the
coordinates (readable first), and every coordinate's constraints padded to all the
variables. -/
def TailoredGame.repeat (G : TailoredGame X) (k : ℕ) : TailoredGame (Fin k → X) where
  μ x y := ∏ i, G.μ (x i) (y i)
  μ_nonneg x y := Finset.prod_nonneg fun i _ => G.μ_nonneg (x i) (y i)
  μ_sum_one := by
    classical
    calc (∑ x : Fin k → X, ∑ y : Fin k → X, ∏ i, G.μ (x i) (y i))
        = ∑ x : Fin k → X, ∏ i, ∑ y, G.μ (x i) y :=
          Finset.sum_congr rfl fun x _ => (Fintype.prod_sum fun i y => G.μ (x i) y).symm
      _ = ∏ _i : Fin k, ∑ x, ∑ y, G.μ x y :=
          (Fintype.prod_sum fun _ x => ∑ y, G.μ x y).symm
      _ = 1 := by simp [G.μ_sum_one]
  lenR x := G.lenRSum x
  lenL x := G.lenLSum x
  cons x y aR bR := (List.finRange k).flatMap fun i =>
    (G.cons (x i) (y i) (G.coordR x aR i) (G.coordR y bR i)).map (G.padCons x y i)

namespace TailoredGame

variable (G : TailoredGame X) {k : ℕ}

@[simp] theorem repeat_μ (x y : Fin k → X) :
    (G.repeat k).μ x y = ∏ i, G.μ (x i) (y i) := rfl

@[simp] theorem repeat_lenR (x : Fin k → X) : (G.repeat k).lenR x = G.lenRSum x := rfl

@[simp] theorem repeat_lenL (x : Fin k → X) : (G.repeat k).lenL x = G.lenLSum x := rfl

theorem repeat_len (x : Fin k → X) : (G.repeat k).len x = G.lenRSum x + G.lenLSum x := rfl

/-! ## Linear constraints after padding -/

/-- The number of coincident ones of two concatenations, the first blocks of equal lengths, is
the sum over the blocks. -/
theorem count_zipWith_append {p₁ p₂ v₁ v₂ : Cost.BitStr} (h : p₁.length = v₁.length) :
    (List.zipWith (· && ·) (p₁ ++ p₂) (v₁ ++ v₂)).count true =
      (List.zipWith (· && ·) p₁ v₁).count true + (List.zipWith (· && ·) p₂ v₂).count true := by
  rw [List.zipWith_append h, List.count_append]

@[simp] theorem count_zipWith_zeros (n : ℕ) (m : Cost.BitStr) :
    (List.zipWith (· && ·) (zeros n) m).count true = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.1 hmem
  simp [List.getElem_zipWith] at he

/-- A list is the concatenation of six consecutive blocks of it. -/
theorem eq_flatten_six (a : Cost.BitStr) (p₁ p₂ p₃ p₄ p₅ : ℕ) :
    a = [a.take p₁, (a.drop p₁).take p₂, (a.drop (p₁ + p₂)).take p₃,
      (a.drop (p₁ + p₂ + p₃)).take p₄, (a.drop (p₁ + p₂ + p₃ + p₄)).take p₅,
      a.drop (p₁ + p₂ + p₃ + p₄ + p₅)].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [← List.drop_drop (i := p₅) (j := p₁ + p₂ + p₃ + p₄), List.take_append_drop,
    ← List.drop_drop (i := p₄) (j := p₁ + p₂ + p₃), List.take_append_drop,
    ← List.drop_drop (i := p₃) (j := p₁ + p₂), List.take_append_drop,
    ← List.drop_drop (i := p₂) (j := p₁), List.take_append_drop, List.take_append_drop]

/-- A list is the concatenation of five consecutive blocks of it. -/
theorem eq_flatten_five (c : Cost.BitStr) (p₁ p₂ p₃ p₄ : ℕ) :
    c = [c.take p₁, (c.drop p₁).take p₂, (c.drop (p₁ + p₂)).take p₃,
      (c.drop (p₁ + p₂ + p₃)).take p₄, c.drop (p₁ + p₂ + p₃ + p₄)].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [← List.drop_drop (i := p₄) (j := p₁ + p₂ + p₃), List.take_append_drop,
    ← List.drop_drop (i := p₃) (j := p₁ + p₂), List.take_append_drop,
    ← List.drop_drop (i := p₂) (j := p₁), List.take_append_drop, List.take_append_drop]

/-- The padding lemma on blocks: a constraint cut into the blocks of two answers, with zeros
against every other block, is satisfied exactly when the constraint is satisfied by the blocks
it was cut against. -/
theorem satisfies_pad_blocks (c a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ : Cost.BitStr)
    {n₁ n₂ n₃ n₄ n₅ n₆ m₁ m₂ m₃ m₄ m₅ m₆ : ℕ}
    (h₁ : a₁.length = n₁) (h₂ : a₂.length = n₂) (h₃ : a₃.length = n₃) (h₄ : a₄.length = n₄)
    (h₅ : a₅.length = n₅) (h₆ : a₆.length = n₆) (g₁ : b₁.length = m₁) (g₂ : b₂.length = m₂)
    (g₃ : b₃.length = m₃) (g₄ : b₄.length = m₄) (g₅ : b₅.length = m₅) (g₆ : b₆.length = m₆) :
    Satisfies (zeros n₁ ++ c.take n₂ ++ zeros n₃ ++ zeros n₄ ++ (c.drop n₂).take n₅ ++
        zeros n₆ ++ zeros m₁ ++ (c.drop (n₂ + n₅)).take m₂ ++ zeros m₃ ++ zeros m₄ ++
        (c.drop (n₂ + n₅ + m₂)).take m₅ ++ zeros m₆ ++ c.drop (n₂ + n₅ + m₂ + m₅))
      (a₁ ++ a₂ ++ a₃ ++ a₄ ++ a₅ ++ a₆ ++ (b₁ ++ b₂ ++ b₃ ++ b₄ ++ b₅ ++ b₆) ++ [true]) ↔
      Satisfies c (a₂ ++ a₅ ++ (b₂ ++ b₅) ++ [true]) := by
  subst h₁ h₂ h₃ h₄ h₅ h₆ g₁ g₂ g₃ g₄ g₅ g₆
  by_cases hc : c.length = a₂.length + a₅.length + b₂.length + b₅.length + 1
  · have hc5 := eq_flatten_five c a₂.length a₅.length b₂.length b₅.length
    generalize hc₁ : c.take a₂.length = c₁ at hc5 ⊢
    generalize hc₂ : (c.drop a₂.length).take a₅.length = c₂ at hc5 ⊢
    generalize hc₃ : (c.drop (a₂.length + a₅.length)).take b₂.length = c₃ at hc5 ⊢
    generalize hc₄ : (c.drop (a₂.length + a₅.length + b₂.length)).take b₅.length = c₄
      at hc5 ⊢
    generalize hc₀ : c.drop (a₂.length + a₅.length + b₂.length + b₅.length) = c₅ at hc5 ⊢
    have l₁ : c₁.length = a₂.length := by rw [← hc₁]; simp; omega
    have l₂ : c₂.length = a₅.length := by rw [← hc₂]; simp; omega
    have l₃ : c₃.length = b₂.length := by rw [← hc₃]; simp; omega
    have l₄ : c₄.length = b₅.length := by rw [← hc₄]; simp; omega
    have l₅ : c₅.length = [true].length := by rw [← hc₀]; simp; omega
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hc5
    rw [hc5]
    unfold Satisfies
    simp only [List.append_assoc]
    rw [count_zipWith_append (by simp), count_zipWith_append l₁, count_zipWith_append (by simp),
      count_zipWith_append (by simp), count_zipWith_append l₂, count_zipWith_append (by simp),
      count_zipWith_append (by simp), count_zipWith_append l₃, count_zipWith_append (by simp),
      count_zipWith_append (by simp), count_zipWith_append l₄, count_zipWith_append (by simp),
      count_zipWith_append l₁, count_zipWith_append l₂, count_zipWith_append l₃,
      count_zipWith_append l₄]
    simp only [count_zipWith_zeros, zero_add, List.length_append, List.length_replicate, l₁, l₂,
      l₃, l₄, l₅]
  · refine iff_of_false (fun h => hc ?_) (fun h => hc ?_)
    · have hl := h.1
      simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate,
        List.length_cons, List.length_nil] at hl
      omega
    · have hl := h.1
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      omega

/-- **The padded constraint is satisfied by the whole answers exactly when the constraint is
satisfied by the coordinate's answers.** -/
theorem satisfies_padCons_iff (x y : Fin k → X) (i : Fin k) (c : Cost.BitStr) {a b : Cost.BitStr}
    (ha : a.length = G.lenRSum x + G.lenLSum x) (hb : b.length = G.lenRSum y + G.lenLSum y) :
    Satisfies (G.padCons x y i c) (a ++ b ++ [true]) ↔
      Satisfies c (G.coord x a i ++ G.coord y b i ++ [true]) := by
  have hRx := G.preR_add_le x i
  have hLx := G.preL_add_le x i
  have hRy := G.preR_add_le y i
  have hLy := G.preL_add_le y i
  have hsx : G.preR x i + G.lenR (x i) + G.sufR x i = G.lenRSum x := by unfold sufR; omega
  have hsy : G.preR y i + G.lenR (y i) + G.sufR y i = G.lenRSum y := by unfold sufR; omega
  have htx : G.preL x i + G.lenL (x i) + G.sufL x i = G.lenLSum x := by unfold sufL; omega
  have hty : G.preL y i + G.lenL (y i) + G.sufL y i = G.lenLSum y := by unfold sufL; omega
  have hcx := G.coord_eq x ha i
  have hcy := G.coord_eq y hb i
  rw [← hsx] at hcx
  rw [← hsy] at hcy
  have ha6 := eq_flatten_six a (G.preR x i) (G.lenR (x i)) (G.sufR x i) (G.preL x i)
    (G.lenL (x i))
  have hb6 := eq_flatten_six b (G.preR y i) (G.lenR (y i)) (G.sufR y i) (G.preL y i)
    (G.lenL (y i))
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at ha6 hb6
  have key := satisfies_pad_blocks c (a.take (G.preR x i))
    ((a.drop (G.preR x i)).take (G.lenR (x i)))
    ((a.drop (G.preR x i + G.lenR (x i))).take (G.sufR x i))
    ((a.drop (G.preR x i + G.lenR (x i) + G.sufR x i)).take (G.preL x i))
    ((a.drop (G.preR x i + G.lenR (x i) + G.sufR x i + G.preL x i)).take (G.lenL (x i)))
    (a.drop (G.preR x i + G.lenR (x i) + G.sufR x i + G.preL x i + G.lenL (x i)))
    (b.take (G.preR y i))
    ((b.drop (G.preR y i)).take (G.lenR (y i)))
    ((b.drop (G.preR y i + G.lenR (y i))).take (G.sufR y i))
    ((b.drop (G.preR y i + G.lenR (y i) + G.sufR y i)).take (G.preL y i))
    ((b.drop (G.preR y i + G.lenR (y i) + G.sufR y i + G.preL y i)).take (G.lenL (y i)))
    (b.drop (G.preR y i + G.lenR (y i) + G.sufR y i + G.preL y i + G.lenL (y i)))
    (n₁ := G.preR x i) (n₂ := G.lenR (x i)) (n₃ := G.sufR x i) (n₄ := G.preL x i)
    (n₅ := G.lenL (x i)) (n₆ := G.sufL x i)
    (m₁ := G.preR y i) (m₂ := G.lenR (y i)) (m₃ := G.sufR y i) (m₄ := G.preL y i)
    (m₅ := G.lenL (y i)) (m₆ := G.sufL y i)
    (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
    (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)
    (by simp; omega) (by simp; omega)
  rw [hcx, hcy]
  conv_lhs => arg 2; rw [ha6, hb6]
  simpa only [List.append_assoc, padCons, len, ← Nat.add_assoc] using key

/-- **The acceptance law of the product**: the canonical decider accepts a pair of answers to
`(x⃗, y⃗)` exactly when they have the right lengths and every coordinate is accepted. -/
theorem repeat_accepts_iff (x y : Fin k → X) (a b : Cost.BitStr) :
    (G.repeat k).Accepts x y a b ↔
      a.length = (G.repeat k).len x ∧ b.length = (G.repeat k).len y ∧
        ∀ i, G.Accepts (x i) (y i) (G.coord x a i) (G.coord y b i) := by
  unfold Accepts
  refine and_congr_right fun ha => and_congr_right fun hb => ?_
  simp only [TailoredGame.repeat, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and,
    forall_exists_index, and_imp]
  constructor
  · intro h i
    refine ⟨length_coord _ _ _ _, length_coord _ _ _ _, fun c hc => ?_⟩
    have h' := h _ i c (by rw [coordR_take G x ha, coordR_take G y hb]; exact hc) rfl
    exact (G.satisfies_padCons_iff x y i c ha hb).1 h'
  · intro h c' i c hc hc'
    subst hc'
    rw [coordR_take G x ha, coordR_take G y hb] at hc
    exact (G.satisfies_padCons_iff x y i c ha hb).2 ((h i).2.2 c hc)

end TailoredGame

end MIPRE.Tailored

end
