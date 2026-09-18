/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.CLGame

/-!
# The seeded-CL adapter, part 1: the two games describe the same lines

The seeded CL test `MIPRE.LIDT.CL.clGame` and the canonical-line test
`MIPRE.LIDT.lidtGame` present a line differently, and the adapter of
`planning/lidt-cl-adapter.md` has to know that the two presentations agree where they should.
This file settles the axis-parallel case, which is the one that needs the canonical
representative of `def:cl-canonical` to be *computed* rather than used abstractly.

The seeded test's base point for direction `w` is `rep w u = canonLin (span {w}) u`, the
canonical linear map with kernel `span {w}` applied to `u`. The canonical-line test's is the
first component of `Line.through u w`, which for a normalized direction moves `u` so that the
coordinate of the direction's first nonzero entry vanishes. For `w = eᵢ` both are
`u - uᵢ • eᵢ` (`rep_single`, `through_single`, and `rep_single_eq_through` for the conjunction),
so on axis-parallel lines the two games agree on the base point exactly, with no choice
involved. The seed is the only thing the seeded question carries beyond the line.

Getting `rep` to compute means computing the pivot set: `pivots (span {eᵢ}) = {i}`
(`pivots_line`), from the dimension sequence `dim (span {eᵢ} ⊓ tail n k)`, which is `1` for
`k ≤ i` (`inf_tail_of_le`) and `0` above (`inf_tail_of_gt`), so the sequence drops exactly at
`i`. `card_pivots` then pins the set, since a line has rank one.

`projection_eq_of` is the uniqueness of a complementary decomposition, stated as a rewriting
rule because that is how `canonLin` is pinned down: `canonLin S u` is *the* element of the
canonical complement congruent to `u` modulo `S`.
-/

namespace MIPRE.LIDT.Adapter

open Finset Submodule Module MIPRE.CL

variable {F : Type*} [Field F] {n : ℕ}

/-! ## The pivot set of a coordinate line -/

/-- The coordinate line `span {eᵢ}` meets `tail n k` in itself when `k ≤ i`: a multiple of
`eᵢ` has all its other coordinates zero already. -/
theorem inf_tail_of_le (i : Fin n) (k : ℕ) (hk : k ≤ (i : ℕ)) :
    (span F {(Pi.single i 1 : Fin n → F)} ⊓ tail n k : Submodule F (Fin n → F))
      = span F {(Pi.single i 1 : Fin n → F)} := by
  refine inf_eq_left.mpr ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_tail]
  intro j hj
  rw [Pi.single_apply, if_neg (fun h : j = i => by subst h; omega)]

/-- And meets it in `⊥` when `k > i`: the `i`-th coordinate is then forced to vanish. -/
theorem inf_tail_of_gt (i : Fin n) (k : ℕ) (hk : (i : ℕ) < k) :
    (span F {(Pi.single i 1 : Fin n → F)} ⊓ tail n k : Submodule F (Fin n → F)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxs, hxt⟩ := hx
  simp only [SetLike.mem_coe] at hxs hxt
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxs
  rw [mem_tail] at hxt
  have hi := hxt i hk
  rw [← hc] at hi ⊢
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hi
  simp [hi]

theorem single_ne_zero (i : Fin n) : (Pi.single i 1 : Fin n → F) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

theorem finrank_line (i : Fin n) :
    finrank F (span F {(Pi.single i 1 : Fin n → F)}) = 1 :=
  finrank_span_singleton (single_ne_zero i)

/-- **The pivot set of a coordinate line is the coordinate.** The dimension sequence of
`span {eᵢ}` is `1` up to `i` and `0` after it, so it drops exactly once, at `i`; and a line
has one pivot in all, by `card_pivots`. -/
theorem pivots_line (i : Fin n) :
    pivots (span F {(Pi.single i 1 : Fin n → F)}) = {i} := by
  classical
  set S := span F {(Pi.single i 1 : Fin n → F)} with hS
  have hmem : i ∈ pivots S := by
    rw [mem_pivots, dimTail, dimTail, hS, inf_tail_of_le i (i : ℕ) le_rfl,
      inf_tail_of_gt i ((i : ℕ) + 1) (Nat.lt_succ_self _)]
    rw [finrank_bot, ← hS, finrank_line]
    exact Nat.zero_lt_one
  have hcard : (pivots S).card = 1 := by rw [card_pivots, hS, finrank_line]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  rw [hj] at hmem ⊢
  rw [Finset.mem_singleton] at hmem
  rw [hmem]

/-! ## The two base points -/

/-- Uniqueness of the decomposition along complementary submodules, as a rewriting rule:
an element of `p` congruent to `x` modulo `q` *is* the projection of `x`. This is how
`canonLin` is computed, since `canonLin S` is the projection onto the canonical complement
along `S`. -/
theorem projection_eq_of {E : Type*} [AddCommGroup E] [Module F E] {p q : Submodule F E}
    (hpq : IsCompl p q) {x y : E} (hy : y ∈ p) (hxy : x - y ∈ q) :
    p.projection q hpq x = y := by
  have h1 : (p.projection q hpq x : E) - y ∈ p :=
    Submodule.sub_mem _ (Submodule.projection_apply_mem hpq x) hy
  have h2 : (p.projection q hpq x : E) - y ∈ q := by
    have e : (p.projection q hpq x : E) - y = -(x - (p.projection q hpq x : E)) + (x - y) := by
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.sub_projection_mem hpq x)) hxy
  have hbot := hpq.inf_eq_bot
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨h1, h2⟩)

/-- The seeded test's canonical base point for an axis-parallel direction: `rep eᵢ u`
zeroes the `i`-th coordinate of `u`. -/
theorem rep_single (i : Fin n) (u : Fin n → F) :
    canonLin (span F {(Pi.single i 1 : Fin n → F)}) u
      = u - u i • (Pi.single i 1 : Fin n → F) := by
  classical
  refine projection_eq_of
    (isCompl_canonCompl (span F {(Pi.single i 1 : Fin n → F)})).symm ?_ ?_
  · rw [canonCompl, mem_coordSub]
    intro j hj
    rw [pivots_line, Finset.mem_singleton] at hj
    subst hj
    simp
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨u i, rfl⟩

/-- The canonical-line test's presentation of an axis-parallel line: the direction is already
normalized, so it is unchanged, and the base point zeroes the `i`-th coordinate. -/
theorem through_single [DecidableEq F] (i : Fin n) (u : Fin n → F) :
    Line.through u (Pi.single i 1)
      = (u - u i • (Pi.single i 1 : Fin n → F), (Pi.single i 1 : Fin n → F)) := by
  classical
  have hex : ∃ j, (Pi.single i 1 : Fin n → F) j ≠ 0 := ⟨i, by simp⟩
  have hfind : Fin.find (fun j => (Pi.single i 1 : Fin n → F) j ≠ 0) hex = i := by
    rw [Fin.find_eq_iff]
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [Pi.single_apply, ne_eq, ite_eq_right_iff, not_forall]
    intro hcon
    exact absurd hcon.1 (fun h : j = i => by subst h; exact absurd hj (lt_irrefl _))
  rw [Line.through, dif_pos hex]
  simp only [hfind, Pi.single_eq_same, inv_one, one_smul]

/-- **On axis-parallel lines the two tests agree exactly**: same base point, same direction.
The seeded question `(rep eᵢ u, s)` and the canonical question `Line.through u eᵢ` describe
one line in one presentation, and the seed `s` is all the former carries beyond it. -/
theorem rep_single_eq_through [DecidableEq F] (i : Fin n) (u : Fin n → F) :
    (canonLin (span F {(Pi.single i 1 : Fin n → F)}) u, (Pi.single i 1 : Fin n → F))
      = Line.through u (Pi.single i 1) := by
  rw [through_single, rep_single]

end MIPRE.LIDT.Adapter
