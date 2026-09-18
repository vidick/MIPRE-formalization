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

Two further discrepancies are settled here, both of them differences of presentation rather
than of content.

**The diagonal convention.** The seeded test's diagonal directions have their *first* `i`
coordinates zero (`CL.zeroBelow`), the canonical-line test's have their coordinates *past* `j`
zero (`Sample.extend`). Coordinate reversal exchanges them (`revPoint_zeroBelow`), and is the
`ρ` of the paper's own reduction, there for the same reason against the tensor code test.

**The direction scale.** A `DLine` question of the seeded test carries the direction itself,
scale included, while the canonical-line test normalizes it. So the seeded questions
`(u₀, s, c • w)`, `c ≠ 0`, all describe one canonical line, and an answer in the parameter of
`u₀ + t (c • w)` has to be reparametrized. The parameter scales inversely
(`lineParam_smul`) and the polynomial follows by `rescale`, which is a bijection of the
coefficient vectors preserving the degree bound (`rescaleEquiv`) --- so no answer alphabet
changes and no degree is lost.

What is *not* here is the reconciliation of `CL.lineParam` with `Line.param`, the last of the
geometric discrepancies, nor anything about strategies or values.
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

/-! ## Coordinate reversal, and the two diagonal conventions

The seeded test's diagonal directions have their *first* `i` coordinates zero
(`CL.zeroBelow`); the canonical-line test's have their coordinates *past* `j` zero
(`Sample.extend`). Coordinate reversal exchanges the two, and is the `ρ` of the paper's own
reduction (there it exchanges the seeded test's convention with the tensor code test's, for the
same reason). -/

/-- Coordinate reversal of `F^n`, an involution. -/
def revPoint : (Fin n → F) ≃ (Fin n → F) where
  toFun x := fun j => x (Fin.rev j)
  invFun x := fun j => x (Fin.rev j)
  left_inv x := by funext j; simp [Fin.rev_rev]
  right_inv x := by funext j; simp [Fin.rev_rev]

omit [Field F] in
@[simp] theorem revPoint_apply (x : Fin n → F) (j : Fin n) :
    revPoint x j = x (Fin.rev j) := rfl

omit [Field F] in
@[simp] theorem revPoint_revPoint (x : Fin n → F) : revPoint (revPoint x) = x :=
  revPoint.left_inv x

@[simp] theorem revPoint_add (x y : Fin n → F) :
    revPoint (x + y) = revPoint x + revPoint y := rfl

@[simp] theorem revPoint_smul (c : F) (x : Fin n → F) :
    revPoint (c • x) = c • revPoint x := rfl

omit [Field F] in
/-- Reversal is injective, so membership of a line transports through it. -/
theorem revPoint_eq_iff {x y : Fin n → F} : revPoint x = revPoint y ↔ x = y :=
  revPoint.apply_eq_iff_eq

@[simp] theorem revPoint_sub (x y : Fin n → F) :
    revPoint (x - y) = revPoint x - revPoint y := rfl

/-- Reversal sends the `i`-th coordinate direction to the `rev i`-th. -/
theorem revPoint_single [DecidableEq F] (i : Fin n) :
    revPoint (Pi.single i 1 : Fin n → F) = Pi.single (Fin.rev i) 1 := by
  funext j
  rw [revPoint_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : j = Fin.rev i
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun hc : Fin.rev j = i => h (by rw [← hc, Fin.rev_rev]))]

/-- **Reversal exchanges the two tests' base points on an axis-parallel line.** The adapter sends
the canonical line through `u` in direction `eᵢ` to a seeded question with base point
`rep e_{rev i} (ρ u)`; reversing that back gives exactly the base point the *seeded* test
produces for the unreversed data. This is the form the weight bookkeeping needs, since the
seeded test's own samples carry the unreversed point. -/
theorem revPoint_rep_single [DecidableEq F] (i : Fin n) (u : Fin n → F) :
    revPoint (canonLin (span F {(Pi.single (Fin.rev i) 1 : Fin n → F)}) (revPoint u))
      = canonLin (span F {(Pi.single i 1 : Fin n → F)}) u := by
  rw [rep_single, rep_single, revPoint_sub, revPoint_revPoint, revPoint_smul, revPoint_single,
    Fin.rev_rev, revPoint_apply, Fin.rev_rev]

/-- **Reversal exchanges the two diagonal conventions.** A direction whose first `i`
coordinates vanish becomes one whose coordinates past `rev i` vanish, which is the shape
`Sample.extend` produces. -/
theorem revPoint_zeroBelow [NeZero n] (i : Fin n) (v : Fin n → F) :
    revPoint (CL.zeroBelow i v)
      = Sample.extend (j := Fin.rev i)
          (fun k : Fin ((Fin.rev i).val + 1) =>
            revPoint v ⟨k.val, lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt) (Fin.rev i).isLt⟩) := by
  funext j
  rw [revPoint_apply, CL.zeroBelow, Sample.extend]
  have hrev : (Fin.rev j).val = n - (j.val + 1) := Fin.val_rev j
  have hrevi : (Fin.rev i).val = n - (i.val + 1) := Fin.val_rev i
  by_cases h : j.val ≤ (Fin.rev i).val
  · -- `j` is within the free range, and the reversed coordinate is at or above `i`
    rw [dif_pos h]
    have hge : ¬ ((Fin.rev j).val < i.val) := by omega
    rw [if_neg hge]
    exact congrArg v (Fin.ext (by simp))
  · -- `j` is past the free range, and the reversed coordinate is below `i`
    rw [dif_neg h]
    have hlt : (Fin.rev j).val < i.val := by omega
    rw [if_pos hlt]

/-! ## The direction scale

A `DLine` question of the seeded test carries the direction `v'` itself, scale included, while
the canonical-line test normalizes the direction. So one canonical diagonal line is described
by the seeded questions `(u₀, s, c • w)` for every `c ≠ 0`, and an answer given in the
parameter of `u₀ + t (c • w)` has to be reparametrized into that of `u₀ + t w`. Both halves are
here: `lineParam_smul` for the parameter and `rescale` for the polynomial. -/

/-- Rescaling the variable of a polynomial: `rescale c f` is `t ↦ f (c t)`, on coefficients. -/
def rescale (c : F) {k : ℕ} (f : LinePoly F k) : LinePoly F k :=
  fun i => f i * c ^ (i : ℕ)

@[simp] theorem eval_rescale (c : F) {k : ℕ} (f : LinePoly F k) (t : F) :
    (rescale c f).eval t = f.eval (c * t) := by
  simp only [LinePoly.eval, rescale, mul_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Rescaling by `c` then by `c⁻¹` is the identity, so `rescale` is a bijection of the
coefficient vectors for `c ≠ 0` --- the degree bound is preserved on the nose, which is what
the answer alphabets need. -/
theorem rescale_rescale_inv (c : F) (hc : c ≠ 0) {k : ℕ} (f : LinePoly F k) :
    rescale c⁻¹ (rescale c f) = f := by
  funext i
  simp only [rescale]
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]

/-- Rescaling as an equivalence of the answer alphabet. -/
def rescaleEquiv (c : F) (hc : c ≠ 0) {k : ℕ} : LinePoly F k ≃ LinePoly F k where
  toFun := rescale c
  invFun := rescale c⁻¹
  left_inv f := rescale_rescale_inv c hc f
  right_inv f := by
    have := rescale_rescale_inv c⁻¹ (inv_ne_zero hc) f
    rwa [inv_inv] at this

section Scale

variable [DecidableEq F]

/-- Scaling the direction does not move the first nonzero coordinate. -/
theorem find_smul {c : F} (hc : c ≠ 0) {w : Fin n → F}
    (hex : ∃ j, w j ≠ 0) (hex' : ∃ j, (c • w) j ≠ 0) :
    Fin.find (fun j => (c • w) j ≠ 0) hex' = Fin.find (fun j => w j ≠ 0) hex := by
  rw [Fin.find_eq_iff]
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or]
    exact ⟨hc, Fin.find_spec hex⟩
  · have h0 : w j = 0 := not_not.mp (Fin.find_min hex hj)
    simp [h0]

/-- **The parameter scales inversely to the direction.** A point at parameter `t` on
`u₀ + t w` sits at parameter `c⁻¹ t` on `u₀ + t (c • w)`. -/
theorem lineParam_smul {c : F} (hc : c ≠ 0) (u₀ w x : Fin n → F) :
    CL.lineParam u₀ (c • w) x = c⁻¹ * CL.lineParam u₀ w x := by
  by_cases hex : ∃ j, w j ≠ 0
  · have hex' : ∃ j, (c • w) j ≠ 0 := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, by simpa [hc] using mul_ne_zero hc hj⟩
    simp only [CL.lineParam]
    rw [dif_pos hex, dif_pos hex', find_smul hc hex hex']
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
  · have hex' : ¬ ∃ j, (c • w) j ≠ 0 := by
      rintro ⟨j, hj⟩
      exact hex ⟨j, fun h0 => hj (by simp [h0])⟩
    simp only [CL.lineParam]
    rw [dif_neg hex, dif_neg hex', mul_zero]

/-! ## The two parameter conventions

`CL.lineParam u₀ w x` divides by the direction's first nonzero coordinate; `Line.param ℓ x`
reads off that coordinate of `x`, which is correct only because the canonical-line test's
directions are normalized and its base points vanish there. Both compute *the* parameter `t` of
a point `u₀ + t w` on the line, and that is the form in which they can be compared. -/

/-- `CL.lineParam` recovers the parameter of a point on the line. -/
theorem lineParam_eq_of_mem {w : Fin n → F} (hw : ∃ j, w j ≠ 0) (u₀ : Fin n → F) (t : F) :
    CL.lineParam u₀ w (u₀ + t • w) = t := by
  simp only [CL.lineParam, dif_pos hw]
  set j := Fin.find (fun j => w j ≠ 0) hw with hj
  have hwj : w j ≠ 0 := Fin.find_spec hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  exact mul_div_cancel_right₀ t hwj

/-- And so does `Line.param`, on the canonical presentation the canonical-line test uses: the
direction's first nonzero coordinate is `1` and the base point vanishes there, which is what
makes reading off that one coordinate correct. -/
theorem param_through_eq_of_mem {v : Fin n → F} (hv : ∃ j, v j ≠ 0) (u : Fin n → F) (t : F) :
    Line.param (Line.through u v) ((Line.through u v).1 + t • (Line.through u v).2) = t := by
  classical
  set j := Fin.find (fun k => v k ≠ 0) hv with hj
  have hvj : v j ≠ 0 := Fin.find_spec hv
  have hthr : Line.through u v = (u - u j • ((v j)⁻¹ • v), (v j)⁻¹ • v) := by
    rw [Line.through, dif_pos hv]
  have hd2 : (Line.through u v).2 = (v j)⁻¹ • v := by rw [hthr]
  have hex' : ∃ k, ((Line.through u v).2) k ≠ 0 := by
    refine ⟨j, ?_⟩
    rw [hd2]
    simpa using mul_ne_zero (inv_ne_zero hvj) hvj
  have hfind : Fin.find (fun k => ((Line.through u v).2) k ≠ 0) hex' = j := by
    rw [Fin.find_eq_iff]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hd2]
      simpa using mul_ne_zero (inv_ne_zero hvj) hvj
    · have h0 : v k = 0 := not_not.mp (Fin.find_min hv (hj ▸ hk))
      rw [hd2]
      simp [h0]
  have hb : (Line.through u v).1 j = 0 := by
    rw [hthr]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel₀ hvj, mul_one, sub_self]
  have hd : (Line.through u v).2 j = 1 := by
    rw [hd2]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hvj
  simp only [Line.param, dif_pos hex', hfind, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb, hd,
    mul_one, zero_add]

/-! ## The seeded test's canonical representative, in general

`rep w x` zeroes the coordinate of `x` at the *first nonzero coordinate of `w`*. Under
reversal, the first nonzero coordinate of `ρ dir` is the reversal of the **last** nonzero
coordinate of `dir`, whereas `Line.through` zeroes the coordinate at the **first** nonzero
coordinate of `dir`. So on a diagonal line the two tests pick *different* base points, and the
reparametrization between their answer polynomials is affine rather than linear --- this is the
"canonicalization and rebasing" of `rem:lidt-cl-adapter`. On an axis-parallel line the first and
last nonzero coordinates coincide and the shift vanishes, which is why `rep_single_eq_through`
came out clean. -/

/-- The pivot set of any line is its direction's first nonzero coordinate. -/
theorem pivots_span_singleton {w : Fin n → F} (hw : ∃ j, w j ≠ 0) :
    pivots (span F {w}) = {Fin.find (fun j => w j ≠ 0) hw} := by
  classical
  set p := Fin.find (fun j => w j ≠ 0) hw with hp
  have hwp : w p ≠ 0 := Fin.find_spec hw
  have hle : ∀ k ≤ (p : ℕ), (span F {w} ⊓ tail n k : Submodule F (Fin n → F)) = span F {w} := by
    intro k hk
    refine inf_eq_left.mpr ?_
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_tail]
    intro i hi
    exact not_not.mp (Fin.find_min hw (by rw [hp] at *; omega))
  have hgt : (span F {w} ⊓ tail n ((p : ℕ) + 1) : Submodule F (Fin n → F)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxs, hxt⟩ := hx
    simp only [SetLike.mem_coe] at hxs hxt
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxs
    rw [mem_tail] at hxt
    have hzero := hxt p (Nat.lt_succ_self _)
    rw [← hc] at hzero ⊢
    simp only [Pi.smul_apply, smul_eq_mul] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · simp [h]
    · exact absurd h hwp
  have hrank : finrank F (span F {w}) = 1 := finrank_span_singleton (by
    intro h
    exact hwp (by rw [h]; rfl))
  have hmem : p ∈ pivots (span F {w}) := by
    rw [mem_pivots, dimTail, dimTail, hle (p : ℕ) le_rfl, hgt, finrank_bot, hrank]
    exact Nat.zero_lt_one
  have hcard : (pivots (span F {w})).card = 1 := by rw [card_pivots, hrank]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  rw [hj] at hmem ⊢
  rw [Finset.mem_singleton] at hmem
  rw [hmem]

/-- **The seeded test's base point, in closed form.** -/
theorem rep_eq {w : Fin n → F} (hw : ∃ j, w j ≠ 0) (x : Fin n → F) :
    canonLin (span F {w}) x
      = x - (x (Fin.find (fun j => w j ≠ 0) hw)
          / w (Fin.find (fun j => w j ≠ 0) hw)) • w := by
  classical
  set p := Fin.find (fun j => w j ≠ 0) hw with hp
  have hwp : w p ≠ 0 := Fin.find_spec hw
  refine projection_eq_of (isCompl_canonCompl (span F {w})).symm ?_ ?_
  · rw [canonCompl, mem_coordSub]
    intro i hi
    rw [pivots_span_singleton hw, Finset.mem_singleton] at hi
    subst hi
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hwp, sub_self]
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩

omit [DecidableEq F] in
/-- The base point depends only on the line, not on the point of it that produced it. -/
theorem rep_add_smul (w x : Fin n → F) (t : F) :
    canonLin (span F {w}) (x + t • w) = canonLin (span F {w}) x := by
  have hker : (t • w) ∈ LinearMap.ker (canonLin (span F {w})) := by
    rw [ker_canonLin]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  rw [map_add, (LinearMap.mem_ker).mp hker, add_zero]

/-! ## When two lines through a point coincide

The diagonal weight count needs this: the canonical-line test's diagonal samples `(j, v)` that
produce a given line are exactly those whose direction is *proportional* to it, which is why
several of them contribute and the weight is a sum rather than a single term. -/

/-- The canonical presentation, unfolded. -/
theorem through_eq {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    Line.through u z
      = (u - u (Fin.find (fun k => z k ≠ 0) hz) •
            ((z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z),
          (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z) := by
  rw [Line.through, dif_pos hz]

/-- The canonical direction, projected out. -/
theorem through_snd {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    (Line.through u z).2 = (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z := by
  rw [through_eq hz]

/-- The canonical base point, projected out. -/
theorem through_fst {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    (Line.through u z).1 = u - u (Fin.find (fun k => z k ≠ 0) hz) •
      ((z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z) := by
  rw [through_eq hz]

/-- The point a canonical presentation was built from lies on the line it presents. -/
theorem through_mem {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    u = (Line.through u z).1
      + (u (Fin.find (fun k => z k ≠ 0) hz)) • (Line.through u z).2 := by
  rw [through_fst hz, through_snd hz, sub_add_cancel]

/-- **Two lines through the same point coincide exactly when their directions are
proportional.** -/
theorem through_eq_through_iff {u w z : Fin n → F} (hw : ∃ k, w k ≠ 0) (hz : ∃ k, z k ≠ 0) :
    Line.through u z = Line.through u w ↔ ∃ c : F, c ≠ 0 ∧ z = c • w := by
  classical
  constructor
  · intro h
    set pz := Fin.find (fun k => z k ≠ 0) hz with hpz
    set pw := Fin.find (fun k => w k ≠ 0) hw with hpw
    have hzp : z pz ≠ 0 := Fin.find_spec hz
    have hwp : w pw ≠ 0 := Fin.find_spec hw
    have hdir : (z pz)⁻¹ • z = (w pw)⁻¹ • w := by
      have h2 := congrArg Prod.snd h
      rwa [through_eq hz, through_eq hw] at h2
    refine ⟨z pz * (w pw)⁻¹, mul_ne_zero hzp (inv_ne_zero hwp), ?_⟩
    have h4 : (z pz) • ((z pz)⁻¹ • z) = (z pz) • ((w pw)⁻¹ • w) := by rw [hdir]
    rw [smul_smul, mul_inv_cancel₀ hzp, one_smul, smul_smul] at h4
    exact h4
  · rintro ⟨c, hc, rfl⟩
    have hcw : ∃ k, (c • w) k ≠ 0 := by
      obtain ⟨k, hk⟩ := hw
      exact ⟨k, by simpa using mul_ne_zero hc hk⟩
    have hfind : Fin.find (fun k => (c • w) k ≠ 0) hcw
        = Fin.find (fun k => w k ≠ 0) hw := find_smul hc hw hcw
    have hwp : w (Fin.find (fun k => w k ≠ 0) hw) ≠ 0 := Fin.find_spec hw
    have hsame : ((c • w) (Fin.find (fun k => (c • w) k ≠ 0) hcw))⁻¹ • (c • w)
        = (w (Fin.find (fun k => w k ≠ 0) hw))⁻¹ • w := by
      rw [hfind]
      simp only [Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv_rev]
      congr 1
      field_simp
    rw [through_eq hcw, through_eq hw, hsame, hfind]

end Scale

end MIPRE.LIDT.Adapter
