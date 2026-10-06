/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Game

@[expose] public section

/-!
# Linear forms on windows of the answers

The linear-constraints processor of the tailored question reduction writes its constraints as
linear forms on fixed windows of the two answers: a register sits at a known offset of the
re-encoded answer (`MIPRE.Tailored.Intro.enc`). This file is the arithmetic of that:

* `dotL c v`, the `F₂` inner product of two bit strings, and `satisfies_append_iff`: the
  constraint `α ++ β ++ [γ]` holds of `a ++ b ++ [true]` exactly when `⟨α, a⟩ + ⟨β, b⟩ = γ`;
* `place n off w`, the vector of length `n` carrying `w` at offset `off`, and `dotL_place`: its
  inner product with `a` is that of `w` with the window of `a` at `off`;
* `eqCons`: the constraints that a window of `a` equals a window of `b`, bit by bit, and
  `eqCons_iff`;
* `guardCons b`: no constraint when the readable condition `b` holds, the rejecting one otherwise.
-/

namespace MIPRE.Tailored.Intro

open Cost

/-! ## The inner product -/

/-- The `F₂` inner product of two bit strings, on their common prefix. -/
def dotL : BitStr → BitStr → Bool
  | x :: c, y :: v => xor (x && y) (dotL c v)
  | _, _ => false

@[simp] theorem dotL_nil_left (v : BitStr) : dotL [] v = false := by cases v <;> rfl

@[simp] theorem dotL_cons_cons (x y : Bool) (c v : BitStr) :
    dotL (x :: c) (y :: v) = xor (x && y) (dotL c v) := rfl

theorem dotL_eq_odd : ∀ c v : BitStr,
    dotL c v = decide (Odd ((List.zipWith (· && ·) c v).count true))
  | [], v => by simp
  | x :: c, [] => by simp [dotL]
  | x :: c, y :: v => by
    rw [dotL_cons_cons, dotL_eq_odd c v, List.zipWith_cons_cons, List.count_cons]
    generalize List.count true (List.zipWith (fun x1 x2 => x1 && x2) c v) = n
    simp only [Nat.odd_iff]
    cases x <;> cases y <;> by_cases h : n % 2 = 1 <;> simp [h, Nat.add_mod]
    all_goals omega

theorem satisfies_iff_dotL {c v : BitStr} (h : c.length = v.length) :
    Satisfies c v ↔ dotL c v = false := by
  simp [Satisfies, dotL_eq_odd, h, Nat.not_odd_iff_even]

theorem dotL_append : ∀ {c c' v v' : BitStr}, c.length = v.length →
    dotL (c ++ c') (v ++ v') = xor (dotL c v) (dotL c' v')
  | [], c', [], v', _ => by simp
  | x :: c, c', y :: v, v', h => by
    simp only [List.cons_append, dotL_cons_cons]
    rw [dotL_append (by simpa using h), Bool.xor_assoc]

/-- **A constraint on the two answers and the affine coordinate**, read. -/
theorem satisfies_append_iff {α β a b : BitStr} (γ : Bool) (ha : α.length = a.length)
    (hb : β.length = b.length) :
    Satisfies (α ++ β ++ [γ]) (a ++ b ++ [true]) ↔ xor (dotL α a) (dotL β b) = γ := by
  rw [satisfies_iff_dotL (by simp [ha, hb]), dotL_append (by simp [ha, hb]),
    dotL_append ha]
  simp only [dotL_cons_cons, Bool.and_true, dotL_nil_left, Bool.xor_false]
  cases γ <;> cases dotL α a <;> cases dotL β b <;> simp

theorem dotL_replicate_false (m : ℕ) (v : BitStr) : dotL (List.replicate m false) v = false := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    cases v with
    | nil => simp [List.replicate_succ, dotL]
    | cons y v => simp [List.replicate_succ, ih]

/-! ## Vectors placed at an offset -/

/-- The vector of length `n` with `w` at offset `off` and zeros elsewhere (when it fits). -/
def place (n off : ℕ) (w : BitStr) : BitStr :=
  List.replicate off false ++ w ++ List.replicate (n - off - w.length) false

theorem length_place {n off : ℕ} {w : BitStr} (h : off + w.length ≤ n) :
    (place n off w).length = n := by
  simp [place]; omega

/-- **The inner product with a placed vector is that with the window.** -/
theorem dotL_place {n off : ℕ} {w a : BitStr} (h : off + w.length ≤ n) (ha : a.length = n) :
    dotL (place n off w) a = dotL w ((a.drop off).take w.length) := by
  unfold place
  conv_lhs => rw [← List.take_append_drop off a]
  rw [List.append_assoc, dotL_append (by simp; omega), dotL_replicate_false, Bool.false_xor]
  conv_lhs => rw [← List.take_append_drop w.length (a.drop off)]
  rw [dotL_append (by simp; omega), dotL_replicate_false, Bool.xor_false]

/-! ## Equality of windows -/

/-- The unit vector `eᵢ` of length `m`. -/
def unit (m i : ℕ) : BitStr := place m i [true]

theorem length_unit {m i : ℕ} (hi : i < m) : (unit m i).length = m :=
  length_place (by simp; omega)

theorem dotL_unit {m i : ℕ} (hi : i < m) {w : BitStr} (hw : w.length = m) :
    dotL (unit m i) w = w[i]'(by omega) := by
  rw [unit, dotL_place (by simp; omega) hw]
  rw [show (w.drop i).take [true].length = [w[i]'(by omega)] by
    simp only [List.length_singleton, List.take_one, List.head?_drop,
      List.getElem?_eq_getElem (by omega : i < w.length), Option.toList_some]]
  simp

/-- The constraints `a_{oa+i} = b_{ob+i}` for `i < m`, on answers of lengths `la`, `lb`. -/
def eqCons (la lb oa ob m : ℕ) : List BitStr :=
  (List.range m).map fun i => place la oa (unit m i) ++ place lb ob (unit m i) ++ [false]

/-- **The window equality constraints hold exactly when the windows are equal.** -/
theorem eqCons_iff {la lb oa ob m : ℕ} {a b : BitStr} (ha : a.length = la) (hb : b.length = lb)
    (hoa : oa + m ≤ la) (hob : ob + m ≤ lb) :
    (∀ c ∈ eqCons la lb oa ob m, Satisfies c (a ++ b ++ [true])) ↔
      (a.drop oa).take m = (b.drop ob).take m := by
  have hwa : ((a.drop oa).take m).length = m := by simp; omega
  have hwb : ((b.drop ob).take m).length = m := by simp; omega
  have key : ∀ i (hi : i < m), (Satisfies (place la oa (unit m i) ++ place lb ob (unit m i) ++
      [false]) (a ++ b ++ [true]) ↔
      ((a.drop oa).take m)[i]'(by omega) = ((b.drop ob).take m)[i]'(by omega)) := by
    intro i hi
    have hu := length_unit hi
    rw [satisfies_append_iff false (by rw [length_place (by omega), ha])
      (by rw [length_place (by omega), hb]),
      dotL_place (by omega) ha, dotL_place (by omega) hb, hu,
      dotL_unit hi hwa, dotL_unit hi hwb]
    cases ((a.drop oa).take m)[i]'(by omega) <;> cases ((b.drop ob).take m)[i]'(by omega) <;>
      simp
  constructor
  · intro h
    apply List.ext_getElem (by rw [hwa, hwb])
    intro i h1 h2
    exact (key i (by omega)).1 (h _ (List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩))
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact (key i (List.mem_range.1 hi)).2 (by simp only [h])

/-! ## Readable guards -/

/-- No constraint when the readable condition holds, the rejecting one otherwise. -/
def guardCons (b : Bool) (d : ℕ) : List BitStr := if b then [] else [rejectConstraint d]

theorem guardCons_iff {b : Bool} {d : ℕ} {v : BitStr} :
    (∀ c ∈ guardCons b d, Satisfies c (v ++ [true])) ↔ b = true := by
  unfold guardCons
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton, forall_eq, iff_false]
    have := not_satisfies_rejectConstraint d v
    exact this
  · simp

end MIPRE.Tailored.Intro

end
