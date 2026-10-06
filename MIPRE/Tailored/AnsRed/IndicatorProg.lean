/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.Indicator
public import MIPRE.Tailored.Canonical
public import MIPRE.Tailored.Repeat.Lists
public import MIPRE.Foundations.LowDegree.UnaryDegreeArithmetic

@[expose] public section

/-!
# The output indicator, as a program

The triangulated output indicator `L*` (Definition defn:decider-read, II:8381) of
`MIPRE.Tailored.AnsRed.Indicator`, written as a program of the ambient model: the four runs of
the answer-length calculator and the run of the processor of the canonical decider
(`MIPRE.Tailored.canonProg`, whose input builders it reuses), followed by a polynomial-time check
that decides `LstarOK` at the parameters `prm n` of the index.

* The check's pieces: unary ranges (`rangeU`), the positions of the ones of a window
  (`onesU`), the purified equation with its variables in unary (`pureEqnU`), the triangulation in
  unary (`triangleU`), and the table loop by loop (`tableU`), each with the program computing it
  and its reading (`toEqn_pureEqnU`, `map_toTri_triangleU`, `tableU_eq`).
* `lstarFinal prm`: the check, deciding `LstarOK (2^ℓ) (2^◇)` with `(ℓ, ◇) = prm n` in unary
  (`lstarFinal_apply`, through `lstarCheck_eq`): the powers of two are capped by the input, so
  the check is polynomial-time.
* `lstarProg prm L LP`: the output indicator of a tailored verifier with answer-length
  calculator `L` and processor `LP`; `lstarProg_accepts`: it accepts exactly when the five runs
  halt and `LstarOK` holds of their outputs.
-/

namespace MIPRE.Tailored.AnsRed

open Cost Cost.PolyTimeFun Polynomial
open MIPRE.LowDegree (ofBool)

/-! ## Helpers -/

section helpers

variable {ι α γ : Type*} [SizedEncoding ι] [SizedEncoding α] [SizedEncoding γ]

/-- Map over a list computed from the input, the input as the context. -/
noncomputable def mapR (F : PolyTimeFun (α × ι) γ) (l : PolyTimeFun ι (List α)) :
    PolyTimeFun ι (List γ) :=
  (mapWith F).comp (l.pair (PolyTimeFun.id _))

@[simp] theorem mapR_apply (F : PolyTimeFun (α × ι) γ) (l : PolyTimeFun ι (List α)) (i : ι) :
    mapR F l i = (l i).map fun a => F (a, i) := rfl

/-- `flatMap` over a list computed from the input, the input as the context. -/
noncomputable def flatMapR (F : PolyTimeFun (α × ι) (List γ)) (l : PolyTimeFun ι (List α)) :
    PolyTimeFun ι (List γ) :=
  RepProg.flattenF.comp (mapR F l)

@[simp] theorem flatMapR_apply (F : PolyTimeFun (α × ι) (List γ)) (l : PolyTimeFun ι (List α))
    (i : ι) : flatMapR F l i = (l i).flatMap fun a => F (a, i) := by
  simp [flatMapR, List.flatMap_def]

end helpers

/-- `&&`. -/
noncomputable def andF : PolyTimeFun (Bool × Bool) Bool := SAT.andProg

@[simp] theorem andF_apply (p : Bool × Bool) : andF p = (p.1 && p.2) := rfl

/-- `||`. -/
noncomputable def orF : PolyTimeFun (Bool × Bool) Bool :=
  congr (SAT.notBoolP.comp (andF.comp ((SAT.notBoolP.comp fst).pair (SAT.notBoolP.comp snd))))
    (fun p => p.1 || p.2) (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)

@[simp] theorem orF_apply (p : Bool × Bool) : orF p = (p.1 || p.2) := rfl

/-- Exclusive or. -/
noncomputable def xorF : PolyTimeFun (Bool × Bool) Bool :=
  congr (orF.comp ((andF.comp (fst.pair (SAT.notBoolP.comp snd))).pair
      (andF.comp ((SAT.notBoolP.comp fst).pair snd))))
    (fun p => xor p.1 p.2) (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)

@[simp] theorem xorF_apply (p : Bool × Bool) : xorF p = xor p.1 p.2 := rfl

/-- Some element of the list is `true`. -/
noncomputable def anyF : PolyTimeFun (List Bool) Bool :=
  congr (SAT.notBoolP.comp (SAT.allBoolProg.comp (map SAT.notBoolP))) (fun l => l.any id) (by
    intro l
    simp only [comp_apply, map_apply, SAT.allBoolProg_apply, SAT.notBoolP_apply]
    induction l with
    | nil => rfl
    | cons b l ih => cases b <;> simp_all)

@[simp] theorem anyF_apply (l : List Bool) : anyF l = l.any id := rfl

/-- The bit of a string at a unary position, `false` past the end. -/
noncomputable def getDU : PolyTimeFun (BitStr × Unary) Bool := (headD false).comp drop

theorem headD_drop {α : Type*} (l : List α) (n : ℕ) (d : α) : (l.drop n).headD d = l.getD n d := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => cases n <;> simp

@[simp] theorem getDU_apply (p : BitStr × Unary) : getDU p = p.1.getD p.2.length false := by
  simp [getDU]

/-- A unary list is the unary numeral of its length. -/
theorem unary_eq_of_length {u : Unary} {k : ℕ} (h : u.length = k) : u = unary k := by
  rw [← h, unary_length]

/-- The unary numerals below the length of `u`. -/
noncomputable def rangeU : PolyTimeFun Unary (List Unary) :=
  PolyTimeFun.reverse.comp (PolyTimeFun.tail.comp LowDegree.DegreeArithmetic.descendingUnaryProg)

@[simp] theorem rangeU_apply (u : Unary) : rangeU u = (List.range u.length).map unary := by
  simp only [rangeU, comp_apply, reverse_apply, tail_apply,
    LowDegree.DegreeArithmetic.descendingUnaryProg_apply,
    LowDegree.DegreeArithmetic.descendingUnary_eq]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.length_reverse, List.length_tail, List.length_ofFn,
      Nat.add_sub_cancel] at h₁
    rw [List.getElem_reverse, List.getElem_tail, List.getElem_ofFn, List.getElem_map,
      List.getElem_range]
    exact unary_eq_of_length (by simp; omega)

/-! ## The purified equation, in unary -/

/-- The positions `j < k`, in unary, at which `c` has a one at `o + j`: `onesFrom` in unary. -/
def onesU (c : BitStr) (o k : ℕ) : List Unary :=
  ((List.range k).map unary).flatMap fun j => if c.getD (o + j.length) false then [j] else []

theorem flatMap_filter_eq {β : Type*} (l : List ℕ) (p : ℕ → Bool) (f : ℕ → β) :
    (l.flatMap fun j => if p j then [f j] else []) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [List.flatMap_cons, h, ih]

theorem map_length_onesU (c : BitStr) (o k : ℕ) :
    (onesU c o k).map List.length = onesFrom c o k := by
  unfold onesU onesFrom
  rw [List.flatMap_map]
  simp only [length_unary]
  rw [flatMap_filter_eq (List.range k) (fun j => c.getD (o + j) false) unary, List.map_map]
  conv_rhs => rw [← List.map_id ((List.range k).filter fun j => c.getD (o + j) false)]
  exact List.map_congr_left fun j _ => by simp

/-- The purified equation (`pureEqn`) with its variables in unary and its right-hand side a bit:
the positions of the ones of the two linear windows, those of `y` shifted by `N`, and the parity
of the affine coordinate and the two readable inner products. -/
def pureEqnU (lRx lLx lRy lLy N : ℕ) (aR bR c : BitStr) : List Unary × Bool :=
  if c.length = lRx + lLx + lRy + lLy + 1 then
    (onesU c lRx lLx ++ (onesU c (lRx + lLx + lRy) lLy).map (unary N ++ ·),
      xor (c.getD (lRx + lLx + lRy + lLy) false)
        (xor (LowDegree.BinaryLinear.dotBits (c.take lRx) aR)
          (LowDegree.BinaryLinear.dotBits ((c.drop (lRx + lLx)).take lRy) bR)))
  else ([], true)

/-- An equation with its variables in unary, read. -/
def toEqn (e : List Unary × Bool) : Eqn := ⟨e.1.map List.length, ofBool e.2⟩

/-- The inner product of a window of `c` with `v`, as a sum, when the window lies in `c`. -/
theorem ofBool_dotBits_window {c v : BitStr} {o k : ℕ} (hk : o + k ≤ c.length) :
    (ofBool (LowDegree.BinaryLinear.dotBits ((c.drop o).take k) v) : ZMod 2) =
      ∑ j ∈ Finset.range k, bitAt c (o + j) * bitAt v j := by
  rw [LowDegree.BinaryLinear.ofBool_dotBits]
  induction k generalizing o v with
  | zero => simp
  | succ k ih =>
    have ho : o < c.length := by omega
    rw [List.drop_eq_getElem_cons ho, List.take_succ_cons]
    cases v with
    | nil =>
      simp only [List.zip_nil_right, List.map_nil, List.sum_nil]
      symm
      exact Finset.sum_eq_zero fun j _ => by simp [bitAt, LowDegree.ofBool]
    | cons b v =>
      rw [List.zip_cons_cons, List.map_cons, List.sum_cons,
        ih (o := o + 1) (v := v) (by omega), Finset.sum_range_succ']
      simp only [bitAt_cons_succ, bitAt_cons_zero, Nat.add_zero]
      have e : ∀ j, o + 1 + j = o + (j + 1) := fun j => by omega
      simp only [e]
      have hc : (ofBool c[o] : ZMod 2) = bitAt c o := by
        simp [bitAt, List.getD_eq_getElem?_getD, ho]
      rw [hc]
      ring

theorem toEqn_pureEqnU (lRx lLx lRy lLy N : ℕ) (aR bR c : BitStr) :
    toEqn (pureEqnU lRx lLx lRy lLy N aR bR c) = pureEqn lRx lLx lRy lLy N aR bR c := by
  unfold pureEqnU pureEqn toEqn
  split_ifs with h
  · simp only [List.map_append, List.map_map, map_length_onesU]
    congr 1
    · congr 1
      rw [← map_length_onesU, List.map_map]
      exact List.map_congr_left fun j _ => by simp
    · rw [LowDegree.BinaryLinear.ofBool_xor, LowDegree.BinaryLinear.ofBool_xor]
      have h1 := ofBool_dotBits_window (c := c) (v := aR) (o := 0) (k := lRx) (by omega)
      have h2 := ofBool_dotBits_window (c := c) (v := bR) (o := lRx + lLx) (k := lRy) (by omega)
      simp only [List.drop_zero, Nat.zero_add] at h1
      rw [h1, h2]
      simp only [bitAt]
      ring
  · rfl

/-- The rows the indicator decouples, in unary. -/
def rowsU (N lRx lLx lRy lLy : ℕ) (aR bR : BitStr) (cs : List BitStr) : List (List Unary × Bool) :=
  cs.map (pureEqnU lRx lLx lRy lLy N aR bR)

theorem map_toEqn_rowsU (N lRx lLx lRy lLy : ℕ) (aR bR : BitStr) (cs : List BitStr) :
    (rowsU N lRx lLx lRy lLy aR bR cs).map toEqn = lsRows N lRx lLx lRy lLy aR bR cs := by
  unfold rowsU lsRows
  rw [List.map_map]
  exact List.map_congr_left fun c _ => toEqn_pureEqnU _ _ _ _ _ _ _ _

/-! ## The triangulation, in unary -/

/-- A triangulated equation with its variables in unary, and its coefficients as the signature
word `[0, 0, a₁, a₂, a₃, b]` with which the table compares its signs. -/
abbrev TriU : Type := (Unary × Unary × Unary) × BitStr

/-- A triangulated equation in unary, read. -/
def toTri (t : TriU) : Tri :=
  ⟨t.1.1.length, t.1.2.1.length, t.1.2.2.length, ofBool (t.2.getD 2 false),
    ofBool (t.2.getD 3 false), ofBool (t.2.getD 4 false), ofBool (t.2.getD 5 false)⟩

/-- The signature word is `[0, 0, a₁, a₂, a₃, b]`. -/
def TriU.WF (t : TriU) : Prop :=
  t.2 = [false, false, t.2.getD 2 false, t.2.getD 3 false, t.2.getD 4 false, t.2.getD 5 false]

/-- `yv N r i = N + r N + i`, in unary. -/
def yvU (N r i : Unary) : Unary := N ++ (unary (r.length * N.length) ++ i)

@[simp] theorem length_yvU (N r i : Unary) :
    (yvU N r i).length = yv N.length r.length i.length := by
  simp [yvU, yv]; omega

/-- The triangulation of one row in unary (`triRow`), the row's index `r` in unary. -/
def triRowU (N r : Unary) (e : List Unary × Bool) : List TriU :=
  ((e.1.zip ((List.range e.1.length).map unary)).map fun p =>
      ((p.1, yvU N r p.2.tail, yvU N r p.2), [false, false, true, !p.2.isEmpty, true, false])) ++
    [((yvU N r (unary (e.1.length - 1)), [], []), [false, false, !e.1.isEmpty, false, false, e.2])]

/-- The triangulation in unary (`triangle`). -/
def triangleU (N : Unary) (rows : List (List Unary × Bool)) : List TriU :=
  ((rows.zip ((List.range rows.length).map unary)).map fun p => triRowU N p.2 p.1).flatten

theorem mapIdx_eq_zip_range {α β : Type*} (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = (l.zip (List.range l.length)).map fun p => f p.2 p.1 := by
  rw [List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', ← List.range_eq_range']

theorem map_toTri_triRowU (N r : Unary) (e : List Unary × Bool) :
    (triRowU N r e).map toTri = triRow N.length r.length (toEqn e) := by
  unfold triRowU triRow toEqn
  rw [List.map_append, mapIdx_eq_zip_range, List.zip_map_right, List.map_map, List.map_map,
    List.zip_map_left, List.map_map, List.length_map]
  congr 1
  · refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, toTri, length_yvU,
      List.length_tail, length_unary]
    congr 1
    simp [LowDegree.ofBool, unary]
  · simp only [List.map_cons, List.map_nil, toTri, length_yvU, length_unary, List.length_nil]
    congr 2
    cases e.1 <;> simp [LowDegree.ofBool]

theorem map_toTri_triangleU (N : Unary) (rows : List (List Unary × Bool)) :
    (triangleU N rows).map toTri = triangle N.length (rows.map toEqn) := by
  unfold triangleU triangle
  rw [List.map_flatten, List.map_map, mapIdx_eq_zip_range, List.zip_map_right, List.map_map,
    List.zip_map_left, List.map_map, List.length_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  rw [map_toTri_triRowU, length_unary]

theorem triRowU_wf (N r : Unary) (e : List Unary × Bool) : ∀ t ∈ triRowU N r e, t.WF := by
  intro t ht
  unfold triRowU at ht
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 ht
    rfl
  · rw [List.mem_singleton] at ht
    subst ht
    rfl

theorem triangleU_wf (N : Unary) (rows : List (List Unary × Bool)) :
    ∀ t ∈ triangleU N rows, t.WF := by
  intro t ht
  unfold triangleU at ht
  obtain ⟨l, hl, ht⟩ := List.mem_flatten.1 ht
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hl
  exact triRowU_wf _ _ _ t ht

/-! ## The table, in unary -/

/-- The six signs held by the last coordinate `s`, as a word `[ε_A, ε_B, ε₁, ε₂, ε₃, ε₀]`. -/
def signWord (s : ℕ) : BitStr := (List.range 6).map s.testBit

theorem signWord_eq (s : ℕ) : signWord s =
    [s.testBit 0, s.testBit 1, s.testBit 2, s.testBit 3, s.testBit 4, s.testBit 5] := by
  simp [signWord, List.range_succ]

/-- The 64 sign words, in the order of the last coordinate. -/
def signWords : List BitStr := (List.range 64).map signWord

/-- A triangulated equation matches the signs `w` and the three copy coordinates. -/
def triMatch (u₁ u₂ u₃ : Unary) (w : BitStr) (t : TriU) : Bool :=
  decide (w = t.2) && ((!t.2.getD 2 false || decide (u₁.length = t.1.1.length)) &&
    ((!t.2.getD 3 false || decide (u₂.length = t.1.2.1.length)) &&
      (!t.2.getD 4 false || decide (u₃.length = t.1.2.2.length))))

/-- The indicator at given coordinates and signs, in unary: `decInd` inside the loops, whose
ranges make its range conditions true. -/
def decIndU (uA uB u₁ u₂ u₃ : Unary) (w : BitStr) (N : Unary) (tris : List TriU) : Bool :=
  (decide (w = [true, false, true, false, false, false]) && decide (u₁.length = uA.length)) ||
    ((decide (w = [false, true, true, false, false, false]) &&
        decide (u₁.length = N.length + uB.length)) ||
      ((decide (w = [false, false, true, true, false, false]) &&
          decide (u₂.length = u₁.length)) ||
        ((decide (w = [false, false, false, true, true, false]) &&
            decide (u₃.length = u₂.length)) ||
          (tris.map (triMatch u₁ u₂ u₃ w)).any id)))

/-- The table, loop by loop, in unary. -/
def tableU (N D : Unary) (tris : List TriU) : BitStr :=
  signWords.flatMap fun w => ((List.range D.length).map unary).flatMap fun u₃ =>
    ((List.range D.length).map unary).flatMap fun u₂ =>
      ((List.range D.length).map unary).flatMap fun u₁ =>
        ((List.range N.length).map unary).flatMap fun uB =>
          ((List.range N.length).map unary).map fun uA => decIndU uA uB u₁ u₂ u₃ w N tris

theorem sgn_eq_ofBool {s i : ℕ} {b : Bool} : sgn s i = ofBool b ↔ s.testBit i = b :=
  ⟨fun h => LowDegree.BinaryLinear.ofBool_injective h, fun h => by rw [sgn, h]⟩

theorem sgn_eq_one {s i : ℕ} : sgn s i = 1 ↔ s.testBit i = true := sgn_eq_ofBool (b := true)

theorem sgn_eq_zero {s i : ℕ} : sgn s i = 0 ↔ s.testBit i = false := sgn_eq_ofBool (b := false)

theorem ofBool_ne_zero {b : Bool} : (ofBool b : ZMod 2) ≠ 0 ↔ b = true := by
  cases b <;> simp [LowDegree.ofBool]

/-- The fifth kind of equation of the indicator, read in unary. -/
private theorem row5_iff {s u₁ u₂ u₃ : ℕ} {tris : List TriU} (hwf : ∀ t ∈ tris, t.WF) :
    (sgn s 0 = 0 ∧ sgn s 1 = 0 ∧ ∃ t ∈ tris.map toTri, sgn s 2 = t.a₁ ∧ sgn s 3 = t.a₂ ∧
      sgn s 4 = t.a₃ ∧ sgn s 5 = t.b ∧ (t.a₁ ≠ 0 → u₁ = t.v₁) ∧ (t.a₂ ≠ 0 → u₂ = t.v₂) ∧
      (t.a₃ ≠ 0 → u₃ = t.v₃)) ↔
      ∃ t ∈ tris, triMatch (unary u₁) (unary u₂) (unary u₃) (signWord s) t = true := by
  constructor
  · rintro ⟨h0, h1, t', ht', h2, h3, h4, h5, i1, i2, i3⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
    refine ⟨t, ht, ?_⟩
    have hw := hwf t ht
    simp only [toTri] at h2 h3 h4 h5 i1 i2 i3
    rw [sgn_eq_zero] at h0 h1
    rw [sgn_eq_ofBool] at h2 h3 h4 h5
    rw [ofBool_ne_zero] at i1 i2 i3
    simp only [triMatch, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      length_unary]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hw, signWord_eq, h0, h1, h2, h3, h4, h5]
    · by_cases h : t.2.getD 2 false = true
      · exact Or.inr (i1 h)
      · exact Or.inl (by simpa using h)
    · by_cases h : t.2.getD 3 false = true
      · exact Or.inr (i2 h)
      · exact Or.inl (by simpa using h)
    · by_cases h : t.2.getD 4 false = true
      · exact Or.inr (i3 h)
      · exact Or.inl (by simpa using h)
  · rintro ⟨t, ht, hm⟩
    have hw := hwf t ht
    simp only [triMatch, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      length_unary] at hm
    obtain ⟨hs, j1, j2, j3⟩ := hm
    rw [hw, signWord_eq] at hs
    simp only [List.cons.injEq, and_true] at hs
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hs
    refine ⟨sgn_eq_zero.2 e0, sgn_eq_zero.2 e1, toTri t, List.mem_map_of_mem ht, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · exact sgn_eq_ofBool.2 e2
    · exact sgn_eq_ofBool.2 e3
    · exact sgn_eq_ofBool.2 e4
    · exact sgn_eq_ofBool.2 e5
    · intro h
      rw [toTri, ofBool_ne_zero] at h
      rcases j1 with j | j
      · rw [h] at j; exact absurd j (by decide)
      · exact j
    · intro h
      rw [toTri, ofBool_ne_zero] at h
      rcases j2 with j | j
      · rw [h] at j; exact absurd j (by decide)
      · exact j
    · intro h
      rw [toTri, ofBool_ne_zero] at h
      rcases j3 with j | j
      · rw [h] at j; exact absurd j (by decide)
      · exact j

/-- **The indicator in unary is `decInd`** inside the loops. -/
theorem decIndU_eq {N D uA uB u₁ u₂ u₃ s : ℕ} {tris : List TriU} (hwf : ∀ t ∈ tris, t.WF)
    (hA : uA < N) (hB : uB < N) (h₁ : u₁ < D) (h₂ : u₂ < D) :
    decIndU (unary uA) (unary uB) (unary u₁) (unary u₂) (unary u₃) (signWord s) (unary N) tris =
      decide (decInd N N D (tris.map toTri) uA uB u₁ u₂ u₃ (sgn s 0) (sgn s 1) (sgn s 2)
        (sgn s 3) (sgn s 4) (sgn s 5)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [decIndU, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, length_unary,
    List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  unfold decInd
  rw [← row5_iff hwf, signWord_eq]
  simp only [List.cons.injEq, and_true, sgn_eq_one, sgn_eq_zero]
  constructor
  · rintro (⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩ | ⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩ |
      ⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩ | ⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩ | h)
    · exact Or.inl ⟨e0, e1, e2, e3, e4, e5, hA, h⟩
    · exact Or.inr (Or.inl ⟨e0, e1, e2, e3, e4, e5, hB, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e0, e1, e2, e3, e4, e5, h₁, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e0, e1, e2, e3, e4, e5, h₂, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (⟨e0, e1, e2, e3, e4, e5, -, h⟩ | ⟨e0, e1, e2, e3, e4, e5, -, h⟩ |
      ⟨e0, e1, e2, e3, e4, e5, -, h⟩ | ⟨e0, e1, e2, e3, e4, e5, -, h⟩ | h)
    · exact Or.inl ⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩
    · exact Or.inr (Or.inl ⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨e0, e1, e2, e3, e4, e5⟩, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem flatMap_congr_mem {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- **The table in unary is the table**, on well-formed equations. -/
theorem tableU_eq (N D : ℕ) {tris : List TriU} (hwf : ∀ t ∈ tris, t.WF) :
    tableU (unary N) (unary D) tris = indTable N D (tris.map toTri) := by
  rw [indTable_eq_indLoop]
  unfold tableU indLoop signWords
  simp only [length_unary, List.flatMap_map, List.map_map]
  refine flatMap_congr_mem fun s _ => flatMap_congr_mem fun u₃ _ => flatMap_congr_mem
    fun u₂ hu₂ => flatMap_congr_mem fun u₁ hu₁ => flatMap_congr_mem fun uB huB =>
      List.map_congr_left fun uA huA => ?_
  rw [List.mem_range] at hu₂ hu₁ huB huA
  exact decIndU_eq hwf huA huB hu₁ hu₂

/-! ## The programs of the pieces -/

open LowDegree.DegreeArithmetic (eqUnaryProg leUnaryProg mulUnaryProg isEmptyProg)

/-- `onesU`, as a program on `(c, o, k)`. -/
noncomputable def onesUF : PolyTimeFun (BitStr × Unary × Unary) (List Unary) :=
  congr (flatMapR
      (PolyTimeFun.ite
        (getDU.comp ((fst.comp snd).pair (append.comp ((fst.comp (snd.comp snd)).pair fst))))
        (cons fst (const [])) (const []))
      (rangeU.comp (snd.comp snd)))
    (fun p => onesU p.1 p.2.1.length p.2.2.length) (by
      rintro ⟨c, o, k⟩
      simp [onesU])

@[simp] theorem onesUF_apply (p : BitStr × Unary × Unary) :
    onesUF p = onesU p.1 p.2.1.length p.2.2.length := rfl

/-- The context of a purified equation: the four lengths, the table size, the readable answers. -/
abbrev PCtx : Type := Unary × Unary × Unary × Unary × Unary × BitStr × BitStr

/-- The program computing `pureEqnU` on a constraint and its context. -/
noncomputable def pureEqnRaw : PolyTimeFun (BitStr × PCtx) (List Unary × Bool) :=
  let c : PolyTimeFun (BitStr × PCtx) BitStr := fst
  let lRx : PolyTimeFun (BitStr × PCtx) Unary := fst.comp snd
  let lLx : PolyTimeFun (BitStr × PCtx) Unary := fst.comp (snd.comp snd)
  let lRy : PolyTimeFun (BitStr × PCtx) Unary := fst.comp (snd.comp (snd.comp snd))
  let lLy : PolyTimeFun (BitStr × PCtx) Unary := fst.comp (snd.comp (snd.comp (snd.comp snd)))
  let N : PolyTimeFun (BitStr × PCtx) Unary :=
    fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
  let aR : PolyTimeFun (BitStr × PCtx) BitStr :=
    fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
  let bR : PolyTimeFun (BitStr × PCtx) BitStr :=
    snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
  let s2 : PolyTimeFun (BitStr × PCtx) Unary := append.comp (lRx.pair lLx)
  let s3 : PolyTimeFun (BitStr × PCtx) Unary := append.comp (s2.pair lRy)
  let s4 : PolyTimeFun (BitStr × PCtx) Unary := append.comp (s3.pair lLy)
  PolyTimeFun.ite (eqUnaryProg.comp ((length.comp c).pair (cons (const ()) s4)))
    ((append.comp ((onesUF.comp (c.pair (lRx.pair lLx))).pair
        (mapR (append.comp ((N.comp snd).pair fst)) (onesUF.comp (c.pair (s3.pair lLy)))))).pair
      (xorF.comp ((getDU.comp (c.pair s4)).pair
        (xorF.comp ((LowDegree.BinaryLinear.dotBitsProg.comp
            ((take.comp (c.pair lRx)).pair aR)).pair
          (LowDegree.BinaryLinear.dotBitsProg.comp
            ((take.comp ((drop.comp (c.pair s2)).pair lRy)).pair bR)))))))
    (const ([], true))

theorem pureEqnRaw_apply (p : BitStr × PCtx) :
    pureEqnRaw p = pureEqnU p.2.1.length p.2.2.1.length p.2.2.2.1.length p.2.2.2.2.1.length
      p.2.2.2.2.2.1.length p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2 p.1 := by
  obtain ⟨c, lRx, lLx, lRy, lLy, N, aR, bR⟩ := p
  simp only [pureEqnRaw, PolyTimeFun.ite_apply, comp_apply, pair_apply, fst_apply, snd_apply,
    length_apply, cons_apply, const_apply, append_apply,
    LowDegree.DegreeArithmetic.eqUnaryProg_apply, onesUF_apply, mapR_apply, xorF_apply,
    getDU_apply, LowDegree.BinaryLinear.dotBitsProg_apply,
    take_apply, drop_apply, List.length_append, List.length_cons, length_unary, pureEqnU,
    decide_eq_true_eq]
  by_cases h : c.length = lRx.length + lLx.length + lRy.length + lLy.length + 1
  · rw [ite_eq_left h, ite_eq_left h]
    congr 2
    exact List.map_congr_left fun j _ => by rw [unary_length]
  · rw [ite_eq_right h, ite_eq_right h]

/-- `pureEqnU`, as a program on a constraint and its context. -/
noncomputable def pureEqnUF : PolyTimeFun (BitStr × PCtx) (List Unary × Bool) :=
  congr pureEqnRaw _ pureEqnRaw_apply

@[simp] theorem pureEqnUF_apply (c : BitStr) (lRx lLx lRy lLy N : Unary) (aR bR : BitStr) :
    pureEqnUF (c, lRx, lLx, lRy, lLy, N, aR, bR) =
      pureEqnU lRx.length lLx.length lRy.length lLy.length N.length aR bR c := rfl

/-- The rows, as a program on the constraints and the context. -/
noncomputable def rowsUF : PolyTimeFun (List BitStr × PCtx) (List (List Unary × Bool)) :=
  mapWith pureEqnUF

@[simp] theorem rowsUF_apply (cs : List BitStr) (lRx lLx lRy lLy N : Unary) (aR bR : BitStr) :
    rowsUF (cs, lRx, lLx, lRy, lLy, N, aR, bR) =
      rowsU N.length lRx.length lLx.length lRy.length lLy.length aR bR cs := rfl

/-- `yvU`, as a program on `(N, r, i)`. -/
noncomputable def yvUF : PolyTimeFun (Unary × Unary × Unary) Unary :=
  append.comp (fst.pair (append.comp ((mulUnaryProg.comp ((fst.comp snd).pair fst)).pair
    (snd.comp snd))))

@[simp] theorem yvUF_apply (N r i : Unary) : yvUF (N, r, i) = yvU N r i := rfl

/-- The program computing `triRowU` on `(e, r, N)`. -/
noncomputable def triRowRaw : PolyTimeFun ((List Unary × Bool) × Unary × Unary) (List TriU) :=
  let e : PolyTimeFun ((List Unary × Bool) × Unary × Unary) (List Unary × Bool) := fst
  let r : PolyTimeFun ((List Unary × Bool) × Unary × Unary) Unary := fst.comp snd
  let N : PolyTimeFun ((List Unary × Bool) × Unary × Unary) Unary := snd.comp snd
  let step : PolyTimeFun ((Unary × Unary) × ((List Unary × Bool) × Unary × Unary)) TriU :=
    ((fst.comp fst).pair ((yvUF.comp ((N.comp snd).pair ((r.comp snd).pair
        (tail.comp (snd.comp fst))))).pair
      (yvUF.comp ((N.comp snd).pair ((r.comp snd).pair (snd.comp fst)))))).pair
    (listOf [const false, const false, const true,
      SAT.notBoolP.comp (isEmptyProg.comp (snd.comp fst)), const true, const false])
  let last : PolyTimeFun ((List Unary × Bool) × Unary × Unary) TriU :=
    ((yvUF.comp (N.pair (r.pair (tail.comp (length.comp (fst.comp e)))))).pair
      ((const []).pair (const []))).pair
    (listOf [const false, const false, SAT.notBoolP.comp (isEmptyProg.comp (fst.comp e)),
      const false, const false, snd.comp e])
  append.comp ((mapR step (zip.comp ((fst.comp e).pair
      (rangeU.comp (length.comp (fst.comp e)))))).pair (cons last (const [])))

theorem triRowRaw_apply (p : (List Unary × Bool) × Unary × Unary) :
    triRowRaw p = triRowU p.2.2 p.2.1 p.1 := by
  obtain ⟨⟨vs, b⟩, r, N⟩ := p
  simp only [triRowRaw, comp_apply, append_apply, mapR_apply, zip_apply, pair_apply, fst_apply,
    snd_apply, rangeU_apply, length_apply, length_unary, cons_apply, const_apply,
    listOf_apply, List.map_cons, List.map_nil, yvUF_apply, tail_apply,
    SAT.notBoolP_apply, LowDegree.DegreeArithmetic.isEmptyProg_apply, triRowU]
  congr 2
  simp [unary, List.tail_replicate]

/-- `triRowU`, as a program on `(e, r, N)`. -/
noncomputable def triRowUF : PolyTimeFun ((List Unary × Bool) × Unary × Unary) (List TriU) :=
  congr triRowRaw _ triRowRaw_apply

@[simp] theorem triRowUF_apply (e : List Unary × Bool) (r N : Unary) :
    triRowUF (e, r, N) = triRowU N r e := rfl

/-- `triangleU`, as a program on `(rows, N)`. -/
noncomputable def triangleUF : PolyTimeFun (List (List Unary × Bool) × Unary) (List TriU) :=
  congr (flatMapR (triRowUF.comp ((fst.comp fst).pair ((snd.comp fst).pair (snd.comp snd))))
      (zip.comp (fst.pair (rangeU.comp (length.comp fst)))))
    (fun p => triangleU p.2 p.1) (by
      rintro ⟨rows, N⟩
      simp only [flatMapR_apply, comp_apply, pair_apply, fst_apply, snd_apply, zip_apply,
        rangeU_apply, length_apply, length_unary, triRowUF_apply, triangleU, List.flatMap_def])

@[simp] theorem triangleUF_apply (rows : List (List Unary × Bool)) (N : Unary) :
    triangleUF (rows, N) = triangleU N rows := rfl

/-- `triMatch`, as a program on `(t, u₁, u₂, u₃, w)`. -/
noncomputable def triMatchRaw : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Bool :=
  let sig : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) BitStr := snd.comp fst
  let v₁ : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary := fst.comp (fst.comp fst)
  let v₂ : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary :=
    fst.comp (snd.comp (fst.comp fst))
  let v₃ : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary :=
    snd.comp (snd.comp (fst.comp fst))
  let u₁ : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary := fst.comp snd
  let u₂ : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary := fst.comp (snd.comp snd)
  let u₃ : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary :=
    fst.comp (snd.comp (snd.comp snd))
  let w : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) BitStr :=
    snd.comp (snd.comp (snd.comp snd))
  let slot : ℕ → PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary →
      PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Unary →
      PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Bool := fun k u v =>
    orF.comp ((SAT.notBoolP.comp ((nthD false k).comp sig)).pair (eqUnaryProg.comp (u.pair v)))
  andF.comp ((SAT.ArrayProg.eqBits.comp (w.pair sig)).pair (andF.comp ((slot 2 u₁ v₁).pair
    (andF.comp ((slot 3 u₂ v₂).pair (slot 4 u₃ v₃))))))

theorem triMatchRaw_apply (p : TriU × Unary × Unary × Unary × BitStr) :
    triMatchRaw p = triMatch p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 p.1 := by
  obtain ⟨t, u₁, u₂, u₃, w⟩ := p
  simp only [triMatchRaw, comp_apply, pair_apply, fst_apply, snd_apply, andF_apply, orF_apply,
    SAT.notBoolP_apply, nthD_apply, LowDegree.DegreeArithmetic.eqUnaryProg_apply,
    SAT.ArrayProg.eqBits_apply, triMatch]

/-- `triMatch`, as a program. -/
noncomputable def triMatchF : PolyTimeFun (TriU × Unary × Unary × Unary × BitStr) Bool :=
  congr triMatchRaw _ triMatchRaw_apply

/-- The input of the indicator in the loops: the five coordinates, the signs, `N`, `D` and the
triangulated equations. -/
abbrev IIn : Type := Unary × Unary × Unary × Unary × Unary × BitStr × Unary × Unary × List TriU

/-- `decIndU`, as a program. -/
noncomputable def decIndRaw : PolyTimeFun IIn Bool :=
  let uA : PolyTimeFun IIn Unary := fst
  let uB : PolyTimeFun IIn Unary := fst.comp snd
  let u₁ : PolyTimeFun IIn Unary := fst.comp (snd.comp snd)
  let u₂ : PolyTimeFun IIn Unary := fst.comp (snd.comp (snd.comp snd))
  let u₃ : PolyTimeFun IIn Unary := fst.comp (snd.comp (snd.comp (snd.comp snd)))
  let w : PolyTimeFun IIn BitStr := fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
  let N : PolyTimeFun IIn Unary :=
    fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
  let tris : PolyTimeFun IIn (List TriU) :=
    snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))))
  let row : BitStr → PolyTimeFun IIn Unary → PolyTimeFun IIn Unary → PolyTimeFun IIn Bool :=
    fun k u v => andF.comp ((SAT.ArrayProg.eqBits.comp (w.pair (const k))).pair
      (eqUnaryProg.comp (u.pair v)))
  orF.comp ((row [true, false, true, false, false, false] u₁ uA).pair
    (orF.comp ((row [false, true, true, false, false, false] u₁ (append.comp (N.pair uB))).pair
      (orF.comp ((row [false, false, true, true, false, false] u₂ u₁).pair
        (orF.comp ((row [false, false, false, true, true, false] u₃ u₂).pair
          (anyF.comp (mapR (triMatchF.comp (fst.pair ((u₁.comp snd).pair ((u₂.comp snd).pair
            ((u₃.comp snd).pair (w.comp snd)))))) tris)))))))))

theorem decIndRaw_apply (p : IIn) :
    decIndRaw p = decIndU p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
      p.2.2.2.2.2.2.2.2 := by
  obtain ⟨uA, uB, u₁, u₂, u₃, w, N, D, tris⟩ := p
  simp only [decIndRaw, comp_apply, pair_apply, fst_apply, snd_apply, andF_apply, orF_apply,
    const_apply, append_apply, anyF_apply, mapR_apply, triMatchF, congr_apply,
    LowDegree.DegreeArithmetic.eqUnaryProg_apply, SAT.ArrayProg.eqBits_apply,
    List.length_append, decIndU]

/-- `decIndU`, as a program. -/
noncomputable def decIndF : PolyTimeFun IIn Bool := congr decIndRaw _ decIndRaw_apply

/-- The table program, loop by loop, on `(N, D, tris)`. -/
noncomputable def tableRaw : PolyTimeFun (Unary × Unary × List TriU) BitStr :=
  let B5 : PolyTimeFun (Unary × Unary × Unary × Unary × BitStr × Unary × Unary × List TriU)
      BitStr :=
    mapR decIndF (rangeU.comp (fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))))
  let B4 : PolyTimeFun (Unary × Unary × Unary × BitStr × Unary × Unary × List TriU) BitStr :=
    flatMapR B5 (rangeU.comp (fst.comp (snd.comp (snd.comp (snd.comp snd)))))
  let B3 : PolyTimeFun (Unary × Unary × BitStr × Unary × Unary × List TriU) BitStr :=
    flatMapR B4 (rangeU.comp (fst.comp (snd.comp (snd.comp (snd.comp snd)))))
  let B2 : PolyTimeFun (Unary × BitStr × Unary × Unary × List TriU) BitStr :=
    flatMapR B3 (rangeU.comp (fst.comp (snd.comp (snd.comp snd))))
  let B1 : PolyTimeFun (BitStr × Unary × Unary × List TriU) BitStr :=
    flatMapR B2 (rangeU.comp (fst.comp (snd.comp snd)))
  flatMapR B1 (const signWords)

theorem tableRaw_apply (p : Unary × Unary × List TriU) :
    tableRaw p = tableU p.1 p.2.1 p.2.2 := by
  obtain ⟨N, D, tris⟩ := p
  simp only [tableRaw, flatMapR_apply, mapR_apply, comp_apply, fst_apply, snd_apply, const_apply,
    rangeU_apply, decIndF, congr_apply, tableU]

/-- `tableU`, as a program. -/
noncomputable def tableF : PolyTimeFun (Unary × Unary × List TriU) BitStr :=
  congr tableRaw _ tableRaw_apply

@[simp] theorem tableF_apply (N D : Unary) (tris : List TriU) :
    tableF (N, D, tris) = tableU N D tris := rfl

/-! ## Powers of two, capped -/

/-- The step of `pow2CapF`: double the accumulator, capped at the length of the cap. -/
noncomputable def capStep : PolyTimeFun ((Unary × Unary) × Unit) (Unary × Unary) :=
  (take.comp ((append.comp ((fst.comp fst).pair (fst.comp fst))).pair (snd.comp fst))).pair
    (snd.comp fst)

@[simp] theorem capStep_apply (acc m : Unary) (x : Unit) :
    capStep ((acc, m), x) = ((acc ++ acc).take m.length, m) := rfl

theorem foldl_capStep (l : Unary) {acc m : Unary} (h : acc.length ≤ m.length) :
    l.foldl (fun s a => capStep (s, a)) (acc, m) =
      (unary (min (2 ^ l.length * acc.length) m.length), m) := by
  induction l generalizing acc with
  | nil => simp [unary_length, Nat.min_eq_left h]
  | cons x l ih =>
    rw [List.foldl_cons, capStep_apply, ih (by simp)]
    simp only [List.length_take, List.length_append, List.length_cons, Nat.pow_succ]
    congr 2
    have h1 : 1 ≤ 2 ^ l.length := Nat.one_le_two_pow
    rcases Nat.le_total (acc.length + acc.length) m.length with h' | h'
    · rw [Nat.min_eq_right h']
      congr 1
      ring
    · rw [Nat.min_eq_left h']
      have e1 : m.length ≤ 2 ^ l.length * m.length := Nat.le_mul_of_pos_left _ h1
      have e2 : m.length ≤ 2 ^ l.length * 2 * acc.length := by nlinarith
      rw [Nat.min_eq_right e1, Nat.min_eq_right e2]

private theorem capStep_size (pre acc m : Unary) :
    esize (pre.foldl (fun s a => capStep (s, a)) (acc, m)) ≤
      max (esize acc) (esize m) + esize m + 1 := by
  induction pre generalizing acc with
  | nil => simp only [List.foldl_nil, esize_prod]; omega
  | cons x pre ih =>
    rw [List.foldl_cons, capStep_apply]
    refine (ih _).trans ?_
    have h : esize ((acc ++ acc).take m.length) ≤ esize m := by
      rw [LowDegree.DegreeArithmetic.esize_unary_list, LowDegree.DegreeArithmetic.esize_unary_list,
        List.length_take]
      omega
    omega

theorem capStep_bounded : FoldBounded capStep (2 * X + 1) := by
  rintro l ⟨acc, m⟩ pre xs hl
  refine (capStep_size pre acc m).trans ?_
  simp only [esize_prod, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  omega

/-- `min(2^k, m)` in unary, on `(k, m)`: never more than `m`, so polynomial in the input. -/
noncomputable def pow2CapF : PolyTimeFun (Unary × Unary) Unary :=
  congr (fst.comp ((foldl capStep (2 * X + 1) capStep_bounded).comp
      (fst.pair ((take.comp ((const [()]).pair snd)).pair snd))))
    (fun p => unary (min (2 ^ p.1.length) p.2.length)) (by
      rintro ⟨k, m⟩
      simp only [comp_apply, fst_apply, foldl_apply, pair_apply, take_apply, const_apply,
        snd_apply]
      rw [foldl_capStep k (by simp)]
      simp only [List.length_take, List.length_singleton]
      rcases Nat.eq_zero_or_pos m.length with h | h
      · rw [h]; simp
      · rw [Nat.min_eq_right (by omega : 1 ≤ m.length), mul_one])

@[simp] theorem pow2CapF_apply (k m : Unary) :
    pow2CapF (k, m) = unary (min (2 ^ k.length) m.length) := rfl

/-- The number of indices of the table, `tableSize`, in unary. -/
noncomputable def tableSizeF : PolyTimeFun (Unary × Unary) Unary :=
  congr (mulUnaryProg.comp (fst.pair (mulUnaryProg.comp (fst.pair (mulUnaryProg.comp (snd.pair
      (mulUnaryProg.comp (snd.pair (mulUnaryProg.comp (snd.pair (const (unary 64))))))))))))
    (fun p => unary (tableSize p.1.length p.2.length)) (by
      rintro ⟨N, D⟩
      simp [tableSize])

@[simp] theorem tableSizeF_apply (N D : Unary) :
    tableSizeF (N, D) = unary (tableSize N.length D.length) := rfl

/-! ## The check -/

/-- The input of the check: the output of the processor, the four lengths (`(n, y, true)`
first) and the decider's input `(n, x, y, a, b)`, as the canonical decider stacks them. -/
abbrev FIn : Type := Data × Data × Data × Data × Data × DIn

/-- The program of the check, at the parameter program `prm` of the index. -/
noncomputable def lstarRaw (prm : PolyTimeFun ℕ (Unary × Unary)) : PolyTimeFun FIn Bool :=
  let i : PolyTimeFun FIn DIn := snd.comp (snd.comp (snd.comp (snd.comp snd)))
  let n : PolyTimeFun FIn ℕ := fst.comp i
  let a : PolyTimeFun FIn BitStr := fst.comp (snd.comp (snd.comp (snd.comp i)))
  let b : PolyTimeFun FIn BitStr := snd.comp (snd.comp (snd.comp (snd.comp i)))
  let cs : PolyTimeFun FIn (List BitStr) := bitsListF.comp fst
  let lLy : PolyTimeFun FIn Unary := lenUnaryF.comp (fst.comp snd)
  let lRy : PolyTimeFun FIn Unary := lenUnaryF.comp (fst.comp (snd.comp snd))
  let lLx : PolyTimeFun FIn Unary := lenUnaryF.comp (fst.comp (snd.comp (snd.comp snd)))
  let lRx : PolyTimeFun FIn Unary := lenUnaryF.comp (fst.comp (snd.comp (snd.comp (snd.comp snd))))
  let ℓ : PolyTimeFun FIn Unary := fst.comp (prm.comp n)
  let dm : PolyTimeFun FIn Unary := snd.comp (prm.comp n)
  let bU : PolyTimeFun FIn Unary := length.comp b
  let O : PolyTimeFun FIn BitStr := drop.comp (a.pair bU)
  let Dc : PolyTimeFun FIn Unary := pow2CapF.comp (dm.pair (cons (const ()) (length.comp O)))
  let N2 : PolyTimeFun FIn Unary := append.comp (bU.pair bU)
  let le : PolyTimeFun FIn Unary → PolyTimeFun FIn Bool := fun u => leUnaryProg.comp (u.pair bU)
  let c0 : PolyTimeFun FIn Bool :=
    eqUnaryProg.comp ((pow2CapF.comp (ℓ.pair (cons (const ()) bU))).pair bU)
  let c1 : PolyTimeFun FIn Bool :=
    eqUnaryProg.comp ((length.comp O).pair (tableSizeF.comp (bU.pair Dc)))
  let c2 : PolyTimeFun FIn Bool :=
    andF.comp ((le lRx).pair (andF.comp ((le lLx).pair (andF.comp ((le lRy).pair (le lLy))))))
  let c3 : PolyTimeFun FIn Bool := leUnaryProg.comp ((append.comp
    ((mulUnaryProg.comp ((length.comp cs).pair N2)).pair N2)).pair Dc)
  let rows : PolyTimeFun FIn (List (List Unary × Bool)) := rowsUF.comp (cs.pair (lRx.pair (lLx.pair
    (lRy.pair (lLy.pair (bU.pair ((take.comp (a.pair lRx)).pair (take.comp (b.pair lRy)))))))))
  let c4 : PolyTimeFun FIn Bool := SAT.ArrayProg.eqBits.comp (O.pair
    (tableF.comp (bU.pair (Dc.pair (triangleUF.comp (rows.pair N2))))))
  andF.comp (c0.pair (andF.comp (c1.pair (andF.comp (c2.pair (andF.comp (c3.pair c4)))))))

theorem lstarRaw_apply (prm : PolyTimeFun ℕ (Unary × Unary)) (r₀ r₁ r₂ r₃ r₄ : Data) (i : DIn) :
    lstarRaw prm (r₀, r₁, r₂, r₃, r₄, i) =
      lstarCheck (prm i.1).1.length (prm i.1).2.length (Data.spineList r₄).length
        (Data.spineList r₃).length (Data.spineList r₂).length (Data.spineList r₁).length
        (Data.bitsListD r₀) i.2.2.2.1 i.2.2.2.2 := by
  obtain ⟨n, x, y, a, b⟩ := i
  simp only [lstarRaw, comp_apply, pair_apply, fst_apply, snd_apply, andF_apply,
    LowDegree.DegreeArithmetic.eqUnaryProg_apply, LowDegree.DegreeArithmetic.leUnaryProg_apply,
    LowDegree.DegreeArithmetic.mulUnaryProg_apply, pow2CapF_apply, tableSizeF_apply,
    length_apply, cons_apply, const_apply, append_apply, drop_apply, take_apply, bitsListF_apply,
    lenUnaryF_apply, rowsUF_apply, triangleUF_apply, tableF_apply, SAT.ArrayProg.eqBits_apply,
    length_unary, List.length_cons, List.length_append, lstarCheck]
  have hT : ∀ (N D : ℕ) (rows : List (List Unary × Bool)),
      tableU (unary N) (unary D) (triangleU (unary (N + N)) rows) =
        indTable N D (triangle (N + N) (rows.map toEqn)) := by
    intro N D rows
    rw [tableU_eq N D (triangleU_wf _ _), map_toTri_triangleU, length_unary]
  rw [show (unary b.length ++ unary b.length) = unary (b.length + b.length) from
      unary_eq_of_length (by simp), hT, map_toEqn_rowsU]
  simp only [lsTable, Bool.decide_and, Bool.and_assoc]
  congr

/-- **The check of the output indicator**, as a program: it decides `LstarOK` at the table size
`2^ℓ` and the copy size `2^◇` that `prm` gives the index (`lstarFinal_apply`). -/
noncomputable def lstarFinal (prm : PolyTimeFun ℕ (Unary × Unary)) : PolyTimeFun FIn Bool :=
  congr (lstarRaw prm) (fun z => lstarCheck (prm z.2.2.2.2.2.1).1.length
      (prm z.2.2.2.2.2.1).2.length (Data.spineList z.2.2.2.2.1).length
      (Data.spineList z.2.2.2.1).length (Data.spineList z.2.2.1).length
      (Data.spineList z.2.1).length (Data.bitsListD z.1) z.2.2.2.2.2.2.2.2.1
      z.2.2.2.2.2.2.2.2.2) (by
    rintro ⟨r₀, r₁, r₂, r₃, r₄, i⟩
    exact lstarRaw_apply prm r₀ r₁ r₂ r₃ r₄ i)

theorem lstarFinal_apply (prm : PolyTimeFun ℕ (Unary × Unary)) (r₀ r₁ r₂ r₃ r₄ : Data) (i : DIn) :
    lstarFinal prm (r₀, r₁, r₂, r₃, r₄, i) =
      decide (LstarOK (2 ^ (prm i.1).1.length) (2 ^ (prm i.1).2.length)
        (Data.spineList r₄).length (Data.spineList r₃).length (Data.spineList r₂).length
        (Data.spineList r₁).length (Data.bitsListD r₀) i.2.2.2.1 i.2.2.2.2) := by
  rw [lstarFinal, congr_apply, lstarCheck_eq]

/-! ## The output indicator -/

/-- After the fourth run of the answer-length calculator: run the processor, then check. -/
noncomputable def lstarTail₄ (prm : PolyTimeFun ℕ (Unary × Unary)) (P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₅.code P) (lstarFinal prm).code

/-- After the third run. -/
noncomputable def lstarTail₃ (prm : PolyTimeFun ℕ (Unary × Unary)) (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₄.code L) (lstarTail₄ prm P)

/-- After the second run. -/
noncomputable def lstarTail₂ (prm : PolyTimeFun ℕ (Unary × Unary)) (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₃.code L) (lstarTail₃ prm L P)

/-- After the first run. -/
noncomputable def lstarTail₁ (prm : PolyTimeFun ℕ (Unary × Unary)) (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₂.code L) (lstarTail₂ prm L P)

/-- **The output indicator** `L*` of a tailored verifier with answer-length calculator `L` and
processor `P` (Definition defn:decider-read), at the parameter program `prm`: on
`encode (n, x, y, a, b)`, the four runs of `L` and the run of `P` of the canonical decider, then
the check. -/
noncomputable def lstarProg (prm : PolyTimeFun ℕ (Unary × Unary)) (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₁.code L) (lstarTail₁ prm L P)

section WellScoped

variable (prm : PolyTimeFun ℕ (Unary × Unary)) {L P : Prog} (hL : L.WellScoped 1)
  (hP : P.WellScoped 1)
include hP

theorem lstarTail₄_wellScoped : (lstarTail₄ prm P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₅.closed hP) (lstarFinal prm).closed

include hL

theorem lstarTail₃_wellScoped : (lstarTail₃ prm L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₄.closed hL) (lstarTail₄_wellScoped prm hP)

theorem lstarTail₂_wellScoped : (lstarTail₂ prm L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₃.closed hL) (lstarTail₃_wellScoped prm hL hP)

theorem lstarTail₁_wellScoped : (lstarTail₁ prm L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₂.closed hL) (lstarTail₂_wellScoped prm hL hP)

theorem lstarProg_wellScoped : (lstarProg prm L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₁.closed hL) (lstarTail₁_wellScoped prm hL hP)

end WellScoped

/-- **The output indicator accepts exactly when the five runs halt and the check passes**. -/
theorem lstarProg_accepts (prm : PolyTimeFun ℕ (Unary × Unary)) {L P : Prog}
    (hL : L.WellScoped 1) (hP : P.WellScoped 1) (i : DIn) :
    (∃ t, (lstarProg prm L P).Runs (encode i) (encode true) t) ↔
      ∃ r₁ r₂ r₃ r₄ r₀ : Data,
        (∃ t, L.Runs (encode (i.1, i.2.1, false)) r₁ t) ∧
        (∃ t, L.Runs (encode (i.1, i.2.1, true)) r₂ t) ∧
        (∃ t, L.Runs (encode (i.1, i.2.2.1, false)) r₃ t) ∧
        (∃ t, L.Runs (encode (i.1, i.2.2.1, true)) r₄ t) ∧
        (∃ t, P.Runs (encode (i.1, i.2.1, i.2.2.1, i.2.2.2.1.take (Data.spineList r₁).length,
          i.2.2.2.2.take (Data.spineList r₃).length)) r₀ t) ∧
        LstarOK (2 ^ (prm i.1).1.length) (2 ^ (prm i.1).2.length) (Data.spineList r₁).length
          (Data.spineList r₂).length (Data.spineList r₃).length (Data.spineList r₄).length
          (Data.bitsListD r₀) i.2.2.2.1 i.2.2.2.2 := by
  have e₁ : ∀ (s : DIn) (out : Data), (∃ t, (lstarProg prm L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₁ s)) r t) ∧
        ∃ t, (lstarTail₁ prm L P).Runs (encode ((r, s) : Data × DIn)) out t :=
    pushSeq_iff canonIn₁ hL (lstarTail₁_wellScoped prm hL hP)
  have e₂ : ∀ (s : Data × DIn) (out : Data),
      (∃ t, (lstarTail₁ prm L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₂ s)) r t) ∧
        ∃ t, (lstarTail₂ prm L P).Runs (encode ((r, s) : Data × Data × DIn)) out t :=
    pushSeq_iff canonIn₂ hL (lstarTail₂_wellScoped prm hL hP)
  have e₃ : ∀ (s : Data × Data × DIn) (out : Data),
      (∃ t, (lstarTail₂ prm L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₃ s)) r t) ∧
        ∃ t, (lstarTail₃ prm L P).Runs (encode ((r, s) : Data × Data × Data × DIn)) out t :=
    pushSeq_iff canonIn₃ hL (lstarTail₃_wellScoped prm hL hP)
  have e₄ : ∀ (s : Data × Data × Data × DIn) (out : Data),
      (∃ t, (lstarTail₃ prm L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₄ s)) r t) ∧
        ∃ t, (lstarTail₄ prm P).Runs (encode ((r, s) : Data × Data × Data × Data × DIn)) out t :=
    pushSeq_iff canonIn₄ hL (lstarTail₄_wellScoped prm hP)
  have e₅ : ∀ (s : Data × Data × Data × Data × DIn) (out : Data),
      (∃ t, (lstarTail₄ prm P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, P.Runs (encode (canonIn₅ s)) r t) ∧
        ∃ t, (lstarFinal prm).code.Runs (encode ((r, s) : FIn)) out t :=
    pushSeq_iff canonIn₅ hP (lstarFinal prm).closed
  simp only [e₁, e₂, e₃, e₄, e₅, runs_true_iff, canonIn₁_apply, canonIn₂_apply, canonIn₃_apply,
    canonIn₄_apply, canonIn₅_apply, lstarFinal_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨r₁, h₁, r₂, h₂, r₃, h₃, r₄, h₄, r₀, h₅, h⟩
    exact ⟨r₁, r₂, r₃, r₄, r₀, h₁, h₂, h₃, h₄, h₅, h⟩
  · rintro ⟨r₁, r₂, r₃, r₄, r₀, h₁, h₂, h₃, h₄, h₅, h⟩
    exact ⟨r₁, h₁, r₂, h₂, r₃, h₃, r₄, h₄, r₀, h₅, h⟩

/-- **The output indicator of a tailored verifier**, at the parameter program `prm`, as a decider
on `(n, x, y, a, b)`. -/
noncomputable def lstar (prm : PolyTimeFun ℕ (Unary × Unary)) {ℓ : ℕ} (V : TailoredVerifier ℓ) :
    Decider :=
  ⟨lstarProg prm V.len.prog V.lp.prog, lstarProg_wellScoped prm V.len.closed V.lp.closed⟩

/-- **What the output indicator accepts** (claim:properties_of_L*): `(n, x, y, a, b)` such that
the answer-length calculator gives the four lengths, the processor gives the constraints `cs` on
the readable answers cut at the readable lengths, and the check passes at the parameters of the
index. -/
theorem lstar_accepts_iff (prm : PolyTimeFun ℕ (Unary × Unary)) {ℓ : ℕ} (V : TailoredVerifier ℓ)
    (n : ℕ) (x y a b : BitStr) :
    (lstar prm V).Accepts n x y a b ↔
      ∃ lRx lLx lRy lLy : ℕ, ∃ cs : List BitStr, LenIs V.len n x false lRx ∧
        LenIs V.len n x true lLx ∧ LenIs V.len n y false lRy ∧ LenIs V.len n y true lLy ∧
        LpIs V.lp n x y (a.take lRx) (b.take lRy) cs ∧
        LstarOK (2 ^ (prm n).1.length) (2 ^ (prm n).2.length) lRx lLx lRy lLy cs a b := by
  unfold Decider.Accepts lstar
  rw [lstarProg_accepts prm V.len.closed V.lp.closed (n, x, y, a, b)]
  constructor
  · rintro ⟨r₁, r₂, r₃, r₄, r₀, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨t₃, h₃⟩, ⟨t₄, h₄⟩, ⟨t₅, h₅⟩, h⟩
    exact ⟨_, _, _, _, _, ⟨t₁, r₁, h₁, rfl⟩, ⟨t₂, r₂, h₂, rfl⟩, ⟨t₃, r₃, h₃, rfl⟩,
      ⟨t₄, r₄, h₄, rfl⟩, ⟨t₅, r₀, h₅, rfl⟩, h⟩
  · rintro ⟨_, _, _, _, _, ⟨t₁, r₁, h₁, rfl⟩, ⟨t₂, r₂, h₂, rfl⟩, ⟨t₃, r₃, h₃, rfl⟩,
      ⟨t₄, r₄, h₄, rfl⟩, ⟨t₅, r₀, h₅, rfl⟩, h⟩
    exact ⟨r₁, r₂, r₃, r₄, r₀, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨t₃, h₃⟩, ⟨t₄, h₄⟩, ⟨t₅, h₅⟩, h⟩

end MIPRE.Tailored.AnsRed

end
