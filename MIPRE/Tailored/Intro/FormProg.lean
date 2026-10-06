/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.AuxCons
public import MIPRE.Tailored.Repeat.Lists

@[expose] public section

/-!
# The constraint forms of the introspection processor, in polynomial time

The linear-constraints processor of the tailored introspection verifier writes its constraints
through a handful of forms (`Forms.lean`, `RegCons.lean`, `SourceCons.lean`, `AuxCons.lean`).
This file builds each of them as a `Cost.PolyTimeFun` from already computed data: lengths and
offsets in unary, so that the output, of about `Q` constraints of about `2Q + 2R` bits, is
polynomial in the size of the input; readable conditions as Booleans; coordinate sets
`S ⊆ Fin s` as their bit masks `maskOf S`; vectors of `𝔽₂^s` as their bits `CL.toBits`.

* `placeOf`, `rejectF`: the vector `place n off w` and the rejecting constraint;
* `unitsF`: the unit vectors `units m`, as the orbit of a shift;
* `pairFormF`: the form `place la oa e ++ place lb ob e ++ [false]`;
* `eqConsF`, `guardConsF`, `projEqConsF`, `dualConsF`: `eqCons`, `guardCons`, `projEqCons`,
  `dualCons`;
* `reindexF`, `swapConF`, `swapConsF`: `reindex`, `swapCon` and its map over a list.

Each comes with its `_apply` lemma on arbitrary inputs, and the `_spec` lemma stating that on
the encoding of the semantic data it outputs the semantic list.
-/

namespace MIPRE.Tailored.Intro

open Cost Cost.PolyTimeFun Polynomial CL

/-! ## Pieces on a generic input -/

section Pieces

variable {ι : Type} [SizedEncoding ι]

/-- Concatenation of two computed lists. -/
noncomputable def catF {α : Type} [SizedEncoding α] (F G : PolyTimeFun ι (List α)) :
    PolyTimeFun ι (List α) :=
  append.comp (F.pair G)

@[simp] theorem catF_apply {α : Type} [SizedEncoding α] (F G : PolyTimeFun ι (List α)) (a : ι) :
    catF F G a = F a ++ G a := rfl

/-- `u` zeros. -/
noncomputable def zerosOf (u : PolyTimeFun ι Unary) : PolyTimeFun ι BitStr :=
  replicate.comp (u.pair (const false))

@[simp] theorem zerosOf_apply (u : PolyTimeFun ι Unary) (a : ι) :
    zerosOf u a = List.replicate (u a).length false := rfl

/-- Truncated subtraction of unary numbers. -/
noncomputable def subOf (u v : PolyTimeFun ι Unary) : PolyTimeFun ι Unary := drop.comp (u.pair v)

@[simp] theorem subOf_apply (u v : PolyTimeFun ι Unary) (a : ι) :
    subOf u v a = (u a).drop (v a).length := rfl

/-- The length of a computed list, in unary. -/
noncomputable def lenOf {α : Type} [SizedEncoding α] (l : PolyTimeFun ι (List α)) :
    PolyTimeFun ι Unary :=
  length.comp l

@[simp] theorem lenOf_apply {α : Type} [SizedEncoding α] (l : PolyTimeFun ι (List α)) (a : ι) :
    lenOf l a = unary (l a).length := rfl

/-- A prefix of a computed bit string. -/
noncomputable def takeOf (l : PolyTimeFun ι BitStr) (u : PolyTimeFun ι Unary) :
    PolyTimeFun ι BitStr :=
  take.comp (l.pair u)

@[simp] theorem takeOf_apply (l : PolyTimeFun ι BitStr) (u : PolyTimeFun ι Unary) (a : ι) :
    takeOf l u a = (l a).take (u a).length := rfl

/-- A suffix of a computed bit string. -/
noncomputable def dropOf (l : PolyTimeFun ι BitStr) (u : PolyTimeFun ι Unary) :
    PolyTimeFun ι BitStr :=
  drop.comp (l.pair u)

@[simp] theorem dropOf_apply (l : PolyTimeFun ι BitStr) (u : PolyTimeFun ι Unary) (a : ι) :
    dropOf l u a = (l a).drop (u a).length := rfl

/-- **The placed vector** `place n off w`. -/
noncomputable def placeOf (n off : PolyTimeFun ι Unary) (w : PolyTimeFun ι BitStr) :
    PolyTimeFun ι BitStr :=
  catF (catF (zerosOf off) w) (zerosOf (subOf (subOf n off) (lenOf w)))

@[simp] theorem placeOf_apply (n off : PolyTimeFun ι Unary) (w : PolyTimeFun ι BitStr) (a : ι) :
    placeOf n off w a = place (n a).length (off a).length (w a) := by
  simp [placeOf, place, Nat.sub_sub]

/-- Whether a list is empty. -/
noncomputable def isNilOf {α : Type} [SizedEncoding α] (l : PolyTimeFun ι (List α)) :
    PolyTimeFun ι Bool :=
  (casesList (const true) (const false)).comp ((const ()).pair l)

@[simp] theorem isNilOf_apply {α : Type} [SizedEncoding α] (l : PolyTimeFun ι (List α))
    (a : ι) : isNilOf l a = (l a).isEmpty := by
  simp only [isNilOf, comp_apply, pair_apply, const_apply]
  cases l a <;> rfl

/-- Conjunction of two computed Booleans. -/
noncomputable def andOf (b c : PolyTimeFun ι Bool) : PolyTimeFun ι Bool := ite b c (const false)

@[simp] theorem andOf_apply (b c : PolyTimeFun ι Bool) (a : ι) : andOf b c a = (b a && c a) := by
  change (if b a then c a else false) = _
  cases b a <;> rfl

/-- Equality of two unary numbers. -/
noncomputable def eqUOf (u v : PolyTimeFun ι Unary) : PolyTimeFun ι Bool :=
  andOf (isNilOf (subOf u v)) (isNilOf (subOf v u))

@[simp] theorem eqUOf_apply (u v : PolyTimeFun ι Unary) (a : ι) :
    eqUOf u v a = decide ((u a).length = (v a).length) := by
  simp only [eqUOf, andOf_apply, isNilOf_apply, subOf_apply]
  by_cases h : (u a).length = (v a).length
  · simp [h]
  · simp only [h, decide_false]
    rcases Nat.lt_or_gt_of_ne h with h' | h' <;> simp [Nat.not_le.2 h', le_of_lt h']

end Pieces

/-! ## Unit vectors -/

/-- The shift: a zero in front, the last bit dropped. -/
def shift (w : BitStr) : BitStr := false :: w.dropLast

/-- The shift in polynomial time. -/
noncomputable def shiftF : PolyTimeFun BitStr BitStr :=
  cons (const false) (takeOf (PolyTimeFun.id _) (length.comp tail))

@[simp] theorem shiftF_apply (w : BitStr) : shiftF w = shift w := by
  simp [shiftF, shift, List.dropLast_eq_take]

theorem length_iterate_shift_le (w : BitStr) :
    ∀ n, (shift^[n] w).length ≤ w.length + 1
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    have := length_iterate_shift_le w n
    simp only [shift, List.length_cons, List.length_dropLast]
    omega

theorem esize_iterate_shift_le (n : ℕ) (w : BitStr) :
    esize ((shiftF : BitStr → BitStr)^[n] w) ≤ (C 4 * X + C 5 : Polynomial ℕ).eval (esize w) := by
  have e : (shiftF : BitStr → BitStr) = shift := funext shiftF_apply
  rw [e]
  have h1 := esize_bitStr_le (shift^[n] w)
  have h2 := length_iterate_shift_le w n
  have h3 := length_le_esize_bitStr w
  simp only [eval_add, eval_mul, eval_C, eval_X]
  omega

theorem unit_eq {m i : ℕ} : unit m i = List.replicate i false ++ [true] ++
    List.replicate (m - i - 1) false := by
  simp [unit, place]

theorem shift_unit {m i : ℕ} (h : i + 1 < m) : shift (unit m i) = unit m (i + 1) := by
  rw [unit_eq, unit_eq, show m - i - 1 = (m - (i + 1) - 1) + 1 by omega, List.replicate_succ',
    ← List.append_assoc, shift, List.dropLast_concat, List.replicate_succ]
  simp

theorem iterate_shift_unit {m : ℕ} : ∀ i, i < m → shift^[i] (unit m 0) = unit m i
  | 0, _ => rfl
  | i + 1, h => by
    rw [Function.iterate_succ_apply', iterate_shift_unit i (by omega), shift_unit h]

/-- The unit vectors of length `m`, in order. -/
def units (m : ℕ) : List BitStr := (List.range m).map (unit m)

/-- **The unit vectors**, as the orbit of the first under the shift. -/
noncomputable def unitsF : PolyTimeFun Unary (List BitStr) :=
  congr ((recordIteratesProg shiftF (C 4 * X + C 5) esize_iterate_shift_le).comp
      ((PolyTimeFun.id _).pair (cons (const true) (zerosOf tail))))
    (fun u => units u.length) (by
      intro u
      simp only [comp_apply, pair_apply, id_apply, recordIteratesProg_apply, recordIterates]
      apply List.ext_getElem (by simp [units])
      intro i h1 h2
      simp only [List.getElem_ofFn, units, List.getElem_map, List.getElem_range]
      have e : (shiftF : BitStr → BitStr) = shift := funext shiftF_apply
      rw [e]
      simp only [List.length_ofFn] at h1
      rw [← iterate_shift_unit i h1, unit_eq]
      simp)

@[simp] theorem unitsF_apply (u : Unary) : unitsF u = units u.length := congr_apply _ _ _ _

theorem unit_eq_ofFn {m i : ℕ} (hi : i < m) :
    unit m i = List.ofFn fun j : Fin m => decide (j.val = i) := by
  rw [unit_eq]
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.getElem_ofFn]
  rcases Nat.lt_trichotomy j i with h | rfl | h
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp; omega
  · rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp
  · rw [List.getElem_append_right (by simp; omega)]
    simp; omega

theorem toBits_single {s : ℕ} (i : Fin s) : CL.toBits (Pi.single i (1 : 𝔽₂)) = unit s i := by
  rw [unit_eq_ofFn i.isLt, CL.toBits]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h, Fin.val_ne_of_ne h]

theorem units_eq_map_finRange (s : ℕ) :
    units s = (List.finRange s).map fun i => CL.toBits (Pi.single i (1 : 𝔽₂)) := by
  apply List.ext_getElem (by simp [units])
  intro i h1 h2
  simp [units, toBits_single]

/-! ## The two-sided form -/

/-- The layout of a two-sided form: the lengths and offsets `((la, oa), (lb, ob))`. -/
abbrev Lay := (Unary × Unary) × (Unary × Unary)

/-- The layout of `(la, oa, lb, ob)`. -/
def lay (la oa lb ob : ℕ) : Lay := ((unary la, unary oa), (unary lb, unary ob))

/-- The constraint `⟨e, a_{oa..}⟩ + ⟨e, b_{ob..}⟩ = 0`. -/
def pairForm (la oa lb ob : ℕ) (e : BitStr) : BitStr := place la oa e ++ place lb ob e ++ [false]

/-- The two-sided form in polynomial time, on `(e, layout)`. -/
noncomputable def pairFormF : PolyTimeFun (BitStr × Lay) BitStr :=
  catF (catF (placeOf (fst.comp (fst.comp snd)) (snd.comp (fst.comp snd)) fst)
    (placeOf (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd)) fst)) (const [false])

@[simp] theorem pairFormF_apply (e : BitStr) (L : Lay) :
    pairFormF (e, L) = pairForm L.1.1.length L.1.2.length L.2.1.length L.2.2.length e := by
  simp [pairFormF, pairForm]

/-! ## Equality of windows -/

theorem eqCons_eq_units (la lb oa ob m : ℕ) :
    eqCons la lb oa ob m = (units m).map (pairForm la oa lb ob) := by
  simp [eqCons, units, pairForm]

/-- **The window equality constraints** `eqCons`, on `(layout, m)`. -/
noncomputable def eqConsF : PolyTimeFun (Lay × Unary) (List BitStr) :=
  (mapWith pairFormF).comp ((unitsF.comp snd).pair fst)

@[simp] theorem eqConsF_apply (L : Lay) (m : Unary) :
    eqConsF (L, m) = eqCons L.1.1.length L.2.1.length L.1.2.length L.2.2.length m.length := by
  simp [eqConsF, eqCons_eq_units]

theorem eqConsF_spec (la lb oa ob m : ℕ) :
    eqConsF (lay la oa lb ob, unary m) = eqCons la lb oa ob m := by
  simp [lay]

/-! ## Readable guards -/

/-- The rejecting constraint `rejectConstraint d`, `d` in unary. -/
noncomputable def rejectF : PolyTimeFun Unary BitStr :=
  catF (zerosOf (PolyTimeFun.id _)) (const [true])

@[simp] theorem rejectF_apply (u : Unary) : rejectF u = rejectConstraint u.length := by
  simp [rejectF, rejectConstraint]

/-- **The readable guard** `guardCons`, on `(b, d)`. -/
noncomputable def guardConsF : PolyTimeFun (Bool × Unary) (List BitStr) :=
  ite fst (const []) (cons (rejectF.comp snd) (const []))

@[simp] theorem guardConsF_apply (b : Bool) (d : Unary) :
    guardConsF (b, d) = guardCons b d.length := by
  cases b <;> simp [guardConsF, guardCons]

theorem guardConsF_spec (b : Bool) (d : ℕ) : guardConsF (b, unary d) = guardCons b d := by
  simp

/-! ## Equality on a coordinate set -/

/-- The bit mask of a coordinate set. -/
def maskOf {s : ℕ} (S : Finset (Fin s)) : BitStr := List.ofFn fun i => decide (i ∈ S)

@[simp] theorem length_maskOf {s : ℕ} (S : Finset (Fin s)) : (maskOf S).length = s := by
  simp [maskOf]

/-- The entries of `l` selected by the mask `m`. -/
def selectL {α : Type} (l : List α) (m : BitStr) : List α :=
  ((l.zip m).map fun p => if p.2 then [p.1] else []).flatten

theorem selectL_map {α β : Type} (f : β → α) (p : β → Bool) :
    ∀ l : List β, selectL (l.map f) (l.map p) = (l.filter p).map f
  | [] => rfl
  | b :: l => by
    have ih := selectL_map f p l
    simp only [selectL] at ih ⊢
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.map_cons, List.flatten_cons, ih,
      List.filter_cons]
    cases p b <;> simp

/-- The selection by a mask in polynomial time, on `(l, m)`. -/
noncomputable def selectF {α : Type} [SizedEncoding α] :
    PolyTimeFun (List α × BitStr) (List α) :=
  RepProg.flattenF.comp ((map (ite snd (cons fst (const [])) (const []))).comp zip)

@[simp] theorem selectF_apply {α : Type} [SizedEncoding α] (l : List α) (m : BitStr) :
    selectF (l, m) = selectL l m := by
  simp only [selectF, comp_apply, zip_apply, map_apply, RepProg.flattenF_apply, selectL]
  congr 1

theorem projEqCons_eq_select {s : ℕ} (la lb oa ob : ℕ) (S : Finset (Fin s)) :
    projEqCons la lb oa ob S = (selectL (units s) (maskOf S)).map (pairForm la oa lb ob) := by
  rw [units_eq_map_finRange, maskOf, List.ofFn_eq_map, selectL_map, projEqCons, List.map_map]
  rfl

/-- **The coordinate-set equality constraints** `projEqCons`, on `(layout, mask)`. -/
noncomputable def projEqConsF : PolyTimeFun (Lay × BitStr) (List BitStr) :=
  (mapWith pairFormF).comp ((selectF.comp ((unitsF.comp (length.comp snd)).pair snd)).pair fst)

@[simp] theorem projEqConsF_apply (L : Lay) (m : BitStr) :
    projEqConsF (L, m) = (selectL (units m.length) m).map
      (pairForm L.1.1.length L.1.2.length L.2.1.length L.2.2.length) := by
  simp [projEqConsF]

theorem projEqConsF_spec {s : ℕ} (la lb oa ob : ℕ) (S : Finset (Fin s)) :
    projEqConsF (lay la oa lb ob, maskOf S) = projEqCons la lb oa ob S := by
  rw [projEqConsF_apply, projEqCons_eq_select, length_maskOf]
  simp [lay]

/-! ## Equality of duals -/

/-- The bits of `g` masked by `m`. -/
def andMask (g m : BitStr) : BitStr := (g.zip m).map fun p => p.1 && p.2

/-- The masking in polynomial time, on `(g, m)`. -/
noncomputable def andMaskF : PolyTimeFun (BitStr × BitStr) BitStr :=
  (map (andOf fst snd)).comp zip

@[simp] theorem andMaskF_apply (g m : BitStr) : andMaskF (g, m) = andMask g m := by
  simp [andMaskF, andMask]

theorem toBits_proj {s : ℕ} (S : Finset (Fin s)) (z : Fin s → 𝔽₂) :
    CL.toBits (proj S z) = andMask (CL.toBits z) (maskOf S) := by
  apply List.ext_getElem (by simp [andMask, CL.toBits, maskOf])
  intro i h1 h2
  simp only [CL.toBits, List.length_ofFn] at h1
  simp only [CL.toBits, andMask, maskOf, List.getElem_ofFn, List.getElem_map, List.getElem_zip,
    proj_apply]
  by_cases h : (⟨i, h1⟩ : Fin s) ∈ S <;> simp [h]

theorem dualCons_eq_map {s : ℕ} (la lb oa ob : ℕ) (S : Finset (Fin s))
    (gens : List (Fin s → 𝔽₂)) :
    dualCons la lb oa ob S gens =
      ((gens.map CL.toBits).map fun g => andMask g (maskOf S)).map (pairForm la oa lb ob) := by
  simp only [dualCons, List.map_map]
  apply List.map_congr_left
  intro z _
  simp [regForm, pairForm, toBits_proj]

/-- **The dual equality constraints** `dualCons`, on `(layout, mask, generators)`. -/
noncomputable def dualConsF : PolyTimeFun (Lay × BitStr × List BitStr) (List BitStr) :=
  (mapWith pairFormF).comp
    (((mapWith andMaskF).comp ((snd.comp snd).pair (fst.comp snd))).pair fst)

@[simp] theorem dualConsF_apply (L : Lay) (m : BitStr) (gs : List BitStr) :
    dualConsF (L, m, gs) = (gs.map fun g => andMask g m).map
      (pairForm L.1.1.length L.1.2.length L.2.1.length L.2.2.length) := by
  simp [dualConsF]

theorem dualConsF_spec {s : ℕ} (la lb oa ob : ℕ) (S : Finset (Fin s))
    (gens : List (Fin s → 𝔽₂)) :
    dualConsF (lay la oa lb ob, maskOf S, gens.map CL.toBits) = dualCons la lb oa ob S gens := by
  rw [dualConsF_apply, dualCons_eq_map]
  simp [lay]

/-! ## Re-indexed input constraints -/

/-- The parameters of a re-indexing: `((Q, R), ((lRa, lLa), (lRb, lLb)), (la, lb))`. -/
abbrev RParams := (Unary × Unary) × ((Unary × Unary) × (Unary × Unary)) × (Unary × Unary)

/-- The parameters of `reindex Q R lRa lLa lRb lLb la lb`. -/
def rparams (Q R lRa lLa lRb lLb la lb : ℕ) : RParams :=
  ((unary Q, unary R), ((unary lRa, unary lLa), (unary lRb, unary lLb)), (unary la, unary lb))

section Reindex

variable {ι : Type} [SizedEncoding ι]

/-- The vector `place2 n o₁ w₁ o₂ w₂`. -/
noncomputable def place2Of (n o₁ : PolyTimeFun ι Unary) (w₁ : PolyTimeFun ι BitStr)
    (o₂ : PolyTimeFun ι Unary) (w₂ : PolyTimeFun ι BitStr) : PolyTimeFun ι BitStr :=
  catF (catF (zerosOf o₁) w₁)
    (placeOf (subOf (subOf n o₁) (lenOf w₁)) (subOf (subOf o₂ o₁) (lenOf w₁)) w₂)

@[simp] theorem place2Of_apply (n o₁ : PolyTimeFun ι Unary) (w₁ : PolyTimeFun ι BitStr)
    (o₂ : PolyTimeFun ι Unary) (w₂ : PolyTimeFun ι BitStr) (a : ι) :
    place2Of n o₁ w₁ o₂ w₂ a =
      place2 (n a).length (o₁ a).length (w₁ a) (o₂ a).length (w₂ a) := by
  simp [place2Of, place2, Nat.sub_sub]

end Reindex

section ReindexProj

/-- The projections of the input `(c, params)` of the re-indexing. -/
noncomputable def rQ : PolyTimeFun (BitStr × RParams) Unary := fst.comp (fst.comp snd)
noncomputable def rR : PolyTimeFun (BitStr × RParams) Unary := snd.comp (fst.comp snd)
noncomputable def rRa : PolyTimeFun (BitStr × RParams) Unary :=
  fst.comp (fst.comp (fst.comp (snd.comp snd)))
noncomputable def rLa : PolyTimeFun (BitStr × RParams) Unary :=
  snd.comp (fst.comp (fst.comp (snd.comp snd)))
noncomputable def rRb : PolyTimeFun (BitStr × RParams) Unary :=
  fst.comp (snd.comp (fst.comp (snd.comp snd)))
noncomputable def rLb : PolyTimeFun (BitStr × RParams) Unary :=
  snd.comp (snd.comp (fst.comp (snd.comp snd)))
noncomputable def rla : PolyTimeFun (BitStr × RParams) Unary := fst.comp (snd.comp (snd.comp snd))
noncomputable def rlb : PolyTimeFun (BitStr × RParams) Unary := snd.comp (snd.comp (snd.comp snd))

end ReindexProj

/-- **The re-indexing** `reindex`, on `(c, params)`. -/
noncomputable def reindexF : PolyTimeFun (BitStr × RParams) BitStr :=
  let s₁ := catF rRa rLa
  let s₂ := catF s₁ rRb
  let s₃ := catF s₂ rLb
  ite (eqUOf (lenOf fst) (catF s₃ (const [()])))
    (catF (catF
      (place2Of rla rQ (takeOf fst rRa) (catF rQ rR) (takeOf (dropOf fst rRa) rLa))
      (place2Of rlb rQ (takeOf (dropOf fst s₁) rRb) (catF rQ rR) (takeOf (dropOf fst s₂) rLb)))
      (cons ((headD false).comp (dropOf fst s₃)) (const [])))
    (rejectF.comp (catF rla rlb))

theorem getD_eq_headD_drop (c : BitStr) (k : ℕ) : c.getD k false = (c.drop k).headD false := by
  simp [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

@[simp] theorem reindexF_apply (c : BitStr) (P : RParams) :
    reindexF (c, P) = reindex P.1.1.length P.1.2.length P.2.1.1.1.length P.2.1.1.2.length
      P.2.1.2.1.length P.2.1.2.2.length P.2.2.1.length P.2.2.2.length c := by
  obtain ⟨⟨Q, R⟩, ⟨⟨lRa, lLa⟩, ⟨lRb, lLb⟩⟩, ⟨la, lb⟩⟩ := P
  simp [reindexF, rQ, rR, rRa, rLa, rRb, rLb, rla, rlb, reindex, Nat.add_assoc]

theorem reindexF_spec (Q R lRa lLa lRb lLb la lb : ℕ) (c : BitStr) :
    reindexF (c, rparams Q R lRa lLa lRb lLb la lb) = reindex Q R lRa lLa lRb lLb la lb c := by
  simp [rparams]

/-! ## The other orientation -/

/-- **The swapped constraint** `swapCon`, on `(c, (la, lb))`. -/
noncomputable def swapConF : PolyTimeFun (BitStr × (Unary × Unary)) BitStr :=
  catF (catF (takeOf (dropOf fst (snd.comp snd)) (fst.comp snd)) (takeOf fst (snd.comp snd)))
    (dropOf fst (catF (snd.comp snd) (fst.comp snd)))

@[simp] theorem swapConF_apply (c : BitStr) (la lb : Unary) :
    swapConF (c, (la, lb)) = swapCon la.length lb.length c := by
  simp [swapConF, swapCon]

/-- **The swapped constraints** of a list, on `(cs, (la, lb))`. -/
noncomputable def swapConsF : PolyTimeFun (List BitStr × (Unary × Unary)) (List BitStr) :=
  mapWith swapConF

@[simp] theorem swapConsF_apply (cs : List BitStr) (la lb : Unary) :
    swapConsF (cs, (la, lb)) = cs.map (swapCon la.length lb.length) := by
  simp [swapConsF]

theorem swapConsF_spec (cs : List BitStr) (la lb : ℕ) :
    swapConsF (cs, (unary la, unary lb)) = cs.map (swapCon la lb) := by
  simp

end MIPRE.Tailored.Intro

end
