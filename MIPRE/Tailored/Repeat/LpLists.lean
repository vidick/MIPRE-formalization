/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.Lists

@[expose] public section

/-!
# The padding of the repeated linear-constraints processor, in polynomial time

The processor of the repeated tailored verifier (issue #280) pads each coordinate's constraints
to all the variables (`TailoredGame.padCons`). The padding of a constraint is determined by
twelve lengths — before, at and after the coordinate, for the readable and the linear variables
of each question — which the program holds in unary:

* `padWithL p c`, the padding of `c` by the twelve lengths `p`, and `padWithF`;
* `triples L`, for every position `i` of a list of lengths, the sum of the lengths before it, its
  own and the sum of those after it, and `triplesF`;
* `padData`, the twelve lengths of every coordinate from the four lists of lengths.
-/

namespace MIPRE.Tailored.RepProg

open Cost Cost.PolyTimeFun Polynomial

/-! ## The padding -/

/-- The padding of `c` by twelve lengths `p`: readable before/at/after for the first question,
linear before/at/after, then the same for the second question. -/
def padWithL (p : List Unary) (c : BitStr) : BitStr :=
  List.replicate (p.getD 0 []).length false ++ c.take (p.getD 1 []).length ++
    List.replicate (p.getD 2 []).length false ++ List.replicate (p.getD 3 []).length false ++
    (c.drop (p.getD 1 []).length).take (p.getD 4 []).length ++
    List.replicate (p.getD 5 []).length false ++ List.replicate (p.getD 6 []).length false ++
    (c.drop ((p.getD 1 []).length + (p.getD 4 []).length)).take (p.getD 7 []).length ++
    List.replicate (p.getD 8 []).length false ++ List.replicate (p.getD 9 []).length false ++
    (c.drop ((p.getD 1 []).length + (p.getD 4 []).length + (p.getD 7 []).length)).take
      (p.getD 10 []).length ++
    List.replicate (p.getD 11 []).length false ++
    c.drop ((p.getD 1 []).length + (p.getD 4 []).length +
      ((p.getD 7 []).length + (p.getD 10 []).length))

section Pieces

variable {ι : Type} [SizedEncoding ι]

/-- Concatenation of two computed lists. -/
noncomputable def appF {α : Type} [SizedEncoding α] (F G : PolyTimeFun ι (List α)) :
    PolyTimeFun ι (List α) :=
  append.comp (F.pair G)

@[simp] theorem appF_apply {α : Type} [SizedEncoding α] (F G : PolyTimeFun ι (List α)) (a : ι) :
    appF F G a = F a ++ G a := rfl

end Pieces

/-- The `j`-th length. -/
noncomputable def lenAt (j : ℕ) : PolyTimeFun (BitStr × List Unary) Unary := (nthD [] j).comp snd

@[simp] theorem lenAt_apply (j : ℕ) (q : BitStr × List Unary) : lenAt j q = q.2.getD j [] := by
  simp [lenAt]

/-- `j` zeros, the `j`-th length. -/
noncomputable def zerosAt (j : ℕ) : PolyTimeFun (BitStr × List Unary) BitStr :=
  replicate.comp ((lenAt j).pair (const false))

@[simp] theorem zerosAt_apply (j : ℕ) (q : BitStr × List Unary) :
    zerosAt j q = List.replicate (q.2.getD j []).length false := by
  simp [zerosAt]

/-- The constraint without its first `u` coefficients, kept to its next `v`. -/
noncomputable def sliceF (u v : PolyTimeFun (BitStr × List Unary) Unary) :
    PolyTimeFun (BitStr × List Unary) BitStr :=
  take.comp ((drop.comp (fst.pair u)).pair v)

@[simp] theorem sliceF_apply (u v : PolyTimeFun (BitStr × List Unary) Unary)
    (q : BitStr × List Unary) : sliceF u v q = (q.1.drop (u q).length).take (v q).length := by
  simp [sliceF]

/-- **The padding, in polynomial time**, on `(c, p)`. -/
noncomputable def padWithF : PolyTimeFun (BitStr × List Unary) BitStr :=
  congr
    (appF (appF (appF (appF (appF (appF (appF (appF (appF (appF (appF (appF
      (zerosAt 0) (sliceF (const []) (lenAt 1))) (zerosAt 2)) (zerosAt 3))
      (sliceF (lenAt 1) (lenAt 4))) (zerosAt 5)) (zerosAt 6))
      (sliceF (appF (lenAt 1) (lenAt 4)) (lenAt 7))) (zerosAt 8)) (zerosAt 9))
      (sliceF (appF (appF (lenAt 1) (lenAt 4)) (lenAt 7)) (lenAt 10))) (zerosAt 11))
      (drop.comp (fst.pair (appF (appF (lenAt 1) (lenAt 4)) (appF (lenAt 7) (lenAt 10))))))
    (fun q => padWithL q.2 q.1) (by
      rintro ⟨c, p⟩
      simp [padWithL, Nat.add_assoc])

@[simp] theorem padWithF_apply (c : BitStr) (p : List Unary) : padWithF (c, p) = padWithL p c :=
  congr_apply _ _ _ _

/-! ## Before, at and after -/

/-- The step of the scan: move the head of the remaining lengths onto the accumulated sum. -/
noncomputable def scanStepF : PolyTimeFun (Unary × List Unary) (Unary × List Unary) :=
  (append.comp (fst.pair ((headD []).comp snd))).pair (tail.comp snd)

@[simp] theorem scanStepF_apply (q : Unary × List Unary) :
    scanStepF q = (q.1 ++ q.2.headD [], q.2.tail) := by
  simp [scanStepF]

theorem iterate_scanStepF (L : List Unary) (acc : Unary) (i : ℕ) :
    (scanStepF : Unary × List Unary → Unary × List Unary)^[i] (acc, L) =
      (acc ++ (L.take i).flatten, L.drop i) := by
  induction i generalizing acc L with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, scanStepF_apply, ih]
    cases L with
    | nil => simp
    | cons u L => simp [List.take_succ_cons, List.drop_succ_cons, List.append_assoc]

theorem esize_flatten_unary_le (L : List Unary) : esize L.flatten ≤ esize L := by
  induction L with
  | nil => simp
  | cons u L ih =>
    rw [List.flatten_cons, esize_list_cons]
    have := esize_list_append u L.flatten
    omega

theorem esize_scan_le (L : List Unary) (acc : Unary) (i : ℕ) :
    esize (acc ++ (L.take i).flatten, L.drop i) ≤ 2 * esize (acc, L) := by
  have h1 := esize_list_append acc (L.take i).flatten
  have h2 := esize_flatten_unary_le (L.take i)
  have h3 := esize_take_le L i
  have h4 := esize_drop_le L i
  simp only [esize_prod] at *
  omega

/-- The sum before, the length at and the sum after the position of a scan state. -/
def tripleOut (q : Unary × List Unary) : List Unary := [q.1, q.2.headD [], q.2.tail.flatten]

noncomputable def tripleOutF : PolyTimeFun (Unary × List Unary) (List Unary) :=
  congr (cons fst (cons ((headD []).comp snd) (cons (flattenF.comp (tail.comp snd)) (const []))))
    tripleOut (by rintro ⟨a, L⟩; simp [tripleOut])

/-- **Before, at and after** every position of a list of lengths. -/
def triples (L : List Unary) : List (List Unary) :=
  List.ofFn fun i : Fin L.length => [(L.take i).flatten, L.getD i [], (L.drop (i + 1)).flatten]

noncomputable def triplesF : PolyTimeFun (List Unary) (List (List Unary)) :=
  congr ((map tripleOutF).comp ((recordIteratesProg scanStepF (C 2 * X) (by
      rintro i ⟨acc, L⟩
      rw [iterate_scanStepF]
      simpa using esize_scan_le L acc i)).comp (length.pair ((const []).pair (PolyTimeFun.id _)))))
    triples (by
      intro L
      simp only [comp_apply, pair_apply, length_apply, const_apply, id_apply,
        recordIteratesProg_apply, map_apply, recordIterates, List.map_ofFn, triples, length_unary]
      congr 1
      funext i
      simp only [Function.comp_apply, iterate_scanStepF, List.nil_append]
      simp [tripleOutF, tripleOut, List.tail_drop, List.headD_eq_head?_getD, List.head?_drop,
        List.getD_eq_getElem?_getD])

@[simp] theorem triplesF_apply (L : List Unary) : triplesF L = triples L := congr_apply _ _ _ _

/-- The twelve lengths of every coordinate, from the readable and linear lengths of the two
questions' coordinates. -/
def padData (LRx LLx LRy LLy : List Unary) : List (List Unary) :=
  (((triples LRx).zip (triples LLx)).zip ((triples LRy).zip (triples LLy))).map
    fun q => q.1.1 ++ q.1.2 ++ (q.2.1 ++ q.2.2)

end MIPRE.Tailored.RepProg

end
