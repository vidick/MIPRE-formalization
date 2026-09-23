/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Stages

/-!
# Placing and slicing, on lists

Piece AR-3d of `planning/answer-reduction.md`: the list operations a program uses for the
vector operations of `MIPRE/Background/AnswerReduction/Stages` — `placeL` for `placeV` and
`sliceL` for `sliceV` — and their agreement on the lists of a vector's entries
(`ofFn_placeV`, `ofFn_sliceV`, `ofFn_single`).
-/

namespace MIPRE.AnswerReduction.Pcp

variable {α : Type*}

/-- Replace the run of `l` starting at `o` by `w`, and everything else by `fill`. -/
def placeL (fill : α) (o : ℕ) (w l : List α) : List α :=
  (l.take o).map (fun _ => fill) ++ w ++ (l.drop (o + w.length)).map (fun _ => fill)

/-- The run of `l` of length `sz` starting at `o`. -/
def sliceL (o sz : ℕ) (l : List α) : List α := (l.drop o).take sz

theorem length_placeL (fill : α) (o : ℕ) (w l : List α) (h : o + w.length ≤ l.length) :
    (placeL fill o w l).length = l.length := by
  simp only [placeL, List.length_append, List.length_map, List.length_take, List.length_drop]
  omega

variable {F : Type*} [Zero F]

/-- **Placing a vector** is placing its list of entries. -/
theorem ofFn_placeV (g : F → α) {N sz : ℕ} (o : ℕ) (h : o + sz ≤ N) (w : Fin sz → F)
    (l : List α) (hl : l.length = N) :
    List.ofFn (fun r : Fin N => g (placeV o w r)) =
      placeL (g 0) o (List.ofFn fun j => g (w j)) l := by
  subst hl
  apply List.ext_getElem
  · rw [length_placeL _ _ _ _ (by simp; omega)]
    simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, placeV]
    simp only [placeL, List.getElem_append, List.length_append, List.length_map, List.length_take,
      List.length_ofFn, List.getElem_map, List.getElem_ofFn]
    simp only [List.length_ofFn] at h1
    have ho : min o l.length = o := min_eq_left (by omega)
    simp only [ho]
    by_cases ha : o ≤ i ∧ i < o + sz
    · rw [dif_pos ha, dif_pos (by omega), dif_neg (by omega)]
    · rw [dif_neg ha]
      by_cases hb : i < o + sz
      · rw [dif_pos hb, dif_pos (by omega)]
      · rw [dif_neg hb]

omit [Zero F] in
/-- **Slicing a vector** is slicing its list of entries. -/
theorem ofFn_sliceV (g : F → α) {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → F) :
    List.ofFn (fun j => g (sliceV o sz h v j)) = sliceL o sz (List.ofFn fun r => g (v r)) := by
  apply List.ext_getElem
  · simp [sliceL]; omega
  · intro i h1 h2
    simp [sliceL, sliceV]

/-- The seed run of a single seed. -/
theorem ofFn_single (g : F → α) (c : Fin 6) (a : F) (l : List α)
    (hl : l.length = 6) :
    List.ofFn (fun c' : Fin 6 => g ((Pi.single c a : Fin 6 → F) c')) = placeL (g 0) c [g a] l := by
  have : (Pi.single c a : Fin 6 → F) = placeV (N := 6) (sz := 1) c (fun _ => a) := by
    funext c'
    simp only [Pi.single_apply, placeV]
    by_cases hc : c' = c
    · subst hc; simp
    · rw [if_neg hc, dif_neg]
      intro h'
      exact hc (Fin.ext (by omega))
  rw [this, ofFn_placeV g c (by omega) _ l hl]
  rfl

theorem ofFn_zero (g : F → α) {N : ℕ} (l : List α) (hl : l.length = N) :
    List.ofFn (fun _ : Fin N => g 0) = l.map (fun _ => g 0) := by
  subst hl
  apply List.ext_getElem <;> simp

end MIPRE.AnswerReduction.Pcp
