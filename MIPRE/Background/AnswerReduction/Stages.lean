/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Layout

/-!
# The queries of a copy of the PCP sampler, run by run

Piece AR-3d of `planning/answer-reduction.md`. A copy of the seeded test in the PCP sampler is a
run `[o, o + sz)` of the concatenated registers with a seed `c` (`regsAt`). This file writes
what its presentation's queries return in the three runs of `MIPRE/Background/AnswerReduction/
Layout` (`ptOf6`, `dirOf6`, `seedsOf`), which is the form a program computes:

* the marginals (`comps_marginal`): the seed on the seed run, the cut-down direction placed at
  `o` on the direction run for a diagonal line, the line's base point placed at `o` on the point
  run;
* the stage maps from a prefix (`comps_map_zero`, `comps_map_one`, `comps_map_two`);
* the factor spaces, run by run (`mem_coordSet_*`, `mem_dirSet_*`, `mem_finalSet_*`).
-/

noncomputable section

namespace MIPRE.AnswerReduction.Pcp

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL

/-! ## Placing and slicing vectors -/

section Vec

variable {F : Type*} [Zero F]

/-- A vector of length `sz` placed at offset `o` of `Fin N`, zero elsewhere. -/
def placeV {N sz : ℕ} (o : ℕ) (w : Fin sz → F) : Fin N → F :=
  fun r => if h : o ≤ r ∧ (r : ℕ) < o + sz then w ⟨r - o, by omega⟩ else 0

/-- The run `[o, o + sz)` of a vector of length `N`. -/
def sliceV {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → F) : Fin sz → F :=
  fun j => v ⟨o + j, by omega⟩

end Vec

variable (P : PcpParams) {F : Type*} [Field F]

/-! ## The runs of the three kinds of vectors a copy writes -/

@[simp] theorem ptOf6_add (x y : Coord P → F) : ptOf6 P (x + y) = ptOf6 P x + ptOf6 P y := rfl
@[simp] theorem dirOf6_add (x y : Coord P → F) : dirOf6 P (x + y) = dirOf6 P x + dirOf6 P y :=
  rfl
@[simp] theorem seedsOf_add (x y : Coord P → F) : seedsOf P (x + y) = seedsOf P x + seedsOf P y :=
  rfl
@[simp] theorem ptOf6_zero : ptOf6 P (0 : Coord P → F) = 0 := rfl
@[simp] theorem dirOf6_zero : dirOf6 P (0 : Coord P → F) = 0 := rfl
@[simp] theorem seedsOf_zero : seedsOf P (0 : Coord P → F) = 0 := rfl

variable (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m')

omit [Field F] in
theorem ptOf_regsAt (x : Coord P → F) :
    (regsAt P o sz c h).ptOf x = sliceV o sz h (ptOf6 P x) := rfl

omit [Field F] in
theorem dirOf_regsAt (x : Coord P → F) :
    (regsAt P o sz c h).dirOf x = sliceV o sz h (dirOf6 P x) := rfl

omit [Field F] in
theorem coord_regsAt (x : Coord P → F) : x (regsAt P o sz c h).coord = seedsOf P x c := rfl

theorem pt6_eq_iff (r : Fin P.m') (j : Fin sz) :
    (regsAt P o sz c h).pt j = pt6 P r ↔ (r : ℕ) = o + j := by
  constructor
  · intro he
    have := pt6_injective P he
    rw [← this]
  · intro he
    change pt6 P _ = _
    congr 1
    exact Fin.ext he.symm

theorem dir6_eq_iff (r : Fin P.m') (j : Fin sz) :
    (regsAt P o sz c h).dir j = dir6 P r ↔ (r : ℕ) = o + j := by
  constructor
  · intro he
    have := dir6_injective P he
    rw [← this]
  · intro he
    change dir6 P _ = _
    congr 1
    exact Fin.ext he.symm

theorem ptOf6_putPt (w : Fin sz → F) :
    ptOf6 P ((regsAt P o sz c h).putPt w) = placeV o w := by
  funext r
  simp only [ptOf6, placeV]
  split_ifs with hr
  · have := (regsAt P o sz c h).putPt_pt w ⟨r - o, by omega⟩
    rw [← this]
    exact congrArg ((regsAt P o sz c h).putPt w) ((pt6_eq_iff P o sz c h r ⟨r - o, by omega⟩).mpr
      (by show (r : ℕ) = o + (r - o); omega)).symm
  · exact (regsAt P o sz c h).putPt_of_not (fun j hj => hr (by
      have := (pt6_eq_iff P o sz c h r j).mp hj
      omega)) w

theorem dirOf6_putDir (w : Fin sz → F) :
    dirOf6 P ((regsAt P o sz c h).putDir w) = placeV o w := by
  funext r
  simp only [dirOf6, placeV]
  split_ifs with hr
  · have := (regsAt P o sz c h).putDir_dir w ⟨r - o, by omega⟩
    rw [← this]
    exact congrArg ((regsAt P o sz c h).putDir w) ((dir6_eq_iff P o sz c h r ⟨r - o, by omega⟩).mpr
      (by show (r : ℕ) = o + (r - o); omega)).symm
  · exact (regsAt P o sz c h).putDir_of_not (fun j hj => hr (by
      have := (dir6_eq_iff P o sz c h r j).mp hj
      omega)) w

theorem dirOf6_putPt (w : Fin sz → F) : dirOf6 P ((regsAt P o sz c h).putPt w) = 0 := by
  funext r
  exact (regsAt P o sz c h).putPt_of_not (fun j hj => (regs6 P).pt_ne_dir _ _ hj) w

theorem seedsOf_putPt (w : Fin sz → F) : seedsOf P ((regsAt P o sz c h).putPt w) = 0 := by
  funext c'
  exact (regsAt P o sz c h).putPt_of_not (fun j => pt6_ne_coord P _ c') w

theorem ptOf6_putDir (w : Fin sz → F) : ptOf6 P ((regsAt P o sz c h).putDir w) = 0 := by
  funext r
  exact (regsAt P o sz c h).putDir_of_not (fun j hj => (regs6 P).pt_ne_dir _ _ hj.symm) w

theorem seedsOf_putDir (w : Fin sz → F) : seedsOf P ((regsAt P o sz c h).putDir w) = 0 := by
  funext c'
  exact (regsAt P o sz c h).putDir_of_not (fun j => dir6_ne_coord P _ c') w

theorem mem_coordSet_pt6 (r : Fin P.m') : pt6 P r ∉ (regsAt P o sz c h).coordSet := by
  simp only [Regs.coordSet, mem_singleton]
  exact pt6_ne_coord P r c

theorem mem_coordSet_dir6 (r : Fin P.m') : dir6 P r ∉ (regsAt P o sz c h).coordSet := by
  simp only [Regs.coordSet, mem_singleton]
  exact dir6_ne_coord P r c

theorem mem_coordSet_coord (c' : Fin 6) :
    Coord.coord c' ∈ (regsAt P o sz c h).coordSet ↔ c' = c := by
  simp only [Regs.coordSet, mem_singleton]
  change Coord.coord c' = Coord.coord c ↔ c' = c
  simp

theorem mem_dirSet_pt6 (r : Fin P.m') : pt6 P r ∉ (regsAt P o sz c h).dirSet := by
  simp only [Regs.dirSet, mem_image, mem_univ, true_and, not_exists]
  exact fun j hj => (regs6 P).pt_ne_dir _ _ hj.symm

theorem mem_dirSet_dir6 (r : Fin P.m') :
    dir6 P r ∈ (regsAt P o sz c h).dirSet ↔ o ≤ r ∧ (r : ℕ) < o + sz := by
  simp only [Regs.dirSet, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have := (dir6_eq_iff P o sz c h r j).mp hj
    omega
  · intro hr
    exact ⟨⟨r - o, by omega⟩, (dir6_eq_iff P o sz c h r ⟨r - o, by omega⟩).mpr
      (by show (r : ℕ) = o + (r - o); omega)⟩

theorem mem_dirSet_coord (c' : Fin 6) : Coord.coord c' ∉ (regsAt P o sz c h).dirSet := by
  simp only [Regs.dirSet, mem_image, mem_univ, true_and, not_exists]
  exact fun j => dir6_ne_coord P _ c'

theorem mem_finalSet_pt6 (r : Fin P.m') : pt6 P r ∈ (regsAt P o sz c h).finalSet := by
  simp only [Regs.finalSet, mem_sdiff, mem_univ, true_and]
  exact ⟨mem_coordSet_pt6 P o sz c h r, mem_dirSet_pt6 P o sz c h r⟩

theorem mem_finalSet_dir6 (r : Fin P.m') :
    dir6 P r ∈ (regsAt P o sz c h).finalSet ↔ ¬ (o ≤ r ∧ (r : ℕ) < o + sz) := by
  simp only [Regs.finalSet, mem_sdiff, mem_univ, true_and, mem_dirSet_dir6]
  exact ⟨fun h' => h'.2, fun h' => ⟨mem_coordSet_dir6 P o sz c h r, h'⟩⟩

theorem mem_finalSet_coord (c' : Fin 6) :
    Coord.coord c' ∈ (regsAt P o sz c h).finalSet ↔ c' ≠ c := by
  simp only [Regs.finalSet, mem_sdiff, mem_univ, true_and, mem_coordSet_coord]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', mem_dirSet_coord P o sz c h c'⟩⟩

theorem seedsOf_proj_coordSet (x : Coord P → F) :
    seedsOf P (proj (regsAt P o sz c h).coordSet x) = Pi.single c (seedsOf P x c) := by
  funext c'
  simp only [seedsOf, proj_apply, mem_coordSet_coord]
  by_cases hc : c' = c
  · subst hc; simp
  · simp [hc]

theorem ptOf6_proj_coordSet (x : Coord P → F) :
    ptOf6 P (proj (regsAt P o sz c h).coordSet x) = 0 := by
  funext r
  simp [ptOf6, mem_coordSet_pt6]

theorem dirOf6_proj_coordSet (x : Coord P → F) :
    dirOf6 P (proj (regsAt P o sz c h).coordSet x) = 0 := by
  funext r
  simp [dirOf6, mem_coordSet_dir6]

/-! ## The queries, run by run -/

/-- The three runs of a vector. -/
def comps (x : Coord P → F) : (Fin P.m' → F) × (Fin P.m' → F) × (Fin 6 → F) :=
  (ptOf6 P x, dirOf6 P x, seedsOf P x)

omit [Field F] in
theorem comps_injective : Function.Injective (comps P (F := F)) := by
  intro x y hxy
  simp only [comps, Prod.mk.injEq] at hxy
  funext c'
  rw [← (layout P).symm_apply_apply c']
  rcases (layout P) c' with r | r | c''
  · exact congrFun hxy.1 r
  · exact congrFun hxy.2.1 r
  · exact congrFun hxy.2.2 c''

theorem comps_add (x y : Coord P → F) : comps P (x + y) = comps P x + comps P y := rfl

variable [Fintype F] [DecidableEq F] [NeZero sz] {hsz : sz ∣ Fintype.card F} (S : Sel F sz hsz)

/-- The seed run of a line type's first stage. -/
def seedPart (t : Ty) (s : F) : Fin 6 → F := if t = .point then 0 else Pi.single c s

/-- The direction a diagonal line type's second stage writes, before placing. -/
def dirPart (t : Ty) (s : F) (d : Fin sz → F) : Fin sz → F :=
  if t = .dline then zeroBelow (S.χ s) d else 0

omit [Fintype F] [DecidableEq F] [NeZero sz] in
theorem comps_seedLin (t : Ty) (x : Coord P → F) :
    comps P ((regsAt P o sz c h).seedLin t x) = (0, 0, seedPart c t (seedsOf P x c)) := by
  rw [Regs.seedLin_apply]
  unfold seedPart
  split_ifs
  · rfl
  · simp only [comps, ptOf6_proj_coordSet, dirOf6_proj_coordSet, seedsOf_proj_coordSet]

theorem comps_secondLin (t : Ty) (s : F) (x : Coord P → F) :
    comps P ((regsAt P o sz c h).secondLin S t s x) =
      (0, placeV o (dirPart sz S t s (sliceV o sz h (dirOf6 P x))), 0) := by
  rw [Regs.secondLin_apply]
  unfold dirPart
  split_ifs
  · simp only [comps, ptOf6_putDir, dirOf6_putDir, seedsOf_putDir, dirOf_regsAt]
  · simp only [comps, ptOf6_zero, dirOf6_zero, seedsOf_zero, Prod.mk.injEq, and_true, true_and]
    funext r
    simp [placeV]

omit [Fintype F] [DecidableEq F] [NeZero sz] in
theorem comps_putPt (w : Fin sz → F) :
    comps P ((regsAt P o sz c h).putPt w) = (placeV o w, 0, 0) := by
  simp only [comps, ptOf6_putPt, dirOf6_putPt, seedsOf_putPt]

/-- **The marginals, run by run**, from the first level on. -/
theorem comps_marginal (t : Ty) {j : ℕ} (hj : 1 ≤ j) (x : Coord P → F) :
    comps P ((((regsAt P o sz c h).pres S t).truncate j).eval x) =
      (if 3 ≤ j then placeV o (Regs.ptMap S t (seedsOf P x c)
          (dirPart sz S t (seedsOf P x c) (sliceV o sz h (dirOf6 P x))) (sliceV o sz h (ptOf6 P x)))
        else 0,
       if 2 ≤ j then placeV o (dirPart sz S t (seedsOf P x c) (sliceV o sz h (dirOf6 P x)))
        else 0,
       seedPart c t (seedsOf P x c)) := by
  rcases (show j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | h3
  · rw [Regs.eval_truncate_one, comps_seedLin]
    simp only [show ¬ (3 ≤ 1) by omega, show ¬ (2 ≤ 1) by omega, if_false]
  · rw [Regs.eval_truncate_two, comps_add, comps_seedLin, comps_secondLin,
      show x (regsAt P o sz c h).coord = seedsOf P x c from rfl]
    simp only [show ¬ (3 ≤ 2) by omega, le_refl, if_true, if_false, Prod.mk_add_mk, zero_add,
      add_zero]
  · rw [Regs.eval_truncate_three_le _ _ _ h3, Regs.eval_pres, comps_add, comps_add,
      comps_seedLin, comps_secondLin, comps_putPt,
      show x (regsAt P o sz c h).coord = seedsOf P x c from rfl]
    simp only [h3, show 2 ≤ j by omega, if_true, Prod.mk_add_mk, zero_add, add_zero]
    rfl

/-- The first stage map, run by run. -/
theorem comps_map_zero (t : Ty) (u y : Coord P → F) :
    comps P (((regsAt P o sz c h).pres S t).mapOfPrefix 0 u y) =
      (0, 0, seedPart c t (seedsOf P y c)) := by
  rw [Regs.mapOfPrefix_zero]
  exact comps_seedLin P o sz c h t y

/-- The second stage map, run by run. -/
theorem comps_map_one (t : Ty) (u y : Coord P → F) :
    comps P (((regsAt P o sz c h).pres S t).mapOfPrefix 1 u y) =
      (0, placeV o (dirPart sz S t (seedsOf P u c) (sliceV o sz h (dirOf6 P y))), 0) := by
  rw [Regs.mapOfPrefix_one]
  exact comps_secondLin P o sz c h S t _ y

/-- The third stage map, run by run. -/
theorem comps_map_two (t : Ty) (u y : Coord P → F) :
    comps P (((regsAt P o sz c h).pres S t).mapOfPrefix 2 u y) =
      (placeV o (Regs.ptMap S t (seedsOf P u c) (sliceV o sz h (dirOf6 P u))
        (sliceV o sz h (ptOf6 P y))), 0, 0) := by
  rw [Regs.mapOfPrefix_two]
  change comps P ((regsAt P o sz c h).finalLin S t _ _ y) = _
  rw [Regs.finalLin_apply, comps_putPt]
  rfl

end MIPRE.AnswerReduction.Pcp

end
