/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.StageProg
import MIPRE.Background.QLD.LineRepresentative
import MIPRE.Background.LIDT.Adapter.Geometry

/-!
# The stage programs are correct

Piece AR-3d of `planning/answer-reduction.md`: `copyAnswer` (`MIPRE/Background/AnswerReduction/
StageProg`) computes the Shoup bits of a copy's marginals (`copyAnswer_marginal`), stage maps
(`copyAnswer_linear`) and factor spaces (`copyAnswer_factor`), for a copy whose seed selector is
the high bits of the seed (`hχ`).
-/

noncomputable section

namespace MIPRE.AnswerReduction.StageProg

open Cost Pcp SAT Introspection.SeededLineProgram Introspection.LineProgram
  Introspection.SeedProgram MIPRE.LIDT MIPRE.LIDT.CL MIPRE.CL

/-- The number of a test type. -/
def tyNat : LIDT.CL.Ty → ℕ
  | .point => 0
  | .aline => 1
  | .dline => 2

/-! ## The list lemmas for `k`-bit blocks -/

section Lists

variable {α : Type*}

theorem ofFn_run (g : Bool → α) {N sz : ℕ} (o : ℕ) (h : o + sz ≤ N) (l : List α)
    (hl : l.length = N) :
    List.ofFn (fun r : Fin N => g (decide (o ≤ (r : ℕ) ∧ (r : ℕ) < o + sz))) =
      placeL (g false) o (List.replicate sz (g true)) l := by
  subst hl
  apply List.ext_getElem
  · rw [length_placeL _ _ _ _ (by simp; omega)]
    simp
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    simp only [placeL, List.getElem_append, List.length_append, List.length_map, List.length_take,
      List.length_replicate, List.getElem_map, List.getElem_replicate]
    simp only [List.length_ofFn] at h1
    have ho : min o l.length = o := min_eq_left (by omega)
    simp only [ho]
    by_cases ha : o ≤ i ∧ i < o + sz
    · rw [decide_eq_true ha, dif_pos (by omega), dif_neg (by omega)]
    · rw [decide_eq_false ha]
      by_cases hb : i < o + sz
      · rw [dif_pos hb, dif_pos (by omega)]
      · rw [dif_neg hb]

theorem ofFn_run_not (g : Bool → α) {N sz : ℕ} (o : ℕ) (h : o + sz ≤ N) (l : List α)
    (hl : l.length = N) :
    List.ofFn (fun r : Fin N => g (decide (¬ (o ≤ (r : ℕ) ∧ (r : ℕ) < o + sz)))) =
      placeL (g true) o (List.replicate sz (g false)) l := by
  have := ofFn_run (fun b => g (!b)) o h l hl
  simp only [Bool.not_true, Bool.not_false] at this
  rw [← this]
  simp only [decide_not]

theorem ofFn_eq_seed (g : Bool → α) (c : Fin 6) (l : List α) (hl : l.length = 6) :
    List.ofFn (fun c' : Fin 6 => g (decide (c' = c))) = placeL (g false) c [g true] l := by
  have := ofFn_run g (N := 6) (sz := 1) c (by omega) l hl
  rw [show [g true] = List.replicate 1 (g true) from rfl]
  convert this using 2
  funext c'
  congr 1
  simp only [Fin.ext_iff]
  exact decide_eq_decide.mpr ⟨fun h' => by omega, fun h' => by omega⟩

theorem ofFn_ne_seed (g : Bool → α) (c : Fin 6) (l : List α) (hl : l.length = 6) :
    List.ofFn (fun c' : Fin 6 => g (decide (c' ≠ c))) = placeL (g true) c [g false] l := by
  have := ofFn_eq_seed (fun b => g (!b)) c l hl
  simp only [Bool.not_true, Bool.not_false] at this
  rw [← this]
  simp only [ne_eq, decide_not]

theorem ofFn_const (a : α) {N : ℕ} (l : List α) (hl : l.length = N) :
    List.ofFn (fun _ : Fin N => a) = l.map (fun _ => a) := by
  subst hl
  apply List.ext_getElem <;> simp

end Lists

variable {k : ℕ} (hk : 1 ≤ k)

local notation "E" => shoupBinField k hk

/-! ## Vectors of `F_q` and their blocks -/

theorem vecBits_eq_ofFn {N : ℕ} (v : Fin N → (E).carrier) :
    (E).vecBits v = List.ofFn fun r => (E).toBits (v r) := by
  simp [BinField.vecBits, List.map_ofFn]
  rfl

theorem zb_eq : zb (unary k) = (E).toBits 0 := shoupZeroProg_correct k hk

theorem blk_eq (b : Bool) : blk (unary k) b = List.replicate k b := by
  simp [blk, unary]

theorem vecBits_placeV {N sz : ℕ} (o : ℕ) (h : o + sz ≤ N) (w : Fin sz → (E).carrier)
    (l : List BitStr) (hl : l.length = N) :
    (E).vecBits (placeV o w : Fin N → (E).carrier) = placeL (zb (unary k)) o ((E).vecBits w) l := by
  rw [vecBits_eq_ofFn, vecBits_eq_ofFn, zb_eq hk]
  exact ofFn_placeV (E).toBits o h w l hl

theorem vecBits_sliceV {N : ℕ} (o sz : ℕ) (h : o + sz ≤ N) (v : Fin N → (E).carrier) :
    (E).vecBits (sliceV o sz h v) = sliceL o sz ((E).vecBits v) := by
  rw [vecBits_eq_ofFn, vecBits_eq_ofFn]
  exact ofFn_sliceV (E).toBits o sz h v

theorem vecBits_single (c : Fin 6) (a : (E).carrier) (l : List BitStr) (hl : l.length = 6) :
    (E).vecBits (Pi.single c a : Fin 6 → (E).carrier) =
      placeL (zb (unary k)) c [(E).toBits a] l := by
  rw [vecBits_eq_ofFn, zb_eq hk]
  exact ofFn_single (E).toBits c a l hl

theorem vecBits_zero {N : ℕ} (l : List BitStr) (hl : l.length = N) :
    (E).vecBits (0 : Fin N → (E).carrier) = zeroed (unary k) l := by
  rw [vecBits_eq_ofFn, zeroed, zb_eq hk]
  simp only [Pi.zero_apply]
  exact ofFn_const _ l hl

theorem placeV_zero {F : Type*} [Zero F] {N sz : ℕ} (o : ℕ) :
    (placeV o (0 : Fin sz → F) : Fin N → F) = 0 := by
  funext r; simp [placeV]

/-! ## The seed and the field arithmetic -/

variable (o sz jw : ℕ) (c : Fin 6)

theorem seedOf_vecBits (s6 : Fin 6 → (E).carrier) :
    seedOf (unary o, unary sz, unary jw, unary c) ((E).vecBits s6) = (E).toBits (s6 c) := by
  rw [seedOf, length_unary, vecBits_eq_ofFn, List.drop_eq_getElem_cons (by simp),
    List.headD_cons, List.getElem_ofFn]

variable [NeZero sz] {hsz : sz ∣ Fintype.card (E).carrier} (S : Sel (E).carrier sz hsz)
  (hjw : jw ≤ k) (hχ : ∀ a, (S.χ a : ℕ) = (selector E jw hjw a : ℕ))

include hjw hχ in
theorem selDirL_vecBits (s : (E).carrier) (w : Fin sz → (E).carrier) :
    selDirL (unary k) (unary o, unary sz, unary jw, unary c) ((E).toBits s) ((E).vecBits w) =
      (E).vecBits (zeroBelow (S.χ s) w) := by
  change maskBeforeProg (unary k, selectorProg (unary k, unary jw, (E).toBits s),
    (E).vecBits w) = _
  rw [selectorProg_correct _ jw hjw, ← hχ, maskBeforeProg_correct k hk]
  rfl

include hjw hχ in
theorem ptMapL_vecBits (τ : LIDT.CL.Ty) (s : (E).carrier) (dir w : Fin sz → (E).carrier) :
    ptMapL (unary k) (unary o, unary sz, unary jw, unary c) (tyNat τ) ((E).toBits s)
      ((E).vecBits dir) ((E).vecBits w) = (E).vecBits (Regs.ptMap S τ s dir w) := by
  cases τ with
  | point => rfl
  | aline =>
    simp only [ptMapL, tyNat, if_true]
    change zeroCoordinateProg (unary k, selectorProg (unary k, unary jw, (E).toBits s),
      (E).vecBits w) = _
    rw [selectorProg_correct _ jw hjw, ← hχ, zeroCoordinateProg_correct k hk]
    congr 1
    funext i
    simp only [Regs.ptMap, LIDT.Adapter.rep_single, Pi.sub_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul]
    split_ifs with hi
    · subst hi; simp
    · simp
  | dline =>
    simp only [ptMapL, tyNat, show (2 : ℕ) ≠ 1 by decide, if_false, if_true]
    rw [lineRepresentativeProg_correct k hk, QLD.representative_eq_canonLin]
    rfl

end MIPRE.AnswerReduction.StageProg

end
