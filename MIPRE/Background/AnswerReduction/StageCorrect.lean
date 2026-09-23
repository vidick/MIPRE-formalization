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

variable [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz) (hjw : jw ≤ k)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))

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
    rw [lineRepresentativeProg_correct k hk, QLD.PauliCL.representative_eq_canonLin]
    rfl

/-! ## The blocks of a vector of `V^pcp` -/

section Blocks

variable (P : PcpParams)

theorem flatBits_eq_bitsOf (v : Coord P → (E).carrier) :
    flatBits P hk v = bitsOf ((E).vecBits (ptOf6 P v), (E).vecBits (dirOf6 P v),
      (E).vecBits (seedsOf P v)) := by
  rw [flatBits, vecBits_coordIndex]
  rfl

theorem blocksOf_flatBits (v : Coord P → (E).carrier) :
    blocksOf (unary k) (unary P.m') (flatBits P hk v) =
      ((E).vecBits (ptOf6 P v), (E).vecBits (dirOf6 P v), (E).vecBits (seedsOf P v)) := by
  have hL : ((E).vecBits (ptOf6 P v) ++ (E).vecBits (dirOf6 P v) ++
      (E).vecBits (seedsOf P v)).length = P.m' + (P.m' + 6) := by
    simp only [List.length_append, BinField.length_vecBits]; ring
  have hw : ∀ b ∈ (E).vecBits (ptOf6 P v) ++ (E).vecBits (dirOf6 P v) ++
      (E).vecBits (seedsOf P v), b.length = k := by
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb <;> exact (E).width_vecBits _ hb
  have hs := Introspection.BinaryBlock.splitBlocks_flatten k _ hw
  rw [hL] at hs
  simp only [blocksOf, length_unary, flatBits_eq_bitsOf, bitsOf]
  rw [hs, List.append_assoc]
  simp only [List.take_left' (BinField.length_vecBits _ _), List.drop_left'
    (BinField.length_vecBits _ _)]

/-- The indicator bits of a set of coordinates of `V^pcp`, `k` per coordinate, in the
numbering. -/
def flatInd (k : ℕ) (F : Finset (Coord P)) : BitStr :=
  (List.ofFn fun r => List.replicate k (decide ((coordIndex P).symm r ∈ F))).flatten

omit hk in
theorem flatInd_eq_bitsOf (k : ℕ) (F : Finset (Coord P)) :
    flatInd P k F = bitsOf (List.ofFn (fun r => List.replicate k (decide (pt6 P r ∈ F))),
      List.ofFn (fun r => List.replicate k (decide (dir6 P r ∈ F))),
      List.ofFn (fun c => List.replicate k (decide (Coord.coord c ∈ F)))) := by
  rw [flatInd, ofFn_coordIndex P (fun c => List.replicate k (decide (c ∈ F)))]
  rfl

end Blocks

/-! ## The queries of a copy -/

section Copy

variable (P : PcpParams) (h : o + sz ≤ P.m')

local notation "D" => ((unary o, unary sz, unary jw, unary c) : Desc)

theorem dirPart_ptMap (τ : LIDT.CL.Ty) (s : (E).carrier) (w : Fin sz → (E).carrier) :
    Regs.ptMap S τ s (zeroBelow (S.χ s) w) = Regs.ptMap S τ s (dirPart sz S τ s w) := by
  cases τ <;> rfl

theorem zeroed_vecBits {N : ℕ} (v : Fin N → (E).carrier) :
    zeroed (unary k) ((E).vecBits v) = (E).vecBits (0 : Fin N → (E).carrier) :=
  (vecBits_zero hk _ (BinField.length_vecBits _ _)).symm

theorem seedOut_vecBits (τ : LIDT.CL.Ty) (s : (E).carrier) (s6 : Fin 6 → (E).carrier) :
    seedOut (unary k) D (tyNat τ) ((E).toBits s) ((E).vecBits s6) =
      (E).vecBits (seedPart c τ s) := by
  unfold seedOut seedPart
  cases τ
  · simp only [tyNat, if_true]
    exact zeroed_vecBits hk _
  · simp only [tyNat, show (1 : ℕ) ≠ 0 by decide, if_false, reduceCtorEq, length_unary]
    exact (vecBits_single hk c _ _ (BinField.length_vecBits _ _)).symm
  · simp only [tyNat, show (2 : ℕ) ≠ 0 by decide, if_false, reduceCtorEq, length_unary]
    exact (vecBits_single hk c _ _ (BinField.length_vecBits _ _)).symm

include hjw hχ in
theorem dirOut_vecBits (τ : LIDT.CL.Ty) (s : (E).carrier) (d6 : Fin P.m' → (E).carrier) :
    dirOut (unary k) D (tyNat τ) ((E).toBits s) ((E).vecBits d6) =
      (E).vecBits (placeV o (dirPart sz S τ s (sliceV o sz h d6)) : Fin P.m' → (E).carrier) := by
  unfold dirOut dirPart
  cases τ
  · simp only [tyNat, show (0 : ℕ) ≠ 2 by decide, if_false, reduceCtorEq, placeV_zero]
    exact zeroed_vecBits hk _
  · simp only [tyNat, show (1 : ℕ) ≠ 2 by decide, if_false, reduceCtorEq, placeV_zero]
    exact zeroed_vecBits hk _
  · simp only [tyNat, if_true, length_unary]
    rw [← vecBits_sliceV hk o sz h, selDirL_vecBits hk o sz jw c S hjw hχ,
      vecBits_placeV hk o h _ _ (BinField.length_vecBits _ _)]

include hjw hχ in
theorem ptOut_vecBits (τ : LIDT.CL.Ty) (s : (E).carrier) (dir : Fin sz → (E).carrier)
    (p6 : Fin P.m' → (E).carrier) :
    ptOut (unary k) D (tyNat τ) ((E).toBits s) ((E).vecBits dir) ((E).vecBits p6) =
      (E).vecBits (placeV o (Regs.ptMap S τ s dir (sliceV o sz h p6)) :
        Fin P.m' → (E).carrier) := by
  simp only [ptOut, length_unary]
  rw [← vecBits_sliceV hk o sz h, ptMapL_vecBits hk o sz jw c S hjw hχ,
    vecBits_placeV hk o h _ _ (BinField.length_vecBits _ _)]

include hjw hχ in
/-- **The marginals of a copy**, in bits. -/
theorem copyAnswer_marginal (τ : LIDT.CL.Ty) {j : ℕ} (hj : 1 ≤ j) (v : Coord P → (E).carrier)
    (y : BitStr) :
    copyAnswer (unary k) D (tyNat τ) (unary P.m') 1 j (flatBits P hk v) y =
      flatBits P hk ((((regsAt P o sz c h).pres S τ).truncate j).eval v) := by
  rw [flatBits_eq_bitsOf hk P (((_ : MIPRE.CL.CLFun _ _ 3).truncate j).eval v)]
  have hc := comps_marginal P o sz c h S τ hj v
  simp only [comps, Prod.mk.injEq] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  rw [h1, h2, h3]
  simp only [copyAnswer, if_true, blocksOf_flatBits, margL, seedOf_vecBits]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    split_ifs with h3j
    · simp only [length_unary]
      rw [← vecBits_sliceV hk _ _ h, selDirL_vecBits hk o sz jw c S hjw hχ,
        ptOut_vecBits hk o sz jw c S hjw hχ P h, dirPart_ptMap]
    · exact zeroed_vecBits hk _
  · simp only
    split_ifs with h2j
    · exact dirOut_vecBits hk o sz jw c S hjw hχ P h τ _ _
    · exact zeroed_vecBits hk _
  · exact seedOut_vecBits hk o sz jw c τ _ _

include hjw hχ in
/-- **The stage maps of a copy**, in bits. -/
theorem copyAnswer_linear (τ : LIDT.CL.Ty) {j : ℕ} (hj : 1 ≤ j) (u y : Coord P → (E).carrier) :
    copyAnswer (unary k) D (tyNat τ) (unary P.m') 2 j (flatBits P hk u) (flatBits P hk y) =
      flatBits P hk (((regsAt P o sz c h).pres S τ).mapOfPrefix (j - 1) u y) := by
  rw [flatBits_eq_bitsOf hk P (((_ : MIPRE.CL.CLFun _ _ 3).mapOfPrefix (j - 1) u) y)]
  simp only [copyAnswer, show (2 : ℕ) ≠ 1 by decide, if_false, if_true, blocksOf_flatBits, linL]
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | rfl | h4
  · have hc := comps_map_zero P o sz c h S τ u y
    simp only [comps, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [Nat.sub_self, h1, h2, h3, if_true, seedOf_vecBits, zeroed_vecBits hk,
      seedOut_vecBits hk o sz jw c]
  · have hc := comps_map_one P o sz c h S τ u y
    simp only [comps, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [show 2 - 1 = 1 from rfl, h1, h2, h3, show (2 : ℕ) ≠ 1 by decide, if_false,
      if_true, seedOf_vecBits, zeroed_vecBits hk, dirOut_vecBits hk o sz jw c S hjw hχ P h]
  · have hc := comps_map_two P o sz c h S τ u y
    simp only [comps, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [show 3 - 1 = 2 from rfl, h1, h2, h3, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, if_false, if_true, seedOf_vecBits, zeroed_vecBits hk]
    simp only [length_unary]
    rw [← vecBits_sliceV hk o sz h, ptOut_vecBits hk o sz jw c S hjw hχ P h]
  · rw [Regs.mapOfPrefix_three_le _ _ _ (by omega)]
    simp only [show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega, if_false,
      zeroed_vecBits hk, LinearMap.zero_apply, ptOf6_zero, dirOf6_zero, seedsOf_zero]

include hjw hχ in
/-- **The factor spaces of a copy**, in indicator bits. -/
theorem copyAnswer_factor (τ : LIDT.CL.Ty) {j : ℕ} (hj : 1 ≤ j) (u : Coord P → (E).carrier)
    (y : BitStr) :
    copyAnswer (unary k) D (tyNat τ) (unary P.m') 3 j (flatBits P hk u) y =
      flatInd P k (((regsAt P o sz c h).pres S τ).factorOfPrefix (j - 1) u) := by
  rw [flatInd_eq_bitsOf]
  simp only [copyAnswer, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false,
    if_true, blocksOf_flatBits, facL, blk_eq, length_unary]
  have hp := BinField.length_vecBits (shoupBinField k hk) (ptOf6 P u)
  have hd := BinField.length_vecBits (shoupBinField k hk) (dirOf6 P u)
  have hs := BinField.length_vecBits (shoupBinField k hk) (seedsOf P u)
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | rfl | h4
  · simp only [Nat.sub_self, Regs.factorOfPrefix_zero, if_true, mem_coordSet_pt6,
      mem_coordSet_dir6, mem_coordSet_coord, decide_false]
    rw [ofFn_eq_seed (fun b => List.replicate k b) c _ hs]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · simp only [show 2 - 1 = 1 from rfl, Regs.factorOfPrefix_one, show (2 : ℕ) ≠ 1 by decide,
      if_false, if_true, mem_dirSet_pt6, mem_dirSet_dir6, mem_dirSet_coord, decide_false]
    rw [ofFn_run (fun b => List.replicate k b) o h _ hd]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · simp only [show 3 - 1 = 2 from rfl, Regs.factorOfPrefix_two, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, if_false, if_true, mem_finalSet_pt6, mem_finalSet_dir6,
      mem_finalSet_coord, decide_true]
    rw [ofFn_run_not (fun b => List.replicate k b) o h _ hd,
      ofFn_ne_seed (fun b => List.replicate k b) c _ hs]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · rw [Regs.factorOfPrefix_three_le _ _ _ (by omega)]
    simp only [show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega, if_false,
      Finset.notMem_empty, decide_false]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]

end Copy

end MIPRE.AnswerReduction.StageProg

end
