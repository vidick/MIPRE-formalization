/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArFamily
public import MIPRE.Background.AnswerReduction.PcpSampler

@[expose] public section

/-!
# The low-degree half of the answer-reduced sampler, directly answered

Slice P4h of `planning/aldous-lyons-track.md`: the seeded low-degree test's presentation on the
registers `regs j` (`F_q^{D}`, `D = 2M + 1`: the point, the direction, one seed), downsized along
the Shoup basis and numbered coordinate by coordinate (`ldCl`), as a sampler answered by a
polynomial-time function of its parameters (`CL.DirectSampler`), the right factor of the
answer-reduced typed sampler (`TypedSampler.prodDirect`).

The bits of a vector are its coordinates' Shoup bits, `t` per coordinate (`toBits_ld`): three runs
of `t`-bit blocks, `M` point blocks, `M` direction blocks and one seed block (`blocks1_ldBitsV`).
The MIP* answer reduction answers one copy of the test on such runs (`AnswerReduction.StageProg`,
with six seed blocks there): its run functions `margL`, `linL`, `facL` and their programs are
reused unchanged on the one-copy layout, at offset `0` and length `M` (`ldDesc`), with a split
into `M + M + 1` blocks (`blocks1`). What a query returns, run by run, is `comps1_marginal` and
`comps1_map_*`; `ldAnswer_marginal`, `ldAnswer_linear` and `ldAnswer_factor` are the answers in
bits, and `LdFamily.directSampler` the sampler, for any parameter routine.

The selector is the high bits of the seed (`AnswerReduction.powSel`), which the field
arithmetic programs compute.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset Cost Cost.PolyTimeFun MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT MIPRE.LIDT.CL MIPRE.SAT
open MIPRE.AnswerReduction.StageProg MIPRE.AnswerReduction.Pcp

/-! ## The components of a vector of the registers -/

section Comps

variable (j : ℕ) {F : Type*} [Field F]

/-- **The three components of a vector of the registers**: the point, the direction, the
seed. -/
def comps1 (x : Fin (D j) → F) : (Fin (2 ^ j) → F) × (Fin (2 ^ j) → F) × F :=
  ((regs j).ptOf x, (regs j).dirOf x, x (regs j).coord)

theorem comps1_add (x y : Fin (D j) → F) : comps1 j (x + y) = comps1 j x + comps1 j y := rfl

theorem comps1_putPt (w : Fin (2 ^ j) → F) : comps1 j ((regs j).putPt w) = (w, 0, 0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i; exact (regs j).putPt_pt w i
  · funext i; exact (regs j).putPt_of_not (fun i' h => (regs j).pt_ne_dir _ _ h) w
  · exact (regs j).putPt_of_not (fun i' h => (regs j).pt_ne_coord _ h) w

theorem comps1_putDir (w : Fin (2 ^ j) → F) : comps1 j ((regs j).putDir w) = (0, w, 0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i; exact (regs j).putDir_of_not (fun i' h => (regs j).pt_ne_dir _ _ h.symm) w
  · funext i; exact (regs j).putDir_dir w i
  · exact (regs j).putDir_of_not (fun i' h => (regs j).dir_ne_coord _ h) w

theorem comps1_proj_coordSet (x : Fin (D j) → F) :
    comps1 j (proj (regs j).coordSet x) = (0, 0, x (regs j).coord) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    simp only [comps1, Regs.ptOf, proj_apply, Regs.coordSet, mem_singleton, Pi.zero_apply]
    rw [ite_eq_right ((regs j).pt_ne_coord i)]
  · funext i
    simp only [comps1, Regs.dirOf, proj_apply, Regs.coordSet, mem_singleton, Pi.zero_apply]
    rw [ite_eq_right ((regs j).dir_ne_coord i)]
  · simp [comps1, Regs.coordSet]

variable [Fintype F] [DecidableEq F] {hM : 2 ^ j ∣ Fintype.card F} (S : Sel F (2 ^ j) hM)

/-- The seed component of a line type's first stage. -/
def seedPart1 (τ : Ty) (s : F) : F := if τ = .point then 0 else s

omit [Fintype F] [DecidableEq F] in
theorem comps1_seedLin (τ : Ty) (x : Fin (D j) → F) :
    comps1 j ((regs j).seedLin τ x) = (0, 0, seedPart1 τ (x (regs j).coord)) := by
  rw [Regs.seedLin_apply]
  unfold seedPart1
  split_ifs
  · rfl
  · exact comps1_proj_coordSet j x

theorem comps1_secondLin (τ : Ty) (s : F) (x : Fin (D j) → F) :
    comps1 j ((regs j).secondLin S τ s x) = (0, dirPart (2 ^ j) S τ s ((regs j).dirOf x), 0) := by
  rw [Regs.secondLin_apply]
  unfold dirPart
  split_ifs
  · exact comps1_putDir j _
  · rfl

/-- **The marginals, run by run**: the line's base point on the point run, the cut-down
direction on the direction run for a diagonal line, the seed for a line. -/
theorem comps1_marginal (τ : Ty) {lev : ℕ} (hl : 1 ≤ lev) (x : Fin (D j) → F) :
    comps1 j ((((regs j).pres S τ).truncate lev).eval x) =
      (if 3 ≤ lev then Regs.ptMap S τ (x (regs j).coord)
          (dirPart (2 ^ j) S τ (x (regs j).coord) ((regs j).dirOf x)) ((regs j).ptOf x) else 0,
       if 2 ≤ lev then dirPart (2 ^ j) S τ (x (regs j).coord) ((regs j).dirOf x) else 0,
       seedPart1 τ (x (regs j).coord)) := by
  rcases (show lev = 1 ∨ lev = 2 ∨ 3 ≤ lev by omega) with rfl | rfl | h3
  · rw [Regs.eval_truncate_one, comps1_seedLin]
    simp only [show ¬ (3 ≤ 1) by omega, show ¬ (2 ≤ 1) by omega, ite_false]
  · rw [Regs.eval_truncate_two, comps1_add, comps1_seedLin, comps1_secondLin]
    simp only [show ¬ (3 ≤ 2) by omega, le_refl, ite_true, ite_false, Prod.mk_add_mk, zero_add,
      add_zero]
  · rw [Regs.eval_truncate_three_le _ _ _ h3, Regs.eval_pres, comps1_add, comps1_add,
      comps1_seedLin, comps1_secondLin, comps1_putPt]
    simp only [h3, show 2 ≤ lev by omega, ite_true, Prod.mk_add_mk, zero_add, add_zero]
    rfl

/-- The first stage map, run by run. -/
theorem comps1_map_zero (τ : Ty) (u y : Fin (D j) → F) :
    comps1 j (((regs j).pres S τ).mapOfPrefix 0 u y) = (0, 0, seedPart1 τ (y (regs j).coord)) := by
  rw [Regs.mapOfPrefix_zero]
  exact comps1_seedLin j τ y

/-- The second stage map, run by run. -/
theorem comps1_map_one (τ : Ty) (u y : Fin (D j) → F) :
    comps1 j (((regs j).pres S τ).mapOfPrefix 1 u y) =
      (0, dirPart (2 ^ j) S τ (u (regs j).coord) ((regs j).dirOf y), 0) := by
  rw [Regs.mapOfPrefix_one]
  exact comps1_secondLin j S τ _ y

/-- The third stage map, run by run. -/
theorem comps1_map_two (τ : Ty) (u y : Fin (D j) → F) :
    comps1 j (((regs j).pres S τ).mapOfPrefix 2 u y) =
      (Regs.ptMap S τ (u (regs j).coord) ((regs j).dirOf u) ((regs j).ptOf y), 0, 0) := by
  rw [Regs.mapOfPrefix_two]
  change comps1 j ((regs j).finalLin S τ _ _ y) = _
  rw [Regs.finalLin_apply, comps1_putPt]

end Comps

/-! ## The factor spaces, coordinate by coordinate -/

section Sets

variable (j : ℕ)

theorem mem_coordSet_regs (r : Fin (D j)) :
    r ∈ (regs j).coordSet ↔ (r : ℕ) = 2 * 2 ^ j := by
  simp only [Regs.coordSet, mem_singleton, Fin.ext_iff]
  rfl

theorem mem_dirSet_regs (r : Fin (D j)) :
    r ∈ (regs j).dirSet ↔ 2 ^ j ≤ (r : ℕ) ∧ (r : ℕ) < 2 * 2 ^ j := by
  simp only [Regs.dirSet, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    have := i.2
    change 2 ^ j ≤ 2 ^ j + (i : ℕ) ∧ 2 ^ j + (i : ℕ) < 2 * 2 ^ j
    omega
  · intro h
    refine ⟨⟨r - 2 ^ j, by omega⟩, Fin.ext ?_⟩
    change 2 ^ j + ((r : ℕ) - 2 ^ j) = r
    omega

theorem mem_finalSet_regs (r : Fin (D j)) : r ∈ (regs j).finalSet ↔ (r : ℕ) < 2 ^ j := by
  simp only [Regs.finalSet, mem_sdiff, mem_univ, true_and, mem_coordSet_regs, mem_dirSet_regs]
  have := r.2
  simp only [D] at this
  omega

end Sets

/-! ## The bits of a vector of the registers -/

section Bits

variable (j : ℕ) (t : ℕ) (ht : 1 ≤ t)

local notation "E" => shoupBinField t ht

/-- **The Shoup bits of a vector of the registers**, coordinate by coordinate. -/
def ldBitsV (v : Fin (D j) → (E).carrier) : BitStr := ((E).vecBits v).flatten

theorem finProdFinEquiv_symm_mk (r : Fin (D j)) (b : Fin t) (h : (r : ℕ) * t + b < D j * t) :
    (finProdFinEquiv : Fin (D j) × Fin t ≃ Fin (D j * t)).symm ⟨r * t + b, h⟩ = (r, b) := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp [finProdFinEquiv]; ring)

/-- **The bits of the downsized vector** are its coordinates' Shoup bits, in order. -/
theorem toBits_ld (v : Fin (D j) → (E).carrier) :
    CL.toBits (reindexEquiv finProdFinEquiv (downsizeEquiv (shoupPowerBasis t ht) v)) =
      ldBitsV j t ht v := by
  simp only [CL.toBits, ldBitsV, BinField.vecBits]
  rw [List.ofFn_mul, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  simp only [Function.comp_apply]
  rw [← repr_shoup ht]
  congr 1
  funext b
  rw [reindexEquiv_apply, finProdFinEquiv_symm_mk, downsizeEquiv_apply]

theorem ofBits_ld (v : Fin (D j) → (E).carrier) :
    ofBits (D j * t) (ldBitsV j t ht v) =
      reindexEquiv finProdFinEquiv (downsizeEquiv (shoupPowerBasis t ht) v) := by
  rw [← toBits_ld, ofBits_toBits]

/-- Every bit string of the right length is the bits of a vector of the registers. -/
theorem exists_ldBitsV {z : BitStr} (hz : z.length = D j * t) :
    ∃ v : Fin (D j) → (E).carrier, z = ldBitsV j t ht v := by
  refine ⟨(downsizeEquiv (shoupPowerBasis t ht)).symm
    ((reindexEquiv finProdFinEquiv).symm (ofBits _ z)), ?_⟩
  rw [← toBits_ld, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, toBits_ofBits hz]

/-- **The bits of a vector are its three runs of blocks.** -/
theorem vecBits_regs (v : Fin (D j) → (E).carrier) :
    (E).vecBits v = (E).vecBits ((regs j).ptOf v) ++ (E).vecBits ((regs j).dirOf v) ++
      [(E).toBits (v (regs j).coord)] := by
  rw [vecBits_eq_ofFn ht, vecBits_eq_ofFn ht, vecBits_eq_ofFn ht]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_singleton, D]
    omega
  · intro i h1 h2
    simp only [List.length_ofFn, D] at h1
    simp only [List.getElem_ofFn, List.getElem_append, List.length_append, List.length_ofFn,
      List.getElem_singleton]
    by_cases ha : i < 2 ^ j
    · rw [dite_eq_left (by omega), dite_eq_left ha]
      rfl
    · by_cases hb : i < 2 ^ j + 2 ^ j
      · rw [dite_eq_left hb, dite_eq_right ha]
        simp only [Regs.dirOf, regs]
        congr 2
        exact Fin.ext (by simp only; omega)
      · rw [dite_eq_right hb]
        simp only [regs]
        congr 2
        exact Fin.ext (by simp only; omega)

/-- **The three runs of a bit string** of `M + M + 1` blocks of `k` bits. -/
def blocks1 (k m' : Unary) (z : BitStr) : Blocks :=
  let l := Introspection.BinaryBlock.splitBlocks (m'.length + (m'.length + 1)) k.length z
  (l.take m'.length, (l.drop m'.length).take m'.length, (l.drop m'.length).drop m'.length)

theorem blocks1_ldBitsV (v : Fin (D j) → (E).carrier) :
    blocks1 (unary t) (unary (2 ^ j)) (ldBitsV j t ht v) =
      ((E).vecBits ((regs j).ptOf v), (E).vecBits ((regs j).dirOf v),
        [(E).toBits (v (regs j).coord)]) := by
  have hL : ((E).vecBits ((regs j).ptOf v) ++ (E).vecBits ((regs j).dirOf v) ++
      [(E).toBits (v (regs j).coord)]).length = 2 ^ j + (2 ^ j + 1) := by
    simp only [List.length_append, BinField.length_vecBits, List.length_singleton]; ring
  have hw : ∀ b ∈ (E).vecBits ((regs j).ptOf v) ++ (E).vecBits ((regs j).dirOf v) ++
      [(E).toBits (v (regs j).coord)], b.length = t := by
    intro b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (hb | hb) | rfl
    · exact (E).width_vecBits _ hb
    · exact (E).width_vecBits _ hb
    · exact (E).length_toBits _
  have hs := Introspection.BinaryBlock.splitBlocks_flatten t _ hw
  rw [hL] at hs
  simp only [blocks1, length_unary, ldBitsV, vecBits_regs]
  rw [hs, List.append_assoc]
  simp only [List.take_left' (BinField.length_vecBits _ _),
    List.drop_left' (BinField.length_vecBits _ _)]

/-- The indicator bits of a set of coordinates of the registers, `k` per coordinate. -/
def ldInd (k : ℕ) (F : Finset (Fin (D j))) : BitStr :=
  (List.ofFn fun r => List.replicate k (decide (r ∈ F))).flatten

theorem ldInd_eq_bitsOf (k : ℕ) (F : Finset (Fin (D j))) :
    ldInd j k F = bitsOf (List.ofFn (fun r => List.replicate k (decide ((regs j).pt r ∈ F))),
      List.ofFn (fun r => List.replicate k (decide ((regs j).dir r ∈ F))),
      [List.replicate k (decide ((regs j).coord ∈ F))]) := by
  rw [ldInd, bitsOf]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_singleton, D]
    omega
  · intro i h1 h2
    simp only [List.length_ofFn, D] at h1
    simp only [List.getElem_ofFn, List.getElem_append, List.length_append, List.length_ofFn,
      List.getElem_singleton]
    by_cases ha : i < 2 ^ j
    · rw [dite_eq_left (by omega), dite_eq_left ha]
      rfl
    · by_cases hb : i < 2 ^ j + 2 ^ j
      · rw [dite_eq_left hb, dite_eq_right ha]
        simp only [regs]
        congr 3
        exact Fin.ext (by simp only; omega)
      · rw [dite_eq_right hb]
        simp only [regs]
        congr 3
        exact Fin.ext (by simp only; omega)

end Bits

/-! ## The downsized presentation in bits -/

section Downsized

variable {j : ℕ} {t : ℕ} {ht : 1 ≤ t} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  (S : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM)

theorem toBits_eval_truncate_ldCl (τ : Ty) (lev : ℕ) (v : Fin (D j) → Fq t ht) :
    CL.toBits (((ldCl t ht S τ).truncate lev).eval (ofBits _ (ldBitsV j t ht v))) =
      ldBitsV j t ht ((((regs j).pres S τ).truncate lev).eval v) := by
  rw [ofBits_ld, ldCl, truncate_reindex, eval_reindex, eval_truncate_downsize, toBits_ld]

theorem toBits_mapOfPrefix_ldCl (τ : Ty) (lev : ℕ) (u y : Fin (D j) → Fq t ht) :
    CL.toBits ((ldCl t ht S τ).mapOfPrefix lev (ofBits _ (ldBitsV j t ht u))
      (ofBits _ (ldBitsV j t ht y))) =
      ldBitsV j t ht (((regs j).pres S τ).mapOfPrefix lev u y) := by
  rw [ofBits_ld, ofBits_ld, ldCl, mapOfPrefix_reindex,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, mapOfPrefix_downsize, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.restrictScalars_apply, toBits_ld]

theorem indicatorBits_factorOfPrefix_ldCl (τ : Ty) (lev : ℕ) (u : Fin (D j) → Fq t ht) :
    indicatorBits ((ldCl t ht S τ).factorOfPrefix lev (ofBits _ (ldBitsV j t ht u))) =
      ldInd j t (((regs j).pres S τ).factorOfPrefix lev u) := by
  rw [ofBits_ld, ldCl, factorOfPrefix_reindex, factorOfPrefix_downsize, indicatorBits, ldInd,
    List.ofFn_mul]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  rw [← List.ofFn_const]
  apply List.ofFn_inj.mpr
  funext b
  congr 1
  rw [Finset.mem_map_equiv, finProdFinEquiv_symm_mk, Finset.mem_product]
  simp

end Downsized

/-! ## The answers of the one-copy test -/

section Answer

/-- The copy's description: offset `0`, length `M = 2^j`, selector width `j`, seed `0`. -/
def ldDesc (j : ℕ) : Desc := (unary 0, unary (2 ^ j), unary j, unary 0)

/-- **The answer of the one-copy test** to a query of kind `kind` at level `lev` with vectors
`u`, `y`: the MIP* answer reduction's run functions on runs of `M + M + 1` blocks. -/
def ldAnswer (k : Unary) (d : Desc) (τ : ℕ) (m' : Unary) (kind lev : ℕ) (u y : BitStr) :
    BitStr :=
  if kind = 1 then bitsOf (margL k d τ lev (blocks1 k m' u))
  else if kind = 2 then bitsOf (linL k d τ lev (blocks1 k m' u) (blocks1 k m' y))
  else if kind = 3 then bitsOf (facL k d lev (blocks1 k m' u))
  else []

theorem sliceL_zero_full {α : Type*} (l : List α) {N : ℕ} (hl : l.length = N) :
    sliceL 0 N l = l := by
  simp [sliceL, ← hl]

theorem placeL_zero_full {α : Type*} (fill : α) (w l : List α) (h : w.length = l.length) :
    placeL fill 0 w l = w := by
  simp only [placeL, List.take_zero, List.map_nil, List.nil_append, zero_add, h,
    List.drop_length, List.append_nil]

theorem placeL_zero_one {α : Type*} (fill a b : α) : placeL fill 0 [a] [b] = [a] :=
  placeL_zero_full fill [a] [b] rfl

variable {j t : ℕ} {ht : 1 ≤ t}

local notation "EA" => shoupBinField t ht

theorem ldBitsV_eq_bitsOf (v : Fin (D j) → (EA).carrier) :
    ldBitsV j t ht v = bitsOf ((EA).vecBits ((regs j).ptOf v), (EA).vecBits ((regs j).dirOf v),
      [(EA).toBits (v (regs j).coord)]) := by
  rw [ldBitsV, vecBits_regs]
  rfl

theorem seedOf_ldDesc (s : (EA).carrier) : seedOf (ldDesc j) [(EA).toBits s] = (EA).toBits s := by
  simp [seedOf, ldDesc]

theorem zeroed_one (a : BitStr) : zeroed (unary t) [a] = [(EA).toBits 0] := by
  simp only [zeroed, List.map_cons, List.map_nil, zb_eq ht]

theorem seedOut_ldDesc (τ : Ty) (s s' : (EA).carrier) :
    seedOut (unary t) (ldDesc j) (tyNat τ) ((EA).toBits s) [(EA).toBits s'] =
      [(EA).toBits (seedPart1 τ s)] := by
  unfold seedOut seedPart1
  cases τ
  · simp only [tyNat, ite_true]
    exact zeroed_one _
  · simp only [tyNat, show (1 : ℕ) ≠ 0 by decide, ite_false, reduceCtorEq, ldDesc, length_unary]
    exact placeL_zero_full _ _ _ rfl
  · simp only [tyNat, show (2 : ℕ) ≠ 0 by decide, ite_false, reduceCtorEq, ldDesc, length_unary]
    exact placeL_zero_full _ _ _ rfl

variable [NeZero (2 ^ j)] {hsz : 2 ^ j ∣ Fintype.card (shoupBinField t ht).carrier}
  (S : Sel (shoupBinField t ht).carrier (2 ^ j) hsz) (hjw : j ≤ t)
  (hχ : ∀ a, (S.χ a : ℕ) = (Introspection.SeedProgram.selector (shoupBinField t ht) j hjw a : ℕ))

include hjw hχ in
theorem selDirL_ldDesc (s : (EA).carrier) (w : Fin (2 ^ j) → (EA).carrier) :
    selDirL (unary t) (ldDesc j) ((EA).toBits s) ((EA).vecBits w) =
      (EA).vecBits (zeroBelow (S.χ s) w) :=
  selDirL_vecBits ht 0 (2 ^ j) j 0 S hjw hχ s w

include hjw hχ in
theorem ptMapL_ldDesc (τ : Ty) (s : (EA).carrier) (dir w : Fin (2 ^ j) → (EA).carrier) :
    ptMapL (unary t) (ldDesc j) (tyNat τ) ((EA).toBits s) ((EA).vecBits dir) ((EA).vecBits w) =
      (EA).vecBits (Regs.ptMap S τ s dir w) :=
  ptMapL_vecBits ht 0 (2 ^ j) j 0 S hjw hχ τ s dir w

include hjw hχ in
theorem ptOut_ldDesc (τ : Ty) (s : (EA).carrier) (dir pts : Fin (2 ^ j) → (EA).carrier) :
    ptOut (unary t) (ldDesc j) (tyNat τ) ((EA).toBits s) ((EA).vecBits dir) ((EA).vecBits pts) =
      (EA).vecBits (Regs.ptMap S τ s dir pts) := by
  have h0 : (ldDesc j).1.length = 0 := by simp [ldDesc]
  have h1 : (ldDesc j).2.1.length = 2 ^ j := by simp [ldDesc]
  rw [ptOut, h0, h1, sliceL_zero_full _ (BinField.length_vecBits _ _),
    ptMapL_ldDesc S hjw hχ]
  exact placeL_zero_full _ _ _ (by simp [BinField.length_vecBits])

include hjw hχ in
theorem dirOut_ldDesc (τ : Ty) (s : (EA).carrier) (dirs : Fin (2 ^ j) → (EA).carrier) :
    dirOut (unary t) (ldDesc j) (tyNat τ) ((EA).toBits s) ((EA).vecBits dirs) =
      (EA).vecBits (dirPart (2 ^ j) S τ s dirs) := by
  have h0 : (ldDesc j).1.length = 0 := by simp [ldDesc]
  have h1 : (ldDesc j).2.1.length = 2 ^ j := by simp [ldDesc]
  unfold dirOut dirPart
  cases τ
  · simp only [tyNat, show (0 : ℕ) ≠ 2 by decide, ite_false, reduceCtorEq]
    exact zeroed_vecBits ht _
  · simp only [tyNat, show (1 : ℕ) ≠ 2 by decide, ite_false, reduceCtorEq]
    exact zeroed_vecBits ht _
  · simp only [tyNat, ite_true]
    rw [h0, h1, sliceL_zero_full _ (BinField.length_vecBits _ _), selDirL_ldDesc S hjw hχ]
    exact placeL_zero_full _ _ _ (by simp [BinField.length_vecBits])

include hjw hχ in
/-- **The marginals of the one-copy test**, in bits. -/
theorem ldAnswer_marginal (τ : Ty) {lev : ℕ} (hl : 1 ≤ lev) (v : Fin (D j) → (EA).carrier)
    (y : BitStr) :
    ldAnswer (unary t) (ldDesc j) (tyNat τ) (unary (2 ^ j)) 1 lev (ldBitsV j t ht v) y =
      ldBitsV j t ht ((((regs j).pres S τ).truncate lev).eval v) := by
  have hc := comps1_marginal j S τ hl v
  simp only [comps1, Prod.mk.injEq] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  rw [ldBitsV_eq_bitsOf ((((regs j).pres S τ).truncate lev).eval v), h1, h2, h3]
  simp only [ldAnswer, ite_true, blocks1_ldBitsV, margL, seedOf_ldDesc]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    split_ifs with h3j
    · have h0 : (ldDesc j).1.length = 0 := by simp [ldDesc]
      have h1' : (ldDesc j).2.1.length = 2 ^ j := by simp [ldDesc]
      rw [h0, h1', sliceL_zero_full _ (BinField.length_vecBits _ _), selDirL_ldDesc S hjw hχ,
        ptOut_ldDesc S hjw hχ, dirPart_ptMap ht (2 ^ j) S]
    · exact zeroed_vecBits ht _
  · simp only
    split_ifs with h2j
    · exact dirOut_ldDesc S hjw hχ τ _ _
    · exact zeroed_vecBits ht _
  · exact seedOut_ldDesc τ _ _

include hjw hχ in
/-- **The stage maps of the one-copy test**, in bits. -/
theorem ldAnswer_linear (τ : Ty) {lev : ℕ} (hl : 1 ≤ lev) (u y : Fin (D j) → (EA).carrier) :
    ldAnswer (unary t) (ldDesc j) (tyNat τ) (unary (2 ^ j)) 2 lev (ldBitsV j t ht u)
        (ldBitsV j t ht y) =
      ldBitsV j t ht (((regs j).pres S τ).mapOfPrefix (lev - 1) u y) := by
  rw [ldBitsV_eq_bitsOf (((regs j).pres S τ).mapOfPrefix (lev - 1) u y)]
  simp only [ldAnswer, show (2 : ℕ) ≠ 1 by decide, ite_false, ite_true, blocks1_ldBitsV, linL]
  rcases (show lev = 1 ∨ lev = 2 ∨ lev = 3 ∨ 4 ≤ lev by omega) with rfl | rfl | rfl | h4
  · have hc := comps1_map_zero j S τ u y
    simp only [comps1, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [Nat.sub_self, h1, h2, h3, ite_true, seedOf_ldDesc, zeroed_vecBits ht,
      seedOut_ldDesc]
  · have hc := comps1_map_one j S τ u y
    simp only [comps1, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [show 2 - 1 = 1 from rfl, h1, h2, h3, show (2 : ℕ) ≠ 1 by decide, ite_false,
      ite_true, seedOf_ldDesc, zeroed_vecBits ht, dirOut_ldDesc S hjw hχ, zeroed_one (ht := ht)]
  · have hc := comps1_map_two j S τ u y
    simp only [comps1, Prod.mk.injEq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have h0 : (ldDesc j).1.length = 0 := by simp [ldDesc]
    have h1' : (ldDesc j).2.1.length = 2 ^ j := by simp [ldDesc]
    simp only [show 3 - 1 = 2 from rfl, h1, h2, h3, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, ite_false, ite_true, seedOf_ldDesc, zeroed_vecBits ht,
      zeroed_one (ht := ht), h0, h1', sliceL_zero_full _ (BinField.length_vecBits _ _),
      ptOut_ldDesc S hjw hχ]
  · rw [Regs.mapOfPrefix_three_le _ _ _ (by omega)]
    simp only [show lev ≠ 1 by omega, show lev ≠ 2 by omega, show lev ≠ 3 by omega, ite_false,
      zeroed_vecBits ht, zeroed_one (ht := ht), LinearMap.zero_apply]
    rfl

omit [NeZero (2 ^ j)] in
theorem pt_mem_sets (r : Fin (2 ^ j)) :
    (regs j).pt r ∉ (regs j).coordSet ∧ (regs j).pt r ∉ (regs j).dirSet ∧
      (regs j).pt r ∈ (regs j).finalSet := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_coordSet_regs]; change (r : ℕ) ≠ 2 * 2 ^ j; omega
  · rw [mem_dirSet_regs]; change ¬ (2 ^ j ≤ (r : ℕ) ∧ _); omega
  · rw [mem_finalSet_regs]; exact r.2

omit [NeZero (2 ^ j)] in
theorem dir_mem_sets (r : Fin (2 ^ j)) :
    (regs j).dir r ∉ (regs j).coordSet ∧ (regs j).dir r ∈ (regs j).dirSet ∧
      (regs j).dir r ∉ (regs j).finalSet := by
  refine ⟨?_, (regs j).dir_mem_dirSet r, ?_⟩
  · rw [mem_coordSet_regs]; change 2 ^ j + (r : ℕ) ≠ 2 * 2 ^ j; omega
  · rw [mem_finalSet_regs]; change ¬ (2 ^ j + (r : ℕ) < 2 ^ j); omega

omit [NeZero (2 ^ j)] in
theorem coord_mem_sets :
    (regs j).coord ∈ (regs j).coordSet ∧ (regs j).coord ∉ (regs j).dirSet ∧
      (regs j).coord ∉ (regs j).finalSet := by
  refine ⟨(regs j).coord_mem_coordSet, ?_, ?_⟩
  · rw [mem_dirSet_regs]; change ¬ (2 ^ j ≤ 2 * 2 ^ j ∧ 2 * 2 ^ j < 2 * 2 ^ j); omega
  · rw [mem_finalSet_regs]; change ¬ (2 * 2 ^ j < 2 ^ j); omega

/-- **The factor spaces of the one-copy test**, in indicator bits. -/
theorem ldAnswer_factor (τ : Ty) {lev : ℕ} (hl : 1 ≤ lev) (u : Fin (D j) → (EA).carrier)
    (y : BitStr) :
    ldAnswer (unary t) (ldDesc j) (tyNat τ) (unary (2 ^ j)) 3 lev (ldBitsV j t ht u) y =
      ldInd j t (((regs j).pres S τ).factorOfPrefix (lev - 1) u) := by
  rw [ldInd_eq_bitsOf]
  simp only [ldAnswer, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ite_false,
    ite_true, blocks1_ldBitsV, facL]
  have h0 : (ldDesc j).1.length = 0 := by simp [ldDesc]
  have h1 : (ldDesc j).2.1.length = 2 ^ j := by simp [ldDesc]
  have h3 : (ldDesc j).2.2.2.length = 0 := by simp [ldDesc]
  rcases (show lev = 1 ∨ lev = 2 ∨ lev = 3 ∨ 4 ≤ lev by omega) with rfl | rfl | rfl | h4
  · simp only [Nat.sub_self, Regs.factorOfPrefix_zero, ite_true, h3,
      fun r => (pt_mem_sets (j := j) r).1, fun r => (dir_mem_sets (j := j) r).1,
      coord_mem_sets.1, decide_false, decide_true, blk_eq]
    rw [placeL_zero_one]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · simp only [show 2 - 1 = 1 from rfl, Regs.factorOfPrefix_one, show (2 : ℕ) ≠ 1 by decide,
      ite_false, ite_true, h0, h1, fun r => (pt_mem_sets (j := j) r).2.1,
      fun r => (dir_mem_sets (j := j) r).2.1, coord_mem_sets.2.1, decide_false, decide_true,
      blk_eq, List.map_cons, List.map_nil]
    rw [placeL_zero_full _ _ _ (by simp [BinField.length_vecBits])]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · simp only [show 3 - 1 = 2 from rfl, Regs.factorOfPrefix_two, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, ite_false, ite_true, h0, h1, h3,
      fun r => (pt_mem_sets (j := j) r).2.2, fun r => (dir_mem_sets (j := j) r).2.2,
      coord_mem_sets.2.2, decide_false, decide_true, blk_eq]
    rw [placeL_zero_full _ _ _ (by simp [BinField.length_vecBits]), placeL_zero_one]
    simp only [List.map_const', BinField.length_vecBits, List.ofFn_const]
  · rw [Regs.factorOfPrefix_three_le _ _ _ (by omega)]
    simp only [show lev ≠ 1 by omega, show lev ≠ 2 by omega, show lev ≠ 3 by omega, ite_false,
      Finset.notMem_empty, decide_false, blk_eq, List.map_cons, List.map_nil,
      List.map_const', BinField.length_vecBits, List.ofFn_const]

end Answer

/-! ## The program -/

section Prog

/-- The three runs of the input's `u` or `y`, as a program. -/
def blocks1P (z : PolyTimeFun Input BitStr) : PolyTimeFun Input Blocks :=
  let n := ap₂ append mI (ap₂ append mI (const (unary 1)))
  let l := Introspection.BinaryBlock.splitBlocksProg.comp (n.pair (kI.pair z))
  (take.comp (l.pair mI)).pair ((take.comp ((drop.comp (l.pair mI)).pair mI)).pair
    (drop.comp ((drop.comp (l.pair mI)).pair mI)))

theorem blocks1P_apply (z : PolyTimeFun Input BitStr) (x : Input) :
    blocks1P z x = blocks1 (kI x) (mI x) (z x) := by
  simp only [blocks1P, blocks1, pair_apply, comp_apply, take_apply, drop_apply, ap₂_apply,
    append_apply, const_apply, Introspection.BinaryBlock.splitBlocksProg_apply,
    List.length_append, length_unary]

/-- **The program of the one-copy test.** -/
def ldProg : PolyTimeFun Input BitStr :=
  ite (isKind 1) (bitsP (margP (blocks1P uI)))
    (ite (isKind 2) (bitsP (linP (blocks1P uI) (blocks1P yI)))
      (ite (isKind 3) (bitsP (facP (blocks1P uI))) (const [])))

theorem ldProg_apply (k : Unary) (d : Desc) (τ : ℕ) (m' : Unary) (kind lev : ℕ) (u y : BitStr) :
    ldProg (k, d, τ, m', kind, lev, u, y) = ldAnswer k d τ m' kind lev u y := by
  simp only [ldProg, ldAnswer, PolyTimeFun.ite_apply, isKind, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, kindI, comp_apply, fst_apply, snd_apply, const_apply,
    decide_eq_true_eq, bitsP_apply, margP_apply, linP_apply, facP_apply, blocks1P_apply]
  rfl

/-- The field width, read off the parameters. -/
def kL : PolyTimeFun DirectInput Unary :=
  AnswerReduction.readU.comp (treeHead.comp AnswerReduction.pdI)
/-- The register length `M`, read off the parameters. -/
def mL : PolyTimeFun DirectInput Unary :=
  AnswerReduction.readU.comp (treeHead.comp (treeTail.comp AnswerReduction.pdI))
/-- The copy's description, read off the parameters. -/
def dL : PolyTimeFun DirectInput Desc :=
  AnswerReduction.readDesc.comp (treeTail.comp (treeTail.comp AnswerReduction.pdI))
/-- The test type's number, read off the type. -/
def τL : PolyTimeFun DirectInput ℕ := Detyping.Program.readNat.comp AnswerReduction.tagI

/-- The one-copy program's input, read off a direct query. -/
def ldAssemble : PolyTimeFun DirectInput Input :=
  kL.pair (dL.pair (τL.pair (mL.pair (AnswerReduction.kindA.pair (AnswerReduction.jA.pair
    (AnswerReduction.uA.pair AnswerReduction.yA))))))

/-- **The answer program** of the low-degree half: the one-copy program on the parameters. -/
def ldAnswerProg : PolyTimeFun DirectInput BitStr := ldProg.comp ldAssemble

/-- The dimension program: `(2M + 1) k` in unary. -/
def ldDimProg : PolyTimeFun Data Unary :=
  LowDegree.DegreeArithmetic.mulUnaryProg.comp
    ((ap₂ append (AnswerReduction.readU.comp (treeHead.comp treeTail)) (ap₂ append
      (AnswerReduction.readU.comp (treeHead.comp treeTail)) (const (unary 1)))).pair
      (AnswerReduction.readU.comp treeHead))

end Prog

/-! ## The low-degree half as a directly answered sampler -/

/-- **A family of parameters of the low-degree half**: the field width `t`, with `q = 2^t`, and
the selector width `j ≤ t`, with `M = 2^j` variables. -/
structure LdFamily where
  /-- The field width. -/
  t : ℕ → ℕ
  ht : ∀ n, 1 ≤ t n
  /-- The selector width, `log₂ M`. -/
  j : ℕ → ℕ
  hjt : ∀ n, j n ≤ t n

namespace LdFamily

variable (F : LdFamily) (n : ℕ)

theorem dvd : 2 ^ F.j n ∣ Fintype.card (Fq (F.t n) (F.ht n)) :=
  AnswerReduction.pow_dvd_card _ _ _ _ rfl (F.hjt n)

/-- The selector at index `n`: the high `j` bits of the seed. -/
def sel : LIDT.CL.Sel (Fq (F.t n) (F.ht n)) (2 ^ F.j n) (F.dvd n) :=
  AnswerReduction.powSel (F.t n) (F.ht n) (2 ^ F.j n) (F.j n) rfl (F.hjt n)

/-- The CL functions at index `n`: the presentation of the type, downsized and numbered. -/
def cl (τ : LIDT.CL.Ty) : CLFun 𝔽₂ (Fin (D (F.j n) * F.t n)) 3 :=
  ldCl (F.t n) (F.ht n) (F.sel n) τ

/-- **The parameters at index `n`**: `t` and `M` and the copy's description, in unary. -/
def pd : Data :=
  encode ((unary (F.t n), unary (2 ^ F.j n), ldDesc (F.j n)) : Unary × Unary × Desc)

theorem ldAnswerProg_apply (τ : LIDT.CL.Ty) (kind lev : ℕ) (u y : BitStr) :
    ldAnswerProg (F.pd n, encode τ, kind, lev, u, y) =
      ldAnswer (unary (F.t n)) (ldDesc (F.j n)) (tyNat τ) (unary (2 ^ F.j n)) kind lev u y := by
  rw [ldAnswerProg, comp_apply, ← ldProg_apply]
  congr 1
  have hτ : Detyping.Program.readNat (encode τ) = tyNat τ :=
    Detyping.Program.readNat_encode (tyNat τ)
  simp only [ldAssemble, pair_apply, kL, mL, dL, τL, AnswerReduction.pdI, AnswerReduction.tagI,
    AnswerReduction.kindA, AnswerReduction.jA, AnswerReduction.uA, AnswerReduction.yA,
    comp_apply, fst_apply, snd_apply, pd, encode_prod, treeHead_cons, treeTail_cons,
    AnswerReduction.readU_encode, AnswerReduction.readDesc_encode, hτ]

theorem ldDimProg_pd : (ldDimProg (F.pd n)).length = D (F.j n) * F.t n := by
  simp only [ldDimProg, comp_apply, pair_apply, ap₂_apply, append_apply, const_apply, pd,
    encode_prod, treeHead_cons, treeTail_cons, AnswerReduction.readU_encode,
    LowDegree.DegreeArithmetic.mulUnaryProg_apply, length_unary, List.length_append, D]
  ring

theorem exists_ldBitsV_of_toBits {lev : ℕ} (τ : LIDT.CL.Ty)
    (x : Fin (D (F.j n) * F.t n) → 𝔽₂) :
    ∃ u, CL.toBits (((F.cl n τ).truncate lev).eval x) = ldBitsV (F.j n) (F.t n) (F.ht n) u :=
  exists_ldBitsV _ _ _ (length_toBits _)

/-- **The low-degree half of the answer-reduced sampler**, directly answered, given a routine
computing its parameters. -/
def directSampler (pp : Prog) (hpp : pp.WellScoped 1)
    (hruns : ∀ n, ∃ t, pp.Runs (encode n) (F.pd n) t) : DirectSampler 3 LIDT.CL.Ty where
  parProg := pp
  parProg_closed := hpp
  pd := F.pd
  parProg_runs := hruns
  dim n := D (F.j n) * F.t n
  cl := F.cl
  cl_exactlyOn n τ := ldCl_exactlyOn (F.sel n) τ
  dimProg := ldDimProg
  dimProg_eq := F.ldDimProg_pd
  answer := ldAnswerProg
  answer_marginal n τ lev z hl hz := by
    obtain ⟨v, rfl⟩ := exists_ldBitsV (F.j n) (F.t n) (F.ht n) hz
    rw [F.ldAnswerProg_apply n τ, ldAnswer_marginal (F.sel n) (F.hjt n)
      (AnswerReduction.powSel_χ _ _ _ _ _ _) τ hl v]
    exact (toBits_eval_truncate_ldCl (F.sel n) τ lev v).symm
  answer_linear n τ lev u y hl hu hy := by
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨u', hu'⟩ := F.exists_ldBitsV_of_toBits n (lev := lev - 1) τ x
    obtain ⟨y', rfl⟩ := exists_ldBitsV (F.j n) (F.t n) (F.ht n) hy
    rw [hu', F.ldAnswerProg_apply n τ, ldAnswer_linear (F.sel n) (F.hjt n)
      (AnswerReduction.powSel_χ _ _ _ _ _ _) τ hl u' y']
    exact (toBits_mapOfPrefix_ldCl (F.sel n) τ (lev - 1) u' y').symm
  answer_factor n τ lev u hl hu := by
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨u', hu'⟩ := F.exists_ldBitsV_of_toBits n (lev := lev - 1) τ x
    rw [hu', F.ldAnswerProg_apply n τ, ldAnswer_factor (F.sel n) τ hl u']
    exact (indicatorBits_factorOfPrefix_ldCl (F.sel n) τ (lev - 1) u').symm

end LdFamily

end MIPRE.Tailored.AnsRed.Typed

end
