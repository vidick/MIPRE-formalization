/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.PcpPresentation
import MIPRE.Background.LIDT.PresentationQueries
import MIPRE.Foundations.CL.Downsize
import MIPRE.Foundations.SAT.FieldCoordinates

/-!
# The layout of the PCP coordinates

Piece AR-3d of `planning/answer-reduction.md`: how a program reads a vector of `V^pcp`.

* The coordinates are numbered in three runs (`coordIndex`): the concatenated point register
  `V_{6,pt}` (`pt6`, `m'` coordinates), the concatenated direction register `V_{6,dir}` (`dir6`),
  and the six seeds. A vector of `V^pcp` is thus the three lists `ptOf6`, `dirOf6`, `seedsOf`.
* Each copy of the test is a contiguous run of `V_{6,pt}` and of `V_{6,dir}` with its own seed
  (`regsAt`): copy `i ≤ 5` at offset `i·m` and length `m` (`regs_eq`), copy `6` at offset `0` and
  length `m'` (`regs6_eq`).
* The bits of the downsized vector, numbered by `bitIndex`, are the field elements' Shoup bits in
  that order (`toBits_pcp`), so a program reads them by cutting `k`-bit blocks.
-/

noncomputable section

namespace MIPRE.AnswerReduction.Pcp

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL Cost

variable (P : PcpParams)

/-! ## The concatenated registers -/

theorem dir6_block (i : Fin 5) (j : Fin P.m) :
    dir6 P ⟨i * P.m + j, by
      have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
      have h2 : (j : ℕ) < P.m := j.isLt
      simp only [PcpParams.m']
      omega⟩ = .dir i j := by
  have hj : (j : ℕ) < P.m := j.isLt
  have hi : (i : ℕ) < 5 := i.isLt
  have hlt : (i : ℕ) * P.m + j < 5 * P.m := by nlinarith
  have hm : 0 < P.m := by omega
  simp only [dir6, dif_pos hlt]
  congr 1
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_div_left _ _ hm,
      Nat.div_eq_of_lt hj, zero_add]
  · apply Fin.ext
    simp only
    rw [show (i : ℕ) * P.m + j = j + P.m * i by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj]

theorem pt6_aux (j : Fin (5 + P.s)) :
    pt6 P ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩ = .auxPt j := by
  simp only [pt6, show ¬ (5 * P.m + (j : ℕ) < 5 * P.m) by omega, dif_neg, not_false_eq_true]
  congr 1
  exact Fin.ext (by simp)

theorem dir6_aux (j : Fin (5 + P.s)) :
    dir6 P ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩ = .auxDir j := by
  simp only [dir6, show ¬ (5 * P.m + (j : ℕ) < 5 * P.m) by omega, dif_neg, not_false_eq_true]
  congr 1
  exact Fin.ext (by simp)

theorem pt6_ne_coord (r : Fin P.m') (c : Fin 6) : pt6 P r ≠ .coord c := by
  unfold pt6; split_ifs <;> simp

theorem dir6_ne_coord (r : Fin P.m') (c : Fin 6) : dir6 P r ≠ .coord c := by
  unfold dir6; split_ifs <;> simp

/-! ## A copy of the test as a run of the concatenated registers -/

/-- The registers of a copy at offset `o` and length `sz` of the concatenated registers, with
the seed `c`. -/
def regsAt (o sz : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') : Regs (Coord P) sz where
  pt j := pt6 P ⟨o + j, by omega⟩
  dir j := dir6 P ⟨o + j, by omega⟩
  coord := .coord c
  pt_injective a b hab := by
    have := pt6_injective P hab
    exact Fin.ext (by simpa using this)
  dir_injective a b hab := by
    have := dir6_injective P hab
    exact Fin.ext (by simpa using this)
  pt_ne_dir _ _ hab := (regs6 P).pt_ne_dir _ _ hab
  pt_ne_coord _ := pt6_ne_coord P _ c
  dir_ne_coord _ := dir6_ne_coord P _ c

theorem regs_le (i : Fin 5) : (i : ℕ) * P.m + P.m ≤ P.m' := by
  have := i.isLt
  have : (i : ℕ) * P.m + P.m ≤ 5 * P.m := by nlinarith
  simp only [PcpParams.m']
  omega

theorem regs_eq (i : Fin 5) : regs P i = regsAt P (i * P.m) P.m i.castSucc (regs_le P i) := by
  unfold regs regsAt
  congr 1
  · funext j; exact (pt6_block P i j).symm
  · funext j; exact (dir6_block P i j).symm

theorem regs6_eq : regs6 P = regsAt P 0 P.m' 5 (by simp) := by
  simp only [regs6, regsAt, Regs.mk.injEq, zero_add]

/-! ## The three runs -/

variable {F : Type*}

/-- The concatenated point register of a vector. -/
def ptOf6 (x : Coord P → F) : Fin P.m' → F := fun r => x (pt6 P r)

/-- The concatenated direction register of a vector. -/
def dirOf6 (x : Coord P → F) : Fin P.m' → F := fun r => x (dir6 P r)

/-- The six seeds of a vector. -/
def seedsOf (x : Coord P → F) : Fin 6 → F := fun c => x (.coord c)

/-- The three runs of the coordinates. -/
def layout : Coord P ≃ Fin P.m' ⊕ Fin P.m' ⊕ Fin 6 where
  toFun
    | .pt i j => .inl ⟨i * P.m + j, by have := regs_le P i; have := j.isLt; omega⟩
    | .dir i j => .inr (.inl ⟨i * P.m + j, by have := regs_le P i; have := j.isLt; omega⟩)
    | .coord c => .inr (.inr c)
    | .auxPt j => .inl ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩
    | .auxDir j => .inr (.inl ⟨5 * P.m + j, by have := j.isLt; simp only [PcpParams.m']; omega⟩)
  invFun
    | .inl r => pt6 P r
    | .inr (.inl r) => dir6 P r
    | .inr (.inr c) => .coord c
  left_inv c := by
    cases c with
    | pt i j => exact pt6_block P i j
    | dir i j => exact dir6_block P i j
    | coord c => rfl
    | auxPt j => exact pt6_aux P j
    | auxDir j => exact dir6_aux P j
  right_inv c := by
    rcases c with r | r | c
    · simp only [pt6]
      split_ifs with h
      · simp only [Sum.inl.injEq]
        exact Fin.ext (by simp only; rw [Nat.mul_comm]; exact Nat.div_add_mod _ _)
      · simp only [Sum.inl.injEq]
        exact Fin.ext (by simp only; omega)
    · simp only [dir6]
      split_ifs with h
      · simp only [Sum.inr.injEq, Sum.inl.injEq]
        exact Fin.ext (by simp only; rw [Nat.mul_comm]; exact Nat.div_add_mod _ _)
      · simp only [Sum.inr.injEq, Sum.inl.injEq]
        exact Fin.ext (by simp only; omega)
    · rfl

/-- The number of coordinates of `V^pcp`, in the three runs. -/
abbrev pcpDim : ℕ := P.m' + (P.m' + 6)

theorem pcpDim_eq : pcpDim P = 10 * P.m + 2 * P.s + 16 := by
  simp only [pcpDim, PcpParams.m']; ring

/-- The numbering of the coordinates: `V_{6,pt}`, then `V_{6,dir}`, then the seeds. -/
def coordIndex : Coord P ≃ Fin (pcpDim P) :=
  (layout P).trans ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)

theorem layout_pt6 (r : Fin P.m') : layout P (pt6 P r) = .inl r :=
  (layout P).apply_symm_apply (.inl r)

theorem layout_dir6 (r : Fin P.m') : layout P (dir6 P r) = .inr (.inl r) :=
  (layout P).apply_symm_apply (.inr (.inl r))

theorem layout_coord (c : Fin 6) : layout P (.coord c) = .inr (.inr c) := rfl

@[simp] theorem coordIndex_symm_castAdd (r : Fin P.m') :
    (coordIndex P).symm (Fin.castAdd (P.m' + 6) r) = pt6 P r := by
  rw [Equiv.symm_apply_eq]
  simp [coordIndex, layout_pt6]

@[simp] theorem coordIndex_symm_natAdd_castAdd (r : Fin P.m') :
    (coordIndex P).symm (Fin.natAdd P.m' (Fin.castAdd 6 r)) = dir6 P r := by
  rw [Equiv.symm_apply_eq]
  simp [coordIndex, layout_dir6]

@[simp] theorem coordIndex_symm_natAdd_natAdd (c : Fin 6) :
    (coordIndex P).symm (Fin.natAdd P.m' (Fin.natAdd P.m' c)) = .coord c := by
  rw [Equiv.symm_apply_eq]
  simp [coordIndex, layout_coord]

/-- **Reading a vector in the numbering** is reading its three runs. -/
theorem ofFn_coordIndex {α : Type*} (g : Coord P → α) :
    List.ofFn (fun r => g ((coordIndex P).symm r)) =
      List.ofFn (fun r => g (pt6 P r)) ++ List.ofFn (fun r => g (dir6 P r)) ++
        List.ofFn (fun c => g (.coord c)) := by
  change List.ofFn (fun r : Fin (P.m' + (P.m' + 6)) => g ((coordIndex P).symm r)) = _
  rw [List.ofFn_add, List.ofFn_add]
  simp only [List.append_assoc]
  congr 1
  · congr 1; funext i; exact congrArg g (coordIndex_symm_castAdd P i)
  · congr 1
    · congr 1; funext i; exact congrArg g (coordIndex_symm_natAdd_castAdd P i)
    · congr 1; funext i; exact congrArg g (coordIndex_symm_natAdd_natAdd P i)

/-! ## The bits of a downsized vector -/

variable {k : ℕ} (hk : 1 ≤ k)

/-- The numbering of the bits: coordinate by coordinate, `k` bits each. -/
def bitIndex (k : ℕ) : Coord P × Fin k ≃ Fin (pcpDim P * k) :=
  ((coordIndex P).prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- The Shoup bits of a vector of `V^pcp`, in the numbering. -/
def flatBits (v : Coord P → (shoupBinField k hk).carrier) : BitStr :=
  ((shoupBinField k hk).vecBits fun r => v ((coordIndex P).symm r)).flatten

theorem vecBits_coordIndex (v : Coord P → (shoupBinField k hk).carrier) :
    (shoupBinField k hk).vecBits (fun r => v ((coordIndex P).symm r)) =
      (shoupBinField k hk).vecBits (ptOf6 P v) ++ (shoupBinField k hk).vecBits (dirOf6 P v) ++
        (shoupBinField k hk).vecBits (seedsOf P v) := by
  simp only [BinField.vecBits]
  rw [← List.map_append, ← List.map_append, ofFn_coordIndex]
  rfl

theorem repr_shoup (a : (shoupBinField k hk).carrier) :
    (List.ofFn fun j : Fin k => decide ((shoupPowerBasis k hk).repr a j = 1)) =
      (shoupBinField k hk).toBits a := by
  rw [← shoupCoordinateEquiv_encoding]
  simp only [shoupPowerBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem bitIndex_symm (r : Fin (pcpDim P)) (j : Fin k) (h : (r : ℕ) * k + j < pcpDim P * k) :
    (bitIndex P k).symm ⟨r * k + j, h⟩ = ((coordIndex P).symm r, j) := by
  rw [Equiv.symm_apply_eq]
  simp only [bitIndex, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.apply_symm_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq]
  exact Fin.ext (by simp [finProdFinEquiv]; ring)

/-- **The bits of the downsized vector** are its coordinates' Shoup bits, in the numbering. -/
theorem toBits_pcp (v : Coord P → (shoupBinField k hk).carrier) :
    toBits (reindexEquiv (bitIndex P k) (downsizeEquiv (shoupPowerBasis k hk) v)) =
      flatBits P hk v := by
  simp only [toBits, flatBits, BinField.vecBits]
  rw [List.ofFn_mul, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  simp only [Function.comp_apply]
  rw [← repr_shoup]
  congr 1
  funext j
  rw [reindexEquiv_apply, bitIndex_symm, downsizeEquiv_apply]

theorem length_flatBits (v : Coord P → (shoupBinField k hk).carrier) :
    (flatBits P hk v).length = pcpDim P * k := by
  have h := congrArg (List.length (α := Bool)) (toBits_pcp P hk v)
  rw [length_toBits] at h
  exact h.symm

/-- Every bit string of the right length is the bits of a vector of `V^pcp`. -/
theorem exists_flatBits {z : BitStr} (hz : z.length = pcpDim P * k) :
    ∃ v : Coord P → (shoupBinField k hk).carrier, z = flatBits P hk v := by
  refine ⟨(downsizeEquiv (shoupPowerBasis k hk)).symm
    ((reindexEquiv (bitIndex P k)).symm (ofBits _ z)), ?_⟩
  rw [← toBits_pcp, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, toBits_ofBits hz]

end MIPRE.AnswerReduction.Pcp

end
