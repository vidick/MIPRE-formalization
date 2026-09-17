/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.AnsEnd
import Mathlib.Data.Nat.Bitwise

/-!
# The canonical index of a tableau variable

`idxOf e G T v` is the index of the variable `v` in the described 3SAT formula: the *answer
index* `j < 4T` for a cell of one of the two free tapes inside the answer block — tape `5`
for `j < 2T` and tape `6` otherwise, position `r / 2 + 3` for `r = j mod 2T`, the value `1`
for `r` odd and the blank for `r` even — and the structured index (`encodeVar`) for every
other variable. So the first `4T` variables of the formula are exactly the two answer blocks,
which is what item 1 of `thm:succinct-sat` needs, and `decodeVar_fieldsOf_idxOf` says that
decoding the canonical index returns the variable. `decodeVar_ans` is the other half: every
index below `4T` decodes to the answer variable it stands for
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Reading an index built from a number -/

theorem getD_bitsOfNat {w : ℕ} (n : ℕ) {i : ℕ} (hi : i < w) :
    (bitsOfNat w n).getD i false = n.testBit i := by
  rw [bitsOfNat, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl

theorem bitField_bitsOfNat_zero (w n k : ℕ) (hk : k ≤ w) :
    bitField (bitsOfNat w n) 0 k = n % 2 ^ k := by
  rw [bitField, List.drop_zero, bitsVal_take, bitsVal_bitsOfNat,
    Nat.mod_mod_of_dvd n (pow_dvd_pow 2 hk)]

/-! ## The answer variables -/

variable (e G T : ℕ)

/-- The offset of an answer index inside its block. -/
def rOf (j : ℕ) : ℕ := if j < 2 * T then j else j - 2 * T

/-- The tape code of an answer index: `5` for the first block, `6` for the second. -/
def tapeIdx (j : ℕ) : ℕ := if j < 2 * T then 5 else 6

/-- The cell value of an answer index: `1` for an odd offset, the blank for an even one. -/
def valOf (j : ℕ) : CellVal Sym := if rOf T j % 2 = 1 then .sym .one else .blank

theorem tapeIdx_lt (j : ℕ) : tapeIdx T j < 7 := by unfold tapeIdx; split_ifs <;> omega

theorem symCode_valOf (j : ℕ) : symCode (valOf T j) = if rOf T j % 2 = 1 then 1 else 5 := by
  unfold valOf; split_ifs <;> rfl

theorem rOf_lt (j : ℕ) (hj : j < 4 * T) : rOf T j < 2 * T := by
  unfold rOf; split_ifs <;> omega

/-- `4T` fits below the flag bit. -/
theorem four_T_le_flag (hT : T ≤ Sof e) : 4 * T ≤ 2 ^ flagOff e G := by
  have h1 : (4 : ℕ) * 2 ^ e = 2 ^ (e + 2) := by rw [pow_add]; ring
  have h2 : (2 : ℕ) ^ (e + 2) ≤ 2 ^ flagOff e G :=
    Nat.pow_le_pow_right (by omega) (by unfold flagOff W; omega)
  have h3 : 4 * T ≤ 4 * 2 ^ e := by
    have : T ≤ 2 ^ e := by rw [Sof] at hT; exact hT
    omega
  omega

theorem flag_lt_m : flagOff e G < mOf e G := by unfold flagOff mOf; omega

/-- **Every index below `4T` decodes to the answer variable it stands for.** -/
theorem decodeVar_ans (hT : T ≤ Sof e) {j : ℕ} (hj : j < 4 * T) :
    ∃ (jt : Fin 7) (p : Pos (Sof e)), (jt : ℕ) = tapeIdx T j ∧ (p : ℕ) = rOf T j / 2 + 3 ∧
      decodeVar e G (fieldsOf e G T (bitsOfNat (mOf e G) j)) =
        some (.cell 0 (.inl jt) p (valOf T j)) := by
  have hfl := four_T_le_flag e G T hT
  have hflm := flag_lt_m e G
  have hW := numCells_lt_two_pow_W e
  have hr : rOf T j < 2 * T := rOf_lt T j hj
  have hrd : rOf T j / 2 ≤ Sof e := by omega
  have hnc : numCells (Sof e) = 2 * Sof e + 7 := rfl
  -- the flag bit is clear
  have hflag : (bitsOfNat (mOf e G) j).getD (flagOff e G) false = false := by
    rw [getD_bitsOfNat _ hflm]
    exact Nat.testBit_eq_false_of_lt (by omega : j < 2 ^ flagOff e G)
  -- the value of the low bits
  have hj' : bitField (bitsOfNat (mOf e G) j) 0 (flagOff e G) = j := by
    rw [bitField_bitsOfNat_zero _ _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
  -- the fields
  have hF : fieldsOf e G T (bitsOfNat (mOf e G) j) =
      { flag := false, tag := 0, t := 0, d := tapeIdx T j, p := (rOf T j / 2 + 3) % 2 ^ W e,
        v := if rOf T j % 2 = 1 then 1 else 5, q := 0, js := fun _ => 0, g := 0,
        ansOk := decide (j < 4 * T) } := by
    simp only [fieldsOf, hflag, Bool.false_eq_true, if_false, hj', rOf, tapeIdx]
    rfl
  have hp : (rOf T j / 2 + 3) % 2 ^ W e = rOf T j / 2 + 3 := Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨tapeIdx T j, tapeIdx_lt T j⟩, ⟨rOf T j / 2 + 3, by omega⟩, rfl, rfl, ?_⟩
  rw [hF]
  simp only [decodeVar, Bool.false_eq_true, if_false, hp]
  rw [if_pos ⟨by simp [hj], trivial, trivial⟩, dif_pos ⟨tapeIdx_lt T j, by omega⟩]
  have hv : symOfCode (if rOf T j % 2 = 1 then 1 else 5) = some (valOf T j) := by
    unfold valOf
    split_ifs <;> rfl
  rw [hv]

/-! ## The canonical index -/

/-- The cell is an *answer cell*: at time `0` on a free tape, inside the answer block, holding
`1` or the blank. -/
def IsAnsCell (T : ℕ) (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym) :
    Prop :=
  (t : ℕ) = 0 ∧ (tapeCode d = 5 ∨ tapeCode d = 6) ∧ 3 ≤ (p : ℕ) ∧ (p : ℕ) - 3 < T ∧
    (v = .blank ∨ v = .sym .one)

instance (T : ℕ) (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym) :
    Decidable (IsAnsCell e T t d p v) := by unfold IsAnsCell; infer_instance

/-- The answer index of an answer cell. -/
def ansIdx (T : ℕ) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym) : ℕ :=
  (if tapeCode d = 5 then 0 else 2 * T) + 2 * ((p : ℕ) - 3) + (if v = .sym .one then 1 else 0)

/-- The canonical index of a tableau variable: the answer index for an answer cell, the
structured index (`encodeVar`) otherwise. -/
noncomputable def idxOf : TabVar 7 6 Sym Ctl (Sof e) G → ℕ
  | .cell t d p v =>
      if IsAnsCell e T t d p v then ansIdx e T d p v else bitsVal (encodeVar e G (.cell t d p v))
  | .head t d p => bitsVal (encodeVar e G (.head t d p))
  | .state t q => bitsVal (encodeVar e G (.state t q))
  | .emitOne t => bitsVal (encodeVar e G (.emitOne t))
  | .emitBad t => bitsVal (encodeVar e G (.emitBad t))
  | .emitted t => bitsVal (encodeVar e G (.emitted t))
  | .aux t js g => bitsVal (encodeVar e G (.aux t js g))

theorem bitsVal_encodeVar_lt (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    bitsVal (encodeVar e G v) < 2 ^ mOf e G := by
  have := bitsVal_lt (encodeVar e G v)
  rwa [length_encodeVar] at this

theorem ansIdx_lt (hT : T ≤ Sof e) {t : Fin (Sof e + 1)} {d : Tape 7 6} {p : Pos (Sof e)}
    {v : CellVal Sym} (h : IsAnsCell e T t d p v) : ansIdx e T d p v < 4 * T := by
  obtain ⟨-, -, -, hpT, -⟩ := h
  unfold ansIdx
  split_ifs <;> omega

theorem idxOf_lt (hT : T ≤ Sof e) (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    idxOf e G T v < 2 ^ mOf e G := by
  have hfl := four_T_le_flag e G T hT
  have h2 : (2 : ℕ) ^ flagOff e G < 2 ^ mOf e G :=
    Nat.pow_lt_pow_right (by omega) (flag_lt_m e G)
  cases v with
  | cell t d p v =>
    rw [idxOf]
    split_ifs with h
    · have := ansIdx_lt e T hT h
      omega
    · exact bitsVal_encodeVar_lt e G _
  | head t d p => exact bitsVal_encodeVar_lt e G _
  | state t q => exact bitsVal_encodeVar_lt e G _
  | emitOne t => exact bitsVal_encodeVar_lt e G _
  | emitBad t => exact bitsVal_encodeVar_lt e G _
  | emitted t => exact bitsVal_encodeVar_lt e G _
  | aux t js g => exact bitsVal_encodeVar_lt e G _

theorem decodeVar_fieldsOf_bitsVal (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    decodeVar e G (fieldsOf e G T (bitsOfNat (mOf e G) (bitsVal (encodeVar e G v)))) = some v := by
  rw [show mOf e G = (encodeVar e G v).length from (length_encodeVar e G v).symm,
    bitsOfNat_bitsVal, decodeVar_encodeVar]

/-- **Decoding the canonical index returns the variable.** -/
theorem decodeVar_fieldsOf_idxOf (hT : T ≤ Sof e) (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    decodeVar e G (fieldsOf e G T (bitsOfNat (mOf e G) (idxOf e G T v))) = some v := by
  cases v with
  | cell t d p v =>
    rw [idxOf]
    split_ifs with h
    · obtain ⟨ht, hd, hp3, hpT, hv⟩ := h
      have hj : ansIdx e T d p v < 4 * T := ansIdx_lt e T hT ⟨ht, hd, hp3, hpT, hv⟩
      obtain ⟨jt, p', hjt, hp', hdec⟩ := decodeVar_ans e G T hT hj
      rw [hdec]
      have hpar : (if v = CellVal.sym Sym.one then 1 else 0) < 2 := by split_ifs <;> omega
      have hlt : (ansIdx e T d p v < 2 * T) ↔ tapeCode d = 5 := by
        unfold ansIdx
        constructor
        · intro hle
          by_contra hne
          rw [if_neg hne] at hle
          omega
        · intro h5
          rw [if_pos h5]
          omega
      have hr : rOf T (ansIdx e T d p v) = 2 * ((p : ℕ) - 3) +
          (if v = CellVal.sym Sym.one then 1 else 0) := by
        unfold rOf
        by_cases h5 : tapeCode d = 5
        · rw [if_pos (hlt.mpr h5)]
          unfold ansIdx
          rw [if_pos h5]
          omega
        · rw [if_neg (by simp only [hlt]; exact h5)]
          unfold ansIdx
          rw [if_neg h5]
          omega
      have hti : tapeIdx T (ansIdx e T d p v) = tapeCode d := by
        unfold tapeIdx
        by_cases h5 : tapeCode d = 5
        · rw [if_pos (hlt.mpr h5), h5]
        · rw [if_neg (by simp only [hlt]; exact h5)]
          rcases hd with h | h
          · exact absurd h h5
          · exact h.symm
      have hd' : (.inl jt : Tape 7 6) = d := by
        have hjt' : (jt : ℕ) = tapeCode d := by rw [hjt, hti]
        rw [tape_eq_inl_of_lt d (by rw [← hjt']; exact jt.isLt)]
        congr 1
        exact Fin.ext hjt'
      have hp'' : p' = p := by
        apply Fin.ext
        rw [hp', hr]
        omega
      have hvv : valOf T (ansIdx e T d p v) = v := by
        unfold valOf
        rw [hr]
        rcases hv with rfl | rfl
        · rw [if_neg (by simp)]
        · rw [if_pos (by simp)]
      have ht0 : (0 : Fin (Sof e + 1)) = t := Fin.ext (by simp [ht])
      rw [hd', hp'', hvv, ht0]
    · exact decodeVar_fieldsOf_bitsVal e G T _
  | head t d p => exact decodeVar_fieldsOf_bitsVal e G T _
  | state t q => exact decodeVar_fieldsOf_bitsVal e G T _
  | emitOne t => exact decodeVar_fieldsOf_bitsVal e G T _
  | emitBad t => exact decodeVar_fieldsOf_bitsVal e G T _
  | emitted t => exact decodeVar_fieldsOf_bitsVal e G T _
  | aux t js g => exact decodeVar_fieldsOf_bitsVal e G T _

/-- The canonical index of the answer variable of `j` is `j`. -/
theorem idxOf_ans (hT : T ≤ Sof e) {j : ℕ} (hj : j < 4 * T) {jt : Fin 7} {p : Pos (Sof e)}
    (hjt : (jt : ℕ) = tapeIdx T j) (hp : (p : ℕ) = rOf T j / 2 + 3) :
    idxOf e G T (.cell 0 (.inl jt) p (valOf T j)) = j := by
  have hr : rOf T j < 2 * T := rOf_lt T j hj
  have hti : tapeCode (.inl jt : Tape 7 6) = tapeIdx T j := by rw [tapeCode_inl]; exact hjt
  have hvone : (valOf T j = CellVal.sym Sym.one) ↔ rOf T j % 2 = 1 := by
    unfold valOf
    split_ifs with h
    · simp [h]
    · simp [h]
  have hcond : IsAnsCell e T 0 (.inl jt) p (valOf T j) := by
    refine ⟨by simp, ?_, by omega, by omega, ?_⟩
    · rw [hti]
      unfold tapeIdx
      split_ifs <;> simp
    · unfold valOf
      split_ifs <;> simp
  rw [idxOf, if_pos hcond, ansIdx, hti, hp]
  by_cases hlt : j < 2 * T
  · have h5 : tapeIdx T j = 5 := by unfold tapeIdx; rw [if_pos hlt]
    have hrj : rOf T j = j := by unfold rOf; rw [if_pos hlt]
    rw [if_pos h5, hrj]
    by_cases hodd : j % 2 = 1
    · rw [if_pos (hvone.mpr (by rw [hrj]; exact hodd))]
      omega
    · rw [if_neg (by rw [hvone, hrj]; exact hodd)]
      omega
  · have h6 : tapeIdx T j = 6 := by unfold tapeIdx; rw [if_neg hlt]
    have hrj : rOf T j = j - 2 * T := by unfold rOf; rw [if_neg hlt]
    rw [if_neg (by rw [h6]; omega), hrj]
    by_cases hodd : (j - 2 * T) % 2 = 1
    · rw [if_pos (hvone.mpr (by rw [hrj]; exact hodd))]
      omega
    · rw [if_neg (by rw [hvone, hrj]; exact hodd)]
      omega

end MIPRE.TM.CookLevin.Desc
