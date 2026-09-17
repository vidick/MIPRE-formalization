/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Layout

/-!
# The fields of a literal, as formulas

For a literal whose `m` index bits are the input bits `b .. b + m`, the formulas computing
its fields (`litFields`): the flag, the structured fields as slices of the input, and the
answer decoding (`j < 2T`, `r = j` or `j - 2T`, `p = r / 2 + 3`, `v` from the parity of
`r`), multiplexed by the flag. `evalFields_litFields` says that they compute exactly
`fieldsOf` on the index (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open SAT Cost Fml

/-! ## Input slices -/

/-- The input bits `b .. b + m` as a bit string. -/
def ibOf (b m : ℕ) (x : ℕ → Bool) : BitStr := (List.range' b m).map x

@[simp] theorem length_ibOf (b m : ℕ) (x : ℕ → Bool) : (ibOf b m x).length = m := by simp [ibOf]

theorem range'_drop_take (s n off w : ℕ) (h : off + w ≤ n) :
    ((List.range' s n).drop off).take w = List.range' (s + off) w := by
  have h1 : List.range' s n = List.range' s off ++ List.range' (s + off) (n - off) := by
    rw [List.range'_append_1, Nat.add_sub_cancel' (by omega)]
  have h2 : List.range' (s + off) (n - off) = List.range' (s + off) w ++ List.range' (s + off + w) (n - off - w) := by
    rw [List.range'_append_1, Nat.add_sub_cancel' (by omega)]
  rw [h1, List.drop_left' (by simp), h2, List.take_left' (by simp)]

theorem bitsOf_field_ibOf (b m off w : ℕ) (h : off + w ≤ m) (x : ℕ → Bool) :
    bitsOf (field (b + off) w) x = ((ibOf b m x).drop off).take w := by
  rw [bitsOf_field, ibOf, ← List.map_drop, ← List.map_take, range'_drop_take _ _ _ _ h]

theorem val_field_ibOf (b m off w : ℕ) (h : off + w ≤ m) (x : ℕ → Bool) :
    val (field (b + off) w) x = bitField (ibOf b m x) off w := by
  rw [val, bitsOf_field_ibOf b m off w h]; rfl

theorem getD_ibOf (b m i : ℕ) (h : i < m) (x : ℕ → Bool) : (ibOf b m x).getD i false = x (b + i) := by
  rw [ibOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range' (by simpa using h)]
  simp

/-! ## Multiplexed fields and constants -/

/-- `if s then as else bs`, bitwise. -/
def muxList (s : Fml) (as bs : List Fml) : List Fml := List.zipWith (mux s) as bs

theorem length_muxList (s : Fml) (as bs : List Fml) (h : as.length = bs.length) :
    (muxList s as bs).length = as.length := by
  simp [muxList, h]

theorem bitsOf_muxList (s : Fml) (as bs : List Fml) (h : as.length = bs.length) (x : ℕ → Bool) :
    bitsOf (muxList s as bs) x = if s.eval x then bitsOf as x else bitsOf bs x := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => simp [muxList]
    | cons _ _ => simp at h
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [muxList, List.zipWith_cons_cons, bitsOf_cons, eval_mux]
      rw [show List.zipWith (mux s) as bs = muxList s as bs from rfl, ih bs h]
      split <;> rfl

theorem val_muxList (s : Fml) (as bs : List Fml) (h : as.length = bs.length) (x : ℕ → Bool) :
    val (muxList s as bs) x = if s.eval x then val as x else val bs x := by
  rw [val, bitsOf_muxList s as bs h]; split <;> rfl

/-- The constant `c` on `w` bits. -/
def cst (w c : ℕ) : List Fml := constBits (nbits w c)

@[simp] theorem length_cst (w c : ℕ) : (cst w c).length = w := by simp [cst]

theorem val_cst (w c : ℕ) (x : ℕ → Bool) : val (cst w c) x = c % 2 ^ w := by
  rw [val, cst, bitsOf_constBits, bitsVal_nbits]

theorem val_take (fs : List Fml) (w : ℕ) (x : ℕ → Bool) : val (fs.take w) x = val fs x % 2 ^ w := by
  rw [val, val, bitsOf, bitsOf, List.map_take, bitsVal_take]

theorem val_tail (fs : List Fml) (x : ℕ → Bool) : val fs.tail x = val fs x / 2 := by
  cases fs with
  | nil => simp [val, bitsVal_nil]
  | cons f fs => rw [List.tail_cons, val_cons]; cases f.eval x <;> simp <;> omega

theorem headD_eval_toNat (fs : List Fml) (x : ℕ → Bool) (hne : fs ≠ []) :
    ((fs.headD (const false)).eval x).toNat = val fs x % 2 := by
  cases fs with
  | nil => exact absurd rfl hne
  | cons f fs => rw [List.headD_cons, val_cons]; cases f.eval x <;> simp <;> omega

/-! ## The fields of a literal -/

/-- The fields of a literal as formulas. -/
structure FieldsF where
  flag : Fml
  tag : List Fml
  t : List Fml
  d : List Fml
  p : List Fml
  v : List Fml
  q : List Fml
  js : Fin 13 → List Fml
  g : List Fml
  ansOk : Fml

/-- The values of the field formulas. -/
def evalFields (F : FieldsF) (x : ℕ → Bool) : Fields :=
  { flag := F.flag.eval x, tag := val F.tag x, t := val F.t x, d := val F.d x, p := val F.p x,
    v := val F.v x, q := val F.q x, js := fun k => val (F.js k) x, g := val F.g x,
    ansOk := F.ansOk.eval x }

section Lit

variable (e G T b : ℕ)

/-- The flag bit. -/
def flagF : Fml := inp (b + flagOff e G)

/-- The low `m - 1` bits, the value `j` of an answer index. -/
def jF : List Fml := field b (flagOff e G)

/-- `2T` on `m - 1` bits. -/
def twoTb : BitStr := nbits (flagOff e G) (2 * T)

/-- `j < 2T`. -/
def lt2TF : Fml := ltConst (jF e G b) (twoTb e G T)

/-- `r = j` or `j - 2T`. -/
def rF : List Fml := muxList (lt2TF e G T b) (jF e G b) (subConstBits (jF e G b) (twoTb e G T))

/-- `p = r / 2 + 3`, on `W` bits. -/
def pAnsF : List Fml := addConstBits ((rF e G T b).tail.take (W e)) (nbits (W e) 3)

/-- The field formulas of the literal with base `b`. -/
def litFields : FieldsF where
  flag := flagF e G b
  tag := muxList (flagF e G b) (field (b + tagOff) 3) (cst 3 0)
  t := muxList (flagF e G b) (field (b + tOff) (W e)) (cst (W e) 0)
  d := muxList (flagF e G b) (field (b + dOff e) 4) (muxList (lt2TF e G T b) (cst 4 5) (cst 4 6))
  p := muxList (flagF e G b) (field (b + pOff e) (W e)) (pAnsF e G T b)
  v := muxList (flagF e G b) (field (b + vOff e) 3)
    (muxList ((rF e G T b).headD (const false)) (cst 3 1) (cst 3 5))
  q := muxList (flagF e G b) (field (b + qOff e) Qb) (cst Qb 0)
  js := fun k => muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)
  g := muxList (flagF e G b) (field (b + gOff e) (Gb G)) (cst (Gb G) 0)
  ansOk := and (not (flagF e G b)) (ltConst (jF e G b) (nbits (flagOff e G) (4 * T)))

/-! ### Lengths -/

theorem W_le_flagOff : W e + 1 ≤ flagOff e G := by unfold flagOff; omega

theorem length_jF : (jF e G b).length = flagOff e G := by simp [jF]

theorem length_rF : (rF e G T b).length = flagOff e G := by
  rw [rF, length_muxList _ _ _ (by rw [length_jF, length_subConstBits _ _ (by rw [length_jF, twoTb, length_nbits]), length_jF]),
    length_jF]

theorem length_pAnsF : (pAnsF e G T b).length = W e := by
  rw [pAnsF, length_addConstBits _ _ (by simp [List.length_take, length_rF]; have := W_le_flagOff e G; omega)]
  simp [List.length_take, length_rF]; have := W_le_flagOff e G; omega

/-! ### Values -/

variable (x : ℕ → Bool)

theorem eval_flagF : (flagF e G b).eval x = (ibOf b (mOf e G) x).getD (flagOff e G) false := by
  rw [getD_ibOf _ _ _ (by rw [flagOff_eq]; unfold mOf; omega)]; rfl

theorem val_jF : val (jF e G b) x = bitField (ibOf b (mOf e G) x) 0 (flagOff e G) := by
  have := val_field_ibOf b (mOf e G) 0 (flagOff e G) (by rw [flagOff_eq]; unfold mOf; omega) x
  rw [Nat.add_zero] at this
  exact this

/-- The answer bound: `4T < 2^{m-1}`, from `T ≤ S`. -/
theorem fourT_lt (hT : T ≤ Sof e) : 4 * T < 2 ^ flagOff e G := by
  have h1 : 2 ^ (e + 2) ≤ 2 ^ flagOff e G := Nat.pow_le_pow_right (by omega) (by unfold flagOff W; omega)
  have : 4 * T ≤ 2 ^ (e + 2) := by
    rw [Nat.pow_succ, Nat.pow_succ]; unfold Sof at hT; omega
  have h2 : 2 ^ (e + 2) < 2 ^ flagOff e G := Nat.pow_lt_pow_right (by omega) (by unfold flagOff W; omega)
  omega

theorem eval_lt2TF (hT : T ≤ Sof e) :
    (lt2TF e G T b).eval x = true ↔ bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T := by
  rw [lt2TF, eval_ltConst_iff _ _ (by rw [length_jF, twoTb, length_nbits]), val_jF, twoTb,
    bitsVal_nbits_of_lt (by have := fourT_lt e G T hT; omega)]

theorem val_rF (hT : T ≤ Sof e) :
    val (rF e G T b) x =
      if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
      else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T := by
  rw [rF, val_muxList _ _ _ (by rw [length_jF, length_subConstBits _ _ (by rw [length_jF, twoTb, length_nbits]), length_jF])]
  have h2T : bitsVal (twoTb e G T) = 2 * T := by
    rw [twoTb, bitsVal_nbits_of_lt (by have := fourT_lt e G T hT; omega)]
  by_cases hlt : bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T
  · rw [if_pos ((eval_lt2TF e G T b x hT).mpr hlt), if_pos hlt, val_jF]
  · rw [if_neg (by rw [eval_lt2TF e G T b x hT]; exact hlt), if_neg hlt,
      val_subConstBits _ _ (by rw [length_jF, twoTb, length_nbits]) x (by rw [h2T, val_jF]; omega), h2T, val_jF]

theorem val_pAnsF (hT : T ≤ Sof e) :
    val (pAnsF e G T b) x =
      ((if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
        else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) / 2 + 3) % 2 ^ W e := by
  have hW := W_le_flagOff e G
  have hlen : ((rF e G T b).tail.take (W e)).length = W e := by
    simp [List.length_take, length_rF]; omega
  rw [pAnsF, val_addConstBits_mod _ _ (by rw [hlen]; simp), hlen, val_take, val_tail, val_rF e G T b x hT,
    bitsVal_nbits_of_lt (by unfold W; rw [Nat.pow_succ, Nat.pow_succ]; have := Nat.one_le_two_pow (n := e + 2); omega),
    Nat.mod_add_mod]

theorem eval_ansOkF (hT : T ≤ Sof e) :
    (and (not (flagF e G b)) (ltConst (jF e G b) (nbits (flagOff e G) (4 * T)))).eval x =
      (!(flagF e G b).eval x && decide (bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 4 * T)) := by
  simp only [eval]
  congr 1
  rw [Bool.eq_iff_iff, eval_ltConst_iff _ _ (by simp [jF]), val_jF, bitsVal_nbits_of_lt (fourT_lt e G T hT),
    decide_eq_true_iff]

theorem length_dAns : (muxList (lt2TF e G T b) (cst 4 5) (cst 4 6)).length = 4 := by
  rw [length_muxList _ _ _ (by simp)]; simp

theorem length_vAns : (muxList ((rF e G T b).headD (const false)) (cst 3 1) (cst 3 5)).length = 3 := by
  rw [length_muxList _ _ _ (by simp)]; simp

/-- **The field formulas compute the fields of the index.** -/
theorem evalFields_litFields (hT : T ≤ Sof e) :
    evalFields (litFields e G T b) x = fieldsOf e G T (ibOf b (mOf e G) x) := by
  have hm : mOf e G = flagOff e G + 1 := by rw [flagOff_eq]; unfold mOf; omega
  have hoff : ∀ off w, off + w ≤ flagOff e G →
      val (field (b + off) w) x = bitField (ibOf b (mOf e G) x) off w :=
    fun off w h => val_field_ibOf b (mOf e G) off w (by omega) x
  have hflag := eval_flagF e G b x
  have hansOk := eval_ansOkF e G T b x hT
  rw [hflag] at hansOk
  have hQ : Qb ≤ flagOff e G := by unfold flagOff; omega
  have hGb : Gb G ≤ flagOff e G := by unfold flagOff; omega
  have hjs : ∀ k : Fin 13, jsOff e k + W e ≤ flagOff e G := fun k => by
    unfold jsOff flagOff; have := k.isLt; nlinarith
  unfold evalFields litFields fieldsOf
  simp only
  cases hb : (ibOf b (mOf e G) x).getD (flagOff e G) false
  · rw [if_neg (by simp)]
    rw [hb] at hflag hansOk
    have hmux : ∀ (as bs : List Fml) (h : as.length = bs.length),
        val (muxList (flagF e G b) as bs) x = val bs x := fun as bs h => by
      rw [val_muxList _ _ _ h, hflag]; rfl
    have h_tag : val (muxList (flagF e G b) (field (b + tagOff) 3) (cst 3 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_t : val (muxList (flagF e G b) (field (b + tOff) (W e)) (cst (W e) 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_q : val (muxList (flagF e G b) (field (b + qOff e) Qb) (cst Qb 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_g : val (muxList (flagF e G b) (field (b + gOff e) (Gb G)) (cst (Gb G) 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_js : ∀ k : Fin 13,
        val (muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)) x = 0 := fun k => by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_d : val (muxList (flagF e G b) (field (b + dOff e) 4)
        (muxList (lt2TF e G T b) (cst 4 5) (cst 4 6))) x =
        if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then 5 else 6 := by
      rw [hmux _ _ (by rw [length_dAns]; simp), val_muxList _ _ _ (by simp)]
      by_cases hlt : bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T
      · rw [if_pos ((eval_lt2TF e G T b x hT).mpr hlt), if_pos hlt, val_cst]; rfl
      · rw [if_neg (by rw [eval_lt2TF e G T b x hT]; exact hlt), if_neg hlt, val_cst]; rfl
    have h_p : val (muxList (flagF e G b) (field (b + pOff e) (W e)) (pAnsF e G T b)) x =
        ((if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then
          bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
          else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) / 2 + 3) % 2 ^ W e := by
      rw [hmux _ _ (by rw [length_pAnsF]; simp), val_pAnsF e G T b x hT]
    have h_v : val (muxList (flagF e G b) (field (b + vOff e) 3)
        (muxList ((rF e G T b).headD (const false)) (cst 3 1) (cst 3 5))) x =
        if (if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then
          bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
          else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) % 2 = 1 then 1 else 5 := by
      rw [hmux _ _ (by rw [length_vAns]; simp), val_muxList _ _ _ (by simp)]
      have hne : rF e G T b ≠ [] := by
        intro h; have := length_rF e G T b; rw [h] at this; simp at this; unfold flagOff at this; omega
      have hhead := headD_eval_toNat (rF e G T b) x hne
      rw [val_rF e G T b x hT] at hhead
      generalize (if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then
          bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
          else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) = r at hhead ⊢
      by_cases hodd : r % 2 = 1
      · have : ((rF e G T b).headD (const false)).eval x = true := by
          cases h : ((rF e G T b).headD (const false)).eval x
          · rw [h, Bool.toNat_false] at hhead; omega
          · rfl
        rw [if_pos hodd, if_pos this, val_cst]; rfl
      · have : ((rF e G T b).headD (const false)).eval x = false := by
          cases h : ((rF e G T b).headD (const false)).eval x
          · rfl
          · rw [h, Bool.toNat_true] at hhead; omega
        rw [if_neg hodd, if_neg (by rw [this]; decide), val_cst]; rfl
    have hjsf : (fun k : Fin 13 => val (muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)) x) =
        fun _ => 0 := funext h_js
    rw [hflag, hansOk, h_tag, h_t, h_q, h_g, h_d, h_p, h_v, hjsf]
    simp only [Bool.not_false, Bool.true_and]
  · rw [if_pos (by simp)]
    rw [hb] at hflag hansOk
    have hmux : ∀ (as bs : List Fml) (h : as.length = bs.length),
        val (muxList (flagF e G b) as bs) x = val as x := fun as bs h => by
      rw [val_muxList _ _ _ h, hflag]; rfl
    have hjsf : (fun k : Fin 13 => val (muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)) x) =
        fun k : Fin 13 => bitField (ibOf b (mOf e G) x) (jsOff e k) (W e) := by
      funext k; rw [hmux _ _ (by simp), hoff _ _ (hjs k)]
    rw [hflag, hansOk, hmux _ _ (by simp), hmux _ _ (by simp), hmux _ _ (by rw [length_dAns]; simp),
      hmux _ _ (by rw [length_pAnsF]; simp), hmux _ _ (by rw [length_vAns]; simp),
      hmux _ _ (by simp), hmux _ _ (by simp), hjsf,
      hoff _ _ (by unfold tagOff flagOff; omega), hoff _ _ (by unfold tOff flagOff; omega),
      hoff _ _ (by unfold dOff flagOff; omega), hoff _ _ (by unfold pOff flagOff; omega),
      hoff _ _ (by unfold vOff flagOff; omega), hoff _ _ (by unfold qOff flagOff; omega),
      hoff _ _ (by unfold gOff flagOff; omega)]
    simp only [Bool.not_true, Bool.false_and]

end Lit

end MIPRE.TM.CookLevin.Desc
