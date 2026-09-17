/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Tableau
import MIPRE.TM.Interp.Machine
import MIPRE.Foundations.SAT.FmlLib

/-!
# The variable format of the describer

The binary format of the variables of the Cook–Levin tableau of the interpreter machine
`U` (`planning/succinct-cook-levin.md`, S3). An index is a list of `m` bits, least
significant first. With its top bit set it is *structured*: a tag (3 bits), the time `t`
(`W` bits), the tape `d` (4), the position `p` (`W`), the cell value `v` (3), the state `q`
(`Qb`), the thirteen window centers (`13 W`) and the gate `g` (`Gb`); tags `0..6` are
`cell`, `head`, `state`, `emitOne`, `emitBad`, `emitted`, `aux`. With its top bit clear and
value `j < 4T` it is an *answer* variable: the cell at position `j' / 2 + 3` of tape `A` (for
`j < 2T`, `j' = j`) or `B` (`j' = j - 2T`), with the value blank for `j'` even and `1` for `j'`
odd, so that the first `4T` variables are the `tapeBits` of the two answers.

`fieldsOf` reads the fields of an index, `decodeVar` the tableau variable they denote (if
any), and `encodeVar` is the structured index of a variable; `decodeVar_encodeVar` is the
round trip. The circuit computes exactly `fieldsOf` on its input bits (`FieldFml.lean`).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Codes of symbols, tapes and states -/

/-- The code of a cell value. -/
def symCode : CellVal Sym → ℕ
  | .sym .zero => 0
  | .sym .one => 1
  | .sym .sep => 2
  | .sym .fr => 3
  | .sym .en => 4
  | .blank => 5
  | .bdry => 6

/-- The cell value of a code. -/
def symOfCode : ℕ → Option (CellVal Sym)
  | 0 => some (.sym .zero)
  | 1 => some (.sym .one)
  | 2 => some (.sym .sep)
  | 3 => some (.sym .fr)
  | 4 => some (.sym .en)
  | 5 => some .blank
  | 6 => some .bdry
  | _ => none

theorem symOfCode_symCode (v : CellVal Sym) : symOfCode (symCode v) = some v := by
  rcases v with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;> rfl

theorem symCode_lt (v : CellVal Sym) : symCode v < 7 := by
  rcases v with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;> decide

theorem symOfCode_eq_some {k : ℕ} {v : CellVal Sym} (h : symOfCode k = some v) : symCode v = k := by
  match k, h with
  | 0, h => cases h; rfl
  | 1, h => cases h; rfl
  | 2, h => cases h; rfl
  | 3, h => cases h; rfl
  | 4, h => cases h; rfl
  | 5, h => cases h; rfl
  | 6, h => cases h; rfl
  | n + 7, h => simp [symOfCode] at h

/-- The code of a tape: the input tapes `0..6`, the work tapes `7..12`. -/
def tapeCode : Tape 7 6 → ℕ
  | .inl j => j
  | .inr j => 7 + j

/-- The tape of a code. -/
def tapeOfCode (d : ℕ) : Option (Tape 7 6) :=
  if h : d < 7 then some (.inl ⟨d, h⟩) else if h' : d < 13 then some (.inr ⟨d - 7, by omega⟩) else none

theorem tapeOfCode_tapeCode (d : Tape 7 6) : tapeOfCode (tapeCode d) = some d := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩
  · simp [tapeOfCode, tapeCode, hj]
  · show tapeOfCode (7 + j) = _
    unfold tapeOfCode
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    ext
    simp

theorem tapeCode_lt (d : Tape 7 6) : tapeCode d < 13 := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩ <;> simp [tapeCode] <;> omega

theorem tapeOfCode_eq_some {k : ℕ} {d : Tape 7 6} (h : tapeOfCode k = some d) : tapeCode d = k := by
  unfold tapeOfCode at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; simp [tapeCode]; omega
    · cases h

/-- The number of states, including the halting state. -/
def QC : ℕ := Fintype.card (Option Ctl)

/-- The code of a state. -/
noncomputable def qCode (q : Option Ctl) : ℕ := Fintype.equivFin (Option Ctl) q

/-- The state of a code. -/
noncomputable def qOfCode (k : ℕ) : Option (Option Ctl) :=
  if h : k < QC then some ((Fintype.equivFin (Option Ctl)).symm ⟨k, h⟩) else none

theorem qOfCode_qCode (q : Option Ctl) : qOfCode (qCode q) = some q := by
  unfold qOfCode qCode
  rw [dif_pos (show ((Fintype.equivFin (Option Ctl)) q : ℕ) < QC from (Fintype.equivFin (Option Ctl) q).isLt)]
  simp

theorem qCode_lt (q : Option Ctl) : qCode q < QC := (Fintype.equivFin (Option Ctl) q).isLt

theorem qOfCode_eq_some {k : ℕ} {q : Option Ctl} (h : qOfCode k = some q) : qCode q = k := by
  unfold qOfCode at h
  split at h
  · cases h; simp [qCode]
  · cases h

/-! ## Widths and offsets -/

/-- The width of the state field. -/
def Qb : ℕ := Nat.size QC

theorem QC_lt_two_pow_Qb : QC < 2 ^ Qb := by
  rw [Qb]
  exact Nat.lt_size_self QC

/-- The width of the time, position and center fields: `W = e + 4`, where `S = 2^e`. -/
def W (e : ℕ) : ℕ := e + 4

/-- The tableau length. -/
def Sof (e : ℕ) : ℕ := 2 ^ e

/-- The width of the gate field for a check circuit of `G` gates. -/
def Gb (G : ℕ) : ℕ := Nat.size G

theorem G_lt_two_pow_Gb (G : ℕ) : G < 2 ^ Gb G := Nat.lt_size_self G

/-- The offsets of the fields of a structured index. -/
def tagOff : ℕ := 0
def tOff : ℕ := 3
def dOff (e : ℕ) : ℕ := 3 + W e
def pOff (e : ℕ) : ℕ := 7 + W e
def vOff (e : ℕ) : ℕ := 7 + 2 * W e
def qOff (e : ℕ) : ℕ := 10 + 2 * W e
def jsOff (e : ℕ) (d : ℕ) : ℕ := 10 + 2 * W e + Qb + d * W e
def gOff (e : ℕ) : ℕ := 10 + 15 * W e + Qb
def flagOff (e G : ℕ) : ℕ := 10 + 15 * W e + Qb + Gb G

/-- The index width. -/
def mOf (e G : ℕ) : ℕ := 11 + 15 * W e + Qb + Gb G

theorem flagOff_eq (e G : ℕ) : flagOff e G = mOf e G - 1 := by unfold flagOff mOf; omega

/-! ## Bit strings and numbers -/

theorem bitsOfNat_zero (i : ℕ) : bitsOfNat 0 i = [] := rfl

theorem bitsOfNat_succ (m i : ℕ) :
    bitsOfNat (m + 1) i = decide (i % 2 = 1) :: bitsOfNat m (i / 2) := by
  rw [bitsOfNat, List.ofFn_succ, bitsOfNat]
  congr 1
  · simp
  · congr 1
    funext k
    simp [Nat.testBit_succ]

theorem bitsVal_bitsOfNat (m i : ℕ) : bitsVal (bitsOfNat m i) = i % 2 ^ m := by
  induction m generalizing i with
  | zero => simp [bitsOfNat_zero, bitsVal_nil, Nat.mod_one]
  | succ m ih =>
    rw [bitsOfNat_succ, bitsVal_cons', ih, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
    have h2 : 0 < 2 ^ m := Nat.two_pow_pos m
    have hi := Nat.div_add_mod i 2
    have hlt := Nat.mod_lt i (show 0 < 2 by omega)
    obtain ⟨q, r, hqr, hr⟩ : ∃ q r, i / 2 = r + q * 2 ^ m ∧ r < 2 ^ m :=
      ⟨i / 2 / 2 ^ m, i / 2 % 2 ^ m, by rw [Nat.add_comm, Nat.div_add_mod'], Nat.mod_lt _ h2⟩
    rw [hqr, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    have hb : (decide (i % 2 = 1)).toNat = i % 2 := by
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
    rw [hb]
    have hq : q * (2 * 2 ^ m) = 2 * (q * 2 ^ m) := by ring
    have : i = (2 * r + i % 2) + q * (2 * 2 ^ m) := by omega
    calc 2 * r + i % 2 = (2 * r + i % 2) % (2 * 2 ^ m) := (Nat.mod_eq_of_lt (by omega)).symm
      _ = ((2 * r + i % 2) + q * (2 * 2 ^ m)) % (2 * 2 ^ m) := (Nat.add_mul_mod_self_right _ _ _).symm
      _ = i % (2 * 2 ^ m) := by rw [← this]

theorem bitsOfNat_bitsVal (l : BitStr) : bitsOfNat l.length (bitsVal l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, bitsOfNat_succ, bitsVal_cons']
    have h1 : (2 * bitsVal l + b.toNat) / 2 = bitsVal l := by cases b <;> simp <;> omega
    have h2 : decide ((2 * bitsVal l + b.toNat) % 2 = 1) = b := by cases b <;> simp <;> omega
    rw [h1, h2, ih]

/-- The value of the bits `off .. off + w` of a bit string. -/
def bitField (ib : BitStr) (off w : ℕ) : ℕ := bitsVal ((ib.drop off).take w)

theorem bitField_lt (ib : BitStr) (off w : ℕ) : bitField ib off w < 2 ^ w := by
  unfold bitField
  have := bitsVal_lt ((ib.drop off).take w)
  have hl : ((ib.drop off).take w).length ≤ w := by simp
  exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hl)

/-! ## The fields of an index -/

/-- The fields read from an index: the top bit, the structured fields, and for an answer
index the decoded tape, position and value with the range check `ansOk`. -/
structure Fields where
  flag : Bool
  tag : ℕ
  t : ℕ
  d : ℕ
  p : ℕ
  v : ℕ
  q : ℕ
  js : Fin 13 → ℕ
  g : ℕ
  ansOk : Bool

/-- The fields of the index `ib` (a bit string of length `m`), for the answer length `T`. -/
def fieldsOf (e G T : ℕ) (ib : BitStr) : Fields :=
  if ib.getD (flagOff e G) false then
    { flag := true, tag := bitField ib tagOff 3, t := bitField ib tOff (W e), d := bitField ib (dOff e) 4,
      p := bitField ib (pOff e) (W e), v := bitField ib (vOff e) 3, q := bitField ib (qOff e) Qb,
      js := fun d => bitField ib (jsOff e d) (W e), g := bitField ib (gOff e) (Gb G), ansOk := false }
  else
    let j := bitField ib 0 (flagOff e G)
    let r := if j < 2 * T then j else j - 2 * T
    { flag := false, tag := 0, t := 0, d := if j < 2 * T then 5 else 6, p := r / 2 + 3,
      v := if r % 2 = 1 then 1 else 5, q := 0, js := fun _ => 0, g := 0, ansOk := decide (j < 4 * T) }

/-! ## Decoding -/

section Decode

variable (e G : ℕ)

local notation "S" => Sof e

/-- The tableau variable denoted by the fields of an index, if any. -/
noncomputable def decodeVar (F : Fields) : Option (TabVar 7 6 Sym Ctl S G) :=
  if F.flag then
    if F.tag = 0 then
      if h : F.t ≤ S ∧ F.p < numCells S then
        match tapeOfCode F.d, symOfCode F.v with
        | some d, some v => some (.cell ⟨F.t, by omega⟩ d ⟨F.p, h.2⟩ v)
        | _, _ => none
      else none
    else if F.tag = 1 then
      if h : F.t ≤ S ∧ F.p < numCells S then
        match tapeOfCode F.d with
        | some d => some (.head ⟨F.t, by omega⟩ d ⟨F.p, h.2⟩)
        | none => none
      else none
    else if F.tag = 2 then
      if h : F.t ≤ S then
        match qOfCode F.q with
        | some q => some (.state ⟨F.t, by omega⟩ q)
        | none => none
      else none
    else if F.tag = 3 then
      if h : F.t < S then some (.emitOne ⟨F.t, h⟩) else none
    else if F.tag = 4 then
      if h : F.t < S then some (.emitBad ⟨F.t, h⟩) else none
    else if F.tag = 5 then
      if h : F.t ≤ S then some (.emitted ⟨F.t, by omega⟩) else none
    else if F.tag = 6 then
      if h : F.t < S ∧ (∀ d, F.js d < 2 * S + 3) ∧ F.g < G then
        some (.aux ⟨F.t, h.1⟩ (fun d => ⟨F.js ⟨tapeCode d, tapeCode_lt d⟩, h.2.1 _⟩) ⟨F.g, h.2.2⟩)
      else none
    else none
  else
    if F.ansOk then
      if h : F.d < 7 ∧ F.p < numCells S then
        match symOfCode F.v with
        | some v => some (.cell 0 (.inl ⟨F.d, h.1⟩) ⟨F.p, h.2⟩ v)
        | none => none
      else none
    else none

end Decode

/-! ## Encoding -/

/-- The `w`-bit binary representation of `n`, least significant bit first. -/
def nbits (w n : ℕ) : BitStr := bitsOfNat w n

@[simp] theorem length_nbits (w n : ℕ) : (nbits w n).length = w := length_bitsOfNat w n

theorem bitsVal_nbits (w n : ℕ) : bitsVal (nbits w n) = n % 2 ^ w := bitsVal_bitsOfNat w n

theorem bitsVal_nbits_of_lt {w n : ℕ} (h : n < 2 ^ w) : bitsVal (nbits w n) = n := by
  rw [bitsVal_nbits, Nat.mod_eq_of_lt h]

/-- The `w`-bit fields `js a, …, js (a + n - 1)`, concatenated. -/
def jsPack (w : ℕ) (js : ℕ → ℕ) : ℕ → ℕ → BitStr
  | _, 0 => []
  | a, n + 1 => nbits w (js a) ++ jsPack w js (a + 1) n

@[simp] theorem length_jsPack (w : ℕ) (js : ℕ → ℕ) : ∀ (a n : ℕ), (jsPack w js a n).length = n * w
  | _, 0 => by simp [jsPack]
  | a, n + 1 => by simp [jsPack, length_jsPack w js (a + 1) n]; ring

theorem jsPack_add (w : ℕ) (js : ℕ → ℕ) : ∀ (a n k : ℕ),
    jsPack w js a (n + k) = jsPack w js a n ++ jsPack w js (a + n) k
  | _, 0, k => by simp [jsPack]
  | a, n + 1, k => by
    rw [Nat.succ_add, jsPack, jsPack, jsPack_add w js (a + 1) n k, List.append_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- The structured index with the given fields. -/
def packFields (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ) : BitStr :=
  nbits 3 tag ++ (nbits (W e) t ++ (nbits 4 d ++ (nbits (W e) p ++ (nbits 3 v ++ (nbits Qb q ++
    (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])))))))

theorem length_packFields (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ) :
    (packFields e G tag t d p v q js g).length = mOf e G := by
  simp [packFields, mOf]; ring

/-- Reading a field out of a concatenation. -/
theorem bitField_of_eq (ib pre mid post : BitStr) (off w : ℕ) (h : ib = pre ++ (mid ++ post))
    (hoff : pre.length = off) (hw : mid.length = w) : bitField ib off w = bitsVal mid := by
  rw [bitField, h, List.drop_left' hoff, List.take_left' hw]

theorem getD_of_eq (ib pre post : BitStr) (b : Bool) (off : ℕ) (h : ib = pre ++ (b :: post))
    (hoff : pre.length = off) : ib.getD off false = b := by
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hoff, Nat.sub_self]
  rfl

section Pack

variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)

theorem packFields_flag : (packFields e G tag t d p v q js g).getD (flagOff e G) false = true := by
  refine getD_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v ++
    nbits Qb q ++ jsPack (W e) js 0 13 ++ nbits (Gb G) g) [] true _
    (by simp only [packFields, List.append_assoc, List.singleton_append]) ?_
  simp [flagOff]; ring

theorem packFields_tag : bitField (packFields e G tag t d p v q js g) tagOff 3 = tag % 2 ^ 3 := by
  rw [bitField_of_eq _ [] (nbits 3 tag) (nbits (W e) t ++ (nbits 4 d ++ (nbits (W e) p ++ (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true]))))))) tagOff 3
    (by simp only [packFields, List.nil_append]) (by simp [tagOff]) (by simp), bitsVal_nbits]

theorem packFields_t : bitField (packFields e G tag t d p v q js g) tOff (W e) = t % 2 ^ W e := by
  rw [bitField_of_eq _ (nbits 3 tag) (nbits (W e) t) (nbits 4 d ++ (nbits (W e) p ++ (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])))))) _ _
    (by simp only [packFields]) (by simp [tOff]) (by simp), bitsVal_nbits]

theorem packFields_d : bitField (packFields e G tag t d p v q js g) (dOff e) 4 = d % 2 ^ 4 := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t) (nbits 4 d) (nbits (W e) p ++ (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true]))))) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [dOff]) (by simp), bitsVal_nbits]

theorem packFields_p : bitField (packFields e G tag t d p v q js g) (pOff e) (W e) = p % 2 ^ W e := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d) (nbits (W e) p) (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])))) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [pOff]; ring) (by simp), bitsVal_nbits]

theorem packFields_v : bitField (packFields e G tag t d p v q js g) (vOff e) 3 = v % 2 ^ 3 := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p) (nbits 3 v)
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true]))) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [vOff]; ring) (by simp), bitsVal_nbits]

theorem packFields_q : bitField (packFields e G tag t d p v q js g) (qOff e) Qb = q % 2 ^ Qb := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v)
    (nbits Qb q) (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [qOff]; ring) (by simp), bitsVal_nbits]

theorem packFields_js (k : ℕ) (hk : k < 13) :
    bitField (packFields e G tag t d p v q js g) (jsOff e k) (W e) = js k % 2 ^ W e := by
  have hsplit : jsPack (W e) js 0 13 =
      jsPack (W e) js 0 k ++ (nbits (W e) (js k) ++ jsPack (W e) js (k + 1) (12 - k)) := by
    rw [show 13 = k + (1 + (12 - k)) by omega, jsPack_add, jsPack_add, Nat.zero_add]
    simp [jsPack]
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v ++
    nbits Qb q ++ jsPack (W e) js 0 k) (nbits (W e) (js k))
    (jsPack (W e) js (k + 1) (12 - k) ++ (nbits (Gb G) g ++ [true])) _ _
    (by simp only [packFields, hsplit, List.append_assoc]) (by simp [jsOff]; ring) (by simp),
    bitsVal_nbits]

theorem packFields_g : bitField (packFields e G tag t d p v q js g) (gOff e) (Gb G) = g % 2 ^ Gb G := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v ++
    nbits Qb q ++ jsPack (W e) js 0 13) (nbits (Gb G) g) [true] _ _
    (by simp only [packFields, List.append_assoc]) (by simp [gOff]; ring) (by simp), bitsVal_nbits]

/-- The fields of a structured index are the packed values (reduced modulo their widths). -/
theorem fieldsOf_packFields (T : ℕ) :
    fieldsOf e G T (packFields e G tag t d p v q js g) =
      { flag := true, tag := tag % 2 ^ 3, t := t % 2 ^ W e, d := d % 2 ^ 4, p := p % 2 ^ W e,
        v := v % 2 ^ 3, q := q % 2 ^ Qb, js := (fun k : Fin 13 => js k % 2 ^ W e),
        g := g % 2 ^ Gb G, ansOk := false } := by
  unfold fieldsOf
  rw [if_pos (packFields_flag e G tag t d p v q js g)]
  simp only [packFields_tag, packFields_t, packFields_d, packFields_p, packFields_v, packFields_q,
    packFields_g]
  congr 1
  funext k
  exact packFields_js e G tag t d p v q js g k k.isLt

end Pack

section Encode

variable (e G : ℕ)

local notation "S" => Sof e

/-- The window centers of an `aux` variable as a function on tape codes. -/
def jsFun (js : Tape 7 6 → Center S) (k : ℕ) : ℕ :=
  match tapeOfCode k with
  | some d => js d
  | none => 0

theorem jsFun_tapeCode (js : Tape 7 6 → Center S) (d : Tape 7 6) : jsFun e js (tapeCode d) = js d := by
  simp [jsFun, tapeOfCode_tapeCode]

/-- The structured index of a tableau variable. -/
noncomputable def encodeVar : TabVar 7 6 Sym Ctl S G → BitStr
  | .cell t d p v => packFields e G 0 t (tapeCode d) p (symCode v) 0 (fun _ => 0) 0
  | .head t d p => packFields e G 1 t (tapeCode d) p 0 0 (fun _ => 0) 0
  | .state t q => packFields e G 2 t 0 0 0 (qCode q) (fun _ => 0) 0
  | .emitOne t => packFields e G 3 t 0 0 0 0 (fun _ => 0) 0
  | .emitBad t => packFields e G 4 t 0 0 0 0 (fun _ => 0) 0
  | .emitted t => packFields e G 5 t 0 0 0 0 (fun _ => 0) 0
  | .aux t js g => packFields e G 6 t 0 0 0 0 (jsFun e js) g

theorem length_encodeVar (v : TabVar 7 6 Sym Ctl S G) : (encodeVar e G v).length = mOf e G := by
  cases v <;> simp [encodeVar, length_packFields]

/-- `S < 2^W` and `2S + 7 < 2^W`. -/
theorem numCells_lt_two_pow_W : numCells S < 2 ^ W e := by
  unfold numCells Sof W
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
  have := Nat.one_le_two_pow (n := e)
  omega

theorem Sof_lt_two_pow_W : S < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega

/-- **Decoding inverts encoding.** -/
theorem decodeVar_encodeVar (T : ℕ) (v : TabVar 7 6 Sym Ctl S G) :
    decodeVar e G (fieldsOf e G T (encodeVar e G v)) = some v := by
  have hW := numCells_lt_two_pow_W e
  have hS := Sof_lt_two_pow_W e
  cases v with
  | cell t d p v =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hp : (p : ℕ) % 2 ^ W e = p := Nat.mod_eq_of_lt (by have := p.isLt; omega)
    have hd : tapeCode d % 16 = tapeCode d := Nat.mod_eq_of_lt (by have := tapeCode_lt d; omega)
    have hv : symCode v % 8 = symCode v := Nat.mod_eq_of_lt (by have := symCode_lt v; omega)
    simp only [decodeVar, ht, hp, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [dif_pos ⟨by have := t.isLt; omega, p.isLt⟩, hd, hv, tapeOfCode_tapeCode, symOfCode_symCode]
  | head t d p =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hp : (p : ℕ) % 2 ^ W e = p := Nat.mod_eq_of_lt (by have := p.isLt; omega)
    have hd : tapeCode d % 16 = tapeCode d := Nat.mod_eq_of_lt (by have := tapeCode_lt d; omega)
    simp only [decodeVar, ht, hp, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [dif_pos ⟨by have := t.isLt; omega, p.isLt⟩, hd, tapeOfCode_tapeCode]
  | state t q =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hq : qCode q % 2 ^ Qb = qCode q :=
      Nat.mod_eq_of_lt (lt_trans (qCode_lt q) QC_lt_two_pow_Qb)
    simp only [decodeVar, ht, hq, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte, qOfCode_qCode]
    rw [dif_pos (by have := t.isLt; omega)]
  | emitOne t =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    simp only [decodeVar, ht, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte]
    rw [dif_pos t.isLt]
  | emitBad t =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    simp only [decodeVar, ht, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte]
    rw [dif_pos t.isLt]
  | emitted t =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    simp only [decodeVar, ht, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte]
    rw [dif_pos (by have := t.isLt; omega)]
  | aux t js g =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hg : (g : ℕ) % 2 ^ Gb G = g := Nat.mod_eq_of_lt (lt_trans g.isLt (G_lt_two_pow_Gb G))
    have hjs : ∀ k : ℕ, jsFun e js k % 2 ^ W e = jsFun e js k := by
      intro k
      apply Nat.mod_eq_of_lt
      unfold jsFun
      split
      · rename_i d _
        have := (js d).isLt
        have h1 := Nat.one_le_two_pow (n := e)
        unfold Sof at this; unfold W; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
      · exact Nat.two_pow_pos _
    simp only [decodeVar, ht, hg, hjs, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte]
    have hjs' : ∀ k : Fin 13, jsFun e js k < 2 * S + 3 := fun k => by
      unfold jsFun
      split
      · rename_i d _; exact (js d).isLt
      · omega
    rw [dif_pos ⟨t.isLt, hjs', g.isLt⟩]
    congr 1
    congr 1
    funext d
    ext
    simp [jsFun_tapeCode]

end Encode

end MIPRE.TM.CookLevin.Desc
