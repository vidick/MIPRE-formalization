/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.PcpComplete

@[expose] public section

/-!
# The honest PCP of accepted answers

The completeness clause of cor:functional_viewpoint_final: the map `PCP_{xy}` from answers
`a^R, a^L, b^R, b^L` at a pair of questions `(x, y)` of the `n`-th game of a tailored verifier
to a PCP, for a circuit that describes the output indicator `L*` of the verifier through the
windows of `lem:ar-window-describer`.

* The readable tables (`honestR`): the readable answers padded with zeros to `2^ℓ` bits, the
  table `O` of the decoupled system (`lsTable`), and witnesses of the described formula for
  their windows (`honestW`, chosen once from the readable data). They depend only on `a^R, b^R`.
* The linear tables (`honestL`): `Extend` of the linear answers (`tbl`, `ext`), `F₂`-linear in
  `a^L, b^L` with coefficients read from `a^R, b^R`.
* `identities_honest`: when the game accepts the answers, the honest PCP of these tables
  satisfies the thirteen checks identically. `L*` accepts the padded strings
  (claim:properties_of_L*, item 1), so the circuit's formula is satisfied by their windows
  (`lem:ar-window-describer`), and the linear tables satisfy the system the table holds
  (claim:properties_of_L*, item 2).
-/

namespace MIPRE.Tailored.AnsRed

open MvPolynomial LowDegree SAT Cost

variable {F : Type*} [Field F] {L : PcpDims}

/-! ## Windows of strings -/

/-- The window table read off a string at a cell offset is the string's tape encoding there. -/
theorem winOf_getD (s : BitStr) (o : ℕ) {j : ℕ} (hj : o + j / 2 < s.length) :
    winOf (fun c => s.getD (o + c) false) j = tapeBits s (2 * o + j) := by
  unfold winOf tapeBits
  dsimp only
  rw [show (2 * o + j) / 2 = o + j / 2 by omega, show (2 * o + j) % 2 = j % 2 by omega,
    Nat.testBit_zero, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [ite_eq_left (show j % 2 = 0 from h)]
    simp [h, cellBits]
    cases s[o + j / 2] <;> rfl
  · rw [ite_eq_right (show ¬ j % 2 = 0 by omega)]
    simp only [h, decide_true, Bool.true_and]
    cases s[o + j / 2] <;> rfl

theorem winOf_getD_zero (s : BitStr) {j : ℕ} (hj : j / 2 < s.length) :
    winOf (fun c => s.getD c false) j = tapeBits s j := by
  have := winOf_getD s 0 (j := j) (by omega)
  simpa using this

/-! ## The honest tables -/

variable (prm : PolyTimeFun ℕ (Unary × Unary)) {ℓV : ℕ} (V : TailoredVerifier ℓV) (n : ℕ)

variable (L) in
/-- The first string `L*` reads on honest answers (claim:properties_of_L*, item 1): the readable
answer padded with zeros to `2^ℓ` bits, then the table of the decoupled system. -/
noncomputable def honestA (xq yq : V.Questions n) (aR bR : BitStr) : BitStr :=
  aR ++ List.replicate (2 ^ L.ℓ - (V.tgame n).lenR xq) false ++
    lsTable (2 ^ L.ℓ) (2 ^ L.dm) ((V.tgame n).lenR xq) ((V.tgame n).lenL xq)
      ((V.tgame n).lenR yq) ((V.tgame n).lenL yq) aR bR ((V.tgame n).cons xq yq aR bR)

variable (L) in
/-- The second string `L*` reads on honest answers: the readable answer padded with zeros. -/
noncomputable def honestB (yq : V.Questions n) (bR : BitStr) : BitStr :=
  bR ++ List.replicate (2 ^ L.ℓ - (V.tgame n).lenR yq) false

variable (L) in
open Classical in
/-- Witnesses of the formula a circuit describes for three window tables, when there are some. -/
noncomputable def honestW (Cc : Circuit) (A B C : ℕ → Bool) : Fin 3 → ℕ → Bool :=
  if h : ∃ w₁ w₂ w₃ : Fin (2 ^ L.r) → Bool,
      (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat (fun j => A j) (fun j => B j)
        (fun j => C j) w₁ w₂ w₃ then
    fun k c => if hc : c < 2 ^ L.r then
      ![h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose] k ⟨c, hc⟩ else false
  else fun _ _ => false

theorem sat_honestW {Cc : Circuit} {A B C : ℕ → Bool}
    (h : ∃ w₁ w₂ w₃ : Fin (2 ^ L.r) → Bool,
      (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat (fun j => A j) (fun j => B j)
        (fun j => C j) w₁ w₂ w₃) :
    (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat (fun j => A j) (fun j => B j)
      (fun j => C j) (fun j => honestW L Cc A B C 0 j) (fun j => honestW L Cc A B C 1 j)
      (fun j => honestW L Cc A B C 2 j) := by
  have e : ∀ k : Fin 3, (fun j : Fin (2 ^ L.r) => honestW L Cc A B C k j) =
      ![h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose] k := by
    intro k
    funext j
    simp only [honestW, dite_eq_left h, dite_eq_left j.2]
  rw [e 0, e 1, e 2]
  exact h.choose_spec.choose_spec.choose_spec

variable (L) in
/-- **The readable tables of the honest PCP**: the cells of the padded readable answers, the
table `O`, and witnesses for their windows. They depend only on the readable answers. -/
noncomputable def honestR (Cc : Circuit) (xq yq : V.Questions n) (aR bR : BitStr) : RTables :=
  let tA : ℕ → Bool := fun c => (honestA L V n xq yq aR bR).getD c false
  let tB : ℕ → Bool := fun c => (honestB L V n yq bR).getD c false
  let tO : ℕ → Bool := fun c => (honestA L V n xq yq aR bR).getD (2 ^ L.ℓ + c) false
  ⟨tA, tB, tO, honestW L Cc (winOf tA) (winOf tB) (winOf tO)⟩

variable (L) in
/-- **The linear tables of the honest PCP**: `Extend` of the linear answers (the table of the
linear answers, and three times its extension to the triangulation variables). -/
noncomputable def honestL (xq yq : V.Questions n) (aR aL bR bL : BitStr) : LTables where
  fLa := tbl (2 ^ L.ℓ) aL bL
  fLb := fun j => tbl (2 ^ L.ℓ) aL bL (2 ^ L.ℓ + j)
  fL _ := ext (2 ^ L.ℓ + 2 ^ L.ℓ) (pureRows (V.tgame n) (2 ^ L.ℓ) xq yq aR bR) (tbl (2 ^ L.ℓ) aL bL)

/-! ## Completeness -/

theorem lenIs_lenOf {x : BitStr} (h : V.LenDefined n x) (κ : Bool) :
    LenIs V.len n x κ (V.lenOf n x κ) := by
  obtain ⟨k, hk⟩ := h κ
  rw [lenOf_eq_of_lenIs V hk]
  exact hk

/-- **`L*` accepts the padded readable answers and the table** (claim:properties_of_L*, item 1),
when the verifier's programs halt at the two questions and the lengths fit the parameters. -/
theorem lstar_accepts_honest (xq yq : V.Questions n) {aR bR : BitStr}
    (hℓ : (prm n).1.length = L.ℓ) (hdm : (prm n).2.length = L.dm)
    (hx : V.LenDefined n (CL.toBits xq)) (hy : V.LenDefined n (CL.toBits yq))
    (hlp : ∃ cs, LpIs V.lp n (CL.toBits xq) (CL.toBits yq) aR bR cs)
    (haR : aR.length = (V.tgame n).lenR xq) (hbR : bR.length = (V.tgame n).lenR yq)
    (hRx : (V.tgame n).lenR xq ≤ 2 ^ L.ℓ) (hLx : (V.tgame n).lenL xq ≤ 2 ^ L.ℓ)
    (hRy : (V.tgame n).lenR yq ≤ 2 ^ L.ℓ) (hLy : (V.tgame n).lenL yq ≤ 2 ^ L.ℓ)
    (hD : ((V.tgame n).cons xq yq aR bR).length * (2 ^ L.ℓ + 2 ^ L.ℓ) + (2 ^ L.ℓ + 2 ^ L.ℓ) ≤
      2 ^ L.dm) :
    (lstar prm V).Accepts n (CL.toBits xq) (CL.toBits yq) (honestA L V n xq yq aR bR)
      (honestB L V n yq bR) := by
  obtain ⟨cs, hcs⟩ := hlp
  have hcons : (V.tgame n).cons xq yq aR bR = cs := V.consOf_eq_of hx hy hcs
  have hok := lstarOK_pad (N := 2 ^ L.ℓ) (D := 2 ^ L.dm) (cs := (V.tgame n).cons xq yq aR bR)
    haR hbR hRx hLx hRy hLy hD
  have htakeA : (honestA L V n xq yq aR bR).take ((V.tgame n).lenR xq) = aR := by
    rw [honestA, List.append_assoc, ← haR, List.take_left]
  have htakeB : (honestB L V n yq bR).take ((V.tgame n).lenR yq) = bR := by
    rw [honestB, ← hbR, List.take_left]
  rw [lstar_accepts_iff]
  refine ⟨_, _, _, _, (V.tgame n).cons xq yq aR bR, lenIs_lenOf V n hx false,
    lenIs_lenOf V n hx true,
    lenIs_lenOf V n hy false, lenIs_lenOf V n hy true, ?_, ?_⟩
  · have htakeA' : (honestA L V n xq yq aR bR).take (V.lenOf n (CL.toBits xq) false) = aR :=
      htakeA
    have htakeB' : (honestB L V n yq bR).take (V.lenOf n (CL.toBits yq) false) = bR := htakeB
    rw [htakeA', htakeB', hcons]
    exact hcs
  · rw [hℓ, hdm]
    exact hok

theorem length_honestA (xq yq : V.Questions n) {aR bR : BitStr}
    (haR : aR.length = (V.tgame n).lenR xq) (hRx : (V.tgame n).lenR xq ≤ 2 ^ L.ℓ) :
    (honestA L V n xq yq aR bR).length = 2 ^ L.ℓ + 2 ^ L.oW := by
  rw [honestA, List.length_append, List.length_append, List.length_replicate, lsTable,
    length_indTable, tableSize_eq_oW]
  omega

theorem length_honestB (yq : V.Questions n) {bR : BitStr}
    (hbR : bR.length = (V.tgame n).lenR yq) (hRy : (V.tgame n).lenR yq ≤ 2 ^ L.ℓ) :
    (honestB L V n yq bR).length = 2 ^ L.ℓ := by
  rw [honestB, List.length_append, List.length_replicate]
  omega

/-- **The honest PCP of accepted answers satisfies the thirteen checks identically**
(cor:functional_viewpoint_final, item 1): when the game accepts the answers at `(x, y)` and the
circuit describes the output indicator through the windows, at parameters the lengths fit and
within a time `L*` meets on the padded strings, the honest PCP of the readable tables
`honestR` (the padded readable answers, the table, witnesses) and the linear tables `honestL`
(`Extend` of the linear answers) satisfies the checks identically. -/
theorem identities_honest [CharP F 2] (xq yq : V.Questions n) {aR aL bR bL : BitStr}
    (hℓ : (prm n).1.length = L.ℓ) (hdm : (prm n).2.length = L.dm) {Cc : Circuit} {Tt : ℕ}
    (hWF : Cc.WellFormed) (hin : Cc.inputs = L.nIn) (hm : Cc.inputs + Cc.size = L.m)
    (hdesc : Cc.DescribesWindows (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r (lstar prm V) n
      (CL.toBits xq) (CL.toBits yq) Tt)
    (hT : (lstar prm V).Accepts n (CL.toBits xq) (CL.toBits yq) (honestA L V n xq yq aR bR)
        (honestB L V n yq bR) →
      (lstar prm V).AcceptsWithin n (CL.toBits xq) (CL.toBits yq) (honestA L V n xq yq aR bR)
        (honestB L V n yq bR) Tt)
    (hTlen : 2 ^ L.ℓ + 2 ^ L.oW ≤ Tt)
    (hx : V.LenDefined n (CL.toBits xq)) (hy : V.LenDefined n (CL.toBits yq))
    (hlp : ∃ cs, LpIs V.lp n (CL.toBits xq) (CL.toBits yq) aR bR cs)
    (haR : aR.length = (V.tgame n).lenR xq) (haL : aL.length = (V.tgame n).lenL xq)
    (hbR : bR.length = (V.tgame n).lenR yq) (hbL : bL.length = (V.tgame n).lenL yq)
    (hRx : (V.tgame n).lenR xq ≤ 2 ^ L.ℓ) (hLx : (V.tgame n).lenL xq ≤ 2 ^ L.ℓ)
    (hRy : (V.tgame n).lenR yq ≤ 2 ^ L.ℓ) (hLy : (V.tgame n).lenL yq ≤ 2 ^ L.ℓ)
    (hD : ((V.tgame n).cons xq yq aR bR).length * (2 ^ L.ℓ + 2 ^ L.ℓ) + (2 ^ L.ℓ + 2 ^ L.ℓ) ≤
      2 ^ L.dm)
    (hacc : (V.tgame n).Accepts xq yq (aR ++ aL) (bR ++ bL)) :
    (induce L (rename (Fin.cast hm) (Cc.finiteArith (F := F))) (honestR L V n Cc xq yq aR bR)
      (honestL L V n xq yq aR aL bR bL)).Identities (rename (Fin.cast hm) Cc.finiteArith) := by
  have hAlen := length_honestA V n xq yq (bR := bR) haR hRx
  have hBlen := length_honestB V n yq hbR hRy
  have hN : 0 < 2 ^ L.ℓ := Nat.two_pow_pos _
  have hpow : 2 ^ (L.ℓ + 1) = 2 * 2 ^ L.ℓ := by rw [pow_succ]; ring
  have hpowO : 2 ^ (L.oW + 1) = 2 * 2 ^ L.oW := by rw [pow_succ]; ring
  -- `L*` accepts the padded strings within `Tt`
  have hwithin := hT (lstar_accepts_honest prm V n xq yq hℓ hdm hx hy hlp haR hbR hRx hLx hRy
    hLy hD)
  -- so the circuit's formula is satisfied by their windows
  have hex : ∃ w₁ w₂ w₃ : Fin (2 ^ L.r) → Bool,
      (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat
        (fun j => winOf (fun c => (honestA L V n xq yq aR bR).getD c false) j)
        (fun j => winOf (fun c => (honestB L V n yq bR).getD c false) j)
        (fun j => winOf (fun c => (honestA L V n xq yq aR bR).getD (2 ^ L.ℓ + c) false) j)
        w₁ w₂ w₃ := by
    refine (hdesc _ _ _).2 ⟨_, _, by omega, by omega, fun j => ?_, fun j => ?_, fun j => ?_,
      hwithin⟩
    · have := j.2
      exact winOf_getD_zero _ (by omega)
    · have := j.2
      exact winOf_getD_zero _ (by omega)
    · have := j.2
      rw [winOf_getD _ _ (by omega), hpow]
  have hsat := sat_honestW hex
  -- and the linear tables satisfy the system the table holds
  have htab := tableSat_of_accepts (V.tgame n) haR haL hbR hbL hN hLx hLy hD hacc
  have hstr : tblStr L.oW (fun c => (honestA L V n xq yq aR bR).getD (2 ^ L.ℓ + c) false) =
      lsTable (2 ^ L.ℓ) (2 ^ L.dm) ((V.tgame n).lenR xq) ((V.tgame n).lenL xq)
        ((V.tgame n).lenR yq) ((V.tgame n).lenL yq) aR bR ((V.tgame n).cons xq yq aR bR) := by
    have hdrop : (honestA L V n xq yq aR bR).drop (2 ^ L.ℓ) = lsTable (2 ^ L.ℓ) (2 ^ L.dm)
        ((V.tgame n).lenR xq) ((V.tgame n).lenL xq) ((V.tgame n).lenR yq) ((V.tgame n).lenL yq)
        aR bR ((V.tgame n).cons xq yq aR bR) := by
      rw [honestA, List.drop_left' (by simp; omega)]
    rw [← hdrop]
    apply List.ext_getElem (by simp [tblStr]; omega)
    intro c h1 h2
    simp only [tblStr, List.getElem_ofFn, List.getElem_drop]
    exact List.getD_eq_getElem _ _ _
  rw [← hstr] at htab
  exact identities_induce hWF hin hm _ _ hsat htab

/-! ## The linear tables are linear in the linear answers -/

theorem bitAt_xorBits {a b : BitStr} (h : a.length = b.length) (i : ℕ) :
    bitAt (BinaryPolynomial.xorBits a b) i = bitAt a i + bitAt b i := by
  unfold bitAt BinaryPolynomial.xorBits
  by_cases hi : i < a.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith]
    exact BinaryLinear.ofBool_xor _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]
    rfl

theorem tbl_xorBits (N : ℕ) {a₁ a₂ b₁ b₂ : BitStr} (ha : a₁.length = a₂.length)
    (hb : b₁.length = b₂.length) (v : ℕ) :
    tbl N (BinaryPolynomial.xorBits a₁ a₂) (BinaryPolynomial.xorBits b₁ b₂) v =
      tbl N a₁ b₁ v + tbl N a₂ b₂ v := by
  unfold tbl
  split_ifs
  · exact bitAt_xorBits ha v
  · exact bitAt_xorBits hb (v - N)

/-- **The linear tables are `F₂`-linear in the linear answers**, the readable answers fixed: the
table of the linear answers and its extension are additive under the bitwise sum. -/
theorem honestL_xorBits (xq yq : V.Questions n) (aR bR : BitStr) {aL₁ aL₂ bL₁ bL₂ : BitStr}
    (ha : aL₁.length = aL₂.length) (hb : bL₁.length = bL₂.length) :
    honestL L V n xq yq aR (BinaryPolynomial.xorBits aL₁ aL₂) bR
        (BinaryPolynomial.xorBits bL₁ bL₂) =
      honestL L V n xq yq aR aL₁ bR bL₁ + honestL L V n xq yq aR aL₂ bR bL₂ := by
  have ht : tbl (2 ^ L.ℓ) (BinaryPolynomial.xorBits aL₁ aL₂) (BinaryPolynomial.xorBits bL₁ bL₂) =
      tbl (2 ^ L.ℓ) aL₁ bL₁ + tbl (2 ^ L.ℓ) aL₂ bL₂ := funext (tbl_xorBits _ ha hb)
  unfold honestL
  show (⟨_, _, _⟩ : LTables) = ⟨_, _, _⟩
  rw [ht]
  congr 1
  funext k v
  simp only [Pi.add_apply, ext]
  exact List.sum_map_add

end MIPRE.Tailored.AnsRed

end
