/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TM.CookLevin.Link
public import MIPRE.Foundations.SAT.Decoupled6

@[expose] public section

/-!
# The link clauses of the windowed describer

The windowed describer of `MIPRE.SAT.WindowDescriber` (slice P4g of the Aldous–Lyons track) ties
three input blocks to the first `4T` variables of three witness blocks, which carry the
tableau of `thm:succinct-sat`: the first and third blocks to the consecutive windows
`[0, 2^ℓa)` and `[2^ℓa, 2^ℓa + 2^ℓc)` of the tape encoding of the first answer, the second to
the window `[2T, 2T + 2^ℓb)` of that of the second, and it makes the three witness blocks
agree. There are five rows, the analogue of rows 2, 3, 8 and 9 of `Link.lean`; nothing pins the
tape outside the windows, which the decider's own checks of its input lengths do.

`Link6` is the disjunction of the five conditions on a decoded clause and `link6Fml` the formula
that decides it on the `ℓa + ℓb + ℓc + 3r + 6` input bits, with `eval_link6Fml` their
equivalence. Every comparison is made at width `r`, the window indices zero-padded.
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## The input layout -/

section Layout

variable (ℓa ℓb ℓc r : ℕ)

/-- The offset of the three witness indices. -/
def wOff : ℕ := ℓa + ℓb + ℓc

/-- The offset of the six signs. -/
def sgOff6 : ℕ := wOff ℓa ℓb ℓc + 3 * r

/-- The three window indices, zero-padded to `r` bits, and the three witness indices. -/
def k₁F : List Fml := padTo r (field 0 ℓa)
def k₂F : List Fml := padTo r (field ℓa ℓb)
def k₃F : List Fml := padTo r (field (ℓa + ℓb) ℓc)
def k₄F : List Fml := field (wOff ℓa ℓb ℓc) r
def k₅F : List Fml := field (wOff ℓa ℓb ℓc + r) r
def k₆F : List Fml := field (wOff ℓa ℓb ℓc + 2 * r) r

/-- The `k`-th of the six signs. -/
def t₀F (k : ℕ) : Fml := inp (sgOff6 ℓa ℓb ℓc r + k)

theorem length_k₁F (h : ℓa ≤ r) : (k₁F ℓa r).length = r := by
  rw [k₁F, length_padTo _ _ (by rw [length_field]; exact h)]

theorem length_k₂F (h : ℓb ≤ r) : (k₂F ℓa ℓb r).length = r := by
  rw [k₂F, length_padTo _ _ (by rw [length_field]; exact h)]

theorem length_k₃F (h : ℓc ≤ r) : (k₃F ℓa ℓb ℓc r).length = r := by
  rw [k₃F, length_padTo _ _ (by rw [length_field]; exact h)]

@[simp] theorem length_k₄F : (k₄F ℓa ℓb ℓc r).length = r := length_field _ _
@[simp] theorem length_k₅F : (k₅F ℓa ℓb ℓc r).length = r := length_field _ _
@[simp] theorem length_k₆F : (k₆F ℓa ℓb ℓc r).length = r := length_field _ _

end Layout

/-! ## The five conditions -/

variable (ℓa ℓb ℓc r T : ℕ)

/-- **The link conditions** on a decoupled clause of the windowed describer. -/
def Link6 (c : Clause6W ℓa ℓb ℓc r) : Prop :=
  ((c.l₄.var : ℕ) = (c.l₁.var : ℕ) ∧ c.l₁.pos ≠ c.l₄.pos) ∨
  ((c.l₄.var : ℕ) = (c.l₂.var : ℕ) + 2 * T ∧ c.l₂.pos ≠ c.l₄.pos) ∨
  ((c.l₄.var : ℕ) = (c.l₃.var : ℕ) + 2 ^ ℓa ∧ c.l₃.pos ≠ c.l₄.pos) ∨
  ((c.l₄.var : ℕ) = (c.l₅.var : ℕ) ∧ c.l₄.pos ≠ c.l₅.pos) ∨
  ((c.l₅.var : ℕ) = (c.l₆.var : ℕ) ∧ c.l₅.pos ≠ c.l₆.pos)

/-- The formula deciding `Link6` on the `ℓa + ℓb + ℓc + 3r + 6` input bits. -/
def link6Fml : Fml :=
  orList [
    andList [eqFields (k₁F ℓa r) (k₄F ℓa ℓb ℓc r), xor (t₀F ℓa ℓb ℓc r 0) (t₀F ℓa ℓb ℓc r 3)],
    andList [addConstRel (k₂F ℓa ℓb r) (k₄F ℓa ℓb ℓc r) (nbits r (2 * T)),
      xor (t₀F ℓa ℓb ℓc r 1) (t₀F ℓa ℓb ℓc r 3)],
    andList [addConstRel (k₃F ℓa ℓb ℓc r) (k₄F ℓa ℓb ℓc r) (nbits r (2 ^ ℓa)),
      xor (t₀F ℓa ℓb ℓc r 2) (t₀F ℓa ℓb ℓc r 3)],
    andList [eqFields (k₄F ℓa ℓb ℓc r) (k₅F ℓa ℓb ℓc r),
      xor (t₀F ℓa ℓb ℓc r 3) (t₀F ℓa ℓb ℓc r 4)],
    andList [eqFields (k₅F ℓa ℓb ℓc r) (k₆F ℓa ℓb ℓc r),
      xor (t₀F ℓa ℓb ℓc r 4) (t₀F ℓa ℓb ℓc r 5)]]

theorem InputsLt.link6Fml : (link6Fml ℓa ℓb ℓc r T).InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) := by
  have hk₁ : ∀ f ∈ k₁F ℓa r, f.InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) :=
    InputsLt.padTo (InputsLt.field (by omega))
  have hk₂ : ∀ f ∈ k₂F ℓa ℓb r, f.InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) :=
    InputsLt.padTo (InputsLt.field (by omega))
  have hk₃ : ∀ f ∈ k₃F ℓa ℓb ℓc r, f.InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) :=
    InputsLt.padTo (InputsLt.field (by omega))
  have hk₄ : ∀ f ∈ k₄F ℓa ℓb ℓc r, f.InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) :=
    InputsLt.field (by unfold wOff; omega)
  have hk₅ : ∀ f ∈ k₅F ℓa ℓb ℓc r, f.InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) :=
    InputsLt.field (by unfold wOff; omega)
  have hk₆ : ∀ f ∈ k₆F ℓa ℓb ℓc r, f.InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) :=
    InputsLt.field (by unfold wOff; omega)
  have ht : ∀ k, k < 6 → (t₀F ℓa ℓb ℓc r k).InputsLt (ℓa + ℓb + ℓc + 3 * r + 6) := by
    intro k hk
    show sgOff6 ℓa ℓb ℓc r + k < ℓa + ℓb + ℓc + 3 * r + 6
    unfold sgOff6 wOff; omega
  refine InputsLt.orList _ ?_
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hk₁ hk₄)
      (InputsLt.list_cons (InputsLt.xor (ht 0 (by omega)) (ht 3 (by omega))) InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.addConstRel _ hk₂ hk₄)
      (InputsLt.list_cons (InputsLt.xor (ht 1 (by omega)) (ht 3 (by omega))) InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.addConstRel _ hk₃ hk₄)
      (InputsLt.list_cons (InputsLt.xor (ht 2 (by omega)) (ht 3 (by omega))) InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hk₄ hk₅)
      (InputsLt.list_cons (InputsLt.xor (ht 3 (by omega)) (ht 4 (by omega))) InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hk₅ hk₆)
      (InputsLt.list_cons (InputsLt.xor (ht 4 (by omega)) (ht 5 (by omega))) InputsLt.list_nil))

/-! ## The slices of a clause's input -/

section Slices

variable {ℓa ℓb ℓc r : ℕ} (c : Clause6W ℓa ℓb ℓc r)

/-- The six signs, as a list. -/
def sgList6 : BitStr := [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos, c.l₆.pos]

theorem clauseInput6_eq : clauseInput6 ℓa ℓb ℓc r c =
    bitsOfNat ℓa c.l₁.var ++ (bitsOfNat ℓb c.l₂.var ++ (bitsOfNat ℓc c.l₃.var ++
      (bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ (bitsOfNat r c.l₆.var ++
        sgList6 c))))) := by
  simp only [clauseInput6, sgList6, List.append_assoc]

theorem drop6_one : (clauseInput6 ℓa ℓb ℓc r c).drop ℓa =
    bitsOfNat ℓb c.l₂.var ++ (bitsOfNat ℓc c.l₃.var ++ (bitsOfNat r c.l₄.var ++
      (bitsOfNat r c.l₅.var ++ (bitsOfNat r c.l₆.var ++ sgList6 c)))) := by
  rw [clauseInput6_eq, List.drop_left' (by rw [length_bitsOfNat])]

theorem drop6_two : (clauseInput6 ℓa ℓb ℓc r c).drop (ℓa + ℓb) =
    bitsOfNat ℓc c.l₃.var ++ (bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++
      (bitsOfNat r c.l₆.var ++ sgList6 c))) := by
  rw [← List.drop_drop, drop6_one, List.drop_left' (by rw [length_bitsOfNat])]

theorem drop6_three : (clauseInput6 ℓa ℓb ℓc r c).drop (wOff ℓa ℓb ℓc) =
    bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ (bitsOfNat r c.l₆.var ++ sgList6 c)) := by
  rw [wOff, ← List.drop_drop, drop6_two, List.drop_left' (by rw [length_bitsOfNat])]

theorem drop6_four : (clauseInput6 ℓa ℓb ℓc r c).drop (wOff ℓa ℓb ℓc + r) =
    bitsOfNat r c.l₅.var ++ (bitsOfNat r c.l₆.var ++ sgList6 c) := by
  rw [← List.drop_drop, drop6_three, List.drop_left' (by rw [length_bitsOfNat])]

theorem drop6_five : (clauseInput6 ℓa ℓb ℓc r c).drop (wOff ℓa ℓb ℓc + 2 * r) =
    bitsOfNat r c.l₆.var ++ sgList6 c := by
  rw [show wOff ℓa ℓb ℓc + 2 * r = wOff ℓa ℓb ℓc + r + r by omega, ← List.drop_drop, drop6_four,
    List.drop_left' (by rw [length_bitsOfNat])]

theorem drop6_signs : (clauseInput6 ℓa ℓb ℓc r c).drop (sgOff6 ℓa ℓb ℓc r) = sgList6 c := by
  rw [show sgOff6 ℓa ℓb ℓc r = wOff ℓa ℓb ℓc + 2 * r + r by unfold sgOff6; omega,
    ← List.drop_drop, drop6_five, List.drop_left' (by rw [length_bitsOfNat])]

theorem val_k₁F :
    val (k₁F ℓa r) (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) = (c.l₁.var : ℕ) := by
  rw [k₁F, val_padTo, val, bitsOf_field]
  show bitsVal (ibOf 0 ℓa _) = _
  rw [ibOf_getD _ 0 ℓa (by rw [length_clauseInput6]; omega), List.drop_zero, clauseInput6_eq,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₁.var.isLt]

theorem val_k₂F :
    val (k₂F ℓa ℓb r) (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) = (c.l₂.var : ℕ) := by
  rw [k₂F, val_padTo, val, bitsOf_field]
  show bitsVal (ibOf ℓa ℓb _) = _
  rw [ibOf_getD _ ℓa ℓb (by rw [length_clauseInput6]; omega), drop6_one,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₂.var.isLt]

theorem val_k₃F :
    val (k₃F ℓa ℓb ℓc r) (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) =
      (c.l₃.var : ℕ) := by
  rw [k₃F, val_padTo, val, bitsOf_field]
  show bitsVal (ibOf (ℓa + ℓb) ℓc _) = _
  rw [ibOf_getD _ (ℓa + ℓb) ℓc (by rw [length_clauseInput6]; omega), drop6_two,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₃.var.isLt]

theorem val_k₄F :
    val (k₄F ℓa ℓb ℓc r) (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) =
      (c.l₄.var : ℕ) := by
  rw [k₄F, val, bitsOf_field]
  show bitsVal (ibOf (wOff ℓa ℓb ℓc) r _) = _
  rw [ibOf_getD _ (wOff ℓa ℓb ℓc) r (by rw [length_clauseInput6]; unfold wOff; omega),
    drop6_three, List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₄.var.isLt]

theorem val_k₅F :
    val (k₅F ℓa ℓb ℓc r) (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) =
      (c.l₅.var : ℕ) := by
  rw [k₅F, val, bitsOf_field]
  show bitsVal (ibOf (wOff ℓa ℓb ℓc + r) r _) = _
  rw [ibOf_getD _ (wOff ℓa ℓb ℓc + r) r (by rw [length_clauseInput6]; unfold wOff; omega),
    drop6_four, List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₅.var.isLt]

theorem val_k₆F :
    val (k₆F ℓa ℓb ℓc r) (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) =
      (c.l₆.var : ℕ) := by
  rw [k₆F, val, bitsOf_field]
  show bitsVal (ibOf (wOff ℓa ℓb ℓc + 2 * r) r _) = _
  rw [ibOf_getD _ (wOff ℓa ℓb ℓc + 2 * r) r (by rw [length_clauseInput6]; unfold wOff; omega),
    drop6_five, List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₆.var.isLt]

theorem eval_t₀F (k : ℕ) :
    (t₀F ℓa ℓb ℓc r k).eval (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) =
      (sgList6 c).getD k false := by
  show (clauseInput6 ℓa ℓb ℓc r c).getD (sgOff6 ℓa ℓb ℓc r + k) false = _
  rw [← getD_drop_eq, drop6_signs]

end Slices

/-! ## The formula decides the conditions -/

/-- **The link formula decides the link conditions.** -/
theorem eval_link6Fml {ℓa ℓb ℓc r T : ℕ} (ha : ℓa ≤ r) (hb : ℓb ≤ r) (hc : ℓc ≤ r)
    (hT : 2 * T < 2 ^ r) (hTa : 2 ^ ℓa < 2 ^ r) (c : Clause6W ℓa ℓb ℓc r) :
    (link6Fml ℓa ℓb ℓc r T).eval (fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false) = true ↔
      Link6 ℓa ℓb ℓc r T c := by
  have h1 := length_k₁F ℓa r ha
  have h2 := length_k₂F ℓa ℓb r hb
  have h3 := length_k₃F ℓa ℓb ℓc r hc
  set x : ℕ → Bool := fun i => (clauseInput6 ℓa ℓb ℓc r c).getD i false with hx
  have e₁ : val (k₁F ℓa r) x = (c.l₁.var : ℕ) := val_k₁F c
  have e₂ : val (k₂F ℓa ℓb r) x = (c.l₂.var : ℕ) := val_k₂F c
  have e₃ : val (k₃F ℓa ℓb ℓc r) x = (c.l₃.var : ℕ) := val_k₃F c
  have e₄ : val (k₄F ℓa ℓb ℓc r) x = (c.l₄.var : ℕ) := val_k₄F c
  have e₅ : val (k₅F ℓa ℓb ℓc r) x = (c.l₅.var : ℕ) := val_k₅F c
  have e₆ : val (k₆F ℓa ℓb ℓc r) x = (c.l₆.var : ℕ) := val_k₆F c
  have g₁ : (t₀F ℓa ℓb ℓc r 0).eval x = c.l₁.pos := eval_t₀F c 0
  have g₂ : (t₀F ℓa ℓb ℓc r 1).eval x = c.l₂.pos := eval_t₀F c 1
  have g₃ : (t₀F ℓa ℓb ℓc r 2).eval x = c.l₃.pos := eval_t₀F c 2
  have g₄ : (t₀F ℓa ℓb ℓc r 3).eval x = c.l₄.pos := eval_t₀F c 3
  have g₅ : (t₀F ℓa ℓb ℓc r 4).eval x = c.l₅.pos := eval_t₀F c 4
  have g₆ : (t₀F ℓa ℓb ℓc r 5).eval x = c.l₆.pos := eval_t₀F c 5
  have eq₁₄ : (eqFields (k₁F ℓa r) (k₄F ℓa ℓb ℓc r)).eval x = true ↔
      (c.l₄.var : ℕ) = (c.l₁.var : ℕ) := by
    rw [eval_eqF h1 (length_k₄F ℓa ℓb ℓc r), e₁, e₄, eq_comm]
  have add₂₄ : (addConstRel (k₂F ℓa ℓb r) (k₄F ℓa ℓb ℓc r) (nbits r (2 * T))).eval x = true ↔
      (c.l₄.var : ℕ) = (c.l₂.var : ℕ) + 2 * T := by
    rw [eval_addN h2 (length_k₄F ℓa ℓb ℓc r) hT, e₂, e₄]
  have add₃₄ : (addConstRel (k₃F ℓa ℓb ℓc r) (k₄F ℓa ℓb ℓc r)
      (nbits r (2 ^ ℓa))).eval x = true ↔
      (c.l₄.var : ℕ) = (c.l₃.var : ℕ) + 2 ^ ℓa := by
    rw [eval_addN h3 (length_k₄F ℓa ℓb ℓc r) hTa, e₃, e₄]
  have eq₄₅ : (eqFields (k₄F ℓa ℓb ℓc r) (k₅F ℓa ℓb ℓc r)).eval x = true ↔
      (c.l₄.var : ℕ) = (c.l₅.var : ℕ) := by
    rw [eval_eqF (length_k₄F ℓa ℓb ℓc r) (length_k₅F ℓa ℓb ℓc r), e₄, e₅]
  have eq₅₆ : (eqFields (k₅F ℓa ℓb ℓc r) (k₆F ℓa ℓb ℓc r)).eval x = true ↔
      (c.l₅.var : ℕ) = (c.l₆.var : ℕ) := by
    rw [eval_eqF (length_k₅F ℓa ℓb ℓc r) (length_k₆F ℓa ℓb ℓc r), e₅, e₆]
  rw [link6Fml, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    eval_andList₂, eval_xor_iff, eq₁₄, add₂₄, add₃₄, eq₄₅, eq₅₆, g₁, g₂, g₃, g₄, g₅, g₆, Link6]

end MIPRE.TM.CookLevin.Desc

end
