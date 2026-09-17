/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Assemble
import MIPRE.Foundations.SAT.Remap
import MIPRE.Foundations.SAT.Decoupled

/-!
# The link clauses of the decoupled describer

Rows 2 to 9 of the paper's circuit (`prop:explicit-succinct-deciders`): the clause families
that tie the two answer blocks `a, b` of a decoupled 5SAT instance to the first `4T`
variables of the three auxiliary blocks, pin the padding of `a` and `b` above `2T`, and force
the three auxiliary blocks to agree.

`Link` is the disjunction of the eight conditions on a decoded clause and `linkFml` the
formula that decides it on the `2ℓ + 3r + 5` input bits, with `eval_linkFml` their
equivalence. Every comparison is made at width `r`, with the two `ℓ`-bit answer indices
zero-padded: at width `ℓ` the constant `2T` is not representable when `T` is a power of two,
since then `2T = 2 ^ ℓ` exactly (`planning/decoupled-5sat.md`, A1b).

**The parities of rows 4 to 7 are a repair of the verification campaign.** Blocks are
`0`-indexed and the blank encodes as `10`, so the honest padding starts at the even index
`2T` and puts `1` at even indices and `0` at odd ones. The pre-repair text had it the other
way round, which is violated by the honest assignment and breaks completeness. Our
`tapeBits` past the end of a string is the blank cell, hence `true` at even and `false` at
odd positions, so it agrees with the repaired parity.
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## The input layout -/

section Layout

variable (ℓ r : ℕ)

/-- The offset of the five signs. -/
def sgOff : ℕ := 2 * ℓ + 3 * r

/-- The two answer indices, zero-padded to `r` bits, and the three auxiliary indices. -/
def j₁F : List Fml := padTo r (field 0 ℓ)
def j₂F : List Fml := padTo r (field ℓ ℓ)
def j₃F : List Fml := field (2 * ℓ) r
def j₄F : List Fml := field (2 * ℓ + r) r
def j₅F : List Fml := field (2 * ℓ + 2 * r) r

/-- The five signs. -/
def s₁F : Fml := inp (sgOff ℓ r)
def s₂F : Fml := inp (sgOff ℓ r + 1)
def s₃F : Fml := inp (sgOff ℓ r + 2)
def s₄F : Fml := inp (sgOff ℓ r + 3)
def s₅F : Fml := inp (sgOff ℓ r + 4)

theorem length_j₁F (h : ℓ ≤ r) : (j₁F ℓ r).length = r := by
  rw [j₁F, length_padTo _ _ (by rw [length_field]; exact h)]

theorem length_j₂F (h : ℓ ≤ r) : (j₂F ℓ r).length = r := by
  rw [j₂F, length_padTo _ _ (by rw [length_field]; exact h)]

@[simp] theorem length_j₃F : (j₃F ℓ r).length = r := length_field _ _
@[simp] theorem length_j₄F : (j₄F ℓ r).length = r := length_field _ _
@[simp] theorem length_j₅F : (j₅F ℓ r).length = r := length_field _ _

end Layout

/-! ## The eight conditions -/

variable (ℓ r T : ℕ)

/-- **The link conditions** on a decoupled clause: rows 2 to 9 of the paper's circuit. -/
def Link (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    Prop :=
  ((c.l₁.var : ℕ) < 2 * T ∧ (c.l₁.var : ℕ) = (c.l₃.var : ℕ) ∧ c.l₁.pos ≠ c.l₃.pos) ∨
  ((c.l₂.var : ℕ) < 2 * T ∧ (c.l₃.var : ℕ) = (c.l₂.var : ℕ) + 2 * T ∧ c.l₂.pos ≠ c.l₃.pos) ∨
  (¬ (c.l₁.var : ℕ) < 2 * T ∧ (c.l₁.var : ℕ) % 2 = 0 ∧ c.l₁.pos = true) ∨
  (¬ (c.l₁.var : ℕ) < 2 * T ∧ ¬ (c.l₁.var : ℕ) % 2 = 0 ∧ c.l₁.pos = false) ∨
  (¬ (c.l₂.var : ℕ) < 2 * T ∧ (c.l₂.var : ℕ) % 2 = 0 ∧ c.l₂.pos = true) ∨
  (¬ (c.l₂.var : ℕ) < 2 * T ∧ ¬ (c.l₂.var : ℕ) % 2 = 0 ∧ c.l₂.pos = false) ∨
  ((c.l₃.var : ℕ) = (c.l₄.var : ℕ) ∧ c.l₃.pos ≠ c.l₄.pos) ∨
  ((c.l₄.var : ℕ) = (c.l₅.var : ℕ) ∧ c.l₄.pos ≠ c.l₅.pos)

/-- The formula deciding `Link` on the `2ℓ + 3r + 5` input bits. -/
def linkFml : Fml :=
  orList [
    andList [ltConst (j₁F ℓ r) (nbits r (2 * T)), eqFields (j₁F ℓ r) (j₃F ℓ r),
      xor (s₁F ℓ r) (s₃F ℓ r)],
    andList [ltConst (j₂F ℓ r) (nbits r (2 * T)),
      addConstRel (j₂F ℓ r) (j₃F ℓ r) (nbits r (2 * T)), xor (s₂F ℓ r) (s₃F ℓ r)],
    andList [not (ltConst (j₁F ℓ r) (nbits r (2 * T))),
      not ((j₁F ℓ r).headD (const false)), s₁F ℓ r],
    andList [not (ltConst (j₁F ℓ r) (nbits r (2 * T))),
      (j₁F ℓ r).headD (const false), not (s₁F ℓ r)],
    andList [not (ltConst (j₂F ℓ r) (nbits r (2 * T))),
      not ((j₂F ℓ r).headD (const false)), s₂F ℓ r],
    andList [not (ltConst (j₂F ℓ r) (nbits r (2 * T))),
      (j₂F ℓ r).headD (const false), not (s₂F ℓ r)],
    andList [eqFields (j₃F ℓ r) (j₄F ℓ r), xor (s₃F ℓ r) (s₄F ℓ r)],
    andList [eqFields (j₄F ℓ r) (j₅F ℓ r), xor (s₄F ℓ r) (s₅F ℓ r)]]

theorem InputsLt.linkFml (h : ℓ ≤ r) : (linkFml ℓ r T).InputsLt (2 * ℓ + 3 * r + 5) := by
  have hj₁ : ∀ f ∈ j₁F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) :=
    InputsLt.padTo (InputsLt.field (by omega))
  have hj₂ : ∀ f ∈ j₂F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) :=
    InputsLt.padTo (InputsLt.field (by omega))
  have hj₃ : ∀ f ∈ j₃F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) := InputsLt.field (by omega)
  have hj₄ : ∀ f ∈ j₄F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) := InputsLt.field (by omega)
  have hj₅ : ∀ f ∈ j₅F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) := InputsLt.field (by omega)
  have hs₁ : (s₁F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₂ : (s₂F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 1 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₃ : (s₃F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 2 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₄ : (s₄F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 3 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₅ : (s₅F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 4 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hh₁ := InputsLt.headD (n := 2 * ℓ + 3 * r + 5) hj₁
  have hh₂ := InputsLt.headD (n := 2 * ℓ + 3 * r + 5) hj₂
  refine InputsLt.orList _ ?_
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.ltConst _ hj₁)
      (InputsLt.list_cons (InputsLt.eqFields hj₁ hj₃)
      (InputsLt.list_cons (InputsLt.xor hs₁ hs₃) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.ltConst _ hj₂)
      (InputsLt.list_cons (InputsLt.addConstRel _ hj₂ hj₃)
      (InputsLt.list_cons (InputsLt.xor hs₂ hs₃) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₁))
      (InputsLt.list_cons (InputsLt.not' hh₁) (InputsLt.list_cons hs₁ InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₁))
      (InputsLt.list_cons hh₁ (InputsLt.list_cons (InputsLt.not' hs₁) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₂))
      (InputsLt.list_cons (InputsLt.not' hh₂) (InputsLt.list_cons hs₂ InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₂))
      (InputsLt.list_cons hh₂ (InputsLt.list_cons (InputsLt.not' hs₂) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hj₃ hj₄)
      (InputsLt.list_cons (InputsLt.xor hs₃ hs₄) InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hj₄ hj₅)
      (InputsLt.list_cons (InputsLt.xor hs₄ hs₅) InputsLt.list_nil))

/-! ## The slices of a clause's input -/

section Slices

variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))

/-- The five signs, as a list. -/
def sgList : BitStr := [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos]

theorem clauseInput5_eq : clauseInput5 ℓ r c =
    bitsOfNat ℓ c.l₁.var ++ (bitsOfNat ℓ c.l₂.var ++ (bitsOfNat r c.l₃.var ++
      (bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ sgList c)))) := by
  simp only [clauseInput5, sgList, List.append_assoc]

theorem drop_two : (clauseInput5 ℓ r c).drop (2 * ℓ) =
    bitsOfNat r c.l₃.var ++ (bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ sgList c)) := by
  have h : 2 * ℓ = ℓ + ℓ := by omega
  rw [h, ← List.drop_drop, clauseInput5_eq, List.drop_left' (by rw [length_bitsOfNat]),
    List.drop_left' (by rw [length_bitsOfNat])]

theorem drop_three : (clauseInput5 ℓ r c).drop (2 * ℓ + r) =
    bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ sgList c) := by
  rw [← List.drop_drop, drop_two, List.drop_left' (by rw [length_bitsOfNat])]

theorem drop_four : (clauseInput5 ℓ r c).drop (2 * ℓ + 2 * r) =
    bitsOfNat r c.l₅.var ++ sgList c := by
  have h : 2 * ℓ + 2 * r = 2 * ℓ + r + r := by omega
  rw [h, ← List.drop_drop, drop_three, List.drop_left' (by rw [length_bitsOfNat])]

theorem drop_signs : (clauseInput5 ℓ r c).drop (sgOff ℓ r) = sgList c := by
  have h : sgOff ℓ r = 2 * ℓ + 2 * r + r := by unfold sgOff; omega
  rw [h, ← List.drop_drop, drop_four, List.drop_left' (by rw [length_bitsOfNat])]

theorem val_j₁F :
    val (j₁F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) = (c.l₁.var : ℕ) := by
  rw [j₁F, val_padTo, val, bitsOf_field]
  show bitsVal (ibOf 0 ℓ _) = _
  rw [ibOf_getD _ 0 ℓ (by rw [length_clauseInput5]; omega), List.drop_zero, clauseInput5_eq,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₁.var.isLt]

theorem val_j₂F :
    val (j₂F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) = (c.l₂.var : ℕ) := by
  rw [j₂F, val_padTo, val, bitsOf_field]
  show bitsVal (ibOf ℓ ℓ _) = _
  rw [ibOf_getD _ ℓ ℓ (by rw [length_clauseInput5]; omega), clauseInput5_eq,
    List.drop_left' (by rw [length_bitsOfNat]), List.take_left' (by rw [length_bitsOfNat]),
    bitsVal_bitsOfNat, Nat.mod_eq_of_lt c.l₂.var.isLt]

theorem val_j₃F : val (j₃F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) =
    (c.l₃.var : ℕ) := by
  rw [j₃F, val, bitsOf_field]
  show bitsVal (ibOf (2 * ℓ) r _) = _
  rw [ibOf_getD _ (2 * ℓ) r (by rw [length_clauseInput5]; omega), drop_two,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₃.var.isLt]

theorem val_j₄F : val (j₄F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) =
    (c.l₄.var : ℕ) := by
  rw [j₄F, val, bitsOf_field]
  show bitsVal (ibOf (2 * ℓ + r) r _) = _
  rw [ibOf_getD _ (2 * ℓ + r) r (by rw [length_clauseInput5]; omega), drop_three,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₄.var.isLt]

theorem val_j₅F : val (j₅F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) =
    (c.l₅.var : ℕ) := by
  rw [j₅F, val, bitsOf_field]
  show bitsVal (ibOf (2 * ℓ + 2 * r) r _) = _
  rw [ibOf_getD _ (2 * ℓ + 2 * r) r (by rw [length_clauseInput5]; omega), drop_four,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₅.var.isLt]

theorem eval_sgF (k : ℕ) :
    (Fml.inp (sgOff ℓ r + k)).eval (fun i => (clauseInput5 ℓ r c).getD i false) =
      (sgList c).getD k false := by
  show (clauseInput5 ℓ r c).getD (sgOff ℓ r + k) false = _
  rw [← getD_drop_eq, drop_signs]

end Slices

/-! ## The formula decides the conditions -/

theorem eval_xor_iff (f g : Fml) (x : ℕ → Bool) :
    (xor f g).eval x = true ↔ f.eval x ≠ g.eval x := by
  rw [eval_xor]
  cases f.eval x <;> cases g.eval x <;> simp

theorem eval_headD_iff {fs : List Fml} (hne : fs ≠ []) (x : ℕ → Bool) :
    (fs.headD (const false)).eval x = true ↔ ¬ val fs x % 2 = 0 := by
  have h := headD_eval_toNat fs x hne
  cases hb : (fs.headD (const false)).eval x
  · rw [hb] at h; simp at h ⊢; omega
  · rw [hb] at h; simp at h ⊢; omega

/-- **The link formula decides the link conditions.** -/
theorem eval_linkFml {ℓ r T : ℕ} (hℓr : ℓ ≤ r) (hr : 1 ≤ r) (hT : 2 * T < 2 ^ r)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (linkFml ℓ r T).eval (fun i => (clauseInput5 ℓ r c).getD i false) = true ↔ Link ℓ r T c := by
  have h1 := length_j₁F ℓ r hℓr
  have h2 := length_j₂F ℓ r hℓr
  have hne₁ : j₁F ℓ r ≠ [] := by
    intro hcon; rw [hcon, List.length_nil] at h1; omega
  have hne₂ : j₂F ℓ r ≠ [] := by
    intro hcon; rw [hcon, List.length_nil] at h2; omega
  set x : ℕ → Bool := fun i => (clauseInput5 ℓ r c).getD i false with hx
  -- the five indices and the five signs
  have e₁ : val (j₁F ℓ r) x = (c.l₁.var : ℕ) := val_j₁F c
  have e₂ : val (j₂F ℓ r) x = (c.l₂.var : ℕ) := val_j₂F c
  have e₃ : val (j₃F ℓ r) x = (c.l₃.var : ℕ) := val_j₃F c
  have e₄ : val (j₄F ℓ r) x = (c.l₄.var : ℕ) := val_j₄F c
  have e₅ : val (j₅F ℓ r) x = (c.l₅.var : ℕ) := val_j₅F c
  have g₁ : (s₁F ℓ r).eval x = c.l₁.pos := eval_sgF c 0
  have g₂ : (s₂F ℓ r).eval x = c.l₂.pos := eval_sgF c 1
  have g₃ : (s₃F ℓ r).eval x = c.l₃.pos := eval_sgF c 2
  have g₄ : (s₄F ℓ r).eval x = c.l₄.pos := eval_sgF c 3
  have g₅ : (s₅F ℓ r).eval x = c.l₅.pos := eval_sgF c 4
  -- the tests
  have lt₁ : (ltConst (j₁F ℓ r) (nbits r (2 * T))).eval x = true ↔ (c.l₁.var : ℕ) < 2 * T := by
    rw [eval_ltN h1 hT, e₁]
  have lt₂ : (ltConst (j₂F ℓ r) (nbits r (2 * T))).eval x = true ↔ (c.l₂.var : ℕ) < 2 * T := by
    rw [eval_ltN h2 hT, e₂]
  have eq₁₃ : (eqFields (j₁F ℓ r) (j₃F ℓ r)).eval x = true ↔
      (c.l₁.var : ℕ) = (c.l₃.var : ℕ) := by
    rw [eval_eqF h1 (length_j₃F ℓ r), e₁, e₃]
  have add₂₃ : (addConstRel (j₂F ℓ r) (j₃F ℓ r) (nbits r (2 * T))).eval x = true ↔
      (c.l₃.var : ℕ) = (c.l₂.var : ℕ) + 2 * T := by
    rw [eval_addN h2 (length_j₃F ℓ r) hT, e₂, e₃]
  have eq₃₄ : (eqFields (j₃F ℓ r) (j₄F ℓ r)).eval x = true ↔
      (c.l₃.var : ℕ) = (c.l₄.var : ℕ) := by
    rw [eval_eqF (length_j₃F ℓ r) (length_j₄F ℓ r), e₃, e₄]
  have eq₄₅ : (eqFields (j₄F ℓ r) (j₅F ℓ r)).eval x = true ↔
      (c.l₄.var : ℕ) = (c.l₅.var : ℕ) := by
    rw [eval_eqF (length_j₄F ℓ r) (length_j₅F ℓ r), e₄, e₅]
  have par₁ : ((j₁F ℓ r).headD (const false)).eval x = true ↔ ¬ (c.l₁.var : ℕ) % 2 = 0 := by
    rw [eval_headD_iff hne₁, e₁]
  have par₂ : ((j₂F ℓ r).headD (const false)).eval x = true ↔ ¬ (c.l₂.var : ℕ) % 2 = 0 := by
    rw [eval_headD_iff hne₂, e₂]
  rw [linkFml, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    eval_andList₃, eval_andList₂, eval_not_iff, eval_xor_iff, lt₁, lt₂, eq₁₃, add₂₃, eq₃₄, eq₄₅,
    par₁, par₂, g₁, g₂, g₃, g₄, g₅, Link]
  constructor
  · rintro (⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · exact Or.inl ⟨a, b, d⟩
    · exact Or.inr (Or.inl ⟨a, b, d⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b⟩))))))
  · rintro (⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · exact Or.inl ⟨a, b, d⟩
    · exact Or.inr (Or.inl ⟨a, b, d⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b⟩))))))

end MIPRE.TM.CookLevin.Desc
