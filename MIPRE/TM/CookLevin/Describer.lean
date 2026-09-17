/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Index

/-!
# The describer circuit and the clauses it describes

`descCirc e T D n x y` is the circuit of the describer: the flattening of the formula
`tableauPlusF` on the candidate that reads the three `m`-bit indices and the three signs off
its `3m + 3` inputs (`candOf`). `mem_formula3_iff` is what it describes: a clause of
`Fin (2 ^ m)` is accepted iff its three indices decode to the literals of a clause of
`tableauPlus` — the tableau of `U` on the input tapes `fixedOf` together with the two
answer-end clauses (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## Reading the input bits of a clause -/

theorem getD_drop_eq (l : BitStr) (k i : ℕ) : (l.drop k).getD i false = l.getD (k + i) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem ibOf_getD (l : BitStr) (b n : ℕ) (h : b + n ≤ l.length) :
    ibOf b n (fun i => l.getD i false) = (l.drop b).take n := by
  have hlen : (ibOf b n (fun i => l.getD i false)).length = ((l.drop b).take n).length := by
    simp [List.length_take, List.length_drop]; omega
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have hi : i < n := by simpa [ibOf] using h1
  have e1 : (ibOf b n (fun i => l.getD i false))[i] = l.getD (b + i) false := by
    simp [ibOf, List.getElem_map, List.getElem_range']
  have e2 : ((l.drop b).take n)[i] = l[b + i] := by
    simp [List.getElem_take, List.getElem_drop]
  rw [e1, e2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-! ## The input tapes -/

/-- The input tapes of the interpreter machine: the program, the index, the time bound in
unary and the two questions are fixed; the two answer tapes are free. -/
def fixedOf (D : Prog) (n T : ℕ) (x y : BitStr) : Fin 7 → Option (List Sym) :=
  ![some (S D.toData), some (S (encode n)), some (List.replicate T .one), some (S (encode x)),
    some (S (encode y)), none, none]

theorem freeSpec (D : Prog) (n T : ℕ) (x y : BitStr) : FreeSpec (fixedOf D n T x y) [5, 6] where
  lt j hj := by simp at hj; rcases hj with rfl | rfl <;> omega
  iff j := by fin_cases j <;> simp [fixedOf]

/-- The tapes are short enough for the tableau. -/
def FixedLen (e : ℕ) (D : Prog) (n T : ℕ) (x y : BitStr) : Prop :=
  ∀ (j : Fin 7) (s : List Sym), fixedOf D n T x y j = some s → s.length ≤ Sof e

/-- The value formulas of the fixed tapes. -/
noncomputable def tabsOf (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) (A : FieldsF) :
    List (ℕ × Fml) :=
  [(0, cellValF e A (codesOf (S D.toData))), (1, cellValF e A (codesOf (S (encode n)))),
    (2, unaryValF e T A), (3, cellValF e A (codesOf (S (encode x)))),
    (4, cellValF e A (codesOf (S (encode y))))]

theorem tapeSpec (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) (G : ℕ) {A : FieldsF}
    (hA : A.Lengths e G) (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y) :
    TapeSpec e A (fixedOf D n T x y) (tabsOf e T D n x y A) := by
  have hval : ∀ (j : Fin 7) (s : List Sym), fixedOf D n T x y j = some s →
      ∀ x' : ℕ → Bool, (cellValF e A (codesOf s)).eval x' =
        decide ((evalFields A x').v = cellCode s (Sof e) (evalFields A x').p) := by
    intro j s hj x'
    exact Bool.eq_decide_of_iff (eval_cellValF e G hA x' s (hlen j s hj))
  constructor
  · intro jv hjv
    simp only [tabsOf, List.mem_cons, List.not_mem_nil, or_false] at hjv
    rcases hjv with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, S D.toData, rfl, by simp [fixedOf], hval 0 _ (by simp [fixedOf])⟩
    · exact ⟨1, S (encode n), rfl, by simp [fixedOf], hval 1 _ (by simp [fixedOf])⟩
    · refine ⟨2, List.replicate T .one, rfl, by simp [fixedOf], fun x' => ?_⟩
      exact Bool.eq_decide_of_iff (eval_unaryValF e G hA x' T hT)
    · exact ⟨3, S (encode x), rfl, by simp [fixedOf], hval 3 _ (by simp [fixedOf])⟩
    · exact ⟨4, S (encode y), rfl, by simp [fixedOf], hval 4 _ (by simp [fixedOf])⟩
  · intro j s hj
    fin_cases j
    · exact ⟨cellValF e A (codesOf (S D.toData)), by simp [tabsOf]⟩
    · exact ⟨cellValF e A (codesOf (S (encode n))), by simp [tabsOf]⟩
    · exact ⟨unaryValF e T A, by simp [tabsOf]⟩
    · exact ⟨cellValF e A (codesOf (S (encode x))), by simp [tabsOf]⟩
    · exact ⟨cellValF e A (codesOf (S (encode y))), by simp [tabsOf]⟩
    · simp [fixedOf] at hj
    · simp [fixedOf] at hj

theorem tabsOf_inputsLt (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) {N : ℕ} {A : FieldsF}
    (hA : A.InputsLt N) : ∀ jv ∈ tabsOf e T D n x y A, jv.2.InputsLt N := by
  intro jv hjv
  simp only [tabsOf, List.mem_cons, List.not_mem_nil, or_false] at hjv
  rcases hjv with rfl | rfl | rfl | rfl | rfl
  · exact InputsLt.cellValF e hA _
  · exact InputsLt.cellValF e hA _
  · exact InputsLt.unaryValF e hA _
  · exact InputsLt.cellValF e hA _
  · exact InputsLt.cellValF e hA _

/-! ## The candidate of formulas -/

/-- The candidate the describer reads off its inputs: the three `m`-bit indices at bases `0`,
`m`, `2m` and the three signs at `3m`, `3m + 1`, `3m + 2`. -/
noncomputable def candOf (e G T : ℕ) : CandF :=
  ⟨litFields e G T 0, inp (3 * mOf e G), litFields e G T (mOf e G), inp (3 * mOf e G + 1),
    litFields e G T (2 * mOf e G), inp (3 * mOf e G + 2)⟩

theorem candOf_lengths (e G T : ℕ) : (candOf e G T).Lengths e G :=
  ⟨litFields_lengths e G T 0, litFields_lengths e G T _, litFields_lengths e G T _⟩

theorem candOf_inputsLt (e G T : ℕ) : (candOf e G T).InputsLt (3 * mOf e G + 3) where
  A₁ := litFields_inputsLt e G T 0 _ (by omega)
  σ₁ := by show 3 * mOf e G < 3 * mOf e G + 3; omega
  A₂ := litFields_inputsLt e G T _ _ (by omega)
  σ₂ := by show 3 * mOf e G + 1 < 3 * mOf e G + 3; omega
  A₃ := litFields_inputsLt e G T _ _ (by omega)
  σ₃ := by show 3 * mOf e G + 2 < 3 * mOf e G + 3; omega

/-! ## The circuit -/

/-- The formula of the describer. -/
noncomputable def descFml (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  tableauPlusF e Gc T (tabsOf e T D n x y (litFields e Gc T 0)) [5, 6] (tplsOf Gc chk)
    (candOf e Gc T)

/-- **The describer circuit**: the flattening of `descFml` on `3 m + 3` inputs. -/
noncomputable def descCirc (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Circuit :=
  (descFml e T D n x y).toCircuit (3 * mOf e Gc + 3)

theorem descCirc_inputs (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descCirc e T D n x y).inputs = 3 * mOf e Gc + 3 := rfl

theorem descFml_inputsLt (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descFml e T D n x y).InputsLt (3 * mOf e Gc + 3) :=
  InputsLt.tableauPlusF e Gc T _
    (tabsOf_inputsLt e T D n x y (candOf_inputsLt e Gc T).A₁) _ _ (candOf_inputsLt e Gc T)

theorem descCirc_wellFormed (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descCirc e T D n x y).WellFormed :=
  Fml.toCircuit_wellFormed _ (descFml_inputsLt e T D n x y)

theorem descCirc_size (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descCirc e T D n x y).size = (descFml e T D n x y).size :=
  Fml.toCircuit_size _ _

/-! ## What the circuit describes -/

/-- The candidate of a clause: the fields of its three indices and its three signs. -/
noncomputable def candOfClause (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc))) : Cand :=
  ⟨fieldsOf e Gc T (bitsOfNat (mOf e Gc) c.l₁.var), c.l₁.pos,
    fieldsOf e Gc T (bitsOfNat (mOf e Gc) c.l₂.var), c.l₂.pos,
    fieldsOf e Gc T (bitsOfNat (mOf e Gc) c.l₃.var), c.l₃.pos⟩

section Eval

variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))

theorem clauseInput_eq (m : ℕ) (c' : Clause3 (Fin (2 ^ m))) :
    clauseInput m c' = bitsOfNat m c'.l₁.var ++ (bitsOfNat m c'.l₂.var ++
      (bitsOfNat m c'.l₃.var ++ [c'.l₁.pos, c'.l₂.pos, c'.l₃.pos])) := by
  rw [clauseInput, List.append_assoc, List.append_assoc]

/-- The bits of the three blocks of the input of a clause. -/
theorem ibOf_clauseInput_zero :
    ibOf 0 (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      bitsOfNat (mOf e Gc) c.l₁.var := by
  rw [ibOf_getD _ _ _ (by rw [length_clauseInput]; omega), List.drop_zero, clauseInput_eq,
    List.take_left' (by rw [length_bitsOfNat])]

theorem ibOf_clauseInput_one :
    ibOf (mOf e Gc) (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      bitsOfNat (mOf e Gc) c.l₂.var := by
  rw [ibOf_getD _ _ _ (by rw [length_clauseInput]; omega), clauseInput_eq,
    List.drop_left' (by rw [length_bitsOfNat]), List.take_left' (by rw [length_bitsOfNat])]

theorem ibOf_clauseInput_two :
    ibOf (2 * mOf e Gc) (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      bitsOfNat (mOf e Gc) c.l₃.var := by
  rw [ibOf_getD _ _ _ (by rw [length_clauseInput]; omega)]
  have h2 : 2 * mOf e Gc = mOf e Gc + mOf e Gc := by omega
  rw [h2, ← List.drop_drop, clauseInput_eq, List.drop_left' (by rw [length_bitsOfNat]),
    List.drop_left' (by rw [length_bitsOfNat]), List.take_left' (by rw [length_bitsOfNat])]

theorem drop_clauseInput :
    (clauseInput (mOf e Gc) c).drop (3 * mOf e Gc) = [c.l₁.pos, c.l₂.pos, c.l₃.pos] := by
  have h3 : 3 * mOf e Gc = mOf e Gc + (mOf e Gc + mOf e Gc) := by omega
  rw [h3, ← List.drop_drop, ← List.drop_drop, clauseInput_eq,
    List.drop_left' (by rw [length_bitsOfNat]), List.drop_left' (by rw [length_bitsOfNat]),
    List.drop_left' (by rw [length_bitsOfNat])]

theorem getD_clauseInput_sign0 :
    (clauseInput (mOf e Gc) c).getD (3 * mOf e Gc) false = c.l₁.pos := by
  have h := getD_drop_eq (clauseInput (mOf e Gc) c) (3 * mOf e Gc) 0
  rw [drop_clauseInput] at h
  simpa using h.symm

theorem getD_clauseInput_sign1 :
    (clauseInput (mOf e Gc) c).getD (3 * mOf e Gc + 1) false = c.l₂.pos := by
  have h := getD_drop_eq (clauseInput (mOf e Gc) c) (3 * mOf e Gc) 1
  rw [drop_clauseInput] at h
  simpa using h.symm

theorem getD_clauseInput_sign2 :
    (clauseInput (mOf e Gc) c).getD (3 * mOf e Gc + 2) false = c.l₃.pos := by
  have h := getD_drop_eq (clauseInput (mOf e Gc) c) (3 * mOf e Gc) 2
  rw [drop_clauseInput] at h
  simpa using h.symm

/-- The candidate of formulas, evaluated on the input bits of a clause, is the candidate of
the clause. -/
theorem evalCand_candOf (hT : T ≤ Sof e) :
    evalCand (candOf e Gc T) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      candOfClause e T c := by
  have hlf : ∀ b, evalFields (litFields e Gc T b) (fun i => (clauseInput (mOf e Gc) c).getD i false)
      = fieldsOf e Gc T (ibOf b (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false)) :=
    fun b => evalFields_litFields e Gc T b _ hT
  simp only [evalCand, candOf, candOfClause, hlf, ibOf_clauseInput_zero, ibOf_clauseInput_one,
    ibOf_clauseInput_two, eval, getD_clauseInput_sign0, getD_clauseInput_sign1,
    getD_clauseInput_sign2]

/-- **What the describer describes**: a clause is accepted iff its three indices decode to the
literals of a clause of `tableauPlus`. -/
theorem mem_formula3_iff (D : Prog) (n : ℕ) (x y : BitStr) (hT : T ≤ Sof e)
    (hlen : FixedLen e D n T x y) (hTm : T + 3 < 2 ^ W e) :
    c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ↔
      ∃ cl ∈ tableauPlus e T (fixedOf D n T x y) chk, (candOfClause e T c).Dec e Gc cl := by
  have h1 : (descCirc e T D n x y).evalBits (clauseInput (mOf e Gc) c) =
      (descFml e T D n x y).eval (fun i => (clauseInput (mOf e Gc) c).getD i false) :=
    Fml.evalBits_toCircuit _ _ _
  have h2 := eval_tableauPlusF e T (candOf_lengths e Gc T)
    (fun i => (clauseInput (mOf e Gc) c).getD i false)
    (tapeSpec e T D n x y Gc (litFields_lengths e Gc T 0) hT hlen) (freeSpec D n T x y) hTm
  rw [evalCand_candOf e T c hT] at h2
  show (descCirc e T D n x y).evalBits (clauseInput (mOf e Gc) c) = true ↔ _
  rw [h1]
  exact h2

end Eval

end MIPRE.TM.CookLevin.Desc
