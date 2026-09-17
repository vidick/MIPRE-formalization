/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Link

/-!
# The decoupled describer, and the clauses it describes

The describer of `lem:decoupled-5sat`: the 3SAT describer of `thm:succinct-sat`, its inputs
renamed into the five-block layout, in disjunction with the link formula of `Link.lean`, all
flattened once to a circuit. `mem_formula5_iff` is the bridge — a clause is accepted exactly
when the 3-clause of its last three literals is accepted by the 3SAT describer, or the clause
satisfies one of the eight link conditions (`planning/decoupled-5sat.md`, A1c).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## Where the 3SAT describer's inputs go -/

/-- The renaming: the `3r` index bits of the 3SAT describer sit after the two answer
indices, and its three signs after the two answer signs. -/
def rho (ℓ r : ℕ) (k : ℕ) : ℕ := if k < 3 * r then k + 2 * ℓ else k + 2 * ℓ + 2

theorem rho_lt {ℓ r k : ℕ} (h : k < 3 * r + 3) : rho ℓ r k < 2 * ℓ + 3 * r + 5 := by
  unfold rho
  split <;> omega

/-- The 3-clause of the last three literals of a decoupled clause. -/
def lastThree {ℓ r : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    Clause3 (Fin (2 ^ r)) := ⟨c.l₃, c.l₄, c.l₅⟩

/-! ## The renaming reads the right bits -/

theorem getD_append_left {α : Type*} (pre u : List α) (d : α) {k : ℕ} (h : k < pre.length) :
    (pre ++ u).getD k d = pre.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {α : Type*} (pre u : List α) (d : α) (t : ℕ) :
    (pre ++ u).getD (pre.length + t) d = u.getD t d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem clauseInput_eq' (r : ℕ) (c : Clause3 (Fin (2 ^ r))) :
    clauseInput r c = (bitsOfNat r c.l₁.var ++ bitsOfNat r c.l₂.var ++ bitsOfNat r c.l₃.var) ++
      [c.l₁.pos, c.l₂.pos, c.l₃.pos] := by
  rw [clauseInput]

theorem drop_two' {ℓ r : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (clauseInput5 ℓ r c).drop (2 * ℓ) =
      (bitsOfNat r c.l₃.var ++ bitsOfNat r c.l₄.var ++ bitsOfNat r c.l₅.var) ++ sgList c := by
  rw [drop_two, List.append_assoc, List.append_assoc]

/-- **The renaming reads the 3SAT describer's clause off the five-block input.** -/
theorem getD_rho {ℓ r : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
    {k : ℕ} (hk : k < 3 * r + 3) :
    (clauseInput5 ℓ r c).getD (rho ℓ r k) false =
      (clauseInput r (lastThree c)).getD k false := by
  set pre : BitStr :=
    bitsOfNat r c.l₃.var ++ bitsOfNat r c.l₄.var ++ bitsOfNat r c.l₅.var with hpre
  have hlen : pre.length = 3 * r := by rw [hpre]; simp [length_bitsOfNat]; omega
  have h5 : clauseInput r (lastThree c) = pre ++ [c.l₃.pos, c.l₄.pos, c.l₅.pos] := by
    rw [clauseInput, hpre, lastThree]
  rcases lt_or_ge k (3 * r) with h | h
  · rw [rho, if_pos h, Nat.add_comm k (2 * ℓ), ← getD_drop_eq, drop_two',
      getD_append_left pre (sgList c) false (by rw [hlen]; exact h), h5,
      getD_append_left pre _ false (by rw [hlen]; exact h)]
  · obtain ⟨t, rfl⟩ : ∃ t, k = 3 * r + t := ⟨k - 3 * r, by omega⟩
    have ht : t < 3 := by omega
    have hL : (clauseInput5 ℓ r c).getD (rho ℓ r (3 * r + t)) false =
        (sgList c).getD (t + 2) false := by
      rw [rho, if_neg (by omega),
        show 3 * r + t + 2 * ℓ + 2 = sgOff ℓ r + (t + 2) from by unfold sgOff; omega]
      show (Fml.inp (sgOff ℓ r + (t + 2))).eval
        (fun i => (clauseInput5 ℓ r c).getD i false) = _
      exact eval_sgF c (t + 2)
    rw [hL, h5, show 3 * r + t = pre.length + t from by rw [hlen], getD_append_right]
    interval_cases t <;> rfl

/-! ## The describer -/

/-- The formula of the decoupled describer: the 3SAT describer's formula, its inputs renamed
into the five-block layout, in disjunction with the link formula. -/
noncomputable def descFml5 (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  or (Fml.remap (rho ℓ (mOf e Gc)) (descFml e T D n x y)) (linkFml ℓ (mOf e Gc) T)

/-- **The decoupled describer circuit**: the flattening of `descFml5` on `2ℓ + 3r + 5`
inputs. -/
noncomputable def descCirc5 (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Circuit :=
  (descFml5 ℓ T e D n x y).toCircuit (2 * ℓ + 3 * mOf e Gc + 5)

theorem descCirc5_inputs (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descCirc5 ℓ T e D n x y).inputs = 2 * ℓ + 3 * mOf e Gc + 5 := rfl

theorem descFml5_inputsLt (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
    (hℓr : ℓ ≤ mOf e Gc) :
    (descFml5 ℓ T e D n x y).InputsLt (2 * ℓ + 3 * mOf e Gc + 5) :=
  InputsLt.or'
    (Fml.InputsLt.remap (rho ℓ (mOf e Gc)) (fun _ hk => rho_lt hk) _
      (descFml_inputsLt e T D n x y))
    (InputsLt.linkFml ℓ (mOf e Gc) T hℓr)

theorem descCirc5_wellFormed (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
    (hℓr : ℓ ≤ mOf e Gc) : (descCirc5 ℓ T e D n x y).WellFormed :=
  Fml.toCircuit_wellFormed _ (descFml5_inputsLt ℓ T e D n x y hℓr)

theorem descCirc5_size (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descCirc5 ℓ T e D n x y).size = (descFml5 ℓ T e D n x y).size :=
  Fml.toCircuit_size _ _

/-- **What the decoupled describer accepts**: a clause is accepted exactly when the 3-clause
of its last three literals is accepted by the 3SAT describer, or the clause satisfies one of
the eight link conditions. -/
theorem mem_formula5_iff (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
    (hℓr : ℓ ≤ mOf e Gc) (hr : 1 ≤ mOf e Gc) (hT : 2 * T < 2 ^ mOf e Gc)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ mOf e Gc)) (Fin (2 ^ mOf e Gc))
      (Fin (2 ^ mOf e Gc))) :
    c ∈ (descCirc5 ℓ T e D n x y).formula5 ℓ (mOf e Gc) ↔
      lastThree c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ∨
        Link ℓ (mOf e Gc) T c := by
  have h3 : (descFml e T D n x y).eval
        (fun k => (clauseInput5 ℓ (mOf e Gc) c).getD (rho ℓ (mOf e Gc) k) false) =
      (descFml e T D n x y).eval
        (fun k => (clauseInput (mOf e Gc) (lastThree c)).getD k false) :=
    Fml.eval_congr_of_lt (fun k hk => getD_rho c hk) _ (descFml_inputsLt e T D n x y)
  show (descCirc5 ℓ T e D n x y).evalBits (clauseInput5 ℓ (mOf e Gc) c) = true ↔ _
  rw [descCirc5, Fml.evalBits_toCircuit, descFml5, eval_or_iff, Fml.eval_remap, h3,
    eval_linkFml hℓr hr hT c]
  constructor
  · rintro (h | h)
    · exact Or.inl (by
        show (descCirc e T D n x y).evalBits (clauseInput (mOf e Gc) (lastThree c)) = true
        rw [descCirc, Fml.evalBits_toCircuit]; exact h)
    · exact Or.inr h
  · rintro (h | h)
    · refine Or.inl ?_
      have : (descCirc e T D n x y).evalBits (clauseInput (mOf e Gc) (lastThree c)) = true := h
      rwa [descCirc, Fml.evalBits_toCircuit] at this
    · exact Or.inr h

end MIPRE.TM.CookLevin.Desc
