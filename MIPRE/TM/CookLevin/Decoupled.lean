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

/-! ## What a satisfying five-tuple is

Following the paper: for a fixed triple of indices the three signs of the *other* blocks
range over all of `{0,1}³`, so a decoupled clause is satisfied exactly when the literals of
the blocks the condition constrains are. Rows 8 and 9 therefore read as equalities of whole
blocks, and rows 2 and 3 as equalities of single bits. -/

/-- The index `0` of a block. -/
def zeroIdx (k : ℕ) : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩

/-- A literal of a block that the given assignment falsifies. -/
def offLit {k : ℕ} (w : Fin (2 ^ k) → Bool) : Lit (Fin (2 ^ k)) :=
  ⟨zeroIdx k, !w (zeroIdx k)⟩

@[simp] theorem offLit_eval {k : ℕ} (w : Fin (2 ^ k) → Bool) : (offLit w).eval w = false := by
  cases hw : w (zeroIdx k) <;> simp [offLit, Lit.eval, hw]

/-- Two literals of opposite sign force the two bits to agree. -/
theorem eq_of_lit_or {V W : Type*} (u : V → Bool) (v : W → Bool) (i : V) (j : W)
    (h : ∀ o : Bool, ((Lit.mk i o).eval u || (Lit.mk j (!o)).eval v) = true) : u i = v j := by
  have h1 := h true
  have h2 := h false
  cases hu : u i
  · cases hv : v j
    · rfl
    · simp [Lit.eval, hu, hv] at h1
  · cases hv : v j
    · simp [Lit.eval, hu, hv] at h2
    · rfl

/-- One literal forced true. -/
theorem eq_of_lit {V : Type*} (u : V → Bool) (i : V) (o : Bool)
    (h : (Lit.mk i o).eval u = true) : u i = o := by
  cases o <;> cases hu : u i <;> simp [Lit.eval, hu] at h ⊢

/-- The three-block half: the described 3SAT formula on the three auxiliary blocks. -/
def Tri {r : ℕ} (φ : Cnf3 (Fin (2 ^ r))) (w₁ w₂ w₃ : Fin (2 ^ r) → Bool) : Prop :=
  ∀ c ∈ φ, (c.l₁.eval w₁ || c.l₂.eval w₂ || c.l₃.eval w₃) = true

/-- The link half: what rows 2 to 9 force. -/
structure LinkSat (ℓ r T : ℕ) (a b : Fin (2 ^ ℓ) → Bool) (w₁ w₂ w₃ : Fin (2 ^ r) → Bool) :
    Prop where
  aLow : ∀ (i : Fin (2 ^ ℓ)) (j : Fin (2 ^ r)), (i : ℕ) < 2 * T → (i : ℕ) = (j : ℕ) →
    a i = w₁ j
  bLow : ∀ (i : Fin (2 ^ ℓ)) (j : Fin (2 ^ r)), (i : ℕ) < 2 * T → (j : ℕ) = (i : ℕ) + 2 * T →
    b i = w₁ j
  aPad : ∀ i : Fin (2 ^ ℓ), ¬ (i : ℕ) < 2 * T → a i = decide ((i : ℕ) % 2 = 0)
  bPad : ∀ i : Fin (2 ^ ℓ), ¬ (i : ℕ) < 2 * T → b i = decide ((i : ℕ) % 2 = 0)
  w12 : ∀ i j : Fin (2 ^ r), (i : ℕ) = (j : ℕ) → w₁ i = w₂ j
  w23 : ∀ i j : Fin (2 ^ r), (i : ℕ) = (j : ℕ) → w₂ i = w₃ j

/-- **The two halves of satisfaction.** -/
theorem sat_formula5_iff (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
    (hℓr : ℓ ≤ mOf e Gc) (hr : 1 ≤ mOf e Gc) (hT : 2 * T < 2 ^ mOf e Gc)
    (a b : Fin (2 ^ ℓ) → Bool) (w₁ w₂ w₃ : Fin (2 ^ mOf e Gc) → Bool) :
    ((descCirc5 ℓ T e D n x y).formula5 ℓ (mOf e Gc)).Sat a b w₁ w₂ w₃ ↔
      Tri ((descCirc e T D n x y).formula3 (mOf e Gc)) w₁ w₂ w₃ ∧
        LinkSat ℓ (mOf e Gc) T a b w₁ w₂ w₃ := by
  constructor
  · intro hsat
    have key : ∀ c, (lastThree c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ∨
        Link ℓ (mOf e Gc) T c) → Clause5.eval a b w₁ w₂ w₃ c = true := fun c hc =>
      hsat c ((mem_formula5_iff ℓ T e D n x y hℓr hr hT c).mpr hc)
    refine ⟨?_, ?_⟩
    · intro c₃ hc₃
      have h := key ⟨offLit a, offLit b, c₃.l₁, c₃.l₂, c₃.l₃⟩ (Or.inl hc₃)
      simpa [Clause5.eval] using h
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j hi hij
        refine eq_of_lit_or a w₁ i j fun o => ?_
        have h := key ⟨⟨i, o⟩, offLit b, ⟨j, !o⟩, offLit w₂, offLit w₃⟩
          (Or.inr (Or.inl ⟨hi, hij, by simp⟩))
        simpa [Clause5.eval] using h
      · intro i j hi hij
        refine eq_of_lit_or b w₁ i j fun o => ?_
        have h := key ⟨offLit a, ⟨i, o⟩, ⟨j, !o⟩, offLit w₂, offLit w₃⟩
          (Or.inr (Or.inr (Or.inl ⟨hi, hij, by simp⟩)))
        simpa [Clause5.eval] using h
      · intro i hi
        rcases Nat.eq_zero_or_pos ((i : ℕ) % 2) with hp | hp
        · have h := key ⟨⟨i, true⟩, offLit b, offLit w₁, offLit w₂, offLit w₃⟩
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, hp, rfl⟩))))
          have := eq_of_lit a i true (by simpa [Clause5.eval] using h)
          rw [this, hp]
          rfl
        · have hp' : ¬ (i : ℕ) % 2 = 0 := by omega
          have h := key ⟨⟨i, false⟩, offLit b, offLit w₁, offLit w₂, offLit w₃⟩
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, hp', rfl⟩)))))
          have := eq_of_lit a i false (by simpa [Clause5.eval] using h)
          rw [this, decide_eq_false hp']
      · intro i hi
        rcases Nat.eq_zero_or_pos ((i : ℕ) % 2) with hp | hp
        · have h := key ⟨offLit a, ⟨i, true⟩, offLit w₁, offLit w₂, offLit w₃⟩
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, hp, rfl⟩))))))
          have := eq_of_lit b i true (by simpa [Clause5.eval] using h)
          rw [this, hp]
          rfl
        · have hp' : ¬ (i : ℕ) % 2 = 0 := by omega
          have h := key ⟨offLit a, ⟨i, false⟩, offLit w₁, offLit w₂, offLit w₃⟩
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, hp', rfl⟩)))))))
          have := eq_of_lit b i false (by simpa [Clause5.eval] using h)
          rw [this, decide_eq_false hp']
      · intro i j hij
        refine eq_of_lit_or w₁ w₂ i j fun o => ?_
        have h := key ⟨offLit a, offLit b, ⟨i, o⟩, ⟨j, !o⟩, offLit w₃⟩
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hij, by simp⟩))))))))
        simpa [Clause5.eval] using h
      · intro i j hij
        refine eq_of_lit_or w₂ w₃ i j fun o => ?_
        have h := key ⟨offLit a, offLit b, offLit w₁, ⟨i, o⟩, ⟨j, !o⟩⟩
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hij, by simp⟩))))))))
        simpa [Clause5.eval] using h
  · rintro ⟨htri, hlink⟩ c hc
    rcases (mem_formula5_iff ℓ T e D n x y hℓr hr hT c).mp hc with h3 | hlk
    · have h := htri (lastThree c) h3
      simp only [lastThree, Bool.or_eq_true] at h
      simp only [Clause5.eval, Bool.or_eq_true]
      rcases h with (hc | hd) | he
      · exact Or.inl (Or.inl (Or.inr hc))
      · exact Or.inl (Or.inr hd)
      · exact Or.inr he
    · rcases hlk with ⟨hi, hij, ho⟩ | ⟨hi, hij, ho⟩ | ⟨hi, hp, ho⟩ | ⟨hi, hp, ho⟩ |
        ⟨hi, hp, ho⟩ | ⟨hi, hp, ho⟩ | ⟨hij, ho⟩ | ⟨hij, ho⟩
      · have h := hlink.aLow c.l₁.var c.l₃.var hi hij
        cases hp1 : c.l₁.pos <;> cases hp3 : c.l₃.pos <;> cases hv : w₁ c.l₃.var <;>
          simp_all [Clause5.eval, Lit.eval]
      · have h := hlink.bLow c.l₂.var c.l₃.var hi hij
        cases hp2 : c.l₂.pos <;> cases hp3 : c.l₃.pos <;> cases hv : w₁ c.l₃.var <;>
          simp_all [Clause5.eval, Lit.eval]
      · have h := hlink.aPad c.l₁.var hi
        simp_all [Clause5.eval, Lit.eval]
      · have h := hlink.aPad c.l₁.var hi
        simp_all [Clause5.eval, Lit.eval]
      · have h := hlink.bPad c.l₂.var hi
        simp_all [Clause5.eval, Lit.eval]
      · have h := hlink.bPad c.l₂.var hi
        simp_all [Clause5.eval, Lit.eval]
      · have h := hlink.w12 c.l₃.var c.l₄.var hij
        cases hp3 : c.l₃.pos <;> cases hp4 : c.l₄.pos <;> cases hv : w₂ c.l₄.var <;>
          simp_all [Clause5.eval, Lit.eval]
      · have h := hlink.w23 c.l₄.var c.l₅.var hij
        cases hp4 : c.l₄.pos <;> cases hp5 : c.l₅.pos <;> cases hv : w₃ c.l₅.var <;>
          simp_all [Clause5.eval, Lit.eval]

end MIPRE.TM.CookLevin.Desc
