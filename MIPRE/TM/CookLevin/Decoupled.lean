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

/-! ## The shifted candidate

The 3SAT describer's inputs cannot be *renamed* into the five-block layout by a program: the
renaming is `k ↦ k + 2ℓ` below `3r` and `k ↦ k + 2ℓ + 2` above, and deciding which needs a
comparison of two binary numbers, which the ambient model does not have. So the describer is
rebuilt on the shifted layout instead — the candidate reads its three field records at the
bases `2ℓ`, `2ℓ + r`, `2ℓ + 2r` and its three signs at `2ℓ + 3r + 2, 3, 4`. That is cheaper
in both directions: every offset is unary, so the program is the one S3 already has, and the
correctness goes straight through `eval_tableauPlusF` instead of through the renaming. -/

/-- A slice of the five-block input at a shifted base is the 3SAT describer's own slice. -/
theorem ibOf_shift {ℓ m b : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ m)) (Fin (2 ^ m)) (Fin (2 ^ m)))
    (h : b + m ≤ 3 * m) :
    ibOf (2 * ℓ + b) m (fun i => (clauseInput5 ℓ m c).getD i false) =
      ibOf b m (fun i => (clauseInput m (lastThree c)).getD i false) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < m := by simpa using h1
  have hr := getD_rho c (k := b + i) (by omega)
  rw [rho, if_pos (by omega)] at hr
  simp only [ibOf, List.getElem_map, List.getElem_range']
  rw [show 2 * ℓ + b + 1 * i = b + i + 2 * ℓ from by omega, hr]
  congr 1
  omega

/-- The candidate of the decoupled describer: the three field records at the shifted bases and
the three auxiliary signs. -/
noncomputable def candOf5 (ℓ e T : ℕ) : CandF :=
  ⟨litFields e Gc T (2 * ℓ), inp (2 * ℓ + 3 * mOf e Gc + 2),
    litFields e Gc T (2 * ℓ + mOf e Gc), inp (2 * ℓ + 3 * mOf e Gc + 3),
    litFields e Gc T (2 * ℓ + 2 * mOf e Gc), inp (2 * ℓ + 3 * mOf e Gc + 4)⟩

theorem candOf5_lengths (ℓ e T : ℕ) : (candOf5 ℓ e T).Lengths e Gc :=
  ⟨litFields_lengths e Gc T _, litFields_lengths e Gc T _, litFields_lengths e Gc T _⟩

theorem candOf5_inputsLt (ℓ e T : ℕ) :
    (candOf5 ℓ e T).InputsLt (2 * ℓ + 3 * mOf e Gc + 5) where
  A₁ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₁ := by show 2 * ℓ + 3 * mOf e Gc + 2 < 2 * ℓ + 3 * mOf e Gc + 5; omega
  A₂ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₂ := by show 2 * ℓ + 3 * mOf e Gc + 3 < 2 * ℓ + 3 * mOf e Gc + 5; omega
  A₃ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₃ := by show 2 * ℓ + 3 * mOf e Gc + 4 < 2 * ℓ + 3 * mOf e Gc + 5; omega

/-- **The shifted candidate reads the 3SAT describer's clause.** -/
theorem evalCand_candOf5 (ℓ e T : ℕ)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ mOf e Gc)) (Fin (2 ^ mOf e Gc))
      (Fin (2 ^ mOf e Gc))) (hT : T ≤ Sof e) :
    evalCand (candOf5 ℓ e T) (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
      candOfClause e T (lastThree c) := by
  have hlf : ∀ b, b + mOf e Gc ≤ 3 * mOf e Gc →
      evalFields (litFields e Gc T (2 * ℓ + b))
          (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
        fieldsOf e Gc T (bitsOfNat (mOf e Gc) (lastThree c).l₁.var) ∨ True := fun _ _ => Or.inr trivial
  clear hlf
  have key : ∀ b, b + mOf e Gc ≤ 3 * mOf e Gc →
      evalFields (litFields e Gc T (2 * ℓ + b))
          (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
        fieldsOf e Gc T (ibOf b (mOf e Gc)
          (fun i => (clauseInput (mOf e Gc) (lastThree c)).getD i false)) := by
    intro b hb
    rw [evalFields_litFields e Gc T (2 * ℓ + b) _ hT, ibOf_shift c hb]
  have hs : ∀ t : ℕ, t < 3 →
      (Fml.inp (2 * ℓ + 3 * mOf e Gc + (t + 2))).eval
          (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
        (sgList c).getD (t + 2) false := by
    intro t _
    have := eval_sgF c (t + 2)
    rwa [show sgOff ℓ (mOf e Gc) + (t + 2) = 2 * ℓ + 3 * mOf e Gc + (t + 2) from by
      unfold sgOff; omega] at this
  have h0 := key 0 (by omega)
  have h1 := key (mOf e Gc) (by omega)
  have h2 := key (2 * mOf e Gc) (by omega)
  have g0 := hs 0 (by omega)
  have g1 := hs 1 (by omega)
  have g2 := hs 2 (by omega)
  simp only [evalCand, candOf5, candOfClause, lastThree]
  rw [show 2 * ℓ + 0 = 2 * ℓ from by omega] at h0
  rw [show 2 * ℓ + 3 * mOf e Gc + 2 = 2 * ℓ + 3 * mOf e Gc + (0 + 2) from by omega]
  rw [show 2 * ℓ + 3 * mOf e Gc + 3 = 2 * ℓ + 3 * mOf e Gc + (1 + 2) from by omega]
  rw [show 2 * ℓ + 3 * mOf e Gc + 4 = 2 * ℓ + 3 * mOf e Gc + (2 + 2) from by omega]
  rw [h0, h1, h2, g0, g1, g2, ibOf_clauseInput_zero, ibOf_clauseInput_one,
    ibOf_clauseInput_two]
  rfl

/-! ## The describer -/

/-- The tableau half of the describer's formula, on the shifted candidate. -/
noncomputable def descBody5 (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  tableauPlusF e Gc T (tabsOf e T D n x y (litFields e Gc T (2 * ℓ))) [5, 6]
    (tplsOf Gc chk) (candOf5 ℓ e T)

/-- The formula of the decoupled describer. -/
noncomputable def descFml5 (ℓ T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  or (descBody5 ℓ T e D n x y) (linkFml ℓ (mOf e Gc) T)

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
    (InputsLt.tableauPlusF e Gc T _
      (tabsOf_inputsLt e T D n x y (candOf5_inputsLt ℓ e T).A₁) _ _ (candOf5_inputsLt ℓ e T))
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
    (hℓr : ℓ ≤ mOf e Gc) (hr : 1 ≤ mOf e Gc) (hT2 : 2 * T < 2 ^ mOf e Gc)
    (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y) (hTm : T + 3 < 2 ^ W e)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ mOf e Gc)) (Fin (2 ^ mOf e Gc))
      (Fin (2 ^ mOf e Gc))) :
    c ∈ (descCirc5 ℓ T e D n x y).formula5 ℓ (mOf e Gc) ↔
      lastThree c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ∨
        Link ℓ (mOf e Gc) T c := by
  have hbody := eval_tableauPlusF e T (candOf5_lengths ℓ e T)
    (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false)
    (tapeSpec e T D n x y Gc (litFields_lengths e Gc T (2 * ℓ)) hT hlen) (freeSpec D n T x y)
    hTm
  rw [evalCand_candOf5 ℓ e T c hT] at hbody
  have h3 := mem_formula3_iff e T (lastThree c) D n x y hT hlen hTm
  show (descCirc5 ℓ T e D n x y).evalBits (clauseInput5 ℓ (mOf e Gc) c) = true ↔ _
  rw [descCirc5, Fml.evalBits_toCircuit, descFml5, eval_or_iff,
    eval_linkFml hℓr hr hT2 c, h3]
  exact or_congr hbody Iff.rfl

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
    (hℓr : ℓ ≤ mOf e Gc) (hr : 1 ≤ mOf e Gc) (hT2 : 2 * T < 2 ^ mOf e Gc)
    (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y) (hTm : T + 3 < 2 ^ W e)
    (a b : Fin (2 ^ ℓ) → Bool) (w₁ w₂ w₃ : Fin (2 ^ mOf e Gc) → Bool) :
    ((descCirc5 ℓ T e D n x y).formula5 ℓ (mOf e Gc)).Sat a b w₁ w₂ w₃ ↔
      Tri ((descCirc e T D n x y).formula3 (mOf e Gc)) w₁ w₂ w₃ ∧
        LinkSat ℓ (mOf e Gc) T a b w₁ w₂ w₃ := by
  constructor
  · intro hsat
    have key : ∀ c, (lastThree c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ∨
        Link ℓ (mOf e Gc) T c) → Clause5.eval a b w₁ w₂ w₃ c = true := fun c hc =>
      hsat c ((mem_formula5_iff ℓ T e D n x y hℓr hr hT2 hT hlen hTm c).mpr hc)
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
    rcases (mem_formula5_iff ℓ T e D n x y hℓr hr hT2 hT hlen hTm c).mp hc with h3 | hlk
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

/-! ## The padding of an answer block -/

/-- Past twice the length of the string, a tape block is the blank cell `10`: `true` at even
positions and `false` at odd ones. This is the parity the audit campaign repaired, and it is
what rows 4 to 7 assert. -/
theorem tapeBits_of_ge {s : BitStr} {T p : ℕ} (hs : s.length ≤ T) (hp : 2 * T ≤ p) :
    tapeBits s p = decide (p % 2 = 0) := by
  have hnone : s[p / 2]? = none := List.getElem?_eq_none (by omega)
  rw [tapeBits, hnone]
  rcases Nat.eq_zero_or_pos (p % 2) with h | h
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg (by omega), decide_eq_false (by omega)]
    rfl

/-! ## The describer describes the decider -/

/-- **The decoupled describer describes the decider** (`lem:decoupled-5sat`, the description
clause). -/
theorem describes5 (𝒟 : Decider) (ℓ T e : ℕ) (n : ℕ) (x y : BitStr)
    (hℓ : 2 * T ≤ 2 ^ ℓ) (hℓr : ℓ ≤ mOf e Gc) (hr : 1 ≤ mOf e Gc)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (hTle : T ≤ Sof e)
    (hlen : FixedLen e 𝒟.prog n T x y) (hTm : T + 3 < 2 ^ W e)
    (hrb : ∀ ap bp : BitStr, ap.length ≤ T → bp.length ≤ T →
      runBound 𝒟.prog n x y ap bp T ≤ Sof e) :
    (descCirc5 ℓ T e 𝒟.prog n x y).DescribesDecider ℓ (mOf e Gc) 𝒟 n x y T := by
  have hT : 2 * T < 2 ^ mOf e Gc := by
    rcases Nat.eq_zero_or_pos T with rfl | hTpos
    · simp
    · omega
  have hiff := extendsAnswers_iff 𝒟 n T x y e hTle hlen hTm hrb h4T
  intro a b
  constructor
  · rintro ⟨w₁, w₂, w₃, hsat⟩
    obtain ⟨htri, hlink⟩ :=
      (sat_formula5_iff ℓ T e 𝒟.prog n x y hℓr hr hT hTle hlen hTm a b w₁ w₂ w₃).mp hsat
    have h12 : ∀ i, w₁ i = w₂ i := fun i => hlink.w12 i i rfl
    have h23 : ∀ i, w₂ i = w₃ i := fun i => hlink.w23 i i rfl
    have e12 : w₁ = w₂ := funext h12
    have e23 : w₂ = w₃ := funext h23
    have hsat3 : ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)).Sat w₁ := by
      intro c₃ hc₃
      have h := htri c₃ hc₃
      rw [← e23, ← e12] at h
      exact h
    have hext : ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc))
        (fun j : Fin (2 * T) => a ⟨j, by omega⟩) (fun j : Fin (2 * T) => b ⟨j, by omega⟩) := by
      refine ⟨w₁, fun j => ?_, fun j => ?_, hsat3⟩
      · exact (hlink.aLow ⟨j, by omega⟩ ⟨j, by omega⟩ j.isLt rfl).symm
      · exact (hlink.bLow ⟨j, by omega⟩ ⟨2 * T + j, by omega⟩ j.isLt (by simp; omega)).symm
    obtain ⟨ap, bp, hap, hbp, ha, hb, hacc⟩ := hiff _ _ |>.mp hext
    refine ⟨ap, bp, hap, hbp, fun j => ?_, fun j => ?_, hacc⟩
    · rcases lt_or_ge (j : ℕ) (2 * T) with hj | hj
      · exact ha ⟨j, hj⟩
      · rw [hlink.aPad j (by omega), tapeBits_of_ge hap hj]
    · rcases lt_or_ge (j : ℕ) (2 * T) with hj | hj
      · exact hb ⟨j, hj⟩
      · rw [hlink.bPad j (by omega), tapeBits_of_ge hbp hj]
  · rintro ⟨ap, bp, hap, hbp, ha, hb, hacc⟩
    obtain ⟨w, hw1, hw2, hsat3⟩ := hiff (fun j : Fin (2 * T) => a ⟨j, by omega⟩)
      (fun j : Fin (2 * T) => b ⟨j, by omega⟩) |>.mpr
      ⟨ap, bp, hap, hbp, fun j => by simpa using ha ⟨j, by omega⟩,
        fun j => by simpa using hb ⟨j, by omega⟩, hacc⟩
    refine ⟨w, w, w, ?_⟩
    rw [sat_formula5_iff ℓ T e 𝒟.prog n x y hℓr hr hT hTle hlen hTm a b w w w]
    refine ⟨fun c₃ hc₃ => hsat3 c₃ hc₃, ⟨?_, ?_, ?_, ?_, fun i j hij => ?_, fun i j hij => ?_⟩⟩
    · intro i j hi hij
      have h := hw1 ⟨(i : ℕ), hi⟩
      calc a i = a ⟨(i : ℕ), by omega⟩ := rfl
        _ = w ⟨(i : ℕ), by omega⟩ := h.symm
        _ = w j := congrArg w (Fin.ext hij)
    · intro i j hi hij
      have h := hw2 ⟨(i : ℕ), hi⟩
      calc b i = b ⟨(i : ℕ), by omega⟩ := rfl
        _ = w ⟨2 * T + (i : ℕ), by omega⟩ := h.symm
        _ = w j := congrArg w (Fin.ext (by simp; omega))
    · intro i hi
      rw [ha i, tapeBits_of_ge hap (by omega)]
    · intro i hi
      rw [hb i, tapeBits_of_ge hbp (by omega)]
    · exact congrArg w (Fin.ext hij)
    · exact congrArg w (Fin.ext hij)

end MIPRE.TM.CookLevin.Desc
