/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TM.CookLevin.Decoupled
public import MIPRE.TM.CookLevin.Link6

@[expose] public section

/-!
# The windowed describer, and the clauses it describes

The describer of `MIPRE.SAT.WindowDescriber` (slice P4g of the Aldous–Lyons track): the 3SAT
describer of `thm:succinct-sat` rebuilt on the six-block layout — its three field records read
at the bases `P`, `P + r`, `P + 2r` with `P = ℓa + ℓb + ℓc`, its three signs after the three
window signs — in disjunction with the link formula of `Link6.lean`, all flattened once to a
circuit, exactly as `descCirc5` is built for two answer blocks (`Decoupled.lean`).
`mem_formula6_iff` is the bridge, `sat_formula6_iff` reads what a satisfying 6-tuple is, and
`describes6` is the description: three tables complete to a satisfying 6-tuple exactly when
they are the windows of the tape encodings of strings the decider accepts within `T`.
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## The 3SAT describer's clause inside a six-block clause -/

/-- The 3-clause of the last three literals of a six-block clause. -/
def lastThree6 {ℓa ℓb ℓc r : ℕ} (c : Clause6W ℓa ℓb ℓc r) : Clause3 (Fin (2 ^ r)) :=
  ⟨c.l₄, c.l₅, c.l₆⟩

theorem drop6_three' {ℓa ℓb ℓc r : ℕ} (c : Clause6W ℓa ℓb ℓc r) :
    (clauseInput6 ℓa ℓb ℓc r c).drop (wOff ℓa ℓb ℓc) =
      (bitsOfNat r c.l₄.var ++ bitsOfNat r c.l₅.var ++ bitsOfNat r c.l₆.var) ++ sgList6 c := by
  rw [drop6_three, List.append_assoc, List.append_assoc]

/-- **The six-block input at the witness offset reads the 3SAT describer's indices.** -/
theorem getD_shift6 {ℓa ℓb ℓc r : ℕ} (c : Clause6W ℓa ℓb ℓc r) {k : ℕ} (hk : k < 3 * r) :
    (clauseInput6 ℓa ℓb ℓc r c).getD (wOff ℓa ℓb ℓc + k) false =
      (clauseInput r (lastThree6 c)).getD k false := by
  set pre : BitStr :=
    bitsOfNat r c.l₄.var ++ bitsOfNat r c.l₅.var ++ bitsOfNat r c.l₆.var with hpre
  have hlen : pre.length = 3 * r := by rw [hpre]; simp [length_bitsOfNat]; omega
  have h3 : clauseInput r (lastThree6 c) = pre ++ [c.l₄.pos, c.l₅.pos, c.l₆.pos] := by
    rw [clauseInput, hpre, lastThree6]
  rw [← getD_drop_eq, drop6_three', List.getD_append pre (sgList6 c) false _ (by rw [hlen]; exact hk),
    h3, List.getD_append pre _ false _ (by rw [hlen]; exact hk)]

/-- A slice of the six-block input at a shifted base is the 3SAT describer's own slice. -/
theorem ibOf_shift6 {ℓa ℓb ℓc m b : ℕ} (c : Clause6W ℓa ℓb ℓc m) (h : b + m ≤ 3 * m) :
    ibOf (wOff ℓa ℓb ℓc + b) m (fun i => (clauseInput6 ℓa ℓb ℓc m c).getD i false) =
      ibOf b m (fun i => (clauseInput m (lastThree6 c)).getD i false) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < m := by simpa using h1
  have hr := getD_shift6 c (k := b + i) (by omega)
  simp only [ibOf, List.getElem_map, List.getElem_range']
  rw [show wOff ℓa ℓb ℓc + b + 1 * i = wOff ℓa ℓb ℓc + (b + i) from by omega, hr]
  congr 1
  omega

/-! ## The shifted candidate -/

/-- The candidate of the windowed describer: the three field records at the shifted bases and
the three witness signs. -/
noncomputable def candOf6 (P e T : ℕ) : CandF :=
  ⟨litFields e Gc T P, inp (P + 3 * mOf e Gc + 3),
    litFields e Gc T (P + mOf e Gc), inp (P + 3 * mOf e Gc + 4),
    litFields e Gc T (P + 2 * mOf e Gc), inp (P + 3 * mOf e Gc + 5)⟩

theorem candOf6_lengths (P e T : ℕ) : (candOf6 P e T).Lengths e Gc :=
  ⟨litFields_lengths e Gc T _, litFields_lengths e Gc T _, litFields_lengths e Gc T _⟩

theorem candOf6_inputsLt (P e T : ℕ) : (candOf6 P e T).InputsLt (P + 3 * mOf e Gc + 6) where
  A₁ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₁ := by show P + 3 * mOf e Gc + 3 < P + 3 * mOf e Gc + 6; omega
  A₂ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₂ := by show P + 3 * mOf e Gc + 4 < P + 3 * mOf e Gc + 6; omega
  A₃ := litFields_inputsLt e Gc T _ _ (by omega)
  σ₃ := by show P + 3 * mOf e Gc + 5 < P + 3 * mOf e Gc + 6; omega

/-- **The shifted candidate reads the 3SAT describer's clause.** -/
theorem evalCand_candOf6 (ℓa ℓb ℓc e T : ℕ) (c : Clause6W ℓa ℓb ℓc (mOf e Gc))
    (hT : T ≤ Sof e) :
    evalCand (candOf6 (wOff ℓa ℓb ℓc) e T)
        (fun i => (clauseInput6 ℓa ℓb ℓc (mOf e Gc) c).getD i false) =
      candOfClause e T (lastThree6 c) := by
  have key : ∀ b, b + mOf e Gc ≤ 3 * mOf e Gc →
      evalFields (litFields e Gc T (wOff ℓa ℓb ℓc + b))
          (fun i => (clauseInput6 ℓa ℓb ℓc (mOf e Gc) c).getD i false) =
        fieldsOf e Gc T (ibOf b (mOf e Gc)
          (fun i => (clauseInput (mOf e Gc) (lastThree6 c)).getD i false)) := by
    intro b hb
    rw [evalFields_litFields e Gc T (wOff ℓa ℓb ℓc + b) _ hT, ibOf_shift6 c hb]
  have hs : ∀ t : ℕ, t < 3 →
      (Fml.inp (wOff ℓa ℓb ℓc + 3 * mOf e Gc + (t + 3))).eval
          (fun i => (clauseInput6 ℓa ℓb ℓc (mOf e Gc) c).getD i false) =
        (sgList6 c).getD (t + 3) false := by
    intro t _
    have := eval_t₀F c (t + 3)
    unfold t₀F at this
    rwa [show sgOff6 ℓa ℓb ℓc (mOf e Gc) + (t + 3) = wOff ℓa ℓb ℓc + 3 * mOf e Gc + (t + 3) from by
      unfold sgOff6; omega] at this
  have h0 := key 0 (by omega)
  have h1 := key (mOf e Gc) (by omega)
  have h2 := key (2 * mOf e Gc) (by omega)
  have g0 := hs 0 (by omega)
  have g1 := hs 1 (by omega)
  have g2 := hs 2 (by omega)
  simp only [evalCand, candOf6, candOfClause, lastThree6]
  rw [show wOff ℓa ℓb ℓc + 0 = wOff ℓa ℓb ℓc from by omega] at h0
  rw [show wOff ℓa ℓb ℓc + 3 * mOf e Gc + 3 = wOff ℓa ℓb ℓc + 3 * mOf e Gc + (0 + 3) from by omega]
  rw [show wOff ℓa ℓb ℓc + 3 * mOf e Gc + 4 = wOff ℓa ℓb ℓc + 3 * mOf e Gc + (1 + 3) from by omega]
  rw [show wOff ℓa ℓb ℓc + 3 * mOf e Gc + 5 = wOff ℓa ℓb ℓc + 3 * mOf e Gc + (2 + 3) from by omega]
  rw [h0, h1, h2, g0, g1, g2, ibOf_clauseInput_zero, ibOf_clauseInput_one,
    ibOf_clauseInput_two]
  rfl

/-! ## The describer -/

/-- The tableau half of the windowed describer's formula, on the shifted candidate. -/
noncomputable def descBody6 (P T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  tableauPlusF e Gc T (tabsOf e T D n x y (litFields e Gc T P)) [5, 6]
    (tplsOf Gc chk) (candOf6 P e T)

/-- The formula of the windowed describer. -/
noncomputable def descFml6 (ℓa ℓb ℓc T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Fml :=
  or (descBody6 (wOff ℓa ℓb ℓc) T e D n x y) (link6Fml ℓa ℓb ℓc (mOf e Gc) T)

/-- **The windowed describer circuit**: the flattening of `descFml6` on
`ℓa + ℓb + ℓc + 3r + 6` inputs. -/
noncomputable def descCirc6 (ℓa ℓb ℓc T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) : Circuit :=
  (descFml6 ℓa ℓb ℓc T e D n x y).toCircuit (ℓa + ℓb + ℓc + 3 * mOf e Gc + 6)

theorem descCirc6_inputs (ℓa ℓb ℓc T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descCirc6 ℓa ℓb ℓc T e D n x y).inputs = ℓa + ℓb + ℓc + 3 * mOf e Gc + 6 := rfl

theorem descFml6_inputsLt (ℓa ℓb ℓc T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descFml6 ℓa ℓb ℓc T e D n x y).InputsLt (ℓa + ℓb + ℓc + 3 * mOf e Gc + 6) :=
  InputsLt.or'
    (InputsLt.tableauPlusF e Gc T _
      (tabsOf_inputsLt e T D n x y (candOf6_inputsLt (wOff ℓa ℓb ℓc) e T).A₁) _ _
      (candOf6_inputsLt (wOff ℓa ℓb ℓc) e T))
    (InputsLt.link6Fml ℓa ℓb ℓc (mOf e Gc) T)

theorem descCirc6_wellFormed (ℓa ℓb ℓc T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) :
    (descCirc6 ℓa ℓb ℓc T e D n x y).WellFormed :=
  Fml.toCircuit_wellFormed _ (descFml6_inputsLt ℓa ℓb ℓc T e D n x y)

/-- **What the windowed describer accepts**: a clause is accepted exactly when the 3-clause of
its last three literals is accepted by the 3SAT describer, or the clause satisfies one of the
five link conditions. -/
theorem mem_formula6_iff (ℓa ℓb ℓc T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
    (ha : ℓa ≤ mOf e Gc) (hb : ℓb ≤ mOf e Gc) (hc : ℓc ≤ mOf e Gc)
    (hT2 : 2 * T < 2 ^ mOf e Gc) (hTa : 2 ^ ℓa < 2 ^ mOf e Gc) (hT : T ≤ Sof e)
    (hlen : FixedLen e D n T x y) (hTm : T + 3 < 2 ^ W e) (c : Clause6W ℓa ℓb ℓc (mOf e Gc)) :
    c ∈ (descCirc6 ℓa ℓb ℓc T e D n x y).formula6 ℓa ℓb ℓc (mOf e Gc) ↔
      lastThree6 c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ∨
        Link6 ℓa ℓb ℓc (mOf e Gc) T c := by
  have hbody := eval_tableauPlusF e T (candOf6_lengths (wOff ℓa ℓb ℓc) e T)
    (fun i => (clauseInput6 ℓa ℓb ℓc (mOf e Gc) c).getD i false)
    (tapeSpec e T D n x y Gc (litFields_lengths e Gc T (wOff ℓa ℓb ℓc)) hT hlen)
    (freeSpec D n T x y) hTm
  rw [evalCand_candOf6 ℓa ℓb ℓc e T c hT] at hbody
  have h3 := mem_formula3_iff e T (lastThree6 c) D n x y hT hlen hTm
  show (descCirc6 ℓa ℓb ℓc T e D n x y).evalBits (clauseInput6 ℓa ℓb ℓc (mOf e Gc) c) = true ↔ _
  rw [descCirc6, Fml.evalBits_toCircuit, descFml6, eval_or_iff,
    eval_link6Fml ha hb hc hT2 hTa c, h3]
  exact or_congr hbody Iff.rfl

/-! ## What a satisfying 6-tuple is -/

/-- The link half: what the five rows force. -/
structure LinkSat6 (ℓa ℓb ℓc r T : ℕ) (A : Fin (2 ^ ℓa) → Bool) (B : Fin (2 ^ ℓb) → Bool)
    (C : Fin (2 ^ ℓc) → Bool) (w₁ w₂ w₃ : Fin (2 ^ r) → Bool) : Prop where
  aWin : ∀ (i : Fin (2 ^ ℓa)) (j : Fin (2 ^ r)), (j : ℕ) = (i : ℕ) → A i = w₁ j
  bWin : ∀ (i : Fin (2 ^ ℓb)) (j : Fin (2 ^ r)), (j : ℕ) = (i : ℕ) + 2 * T → B i = w₁ j
  cWin : ∀ (i : Fin (2 ^ ℓc)) (j : Fin (2 ^ r)), (j : ℕ) = (i : ℕ) + 2 ^ ℓa → C i = w₁ j
  w12 : ∀ i j : Fin (2 ^ r), (i : ℕ) = (j : ℕ) → w₁ i = w₂ j
  w23 : ∀ i j : Fin (2 ^ r), (i : ℕ) = (j : ℕ) → w₂ i = w₃ j

/-- **The two halves of satisfaction.** -/
theorem sat_formula6_iff (ℓa ℓb ℓc T e : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
    (ha : ℓa ≤ mOf e Gc) (hb : ℓb ≤ mOf e Gc) (hc : ℓc ≤ mOf e Gc)
    (hT2 : 2 * T < 2 ^ mOf e Gc) (hTa : 2 ^ ℓa < 2 ^ mOf e Gc) (hT : T ≤ Sof e)
    (hlen : FixedLen e D n T x y) (hTm : T + 3 < 2 ^ W e) (A : Fin (2 ^ ℓa) → Bool) (B : Fin (2 ^ ℓb) → Bool)
    (C : Fin (2 ^ ℓc) → Bool) (w₁ w₂ w₃ : Fin (2 ^ mOf e Gc) → Bool) :
    ((descCirc6 ℓa ℓb ℓc T e D n x y).formula6 ℓa ℓb ℓc (mOf e Gc)).Sat A B C w₁ w₂ w₃ ↔
      Tri ((descCirc e T D n x y).formula3 (mOf e Gc)) w₁ w₂ w₃ ∧
        LinkSat6 ℓa ℓb ℓc (mOf e Gc) T A B C w₁ w₂ w₃ := by
  have hmem := mem_formula6_iff ℓa ℓb ℓc T e D n x y ha hb hc hT2 hTa hT hlen hTm
  constructor
  · intro hsat
    have key : ∀ c, (lastThree6 c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ∨
        Link6 ℓa ℓb ℓc (mOf e Gc) T c) → Clause6.eval A B C w₁ w₂ w₃ c = true := fun c hc =>
      hsat c ((hmem c).mpr hc)
    refine ⟨?_, ?_⟩
    · intro c₃ hc₃
      have h := key ⟨offLit A, offLit B, offLit C, c₃.l₁, c₃.l₂, c₃.l₃⟩ (Or.inl hc₃)
      simpa [Clause6.eval] using h
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        refine eq_of_lit_or A w₁ i j fun o => ?_
        have h := key ⟨⟨i, o⟩, offLit B, offLit C, ⟨j, !o⟩, offLit w₂, offLit w₃⟩
          (Or.inr (Or.inl ⟨hij, by simp⟩))
        simpa [Clause6.eval] using h
      · intro i j hij
        refine eq_of_lit_or B w₁ i j fun o => ?_
        have h := key ⟨offLit A, ⟨i, o⟩, offLit C, ⟨j, !o⟩, offLit w₂, offLit w₃⟩
          (Or.inr (Or.inr (Or.inl ⟨hij, by simp⟩)))
        simpa [Clause6.eval] using h
      · intro i j hij
        refine eq_of_lit_or C w₁ i j fun o => ?_
        have h := key ⟨offLit A, offLit B, ⟨i, o⟩, ⟨j, !o⟩, offLit w₂, offLit w₃⟩
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨hij, by simp⟩))))
        simpa [Clause6.eval] using h
      · intro i j hij
        refine eq_of_lit_or w₁ w₂ i j fun o => ?_
        have h := key ⟨offLit A, offLit B, offLit C, ⟨i, o⟩, ⟨j, !o⟩, offLit w₃⟩
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hij, by simp⟩)))))
        simpa [Clause6.eval] using h
      · intro i j hij
        refine eq_of_lit_or w₂ w₃ i j fun o => ?_
        have h := key ⟨offLit A, offLit B, offLit C, offLit w₁, ⟨i, o⟩, ⟨j, !o⟩⟩
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hij, by simp⟩)))))
        simpa [Clause6.eval] using h
  · rintro ⟨htri, hlink⟩ c hc
    rcases (hmem c).mp hc with h3 | hlk
    · have h := htri (lastThree6 c) h3
      simp only [lastThree6, Bool.or_eq_true] at h
      simp only [Clause6.eval, Bool.or_eq_true]
      rcases h with (hd | he) | hf
      · exact Or.inl (Or.inl (Or.inr hd))
      · exact Or.inl (Or.inr he)
      · exact Or.inr hf
    · rcases hlk with ⟨hij, ho⟩ | ⟨hij, ho⟩ | ⟨hij, ho⟩ | ⟨hij, ho⟩ | ⟨hij, ho⟩
      · have h := hlink.aWin c.l₁.var c.l₄.var hij
        cases hp1 : c.l₁.pos <;> cases hp4 : c.l₄.pos <;> cases hv : w₁ c.l₄.var <;>
          simp_all [Clause6.eval, Lit.eval]
      · have h := hlink.bWin c.l₂.var c.l₄.var hij
        cases hp2 : c.l₂.pos <;> cases hp4 : c.l₄.pos <;> cases hv : w₁ c.l₄.var <;>
          simp_all [Clause6.eval, Lit.eval]
      · have h := hlink.cWin c.l₃.var c.l₄.var hij
        cases hp3 : c.l₃.pos <;> cases hp4 : c.l₄.pos <;> cases hv : w₁ c.l₄.var <;>
          simp_all [Clause6.eval, Lit.eval]
      · have h := hlink.w12 c.l₄.var c.l₅.var hij
        cases hp4 : c.l₄.pos <;> cases hp5 : c.l₅.pos <;> cases hv : w₂ c.l₅.var <;>
          simp_all [Clause6.eval, Lit.eval]
      · have h := hlink.w23 c.l₅.var c.l₆.var hij
        cases hp5 : c.l₅.pos <;> cases hp6 : c.l₆.pos <;> cases hv : w₃ c.l₆.var <;>
          simp_all [Clause6.eval, Lit.eval]

/-! ## The describer describes the decider through the windows -/

/-- **The windowed describer describes the decider** (slice P4g, the description clause). -/
theorem describes6 (𝒟 : Decider) (ℓa ℓb ℓc T e : ℕ) (n : ℕ) (x y : BitStr)
    (hwac : 2 ^ ℓa + 2 ^ ℓc ≤ 2 * T) (hwb : 2 ^ ℓb ≤ 2 * T)
    (ha : ℓa ≤ mOf e Gc) (hb : ℓb ≤ mOf e Gc) (hc : ℓc ≤ mOf e Gc)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (hTle : T ≤ Sof e)
    (hlen : FixedLen e 𝒟.prog n T x y) (hTm : T + 3 < 2 ^ W e)
    (hrb : ∀ ap bp : BitStr, ap.length ≤ T → bp.length ≤ T →
      runBound 𝒟.prog n x y ap bp T ≤ Sof e) :
    (descCirc6 ℓa ℓb ℓc T e 𝒟.prog n x y).DescribesWindows ℓa ℓb ℓc (mOf e Gc) 𝒟 n x y T := by
  have hcpos : 1 ≤ 2 ^ ℓc := Nat.one_le_two_pow
  have hmpos : 1 ≤ 2 ^ mOf e Gc := Nat.one_le_two_pow
  have hT2 : 2 * T < 2 ^ mOf e Gc := by omega
  have hTa : 2 ^ ℓa < 2 ^ mOf e Gc := by omega
  have hiff := extendsAnswers_iff 𝒟 n T x y e hTle hlen hTm hrb h4T
  intro A B C
  constructor
  · rintro ⟨w₁, w₂, w₃, hsat⟩
    obtain ⟨htri, hlink⟩ :=
      (sat_formula6_iff ℓa ℓb ℓc T e 𝒟.prog n x y ha hb hc hT2 hTa hTle hlen hTm A B C w₁ w₂
        w₃).mp hsat
    have e12 : w₁ = w₂ := funext fun i => hlink.w12 i i rfl
    have e23 : w₂ = w₃ := funext fun i => hlink.w23 i i rfl
    have hsat3 : ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)).Sat w₁ := by
      intro c₃ hc₃
      have h := htri c₃ hc₃
      rw [← e23, ← e12] at h
      exact h
    have hext : ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc))
        (fun j : Fin (2 * T) => w₁ ⟨j, by omega⟩)
        (fun j : Fin (2 * T) => w₁ ⟨2 * T + j, by omega⟩) :=
      ⟨w₁, fun _ => rfl, fun _ => rfl, hsat3⟩
    obtain ⟨ap, bp, hap, hbp, ha', hb', hacc⟩ := hiff _ _ |>.mp hext
    refine ⟨ap, bp, hap, hbp, fun j => ?_, fun j => ?_, fun j => ?_, hacc⟩
    · rw [hlink.aWin j ⟨j, by omega⟩ rfl]
      exact ha' ⟨j, by omega⟩
    · rw [hlink.bWin j ⟨(j : ℕ) + 2 * T, by omega⟩ rfl]
      exact (congrArg w₁ (Fin.ext (by simp; omega))).trans (hb' ⟨j, by omega⟩)
    · rw [hlink.cWin j ⟨(j : ℕ) + 2 ^ ℓa, by omega⟩ rfl]
      exact (congrArg w₁ (Fin.ext (by simp; omega))).trans (ha' ⟨2 ^ ℓa + j, by omega⟩)
  · rintro ⟨ap, bp, hap, hbp, ha', hb', hc', hacc⟩
    obtain ⟨w, hw1, hw2, hsat3⟩ := hiff (fun j : Fin (2 * T) => tapeBits ap j)
      (fun j : Fin (2 * T) => tapeBits bp j) |>.mpr
      ⟨ap, bp, hap, hbp, fun _ => rfl, fun _ => rfl, hacc⟩
    refine ⟨w, w, w, ?_⟩
    rw [sat_formula6_iff ℓa ℓb ℓc T e 𝒟.prog n x y ha hb hc hT2 hTa hTle hlen hTm A B C w w w]
    refine ⟨fun c₃ hc₃ => hsat3 c₃ hc₃, ⟨?_, ?_, ?_, fun i j hij => ?_, fun i j hij => ?_⟩⟩
    · intro i j hij
      have h := hw1 ⟨(i : ℕ), by omega⟩
      rw [ha' i]
      calc tapeBits ap i = w ⟨(i : ℕ), by omega⟩ := h.symm
        _ = w j := congrArg w (Fin.ext hij.symm)
    · intro i j hij
      have h := hw2 ⟨(i : ℕ), by omega⟩
      rw [hb' i]
      calc tapeBits bp i = w ⟨2 * T + (i : ℕ), by omega⟩ := h.symm
        _ = w j := congrArg w (Fin.ext (by simp; omega))
    · intro i j hij
      have h := hw1 ⟨2 ^ ℓa + (i : ℕ), by omega⟩
      rw [hc' i]
      calc tapeBits ap (2 ^ ℓa + i) = w ⟨2 ^ ℓa + (i : ℕ), by omega⟩ := h.symm
        _ = w j := congrArg w (Fin.ext (by simp; omega))
    · exact congrArg w (Fin.ext hij)
    · exact congrArg w (Fin.ext hij)

end MIPRE.TM.CookLevin.Desc

end
