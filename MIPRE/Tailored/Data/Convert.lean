/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Data.Bridge
public import MIPRE.Foundations.Cost.Codable
public import MIPRE.Tactics

@[expose] public section

/-!
# A tailored game description as a game description

`TailoredGameData.toGameData` turns a tailored game description into a `HaltingGameValue.GameData`
with the same game: the questions are the same vertices, the answers the bit vectors of length
`Λ` named by the numbers below `2 ^ Λ` (bit `i` of the number is coordinate `i`, `vecEquiv`), the
weights the same list, and the acceptance table every tuple the canonical decider accepts
(`acceptsN`, the decider on numbers). So the machinery written for game descriptions applies to
tailored ones: the quantum value is the same (`quantumValue_toGameData`), and it is r.e. from
below along a computable family (`ValueApprox.rePred_lt_quantumValue`), because the conversion is
primitive recursive (`primrec_toGameData`).
-/

namespace TailoredGameValue.TailoredGameData

open HaltingGameValue MIPRE.Cost

/-! ## Answers as numbers -/

/-- The bit vectors of length `L` as the numbers below `2 ^ L`: coordinate `i` is bit `i`. -/
def vecEquiv (L : ℕ) : Fin (2 ^ L) ≃ (Fin L → Bool) :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finTwoEquiv)

theorem vecEquiv_apply (L : ℕ) (a : Fin (2 ^ L)) (i : Fin L) :
    vecEquiv L a i = (a : ℕ).testBit i := by
  have h : ((finFunctionFinEquiv.symm a i : Fin 2) : ℕ) = (a : ℕ) / 2 ^ (i : ℕ) % 2 :=
    finFunctionFinEquiv_symm_apply_val a i
  show finTwoEquiv (finFunctionFinEquiv.symm a i) = _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  generalize hb : finFunctionFinEquiv.symm a i = b at h
  rw [← h]
  fin_cases b <;> rfl

/-! ## The answer length and the canonical decider, on numbers -/

variable (g : TailoredGameData)

/-- The answer length `Λ`, computed by a fold over the vertices. -/
def ansLenL : ℕ := ((List.range (g.nV + 1)).map g.lenAt).foldr max 0

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons b l ih =>
    rw [List.foldr_cons]
    exact max_le (h b List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem lenAt_le_ansLen (x : Fin (g.nV + 1)) : g.lenAt x ≤ g.ansLen :=
  Finset.le_sup (f := fun x : Fin (g.nV + 1) => g.lenAt x.val) (Finset.mem_univ x)

theorem ansLenL_eq : g.ansLenL = g.ansLen := by
  apply le_antisymm
  · refine foldr_max_le fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    exact g.lenAt_le_ansLen ⟨x, List.mem_range.1 hx⟩
  · refine Finset.sup_le fun x _ => le_foldr_max (List.mem_map.2 ⟨x.val, ?_, rfl⟩)
    exact List.mem_range.2 x.isLt

/-- The readable part of an answer given as a number. -/
def rdN (x a : ℕ) : List Bool := (List.range (g.lenRAt x)).map a.testBit

/-- The full answer, given as a number. -/
def flN (x a : ℕ) : List Bool := (List.range (g.lenAt x)).map a.testBit

/-- The parity of a list of bits, by a fold. -/
def parityB (l : List Bool) : Bool := l.foldr (fun b acc => !decide (b = acc)) false

theorem parityB_eq_false_iff (l : List Bool) : parityB l = false ↔ Even (l.count true) := by
  induction l with
  | nil => simp [parityB]
  | cons b l ih =>
    unfold parityB at ih ⊢
    rw [List.foldr_cons, List.count_cons]
    cases b <;> cases h : l.foldr (fun b acc => !decide (b = acc)) false <;>
      simp_all [Nat.even_add_one]

/-- Satisfaction of a linear constraint, as a Boolean function. -/
def satB (c v : List Bool) : Bool :=
  decide (c.length = v.length) &&
    !parityB ((List.range c.length).map fun i => c.getD i false && v.getD i false)

theorem zipWith_eq_range (c v : List Bool) (h : c.length = v.length) :
    List.zipWith (· && ·) c v =
      (List.range c.length).map fun i => c.getD i false && v.getD i false := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    have hc : i < c.length := by simpa using h2
    have hv : i < v.length := h ▸ hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]

theorem satB_iff (c v : List Bool) : satB c v = true ↔ Satisfies c v := by
  unfold satB Satisfies
  rw [Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true']
  constructor
  · rintro ⟨h, hp⟩
    refine ⟨h, ?_⟩
    rw [zipWith_eq_range c v h, ← parityB_eq_false_iff]
    exact hp
  · rintro ⟨h, he⟩
    refine ⟨h, ?_⟩
    rw [parityB_eq_false_iff, ← zipWith_eq_range c v h]
    exact he

/-- **The canonical decider on numbers**: answers given as numbers, read as bit vectors. -/
def acceptsN (x y a b : ℕ) : Bool :=
  (!decide (x = y) || decide (a = b)) && decide (a < 2 ^ g.lenAt x) &&
    decide (b < 2 ^ g.lenAt y) &&
    g.cons.all fun e =>
      !(decide (e.1 = x) && decide (e.2.1 = y) && decide (e.2.2.1 = g.rdN x a ++ g.rdN y b)) ||
        satB e.2.2.2 (g.flN x a ++ g.flN y b ++ [true])

/-- **The acceptance table**: every tuple of numbers in range that the decider accepts. -/
def accN : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (g.nV + 1)).flatMap fun x => (List.range (g.nV + 1)).flatMap fun y =>
    (List.range (2 ^ g.ansLenL)).flatMap fun a =>
      (List.range (2 ^ g.ansLenL)).filterMap fun b =>
        if g.acceptsN x y a b = true then some (x, y, a, b) else none

/-- **A tailored game description as a game description.** -/
def toGameData : GameData := ⟨g.nV, 2 ^ g.ansLenL - 1, g.w, g.accN⟩

theorem mem_accN (x y a b : ℕ) :
    (x, y, a, b) ∈ g.accN ↔ x < g.nV + 1 ∧ y < g.nV + 1 ∧ a < 2 ^ g.ansLenL ∧
      b < 2 ^ g.ansLenL ∧ g.acceptsN x y a b = true := by
  simp only [accN, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨x', hx, y', hy, a', ha, b', hb, hab⟩
    split_ifs at hab with hacc
    cases hab
    exact ⟨hx, hy, ha, hb, hacc⟩
  · rintro ⟨hx, hy, ha, hb, hacc⟩
    exact ⟨x, hx, y, hy, a, ha, b, hb, by rw [ite_eq_left hacc]⟩

/-! ## The canonical decider on numbers is the canonical decider -/

theorem wellFormatted_iff (x : Fin (g.nV + 1)) (a : Fin (2 ^ g.ansLen)) :
    g.WellFormatted x (vecEquiv _ a) ↔ (a : ℕ) < 2 ^ g.lenAt x := by
  unfold WellFormatted
  constructor
  · intro h
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    by_cases hL : i < g.ansLen
    · have := h ⟨i, hL⟩ hi
      rwa [vecEquiv_apply] at this
    · exact Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right two_pos (by omega)))
  · intro h i hi
    rw [vecEquiv_apply]
    exact Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right two_pos hi))

theorem bit_vecEquiv (a : Fin (2 ^ g.ansLen)) {i : ℕ} (hi : i < g.ansLen) :
    bit (vecEquiv _ a) i = (a : ℕ).testBit i := by
  rw [bit, dite_eq_left hi, vecEquiv_apply]

theorem readable_vecEquiv (x : Fin (g.nV + 1)) (a : Fin (2 ^ g.ansLen)) :
    g.readable x (vecEquiv _ a) = g.rdN x a := by
  refine List.map_congr_left fun i hi => g.bit_vecEquiv a ?_
  have := List.mem_range.1 hi
  have hx := g.lenAt_le_ansLen x
  unfold lenAt at hx
  omega

theorem full_vecEquiv (x : Fin (g.nV + 1)) (a : Fin (2 ^ g.ansLen)) :
    g.full x (vecEquiv _ a) = g.flN x a := by
  refine List.map_congr_left fun i hi => g.bit_vecEquiv a ?_
  exact (List.mem_range.1 hi).trans_le (g.lenAt_le_ansLen x)

theorem elem_iff (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] (s : Bool) :
    ((!(decide A && decide B && decide C) || s) = true) ↔ (A → B → C → s = true) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

/-- **The canonical decider on numbers is the canonical decider.** -/
theorem acceptsN_iff (x y : Fin (g.nV + 1)) (a b : Fin (2 ^ g.ansLen)) :
    g.acceptsN x y a b = true ↔ g.Accepts x y (vecEquiv _ a) (vecEquiv _ b) := by
  have hxy : (x : ℕ) = y ↔ x = y := Fin.val_inj
  have hab : (a : ℕ) = b ↔ vecEquiv _ a = vecEquiv _ b :=
    Fin.val_inj.trans (vecEquiv _).injective.eq_iff.symm
  have himp : ((!decide ((x : ℕ) = y) || decide ((a : ℕ) = b)) = true) ↔
      (x = y → vecEquiv _ a = vecEquiv _ b) := by
    rw [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff, hxy, hab]
    tauto
  unfold acceptsN Accepts
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, himp, decide_eq_true_iff,
    decide_eq_true_iff, ← g.wellFormatted_iff x a, ← g.wellFormatted_iff y b, List.all_eq_true]
  simp only [and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  refine forall₂_congr fun e _ => ?_
  rw [elem_iff, g.readable_vecEquiv, g.readable_vecEquiv, g.full_vecEquiv, g.full_vecEquiv,
    satB_iff]

/-! ## The same game -/

theorem toGameData_nA_succ : g.toGameData.nA + 1 = 2 ^ g.ansLen := by
  show 2 ^ g.ansLenL - 1 + 1 = _
  rw [g.ansLenL_eq]
  exact Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)

/-- The answers of the game description, as bit vectors. -/
def ansIdx : Fin (g.toGameData.nA + 1) ≃ (Fin g.ansLen → Bool) :=
  (finCongr g.toGameData_nA_succ).trans (vecEquiv g.ansLen)

theorem toGameData_μ (x y : Fin (g.nV + 1)) : g.toGameData.game.μ x y = g.game.μ x y := rfl

theorem toGameData_D (x y : Fin (g.nV + 1)) (a b : Fin (g.toGameData.nA + 1)) :
    g.toGameData.game.D x y a b = g.game.D x y (g.ansIdx a) (g.ansIdx b) := by
  refine (GameData.game_D g.toGameData x y a b).trans ?_
  change _ = decide (g.Accepts x y (g.ansIdx a) (g.ansIdx b))
  have hlt : ∀ c : Fin (g.toGameData.nA + 1), (c : ℕ) < 2 ^ g.ansLenL := fun c => by
    rw [g.ansLenL_eq, ← g.toGameData_nA_succ]; exact c.isLt
  have key : decide ((x.val, y.val, a.val, b.val) ∈ g.toGameData.acc) =
      decide (g.Accepts x y (g.ansIdx a) (g.ansIdx b)) := by
    rw [decide_eq_decide]
    change (x.val, y.val, a.val, b.val) ∈ g.accN ↔ _
    rw [g.mem_accN]
    simp only [x.isLt, y.isLt, hlt a, hlt b, true_and]
    exact g.acceptsN_iff x y (finCongr g.toGameData_nA_succ a) (finCongr g.toGameData_nA_succ b)
  split_ifs with h
  · obtain ⟨rfl, hne⟩ := h
    symm
    rw [decide_eq_false_iff_not]
    exact fun hacc => hne (g.ansIdx.injective (hacc.1 rfl))
  · exact key

/-- **The game description has the quantum value of the tailored one.** -/
theorem quantumValue_toGameData :
    MIPRE.quantumValue g.toGameData.game = MIPRE.quantumValue g.game :=
  MIPRE.quantumValue_eq_of_equiv g.game g.toGameData.game (Equiv.refl _) (Equiv.refl _) g.ansIdx
    g.ansIdx (fun x y => g.toGameData_μ x y) (fun x y a b => g.toGameData_D x y a b)

/-! ## The conversion is primitive recursive -/

section Primrec

theorem primrec_tuple : Primrec (equivTuple : TailoredGameData → _) :=
  Primrec.of_equiv (e := equivTuple)

theorem primrec_nV : Primrec fun g : TailoredGameData => g.nV :=
  Primrec.fst.comp primrec_tuple

theorem primrec_lenR : Primrec fun g : TailoredGameData => g.lenR :=
  Primrec.fst.comp (Primrec.snd.comp primrec_tuple)

theorem primrec_lenL : Primrec fun g : TailoredGameData => g.lenL :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp primrec_tuple))

theorem primrec_w : Primrec fun g : TailoredGameData => g.w :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp primrec_tuple)))

theorem primrec_cons : Primrec fun g : TailoredGameData => g.cons :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp primrec_tuple)))

theorem primrec_lenRAt : Primrec₂ fun (g : TailoredGameData) (x : ℕ) => g.lenRAt x :=
  (Primrec.list_getD 0).comp (primrec_lenR.comp Primrec.fst) Primrec.snd

theorem primrec_lenLAt : Primrec₂ fun (g : TailoredGameData) (x : ℕ) => g.lenLAt x :=
  (Primrec.list_getD 0).comp (primrec_lenL.comp Primrec.fst) Primrec.snd

theorem primrec_lenAt : Primrec₂ fun (g : TailoredGameData) (x : ℕ) => g.lenAt x :=
  Primrec.nat_add.comp primrec_lenRAt primrec_lenLAt

theorem primrec_ansLenL : Primrec fun g : TailoredGameData => g.ansLenL := by
  have hmap : Primrec fun g : TailoredGameData => (List.range (g.nV + 1)).map g.lenAt :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp primrec_nV)) primrec_lenAt
  exact (Primrec.list_foldr hmap (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun g => rfl

theorem primrec_testBit : Primrec₂ fun a i : ℕ => a.testBit i := by
  have h : PrimrecPred fun p : ℕ × ℕ => p.1 / 2 ^ p.2 % 2 = 1 :=
    Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.fst
      (primrec_nat_pow.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2))
      (Primrec.const 1)
  exact h.decide.of_eq fun p => Nat.testBit_eq_decide_div_mod_eq.symm

theorem primrec_rdN : Primrec fun q : TailoredGameData × ℕ × ℕ => q.1.rdN q.2.1 q.2.2 :=
  Primrec.list_map (Primrec.list_range.comp (primrec_lenRAt.comp Primrec.fst
    (Primrec.fst.comp Primrec.snd)))
    (primrec_testBit.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem primrec_flN : Primrec fun q : TailoredGameData × ℕ × ℕ => q.1.flN q.2.1 q.2.2 :=
  Primrec.list_map (Primrec.list_range.comp (primrec_lenAt.comp Primrec.fst
    (Primrec.fst.comp Primrec.snd)))
    (primrec_testBit.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem primrec_parityB : Primrec parityB := by
  have hstep : Primrec₂ fun (_ : List Bool) (p : Bool × Bool) => !decide (p.1 = p.2) :=
    (Primrec.not.comp (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).decide).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const false) hstep).of_eq fun l => rfl

theorem primrec_satB : Primrec₂ satB := by
  have hlen : PrimrecPred fun p : List Bool × List Bool => p.1.length = p.2.length :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)
  have hmap : Primrec fun p : List Bool × List Bool =>
      (List.range p.1.length).map fun i => p.1.getD i false && p.2.getD i false :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
      (Primrec.and.comp ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst)
        Primrec.snd) ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (Primrec.and.comp hlen.decide (Primrec.not.comp (primrec_parityB.comp hmap))).to₂.of_eq
    fun c v => rfl

/-- The per-constraint test of `acceptsN`, as a function of the description, the tuple and the
constraint entry. -/
def consTest (q : TailoredGameData × ℕ × ℕ × ℕ × ℕ) (e : ℕ × ℕ × List Bool × List Bool) : Bool :=
  !(decide (e.1 = q.2.1) && decide (e.2.1 = q.2.2.1) &&
      decide (e.2.2.1 = q.1.rdN q.2.1 q.2.2.2.1 ++ q.1.rdN q.2.2.1 q.2.2.2.2)) ||
    satB e.2.2.2 (q.1.flN q.2.1 q.2.2.2.1 ++ q.1.flN q.2.2.1 q.2.2.2.2 ++ [true])

set_option maxHeartbeats 1000000 in
theorem primrec_consTest : Primrec₂ consTest := by
  -- the components of the tuple and of the entry
  have hg : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.1.1 := Primrec.fst.comp Primrec.fst
  have hx : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.1.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hy : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.1.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have ha : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hb : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.1.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have he1 : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.2.1 := Primrec.fst.comp Primrec.snd
  have he2 : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he3 : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.2.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have he4 : Primrec fun p : (TailoredGameData × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × List Bool × List Bool) =>
      p.2.2.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrdx := primrec_rdN.comp (hg.pair (hx.pair ha))
  have hrdy := primrec_rdN.comp (hg.pair (hy.pair hb))
  have hflx := primrec_flN.comp (hg.pair (hx.pair ha))
  have hfly := primrec_flN.comp (hg.pair (hy.pair hb))
  have hc1 := (Primrec.eq.comp he1 hx).decide
  have hc2 := (Primrec.eq.comp he2 hy).decide
  have hc3 := (Primrec.eq.comp he3 (Primrec.list_append.comp hrdx hrdy)).decide
  have hsat := primrec_satB.comp he4
    (Primrec.list_append.comp (Primrec.list_append.comp hflx hfly) (Primrec.const [true]))
  exact (Primrec.or.comp (Primrec.not.comp (Primrec.and.comp (Primrec.and.comp hc1 hc2) hc3))
    hsat).to₂.of_eq fun q e => rfl

theorem all_eq_foldr {α : Type*} (l : List α) (f : α → Bool) :
    l.all f = l.foldr (fun e b => f e && b) true := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [List.all_cons, ih, List.foldr_cons]

set_option maxHeartbeats 1000000 in
theorem primrec_acceptsN :
    Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ × ℕ =>
      q.1.acceptsN q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have hg : Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ × ℕ => q.1 := Primrec.fst
  have hx : Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ × ℕ => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hy : Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ × ℕ => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ × ℕ => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ × ℕ => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h1 := Primrec.or.comp (Primrec.not.comp (Primrec.eq.comp hx hy).decide)
    (Primrec.eq.comp ha hb).decide
  have h2 := (Primrec.nat_lt.comp ha
    (primrec_nat_pow.comp (Primrec.const 2) (primrec_lenAt.comp hg hx))).decide
  have h3 := (Primrec.nat_lt.comp hb
    (primrec_nat_pow.comp (Primrec.const 2) (primrec_lenAt.comp hg hy))).decide
  have h4 : Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ × ℕ =>
      q.1.cons.foldr (fun e b => consTest q e && b) true :=
    Primrec.list_foldr (primrec_cons.comp hg) (Primrec.const true)
      (Primrec.and.comp (primrec_consTest.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp h1 h2) h3) h4).of_eq fun q => ?_
  rw [acceptsN, all_eq_foldr]
  rfl

set_option maxHeartbeats 1000000 in
theorem primrec_accN : Primrec accN := by
  -- the innermost filter, over `b`, with the context `(g, x, y, a)`
  have hopt : Primrec₂ fun (q : TailoredGameData × ℕ × ℕ × ℕ) (b : ℕ) =>
      if q.1.acceptsN q.2.1 q.2.2.1 q.2.2.2 b = true then
        some (q.2.1, q.2.2.1, q.2.2.2, b) else none := by
    have hacc : PrimrecPred fun p : (TailoredGameData × ℕ × ℕ × ℕ) × ℕ =>
        p.1.1.acceptsN p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 = true :=
      Primrec.eq.comp (primrec_acceptsN.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
            ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
              Primrec.snd))))) (Primrec.const true)
    exact (Primrec.ite hacc (Primrec.option_some.comp
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
            Primrec.snd)))) (Primrec.const none)).to₂
  have hrangeA : Primrec fun q : TailoredGameData × ℕ × ℕ × ℕ =>
      List.range (2 ^ q.1.ansLenL) :=
    Primrec.list_range.comp (primrec_nat_pow.comp (Primrec.const 2)
      (primrec_ansLenL.comp Primrec.fst))
  have hA : Primrec₂ fun (q : TailoredGameData × ℕ × ℕ) (a : ℕ) =>
      (List.range (2 ^ q.1.ansLenL)).filterMap fun b =>
        if q.1.acceptsN q.2.1 q.2.2 a b = true then some (q.2.1, q.2.2, a, b) else none :=
    (Primrec.listFilterMap (hrangeA.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))))
      (hopt.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
            (Primrec.snd.comp Primrec.fst)))) Primrec.snd).to₂).to₂
  have hY : Primrec₂ fun (q : TailoredGameData × ℕ) (y : ℕ) =>
      (List.range (2 ^ q.1.ansLenL)).flatMap fun a =>
        (List.range (2 ^ q.1.ansLenL)).filterMap fun b =>
          if q.1.acceptsN q.2 y a b = true then some (q.2, y, a, b) else none :=
    (Primrec.list_flatMap (Primrec.list_range.comp (primrec_nat_pow.comp (Primrec.const 2)
      (primrec_ansLenL.comp (Primrec.fst.comp Primrec.fst))))
      (hA.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)))
        Primrec.snd).to₂).to₂
  have hX : Primrec₂ fun (g : TailoredGameData) (x : ℕ) =>
      (List.range (g.nV + 1)).flatMap fun y =>
        (List.range (2 ^ g.ansLenL)).flatMap fun a =>
          (List.range (2 ^ g.ansLenL)).filterMap fun b =>
            if g.acceptsN x y a b = true then some (x, y, a, b) else none :=
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp
      (primrec_nV.comp Primrec.fst))) (hY.comp Primrec.fst Primrec.snd).to₂).to₂
  exact (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp primrec_nV))
    hX).of_eq fun g => rfl

/-- **The conversion is primitive recursive.** -/
theorem primrec_toGameData : Primrec toGameData :=
  ((Primrec.of_equiv_symm (e := GameData.equivTuple)).comp
    (primrec_nV.pair ((Primrec.nat_sub.comp (primrec_nat_pow.comp (Primrec.const 2)
      primrec_ansLenL) (Primrec.const 1)).pair (primrec_w.pair primrec_accN)))).of_eq fun _ => rfl

end Primrec

end TailoredGameValue.TailoredGameData

end
