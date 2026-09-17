/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Kinds

/-!
# The clause families of the tableau, on decoded fields

A *candidate* clause is three field records and three signs (`Cand`): what the describer
reads off its `3m + 3` input bits. `Cand.Dec c cl` says the candidate decodes to the tableau
clause `cl` (each record to the variable of the corresponding literal, each sign to its
polarity). For each sub-family of the tableau of the interpreter machine
(`startClauses`, `freeClauses`, `bdryClauses`, `emitClauses`, `finalClauses` of
`Tableau.lean`) this file gives a predicate on candidates, stated on the numeric fields
alone, and proves it exact: it holds iff the candidate decodes to a clause of the
sub-family. The window family is `Window.lean`; the formulas computing these predicates are
`FamilyFml.lean` (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Candidates and decoding -/

/-- A candidate clause: three field records and three signs. -/
structure Cand where
  F₁ : Fields
  s₁ : Bool
  F₂ : Fields
  s₂ : Bool
  F₃ : Fields
  s₃ : Bool

variable (e G : ℕ)

/-- The record `F` with sign `s` decodes to the literal `l`. -/
def LitDec (F : Fields) (s : Bool) (l : Lit (TabVar 7 6 Sym Ctl (Sof e) G)) : Prop :=
  decodeVar e G F = some l.var ∧ s = l.pos

/-- The candidate decodes to the clause `cl`. -/
def Cand.Dec (c : Cand) (cl : Clause3 (TabVar 7 6 Sym Ctl (Sof e) G)) : Prop :=
  LitDec e G c.F₁ c.s₁ cl.l₁ ∧ LitDec e G c.F₂ c.s₂ cl.l₂ ∧ LitDec e G c.F₃ c.s₃ cl.l₃

theorem Cand.dec_unit (c : Cand) (v : TabVar 7 6 Sym Ctl (Sof e) G) (b : Bool) :
    c.Dec e G (unit v b) ↔
      decodeVar e G c.F₁ = some v ∧ c.s₁ = b ∧ decodeVar e G c.F₂ = some v ∧ c.s₂ = b ∧
        decodeVar e G c.F₃ = some v ∧ c.s₃ = b := by
  simp only [Cand.Dec, LitDec, unit, cl]
  tauto

theorem Cand.dec_cl (c : Cand) (l₁ l₂ l₃ : Lit (TabVar 7 6 Sym Ctl (Sof e) G)) :
    c.Dec e G (cl l₁ l₂ l₃) ↔
      decodeVar e G c.F₁ = some l₁.var ∧ c.s₁ = l₁.pos ∧ decodeVar e G c.F₂ = some l₂.var ∧
        c.s₂ = l₂.pos ∧ decodeVar e G c.F₃ = some l₃.var ∧ c.s₃ = l₃.pos := by
  simp only [Cand.Dec, LitDec, cl]
  tauto

/-! ## Codes of positions and values -/

theorem tapeOfCode_of_lt {k : ℕ} (h : k < 13) : ∃ d, tapeOfCode k = some d := by
  unfold tapeOfCode
  split_ifs <;> exact ⟨_, rfl⟩

theorem symOfCode_of_lt {k : ℕ} (h : k < 7) : ∃ v, symOfCode k = some v := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | exact ⟨_, rfl⟩ | omega

theorem qOfCode_of_lt {k : ℕ} (h : k < QC) : ∃ q, qOfCode k = some q := by
  unfold qOfCode
  rw [dif_pos h]
  exact ⟨_, rfl⟩

theorem tapeCode_lt_seven_iff (d : Tape 7 6) : tapeCode d < 7 ↔ ∃ j, d = .inl j := by
  rcases d with j | j
  · exact ⟨fun _ => ⟨j, rfl⟩, fun _ => by simp [tapeCode]⟩
  · simp [tapeCode]

/-- The start cell, numerically. -/
theorem startCell_val (S : ℕ) (d : Tape 7 6) :
    (startCell S d : ℕ) = if tapeCode d < 7 then 3 else S + 3 := by
  rcases d with j | j <;> simp [startCell, tapeCode]

/-- Boundary cells, numerically. -/
theorem isBdry_iff {S : ℕ} (p : Pos S) : p.IsBdry ↔ (p : ℕ) < 2 ∨ 2 * S + 5 ≤ p := by
  unfold Pos.IsBdry numCells
  omega

/-- The code of the value of cell `p` of an input tape holding `x`. -/
def cellCode (x : List Sym) (S p : ℕ) : ℕ :=
  if p < 2 ∨ 2 * S + 5 ≤ p then 6
  else if h : 3 ≤ p ∧ p - 3 < x.length then symCode (.sym x[p - 3]) else 5

theorem symCode_inputCellVal (x : List Sym) {S : ℕ} (p : Pos S) :
    symCode (inputCellVal x p) = cellCode x S p := by
  unfold inputCellVal cellCode
  by_cases hb : p.IsBdry
  · rw [if_pos hb, if_pos ((isBdry_iff p).mp hb)]; rfl
  · rw [if_neg hb, if_neg (fun h => hb ((isBdry_iff p).mpr h))]
    split_ifs <;> rfl

/-- The code of the value of cell `p` of a work tape at time `0`. -/
def workCode (S p : ℕ) : ℕ := if p < 2 ∨ 2 * S + 5 ≤ p then 6 else 5

theorem symCode_workCellVal₀ {S : ℕ} (p : Pos S) : symCode (workCellVal₀ (Symbol := Sym) p) = workCode S p := by
  unfold workCellVal₀ workCode
  by_cases hb : p.IsBdry
  · rw [if_pos hb, if_pos ((isBdry_iff p).mp hb)]; rfl
  · rw [if_neg hb, if_neg (fun h => hb ((isBdry_iff p).mpr h))]; rfl

/-- The unary tape `1^T`: cells `3 .. T + 2` hold `1`. -/
theorem cellCode_replicate (T S p : ℕ) :
    cellCode (List.replicate T .one) S p =
      if p < 2 ∨ 2 * S + 5 ≤ p then 6 else if 3 ≤ p ∧ p < T + 3 then 1 else 5 := by
  unfold cellCode
  by_cases h1 : p < 2 ∨ 2 * S + 5 ≤ p
  · simp [h1]
  · simp only [h1, if_false, List.length_replicate]
    by_cases h2 : 3 ≤ p ∧ p - 3 < T
    · rw [dif_pos h2, if_pos (by omega)]; simp [symCode]
    · rw [dif_neg h2, if_neg (by omega)]

/-! ## Decoding by kind: existence and same-variable lemmas -/

theorem exists_cell {F : Fields} (h : IsCell e F) :
    ∃ (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym),
      decodeVar e G F = some (.cell t d p v) := by
  rcases h with ⟨hf, htag, ht, hd, hp, hv⟩ | ⟨hf, hok, htag, ht, hd, hp, hv⟩
  · obtain ⟨d, hd'⟩ := tapeOfCode_of_lt hd
    obtain ⟨v, hv'⟩ := symOfCode_of_lt hv
    exact ⟨⟨F.t, by omega⟩, d, ⟨F.p, hp⟩, v, (decodeVar_cell_iff e G F _ _ _ _).mpr
      ⟨Or.inl ⟨hf, htag, ht, hd, hp, hv⟩, rfl, (tapeOfCode_eq_some hd').symm, rfl,
        (symOfCode_eq_some hv').symm⟩⟩
  · obtain ⟨d, hd'⟩ := tapeOfCode_of_lt (by omega : F.d < 13)
    obtain ⟨v, hv'⟩ := symOfCode_of_lt hv
    exact ⟨⟨F.t, by omega⟩, d, ⟨F.p, hp⟩, v, (decodeVar_cell_iff e G F _ _ _ _).mpr
      ⟨Or.inr ⟨hf, hok, htag, ht, hd, hp, hv⟩, rfl, (tapeOfCode_eq_some hd').symm, rfl,
        (symOfCode_eq_some hv').symm⟩⟩

theorem exists_head {F : Fields} (h : IsHead e F) :
    ∃ (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)), decodeVar e G F = some (.head t d p) := by
  obtain ⟨hf, htag, ht, hd, hp⟩ := h
  obtain ⟨d, hd'⟩ := tapeOfCode_of_lt hd
  exact ⟨⟨F.t, by omega⟩, d, ⟨F.p, hp⟩, (decodeVar_head_iff e G F _ _ _).mpr
    ⟨⟨hf, htag, ht, hd, hp⟩, rfl, (tapeOfCode_eq_some hd').symm, rfl⟩⟩

theorem exists_state {F : Fields} (h : IsState e F) :
    ∃ (t : Fin (Sof e + 1)) (q : Option Ctl), decodeVar e G F = some (.state t q) := by
  obtain ⟨hf, htag, ht, hq⟩ := h
  obtain ⟨q, hq'⟩ := qOfCode_of_lt hq
  exact ⟨⟨F.t, by omega⟩, q, (decodeVar_state_iff e G F _ _).mpr
    ⟨⟨hf, htag, ht, hq⟩, rfl, (qOfCode_eq_some hq').symm⟩⟩

theorem exists_emitOne {F : Fields} (h : IsEmitOne e F) :
    ∃ t : Fin (Sof e), decodeVar e G F = some (.emitOne t) :=
  ⟨⟨F.t, h.2.2⟩, (decodeVar_emitOne_iff e G F _).mpr ⟨h, rfl⟩⟩

theorem exists_emitBad {F : Fields} (h : IsEmitBad e F) :
    ∃ t : Fin (Sof e), decodeVar e G F = some (.emitBad t) :=
  ⟨⟨F.t, h.2.2⟩, (decodeVar_emitBad_iff e G F _).mpr ⟨h, rfl⟩⟩

theorem exists_emitted {F : Fields} (h : IsEmitted e F) :
    ∃ t : Fin (Sof e + 1), decodeVar e G F = some (.emitted t) :=
  ⟨⟨F.t, by have := h.2.2; omega⟩, (decodeVar_emitted_iff e G F _).mpr ⟨h, rfl⟩⟩

theorem exists_aux {F : Fields} (h : IsAux e G F) :
    ∃ (t : Fin (Sof e)) (js : Tape 7 6 → Center (Sof e)) (g : Fin G),
      decodeVar e G F = some (.aux t js g) :=
  ⟨⟨F.t, h.2.2.1⟩, fun d => ⟨F.js ⟨tapeCode d, tapeCode_lt d⟩, h.2.2.2.1 _⟩, ⟨F.g, h.2.2.2.2⟩,
    (decodeVar_aux_iff e G F _ _ _).mpr ⟨h, rfl, fun _ => rfl, rfl⟩⟩

/-- Two records denote the same cell variable. -/
def cellEq (F F' : Fields) : Prop := F.t = F'.t ∧ F.d = F'.d ∧ F.p = F'.p ∧ F.v = F'.v

/-- Two records denote the same head variable. -/
def headEq (F F' : Fields) : Prop := F.t = F'.t ∧ F.d = F'.d ∧ F.p = F'.p

/-- Two records denote the same state variable. -/
def stateEq (F F' : Fields) : Prop := F.t = F'.t ∧ F.q = F'.q

/-- Two records denote the same gate variable. -/
def auxEq (F F' : Fields) : Prop := F.t = F'.t ∧ (∀ k, F.js k = F'.js k) ∧ F.g = F'.g

theorem decodeVar_cell_congr {F F' : Fields} (h : IsCell e F) (h' : IsCell e F') (heq : cellEq F F') :
    decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h
  obtain ⟨-, h1, h2, h3, h4⟩ := (decodeVar_cell_iff e G F t d p v).mp hd
  rw [hd, eq_comm, decodeVar_cell_iff]
  exact ⟨h', heq.1 ▸ h1, heq.2.1 ▸ h2, heq.2.2.1 ▸ h3, heq.2.2.2 ▸ h4⟩

theorem cellEq_of_decode {F F' : Fields} {t d p v} (h : decodeVar e G F = some (.cell t d p v))
    (h' : decodeVar e G F' = some (.cell t d p v)) : cellEq F F' := by
  obtain ⟨-, h1, h2, h3, h4⟩ := (decodeVar_cell_iff e G F t d p v).mp h
  obtain ⟨-, h1', h2', h3', h4'⟩ := (decodeVar_cell_iff e G F' t d p v).mp h'
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem decodeVar_head_congr {F F' : Fields} (h : IsHead e F) (h' : IsHead e F') (heq : headEq F F') :
    decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, d, p, hd⟩ := exists_head e G h
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_head_iff e G F t d p).mp hd
  rw [hd, eq_comm, decodeVar_head_iff]
  exact ⟨h', heq.1 ▸ h1, heq.2.1 ▸ h2, heq.2.2 ▸ h3⟩

theorem headEq_of_decode {F F' : Fields} {t d p} (h : decodeVar e G F = some (.head t d p))
    (h' : decodeVar e G F' = some (.head t d p)) : headEq F F' := by
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_head_iff e G F t d p).mp h
  obtain ⟨-, h1', h2', h3'⟩ := (decodeVar_head_iff e G F' t d p).mp h'
  exact ⟨by omega, by omega, by omega⟩

theorem decodeVar_state_congr {F F' : Fields} (h : IsState e F) (h' : IsState e F')
    (heq : stateEq F F') : decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, q, hd⟩ := exists_state e G h
  obtain ⟨-, h1, h2⟩ := (decodeVar_state_iff e G F t q).mp hd
  rw [hd, eq_comm, decodeVar_state_iff]
  exact ⟨h', heq.1 ▸ h1, heq.2 ▸ h2⟩

theorem stateEq_of_decode {F F' : Fields} {t q} (h : decodeVar e G F = some (.state t q))
    (h' : decodeVar e G F' = some (.state t q)) : stateEq F F' := by
  obtain ⟨-, h1, h2⟩ := (decodeVar_state_iff e G F t q).mp h
  obtain ⟨-, h1', h2'⟩ := (decodeVar_state_iff e G F' t q).mp h'
  exact ⟨by omega, by omega⟩

theorem decodeVar_emitOne_congr {F F' : Fields} (h : IsEmitOne e F) (h' : IsEmitOne e F')
    (heq : F.t = F'.t) : decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, hd⟩ := exists_emitOne e G h
  obtain ⟨-, h1⟩ := (decodeVar_emitOne_iff e G F t).mp hd
  rw [hd, eq_comm, decodeVar_emitOne_iff]
  exact ⟨h', heq ▸ h1⟩

theorem decodeVar_emitBad_congr {F F' : Fields} (h : IsEmitBad e F) (h' : IsEmitBad e F')
    (heq : F.t = F'.t) : decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, hd⟩ := exists_emitBad e G h
  obtain ⟨-, h1⟩ := (decodeVar_emitBad_iff e G F t).mp hd
  rw [hd, eq_comm, decodeVar_emitBad_iff]
  exact ⟨h', heq ▸ h1⟩

theorem decodeVar_emitted_congr {F F' : Fields} (h : IsEmitted e F) (h' : IsEmitted e F')
    (heq : F.t = F'.t) : decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, hd⟩ := exists_emitted e G h
  obtain ⟨-, h1⟩ := (decodeVar_emitted_iff e G F t).mp hd
  rw [hd, eq_comm, decodeVar_emitted_iff]
  exact ⟨h', heq ▸ h1⟩

theorem decodeVar_aux_congr {F F' : Fields} (h : IsAux e G F) (h' : IsAux e G F') (heq : auxEq F F') :
    decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, js, g, hd⟩ := exists_aux e G h
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_aux_iff e G F t js g).mp hd
  rw [hd, eq_comm, decodeVar_aux_iff]
  exact ⟨h', heq.1 ▸ h1, fun d => (heq.2.1 _) ▸ h2 d, heq.2.2 ▸ h3⟩

theorem auxEq_of_decode {F F' : Fields} {t js g} (h : decodeVar e G F = some (.aux t js g))
    (h' : decodeVar e G F' = some (.aux t js g)) : auxEq F F' := by
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_aux_iff e G F t js g).mp h
  obtain ⟨-, h1', h2', h3'⟩ := (decodeVar_aux_iff e G F' t js g).mp h'
  refine ⟨by omega, fun k => ?_, by omega⟩
  obtain ⟨d, hd⟩ := tapeOfCode_of_lt k.isLt
  have hk : k = ⟨tapeCode d, tapeCode_lt d⟩ := by ext; simp [tapeOfCode_eq_some hd]
  rw [hk, h2 d, h2' d]


theorem symCode_inj {v v' : CellVal Sym} : symCode v = symCode v' ↔ v = v' :=
  ⟨fun h => by
    have := symOfCode_symCode v
    rw [h, symOfCode_symCode] at this
    exact (Option.some.inj this).symm, fun h => h ▸ rfl⟩

theorem qCode_inj {q q' : Option Ctl} : qCode q = qCode q' ↔ q = q' := by
  unfold qCode
  rw [Fin.val_inj]
  exact (Fintype.equivFin (Option Ctl)).injective.eq_iff

theorem tapeCode_inl (j : Fin 7) : tapeCode (.inl j) = j := rfl

theorem tapeCode_inr (j : Fin 6) : tapeCode (.inr j) = 7 + j := rfl

theorem seven_le_tapeCode_iff (d : Tape 7 6) : 7 ≤ tapeCode d ↔ ∃ j, d = .inr j := by
  rcases d with j | j
  · simp [tapeCode]
  · exact ⟨fun _ => ⟨j, rfl⟩, fun _ => by simp [tapeCode]⟩

/-! ## Unit clauses by kind -/

/-- The three records denote the same cell variable. -/
def UnitCell (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ cellEq c.F₁ c.F₂ ∧ cellEq c.F₁ c.F₃

/-- The three records denote the same head variable. -/
def UnitHead (c : Cand) : Prop :=
  IsHead e c.F₁ ∧ IsHead e c.F₂ ∧ IsHead e c.F₃ ∧ headEq c.F₁ c.F₂ ∧ headEq c.F₁ c.F₃

/-- The three records denote the same state variable. -/
def UnitState (c : Cand) : Prop :=
  IsState e c.F₁ ∧ IsState e c.F₂ ∧ IsState e c.F₃ ∧ stateEq c.F₁ c.F₂ ∧ stateEq c.F₁ c.F₃

/-- The three records denote the same `emitBad` variable. -/
def UnitEmitBad (c : Cand) : Prop :=
  IsEmitBad e c.F₁ ∧ IsEmitBad e c.F₂ ∧ IsEmitBad e c.F₃ ∧ c.F₁.t = c.F₂.t ∧ c.F₁.t = c.F₃.t

/-- The three records denote the same `emitted` variable. -/
def UnitEmitted (c : Cand) : Prop :=
  IsEmitted e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₁.t = c.F₂.t ∧ c.F₁.t = c.F₃.t

/-- The three records denote the same gate variable. -/
def UnitAux (c : Cand) : Prop :=
  IsAux e G c.F₁ ∧ IsAux e G c.F₂ ∧ IsAux e G c.F₃ ∧ auxEq c.F₁ c.F₂ ∧ auxEq c.F₁ c.F₃

/-- The three signs agree. -/
def SameSigns (c : Cand) : Prop := c.s₂ = c.s₁ ∧ c.s₃ = c.s₁

theorem dec_unit_cell (c : Cand) (t d p v) (b : Bool) :
    c.Dec e G (unit (.cell t d p v) b) ↔
      decodeVar e G c.F₁ = some (.cell t d p v) ∧ UnitCell e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_cell_iff e G _ _ _ _ _).mp h₁).1, ((decodeVar_cell_iff e G _ _ _ _ _).mp h₂).1,
      ((decodeVar_cell_iff e G _ _ _ _ _).mp h₃).1, cellEq_of_decode e G h₁ h₂, cellEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_cell_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_cell_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩

theorem dec_unit_head (c : Cand) (t d p) (b : Bool) :
    c.Dec e G (unit (.head t d p) b) ↔
      decodeVar e G c.F₁ = some (.head t d p) ∧ UnitHead e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_head_iff e G _ _ _ _).mp h₁).1, ((decodeVar_head_iff e G _ _ _ _).mp h₂).1,
      ((decodeVar_head_iff e G _ _ _ _).mp h₃).1, headEq_of_decode e G h₁ h₂, headEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_head_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_head_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩

theorem dec_unit_state (c : Cand) (t q) (b : Bool) :
    c.Dec e G (unit (.state t q) b) ↔
      decodeVar e G c.F₁ = some (.state t q) ∧ UnitState e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_state_iff e G _ _ _).mp h₁).1, ((decodeVar_state_iff e G _ _ _).mp h₂).1,
      ((decodeVar_state_iff e G _ _ _).mp h₃).1, stateEq_of_decode e G h₁ h₂, stateEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_state_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_state_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩

theorem dec_unit_emitBad (c : Cand) (t) (b : Bool) :
    c.Dec e G (unit (.emitBad t) b) ↔
      decodeVar e G c.F₁ = some (.emitBad t) ∧ UnitEmitBad e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    have k₁ := (decodeVar_emitBad_iff e G _ _).mp h₁
    have k₂ := (decodeVar_emitBad_iff e G _ _).mp h₂
    have k₃ := (decodeVar_emitBad_iff e G _ _).mp h₃
    exact ⟨h₁, ⟨k₁.1, k₂.1, k₃.1, by rw [k₁.2, k₂.2], by rw [k₁.2, k₃.2]⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_emitBad_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_emitBad_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩

theorem dec_unit_emitted (c : Cand) (t) (b : Bool) :
    c.Dec e G (unit (.emitted t) b) ↔
      decodeVar e G c.F₁ = some (.emitted t) ∧ UnitEmitted e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    have k₁ := (decodeVar_emitted_iff e G _ _).mp h₁
    have k₂ := (decodeVar_emitted_iff e G _ _).mp h₂
    have k₃ := (decodeVar_emitted_iff e G _ _).mp h₃
    exact ⟨h₁, ⟨k₁.1, k₂.1, k₃.1, by rw [k₁.2, k₂.2], by rw [k₁.2, k₃.2]⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_emitted_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_emitted_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩

theorem dec_unit_aux (c : Cand) (t js g) (b : Bool) :
    c.Dec e G (unit (.aux t js g) b) ↔
      decodeVar e G c.F₁ = some (.aux t js g) ∧ UnitAux e G c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_aux_iff e G _ _ _ _).mp h₁).1, ((decodeVar_aux_iff e G _ _ _ _).mp h₂).1,
      ((decodeVar_aux_iff e G _ _ _ _).mp h₃).1, auxEq_of_decode e G h₁ h₂, auxEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_aux_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_aux_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩

theorem exists_mem_union {α : Type*} (A B : Set α) (P : α → Prop) :
    (∃ x ∈ A ∪ B, P x) ↔ (∃ x ∈ A, P x) ∨ (∃ x ∈ B, P x) := by
  simp only [Set.mem_union, or_and_right, exists_or]

/-! ## The start family -/

variable (fixed : Fin 7 → Option (List Sym))

/-- `unit (head 0 d p) (decide (p = startCell S d))`. -/
def StartHead (c : Cand) : Prop :=
  UnitHead e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧
    c.s₁ = decide (c.F₁.p = if c.F₁.d < 7 then 3 else Sof e + 3)

theorem startHead_iff (c : Cand) :
    StartHead e c ↔ ∃ cl ∈ ({cl | ∃ d p, cl = unit (.head 0 d p) (decide (p = startCell (Sof e) d))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hs⟩
    obtain ⟨t, d, p, hd⟩ := exists_head e G hu.1
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ t d p).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    refine ⟨_, ⟨d, p, rfl⟩, (dec_unit_head e G c _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff, startCell_val, ← hpp, ← hdd]
  · rintro ⟨_, ⟨d, p, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_head e G c _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ _ d p).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff, startCell_val, ← hpp, ← hdd]

/-- `unit (state 0 q) (decide (q = some U.q₀))`. -/
def StartState (c : Cand) : Prop :=
  UnitState e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ c.s₁ = decide (c.F₁.q = qCode (some U.q₀))

theorem startState_iff (c : Cand) :
    StartState e c ↔ ∃ cl ∈ ({cl | ∃ q, cl = unit (.state 0 q) (decide (q = some U.q₀))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hs⟩
    obtain ⟨t, q, hd⟩ := exists_state e G hu.1
    obtain ⟨-, htt, hqq⟩ := (decodeVar_state_iff e G _ t q).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    refine ⟨_, ⟨q, rfl⟩, (dec_unit_state e G c _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [hqq, qCode_inj]
  · rintro ⟨_, ⟨q, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_state e G c _ _ _).mp hdec
    obtain ⟨-, htt, hqq⟩ := (decodeVar_state_iff e G _ _ q).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [hqq, qCode_inj]

/-- `unit (cell 0 (inl j) p v) (decide (v = inputCellVal x p))` for `fixed j = some x`. -/
def StartFixed (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧
    ∃ (j : Fin 7) (x : List Sym), fixed j = some x ∧ c.F₁.d = j ∧
      c.s₁ = decide (c.F₁.v = cellCode x (Sof e) c.F₁.p)

theorem startFixed_iff (c : Cand) :
    StartFixed e fixed c ↔ ∃ cl ∈ ({cl | ∃ j x p v, fixed j = some x ∧
      cl = unit (.cell 0 (.inl j) p v) (decide (v = inputCellVal x p))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, j, x, hx, hj, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hj]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    refine ⟨_, ⟨j', x, p, v, hx, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_inputCellVal, ← hvv, ← hpp]
  · rintro ⟨_, ⟨j, x, p, v, hx, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], j, x, hx, by rw [hdd, tapeCode_inl], ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_inputCellVal, ← hvv, ← hpp]

/-- `unit (cell 0 (inr j) p v) (decide (v = workCellVal₀ p))`. -/
def StartWork (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ 7 ≤ c.F₁.d ∧
    c.s₁ = decide (c.F₁.v = workCode (Sof e) c.F₁.p)

theorem startWork_iff (c : Cand) :
    StartWork e c ↔ ∃ cl ∈ ({cl | ∃ j p v, cl = unit (.cell 0 (.inr j) p v) (decide (v = workCellVal₀ p))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hj, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j, rfl⟩ := (seven_le_tapeCode_iff d).mp (by omega)
    refine ⟨_, ⟨j, p, v, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_workCellVal₀, ← hvv, ← hpp]
  · rintro ⟨_, ⟨j, p, v, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], by rw [hdd, tapeCode_inr]; omega, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_workCellVal₀, ← hvv, ← hpp]

/-- The start family. -/
def StartPred (c : Cand) : Prop :=
  StartHead e c ∨ StartState e c ∨ StartFixed e fixed c ∨ StartWork e c

theorem startPred_iff (c : Cand) :
    StartPred e fixed c ↔ ∃ cl ∈ startClauses (S := Sof e) (G := G) U fixed, c.Dec e G cl := by
  unfold startClauses StartPred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, ← startHead_iff, ← startState_iff,
    ← startFixed_iff, ← startWork_iff]
  tauto

/-! ## The free family -/

/-- The tape `F.d` is free. -/
def FreeTape (F : Fields) : Prop := ∃ j : Fin 7, fixed j = none ∧ F.d = j

/-- `p` is a boundary cell. -/
def Bdry (S p : ℕ) : Prop := p < 2 ∨ 2 * S + 5 ≤ p

instance (S p : ℕ) : Decidable (Bdry S p) := by unfold Bdry; infer_instance

/-- `unit (cell 0 (inl j) p v) (decide (v = bdry))` for `p` a boundary cell. -/
def FreeBdry (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ Bdry (Sof e) c.F₁.p ∧
    c.s₁ = decide (c.F₁.v = 6)

theorem freeBdry_iff (c : Cand) :
    FreeBdry e fixed c ↔ ∃ cl ∈ ({cl | ∃ j p v, fixed j = none ∧ p.IsBdry ∧
      cl = unit (.cell 0 (.inl j) p v) (decide (v = .bdry))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, ⟨j, hj, hjd⟩, hb, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    refine ⟨_, ⟨j', p, v, hj, (isBdry_iff p).mpr (by rw [← hpp]; exact hb), rfl⟩,
      (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
  · rintro ⟨_, ⟨j, p, v, hj, hb, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ⟨j, hj, by rw [hdd, tapeCode_inl]⟩,
      by rw [hpp]; exact (isBdry_iff p).mp hb, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl

/-- `unit (cell 0 (inl j) p v) false` for `p` interior and `v` none of `0`, `1`, blank. -/
def FreeOther (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ ¬ Bdry (Sof e) c.F₁.p ∧
    c.F₁.v ≠ 0 ∧ c.F₁.v ≠ 1 ∧ c.F₁.v ≠ 5 ∧ c.s₁ = false

theorem freeOther_iff (c : Cand) :
    FreeOther e fixed c ↔ ∃ cl ∈ ({cl | ∃ j p v, fixed j = none ∧ ¬ p.IsBdry ∧ v ≠ .sym .zero ∧
      v ≠ .sym .one ∧ v ≠ .blank ∧ cl = unit (.cell 0 (.inl j) p v) false} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, ⟨j, hj, hjd⟩, hb, h0, h1, h5, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    refine ⟨_, ⟨j', p, v, hj, fun h => hb (by rw [hpp]; exact (isBdry_iff p).mp h), ?_, ?_, ?_, rfl⟩,
      (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, hs, hss⟩⟩
    · rintro rfl; exact h0 hvv
    · rintro rfl; exact h1 hvv
    · rintro rfl; exact h5 hvv
  · rintro ⟨_, ⟨j, p, v, hj, hb, h0, h1, h5, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ⟨j, hj, by rw [hdd, tapeCode_inl]⟩,
      fun h => hb ((isBdry_iff p).mpr (by rw [← hpp]; exact h)), ?_, ?_, ?_, hs⟩
    · rw [hvv]; intro h; exact h0 (symCode_inj.mp h)
    · rw [hvv]; intro h; exact h1 (symCode_inj.mp h)
    · rw [hvv]; intro h; exact h5 (symCode_inj.mp h)

/-- `unit (cell 0 (inl j) 2 v) (decide (v = blank))`. -/
def FreeTwo (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ c.F₁.p = 2 ∧
    c.s₁ = decide (c.F₁.v = 5)

theorem freeTwo_iff (c : Cand) :
    FreeTwo e fixed c ↔ ∃ cl ∈ ({cl | ∃ j v, fixed j = none ∧
      cl = unit (.cell 0 (.inl j) ⟨2, by unfold numCells; omega⟩ v) (decide (v = .blank))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, ⟨j, hj, hjd⟩, hp, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    have hp2 : p = ⟨2, by unfold numCells; omega⟩ := Fin.ext (by simp; omega)
    rw [hp2] at hd
    refine ⟨_, ⟨j', v, hj, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
  · rintro ⟨_, ⟨j, v, hj, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ _ v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ⟨j, hj, by rw [hdd, tapeCode_inl]⟩, hpp, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl

/-- The records `F` and `F'` denote cells of the same tape and position. -/
def samePos (F F' : Fields) : Prop := F.t = F'.t ∧ F.d = F'.d ∧ F.p = F'.p

/-- `cell 0 (inl j) p 0 ∨ cell 0 (inl j) p 1 ∨ cell 0 (inl j) p blank` for `p` interior. -/
def FreeOneOf (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ samePos c.F₁ c.F₂ ∧ samePos c.F₁ c.F₃ ∧
    c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ ¬ Bdry (Sof e) c.F₁.p ∧
    c.F₁.v = 0 ∧ c.F₂.v = 1 ∧ c.F₃.v = 5 ∧ c.s₁ = true ∧ c.s₂ = true ∧ c.s₃ = true

theorem freeOneOf_iff (c : Cand) :
    FreeOneOf e fixed c ↔ ∃ c' ∈ ({c' | ∃ (j : Fin 7) (p : Pos (Sof e)), fixed j = none ∧ ¬ p.IsBdry ∧
      c' = cl ⟨.cell 0 (.inl j) p (.sym .zero), true⟩ ⟨.cell 0 (.inl j) p (.sym .one), true⟩
        ⟨.cell 0 (.inl j) p .blank, true⟩} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, ⟨t₂, d₂, p₂⟩, ⟨t₃, d₃, p₃⟩, ht, ⟨j, hj, hjd⟩, hb, v₁, v₂, v₃, s₁, s₂, s₃⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h₁
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    have hv : v = .sym .zero := symCode_inj.mp (by rw [← hvv, v₁]; rfl)
    subst hv
    refine ⟨_, ⟨j', p, hj, fun h => hb (by rw [hpp]; exact (isBdry_iff p).mp h), rfl⟩,
      (Cand.dec_cl e G c _ _ _).mpr ⟨hd, s₁, ?_, s₂, ?_, s₃⟩⟩
    · exact (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₂, by rw [← t₂, htt], by rw [← d₂, hdd],
        by rw [← p₂, hpp], v₂⟩
    · exact (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₃, by rw [← t₃, htt], by rw [← d₃, hdd],
        by rw [← p₃, hpp], v₃⟩
  · rintro ⟨_, ⟨j, p, hj, hb, rfl⟩, hdec⟩
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := (Cand.dec_cl e G c _ _ _).mp hdec
    obtain ⟨h₁, t₁, d₁, p₁, v₁⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₁
    obtain ⟨h₂, t₂, d₂, p₂, v₂⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₂
    obtain ⟨h₃, t₃, d₃, p₃, v₃⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₃
    refine ⟨h₁, h₂, h₃, ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩,
      by rw [t₁, Fin.val_zero], ⟨j, hj, by rw [d₁, tapeCode_inl]⟩,
      fun h => hb ((isBdry_iff p).mpr (by rw [← p₁]; exact h)), v₁, v₂, v₃, s₁, s₂, s₃⟩

/-- `nand2 (cell 0 (inl j) p v) (cell 0 (inl j) p v')` for `p` interior and `v ≠ v'`. -/
def FreeNand (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ samePos c.F₁ c.F₂ ∧ cellEq c.F₂ c.F₃ ∧
    c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ ¬ Bdry (Sof e) c.F₁.p ∧ c.F₁.v ≠ c.F₂.v ∧
    c.s₁ = false ∧ c.s₂ = false ∧ c.s₃ = false

theorem freeNand_iff (c : Cand) :
    FreeNand e fixed c ↔ ∃ cl ∈ ({cl | ∃ j p v v', fixed j = none ∧ ¬ p.IsBdry ∧ v ≠ v' ∧
      cl = nand2 (.cell 0 (.inl j) p v) (.cell 0 (.inl j) p v')} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨h₁, h₂, h₃, ⟨t₂, d₂, p₂⟩, e₂₃, ht, ⟨j, hj, hjd⟩, hb, hne, s₁, s₂, s₃⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h₁
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    obtain ⟨v', hv'⟩ := symOfCode_of_lt (show c.F₂.v < 7 by
      rcases h₂ with ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, h⟩ <;> exact h)
    have hvv' := symOfCode_eq_some hv'
    have hd₂ : decodeVar e G c.F₂ = some (.cell 0 (.inl j') p v') :=
      (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₂, by rw [← t₂, htt], by rw [← d₂, hdd],
        by rw [← p₂, hpp], hvv'.symm⟩
    refine ⟨_, ⟨j', p, v, v', hj, fun h => hb (by rw [hpp]; exact (isBdry_iff p).mp h),
      fun h => hne (by rw [hvv, ← hvv', h]), rfl⟩, ?_⟩
    simp only [nand2, Cand.dec_cl]
    exact ⟨hd, s₁, hd₂, s₂, by rw [← decodeVar_cell_congr e G h₂ h₃ e₂₃]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨j, p, v, v', hj, hb, hne, rfl⟩, hdec⟩
    simp only [nand2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁, d₁, p₁, v₁⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₁
    obtain ⟨h₂, t₂, d₂, p₂, v₂⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₂
    refine ⟨h₁, h₂, ((decodeVar_cell_iff e G _ _ _ _ _).mp hd₃).1, ⟨by omega, by omega, by omega⟩,
      cellEq_of_decode e G hd₂ hd₃, by rw [t₁, Fin.val_zero], ⟨j, hj, by rw [d₁, tapeCode_inl]⟩,
      fun h => hb ((isBdry_iff p).mpr (by rw [← p₁]; exact h)), ?_, s₁, s₂, s₃⟩
    rw [v₁, v₂]
    exact fun h => hne (symCode_inj.mp h)

/-- `imp2 (cell 0 (inl j) p blank) (cell 0 (inl j) p' blank)` for `2 < p < p'`, `p'` interior. -/
def FreeBlank (c : Cand) : Prop :=
  IsCell e c.F₁ ∧ IsCell e c.F₂ ∧ IsCell e c.F₃ ∧ cellEq c.F₂ c.F₃ ∧
    c.F₁.t = 0 ∧ FreeTape fixed c.F₁ ∧ c.F₂.t = c.F₁.t ∧ c.F₂.d = c.F₁.d ∧
    2 < c.F₁.p ∧ ¬ Bdry (Sof e) c.F₂.p ∧ c.F₁.p < c.F₂.p ∧ c.F₁.v = 5 ∧ c.F₂.v = 5 ∧
    c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

theorem freeBlank_iff (c : Cand) :
    FreeBlank e fixed c ↔ ∃ cl ∈ ({cl | ∃ (j : Fin 7) (p p' : Pos (Sof e)), fixed j = none ∧ 2 < (p : ℕ) ∧
      ¬ p'.IsBdry ∧ p < p' ∧ cl = imp2 (.cell 0 (.inl j) p .blank) (.cell 0 (.inl j) p' .blank)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨h₁, h₂, h₃, e₂₃, ht, ⟨j, hj, hjd⟩, t₂, d₂, hp2, hb, hlt, v₁, v₂, s₁, s₂, s₃⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h₁
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    have hv : v = .blank := symCode_inj.mp (by rw [← hvv, v₁]; rfl)
    subst hv
    have hp' : c.F₂.p < numCells (Sof e) := by
      rcases h₂ with ⟨-, -, -, -, h, -⟩ | ⟨-, -, -, -, -, h, -⟩ <;> exact h
    have hd₂ : decodeVar e G c.F₂ = some (.cell 0 (.inl j') ⟨c.F₂.p, hp'⟩ .blank) :=
      (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₂, by rw [t₂, htt], by rw [d₂, hdd], rfl, v₂⟩
    refine ⟨_, ⟨j', p, ⟨c.F₂.p, hp'⟩, hj, by omega, fun h => hb ((isBdry_iff _).mp h),
      by rw [Fin.lt_iff_val_lt_val, ← hpp]; exact hlt, rfl⟩, ?_⟩
    simp only [imp2, Cand.dec_cl]
    exact ⟨hd, s₁, hd₂, s₂, by rw [← decodeVar_cell_congr e G h₂ h₃ e₂₃]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨j, p, p', hj, hp2, hb, hlt, rfl⟩, hdec⟩
    simp only [imp2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁, d₁, p₁, v₁⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₁
    obtain ⟨h₂, t₂, d₂, p₂, v₂⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₂
    refine ⟨h₁, h₂, ((decodeVar_cell_iff e G _ _ _ _ _).mp hd₃).1, cellEq_of_decode e G hd₂ hd₃,
      by rw [t₁, Fin.val_zero], ⟨j, hj, by rw [d₁, tapeCode_inl]⟩, by rw [t₁, t₂], by rw [d₁, d₂],
      by omega, fun h => hb ((isBdry_iff p').mpr (by rw [← p₂]; exact h)),
      by rw [p₁, p₂]; exact hlt, v₁, v₂, s₁, s₂, s₃⟩

/-- The free family. -/
def FreePred (c : Cand) : Prop :=
  FreeBdry e fixed c ∨ FreeOther e fixed c ∨ FreeTwo e fixed c ∨ FreeOneOf e fixed c ∨
    FreeNand e fixed c ∨ FreeBlank e fixed c

theorem freePred_iff (c : Cand) :
    FreePred e fixed c ↔ ∃ cl ∈ freeClauses (S := Sof e) (G := G) Sym.zero Sym.one fixed, c.Dec e G cl := by
  unfold freeClauses FreePred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union,
    ← freeBdry_iff, ← freeOther_iff, ← freeTwo_iff, ← freeOneOf_iff, ← freeNand_iff, ← freeBlank_iff]
  tauto


/-! ## The boundary family -/

/-- `unit (cell t d p v) (decide (v = bdry))` for `p` a boundary cell. -/
def BdryCell (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ Bdry (Sof e) c.F₁.p ∧ c.s₁ = decide (c.F₁.v = 6)

theorem bdryCell_iff (c : Cand) :
    BdryCell e c ↔ ∃ cl ∈ ({cl | ∃ t d p v, p.IsBdry ∧ cl = unit (.cell t d p v) (decide (v = .bdry))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, hb, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    refine ⟨_, ⟨t, d, p, v, (isBdry_iff p).mpr (by rw [← hpp]; exact hb), rfl⟩,
      (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
  · rintro ⟨_, ⟨t, d, p, v, hb, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [hpp]; exact (isBdry_iff p).mp hb, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl

/-- `unit (head t d p) false` for `p` a boundary cell. -/
def BdryHead (c : Cand) : Prop :=
  UnitHead e c ∧ SameSigns c ∧ Bdry (Sof e) c.F₁.p ∧ c.s₁ = false

theorem bdryHead_iff (c : Cand) :
    BdryHead e c ↔ ∃ cl ∈ ({cl | ∃ t d p, p.IsBdry ∧ cl = unit (.head t d p) false} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, hb, hs⟩
    obtain ⟨t, d, p, hd⟩ := exists_head e G hu.1
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ t d p).mp hd
    exact ⟨_, ⟨t, d, p, (isBdry_iff p).mpr (by rw [← hpp]; exact hb), rfl⟩,
      (dec_unit_head e G c _ _ _ _).mpr ⟨hd, hu, hs, hss⟩⟩
  · rintro ⟨_, ⟨t, d, p, hb, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_head e G c _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ _ _ p).mp hd
    exact ⟨hu, hss, by rw [hpp]; exact (isBdry_iff p).mp hb, hs⟩

/-- The boundary family. -/
def BdryPred (c : Cand) : Prop := BdryCell e c ∨ BdryHead e c

theorem bdryPred_iff (c : Cand) :
    BdryPred e c ↔ ∃ cl ∈ bdryClauses (i := 7) (w := 6) (Symbol := Sym) (State := Ctl) (S := Sof e) (G := G),
      c.Dec e G cl := by
  unfold bdryClauses BdryPred
  rw [exists_mem_union, ← bdryCell_iff, ← bdryHead_iff]

/-! ## The emission family -/

/-- `unit (emitted 0) false`. -/
def EmitZero (c : Cand) : Prop := UnitEmitted e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ c.s₁ = false

theorem emitZero_iff (c : Cand) :
    EmitZero e c ↔ ∃ cl ∈ ({unit (.emitted 0) false} : Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)),
      c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hs⟩
    obtain ⟨t, hd⟩ := exists_emitted e G hu.1
    obtain ⟨-, htt⟩ := (decodeVar_emitted_iff e G _ t).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    exact ⟨_, rfl, (dec_unit_emitted e G c _ _).mpr ⟨hd, hu, hs, hss⟩⟩
  · rintro ⟨_, rfl, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_emitted e G c _ _).mp hdec
    obtain ⟨-, htt⟩ := (decodeVar_emitted_iff e G _ _).mp hd
    exact ⟨hu, hss, by rw [htt, Fin.val_zero], hs⟩

/-- `¬ emitted (t + 1) ∨ emitted t ∨ emitOne t`. -/
def EmitStep (c : Cand) : Prop :=
  IsEmitted e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitOne e c.F₃ ∧ c.F₁.t = c.F₃.t + 1 ∧ c.F₂.t = c.F₃.t ∧
    c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

theorem emitStep_iff (c : Cand) :
    EmitStep e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e),
      c' = cl ⟨.emitted t.succ, false⟩ ⟨.emitted t.castSucc, true⟩ ⟨.emitOne t, true⟩} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, t₁, t₂, s₁, s₂, s₃⟩
    obtain ⟨t, hd₃⟩ := exists_emitOne e G h₃
    obtain ⟨-, htt⟩ := (decodeVar_emitOne_iff e G _ t).mp hd₃
    refine ⟨_, ⟨t, rfl⟩, (Cand.dec_cl e G c _ _ _).mpr ⟨?_, s₁, ?_, s₂, hd₃, s₃⟩⟩
    · exact (decodeVar_emitted_iff e G _ _).mpr ⟨h₁, by rw [Fin.val_succ, ← htt, t₁]⟩
    · exact (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.coe_castSucc, ← htt, t₂]⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := (Cand.dec_cl e G c _ _ _).mp hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitted_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitOne_iff e G _ _).mp hd₃
    rw [Fin.val_succ] at t₁
    rw [Fin.coe_castSucc] at t₂
    exact ⟨h₁, h₂, h₃, by omega, by omega, s₁, s₂, s₃⟩

/-- `imp2 (emitted t) (emitted (t + 1))`. -/
def EmitMono (c : Cand) : Prop :=
  IsEmitted e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₁.t < Sof e ∧ c.F₂.t = c.F₁.t + 1 ∧
    c.F₃.t = c.F₂.t ∧ c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

theorem emitMono_iff (c : Cand) :
    EmitMono e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e), c' = imp2 (.emitted t.castSucc) (.emitted t.succ)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, hlt, t₂, t₃, s₁, s₂, s₃⟩
    have hd₂ : decodeVar e G c.F₂ = some (.emitted (⟨c.F₁.t, hlt⟩ : Fin (Sof e)).succ) :=
      (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.val_succ, t₂]⟩
    refine ⟨_, ⟨⟨c.F₁.t, hlt⟩, rfl⟩, ?_⟩
    simp only [imp2, Cand.dec_cl]
    refine ⟨(decodeVar_emitted_iff e G _ _).mpr ⟨h₁, by rw [Fin.coe_castSucc]⟩, s₁, hd₂, s₂,
      by rw [← decodeVar_emitted_congr e G h₂ h₃ t₃.symm]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    simp only [imp2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitted_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitted_iff e G _ _).mp hd₃
    rw [Fin.coe_castSucc] at t₁
    rw [Fin.val_succ] at t₂ t₃
    exact ⟨h₁, h₂, h₃, by rw [t₁]; exact t.isLt, by omega, by omega, s₁, s₂, s₃⟩

/-- `imp2 (emitOne t) (emitted (t + 1))`. -/
def EmitOne (c : Cand) : Prop :=
  IsEmitOne e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₂.t = c.F₁.t + 1 ∧ c.F₃.t = c.F₂.t ∧
    c.s₁ = false ∧ c.s₂ = true ∧ c.s₃ = true

theorem emitOne_iff (c : Cand) :
    EmitOne e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e), c' = imp2 (.emitOne t) (.emitted t.succ)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, t₂, t₃, s₁, s₂, s₃⟩
    obtain ⟨t, hd₁⟩ := exists_emitOne e G h₁
    obtain ⟨-, htt⟩ := (decodeVar_emitOne_iff e G _ t).mp hd₁
    have hd₂ : decodeVar e G c.F₂ = some (.emitted t.succ) :=
      (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.val_succ, ← htt, t₂]⟩
    refine ⟨_, ⟨t, rfl⟩, ?_⟩
    simp only [imp2, Cand.dec_cl]
    exact ⟨hd₁, s₁, hd₂, s₂, by rw [← decodeVar_emitted_congr e G h₂ h₃ t₃.symm]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    simp only [imp2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitOne_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitted_iff e G _ _).mp hd₃
    rw [Fin.val_succ] at t₂ t₃
    exact ⟨h₁, h₂, h₃, by omega, by omega, s₁, s₂, s₃⟩

/-- `nand2 (emitOne t) (emitted t)`. -/
def EmitOnce (c : Cand) : Prop :=
  IsEmitOne e c.F₁ ∧ IsEmitted e c.F₂ ∧ IsEmitted e c.F₃ ∧ c.F₂.t = c.F₁.t ∧ c.F₃.t = c.F₂.t ∧
    c.s₁ = false ∧ c.s₂ = false ∧ c.s₃ = false

theorem emitOnce_iff (c : Cand) :
    EmitOnce e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e), c' = nand2 (.emitOne t) (.emitted t.castSucc)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, t₂, t₃, s₁, s₂, s₃⟩
    obtain ⟨t, hd₁⟩ := exists_emitOne e G h₁
    obtain ⟨-, htt⟩ := (decodeVar_emitOne_iff e G _ t).mp hd₁
    have hd₂ : decodeVar e G c.F₂ = some (.emitted t.castSucc) :=
      (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.coe_castSucc, ← htt, t₂]⟩
    refine ⟨_, ⟨t, rfl⟩, ?_⟩
    simp only [nand2, Cand.dec_cl]
    exact ⟨hd₁, s₁, hd₂, s₂, by rw [← decodeVar_emitted_congr e G h₂ h₃ t₃.symm]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    simp only [nand2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitOne_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitted_iff e G _ _).mp hd₃
    rw [Fin.coe_castSucc] at t₂ t₃
    exact ⟨h₁, h₂, h₃, by omega, by omega, s₁, s₂, s₃⟩

/-- `unit (emitBad t) false`. -/
def EmitBad (c : Cand) : Prop := UnitEmitBad e c ∧ SameSigns c ∧ c.s₁ = false

theorem emitBad_iff (c : Cand) :
    EmitBad e c ↔ ∃ cl ∈ ({cl | ∃ t : Fin (Sof e), cl = unit (.emitBad t) false} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, hs⟩
    obtain ⟨t, hd⟩ := exists_emitBad e G hu.1
    exact ⟨_, ⟨t, rfl⟩, (dec_unit_emitBad e G c _ _).mpr ⟨hd, hu, hs, hss⟩⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_emitBad e G c _ _).mp hdec
    exact ⟨hu, hss, hs⟩

/-- The emission family. -/
def EmitPred (c : Cand) : Prop :=
  EmitZero e c ∨ EmitStep e c ∨ EmitMono e c ∨ EmitOne e c ∨ EmitOnce e c ∨ EmitBad e c

theorem emitPred_iff (c : Cand) :
    EmitPred e c ↔ ∃ cl ∈ emitClauses (i := 7) (w := 6) (Symbol := Sym) (State := Ctl) (S := Sof e) (G := G),
      c.Dec e G cl := by
  unfold emitClauses EmitPred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union,
    ← emitZero_iff, ← emitStep_iff, ← emitMono_iff, ← emitOne_iff, ← emitOnce_iff, ← emitBad_iff]
  tauto

/-! ## The final family -/

/-- `unit (state S none) true`. -/
def FinalState (c : Cand) : Prop :=
  UnitState e c ∧ SameSigns c ∧ c.F₁.t = Sof e ∧ c.F₁.q = qCode none ∧ c.s₁ = true

/-- `unit (emitted S) true`. -/
def FinalEmitted (c : Cand) : Prop :=
  UnitEmitted e c ∧ SameSigns c ∧ c.F₁.t = Sof e ∧ c.s₁ = true

/-- The final family. -/
def FinalPred (c : Cand) : Prop := FinalState e c ∨ FinalEmitted e c

theorem finalPred_iff (c : Cand) :
    FinalPred e c ↔ ∃ cl ∈ finalClauses (i := 7) (w := 6) (Symbol := Sym) (State := Ctl) (S := Sof e) (G := G),
      c.Dec e G cl := by
  unfold finalClauses FinalPred FinalState FinalEmitted
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right, exists_or, exists_eq_left,
    dec_unit_state, dec_unit_emitted]
  constructor
  · rintro (⟨hu, hss, ht, hq, hs⟩ | ⟨hu, hss, ht, hs⟩)
    · exact Or.inl ⟨(decodeVar_state_iff e G _ _ _).mpr ⟨hu.1, by rw [Fin.val_last]; exact ht, hq⟩,
        hu, hs, hss⟩
    · exact Or.inr ⟨(decodeVar_emitted_iff e G _ _).mpr ⟨hu.1, by rw [Fin.val_last]; exact ht⟩,
        hu, hs, hss⟩
  · rintro (⟨hd, hu, hs, hss⟩ | ⟨hd, hu, hs, hss⟩)
    · obtain ⟨-, ht, hq⟩ := (decodeVar_state_iff e G _ _ _).mp hd
      exact Or.inl ⟨hu, hss, by rw [ht, Fin.val_last], hq, hs⟩
    · obtain ⟨-, ht⟩ := (decodeVar_emitted_iff e G _ _).mp hd
      exact Or.inr ⟨hu, hss, by rw [ht, Fin.val_last], hs⟩

/-! ## The non-window families together -/

/-- The five explicit families. -/
def MainPred (c : Cand) : Prop :=
  StartPred e fixed c ∨ FreePred e fixed c ∨ BdryPred e c ∨ EmitPred e c ∨ FinalPred e c

/-- The candidate decodes to a clause of the five explicit families iff `MainPred`. -/
theorem mainPred_iff (c : Cand) :
    MainPred e fixed c ↔ ∃ cl ∈ startClauses (S := Sof e) (G := G) U fixed ∪
      freeClauses (S := Sof e) (G := G) Sym.zero Sym.one fixed ∪ bdryClauses (S := Sof e) (G := G) ∪
      emitClauses (S := Sof e) (G := G) ∪ finalClauses (S := Sof e) (G := G), c.Dec e G cl := by
  unfold MainPred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union, ← startPred_iff,
    ← freePred_iff, ← bdryPred_iff, ← emitPred_iff, ← finalPred_iff]
  tauto

end MIPRE.TM.CookLevin.Desc
