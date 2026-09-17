/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Families

/-!
# The window family, on decoded fields

The window clauses of the tableau are the Tseitin clauses of the check circuit `chk` at
every step `t` and window `js` (`windowClauses`). Every such clause has a gate literal
(`aux t js g`) in its third position: the *templates* of a gate (`gateTemplates`) list its
clauses as triples of literal *specs* — a gate index (`.aux u`) or a window input (`.win n`)
— with their signs, and the clause is recovered from the templates by instantiating the
specs at `(t, js)` (`gateClauses_eq_templates`). A candidate matches a template when its
third record is a gate variable of the template's gate and the other two records denote the
spec's variable relative to it (`SpecMatch`: the time and centers are read off the third
record). `windowPred_iff`: the candidate decodes to a window clause iff it matches a
template of a gate, or is the output unit clause (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## Templates -/

/-- A literal of a Tseitin clause, before instantiation: a gate variable or a window input. -/
inductive LitSpec where
  | aux (u : ℕ)
  | win (n : ℕ)
  deriving DecidableEq

/-- A clause template: three specs with their signs. -/
abbrev Tpl := (LitSpec × Bool) × (LitSpec × Bool) × (LitSpec × Bool)

/-- The Tseitin clauses of gate `g`, as templates (`gateClauses`, `Tseitin.lean`). -/
def gateTemplates (g : ℕ) : Gate → List Tpl
  | .input i => [((.win i, false), (.aux g, true), (.aux g, true)),
      ((.win i, true), (.aux g, false), (.aux g, false))]
  | .const b => [((.aux g, b), (.aux g, b), (.aux g, b))]
  | .and u v => [((.aux u, false), (.aux v, false), (.aux g, true)),
      ((.aux u, true), (.aux v, true), (.aux g, false)),
      ((.aux u, true), (.aux v, false), (.aux g, false)),
      ((.aux u, false), (.aux v, true), (.aux g, false))]
  | .or u v => [((.aux u, true), (.aux v, true), (.aux g, false)),
      ((.aux u, false), (.aux v, false), (.aux g, true)),
      ((.aux u, false), (.aux v, true), (.aux g, true)),
      ((.aux u, true), (.aux v, false), (.aux g, true))]
  | .not u => [((.aux u, true), (.aux g, true), (.aux g, true)),
      ((.aux u, false), (.aux g, false), (.aux g, false))]

section Instantiate

variable {S G : ℕ}

/-- The tableau variable of a spec at step `t` and window `js`. -/
noncomputable def specVar (t : Fin S) (js : Tape 7 6 → Center S) : LitSpec → TabVar 7 6 Sym Ctl S G
  | .aux u => auxOf t js u
  | .win n => inpOf t js n

/-- The clause of a template at step `t` and window `js`. -/
noncomputable def Tpl.clause (t : Fin S) (js : Tape 7 6 → Center S) (tp : Tpl) :
    Clause3 (TabVar 7 6 Sym Ctl S G) :=
  cl ⟨specVar t js tp.1.1, tp.1.2⟩ ⟨specVar t js tp.2.1.1, tp.2.1.2⟩ ⟨specVar t js tp.2.2.1, tp.2.2.2⟩

theorem gateClauses_eq_templates (t : Fin S) (js : Tape 7 6 → Center S) (g : ℕ) (gate : Gate) :
    gateClauses (inpOf t js) (auxOf t js) (auxOf (G := G) t js g) gate =
      (gateTemplates g gate).map (Tpl.clause t js) := by
  cases gate <;> rfl

/-- The third spec of every template of gate `g` is the gate itself. -/
theorem third_of_templates (g : ℕ) (gate : Gate) (tp : Tpl) (h : tp ∈ gateTemplates g gate) :
    tp.2.2.1 = .aux g := by
  cases gate <;> simp only [gateTemplates, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- A spec of a template of gate `g` is the gate, a gate it reads, or the input it reads. -/
theorem spec_of_templates (g : ℕ) (gate : Gate) (tp : Tpl) (h : tp ∈ gateTemplates g gate)
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) :
    (∃ u, sp = .aux u ∧ (u = g ∨ u ∈ gate.refs)) ∨ (∃ i, sp = .win i ∧ gate = .input i) := by
  cases gate <;> simp only [gateTemplates, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl <;> rcases hsp with rfl | rfl | rfl <;> simp [Gate.refs]

end Instantiate

/-! ## Matching a spec against the gate literal -/

variable (e G : ℕ)

/-- The record `F` denotes the window variable `wv` of the window of the record `Fa` (a gate
variable: its time and centers are `Fa.t`, `Fa.js`). -/
def WinMatch (Fa : Fields) : WinVar 7 6 Sym Ctl → Fields → Prop
  | .cellPre d δ v, F => IsCell e F ∧ F.t = Fa.t ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + δ ∧ F.v = symCode v
  | .headPre d δ, F => IsHead e F ∧ F.t = Fa.t ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + δ
  | .cellPost d v, F => IsCell e F ∧ F.t = Fa.t + 1 ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + 2 ∧ F.v = symCode v
  | .headPost d, F => IsHead e F ∧ F.t = Fa.t + 1 ∧ F.d = tapeCode d ∧
      F.p = Fa.js ⟨tapeCode d, tapeCode_lt d⟩ + 2
  | .statePre q, F => IsState e F ∧ F.t = Fa.t ∧ F.q = qCode q
  | .statePost q, F => IsState e F ∧ F.t = Fa.t + 1 ∧ F.q = qCode q
  | .emitOne, F => IsEmitOne e F ∧ F.t = Fa.t
  | .emitBad, F => IsEmitBad e F ∧ F.t = Fa.t

/-- The record `F` denotes the variable of the spec, relative to the gate record `Fa`. -/
def SpecMatch (Fa : Fields) : LitSpec → Fields → Prop
  | .aux u, F => IsAux e G F ∧ F.t = Fa.t ∧ (∀ k, F.js k = Fa.js k) ∧ F.g = u
  | .win n, F => ∃ h : n < winCard 7 6 Sym Ctl, WinMatch e Fa ((Fintype.equivFin _).symm ⟨n, h⟩) F

section Match

variable {Fa : Fields} {t : Fin (Sof e)} {js : Tape 7 6 → Center (Sof e)}
  (ht : Fa.t = t) (hjs : ∀ d, Fa.js ⟨tapeCode d, tapeCode_lt d⟩ = js d)
include ht hjs

theorem winMatch_iff (wv : WinVar 7 6 Sym Ctl) (F : Fields) :
    WinMatch e Fa wv F ↔ decodeVar e G F = some (winVarOf (G := G) t js wv) := by
  cases wv with
  | cellPre d δ v =>
    rw [WinMatch, winVarOf, decodeVar_cell_iff, Fin.coe_castSucc, ht, hjs]
    rfl
  | headPre d δ =>
    rw [WinMatch, winVarOf, decodeVar_head_iff, Fin.coe_castSucc, ht, hjs]
    rfl
  | cellPost d v =>
    rw [WinMatch, winVarOf, decodeVar_cell_iff, Fin.val_succ, ht, hjs]
    rfl
  | headPost d =>
    rw [WinMatch, winVarOf, decodeVar_head_iff, Fin.val_succ, ht, hjs]
    rfl
  | statePre q =>
    rw [WinMatch, winVarOf, decodeVar_state_iff, Fin.coe_castSucc, ht]
  | statePost q =>
    rw [WinMatch, winVarOf, decodeVar_state_iff, Fin.val_succ, ht]
  | emitOne =>
    rw [WinMatch, winVarOf, decodeVar_emitOne_iff, ht]
  | emitBad =>
    rw [WinMatch, winVarOf, decodeVar_emitBad_iff, ht]

theorem specMatch_aux_iff (u : ℕ) (hu : u < G) (F : Fields) :
    SpecMatch e G Fa (.aux u) F ↔ decodeVar e G F = some (specVar t js (.aux u)) := by
  simp only [SpecMatch, specVar, auxOf, dif_pos hu, decodeVar_aux_iff]
  constructor
  · rintro ⟨h, h1, h2, h3⟩
    refine ⟨h, by rw [h1, ht], fun d => ?_, h3⟩
    rw [h2, hjs]
  · rintro ⟨h, h1, h2, h3⟩
    refine ⟨h, by rw [h1, ht], fun k => ?_, h3⟩
    obtain ⟨d, hd⟩ := tapeOfCode_of_lt k.isLt
    have hk : k = ⟨tapeCode d, tapeCode_lt d⟩ := by ext; simp [tapeOfCode_eq_some hd]
    rw [hk, h2 d, hjs]

theorem specMatch_win_iff (n : ℕ) (hn : n < winCard 7 6 Sym Ctl) (F : Fields) :
    SpecMatch e G Fa (.win n) F ↔ decodeVar e G F = some (specVar t js (.win n)) := by
  simp only [SpecMatch, specVar, inpOf, dif_pos hn, exists_prop_of_true hn]
  exact winMatch_iff e G ht hjs _ F

end Match

/-! ## The window predicate -/

/-- The candidate matches the template, its third record being the gate literal. -/
def TplMatch (tp : Tpl) (c : Cand) : Prop :=
  SpecMatch e G c.F₃ tp.1.1 c.F₁ ∧ c.s₁ = tp.1.2 ∧ SpecMatch e G c.F₃ tp.2.1.1 c.F₂ ∧ c.s₂ = tp.2.1.2 ∧
    SpecMatch e G c.F₃ tp.2.2.1 c.F₃ ∧ c.s₃ = tp.2.2.2

/-- The candidate matches a template of some gate of `chk`. -/
def WindowGates (chk : Circuit) (c : Cand) : Prop :=
  ∃ g : Fin chk.gates.length, ∃ tp ∈ gateTemplates g chk.gates[g], TplMatch e G tp c

/-- The candidate is the output unit clause of a window. -/
def WindowOut (c : Cand) : Prop := UnitAux e G c ∧ SameSigns c ∧ c.F₁.g = G - 1 ∧ c.s₁ = true

/-- The window family. -/
def WindowPred (chk : Circuit) (c : Cand) : Prop := WindowGates e G chk c ∨ WindowOut e G c

section Iff

variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
  (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ [])

include hC hin hinp in
/-- The specs of a template of a gate of `chk` are in range. -/
theorem spec_lt (g : Fin chk.gates.length) (tp : Tpl) (h : tp ∈ gateTemplates g chk.gates[g])
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) :
    (∃ u, sp = .aux u ∧ u < chk.gates.length) ∨ (∃ i, sp = .win i ∧ i < winCard 7 6 Sym Ctl) := by
  rcases spec_of_templates g _ tp h sp hsp with ⟨u, rfl, rfl | hu⟩ | ⟨i, rfl, hi⟩
  · exact Or.inl ⟨_, rfl, g.isLt⟩
  · exact Or.inl ⟨u, rfl, lt_trans (hC g g.isLt u hu) g.isLt⟩
  · exact Or.inr ⟨i, rfl, hinp ▸ hin i (hi ▸ List.getElem_mem g.isLt)⟩

include hC hin hinp in
theorem specMatch_iff {Fa : Fields} {t : Fin (Sof e)} {js : Tape 7 6 → Center (Sof e)}
    (ht : Fa.t = t) (hjs : ∀ d, Fa.js ⟨tapeCode d, tapeCode_lt d⟩ = js d)
    (g : Fin chk.gates.length) (tp : Tpl) (h : tp ∈ gateTemplates g chk.gates[g])
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) (F : Fields) :
    SpecMatch e chk.gates.length Fa sp F ↔ decodeVar e chk.gates.length F = some (specVar t js sp) := by
  rcases spec_lt chk hC hin hinp g tp h sp hsp with ⟨u, rfl, hu⟩ | ⟨i, rfl, hi⟩
  · exact specMatch_aux_iff e _ ht hjs u hu F
  · exact specMatch_win_iff e _ ht hjs i hi F

include hC hin hinp hne in
/-- **The window family is exact**: a candidate satisfies `WindowPred` iff it decodes to a
window clause of the tableau. -/
theorem windowPred_iff (c : Cand) :
    WindowPred e chk.gates.length chk c ↔
      ∃ cl ∈ windowClauses (S := Sof e) chk, c.Dec e chk.gates.length cl := by
  have hlen : 0 < chk.gates.length := List.length_pos_iff.mpr hne
  constructor
  · rintro (⟨g, tp, htp, m₁, s₁, m₂, s₂, m₃, s₃⟩ | ⟨hu, hss, hg, hs⟩)
    · have h3 := third_of_templates g _ tp htp
      rw [h3] at m₃
      obtain ⟨ha, -, -, hg⟩ := m₃
      obtain ⟨t, js, g', hd₃⟩ := exists_aux e _ ha
      obtain ⟨-, ht, hjs, hg'⟩ := (decodeVar_aux_iff e _ _ t js g').mp hd₃
      have hgg : g' = g := Fin.ext (by omega)
      subst hgg
      refine ⟨tp.clause t js, ⟨t, js, Or.inl ⟨g', ?_⟩⟩, ?_⟩
      · rw [gateClauses_eq_templates]
        exact List.mem_map_of_mem htp
      · refine (Cand.dec_cl e _ c _ _ _).mpr ⟨?_, s₁, ?_, s₂, ?_, s₃⟩
        · exact (specMatch_iff e chk hC hin hinp ht hjs g' tp htp _ (Or.inl rfl) _).mp m₁
        · exact (specMatch_iff e chk hC hin hinp ht hjs g' tp htp _ (Or.inr (Or.inl rfl)) _).mp m₂
        · rw [h3, specVar, auxOf, dif_pos g'.isLt]
          exact hd₃
    · obtain ⟨t, js, g, hd₁⟩ := exists_aux e _ hu.1
      obtain ⟨-, -, -, hg'⟩ := (decodeVar_aux_iff e _ _ t js g).mp hd₁
      refine ⟨_, ⟨t, js, Or.inr rfl⟩, ?_⟩
      have hgg : g = ⟨chk.gates.length - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hgg] at hd₁
      show c.Dec e _ (unit (auxOf t js (chk.gates.length - 1)) true)
      rw [auxOf, dif_pos (by omega)]
      exact (dec_unit_aux e _ c _ _ _ _).mpr ⟨hd₁, hu, hs, hss⟩
  · rintro ⟨_, ⟨t, js, ⟨g, hg⟩ | rfl⟩, hdec⟩
    · rw [gateClauses_eq_templates, List.mem_map] at hg
      obtain ⟨tp, htp, rfl⟩ := hg
      obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := (Cand.dec_cl e _ c _ _ _).mp hdec
      have h3 := third_of_templates g _ tp htp
      rw [h3, specVar, auxOf, dif_pos g.isLt] at hd₃
      obtain ⟨ha, ht, hjs, hg⟩ := (decodeVar_aux_iff e _ _ t js _).mp hd₃
      refine Or.inl ⟨g, tp, htp, ?_, s₁, ?_, s₂, ?_, s₃⟩
      · exact (specMatch_iff e chk hC hin hinp ht hjs g tp htp _ (Or.inl rfl) _).mpr hd₁
      · exact (specMatch_iff e chk hC hin hinp ht hjs g tp htp _ (Or.inr (Or.inl rfl)) _).mpr hd₂
      · rw [h3]
        exact ⟨ha, rfl, fun _ => rfl, hg⟩
    · change c.Dec e _ (unit (auxOf t js (chk.gates.length - 1)) true) at hdec
      rw [auxOf, dif_pos (by omega)] at hdec
      obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_aux e _ c _ _ _ _).mp hdec
      obtain ⟨-, -, -, hg⟩ := (decodeVar_aux_iff e _ _ t js _).mp hd
      exact Or.inr ⟨hu, hss, hg, hs⟩

end Iff

/-! ## The whole tableau -/

/-- The candidate decodes to a clause of the tableau iff it satisfies one of the family
predicates. -/
theorem tableau_dec_iff (fixed : Fin 7 → Option (List Sym)) (chk : Circuit) (hC : chk.RefsLt)
    (hin : chk.InputsLt) (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ []) (c : Cand) :
    (MainPred e fixed c ∨ WindowPred e chk.gates.length chk c) ↔
      ∃ cl ∈ tableau U Sym.zero Sym.one (Sof e) fixed chk, c.Dec e chk.gates.length cl := by
  unfold tableau
  rw [exists_mem_union, ← mainPred_iff, ← windowPred_iff e chk hC hin hinp hne]

end MIPRE.TM.CookLevin.Desc
