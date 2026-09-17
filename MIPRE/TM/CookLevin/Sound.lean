/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Correct

/-!
# Soundness of the Cook–Levin tableau

A satisfying assignment of the tableau formula comes from an accepting run
(`acceptsIn_of_tableau_sat`), and the equivalence `tableau_sat_iff`
(`planning/succinct-cook-levin.md`, S1).

* The successor part of a locally consistent window is a function of its time-`t` part
  (`post_of_pre`): two locally consistent local configurations with the same cells, heads
  and state at time `t`, one of them with at most one head per tape, agree on the cell and
  head at time `t + 1` of every tape whose head is far, and on everything when every head is
  in the window.
* The free input strings are read off the time-`0` rows (`freeString`): the symbols from
  cell `3` up to the first blank, which the free-tape clauses make well defined
  (`FreeFacts.cell_eq`).
* The rows encode the run (`rows_of_sat`), by induction on time: the window centered at a
  cell, with the other windows centered at the heads, determines the cell and head at the
  next time; the window centered at every head determines the state and the emission bits.
-/

namespace MIPRE.TM.CookLevin

open Turing SAT MultiInputTM

/-! ## The successor part of a window is determined -/

section Post

variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
  (M : MultiInputTM i w Symbol State) (acc : Symbol)

omit [DecidableEq Symbol] [DecidableEq State] in
theorem LocalCfg.HeadAt.unique {L : LocalCfg i w Symbol State} {d : Tape i w} {δ δ' : Fin 5}
    (h : L.HeadAt d δ) (h' : L.HeadAt d δ') : δ = δ' := by
  have := (h' δ).symm.trans (h δ)
  simpa using this

omit [DecidableEq State] in
/-- Two windows satisfying the full-step check at the same offsets, with the same time-`t`
part, have the same time-`t + 1` part. -/
theorem fullStep_post_eq {L L' : LocalCfg i w Symbol State} (δ : Tape i w → Fin 5)
    (hL : FullStep M acc L δ) (hL' : FullStep M acc L' δ)
    (hc : L.cellPre = L'.cellPre) (hh : L.headPre = L'.headPre) (hs : L.statePre = L'.statePre) :
    L.cellPost = L'.cellPost ∧ L.headPost = L'.headPost ∧ L.statePost = L'.statePost ∧
      L.emitOne = L'.emitOne ∧ L.emitBad = L'.emitBad := by
  obtain ⟨cp, hp, cpo, hpo, sp, spo, e1, e2⟩ := L
  obtain ⟨cp', hp', cpo', hpo', sp', spo', e1', e2'⟩ := L'
  simp only at hc hh hs
  subst hc hh hs
  unfold FullStep at hL hL'
  cases sp with
  | none =>
    dsimp only at hL hL'
    obtain ⟨c1, h1, s1, o1, b1⟩ := hL
    obtain ⟨c1', h1', s1', o1', b1'⟩ := hL'
    dsimp only
    refine ⟨funext fun d => ?_, funext fun d => ?_, ?_, ?_, ?_⟩
    · rw [c1, c1']
    · rw [h1, h1']
    · rw [s1, s1']
    · rw [o1, o1']
    · rw [b1, b1']
  | some q =>
    dsimp only at hL hL'
    obtain ⟨-, c1, c2, h1, h2, s1, o1, b1⟩ := hL
    obtain ⟨-, c1', c2', h1', h2', s1', o1', b1'⟩ := hL'
    dsimp only
    refine ⟨funext fun d => ?_, funext fun d => ?_, ?_, ?_, ?_⟩
    · cases d with
      | inl j => rw [c1, c1']
      | inr j => rw [c2, c2']
    · cases d with
      | inl j => rw [h1, h1']
      | inr j => rw [h2, h2']
    · rw [s1, s1']
    · rw [o1, o1']
    · rw [b1, b1']

omit [DecidableEq State] in
/-- **The successor part of a locally consistent window is determined by its time-`t`
part.** For every tape whose head is far the cell and head at time `t + 1`, and when every
head is in the window everything. -/
theorem post_of_pre {L L' : LocalCfg i w Symbol State} (hL : LocallyConsistent M acc L)
    (hL' : LocallyConsistent M acc L') (hno : ∀ d, ¬ L'.TwoHeads d)
    (hc : L.cellPre = L'.cellPre) (hh : L.headPre = L'.headPre) (hs : L.statePre = L'.statePre) :
    (∀ d, L'.HeadFar d → L.cellPost d = L'.cellPost d ∧ L.headPost d = L'.headPost d) ∧
    ((∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ L'.HeadAt d δ) →
      L.cellPost = L'.cellPost ∧ L.headPost = L'.headPost ∧ L.statePost = L'.statePost ∧
        L.emitOne = L'.emitOne ∧ L.emitBad = L'.emitBad) := by
  have hno' : ∀ d, ¬ L.TwoHeads d := fun d h =>
    hno d (by unfold LocalCfg.TwoHeads at h ⊢; rwa [hh] at h)
  have hat : ∀ d δ, L.HeadAt d δ ↔ L'.HeadAt d δ := fun d δ => by
    unfold LocalCfg.HeadAt; rw [hh]
  have hfarI : ∀ d, L.HeadFar d ↔ L'.HeadFar d := fun d => by
    unfold LocalCfg.HeadFar; rw [hh]
  rcases hL with ⟨d, h⟩ | ⟨hfar, hfull⟩
  · exact absurd h (hno' d)
  rcases hL' with ⟨d, h⟩ | ⟨hfar', hfull'⟩
  · exact absurd h (hno d)
  refine ⟨fun d hd => ?_, fun hall => ?_⟩
  · obtain ⟨c1, h1⟩ := hfar d ((hfarI d).mpr hd)
    obtain ⟨c1', h1'⟩ := hfar' d hd
    exact ⟨by rw [c1, c1', hc], by rw [h1, h1']⟩
  · have hall' : ∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ L.HeadAt d δ := fun d =>
      let ⟨δ, h1, h2, h3⟩ := hall d; ⟨δ, h1, h2, (hat d δ).mpr h3⟩
    rcases hfull' with ⟨δ', hδ', hF'⟩ | hn
    swap; · exact absurd hall hn
    rcases hfull with ⟨δ, hδ, hF⟩ | hn
    swap; · exact absurd hall' hn
    have hδδ : δ = δ' := funext fun d =>
      LocalCfg.HeadAt.unique (hδ d).2.2 ((hat d (δ' d)).mpr (hδ' d).2.2)
    subst hδδ
    exact fullStep_post_eq M acc δ hF hF' hc hh hs

end Post

/-! ## The free input strings -/

section Extract

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}

/-- The blank bit of cell `k + 3` of input tape `j` at time `0` (`true` past the last cell). -/
def blankBit (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (k : ℕ) : Bool :=
  if h : k + 3 < numCells S then a (.cell 0 (.inl j) ⟨k + 3, h⟩ .blank) else true

/-- The `s` bit of cell `k + 3` of input tape `j` at time `0`. -/
def symBit (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (s : Symbol) (k : ℕ) : Bool :=
  if h : k + 3 < numCells S then a (.cell 0 (.inl j) ⟨k + 3, h⟩ (.sym s)) else false

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeLen_exists (a : TabVar i w Symbol State S G → Bool) (j : Fin i) :
    ∃ k, blankBit a j k = true ∨ numCells S ≤ k + 5 :=
  ⟨numCells S, Or.inr (by omega)⟩

/-- The length of the string on a free tape: the first cell, from cell `3`, that is blank
or a boundary cell. -/
noncomputable def freeLen (a : TabVar i w Symbol State S G → Bool) (j : Fin i) : ℕ :=
  Nat.find (freeLen_exists a j)

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeLen_spec (a : TabVar i w Symbol State S G → Bool) (j : Fin i) :
    blankBit a j (freeLen a j) = true ∨ numCells S ≤ freeLen a j + 5 :=
  Nat.find_spec (freeLen_exists a j)

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeLen_min (a : TabVar i w Symbol State S G → Bool) (j : Fin i) {k : ℕ}
    (hk : k < freeLen a j) : ¬ (blankBit a j k = true ∨ numCells S ≤ k + 5) :=
  Nat.find_min (freeLen_exists a j) hk

/-- The string on free tape `j`, read off row `0`: `s₀` where the `s₀` bit is set, else
`s₁`, up to the first blank. -/
noncomputable def freeString (a : TabVar i w Symbol State S G → Bool) (j : Fin i)
    (s₀ s₁ : Symbol) : List Symbol :=
  List.ofFn fun k : Fin (freeLen a j) => if symBit a j s₀ k then s₀ else s₁

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeString_mem (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (s₀ s₁ : Symbol) :
    ∀ s ∈ freeString a j s₀ s₁, s = s₀ ∨ s = s₁ := by
  intro s hs
  rw [freeString, List.mem_ofFn] at hs
  obtain ⟨k, hk⟩ := hs
  split_ifs at hk
  · exact Or.inl hk.symm
  · exact Or.inr hk.symm

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem length_freeString (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (s₀ s₁ : Symbol) :
    (freeString a j s₀ s₁).length = freeLen a j :=
  List.length_ofFn

variable (s₀ s₁ : Symbol)

/-- What the free-tape clauses say about tape `j` at time `0`. -/
structure FreeFacts (a : TabVar i w Symbol State S G → Bool) (j : Fin i) : Prop where
  bdry : ∀ (p : Pos S) v, p.IsBdry → a (.cell 0 (.inl j) p v) = decide (v = .bdry)
  other : ∀ (p : Pos S) v, ¬ p.IsBdry → v ≠ .sym s₀ → v ≠ .sym s₁ → v ≠ .blank →
    a (.cell 0 (.inl j) p v) = false
  two : ∀ v, a (.cell 0 (.inl j) ⟨2, by unfold numCells; omega⟩ v) = decide (v = .blank)
  some : ∀ p : Pos S, ¬ p.IsBdry → a (.cell 0 (.inl j) p (.sym s₀)) = true ∨
    a (.cell 0 (.inl j) p (.sym s₁)) = true ∨ a (.cell 0 (.inl j) p .blank) = true
  once : ∀ (p : Pos S) v v', ¬ p.IsBdry → v ≠ v' →
    ¬ (a (.cell 0 (.inl j) p v) = true ∧ a (.cell 0 (.inl j) p v') = true)
  mono : ∀ p p' : Pos S, 2 < (p : ℕ) → ¬ p'.IsBdry → p < p' →
    a (.cell 0 (.inl j) p .blank) = true → a (.cell 0 (.inl j) p' .blank) = true

variable {s₀ s₁}

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem freeFacts (fixed : Fin i → Option (List Symbol)) (a : TabVar i w Symbol State S G → Bool)
    (hSat : (freeClauses (S := S) (G := G) s₀ s₁ fixed).Sat a) (j : Fin i) (hj : fixed j = none) :
    FreeFacts s₀ s₁ a j where
  bdry p v hb := (unit_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, p, v, hj, hb, rfl⟩))))))
  other p v hnb h0 h1 hbl := (unit_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, p, v, hj, hnb, h0, h1, hbl, rfl⟩))))))
  two v := (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨j, v, hj, rfl⟩)))))
  some p hnb := by
    have := hSat _ (Or.inl (Or.inl (Or.inr ⟨j, p, hj, hnb, rfl⟩)))
    rw [cl_eval] at this
    simpa using this
  once p v v' hnb hvv' := (nand2_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inr ⟨j, p, v, v', hj, hnb, hvv', rfl⟩)))
  mono p p' h2 hnb' hpp' := (imp2_eval _ _ _).mp
    (hSat _ (Or.inr ⟨j, p, p', hj, h2, hnb', hpp', rfl⟩))

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- An interior cell carrying one value carries no other. -/
theorem FreeFacts.onehot {a : TabVar i w Symbol State S G → Bool} {j : Fin i}
    (F : FreeFacts s₀ s₁ a j) (p : Pos S) (hnb : ¬ p.IsBdry) (u : CellVal Symbol)
    (hu : a (.cell 0 (.inl j) p u) = true) (v : CellVal Symbol) :
    a (.cell 0 (.inl j) p v) = decide (v = u) := by
  by_cases hv : v = u
  · subst hv; simp [hu]
  · rw [decide_eq_false hv]
    have := F.once p v u hnb hv
    cases h : a (.cell 0 (.inl j) p v)
    · rfl
    · exact absurd ⟨h, hu⟩ this

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- **The time-`0` row of a free tape is the encoding of the string read off it.** -/
theorem FreeFacts.cell_eq {a : TabVar i w Symbol State S G → Bool} {j : Fin i}
    (F : FreeFacts s₀ s₁ a j) (p : Pos S) (v : CellVal Symbol) :
    a (.cell 0 (.inl j) p v) = decide (v = inputCellVal (freeString a j s₀ s₁) p) := by
  by_cases hb : p.IsBdry
  · rw [F.bdry p v hb, (inputCellVal_bdry_iff _ _).mpr hb]
  by_cases h2 : (p : ℕ) = 2
  · rw [show p = ⟨2, Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 7 (2 * S))⟩ from Fin.ext h2,
      F.two v, inputCellVal_two]
  have h3 : 3 ≤ (p : ℕ) := by rw [not_isBdry_iff] at hb; omega
  obtain ⟨k, hk3, rfl⟩ : ∃ k, ∃ hk3 : k + 3 < numCells S, p = ⟨k + 3, hk3⟩ :=
    ⟨(p : ℕ) - 3, by have := p.isLt; omega, Fin.ext (by dsimp only; omega)⟩
  have hk5 : k + 5 < numCells S := by
    rw [not_isBdry_iff] at hb; dsimp only at hb; omega
  have hlen := length_freeString a j s₀ s₁
  rw [inputCellVal_eq _ _ hb, if_pos (by omega)]
  simp only [Nat.add_sub_cancel]
  by_cases hkn : k < freeLen a j
  · have hmin := freeLen_min a j hkn
    have hblank : a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ .blank) = false := by
      have : blankBit a j k = a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ .blank) := dif_pos hk3
      rw [← this]
      cases h : blankBit a j k
      · rfl
      · exact absurd (Or.inl h) hmin
    have hsym : symBit a j s₀ k = a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ (.sym s₀)) := dif_pos hk3
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hkn)]
    simp only [freeString, List.getElem_ofFn]
    rw [hsym]
    rcases F.some _ hb with h0 | h1 | hbl
    · rw [h0, if_pos rfl]; exact F.onehot _ hb _ h0 v
    · cases h0 : a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ (.sym s₀))
      · rw [if_neg Bool.false_ne_true]; exact F.onehot _ hb _ h1 v
      · rw [if_pos rfl]; exact F.onehot _ hb _ h0 v
    · rw [hblank] at hbl; exact absurd hbl Bool.false_ne_true
  · have hnk : freeLen a j ≤ k := Nat.le_of_not_lt hkn
    rcases freeLen_spec a j with hbn | hbn
    swap; · omega
    have hn3 : freeLen a j + 3 < numCells S := by omega
    have hcell : a (.cell 0 (.inl j) ⟨freeLen a j + 3, hn3⟩ .blank) = true := by
      have : blankBit a j (freeLen a j) =
          a (.cell 0 (.inl j) ⟨freeLen a j + 3, hn3⟩ .blank) := dif_pos hn3
      rw [← this]; exact hbn
    have hblank : a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ .blank) = true := by
      rcases Nat.eq_or_lt_of_le hnk with h | h
      · subst h; exact hcell
      · exact F.mono ⟨freeLen a j + 3, hn3⟩ ⟨k + 3, hk3⟩ (by dsimp only; omega) hb
          (Fin.lt_def.mpr (by dsimp only; omega)) hcell
    rw [List.getElem?_eq_none (by rw [hlen]; exact hnk)]
    exact F.onehot _ hb _ hblank v

end Extract

/-! ## The rows encode the run -/

section Rows

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}

/-- Row `t` of the assignment `a` encodes the configuration `c`. -/
structure RowOk (a : TabVar i w Symbol State S G → Bool) (t : Fin (S + 1))
    (c : Cfg i w Symbol State input) : Prop where
  cell : ∀ d p v, a (.cell t d p v) = decide (cellValAt (S := S) c d p = v)
  head : ∀ d p, a (.head t d p) = decide (headCell (S := S) c d = p)
  state : ∀ q, a (.state t q) = decide (c.state = q)

omit [Fintype Symbol] [Fintype State] in
/-- A locally consistent window of `a` at step `t` whose time-`t` part is that of `c`. -/
theorem window_of_sat (a : TabVar i w Symbol State S G → Bool) (t : Fin S)
    (c : Cfg i w Symbol State input) (hrow : RowOk a t.castSucc c) (js : Tape i w → Center S)
    (hwin : checkPred M acc (fun v => a (winVarOf (G := G) t js v))) :
    ∃ L : LocalCfg i w Symbol State, LocallyConsistent M acc L ∧
      (∀ v, L.encode v = a (winVarOf (G := G) t js v)) ∧
      L.cellPre = (localCfgOf M acc c js).cellPre ∧ L.headPre = (localCfgOf M acc c js).headPre ∧
      L.statePre = (localCfgOf M acc c js).statePre := by
  obtain ⟨L, hLe, hLc⟩ := hwin
  have he : ∀ v, L.encode v = a (winVarOf (G := G) t js v) := fun v => congrFun hLe v
  refine ⟨L, hLc, he, ?_, ?_, ?_⟩
  · funext d δ
    have := he (.cellPre d δ ((localCfgOf M acc c js).cellPre d δ))
    simp only [LocalCfg.encode, winVarOf] at this
    rw [hrow.cell] at this
    exact of_decide_eq_true (this.trans (decide_eq_true rfl))
  · funext d δ
    have := he (.headPre d δ)
    simp only [LocalCfg.encode, winVarOf] at this
    rw [hrow.head] at this
    exact this
  · have := he (.statePre (localCfgOf M acc c js).statePre)
    simp only [LocalCfg.encode, winVarOf] at this
    rw [hrow.state] at this
    exact of_decide_eq_true (this.trans (decide_eq_true rfl))

/-! ### Windows centered at the heads and at a cell -/

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem headCell_sub_two_toNat (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w) :
    (((headCell (S := S) c d - 2).toNat : ℕ) : ℤ) = headCell (S := S) c d - 2 :=
  Int.toNat_of_nonneg (by have := hin.headCell_bounds d; omega)

/-- The center putting the head of `d` at offset `2`. -/
def headCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w) : Center S :=
  ⟨(headCell (S := S) c d - 2).toNat, by
    have := hin.headCell_bounds d
    have h := headCell_sub_two_toNat c hin d
    have hnc : numCells S = 2 * S + 7 := rfl
    omega⟩

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem headAt_headCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S)
    (js : Tape i w → Center S) (d : Tape i w) (hd : js d = headCenter c hin d) :
    (localCfgOf M acc c js).HeadAt d 2 := by
  apply headAt_localCfgOf
  rw [hd]
  simp only [cellIdx_val, headCenter, Fin.val_two]
  have := headCell_sub_two_toNat c hin d
  push_cast
  omega

/-- The centers putting the cell `p` of tape `d` at the middle of its window and the head of
every other tape at offset `2`. -/
def cellCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w) (p : Pos S)
    (hnb : ¬ p.IsBdry) : Tape i w → Center S :=
  fun d' => if d' = d then
    ⟨(p : ℕ) - 2, by
      rw [not_isBdry_iff] at hnb
      have hnc : numCells S = 2 * S + 7 := rfl
      omega⟩
  else headCenter c hin d'

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem center_cellCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w)
    (p : Pos S) (hnb : ¬ p.IsBdry) : center (cellCenter c hin d p hnb d) = p := by
  apply Fin.ext
  simp only [center_val, cellCenter, if_true]
  rw [not_isBdry_iff] at hnb
  omega

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- Every head is in its window when the windows are centered at the heads. -/
theorem allIn_headCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) :
    ∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
      (localCfgOf M acc c (headCenter c hin)).HeadAt d δ :=
  fun d => ⟨2, by simp, by simp, headAt_headCenter M acc c hin _ d rfl⟩

omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- At the window of a cell, either every head is in its window or the head of the cell's
tape is far. -/
theorem cellCenter_cases (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w)
    (p : Pos S) (hnb : ¬ p.IsBdry) :
    (∀ d', ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
      (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadAt d' δ) ∨
    (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadFar d := by
  by_cases hnear : ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
      headCell (S := S) c d = ((cellIdx (cellCenter c hin d p hnb d) δ : Pos S) : ℕ)
  · left
    intro d'
    by_cases hd : d' = d
    · subst hd
      obtain ⟨δ, h1, h3, hδ⟩ := hnear
      exact ⟨δ, h1, h3, headAt_localCfgOf M acc c _ d' δ hδ⟩
    · exact ⟨2, by simp, by simp, headAt_headCenter M acc c hin _ d'
        (by simp only [cellCenter, if_neg hd])⟩
  · right
    have h : ∀ δ : Fin 5, 1 ≤ (δ : ℕ) → (δ : ℕ) ≤ 3 →
        (localCfgOf M acc c (cellCenter c hin d p hnb)).headPre d δ = false := by
      intro δ h1 h3
      cases h : (localCfgOf M acc c (cellCenter c hin d p hnb)).headPre d δ
      · rfl
      · exact absurd ⟨δ, h1, h3, (headPre_localCfgOf M acc c _ d δ).mp h⟩ hnear
    exact ⟨h 1 (by simp) (by simp), h 2 (by simp) (by simp), h 3 (by simp) (by simp)⟩

/-! ### The step -/

omit [Fintype Symbol] [Fintype State] in
/-- **A row encoding `c` is followed by a row encoding `M.step c`**, when every window is
locally consistent; the emission bits of the step are those of `c`. -/
theorem rowOk_step (a : TabVar i w Symbol State S G → Bool) (t : Fin S)
    (c : Cfg i w Symbol State input) (hrow : RowOk a t.castSucc c) (hin : HeadsIn c S)
    (hin' : HeadsIn (M.step c) S)
    (hwin : ∀ js, checkPred M acc (fun v => a (winVarOf (G := G) t js v)))
    (hbdry : ∀ d (p : Pos S) v, p.IsBdry → a (.cell t.succ d p v) = decide (v = .bdry))
    (hbdryh : ∀ d (p : Pos S), p.IsBdry → a (.head t.succ d p) = false) :
    RowOk a t.succ (M.step c) ∧ a (.emitOne t) = decide (M.outputSymbol c = some acc) ∧
      a (.emitBad t) = decide (M.outputSymbol c ≠ none ∧ M.outputSymbol c ≠ some acc) := by
  have key : ∀ js, ∃ L : LocalCfg i w Symbol State,
      (∀ v, L.encode v = a (winVarOf (G := G) t js v)) ∧
      (∀ d, (localCfgOf M acc c js).HeadFar d →
        L.cellPost d = (localCfgOf M acc c js).cellPost d ∧
        L.headPost d = (localCfgOf M acc c js).headPost d) ∧
      ((∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ (localCfgOf M acc c js).HeadAt d δ) →
        L.cellPost = (localCfgOf M acc c js).cellPost ∧
        L.headPost = (localCfgOf M acc c js).headPost ∧
        L.statePost = (localCfgOf M acc c js).statePost ∧
        L.emitOne = (localCfgOf M acc c js).emitOne ∧
        L.emitBad = (localCfgOf M acc c js).emitBad) := by
    intro js
    obtain ⟨L, hLc, he, hc, hh, hs⟩ := window_of_sat M acc a t c hrow js (hwin js)
    exact ⟨L, he, post_of_pre M acc hLc (locallyConsistent_localCfgOf M acc c js hin)
      (not_twoHeads_localCfgOf M acc c js) hc hh hs⟩
  obtain ⟨L₀, he₀, -, hfull₀⟩ := key (headCenter c hin)
  obtain ⟨-, -, hs₀, ho₀, hb₀⟩ := hfull₀ (allIn_headCenter M acc c hin)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro d p v
    by_cases hb : p.IsBdry
    · rw [hbdry d p v hb, cellValAt_bdry _ _ _ hb]
      exact decide_eq_decide.mpr eq_comm
    · obtain ⟨L, he, hfar, hfull⟩ := key (cellCenter c hin d p hb)
      have hcen := center_cellCenter c hin d p hb
      have hpost : L.cellPost d = (localCfgOf M acc c (cellCenter c hin d p hb)).cellPost d := by
        rcases cellCenter_cases M acc c hin d p hb with hall | hfar'
        · exact congrFun (hfull hall).1 d
        · exact (hfar d hfar').1
      have := he (.cellPost d v)
      simp only [LocalCfg.encode, winVarOf, hcen] at this
      rw [← this, hpost]
      simp only [localCfgOf, hcen]
  · intro d p
    by_cases hb : p.IsBdry
    · rw [hbdryh d p hb]
      apply (decide_eq_false _).symm
      intro h
      have hbd := hin'.headCell_bounds d
      have hnc : numCells S = 2 * S + 7 := rfl
      unfold Pos.IsBdry at hb
      omega
    · obtain ⟨L, he, hfar, hfull⟩ := key (cellCenter c hin d p hb)
      have hcen := center_cellCenter c hin d p hb
      have hpost : L.headPost d = (localCfgOf M acc c (cellCenter c hin d p hb)).headPost d := by
        rcases cellCenter_cases M acc c hin d p hb with hall | hfar'
        · exact congrFun (hfull hall).2.1 d
        · exact (hfar d hfar').2
      have := he (.headPost d)
      simp only [LocalCfg.encode, winVarOf, hcen] at this
      rw [← this, hpost]
      simp only [localCfgOf, hcen]
  · intro q
    have := he₀ (.statePost q)
    simp only [LocalCfg.encode, winVarOf] at this
    rw [← this, hs₀]
    rfl
  · have := he₀ .emitOne
    simp only [LocalCfg.encode, winVarOf] at this
    rw [← this, ho₀]
    rfl
  · have := he₀ .emitBad
    simp only [LocalCfg.encode, winVarOf] at this
    rw [← this, hb₀]
    rfl

end Rows

theorem eq_singleton_of_length_le_one {α : Type*} {l : List α} {x : α} (hne : l ≠ [])
    (hlen : l.length ≤ 1) (hall : ∀ s ∈ l, s = x) : l = [x] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons s l' =>
    cases l' with
    | nil => rw [hall s (by simp)]
    | cons s' l'' => simp at hlen

/-! ## From a satisfying assignment to an accepting run -/

section Sound

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)

/-- The inputs read off a satisfying assignment: the fixed strings, and on the free tapes
the strings on the time-`0` rows. -/
noncomputable def inputOf : Fin i → List Symbol :=
  fun j => (fixed j).getD (freeString a j s₀ s₁)

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem inputOf_fixed (j : Fin i) (x : List Symbol) (hx : fixed j = some x) :
    inputOf s₀ s₁ fixed chk a j = x := by
  simp [inputOf, hx]

omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem inputOf_free (j : Fin i) (hx : fixed j = none) :
    inputOf s₀ s₁ fixed chk a j = freeString a j s₀ s₁ := by
  simp [inputOf, hx]

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem headCell_initCfg_iff (input : Fin i → List Symbol) (d : Tape i w) (p : Pos S) :
    headCell (S := S) (M.initCfg input) d = (p : ℕ) ↔ p = startCell S d := by
  cases d with
  | inl j =>
    simp only [headCell, initCfg, startCell, Fin.ext_iff, Fin.val_one]
    push_cast; omega
  | inr j =>
    simp only [headCell, initCfg, startCell, Fin.ext_iff]
    omega

omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem cellValAt_initCfg_inr (input : Fin i → List Symbol) (j : Fin w) (p : Pos S) :
    cellValAt (S := S) (M.initCfg input) (.inr j) p = workCellVal₀ p := by
  unfold cellValAt workCellVal₀
  split_ifs <;> rfl

variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat

theorem sat_start : (startClauses (S := S) (G := chk.gates.length) M fixed).Sat a :=
  fun c hc => hSat c (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc)))))

theorem sat_free : (freeClauses (S := S) (G := chk.gates.length) s₀ s₁ fixed).Sat a :=
  fun c hc => hSat c (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))

theorem sat_bdry_cell (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) (v : CellVal Symbol)
    (hb : p.IsBdry) : a (.cell t d p v) = decide (v = .bdry) :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨t, d, p, v, hb, rfl⟩))))))

theorem sat_bdry_head (t : Fin (S + 1)) (d : Tape i w) (p : Pos S) (hb : p.IsBdry) :
    a (.head t d p) = false :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨t, d, p, hb, rfl⟩))))))

theorem sat_emitted_zero : a (.emitted 0) = false :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl rfl)))))))))

theorem sat_emitted_succ (t : Fin S) :
    a (.emitted t.succ) = true → a (.emitted t.castSucc) = true ∨ a (.emitOne t) = true := by
  have := hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨t, rfl⟩))))))))
  rw [cl_eval] at this
  simp only [lit_eval_true, lit_eval_false, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  intro h
  rcases this with h' | h' | h'
  · rw [h] at h'; exact Bool.noConfusion h'
  · exact Or.inl h'
  · exact Or.inr h'

theorem sat_emitted_mono (t : Fin S) :
    a (.emitted t.castSucc) = true → a (.emitted t.succ) = true :=
  (imp2_eval _ _ _).mp
    (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨t, rfl⟩))))))))

theorem sat_emitOne_emitted (t : Fin S) :
    a (.emitOne t) = true → a (.emitted t.succ) = true :=
  (imp2_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr ⟨t, rfl⟩)))))))

theorem sat_emitOne_once (t : Fin S) :
    ¬ (a (.emitOne t) = true ∧ a (.emitted t.castSucc) = true) :=
  (nand2_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨t, rfl⟩))))))

theorem sat_emitBad (t : Fin S) : a (.emitBad t) = false :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inr ⟨t, rfl⟩)))))

theorem sat_final_state : a (.state (Fin.last S) none) = true :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inr (Or.inl rfl))))

theorem sat_final_emitted : a (.emitted (Fin.last S)) = true :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inr (Or.inr rfl))))

/-- The window clauses force, through the check circuit, local consistency of every
window. -/
theorem sat_window (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) (hin : chk.InputsLt)
    (hne : chk.gates ≠ []) (t : Fin S) (js : Tape i w → Center S) :
    checkPred M acc (fun v => a (winVarOf (G := chk.gates.length) t js v)) := by
  have hts : (chk.tseitin (inpOf (G := chk.gates.length) t js) (auxOf t js)).Sat a :=
    fun c hc => hSat c (Or.inr ⟨t, js, hc⟩)
  have heval := Circuit.eval_of_tseitin_sat chk hC hin hne _ _
    (fun n => a (inpOf (G := chk.gates.length) t js n)) a (fun _ _ => rfl) hts
  have hfun : (fun n => (winBits fun v => a (winVarOf (G := chk.gates.length) t js v)).getD n false) =
      fun n => a (inpOf (G := chk.gates.length) t js n) :=
    funext (getD_winBits _ (sat_emitted_zero M s₀ s₁ fixed chk a hSat) t js)
  have := hchk (fun v => a (winVarOf (G := chk.gates.length) t js v))
  unfold Circuit.evalBits at this
  rw [hfun] at this
  exact this.mp heval

/-- Row `0` encodes the initial configuration on the inputs read off the assignment. -/
theorem rowOk_zero : RowOk (input := inputOf s₀ s₁ fixed chk a) a 0 (M.initCfg _) where
  cell d p v := by
    cases d with
    | inl j =>
      rw [cellValAt_inl]
      cases hj : fixed j with
      | none =>
        rw [inputOf_free s₀ s₁ fixed chk a j hj,
          (freeFacts fixed a (sat_free M s₀ s₁ fixed chk a hSat) j hj).cell_eq p v]
        exact decide_eq_decide.mpr eq_comm
      | some x =>
        rw [inputOf_fixed s₀ s₁ fixed chk a j x hj,
          (unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
            (Or.inl (Or.inr ⟨j, x, p, v, hj, rfl⟩)))]
        exact decide_eq_decide.mpr eq_comm
    | inr j =>
      rw [cellValAt_initCfg_inr, (unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
        (Or.inr ⟨j, p, v, rfl⟩))]
      exact decide_eq_decide.mpr eq_comm
  head d p := by
    rw [(unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
      (Or.inl (Or.inl (Or.inl ⟨d, p, rfl⟩))))]
    exact decide_eq_decide.mpr (headCell_initCfg_iff M _ d p).symm
  state q := by
    rw [(unit_eval a _ _).mp (sat_start M s₀ s₁ fixed chk a hSat _
      (Or.inl (Or.inl (Or.inr ⟨q, rfl⟩))))]
    exact decide_eq_decide.mpr eq_comm

/-- **The rows of a satisfying assignment encode the run** on the inputs read off it, with
the emission bookkeeping: `emitted t` iff something was output before time `t`, at most one
symbol, and only `acc`. -/
theorem rows_of_sat (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) (hin : chk.InputsLt)
    (hne : chk.gates ≠ []) (t : ℕ) (ht : t ≤ S) :
    RowOk (input := inputOf s₀ s₁ fixed chk a) a ⟨t, Nat.lt_succ_of_le ht⟩ (cfgAt M t) ∧
      a (.emitted ⟨t, Nat.lt_succ_of_le ht⟩) =
        decide (M.outputString (M.initCfg (inputOf s₀ s₁ fixed chk a)) t ≠ []) ∧
      (M.outputString (M.initCfg (inputOf s₀ s₁ fixed chk a)) t).length ≤ 1 ∧
      ∀ s ∈ M.outputString (M.initCfg (inputOf s₀ s₁ fixed chk a)) t, s = acc := by
  induction t with
  | zero =>
    refine ⟨?_, ?_, by simp [outputString_zero], by simp [outputString_zero]⟩
    · rw [cfgAt_zero]
      exact rowOk_zero M s₀ s₁ fixed chk a hSat
    · rw [show (⟨0, Nat.lt_succ_of_le ht⟩ : Fin (S + 1)) = 0 from rfl,
        sat_emitted_zero M s₀ s₁ fixed chk a hSat]
      simp [outputString_zero]
  | succ t ih =>
    obtain ⟨hrow, hem, hlen, hacc⟩ := ih (by omega)
    set input := inputOf s₀ s₁ fixed chk a with hinput
    let tf : Fin S := ⟨t, by omega⟩
    have hstep := rowOk_step M acc a tf (cfgAt M (input := input) t) hrow
      (headsIn_cfgAt M (input := input) t (by omega))
      (by rw [← cfgAt_succ]; exact headsIn_cfgAt M (input := input) (t + 1) ht)
      (fun js => sat_window M acc s₀ s₁ fixed chk a hSat hchk hC hin hne tf js)
      (fun d p v hb => sat_bdry_cell M s₀ s₁ fixed chk a hSat _ d p v hb)
      (fun d p hb => sat_bdry_head M s₀ s₁ fixed chk a hSat _ d p hb)
    obtain ⟨hrow', hone, hbad⟩ := hstep
    have hem' : a (.emitted tf.castSucc) =
        decide (M.outputString (M.initCfg input) t ≠ []) := hem
    have hbad' := sat_emitBad M s₀ s₁ fixed chk a hSat tf
    rw [hbad] at hbad'
    have hsym : M.outputSymbol (cfgAt M (input := input) t) = none ∨
        M.outputSymbol (cfgAt M (input := input) t) = some acc := by
      by_cases h : M.outputSymbol (cfgAt M (input := input) t) = none
      · exact Or.inl h
      · right
        by_contra h'
        exact absurd hbad' (by simp [h, h'])
    rw [outputString_succ']
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [cfgAt_succ]; exact hrow'
    · apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_iff]
      constructor
      · intro h
        rcases sat_emitted_succ M s₀ s₁ fixed chk a hSat tf h with h' | h'
        · rw [hem', decide_eq_true_iff] at h'
          exact fun h'' => h' (List.append_eq_nil_iff.mp h'').1
        · rw [hone, decide_eq_true_iff] at h'
          rw [h']; simp
      · intro h
        by_cases hA : M.outputString (M.initCfg input) t = []
        · rw [hA, List.nil_append] at h
          rcases hsym with h' | h'
          · rw [h'] at h; exact absurd rfl h
          · exact sat_emitOne_emitted M s₀ s₁ fixed chk a hSat tf
              (by rw [hone, h']; simp)
        · exact sat_emitted_mono M s₀ s₁ fixed chk a hSat tf (by rw [hem']; exact decide_eq_true hA)
    · rcases hsym with h' | h'
      · rw [h']; simpa using hlen
      · have hnot := sat_emitOne_once M s₀ s₁ fixed chk a hSat tf
        rw [hone, h', hem'] at hnot
        have hA : M.outputString (M.initCfg input) t = [] := by
          by_contra hA
          exact hnot ⟨by simp, decide_eq_true hA⟩
        rw [hA, h']; simp
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact hacc s hs
      · rcases hsym with h' | h'
        · rw [h'] at hs; simp at hs
        · rw [h'] at hs; simpa using hs

/-- **Soundness of the tableau.** A satisfying assignment reads, on its time-`0` rows, the
inputs `inputOf`, which extend the fixed strings by strings over `{s₀, s₁}`, and `M`
accepts them within `S` steps. -/
theorem acceptsIn_of_tableau_sat (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt)
    (hin : chk.InputsLt) (hne : chk.gates ≠ []) :
    (∀ j x, fixed j = some x → inputOf s₀ s₁ fixed chk a j = x) ∧
    (∀ j, fixed j = none → ∀ s ∈ inputOf s₀ s₁ fixed chk a j, s = s₀ ∨ s = s₁) ∧
    (∀ j (p : Pos S) v, a (.cell 0 (.inl j) p v) =
      decide (v = inputCellVal (inputOf s₀ s₁ fixed chk a j) p)) ∧
    AcceptsIn M acc (inputOf s₀ s₁ fixed chk a) S := by
  obtain ⟨hrow, hem, hlen, hacc⟩ :=
    rows_of_sat M acc s₀ s₁ fixed chk a hSat hchk hC hin hne S le_rfl
  refine ⟨fun j x hx => inputOf_fixed s₀ s₁ fixed chk a j x hx, fun j hj => ?_, fun j p v => ?_, ?_, ?_⟩
  · rw [inputOf_free s₀ s₁ fixed chk a j hj]
    exact freeString_mem a j s₀ s₁
  · have := (rowOk_zero M s₀ s₁ fixed chk a hSat).cell (.inl j) p v
    rw [this, cellValAt_inl]
    exact decide_eq_decide.mpr eq_comm
  · have h := sat_final_state M s₀ s₁ fixed chk a hSat
    have h' := hrow.state none
    rw [show (Fin.last S) = ⟨S, Nat.lt_succ_of_le le_rfl⟩ from rfl, h', decide_eq_true_iff] at h
    exact h
  · have h := sat_final_emitted M s₀ s₁ fixed chk a hSat
    rw [show (Fin.last S) = ⟨S, Nat.lt_succ_of_le le_rfl⟩ from rfl, hem, decide_eq_true_iff] at h
    exact eq_singleton_of_length_le_one h hlen hacc

end Sound

/-! ## The equivalence -/

section Iff

variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit)

/-- **Correctness of the Cook–Levin tableau** (`lem:correct-tableau`): the tableau formula
of `S` steps is satisfiable iff `M` accepts, within `S` steps, some inputs that extend the
fixed strings by strings over `{s₀, s₁}` on the free tapes. -/
theorem tableau_sat_iff (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) (hin : chk.InputsLt)
    (hne : chk.gates ≠ []) :
    (∃ a, (tableau M s₀ s₁ S fixed chk).Sat a) ↔
      ∃ input : Fin i → List Symbol, (∀ j x, fixed j = some x → input j = x) ∧
        (∀ j, fixed j = none → ∀ s ∈ input j, s = s₀ ∨ s = s₁) ∧ AcceptsIn M acc input S := by
  constructor
  · rintro ⟨a, hSat⟩
    obtain ⟨h1, h2, -, h4⟩ := acceptsIn_of_tableau_sat M acc s₀ s₁ fixed chk a hSat hchk hC hin hne
    exact ⟨_, h1, h2, h4⟩
  · rintro ⟨input, hfix, hfree, hacc⟩
    exact ⟨_, tableau_sat_of_acceptsIn M acc chk s₀ s₁ fixed hchk hC hfix hfree hacc⟩

end Iff

end MIPRE.TM.CookLevin
