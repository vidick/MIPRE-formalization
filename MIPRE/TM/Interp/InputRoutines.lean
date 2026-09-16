/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Routines
import MIPRE.TM.Interp.Repr

/-!
# The input-tape routines

`copyUnary`, `copyInputBits`, `checkLen` and `buildAnswer` read an input tape from its
head to the blank after the input, writing on a work tape; their specifications are by
induction on the remaining suffix of the input.
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)

variable {input : Fin 7 → List Sym}

/-- The effect of writing `l` at the head of `t` (as in `CopyTree.lean`). -/
structure WEff (t : WT) (c c' : Cfg input) (l : List Sym) : Prop where
  holds : Holds (c'.workTapes t) (c.workTapePos t) l
  outside : ∀ q, (q < c.workTapePos t ∨ c.workTapePos t + l.length ≤ q) →
    c'.workTapes t q = c.workTapes t q
  pos : c'.workTapePos t = c.workTapePos t + l.length

theorem WEff.trans {t : WT} {c c' c'' : Cfg input} {l l' : List Sym} (h : WEff t c c' l)
    (h' : WEff t c' c'' l') : WEff t c c'' (l ++ l') where
  holds := by
    refine Holds.append ?_ ?_
    · exact h.holds.congr fun q hq1 hq2 => h'.outside q (Or.inl (by rw [h.pos]; omega))
    · rw [← h.pos]; exact h'.holds
  outside q hq := by
    simp only [List.length_append, Nat.cast_add] at hq
    rw [h'.outside q (by rw [h.pos]; omega), h.outside q (by omega)]
  pos := by rw [h'.pos, h.pos, List.length_append]; push_cast; ring

theorem WEff.cast {t : WT} {c c' : Cfg input} {l l' : List Sym} (h : WEff t c c' l)
    (e : l = l') : WEff t c c' l' := e ▸ h

theorem moveInputPos_val_one {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) < n + 1) :
    (moveInputPos p 1 : ℕ) = p + 1 := moveInputPos_val_pos p h

theorem WEff.nil {t : WT} {c c' : Cfg input} (htape : c'.workTapes t = c.workTapes t)
    (hpos : c'.workTapePos t = c.workTapePos t) : WEff t c c' [] where
  holds := by simp
  outside q _ := by rw [htape]
  pos := by simp [hpos]

theorem WEff.single {t : WT} {c c' : Cfg input} {s : Sym}
    (htape : c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some s))
    (hpos : c'.workTapePos t = c.workTapePos t + 1) : WEff t c c' [s] where
  holds := by rw [htape]; exact holds_update_self _ _ _
  outside q hq := by
    rw [htape, Function.update_of_ne]
    simp only [List.length_singleton, Nat.cast_one] at hq
    omega
  pos := by simp [hpos]

/-! ## `copyUnary` -/

/-- From position `q + 1` of input `j`: one `1` per remaining symbol. -/
theorem exec_copyUnary {k : ProgId} {pc : Fin maxPc} {j : IT} {dst : WT}
    (hins : instrAt k pc = .copyUnary j dst) (hpc : pc.val + 1 < maxPc) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (input j).length = q + m →
    ∃ c', Reach c (m + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j] [dst] ∧
      (c'.inputPos j : ℕ) = (input j).length + 1 ∧ WEff dst c c' (List.replicate m .one) := by
  induction m with
  | zero =>
    intro c q hq hpos hlen
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_end c j (by omega), Act.base_out, Option.toList_none,
      Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _,
      by simp; omega, WEff.nil ?_ ?_⟩
    · rw [applyAct_workTapes_of_none _ _ _ dst (by simp)]
    · simp
  | succ m ih =>
    intro c q hq hpos hlen
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_of_lt c j hpos (by omega), Act.mi_out, Act.mw_out, Act.ww_out,
      Act.base_out, Option.toList_none, Act.mi_next, Act.mw_next, Act.ww_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((((Act.base (.stay p0)).ww dst (some .one)).mw dst 1).mi j 1)
      (some ⟨k, pc, p0⟩) c with hc₁
    have hu : Untouched c c₁ [j] [dst] :=
      untouched_applyAct ⟨fun j' hj => by
        have : j' ≠ j := by simpa using hj
        simp [Act.mi, Function.update_of_ne this], fun d hd => by
        have : d ≠ dst := by simpa using hd
        simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
    have hpos₁ : (c₁.inputPos j : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_self]
      rw [moveInputPos_val_one (c.inputPos j) (by omega), hpos]
    have hw : WEff dst c c₁ [.one] := WEff.single
      (by rw [hc₁, applyAct_workTapes_of_some _ _ _ dst (s := some .one) (by simp)])
      (by simp [hc₁])
    obtain ⟨c', hr, hst, hu', hpos', hw'⟩ := ih c₁ (q + 1) (by simp [hc₁]) hpos₁ (by omega)
    refine ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), hpos', ?_⟩
    exact (hw.trans hw').cast (by simp [List.replicate_succ])

/-! ## `copyInputBits` -/

/-- From position `q + 1` of input `j`: the remaining symbols. -/
theorem exec_copyInputBits {k : ProgId} {pc : Fin maxPc} {j : IT} {dst : WT}
    (hins : instrAt k pc = .copyInputBits j dst) (hpc : pc.val + 1 < maxPc) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (input j).length = q + m →
    ∃ c', Reach c (m + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j] [dst] ∧
      (c'.inputPos j : ℕ) = (input j).length + 1 ∧ WEff dst c c' ((input j).drop q) := by
  induction m with
  | zero =>
    intro c q hq hpos hlen
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_end c j (by omega), Act.base_out, Option.toList_none,
      Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _,
      by simp; omega, ?_⟩
    rw [List.drop_of_length_le (by omega)]
    refine WEff.nil ?_ ?_
    · rw [applyAct_workTapes_of_none _ _ _ dst (by simp)]
    · simp
  | succ m ih =>
    intro c q hq hpos hlen
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_of_lt c j hpos (by omega), Act.mi_out, Act.mw_out, Act.ww_out,
      Act.base_out, Option.toList_none, Act.mi_next, Act.mw_next, Act.ww_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((((Act.base (.stay p0)).ww dst (some (input j)[q])).mw dst 1).mi j 1)
      (some ⟨k, pc, p0⟩) c with hc₁
    have hu : Untouched c c₁ [j] [dst] :=
      untouched_applyAct ⟨fun j' hj => by
        have : j' ≠ j := by simpa using hj
        simp [Act.mi, Function.update_of_ne this], fun d hd => by
        have : d ≠ dst := by simpa using hd
        simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
    have hpos₁ : (c₁.inputPos j : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_self]
      rw [moveInputPos_val_one (c.inputPos j) (by omega), hpos]
    have hw : WEff dst c c₁ [(input j)[q]] := WEff.single
      (by rw [hc₁, applyAct_workTapes_of_some _ _ _ dst (s := some (input j)[q]) (by simp)])
      (by simp [hc₁])
    obtain ⟨c', hr, hst, hu', hpos', hw'⟩ := ih c₁ (q + 1) (by simp [hc₁]) hpos₁ (by omega)
    refine ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), hpos', ?_⟩
    rw [List.drop_eq_getElem_cons (by omega)]
    exact (hw.trans hw').cast (by simp)

/-! ## `checkLen` -/

/-- From position `q + 1` on both `j` and `ref`, with `|j| - q ≤ |ref| - q`: both heads advance
to the end of `j`. -/
theorem exec_checkLen {k : ProgId} {pc : Fin maxPc} {j ref : IT}
    (hins : instrAt k pc = .checkLen j ref) (hpc : pc.val + 1 < maxPc) (hjr : j ≠ ref) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (c.inputPos ref : ℕ) = q + 1 → (input j).length = q + m → q + m ≤ (input ref).length →
    ∃ c', Reach c (m + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j, ref] [] ∧
      (c'.inputPos j : ℕ) = (input j).length + 1 ∧ (c'.inputPos ref : ℕ) = (input j).length + 1 := by
  induction m with
  | zero =>
    intro c q hq hpj hpr hlen _
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_end c j (by omega), Act.base_out, Option.toList_none,
      Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _,
      by simp; omega, by simp; omega⟩
  | succ m ih =>
    intro c q hq hpj hpr hlen hle
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_of_lt c j hpj (by omega), inputSymbol_of_lt c ref hpr (by omega),
      Act.mi_out, Act.base_out, Option.toList_none, Act.mi_next, Act.base_next, resolve_stay] at h
    set c₁ := applyAct (((Act.base (.stay p0)).mi j 1).mi ref 1) (some ⟨k, pc, p0⟩) c with hc₁
    have hu : Untouched c c₁ [j, ref] [] :=
      untouched_applyAct ⟨fun j' hj => by
        have h1 : j' ≠ j := fun e => hj (by simp [e])
        have h2 : j' ≠ ref := fun e => hj (by simp [e])
        simp [Act.mi, Function.update_of_ne h1, Function.update_of_ne h2], fun d _ => rfl⟩ _ _
    have hpj₁ : (c₁.inputPos j : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_of_ne hjr,
        Function.update_self]
      rw [moveInputPos_val_one (c.inputPos j) (by omega), hpj]
    have hpr₁ : (c₁.inputPos ref : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_self]
      rw [moveInputPos_val_one (c.inputPos ref) (by omega), hpr]
    obtain ⟨c', hr, hst, hu', hpj', hpr'⟩ := ih c₁ (q + 1) (by simp [hc₁]) hpj₁ hpr₁ (by omega) (by omega)
    exact ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), hpj', hpr'⟩

/-- `checkLen` halts when `j` is longer than `ref`. -/
theorem exec_checkLen_fail {k : ProgId} {pc : Fin maxPc} {j ref : IT}
    (hins : instrAt k pc = .checkLen j ref) (hjr : j ≠ ref) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (c.inputPos ref : ℕ) = q + 1 → (input ref).length = q + m → q + m < (input j).length →
    HaltsIn c (m + 1) := by
  induction m with
  | zero =>
    intro c q hq hpj hpr hlen hlt
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_of_lt c j hpj (by omega), inputSymbol_end c ref (by omega),
      Act.base_out, Option.toList_none, Act.base_next, resolve_halt] at h
    exact HaltsIn.of_reach h rfl
  | succ m ih =>
    intro c q hq hpj hpr hlen hlt
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_of_lt c j hpj (by omega), inputSymbol_of_lt c ref hpr (by omega),
      Act.mi_out, Act.base_out, Option.toList_none, Act.mi_next, Act.base_next, resolve_stay] at h
    set c₁ := applyAct (((Act.base (.stay p0)).mi j 1).mi ref 1) (some ⟨k, pc, p0⟩) c with hc₁
    have hpj₁ : (c₁.inputPos j : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_of_ne hjr,
        Function.update_self]
      rw [moveInputPos_val_one (c.inputPos j) (by omega), hpj]
    have hpr₁ : (c₁.inputPos ref : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_self]
      rw [moveInputPos_val_one (c.inputPos ref) (by omega), hpr]
    have := ih c₁ (q + 1) (by simp [hc₁]) hpj₁ hpr₁ (by omega) (by omega)
    unfold HaltsIn at this ⊢
    rw [show m + 1 + 1 = 1 + (m + 1) by omega, configs_add, h.1]
    exact this

/-! ## `buildAnswer` -/

/-- The bit of an input symbol. -/
def boolOf : Sym → Bool
  | .one => true
  | _ => false

/-- The written form of an answer suffix: `S(encode (l.map boolOf))`. -/
def answerBits (l : List Sym) : List Sym := S (Data.ofList Data.ofBool (l.map boolOf))

theorem answerBits_nil : answerBits [] = [.zero] := rfl

theorem answerBits_zero (l : List Sym) : answerBits (.zero :: l) = .one :: .zero :: answerBits l := by
  simp [answerBits, Data.ofList, boolOf, Data.ofBool, S_cons]

theorem answerBits_one (l : List Sym) :
    answerBits (.one :: l) = .one :: .one :: .zero :: .zero :: answerBits l := by
  simp [answerBits, Data.ofList, boolOf, Data.ofBool, S_cons]

/-- From position `q + 1` of a bit input `j`: `S(encode)` of the remaining bits. -/
theorem exec_buildAnswer {k : ProgId} {pc : Fin maxPc} {j : IT} {dst : WT}
    (hins : instrAt k pc = .buildAnswer j dst) (hpc : pc.val + 1 < maxPc)
    (hbits : ∀ s ∈ input j, s = .zero ∨ s = .one) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (input j).length = q + m →
    ∃ n ≤ 4 * m + 1, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j] [dst] ∧
      (c'.inputPos j : ℕ) = (input j).length + 1 ∧ WEff dst c c' (answerBits ((input j).drop q)) := by
  induction m with
  | zero =>
    intro c q hq hpos hlen
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_end c j (by omega), Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next] at h
    refine ⟨1, by omega, _, h, by simp [resolve_adv k pc hpc], ?_, by simp; omega, ?_⟩
    · exact untouched_applyAct ⟨fun _ _ => rfl, fun d hd => by
        have : d ≠ dst := by simpa using hd
        simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
    · rw [List.drop_of_length_le (by omega), answerBits_nil]
      exact WEff.single (by rw [applyAct_workTapes_of_some _ _ _ dst (s := some .zero) (by simp)])
        (by simp)
  | succ m ih =>
    intro c q hq hpos hlen
    have hmem : (input j)[q] ∈ input j := List.getElem_mem (by omega)
    -- a helper: a write step at phase `ph` moving to phase `ph'`, with or without an input move
    have wstep : ∀ (c₀ : Cfg input) (ph ph' : Phase) (s : Sym) (mv : Bool),
        c₀.state = some ⟨k, pc, ph⟩ →
        execInstr (.buildAnswer j dst) ph c₀.inputSymbols c₀.workTapeSymbols =
          (if mv then (((Act.base (.stay ph')).ww dst (some s)).mw dst 1).mi j 1
            else ((Act.base (.stay ph')).ww dst (some s)).mw dst 1) →
        ∃ c₁, Reach c₀ 1 c₁ [] ∧ c₁.state = some ⟨k, pc, ph'⟩ ∧ Untouched c₀ c₁ [j] [dst] ∧
          WEff dst c₀ c₁ [s] ∧
          c₁.inputPos j = moveInputPos (c₀.inputPos j) (if mv then 1 else 0) := by
      intro c₀ ph ph' s mv hq₀ hact
      have h := step_instr hq₀ hins
      rw [hact] at h
      cases mv
      · simp only [if_false, Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none,
          Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h
        refine ⟨_, h, rfl, ?_, WEff.single ?_ (by simp), ?_⟩
        · exact untouched_applyAct ⟨fun _ _ => rfl, fun d hd => by
            have : d ≠ dst := by simpa using hd
            simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
        · rw [applyAct_workTapes_of_some _ _ _ dst (s := some s) (by simp)]
        · simp
      · simp only [if_true, Act.mi_out, Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none,
          Act.mi_next, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h
        refine ⟨_, h, rfl, ?_, WEff.single ?_ (by simp), ?_⟩
        · exact untouched_applyAct ⟨fun j' hj => by
            have : j' ≠ j := by simpa using hj
            simp [Act.mi, Function.update_of_ne this], fun d hd => by
            have : d ≠ dst := by simpa using hd
            simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
        · rw [applyAct_workTapes_of_some _ _ _ dst (s := some s) (by simp)]
        · simp [Act.mi]
    rcases hbits _ hmem with h0 | h1
    · -- a `0`: write `1 0`
      obtain ⟨c₁, hr₁, hs₁, hu₁, hw₁, hp₁⟩ := wstep c p0 p1 .one false hq (by
        simp only [execInstr, inputSymbol_of_lt c j hpos (by omega), h0]; rfl)
      have hpos₁ : (c₁.inputPos j : ℕ) = q + 1 := by rw [hp₁]; simp [hpos]
      obtain ⟨c₂, hr₂, hs₂, hu₂, hw₂, hp₂⟩ := wstep c₁ p1 p0 .zero true hs₁ (by
        simp only [execInstr]; rfl)
      have hpos₂ : (c₂.inputPos j : ℕ) = (q + 1) + 1 := by
        rw [hp₂]; simp only [if_true]; rw [moveInputPos_val_one (c₁.inputPos j) (by omega), hpos₁]
      obtain ⟨n, hn, c', hr, hst, hu', hpos', hw'⟩ := ih c₂ (q + 1) hs₂ hpos₂ (by omega)
      refine ⟨n + 2, by omega, c', ?_, hst, ?_, hpos', ?_⟩
      · exact (((hr₁.trans hr₂).trans hr).cast_n (by omega)).cast_out (by simp)
      · exact ((hu₁.trans hu₂).trans hu').mono (by simp) (by simp)
      · rw [List.drop_eq_getElem_cons (by omega), h0, answerBits_zero]
        exact ((hw₁.trans hw₂).trans hw').cast (by simp)
    · -- a `1`: write `1 1 0 0`
      obtain ⟨c₁, hr₁, hs₁, hu₁, hw₁, hp₁⟩ := wstep c p0 p2 .one false hq (by
        simp only [execInstr, inputSymbol_of_lt c j hpos (by omega), h1]; rfl)
      have hpos₁ : (c₁.inputPos j : ℕ) = q + 1 := by rw [hp₁]; simp [hpos]
      obtain ⟨c₂, hr₂, hs₂, hu₂, hw₂, hp₂⟩ := wstep c₁ p2 p3 .one false hs₁ (by
        simp only [execInstr]; rfl)
      have hpos₂ : (c₂.inputPos j : ℕ) = q + 1 := by rw [hp₂]; simp [hpos₁]
      obtain ⟨c₃, hr₃, hs₃, hu₃, hw₃, hp₃⟩ := wstep c₂ p3 p4 .zero false hs₂ (by
        simp only [execInstr]; rfl)
      have hpos₃ : (c₃.inputPos j : ℕ) = q + 1 := by rw [hp₃]; simp [hpos₂]
      obtain ⟨c₄, hr₄, hs₄, hu₄, hw₄, hp₄⟩ := wstep c₃ p4 p0 .zero true hs₃ (by
        simp only [execInstr]; rfl)
      have hpos₄ : (c₄.inputPos j : ℕ) = (q + 1) + 1 := by
        rw [hp₄]; simp only [if_true]; rw [moveInputPos_val_one (c₃.inputPos j) (by omega), hpos₃]
      obtain ⟨n, hn, c', hr, hst, hu', hpos', hw'⟩ := ih c₄ (q + 1) hs₄ hpos₄ (by omega)
      refine ⟨n + 4, by omega, c', ?_, hst, ?_, hpos', ?_⟩
      · exact (((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr).cast_n (by omega)).cast_out
          (by simp)
      · exact ((((hu₁.trans hu₂).trans hu₃).trans hu₄).trans hu').mono (by simp) (by simp)
      · rw [List.drop_eq_getElem_cons (by omega), h1, answerBits_one]
        exact ((((hw₁.trans hw₂).trans hw₃).trans hw₄).trans hw').cast (by simp)

end MIPRE.TM.Interp
