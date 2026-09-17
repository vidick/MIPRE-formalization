/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.CopyTree

/-!
# The `getEnv` routine

With the unary index `S(ofNat i)` under the head of `C` and the environment `envRepr env` on
`E` with its head at the end, `getEnv` writes `S(env.get i)` at the head of `X`: it walks
left over `i` separators (phases `p1`–`p3`), then to the start of the element (`p4`), copies
it (`p5`) and returns the head of `E` to the end (`p8`); past the start of the environment
the index is out of range, the rest of it is consumed (`p6`, `p7`) and `nil` is written
(`p9`). The proof is by induction on the index, over the suffix of the environment not yet
passed.
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost

variable {input : Fin 7 → List Sym}

/-- The unary index `S(ofNat i)`: `(1 0)^i 0`. -/
theorem S_ofNat_succ (i : ℕ) : S (Data.ofNat (i + 1)) = .one :: .zero :: S (Data.ofNat i) := by
  simp [Data.ofNat, S_cons]

theorem length_S_ofNat (i : ℕ) : (S (Data.ofNat i)).length = 2 * i + 1 := by simp

/-- The environment representation of a suffix is a prefix of the whole. -/
theorem envRepr_drop_prefix (env : Env) (j : ℕ) :
    ∃ l, envRepr env = envRepr (env.drop j) ++ l := by
  induction j generalizing env with
  | zero => exact ⟨[], by simp⟩
  | succ j ih =>
    cases env with
    | nil => exact ⟨[], by simp⟩
    | cons v env =>
      obtain ⟨l, hl⟩ := ih env
      exact ⟨l ++ S v ++ [.sep], by simp only [List.drop_succ_cons, envRepr_cons, hl]; simp⟩

/-- The last symbol of a nonempty environment is `#`. -/
theorem envRepr_getLast (v : Data) (rest : Env) :
    envRepr (v :: rest) = envRepr rest ++ S v ++ [.sep] := rfl

/-- A tape holding the environment from `0`, blank before. -/
structure EnvTape (τ : Tape) (env : Env) : Prop where
  holds : Holds τ 0 (envRepr env)
  before : BlankBefore τ 0
  beyond : BlankBeyond τ (envRepr env).length

theorem EnvTape.cell_of_lt {τ : Tape} {env : Env} (h : EnvTape τ env) {k : ℕ}
    (hk : k < (envRepr env).length) : τ k = some (envRepr env)[k] := by
  simpa using h.holds k hk

theorem EnvTape.cell_neg {τ : Tape} {env : Env} (h : EnvTape τ env) {q : ℤ} (hq : q < 0) :
    τ q = none := h.before q hq

/-! ## The scans -/

/-- Phase `p3`: over the bits `l` held on `p₀ … p₀ + |l| - 1`, from the last, to `p₀ - 1`. -/
theorem getEnv_scan3 {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv) (l : List Sym)
    (hl : ∀ s ∈ l, s = .zero ∨ s = .one) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p3⟩ →
      Holds (c.workTapes E) (c.workTapePos E + 1 - l.length) l →
    ∃ c', Reach c l.length c' [] ∧ c'.state = some ⟨k, pc, p3⟩ ∧ Untouched c c' [] [E] ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = c.workTapePos E - l.length := by
  induction l using List.reverseRecOn with
  | nil =>
    intro c hq _
    exact ⟨c, Reach.refl c, hq, Untouched.refl c _ _, rfl, by simp⟩
  | append_singleton l a ih =>
    intro c hq hhold
    have hlen : ((l ++ [a]).length : ℤ) = l.length + 1 := by simp
    have ha : c.workTapes E (c.workTapePos E) = some a := by
      have := hhold.of_append_right
      rw [Holds.singleton_iff] at this
      convert this using 2
      rw [hlen]; ring
    have h := step_instr hq hins
    have hact : execInstr .getEnv p3 c.inputSymbols c.workTapeSymbols =
        (Act.base (.stay p3)).mw E (-1) := by
      simp only [execInstr, workTapeSymbols_eq, ha]
      rcases hl a (by simp) with rfl | rfl <;> rfl
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p3)).mw E (-1)) (some ⟨k, pc, p3⟩) c with hc₁
    have hu : Untouched c c₁ [] [E] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ E := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes E = c.workTapes E := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp)]
    have hpos : c₁.workTapePos E = c.workTapePos E - 1 := by simp [hc₁]; ring
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih (fun s hs => hl s (by simp [hs])) c₁
      (by simp [hc₁]) (by
        rw [htape, hpos]
        have := hhold.of_append_left
        convert this using 1
        rw [hlen]; ring)
    refine ⟨c', ((h.trans hr).cast_n (by simp; omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), htape'.trans htape, ?_⟩
    rw [hpos', hpos, hlen]; ring

/-- Phase `p4`: over the bits `l`, from the last, to `p₀ - 1`, then one right to `p₀` at `p5`. -/
theorem getEnv_scan4 {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv) (l : List Sym)
    (hl : ∀ s ∈ l, s = .zero ∨ s = .one) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p4⟩ →
      Holds (c.workTapes E) (c.workTapePos E + 1 - l.length) l →
      (c.workTapes E (c.workTapePos E - l.length) = some .sep ∨
        c.workTapes E (c.workTapePos E - l.length) = none) →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = some ⟨k, pc, p5⟩ ∧ Untouched c c' [] [E] ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = c.workTapePos E - l.length + 1 := by
  induction l using List.reverseRecOn with
  | nil =>
    intro c hq _ hend
    have h := step_instr hq hins
    simp only [List.length_nil, Nat.cast_zero, sub_zero] at hend
    have hact : execInstr .getEnv p4 c.inputSymbols c.workTapeSymbols =
        (Act.base (.stay p5)).mw E 1 := by
      simp only [execInstr, workTapeSymbols_eq]
      rcases hend with h1 | h1 <;> rw [h1]
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    refine ⟨_, h, rfl, ?_, ?_, ?_⟩
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ E := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    · rw [applyAct_workTapes_of_none _ _ _ E (by simp)]
    · simp
  | append_singleton l a ih =>
    intro c hq hhold hend
    have hlen : ((l ++ [a]).length : ℤ) = l.length + 1 := by simp
    have ha : c.workTapes E (c.workTapePos E) = some a := by
      have := hhold.of_append_right
      rw [Holds.singleton_iff] at this
      convert this using 2
      rw [hlen]; ring
    have h := step_instr hq hins
    have hact : execInstr .getEnv p4 c.inputSymbols c.workTapeSymbols =
        (Act.base (.stay p4)).mw E (-1) := by
      simp only [execInstr, workTapeSymbols_eq, ha]
      rcases hl a (by simp) with rfl | rfl <;> rfl
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p4)).mw E (-1)) (some ⟨k, pc, p4⟩) c with hc₁
    have hu : Untouched c c₁ [] [E] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ E := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes E = c.workTapes E := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp)]
    have hpos : c₁.workTapePos E = c.workTapePos E - 1 := by simp [hc₁]; ring
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih (fun s hs => hl s (by simp [hs])) c₁
      (by simp [hc₁]) (by
        rw [htape, hpos]
        have := hhold.of_append_left
        convert this using 1
        rw [hlen]; ring)
      (by rw [htape, hpos]; convert hend using 3 <;> (rw [hlen]; ring))
    refine ⟨c', ((h.trans hr).cast_n (by simp; omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), htape'.trans htape, ?_⟩
    rw [hpos', hpos, hlen]; ring

/-- Phase `p5`: copy the bits `l` under the head of `E` to `X`, to the `#` after them. -/
theorem getEnv_copy5 {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv) (l : List Sym)
    (hl : ∀ s ∈ l, s = .zero ∨ s = .one) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p5⟩ →
      Holds (c.workTapes E) (c.workTapePos E) l →
      c.workTapes E (c.workTapePos E + l.length) = some .sep →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = some ⟨k, pc, p8⟩ ∧ Untouched c c' [] [E, X] ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = c.workTapePos E + l.length ∧
      DstEff X c c' l := by
  induction l with
  | nil =>
    intro c hq _ hend
    have h := step_instr hq hins
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    simp only [execInstr, workTapeSymbols_eq, hend, Act.base_out, Option.toList_none,
      Act.base_next, resolve_stay] at h
    refine ⟨_, h, rfl, untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _, ?_, by simp,
      DstEff.nil ?_ (by simp)⟩
    · rw [applyAct_workTapes_of_none _ _ _ E (by simp)]
    · rw [applyAct_workTapes_of_none _ _ _ X (by simp)]
  | cons s l ih =>
    intro c hq hhold hend
    have hs := hhold.head
    have h := step_instr hq hins
    have hact : execInstr .getEnv p5 c.inputSymbols c.workTapeSymbols =
        (((Act.base (.stay p5)).ww X (some s)).mw X 1).mw E 1 := by
      simp only [execInstr, workTapeSymbols_eq, hs]
      rcases hl s (by simp) with rfl | rfl <;> rfl
    rw [hact] at h
    simp only [Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next, Act.ww_next,
      Act.base_next, resolve_stay] at h
    set c₁ := applyAct ((((Act.base (.stay p5)).ww X (some s)).mw X 1).mw E 1) (some ⟨k, pc, p5⟩) c
      with hc₁
    have hEX : E ≠ X := by decide
    have hu : Untouched c c₁ [] [E, X] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ E := fun e => hd (by simp [e])
        have h2 : d ≠ X := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2]⟩ _ _
    have htape : c₁.workTapes E = c.workTapes E := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp [Act.mw_works_of_ne _ hEX,
        Act.ww_works_of_ne _ hEX])]
    have hpos : c₁.workTapePos E = c.workTapePos E + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hEX, Act.ww_works_of_ne _ hEX]
    have hde : DstEff X c c₁ [s] := DstEff.single
      (by rw [hc₁, applyAct_workTapes_of_some _ _ _ X (s := some s) (by simp [Act.mw_works_of_ne _ hEX.symm])])
      (by simp [hc₁, Act.mw_works_of_ne _ hEX.symm])
    obtain ⟨c', hr, hst, hu', htape', hpos', hde'⟩ := ih (fun s' hs' => hl s' (by simp [hs'])) c₁
      (by simp [hc₁]) (by rw [htape, hpos]; exact hhold.tail)
      (by
        rw [htape, hpos]
        simp only [List.length_cons] at hend
        convert hend using 2
        push_cast; ring)
    refine ⟨c', ((h.trans hr).cast_n (by simp only [List.length_cons]; omega)).cast_out
      (List.nil_append _), hst, (hu.trans hu').mono (by simp) (by simp), htape'.trans htape, ?_, ?_⟩
    · rw [hpos', hpos]; simp only [List.length_cons]; push_cast; ring
    · exact (hde.trans hde').cast (by simp)

/-- Phases `p8`/`p9`: the head of `E` right to the first blank. -/
theorem getEnv_toEnd {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv)
    (hpc : pc.val + 1 < maxPc) (ph : Phase) (hph : ph = p8 ∨ ph = p9) (l : List Sym) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, ph⟩ → Holds (c.workTapes E) (c.workTapePos E) l →
      c.workTapes E (c.workTapePos E + l.length) = none →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [E] ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = c.workTapePos E + l.length := by
  induction l with
  | nil =>
    intro c hq _ hend
    have h := step_instr hq hins
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hend
    have hact : execInstr .getEnv ph c.inputSymbols c.workTapeSymbols = Act.base .adv := by
      rcases hph with rfl | rfl <;> simp [execInstr, workTapeSymbols_eq, hend]
    rw [hact] at h
    simp only [Act.base_out, Option.toList_none, Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _, ?_, by simp⟩
    rw [applyAct_workTapes_of_none _ _ _ E (by simp)]
  | cons s l ih =>
    intro c hq hhold hend
    have hs := hhold.head
    have h := step_instr hq hins
    have hact : execInstr .getEnv ph c.inputSymbols c.workTapeSymbols =
        (Act.base (.stay ph)).mw E 1 := by
      rcases hph with rfl | rfl <;> simp [execInstr, workTapeSymbols_eq, hs]
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay ph)).mw E 1) (some ⟨k, pc, ph⟩) c with hc₁
    have hu : Untouched c c₁ [] [E] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ E := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes E = c.workTapes E := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp)]
    have hpos : c₁.workTapePos E = c.workTapePos E + 1 := by simp [hc₁]
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih c₁ (by simp [hc₁])
      (by rw [htape, hpos]; exact hhold.tail)
      (by
        rw [htape, hpos]
        simp only [List.length_cons] at hend
        convert hend using 2
        push_cast; ring)
    refine ⟨c', ((h.trans hr).cast_n (by simp only [List.length_cons]; omega)).cast_out
      (List.nil_append _), hst, (hu.trans hu').mono (by simp) (by simp), htape'.trans htape, ?_⟩
    rw [hpos', hpos]; simp only [List.length_cons]; push_cast; ring

/-- Phases `p6`/`p7`: consume the index `S(ofNat j)` on `C`, then write `nil` on `X` and move
`E` one right, at `p9`. -/
theorem getEnv_consume {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv) (j : ℕ) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p6⟩ →
      Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat j)) →
    ∃ c', Reach c (2 * j + 1) c' [] ∧ c'.state = some ⟨k, pc, p9⟩ ∧ Untouched c c' [] [C, E, X] ∧
      c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * j + 1 : ℕ) ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = c.workTapePos E + 1 ∧
      DstEff X c c' [.zero] := by
  have hCE : C ≠ E := by decide
  have hCX : C ≠ X := by decide
  have hEX : E ≠ X := by decide
  induction j with
  | zero =>
    intro c hq hhold
    have hs : c.workTapes C (c.workTapePos C) = some .zero := by simpa using hhold.head
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hs, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h
    refine ⟨_, h, rfl, ?_, ?_, ?_, ?_, ?_, DstEff.single ?_ ?_⟩
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ C := fun e => hd (by simp [e])
        have h2 : d ≠ E := fun e => hd (by simp [e])
        have h3 : d ≠ X := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.ww_works_of_ne _ h3]⟩ _ _
    · rw [applyAct_workTapes_of_none _ _ _ C (by simp [Act.mw_works_of_ne _ hCE,
        Act.mw_works_of_ne _ hCX, Act.ww_works_of_ne _ hCX])]
    · simp [Act.mw_works_of_ne _ hCE, Act.mw_works_of_ne _ hCX, Act.ww_works_of_ne _ hCX]
    · rw [applyAct_workTapes_of_none _ _ _ E (by simp [Act.mw_works_of_ne _ hEX,
        Act.ww_works_of_ne _ hEX, Act.mw_works_of_ne _ hCE.symm])]
    · simp [Act.mw_works_of_ne _ hEX, Act.ww_works_of_ne _ hEX, Act.mw_works_of_ne _ hCE.symm]
    · rw [applyAct_workTapes_of_some _ _ _ X (s := some .zero) (by simp [Act.mw_works_of_ne _ hEX.symm])]
    · simp [Act.mw_works_of_ne _ hEX.symm]
  | succ j ih =>
    intro c hq hhold
    rw [S_ofNat_succ] at hhold
    have hs : c.workTapes C (c.workTapePos C) = some .one := hhold.head
    have h := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hs, Act.mw_out, Act.base_out, Option.toList_none,
      Act.mw_next, Act.base_next, resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p7)).mw C 1) (some ⟨k, pc, p7⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [C] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ C := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have hC₁ : c₁.workTapes C = c.workTapes C := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ C (by simp)]
    have hCp₁ : c₁.workTapePos C = c.workTapePos C + 1 := by simp [hc₁]
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p7) (by simp [hc₁]) hins
    simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h2
    set c₂ := applyAct ((Act.base (.stay p6)).mw C 1) (some ⟨k, pc, p6⟩) c₁ with hc₂
    have hu₂ : Untouched c₁ c₂ [] [C] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ C := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have hC₂ : c₂.workTapes C = c.workTapes C := by
      rw [hc₂, applyAct_workTapes_of_none _ _ _ C (by simp), hC₁]
    have hCp₂ : c₂.workTapePos C = c.workTapePos C + 2 := by simp [hc₂, hCp₁]; ring
    obtain ⟨c', hr, hst, hu', hC', hCp', hE', hEp', hde⟩ := ih c₂ (by simp [hc₂])
      (by rw [hC₂, hCp₂]; convert hhold.tail.tail using 1; ring)
    refine ⟨c', (((h.trans h2).trans hr).cast_n (by omega)).cast_out (by simp), hst,
      ((hu₁.trans hu₂).trans hu').mono (by simp) (by simp), hC'.trans hC₂, ?_, ?_, ?_, ?_⟩
    · rw [hCp', hCp₂]; push_cast; ring
    · rw [hE', hu₂.tapes (d := E) (by decide), hu₁.tapes (d := E) (by decide)]
    · rw [hEp', hu₂.pos (d := E) (by decide), hu₁.pos (d := E) (by decide)]
    · refine ⟨?_, ?_, ?_⟩
      · rw [← hu₁.pos (d := X) (by decide), ← hu₂.pos (d := X) (by decide)]; exact hde.holds
      · intro q hq'
        rw [hde.outside q (by rw [hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]; exact hq'),
          hu₂.tapes (d := X) (by decide), hu₁.tapes (d := X) (by decide)]
      · rw [hde.pos, hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]

/-! ## The walk -/

/-- Cells of a suffix of the environment: for `env' = v :: rest` a prefix of `env`, `S v` sits
at `|envRepr rest|`, followed by `#`, and preceded by `#` or the blank before the tape. -/
theorem EnvTape.suffix_cells {τ : Tape} {env : Env} (h : EnvTape τ env) (v : Data) (rest : Env)
    {l₀ : List Sym} (hpre : envRepr env = envRepr (v :: rest) ++ l₀) :
    Holds τ (envRepr rest).length (S v) ∧
    τ ((envRepr rest).length + (S v).length) = some .sep ∧
    (τ ((envRepr rest).length - 1) = some .sep ∨ τ ((envRepr rest).length - 1) = none) := by
  have hh := h.holds
  rw [hpre, envRepr_cons] at hh
  have h1 := hh.of_append_left
  have h2 := h1.of_append_right
  have h3 := h1.of_append_left
  refine ⟨by simpa using h3.of_append_right, ?_, ?_⟩
  · rw [Holds.singleton_iff] at h2
    simpa [add_assoc] using h2
  · cases rest with
    | nil => right; exact h.before _ (by simp)
    | cons w rest' =>
      left
      have h4 := h3.of_append_left
      rw [envRepr_cons] at h4
      have h5 := h4.of_append_right
      rw [Holds.singleton_iff] at h5
      convert h5 using 2
      simp [envRepr_cons]; ring

/-- The cells from `q` to the end of the environment. -/
theorem EnvTape.tail_cells {τ : Tape} {env : Env} (h : EnvTape τ env) (q : ℕ)
    (hq : q ≤ (envRepr env).length) :
    Holds τ q ((envRepr env).drop q) ∧ τ (q + ((envRepr env).drop q).length) = none := by
  refine ⟨?_, ?_⟩
  · have := h.holds
    rw [← List.take_append_drop q (envRepr env)] at this
    have h2 := this.of_append_right
    simpa [List.length_take, hq] using h2
  · apply h.beyond
    simp [List.length_drop]; omega

theorem Env.get_nil' (j : ℕ) : Env.get [] j = .nil := by simp

/-- The walk from phase `p1`: at the separator of the last element of the suffix `env'` of
`env` (or before the tape if `env'` is empty), with the index `S(ofNat j)` on `C`. -/
theorem getEnv_walk {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv)
    (hpc : pc.val + 1 < maxPc) (env : Env) (j : ℕ) :
    ∀ (env' : Env) (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
      EnvTape (c.workTapes E) env → (∃ l₀, envRepr env = envRepr env' ++ l₀) →
      c.workTapePos E = (envRepr env').length - 1 →
      Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat j)) →
    ∃ n ≤ 3 * j + 2 * (envRepr env).length + (envRepr env').length + 8,
    ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [C, E, X] ∧
      c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * j + 1 : ℕ) ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = (envRepr env).length ∧
      DstEff X c c' (S (Env.get env' j)) := by
  have hCE : C ≠ E := by decide
  have hCX : C ≠ X := by decide
  have hEX : E ≠ X := by decide
  -- the out-of-range exit from `p6`: consume the index, write `nil`, move to the end
  have exit6 : ∀ (j : ℕ) (c : Cfg input), c.state = some ⟨k, pc, p6⟩ →
      EnvTape (c.workTapes E) env →
      c.workTapePos E = -1 → Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat j)) →
      ∃ c', Reach c (2 * j + 1 + ((envRepr env).length + 1)) c' [] ∧ c'.state = next_ k pc hpc ∧
        Untouched c c' [] [C, E, X] ∧
        c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * j + 1 : ℕ) ∧
        c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = (envRepr env).length ∧
        DstEff X c c' [.zero] := by
    intro j c hq hE hpos hC
    obtain ⟨c₁, hr₁, hs₁, hu₁, hC₁, hCp₁, hE₁, hEp₁, hde₁⟩ := getEnv_consume hins j c hq hC
    have hE₁' : EnvTape (c₁.workTapes E) env := by rw [hE₁]; exact hE
    obtain ⟨hhold, hend⟩ := hE₁'.tail_cells 0 (by omega)
    obtain ⟨c₂, hr₂, hs₂, hu₂, hE₂, hEp₂⟩ := getEnv_toEnd hins hpc p9 (Or.inr rfl) _ c₁ hs₁
      (by rw [hEp₁, hpos]; simpa using hhold) (by rw [hEp₁, hpos]; simpa using hend)
    refine ⟨c₂, ((hr₁.trans hr₂).cast_n (by simp)).cast_out (by simp), hs₂,
      (hu₁.trans hu₂).mono (by simp) (by simp), ?_, ?_, hE₂.trans hE₁, ?_, ?_⟩
    · rw [hu₂.tapes (d := C) (by decide), hC₁]
    · rw [hu₂.pos (d := C) (by decide), hCp₁]
    · rw [hEp₂, hEp₁, hpos]; simp
    · refine ⟨?_, ?_, ?_⟩
      · rw [hu₂.tapes (d := X) (by decide)]; exact hde₁.holds
      · intro q hq'; rw [hu₂.tapes (d := X) (by decide)]; exact hde₁.outside q hq'
      · rw [hu₂.pos (d := X) (by decide)]; exact hde₁.pos
  induction j with
  | zero =>
    intro env' c hq hE hpre hpos hC
    cases env' with
    | nil =>
      -- before the tape: out of range
      simp only [envRepr_nil, List.length_nil, Nat.cast_zero, zero_sub] at hpos
      have hread : c.workTapes E (c.workTapePos E) = none := by rw [hpos]; exact hE.before _ (by norm_num)
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, Act.base_out, Option.toList_none, Act.base_next,
        resolve_stay] at h
      set c₁ := applyAct (Act.base (.stay p6)) (some ⟨k, pc, p6⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
      obtain ⟨c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := exit6 _ c₁ (by simp [hc₁])
        (by rw [hu₁.tapes (d := E) (by simp)]; exact hE) (by rw [hu₁.pos (d := E) (by simp)]; exact hpos)
        (by rw [hu₁.tapes (d := C) (by simp), hu₁.pos (d := C) (by simp)]; exact hC)
      refine ⟨_, by simp; omega, c', ((h.trans hr).cast_n rfl).cast_out (by simp), hs,
        (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, ?_, hEp', ?_⟩
      · rw [hC', hu₁.tapes (d := C) (by simp)]
      · rw [hCp', hu₁.pos (d := C) (by simp)]
      · rw [hE', hu₁.tapes (d := E) (by simp)]
      · rw [Env.get_nil', S_nil]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hu₁.pos (d := X) (by simp)]; exact hde.holds
        · intro q hq'
          rw [hde.outside q (by rw [hu₁.pos (d := X) (by simp)]; exact hq'), hu₁.tapes (d := X) (by simp)]
        · rw [hde.pos, hu₁.pos (d := X) (by simp)]
    | cons v rest =>
      obtain ⟨l₀, hpre⟩ := hpre
      obtain ⟨hSv, hsep, hbefore⟩ := hE.suffix_cells v rest hpre
      have hposv : c.workTapePos E = (envRepr rest).length + (S v).length := by
        rw [hpos, envRepr_cons]; simp; ring
      have hread : c.workTapes E (c.workTapePos E) = some .sep := by rw [hposv]; exact hsep
      have hCread : c.workTapes C (c.workTapePos C) = some .zero := by simpa using hC.head
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, hCread, Act.mw_out, Act.base_out,
        Option.toList_none, Act.mw_next, Act.base_next, resolve_stay] at h
      set c₁ := applyAct (((Act.base (.stay p4)).mw C 1).mw E (-1)) (some ⟨k, pc, p4⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [C, E] :=
        untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
          have h1 : d ≠ C := fun e => hd (by simp [e])
          have h2 : d ≠ E := fun e => hd (by simp [e])
          simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2]⟩ _ _
      have hC₁ : c₁.workTapes C = c.workTapes C := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ C (by simp [Act.mw_works_of_ne _ hCE])]
      have hCp₁ : c₁.workTapePos C = c.workTapePos C + 1 := by simp [hc₁, Act.mw_works_of_ne _ hCE]
      have hE₁ : c₁.workTapes E = c.workTapes E := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp [Act.mw_works_of_ne _ hCE.symm])]
      have hEp₁ : c₁.workTapePos E = (envRepr rest).length + (S v).length - 1 := by
        simp [hc₁, hposv]; ring
      -- to the start of `S v`
      obtain ⟨c₂, hr₂, hs₂, hu₂, hE₂, hEp₂⟩ := getEnv_scan4 hins (S v) (mem_S v) c₁ (by simp [hc₁])
        (by rw [hE₁, hEp₁]; convert hSv using 1; ring)
        (by rw [hE₁, hEp₁]; convert hbefore using 3 <;> ring)
      have hEp₂' : c₂.workTapePos E = (envRepr rest).length := by rw [hEp₂, hEp₁]; ring
      -- copy it
      obtain ⟨c₃, hr₃, hs₃, hu₃, hE₃, hEp₃, hde₃⟩ := getEnv_copy5 hins (S v) (mem_S v) c₂ hs₂
        (by rw [hE₂, hE₁, hEp₂']; exact hSv) (by rw [hE₂, hE₁, hEp₂']; exact hsep)
      have hEp₃' : c₃.workTapePos E = (envRepr rest).length + (S v).length := by rw [hEp₃, hEp₂']
      -- to the end
      have hE₃' : EnvTape (c₃.workTapes E) env := by rw [hE₃, hE₂, hE₁]; exact hE
      have hqle : (envRepr rest).length + (S v).length ≤ (envRepr env).length := by
        rw [hpre, envRepr_cons]; simp
      obtain ⟨hhold, hend⟩ := hE₃'.tail_cells _ hqle
      obtain ⟨c₄, hr₄, hs₄, hu₄, hE₄, hEp₄⟩ := getEnv_toEnd hins hpc p8 (Or.inl rfl) _ c₃ hs₃
        (by rw [hEp₃']; exact_mod_cast hhold) (by rw [hEp₃']; exact_mod_cast hend)
      have hlen : (envRepr env).length = (envRepr rest).length + v.size + 1 + l₀.length := by
        rw [hpre, envRepr_cons]; simp; omega
      refine ⟨_, ?_, c₄, (((h.trans hr₂).trans hr₃).trans hr₄).cast_out (by simp), hs₄,
        (((hu₁.trans hu₂).trans hu₃).trans hu₄).mono (by simp) (by simp), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_drop, envRepr_cons, List.length_append, List.length_singleton, length_S]
        omega
      · rw [hu₄.tapes (d := C) (by decide), hu₃.tapes (d := C) (by decide),
          hu₂.tapes (d := C) (by decide), hC₁]
      · rw [hu₄.pos (d := C) (by decide), hu₃.pos (d := C) (by decide),
          hu₂.pos (d := C) (by decide), hCp₁]; simp
      · rw [hE₄, hE₃, hE₂, hE₁]
      · rw [hEp₄, hEp₃']; simp only [List.length_drop]; push_cast; omega
      · rw [Env.get_cons_zero]
        refine ⟨?_, ?_, ?_⟩
        · rw [hu₄.tapes (d := X) (by decide), ← hu₁.pos (d := X) (by decide),
            ← hu₂.pos (d := X) (by decide)]
          exact hde₃.holds
        · intro q hq'
          rw [hu₄.tapes (d := X) (by decide),
            hde₃.outside q (by rw [hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]; exact hq'),
            hu₂.tapes (d := X) (by decide), hu₁.tapes (d := X) (by decide)]
        · rw [hu₄.pos (d := X) (by decide), hde₃.pos, hu₂.pos (d := X) (by decide),
            hu₁.pos (d := X) (by decide)]
  | succ j ih =>
    intro env' c hq hE hpre hpos hC
    cases env' with
    | nil =>
      simp only [envRepr_nil, List.length_nil, Nat.cast_zero, zero_sub] at hpos
      have hread : c.workTapes E (c.workTapePos E) = none := by rw [hpos]; exact hE.before _ (by norm_num)
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, Act.base_out, Option.toList_none, Act.base_next,
        resolve_stay] at h
      set c₁ := applyAct (Act.base (.stay p6)) (some ⟨k, pc, p6⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
      obtain ⟨c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := exit6 _ c₁ (by simp [hc₁])
        (by rw [hu₁.tapes (d := E) (by simp)]; exact hE) (by rw [hu₁.pos (d := E) (by simp)]; exact hpos)
        (by rw [hu₁.tapes (d := C) (by simp), hu₁.pos (d := C) (by simp)]; exact hC)
      refine ⟨_, by simp; omega, c', ((h.trans hr).cast_n rfl).cast_out (by simp), hs,
        (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, ?_, hEp', ?_⟩
      · rw [hC', hu₁.tapes (d := C) (by simp)]
      · rw [hCp', hu₁.pos (d := C) (by simp)]
      · rw [hE', hu₁.tapes (d := E) (by simp)]
      · rw [Env.get_nil', S_nil]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hu₁.pos (d := X) (by simp)]; exact hde.holds
        · intro q hq'
          rw [hde.outside q (by rw [hu₁.pos (d := X) (by simp)]; exact hq'), hu₁.tapes (d := X) (by simp)]
        · rw [hde.pos, hu₁.pos (d := X) (by simp)]
    | cons v rest =>
      obtain ⟨l₀, hpre⟩ := hpre
      obtain ⟨hSv, hsep, hbefore⟩ := hE.suffix_cells v rest hpre
      have hposv : c.workTapePos E = (envRepr rest).length + (S v).length := by
        rw [hpos, envRepr_cons]; simp; ring
      have hread : c.workTapes E (c.workTapePos E) = some .sep := by rw [hposv]; exact hsep
      rw [S_ofNat_succ] at hC
      have hCread : c.workTapes C (c.workTapePos C) = some .one := hC.head
      -- the unit: `p1` then `p2`
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, hCread, Act.mw_out, Act.base_out,
        Option.toList_none, Act.mw_next, Act.base_next, resolve_stay] at h
      set c₁ := applyAct (((Act.base (.stay p2)).mw C 1).mw E (-1)) (some ⟨k, pc, p2⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [C, E] :=
        untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
          have h1 : d ≠ C := fun e => hd (by simp [e])
          have h2 : d ≠ E := fun e => hd (by simp [e])
          simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2]⟩ _ _
      have hC₁ : c₁.workTapes C = c.workTapes C := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ C (by simp [Act.mw_works_of_ne _ hCE])]
      have hCp₁ : c₁.workTapePos C = c.workTapePos C + 1 := by simp [hc₁, Act.mw_works_of_ne _ hCE]
      have hE₁ : c₁.workTapes E = c.workTapes E := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp [Act.mw_works_of_ne _ hCE.symm])]
      have hEp₁ : c₁.workTapePos E = (envRepr rest).length + (S v).length - 1 := by
        simp [hc₁, hposv]; ring
      have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p2) (by simp [hc₁]) hins
      simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
        resolve_stay] at h2
      set c₂ := applyAct ((Act.base (.stay p3)).mw C 1) (some ⟨k, pc, p3⟩) c₁ with hc₂
      have hu₂ : Untouched c₁ c₂ [] [C] :=
        untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
          have : d ≠ C := by simpa using hd
          simp [Act.mw_works_of_ne _ this]⟩ _ _
      have hC₂ : c₂.workTapes C = c.workTapes C := by
        rw [hc₂, applyAct_workTapes_of_none _ _ _ C (by simp), hC₁]
      have hCp₂ : c₂.workTapePos C = c.workTapePos C + 2 := by simp [hc₂, hCp₁]; ring
      have hE₂ : c₂.workTapes E = c.workTapes E := by rw [hu₂.tapes (d := E) (by decide), hE₁]
      have hEp₂ : c₂.workTapePos E = (envRepr rest).length + (S v).length - 1 := by
        rw [hu₂.pos (d := E) (by decide), hEp₁]
      -- over `S v` to the previous separator
      obtain ⟨c₃, hr₃, hs₃, hu₃, hE₃, hEp₃⟩ := getEnv_scan3 hins (S v) (mem_S v) c₂ (by simp [hc₂])
        (by rw [hE₂, hEp₂]; convert hSv using 1; ring)
      have hE₃' : c₃.workTapes E = c.workTapes E := by rw [hE₃, hE₂]
      have hEp₃' : c₃.workTapePos E = (envRepr rest).length - 1 := by rw [hEp₃, hEp₂]; ring
      have hC₃ : c₃.workTapes C = c.workTapes C := by rw [hu₃.tapes (d := C) (by decide), hC₂]
      have hCp₃ : c₃.workTapePos C = c.workTapePos C + 2 := by rw [hu₃.pos (d := C) (by decide), hCp₂]
      have hC₃' : Holds (c₃.workTapes C) (c₃.workTapePos C) (S (Data.ofNat j)) := by
        rw [hC₃, hCp₃]; convert hC.tail.tail using 1; ring
      have hlen : (envRepr env).length = (envRepr rest).length + v.size + 1 + l₀.length := by
        rw [hpre, envRepr_cons]; simp; omega
      -- the separator or the blank before the tape
      have h4 := step_instr (c := c₃) (k := k) (pc := pc) (ph := p3) hs₃ hins
      rcases hbefore with hb | hb
      · -- a separator: continue the walk at `p1`
        have hread₃ : c₃.workTapes E (c₃.workTapePos E) = some .sep := by rw [hE₃', hEp₃']; exact hb
        simp only [execInstr, workTapeSymbols_eq, hread₃, Act.base_out, Option.toList_none,
          Act.base_next, resolve_stay] at h4
        set c₄ := applyAct (Act.base (.stay p1)) (some ⟨k, pc, p1⟩) c₃ with hc₄
        have hu₄ : Untouched c₃ c₄ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
        obtain ⟨n, hn, c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := ih rest c₄ (by simp [hc₄])
          (by rw [hu₄.tapes (d := E) (by simp), hE₃']; exact hE)
          ⟨S v ++ [.sep] ++ l₀, by rw [hpre, envRepr_cons]; simp⟩
          (by rw [hu₄.pos (d := E) (by simp), hEp₃'])
          (by rw [hu₄.tapes (d := C) (by simp), hu₄.pos (d := C) (by simp)]; exact hC₃')
        refine ⟨1 + 1 + (S v).length + 1 + n, ?_, c', ?_, hs,
          ((((hu₁.trans hu₂).trans hu₃).trans hu₄).trans hu).mono (by simp) (by simp), ?_, ?_, ?_,
          hEp', ?_⟩
        · simp only [envRepr_cons, List.length_append, List.length_singleton] at hn ⊢; omega
        · exact ((((h.trans h2).trans hr₃).trans h4).trans hr).cast_out (by simp)
        · rw [hC', hu₄.tapes (d := C) (by simp), hC₃]
        · rw [hCp', hu₄.pos (d := C) (by simp), hCp₃]; push_cast; ring
        · rw [hE', hu₄.tapes (d := E) (by simp), hE₃']
        · rw [Env.get_cons_succ]
          have hXt : c₄.workTapes X = c.workTapes X := by
            rw [hu₄.tapes (d := X) (by simp), hu₃.tapes (d := X) (by decide),
              hu₂.tapes (d := X) (by decide), hu₁.tapes (d := X) (by decide)]
          have hXp : c₄.workTapePos X = c.workTapePos X := by
            rw [hu₄.pos (d := X) (by simp), hu₃.pos (d := X) (by decide),
              hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]
          refine ⟨?_, ?_, ?_⟩
          · rw [← hXp]; exact hde.holds
          · intro q hq'; rw [hde.outside q (by rw [hXp]; exact hq'), hXt]
          · rw [hde.pos, hXp]
      · -- the blank before the tape: out of range
        have hread₃ : c₃.workTapes E (c₃.workTapePos E) = none := by rw [hE₃', hEp₃']; exact hb
        simp only [execInstr, workTapeSymbols_eq, hread₃, Act.base_out, Option.toList_none,
          Act.base_next, resolve_stay] at h4
        set c₄ := applyAct (Act.base (.stay p6)) (some ⟨k, pc, p6⟩) c₃ with hc₄
        have hu₄ : Untouched c₃ c₄ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
        have hrest : rest = [] := by
          cases rest with
          | nil => rfl
          | cons w rest' =>
            exfalso
            have h6 : (envRepr (w :: rest')).length - 1 < (envRepr env).length := by
              rw [hpre]; simp only [envRepr_cons, List.length_append, List.length_singleton]; omega
            have h7 : 1 ≤ (envRepr (w :: rest')).length := by
              simp only [envRepr_cons, List.length_append, List.length_singleton]; omega
            have h8 := hE.holds ((envRepr (w :: rest')).length - 1) h6
            rw [zero_add, Nat.cast_sub h7, Nat.cast_one, hb] at h8
            exact absurd h8 (by simp)
        subst hrest
        obtain ⟨c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := exit6 j c₄ (by simp [hc₄])
          (by rw [hu₄.tapes (d := E) (by simp), hE₃']; exact hE)
          (by rw [hu₄.pos (d := E) (by simp), hEp₃']; simp)
          (by rw [hu₄.tapes (d := C) (by simp), hu₄.pos (d := C) (by simp)]; exact hC₃')
        refine ⟨_, ?_, c', ((((h.trans h2).trans hr₃).trans h4).trans hr).cast_out (by simp), hs,
          ((((hu₁.trans hu₂).trans hu₃).trans hu₄).trans hu).mono (by simp) (by simp), ?_, ?_, ?_,
          hEp', ?_⟩
        · simp only [envRepr_cons, envRepr_nil, List.nil_append, List.length_append,
            List.length_singleton] at hlen ⊢
          omega
        · rw [hC', hu₄.tapes (d := C) (by simp), hC₃]
        · rw [hCp', hu₄.pos (d := C) (by simp), hCp₃]; push_cast; ring
        · rw [hE', hu₄.tapes (d := E) (by simp), hE₃']
        · rw [Env.get_cons_succ, Env.get_nil', S_nil]
          have hXt : c₄.workTapes X = c.workTapes X := by
            rw [hu₄.tapes (d := X) (by simp), hu₃.tapes (d := X) (by decide),
              hu₂.tapes (d := X) (by decide), hu₁.tapes (d := X) (by decide)]
          have hXp : c₄.workTapePos X = c.workTapePos X := by
            rw [hu₄.pos (d := X) (by simp), hu₃.pos (d := X) (by decide),
              hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]
          refine ⟨?_, ?_, ?_⟩
          · rw [← hXp]; exact hde.holds
          · intro q hq'; rw [hde.outside q (by rw [hXp]; exact hq'), hXt]
          · rw [hde.pos, hXp]

/-- **`getEnv`**: with `S(ofNat i)` under the head of `C` and the environment on `E` with
its head at the end, write `S(env.get i)` at the head of `X`. -/
theorem exec_getEnv {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv)
    (hpc : pc.val + 1 < maxPc) (env : Env) (i : ℕ) (c : Cfg input) (hq : c.state = at_ k pc)
    (hE : EnvTape (c.workTapes E) env) (hpos : c.workTapePos E = (envRepr env).length)
    (hC : Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat i))) :
    ∃ n ≤ 3 * i + 3 * (envRepr env).length + 9,
    ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [C, E, X] ∧
      c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * i + 1 : ℕ) ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = (envRepr env).length ∧
      DstEff X c c' (S (Env.get env i)) := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw E (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu₁ : Untouched c c₁ [] [E] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ E := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _
  have hE₁ : c₁.workTapes E = c.workTapes E := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp)]
  have hEp₁ : c₁.workTapePos E = (envRepr env).length - 1 := by simp [hc₁, hpos]; ring
  obtain ⟨n, hn, c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := getEnv_walk hins hpc env i env c₁
    (by simp [hc₁]) (by rw [hE₁]; exact hE) ⟨[], by simp⟩ hEp₁
    (by rw [hu₁.tapes (d := C) (by decide), hu₁.pos (d := C) (by decide)]; exact hC)
  refine ⟨1 + n, by omega, c', (h.trans hr).cast_out (by simp), hs,
    (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, hE'.trans hE₁, hEp', ?_⟩
  · rw [hC', hu₁.tapes (d := C) (by decide)]
  · rw [hCp', hu₁.pos (d := C) (by decide)]
  · refine ⟨?_, ?_, ?_⟩
    · rw [← hu₁.pos (d := X) (by decide)]; exact hde.holds
    · intro q hq'
      rw [hde.outside q (by rw [hu₁.pos (d := X) (by decide)]; exact hq'), hu₁.tapes (d := X) (by decide)]
    · rw [hde.pos, hu₁.pos (d := X) (by decide)]

end MIPRE.TM.Interp
