/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Step
import MIPRE.TM.Interp.InputRoutines
import MIPRE.Foundations.Verifier

/-!
# The run of the interpreter

The inputs of `U` (`uInput`), the initialization (`init_run`), the simulation of a run of the
evaluation machine (`sim_run`), and the acceptance theorem: on the inputs
`(𝒟, n, T, x, y, a, b)` with `|a|, |b| ≤ T`, `U` accepts (halts having output `1`) iff `𝒟`
accepts `(n, x, y, a, b)` within cost `T`, and then within an explicit polynomial number of
steps.
-/

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)

/-! ## The inputs -/

/-- The seven inputs of `U`: the program, `n`, the budget `T` in unary, `x`, `y` as the bits
of their encodings, and the answers `a`, `b` as raw bit strings. -/
def uInput (D : Prog) (n Tb : ℕ) (x y a b : BitStr) : Fin 7 → List Sym :=
  ![S D.toData, S (encode n), List.replicate Tb .one, S (encode x), S (encode y), bits a, bits b]

@[simp] theorem uInput_PROG (D n Tb x y a b) : uInput D n Tb x y a b PROG = S D.toData := rfl
@[simp] theorem uInput_N (D n Tb x y a b) : uInput D n Tb x y a b N = S (encode n) := rfl
@[simp] theorem uInput_T (D n Tb x y a b) : uInput D n Tb x y a b T = List.replicate Tb .one := rfl
@[simp] theorem uInput_XS (D n Tb x y a b) : uInput D n Tb x y a b XS = S (encode x) := rfl
@[simp] theorem uInput_YS (D n Tb x y a b) : uInput D n Tb x y a b YS = S (encode y) := rfl
@[simp] theorem uInput_A (D n Tb x y a b) : uInput D n Tb x y a b A = bits a := rfl
@[simp] theorem uInput_B (D n Tb x y a b) : uInput D n Tb x y a b B = bits b := rfl

theorem mem_bits (l : List Bool) : ∀ s ∈ bits l, s = .zero ∨ s = .one := by
  intro s hs
  simp only [bits, List.mem_map] at hs
  obtain ⟨b, -, rfl⟩ := hs
  cases b <;> simp

theorem map_boolOf_bits (l : List Bool) : (bits l).map boolOf = l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [bits, boolOf] at ih ⊢ <;> exact ih

theorem answerBits_bits (l : BitStr) : answerBits (bits l) = S (encode l) := by
  simp [answerBits, map_boolOf_bits]; rfl

theorem encode_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (p : α × β) :
    encode p = .cons (encode p.1) (encode p.2) := rfl

/-! ## Input heads -/

variable {input : Fin 7 → List Sym}

/-- The input heads are at the positions `f`. -/
def InPos (c : Cfg input) (f : IT → ℕ) : Prop := ∀ j, (c.inputPos j : ℕ) = f j

theorem InPos.of_untouched {c c' : Cfg input} {f : IT → ℕ} (h : InPos c f) {SW : List WT}
    (hu : Untouched c c' [] SW) : InPos c' f := by
  intro j; rw [hu.inputPos_eq]; exact h j

/-- A run touching only input heads leaves the descriptions. -/
theorem Desc.of_untouched_inputs {c c' : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
    (hd : Desc c q ds) {SI : List IT} (hu : Untouched c c' SI []) {q' : Option Ctl}
    (hs : c'.state = q') : Desc c' q' ds :=
  ⟨hs, fun t => by rw [hu.tapes (d := t) (by simp), hu.pos (d := t) (by simp)]; exact hd.tape t⟩

theorem InPos.update {c c' : Cfg input} {f : IT → ℕ} (h : InPos c f) {j : IT} {SW : List WT}
    (hu : Untouched c c' [j] SW) {v : ℕ} (hv : (c'.inputPos j : ℕ) = v) :
    InPos c' (Function.update f j v) := by
  intro j'
  by_cases hj : j' = j
  · subst hj; simpa using hv
  · rw [Function.update_of_ne hj, hu.inputPos (by simpa using hj)]; exact h j'

theorem InPos.update₂ {c c' : Cfg input} {f : IT → ℕ} (h : InPos c f) {j j' : IT} {SW : List WT}
    (hu : Untouched c c' [j, j'] SW) {v v' : ℕ} (hv : (c'.inputPos j : ℕ) = v)
    (hv' : (c'.inputPos j' : ℕ) = v') (hjj : j ≠ j') :
    InPos c' (Function.update (Function.update f j v) j' v') := by
  intro i
  by_cases hi' : i = j'
  · subst hi'; simpa using hv'
  by_cases hi : i = j
  · subst hi; rw [Function.update_of_ne hjj, Function.update_self]; exact hv
  · rw [Function.update_of_ne hi', Function.update_of_ne hi, hu.inputPos (by simp [hi, hi'])]
    exact h i

section Names

@[simp] theorem PROG_ne_N : PROG ≠ N := by decide
@[simp] theorem PROG_ne_T : PROG ≠ T := by decide
@[simp] theorem PROG_ne_XS : PROG ≠ XS := by decide
@[simp] theorem PROG_ne_YS : PROG ≠ YS := by decide
@[simp] theorem PROG_ne_A : PROG ≠ A := by decide
@[simp] theorem PROG_ne_B : PROG ≠ B := by decide
@[simp] theorem N_ne_PROG : N ≠ PROG := by decide
@[simp] theorem N_ne_T : N ≠ T := by decide
@[simp] theorem N_ne_XS : N ≠ XS := by decide
@[simp] theorem N_ne_YS : N ≠ YS := by decide
@[simp] theorem N_ne_A : N ≠ A := by decide
@[simp] theorem N_ne_B : N ≠ B := by decide
@[simp] theorem T_ne_PROG : T ≠ PROG := by decide
@[simp] theorem T_ne_N : T ≠ N := by decide
@[simp] theorem T_ne_XS : T ≠ XS := by decide
@[simp] theorem T_ne_YS : T ≠ YS := by decide
@[simp] theorem T_ne_A : T ≠ A := by decide
@[simp] theorem T_ne_B : T ≠ B := by decide
@[simp] theorem XS_ne_PROG : XS ≠ PROG := by decide
@[simp] theorem XS_ne_N : XS ≠ N := by decide
@[simp] theorem XS_ne_T : XS ≠ T := by decide
@[simp] theorem XS_ne_YS : XS ≠ YS := by decide
@[simp] theorem XS_ne_A : XS ≠ A := by decide
@[simp] theorem XS_ne_B : XS ≠ B := by decide
@[simp] theorem YS_ne_PROG : YS ≠ PROG := by decide
@[simp] theorem YS_ne_N : YS ≠ N := by decide
@[simp] theorem YS_ne_T : YS ≠ T := by decide
@[simp] theorem YS_ne_XS : YS ≠ XS := by decide
@[simp] theorem YS_ne_A : YS ≠ A := by decide
@[simp] theorem YS_ne_B : YS ≠ B := by decide
@[simp] theorem A_ne_PROG : A ≠ PROG := by decide
@[simp] theorem A_ne_N : A ≠ N := by decide
@[simp] theorem A_ne_T : A ≠ T := by decide
@[simp] theorem A_ne_XS : A ≠ XS := by decide
@[simp] theorem A_ne_YS : A ≠ YS := by decide
@[simp] theorem A_ne_B : A ≠ B := by decide
@[simp] theorem B_ne_PROG : B ≠ PROG := by decide
@[simp] theorem B_ne_N : B ≠ N := by decide
@[simp] theorem B_ne_T : B ≠ T := by decide
@[simp] theorem B_ne_XS : B ≠ XS := by decide
@[simp] theorem B_ne_YS : B ≠ YS := by decide
@[simp] theorem B_ne_A : B ≠ A := by decide

end Names

/-! ## The input routines on descriptions -/

section Routines

variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}

theorem I_jump {target : ProgId} (hins : instrAt k pc = .jump target) (hd : Desc c (at_ k pc) ds)
    (hi : InPos c f) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (at_ target ⟨0, by decide⟩) ds ∧ InPos c' f := by
  obtain ⟨c', hr, hs, hu, _⟩ := exec_jump hins c hd.state
  obtain ⟨c'', hr', hd'⟩ := D_jump hins hd
  have e : c'' = c' := by rw [← hr.1, ← hr'.1]
  subst e
  exact ⟨c'', hr', hd', hi.of_untouched hu⟩

/-- A written effect on `dst` at the end of its content, as a description. -/
theorem Desc.of_weff_end {q : Option Ctl} (hd : Desc c q ds) {c' : Cfg input} {dst : WT}
    {SI : List IT} (hu : Untouched c c' SI [dst]) {q' : Option Ctl} (hs : c'.state = q')
    {w : List Sym} (hw : WEff dst c c' w) (hp : (ds dst).p = (ds dst).l.length) :
    Desc c' q' (Function.update ds dst ⟨(ds dst).l ++ w, ((ds dst).l ++ w).length⟩) := by
  refine ⟨hs, fun t => ?_⟩
  by_cases ht : t = dst
  · subst ht
    rw [Function.update_self]
    have := (hd.tape t).of_overwrite (p' := ((ds t).l ++ w).length) (pos' := c'.workTapePos t)
      hp.le (by rw [← hd.pos]; exact hw.holds) (fun q hq => hw.outside q (by rw [hd.pos]; exact hq))
      (by rw [hw.pos, hd.pos, hp]; simp)
    rwa [overwrite_append_nil _ _ hp] at this
  · rw [Function.update_of_ne ht, hu.tapes (d := t) (by simpa using ht), hu.pos (d := t) (by simpa using ht)]
    exact hd.tape t

theorem I_write_end {t : WT} {s : Sym} (hins : instrAt k pc = .write t s) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p = (ds t).l.length) (hi : InPos c f) :
    ∃ c', Reach c 1 c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l ++ [s], ((ds t).l ++ [s]).length⟩) ∧
      InPos c' f := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_write hins hpc c hd.state
  refine ⟨c', hr, hd.of_weff_end (SI := []) hu hs ⟨?_, ?_, ?_⟩ hp, hi.of_untouched hu⟩
  · rw [Holds.singleton_iff, htape, Function.update_self]
  · intro q hq
    rw [htape, Function.update_of_ne (by simp only [List.length_singleton] at hq; omega)]
  · rw [hpos]; simp

theorem I_copyUnary_end {j : IT} {dst : WT} (hins : instrAt k pc = .copyUnary j dst)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1)
    (hp : (ds dst).p = (ds dst).l.length) :
    ∃ c', Reach c ((input j).length + 1) c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds dst
        ⟨(ds dst).l ++ List.replicate (input j).length Sym.one,
          ((ds dst).l ++ List.replicate (input j).length Sym.one).length⟩) ∧
      InPos c' (Function.update f j ((input j).length + 1)) := by
  obtain ⟨c', hr, hs, hu, hj', hw⟩ := exec_copyUnary hins hpc (input j).length c 0 hd.state
    (by rw [hi j, hj]) (by simp)
  exact ⟨c', hr, hd.of_weff_end hu hs hw hp, hi.update hu hj'⟩

theorem I_copyInputBits_end {j : IT} {dst : WT} (hins : instrAt k pc = .copyInputBits j dst)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1)
    (hp : (ds dst).p = (ds dst).l.length) :
    ∃ c', Reach c ((input j).length + 1) c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds dst
        ⟨(ds dst).l ++ input j, ((ds dst).l ++ input j).length⟩) ∧
      InPos c' (Function.update f j ((input j).length + 1)) := by
  obtain ⟨c', hr, hs, hu, hj', hw⟩ := exec_copyInputBits hins hpc (input j).length c 0 hd.state
    (by rw [hi j, hj]) (by simp)
  simp only [List.drop_zero] at hw
  exact ⟨c', hr, hd.of_weff_end hu hs hw hp, hi.update hu hj'⟩

theorem I_buildAnswer_end {j : IT} {dst : WT} (hins : instrAt k pc = .buildAnswer j dst)
    (hpc : pc.val + 1 < maxPc) (hbits : ∀ s ∈ input j, s = .zero ∨ s = .one)
    (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1)
    (hp : (ds dst).p = (ds dst).l.length) :
    ∃ n ≤ 4 * (input j).length + 1, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds dst
        ⟨(ds dst).l ++ answerBits (input j), ((ds dst).l ++ answerBits (input j)).length⟩) ∧
      InPos c' (Function.update f j ((input j).length + 1)) := by
  obtain ⟨n, hn, c', hr, hs, hu, hj', hw⟩ := exec_buildAnswer hins hpc hbits (input j).length c 0
    hd.state (by rw [hi j, hj]) (by simp)
  simp only [List.drop_zero] at hw
  exact ⟨n, hn, c', hr, hd.of_weff_end hu hs hw hp, hi.update hu hj'⟩

theorem I_checkLen {j ref : IT} (hins : instrAt k pc = .checkLen j ref) (hpc : pc.val + 1 < maxPc)
    (hjr : j ≠ ref) (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1) (hr : f ref = 1)
    (hlen : (input j).length ≤ (input ref).length) :
    ∃ c', Reach c ((input j).length + 1) c' [] ∧ Desc c' (next_ k pc hpc) ds ∧
      InPos c' (Function.update (Function.update f j ((input j).length + 1)) ref
        ((input j).length + 1)) := by
  obtain ⟨c', hr', hs, hu, hj', hr''⟩ := exec_checkLen hins hpc hjr (input j).length c 0 hd.state
    (by rw [hi j, hj]) (by rw [hi ref, hr]) (by simp) (by simpa using hlen)
  exact ⟨c', hr', hd.of_untouched_inputs hu hs, hi.update₂ hu hj' hr'' hjr⟩

theorem I_rewindInput {j : IT} (hins : instrAt k pc = .rewindInput j) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hi : InPos c f) :
    ∃ n ≤ f j + 2, ∃ c', Reach c n c' [] ∧ Desc c' (next_ k pc hpc) ds ∧
      InPos c' (Function.update f j 0) := by
  obtain ⟨n, hn, c', hr, hs, hu, hj'⟩ := exec_rewindInput hins hpc c hd.state
  exact ⟨n, by rw [hi j] at hn; exact hn, c', hr, hd.of_untouched_inputs hu hs, hi.update hu hj'⟩

theorem I_moveInput_right {j : IT} (hins : instrAt k pc = .moveInput j true)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) (hi : InPos c f)
    (hlt : f j < (input j).length + 1) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) ds ∧ InPos c' (Function.update f j (f j + 1)) := by
  obtain ⟨c', hr, hs, hu, hj'⟩ := exec_moveInput hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched_inputs hu hs, hi.update hu ?_⟩
  rw [hj', if_pos rfl, moveInputPos_val_one _ (by rw [hi j]; exact hlt), hi j]

end Routines

/-! ## The initialization -/

/-- The bound on the steps of the initialization. -/
def initBound (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) : ℕ :=
  3 * Tb + 8 * (a.length + b.length) + (S D.toData).length + (S (encode n)).length +
    (S (encode x)).length + (S (encode y)).length + 40

theorem length_answerBits (l : List Sym) : (answerBits l).length ≤ 4 * l.length + 1 := by
  induction l with
  | nil => simp [answerBits_nil]
  | cons s l ih =>
    rcases s with _ | _ | _ | _ | _ <;> simp [answerBits, boolOf, Data.ofList, Data.ofBool, S_cons,
      length_S] at ih ⊢ <;> omega

/-- The initial configuration is described by empty tapes. -/
theorem desc_initCfg (input : Fin 7 → List Sym) :
    Desc (U.initCfg input) (at_ .init 0) (fun _ => ⟨[], 0⟩) := by
  refine ⟨rfl, fun t => ⟨Holds.nil, fun _ _ => rfl, fun _ _ => rfl, rfl⟩⟩

theorem inPos_initCfg (input : Fin 7 → List Sym) : InPos (U.initCfg input) (fun _ => 1) :=
  fun j => by simp [initCfg]

/-- **The initialization**: from the initial configuration on the inputs `(𝒟, n, T, x, y, a, b)`
with `|a|, |b| ≤ T`, `U` reaches the dispatcher representing `⟨ev 𝒟, [encode (n, x, y, a, b)], []⟩`
with budget `Tb` and an empty scratch tape. -/
theorem init_run (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) (ha : a.length ≤ Tb)
    (hb : b.length ≤ Tb) :
    ∃ m ≤ initBound D n x y a b Tb, ∃ (c : Cfg (uInput D n Tb x y a b)) (ds : WT → TapeSt),
      Reach (U.initCfg (uInput D n Tb x y a b)) m c [] ∧ Desc c (at_ .dispatch 0) ds ∧
      RepOf ds ⟨.ev D, [encode (n, x, y, a, b)], []⟩ Tb (ctrlRepr (.ev D)).length 0 ∧
      (ds X).l.length = 0 := by
  have hd := desc_initCfg (uInput D n Tb x y a b)
  have hi := inPos_initCfg (uInput D n Tb x y a b)
  obtain ⟨c₁, hr₁, hd₁, hi₁⟩ := I_copyUnary_end rfl (by decide) hd hi rfl rfl
  simp only [uInput_T, List.length_replicate] at hr₁ hd₁ hi₁
  obtain ⟨n₂, hn₂, c₂, hr₂, hd₂, hi₂⟩ := I_rewindInput rfl (by decide) hd₁ hi₁
  simp at hn₂
  obtain ⟨c₃, hr₃, hd₃, hi₃⟩ := I_moveInput_right rfl (by decide) hd₂ hi₂ (by simp)
  obtain ⟨c₄, hr₄, hd₄, hi₄⟩ := I_checkLen rfl (by decide) (by decide) hd₃ hi₃ (by simp) (by simp)
    (by simpa using ha)
  simp only [uInput_A, length_bits] at hr₄ hi₄
  obtain ⟨n₅, hn₅, c₅, hr₅, hd₅, hi₅⟩ := I_rewindInput rfl (by decide) hd₄ hi₄
  simp at hn₅
  obtain ⟨c₆, hr₆, hd₆, hi₆⟩ := I_moveInput_right rfl (by decide) hd₅ hi₅ (by simp)
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇, hi₇⟩ := I_rewindInput rfl (by decide) hd₆ hi₆
  simp at hn₇
  obtain ⟨c₈, hr₈, hd₈, hi₈⟩ := I_moveInput_right rfl (by decide) hd₇ hi₇ (by simp)
  obtain ⟨c₉, hr₉, hd₉, hi₉⟩ := I_checkLen rfl (by decide) (by decide) hd₈ hi₈ (by simp) (by simp)
    (by simpa using hb)
  simp only [uInput_B, length_bits] at hr₉ hi₉
  obtain ⟨n₁₀, hn₁₀, c₁₀, hr₁₀, hd₁₀, hi₁₀⟩ := I_rewindInput rfl (by decide) hd₉ hi₉
  simp at hn₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁, hi₁₁⟩ := I_moveInput_right rfl (by decide) hd₁₀ hi₁₀ (by simp)
  obtain ⟨c₁₂, hr₁₂, hd₁₂, hi₁₂⟩ := I_write_end rfl (by decide) hd₁₁ (by simp) hi₁₁
  obtain ⟨c₁₃, hr₁₃, hd₁₃, hi₁₃⟩ := I_copyInputBits_end rfl (by decide) hd₁₂ hi₁₂ (by simp) (by simp)
  simp only [uInput_PROG] at hr₁₃ hd₁₃ hi₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄, hi₁₄⟩ := I_write_end rfl (by decide) hd₁₃ (by simp) hi₁₃
  obtain ⟨c₁₅, hr₁₅, hd₁₅, hi₁₅⟩ := I_copyInputBits_end rfl (by decide) hd₁₄ hi₁₄ (by simp) (by simp)
  simp only [uInput_N] at hr₁₅ hd₁₅ hi₁₅
  obtain ⟨c₁₆, hr₁₆, hd₁₆, hi₁₆⟩ := I_write_end rfl (by decide) hd₁₅ (by simp) hi₁₅
  obtain ⟨c₁₇, hr₁₇, hd₁₇, hi₁₇⟩ := I_copyInputBits_end rfl (by decide) hd₁₆ hi₁₆ (by simp) (by simp)
  simp only [uInput_XS] at hr₁₇ hd₁₇ hi₁₇
  obtain ⟨c₁₈, hr₁₈, hd₁₈, hi₁₈⟩ := I_write_end rfl (by decide) hd₁₇ (by simp) hi₁₇
  obtain ⟨c₁₉, hr₁₉, hd₁₉, hi₁₉⟩ := I_copyInputBits_end rfl (by decide) hd₁₈ hi₁₈ (by simp) (by simp)
  simp only [uInput_YS] at hr₁₉ hd₁₉ hi₁₉
  obtain ⟨c₂₀, hr₂₀, hd₂₀, hi₂₀⟩ := I_write_end rfl (by decide) hd₁₉ (by simp) hi₁₉
  obtain ⟨n₂₁, hn₂₁, c₂₁, hr₂₁, hd₂₁, hi₂₁⟩ := I_buildAnswer_end rfl (by decide) (mem_bits a) hd₂₀
    hi₂₀ (by simp) (by simp)
  simp only [uInput_A, length_bits, answerBits_bits] at hn₂₁ hd₂₁ hi₂₁
  obtain ⟨n₂₂, hn₂₂, c₂₂, hr₂₂, hd₂₂, hi₂₂⟩ := I_buildAnswer_end rfl (by decide) (mem_bits b) hd₂₁
    hi₂₁ (by simp) (by simp)
  simp only [uInput_B, length_bits, answerBits_bits] at hn₂₂ hd₂₂ hi₂₂
  obtain ⟨c₂₃, hr₂₃, hd₂₃, hi₂₃⟩ := I_write_end rfl (by decide) hd₂₂ (by simp) hi₂₂
  obtain ⟨c₂₄, hr₂₄, hd₂₄, hi₂₄⟩ := I_jump rfl hd₂₃ hi₂₃
  have hR := hr₁.trans hr₂
  have hR := hR.trans hr₃
  have hR := hR.trans hr₄
  have hR := hR.trans hr₅
  have hR := hR.trans hr₆
  have hR := hR.trans hr₇
  have hR := hR.trans hr₈
  have hR := hR.trans hr₉
  have hR := hR.trans hr₁₀
  have hR := hR.trans hr₁₁
  have hR := hR.trans hr₁₂
  have hR := hR.trans hr₁₃
  have hR := hR.trans hr₁₄
  have hR := hR.trans hr₁₅
  have hR := hR.trans hr₁₆
  have hR := hR.trans hr₁₇
  have hR := hR.trans hr₁₈
  have hR := hR.trans hr₁₉
  have hR := hR.trans hr₂₀
  have hR := hR.trans hr₂₁
  have hR := hR.trans hr₂₂
  have hR := hR.trans hr₂₃
  have hR := hR.trans hr₂₄
  refine ⟨_, ?_, c₂₄, _, hR.cast_out (by simp), hd₂₄, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [initBound]; omega
  · exact ⟨[], by simp [ctrlRepr]⟩
  · simp [encode_prod, S_cons, List.append_assoc]
  · simp
  · simp
  · simp
  · simp
  · simp

end MIPRE.TM.Interp
