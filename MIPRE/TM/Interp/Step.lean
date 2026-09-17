/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Desc

/-!
# One step of the evaluation machine

The representation of a configuration of the CEK machine on the tapes (`RepOf`), the
dispatcher, and, for each case of `Machine.step`, the run of the case program from the
representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting
silently when the budget is short.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

namespace MIPRE.TM.Interp

open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine

variable {input : Fin 7 → List Sym}

instance : NeZero maxPc := ⟨by decide⟩


/-! ## The tape names are distinct -/

@[simp] theorem C_ne_E : C ≠ E := by decide
@[simp] theorem C_ne_K : C ≠ K := by decide
@[simp] theorem C_ne_X : C ≠ X := by decide
@[simp] theorem C_ne_CNT : C ≠ CNT := by decide
@[simp] theorem C_ne_BUD : C ≠ BUD := by decide
@[simp] theorem E_ne_C : E ≠ C := by decide
@[simp] theorem E_ne_K : E ≠ K := by decide
@[simp] theorem E_ne_X : E ≠ X := by decide
@[simp] theorem E_ne_CNT : E ≠ CNT := by decide
@[simp] theorem E_ne_BUD : E ≠ BUD := by decide
@[simp] theorem K_ne_C : K ≠ C := by decide
@[simp] theorem K_ne_E : K ≠ E := by decide
@[simp] theorem K_ne_X : K ≠ X := by decide
@[simp] theorem K_ne_CNT : K ≠ CNT := by decide
@[simp] theorem K_ne_BUD : K ≠ BUD := by decide
@[simp] theorem X_ne_C : X ≠ C := by decide
@[simp] theorem X_ne_E : X ≠ E := by decide
@[simp] theorem X_ne_K : X ≠ K := by decide
@[simp] theorem X_ne_CNT : X ≠ CNT := by decide
@[simp] theorem X_ne_BUD : X ≠ BUD := by decide
@[simp] theorem CNT_ne_C : CNT ≠ C := by decide
@[simp] theorem CNT_ne_E : CNT ≠ E := by decide
@[simp] theorem CNT_ne_K : CNT ≠ K := by decide
@[simp] theorem CNT_ne_X : CNT ≠ X := by decide
@[simp] theorem CNT_ne_BUD : CNT ≠ BUD := by decide
@[simp] theorem BUD_ne_C : BUD ≠ C := by decide
@[simp] theorem BUD_ne_E : BUD ≠ E := by decide
@[simp] theorem BUD_ne_K : BUD ≠ K := by decide
@[simp] theorem BUD_ne_X : BUD ≠ X := by decide
@[simp] theorem BUD_ne_CNT : BUD ≠ CNT := by decide

/-! ## The representation -/

/-- The descriptions representing the machine configuration `m` with budget `r`: the
control followed by garbage `g` (its head at `pC`), the environment and the stack exactly
(the stack head at `pK`), a scratch tape with its head inside its content, an empty
counter, a unary budget. -/
structure RepOf (ds : WT → TapeSt) (m : Machine.Cfg) (r pC pK : ℕ) : Prop where
  ctrl : ∃ g, ds C = ⟨ctrlRepr m.ctrl ++ g, pC⟩
  env : ds E = ⟨envRepr m.env, (envRepr m.env).length⟩
  kont : ds K = ⟨kontRepr m.kont, pK⟩
  scratch : (ds X).p ≤ (ds X).l.length
  cnt : ds CNT = ⟨[], 0⟩
  bud : ds BUD = ⟨List.replicate r .one, r⟩

/-- The representation, as an explicit description (the scratch tape as it is). -/
theorem RepOf.eq {ds : WT → TapeSt} {m : Machine.Cfg} {r pC pK : ℕ} (h : RepOf ds m r pC pK) :
    ∃ g, ds = Function.update (Function.update (Function.update (Function.update (Function.update ds
      C ⟨ctrlRepr m.ctrl ++ g, pC⟩) E ⟨envRepr m.env, (envRepr m.env).length⟩)
      K ⟨kontRepr m.kont, pK⟩) CNT ⟨[], 0⟩) BUD ⟨List.replicate r .one, r⟩ := by
  obtain ⟨g, hC⟩ := h.ctrl
  refine ⟨g, funext fun t => ?_⟩
  fin_cases t
  · simpa using hC
  · simpa using h.env
  · simpa using h.kont
  · simp
  · simpa using h.cnt
  · simpa using h.bud

/-- The size of the representation of `m`. -/
def sz (m : Machine.Cfg) : ℕ :=
  (ctrlRepr m.ctrl).length + (envRepr m.env).length + (kontRepr m.kont).length + 1

/-- `c` reaches, within `B` silent steps, the control `q` with tapes representing `m'`
(budget `r'`, heads of `C` and `K` at `pC`, `pK`), its scratch tape of length at most `xl`. -/
abbrev PreTo (c : Cfg input) (B : ℕ) (q : Option Ctl) (m' : Machine.Cfg) (r' pC pK xl : ℕ) : Prop :=
  ∃ n ≤ B, ∃ c' ds', Reach c n c' [] ∧ Desc c' q ds' ∧ RepOf ds' m' r' pC pK ∧
    (ds' X).l.length ≤ xl

/-- `c` reaches, within `B` silent steps, the dispatcher representing `m'` with budget `r'`,
its scratch tape of length at most `xl`. -/
abbrev StepTo (c : Cfg input) (B : ℕ) (m' : Machine.Cfg) (r' xl : ℕ) : Prop :=
  PreTo c B (at_ .dispatch 0) m' r' (ctrlRepr m'.ctrl).length (kontRepr m'.kont).length xl

/-- `PreTo` with at least one step. -/
def PreTo1 (c : Cfg input) (B : ℕ) (q : Option Ctl) (m' : Machine.Cfg) (r' pC pK xl : ℕ) : Prop :=
  ∃ n, 1 ≤ n ∧ n ≤ B ∧ ∃ c' ds', Reach c n c' [] ∧ Desc c' q ds' ∧ RepOf ds' m' r' pC pK ∧
    (ds' X).l.length ≤ xl

/-- `StepTo` with at least one step. -/
abbrev RunTo (c : Cfg input) (B : ℕ) (m' : Machine.Cfg) (r' xl : ℕ) : Prop :=
  PreTo1 c B (at_ .dispatch 0) m' r' (ctrlRepr m'.ctrl).length (kontRepr m'.kont).length xl

theorem PreTo1.mono {c : Cfg input} {B B' : ℕ} {q : Option Ctl} {m' : Machine.Cfg}
    {r' pC pK xl xl' : ℕ} (h : PreTo1 c B q m' r' pC pK xl) (hB : B ≤ B') (hx : xl ≤ xl') :
    PreTo1 c B' q m' r' pC pK xl' := by
  obtain ⟨n, h1, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  exact ⟨n, h1, by omega, c', ds', hr, hd, hrep, by omega⟩

theorem PreTo1.toPreTo {c : Cfg input} {B : ℕ} {q : Option Ctl} {m' : Machine.Cfg}
    {r' pC pK xl : ℕ} (h : PreTo1 c B q m' r' pC pK xl) : PreTo c B q m' r' pC pK xl := by
  obtain ⟨n, _, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  exact ⟨n, hn, c', ds', hr, hd, hrep, hxl⟩

theorem PreTo.mono {c : Cfg input} {B B' : ℕ} {q : Option Ctl} {m' : Machine.Cfg}
    {r' pC pK xl xl' : ℕ} (h : PreTo c B q m' r' pC pK xl) (hB : B ≤ B') (hx : xl ≤ xl') :
    PreTo c B' q m' r' pC pK xl' := by
  obtain ⟨n, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  exact ⟨n, by omega, c', ds', hr, hd, hrep, by omega⟩

/-! ## The control words -/

theorem S_ofNat_zero : S (Data.ofNat 0) = [.zero] := rfl

theorem ctrlRepr_var (i : ℕ) :
    ctrlRepr (.ev (.var i)) = .zero :: .one :: .zero :: S (Data.ofNat i) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]

theorem ctrlRepr_nil :
    ctrlRepr (.ev .nil) = [.zero, .one, .one, .zero, .zero, .zero] := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]

theorem ctrlRepr_cons (h t : Prog) :
    ctrlRepr (.ev (.cons h t)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .zero :: .one :: (S h.toData ++ S t.toData) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]

theorem ctrlRepr_elim (i : ℕ) (n c : Prog) :
    ctrlRepr (.ev (.elim i n c)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .zero :: .one ::
        (S (Data.ofNat i) ++ .one :: (S n.toData ++ S c.toData)) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]

theorem ctrlRepr_let (e b : Prog) :
    ctrlRepr (.ev (.let_ e b)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .zero ::
        .one :: (S e.toData ++ S b.toData) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]

theorem ctrlRepr_loop (b : Prog) :
    ctrlRepr (.ev (.loop b)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one ::
        .zero :: .zero :: S b.toData := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]

theorem ctrlRepr_const (d : Data) :
    ctrlRepr (.ev (.const d)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one ::
        .zero :: .one :: .zero :: .zero :: S d := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]

theorem ctrlRepr_ret (v : Data) : ctrlRepr (.ret v) = .one :: S v := rfl

/-! ## List facts -/

theorem overwrite_cons_one_add (a : Sym) (l : List Sym) (p : ℕ) (w : List Sym) :
    overwrite (a :: l) (1 + p) w = a :: overwrite l p w := by
  rw [Nat.add_comm]; exact overwrite_cons_succ a l p w

theorem overwrite_append_nil' (a w : List Sym) {p : ℕ} (hp : p = a.length) :
    overwrite a p w = a ++ w := overwrite_append_nil a w hp

theorem kontRepr_nil_or_fr (k : List Frame) :
    kontRepr k = [] ∨ ∃ l₀, kontRepr k = l₀ ++ [.fr] := by
  cases k with
  | nil => exact Or.inl rfl
  | cons f k => exact Or.inr ⟨kontRepr k ++ frameBody f, by simp [frameRepr_eq]⟩

theorem envRepr_nil_or_sep (env : Env) :
    envRepr env = [] ∨ ∃ l₀, envRepr env = l₀ ++ [.sep] := by
  cases env with
  | nil => exact Or.inl rfl
  | cons v env => exact Or.inr ⟨envRepr env ++ S v, by simp⟩

theorem mem_envRepr_ne_fr (env : Env) : ∀ s ∈ envRepr env, some s ≠ some Sym.fr :=
  fun s hs h => (mem_envRepr env s hs).1 (Option.some_injective _ h)

theorem mem_envRepr_ne_en (env : Env) : ∀ s ∈ envRepr env, s ≠ Sym.en :=
  fun s hs => (mem_envRepr env s hs).2

theorem mem_envRepr_ne_none (env : Env) : ∀ s ∈ envRepr env, some s ≠ none :=
  fun _ _ => Option.some_ne_none _

theorem size_get_le (env : Env) (i : ℕ) : (Env.get env i).size ≤ (envRepr env).length + 1 := by
  by_cases hi : i < env.length
  · have hmem : Env.get env i ∈ env := by
      simp only [Env.get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    rw [length_envRepr]
    have : (Env.get env i).size ≤ (env.map Data.size).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    omega
  · have hnone : env[i]? = none := List.getElem?_eq_none (by omega)
    simp only [Env.get, List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    simp

theorem frameBody_ne_fr (f : Frame) : ∀ s ∈ frameBody f, s ≠ Sym.fr := mem_frameBody f

/-- Normalize a description after a routine. -/
macro "norm_ds" "at" hs:(ppSpace colGt ident)+ : tactic =>
  `(tactic| try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq,
      not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT,
      overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil',
      overwrite_append', List.cons_append, List.nil_append, List.append_nil,
      List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil,
      List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add,
      List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim,
      ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at $hs*)

macro "norm_ds_goal" : tactic =>
  `(tactic| try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq,
      not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT,
      overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil',
      overwrite_append', List.cons_append, List.nil_append, List.append_nil,
      List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil,
      List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add,
      List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim,
      ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret])

/-! ## The dispatcher on `ev` -/

/-- One round of `evDispatch`: two moves and a branch on the bit two cells right. -/
theorem evDispatch_round {pc : Fin maxPc} {tgt : ProgId} (h1 : instrAt .evDispatch pc = .move C true)
    (h2 : pc.val + 1 < maxPc) (h2' : instrAt .evDispatch ⟨pc.val + 1, h2⟩ = .move C true)
    (h3 : pc.val + 2 < maxPc) (h3' : instrAt .evDispatch ⟨pc.val + 2, h3⟩ = .branch C (some .zero) tgt)
    {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evDispatch pc) ds) :
    ((ds C).l[(ds C).p + 2]? = some .zero →
      ∃ c', Reach c 3 c' [] ∧ Desc c' (at_ tgt 0) (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩)) ∧
    ((ds C).l[(ds C).p + 2]? ≠ some .zero → (h4 : pc.val + 2 + 1 < maxPc) →
      ∃ c', Reach c 3 c' [] ∧
        Desc c' (next_ .evDispatch ⟨pc.val + 2, h3⟩ h4)
          (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩)) := by
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right h1 h2 hd
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right h2' h3 hd₁
  simp only [Function.update_idem, Function.update_self] at hd₂
  constructor
  · intro hz
    obtain ⟨c₃, hr₃, hd₃⟩ := D_branch_taken h3' hd₂ (by simpa [Nat.add_assoc] using hz)
    exact ⟨c₃, ((hr₁.trans hr₂).trans hr₃).cast_out (by simp), hd₃.cast rfl (by simp [Nat.add_assoc])⟩
  · intro hz h4
    obtain ⟨c₃, hr₃, hd₃⟩ := D_branch_not h3' h4 hd₂ (by simpa [Nat.add_assoc] using hz)
    exact ⟨c₃, ((hr₁.trans hr₂).trans hr₃).cast_out (by simp),
      hd₃.cast rfl (by simp [Nat.add_assoc])⟩

/-- The case program of a control to evaluate, and the position of the final `0` of its tag. -/
def evTarget : Prog → ProgId
  | .var _ => .evVar
  | .nil => .evNil
  | .cons _ _ => .evCons
  | .elim _ _ _ => .evElim
  | .let_ _ _ => .evLet
  | .loop _ => .evLoop
  | .const _ => .evConst

def evHead : Prog → ℕ
  | .var _ => 2
  | .nil => 4
  | .cons _ _ => 6
  | .elim _ _ _ => 8
  | .let_ _ _ => 10
  | .loop _ => 12
  | .const _ => 14

/-- From the dispatcher, a control `ev p` reaches its case program with the head of `C` on the
final `0` of the tag. -/
theorem dispatch_ev {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {p : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev p, env, k⟩ r (ctrlRepr (.ev p)).length (kontRepr k).length) :
    PreTo1 c ((ctrlRepr (.ev p)).length + 26) (at_ (evTarget p) 0) ⟨.ev p, env, k⟩ r (evHead p)
      (kontRepr k).length (ds X).l.length := by
  obtain ⟨g, hC⟩ := hr.ctrl
  have hE := hr.env
  have hK := hr.kont
  have hX := hr.scratch
  have hN := hr.cnt
  have hB := hr.bud
  have hlen : (ds C).l.length = (ctrlRepr (.ev p)).length + g.length := by simp [hC]
  obtain ⟨c₁, hr₁, hd₁⟩ := D_rewind rfl (by decide) hd (by simp [hC])
  norm_ds at hr₁ hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_branch_taken rfl hd₁ (by simp [hC, ctrlRepr])
  -- at `evDispatch 0`, head at `0`
  have hR : Reach c ((ctrlRepr (.ev p)).length + 3) c₂ [] := by
    rw [hC] at hr₁
    exact ((hr₁.trans hr₂).cast_n (by simp)).cast_out (by simp)
  clear hr₁ hr₂ hd₁
  -- the description after the dispatcher, with the head of `C` at `n`
  have fin : ∀ (n : ℕ) (c' : Cfg input), Reach c₂ (3 * (n / 2)) c' [] →
      Desc c' (at_ (evTarget p) 0) (Function.update ds C ⟨(ds C).l, n⟩) → n = evHead p →
      PreTo1 c ((ctrlRepr (.ev p)).length + 26) (at_ (evTarget p) 0) ⟨.ev p, env, k⟩ r (evHead p)
        (kontRepr k).length (ds X).l.length := by
    intro n c' hr' hd' hn
    subst hn
    refine ⟨_, by omega, ?_, c', _, (hR.trans hr').cast_out (by simp), hd', ⟨⟨g, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩,
      ?_⟩
    · cases p <;> simp [evHead] <;> omega
    · simp [hC]
    · simp [hE]
    · simp [hK]
    · simp [hX]
    · simp [hN]
    · simp [hB]
    · simp
  cases p with
  | var i =>
    simp only [ctrlRepr_var] at hC
    obtain ⟨c₃, hr₃, hd₃⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₂).1 (by simp [hC])
    exact fin 2 c₃ hr₃ (by simpa [evTarget] using hd₃) rfl
  | nil =>
    simp only [ctrlRepr_nil] at hC
    obtain ⟨c₃, hr₃, hd₃⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₂).2 (by simp [hC])
      (by decide)
    obtain ⟨c₄, hr₄, hd₄⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₃).1 (by simp [hC])
    exact fin 4 c₄ ((hr₃.trans hr₄).cast_out (by simp)) (by simpa [evTarget] using hd₄) rfl
  | cons h t =>
    simp only [ctrlRepr_cons] at hC
    obtain ⟨c₃, hr₃, hd₃⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₂).2 (by simp [hC])
      (by decide)
    obtain ⟨c₄, hr₄, hd₄⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₃).2 (by simp [hC])
      (by decide)
    obtain ⟨c₅, hr₅, hd₅⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₄).1 (by simp [hC])
    exact fin 6 c₅ (((hr₃.trans hr₄).trans hr₅).cast_out (by simp)) (by simpa [evTarget] using hd₅) rfl
  | elim i n c =>
    simp only [ctrlRepr_elim] at hC
    obtain ⟨c₃, hr₃, hd₃⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₂).2 (by simp [hC])
      (by decide)
    obtain ⟨c₄, hr₄, hd₄⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₃).2 (by simp [hC])
      (by decide)
    obtain ⟨c₅, hr₅, hd₅⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₄).2 (by simp [hC])
      (by decide)
    obtain ⟨c₆, hr₆, hd₆⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₅).1 (by simp [hC])
    exact fin 8 c₆ ((((hr₃.trans hr₄).trans hr₅).trans hr₆).cast_out (by simp)) (by simpa [evTarget] using hd₆) rfl
  | let_ e b =>
    simp only [ctrlRepr_let] at hC
    obtain ⟨c₃, hr₃, hd₃⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₂).2 (by simp [hC])
      (by decide)
    obtain ⟨c₄, hr₄, hd₄⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₃).2 (by simp [hC])
      (by decide)
    obtain ⟨c₅, hr₅, hd₅⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₄).2 (by simp [hC])
      (by decide)
    obtain ⟨c₆, hr₆, hd₆⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₅).2 (by simp [hC])
      (by decide)
    obtain ⟨c₇, hr₇, hd₇⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₆).1 (by simp [hC])
    exact fin 10 c₇ (((((hr₃.trans hr₄).trans hr₅).trans hr₆).trans hr₇).cast_out (by simp))
      (by simpa [evTarget] using hd₇) rfl
  | loop b =>
    simp only [ctrlRepr_loop] at hC
    obtain ⟨c₃, hr₃, hd₃⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₂).2 (by simp [hC])
      (by decide)
    obtain ⟨c₄, hr₄, hd₄⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₃).2 (by simp [hC])
      (by decide)
    obtain ⟨c₅, hr₅, hd₅⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₄).2 (by simp [hC])
      (by decide)
    obtain ⟨c₆, hr₆, hd₆⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₅).2 (by simp [hC])
      (by decide)
    obtain ⟨c₇, hr₇, hd₇⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₆).2 (by simp [hC])
      (by decide)
    obtain ⟨c₈, hr₈, hd₈⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₇).1 (by simp [hC])
    exact fin 12 c₈ ((((((hr₃.trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans hr₈).cast_out (by simp))
      (by simpa [evTarget] using hd₈) rfl
  | const d =>
    simp only [ctrlRepr_const] at hC
    obtain ⟨c₃, hr₃, hd₃⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₂).2 (by simp [hC])
      (by decide)
    obtain ⟨c₄, hr₄, hd₄⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₃).2 (by simp [hC])
      (by decide)
    obtain ⟨c₅, hr₅, hd₅⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₄).2 (by simp [hC])
      (by decide)
    obtain ⟨c₆, hr₆, hd₆⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₅).2 (by simp [hC])
      (by decide)
    obtain ⟨c₇, hr₇, hd₇⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₆).2 (by simp [hC])
      (by decide)
    obtain ⟨c₈, hr₈, hd₈⟩ := (evDispatch_round rfl (by decide) rfl (by decide) rfl hd₇).2 (by simp [hC])
      (by decide)
    -- the tail: two moves and the jump
    obtain ⟨c₉, hr₉, hd₉⟩ := D_move_right rfl (by decide) hd₈
    obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_move_right rfl (by decide) hd₉
    obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_jump rfl hd₁₀
    simp only [Function.update_idem, Function.update_self] at hd₁₁
    exact fin 14 c₁₁
      ((((((((hr₃.trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans hr₈).trans hr₉).trans hr₁₀).trans
        hr₁₁ |>.cast_out (by simp)) (by simpa [evTarget] using hd₁₁) rfl

/-! ## The cases: `ev` -/

/-- The bound on the steps of a case program. -/
def caseBound (m : Machine.Cfg) (xl : ℕ) : ℕ := 100 * (sz m + xl + 1)

theorem case_evNil {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evNil 0) ds)
    {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev .nil, env, k⟩ (r + 1) 4 (kontRepr k).length) :
    StepTo c (caseBound ⟨.ev .nil, env, k⟩ (ds X).l.length) ⟨.ret .nil, env, k⟩ r
      ((ds X).l.length + sz ⟨.ev .nil, env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_rewind rfl (by decide) hd (by simp <;> omega)
  norm_ds at hr₁ hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_write rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_write rfl (by decide) hd₂ (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_charge rfl (by decide) hd₃ (r := r) (by simp <;> omega)
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_jump rfl hd₄
  refine ⟨_, ?_, c₅, _, ((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).cast_out (by simp <;> omega), hd₅,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound]; omega
  · simp [ctrlRepr_ret] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]

theorem case_evNil_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evNil 0) ds)
    {env : Env} {k : List Frame}
    (hr : RepOf ds ⟨.ev .nil, env, k⟩ 0 4 (kontRepr k).length) :
    HaltsIn c (caseBound ⟨.ev .nil, env, k⟩ (ds X).l.length) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_rewind rfl (by decide) hd (by simp <;> omega)
  norm_ds at hr₁ hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_write rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_write rfl (by decide) hd₂ (by simp <;> omega)
  norm_ds at hd₃
  have h4 := D_charge_fail rfl hd₃ (by simp <;> omega)
  exact (HaltsIn.after (((hr₁.trans hr₂).trans hr₃).cast_out (by simp <;> omega)) h4).mono
    (by simp only [caseBound]; omega)

theorem case_evVar {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evVar 0) ds)
    {i : ℕ} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.var i), env, k⟩ (r + ((Env.get env i).size + 1)) 2 (kontRepr k).length) :
    StepTo c (caseBound ⟨.ev (.var i), env, k⟩ (ds X).l.length) ⟨.ret (Env.get env i), env, k⟩ r
      ((ds X).l.length + sz ⟨.ev (.var i), env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  have hvl := size_get_le env i
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_getEnv rfl (by decide) hd₂ (env := env) (by simp <;> omega) (i := i)
    (l₁ := [.zero, .one, .zero]) (l₂ := g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_rewind rfl (by decide) hd₃ (by simp <;> omega)
  norm_ds at hr₄ hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_rewind rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hr₅ hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_write rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hd₆
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree_charge rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hd₆ (by simp <;> omega) (r := r + ((Env.get env i).size + 1)) (by simp <;> omega)
    (v := Env.get env i) (l₁ := []) (l₂ := (ds X).l.drop (S (Env.get env i)).length) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega) (by omega)
  norm_ds at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_charge rfl (by decide) hd₇ (r := r)
    (by simp <;> omega)
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_jump rfl hd₈
  refine ⟨_, ?_, c₉, _,
    ((((((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans hr₈).trans
      hr₉).cast_out (by simp <;> omega), hd₉, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_var, List.length_cons, List.length_append, length_S_ofNat]
    omega
  · simp [ctrlRepr_ret] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_var, List.length_cons, List.length_append, length_S_ofNat, length_S,
      List.length_drop]
    omega

theorem case_evVar_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evVar 0) ds)
    {i : ℕ} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.var i), env, k⟩ r 2 (kontRepr k).length)
    (hlt : r < (Env.get env i).size + 1) :
    HaltsIn c (caseBound ⟨.ev (.var i), env, k⟩ (ds X).l.length) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  have hvl := size_get_le env i
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_getEnv rfl (by decide) hd₂ (env := env) (by simp <;> omega) (i := i)
    (l₁ := [.zero, .one, .zero]) (l₂ := g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_rewind rfl (by decide) hd₃ (by simp <;> omega)
  norm_ds at hr₄ hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_rewind rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hr₅ hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_write rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hd₆
  have hR : Reach c _ c₆ [] :=
    (((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).cast_out (by simp <;> omega)
  rcases Nat.lt_or_ge r (Env.get env i).size with hr' | hr'
  · have h7 := D_copyTree_charge_fail rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hd₆ (by simp <;> omega) (r := r) (by simp <;> omega) (v := Env.get env i) (l₁ := [])
      (l₂ := (ds X).l.drop (S (Env.get env i)).length) (by simp <;> omega) (by simp <;> omega) hr'
    refine (HaltsIn.after hR h7).mono ?_
    simp only [caseBound, sz, ctrlRepr_var, List.length_cons, List.length_append, length_S_ofNat]
    omega
  · have hr0 : r = (Env.get env i).size := by omega
    subst hr0
    obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree_charge rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hd₆ (by simp <;> omega) (r := (Env.get env i).size) (by simp <;> omega)
      (v := Env.get env i) (l₁ := []) (l₂ := (ds X).l.drop (S (Env.get env i)).length) (by simp <;> omega) (by simp <;> omega)
      (by simp <;> omega) le_rfl
    norm_ds at hd₇
    have h8 := D_charge_fail rfl hd₇ (by simp <;> omega)
    refine (HaltsIn.after (hR.trans hr₇ |>.cast_out (by simp <;> omega)) h8).mono ?_
    simp only [caseBound, sz, ctrlRepr_var, List.length_cons, List.length_append, length_S_ofNat]
    omega

theorem case_evConst {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evConst 0) ds)
    {d : Data} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.const d), env, k⟩ (r + d.size) 14 (kontRepr k).length) :
    StepTo c (caseBound ⟨.ev (.const d), env, k⟩ (ds X).l.length) ⟨.ret d, env, k⟩ r
      ((ds X).l.length + sz ⟨.ev (.const d), env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_copyTree_charge rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hd₂ (by simp <;> omega) (r := r + d.size) (by simp <;> omega) (v := d)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .one, .zero,
      .zero]) (l₂ := g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega) (by omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_rewind rfl (by decide) hd₃ (by simp <;> omega)
  norm_ds at hr₄ hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_write rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_rewind rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hr₆ hd₆
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₆
    (by simp <;> omega) (v := d) (l₁ := []) (l₂ := (ds X).l.drop (S d).length) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_jump rfl hd₇
  refine ⟨_, ?_, c₈, _,
    (((((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans hr₈).cast_out
      (by simp <;> omega), hd₈, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_const, List.length_cons, List.length_append, length_S]
    omega
  · simp [ctrlRepr_ret] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_const, List.length_cons, List.length_append, length_S, List.length_drop]
    omega

theorem case_evConst_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evConst 0) ds)
    {d : Data} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.const d), env, k⟩ r 14 (kontRepr k).length) (hlt : r < d.size) :
    HaltsIn c (caseBound ⟨.ev (.const d), env, k⟩ (ds X).l.length) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  have h3 := D_copyTree_charge_fail rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hd₂ (by simp <;> omega) (r := r) (by simp <;> omega) (v := d)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .one, .zero,
      .zero]) (l₂ := g) (by simp <;> omega) (by simp <;> omega) hlt
  refine (HaltsIn.after ((hr₁.trans hr₂).cast_out (by simp <;> omega)) h3).mono ?_
  simp only [caseBound, sz, ctrlRepr_const, List.length_cons, List.length_append, length_S]
  omega

/-- The common tail of `evCons` and `evLet`: after the frame is pushed, rebuild the control
from the scratch tape and charge. Stated inline in each case. -/
theorem case_evCons {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evCons 0) ds)
    {h t : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.cons h t), env, k⟩ r 6 (kontRepr k).length) :
    PreTo c (caseBound ⟨.ev (.cons h t), env, k⟩ (ds X).l.length) (at_ .evCons 15)
      ⟨.ev h, env, .cons1 t env :: k⟩ r (ctrlRepr (.ev h)).length
      (kontRepr (.cons1 t env :: k)).length ((ds X).l.length + sz ⟨.ev (.cons h t), env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_rewind rfl (by decide) hd₂ (by simp <;> omega)
  norm_ds at hr₃ hd₃
  obtain ⟨n₄, hn₄, c₄, hr₄, hd₄⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₃
    (by simp <;> omega) (v := h.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .zero, .one]) (l₂ := S t.toData ++ g)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_write rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_write rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hd₆
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₆
    (by simp <;> omega) (v := t.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .zero, .one] ++ S h.toData) (l₂ := g)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_write rfl (by decide) hd₇ (by simp <;> omega)
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_rewind rfl (by decide) hd₈ (by simp <;> omega)
  norm_ds at hr₉ hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_copyUntil rfl (by decide) (by decide) hd₉ (l₁ := []) (w := envRepr env)
    (l₂ := []) (by simp <;> omega) (by simp <;> omega) (mem_envRepr_ne_none env) rfl (by simp <;> omega)
  norm_ds at hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_write rfl (by decide) hd₁₀ (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_rewind rfl (by decide) hd₁₁ (by simp <;> omega)
  norm_ds at hr₁₂ hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_write rfl (by decide) hd₁₂ (by simp <;> omega)
  norm_ds at hd₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄⟩ := D_rewind rfl (by decide) hd₁₃ (by simp <;> omega)
  norm_ds at hr₁₄ hd₁₄
  obtain ⟨n₁₅, hn₁₅, c₁₅, hr₁₅, hd₁₅⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₄ (by simp <;> omega) (v := h.toData) (l₁ := []) (l₂ := (ds X).l.drop (S h.toData).length) (by simp <;> omega)
    (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₅
  refine ⟨_, ?_, c₁₅, _,
    ((((((((((((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans
      hr₈).trans hr₉).trans hr₁₀).trans hr₁₁).trans hr₁₂).trans hr₁₃).trans hr₁₄).trans
      hr₁₅).cast_out (by simp <;> omega), hd₁₅, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_cons, List.length_cons, List.length_append, length_S]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [hX]
  · simp [frameRepr, List.append_assoc] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_cons, List.length_cons, List.length_append, length_S, List.length_drop]
    omega


/-! ## Finishing a case: the charge and the jump -/

theorem PreTo.charge_jump {c : Cfg input} {B : ℕ} {k : ProgId} {pc : Fin maxPc} {m' : Machine.Cfg}
    {r xl : ℕ} (h : PreTo c B (at_ k pc) m' (r + 1) (ctrlRepr m'.ctrl).length
      (kontRepr m'.kont).length xl)
    (hins : instrAt k pc = .charge false) (hpc : pc.val + 1 < maxPc)
    (hins' : instrAt k ⟨pc.val + 1, hpc⟩ = .jump .dispatch) : StepTo c (B + 3) m' r xl := by
  obtain ⟨n, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  obtain ⟨c₁, hr₁, hd₁⟩ := D_charge hins hpc hd (r := r) hrep.bud
  obtain ⟨c₂, hr₂, hd₂⟩ := D_jump hins' hd₁
  refine ⟨n + 2 + 1, by omega, c₂, _, ((hr.trans hr₁).trans hr₂).cast_out (by simp <;> omega), hd₂,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨g, hg⟩ := hrep.ctrl
    exact ⟨g, by simp [hg]⟩
  · simp [hrep.env]
  · simp [hrep.kont]
  · simpa using hrep.scratch
  · simp [hrep.cnt]
  · simp
  · simpa using hxl

theorem PreTo.charge_fail {c : Cfg input} {B : ℕ} {k : ProgId} {pc : Fin maxPc} {m' : Machine.Cfg}
    {pC pK xl : ℕ} (h : PreTo c B (at_ k pc) m' 0 pC pK xl) (hins : instrAt k pc = .charge false) :
    HaltsIn c (B + 2) := by
  obtain ⟨n, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  exact (HaltsIn.after hr (D_charge_fail hins hd (by simpa using hrep.bud))).mono (by omega)

theorem PreTo.jump {c : Cfg input} {B : ℕ} {k : ProgId} {pc : Fin maxPc} {m' : Machine.Cfg}
    {r xl : ℕ} (h : PreTo c B (at_ k pc) m' r (ctrlRepr m'.ctrl).length (kontRepr m'.kont).length xl)
    (hins : instrAt k pc = .jump .dispatch) : StepTo c (B + 1) m' r xl := by
  obtain ⟨n, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  obtain ⟨c₁, hr₁, hd₁⟩ := D_jump hins hd
  exact ⟨n + 1, by omega, c₁, _, (hr.trans hr₁).cast_out (by simp <;> omega), hd₁, hrep, hxl⟩

/-! ## `ev elim` -/

/-- `elim` when the value is `nil`: evaluate `n`. -/
theorem case_evElim_nil {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evElim 0) ds)
    {i : ℕ} {n cc : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.elim i n cc), env, k⟩ r 8 (kontRepr k).length)
    (hv : Env.get env i = .nil) :
    PreTo c (caseBound ⟨.ev (.elim i n cc), env, k⟩ (ds X).l.length) (at_ .evElimNil 6)
      ⟨.ev n, env, k⟩ r (ctrlRepr (.ev n)).length (kontRepr k).length
      ((ds X).l.length + sz ⟨.ev (.elim i n cc), env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_rewind rfl (by decide) hd₂ (by simp <;> omega)
  norm_ds at hr₃ hd₃
  obtain ⟨n₄, hn₄, c₄, hr₄, hd₄⟩ := D_getEnv rfl (by decide) hd₃ (env := env) (by simp <;> omega) (i := i)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .zero, .one])
    (l₂ := .one :: (S n.toData ++ S cc.toData) ++ g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  rw [hv] at hd₄
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_move_right rfl (by decide) hd₄
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_rewind rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hr₆ hd₆
  obtain ⟨c₇, hr₇, hd₇⟩ := D_branch_taken rfl hd₆ (by simp <;> omega)
  -- `evElimNil`
  obtain ⟨c₈, hr₈, hd₈⟩ := D_rewind rfl (by decide) hd₇ (by simp <;> omega)
  norm_ds at hr₈ hd₈
  obtain ⟨n₉, hn₉, c₉, hr₉, hd₉⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₈
    (by simp <;> omega) (v := n.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .zero, .one] ++ S (Data.ofNat i) ++ [.one])
    (l₂ := S cc.toData ++ g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_rewind rfl (by decide) hd₉ (by simp <;> omega)
  norm_ds at hr₁₀ hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_write rfl (by decide) hd₁₀ (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_rewind rfl (by decide) hd₁₁ (by simp <;> omega)
  norm_ds at hr₁₂ hd₁₂
  obtain ⟨n₁₃, hn₁₃, c₁₃, hr₁₃, hd₁₃⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₂ (by simp <;> omega) (v := n.toData) (l₁ := [])
    (l₂ := (S .nil ++ (ds X).l.drop (S Data.nil).length).drop (S n.toData).length) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₁₃
  refine ⟨_, ?_, c₁₃, _,
    ((((((((((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans
      hr₈).trans hr₉).trans hr₁₀).trans hr₁₁).trans hr₁₂).trans hr₁₃).cast_out (by simp <;> omega), hd₁₃,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_elim, List.length_cons, List.length_append, length_S,
      length_S_ofNat, Data.size_ofNat, Data.size_nil, Data.size_cons]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_elim, List.length_cons, List.length_append, length_S, length_S_ofNat,
      List.length_drop, Data.size_ofNat, Data.size_nil, Data.size_cons]
    omega

/-- `elim` when the value is a pair: push its components, evaluate `cc`. -/
theorem case_evElim_cons {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evElim 0) ds)
    {i : ℕ} {n cc : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.elim i n cc), env, k⟩ r 8 (kontRepr k).length)
    {a b : Data} (hv : Env.get env i = .cons a b) :
    PreTo c (caseBound ⟨.ev (.elim i n cc), env, k⟩ (ds X).l.length) (at_ .evElimCons 15)
      ⟨.ev cc, a :: b :: env, k⟩ r (ctrlRepr (.ev cc)).length (kontRepr k).length
      ((ds X).l.length + sz ⟨.ev (.elim i n cc), env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  have hab := size_get_le env i
  rw [hv, Data.size_cons] at hab
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_rewind rfl (by decide) hd₂ (by simp <;> omega)
  norm_ds at hr₃ hd₃
  obtain ⟨n₄, hn₄, c₄, hr₄, hd₄⟩ := D_getEnv rfl (by decide) hd₃ (env := env) (by simp <;> omega) (i := i)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .zero, .one])
    (l₂ := .one :: (S n.toData ++ S cc.toData) ++ g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  rw [hv, S_cons] at hd₄
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_move_right rfl (by decide) hd₄
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_rewind rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hr₆ hd₆
  obtain ⟨c₇, hr₇, hd₇⟩ := D_branch_not rfl (by decide) hd₆ (by simp <;> omega)
  obtain ⟨c₈, hr₈, hd₈⟩ := D_jump rfl hd₇
  -- `evElimCons`
  obtain ⟨c₉, hr₉, hd₉⟩ := D_move_right rfl (by decide) hd₈
  norm_ds at hd₉
  obtain ⟨n₁₀, hn₁₀, c₁₀, hr₁₀, hd₁₀⟩ := D_skipTree rfl (by decide) (by decide) hd₉ (by simp <;> omega) (v := a)
    (l₁ := [.one]) (l₂ := S b ++ (ds X).l.drop (S a ++ S b).length.succ) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₀
  obtain ⟨n₁₁, hn₁₁, c₁₁, hr₁₁, hd₁₁⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₀ (by simp <;> omega) (v := b) (l₁ := [.one] ++ S a) (l₂ := (ds X).l.drop (S a ++ S b).length.succ)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_write rfl (by decide) hd₁₁ (by simp <;> omega)
  norm_ds at hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_rewind rfl (by decide) hd₁₂ (by simp <;> omega)
  norm_ds at hr₁₃ hd₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄⟩ := D_move_right rfl (by decide) hd₁₃
  norm_ds at hd₁₄
  obtain ⟨n₁₅, hn₁₅, c₁₅, hr₁₅, hd₁₅⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₄ (by simp <;> omega) (v := a) (l₁ := [.one]) (l₂ := S b ++ (ds X).l.drop (S a ++ S b).length.succ)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₅
  obtain ⟨c₁₆, hr₁₆, hd₁₆⟩ := D_write rfl (by decide) hd₁₅ (by simp <;> omega)
  norm_ds at hd₁₆
  obtain ⟨n₁₇, hn₁₇, c₁₇, hr₁₇, hd₁₇⟩ := D_skipTree rfl (by decide) (by decide) hd₁₆ (by simp <;> omega)
    (v := n.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .zero, .one] ++ S (Data.ofNat i) ++ [.one])
    (l₂ := S cc.toData ++ g) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₇
  obtain ⟨c₁₈, hr₁₈, hd₁₈⟩ := D_rewind rfl (by decide) hd₁₇ (by simp <;> omega)
  norm_ds at hr₁₈ hd₁₈
  obtain ⟨n₁₉, hn₁₉, c₁₉, hr₁₉, hd₁₉⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₈ (by simp <;> omega) (v := cc.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .zero, .one] ++ S (Data.ofNat i) ++ [.one]
      ++ S n.toData) (l₂ := g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₉
  obtain ⟨c₂₀, hr₂₀, hd₂₀⟩ := D_rewind rfl (by decide) hd₁₉ (by simp <;> omega)
  norm_ds at hr₂₀ hd₂₀
  obtain ⟨c₂₁, hr₂₁, hd₂₁⟩ := D_write rfl (by decide) hd₂₀ (by simp <;> omega)
  norm_ds at hd₂₁
  obtain ⟨c₂₂, hr₂₂, hd₂₂⟩ := D_rewind rfl (by decide) hd₂₁ (by simp <;> omega)
  norm_ds at hr₂₂ hd₂₂
  obtain ⟨n₂₃, hn₂₃, c₂₃, hr₂₃, hd₂₃⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₂₂ (by simp <;> omega) (v := cc.toData) (l₁ := [])
    (l₂ := (Sym.one :: (S a ++ (S b ++ (ds X).l.drop (a.size + b.size + 1)))).drop cc.toData.size)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₂₃
  refine ⟨_, ?_, c₂₃, _,
    ((((((((((((((((((((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).trans
      hr₇).trans hr₈).trans hr₉).trans hr₁₀).trans hr₁₁).trans hr₁₂).trans hr₁₃).trans hr₁₄).trans
      hr₁₅).trans hr₁₆).trans hr₁₇).trans hr₁₈).trans hr₁₉).trans hr₂₀).trans hr₂₁).trans
      hr₂₂).trans hr₂₃).cast_out (by simp <;> omega), hd₂₃, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_elim, List.length_cons, List.length_append, length_S,
      length_S_ofNat, Data.size_ofNat, Data.size_nil, Data.size_cons]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [List.append_assoc] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_elim, List.length_cons, List.length_append, length_S, length_S_ofNat,
      List.length_drop, Data.size_ofNat, Data.size_nil, Data.size_cons]
    omega

/-! ## `ev let` and `ev loop` -/

theorem case_evLet {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evLet 0) ds)
    {e b : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.let_ e b), env, k⟩ r 10 (kontRepr k).length) :
    PreTo c (caseBound ⟨.ev (.let_ e b), env, k⟩ (ds X).l.length) (at_ .evLet 15)
      ⟨.ev e, env, .let1 b env :: k⟩ r (ctrlRepr (.ev e)).length
      (kontRepr (.let1 b env :: k)).length ((ds X).l.length + sz ⟨.ev (.let_ e b), env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_rewind rfl (by decide) hd₂ (by simp <;> omega)
  norm_ds at hr₃ hd₃
  obtain ⟨n₄, hn₄, c₄, hr₄, hd₄⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₃
    (by simp <;> omega) (v := e.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .zero, .one])
    (l₂ := S b.toData ++ g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_write rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_write rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hd₆
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₆
    (by simp <;> omega) (v := b.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .zero, .one] ++ S e.toData)
    (l₂ := g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_write rfl (by decide) hd₇ (by simp <;> omega)
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_rewind rfl (by decide) hd₈ (by simp <;> omega)
  norm_ds at hr₉ hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_copyUntil rfl (by decide) (by decide) hd₉ (l₁ := []) (w := envRepr env)
    (l₂ := []) (by simp <;> omega) (by simp <;> omega) (mem_envRepr_ne_none env) rfl (by simp <;> omega)
  norm_ds at hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_write rfl (by decide) hd₁₀ (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_rewind rfl (by decide) hd₁₁ (by simp <;> omega)
  norm_ds at hr₁₂ hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_write rfl (by decide) hd₁₂ (by simp <;> omega)
  norm_ds at hd₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄⟩ := D_rewind rfl (by decide) hd₁₃ (by simp <;> omega)
  norm_ds at hr₁₄ hd₁₄
  obtain ⟨n₁₅, hn₁₅, c₁₅, hr₁₅, hd₁₅⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₄ (by simp <;> omega) (v := e.toData) (l₁ := []) (l₂ := (ds X).l.drop (S e.toData).length) (by simp <;> omega)
    (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₅
  refine ⟨_, ?_, c₁₅, _,
    ((((((((((((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans
      hr₈).trans hr₉).trans hr₁₀).trans hr₁₁).trans hr₁₂).trans hr₁₃).trans hr₁₄).trans
      hr₁₅).cast_out (by simp <;> omega), hd₁₅, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_let, List.length_cons, List.length_append, length_S]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [hX]
  · simp [frameRepr, List.append_assoc] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_let, List.length_cons, List.length_append, length_S, List.length_drop]
    omega

theorem case_evLoop {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evLoop 0) ds)
    {b : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.loop b), env, k⟩ r 12 (kontRepr k).length) :
    StepTo c (caseBound ⟨.ev (.loop b), env, k⟩ (ds X).l.length) ⟨.ev b, env, .loop1 b env :: k⟩ r
      ((ds X).l.length + sz ⟨.ev (.loop b), env, k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₂
    (by simp <;> omega) (v := b.toData)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .zero])
    (l₂ := g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_write rfl (by decide) hd₃ (by simp <;> omega)
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_write rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_rewind rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hr₆ hd₆
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₆
    (by simp <;> omega) (v := b.toData) (l₁ := []) (l₂ := (ds X).l.drop (S b.toData).length) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_write rfl (by decide) hd₇ (by simp <;> omega)
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_rewind rfl (by decide) hd₈ (by simp <;> omega)
  norm_ds at hr₉ hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_copyUntil rfl (by decide) (by decide) hd₉ (l₁ := []) (w := envRepr env)
    (l₂ := []) (by simp <;> omega) (by simp <;> omega) (mem_envRepr_ne_none env) rfl (by simp <;> omega)
  norm_ds at hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_write rfl (by decide) hd₁₀ (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_rewind rfl (by decide) hd₁₁ (by simp <;> omega)
  norm_ds at hr₁₂ hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_write rfl (by decide) hd₁₂ (by simp <;> omega)
  norm_ds at hd₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄⟩ := D_rewind rfl (by decide) hd₁₃ (by simp <;> omega)
  norm_ds at hr₁₄ hd₁₄
  obtain ⟨n₁₅, hn₁₅, c₁₅, hr₁₅, hd₁₅⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₄ (by simp <;> omega) (v := b.toData) (l₁ := []) (l₂ := (ds X).l.drop (S b.toData).length) (by simp <;> omega)
    (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₅
  obtain ⟨c₁₆, hr₁₆, hd₁₆⟩ := D_jump rfl hd₁₅
  refine ⟨_, ?_, c₁₆, _,
    (((((((((((((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).trans hr₇).trans
      hr₈).trans hr₉).trans hr₁₀).trans hr₁₁).trans hr₁₂).trans hr₁₃).trans hr₁₄).trans
      hr₁₅).trans hr₁₆).cast_out (by simp <;> omega), hd₁₆, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_loop, List.length_cons, List.length_append, length_S]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [hX]
  · simp [frameRepr, List.append_assoc] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_loop, List.length_cons, List.length_append, length_S, List.length_drop]
    omega


/-! ## The dispatcher on `ret` -/

/-- The case program of a return to a frame. -/
def retTarget : Frame → ProgId
  | .cons1 _ _ => .retCons1
  | .cons2 _ => .retCons2
  | .let1 _ _ => .retLet1
  | .loop1 _ _ => .retLoop1

theorem frameBody_cons1 (t : Prog) (env : Env) :
    frameBody (.cons1 t env) = .zero :: .zero :: (S t.toData ++ [.en] ++ envRepr env) := by
  simp [frameBody]

theorem frameBody_cons2 (a : Data) : frameBody (.cons2 a) = .zero :: .one :: S a := by
  simp [frameBody]

theorem frameBody_let1 (b : Prog) (env : Env) :
    frameBody (.let1 b env) = .one :: .zero :: (S b.toData ++ [.en] ++ envRepr env) := by
  simp [frameBody]

theorem frameBody_loop1 (b : Prog) (env : Env) :
    frameBody (.loop1 b env) = .one :: .one :: (S b.toData ++ [.en] ++ envRepr env) := by
  simp [frameBody]

theorem kontRepr_cons' (f : Frame) (k : List Frame) :
    kontRepr (f :: k) = kontRepr k ++ frameBody f ++ [.fr] := by
  simp [frameRepr_eq]

theorem getElem?_append_right' (l₁ l₂ : List Sym) {i j : ℕ} (h : i = l₁.length + j) :
    (l₁ ++ l₂)[i]? = l₂[j]? := by
  subst h; rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- The two tag bits of a frame, read off the stack. -/
theorem read_tag (k : List Frame) (f : Frame) (j : ℕ) (hj : j < 2) :
    (kontRepr k ++ frameBody f ++ [Sym.fr])[(kontRepr k).length + j]? = (frameTag f)[j]? := by
  have h2 : (frameTag f).length = 2 := by cases f <;> rfl
  have hb : frameBody f = frameTag f ++ (frameBody f).drop 2 := by
    cases f <;> simp [frameBody, frameTag]
  rw [List.append_assoc, getElem?_append_right' _ _ rfl, hb, List.append_assoc,
    List.getElem?_append_left (by omega)]

theorem read_tag0 (k : List Frame) (f : Frame) :
    (kontRepr k ++ frameBody f ++ [Sym.fr])[(kontRepr k).length]? = (frameTag f)[0]? := by
  simpa using read_tag k f 0 (by norm_num)

theorem read_tag1 (k : List Frame) (f : Frame) :
    (kontRepr k ++ frameBody f ++ [Sym.fr])[(kontRepr k).length + 1]? = (frameTag f)[1]? :=
  read_tag k f 1 (by norm_num)

theorem read_end (k : List Frame) (f : Frame) :
    (kontRepr k ++ frameBody f ++ [Sym.fr])[(kontRepr k).length + (frameBody f).length]? = some .fr := by
  rw [List.append_assoc, getElem?_append_right' _ _ rfl, List.getElem?_concat_length]

/-- From the dispatcher, a return to a frame reaches its case program with the head of `C`
on the value and the head of `K` on the second tag bit. -/
theorem dispatch_ret {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {v : Data} {env : Env} {f : Frame} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret v, env, f :: k⟩ r (ctrlRepr (.ret v)).length (kontRepr (f :: k)).length) :
    PreTo1 c (v.size + (frameBody f).length + 20) (at_ (retTarget f) 0) ⟨.ret v, env, f :: k⟩ r 1
      ((kontRepr k).length + 1) (ds X).l.length := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons'] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_rewind rfl (by decide) hd (by simp <;> omega)
  norm_ds at hr₁ hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_branch_not rfl (by decide) hd₁ (by simp)
  obtain ⟨c₃, hr₃, hd₃⟩ := D_move_right rfl (by decide) hd₂
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_move_left rfl (by decide) hd₃ (by simp <;> omega)
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_branch_not rfl (by decide) hd₄ (by simp [read_end])
  obtain ⟨c₆, hr₆, hd₆⟩ := D_leftToMarker rfl (by decide) hd₅ (l₁ := kontRepr k) (w := frameBody f)
    (l₂ := [.fr]) (by simp) (by simp <;> omega) (frameBody_ne_fr f) (kontRepr_nil_or_fr k)
  norm_ds at hd₆
  have hR := hr₁.trans hr₂
  have hR := hR.trans hr₃
  have hR := hR.trans hr₄
  have hR := hR.trans hr₅
  have hR := hR.trans hr₆
  have hR : Reach c _ c₆ [] := hR.cast_out (by simp)
  -- the tag
  have fin : ∀ (m : ℕ) (c' : Cfg input) (ds' : WT → TapeSt), Reach c₆ m c' [] → m ≤ 4 →
      Desc c' (at_ (retTarget f) 0) ds' →
      RepOf ds' ⟨.ret v, env, f :: k⟩ r 1 ((kontRepr k).length + 1) →
      (ds' X).l.length ≤ (ds X).l.length →
      PreTo1 c (v.size + (frameBody f).length + 20) (at_ (retTarget f) 0) ⟨.ret v, env, f :: k⟩ r 1
        ((kontRepr k).length + 1) (ds X).l.length := by
    intro m c' ds' hr' hm hd' hrep hxl
    exact ⟨_, by omega, by omega, c', ds', (hR.trans hr').cast_out (by simp), hd', hrep, hxl⟩
  cases f with
  | cons1 t env' =>
    obtain ⟨c₇, hr₇, hd₇⟩ := D_branch_taken rfl hd₆ (by norm_ds_goal; rw [read_tag0]; rfl)
    obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
    norm_ds at hd₈
    obtain ⟨c₉, hr₉, hd₉⟩ := D_branch_taken rfl hd₈ (by norm_ds_goal; rw [read_tag1]; rfl)
    refine fin 3 c₉ _ (((hr₇.trans hr₈).trans hr₉).cast_out (by simp)) (by norm_num) hd₉
      ⟨⟨g, by simp [ctrlRepr_ret]⟩, by simp, by simp [kontRepr_cons', frameRepr_eq], by simp [hX], by simp,
        by simp⟩
      (by simp)
  | cons2 a =>
    obtain ⟨c₇, hr₇, hd₇⟩ := D_branch_taken rfl hd₆ (by norm_ds_goal; rw [read_tag0]; rfl)
    obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
    norm_ds at hd₈
    obtain ⟨c₉, hr₉, hd₉⟩ := D_branch_not rfl (by decide) hd₈ (by norm_ds_goal; rw [read_tag1]; simp [frameTag])
    obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_jump rfl hd₉
    refine fin 4 c₁₀ _ ((((hr₇.trans hr₈).trans hr₉).trans hr₁₀).cast_out (by simp)) (by norm_num) hd₁₀
      ⟨⟨g, by simp [ctrlRepr_ret]⟩, by simp, by simp [kontRepr_cons', frameRepr_eq], by simp [hX], by simp,
        by simp⟩
      (by simp)
  | let1 b env' =>
    obtain ⟨c₇, hr₇, hd₇⟩ := D_branch_not rfl (by decide) hd₆ (by norm_ds_goal; rw [read_tag0]; simp [frameTag])
    obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
    norm_ds at hd₈
    obtain ⟨c₉, hr₉, hd₉⟩ := D_branch_taken rfl hd₈ (by norm_ds_goal; rw [read_tag1]; rfl)
    refine fin 3 c₉ _ (((hr₇.trans hr₈).trans hr₉).cast_out (by simp)) (by norm_num) hd₉
      ⟨⟨g, by simp [ctrlRepr_ret]⟩, by simp, by simp [kontRepr_cons', frameRepr_eq], by simp [hX], by simp,
        by simp⟩
      (by simp)
  | loop1 b env' =>
    obtain ⟨c₇, hr₇, hd₇⟩ := D_branch_not rfl (by decide) hd₆ (by norm_ds_goal; rw [read_tag0]; simp [frameTag])
    obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
    norm_ds at hd₈
    obtain ⟨c₉, hr₉, hd₉⟩ := D_branch_not rfl (by decide) hd₈ (by norm_ds_goal; rw [read_tag1]; simp [frameTag])
    obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_jump rfl hd₉
    refine fin 4 c₁₀ _ ((((hr₇.trans hr₈).trans hr₉).trans hr₁₀).cast_out (by simp)) (by norm_num) hd₁₀
      ⟨⟨g, by simp [ctrlRepr_ret]⟩, by simp, by simp [kontRepr_cons', frameRepr_eq], by simp [hX], by simp,
        by simp⟩
      (by simp)

/-! ## Popping the innermost environment entry -/

theorem D_popEnv {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
    (hins : instrAt k pc = .popBack .sep E) (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds)
    {env' : Env} (hE : ds E = ⟨envRepr env', (envRepr env').length⟩) :
    ∃ n ≤ (envRepr env').length + 3, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update ds E ⟨envRepr env'.tail, (envRepr env'.tail).length⟩) := by
  cases env' with
  | nil =>
    obtain ⟨c', hr, hd'⟩ := D_popBack_empty hins hpc hd (by simp [hE]) (by simp [hE])
    refine ⟨2, by simp, c', hr, hd'.cast rfl ?_⟩
    rw [show (⟨envRepr [].tail, (envRepr [].tail).length⟩ : TapeSt) = ds E by simp [hE]]
    exact (Function.update_eq_self E ds).symm
  | cons e₁ rest =>
    obtain ⟨c', hr, hd'⟩ := D_popBack hins hpc hd (l₁ := envRepr rest) (w := S e₁) (a := .sep)
      (by simp [hE]) (by simp [hE])
      (fun s hs h => by subst h; rcases mem_S e₁ _ hs with h | h <;> simp at h)
      (envRepr_nil_or_sep rest)
    exact ⟨_, by simp; omega, c', hr, hd'⟩

theorem drop_env_ne_fr (env : Env) (n : ℕ) : ∀ s ∈ (envRepr env).drop n, s ≠ Sym.fr :=
  fun s hs => (mem_envRepr env s (List.mem_of_mem_drop hs)).1

/-! ## The cases: `ret` -/

theorem case_retCons1 {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retCons1 0) ds)
    {v : Data} {t : Prog} {env env' : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret v, env, .cons1 t env' :: k⟩ r 1 ((kontRepr k).length + 1)) :
    StepTo c (caseBound ⟨.ret v, env, .cons1 t env' :: k⟩ (ds X).l.length)
      ⟨.ev t, env', .cons2 v :: k⟩ r ((ds X).l.length + sz ⟨.ret v, env, .cons1 t env' :: k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons', frameBody_cons1] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₂
    (by simp <;> omega) (v := t.toData) (l₁ := kontRepr k ++ [.zero, .zero])
    (l₂ := [.en] ++ envRepr env' ++ [.fr]) (by simp [List.append_assoc]) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_move_right rfl (by decide) hd₃
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_rewind rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hr₅ hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_copyUntil rfl (by decide) (by decide) hd₅
    (l₁ := kontRepr k ++ [.zero, .zero] ++ S t.toData ++ [.en]) (w := envRepr env') (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_fr env') rfl (by simp <;> omega)
  norm_ds at hd₆
  obtain ⟨c₇, hr₇, hd₇⟩ := D_eraseRight rfl (by decide) hd₆ (by simp <;> omega)
    (by simp only [Function.update_self, List.drop_left']; exact drop_env_ne_fr env _)
  norm_ds at hr₇ hd₇
  simp only [List.take_left'] at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_popBack rfl (by decide) hd₈ (l₁ := kontRepr k)
    (w := .zero :: .zero :: (S t.toData ++ [.en] ++ envRepr env')) (a := .fr)
    (by simp [List.append_assoc]) (by simp <;> omega)
    (by simpa [frameBody_cons1] using frameBody_ne_fr (.cons1 t env')) (kontRepr_nil_or_fr k)
  norm_ds at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_write rfl (by decide) hd₉ (by simp <;> omega)
  norm_ds at hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_write rfl (by decide) hd₁₀ (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨n₁₂, hn₁₂, c₁₂, hr₁₂, hd₁₂⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₁ (by simp <;> omega) (v := v) (l₁ := [.one]) (l₂ := g) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_write rfl (by decide) hd₁₂ (by simp <;> omega)
  norm_ds at hd₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄⟩ := D_rewind rfl (by decide) hd₁₃ (by simp <;> omega)
  norm_ds at hr₁₄ hd₁₄
  obtain ⟨c₁₅, hr₁₅, hd₁₅⟩ := D_write rfl (by decide) hd₁₄ (by simp <;> omega)
  norm_ds at hd₁₅
  obtain ⟨c₁₆, hr₁₆, hd₁₆⟩ := D_rewind rfl (by decide) hd₁₅ (by simp <;> omega)
  norm_ds at hr₁₆ hd₁₆
  obtain ⟨n₁₇, hn₁₇, c₁₇, hr₁₇, hd₁₇⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₆ (by simp <;> omega) (v := t.toData) (l₁ := []) (l₂ := (ds X).l.drop (S t.toData).length)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₇
  obtain ⟨c₁₈, hr₁₈, hd₁₈⟩ := D_jump rfl hd₁₇
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
  refine ⟨_, ?_, c₁₈, _, hR.cast_out (by simp), hd₁₈, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_ret, kontRepr_cons', frameBody_cons1, List.length_cons,
      List.length_append, length_S, List.length_singleton, List.length_nil, List.length_drop,
      Data.size_cons, Data.size_nil]
    omega
  · simp [ctrlRepr] <;> omega
  · simp
  · simp [kontRepr_cons, frameRepr, List.append_assoc] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_ret, kontRepr_cons', frameBody_cons1, List.length_cons, List.length_append,
      length_S, List.length_singleton, List.length_drop, List.length_nil, Data.size_cons, Data.size_nil]
    omega

theorem case_retCons2 {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retCons2 0) ds)
    {v a : Data} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret v, env, .cons2 a :: k⟩ r 1 ((kontRepr k).length + 1)) :
    StepTo c (caseBound ⟨.ret v, env, .cons2 a :: k⟩ (ds X).l.length)
      ⟨.ret (.cons a v), env, k⟩ r ((ds X).l.length + sz ⟨.ret v, env, .cons2 a :: k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons', frameBody_cons2] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_write rfl (by decide) hd₂ (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨n₄, hn₄, c₄, hr₄, hd₄⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₃
    (by simp <;> omega) (v := a) (l₁ := kontRepr k ++ [.zero, .one]) (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₄
  obtain ⟨n₅, hn₅, c₅, hr₅, hd₅⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₄
    (by simp <;> omega) (v := v) (l₁ := [.one]) (l₂ := g) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_move_right rfl (by decide) hd₅
  norm_ds at hd₆
  obtain ⟨c₇, hr₇, hd₇⟩ := D_popBack rfl (by decide) hd₆ (l₁ := kontRepr k)
    (w := .zero :: .one :: S a) (a := .fr) (by simp [List.append_assoc]) (by simp <;> omega)
    (by simpa [frameBody_cons2] using frameBody_ne_fr (.cons2 a)) (kontRepr_nil_or_fr k)
  norm_ds at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_rewind rfl (by decide) hd₇ (by simp <;> omega)
  norm_ds at hr₈ hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_write rfl (by decide) hd₈ (by simp <;> omega)
  norm_ds at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_rewind rfl (by decide) hd₉ (by simp <;> omega)
  norm_ds at hr₁₀ hd₁₀
  obtain ⟨n₁₁, hn₁₁, c₁₁, hr₁₁, hd₁₁⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₀ (by simp <;> omega) (v := .cons a v) (l₁ := [])
    (l₂ := (((ds X).l.drop 1).drop a.size).drop v.size) (by simp [S_cons, List.append_assoc])
    (by simp <;> omega) (by simp <;> omega)
  simp only [Data.size_cons] at hn₁₁
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_jump rfl hd₁₁
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
  refine ⟨_, ?_, c₁₂, _, hR.cast_out (by simp), hd₁₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_ret, kontRepr_cons', frameBody_cons2, List.length_cons,
      List.length_append, length_S, List.length_singleton, List.length_nil, List.length_drop,
      Data.size_cons, Data.size_nil]
    omega
  · simp [ctrlRepr_ret, S_cons] <;> omega
  · simp
  · simp
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_ret, kontRepr_cons', frameBody_cons2, List.length_cons, List.length_append,
      length_S, List.length_singleton, List.length_drop, S_cons, Data.size_cons, List.length_nil,
      Data.size_nil]
    omega

theorem case_retLet1 {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retLet1 0) ds)
    {v : Data} {b : Prog} {env env' : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret v, env, .let1 b env' :: k⟩ r 1 ((kontRepr k).length + 1)) :
    StepTo c (caseBound ⟨.ret v, env, .let1 b env' :: k⟩ (ds X).l.length)
      ⟨.ev b, v :: env', k⟩ r ((ds X).l.length + sz ⟨.ret v, env, .let1 b env' :: k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons', frameBody_let1] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  norm_ds at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  norm_ds at hr₂ hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₂
    (by simp <;> omega) (v := b.toData) (l₁ := kontRepr k ++ [.one, .zero])
    (l₂ := [.en] ++ envRepr env' ++ [.fr]) (by simp [List.append_assoc]) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_move_right rfl (by decide) hd₃
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_rewind rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hr₅ hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_copyUntil rfl (by decide) (by decide) hd₅
    (l₁ := kontRepr k ++ [.one, .zero] ++ S b.toData ++ [.en]) (w := envRepr env') (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_fr env') rfl (by simp <;> omega)
  norm_ds at hd₆
  obtain ⟨c₇, hr₇, hd₇⟩ := D_eraseRight rfl (by decide) hd₆ (by simp <;> omega)
    (by simp only [Function.update_self, List.drop_left']; exact drop_env_ne_fr env _)
  norm_ds at hr₇ hd₇
  simp only [List.take_left'] at hd₇
  obtain ⟨n₈, hn₈, c₈, hr₈, hd₈⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₇
    (by simp <;> omega) (v := v) (l₁ := [.one]) (l₂ := g) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_write rfl (by decide) hd₈ (by simp <;> omega)
  norm_ds at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_move_right rfl (by decide) hd₉
  norm_ds at hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_popBack rfl (by decide) hd₁₀ (l₁ := kontRepr k)
    (w := .one :: .zero :: (S b.toData ++ [.en] ++ envRepr env')) (a := .fr)
    (by simp [List.append_assoc]) (by simp <;> omega)
    (by simpa [frameBody_let1] using frameBody_ne_fr (.let1 b env')) (kontRepr_nil_or_fr k)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_rewind rfl (by decide) hd₁₁ (by simp <;> omega)
  norm_ds at hr₁₂ hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_write rfl (by decide) hd₁₂ (by simp <;> omega)
  norm_ds at hd₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄⟩ := D_rewind rfl (by decide) hd₁₃ (by simp <;> omega)
  norm_ds at hr₁₄ hd₁₄
  obtain ⟨n₁₅, hn₁₅, c₁₅, hr₁₅, hd₁₅⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₄ (by simp <;> omega) (v := b.toData) (l₁ := []) (l₂ := (ds X).l.drop (S b.toData).length)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₅
  obtain ⟨c₁₆, hr₁₆, hd₁₆⟩ := D_jump rfl hd₁₅
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
  refine ⟨_, ?_, c₁₆, _, hR.cast_out (by simp), hd₁₆, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_ret, kontRepr_cons', frameBody_let1, List.length_cons,
      List.length_append, length_S, List.length_singleton, List.length_nil, List.length_drop,
      Data.size_cons, Data.size_nil]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [List.append_assoc] <;> omega
  · simp
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_ret, kontRepr_cons', frameBody_let1, List.length_cons, List.length_append,
      length_S, List.length_singleton, List.length_drop, List.length_nil, Data.size_cons, Data.size_nil]
    omega


/-! ## `ret` to a `loop1` frame -/

theorem case_retLoopNil {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retLoop1 0) ds)
    {b : Prog} {env env' : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret .nil, env, .loop1 b env' :: k⟩ r 1 ((kontRepr k).length + 1)) :
    PreTo c (caseBound ⟨.ret .nil, env, .loop1 b env' :: k⟩ (ds X).l.length) (at_ .retLoopNil 11)
      ⟨.ret .nil, env', k⟩ r (ctrlRepr (.ret .nil)).length (kontRepr k).length
      ((ds X).l.length + sz ⟨.ret .nil, env, .loop1 b env' :: k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons', frameBody_loop1] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_branch_taken rfl hd (by simp)
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  norm_ds at hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_skipTree rfl (by decide) (by decide) hd₂ (by simp <;> omega)
    (v := b.toData) (l₁ := kontRepr k ++ [.one, .one]) (l₂ := [.en] ++ envRepr env' ++ [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega)
  norm_ds at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_move_right rfl (by decide) hd₃
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_rewind rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hr₅ hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_copyUntil rfl (by decide) (by decide) hd₅
    (l₁ := kontRepr k ++ [.one, .one] ++ S b.toData ++ [.en]) (w := envRepr env') (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_fr env') rfl (by simp <;> omega)
  norm_ds at hd₆
  obtain ⟨c₇, hr₇, hd₇⟩ := D_eraseRight rfl (by decide) hd₆ (by simp <;> omega)
    (by simp only [Function.update_self, List.drop_left']; exact drop_env_ne_fr env _)
  norm_ds at hr₇ hd₇
  simp only [List.take_left'] at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_popBack rfl (by decide) hd₈ (l₁ := kontRepr k)
    (w := .one :: .one :: (S b.toData ++ [.en] ++ envRepr env')) (a := .fr)
    (by simp [List.append_assoc]) (by simp <;> omega)
    (by simpa [frameBody_loop1] using frameBody_ne_fr (.loop1 b env')) (kontRepr_nil_or_fr k)
  norm_ds at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_rewind rfl (by decide) hd₉ (by simp <;> omega)
  norm_ds at hr₁₀ hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_write rfl (by decide) hd₁₀ (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_write rfl (by decide) hd₁₁ (by simp <;> omega)
  norm_ds at hd₁₂
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
  refine ⟨_, ?_, c₁₂, _, hR.cast_out (by simp), hd₁₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons,
      List.length_append, length_S, List.length_singleton, List.length_nil, List.length_drop,
      Data.size_cons, Data.size_nil, S_nil]
    omega
  · simp [ctrlRepr_ret] <;> omega
  · simp
  · simp
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons, List.length_append,
      length_S, List.length_singleton, List.length_drop, List.length_nil, Data.size_cons, Data.size_nil]
    omega

theorem case_retLoopStop {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retLoop1 0) ds)
    {r' : Data} {b : Prog} {env env' : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret (.cons .nil r'), env, .loop1 b env' :: k⟩ r 1 ((kontRepr k).length + 1)) :
    PreTo c (caseBound ⟨.ret (.cons .nil r'), env, .loop1 b env' :: k⟩ (ds X).l.length)
      (at_ .retLoopStop 15) ⟨.ret r', env', k⟩ r (ctrlRepr (.ret r')).length (kontRepr k).length
      ((ds X).l.length + sz ⟨.ret (.cons .nil r'), env, .loop1 b env' :: k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons', frameBody_loop1] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_branch_not rfl (by decide) hd (by simp)
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_branch_taken rfl hd₂ (by simp)
  -- `retLoopStop`
  obtain ⟨c₄, hr₄, hd₄⟩ := D_move_right rfl (by decide) hd₃
  norm_ds at hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_rewind rfl (by decide) hd₄ (by simp <;> omega)
  norm_ds at hr₅ hd₅
  obtain ⟨n₆, hn₆, c₆, hr₆, hd₆⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₅
    (by simp <;> omega) (v := r') (l₁ := [.one, .one, .zero]) (l₂ := g) (by simp <;> omega)
    (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₆
  obtain ⟨c₇, hr₇, hd₇⟩ := D_move_right rfl (by decide) hd₆
  norm_ds at hd₇
  obtain ⟨n₈, hn₈, c₈, hr₈, hd₈⟩ := D_skipTree rfl (by decide) (by decide) hd₇ (by simp <;> omega)
    (v := b.toData) (l₁ := kontRepr k ++ [.one, .one]) (l₂ := [.en] ++ envRepr env' ++ [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega)
  norm_ds at hd₈
  obtain ⟨c₉, hr₉, hd₉⟩ := D_move_right rfl (by decide) hd₈
  norm_ds at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_rewind rfl (by decide) hd₉ (by simp <;> omega)
  norm_ds at hr₁₀ hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_copyUntil rfl (by decide) (by decide) hd₁₀
    (l₁ := kontRepr k ++ [.one, .one] ++ S b.toData ++ [.en]) (w := envRepr env') (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_fr env') rfl (by simp <;> omega)
  norm_ds at hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_eraseRight rfl (by decide) hd₁₁ (by simp <;> omega)
    (by simp only [Function.update_self, List.drop_left']; exact drop_env_ne_fr env _)
  norm_ds at hr₁₂ hd₁₂
  simp only [List.take_left'] at hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_move_right rfl (by decide) hd₁₂
  norm_ds at hd₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄⟩ := D_popBack rfl (by decide) hd₁₃ (l₁ := kontRepr k)
    (w := .one :: .one :: (S b.toData ++ [.en] ++ envRepr env')) (a := .fr)
    (by simp [List.append_assoc]) (by simp <;> omega)
    (by simpa [frameBody_loop1] using frameBody_ne_fr (.loop1 b env')) (kontRepr_nil_or_fr k)
  norm_ds at hd₁₄
  obtain ⟨c₁₅, hr₁₅, hd₁₅⟩ := D_rewind rfl (by decide) hd₁₄ (by simp <;> omega)
  norm_ds at hr₁₅ hd₁₅
  obtain ⟨c₁₆, hr₁₆, hd₁₆⟩ := D_write rfl (by decide) hd₁₅ (by simp <;> omega)
  norm_ds at hd₁₆
  obtain ⟨c₁₇, hr₁₇, hd₁₇⟩ := D_rewind rfl (by decide) hd₁₆ (by simp <;> omega)
  norm_ds at hr₁₇ hd₁₇
  obtain ⟨n₁₈, hn₁₈, c₁₈, hr₁₈, hd₁₈⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₇ (by simp <;> omega) (v := r') (l₁ := []) (l₂ := (ds X).l.drop (S r').length)
    (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₈
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
  refine ⟨_, ?_, c₁₈, _, hR.cast_out (by simp), hd₁₈, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons,
      List.length_append, length_S, List.length_singleton, List.length_nil, List.length_drop,
      Data.size_cons, Data.size_nil, S_cons, S_nil]
    omega
  · simp [ctrlRepr_ret] <;> omega
  · simp
  · simp
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons, List.length_append,
      length_S, List.length_singleton, List.length_drop, List.length_nil, Data.size_cons, Data.size_nil,
      S_cons, S_nil]
    omega

theorem case_retLoopCont {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retLoop1 0) ds)
    {y z v' : Data} {b : Prog} {env env' : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret (.cons (.cons y z) v'), env, .loop1 b env' :: k⟩ r 1
      ((kontRepr k).length + 1)) :
    PreTo c (caseBound ⟨.ret (.cons (.cons y z) v'), env, .loop1 b env' :: k⟩ (ds X).l.length)
      (at_ .retLoopCont 29) ⟨.ev b, v' :: env'.tail, .loop1 b (v' :: env'.tail) :: k⟩ r
      (ctrlRepr (.ev b)).length (kontRepr (.loop1 b (v' :: env'.tail) :: k)).length
      ((ds X).l.length + sz ⟨.ret (.cons (.cons y z) v'), env, .loop1 b env' :: k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons', frameBody_loop1] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_branch_not rfl (by decide) hd (by simp)
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  norm_ds at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_branch_not rfl (by decide) hd₂ (by simp)
  obtain ⟨c₄, hr₄, hd₄⟩ := D_jump rfl hd₃
  -- `retLoopCont`
  obtain ⟨n₅, hn₅, c₅, hr₅, hd₅⟩ := D_skipTree rfl (by decide) (by decide) hd₄ (by simp <;> omega)
    (v := .cons y z) (l₁ := [.one, .one]) (l₂ := S v' ++ g) (by simp [S_cons, List.append_assoc])
    (by simp <;> omega)
  simp only [Data.size_cons] at hn₅
  norm_ds at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_rewind rfl (by decide) hd₅ (by simp <;> omega)
  norm_ds at hr₆ hd₆
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₆
    (by simp <;> omega) (v := v') (l₁ := [.one, .one] ++ S (.cons y z)) (l₂ := g)
    (by simp [S_cons, List.append_assoc]) (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
  norm_ds at hd₈
  obtain ⟨n₉, hn₉, c₉, hr₉, hd₉⟩ := D_skipTree rfl (by decide) (by decide) hd₈ (by simp <;> omega)
    (v := b.toData) (l₁ := kontRepr k ++ [.one, .one]) (l₂ := [.en] ++ envRepr env' ++ [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega)
  norm_ds at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_move_right rfl (by decide) hd₉
  norm_ds at hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_rewind rfl (by decide) hd₁₀ (by simp <;> omega)
  norm_ds at hr₁₁ hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_copyUntil rfl (by decide) (by decide) hd₁₁
    (l₁ := kontRepr k ++ [.one, .one] ++ S b.toData ++ [.en]) (w := envRepr env') (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_fr env') rfl (by simp <;> omega)
  norm_ds at hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_eraseRight rfl (by decide) hd₁₂ (by simp <;> omega)
    (by simp only [Function.update_self, List.drop_left']; exact drop_env_ne_fr env _)
  norm_ds at hr₁₃ hd₁₃
  simp only [List.take_left'] at hd₁₃
  obtain ⟨n₁₄, hn₁₄, c₁₄, hr₁₄, hd₁₄⟩ := D_popEnv rfl (by decide) hd₁₃ (env' := env') (by simp)
  norm_ds at hd₁₄
  obtain ⟨c₁₅, hr₁₅, hd₁₅⟩ := D_rewind rfl (by decide) hd₁₄ (by simp <;> omega)
  norm_ds at hr₁₅ hd₁₅
  obtain ⟨n₁₆, hn₁₆, c₁₆, hr₁₆, hd₁₆⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₅ (by simp <;> omega) (v := v') (l₁ := []) (l₂ := (ds X).l.drop v'.size) (by simp <;> omega)
    (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₁₆
  obtain ⟨c₁₇, hr₁₇, hd₁₇⟩ := D_write rfl (by decide) hd₁₆ (by simp <;> omega)
  norm_ds at hd₁₇
  obtain ⟨c₁₈, hr₁₈, hd₁₈⟩ := D_move_right rfl (by decide) hd₁₇
  norm_ds at hd₁₈
  obtain ⟨c₁₉, hr₁₉, hd₁₉⟩ := D_popBack rfl (by decide) hd₁₈
    (l₁ := kontRepr k ++ [.one, .one] ++ S b.toData ++ [.en]) (w := envRepr env') (a := .fr)
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_en env')
    (Or.inr ⟨kontRepr k ++ [.one, .one] ++ S b.toData, by simp⟩)
  norm_ds at hd₁₉
  obtain ⟨c₂₀, hr₂₀, hd₂₀⟩ := D_rewind rfl (by decide) hd₁₉ (by simp <;> omega)
  norm_ds at hr₂₀ hd₂₀
  obtain ⟨c₂₁, hr₂₁, hd₂₁⟩ := D_copyUntil rfl (by decide) (by decide) hd₂₀ (l₁ := [])
    (w := envRepr env'.tail ++ S v' ++ [.sep]) (l₂ := []) (by simp [List.append_assoc])
    (by simp <;> omega) (fun _ _ => Option.some_ne_none _) rfl (by simp <;> omega)
  norm_ds at hd₂₁
  obtain ⟨c₂₂, hr₂₂, hd₂₂⟩ := D_write rfl (by decide) hd₂₁ (by simp <;> omega)
  norm_ds at hd₂₂
  obtain ⟨c₂₃, hr₂₃, hd₂₃⟩ := D_move_left rfl (by decide) hd₂₂ (by simp <;> omega)
  norm_ds at hd₂₃
  obtain ⟨c₂₄, hr₂₄, hd₂₄⟩ := D_leftToMarker rfl (by decide) hd₂₃ (l₁ := kontRepr k)
    (w := .one :: .one :: (S b.toData ++ [.en] ++ envRepr (v' :: env'.tail))) (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega)
    (by simpa [frameBody_loop1] using frameBody_ne_fr (.loop1 b (v' :: env'.tail)))
    (kontRepr_nil_or_fr k)
  norm_ds at hd₂₄
  obtain ⟨c₂₅, hr₂₅, hd₂₅⟩ := D_move_right rfl (by decide) hd₂₄
  norm_ds at hd₂₅
  obtain ⟨c₂₆, hr₂₆, hd₂₆⟩ := D_move_right rfl (by decide) hd₂₅
  norm_ds at hd₂₆
  obtain ⟨c₂₇, hr₂₇, hd₂₇⟩ := D_rewind rfl (by decide) hd₂₆ (by simp <;> omega)
  norm_ds at hr₂₇ hd₂₇
  obtain ⟨n₂₈, hn₂₈, c₂₈, hr₂₈, hd₂₈⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₂₇ (by simp <;> omega) (v := b.toData) (l₁ := kontRepr k ++ [.one, .one])
    (l₂ := [.en] ++ (envRepr env'.tail ++ S v' ++ [.sep]) ++ [.fr]) (by simp [List.append_assoc])
    (by simp <;> omega) (by simp <;> omega)
  norm_ds at hd₂₈
  obtain ⟨c₂₉, hr₂₉, hd₂₉⟩ := D_rewind rfl (by decide) hd₂₈ (by simp <;> omega)
  norm_ds at hr₂₉ hd₂₉
  obtain ⟨c₃₀, hr₃₀, hd₃₀⟩ := D_write rfl (by decide) hd₂₉ (by simp <;> omega)
  norm_ds at hd₃₀
  obtain ⟨c₃₁, hr₃₁, hd₃₁⟩ := D_rewind rfl (by decide) hd₃₀ (by simp <;> omega)
  norm_ds at hr₃₁ hd₃₁
  obtain ⟨n₃₂, hn₃₂, c₃₂, hr₃₂, hd₃₂⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₃₁ (by simp <;> omega) (v := b.toData) (l₁ := [])
    (l₂ := (S v' ++ (ds X).l.drop v'.size).drop b.toData.size) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  norm_ds at hd₃₂
  obtain ⟨c₃₃, hr₃₃, hd₃₃⟩ := D_toEnd rfl (by decide) hd₃₂ (by simp <;> omega)
  norm_ds at hr₃₃ hd₃₃
  have htail : (envRepr env'.tail).length ≤ (envRepr env').length := by
    cases env' <;> simp
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
  have hR := hR.trans hr₂₅
  have hR := hR.trans hr₂₆
  have hR := hR.trans hr₂₇
  have hR := hR.trans hr₂₈
  have hR := hR.trans hr₂₉
  have hR := hR.trans hr₃₀
  have hR := hR.trans hr₃₁
  have hR := hR.trans hr₃₂
  have hR := hR.trans hr₃₃
  refine ⟨_, ?_, c₃₃, _, hR.cast_out (by simp), hd₃₃, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons,
      List.length_append, length_S, List.length_singleton, List.length_nil, List.length_drop,
      Data.size_cons, Data.size_nil, S_cons, S_nil, envRepr_cons]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [List.append_assoc] <;> omega
  · simp [kontRepr_cons, frameRepr, List.append_assoc] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · norm_ds_goal
    simp only [sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons, List.length_append,
      length_S, List.length_singleton, List.length_drop, List.length_nil, Data.size_cons, Data.size_nil,
      S_cons, S_nil]
    omega


/-! ## The final check -/

/-- The control and the tape `C` alone (the stack head may sit before the tape). -/
def CDesc (c : Cfg input) (q : Option Ctl) (s : TapeSt) : Prop :=
  c.state = q ∧ TapeIs (c.workTapes C) (c.workTapePos C) s

theorem F_move_right {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ}
    (hins : instrAt k pc = .move C true) (hpc : pc.val + 1 < maxPc) (h : CDesc c (at_ k pc) ⟨l, p⟩) :
    ∃ c', Reach c 1 c' [] ∧ CDesc c' (next_ k pc hpc) ⟨l, p + 1⟩ := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_move hins hpc c h.1
  exact ⟨c', hr, hs, h.2.of_same htape (by rw [hpos, h.2.pos_eq]; simp)⟩

theorem F_branch_taken {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ}
    {s : Option Sym} {target : ProgId} (hins : instrAt k pc = .branch C s target)
    (h : CDesc c (at_ k pc) ⟨l, p⟩) (hs : l[p]? = s) :
    ∃ c', Reach c 1 c' [] ∧ CDesc c' (at_ target ⟨0, by decide⟩) ⟨l, p⟩ := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_branch_taken hins c h.1 (by rw [h.2.read_pos]; exact hs)
  exact ⟨c', hr, hst, h.2.of_same (hall C).1 ((hall C).2.trans h.2.pos_eq)⟩

theorem F_branch_not {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ}
    {s : Option Sym} {target : ProgId} (hins : instrAt k pc = .branch C s target)
    (hpc : pc.val + 1 < maxPc) (h : CDesc c (at_ k pc) ⟨l, p⟩) (hs : l[p]? ≠ s) :
    ∃ c', Reach c 1 c' [] ∧ CDesc c' (next_ k pc hpc) ⟨l, p⟩ := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_branch_not hins hpc c h.1 (by rw [h.2.read_pos]; exact hs)
  exact ⟨c', hr, hst, h.2.of_same (hall C).1 ((hall C).2.trans h.2.pos_eq)⟩

theorem F_emit {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ} {s : Sym}
    (hins : instrAt k pc = .emit s) (hpc : pc.val + 1 < maxPc) (h : CDesc c (at_ k pc) ⟨l, p⟩) :
    ∃ c', Reach c 1 c' [s] ∧ CDesc c' (next_ k pc hpc) ⟨l, p⟩ := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_emit hins hpc c h.1
  exact ⟨c', hr, hst, h.2.of_same (hall C).1 ((hall C).2.trans h.2.pos_eq)⟩

theorem F_halt {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {s : TapeSt}
    (hins : instrAt k pc = .halt) (h : CDesc c (at_ k pc) s) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = none :=
  have := exec_halt hins c h.1
  ⟨_, ⟨rfl, this.2⟩, this.1⟩

/-- `U` accepts from `c` within `n` silent steps followed by the output `1`. -/
def AcceptsFrom (c : Cfg input) (n : ℕ) : Prop := ∃ c', Reach c n c' [.one] ∧ c'.state = none

/-- The final check on `ret v` with an empty stack: accept iff `v = encode true`. -/
theorem final_run {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {v : Data} {env : Env} {r : ℕ}
    (hr : RepOf ds ⟨.ret v, env, []⟩ r (ctrlRepr (.ret v)).length (kontRepr []).length) :
    (v = Data.ofBool true → ∃ n ≤ v.size + 16, AcceptsFrom c n) ∧
    (v ≠ Data.ofBool true → HaltsIn c (v.size + 16)) := by
  obtain ⟨g, hds⟩ := hr.eq
  rw [hds] at hd
  norm_ds at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_rewind rfl (by decide) hd (by simp <;> omega)
  norm_ds at hr₁ hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_branch_not rfl (by decide) hd₁ (by simp)
  obtain ⟨c₃, hr₃, hd₃⟩ := D_move_right rfl (by decide) hd₂
  norm_ds at hd₃
  -- the stack is empty: the head of `K` moves before the tape and the branch to `final` is taken
  obtain ⟨c₄, hr₄, hs₄, hu₄, hK₄, hKp₄⟩ := exec_move (t := K) (dir := false) rfl (by decide) c₃ hd₃.state
  have hread : c₄.workTapes K (c₄.workTapePos K) = none := by
    rw [hK₄, hKp₄, hd₃.pos K]
    exact (hd₃.tape K).before _ (by simp)
  obtain ⟨c₅, hr₅, hs₅, hu₅, hall₅⟩ := exec_branch_taken (t := K) (s := none) (target := .final) rfl c₄
    hs₄ hread
  have hC₅ : CDesc c₅ (at_ .final 0) ⟨.one :: (S v ++ g), 1⟩ := by
    refine ⟨hs₅, ?_⟩
    have := hd₃.tape C
    simp only [Function.update_self] at this
    exact this.of_same ((hall₅ C).1.trans (hu₄.tapes (d := C) (by decide)))
      (((hall₅ C).2.trans (hu₄.pos (d := C) (by decide))).trans (by rw [hd₃.pos C]; rfl))
  have hR := hr₁.trans hr₂
  have hR := hR.trans hr₃
  have hR := hR.trans hr₄
  have hR := hR.trans hr₅
  have hR : Reach c _ c₅ [] := hR.cast_out (by simp)
  -- the final program reads the bits of `v`
  cases v with
  | nil =>
    refine ⟨fun h => by simp [Data.ofBool] at h, fun _ => ?_⟩
    obtain ⟨c₆, hr₆, hd₆⟩ := F_branch_not rfl (by decide) hC₅ (by simp)
    obtain ⟨c₇, hr₇, hs₇⟩ := F_halt rfl hd₆
    exact (HaltsIn.of_reach ((hR.trans hr₆).trans hr₇ |>.cast_out (by simp)) hs₇).mono (by simp)
  | cons a b =>
    obtain ⟨c₆, hr₆, hd₆⟩ := F_branch_taken rfl hC₅ (by simp [S_cons])
    obtain ⟨c₇, hr₇, hd₇⟩ := F_move_right rfl (by decide) hd₆
    cases a with
    | cons a₁ a₂ =>
      refine ⟨fun h => by simp [Data.ofBool] at h, fun _ => ?_⟩
      obtain ⟨c₈, hr₈, hd₈⟩ := F_branch_not rfl (by decide) hd₇ (by simp [S_cons])
      obtain ⟨c₉, hr₉, hs₉⟩ := F_halt rfl hd₈
      exact (HaltsIn.of_reach ((((hR.trans hr₆).trans hr₇).trans hr₈).trans hr₉ |>.cast_out (by simp))
        hs₉).mono (by simp [Data.size_cons] <;> omega)
    | nil =>
      obtain ⟨c₈, hr₈, hd₈⟩ := F_branch_taken rfl hd₇ (by simp [S_cons])
      obtain ⟨c₉, hr₉, hd₉⟩ := F_move_right rfl (by decide) hd₈
      cases b with
      | cons b₁ b₂ =>
        refine ⟨fun h => by simp [Data.ofBool] at h, fun _ => ?_⟩
        obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := F_branch_not rfl (by decide) hd₉ (by simp [S_cons])
        obtain ⟨c₁₁, hr₁₁, hs₁₁⟩ := F_halt rfl hd₁₀
        exact (HaltsIn.of_reach ((((((hR.trans hr₆).trans hr₇).trans hr₈).trans hr₉).trans hr₁₀).trans
          hr₁₁ |>.cast_out (by simp)) hs₁₁).mono (by simp [Data.size_cons] <;> omega)
      | nil =>
        refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
        obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := F_branch_taken rfl hd₉ (by simp [S_cons])
        obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := F_emit rfl (by decide) hd₁₀
        obtain ⟨c₁₂, hr₁₂, hs₁₂⟩ := F_halt rfl hd₁₁
        refine ⟨_, ?_, c₁₂, ((((((hR.trans hr₆).trans hr₇).trans hr₈).trans hr₉).trans
          hr₁₀).trans hr₁₁).trans hr₁₂ |>.cast_out (by simp), hs₁₂⟩
        simp [Data.size_cons] <;> omega

/-! ## The step -/

/-- The bound on the steps of `U` simulating one step of the machine from a representation with
a scratch tape of length `xl`. -/
def stepBound (m : Machine.Cfg) (xl : ℕ) : ℕ := caseBound m xl + sz m + 30

theorem PreTo.after_dispatch {c c₁ : Cfg input} {n₁ B₁ : ℕ} (hr₁ : Reach c n₁ c₁ []) (h1 : 1 ≤ n₁)
    (hn₁ : n₁ ≤ B₁) {B q m' r pC pK xl} (h : PreTo c₁ B q m' r pC pK xl) :
    PreTo1 c (B₁ + B) q m' r pC pK xl := by
  obtain ⟨n, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  exact ⟨n₁ + n, by omega, by omega, c', ds', (hr₁.trans hr).cast_out (by simp), hd, hrep, hxl⟩

/-- **One step of the machine**, when the budget covers its cost: from the dispatcher
representing `m`, `U` reaches the dispatcher representing `step m` with the cost charged. -/
theorem step_run {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {m : Machine.Cfg} {r : ℕ}
    (hr : RepOf ds m r (ctrlRepr m.ctrl).length (kontRepr m.kont).length)
    (hnf : ∀ v, m.ctrl = .ret v → m.kont ≠ []) (hcost : stepCost m ≤ r) :
    RunTo c (stepBound m (ds X).l.length) (Machine.step m) (r - stepCost m) ((ds X).l.length + sz m) := by
  obtain ⟨ctrl, env, k⟩ := m
  cases ctrl with
  | ev p =>
    obtain ⟨n₁, hn₁₀, hn₁, c₁, ds₁, hr₁, hd₁, hrep₁, hxl₁⟩ := dispatch_ev hd hr
    have hmono : caseBound ⟨.ev p, env, k⟩ (ds₁ X).l.length ≤ caseBound ⟨.ev p, env, k⟩ (ds X).l.length := by
      simp only [caseBound]; omega
    cases p with
    | var i =>
      simp only [stepCost] at hcost ⊢
      simp only [Machine.step]
      rw [show r = r - ((Env.get env i).size + 1) + ((Env.get env i).size + 1) by omega] at hrep₁
      refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ (case_evVar hd₁ hrep₁)).mono ?_ ?_
      · simp only [stepBound, sz]; omega
      · simp only [sz]; omega
    | nil =>
      simp only [stepCost] at hcost ⊢
      simp only [Machine.step]
      rw [show r = r - 1 + 1 by omega] at hrep₁
      refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ (case_evNil hd₁ hrep₁)).mono ?_ ?_
      · simp only [stepBound, sz]; omega
      · simp only [sz]; omega
    | const d =>
      simp only [stepCost] at hcost ⊢
      simp only [Machine.step]
      rw [show r = r - d.size + d.size by omega] at hrep₁
      refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ (case_evConst hd₁ hrep₁)).mono ?_ ?_
      · simp only [stepBound, sz]; omega
      · simp only [sz]; omega
    | cons h t =>
      simp only [stepCost] at hcost ⊢
      simp only [Machine.step]
      rw [show r = r - 1 + 1 by omega] at hrep₁
      refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ ((case_evCons hd₁ hrep₁).charge_jump rfl (by decide) rfl)).mono ?_ ?_
      · simp only [stepBound, sz]; omega
      · simp only [sz]; omega
    | elim i n cc =>
      simp only [stepCost] at hcost ⊢
      simp only [Machine.step]
      rw [show r = r - 1 + 1 by omega] at hrep₁
      rcases hv : Env.get env i with _ | ⟨a, b⟩
      · refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ ((case_evElim_nil hd₁ hrep₁ hv).charge_jump rfl (by decide) rfl)).mono ?_ ?_
        · simp only [stepBound, sz]; omega
        · simp only [sz]; omega
      · refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ ((case_evElim_cons hd₁ hrep₁ hv).charge_jump rfl (by decide) rfl)).mono ?_ ?_
        · simp only [stepBound, sz]; omega
        · simp only [sz]; omega
    | let_ e b =>
      simp only [stepCost] at hcost ⊢
      simp only [Machine.step]
      rw [show r = r - 1 + 1 by omega] at hrep₁
      refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ ((case_evLet hd₁ hrep₁).charge_jump rfl (by decide) rfl)).mono ?_ ?_
      · simp only [stepBound, sz]; omega
      · simp only [sz]; omega
    | loop b =>
      simp only [stepCost] at hcost ⊢
      simp only [Machine.step]
      refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ (case_evLoop hd₁ hrep₁)).mono ?_ ?_
      · simp only [stepBound, sz]; omega
      · simp only [sz]; omega
  | ret v =>
    cases k with
    | nil => exact absurd rfl (hnf v rfl)
    | cons f k =>
      obtain ⟨n₁, hn₁₀, hn₁, c₁, ds₁, hr₁, hd₁, hrep₁, hxl₁⟩ := dispatch_ret hd hr
      have hmono : caseBound ⟨.ret v, env, f :: k⟩ (ds₁ X).l.length ≤
          caseBound ⟨.ret v, env, f :: k⟩ (ds X).l.length := by
        simp only [caseBound]; omega
      have hfb : (frameBody f).length ≤ (kontRepr (f :: k)).length := by
        rw [kontRepr_cons', List.length_append, List.length_append]; omega
      cases f with
      | cons1 t env' =>
        simp only [stepCost, Nat.sub_zero] at hcost ⊢
        simp only [Machine.step]
        refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ (case_retCons1 hd₁ hrep₁)).mono ?_ ?_
        · simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
        · simp only [sz]; omega
      | cons2 a =>
        simp only [stepCost, Nat.sub_zero] at hcost ⊢
        simp only [Machine.step]
        refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ (case_retCons2 hd₁ hrep₁)).mono ?_ ?_
        · simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
        · simp only [sz]; omega
      | let1 b env' =>
        simp only [stepCost, Nat.sub_zero] at hcost ⊢
        simp only [Machine.step]
        refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ (case_retLet1 hd₁ hrep₁)).mono ?_ ?_
        · simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
        · simp only [sz]; omega
      | loop1 b env' =>
        simp only [stepCost] at hcost ⊢
        simp only [Machine.step]
        rw [show r = r - 1 + 1 by omega] at hrep₁
        rcases v with _ | ⟨_ | ⟨y, z⟩, v'⟩
        · refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ ((case_retLoopNil hd₁ hrep₁).charge_jump rfl (by decide) rfl)).mono ?_ ?_
          · simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
          · simp only [sz]; omega
        · refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ ((case_retLoopStop hd₁ hrep₁).charge_jump rfl (by decide) rfl)).mono ?_ ?_
          · simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
          · simp only [sz]; omega
        · refine (PreTo.after_dispatch hr₁ hn₁₀ hn₁ ((case_retLoopCont hd₁ hrep₁).charge_jump rfl (by decide) rfl)).mono ?_ ?_
          · simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
          · simp only [sz]; omega

/-- **One step of the machine**, when the budget is short: `U` halts silently. -/
theorem step_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {m : Machine.Cfg} {r : ℕ}
    (hr : RepOf ds m r (ctrlRepr m.ctrl).length (kontRepr m.kont).length)
    (hnf : ∀ v, m.ctrl = .ret v → m.kont ≠ []) (hcost : r < stepCost m) :
    HaltsIn c (stepBound m (ds X).l.length) := by
  obtain ⟨ctrl, env, k⟩ := m
  cases ctrl with
  | ev p =>
    obtain ⟨n₁, hn₁₀, hn₁, c₁, ds₁, hr₁, hd₁, hrep₁, hxl₁⟩ := dispatch_ev hd hr
    have hmono : caseBound ⟨.ev p, env, k⟩ (ds₁ X).l.length ≤ caseBound ⟨.ev p, env, k⟩ (ds X).l.length := by
      simp only [caseBound]; omega
    cases p with
    | var i =>
      simp only [stepCost] at hcost
      refine (HaltsIn.after hr₁ (case_evVar_fail hd₁ hrep₁ hcost)).mono ?_
      simp only [stepBound, sz]; omega
    | nil =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      refine (HaltsIn.after hr₁ (case_evNil_fail hd₁ hrep₁)).mono ?_
      simp only [stepBound, sz]; omega
    | const d =>
      simp only [stepCost] at hcost
      refine (HaltsIn.after hr₁ (case_evConst_fail hd₁ hrep₁ hcost)).mono ?_
      simp only [stepBound, sz]; omega
    | cons h t =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      refine (HaltsIn.after hr₁ ((case_evCons hd₁ hrep₁).charge_fail rfl)).mono ?_
      simp only [stepBound, sz]; omega
    | elim i n cc =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      rcases hv : Env.get env i with _ | ⟨a, b⟩
      · refine (HaltsIn.after hr₁ ((case_evElim_nil hd₁ hrep₁ hv).charge_fail rfl)).mono ?_
        simp only [stepBound, sz]; omega
      · refine (HaltsIn.after hr₁ ((case_evElim_cons hd₁ hrep₁ hv).charge_fail rfl)).mono ?_
        simp only [stepBound, sz]; omega
    | let_ e b =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      refine (HaltsIn.after hr₁ ((case_evLet hd₁ hrep₁).charge_fail rfl)).mono ?_
      simp only [stepBound, sz]; omega
    | loop b => simp [stepCost] at hcost
  | ret v =>
    cases k with
    | nil => exact absurd rfl (hnf v rfl)
    | cons f k =>
      obtain ⟨n₁, hn₁₀, hn₁, c₁, ds₁, hr₁, hd₁, hrep₁, hxl₁⟩ := dispatch_ret hd hr
      have hmono : caseBound ⟨.ret v, env, f :: k⟩ (ds₁ X).l.length ≤
          caseBound ⟨.ret v, env, f :: k⟩ (ds X).l.length := by
        simp only [caseBound]; omega
      have hfb : (frameBody f).length ≤ (kontRepr (f :: k)).length := by
        rw [kontRepr_cons', List.length_append, List.length_append]; omega
      cases f with
      | cons1 t env' => simp [stepCost] at hcost
      | cons2 a => simp [stepCost] at hcost
      | let1 b env' => simp [stepCost] at hcost
      | loop1 b env' =>
        simp only [stepCost] at hcost
        obtain rfl : r = 0 := by omega
        rcases v with _ | ⟨_ | ⟨y, z⟩, v'⟩
        · refine (HaltsIn.after hr₁ ((case_retLoopNil hd₁ hrep₁).charge_fail rfl)).mono ?_
          simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
        · refine (HaltsIn.after hr₁ ((case_retLoopStop hd₁ hrep₁).charge_fail rfl)).mono ?_
          simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
        · refine (HaltsIn.after hr₁ ((case_retLoopCont hd₁ hrep₁).charge_fail rfl)).mono ?_
          simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega

end MIPRE.TM.Interp
