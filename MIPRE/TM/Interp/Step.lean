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
      List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim,
      ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at $hs*)

macro "norm_ds_goal" : tactic =>
  `(tactic| try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq,
      not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT,
      overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil',
      overwrite_append', List.cons_append, List.nil_append, List.append_nil,
      List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil,
      List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add,
      List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim,
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
    PreTo c ((ctrlRepr (.ev p)).length + 26) (at_ (evTarget p) 0) ⟨.ev p, env, k⟩ r (evHead p)
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
      PreTo c ((ctrlRepr (.ev p)).length + 26) (at_ (evTarget p) 0) ⟨.ev p, env, k⟩ r (evHead p)
        (kontRepr k).length (ds X).l.length := by
    intro n c' hr' hd' hn
    subst hn
    refine ⟨_, ?_, c', _, (hR.trans hr').cast_out (by simp), hd', ⟨⟨g, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
    (hr : RepOf ds ⟨.ev (.cons h t), env, k⟩ (r + 1) 6 (kontRepr k).length) :
    PreTo c (caseBound ⟨.ev (.cons h t), env, k⟩ (ds X).l.length) (at_ .evCons 15)
      ⟨.ev h, env, .cons1 t env :: k⟩ (r + 1) (ctrlRepr (.ev h)).length
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

end MIPRE.TM.Interp
