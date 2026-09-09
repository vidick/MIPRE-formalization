/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.MachineData
import MIPRE.Foundations.Cost.Unary

/-!
# Size bounds along machine runs

Along the run of the evaluation machine that simulates a derivation `Eval env p r t`, every
configuration stays bounded (`CfgBound`): values have size at most `V` (where `t ≤ V` and
the initial values are at most `V`, since every value produced is the result of a
sub-derivation of cost at most `t`), environments have length at most `L + 2 t`, programs
are subterms of the initial ones, and the stack gains at most `t` frames
(`eval_steps_bound`). Consequently the data encoding of every configuration along the run
has size polynomial in the sizes of the program, the input and the cost
(`size_toData_le`). This is what bounds the cost of the self-interpreter.
-/

namespace MIPRE.Cost

namespace Machine

/-! ## Bounds on configurations -/

/-- Bounds on a frame: values of size at most `V`, an environment of length at most `L`,
a program of size at most `P`. -/
def FrameBound (V L P : ℕ) : Frame → Prop
  | .cons1 t env => esize t ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V
  | .cons2 a => a.size ≤ V
  | .let1 b env => esize b ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V
  | .loop1 b env => esize b ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V

/-- Bounds on a configuration: values of size at most `V`, environments of length at most
`L`, programs of size at most `P`, a stack of length at most `K`. -/
structure CfgBound (V L P K : ℕ) (c : Cfg) : Prop where
  ctrl_val : ∀ v, c.ctrl = .ret v → v.size ≤ V
  ctrl_prog : ∀ p, c.ctrl = .ev p → esize p ≤ P
  env_len : c.env.length ≤ L
  env_val : ∀ v ∈ c.env, v.size ≤ V
  kont_len : c.kont.length ≤ K
  frames : ∀ f ∈ c.kont, FrameBound V L P f

theorem FrameBound.mono {V L P V' L' P' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    {f : Frame} (h : FrameBound V L P f) : FrameBound V' L' P' f := by
  cases f with
  | cons2 a => exact le_trans h hV
  | cons1 t env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | let1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | loop1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩

theorem CfgBound.mono {V L P K V' L' P' K' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    (hK : K ≤ K') {c : Cfg} (h : CfgBound V L P K c) : CfgBound V' L' P' K' c where
  ctrl_val v hv := le_trans (h.ctrl_val v hv) hV
  ctrl_prog p hp := le_trans (h.ctrl_prog p hp) hP
  env_len := le_trans h.env_len hL
  env_val v hv := le_trans (h.env_val v hv) hV
  kont_len := le_trans h.kont_len hK
  frames f hf := (h.frames f hf).mono hV hL hP

/-! ## Program subterms -/

theorem esize_cons_left (h t : Prog) : esize h ≤ esize (Prog.cons h t) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

theorem esize_cons_right (h t : Prog) : esize t ≤ esize (Prog.cons h t) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

theorem esize_elim_left (i : ℕ) (n c : Prog) : esize n ≤ esize (Prog.elim i n c) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

theorem esize_elim_right (i : ℕ) (n c : Prog) : esize c ≤ esize (Prog.elim i n c) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

theorem esize_let_left (e b : Prog) : esize e ≤ esize (Prog.let_ e b) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

theorem esize_let_right (e b : Prog) : esize b ≤ esize (Prog.let_ e b) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

theorem esize_loop (b : Prog) : esize b ≤ esize (Prog.loop b) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

theorem size_const_le (d : Data) : d.size ≤ esize (Prog.const d) := by
  simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]; omega

/-! ## Chaining bounds along runs -/

theorem bound_chain {B : Cfg → Prop} {c₁ c₂ : Cfg} {m₁ m₂ : ℕ} (h₁ : step^[m₁] c₁ = c₂)
    (hb₁ : ∀ n ≤ m₁, B (step^[n] c₁)) (hb₂ : ∀ n ≤ m₂, B (step^[n] c₂)) :
    ∀ n ≤ m₁ + m₂, B (step^[n] c₁) := by
  intro n hn
  by_cases h : n ≤ m₁
  · exact hb₁ n h
  · obtain ⟨n', rfl⟩ : ∃ n', n = m₁ + n' := ⟨n - m₁, by omega⟩
    rw [Nat.add_comm, Function.iterate_add_apply, h₁]
    exact hb₂ n' (by omega)

theorem bound_one {B : Cfg → Prop} {c : Cfg} (h₀ : B c) (h₁ : B (step c)) :
    ∀ n ≤ 1, B (step^[n] c) := by
  intro n hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · exact h₀
  · exact h₁

/-- Every configuration along the machine run of a derivation is bounded. -/
theorem eval_steps_bound {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t) :
    ∀ (k : List Frame) (V L P K : ℕ), CfgBound V L P K ⟨.ev p, env, k⟩ → t ≤ V →
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t ∧
      ∀ n ≤ N, CfgBound V (L + 2 * t) P (K + t) (step^[n] ⟨.ev p, env, k⟩) := by
  induction h with
  | var env i =>
    intro k V L P K hb ht
    refine ⟨1, env, Steps.one _, bound_one (hb.mono le_rfl (by omega) le_rfl (by omega)) ?_⟩
    exact ⟨fun v hv => by simp only [step, Ctrl.ret.injEq] at hv; subst hv; omega,
      fun p hp => by simp [step] at hp, hb.env_len.trans (by omega), hb.env_val,
      hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
  | nil env =>
    intro k V L P K hb ht
    refine ⟨1, env, Steps.one _, bound_one (hb.mono le_rfl (by omega) le_rfl (by omega)) ?_⟩
    exact ⟨fun v hv => by simp only [step, Ctrl.ret.injEq] at hv; subst hv; simpa using ht,
      fun p hp => by simp [step] at hp, hb.env_len.trans (by omega), hb.env_val,
      hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
  | const env d =>
    intro k V L P K hb ht
    refine ⟨1, env, Steps.one _, bound_one (hb.mono le_rfl (by omega) le_rfl (by omega)) ?_⟩
    exact ⟨fun v hv => by simp only [step, Ctrl.ret.injEq] at hv; subst hv; exact ht,
      fun p hp => by simp [step] at hp, hb.env_len.trans (by omega), hb.env_val,
      hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
  | cons h₁ h₂ ih₁ ih₂ =>
    rename_i env h t a b s u
    intro k V L P K hb ht
    have hP : esize (Prog.cons h t) ≤ P := hb.ctrl_prog _ rfl
    -- the sub-run of `h`
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev h, env, .cons1 t env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_cons_left h t).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_cons_right h t).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N₁, e₁, s₁, b₁⟩ := ih₁ _ V L P (K + 1) hb₁ (by omega)
    -- the return to the `cons1` frame
    have hret₁ := b₁ N₁ le_rfl
    rw [s₁.1] at hret₁
    have hb₂ : CfgBound V L P (K + 1) ⟨.ev t, env, .cons2 a :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_cons_right h t).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact h₁.size_le.trans (by omega)
          · exact hb.frames f hf⟩
    obtain ⟨N₂, e₂, s₂, b₂⟩ := ih₂ _ V L P (K + 1) hb₂ (by omega)
    have hret₂ := b₂ N₂ le_rfl
    rw [s₂.1] at hret₂
    have hfin : CfgBound V (L + 2 * (s + u + 1)) P (K + (s + u + 1)) ⟨.ret (.cons a b), e₂, k⟩ :=
      ⟨fun v hv => by
          simp only [Ctrl.ret.injEq] at hv; subst hv
          exact (Eval.cons h₁ h₂).size_le.trans ht,
        fun p hp => by simp at hp, hret₂.env_len.trans (by omega),
        hret₂.env_val, hb.kont_len.trans (by omega),
        fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    have c1 := Steps.one ⟨.ev (.cons h t), env, k⟩
    have c2 := c1.trans s₁
    have c3 := c2.trans (Steps.one ⟨.ret a, e₁, .cons1 t env :: k⟩)
    have c4 := c3.trans s₂
    have chain := c4.trans (Steps.one ⟨.ret b, e₂, .cons2 a :: k⟩)
    refine ⟨_, e₂, chain.cast (by simp [stepCost]; omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (s + u + 1)) P (K + (s + u + 1))) c4.1 ?_
      (bound_one (hret₂.mono le_rfl (by omega) le_rfl (by omega)) hfin)
    refine bound_chain c3.1 ?_ (fun n hn => (b₂ n hn).mono le_rfl (by omega) le_rfl (by omega))
    refine bound_chain c2.1 ?_ (bound_one (hret₁.mono le_rfl (by omega) le_rfl (by omega))
      (hb₂.mono le_rfl (by omega) le_rfl (by omega)))
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b₁ n hn).mono le_rfl (by omega) le_rfl (by omega))
  | elim_nil hget h₁ ih =>
    rename_i env i n c r t
    intro k V L P K hb ht
    have hP : esize (Prog.elim i n c) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P K ⟨.ev n, env, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_elim_left i n c).trans hP,
        hb.env_len, hb.env_val, hb.kont_len, hb.frames⟩
    obtain ⟨N, e, s, b⟩ := ih _ V L P K hb₁ (by omega)
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev n, env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    refine ⟨_, e, (h0.trans s).cast (by omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) h0.1
      (bound_one (hb.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
          (by omega))
        (by
          have := hb₁.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
            (by omega)
          simpa only [step, hget] using this)) ?_
    intro m hm
    exact (b m hm).mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
      (by omega)
  | elim_cons hget h₁ ih =>
    rename_i env i n c a b r t
    intro k V L P K hb ht
    have hP : esize (Prog.elim i n c) ≤ P := hb.ctrl_prog _ rfl
    have hab : (Data.cons a b).size ≤ V := by
      have hmem : Env.get env i ∈ env := by
        unfold Env.get at hget ⊢
        rw [List.getD_eq_getElem?_getD] at hget ⊢
        rcases h : env[i]? with _ | w
        · rw [h] at hget; simp at hget
        · simpa using List.mem_of_getElem? h
      rw [hget] at hmem
      exact hb.env_val _ hmem
    have hb₁ : CfgBound V (L + 2) P K ⟨.ev c, a :: b :: env, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_elim_right i n c).trans hP,
        by simpa using hb.env_len, fun v hv => by
          rcases List.mem_cons.1 hv with rfl | hv
          · simp only [Data.size_cons] at hab; omega
          rcases List.mem_cons.1 hv with rfl | hv
          · simp only [Data.size_cons] at hab; omega
          · exact hb.env_val v hv,
        hb.kont_len, fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    obtain ⟨N, e, s, b'⟩ := ih _ V (L + 2) P K hb₁ (by omega)
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev c, a :: b :: env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    refine ⟨_, e, (h0.trans s).cast (by omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) h0.1
      (bound_one (hb.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
          (by omega))
        (by
          have := hb₁.mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
            (by omega)
          simpa only [step, hget] using this)) ?_
    intro m hm
    exact (b' m hm).mono (L' := L + 2 * (t + 1)) (K' := K + (t + 1)) le_rfl (by omega) le_rfl
      (by omega)
  | let_ h₁ h₂ ih₁ ih₂ =>
    rename_i env e b v r s u
    intro k V L P K hb ht
    have hP : esize (Prog.let_ e b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev e, env, .let1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_let_left e b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_let_right e b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N₁, e₁, s₁, b₁⟩ := ih₁ _ V L P (K + 1) hb₁ (by omega)
    have hret₁ := b₁ N₁ le_rfl
    rw [s₁.1] at hret₁
    have hb₂ : CfgBound V (L + 1) P K ⟨.ev b, v :: env, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_let_right e b).trans hP,
        by simpa using hb.env_len, fun w hw => by
          rcases List.mem_cons.1 hw with rfl | hw
          · exact h₁.size_le.trans (by omega)
          · exact hb.env_val w hw,
        hb.kont_len, fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    obtain ⟨N₂, e₂, s₂, b₂⟩ := ih₂ _ V (L + 1) P K hb₂ (by omega)
    have c1 := Steps.one ⟨.ev (.let_ e b), env, k⟩
    have c2 := c1.trans s₁
    have c3 := c2.trans (Steps.one ⟨.ret v, e₁, .let1 b env :: k⟩)
    have chain := c3.trans s₂
    refine ⟨_, e₂, chain.cast (by simp [stepCost]; omega), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (s + u + 1)) P (K + (s + u + 1))) c3.1 ?_
      (fun n hn => (b₂ n hn).mono le_rfl (by omega) le_rfl (by omega))
    refine bound_chain c2.1 ?_ (bound_one (hret₁.mono le_rfl (by omega) le_rfl (by omega))
      (hb₂.mono le_rfl (by omega) le_rfl (by omega)))
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b₁ n hn).mono le_rfl (by omega) le_rfl (by omega))
  | loop_nil h₁ ih =>
    rename_i env b t
    intro k V L P K hb ht
    have hP : esize (Prog.loop b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev b, env, .loop1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_loop b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_loop b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N, e, s, b'⟩ := ih _ V L P (K + 1) hb₁ (by omega)
    have hret := b' N le_rfl
    rw [s.1] at hret
    have hfin : CfgBound V (L + 2 * (t + 1)) P (K + (t + 1)) ⟨.ret .nil, env, k⟩ :=
      ⟨fun v hv => by simp only [Ctrl.ret.injEq] at hv; subst hv; simp; omega,
        fun p hp => by simp at hp, hb.env_len.trans (by omega), hb.env_val,
        hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    have c1 := Steps.one ⟨.ev (.loop b), env, k⟩
    have c2 := c1.trans s
    have chain := c2.trans (Steps.one ⟨.ret .nil, e, .loop1 b env :: k⟩)
    refine ⟨_, env, chain.cast (by simp [stepCost]), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) c2.1 ?_
      (bound_one (hret.mono le_rfl (by omega) le_rfl (by omega)) hfin)
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b' n hn).mono le_rfl (by omega) le_rfl (by omega))
  | loop_stop h₁ ih =>
    rename_i env b r t
    intro k V L P K hb ht
    have hP : esize (Prog.loop b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev b, env, .loop1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_loop b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_loop b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N, e, s, b'⟩ := ih _ V L P (K + 1) hb₁ (by omega)
    have hret := b' N le_rfl
    rw [s.1] at hret
    have hfin : CfgBound V (L + 2 * (t + 1)) P (K + (t + 1)) ⟨.ret r, env, k⟩ :=
      ⟨fun v hv => by
          simp only [Ctrl.ret.injEq] at hv; subst hv
          have := h₁.size_le; simp only [Data.size_cons] at this; omega,
        fun p hp => by simp at hp, hb.env_len.trans (by omega), hb.env_val,
        hb.kont_len.trans (by omega), fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    have c1 := Steps.one ⟨.ev (.loop b), env, k⟩
    have c2 := c1.trans s
    have chain := c2.trans (Steps.one ⟨.ret (.cons .nil r), e, .loop1 b env :: k⟩)
    refine ⟨_, env, chain.cast (by simp [stepCost]), ?_⟩
    refine bound_chain (B := CfgBound V (L + 2 * (t + 1)) P (K + (t + 1))) c2.1 ?_
      (bound_one (hret.mono le_rfl (by omega) le_rfl (by omega)) hfin)
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b' n hn).mono le_rfl (by omega) le_rfl (by omega))
  | loop_step h₁ h₂ ih₁ ih₂ =>
    rename_i env b x y v r s t
    intro k V L P K hb ht
    have hP : esize (Prog.loop b) ≤ P := hb.ctrl_prog _ rfl
    have hb₁ : CfgBound V L P (K + 1) ⟨.ev b, env, .loop1 b env :: k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact (esize_loop b).trans hP,
        hb.env_len, hb.env_val, by simpa using hb.kont_len, fun f hf => by
          rcases List.mem_cons.1 hf with rfl | hf
          · exact ⟨(esize_loop b).trans hP, hb.env_len, hb.env_val⟩
          · exact hb.frames f hf⟩
    obtain ⟨N₁, e₁, s₁, b₁⟩ := ih₁ _ V L P (K + 1) hb₁ (by omega)
    have hret₁ := b₁ N₁ le_rfl
    rw [s₁.1] at hret₁
    have hb₂ : CfgBound V (L + 1) P K ⟨.ev (.loop b), v :: env.tail, k⟩ :=
      ⟨fun _ hv => by simp at hv, fun p hp => by
          simp only [Ctrl.ev.injEq] at hp; subst hp; exact hP,
        by
          have h1 : env.length ≤ L := hb.env_len
          have := List.length_tail (l := env); simp only [List.length_cons]; omega,
        fun w hw => by
          rcases List.mem_cons.1 hw with rfl | hw
          · have := h₁.size_le; simp only [Data.size_cons] at this; omega
          · exact hb.env_val w (List.mem_of_mem_tail hw),
        hb.kont_len, fun f hf => (hb.frames f hf).mono le_rfl (by omega) le_rfl⟩
    obtain ⟨N₂, e₂, s₂, b₂⟩ := ih₂ _ V (L + 1) P K hb₂ (by omega)
    obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero s₂.ne_zero
    obtain ⟨t₂, ht₂, s₂'⟩ := s₂.of_succ
    have c1 := Steps.one ⟨.ev (.loop b), env, k⟩
    have c2 := c1.trans s₁
    have c3 := c2.trans (Steps.one ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩)
    have chain := c3.trans s₂'
    refine ⟨_, e₂, chain.cast (by simp only [stepCost] at ht₂ ⊢; omega), ?_⟩
    have b₂' : ∀ n ≤ N₂', CfgBound V (L + 1 + 2 * t) P (K + t)
        (step^[n] (step ⟨.ev (.loop b), v :: env.tail, k⟩)) := fun n hn => by
      rw [← Function.iterate_succ_apply]
      exact b₂ (n + 1) (by omega)
    have hmid : CfgBound V (L + 1 + 2 * t) P (K + t)
        (step ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩) := by
      have := b₂ 1 (by omega)
      simpa only [Function.iterate_one, step] using this
    refine bound_chain (B := CfgBound V (L + 2 * (s + t + 1)) P (K + (s + t + 1))) c3.1 ?_
      (fun n hn => (b₂' n hn).mono le_rfl (by omega) le_rfl (by omega))
    refine bound_chain c2.1 ?_ (bound_one (hret₁.mono le_rfl (by omega) le_rfl (by omega))
      (hmid.mono le_rfl (by omega) le_rfl (by omega)))
    exact bound_chain c1.1 (bound_one (hb.mono le_rfl (by omega) le_rfl (by omega))
      (hb₁.mono le_rfl (by omega) le_rfl (by omega)))
      (fun n hn => (b₁ n hn).mono le_rfl (by omega) le_rfl (by omega))

/-! ## Size of the encoded configurations -/

theorem sumSize_le_of_forall {V : ℕ} :
    ∀ (l : List Data), (∀ v ∈ l, v.size ≤ V) → Data.sumSize l ≤ l.length * V
  | [], _ => by simp
  | a :: l, h => by
    have h₁ := sumSize_le_of_forall l (fun v hv => h v (List.mem_cons_of_mem a hv))
    have h₂ := h a (List.mem_cons_self ..)
    simp only [Data.sumSize_cons, List.length_cons, Nat.succ_mul]
    omega

theorem size_list_le_of_forall {V L : ℕ} (l : List Data) (hl : l.length ≤ L)
    (h : ∀ v ∈ l, v.size ≤ V) : (Data.list l).size ≤ L * V + L + 1 := by
  rw [Data.size_list_eq]
  have h₁ := sumSize_le_of_forall l h
  have h₂ := Nat.mul_le_mul_right V hl
  omega

theorem frame_size_le {V L P : ℕ} {f : Frame} (h : FrameBound V L P f) :
    (Frame.toData f).size ≤ V + P + L * V + L + 10 := by
  cases f with
  | cons1 t env =>
    obtain ⟨hP, hL, hV⟩ := h
    have := size_list_le_of_forall env hL hV
    rw [Prog.esize_eq_size_toData] at hP
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega
  | cons2 a =>
    simp only [FrameBound] at h
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega
  | let1 b env =>
    obtain ⟨hP, hL, hV⟩ := h
    have := size_list_le_of_forall env hL hV
    rw [Prog.esize_eq_size_toData] at hP
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega
  | loop1 b env =>
    obtain ⟨hP, hL, hV⟩ := h
    have := size_list_le_of_forall env hL hV
    rw [Prog.esize_eq_size_toData] at hP
    simp only [Frame.toData, Data.size_cons, Data.size_ofNat]; omega

/-- Size of the encoding of a configuration satisfying `CfgBound V L P K`. -/
def cfgSizeBound (V L P K : ℕ) : ℕ :=
  V + P + L * V + L + K * (V + P + L * V + L + 10) + K + 8

theorem size_toData_le {V L P K : ℕ} {c : Cfg} (h : CfgBound V L P K c) :
    (Cfg.toData c).size ≤ cfgSizeBound V L P K := by
  obtain ⟨ctrl, env, kont⟩ := c
  have henv := size_list_le_of_forall env h.env_len h.env_val
  have hkont : (Data.list (kont.map Frame.toData)).size ≤
      K * (V + P + L * V + L + 10) + K + 1 := by
    refine size_list_le_of_forall _ (by simpa using h.kont_len) ?_
    intro v hv
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hv
    exact frame_size_le (h.frames f hf)
  have hctrl : (Ctrl.toData ctrl).size ≤ V + P + 4 := by
    cases ctrl with
    | ev p =>
      have := h.ctrl_prog p rfl
      rw [Prog.esize_eq_size_toData] at this
      simp only [Ctrl.toData, evD, Data.size_cons, Data.size_nil]; omega
    | ret v =>
      have := h.ctrl_val v rfl
      simp only [Ctrl.toData, retD, Data.size_cons, Data.size_nil]; omega
  unfold cfgSizeBound
  simp only [Cfg.toData, Data.size_cons]
  omega

/-! ## Runs from the empty stack are bounded forever -/

theorem step_final (r : Data) (e : Env) (n : ℕ) :
    step^[n] (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r, e, []⟩ :=
  Function.iterate_fixed rfl n

/-- Along the run of a derivation from the empty stack, every configuration — also after
the final one, which is fixed — is bounded. -/
theorem eval_steps_bound_forever {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (V L P K : ℕ) (hb : CfgBound V L P K ⟨.ev p, env, []⟩) (ht : t ≤ V) :
    ∃ N env', Steps ⟨.ev p, env, []⟩ N ⟨.ret r, env', []⟩ t ∧
      ∀ n, CfgBound V (L + 2 * t) P (K + t) (step^[n] ⟨.ev p, env, []⟩) := by
  obtain ⟨N, env', hs, hb'⟩ := eval_steps_bound h [] V L P K hb ht
  refine ⟨N, env', hs, fun n => ?_⟩
  by_cases hn : n ≤ N
  · exact hb' n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
    have hN := hb' N le_rfl
    rw [show N + m = m + N by omega, Function.iterate_add_apply, hs.1, step_final]
    rwa [hs.1] at hN

/-! ## The number of steps of a run -/

/-- The machine run of a derivation of cost `t` has at most `3 t` steps (the free steps —
entering a loop, and returning to a `cons`/`let` frame — are each matched with a paid one). -/
theorem eval_steps_count {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (k : List Frame) :
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t ∧ N ≤ 3 * t := by
  induction h generalizing k with
  | var env i => exact ⟨1, env, Steps.one _, by omega⟩
  | nil env => exact ⟨1, env, Steps.one _, by omega⟩
  | const env d => exact ⟨1, env, Steps.one _, by have := Data.size_pos d; omega⟩
  | cons h₁ h₂ ih₁ ih₂ =>
    rename_i env h t a b s u
    obtain ⟨N₁, e₁, h₁, hN₁⟩ := ih₁ (.cons1 t env :: k)
    obtain ⟨N₂, e₂, h₂, hN₂⟩ := ih₂ (.cons2 a :: k)
    have := (((Steps.one ⟨.ev (.cons h t), env, k⟩).trans h₁).trans
      ((Steps.one ⟨.ret a, e₁, .cons1 t env :: k⟩).trans h₂)).trans
      (Steps.one ⟨.ret b, e₂, .cons2 a :: k⟩)
    exact ⟨_, e₂, this.cast (by simp [stepCost]; omega), by omega⟩
  | elim_nil hget h₁ ih =>
    rename_i env i n c r t
    obtain ⟨N, e, h, hN⟩ := ih k
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev n, env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    exact ⟨_, e, (h0.trans h).cast (by omega), by omega⟩
  | elim_cons hget h₁ ih =>
    rename_i env i n c a b r t
    obtain ⟨N, e, h, hN⟩ := ih k
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev c, a :: b :: env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    exact ⟨_, e, (h0.trans h).cast (by omega), by omega⟩
  | let_ h₁ h₂ ih₁ ih₂ =>
    rename_i env e b v r s t
    obtain ⟨N₁, e₁, h₁, hN₁⟩ := ih₁ (.let1 b env :: k)
    obtain ⟨N₂, e₂, h₂, hN₂⟩ := ih₂ k
    have := (((Steps.one ⟨.ev (.let_ e b), env, k⟩).trans h₁).trans
      (Steps.one ⟨.ret v, e₁, .let1 b env :: k⟩)).trans h₂
    exact ⟨_, e₂, this.cast (by simp [stepCost]; omega), by omega⟩
  | loop_nil h₁ ih =>
    rename_i env b t
    obtain ⟨N, e, h, hN⟩ := ih (.loop1 b env :: k)
    have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans h).trans
      (Steps.one ⟨.ret .nil, e, .loop1 b env :: k⟩)
    exact ⟨_, env, this.cast (by simp [stepCost]), by omega⟩
  | loop_stop h₁ ih =>
    rename_i env b r t
    obtain ⟨N, e, h, hN⟩ := ih (.loop1 b env :: k)
    have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans h).trans
      (Steps.one ⟨.ret (.cons .nil r), e, .loop1 b env :: k⟩)
    exact ⟨_, env, this.cast (by simp [stepCost]), by omega⟩
  | loop_step h₁ h₂ ih₁ ih₂ =>
    rename_i env b x y v r s t
    obtain ⟨N₁, e₁, h₁, hN₁⟩ := ih₁ (.loop1 b env :: k)
    obtain ⟨N₂, e₂, h₂, hN₂⟩ := ih₂ k
    obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h₂.ne_zero
    obtain ⟨t₂, ht₂, h₂'⟩ := h₂.of_succ
    have := (((Steps.one ⟨.ev (.loop b), env, k⟩).trans h₁).trans
      (Steps.one ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩)).trans h₂'
    exact ⟨_, e₂, this.cast (by simp only [stepCost] at ht₂ ⊢; omega), by omega⟩

/-! ## Cost sums -/

theorem costSum_succ (c : Cfg) (n : ℕ) :
    costSum c (n + 1) = costSum c n + stepCost (step^[n] c) := by
  rw [costSum_add, costSum, costSum]; omega

theorem costSum_le_of_le (c : Cfg) {m n : ℕ} (h : m ≤ n) : costSum c m ≤ costSum c n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [costSum_add]; omega

theorem stepCost_final (r : Data) (e : Env) : stepCost ⟨.ret r, e, []⟩ = 0 := rfl

theorem costSum_final (r : Data) (e : Env) (n : ℕ) : costSum ⟨.ret r, e, []⟩ n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [costSum_succ, ih, step_final, stepCost_final]

end Machine

end MIPRE.Cost
