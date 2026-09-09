/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Kleene
import MIPRE.Foundations.Cost.Codable
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Computability.PartrecCode

/-!
# From Mathlib's partial recursive functions into the ambient model

Mathlib's `Turing.ToPartrec.Code` is a small first-order language on lists of naturals
(`zero'`, `succ`, `tail`, `cons`, `comp`, `case`, `fix`) in which every partial recursive
function is computable (`Turing.ToPartrec.Code.exists_code`). It translates construct by
construct into the ambient language (`Prog.ofCode`), with lists of naturals encoded as
`cons`-chains of unary numerals (`encL`) and `fix` as a `loop`; `ofCode_sound` and
`ofCode_complete` are the two directions of the correctness of the translation.

`exists_compile` is the resulting bridge for the halting problem: a map `compile` from
`Nat.Partrec.Code` to programs, computable on descriptions, such that `compile pc` halts on
the empty input iff `pc` does on `0`: `compile pc` hardcodes the code number of `pc` into
the translation of a `ToPartrec.Code` for the universal partial function `n ↦ (ofNat n).eval 0`.
-/

namespace MIPRE.Cost

open Turing.ToPartrec (Code)

/-- Lists of naturals as data: a `cons`-chain of unary numerals. -/
def encL (v : List ℕ) : Data := Data.list (v.map Data.ofNat)

@[simp] theorem encL_nil : encL [] = .nil := rfl

@[simp] theorem encL_cons (n : ℕ) (v : List ℕ) : encL (n :: v) = .cons (.ofNat n) (encL v) := rfl

theorem encL_injective : Function.Injective encL := by
  intro v w h
  induction v generalizing w with
  | nil => cases w <;> simp_all
  | cons n v ih =>
    cases w with
    | nil => simp at h
    | cons m w =>
      simp only [encL_cons, Data.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have := Data.toNat?_ofNat n
      rw [h1, Data.toNat?_ofNat] at this
      obtain rfl := Option.some.inj this
      rw [ih h2]

namespace Prog

/-- The body of the translation of `fix f`: run `f`, then dispatch on the head of the
result (stop with the tail if it is `0`, continue with the tail otherwise). -/
def fixBody (pf : Prog) : Prog :=
  .let_ (callVar 0 pf)
    (.elim 0 (.cons .nil .nil) (.elim 0 (.cons .nil (.var 1)) (.cons (.cons .nil .nil) (.var 3))))

/-- The `headI :: tail` assembly of the translation of `cons f fs`, in an environment
`[fs v, f v, v]`. -/
def consTail : Prog := .cons (.elim 1 .nil (.var 0)) (.var 0)

/-- Translation of `ToPartrec.Code` into the ambient language. -/
def ofCode : Code → Prog
  | .zero' => .cons .nil (.var 0)
  | .succ => .elim 0 (.cons (.cons .nil .nil) .nil) (.cons (.cons .nil (.var 0)) .nil)
  | .tail => .elim 0 .nil (.var 1)
  | .cons f fs => .let_ (ofCode f) (.let_ (callVar 1 (ofCode fs)) consTail)
  | .comp f g => .let_ (ofCode g) (ofCode f)
  | .case f g =>
    .elim 0 (callVar 0 (ofCode f))
      (.elim 0 (callVar 1 (ofCode f)) (.let_ (.cons (.var 1) (.var 3)) (callVar 0 (ofCode g))))
  | .fix f => .loop (fixBody (ofCode f))

theorem consTail_wellScoped : consTail.WellScoped 3 := by simp [consTail, WellScoped]

theorem fixBody_wellScoped {pf : Prog} (h : pf.WellScoped 1) : (fixBody pf).WellScoped 1 :=
  ⟨callVar_wellScoped (by decide) h, by simp [WellScoped]⟩

theorem ofCode_wellScoped : ∀ c : Code, (ofCode c).WellScoped 1
  | .zero' => by simp [ofCode, WellScoped]
  | .succ => by simp [ofCode, WellScoped]
  | .tail => by simp [ofCode, WellScoped]
  | .cons f fs =>
    ⟨ofCode_wellScoped f, callVar_wellScoped (by decide) (ofCode_wellScoped fs),
      consTail_wellScoped⟩
  | .comp f g => ⟨ofCode_wellScoped g, (ofCode_wellScoped f).mono (by omega) _⟩
  | .case f g =>
    ⟨by decide, callVar_wellScoped (by decide) (ofCode_wellScoped f), by decide,
      callVar_wellScoped (by decide) (ofCode_wellScoped f),
      ⟨by simp [WellScoped], by simp [WellScoped]⟩,
      callVar_wellScoped (by decide) (ofCode_wellScoped g)⟩
  | .fix f => ⟨by decide, fixBody_wellScoped (ofCode_wellScoped f)⟩

/-! ## Forward runs of the pieces -/

/-- The result of the dispatch of `fixBody` on the value `fv` of `f`. -/
def fixFlag : List ℕ → Data
  | [] => .cons .nil .nil
  | 0 :: t => .cons .nil (encL t)
  | (_ + 1) :: t => .cons (.cons .nil .nil) (encL t)

theorem fixBody_runs {pf : Prog} (hpf : pf.WellScoped 1) (v fv : List ℕ) {t : ℕ}
    (h : pf.Runs (encL v) (encL fv) t) :
    ∃ s, Eval [encL v] (fixBody pf) (fixFlag fv) s := by
  have h1 := callVar_eval (env := [encL v]) (i := 0) hpf (v := encL v) (by simp) h
  rcases fv with _ | ⟨_ | y, t'⟩
  · exact ⟨_, Eval.let_ h1 (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.nil _)))⟩
  · exact ⟨_, Eval.let_ h1 (Eval.elim_cons (i := 0) (a := .nil) (b := encL t') (by simp [Data.ofNat])
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := encL t') (by simp)))))⟩
  · exact ⟨_, Eval.let_ h1 (Eval.elim_cons (i := 0) (a := .cons .nil (.ofNat y)) (b := encL t')
      (by simp [Data.ofNat])
      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat y) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 3) (v := encL t') (by simp)))))⟩

theorem consTail_runs (fv fsv v : List ℕ) :
    ∃ s, Eval [encL fsv, encL fv, encL v] consTail (encL (fv.headI :: fsv)) s := by
  rcases fv with _ | ⟨a, fv'⟩
  · exact ⟨_, Eval.cons (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))
      (Eval.var_of_get (i := 0) (v := encL fsv) (by simp))⟩
  · exact ⟨_, Eval.cons (Eval.elim_cons (i := 1) (a := .ofNat a) (b := encL fv') (by simp)
      (Eval.var_of_get (i := 0) (v := .ofNat a) (by simp)))
      (Eval.var_of_get (i := 0) (v := encL fsv) (by simp))⟩

/-- The pairing step of the `case` translation, in an environment
`[nil, ofNat y, ofNat (y + 1), encL v', encL (y + 1 :: v')]`. -/
theorem casePair_runs (y : ℕ) (v' : List ℕ) :
    Eval [Data.nil, .ofNat y, .ofNat (y + 1), encL v', encL ((y + 1) :: v')]
      (.cons (.var 1) (.var 3)) (encL (y :: v')) ((Data.ofNat y).size + 1 + ((encL v').size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 1) (v := .ofNat y) (by simp))
    (Eval.var_of_get (i := 3) (v := encL v') (by simp))

/-! ## Soundness -/

theorem ofCode_sound : ∀ (c : Code) (v w : List ℕ), w ∈ c.eval v →
    ∃ t, (ofCode c).Runs (encL v) (encL w) t
  | .zero', v, w, hw => by
    simp only [Code.eval, Part.pure_eq_some, Part.mem_some_iff] at hw
    subst hw
    exact ⟨_, Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := encL v) (by simp))⟩
  | .succ, v, w, hw => by
    simp only [Code.eval, Part.pure_eq_some, Part.mem_some_iff] at hw
    subst hw
    rcases v with _ | ⟨n, v'⟩
    · exact ⟨_, Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.nil _))⟩
    · exact ⟨_, Eval.elim_cons (i := 0) (a := .ofNat n) (b := encL v') (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := .ofNat n) (by simp)))
          (Eval.nil _))⟩
  | .tail, v, w, hw => by
    simp only [Code.eval, Part.pure_eq_some, Part.mem_some_iff] at hw
    subst hw
    rcases v with _ | ⟨n, v'⟩
    · exact ⟨_, Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
    · exact ⟨_, Eval.elim_cons (i := 0) (a := .ofNat n) (b := encL v') (by simp)
        (Eval.var_of_get (i := 1) (v := encL v') (by simp))⟩
  | .cons f fs, v, w, hw => by
    simp only [Code.eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
      Part.mem_some_iff] at hw
    obtain ⟨fv, hfv, fsv, hfsv, rfl⟩ := hw
    obtain ⟨t₁, h₁⟩ := ofCode_sound f v fv hfv
    obtain ⟨t₂, h₂⟩ := ofCode_sound fs v fsv hfsv
    obtain ⟨s, h₃⟩ := consTail_runs fv fsv v
    have h₂' := callVar_eval (env := [encL fv, encL v]) (i := 1) (ofCode_wellScoped fs)
      (v := encL v) (by simp) h₂
    exact ⟨_, Eval.let_ h₁ (Eval.let_ h₂' h₃)⟩
  | .comp f g, v, w, hw => by
    simp only [Code.eval, Part.bind_eq_bind, Part.mem_bind_iff] at hw
    obtain ⟨u, hu, hw⟩ := hw
    obtain ⟨t₁, h₁⟩ := ofCode_sound g v u hu
    obtain ⟨t₂, h₂⟩ := ofCode_sound f u w hw
    exact ⟨_, Eval.let_ h₁ (Eval.append_of_wellScoped h₂ (ofCode_wellScoped f) [encL v])⟩
  | .case f g, v, w, hw => by
    rcases v with _ | ⟨n, v'⟩
    · simp only [Code.eval, List.headI_nil, List.tail_nil] at hw
      obtain ⟨t, h⟩ := ofCode_sound f [] w hw
      exact ⟨_, Eval.elim_nil (i := 0) (by simp)
        (callVar_eval (env := [encL []]) (i := 0) (ofCode_wellScoped f) (v := encL []) (by simp) h)⟩
    · rcases n with _ | y
      · simp only [Code.eval, List.headI_cons, List.tail_cons] at hw
        obtain ⟨t, h⟩ := ofCode_sound f v' w hw
        exact ⟨_, Eval.elim_cons (i := 0) (a := .nil) (b := encL v') (by simp [Data.ofNat])
          (Eval.elim_nil (i := 0) (by simp)
            (callVar_eval (env := [Data.nil, encL v', encL (0 :: v')]) (i := 1)
              (ofCode_wellScoped f) (v := encL v') (by simp) h))⟩
      · simp only [Code.eval, List.headI_cons, List.tail_cons] at hw
        obtain ⟨t, h⟩ := ofCode_sound g (y :: v') w hw
        exact ⟨_, Eval.elim_cons (i := 0) (a := .cons .nil (.ofNat y)) (b := encL v')
          (by simp [Data.ofNat])
          (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat y) (by simp)
            (Eval.let_ (casePair_runs y v')
              (callVar_eval (env := encL (y :: v') :: [Data.nil, .ofNat y, .ofNat (y + 1), encL v',
                encL ((y + 1) :: v')]) (i := 0) (ofCode_wellScoped g) (v := encL (y :: v'))
                (by simp) h)))⟩
  | .fix f, v, w, hw => by
    simp only [Code.eval] at hw
    refine PFun.fixInduction (C := fun v => ∃ t, (ofCode (.fix f)).Runs (encL v) (encL w) t) hw
      fun v hv ih => ?_
    rcases PFun.mem_fix_iff.1 hv with h1 | ⟨v'', h2, -⟩
    · simp only [Part.mem_map_iff] at h1
      obtain ⟨fv, hfv, hfl⟩ := h1
      obtain ⟨t₁, h₁⟩ := ofCode_sound f v fv hfv
      obtain ⟨s, hb⟩ := fixBody_runs (ofCode_wellScoped f) v fv h₁
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp only [List.headI_nil, Nat.default_eq_zero, List.tail_nil, ↓reduceIte,
          Sum.inl.injEq] at hfl
        subst hfl
        exact ⟨_, Eval.loop_stop hb⟩
      · simp only [List.headI_cons, List.tail_cons, ↓reduceIte, Sum.inl.injEq] at hfl
        subst hfl
        exact ⟨_, Eval.loop_stop hb⟩
      · simp at hfl
    · simp only [Part.mem_map_iff] at h2
      obtain ⟨fv, hfv, hfl⟩ := h2
      obtain ⟨t₁, h₁⟩ := ofCode_sound f v fv hfv
      obtain ⟨s, hb⟩ := fixBody_runs (ofCode_wellScoped f) v fv h₁
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp at hfl
      · simp at hfl
      · simp only [List.headI_cons, List.tail_cons, Nat.succ_ne_zero, ↓reduceIte,
          Sum.inr.injEq] at hfl
        subst hfl
        obtain ⟨t₂, h₂⟩ := ih t' (by
          simp only [Part.mem_map_iff]
          exact ⟨(y + 1) :: t', hfv, by simp⟩)
        exact ⟨_, Eval.loop_step hb h₂⟩

/-! ## Completeness -/

theorem ofCode_complete : ∀ (c : Code) (v : List ℕ) (r : Data) (t : ℕ),
    (ofCode c).Runs (encL v) r t → ∃ w, r = encL w ∧ w ∈ c.eval v
  | .zero', v, r, t, h => by
    obtain ⟨t', h'⟩ := ofCode_sound .zero' v (0 :: v) (by simp [Code.eval])
    obtain ⟨rfl, -⟩ := h.deterministic h'
    exact ⟨0 :: v, rfl, by simp [Code.eval]⟩
  | .succ, v, r, t, h => by
    obtain ⟨t', h'⟩ := ofCode_sound .succ v [v.headI.succ] (by simp [Code.eval])
    obtain ⟨rfl, -⟩ := h.deterministic h'
    exact ⟨[v.headI.succ], rfl, by simp [Code.eval]⟩
  | .tail, v, r, t, h => by
    obtain ⟨t', h'⟩ := ofCode_sound .tail v v.tail (by simp [Code.eval])
    obtain ⟨rfl, -⟩ := h.deterministic h'
    exact ⟨v.tail, rfl, by simp [Code.eval]⟩
  | .cons f fs, v, r, t, h => by
    change Eval [encL v] (.let_ (ofCode f) (.let_ (callVar 1 (ofCode fs)) consTail)) r t at h
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨fv, rfl, hfv⟩ := ofCode_complete f v _ _ h₁
      cases h₂ with
      | let_ h₃ h₄ =>
        obtain ⟨t₃, -, h₃'⟩ := callVar_runs_rev (ofCode_wellScoped fs) h₃
        simp only [Env.get_cons_succ, Env.get_cons_zero] at h₃'
        obtain ⟨fsv, rfl, hfsv⟩ := ofCode_complete fs v _ _ h₃'
        obtain ⟨s, h₅⟩ := consTail_runs fv fsv v
        obtain ⟨rfl, -⟩ := h₄.deterministic h₅
        refine ⟨fv.headI :: fsv, rfl, ?_⟩
        simp only [Code.eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
          Part.mem_some_iff]
        exact ⟨fv, hfv, fsv, hfsv, rfl⟩
  | .comp f g, v, r, t, h => by
    change Eval [encL v] (.let_ (ofCode g) (ofCode f)) r t at h
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨u, rfl, hu⟩ := ofCode_complete g v _ _ h₁
      have h₂' := Eval.of_append_of_wellScoped (env := [encL u]) (extra := [encL v]) h₂
        (ofCode_wellScoped f)
      obtain ⟨w, rfl, hw⟩ := ofCode_complete f u _ _ h₂'
      refine ⟨w, rfl, ?_⟩
      simp only [Code.eval, Part.bind_eq_bind, Part.mem_bind_iff]
      exact ⟨u, hu, hw⟩
  | .case f g, v, r, t, h => by
    change Eval [encL v] (.elim 0 (callVar 0 (ofCode f))
      (.elim 0 (callVar 1 (ofCode f)) (.let_ (.cons (.var 1) (.var 3)) (callVar 0 (ofCode g))))) r t
      at h
    rcases v with _ | ⟨n, v'⟩
    · cases h with
      | elim_nil hget h₁ =>
        obtain ⟨t₁, -, h₁'⟩ := callVar_runs_rev (ofCode_wellScoped f) h₁
        simp only [Env.get_cons_zero] at h₁'
        obtain ⟨w, rfl, hw⟩ := ofCode_complete f [] _ _ h₁'
        exact ⟨w, rfl, by simpa [Code.eval] using hw⟩
      | elim_cons hget _ => simp at hget
    · cases h with
      | elim_nil hget _ => simp at hget
      | elim_cons hget h₁ =>
        simp only [Env.get_cons_zero, encL_cons, Data.cons.injEq] at hget
        obtain ⟨rfl, rfl⟩ := hget
        rcases n with _ | y
        · cases h₁ with
          | elim_nil hget h₂ =>
            obtain ⟨t₂, -, h₂'⟩ := callVar_runs_rev (ofCode_wellScoped f) h₂
            simp only [Env.get_cons_succ, Env.get_cons_zero] at h₂'
            obtain ⟨w, rfl, hw⟩ := ofCode_complete f v' _ _ h₂'
            exact ⟨w, rfl, by simpa [Code.eval] using hw⟩
          | elim_cons hget _ => simp [Data.ofNat] at hget
        · cases h₁ with
          | elim_nil hget _ => simp [Data.ofNat] at hget
          | elim_cons hget h₂ =>
            simp only [Env.get_cons_zero, Data.ofNat, Data.cons.injEq] at hget
            obtain ⟨rfl, rfl⟩ := hget
            cases h₂ with
            | let_ h₃ h₄ =>
              obtain ⟨rfl, -⟩ := h₃.deterministic (casePair_runs y v')
              obtain ⟨t₄, -, h₄'⟩ := callVar_runs_rev (ofCode_wellScoped g) h₄
              simp only [Env.get_cons_zero] at h₄'
              obtain ⟨w, rfl, hw⟩ := ofCode_complete g (y :: v') _ _ h₄'
              exact ⟨w, rfl, by simpa [Code.eval] using hw⟩
  | .fix f, v, r, t, h => by
    induction t using Nat.strongRecOn generalizing v r with
    | ind t ih =>
    change Eval [encL v] (.loop (fixBody (ofCode f))) r t at h
    -- the body's run determines the value of `f`
    have body_inv : ∀ {res : Data} {s : ℕ}, Eval [encL v] (fixBody (ofCode f)) res s →
        ∃ fv, fv ∈ f.eval v ∧ res = fixFlag fv := by
      intro res s hb
      change Eval [encL v] (.let_ (callVar 0 (ofCode f)) _) res s at hb
      cases hb with
      | let_ h₁ h₂ =>
        obtain ⟨t₁, -, h₁'⟩ := callVar_runs_rev (ofCode_wellScoped f) h₁
        simp only [Env.get_cons_zero] at h₁'
        obtain ⟨fv, rfl, hfv⟩ := ofCode_complete f v _ _ h₁'
        obtain ⟨s', hb'⟩ := fixBody_runs (ofCode_wellScoped f) v fv (h₁'.cast_cost rfl)
        change Eval [encL v] (.let_ (callVar 0 (ofCode f)) _) (fixFlag fv) s' at hb'
        cases hb' with
        | let_ h₁'' h₂'' =>
          obtain ⟨rfl, -⟩ := h₁.deterministic h₁''
          obtain ⟨rfl, -⟩ := h₂.deterministic h₂''
          exact ⟨fv, hfv, rfl⟩
    cases h with
    | loop_nil hb =>
      obtain ⟨fv, -, hres⟩ := body_inv hb
      rcases fv with _ | ⟨_ | y, t'⟩ <;> simp [fixFlag] at hres
    | loop_stop hb =>
      obtain ⟨fv, hfv, hres⟩ := body_inv hb
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp only [fixFlag, Data.cons.injEq] at hres
        obtain ⟨-, rfl⟩ := hres
        refine ⟨[], rfl, ?_⟩
        simp only [Code.eval]
        refine PFun.mem_fix_iff.2 (Or.inl ?_)
        simp only [Part.mem_map_iff]
        exact ⟨[], hfv, by simp⟩
      · simp only [fixFlag, Data.cons.injEq] at hres
        obtain ⟨-, rfl⟩ := hres
        refine ⟨t', rfl, ?_⟩
        simp only [Code.eval]
        refine PFun.mem_fix_iff.2 (Or.inl ?_)
        simp only [Part.mem_map_iff]
        exact ⟨0 :: t', hfv, by simp⟩
      · simp [fixFlag] at hres
    | loop_step hb hrest =>
      obtain ⟨fv, hfv, hres⟩ := body_inv hb
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp [fixFlag] at hres
      · simp [fixFlag] at hres
      · simp only [fixFlag, Data.cons.injEq] at hres
        obtain ⟨-, rfl⟩ := hres
        obtain ⟨w, rfl, hw⟩ := ih _ (by omega) t' r hrest
        refine ⟨w, rfl, ?_⟩
        simp only [Code.eval] at hw ⊢
        refine PFun.mem_fix_iff.2 (Or.inr ⟨t', ?_, hw⟩)
        simp only [Part.mem_map_iff]
        exact ⟨(y + 1) :: t', hfv, by simp⟩

/-- Halting of the translation of `c` on `encL v` is halting of `c` on `v`. -/
theorem ofCode_halts_iff (c : Code) (v : List ℕ) :
    Halts (ofCode c) (encL v) ↔ (c.eval v).Dom := by
  constructor
  · rintro ⟨r, t, h⟩
    obtain ⟨w, -, hw⟩ := ofCode_complete c v r t h
    exact Part.dom_iff_mem.2 ⟨w, hw⟩
  · intro h
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 h
    obtain ⟨t, ht⟩ := ofCode_sound c v w hw
    exact ⟨_, t, ht⟩

end Prog

/-! ## The halting-problem bridge -/

/-- The universal partial function on code numbers: `n ↦ (decode n).eval 0`. -/
noncomputable def univPart (n : ℕ) : Part ℕ :=
  ((Encodable.decode n : Option Nat.Partrec.Code) : Part Nat.Partrec.Code).bind fun c => c.eval 0

theorem partrec_univPart : Partrec univPart :=
  (Computable.ofOption Computable.decode).bind
    (Nat.Partrec.Code.eval_part.comp Computable.snd (Computable.const 0))

theorem univPart_encode (pc : Nat.Partrec.Code) : univPart (Encodable.encode pc) = pc.eval 0 := by
  simp [univPart]

/-- The halting problem transfers from `Nat.Partrec.Code` to the ambient model along a map
`compile`, computable on descriptions (`encode (compile pc) : Data`). -/
theorem exists_compile :
    ∃ compile : Nat.Partrec.Code → Prog,
      Computable (fun pc => (encode (compile pc) : Data)) ∧
      ∀ pc : Nat.Partrec.Code, Halts (compile pc) .nil ↔ (pc.eval 0).Dom := by
  obtain ⟨cu, hcu⟩ := Turing.ToPartrec.Code.exists_code (n := 1)
    (f := fun v : List.Vector ℕ 1 => univPart v.head)
    (Nat.Partrec'.of_part (partrec_univPart.comp Computable.vector_head))
  have hcu' : ∀ n : ℕ, cu.eval [n] = (univPart n).map pure := fun n => hcu ⟨[n], rfl⟩
  refine ⟨fun pc => hardcode (Prog.ofCode cu) (Data.ofNat (Encodable.encode pc)), ?_, fun pc => ?_⟩
  · -- `toData (hardcode p d)` is a fixed tree around `d`
    have : Primrec fun pc : Nat.Partrec.Code =>
        Data.cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6)
          (Data.ofNat (Encodable.encode pc))) (.cons .nil .nil))) (Prog.ofCode cu).toData) :=
      Data.primrec_cons.comp (Primrec.const _) (Data.primrec_cons.comp
        (Data.primrec_cons.comp (Primrec.const _) (Data.primrec_cons.comp
          (Data.primrec_cons.comp (Primrec.const _) (Data.primrec_ofNat.comp Primrec.encode))
          (Primrec.const _))) (Primrec.const _))
    exact this.to_comp.of_eq fun pc => (toData_hardcode _ _).symm
  · -- halting of the hardcoded translation is halting of `pc` on `0`
    have hdom : (cu.eval [Encodable.encode pc]).Dom ↔ (pc.eval 0).Dom := by
      rw [hcu', univPart_encode]
      exact Iff.rfl
    rw [← hdom, ← Prog.ofCode_halts_iff]
    constructor
    · rintro ⟨r, t, h⟩
      obtain ⟨t', -, h'⟩ := hardcode_time_rev (Prog.ofCode_wellScoped cu) h
      exact ⟨r, t', h'⟩
    · rintro ⟨r, t, h⟩
      exact ⟨r, _, hardcode_time (Prog.ofCode_wellScoped cu) h⟩

end MIPRE.Cost
