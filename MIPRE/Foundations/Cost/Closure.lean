/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.PolyTime

/-!
# The closure library, part I: calls, projections, pairing, branching

Program-layer combinators on `Prog` with their `Eval` lemmas, and the corresponding
`PolyTimeFun` combinators (`const`, `pair`, `fst`, `snd`, `ite`). Two conventions keep
composition free of de Bruijn bookkeeping:

* a closed program `q` is *called* on the value of variable `i` by `let_ (var i) q`
  (`Prog.callVar`): the callee sees its input at variable `0` and, being well-scoped,
  ignores the rest of the environment (`Eval.append_of_wellScoped`);
* branches re-bind the original input by copying it (`PolyTimeFun.ite`), rather than
  shifting indices.

Costs are exact at the program layer and packaged as polynomials at the function layer
(`planning/compression-track.md`, K2).
-/

namespace MIPRE.Cost

open Polynomial

/-! ## Program layer -/

/-- Transport a run along an equation between costs. -/
theorem Eval.cast_cost {env : Env} {p : Prog} {r : Data} {t t' : ℕ} (h : Eval env p r t)
    (e : t = t') : Eval env p r t' :=
  e ▸ h

/-- Reading a variable whose value is known. -/
theorem Eval.var_of_get {env : Env} {i : ℕ} {v : Data} (h : env.get i = v) :
    Eval env (.var i) v (v.size + 1) :=
  h ▸ Eval.var env i

namespace Prog

/-- Call the closed program `q` on the value of variable `i`. -/
def callVar (i : ℕ) (q : Prog) : Prog := .let_ (.var i) q

/-- First component of the input (variable `0`). -/
def fstProg : Prog := .elim 0 .nil (.var 0)

/-- Second component of the input (variable `0`). -/
def sndProg : Prog := .elim 0 .nil (.var 1)

theorem callVar_wellScoped {n i : ℕ} (hi : i < n) {q : Prog} (hq : q.WellScoped 1) :
    (callVar i q).WellScoped n :=
  ⟨hi, hq.mono (by omega) _⟩

theorem fstProg_wellScoped : fstProg.WellScoped 1 := by simp [fstProg, WellScoped]

theorem sndProg_wellScoped : sndProg.WellScoped 1 := by simp [sndProg, WellScoped]

/-- Calling `q` on variable `i`: copy the value, then run `q` (its input is variable `0`;
the rest of the environment is inert). -/
theorem callVar_eval {env : Env} {i : ℕ} {q : Prog} (hq : q.WellScoped 1) {v r : Data}
    {t : ℕ} (hv : env.get i = v) (h : Eval [v] q r t) :
    Eval env (callVar i q) r (v.size + 1 + t + 1) :=
  .let_ (Eval.var_of_get hv) (Eval.append_of_wellScoped h hq env)

theorem fstProg_runs (a b : Data) : fstProg.Runs (.cons a b) a (a.size + 1 + 1) :=
  Eval.elim_cons (env := [Data.cons a b]) (i := 0) (n := .nil) (c := .var 0) (by simp)
    (Eval.var_of_get (env := [a, b, Data.cons a b]) (i := 0) (v := a) (by simp))

theorem sndProg_runs (a b : Data) : sndProg.Runs (.cons a b) b (b.size + 1 + 1) :=
  Eval.elim_cons (env := [Data.cons a b]) (i := 0) (n := .nil) (c := .var 1) (by simp)
    (Eval.var_of_get (env := [a, b, Data.cons a b]) (i := 1) (v := b) (by simp))

end Prog

/-! ## Function layer -/

namespace PolyTimeFun

variable {α β γ : Type*} [SizedEncoding α] [SizedEncoding β] [SizedEncoding γ]

/-- The constant function, in constant time. -/
noncomputable def const (b : β) : PolyTimeFun α β where
  toFun _ := b
  code := .const (encode b)
  closed := trivial
  timeBound := C (esize b)
  computes _ := ⟨esize b, by simp, Eval.const _ _⟩

@[simp] theorem const_apply (b : β) (a : α) : (const b : PolyTimeFun α β) a = b := rfl

/-- Pairing. -/
noncomputable def pair (F : PolyTimeFun α β) (G : PolyTimeFun α γ) :
    PolyTimeFun α (β × γ) where
  toFun a := (F a, G a)
  code := .cons F.code G.code
  closed := ⟨F.closed, G.closed⟩
  timeBound := F.timeBound + G.timeBound + 1
  computes a := by
    obtain ⟨t₁, h₁, e₁⟩ := F.computes a
    obtain ⟨t₂, h₂, e₂⟩ := G.computes a
    refine ⟨t₁ + t₂ + 1, ?_, Eval.cons e₁ e₂⟩
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    omega

@[simp] theorem pair_apply (F : PolyTimeFun α β) (G : PolyTimeFun α γ) (a : α) :
    F.pair G a = (F a, G a) := rfl

/-- First projection. -/
noncomputable def fst : PolyTimeFun (α × β) α where
  toFun := Prod.fst
  code := Prog.fstProg
  closed := Prog.fstProg_wellScoped
  timeBound := X + C 2
  computes p := by
    obtain ⟨a, b⟩ := p
    refine ⟨esize a + 1 + 1, ?_, Prog.fstProg_runs _ _⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod]
    omega

/-- Second projection. -/
noncomputable def snd : PolyTimeFun (α × β) β where
  toFun := Prod.snd
  code := Prog.sndProg
  closed := Prog.sndProg_wellScoped
  timeBound := X + C 2
  computes p := by
    obtain ⟨a, b⟩ := p
    refine ⟨esize b + 1 + 1, ?_, Prog.sndProg_runs _ _⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod]
    omega

@[simp] theorem fst_apply (p : α × β) : (fst : PolyTimeFun (α × β) α) p = p.1 := rfl

@[simp] theorem snd_apply (p : α × β) : (snd : PolyTimeFun (α × β) β) p = p.2 := rfl

/-- Branching on a boolean: `ite c F G a = if c a then F a else G a`. The condition is bound
as variable `0`; the `nil` (`false`) branch calls `G` on the original input (variable `1`),
the `cons` (`true`) branch calls `F` on it (variable `3`, after `elim` bound the two `nil`
components of `encode true`). -/
noncomputable def ite (c : PolyTimeFun α Bool) (F G : PolyTimeFun α β) : PolyTimeFun α β where
  toFun a := if c a then F a else G a
  code := .let_ c.code (.elim 0 (Prog.callVar 1 G.code) (Prog.callVar 3 F.code))
  closed :=
    ⟨c.closed, Nat.zero_lt_succ 1, Prog.callVar_wellScoped (by decide) G.closed,
      Prog.callVar_wellScoped (by decide) F.closed⟩
  timeBound := c.timeBound + X + F.timeBound + G.timeBound + C 4
  computes a := by
    obtain ⟨t₀, h₀, e₀⟩ := c.computes a
    obtain ⟨t₁, h₁, e₁⟩ := F.computes a
    obtain ⟨t₂, h₂, e₂⟩ := G.computes a
    cases hc : c a with
    | false =>
      rw [hc] at e₀
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨t₀ + ((esize a + 1 + t₂ + 1) + 1) + 1, ?_, ?_⟩
      · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
      · refine Eval.let_ e₀ (Eval.elim_nil (by simp [encode, Data.ofBool]) ?_)
        exact Prog.callVar_eval (env := [encode false, encode a]) (i := 1) G.closed
          (by simp) (e₂ : Eval [encode a] G.code (encode (G a)) t₂)
    | true =>
      rw [hc] at e₀
      simp only [↓reduceIte]
      refine ⟨t₀ + ((esize a + 1 + t₁ + 1) + 1) + 1, ?_, ?_⟩
      · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
      · refine Eval.let_ e₀ (Eval.elim_cons (a := .nil) (b := .nil)
          (by simp [encode, Data.ofBool]) ?_)
        exact Prog.callVar_eval (env := [Data.nil, Data.nil, encode true, encode a])
          (i := 3) F.closed (by simp) (e₁ : Eval [encode a] F.code (encode (F a)) t₁)

@[simp] theorem ite_apply (c : PolyTimeFun α Bool) (F G : PolyTimeFun α β) (a : α) :
    ite c F G a = if c a then F a else G a := rfl

end PolyTimeFun

end MIPRE.Cost
