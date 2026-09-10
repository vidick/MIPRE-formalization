/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Encoding
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial-time computable functions

`PolyTimeFun α β` bundles a function with a closed program of the ambient model
(`Cost.Basic`) computing it on encodings (`Cost.Encoding`), together with an
**explicit** polynomial time bound. Every "there is a polynomial-time Turing
machine …" of the blueprint (`thm:introspection`, `thm:oracularization`,
`thm:answer-reduction`, `thm:parallel-repetition`, `thm:compression`, and the
hypothesis and conclusion of `lem:recursive-compression`) is a `PolyTimeFun`.

The time bound is *data*, not an existential: the recursion of [JNVWY, §12]
closes by choosing the parameter λ above the concrete overhead polynomials of the
toolkit, and that arithmetic needs the polynomials in hand.

The **closure library** — the combinator toolkit through which all concrete deciders
and transformations will be proven polynomial-time (projections, list/string
operations, recursion on notation, arithmetic on binary numbers, `𝔽₂`-linear
algebra, …) — is the main infrastructure investment of this layer
(`planning/compression-track.md`, K2). Only `id` and `comp` are stated here to fix the
interface; the library grows with the sections that consume it.
-/

namespace MIPRE.Cost

open Polynomial

/-- Evaluation of a polynomial with natural coefficients is monotone in the argument. -/
theorem polynomial_eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) :
    p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-- `p` computes `r` from the input `x` at cost `t`: a run in the environment `[x]`. -/
def Prog.Runs (p : Prog) (x r : Data) (t : ℕ) : Prop := Eval [x] p r t

/-- A polynomial-time computable function `α → β`: a closed program computing it on
encodings, with an explicit polynomial bound on the cost in terms of `esize` of the
input. -/
structure PolyTimeFun (α β : Type*) [SizedEncoding α] [SizedEncoding β] where
  /-- The function computed. -/
  toFun : α → β
  /-- A program computing `toFun` on encodings; its input is variable `0`. -/
  code : Prog
  /-- The program is closed (well-scoped in the one-entry environment). -/
  closed : code.WellScoped 1
  /-- The (explicit) polynomial time bound. -/
  timeBound : Polynomial ℕ
  computes : ∀ a : α, ∃ t ≤ timeBound.eval (esize a), code.Runs (encode a) (encode (toFun a)) t

namespace PolyTimeFun

variable {α β γ : Type*} [SizedEncoding α] [SizedEncoding β] [SizedEncoding γ]

instance : CoeFun (PolyTimeFun α β) fun _ => α → β := ⟨PolyTimeFun.toFun⟩

/-- Polynomial-time output-size bound: a run of cost `t` produces a result of size at most
`t` (`Eval.size_le`). This is what makes `comp` below well-bounded. -/
theorem esize_apply_le (F : PolyTimeFun α β) (a : α) :
    esize (F a) ≤ F.timeBound.eval (esize a) := by
  obtain ⟨t, ht, h⟩ := F.computes a
  exact le_trans h.size_le ht

/-- The identity, in polynomial time: `var 0` reads the input at cost `esize a + 1`.
(`noncomputable` refers only to the bundled `Polynomial ℕ`, which is noncomputable data
in Mathlib.) -/
noncomputable def id (α : Type*) [SizedEncoding α] : PolyTimeFun α α where
  toFun := _root_.id
  code := .var 0
  closed := Nat.zero_lt_one
  timeBound := X + 1
  computes a := ⟨esize a + 1, by simp, Eval.var _ _⟩

@[simp] theorem id_apply (a : α) : PolyTimeFun.id α a = a := rfl

/-- Composition: bind the value of `F` and run `G` on it. -/
noncomputable def comp (G : PolyTimeFun β γ) (F : PolyTimeFun α β) : PolyTimeFun α γ where
  toFun := G.toFun ∘ F.toFun
  code := .let_ F.code G.code
  closed := ⟨F.closed, G.closed.mono (by omega) _⟩
  timeBound := F.timeBound + G.timeBound.comp F.timeBound + 1
  computes a := by
    obtain ⟨t₁, ht₁, h₁⟩ := F.computes a
    obtain ⟨t₂, ht₂, h₂⟩ := G.computes (F a)
    refine ⟨t₁ + t₂ + 1, ?_, Eval.let_ h₁ (Eval.append_of_wellScoped h₂ G.closed _)⟩
    have hmono := polynomial_eval_mono G.timeBound (F.esize_apply_le a)
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one]
    omega

@[simp] theorem comp_apply (G : PolyTimeFun β γ) (F : PolyTimeFun α β) (a : α) :
    G.comp F a = G (F a) := rfl

/-!
Further combinators for the closure library (deferred to K2; the list is indicative):

* `const : β → PolyTimeFun α β` (via `Cost.Toolkit.constProg`);
* `pair : PolyTimeFun α β → PolyTimeFun α γ → PolyTimeFun α (β × γ)`, `fst`, `snd`;
* case analysis on a bit, iteration over a list (`loop`) with a size-bounded body — the
  Cobham-style recursion principle: if the step function is polynomial-time and the
  iterate provably shrinks or preserves size, the recursion is polynomial-time;
* binary arithmetic on `ℕ`, `𝔽₂`- and `𝔽_{2^k}`-algebra as needed by samplers, deciders,
  and the answer-reduction verifier.
-/

end PolyTimeFun

end MIPRE.Cost
