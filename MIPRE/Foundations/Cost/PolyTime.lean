/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Encoding
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial-time computable functions

`PolyTimeFun α β` bundles a function with a program of the ambient model
(`Cost.Basic`) computing it on encodings (`Cost.Encoding`), together with an
**explicit** polynomial time bound. Every "there is a polynomial-time Turing
machine …" of the blueprint (`thm:introspection`, `thm:oracularization`,
`thm:answer-reduction`, `thm:parallel-repetition`, `thm:compression`, and the
hypothesis and conclusion of `lem:recursive-compression`) is a `PolyTimeFun`.

The time bound is *data*, not an existential: the recursion of [JNVWY, §12]
closes by choosing the parameter λ above the concrete overhead polynomials of the
toolkit, and that arithmetic needs the polynomials in hand. (Compare Mathlib's
`Turing.TM2ComputableInPolyTime`, also a bundled structure, whose only inhabitant
is the identity and whose composition is `proof_wanted`; the present structure is
its workhorse replacement in the ambient model.)

The **closure library** — the Cobham-style combinator toolkit through which all
concrete deciders and transformations will be proven polynomial-time (projections,
list/string operations, recursion on notation, arithmetic on binary numbers,
`𝔽₂`-linear algebra, …) — is the main infrastructure investment of this layer.
Only `id` and `comp` are stated here to fix the interface; the library grows with
the pipeline sections that consume it. Automation (a `polyfun`-style tactic) is
strongly advisable; see prakol16's Lean 3 experiments for a proof of concept.
-/

namespace MIPRE.Cost

open Turing.ToPartrec Polynomial

/-- A polynomial-time computable function `α → β`: a program of the ambient model
computing it on encodings, with an explicit polynomial bound on `TimedEval` cost
in terms of `esize` of the input. -/
structure PolyTimeFun (α β : Type*) [SizedEncoding α] [SizedEncoding β] where
  /-- The function computed. -/
  toFun : α → β
  /-- A program computing `toFun` on encodings. -/
  code : Code
  /-- The (explicit) polynomial time bound. -/
  timeBound : Polynomial ℕ
  computes : ∀ a : α, ∃ t ≤ timeBound.eval (esize a),
    TimedEval code (encode a) (encode (toFun a)) t

namespace PolyTimeFun

variable {α β γ : Type*} [SizedEncoding α] [SizedEncoding β] [SizedEncoding γ]

instance : CoeFun (PolyTimeFun α β) fun _ => α → β := ⟨PolyTimeFun.toFun⟩

/-- Polynomial-time output-size bound: a cost-`t` run emits at most `t` new cells
(`TimedEval.length_le`), so `esize (F a) ≤ esize a + timeBound.eval (esize a)`.
This is what makes `comp` below well-bounded. -/
theorem esize_apply_le (F : PolyTimeFun α β) (a : α) :
    esize (F a) ≤ esize a + F.timeBound.eval (esize a) := by
  sorry -- from `computes`, `TimedEval.length_le`, `esize = length of encoding`

/-- The identity, in polynomial time (`Code.id = tail.comp zero'`, three steps).
(`noncomputable` refers only to the bundled `Polynomial ℕ`, which is
noncomputable data in Mathlib.) -/
noncomputable def id (α : Type*) [SizedEncoding α] : PolyTimeFun α α where
  toFun := _root_.id
  code := Code.id
  timeBound := C 3
  computes a := ⟨3, by simp, by
    sorry⟩ -- `TimedEval.comp (.zero' _) (.tail _)`, routine

/-- Composition, with the composed time bound explicit. -/
noncomputable def comp (G : PolyTimeFun β γ) (F : PolyTimeFun α β) : PolyTimeFun α γ where
  toFun := G.toFun ∘ F.toFun
  code := G.code.comp F.code
  timeBound := F.timeBound + G.timeBound.comp (X + F.timeBound) + 1
  computes a := by
    sorry -- chain `F.computes`, `G.computes`, `esize_apply_le`; routine

@[simp] theorem comp_apply (G : PolyTimeFun β γ) (F : PolyTimeFun α β) (a : α) :
    G.comp F a = G (F a) := rfl

/-!
Further combinators for the closure library (deferred; the list is indicative):

* `const : β → PolyTimeFun α β` (via `Cost.Toolkit.pushList`);
* `pair : PolyTimeFun α β → PolyTimeFun α γ → PolyTimeFun α (β × γ)`,
  `fst`, `snd`;
* case analysis, bounded `fix` / recursion on notation — the Cobham-style
  recursion principle: if the step function is polynomial-time and the iterate
  provably shrinks or preserves size, the recursion is polynomial-time;
* binary arithmetic on `ℕ`, `𝔽₂`- and `𝔽_{2^k}`-algebra as needed by samplers,
  deciders, and the answer-reduction verifier.
-/

end PolyTimeFun

end MIPRE.Cost
