/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SelfDual.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# Self-dual and normal bases, and the downsize identities

The vocabulary of blueprint `lem:self-dual-basis` and of the paper's `\downsize` maps
(`preliminaries.tex`, `sec:ff-representations`): a basis of `K / F` is *self-dual* when its
trace-form Gram matrix is the identity, and *normal* when its vectors are the Frobenius orbit
of a single element.

The two identities proved here are items 1 and 2 of the paper's `lem:downsize_field`, and they
are the reason the pipeline insists on self-duality:

* `coord_eq_trace` — the coordinates of `x` are its trace pairings, `κ(x)ᵢ = tr(x eᵢ)`, so
  `\downsize` is computed by the trace form and needs no matrix inversion;
* `trace_mul_eq_dot` — `tr(xy) = κ(x) · κ(y)`, so the trace form becomes the standard inner
  product on coordinates.

Both need only self-duality, not normality and not odd degree (ledger node `1.1.6.1.11`).
Normality is what the introspection and Pauli-basis interfaces need on top, and is the harder
half of `lem:self-dual-basis`.
-/

namespace MIPRE.LowDegree

open Finset

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {ι : Type*}

/-- `b` is a **self-dual** basis for the trace form of `K / F`: `tr(eᵢ eⱼ) = δᵢⱼ`, that is,
the Gram matrix of `Algebra.traceForm` in `b` is the identity. -/
def IsSelfDualBasis [DecidableEq ι] (b : Module.Basis ι F K) : Prop :=
  ∀ i j, Algebra.trace F K (b i * b j) = if i = j then 1 else 0

/-- `b` is a **normal** basis of `K / F`: its vectors are the Frobenius orbit
`α, α^q, α^{q²}, …` of a single `α`, where `q = #F`. -/
def IsNormalBasis [Fintype F] {k : ℕ} (b : Module.Basis (Fin k) F K) : Prop :=
  ∃ α : K, ∀ i : Fin k, b i = α ^ (Fintype.card F ^ (i : ℕ))

variable [Fintype ι] [DecidableEq ι]

end MIPRE.LowDegree
