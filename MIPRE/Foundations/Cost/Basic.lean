/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Computability.TuringMachine.Config

/-!
# The ambient cost model

This file fixes the cost model in which **every** polynomial-time statement of the
project is made: the transformations of the compression pipeline (introspection,
oracularization, answer reduction, parallel repetition), the `Compress` map, the
efficient computability toolkit (universal machine, s-m-n, Kleene fixed point;
blueprint Section `sec:rr-computability`), and the recursive compression lemma
(blueprint `lem:recursive-compression`, [MNY] Lemma 5.1).

## The model

Programs are `Turing.ToPartrec.Code` (Mathlib): a term language over `List ℕ` with
primitives `zero'`, `succ`, `tail`, `cons`, `comp`, `case`, `fix`, and big-step
semantics `Code.eval : Code → List ℕ →. List ℕ`. We equip it with a **unit-cost
big-step time semantics**: the inductive relation `TimedEval c v w t` ("`c` on input
`v` halts with output `w` at cost `t`") charges one unit per evaluation rule.

Data is measured by `vsize v = Σᵢ (vᵢ + 1)`: cells are unary-priced. All actual
encodings (see `Cost.Encoding`) use only small cells (bits `0`/`1`, bounded tags and
separators), so on encoded data `vsize` is proportional to string length; a cell can
only hold a large number if someone paid unit cost per `succ` to build it.

## Why this model (decision record)

The choice is driven by the requirements extracted from the JNVWY pipeline:

* **R1 (programmability)**: deciders perform real algorithms (linear algebra over
  `𝔽₂`/`𝔽_{2^k}`, low-degree evaluations, simulations); their polynomial time bounds
  must be provable via a compositional closure library.
* **R2 (self-reference)**: efficient universal machine, s-m-n, and Kleene fixed
  point, with explicit polynomial overheads (the recursion in [MNY, Lemma 5.1] and
  the λ-boundedness bookkeeping of [JNVWY, §12] need them).
* **R3 (arithmetizable tableaux)**: answer reduction needs bounded computations of
  *this* model to have succinct, formula-uniform 3SAT tableaux (blueprint
  `thm:succinct-sat`). This is discharged through a single gateway theorem whose
  proof compiles the model to a low-level machine; Mathlib's `Turing.TMToPartrec`
  (compiling exactly this `Code` to `TM2`) is the natural seed. The low-level
  machine appears in no statement outside that proof.
* **R4 (binary-length sizes)**: indices `n` enter in binary; "succinct" means
  `poly(log)` of the described object.

Two natural alternatives fail:

* `Nat.Partrec.Code` (with any cost semantics) is **not** a viable carrier of
  polynomial time: its primitives reach large values only through `succ`-chains,
  value-indexed `prec` recursion, or `rfind` search, so even `n ↦ 2n` on binary
  representations has no `polylog(n)`-cost program — the induced "P" would not
  contain binary addition. Its numeric pairing (`Nat.pair`, quadratic) also
  distorts lengths exponentially under nesting. It remains the model of the *final*
  computability statements (`MIPRE.HaltingGameValue`), reached via a one-time
  compilation (see `Cost.Compression`).
* Turing machines (`Turing.TM2`, `Turing.FinTM2`) satisfy R3 natively but fail R1/R2
  in practice: Mathlib has no universal machine, no composition, and no way to
  program nontrivial algorithms; `Turing.TM2ComputableInPolyTime` has a single
  inhabitant (the identity) and even composition is `proof_wanted`.

`ToPartrec.Code` sits in the sweet spot: list primitives make binary-string
algorithms and recursion-on-notation direct (R1), `cons`-based hardcoding gives a
*linear*-overhead s-m-n (R2, see `Cost.Toolkit`), sizes are additive (R4), and
Mathlib already compiles it to `TM2` (seed for R3).

**Meta-remark (not formalized).** Unit-cost `TimedEval` is polynomially equivalent
to Turing machine time under pointer/dag simulation: each step allocates `O(1)`
cells, so a cost-`t` run touches a dag of size `O(vsize input + t)`. This standard
fact justifies reading `PolyTimeFun` as honest "polynomial time"; nothing in the
project depends on it formally, since the final theorem only claims `Computable`.

## Main definitions

* `MIPRE.Cost.vsize`: the (unary-cell) size of a machine value `List ℕ`.
* `MIPRE.Cost.TimedEval`: the timed big-step evaluation relation.
* Bridge lemmas to Mathlib's `Code.eval` (soundness, completeness, determinism).

Blueprint: this file is part of `sec:rr-computability` (efficient computability
toolkit), infrastructure level.
-/

namespace MIPRE.Cost

open Turing.ToPartrec

/-- Size of a machine value: cells are priced by their unary size. Encodings
(`Cost.Encoding`) only use bounded cells, so on encoded data this is proportional
to the bit-length. -/
def vsize (v : List ℕ) : ℕ := (v.map (· + 1)).sum

@[simp] theorem vsize_nil : vsize [] = 0 := rfl

@[simp] theorem vsize_cons (n : ℕ) (v : List ℕ) : vsize (n :: v) = n + 1 + vsize v := by
  simp [vsize]

theorem length_le_vsize (v : List ℕ) : v.length ≤ vsize v := by
  induction v with
  | nil => simp
  | cons n v ih => simp only [List.length_cons, vsize_cons]; omega

/-- Timed big-step semantics for `Turing.ToPartrec.Code`: `TimedEval c v w t` holds
if `c` on input `v` halts with output `w`, at total cost `t` (one unit per rule).
Mirrors `Turing.ToPartrec.Code.eval` clause by clause; see `TimedEval.sound` and
`TimedEval.complete`. -/
inductive TimedEval : Code → List ℕ → List ℕ → ℕ → Prop
  | zero' (v : List ℕ) : TimedEval .zero' v (0 :: v) 1
  | succ (v : List ℕ) : TimedEval .succ v [v.headI.succ] 1
  | tail (v : List ℕ) : TimedEval .tail v v.tail 1
  | cons {f fs : Code} {v n ns : List ℕ} {s t : ℕ} :
      TimedEval f v n s → TimedEval fs v ns t →
      TimedEval (.cons f fs) v (n.headI :: ns) (s + t + 1)
  | comp {f g : Code} {v w u : List ℕ} {s t : ℕ} :
      TimedEval g v w s → TimedEval f w u t →
      TimedEval (.comp f g) v u (s + t + 1)
  | case_zero {f g : Code} {v w : List ℕ} {t : ℕ} :
      v.headI = 0 → TimedEval f v.tail w t →
      TimedEval (.case f g) v w (t + 1)
  | case_succ {f g : Code} {v w : List ℕ} {n t : ℕ} :
      v.headI = n + 1 → TimedEval g (n :: v.tail) w t →
      TimedEval (.case f g) v w (t + 1)
  | fix_done {f : Code} {v w : List ℕ} {t : ℕ} :
      w.headI = 0 → TimedEval f v w t →
      TimedEval (.fix f) v w.tail (t + 1)
  | fix_step {f : Code} {v w u : List ℕ} {t s : ℕ} :
      w.headI ≠ 0 → TimedEval f v w t → TimedEval (.fix f) w.tail u s →
      TimedEval (.fix f) v u (t + s + 1)

namespace TimedEval

/-- Soundness: a timed run is a run. Routine induction on the derivation, against
the clauses of `Code.eval` (for `fix`, via `PFun.fix` unfolding). -/
theorem sound {c : Code} {v w : List ℕ} {t : ℕ} (h : TimedEval c v w t) :
    w ∈ c.eval v := by
  induction h with
  | zero' v => simp only [Code.zero'_eval]; exact Part.mem_some _
  | succ v => simp only [Code.succ_eval]; exact Part.mem_some _
  | tail v => simp only [Code.tail_eval]; exact Part.mem_some _
  | cons _ _ ih₁ ih₂ =>
    simp only [Code.cons_eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
      Part.mem_some_iff]
    exact ⟨_, ih₁, _, ih₂, rfl⟩
  | comp _ _ ih₁ ih₂ =>
    simp only [Code.comp_eval, Part.bind_eq_bind, Part.mem_bind_iff]
    exact ⟨_, ih₁, ih₂⟩
  | case_zero h0 _ ih => simp only [Code.case_eval]; rw [h0]; exact ih
  | case_succ hs _ ih => simp only [Code.case_eval]; rw [hs]; exact ih
  | fix_done h0 _ ih =>
    rw [Code.fix_eval]
    exact PFun.mem_fix_iff.2 (Or.inl ((Part.mem_map_iff _).2 ⟨_, ih, by simp [h0]⟩))
  | fix_step hne _ _ ih₁ ih₂ =>
    rw [Code.fix_eval] at ih₂ ⊢
    exact PFun.mem_fix_iff.2 (Or.inr ⟨_, (Part.mem_map_iff _).2 ⟨_, ih₁, by simp [hne]⟩, ih₂⟩)

/-- Completeness: every convergent run has a cost. Induction along `Code.eval`; for
`fix`, by `PFun.fixInduction` on the `PFun.fix` approximation. -/
theorem complete {c : Code} {v w : List ℕ} (h : w ∈ c.eval v) :
    ∃ t, TimedEval c v w t := by
  induction c generalizing v w with
  | zero' =>
    simp only [Code.zero'_eval] at h
    obtain rfl := Part.mem_some_iff.1 h
    exact ⟨_, .zero' v⟩
  | succ =>
    simp only [Code.succ_eval] at h
    obtain rfl := Part.mem_some_iff.1 h
    exact ⟨_, .succ v⟩
  | tail =>
    simp only [Code.tail_eval] at h
    obtain rfl := Part.mem_some_iff.1 h
    exact ⟨_, .tail v⟩
  | cons f fs ihf ihfs =>
    simp only [Code.cons_eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
      Part.mem_some_iff] at h
    obtain ⟨n, hn, ns, hns, rfl⟩ := h
    obtain ⟨s, hs⟩ := ihf hn
    obtain ⟨t, ht⟩ := ihfs hns
    exact ⟨_, .cons hs ht⟩
  | comp f g ihf ihg =>
    simp only [Code.comp_eval, Part.bind_eq_bind, Part.mem_bind_iff] at h
    obtain ⟨w', hw', hw⟩ := h
    obtain ⟨s, hs⟩ := ihg hw'
    obtain ⟨t, ht⟩ := ihf hw
    exact ⟨_, .comp hs ht⟩
  | case f g ihf ihg =>
    simp only [Code.case_eval] at h
    by_cases hv : v.headI = 0
    · rw [hv] at h
      obtain ⟨t, ht⟩ := ihf h
      exact ⟨_, .case_zero hv ht⟩
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
      rw [hn] at h
      obtain ⟨t, ht⟩ := ihg h
      exact ⟨_, .case_succ hn ht⟩
  | fix f ih =>
    rw [Code.fix_eval] at h
    refine PFun.fixInduction h fun v' hv' IH => ?_
    rcases PFun.mem_fix_iff.1 hv' with h1 | ⟨v'', hv'', -⟩
    · obtain ⟨w', hw', hg⟩ := (Part.mem_map_iff _).1 h1
      by_cases h0 : w'.headI = 0
      · simp only [h0, if_true, Sum.inl.injEq] at hg
        subst hg
        obtain ⟨t, ht⟩ := ih hw'
        exact ⟨_, .fix_done h0 ht⟩
      · simp [h0] at hg
    · obtain ⟨w', hw', hg⟩ := (Part.mem_map_iff _).1 hv''
      by_cases h0 : w'.headI = 0
      · simp [h0] at hg
      · simp only [h0, if_false, Sum.inr.injEq] at hg
        subst hg
        obtain ⟨s, hs⟩ := IH _ hv''
        obtain ⟨t, ht⟩ := ih hw'
        exact ⟨_, .fix_step h0 ht hs⟩

/-- The timed semantics is deterministic in both output and cost. -/
theorem deterministic {c : Code} {v w w' : List ℕ} {t t' : ℕ}
    (h : TimedEval c v w t) (h' : TimedEval c v w' t') : w = w' ∧ t = t' := by
  induction h generalizing w' t' with
  | zero' v => cases h'; exact ⟨rfl, rfl⟩
  | succ v => cases h'; exact ⟨rfl, rfl⟩
  | tail v => cases h'; exact ⟨rfl, rfl⟩
  | cons _ _ ih₁ ih₂ =>
    cases h' with
    | cons h₁' h₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
  | comp _ _ ih₁ ih₂ =>
    cases h' with
    | comp h₁' h₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
  | case_zero h0 _ ih =>
    cases h' with
    | case_zero _ h₂' => obtain ⟨rfl, rfl⟩ := ih h₂'; exact ⟨rfl, rfl⟩
    | case_succ hs _ => omega
  | case_succ hs _ ih =>
    cases h' with
    | case_zero h0 _ => omega
    | case_succ hs' h₂' =>
      obtain rfl := Nat.add_right_cancel (hs.symm.trans hs')
      obtain ⟨rfl, rfl⟩ := ih h₂'
      exact ⟨rfl, rfl⟩
  | fix_done h0 _ ih =>
    cases h' with
    | fix_done _ h₂' => obtain ⟨rfl, rfl⟩ := ih h₂'; exact ⟨rfl, rfl⟩
    | fix_step hne h₂' _ => obtain ⟨rfl, rfl⟩ := ih h₂'; exact absurd h0 hne
  | fix_step hne _ _ ih₁ ih₂ =>
    cases h' with
    | fix_done h0 h₂' => obtain ⟨rfl, rfl⟩ := ih₁ h₂'; exact absurd h0 hne
    | fix_step _ h₂' h₃' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₂'
      obtain ⟨rfl, rfl⟩ := ih₂ h₃'
      exact ⟨rfl, rfl⟩

/-- Costs are positive. -/
theorem pos {c : Code} {v w : List ℕ} {t : ℕ} (h : TimedEval c v w t) : 0 < t := by
  cases h <;> omega

/-- Each rule appends at most one cell, so output *length* grows at most linearly
with cost. (No such bound holds for `vsize`: a step may duplicate a reference to a
large cell. This is harmless — encodings use bounded cells — and is where the
dag-simulation meta-remark in the file docstring enters.) -/
theorem length_le {c : Code} {v w : List ℕ} {t : ℕ} (h : TimedEval c v w t) :
    w.length ≤ v.length + t := by
  induction h with
  | zero' v => simp
  | succ v => simp
  | tail v => simp only [List.length_tail]; omega
  | cons _ _ ih₁ ih₂ => simp only [List.length_cons]; omega
  | comp _ _ ih₁ ih₂ => omega
  | case_zero _ _ ih => simp only [List.length_tail] at ih; omega
  | case_succ _ _ ih => simp only [List.length_cons, List.length_tail] at ih; omega
  | fix_done _ _ ih => simp only [List.length_tail]; omega
  | fix_step _ _ _ ih₁ ih₂ => simp only [List.length_tail] at ih₂; omega

/-- Transport a run along an equation between costs. -/
theorem cast_cost {c : Code} {v w : List ℕ} {t t' : ℕ} (h : TimedEval c v w t)
    (e : t = t') : TimedEval c v w t' :=
  e ▸ h

/-- The run of Mathlib's `Code.id = tail.comp zero'`: three steps. -/
theorem code_id (v : List ℕ) : TimedEval Code.id v v 3 :=
  show TimedEval (Code.tail.comp Code.zero') v v 3 from .comp (.zero' v) (.tail _)

/-- The run of Mathlib's `Code.nil = tail.comp succ`: three steps. -/
theorem code_nil (v : List ℕ) : TimedEval Code.nil v [] 3 :=
  show TimedEval (Code.tail.comp Code.succ) v [] 3 from .comp (.succ v) (.tail _)

/-- The run of Mathlib's `Code.zero = cons zero' nil`: five steps. -/
theorem code_zero (v : List ℕ) : TimedEval Code.zero v [0] 5 :=
  show TimedEval (Code.cons Code.zero' Code.nil) v [0] 5 from .cons (.zero' v) (code_nil v)

end TimedEval

/-- `c` halts on `v` within cost `t`, with some output. -/
def HaltsWithin (c : Code) (v : List ℕ) (t : ℕ) : Prop :=
  ∃ w t', t' ≤ t ∧ TimedEval c v w t'

/-- A (total) time bound for `c`, as a function of the input size. This is the
notion `TIME_𝒮, TIME_𝒟 ≤ ⋯` of blueprint `def:lambda-bounded` specializes. -/
def TimeBound (c : Code) (T : ℕ → ℕ) : Prop :=
  ∀ v : List ℕ, HaltsWithin c v (T (vsize v))

end MIPRE.Cost
