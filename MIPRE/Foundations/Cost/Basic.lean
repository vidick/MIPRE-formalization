/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Basic

/-!
# The ambient cost model

This file fixes the cost model in which **every** polynomial-time statement of the
project is made: the transformations of the compression pipeline (introspection,
oracularization, answer reduction, parallel repetition), the `Compress` map, the
efficient computability toolkit (universal machine, s-m-n, Kleene fixed point;
blueprint Section `sec:rr-computability`), and the recursive compression lemma
(blueprint `lem:recursive-compression`, [MNY] Lemma 5.1).

## The model

Data are binary trees (`Data`: `nil` and `cons`), the S-expressions in which bit
strings, numbers, pairs and programs are all encoded (`Cost.Encoding`). `Data.size`
counts nodes; it is the bit-length of the preorder serialization `Data.toBits`, so
sizes are additive under pairing (R4 below).

Programs (`Prog`) form a minimal first-order language with de Bruijn variables over an
environment of `Data` values: `var i` reads a variable, `nil` and `cons h t` build
values, `elim i n c` inspects the `i`-th variable (binding the two components of a
`cons`), `let_ e b` binds, and `loop b` iterates `b` on the state held in variable `0`
until it signals stop. The timed big-step semantics `Eval env p r t` charges one unit
per rule, except that reading a variable additionally costs the size of the value read:
**values are copied when read and inspected in place by `elim`**. Consequently a run
of cost `t` produces a result of size at most `t` (`Eval.size_le`), so every value
occurring in a computation is polynomially bounded by the running time — which is what
makes the unit costs honest under a pointer-machine, and then Turing-machine, simulation
with polynomial overhead (meta-remark below).

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
  proof compiles the model to the machine model of `MIPRE/TM` (planned Milestone H1
  of `planning/tm-infrastructure.md`). The low-level machine appears in no statement
  outside that proof.
* **R4 (binary-length sizes)**: indices `n` enter in binary; "succinct" means
  `poly(log)` of the described object.

Three natural alternatives fail:

* `Nat.Partrec.Code` (with any cost semantics) is **not** a viable carrier of
  polynomial time: its primitives reach large values only through `succ`-chains,
  value-indexed `prec` recursion, or `rfind` search, so even `n ↦ 2n` on binary
  representations has no `polylog(n)`-cost program — the induced "P" would not
  contain binary addition. Its numeric pairing (`Nat.pair`, quadratic) also
  distorts lengths exponentially under nesting. It remains the model of the *final*
  computability statements (`MIPRE.HaltingGameValue`), reached via a one-time
  compilation (`Foundations/Compression.lean`).
* Mathlib's `Turing.ToPartrec.Code`, the model used until 2026-09-08, cannot rebuild
  lists in polynomial time. Its primitives act only on the front of a single `List ℕ`
  value (prepend, drop or replace the first cell), and the value is passed by value; so
  every output has the form `p ++ v.drop k`, and the input suffix can only be discarded
  by first dropping everything built in front of it, which retains a program-size-bounded
  number of cells of polynomially bounded value — `O(log t)` bits of information. Hence
  `List.reverse`, `x ↦ x ++ [b]`, binary addition and the runtime s-m-n map are not
  polynomial-time computable there: it is a one-stack machine with a read-only input,
  adequate for Mathlib's numeric use (`Code.exists_code` returns singletons `[n]`) but
  not for string processing. (Trailing `0` cells are moreover invisible to every program.)
* Turing machines (`Turing.TM2`, `Turing.FinTM2`, the project's own `Turing.Code i`)
  satisfy R3 natively but fail R1/R2 in practice: Mathlib has no universal machine, no
  composition, and no way to program nontrivial algorithms; machine-level combinator
  libraries (CSLib's, under construction) cost hundreds of lines per combinator.

`Prog` sits in the sweet spot: `cons` builds and `elim` destructs anywhere in a value, so
string algorithms and recursion on notation are direct (R1); programs are trees, hence
data with additive sizes (`Prog.toData` in `Cost.Encoding`), and hardcoding an argument is
`let_ (cons (constant) (var 0))` at linear cost (R2, R4); and the language is small enough
for its metatheory and for a self-interpreter — the universal machine of `Cost.Toolkit` —
to be manageable, and to be compiled to the machine model for R3. The design follows the
"rose tree machine" idea of C. Reitwiessner (CSLib issue #611) with binary trees in place of
rose trees and a time-only semantics.

**Meta-remark (not formalized).** A pointer machine represents values as DAGs of `cons`
cells: `cons`, `elim` and `let_` are constant-time, `var i` copies its value in time
proportional to its size (exactly the charged cost), so a run of cost `t` takes `O(t)`
pointer-machine time on `O(t + input)` cells, and Turing-machine time polynomial in that.
This justifies reading `PolyTimeFun` as honest "polynomial time"; nothing in the project
depends on it formally, since the final theorem only claims `Computable`.

## Main definitions

* `MIPRE.Cost.Data`, `Data.size`, `Data.toBits`, `Data.ofNat` (unary numerals).
* `MIPRE.Cost.Prog`, `Prog.WellScoped`.
* `MIPRE.Cost.Env`, `Env.get`.
* `MIPRE.Cost.Eval`: the timed big-step semantics; `Eval.deterministic`, `Eval.pos`,
  `Eval.size_le`, and the scoping lemmas `Eval.append_of_wellScoped` /
  `Eval.of_append_of_wellScoped` (extra environment entries are inert for well-scoped
  programs).
* `MIPRE.Cost.evalFuel`: an executable evaluator with fuel, sound for `Eval`.
* `MIPRE.Cost.Halts`, `HaltsWithin`, `TimeBound`.

Blueprint: this file is part of `sec:rr-computability` (efficient computability
toolkit), infrastructure level.
-/

namespace MIPRE.Cost

/-- Binary trees: the data of the ambient model. -/
inductive Data where
  | nil : Data
  | cons : Data → Data → Data
  deriving DecidableEq, Repr, Inhabited

namespace Data

/-- Size: the number of nodes, `nil` counting one. -/
def size : Data → ℕ
  | nil => 1
  | cons a b => a.size + b.size + 1

@[simp] theorem size_nil : size nil = 1 := rfl

@[simp] theorem size_cons (a b : Data) : (cons a b).size = a.size + b.size + 1 := rfl

theorem size_pos (d : Data) : 0 < d.size := by cases d <;> simp [size]

/-- Preorder serialization, one bit per node: `nil ↦ 0`, `cons a b ↦ 1 · a · b`. It is a
prefix code, and its length is the size. -/
def toBits : Data → List Bool
  | nil => [false]
  | cons a b => true :: (a.toBits ++ b.toBits)

@[simp] theorem length_toBits (d : Data) : d.toBits.length = d.size := by
  induction d with
  | nil => rfl
  | cons a b iha ihb => simp [toBits, iha, ihb]

/-- Unary numerals: `ofNat n` is the list of `n` copies of `nil`. Used for tags, counters
and budgets. -/
def ofNat : ℕ → Data
  | 0 => nil
  | n + 1 => cons nil (ofNat n)

@[simp] theorem size_ofNat (n : ℕ) : (ofNat n).size = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofNat, ih]; omega

/-- Reading a unary numeral back. -/
def toNat? : Data → Option ℕ
  | nil => some 0
  | cons nil d => (toNat? d).map (· + 1)
  | cons (cons _ _) _ => none

@[simp] theorem toNat?_ofNat (n : ℕ) : toNat? (ofNat n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofNat, toNat?, ih]

end Data

/-- Programs of the ambient model, with de Bruijn variables (`var 0` is the innermost
bound variable; the input of a program is `var 0`). -/
inductive Prog where
  /-- Read variable `i` (copying it: cost `1 + size`). -/
  | var (i : ℕ)
  /-- The atom. -/
  | nil
  /-- Build a node from the values of `h` and `t`. -/
  | cons (h t : Prog)
  /-- Inspect variable `i` in place: if it is `nil`, run `n`; if it is `cons a b`, run `c`
  with `a` and `b` bound as variables `0` and `1`. -/
  | elim (i : ℕ) (n c : Prog)
  /-- Bind the value of `e` as variable `0` and run `b`. -/
  | let_ (e b : Prog)
  /-- Iterate `b` on the state held in variable `0`: `b` returns `cons flag s'`; if `flag`
  is `nil` the loop stops with result `s'`, otherwise it continues with state `s'`. (A body
  result `nil` stops with result `nil`.) -/
  | loop (b : Prog)
  deriving DecidableEq, Repr, Inhabited

namespace Prog

/-- `WellScoped n p`: every variable of `p` is bound in an environment of length `n`. -/
def WellScoped : ℕ → Prog → Prop
  | n, var i => i < n
  | _, nil => True
  | n, cons h t => WellScoped n h ∧ WellScoped n t
  | n, elim i a c => i < n ∧ WellScoped n a ∧ WellScoped (n + 2) c
  | n, let_ e b => WellScoped n e ∧ WellScoped (n + 1) b
  | n, loop b => 0 < n ∧ WellScoped n b

theorem WellScoped.mono {n m : ℕ} (h : n ≤ m) :
    ∀ (p : Prog), WellScoped n p → WellScoped m p
  | var _, hp => Nat.lt_of_lt_of_le hp h
  | nil, _ => trivial
  | cons a b, ⟨ha, hb⟩ => ⟨mono h a ha, mono h b hb⟩
  | elim _ a c, ⟨hi, ha, hc⟩ =>
    ⟨Nat.lt_of_lt_of_le hi h, mono h a ha, mono (Nat.add_le_add_right h 2) c hc⟩
  | let_ e b, ⟨he, hb⟩ => ⟨mono h e he, mono (Nat.add_le_add_right h 1) b hb⟩
  | loop b, ⟨h₀, hb⟩ => ⟨Nat.lt_of_lt_of_le h₀ h, mono h b hb⟩

end Prog

/-- Environments: the values of the variables, innermost (index `0`) first. -/
abbrev Env := List Data

/-- Variable lookup; reading beyond the environment gives `nil`, so that the semantics is
total. -/
def Env.get (env : Env) (i : ℕ) : Data := env.getD i .nil

@[simp] theorem Env.get_cons_zero (v : Data) (env : Env) : Env.get (v :: env) 0 = v := by
  simp only [Env.get, List.getD_cons_zero]

@[simp] theorem Env.get_cons_succ (v : Data) (env : Env) (i : ℕ) :
    Env.get (v :: env) (i + 1) = Env.get env i := by
  simp only [Env.get, List.getD_cons_succ]

@[simp] theorem Env.get_nil (i : ℕ) : Env.get [] i = .nil := by
  simp only [Env.get, List.getD_nil]

theorem Env.get_append {env extra : Env} {i : ℕ} (h : i < env.length) :
    Env.get (env ++ extra) i = Env.get env i := by
  induction env generalizing i with
  | nil => simp at h
  | cons v env ih =>
    cases i with
    | zero => simp only [List.cons_append, Env.get_cons_zero]
    | succ i =>
      simp only [List.cons_append, Env.get_cons_succ]
      exact ih (by simpa using h)

/-- Timed big-step semantics: `Eval env p r t` means that `p`, in environment `env`, halts
with result `r` at cost `t`. One unit per rule; reading a variable additionally costs the
size of the value read. -/
inductive Eval : Env → Prog → Data → ℕ → Prop
  | var (env : Env) (i : ℕ) : Eval env (.var i) (env.get i) ((env.get i).size + 1)
  | nil (env : Env) : Eval env .nil .nil 1
  | cons {env : Env} {h t : Prog} {a b : Data} {s u : ℕ} :
      Eval env h a s → Eval env t b u → Eval env (.cons h t) (.cons a b) (s + u + 1)
  | elim_nil {env : Env} {i : ℕ} {n c : Prog} {r : Data} {t : ℕ} :
      env.get i = .nil → Eval env n r t → Eval env (.elim i n c) r (t + 1)
  | elim_cons {env : Env} {i : ℕ} {n c : Prog} {a b r : Data} {t : ℕ} :
      env.get i = .cons a b → Eval (a :: b :: env) c r t → Eval env (.elim i n c) r (t + 1)
  | let_ {env : Env} {e b : Prog} {v r : Data} {s t : ℕ} :
      Eval env e v s → Eval (v :: env) b r t → Eval env (.let_ e b) r (s + t + 1)
  | loop_nil {env : Env} {b : Prog} {t : ℕ} :
      Eval env b .nil t → Eval env (.loop b) .nil (t + 1)
  | loop_stop {env : Env} {b : Prog} {r : Data} {t : ℕ} :
      Eval env b (.cons .nil r) t → Eval env (.loop b) r (t + 1)
  | loop_step {env : Env} {b : Prog} {x y v r : Data} {s t : ℕ} :
      Eval env b (.cons (.cons x y) v) s → Eval (v :: env.tail) (.loop b) r t →
      Eval env (.loop b) r (s + t + 1)

namespace Eval

/-- Costs are positive. -/
theorem pos {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t) : 0 < t := by
  cases h <;> omega

/-- The semantics is deterministic in both result and cost. -/
theorem deterministic {env : Env} {p : Prog} {r r' : Data} {t t' : ℕ}
    (h : Eval env p r t) (h' : Eval env p r' t') : r = r' ∧ t = t' := by
  induction h generalizing r' t' with
  | var env i => cases h'; exact ⟨rfl, rfl⟩
  | nil env => cases h'; exact ⟨rfl, rfl⟩
  | cons _ _ ih₁ ih₂ =>
    cases h' with
    | cons h₁' h₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
  | elim_nil hn _ ih =>
    cases h' with
    | elim_nil _ h₂' => obtain ⟨rfl, rfl⟩ := ih h₂'; exact ⟨rfl, rfl⟩
    | elim_cons hc _ => rw [hn] at hc; cases hc
  | elim_cons hc _ ih =>
    cases h' with
    | elim_nil hn _ => rw [hn] at hc; cases hc
    | elim_cons hc' h₂' =>
      rw [hc] at hc'
      cases hc'
      obtain ⟨rfl, rfl⟩ := ih h₂'
      exact ⟨rfl, rfl⟩
  | let_ _ _ ih₁ ih₂ =>
    cases h' with
    | let_ h₁' h₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
  | loop_nil _ ih =>
    cases h' with
    | loop_nil h₁' => obtain ⟨-, rfl⟩ := ih h₁'; exact ⟨rfl, rfl⟩
    | loop_stop h₁' => obtain ⟨h, -⟩ := ih h₁'; cases h
    | loop_step h₁' _ => obtain ⟨h, -⟩ := ih h₁'; cases h
  | loop_stop _ ih =>
    cases h' with
    | loop_nil h₁' => obtain ⟨h, -⟩ := ih h₁'; cases h
    | loop_stop h₁' => obtain ⟨h, rfl⟩ := ih h₁'; cases h; exact ⟨rfl, rfl⟩
    | loop_step h₁' _ => obtain ⟨h, -⟩ := ih h₁'; cases h
  | loop_step _ _ ih₁ ih₂ =>
    cases h' with
    | loop_nil h₁' => obtain ⟨h, -⟩ := ih₁ h₁'; cases h
    | loop_stop h₁' => obtain ⟨h, -⟩ := ih₁ h₁'; cases h
    | loop_step h₁' h₂' =>
      obtain ⟨h, rfl⟩ := ih₁ h₁'
      cases h
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩

/-- A run of cost `t` produces a result of size at most `t`: every node of the result was
either built (`cons`, `nil`) or copied (`var`) at unit cost per node. -/
theorem size_le {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t) :
    r.size ≤ t := by
  induction h with
  | var env i => omega
  | nil env => simp
  | cons _ _ ih₁ ih₂ => simp only [Data.size_cons]; omega
  | elim_nil _ _ ih => omega
  | elim_cons _ _ ih => omega
  | let_ _ _ ih₁ ih₂ => omega
  | loop_nil _ _ => simp only [Data.size_nil]; omega
  | loop_stop _ ih => simp only [Data.size_cons, Data.size_nil] at ih; omega
  | loop_step _ _ _ ih₂ => omega

/-- Extra environment entries are inert for a well-scoped program (weakening). -/
theorem append_of_wellScoped {env : Env} {p : Prog} {r : Data} {t : ℕ}
    (h : Eval env p r t) (hp : p.WellScoped env.length) (extra : Env) :
    Eval (env ++ extra) p r t := by
  induction h with
  | var env i =>
    have hi : i < env.length := hp
    rw [← Env.get_append (extra := extra) hi]
    exact .var _ _
  | nil env => exact .nil _
  | cons _ _ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hp
    exact .cons (ih₁ h₁) (ih₂ h₂)
  | elim_nil hn _ ih =>
    obtain ⟨hi, h₁, -⟩ := hp
    exact .elim_nil (by rw [Env.get_append hi]; exact hn) (ih h₁)
  | elim_cons hc _ ih =>
    obtain ⟨hi, -, h₂⟩ := hp
    exact .elim_cons (by rw [Env.get_append hi]; exact hc) (ih h₂)
  | let_ _ _ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hp
    exact .let_ (ih₁ h₁) (ih₂ h₂)
  | loop_nil _ ih =>
    obtain ⟨-, h₁⟩ := hp
    exact .loop_nil (ih h₁)
  | loop_stop _ ih =>
    obtain ⟨-, h₁⟩ := hp
    exact .loop_stop (ih h₁)
  | @loop_step env b x y v r s t _ _ ih₁ ih₂ =>
    obtain ⟨h₀, h₁⟩ := hp
    obtain ⟨w, env', rfl⟩ : ∃ w env', env = w :: env' := by
      cases env with
      | nil => simp at h₀
      | cons w env' => exact ⟨w, env', rfl⟩
    exact .loop_step (ih₁ h₁) (ih₂ ⟨h₀, h₁⟩)

/-- Extra environment entries are inert for a well-scoped program (strengthening). -/
theorem of_append_of_wellScoped {env extra : Env} {p : Prog} {r : Data} {t : ℕ}
    (h : Eval (env ++ extra) p r t) (hp : p.WellScoped env.length) : Eval env p r t := by
  generalize henv : env ++ extra = env' at h
  induction h generalizing env with
  | var env'' i =>
    subst henv
    have hi : i < env.length := hp
    rw [Env.get_append hi]
    exact .var _ _
  | nil _ => exact .nil _
  | cons _ _ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hp
    exact .cons (ih₁ (env := env) h₁ henv) (ih₂ (env := env) h₂ henv)
  | elim_nil hn _ ih =>
    subst henv
    obtain ⟨hi, h₁, -⟩ := hp
    exact .elim_nil (by rw [← Env.get_append hi]; exact hn) (ih (env := env) h₁ rfl)
  | @elim_cons _ i n c a b _ _ hc _ ih =>
    subst henv
    obtain ⟨hi, -, h₂⟩ := hp
    exact .elim_cons (by rw [← Env.get_append hi]; exact hc)
      (ih (env := a :: b :: env) h₂ rfl)
  | @let_ _ e b v _ _ _ _ _ ih₁ ih₂ =>
    subst henv
    obtain ⟨h₁, h₂⟩ := hp
    exact .let_ (ih₁ (env := env) h₁ rfl) (ih₂ (env := v :: env) h₂ rfl)
  | loop_nil _ ih =>
    obtain ⟨-, h₁⟩ := hp
    exact .loop_nil (ih (env := env) h₁ henv)
  | loop_stop _ ih =>
    obtain ⟨-, h₁⟩ := hp
    exact .loop_stop (ih (env := env) h₁ henv)
  | @loop_step _ b x y v _ _ _ _ _ ih₁ ih₂ =>
    subst henv
    obtain ⟨h₀, h₁⟩ := hp
    obtain ⟨w, env', rfl⟩ : ∃ w env', env = w :: env' := by
      cases env with
      | nil => simp at h₀
      | cons w env' => exact ⟨w, env', rfl⟩
    exact .loop_step (ih₁ (env := w :: env') h₁ rfl) (ih₂ (env := v :: env') ⟨h₀, h₁⟩ rfl)

end Eval

/-- Executable evaluator with fuel (one unit of fuel per rule), returning the result and
its cost. -/
def evalFuel : ℕ → Env → Prog → Option (Data × ℕ)
  | 0, _, _ => none
  | _ + 1, env, .var i => some (env.get i, (env.get i).size + 1)
  | _ + 1, _, .nil => some (.nil, 1)
  | f + 1, env, .cons h t =>
    match evalFuel f env h, evalFuel f env t with
    | some (a, s), some (b, u) => some (.cons a b, s + u + 1)
    | _, _ => none
  | f + 1, env, .elim i n c =>
    match env.get i with
    | .nil => (evalFuel f env n).map fun x => (x.1, x.2 + 1)
    | .cons a b => (evalFuel f (a :: b :: env) c).map fun x => (x.1, x.2 + 1)
  | f + 1, env, .let_ e b =>
    match evalFuel f env e with
    | some (v, s) => (evalFuel f (v :: env) b).map fun x => (x.1, s + x.2 + 1)
    | none => none
  | f + 1, env, .loop b =>
    match evalFuel f env b with
    | some (.nil, s) => some (.nil, s + 1)
    | some (.cons .nil r, s) => some (r, s + 1)
    | some (.cons (.cons _ _) v, s) =>
      (evalFuel f (v :: env.tail) (.loop b)).map fun x => (x.1, s + x.2 + 1)
    | none => none

/-- The fuel evaluator is sound for the semantics. -/
theorem evalFuel_sound : ∀ (f : ℕ) (env : Env) (p : Prog) (r : Data) (t : ℕ),
    evalFuel f env p = some (r, t) → Eval env p r t := by
  intro f
  induction f with
  | zero => intro env p r t h; simp [evalFuel] at h
  | succ f ih =>
    intro env p r t h
    cases p with
    | var i =>
      simp only [evalFuel, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .var env i
    | nil =>
      simp only [evalFuel, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .nil env
    | cons h₁ t₁ =>
      simp only [evalFuel] at h
      rcases hh : evalFuel f env h₁ with _ | ⟨a, s⟩ <;>
        rcases ht : evalFuel f env t₁ with _ | ⟨b, u⟩ <;>
        simp only [hh, ht, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .cons (ih _ _ _ _ hh) (ih _ _ _ _ ht)
    | elim i n c =>
      simp only [evalFuel] at h
      rcases hg : env.get i with _ | ⟨a, b⟩ <;> simp only [hg] at h
      · rcases hn : evalFuel f env n with _ | ⟨r', t'⟩ <;>
          simp only [hn, Option.map_some, Option.map_none, Option.some.injEq,
            Prod.mk.injEq, reduceCtorEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .elim_nil hg (ih _ _ _ _ hn)
      · rcases hc : evalFuel f (a :: b :: env) c with _ | ⟨r', t'⟩ <;>
          simp only [hc, Option.map_some, Option.map_none, Option.some.injEq,
            Prod.mk.injEq, reduceCtorEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .elim_cons hg (ih _ _ _ _ hc)
    | let_ e b =>
      simp only [evalFuel] at h
      rcases he : evalFuel f env e with _ | ⟨v, s⟩ <;> simp only [he, reduceCtorEq] at h
      rcases hb : evalFuel f (v :: env) b with _ | ⟨r', t'⟩ <;>
        simp only [hb, Option.map_some, Option.map_none, Option.some.injEq,
          Prod.mk.injEq, reduceCtorEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .let_ (ih _ _ _ _ he) (ih _ _ _ _ hb)
    | loop b =>
      simp only [evalFuel] at h
      rcases hb : evalFuel f env b with _ | ⟨w, s⟩ <;> simp only [hb, reduceCtorEq] at h
      rcases w with _ | ⟨_ | ⟨x, y⟩, v⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .loop_nil (ih _ _ _ _ hb)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .loop_stop (ih _ _ _ _ hb)
      · rcases hl : evalFuel f (v :: env.tail) (.loop b) with _ | ⟨r', t'⟩ <;>
          simp only [hl, Option.map_some, Option.map_none, Option.some.injEq,
            Prod.mk.injEq, reduceCtorEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .loop_step (ih _ _ _ _ hb) (ih _ _ _ _ hl)

/-- `p` halts on input `x` (run in the environment `[x]`). -/
def Halts (p : Prog) (x : Data) : Prop := ∃ r t, Eval [x] p r t

/-- `p` halts on `x` within cost `t`. -/
def HaltsWithin (p : Prog) (x : Data) (t : ℕ) : Prop := ∃ r t', t' ≤ t ∧ Eval [x] p r t'

/-- A (total) time bound for `p` as a function of the input size. This is the notion
`TIME_𝒮, TIME_𝒟 ≤ ⋯` of blueprint `def:lambda-bounded` specializes. -/
def TimeBound (p : Prog) (T : ℕ → ℕ) : Prop := ∀ x : Data, HaltsWithin p x (T x.size)

end MIPRE.Cost
