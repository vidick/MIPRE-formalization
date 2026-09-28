/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Cost.Kleene
public import MIPRE.Foundations.Cost.Binary
public import MIPRE.Foundations.Cost.BinaryArithmetic
public import MIPRE.Foundations.Cost.BinaryCompare
public import MIPRE.Foundations.Cost.Reader
public import MIPRE.Foundations.Cost.SizeProgram
public import MIPRE.Foundations.Cost.Threshold
public import MIPRE.Foundations.Halting.Arith

@[expose] public section

/-!
# Stages of the class verifier's programs

The sampler and the decider of the class verifier of the polynomial-time halting reduction
(`Halting/Paper/ClassVerifier.lean`) are chains of stages: polynomial-time functions
(`PolyTimeFun`, run by their `code`), calls of the universal machine on a program and an input
the previous stage produced, and one binary-to-unary conversion of the sampler's dimension.
The universal calls and the conversion are not `PolyTimeFun`s — the first is polynomial in the
simulated program's own time, the second in the number it converts — so the chain is assembled
at the level of programs and `Eval`, with forward run lemmas: each stage is a closed program,
`seq p q` runs `p` then `q` on its output, and the cost of the chain is the sum of the stages'
costs plus the sizes of the intermediate values.

* `runUK univ` on `encode ((c, v), s)` runs `univ` on `(c, v)` and returns `encode (s, r)`,
  keeping the state `s`; `runU univ` returns `r` alone.
* `unaryStage` on `encode (s, n)` returns `encode (s, unary n)` (`toUnaryProg`).
* The polynomial-time pieces: `expBits` (`u ↦ 2 ^ |u|`), `addConstU K` (`u ↦ unary (K + |u|)`),
  `unaryMul D` (`u ↦ unary (D · |u|)`), `lenBin` (the length of a string, in binary).
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-! ## Sequencing, and the universal calls -/

/-- Run `p`, then the closed program `q` on its output. -/
def seq (p q : Prog) : Prog := .let_ p (callVar 0 q)

theorem seq_wellScoped {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
    (seq p q).WellScoped 1 :=
  ⟨hp, callVar_wellScoped (by decide) hq⟩

theorem seq_runs {p q : Prog} (hq : q.WellScoped 1) {x y r : Data} {t₁ t₂ : ℕ}
    (hp : p.Runs x y t₁) (hq' : q.Runs y r t₂) :
    (seq p q).Runs x r (t₁ + (y.size + 1 + t₂ + 1) + 1) :=
  Eval.let_ hp (callVar_eval (env := [y, x]) (i := 0) hq (v := y) (by simp) hq')

/-- Run the universal program on the pair in the input's first component, keeping the second:
`encode ((c, v), s) ↦ encode (s, r)` where `c` on `v` returns `r`. -/
def runUK (univ : Prog) : Prog :=
  .elim 0 .nil (.let_ (callVar 0 univ) (.cons (.var 2) (.var 0)))

theorem runUK_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (runUK univ).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, ⟨Nat.zero_lt_succ _, hU.mono (by omega) _⟩,
    show (2 : ℕ) < 1 + 2 + 1 by omega, show (0 : ℕ) < 1 + 2 + 1 by omega⟩

theorem runUK_runs {univ : Prog} (hU : univ.WellScoped 1) {A B r : Data} {t : ℕ}
    (h : univ.Runs A r t) :
    ∃ t' ≤ A.size + B.size + r.size + t + 8, (runUK univ).Runs (.cons A B) (.cons B r) t' := by
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons A B]) (i := 0) (n := .nil) (by simp)
    (Eval.let_ (callVar_eval (env := [A, B, .cons A B]) (i := 0) hU (v := A) (by simp) h)
      (Eval.cons (Eval.var_of_get (env := [r, A, B, .cons A B]) (i := 2) (v := B) (by simp))
        (Eval.var_of_get (env := [r, A, B, .cons A B]) (i := 0) (v := r) (by simp))))⟩
  omega

/-- Run the universal program on the pair in the input's first component, dropping the
second: `encode ((c, v), s) ↦ r`. -/
def runU (univ : Prog) : Prog := .elim 0 .nil (callVar 0 univ)

theorem runU_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (runU univ).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, Nat.zero_lt_succ _, hU.mono (by omega) _⟩

theorem runU_runs {univ : Prog} (hU : univ.WellScoped 1) {A B r : Data} {t : ℕ}
    (h : univ.Runs A r t) :
    ∃ t' ≤ A.size + t + 3, (runU univ).Runs (.cons A B) r t' := by
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons A B]) (i := 0) (n := .nil) (by simp)
    (callVar_eval (env := [A, B, .cons A B]) (i := 0) hU (v := A) (by simp) h)⟩
  omega

/-- Convert the second component from binary to unary: `encode (s, n) ↦ encode (s, unary n)`. -/
def unaryStage : Prog := .elim 0 .nil (.cons (.var 0) (callVar 1 toUnaryProg))

theorem unaryStage_wellScoped : unaryStage.WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, Nat.zero_lt_succ _, show (1 : ℕ) < 1 + 2 by omega,
    toUnaryProg_wellScoped.mono (by omega) _⟩

theorem unaryStage_runs (S : Data) (n : ℕ) :
    ∃ t ≤ S.size + esize n +
        (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90) + 5,
      unaryStage.Runs (.cons S (encode n)) (.cons S (Data.ofNat n)) t := by
  obtain ⟨t, ht, h⟩ := toUnaryProg_runs n
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons S (encode n)]) (i := 0) (n := .nil) (by simp)
    (Eval.cons (Eval.var_of_get (env := [S, encode n, .cons S (encode n)]) (i := 0) (v := S)
        (by simp))
      (callVar_eval (env := [S, encode n, .cons S (encode n)]) (i := 1)
        toUnaryProg_wellScoped (v := encode n) (by simp) h))⟩
  have : (encode n : Data).size = esize n := rfl
  omega

end Prog

/-! ## Polynomial-time pieces -/

namespace PolyTimeFun

/-- `u ↦ 2 ^ |u|` on unary numerals, by `expBitsProg`. -/
noncomputable def expBits : PolyTimeFun Unary ℕ where
  toFun u := 2 ^ u.length
  code := Prog.expBitsProg
  closed := Prog.expBitsProg_wellScoped
  timeBound := (X + 2) * (C 4 * X + 20)
  computes u := by
    obtain ⟨n, rfl⟩ : ∃ n, u = unary n := ⟨u.length, (unary_length u).symm⟩
    obtain ⟨t, ht, h⟩ := Prog.expBitsProg_runs n
    simp only [length_unary]
    refine ⟨t, ?_, ?_⟩
    · have e : esize (unary n) = 2 * n + 1 := by
        show (encode (unary n) : Data).size = _
        rw [encode_unary, Data.size_ofNat]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_ofNat, e]
      nlinarith
    · show Prog.expBitsProg.Runs (encode (unary n)) _ t
      rw [encode_unary]
      exact h

@[simp] theorem expBits_apply (u : Unary) : expBits u = 2 ^ u.length := rfl

/-- `u ↦ unary (K + |u|)`, by `addConstProg`. -/
noncomputable def addConstU (K : ℕ) : PolyTimeFun Unary Unary where
  toFun u := unary (K + u.length)
  code := Prog.addConstProg K
  closed := Prog.addConstProg_wellScoped K
  timeBound := C ((K + 1) * (4 * K + 15) + 2 * K + 5) + C (K + 2) * X
  computes u := by
    obtain ⟨n, rfl⟩ : ∃ n, u = unary n := ⟨u.length, (unary_length u).symm⟩
    obtain ⟨t, ht, h⟩ := Prog.addConstProg_runs K n
    simp only [length_unary]
    refine ⟨t, ?_, ?_⟩
    · have e : esize (unary n) = 2 * n + 1 := by
        show (encode (unary n) : Data).size = _
        rw [encode_unary, Data.size_ofNat]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        e]
      nlinarith
    · show (Prog.addConstProg K).Runs (encode (unary n)) (encode (unary (K + n))) t
      rw [encode_unary, encode_unary]
      exact h

@[simp] theorem addConstU_apply (K : ℕ) (u : Unary) : addConstU K u = unary (K + u.length) :=
  rfl

/-- `u ↦ unary (D · |u|)`: `D` copies of `u`, appended. -/
noncomputable def unaryMul : ℕ → PolyTimeFun Unary Unary
  | 0 => const []
  | D + 1 => append.comp (pair (id Unary) (unaryMul D))

theorem unaryMul_apply (D : ℕ) (u : Unary) : unaryMul D u = unary (D * u.length) := by
  obtain ⟨n, rfl⟩ : ∃ n, u = unary n := ⟨u.length, (unary_length u).symm⟩
  rw [length_unary]
  induction D with
  | zero => simp [unaryMul, unary]
  | succ D ih =>
    show (id Unary (unary n) ++ unaryMul D (unary n)) = _
    rw [ih, id_apply, Nat.succ_mul, Nat.add_comm]
    simp only [unary, List.replicate_add]

/-- The length of a string, in binary. -/
noncomputable def lenBin {α : Type*} [SizedEncoding α] : PolyTimeFun (List α) ℕ :=
  unaryToBin.comp length

@[simp] theorem lenBin_apply {α : Type*} [SizedEncoding α] (l : List α) :
    lenBin l = l.length := by
  show (length l).length = _
  rw [length_apply, length_unary]

end PolyTimeFun

end MIPRE.Cost

end
