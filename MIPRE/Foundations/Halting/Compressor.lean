/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Reduction
import MIPRE.Foundations.Halting.Serial

/-!
# The compressor's decider: the program

Obligation O4 of blueprint `rem:compression-abstract`, the program half. The compressor of the
halting reduction takes a succinct description `(c, n)` of a string `x` and returns a string
denoting the compressed verifier of *the verifier of `x` frozen at index `2n + 1`*: its
parameter is `λ(n)`, and its decider — the datum a string carries — is the program `haltProg`
below with `(c, n, λ(n))` hardcoded. This module is that program and its acceptance
agreement, `CompressorSpec.accepts_compr`; the accounting is separate.

The decider is the paper's machine `𝓕` (`recursive.tex`, `fig:halt_f`) with the recursion
removed: the paper's `𝓕` hardcodes its own description and compresses the verifier it is the
decider of, while here the string to compress is *read* from the description `c` by bit
queries — the reading is what the compressibility criterion's succinct descriptions make
possible — and the verifier compressed is the string's own, frozen. The paper's Step 2, running
`𝓜` for `n` steps, is the criterion's business and does not appear.

The program `prepProg G U` does everything but the last step, and always halts on a succinct
description:

1. `readProg U.univ`: read `x` from `c` by bit queries `0, 1, 2, …` through the universal
   machine, stopping at the out-of-range marker of `bitQueryAnswer`;
2. `parseProg`, then the two projections and `normBinProg`: the parameter `encode (descLam x)`
   and the decider datum `descDecD x`;
3. `G.samplerProg.code`: the encoded sampler program `sampData G x`;
4. `wrapBuildProg U.univ`: the encoded wrapped decider `decProgData G U x`, which is
   `encode (Vof G U x).decider.prog`;
5. `freezeBuildProg` twice at index `2n + 1`: the encoded programs of the frozen verifier;
6. `G.compress.code` on `((frozen sampler, frozen decider), λ(n))`: the encoded compressed
   decider.

Then `haltProg G U` runs it through the universal machine on the decider's own input, and
returns what the universal machine does. Forward runs of each stage compose to a forward run
of `haltProg`; the inversion (`haltProg_runs_inv`) is three `cases` and determinism, the
preparation being a single closed program with an unconditional run, and gives the acceptance
agreement `haltProg_accepts_iff`.

Every stage carries an explicit cost, in the sizes of what it is handed, so that the accounting
can be done from these lemmas alone.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

open Data

/-! ## Reading a string from its succinct description

`readProg univ` on `encode c`: loop over `i = 0, 1, 2, …`, running `univ` on
`cons (encode c) (encode i)`, until the answer is the out-of-range marker `ofNat 2`; the bits
answered are accumulated in reverse and reversed at the end. On a succinct description of `x`
the answers are `bitQueryAnswer x i`, so the result is `encode x`.

The loop state is `cons cD (cons iD acc)`: the description, the index in binary, and the bits
read so far, most recent first. -/

/-- The body of the reading loop. After taking the state apart (`cD` at `2`, `iD` at `0`,
`acc` at `1`), it runs `univ` on `cons cD iD`. The answer `nil` is the bit `false`,
`cons nil nil` the bit `true`, and anything else — the marker `ofNat 2 = cons nil (cons nil nil)`
— stops the loop with the accumulator. On a bit, the index is incremented with `incProg` and the
bit pushed onto the accumulator. -/
def readTail : Prog :=
  .elim 0
    -- answer `nil`: the bit `false`
    (.let_ (callVar 2 incProg)
      (.cons (.cons .nil .nil) (.cons (.var 5) (.cons (.var 0) (.cons .nil (.var 4))))))
    (.elim 1
      -- answer `cons a nil`: the bit `true`
      (.let_ (callVar 4 incProg)
        (.cons (.cons .nil .nil)
          (.cons (.var 7) (.cons (.var 0) (.cons (.cons .nil .nil) (.var 6))))))
      -- anything else: the marker, stop with the accumulator
      (.cons .nil (.var 7)))

def readBody (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 1 .nil
    (.let_ (.cons (.var 2) (.var 0))
      (.let_ (callVar 0 univ) readTail)))

/-- `readProg univ` on `encode c`: the loop from the state `cons (encode c) (cons nil nil)`
— index `0`, nothing read — followed by the reversal of the accumulator. -/
def readProg (univ : Prog) : Prog :=
  .let_ (.cons (.var 0) (.cons .nil .nil)) (.let_ (.loop (readBody univ)) revProg)

theorem readBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (readBody univ).WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩, ?_⟩
  refine ⟨callVar_wellScoped (by decide) hU, ?_⟩
  refine ⟨by decide, ⟨callVar_wellScoped (by decide) incProg_wellScoped, by simp [WellScoped]⟩, ?_⟩
  refine ⟨by decide, ⟨callVar_wellScoped (by decide) incProg_wellScoped, by simp [WellScoped]⟩,
    by simp [WellScoped]⟩

theorem readProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (readProg univ).WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial, trivial⟩,
    ⟨⟨by decide, (readBody_wellScoped hU).mono (by omega) _⟩, revProg_wellScoped.mono (by omega) _⟩⟩

section Read

variable {univ : Prog} (cD : Data)

/-- The state of the reading loop after `i` bits of `x` have been read. -/
def readState (x : BitStr) (i : ℕ) : Data :=
  .cons cD (.cons (encode i) (encode (x.take i).reverse))

/-- The environment after the body has taken the state apart and queried the description. -/
private def readEnv (iD acc ans : Data) : Env :=
  [ans, .cons cD iD, iD, acc, cD, .cons iD acc, .cons cD (.cons iD acc)]

private theorem readBody_pre (hU : univ.WellScoped 1) {iD acc ans : Data} {t : ℕ}
    (h : univ.Runs (.cons cD iD) ans t) {r : Data} {t' : ℕ}
    (hc : Eval (readEnv cD iD acc ans) readTail r t') :
    Eval [.cons cD (.cons iD acc)] (readBody univ) r
      (t' + t + 2 * cD.size + 2 * iD.size + 10) := by
  have e := Eval.elim_cons (env := [Data.cons cD (.cons iD acc)]) (i := 0) (n := .nil)
    (a := cD) (b := .cons iD acc) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := iD) (b := acc) (by simp)
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := cD) (by simp))
          (Eval.var_of_get (i := 0) (v := iD) (by simp)))
        (Eval.let_ (callVar_eval hU (i := 0) (v := .cons cD iD) (by simp) h) hc)))
  refine e.cast_cost ?_
  simp only [Data.size_cons]
  omega

/-- The body on a bit answer: continue with the next index and the bit pushed. -/
theorem readBody_bit (hU : univ.WellScoped 1) {iD acc : Data} {i : ℕ} (hi : iD = encode i) (b : Bool) {t : ℕ}
    (h : univ.Runs (.cons cD iD) (encode b) t) :
    ∃ t' ≤ t + 3 * cD.size + 4 * iD.size + acc.size +
        2 * ((Nat.size i + 2) * (8 * esize i + 8 * Nat.size i + 60)) + 30,
      Eval [.cons cD (.cons iD acc)] (readBody univ)
        (.cons (.cons .nil .nil) (.cons cD (.cons (encode (i + 1)) (.cons (encode b) acc)))) t' := by
  obtain ⟨ti, hti, hinc⟩ := incProg_runs_nat i
  subst hi
  cases b with
  | false =>
    refine ⟨_, ?_, readBody_pre cD hU h (Eval.elim_nil (i := 0) (by simp [readEnv])
      (Eval.let_ (callVar_eval incProg_wellScoped (i := 2) (v := encode i) (by simp [readEnv]) hinc)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 5) (v := cD) (by simp [readEnv]))
            (Eval.cons (Eval.var_of_get (i := 0) (v := encode (i + 1)) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 4) (v := acc) (by simp [readEnv]))))))))⟩
    have hei : esize i = (encode i : Data).size := rfl
    have : (encode (i + 1) : Data).size ≤ ti := hinc.size_le
    omega
  | true =>
    refine ⟨_, ?_, readBody_pre cD hU h (Eval.elim_cons (i := 0) (a := .nil) (b := .nil)
        (by simp [readEnv])
      (Eval.elim_nil (i := 1) (by simp [readEnv])
        (Eval.let_ (callVar_eval incProg_wellScoped (i := 4) (v := encode i) (by simp [readEnv]) hinc)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 7) (v := cD) (by simp [readEnv]))
              (Eval.cons (Eval.var_of_get (i := 0) (v := encode (i + 1)) (by simp))
                (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                  (Eval.var_of_get (i := 6) (v := acc) (by simp [readEnv])))))))))⟩
    have hei : esize i = (encode i : Data).size := rfl
    have : (encode (i + 1) : Data).size ≤ ti := hinc.size_le
    omega

/-- The body on the marker: stop with the accumulator. -/
theorem readBody_stop (hU : univ.WellScoped 1) {iD acc : Data} {t : ℕ} (h : univ.Runs (.cons cD iD) (Data.ofNat 2) t) :
    Eval [.cons cD (.cons iD acc)] (readBody univ) (.cons .nil acc)
      (t + 2 * cD.size + 2 * iD.size + acc.size + 15) :=
  (readBody_pre cD hU h (Eval.elim_cons (i := 0) (a := .nil) (b := Data.ofNat 1)
      (by simp [readEnv, Data.ofNat])
    (Eval.elim_cons (i := 1) (a := .nil) (b := .nil) (by simp [readEnv, Data.ofNat])
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 7) (v := acc) (by simp [readEnv])))))).cast_cost
    (by omega)

end Read

/-- The cost of one iteration of the reading loop on a succinct description at parameter `n`
of a string of length at most `L`, with the description of size `s`: the universal machine's
overhead on a bit query, plus the bookkeeping. -/
noncomputable def readIter (U : UniversalMachine) (s n L : ℕ) : ℕ :=
  U.bound.eval (s + (4 * Nat.size L + 1) + (n + 1) * (Nat.size L + 1) ^ 2) +
    3 * s + 4 * (4 * Nat.size L + 1) + (4 * L + 1) +
    2 * ((Nat.size L + 2) * (8 * (4 * Nat.size L + 1) + 8 * Nat.size L + 60)) + 30

/-- **The reading loop reads the string.** On a succinct description `(c, n)` of `x`, from the
initial state, the loop of `readBody U.univ` stops with `encode x.reverse`. -/
theorem readLoop_runs (U : UniversalMachine) {c : Prog} {n : ℕ} {x : BitStr}
    (hsd : IsSuccinctDesc c n x) (env : Env) :
    ∃ t ≤ (x.length + 1) * (readIter U (esize c) n x.length + 1),
      Eval (readState (encode c) x 0 :: env) (.loop (readBody U.univ)) (encode x.reverse) t := by
  -- the bit queries, through the universal machine, within the iteration budget
  have hquery : ∀ i, i ≤ x.length → ∃ t ≤ U.bound.eval (esize c + (4 * Nat.size x.length + 1) +
      (n + 1) * (Nat.size x.length + 1) ^ 2),
      U.univ.Runs (.cons (encode c) (encode i)) (bitQueryAnswer x i) t := by
    intro i hi
    obtain ⟨t, ht, hrun⟩ := hsd.2.2 i
    obtain ⟨t', ht', hrun'⟩ := U.time_le c _ _ t hrun
    refine ⟨t', ht'.trans (polynomial_eval_mono U.bound ?_), hrun'⟩
    have h1 : (encode i : Data).size ≤ 4 * Nat.size i + 1 := esize_nat_le i
    have h2 : Nat.size i ≤ Nat.size x.length := Nat.size_le_size hi
    have h3 : (n + 1) * (Nat.size i + 1) ^ 2 ≤ (n + 1) * (Nat.size x.length + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    omega
  have hacc : ∀ i, (encode (x.take i).reverse : Data).size ≤ 4 * x.length + 1 := fun i =>
    (esize_bitStr_le _).trans (by simp only [List.length_reverse, List.length_take]; omega)
  suffices key : ∀ s, (∃ i, i ≤ x.length ∧ s = readState (encode c) x i) →
      ∃ r t, t ≤ (x.length - Data.natOf s.right.left + 1) * (readIter U (esize c) n x.length + 1) ∧
        r = encode x.reverse ∧ Eval (s :: env) (.loop (readBody U.univ)) r t by
    obtain ⟨r, t, ht, rfl, hrun⟩ := key (readState (encode c) x 0) ⟨0, by omega, rfl⟩
    refine ⟨t, ?_, hrun⟩
    simpa [readState, Data.right, Data.left] using ht
  refine Eval.loop_of_invariant (readBody_wellScoped U.closed) env
    (fun s => ∃ i, i ≤ x.length ∧ s = readState (encode c) x i)
    (fun s => x.length - Data.natOf s.right.left)
    (fun r => r = encode x.reverse) (readIter U (esize c) n x.length) ?_
  rintro s ⟨i, hi, rfl⟩
  obtain ⟨t, ht, hrun⟩ := hquery i hi
  have hiD : (encode i : Data).size ≤ 4 * Nat.size x.length + 1 :=
    (esize_nat_le i).trans (by have := Nat.size_le_size hi; omega)
  rcases Nat.lt_or_ge i x.length with hlt | hge
  · -- a bit: continue
    right
    have hans : bitQueryAnswer x i = encode (x.get ⟨i, hlt⟩) := by simp [bitQueryAnswer, hlt]
    rw [hans] at hrun
    obtain ⟨t', ht', hrun'⟩ := readBody_bit (encode c) U.closed (acc := encode (x.take i).reverse)
      rfl (x.get ⟨i, hlt⟩) hrun
    have hst : (encode (x.take (i + 1)).reverse : Data) =
        .cons (encode (x.get ⟨i, hlt⟩)) (encode (x.take i).reverse) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.reverse_append,
        List.reverse_singleton, List.singleton_append, encode_bitStr_cons]
      rfl
    refine ⟨.nil, .nil, readState (encode c) x (i + 1), t', ?_, ?_, ⟨i + 1, hlt, rfl⟩, ?_⟩
    · refine ht'.trans ?_
      unfold readIter
      have h1 : esize i ≤ 4 * Nat.size i + 1 := esize_nat_le i
      have h2 : Nat.size i ≤ Nat.size x.length := Nat.size_le_size hi
      have h3 : (Nat.size i + 2) * (8 * esize i + 8 * Nat.size i + 60) ≤
          (Nat.size x.length + 2) * (8 * (4 * Nat.size x.length + 1) + 8 * Nat.size x.length + 60) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 := hacc i
      have h5 : (encode c : Data).size = esize c := rfl
      omega
    · unfold readState; rw [hst]; exact hrun'
    · simp only [readState, Data.right, Data.left, Data.natOf_encode]
      omega
  · -- the marker: stop
    left
    have hans : bitQueryAnswer x i = Data.ofNat 2 := by simp [bitQueryAnswer, not_lt.2 hge]
    rw [hans] at hrun
    refine ⟨_, _, ?_, readBody_stop (encode c) U.closed hrun, ?_⟩
    · unfold readIter
      have h4 := hacc i
      have h5 : (encode c : Data).size = esize c := rfl
      have h6 : 0 ≤ (Nat.size x.length + 2) *
        (8 * (4 * Nat.size x.length + 1) + 8 * Nat.size x.length + 60) := Nat.zero_le _
      omega
    · have : i = x.length := le_antisymm hi hge
      subst this
      simp

/-- **`readProg` reads the string.** On a succinct description `(c, n)` of `x`, `readProg U.univ`
on `encode c` computes `encode x`. -/
theorem readProg_runs (U : UniversalMachine) {c : Prog} {n : ℕ} {x : BitStr}
    (hsd : IsSuccinctDesc c n x) :
    ∃ t ≤ (x.length + 1) * (readIter U (esize c) n x.length + 1) +
        (x.length + 2) * (4 * x.length + 14) + esize c + 7,
      (readProg U.univ).Runs (encode c) (encode x) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := readLoop_runs U hsd [encode c]
  obtain ⟨t₂, ht₂, h₂⟩ := revProg_runs (x.reverse.map Data.ofBool)
  have hpre : Eval [encode c] (.cons (.var 0) (.cons .nil .nil))
      (readState (encode c) x 0) (esize c + 5) := by
    have := Eval.cons (Eval.var_of_get (env := [encode c]) (i := 0) (v := encode c) (by simp))
      (Eval.cons (Eval.nil [encode c]) (Eval.nil [encode c]))
    exact this.cast_cost (by simp [esize])
  have h₂' : Eval (encode x.reverse :: readState (encode c) x 0 :: [encode c]) revProg
      (encode x) t₂ := by
    have := Eval.append_of_wellScoped h₂ revProg_wellScoped [readState (encode c) x 0, encode c]
    rw [encode_bitStr_eq_list, encode_bitStr_eq_list]
    simpa [List.map_reverse] using this
  refine ⟨_, ?_, Eval.let_ hpre (Eval.let_ h₁ h₂')⟩
  have hlen : (x.reverse.map Data.ofBool).length = x.length := by simp
  have hsz : (Data.list (x.reverse.map Data.ofBool)).size ≤ 4 * x.length + 1 := by
    rw [← encode_bitStr_eq_list]
    exact (esize_bitStr_le _).trans (by simp)
  have hB : t₂ ≤ (x.length + 2) * (4 * x.length + 14) := by
    refine ht₂.trans ?_
    rw [hlen]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Building descriptions of programs

The compressor's decider has to assemble the *descriptions* of the wrapped decider and of the
two frozen programs: `Prog.ProgD.dWrapCore` and `dFreeze` below, at the level of data, with the
sampler program and the string's decider as holes. The programs that build them are the same
trees with `cons`/`const` in place of the constructors — `pK`, `pC`, `pL`, `pE` mirror
`ProgD.dK`, `dC`, `dL`, `dE` — and their cost is the size of what they build plus one per hole
read. -/

namespace ProgD

/-- The description of the frozen program `freezeProg k p`, at the level of data. -/
def dFreeze (kD p : Data) : Data := dL (dE 0 dNil (dC (dK kD) (dV 1))) p

theorem dFreeze_eq (k : ℕ) (p : Prog) :
    dFreeze (encode k) (encode p) = encode (Prog.freezeProg k p) := rfl

/-! The sizes of the constructors' descriptions. -/

theorem size_dV (i : ℕ) : (dV i).size = 2 * i + 3 := by simp [dV]; omega
theorem size_dNil : dNil.size = 5 := by simp [dNil]
theorem size_dK (d : Data) : (dK d).size = d.size + 14 := by simp [dK]; omega
theorem size_dC (a b : Data) : (dC a b).size = a.size + b.size + 7 := by simp [dC]; omega
theorem size_dL (a b : Data) : (dL a b).size = a.size + b.size + 11 := by simp [dL]; omega
theorem size_dE (i : ℕ) (a b : Data) : (dE i a b).size = a.size + b.size + 2 * i + 11 := by
  simp [dE]; omega

theorem size_dFreeze (kD p : Data) : (dFreeze kD p).size = p.size + kD.size + 53 := by
  simp only [dFreeze, size_dL, size_dE, size_dC, size_dK, size_dV, size_dNil]
  omega

/-- The size of the wrapper's description: the two holes, the universal machine twice, and a
fixed number of nodes. -/
def wrapNodes : ℕ :=
  2 * (encode Prog.lenProg : Data).size + 2 * (encode Prog.eqBitsProg : Data).size +
    (encode Prog.toUnaryProg : Data).size + (encode CL.Sampler.Query.dimension : Data).size + 475

theorem size_dWrapCore (univD sampD decD : Data) :
    (dWrapCore univD sampD decD).size = sampD.size + decD.size + 2 * univD.size + wrapNodes := by
  unfold dWrapCore dWrapHead dWrapCheck dWrapTail
  simp only [size_dE, size_dL, size_dC, size_dK, size_dV, size_dNil]
  unfold wrapNodes
  omega

end ProgD

open ProgD

/-- `cons (const 6) e`: builds `dK`. -/
def pK (e : Prog) : Prog := .cons (.const (.ofNat 6)) e
/-- Builds `dC`. -/
def pC (h t : Prog) : Prog := .cons (.const (.ofNat 2)) (.cons h t)
/-- Builds `dL`. -/
def pL (e b : Prog) : Prog := .cons (.const (.ofNat 4)) (.cons e b)
/-- Builds `dE i`. -/
def pE (i : ℕ) (n c : Prog) : Prog :=
  .cons (.const (.ofNat 3)) (.cons (.const (.ofNat i)) (.cons n c))

section Build

variable {env : Env}

theorem pK_eval {e : Prog} {v : Data} {s : ℕ} (h : Eval env e v s) :
    Eval env (pK e) (dK v) (s + 14) :=
  (Eval.cons (Eval.const _ _) h).cast_cost (by simp [Data.size_ofNat]; omega)

theorem pC_eval {h t : Prog} {a b : Data} {s u : ℕ} (h₁ : Eval env h a s) (h₂ : Eval env t b u) :
    Eval env (pC h t) (dC a b) (s + u + 7) :=
  (Eval.cons (Eval.const _ _) (Eval.cons h₁ h₂)).cast_cost (by simp [Data.size_ofNat]; omega)

theorem pL_eval {e b : Prog} {a c : Data} {s u : ℕ} (h₁ : Eval env e a s) (h₂ : Eval env b c u) :
    Eval env (pL e b) (dL a c) (s + u + 11) :=
  (Eval.cons (Eval.const _ _) (Eval.cons h₁ h₂)).cast_cost (by simp [Data.size_ofNat]; omega)

theorem pE_eval (i : ℕ) {n c : Prog} {a b : Data} {s u : ℕ} (h₁ : Eval env n a s)
    (h₂ : Eval env c b u) : Eval env (pE i n c) (dE i a b) (s + u + 2 * i + 11) :=
  (Eval.cons (Eval.const _ _) (Eval.cons (Eval.const _ _) (Eval.cons h₁ h₂))).cast_cost
    (by simp [Data.size_ofNat]; omega)

end Build

theorem pK_wellScoped {n : ℕ} {e : Prog} (h : e.WellScoped n) : (pK e).WellScoped n := ⟨trivial, h⟩
theorem pC_wellScoped {n : ℕ} {h t : Prog} (h₁ : h.WellScoped n) (h₂ : t.WellScoped n) :
    (pC h t).WellScoped n := ⟨trivial, h₁, h₂⟩
theorem pL_wellScoped {n : ℕ} {e b : Prog} (h₁ : e.WellScoped n) (h₂ : b.WellScoped n) :
    (pL e b).WellScoped n := ⟨trivial, h₁, h₂⟩
theorem pE_wellScoped {n i : ℕ} {e b : Prog} (h₁ : e.WellScoped n) (h₂ : b.WellScoped n) :
    (pE i e b).WellScoped n := ⟨trivial, trivial, h₁, h₂⟩

/-- One length check of the wrapper, as a builder with the continuation as a hole. -/
def pCheck (i j : ℕ) (c : Prog) : Prog :=
  pL (.const (dL (dV i) (encode Prog.lenProg)))
    (pL (.const (dC (dV 0) (dV (j + 1))))
      (pL (.const (dL (dV 0) (encode Prog.eqBitsProg))) (pE 0 (.const dNil) c)))

theorem pCheck_eval {env : Env} (i j : ℕ) {c : Prog} {v : Data} {s : ℕ} (h : Eval env c v s) :
    Eval env (pCheck i j c) (dWrapCheck i j v)
      (s + (dL (dV i) (encode Prog.lenProg)).size + (dC (dV 0) (dV (j + 1))).size +
        (dL (dV 0) (encode Prog.eqBitsProg)).size + dNil.size + 44) :=
  (pL_eval (Eval.const _ (dL (dV i) (encode Prog.lenProg)))
    (pL_eval (Eval.const _ (dC (dV 0) (dV (j + 1))))
      (pL_eval (Eval.const _ (dL (dV 0) (encode Prog.eqBitsProg)))
        (pE_eval 0 (Eval.const _ dNil) h)))).cast_cost (by omega)

theorem pCheck_wellScoped {n i j : ℕ} {c : Prog} (h : c.WellScoped n) :
    (pCheck i j c).WellScoped n :=
  pL_wellScoped trivial (pL_wellScoped trivial (pL_wellScoped trivial
    (pE_wellScoped trivial h)))

/-- **The wrapper's description, built.** On `cons sampD decD`, the description
`dWrapCore univD sampD decD` of the wrapped decider. -/
def wrapBuildProg (univD : Data) : Prog :=
  .elim 0 .nil
    (pE 0 (.const dNil)
      (pL (pC (pK (.var 0)) (.const (dC (dV 0) (dK (encode CL.Sampler.Query.dimension)))))
        (pL (.const (dL (dV 0) univD))
          (pL (.const (dL (dV 0) (encode Prog.toUnaryProg)))
            (pE 4 (.const dNil) (pE 1 (.const dNil)
              (pCheck 2 4 (pCheck 5 9
                (pL (pC (pK (.var 1)) (.const (dV 19))) (.const (dL (dV 0) univD)))))))))))

theorem wrapBuildProg_wellScoped (univD : Data) : (wrapBuildProg univD).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, pE_wellScoped trivial (pL_wellScoped
    (pC_wellScoped (pK_wellScoped (by simp [WellScoped])) trivial)
    (pL_wellScoped trivial (pL_wellScoped trivial (pE_wellScoped trivial (pE_wellScoped trivial
      (pCheck_wellScoped (pCheck_wellScoped (pL_wellScoped
        (pC_wellScoped (pK_wellScoped (by simp [WellScoped])) trivial) trivial))))))))⟩

/-- The builder builds the wrapper's description, at a cost linear in the sizes involved. -/
theorem wrapBuildProg_runs (univD sampD decD : Data) :
    ∃ t ≤ sampD.size + decD.size + 2 * univD.size + wrapNodes + 3,
      (wrapBuildProg univD).Runs (.cons sampD decD) (dWrapCore univD sampD decD) t := by
  have run := Eval.elim_cons (env := [Data.cons sampD decD]) (i := 0) (n := .nil)
    (a := sampD) (b := decD) (by simp)
    (pE_eval 0 (Eval.const _ dNil)
      (pL_eval (pC_eval (pK_eval (Eval.var_of_get (i := 0) (v := sampD) (by simp)))
          (Eval.const _ (dC (dV 0) (dK (encode CL.Sampler.Query.dimension)))))
        (pL_eval (Eval.const _ (dL (dV 0) univD))
          (pL_eval (Eval.const _ (dL (dV 0) (encode Prog.toUnaryProg)))
            (pE_eval 4 (Eval.const _ dNil) (pE_eval 1 (Eval.const _ dNil)
              (pCheck_eval 2 4 (pCheck_eval 5 9
                (pL_eval (pC_eval (pK_eval (Eval.var_of_get (i := 1) (v := decD) (by simp)))
                  (Eval.const _ (dV 19))) (Eval.const _ (dL (dV 0) univD)))))))))))
  refine ⟨_, ?_, run⟩
  simp only [size_dL, size_dC, size_dK, size_dV, size_dNil]
  unfold wrapNodes
  omega

/-- **The frozen program's description, built.** On `cons kD p`, the description
`dFreeze kD p`. -/
def freezeBuildProg : Prog :=
  .elim 0 .nil (pL (pE 0 (.const dNil) (pC (pK (.var 0)) (.const (dV 1)))) (.var 1))

theorem freezeBuildProg_wellScoped : freezeBuildProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, pL_wellScoped (pE_wellScoped trivial
    (pC_wellScoped (pK_wellScoped (by simp [WellScoped])) trivial)) (by simp [WellScoped])⟩

theorem freezeBuildProg_runs (kD p : Data) :
    ∃ t ≤ p.size + kD.size + 56, freezeBuildProg.Runs (.cons kD p) (dFreeze kD p) t := by
  have run := Eval.elim_cons (env := [Data.cons kD p]) (i := 0) (n := .nil) (a := kD) (b := p)
    (by simp)
    (pL_eval (pE_eval 0 (Eval.const _ dNil)
      (pC_eval (pK_eval (Eval.var_of_get (i := 0) (v := kD) (by simp))) (Eval.const _ (dV 1))))
      (Eval.var_of_get (i := 1) (v := p) (by simp)))
  refine ⟨_, ?_, run⟩
  simp only [size_dV, size_dNil]
  omega

/-! ## Small pieces -/

/-- The left projection on any datum (`nil` on `nil`). -/
theorem fstProg_runs' (d : Data) : ∃ t ≤ d.left.size + 2, fstProg.Runs d d.left t := by
  cases d with
  | nil => exact ⟨2, by simp [Data.left], Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
  | cons a b => exact ⟨_, le_rfl, fstProg_runs a b⟩

/-- The right projection on any datum (`nil` on `nil`). -/
theorem sndProg_runs' (d : Data) : ∃ t ≤ d.right.size + 2, sndProg.Runs d d.right t := by
  cases d with
  | nil => exact ⟨2, by simp [Data.right], Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
  | cons a b => exact ⟨_, le_rfl, sndProg_runs a b⟩

/-- A pair of two variables, then a closed program on it. -/
def call2 (i j : ℕ) (q : Prog) : Prog := .let_ (.cons (.var i) (.var j)) q

theorem call2_wellScoped {n i j : ℕ} (hi : i < n) (hj : j < n) {q : Prog} (hq : q.WellScoped 1) :
    (call2 i j q).WellScoped n :=
  ⟨⟨hi, hj⟩, hq.mono (by omega) _⟩

theorem call2_eval {env : Env} {i j : ℕ} {q : Prog} (hq : q.WellScoped 1) {a b r : Data}
    {t : ℕ} (ha : env.get i = a) (hb : env.get j = b) (h : Eval [.cons a b] q r t) :
    Eval env (call2 i j q) r (a.size + b.size + t + 4) :=
  (Eval.let_ (Eval.cons (Eval.var_of_get ha) (Eval.var_of_get hb))
    (Eval.append_of_wellScoped h hq env)).cast_cost (by omega)

end Cost.Prog

namespace Halting

open Cost Cost.Prog Cost.Prog.ProgD

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The preparation: from `(c, n, λ)` to the compressed decider's description -/

/-- Everything the compressor's decider does before running the compressed decider: on
`encode (c, n, λ)`, the description of `Compress` applied to the verifier of the string `c`
describes, frozen at `2n + 1`, and to `λ`. The stages are those of the module docstring; the
comments give the environment after each. -/
def prepProg : Prog :=
  .elim 0 .nil (.elim 1 .nil                      -- [nD, lamD, cD, cons nD lamD, input]
    (.let_ (callVar 2 (readProg U.univ))          -- [xD, nD, lamD, cD, …]
      (.let_ (callVar 0 parseProg)                -- [pD, xD, nD, lamD, cD, …]
        (.let_ (callVar 0 sndProg)                -- [decD, pD, xD, nD, lamD, cD, …]
          (.let_ (callVar 1 fstProg)              -- [lamDx, decD, pD, xD, nD, lamD, cD, …]
            (.let_ (callVar 0 normBinProg)        -- [nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
              (.let_ (callVar 0 G.samplerProg.code)
                                                  -- [sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                (.let_ (call2 0 3 (wrapBuildProg (encode U.univ)))
                                                  -- [wD, sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                  (.let_ (.cons (.cons .nil .nil) (.var 7))
                                                  -- [kD, wD, sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                    (.let_ (call2 0 2 freezeBuildProg)
                                                  -- [fsD, kD, wD, sampD, …]
                      (.let_ (call2 1 2 freezeBuildProg)
                                                  -- [fdD, fsD, kD, wD, sampD, nlam, lamDx, decD, pD, xD, nD, lamD, cD, …]
                        (.let_ (.cons (.cons (.var 1) (.var 0)) (.var 11))
                          (callVar 0 G.compress.code)))))))))))))

theorem prepProg_wellScoped : (prepProg G U).WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, trivial, ?_⟩
  refine ⟨callVar_wellScoped (by decide) (readProg_wellScoped U.closed), ?_⟩
  refine ⟨callVar_wellScoped (by decide) parseProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) sndProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) fstProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) normBinProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) G.samplerProg.closed, ?_⟩
  refine ⟨call2_wellScoped (by decide) (by decide) (wrapBuildProg_wellScoped _), ?_⟩
  refine ⟨⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩, ?_⟩
  refine ⟨call2_wellScoped (by decide) (by decide) freezeBuildProg_wellScoped, ?_⟩
  refine ⟨call2_wellScoped (by decide) (by decide) freezeBuildProg_wellScoped, ?_⟩
  refine ⟨by simp [WellScoped], ?_⟩
  exact callVar_wellScoped (by decide) G.compress.closed

/-- The frozen verifier of the string `x`, at index `2n + 1`. -/
abbrev frozen (x : BitStr) (n : ℕ) : Verifier 7 := (Vof G U x).freeze (2 * n + 1)

/-- The description of the compressed decider the preparation produces. -/
def compressedD (x : BitStr) (n lam : ℕ) : Data :=
  encode (G.compress (((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog), lam))

/-- The values of the stages, named. `sampD` is `sampData G x`, `wD` is `decProgData G U x`
and `kD n` is `encode (2n + 1)` (`Cost.encode_two_mul_add_one`); they are `abbrev`s so that
the environment bookkeeping below sees through them. -/
abbrev sampD (x : BitStr) : Data := encode (G.samplerProg (descLam x))
abbrev wD (x : BitStr) : Data := dWrapCore (encode U.univ) (sampD G x) (Data.parse x).right
abbrev kD (n : ℕ) : Data := .cons (.cons .nil .nil) (encode n)

theorem encode_frozen_sampler (x : BitStr) (n : ℕ) :
    (encode (frozen G U x n).sampler.prog : Data) = dFreeze (kD n) (sampD G x) := by
  show encode (Prog.freezeProg (2 * n + 1) (G.sampler (descLam x)).prog) = _
  rw [← dFreeze_eq, Cost.encode_two_mul_add_one, ← G.samplerProg_eq]

theorem encode_frozen_decider (x : BitStr) (n : ℕ) :
    (encode (frozen G U x n).decider.prog : Data) = dFreeze (kD n) (wD G U x) := by
  show encode (Prog.freezeProg (2 * n + 1) (Vof G U x).decider.prog) = _
  rw [← dFreeze_eq, Cost.encode_two_mul_add_one, ← decProgData_eq]
  rfl

/-! The sizes of the stages' values, bounded in the length `L` of the described string and the
level `n`: the sampler program (`sampBound`, by its own time bound at a parameter of size at
most `L + 1`), the wrapped decider (`wBound`), the frozen index (`kBound`) and the two frozen
programs together (`fBound`). -/

/-- The size of the sampler program at a parameter of size at most `L + 1`. -/
noncomputable def sampBound (L : ℕ) : ℕ := G.samplerProg.timeBound.eval (L + 1)
/-- The size of the wrapped decider's description. -/
noncomputable def wBound (L : ℕ) : ℕ := sampBound G L + (L + 1) + 2 * esize U.univ + wrapNodes
/-- The size of `encode (2n + 1)`. -/
def kBound (n : ℕ) : ℕ := 4 * Nat.size n + 5
/-- The sizes of the two frozen programs, summed. -/
noncomputable def fBound (L n : ℕ) : ℕ :=
  sampBound G L + kBound n + 53 + (wBound G U L + kBound n + 53)

/-- The cost of the preparation, in the description's size `s`, the level `n`, a bound `L` on
the described string's length, and the size `l` of the parameter. -/
noncomputable def prepBound (s n L l : ℕ) : ℕ :=
  (L + 1) * (readIter U s n L + 1) + (L + 2) * (4 * L + 14) + s + 7 +      -- reading
    (L + 2) * (4 * L + 1 + 2 * L + 25) + (4 * L + 1) +                     -- parsing
    (L + 3) * (L + 26) + 3 * (L + 1) + 10 +                                -- normalization
    sampBound G L + wBound G U L + fBound G U L n +
      G.compress.timeBound.eval (fBound G U L n + l + 2) +                  -- the three programs
    2 * s + 4 * (4 * L + 1) + 12 * (L + 1) + 2 * sampBound G L + 3 * wBound G U L +
      6 * kBound n + 2 * fBound G U L n + 2 * l + 200

/-- **The preparation computes the compressed decider's description**, on a succinct
description `(c, n)` of `x`. -/
theorem prepProg_runs {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ) :
    ∃ t ≤ prepBound G U (esize c) n x.length (esize lam),
      (prepProg G U).Runs (encode (c, n, lam)) (compressedD G U x n lam) t := by
  -- the runs of the stages
  obtain ⟨t₁, ht₁, h₁⟩ := readProg_runs U hsd
  obtain ⟨t₂, ht₂, h₂⟩ := parseProg_runs x
  obtain ⟨t₃, ht₃, h₃⟩ := sndProg_runs' (Data.parse x)
  obtain ⟨t₄, ht₄, h₄⟩ := fstProg_runs' (Data.parse x)
  obtain ⟨t₅, ht₅, h₅⟩ := normBinProg_runs (Data.parse x).left
  obtain ⟨t₆, ht₆, h₆⟩ := G.samplerProg.computes (descLam x)
  obtain ⟨t₇, ht₇, h₇⟩ := wrapBuildProg_runs (encode U.univ) (sampD G x) (Data.parse x).right
  obtain ⟨t₈, ht₈, h₈⟩ := freezeBuildProg_runs (kD n) (sampD G x)
  obtain ⟨t₉, ht₉, h₉⟩ := freezeBuildProg_runs (kD n) (wD G U x)
  obtain ⟨t₁₀, ht₁₀, h₁₀⟩ := G.compress.computes
    (((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog), lam)
  -- the inputs of the sampler program and of `Compress`, as the stages before them produce them
  have h₆' : G.samplerProg.code.Runs (Data.normBin (Data.parse x).left) (sampD G x) t₆ := by
    rw [← Data.encode_natOf]; exact h₆
  have h₁₀' : G.compress.code.Runs
      (.cons (.cons (dFreeze (kD n) (sampD G x)) (dFreeze (kD n) (wD G U x))) (encode lam))
      (compressedD G U x n lam) t₁₀ := by
    rw [← encode_frozen_sampler, ← encode_frozen_decider]; exact h₁₀
  -- the run
  have run : Eval [encode (c, n, lam)] (prepProg G U) (compressedD G U x n lam) _ :=
    Eval.elim_cons (env := [encode (c, n, lam)]) (i := 0) (a := encode c)
      (b := .cons (encode n) (encode lam)) (by simp; rfl)
      (Eval.elim_cons (i := 1) (a := encode n) (b := encode lam) (by simp)
        (Eval.let_ (callVar_eval (readProg_wellScoped U.closed) (i := 2) (v := encode c) (by simp) h₁)
          (Eval.let_ (callVar_eval parseProg_wellScoped (i := 0) (v := encode x) (by simp) h₂)
            (Eval.let_ (callVar_eval sndProg_wellScoped (i := 0) (v := Data.parse x) (by simp) h₃)
              (Eval.let_ (callVar_eval fstProg_wellScoped (i := 1) (v := Data.parse x) (by simp) h₄)
                (Eval.let_ (callVar_eval normBinProg_wellScoped (i := 0) (v := (Data.parse x).left)
                    (by simp) h₅)
                  (Eval.let_ (callVar_eval G.samplerProg.closed (i := 0)
                      (v := Data.normBin (Data.parse x).left) (by simp) h₆')
                    (Eval.let_ (call2_eval (wrapBuildProg_wellScoped _) (i := 0) (j := 3)
                        (a := sampD G x) (b := (Data.parse x).right) (by simp) (by simp) h₇)
                      (Eval.let_ (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                          (Eval.var_of_get (i := 7) (v := encode n) (by simp)))
                        (Eval.let_ (call2_eval freezeBuildProg_wellScoped (i := 0) (j := 2)
                            (a := kD n) (b := sampD G x) (by simp) (by simp) h₈)
                          (Eval.let_ (call2_eval freezeBuildProg_wellScoped (i := 1) (j := 2)
                              (a := kD n) (b := wD G U x) (by simp) (by simp) h₉)
                            (Eval.let_ (Eval.cons (Eval.cons
                                (Eval.var_of_get (i := 1) (v := dFreeze (kD n) (sampD G x)) (by simp))
                                (Eval.var_of_get (i := 0) (v := dFreeze (kD n) (wD G U x)) (by simp)))
                                (Eval.var_of_get (i := 11) (v := encode lam) (by simp)))
                              (callVar_eval G.compress.closed (i := 0)
                                (v := .cons (.cons (dFreeze (kD n) (sampD G x))
                                  (dFreeze (kD n) (wD G U x))) (encode lam))
                                (by simp) h₁₀')))))))))))))
  refine ⟨_, ?_, run⟩
  -- the sizes of the intermediate values
  have hs : (encode c : Data).size = esize c := rfl
  have hx : (encode x : Data).size ≤ 4 * x.length + 1 := esize_bitStr_le x
  have hp : (Data.parse x).size ≤ x.length + 1 :=
    (Data.size_parse_le x).trans (by omega)
  have hpl : (Data.parse x).left.size ≤ (Data.parse x).size := Machine.size_left_le _
  have hpr : (Data.parse x).right.size ≤ (Data.parse x).size := Machine.size_right_le _
  have hspine : (Data.parse x).left.spine ≤ (Data.parse x).left.size := Data.spine_le_size _
  have hnb : (Data.parse x).left.normBin.size ≤ (Data.parse x).left.size := Data.size_normBin_le _
  have hdl : esize (descLam x) = (Data.parse x).left.normBin.size := by
    show (encode (Data.natOf (Data.parse x).left) : Data).size = _
    rw [Data.encode_natOf]
  have ht₆' : t₆ ≤ sampBound G x.length :=
    ht₆.trans (polynomial_eval_mono _ (by rw [hdl]; omega))
  have hsamp : (sampD G x).size ≤ sampBound G x.length :=
    (G.samplerProg.esize_apply_le (descLam x)).trans (polynomial_eval_mono _ (by rw [hdl]; omega))
  have hu : (encode U.univ : Data).size = esize U.univ := rfl
  have hw : (wD G U x).size ≤ wBound G U x.length := by
    rw [wD, size_dWrapCore, hu, wBound]; omega
  have hn : (encode n : Data).size ≤ 4 * Nat.size n + 1 := esize_nat_le n
  have hk : (kD n).size = (encode n : Data).size + 4 := by
    show (Data.cons (Data.cons .nil .nil) (encode n)).size = _
    simp only [Data.size_cons, Data.size_nil]; omega
  have hkB : (kD n).size ≤ kBound n := by rw [hk, kBound]; omega
  have hfs := size_dFreeze (kD n) (sampD G x)
  have hfd := size_dFreeze (kD n) (wD G U x)
  have hF : (dFreeze (kD n) (sampD G x)).size + (dFreeze (kD n) (wD G U x)).size ≤
      fBound G U x.length n := by
    rw [hfs, hfd, fBound]; omega
  have harg : (Data.cons (Data.cons (dFreeze (kD n) (sampD G x)) (dFreeze (kD n) (wD G U x)))
      (encode lam)).size = (dFreeze (kD n) (sampD G x)).size + (dFreeze (kD n) (wD G U x)).size +
        (encode lam : Data).size + 2 := by
    simp only [Data.size_cons]; omega
  have hl : (encode lam : Data).size = esize lam := rfl
  have e1 : esize (frozen G U x n).sampler.prog = (dFreeze (kD n) (sampD G x)).size := by
    show (encode _ : Data).size = _
    rw [encode_frozen_sampler]
  have e2 : esize (frozen G U x n).decider.prog = (dFreeze (kD n) (wD G U x)).size := by
    show (encode _ : Data).size = _
    rw [encode_frozen_decider]
  have ht₁₀' : t₁₀ ≤ G.compress.timeBound.eval (fBound G U x.length n + esize lam + 2) := by
    refine ht₁₀.trans (polynomial_eval_mono _ ?_)
    rw [esize_prod, esize_prod, e1, e2]; omega
  -- the stages' costs, in the bounds
  have ht₂' : t₂ ≤ (x.length + 2) * (4 * x.length + 1 + 2 * x.length + 25) :=
    ht₂.trans (Nat.mul_le_mul_left _ (by omega))
  have ht₅' : t₅ ≤ (x.length + 3) * (x.length + 26) + 3 * (x.length + 1) + 10 :=
    ht₅.trans (by
      have : ((Data.parse x).left.spine + 2) * ((Data.parse x).left.size + 25) ≤
          (x.length + 3) * (x.length + 26) := Nat.mul_le_mul (by omega) (by omega)
      omega)
  have hwB : wBound G U x.length =
      sampBound G x.length + (x.length + 1) + 2 * esize U.univ + wrapNodes := rfl
  unfold prepBound
  omega


/-! ## The decider -/

/-- **The compressor's decider**, before hardcoding. On `cons P d` with `P = encode (c, n, λ)`
and `d` the decider's own input `encode (m, x', y', a, b)`: prepare the description of the
compressed decider, and run it on `d` through the universal machine; the result is the
universal machine's. -/
def haltProg : Prog :=
  .elim 0 .nil                                   -- [P, d, input]
    (.let_ (callVar 0 (prepProg G U))            -- [cmpD, P, d, input]
      (.let_ (.cons (.var 0) (.var 2))           -- [cons cmpD d, cmpD, P, d, input]
        (callVar 0 U.univ)))

theorem haltProg_wellScoped : (haltProg G U).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, callVar_wellScoped (by decide) (prepProg_wellScoped G U),
    ⟨⟨by simp [WellScoped], by simp [WellScoped]⟩, callVar_wellScoped (by decide) U.closed⟩⟩

/-- The run of the preparation, as the decider calls it, with the size of what it produces. -/
private theorem prep_call {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ)
    (d : Data) : ∃ t ≤ prepBound G U (esize c) n x.length (esize lam),
      (compressedD G U x n lam).size ≤ t ∧
      Eval [encode (c, n, lam), d, .cons (encode (c, n, lam)) d] (callVar 0 (prepProg G U))
        (compressedD G U x n lam) ((encode (c, n, lam) : Data).size + 1 + t + 1) := by
  obtain ⟨t, ht, h⟩ := prepProg_runs G U hsd lam
  exact ⟨t, ht, h.size_le, callVar_eval (prepProg_wellScoped G U) (i := 0)
    (v := encode (c, n, lam)) (by simp) h⟩

/-- The pairing step of the decider. -/
private theorem pair_step (P d cmpD : Data) :
    Eval [cmpD, P, d, .cons P d] (.cons (.var 0) (.var 2)) (.cons cmpD d)
      (cmpD.size + 1 + (d.size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := cmpD) (by simp))
    (Eval.var_of_get (i := 2) (v := d) (by simp))

/-- **Forward run.** A run of the universal machine on the compressed decider's description and
the input is a run of the decider, at the cost of the preparation and the copies. -/
theorem haltProg_runs {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ)
    {d r : Data} {t : ℕ} (h : U.univ.Runs (.cons (compressedD G U x n lam) d) r t) :
    ∃ t' ≤ 3 * prepBound G U (esize c) n x.length (esize lam) + esize (c, n, lam) +
        2 * d.size + t + 12,
      (haltProg G U).Runs (.cons (encode (c, n, lam)) d) r t' := by
  obtain ⟨tp, htp, hsz, hp⟩ := prep_call G U hsd lam d
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons (encode (c, n, lam)) d]) (i := 0)
    (a := encode (c, n, lam)) (b := d) (by simp)
    (Eval.let_ hp (Eval.let_ (pair_step (encode (c, n, lam)) d (compressedD G U x n lam))
      (callVar_eval U.closed (i := 0) (v := .cons (compressedD G U x n lam) d) (by simp) h)))⟩
  have he : (encode (c, n, lam) : Data).size = esize (c, n, lam) := rfl
  simp only [Data.size_cons]
  omega

/-- **Inversion.** The decider halts only if the universal machine does on the compressed
decider's description and the input, with the same result. -/
theorem haltProg_runs_inv {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ)
    {d r : Data} {t : ℕ} (h : (haltProg G U).Runs (.cons (encode (c, n, lam)) d) r t) :
    ∃ t', U.univ.Runs (.cons (compressedD G U x n lam) d) r t' := by
  obtain ⟨tp, -, -, hp⟩ := prep_call G U hsd lam d
  change Eval [Data.cons (encode (c, n, lam)) d] (.elim 0 .nil _) r t at h
  cases h with
  | elim_nil hn _ => simp at hn
  | @elim_cons _ _ _ _ A B _ _ hcx hA =>
    rw [Env.get_cons_zero] at hcx
    obtain ⟨rfl, rfl⟩ := Data.cons.inj hcx.symm
    cases hA with
    | let_ hB hC =>
      obtain ⟨rfl, -⟩ := hB.deterministic hp
      cases hC with
      | let_ hD hE =>
        obtain ⟨rfl, -⟩ := hD.deterministic (pair_step (encode (c, n, lam)) _ _)
        obtain ⟨t', -, h'⟩ := callVar_runs_rev U.closed hE
        simp only [Env.get_cons_zero] at h'
        exact ⟨t', h'⟩

/-- **Acceptance agreement of the decider.** On a succinct description `(c, n)` of `x`, the
decider with `(c, n, λ)` in front accepts `(m, x', y', a, b)` exactly when the compressed
decider of the verifier of `x` frozen at `2n + 1`, at parameter `λ`, accepts it. -/
theorem haltProg_accepts_iff {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x)
    (lam m : ℕ) (x' y' a b : BitStr) :
    (∃ t, (haltProg G U).Runs (.cons (encode (c, n, lam)) (encode (m, x', y', a, b)))
        (encode true) t) ↔
      (G.output ((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog) lam).decider.Accepts
        m x' y' a b := by
  rw [Decider.Accepts, G.output_decider]
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨t', h'⟩ := haltProg_runs_inv G U hsd lam h
    exact U.halts_of _ _ _ _ h'
  · rintro ⟨t, h⟩
    obtain ⟨t', -, h'⟩ := U.time_le _ _ _ t h
    obtain ⟨t'', -, h''⟩ := haltProg_runs G U hsd lam h'
    exact ⟨t'', h''⟩

/-! ## The compressor's output, as a string -/

/-- **The string the compressor outputs** on `(c, n)` at parameter `λ`: it denotes `λ` and the
decider `haltProg` with `(c, n, λ)` hardcoded. -/
def comprStr (c : Prog) (n lam : ℕ) : BitStr :=
  descOf lam (hardcode (haltProg G U) (encode (c, n, lam)))

@[simp] theorem descLam_comprStr (c : Prog) (n lam : ℕ) : descLam (comprStr G U c n lam) = lam :=
  descLam_descOf _ _

/-- The verifier the output denotes: the compressed sampler at `λ`, and the hardcoded decider
as a program. -/
theorem Vof_comprStr (c : Prog) (n lam : ℕ) :
    Vof G U (comprStr G U c n lam) =
      Verifier.ofSamplerDecider U (G.sampler lam) (hardcode (haltProg G U) (encode (c, n, lam))) := by
  rw [Vof, comprStr, descLam_descOf, descDecD_descOf]
  rfl

/-- **The acceptance agreement of the output** (the field `CompressorSpec.accepts_compr`): on a
succinct description `(c, n)` of `x`, the decider of the verifier the output denotes accepts, at
every index, exactly what the compressed decider of the verifier of `x` frozen at `2n + 1`
accepts. -/
theorem comprStr_accepts {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x)
    (lam m : ℕ) (x' y' a b : BitStr) :
    (Vof G U (comprStr G U c n lam)).decider.Accepts m x' y' a b ↔
      (G.output (((Vof G U x).freeze (2 * n + 1)).sampler.prog,
        ((Vof G U x).freeze (2 * n + 1)).decider.prog) lam).decider.Accepts m x' y' a b := by
  rw [Vof_comprStr, Verifier.ofSamplerDecider_accepts]
  constructor
  · rintro ⟨-, -, t, h⟩
    obtain ⟨t', -, h'⟩ := hardcode_time_rev (haltProg_wellScoped G U) h
    exact (haltProg_accepts_iff G U hsd lam m x' y' a b).1 ⟨t', h'⟩
  · intro h
    have hlen := (G.output _ lam).accepts_length m x' y' a b h
    rw [G.output_sampler] at hlen
    obtain ⟨t, ht⟩ := (haltProg_accepts_iff G U hsd lam m x' y' a b).2 h
    exact ⟨hlen.1, hlen.2, _, hardcode_time (haltProg_wellScoped G U) ht⟩

end Halting

end MIPRE
