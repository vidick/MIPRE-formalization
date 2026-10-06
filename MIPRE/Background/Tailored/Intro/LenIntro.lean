/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Typed
public import MIPRE.Background.Introspection.Compiler
public import MIPRE.Foundations.Introspection.PauliSamplerParamsCost
public import MIPRE.Foundations.Introspection.SourceCompilerParamsCost
public import MIPRE.Foundations.Introspection.ClockCompiler
public import MIPRE.Foundations.Introspection.AuxiliaryReadProgram
public import MIPRE.Tailored.Repeat.Calls

@[expose] public section

/-!
# The answer-length calculator of the introspection verifier

Issue #281 (Phase 3 of `planning/aldous-lyons-track.md`): the answer-length calculator
`L^intro_λ` of the tailored presentation of `Introspection.seven`. It depends on `λ` only, not on
the input verifier: the lengths of the presented game at a question are those of the label its
graph view decodes to (`TypedData.detype`), and the typed lengths (`Typed.lenR`, `Typed.len`) are
functions of the parameters `k = fieldBits c λ n`, `j = selectorBits c λ n` and
`R = (2^n)^λ` alone.

On `(n, x, κ)`, for `λ ≥ 1` and `n ≥ 1`, the program

1. computes the binary pair `(Q, R)` (`SourceCompiler.boundsProg`) and puts it in unary;
2. computes the unary parameters `(k, j, m = 2^j)` (`PauliSamplerParameters.prog`);
3. reads the graph view of `x` (its first `graphDim Label` bits), decodes it to a label by a
   finite table (`finiteFunction`, the router's own device), together with `κ`, into the five
   coefficients of the length as a combination of `k`, `m k`, `Q`, `R` and `1` (`coef`), zero
   when the view does not decode;
4. outputs the combination in unary (`linF`).

At `λ = 0` it is the empty program, and at `n = 0` it inspects the index in place and outputs
`nil`: both output length `0` within constant time, which the budget `Introspection.budget`,
constant in the index there, requires.

* `lenIntroC c λ`, `lenIntroProgC c`: the calculator and its program from `λ`, in polynomial time.
* `lenIntroC_lenIs`: what it outputs on every bit string; `lenIntroC_lenIs_question`: at a detyped
  question of the reference verifier, the presented lengths (`introLenR`, `introLenL`).
-/

noncomputable section

namespace MIPRE.Tailored.Intro.LenIntro

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL CL.Detyping CL.Detyping.Program
open MIPRE.Introspection MIPRE.QLD MIPRE.QLD.PauliAnswerProgram Calls

/-- The labels of the introspection verifier's detyping. -/
abbrev Label := Introspection.DecisionKernel.Label

/-- The type graph of the introspection verifier's detyping. -/
abbrev E : Label → Label → Prop := DecisionCompiler.graph

/-! ## The lengths -/

/-- The field width `k = fieldBits c λ n`. -/
abbrev kOf (c lam n : ℕ) : ℕ := SourceCompiler.fieldBits c lam n

/-- The selector width `j = selectorBits c λ n`. -/
abbrev jOf (c lam n : ℕ) : ℕ := PauliSamplerParameters.selectorBits c lam n

/-- The readable length of a label at `(c, λ, n)`: `Typed.lenR` at `k = fieldBits c λ n`,
`j = selectorBits c λ n`, `R = (2^n)^λ`. -/
def introLenR (c lam n : ℕ) : Label → ℕ :=
  Typed.lenR (kOf c lam n) (jOf c lam n) ((2 ^ n) ^ lam)

/-- The linear length of a label at `(c, λ, n)`: `Typed.len - Typed.lenR`. -/
def introLenL (c lam n : ℕ) (t : Label) : ℕ :=
  Typed.len (kOf c lam n) (jOf c lam n) ((2 ^ n) ^ lam) t -
    Typed.lenR (kOf c lam n) (jOf c lam n) ((2 ^ n) ^ lam) t

/-- The length of kind `κ`: readable for `false`, linear for `true`. -/
def introLen (c lam n : ℕ) (κ : Bool) : Label → ℕ :=
  if κ then introLenL c lam n else introLenR c lam n

/-! ## The lengths as combinations of the parameters -/

/-- The five coefficients of a length, on `k`, `m k`, `Q`, `R` and `1`. -/
abbrev Coef := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The combination of the coefficients. -/
def lin (v : Coef) (k m Q R : ℕ) : ℕ :=
  v.1 * k + v.2.1 * (m * k) + v.2.2.1 * Q + v.2.2.2.1 * R + v.2.2.2.2

/-- The coefficients of the length of kind `κ` at a label. -/
def coef : Label → Bool → Coef
  | .inl (.pauli .Z), false => (0, 0, 1, 0, 0)
  | .inl _, false => (0, 0, 0, 0, 0)
  | .inr (.hide _, _), false => (0, 0, 1, 0, 0)
  | .inr _, false => (0, 0, 1, 1, 0)
  | .inl (.pauli .Z), true => (0, 0, 0, 0, 0)
  | .inl (.pauli .X), true => (0, 0, 1, 0, 0)
  | .inl (.point _), true => (1, 0, 0, 0, 0)
  | .inl (.aline _), true => (2, 0, 0, 0, 0)
  | .inl (.dline _), true => (1, 1, 0, 0, 0)
  | .inl (.pairB _), true => (0, 0, 0, 0, 1)
  | .inl (.var _), true => (0, 0, 0, 0, 1)
  | .inl .pair, true => (0, 0, 0, 0, 2)
  | .inl (.con _), true => (0, 0, 0, 0, 3)
  | .inr (.introspect, _), true => (0, 0, 0, 1, 0)
  | .inr (.sample, _), true => (0, 0, 0, 1, 0)
  | .inr (.read, _), true => (0, 0, 1, 1, 0)
  | .inr (.hide _, _), true => (0, 0, 2, 0, 0)

/-- **The typed lengths are the combinations of the coefficients**, at `m = 2^j` and
`Q = 2^m k`. -/
theorem lin_coef (k j R : ℕ) (t : Label) (κ : Bool) :
    lin (coef t κ) k (2 ^ j) (2 ^ 2 ^ j * k) R =
      if κ then Typed.len k j R t - Typed.lenR k j R t else Typed.lenR k j R t := by
  rcases t with p | ⟨t, w⟩
  · cases κ <;> cases p <;>
      first
      | (rename_i W; cases W) <;>
          simp [coef, lin, Typed.lenR, Typed.len, PauliCons.pauliLenR, pauliLen, pauliRead,
            count, width] <;> ring
      | simp [coef, lin, Typed.lenR, Typed.len, PauliCons.pauliLenR, pauliLen, pauliRead,
            count, width]
  · cases κ <;> cases t <;>
      simp [coef, lin, Typed.lenR, Typed.len, auxLenR, auxLen, Typed.Q] <;> omega

/-! ## The decoding of a question -/

/-- The number of bits of a graph view. -/
abbrev gd : ℕ := graphDim Label

/-- The coefficients at a graph view and a kind: those of the label it decodes to, zero when it
does not decode. -/
def coefAt (g : Graph.Coord Label → 𝔽₂) (κ : Bool) : Coef :=
  ((decodeView E g).map fun p => coef p.2 κ).getD (0, 0, 0, 0, 0)

/-- Coefficients in unary. -/
abbrev UCoef := Unary × Unary × Unary × Unary × Unary

/-- A coefficient vector in unary. -/
def ucoef (v : Coef) : UCoef :=
  (unary v.1, unary v.2.1, unary v.2.2.1, unary v.2.2.2.1, unary v.2.2.2.2)

/-- The finite table: from the bits of a graph view and a kind, the coefficients. -/
def tab (p : (Fin gd → 𝔽₂) × Bool) : UCoef :=
  ucoef (coefAt (pull graphEquiv.toEmbedding p.1) p.2)

/-- The combination of unary coefficients with the unary parameters `(k, m, Q, R)`. -/
def linF : PolyTimeFun (UCoef × (Unary × Unary × Unary × Unary)) Unary :=
  let a := fst.comp fst
  let b := fst.comp (snd.comp fst)
  let cq := fst.comp (snd.comp (snd.comp fst))
  let dr := fst.comp (snd.comp (snd.comp (snd.comp fst)))
  let e := snd.comp (snd.comp (snd.comp (snd.comp fst)))
  let k := fst.comp snd
  let m := fst.comp (snd.comp snd)
  let Q := fst.comp (snd.comp (snd.comp snd))
  let R := snd.comp (snd.comp (snd.comp snd))
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ productUnary a k)
    (ap₂ productUnary b (ap₂ productUnary m k))) (ap₂ productUnary cq Q))
    (ap₂ productUnary dr R)) e

theorem length_linF (v : Coef) (k m Q R : ℕ) :
    (linF (ucoef v, (unary k, unary m, unary Q, unary R))).length = lin v k m Q R := by
  simp [linF, ucoef, lin, productUnary_length]
  ring

/-! ## The stages -/

/-- The input of the core: `(λ, n, d)`. -/
abbrev In0 := ℕ × ℕ × Data

/-- Stage 1: keep `(d, (λ, n))`, and pass `(λ, n)` to the bounds program. -/
def g1 : PolyTimeFun In0 ((Data × (ℕ × ℕ)) × (ℕ × ℕ)) :=
  ((snd.comp snd).pair (fst.pair (fst.comp snd))).pair (fst.pair (fst.comp snd))

@[simp] theorem g1_apply (a : In0) : g1 a = ((a.2.2, (a.1, a.2.1)), (a.1, a.2.1)) := rfl

/-- Stage 4: keep `(d, (Q, R))` in unary, and pass `(λ, n)` to the parameters program. -/
def g4 : PolyTimeFun ((Data × (ℕ × ℕ)) × (Unary × Unary)) ((Data × (Unary × Unary)) × (ℕ × ℕ)) :=
  ((fst.comp fst).pair snd).pair (snd.comp fst)

@[simp] theorem g4_apply (a : (Data × (ℕ × ℕ)) × (Unary × Unary)) :
    g4 a = ((a.1.1, a.2), a.1.2) := rfl

/-- The question bits read off `d = (x, κ)`. -/
def readX : PolyTimeFun Data BitStr := readBits.comp treeHead

/-- The kind read off `d = (x, κ)`. -/
def readK : PolyTimeFun Data Bool := rawTruthProg.comp treeTail

theorem readX_encode (x : BitStr) (κ : Bool) : readX (encode (x, κ)) = x := by
  simp [readX, encode_prod, readBits_encode]

theorem readK_encode (x : BitStr) (κ : Bool) : readK (encode (x, κ)) = κ := by
  simp only [readK, encode_prod, comp_apply, treeTail_cons]
  exact rawTruthProg_encode_bool κ

/-- Stage 6, the output: `(d, (Q, R))` and `(k, j, m)` in unary give the length in unary. -/
def g6 : PolyTimeFun ((Data × (Unary × Unary)) × (Unary × Unary × Unary)) Unary :=
  let d := fst.comp fst
  let cv := (finiteFunction tab).comp (((readVector gd).comp (readX.comp d)).pair (readK.comp d))
  let par := (fst.comp snd).pair ((snd.comp (snd.comp snd)).pair
    ((fst.comp (snd.comp fst)).pair (snd.comp (snd.comp fst))))
  linF.comp (cv.pair par)

theorem g6_apply (d : Data) (Q R : ℕ) (k j m : ℕ) :
    g6 ((d, (unary Q, unary R)), (unary k, unary j, unary m)) =
      linF (ucoef (coefAt (graphOfBits (readX d)) (readK d)), (unary k, unary m, unary Q, unary R)) := by
  simp only [g6, comp_apply, pair_apply, fst_apply, snd_apply, finiteFunction_apply, tab,
    readVector_apply]
  rfl

/-- **The core** of the calculator, on `(λ, n, d)`. -/
def core (c : ℕ) : Prog :=
  seq g1.code (seq (withCtx (SourceCompiler.boundsProg c)) (seq (withCtx ClockArithmetic.bothUnary)
    (seq g4.code (seq (withCtx (PauliSamplerParameters.prog c)) g6.code))))

theorem core_wellScoped (c : ℕ) : (core c).WellScoped 1 :=
  seq_wellScoped g1.closed (seq_wellScoped (withCtx_wellScoped (SourceCompiler.boundsProg_closed c))
    (seq_wellScoped (withCtx_wellScoped ClockArithmetic.bothUnary_closed)
      (seq_wellScoped g4.closed (seq_wellScoped
        (withCtx_wellScoped (PauliSamplerParameters.prog_closed c)) g6.closed))))

/-- The output of the core at `(λ, n, d)`. -/
def coreOut (c lam n : ℕ) (d : Data) : Unary :=
  g6 ((d, (unary (SourceCompiler.registerBits c lam n), unary (SourceCompiler.originalBound lam n))),
    PauliSamplerParameters.parameters c lam n)

/-- The cost of the core at `(λ, n, d)`, stage by stage. -/
def coreCost (c lam n : ℕ) (d : Data) : ℕ :=
  let Q := SourceCompiler.registerBits c lam n
  let R := SourceCompiler.originalBound lam n
  let ctx : Data := encode ((d, (lam, n)) : Data × (ℕ × ℕ))
  let ctx' : Data := encode ((d, (unary Q, unary R)) : Data × (Unary × Unary))
  g1.timeBound.eval (esize ((lam, n, d) : In0)) +
    (ctx.size + (encode (lam, n) : Data).size + SourceCompiler.boundsCost c lam n + 5) +
    (ctx.size + (encode (Q, R) : Data).size +
      (ClockArithmetic.unaryCost Q + ClockArithmetic.unaryCost R + esize Q + esize R + 2 * Q +
        2 * R + 20) + 5) +
    g4.timeBound.eval (esize (((d, (lam, n)), (unary Q, unary R)) :
      (Data × (ℕ × ℕ)) × (Unary × Unary))) +
    (ctx'.size + (encode (lam, n) : Data).size + PauliSamplerParameters.cost c lam n + 5) +
    g6.timeBound.eval (esize (((d, (unary Q, unary R)), PauliSamplerParameters.parameters c lam n) :
      (Data × (Unary × Unary)) × (Unary × Unary × Unary))) + 5

/-- **The run of the core.** -/
theorem core_runsLe (c lam n : ℕ) (d : Data) :
    RunsLe (core c) (encode ((lam, n, d) : In0)) (encode (coreOut c lam n d))
      (coreCost c lam n d) := by
  simp only [coreCost, coreOut]
  set Q := SourceCompiler.registerBits c lam n
  set R := SourceCompiler.originalBound lam n
  have h1 := RunsLe.pure g1 ((lam, n, d) : In0)
  obtain ⟨tb, htb, hb⟩ := SourceCompiler.boundsProg_runs_cost c lam n
  have h2 := RunsLe.withCtx (SourceCompiler.boundsProg_closed c)
    (encode ((d, (lam, n)) : Data × (ℕ × ℕ))) ⟨tb, htb, hb⟩
  obtain ⟨tu, htu, hu⟩ := ClockArithmetic.bothUnary_runs Q R
  have h3 := RunsLe.withCtx ClockArithmetic.bothUnary_closed
    (encode ((d, (lam, n)) : Data × (ℕ × ℕ))) ⟨tu, htu, hu⟩
  have h4 := RunsLe.pure g4 (((d, (lam, n)), (unary Q, unary R)) :
    (Data × (ℕ × ℕ)) × (Unary × Unary))
  obtain ⟨tp, htp, hp⟩ := PauliSamplerParameters.prog_runs_cost c lam n
  have h5 := RunsLe.withCtx (PauliSamplerParameters.prog_closed c)
    (encode ((d, (unary Q, unary R)) : Data × (Unary × Unary))) ⟨tp, htp, hp⟩
  have h6 := RunsLe.pure g6 (((d, (unary Q, unary R)), PauliSamplerParameters.parameters c lam n) :
    (Data × (Unary × Unary)) × (Unary × Unary × Unary))
  simp only [g1_apply, g4_apply] at h1 h4
  have w6 := g6.closed
  have w5 := seq_wellScoped (withCtx_wellScoped (PauliSamplerParameters.prog_closed c)) w6
  have w4 := seq_wellScoped g4.closed w5
  have w3 := seq_wellScoped (withCtx_wellScoped ClockArithmetic.bothUnary_closed) w4
  have w2 := seq_wellScoped (withCtx_wellScoped (SourceCompiler.boundsProg_closed c)) w3
  simp only [encode_prod, encode_unary] at h1 h2 h3 h4 h5 h6 ⊢
  have c5 := RunsLe.seq w6 h5 h6
  have c4 := RunsLe.seq w5 h4 c5
  have c3 := RunsLe.seq w4 h3 c4
  have c2 := RunsLe.seq w3 h2 c3
  have c1 := RunsLe.seq w2 h1 c2
  refine c1.mono (le_of_eq ?_)
  omega

/-! ## The calculator -/

/-- Inspect the index in place: at `n = 0` (and on malformed inputs) output `nil`, otherwise run
`p` on the input. -/
def lenWrap (p : Prog) : Prog := .elim 0 .nil (.elim 0 .nil (callVar 4 p))

theorem lenWrap_wellScoped {p : Prog} (hp : p.WellScoped 1) : (lenWrap p).WellScoped 1 :=
  ⟨by omega, trivial, by omega, trivial, callVar_wellScoped (by omega) hp⟩

theorem lenWrap_runs_zero (p : Prog) (d : Data) :
    (lenWrap p).Runs (.cons (encode (0 : ℕ)) d) .nil 3 :=
  Eval.elim_cons (i := 0) (by rfl) (Eval.elim_nil (i := 0) (by rfl) (Eval.nil _))

theorem lenWrap_runs_pos {p : Prog} (hp : p.WellScoped 1) {n : ℕ} (hn : 1 ≤ n)
    (d r : Data) (t : ℕ) (hr : p.Runs (.cons (encode n) d) r t) :
    (lenWrap p).Runs (.cons (encode n) d) r (t + (Data.cons (encode n) d).size + 4) := by
  have hne : encode n ≠ Data.nil := by
    intro h
    have hz : n = 0 := encode_injective (show encode n = encode (0 : ℕ) from h)
    omega
  cases he : encode n with
  | nil => exact False.elim (hne he)
  | cons a b =>
    rw [he] at hr
    have hcall := callVar_eval
      (env := [a, b, Data.cons a b, d, Data.cons (.cons a b) d]) (i := 4) hp (by rfl) hr
    have hinner := Eval.elim_cons (env := [Data.cons a b, d, Data.cons (.cons a b) d])
      (i := 0) (n := Prog.nil) (by rfl) hcall
    have houter := Eval.elim_cons (env := [Data.cons (.cons a b) d])
      (i := 0) (n := Prog.nil) (by rfl) hinner
    exact houter.cast_cost (by omega)

/-- The program of the calculator at `λ`: empty at `λ = 0`, otherwise the core with `λ` stored,
behind the index test. -/
def lenProg (c lam : ℕ) : Prog :=
  if lam = 0 then .nil else lenWrap (hardcode (core c) (encode lam))

theorem lenProg_wellScoped (c lam : ℕ) : (lenProg c lam).WellScoped 1 := by
  unfold lenProg
  split_ifs
  · trivial
  · exact lenWrap_wellScoped (hardcode_wellScoped (core_wellScoped c) _)

/-- **The answer-length calculator of the introspection verifier** at the constant `c` and
level `λ`. -/
def lenIntroC (c lam : ℕ) : Decider := ⟨lenProg c lam, lenProg_wellScoped c lam⟩

/-- The wrapper, as a polynomial-time map on descriptions. -/
def lenWrapF : PolyTimeFun Prog Prog :=
  ap₂ ClockSimulation.codeElim (const .nil)
    (ap₂ ClockSimulation.codeElim (const .nil) (ClockSimulation.codeCall 4))

theorem lenWrapF_apply (p : Prog) : lenWrapF p = lenWrap p := rfl

/-- **The calculator's program from `λ`, in polynomial time.** -/
def lenProgF (c : ℕ) : PolyTimeFun ℕ Prog :=
  ite (AuxiliaryProgram.equal (PolyTimeFun.id ℕ) (const 0)) (const .nil)
    (lenWrapF.comp ((PolyTimeFun.smn ℕ).comp ((const (core c)).pair (PolyTimeFun.id ℕ))))

theorem lenProgF_eq (c lam : ℕ) : lenProgF c lam = (lenIntroC c lam).prog := by
  simp only [lenProgF, PolyTimeFun.ite_apply, AuxiliaryProgram.equal_iff, id_apply, const_apply,
    comp_apply, pair_apply, PolyTimeFun.smn_apply, lenWrapF_apply]
  rfl

/-- The run of the calculator at positive `λ` and `n`. -/
theorem lenIntroC_runs_pos (c : ℕ) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (d : Data) :
    RunsLe (lenIntroC c lam).prog (.cons (encode n) d) (encode (coreOut c lam n d))
      (coreCost c lam n d + (encode lam : Data).size + 2 * (Data.cons (encode n) d).size + 7) := by
  obtain ⟨t, ht, hr⟩ := core_runsLe c lam n d
  have hr' : (core c).Runs (.cons (encode lam) (.cons (encode n) d)) (encode (coreOut c lam n d)) t := by
    simpa only [encode_prod, encode_data] using hr
  have hh := hardcode_time (core_wellScoped c) hr'
  have hw := lenWrap_runs_pos (hardcode_wellScoped (core_wellScoped c) (encode lam)) hn d _ _ hh
  refine ⟨_, ?_, (show (lenProg c lam).Runs _ _ _ by rw [lenProg, if_neg (by omega)]; exact hw)⟩
  omega

/-! ## What the calculator outputs -/

/-- The length the calculator outputs on `(n, x, κ)`: `0` at `λ = 0` or `n = 0`, otherwise the
combination of the coefficients of the label `x`'s graph view decodes to. -/
def lenAt (c lam n : ℕ) (x : BitStr) (κ : Bool) : ℕ :=
  if lam = 0 ∨ n = 0 then 0 else
    lin (coefAt (graphOfBits x) κ) (kOf c lam n) (2 ^ jOf c lam n)
      (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n)

theorem length_coreOut (c lam n : ℕ) (x : BitStr) (κ : Bool) :
    (coreOut c lam n (encode (x, κ))).length =
      lin (coefAt (graphOfBits x) κ) (kOf c lam n) (2 ^ jOf c lam n)
        (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n) := by
  rw [coreOut, PauliSamplerParameters.parameters, g6_apply, length_linF, readX_encode,
    readK_encode]
  rfl

/-- **What the calculator outputs**, on every bit string and every `n`, `λ`. -/
theorem lenIntroC_lenIs (c lam n : ℕ) (x : BitStr) (κ : Bool) :
    LenIs (lenIntroC c lam) n x κ (lenAt c lam n x κ) := by
  by_cases hl : lam = 0
  · subst hl
    refine ⟨1, .nil, ?_, by simp [lenAt]⟩
    show (lenProg c 0).Runs _ _ _
    rw [lenProg, if_pos rfl]
    exact Eval.nil _
  by_cases hn : n = 0
  · subst hn
    refine ⟨3, .nil, ?_, by simp [lenAt]⟩
    show (lenProg c lam).Runs _ _ _
    rw [lenProg, if_neg hl, encode_prod]
    exact lenWrap_runs_zero _ _
  obtain ⟨t, -, hr⟩ := lenIntroC_runs_pos c (lam := lam) (n := n) (by omega) (by omega)
    (encode (x, κ))
  refine ⟨t, _, by rw [encode_prod]; exact hr, ?_⟩
  rw [← unary_length (coreOut c lam n (encode (x, κ))), encode_unary, length_spineList_ofNat,
    length_coreOut, lenAt, if_neg (by omega)]

/-- At positive `λ` and `n`, the output is the length of the label the graph view decodes to,
`0` when it does not decode. -/
theorem lenAt_eq (c : ℕ) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (x : BitStr) (κ : Bool) :
    lenAt c lam n x κ =
      ((decodeView E (graphOfBits x)).map fun p => introLen c lam n κ p.2).getD 0 := by
  rw [lenAt, if_neg (by omega), coefAt]
  cases decodeView E (graphOfBits x) with
  | none => simp [lin]
  | some p =>
    simp only [Option.map_some, Option.getD_some]
    have hQ : SourceCompiler.registerBits c lam n = 2 ^ 2 ^ jOf c lam n * kOf c lam n := rfl
    rw [hQ, SourceCompiler.originalBound_eq, lin_coef]
    cases κ <;> rfl

/-- **The calculator at a detyped question**: at positive `λ` and `n`, on the bits of a detyped
question `q` (numbered as the reference verifier numbers them, `vectorEquiv`), it outputs the
readable (`κ = false`) or linear (`κ = true`) length of the label `q` decodes to, `0` when it
does not decode — the lengths of the presented game, `TypedData.detype`. -/
theorem lenIntroC_lenIs_question (c : ℕ) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) {s : ℕ}
    (q : Coord Label (Fin s) → 𝔽₂) (κ : Bool) :
    LenIs (lenIntroC c lam) n (toBits (DeciderProgram.vectorEquiv s q)) κ
      (((typeOf E q).map (introLen c lam n κ)).getD 0) := by
  have h := lenIntroC_lenIs c lam n (toBits (DeciderProgram.vectorEquiv s q)) κ
  rw [lenAt_eq c hl hn, show DeciderProgram.vectorEquiv s q =
      push (registerEquiv s).toEmbedding q from rfl, DeciderProgram.graphOfBits_register] at h
  rw [typeOf, Option.map_map]
  exact h

/-- The same, read on a detyped tailored game whose typed lengths are `introLenR`,
`introLenL`. -/
theorem lenIntroC_lenIs_detype (c : ℕ) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) {s : ℕ}
    (D : TypedData Label (Fin s)) (hR : D.lenR = introLenR c lam n)
    (hL : D.lenL = introLenL c lam n)
    (μ : (Coord Label (Fin s) → ZMod 2) → (Coord Label (Fin s) → ZMod 2) → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (hμ1 : ∑ x, ∑ y, μ x y = 1) (q : Coord Label (Fin s) → 𝔽₂) :
    LenIs (lenIntroC c lam) n (toBits (DeciderProgram.vectorEquiv s q)) false
        ((D.detype E μ hμ hμ1).lenR q) ∧
      LenIs (lenIntroC c lam) n (toBits (DeciderProgram.vectorEquiv s q)) true
        ((D.detype E μ hμ hμ1).lenL q) := by
  refine ⟨?_, ?_⟩
  · have h := lenIntroC_lenIs_question c hl hn q false
    simpa [TypedData.detype, hR, introLen] using h
  · have h := lenIntroC_lenIs_question c hl hn q true
    simpa [TypedData.detype, hL, introLen] using h

end MIPRE.Tailored.Intro.LenIntro

end
