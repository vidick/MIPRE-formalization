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
public import MIPRE.Foundations.Introspection.DecisionPreparationCost
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
* `lenIntroC_budget`: one constant `C` with the calculator within `2^{(λn + 1)^C}` at degree `C`
  on every input, malformed included, and its lengths at most `2^{(λn + 1)^C}`: the cost is a
  polynomial in `2^{(2c + 2)(λn + 2)} + |d|` (`costF`), the parameters being at most the former
  (`params_le_scale`). `lenIntroC_lenTotal`: it halts everywhere.
* `lenIntro`, `lenIntroProg`, `lenIntro_lenIs`, `lenIntro_budget`: the same at `sevenConstant`, the
  fields `len`, `lenProg`, `lenProg_eq`, `len_total` and the `len` parts of `within` of
  `TailoredIntrospection`.
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

/-! ## The costs -/

theorem esize_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := (Nat.size_le.mpr Nat.lt_two_pow_self : x.size ≤ x); omega)

/-- The scale of the parameters at `u = λ n`: `2^{(2c + 2)(u + 2)}`. -/
def scale (c u : ℕ) : ℕ := 2 ^ ((2 * c + 2) * (u + 2))

theorem one_le_scale (c u : ℕ) : 1 ≤ scale c u := Nat.one_le_two_pow

/-- The parameters at positive `λ` and `n` are at most the scale. -/
theorem params_le_scale (c : ℕ) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    lam ≤ scale c (lam * n) ∧ n ≤ scale c (lam * n) ∧ lam * n ≤ scale c (lam * n) ∧
      SourceCompiler.registerBits c lam n ≤ scale c (lam * n) ∧
      SourceCompiler.originalBound lam n ≤ scale c (lam * n) := by
  set u := lam * n with hu
  have hlu : lam ≤ u := Nat.le_mul_of_pos_right lam hn
  have hnu : n ≤ u := Nat.le_mul_of_pos_left n hl
  have hR : SourceCompiler.originalBound lam n ≤ scale c u :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have huR : u < SourceCompiler.originalBound lam n := Nat.lt_two_pow_self
  have hlog : SourceCompiler.canonicalLog lam n ≤ u + 2 := by
    unfold SourceCompiler.canonicalLog; omega
  have hm := PauliSamplerParameters.registerPower_le c lam n
  have hk := PauliSamplerParameters.fieldBits_le c lam n
  have hw : c * SourceCompiler.canonicalLog lam n + 1 ≤ c * (u + 2) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left c hlog) 1
  have hQ : SourceCompiler.registerBits c lam n ≤ scale c u := by
    unfold SourceCompiler.registerBits scale
    calc 2 ^ SourceCompiler.registerPower c lam n * SourceCompiler.fieldBits c lam n
        ≤ 2 ^ (c * (u + 2) + 1) * 2 ^ (c * (u + 2) + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
            ((show SourceCompiler.fieldBits c lam n ≤ c * (u + 2) + 1 by omega).trans
              Nat.lt_two_pow_self.le)
      _ = 2 ^ (2 * c * (u + 2) + 2) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ ((2 * c + 2) * (u + 2)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  exact ⟨by omega, by omega, by omega, hQ, hR⟩

/-- A majorant of the cost of the calculator at positive `λ` and `n`, in `z = scale + |d|`. -/
def costF (c z : ℕ) : ℕ :=
  g1.timeBound.eval (8 * z + 4) + (20 * z + 10 + DecisionPreparation.boundsMajorant c z) +
    (40 * z + 40 + 2 * PauliSamplerParameters.unaryMajorant z) + g4.timeBound.eval (20 * z + 20) +
    (20 * z + 20 + PauliSamplerParameters.costMajorant c z) +
    g6.timeBound.eval (20 * z + 6 * PauliSamplerParameters.widthBound c z + 20) + 30 * z + 30

theorem costF_polyBounded (c : ℕ) : PolyBounded (costF c) := by
  have hl : ∀ a b : ℕ, PolyBounded fun z => a * z + b := fun a b =>
    (PolyBounded.id.const_mul a).add_const b
  have hu : PolyBounded PauliSamplerParameters.unaryMajorant := by
    unfold PauliSamplerParameters.unaryMajorant
    repeat' first
      | apply PolyBounded.add
      | apply PolyBounded.mul
      | apply PolyBounded.const
      | exact PolyBounded.id
  have hw : PolyBounded (PauliSamplerParameters.widthBound c) := by
    unfold PauliSamplerParameters.widthBound
    exact ((PolyBounded.id.add_const 2).const_mul c).add_const 1
  unfold costF
  refine (((((((PolyBounded.eval _ (hl 8 4)).add ((hl 20 10).add
    (DecisionPreparation.boundsMajorant_polyBounded c))).add ((hl 40 40).add (hu.const_mul 2))).add
    (PolyBounded.eval _ (hl 20 20))).add ((hl 20 20).add
    (PauliSamplerParameters.costMajorant_polyBounded c))).add
    (PolyBounded.eval _ (((PolyBounded.id.const_mul 20).add (hw.const_mul 6)).add_const 20))).add
    (PolyBounded.id.const_mul 30)).add_const 30

/-- **The cost at positive `λ` and `n` is at most the majorant** at `z = scale + |d|`. -/
theorem cost_le_costF {c : ℕ} (hc : 1 ≤ c) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (d : Data) :
    coreCost c lam n d + (encode lam : Data).size + 2 * (Data.cons (encode n) d).size + 7 ≤
      costF c (scale c (lam * n) + d.size) := by
  obtain ⟨hlz, hnz, huz, hQz, hRz⟩ := params_le_scale c hl hn
  simp only [coreCost, costF]
  change _ + (esize ((d, (lam, n)) : Data × (ℕ × ℕ)) + esize (lam, n) + _ + 5) +
    (esize ((d, (lam, n)) : Data × (ℕ × ℕ)) + esize (SourceCompiler.registerBits c lam n,
      SourceCompiler.originalBound lam n) + _ + 5) + _ +
    (esize ((d, (unary (SourceCompiler.registerBits c lam n),
      unary (SourceCompiler.originalBound lam n))) : Data × (Unary × Unary)) + esize (lam, n) +
      _ + 5) + _ + 5 + esize lam + 2 * (esize n + d.size + 1) + 7 ≤ _
  set z := scale c (lam * n) + d.size with hz
  set Q := SourceCompiler.registerBits c lam n
  set R := SourceCompiler.originalBound lam n
  have hlz' : lam ≤ z := by omega
  have hnz' : n ≤ z := by omega
  have huz' : lam * n ≤ z := by omega
  have hQ : Q ≤ z := by omega
  have hR : R ≤ z := by omega
  have hs : d.size ≤ z := by omega
  have el := esize_le_four lam
  have en := esize_le_four n
  have eQ := esize_le_four Q
  have eR := esize_le_four R
  have hb := DecisionPreparation.boundsCost_le_majorant hc hlz' hnz' huz'
  have hp := PauliSamplerParameters.cost_le_majorant hc hlz' hnz' huz'
  have huQ := PauliSamplerParameters.unaryCost_le hQ
  have huR := PauliSamplerParameters.unaryCost_le hR
  have hpar := PauliSamplerParameters.parameters_size_le hc huz'
  have h1 := polynomial_eval_mono g1.timeBound
    (show esize ((lam, n, d) : In0) ≤ 8 * z + 4 by simp only [esize_prod, esize_data]; omega)
  have h4 := polynomial_eval_mono g4.timeBound
    (show esize (((d, (lam, n)), (unary Q, unary R)) : (Data × (ℕ × ℕ)) × (Unary × Unary)) ≤
      20 * z + 20 by simp only [esize_prod, esize_data, esize_unary]; omega)
  have h6 := polynomial_eval_mono g6.timeBound
    (show esize (((d, (unary Q, unary R)), PauliSamplerParameters.parameters c lam n) :
      (Data × (Unary × Unary)) × (Unary × Unary × Unary)) ≤
        20 * z + 6 * PauliSamplerParameters.widthBound c z + 20 by
      rw [esize_prod, esize_prod, esize_prod, esize_data, esize_unary, esize_unary]; omega)
  simp only [esize_prod, esize_data, esize_unary] at h1 h4 h6 ⊢
  omega

/-- `A (u + 1) ≤ (u + 1)^C` once `A ≤ 2^{C - 1}`, for `u ≥ 1`. -/
theorem mul_le_pow {A u C : ℕ} (hu : 1 ≤ u) (hC : 1 ≤ C) (hA : A ≤ 2 ^ (C - 1)) :
    A * (u + 1) ≤ (u + 1) ^ C := by
  have h2 : 2 ^ (C - 1) ≤ (u + 1) ^ (C - 1) := Nat.pow_le_pow_left (by omega) _
  calc A * (u + 1) ≤ (u + 1) ^ (C - 1) * (u + 1) := Nat.mul_le_mul_right _ (hA.trans h2)
    _ = (u + 1) ^ C := by rw [← pow_succ]; congr 1; omega

theorem lin_coef_le (t : Label) (κ : Bool) (k m Q R : ℕ) :
    lin (coef t κ) k m Q R ≤ 2 * k + m * k + 2 * Q + R + 3 := by
  rcases t with p | ⟨t, w⟩
  · cases κ <;> cases p <;>
      first
      | (rename_i W; cases W) <;> simp [coef, lin] <;> omega
      | simp [coef, lin]
  · cases κ <;> cases t <;> simp [coef, lin] <;> omega

theorem lin_coefAt_le (g : Graph.Coord Label → 𝔽₂) (κ : Bool) (k m Q R : ℕ) :
    lin (coefAt g κ) k m Q R ≤ 2 * k + m * k + 2 * Q + R + 3 := by
  unfold coefAt
  cases decodeView E g with
  | none => simp [lin]
  | some p => exact lin_coef_le p.2 κ k m Q R

/-- **The costs of the calculator**, in the shape of `Introspection.budget`: a constant `C` with
the calculator within `2^{(λn + 1)^C}` at degree `C` on every input, and its lengths at most
`2^{(λn + 1)^C}`. -/
theorem lenIntroC_budget {c : ℕ} (hc : 1 ≤ c) : ∃ C : ℕ, ∀ lam n : ℕ,
    (lenIntroC c lam).TimeBoundAt n (ansBound C lam n) C ∧
      LenBound (lenIntroC c lam) n (ansBound C lam n) := by
  obtain ⟨L, hL⟩ := (costF_polyBounded c).exists_le_pow
  set A := 4 * (c + 1) * L + 4 * c + 8 with hA
  refine ⟨L + A + 1, fun lam n => ⟨fun d => ?_, ?_⟩⟩
  · have hs := Data.size_pos d
    have hpos : 1 ≤ (d.size + 1) ^ (L + A + 1) := Nat.one_le_pow _ _ (by omega)
    have hab : 1 ≤ ansBound (L + A + 1) lam n := Nat.one_le_two_pow
    by_cases hl : lam = 0
    · subst hl
      refine ⟨.nil, 1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
      show (lenProg c 0).Runs _ _ _
      rw [lenProg, if_pos rfl]
      exact Eval.nil _
    by_cases hn : n = 0
    · subst hn
      refine ⟨.nil, 3, ?_, ?_⟩
      · have h2 : 2 ≤ (d.size + 1) ^ (L + A + 1) :=
          (show 2 ≤ d.size + 1 by omega).trans (Nat.le_self_pow (by omega) _)
        simp only [ansBound, Nat.mul_zero, Nat.zero_add, one_pow, pow_one]
        omega
      · show (lenProg c lam).Runs _ _ _
        rw [lenProg, if_neg hl]
        exact lenWrap_runs_zero _ _
    have hl1 : 1 ≤ lam := by omega
    have hn1 : 1 ≤ n := by omega
    obtain ⟨t, ht, hr⟩ := lenIntroC_runs_pos c hl1 hn1 d
    refine ⟨_, t, ?_, hr⟩
    set u := lam * n with hu
    have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hsc := one_le_scale c u
    have hz : 2 ≤ scale c u + d.size := by omega
    have hcost := (cost_le_costF hc hl1 hn1 d).trans (hL _ hz)
    -- `z ≤ scale · (|d| + 1)`
    have hz' : scale c u + d.size ≤ scale c u * (d.size + 1) := by nlinarith
    have hzL : (scale c u + d.size) ^ L ≤ scale c u ^ L * (d.size + 1) ^ L := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hz' L
    -- `scale^L ≤ 2^{(u + 1)^C}`
    have hexp : (2 * c + 2) * (u + 2) * L ≤ (u + 1) ^ (L + A + 1) := by
      have h1 : (2 * c + 2) * (u + 2) * L ≤ (4 * (c + 1) * L) * (u + 1) :=
        calc (2 * c + 2) * (u + 2) * L = (2 * c + 2) * L * (u + 2) := by ring
          _ ≤ (2 * c + 2) * L * (2 * (u + 1)) := Nat.mul_le_mul_left _ (by omega)
          _ = (4 * (c + 1) * L) * (u + 1) := by ring
      have h2 : 4 * (c + 1) * L ≤ 2 ^ (L + A + 1 - 1) :=
        (show 4 * (c + 1) * L ≤ L + A + 1 - 1 by omega).trans Nat.lt_two_pow_self.le
      exact h1.trans (mul_le_pow hu1 (by omega) h2)
    have hscale : scale c u ^ L ≤ ansBound (L + A + 1) lam n := by
      unfold scale ansBound
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) hexp
    have hdeg : (d.size + 1) ^ L ≤ (d.size + 1) ^ (L + A + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc t ≤ (scale c u + d.size) ^ L := ht.trans hcost
      _ ≤ scale c u ^ L * (d.size + 1) ^ L := hzL
      _ ≤ ansBound (L + A + 1) lam n * (d.size + 1) ^ (L + A + 1) := Nat.mul_le_mul hscale hdeg
  · intro x κ m hm
    rw [hm.unique (lenIntroC_lenIs c lam n x κ), lenAt]
    split_ifs with h0
    · exact Nat.zero_le _
    have hl1 : 1 ≤ lam := by omega
    have hn1 : 1 ≤ n := by omega
    obtain ⟨-, -, -, hQ, hR⟩ := params_le_scale c hl1 hn1
    set u := lam * n with hu
    have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hle := lin_coefAt_le (graphOfBits x) κ (kOf c lam n) (2 ^ jOf c lam n)
      (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n)
    have hQk : SourceCompiler.registerBits c lam n = 2 ^ 2 ^ jOf c lam n * kOf c lam n := rfl
    have hk : kOf c lam n ≤ SourceCompiler.registerBits c lam n := by
      rw [hQk]; exact Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
    have hmk : 2 ^ jOf c lam n * kOf c lam n ≤ SourceCompiler.registerBits c lam n := by
      rw [hQk]; exact Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    have h9 : 2 * kOf c lam n + 2 ^ jOf c lam n * kOf c lam n +
        2 * SourceCompiler.registerBits c lam n + SourceCompiler.originalBound lam n + 3 ≤
          2 ^ 4 * scale c u := by
      have := one_le_scale c u
      omega
    have hexp : 4 + (2 * c + 2) * (u + 2) ≤ (u + 1) ^ (L + A + 1) := by
      have h1 : 4 + (2 * c + 2) * (u + 2) ≤ (4 * c + 8) * (u + 1) := by nlinarith
      have h2 : 4 * c + 8 ≤ 2 ^ (L + A + 1 - 1) :=
        (show 4 * c + 8 ≤ L + A + 1 - 1 by omega).trans Nat.lt_two_pow_self.le
      exact h1.trans (mul_le_pow hu1 (by omega) h2)
    calc _ ≤ _ := hle
      _ ≤ 2 ^ 4 * scale c u := h9
      _ = 2 ^ (4 + (2 * c + 2) * (u + 2)) := by rw [scale, ← pow_add]
      _ ≤ ansBound (L + A + 1) lam n := Nat.pow_le_pow_right (by norm_num) hexp

/-- The calculator halts at every question, of every dimension. -/
theorem lenIntroC_lenTotal (c lam n dim : ℕ) : LenTotal (lenIntroC c lam) n dim :=
  fun x _ κ => ⟨_, lenIntroC_lenIs c lam n x κ⟩

/-! ## At the constant of `Introspection.seven` -/

/-- **The answer-length calculator `L^intro_λ`** of the tailored presentation of
`Introspection.seven`. -/
def lenIntro (lam : ℕ) : Decider := lenIntroC sevenConstant lam

/-- Its program from `λ`, in polynomial time. -/
def lenIntroProg : PolyTimeFun ℕ Prog := lenProgF sevenConstant

theorem lenIntroProg_eq (lam : ℕ) : lenIntroProg lam = (lenIntro lam).prog :=
  lenProgF_eq sevenConstant lam

/-- **Correctness**: at positive `λ` and `n`, at every detyped question, the presented lengths
of the label the question decodes to (`0` when it does not decode). -/
theorem lenIntro_lenIs {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) {s : ℕ}
    (q : Coord Label (Fin s) → 𝔽₂) (κ : Bool) :
    LenIs (lenIntro lam) n (toBits (DeciderProgram.vectorEquiv s q)) κ
      (((typeOf E q).map (introLen sevenConstant lam n κ)).getD 0) :=
  lenIntroC_lenIs_question sevenConstant hl hn q κ

/-- At `λ = 0` or `n = 0`, the calculator outputs `0` everywhere. -/
theorem lenIntro_lenIs_zero {lam n : ℕ} (h : lam = 0 ∨ n = 0) (x : BitStr) (κ : Bool) :
    LenIs (lenIntro lam) n x κ 0 := by
  have := lenIntroC_lenIs sevenConstant lam n x κ
  rwa [lenAt, if_pos h] at this

/-- **The costs**, in the shape of `Introspection.budget`. -/
theorem lenIntro_budget : ∃ C : ℕ, ∀ lam n : ℕ,
    (lenIntro lam).TimeBoundAt n (Introspection.budget C lam n).D (Introspection.budget C lam n).k ∧
      LenBound (lenIntro lam) n (Introspection.budget C lam n).B :=
  lenIntroC_budget one_le_sevenConstant

/-- The calculator halts at every question. -/
theorem lenIntro_lenTotal (lam n dim : ℕ) : LenTotal (lenIntro lam) n dim :=
  lenIntroC_lenTotal sevenConstant lam n dim

end MIPRE.Tailored.Intro.LenIntro

end
