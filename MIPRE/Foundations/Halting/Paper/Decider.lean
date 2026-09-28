/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Paper.TabulateL
import MIPRE.Foundations.Halting.Compressor
import MIPRE.Foundations.Cost.ManyOne
import MIPRE.Foundations.Cost.Clocked
import MIPRE.Foundations.Cost.Binary

/-!
# The halting verifier along the paper's route: the decider

Blueprint `lem:halt-construction` in the paper's form (`recursive.tex`, `fig:halt_f`), for the
polynomial-time halting reduction of `planning/polytime-halting.md`. For a machine `M` and a
parameter `λ`, the verifier is

  `Vhalt M λ = Verifier.ofSamplerDecider U (G.sampler λ) (dec M λ)`,

the compressed sampler at `λ` together with the decider `dec M λ`, wrapped in the question-length
check of `def:normal-verifier`. The decider is an efficient Kleene fixed point (`Cost.kleeneFix`)
of the map `d' ↦ hardcode body (encode (M, (λ, d')))`, so that on `(n, x, y, a, b)` it runs
`body` on the pair of its own description `(M, (λ, dec M λ))` and the input, where `body`:

1. runs `M` on the empty input for the budget `Nat.size n` (the clocked universal machine); if
   it halts, **accepts**;
2. otherwise runs the semidecider `S'` of the search branch — "`val*` at level `C₀` of the
   verifier this string describes exceeds `1/2`" (`exists_semL`) — on the description
   `descOf λ (dec M λ)`, for the budget `Nat.size n`; if it halts, **rejects**;
3. otherwise computes the compressed decider `Compress ((S^compr_λ, wrap (dec M λ)), λ)` of its
   own verifier and runs it on the input through the universal machine.

Branch 2 is Lin's search branch, which the criterion route (`Compression.lean`, `decFunV`) has
too: the value form of compression has no base case for soundness, and the search supplies it.
Branches 1 and 3 are the paper's `F`. The reading of `M`'s and the search's budgets as `Nat.size
n` rather than `n` is the criterion's, and costs nothing: the levels of the recursion are
`n, 2 ^ n, …`, along which `Nat.size` grows without bound.

`body` is the program of a polynomial-time function `prep` returning the pair "program to run,
its input" — branch 1 returns the constant-`true` program, branch 2 the constant-`false` one,
branch 3 the compressed decider on the input — followed by one call of the universal machine.
That is what makes the acceptance characterization (`accepts_iff`, blueprint
`lem:dhalt-values`) a matter of running `prep` and reading its output, and what keeps the
accounting (`Paper/Cost.lean`) to `prep`'s time bound plus the universal machine's overhead on
the compressed decider.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.Prog.ProgD Polynomial

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-! ## Three polynomial-time pieces -/

/-- The description string `descOf λ d` of a pair, as a polynomial-time function: `serProg`. -/
noncomputable def descPoly : PolyTimeFun (ℕ × Prog) BitStr where
  toFun p := descOf p.1 p.2
  code := serProg
  closed := serProg_wellScoped
  timeBound := (C 3 * X + C 2) * (C 16 * X + C 42) + (X + C 2) * (C 5 * X + C 30)
  computes p := by
    obtain ⟨lam, d⟩ := p
    obtain ⟨t, ht, h⟩ := serProg_runs (encode (lam, d))
    refine ⟨t, ?_, h⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    exact ht

@[simp] theorem descPoly_apply (lam : ℕ) (d : Prog) : descPoly (lam, d) = descOf lam d := rfl

/-- The wrapper's description, as a polynomial-time function of the sampler program and the
inner decider: `wrapBuildProg`. -/
noncomputable def wrapBuild : PolyTimeFun (Prog × Prog) Prog where
  toFun p := wrapCore U.univ p.1 (encode p.2)
  code := wrapBuildProg (encode U.univ)
  closed := wrapBuildProg_wellScoped _
  timeBound := X + C (2 * esize U.univ + wrapNodes + 3)
  computes p := by
    obtain ⟨s, d⟩ := p
    obtain ⟨t, ht, h⟩ := wrapBuildProg_runs (encode U.univ) (encode s) (encode d)
    refine ⟨t, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod]
      have e1 : (encode s : Data).size = esize s := rfl
      have e2 : (encode d : Data).size = esize d := rfl
      have e3 : (encode U.univ : Data).size = esize U.univ := rfl
      omega
    · rw [dWrapCore_eq] at h
      exact h

/-- `(λ, d) ↦ wrapCore U.univ (G.samplerProg λ) (encode d)`, the program of the wrapped decider
of the verifier `(S^compr_λ, d)`. -/
noncomputable def wrapPoly : PolyTimeFun (ℕ × Prog) Prog :=
  (wrapBuild U).comp ((G.samplerProg.comp PolyTimeFun.fst).pair PolyTimeFun.snd)

theorem wrapPoly_apply (lam : ℕ) (d : Prog) :
    wrapPoly G U (lam, d) = wrapCore U.univ (G.sampler lam).prog (encode d) := by
  show wrapCore U.univ (G.samplerProg lam) (encode d) = _
  rw [G.samplerProg_eq]

/-- The pair `(n, rest)` as the datum `encode (n, rest)`: the identity program. -/
noncomputable def reencode : PolyTimeFun (ℕ × Data) Data where
  toFun p := encode p
  code := .var 0
  closed := Nat.zero_lt_one
  timeBound := X + 1
  computes p := ⟨esize p + 1, by simp, Eval.var _ _⟩

/-- The program halting with output `true` on every input. -/
def trueProg : Prog := .const (encode true)

/-- The program halting with output `false` on every input. -/
def falseProg : Prog := .const (encode false)

/-- The search program of the pair `(λ, d)`: the semidecider `S'` hard-coded to the description
`descOf λ d`, to be run on the empty input. -/
def searchP (S' : Prog) (lam : ℕ) (d : Prog) : Prog :=
  hardcode (Prog.onLeft S') (encode (descOf lam d))

theorem halts_searchP_iff {S' : Prog} (hS' : S'.WellScoped 1) (lam : ℕ) (d : Prog) :
    Halts (searchP S' lam d) .nil ↔ Halts S' (encode (descOf lam d)) :=
  halts_haltingReduction_iff hS' (descOf lam d)

/-! ## The preparation, and the decider -/

/-- **The three branches**, as a polynomial-time function of the description `(M, (λ, d'))` and
the input `(n, rest)`: the program to run and its input. -/
noncomputable def prep (S' : Prog) :
    PolyTimeFun ((Prog × (ℕ × Prog)) × (ℕ × Data)) (Prog × Data) :=
  PolyTimeFun.ite
    ((PolyTimeFun.haltsWithin UT).comp
      (PolyTimeFun.pair (PolyTimeFun.fst.comp PolyTimeFun.fst)
        (PolyTimeFun.fst.comp PolyTimeFun.snd)))
    (PolyTimeFun.const (trueProg, Data.nil))
    (PolyTimeFun.ite
      ((PolyTimeFun.haltsWithin UT).comp
        (PolyTimeFun.pair
          ((haltingReduction S').comp (descPoly.comp
            (PolyTimeFun.pair ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)
              ((PolyTimeFun.snd.comp PolyTimeFun.snd).comp PolyTimeFun.fst))))
          (PolyTimeFun.fst.comp PolyTimeFun.snd)))
      (PolyTimeFun.const (falseProg, Data.nil))
      (PolyTimeFun.pair
        (G.compress.comp (PolyTimeFun.pair
          (PolyTimeFun.pair
            (G.samplerProg.comp ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst))
            ((wrapPoly G U).comp
              (PolyTimeFun.pair ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)
                ((PolyTimeFun.snd.comp PolyTimeFun.snd).comp PolyTimeFun.fst))))
          ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)))
        (reencode.comp PolyTimeFun.snd)))

/-- The compressed decider of the verifier `(S^compr_λ, wrap d)`. -/
noncomputable def comprDec (lam : ℕ) (d : Prog) : Prog :=
  G.compress ((G.samplerProg lam, wrapCore U.univ (G.samplerProg lam) (encode d)), lam)

theorem prep_apply (S' M : Prog) (lam : ℕ) (d : Prog) (n : ℕ) (rest : Data) :
    prep G U UT S' ((M, (lam, d)), (n, rest)) =
      if (evalWithin M .nil (Nat.size n)).isSome then (trueProg, Data.nil)
      else if (evalWithin (searchP S' lam d) .nil (Nat.size n)).isSome then (falseProg, Data.nil)
      else (comprDec G U lam d, encode (n, rest)) := rfl

/-- **The body of the decider**: run `prep`, then the universal machine on its output. -/
noncomputable def body (S' : Prog) : Prog := .let_ (prep G U UT S').code (callVar 0 U.univ)

theorem body_wellScoped (S' : Prog) : (body G U UT S').WellScoped 1 :=
  ⟨(prep G U UT S').closed, callVar_wellScoped (by decide) U.closed⟩

/-- The map whose fixed point is the decider: `d' ↦ hardcode body (encode (M, (λ, d')))`. -/
noncomputable def F (S' M : Prog) (lam : ℕ) : PolyTimeFun Prog Prog :=
  (PolyTimeFun.smn (Prog × (ℕ × Prog))).comp
    (PolyTimeFun.pair (PolyTimeFun.const (body G U UT S'))
      (PolyTimeFun.pair (PolyTimeFun.const M)
        (PolyTimeFun.pair (PolyTimeFun.const lam) (PolyTimeFun.id Prog))))

theorem F_apply (S' M : Prog) (lam : ℕ) (d : Prog) :
    F G U UT S' M lam d = hardcode (body G U UT S') (encode (M, (lam, d))) := rfl

/-- **The decider `𝒟^halt`** of the machine `M` at the parameter `λ`: the efficient Kleene fixed
point of `F`. -/
noncomputable def dec (S' M : Prog) (lam : ℕ) : Prog := kleeneFix U (F G U UT S' M lam)

theorem dec_wellScoped (S' M : Prog) (lam : ℕ) : (dec G U UT S' M lam).WellScoped 1 :=
  kleeneFix_wellScoped U _

/-- **The verifier `𝒱^halt`** of the machine `M` at the parameter `λ`. -/
noncomputable def Vhalt (S' M : Prog) (lam : ℕ) : Verifier 7 :=
  Verifier.ofSamplerDecider U (G.sampler lam) (dec G U UT S' M lam)

theorem Vhalt_eq_Vof (S' M : Prog) (lam : ℕ) :
    Vhalt G U UT S' M lam = Vof G U (descOf lam (dec G U UT S' M lam)) :=
  (Vof_descOf G U _ _).symm

@[simp] theorem Vhalt_sampler (S' M : Prog) (lam : ℕ) :
    (Vhalt G U UT S' M lam).sampler = G.sampler lam := rfl

theorem Vhalt_decider_prog (S' M : Prog) (lam : ℕ) :
    (Vhalt G U UT S' M lam).decider.prog =
      wrapCore U.univ (G.sampler lam).prog (encode (dec G U UT S' M lam)) := rfl

/-! ## Running the decider -/

/-- A run of `body` on `(P, (n, rest))` is a run of the program `prep` returns on the input it
returns. -/
theorem body_runs_iff (S' : Prog) (P : Prog × (ℕ × Prog)) (n : ℕ) (rest r : Data) :
    (∃ t, (body G U UT S').Runs (encode (P, (n, rest))) r t) ↔
      ∃ t, (prep G U UT S' (P, (n, rest))).1.Runs (prep G U UT S' (P, (n, rest))).2 r t := by
  obtain ⟨t₀, -, e₀⟩ := (prep G U UT S').computes (P, (n, rest))
  constructor
  · rintro ⟨t, h⟩
    change Eval [encode (P, (n, rest))] (.let_ _ _) r t at h
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨rfl, -⟩ := Eval.deterministic h₁ e₀
      obtain ⟨t', -, hU⟩ := callVar_runs_rev U.closed h₂
      rw [Env.get_cons_zero] at hU
      have hU' : U.univ.Runs (.cons (encode (prep G U UT S' (P, (n, rest))).1)
          (prep G U UT S' (P, (n, rest))).2) r t' := hU
      exact U.halts_of _ _ _ _ hU'
  · rintro ⟨t, h⟩
    obtain ⟨t', -, hU⟩ := U.time_le _ _ _ t h
    have hU' : Eval [encode (prep G U UT S' (P, (n, rest)))] U.univ r t' := hU
    have h₂ := callVar_eval
      (env := [encode (prep G U UT S' (P, (n, rest))), encode (P, (n, rest))]) (i := 0)
      U.closed (v := encode (prep G U UT S' (P, (n, rest)))) (by simp) hU'
    exact ⟨_, Eval.let_ e₀ h₂⟩

/-- A run of the decider on `v` is a run of `body` on its own description and `v`. -/
theorem dec_runs_iff (S' M : Prog) (lam : ℕ) (v r : Data) :
    (∃ t, (dec G U UT S' M lam).Runs v r t) ↔
      ∃ t, (body G U UT S').Runs (.cons (encode (M, (lam, dec G U UT S' M lam))) v) r t := by
  have hw := body_wellScoped G U UT S'
  unfold dec
  rw [kleeneFix_halts_iff]
  constructor
  · rintro ⟨t, h⟩
    have h' : (hardcode (body G U UT S')
        (encode (M, (lam, kleeneFix U (F G U UT S' M lam))))).Runs v r t := h
    obtain ⟨t', -, h''⟩ := hardcode_time_rev hw h'
    exact ⟨t', h''⟩
  · rintro ⟨t, h⟩
    exact ⟨_, hardcode_time hw h⟩

/-- **Acceptance of `𝒱^halt`** (blueprint `lem:dhalt-values`): the two questions have the
sampler's dimension, and then: everything is accepted if `M` halts within `Nat.size n`; nothing
is if the search halts within `Nat.size n`; otherwise exactly what the compressed decider of
`𝒱^halt` itself accepts. -/
theorem accepts_iff (S' M : Prog) (lam n : ℕ) (x y a b : BitStr) :
    (Vhalt G U UT S' M lam).decider.Accepts n x y a b ↔
      x.length = (G.sampler lam).dim n ∧ y.length = (G.sampler lam).dim n ∧
        (if (evalWithin M .nil (Nat.size n)).isSome then True
         else if (evalWithin (searchP S' lam (dec G U UT S' M lam)) .nil (Nat.size n)).isSome
           then False
         else (G.output ((Vhalt G U UT S' M lam).sampler.prog,
           (Vhalt G U UT S' M lam).decider.prog) lam).decider.Accepts n x y a b) := by
  rw [Vhalt, Verifier.ofSamplerDecider_accepts]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [dec_runs_iff,
    show Data.cons (encode (M, (lam, dec G U UT S' M lam))) (encode (n, x, y, a, b))
      = encode ((M, (lam, dec G U UT S' M lam)), (n, (encode (x, y, a, b) : Data))) from rfl,
    body_runs_iff, prep_apply]
  split_ifs with h1 h2
  · exact ⟨fun _ => trivial, fun _ => ⟨_, Eval.const _ _⟩⟩
  · refine ⟨fun ⟨t, h⟩ => ?_, fun h => h.elim⟩
    obtain ⟨he, -⟩ := Eval.deterministic h (Eval.const [Data.nil] (encode false))
    simp [encode_bool, Data.ofBool] at he
  · rw [Decider.Accepts, G.output_decider]
    show (∃ t, (comprDec G U lam (dec G U UT S' M lam)).Runs
      (encode (n, (encode (x, y, a, b) : Data))) (encode true) t) ↔ _
    rw [comprDec, G.samplerProg_eq]
    exact Iff.rfl

end MIPRE.Halting
