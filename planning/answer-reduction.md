# Answer reduction: the construction (AR-3)

Status 2026-09-23. **Done: AR-3a, AR-3b, AR-3c** (the mathematics of the construction):
`Background/LIDT/Presentation.lean`, `Background/AnswerReduction/{PcpPresentation,Predicate,
Family,AnswerFormat,TypedGame}.lean`, `Foundations/CL/Product.lean`. One thing met on the way:
with the 54 types, the kernel unfolds `Finset.univ` of the type pairs when checking the type
graph's nonemptiness, so that one declaration raises `maxRecDepth` locally.

**Done: AR-3d without its running time** (`lem:ar-typed-sampler`): the typed answer-reduced
sampler `AnswerReduction.typedSampler`, correct on every query, with its program computed from
the input sampler's and `(λ, μ, σ)`. Findings on the way:

* **The test's selector is not computable.** `LIDT.CL.chi` numbers `F_q` by
  `Fintype.equivFin`. The presentation now takes any selector with blocks of size `q/n` together
  with a seed permutation carrying it to `chi` (`LIDT.CL.Sel`); the program uses the seed's high
  bits (`powSel`), as the introspection sampler does, and the permutation lives only in the
  analysis.
* **The parameters need a loop.** `Q = (λn + 1)^μ` with `μ` in binary is not a polynomial-time
  function of `(λ, μ, n)`, so the PCP parameters come from a routine (`parProg`) of `whileProg`
  loops (`Foundations/Cost/While.lean`, `Foundations/Pipeline/UnaryArith.lean`), run before the
  router. The contract only bounds the program's time at each index, so this is allowed.
* **The sampler is a generic product.** `CL.TypedSampler.prodDirect` (Foundations) combines any
  typed sampler with a `CL.DirectSampler`, answered by a polynomial-time function of per-index
  parameters, with one call to the former. The PCP coordinates are laid out in three runs (the
  sixth copy's point register, its direction register, the seeds), so every copy is a
  contiguous run and one set of list programs serves all six.

The running time of the sampler moves to AR-3f, with the decider's.

**Done: AR-3e without its running time** (`lem:ar-typed-decider`): the typed answer-reduced
decider `AnswerReduction.typedDecider`, total (`total`), with acceptance law exactly
`typedPred` at the game check (`accepts_iff`). The pieces are `DecideSpec.lean` (the decision on
`k`-bit blocks, `verdictB_eq`), `DecideProg.lean` (its programs) and `ArDecider.lean` (the eight
stages). Findings on the way:

* **No clock.** Unlike O4, the decider never runs the input decider: its program only enters the
  PCP verifier's input as data. The input sampler halts on every input, the parses are total, and
  the PCP verifier is run on the encoding of a genuine `PcpInput`, so every stage halts and
  `Accepts ↔ typedPred` holds by determinism, with no budget hypothesis.
* **Only point-against-line is ever tested.** Steps 3 and 4 of `fig:decider-pcp` call the
  seeded test's decision only on a `Point` question against a line question of the same copy, so
  `D^ld` reduces to the introspection line-versus-point program on the line the question
  describes (`ldB_aline`, `ldB_dline`). The questions' seeds enter only through the selector
  `χ`, and `chi (π s) = χ s`, so the non-computable seed permutation never reaches the program.
* **The five steps are planned by the types.** Each side asks for at most one comparison of
  answer blocks, one low-degree subtest and one game check; which ones is a function of the 54 ×
  54 type pairs (`eqPlan`, `ldPlan`, `chkPlan`), computed by a finite table, and `sideB_eq` is
  one case per role pair.
* **For AR-4: the check reads the Shoup bits.** `gameCheck` hands the PCP verifier the view in
  the Shoup representation `shoupBinField`, while `PcpDecider.completeness` is stated for its own
  field `PD.fld k`. Completeness needs the two representations to agree, or a hypothesis saying
  so; this is to be settled at the start of AR-4.

AR-3f is next: the running times, detyping, and the `AnswerReduction` contract.

Written after reading the paper's `ld_compiler.tex` (`sec:ar-params`,
`sec:ar-verifier`, `fig:decider-pcp`, `thm:ar` and the complexity part of its proof), ledger node
`1.3.4.1` and `1.3.4.12`, the blueprint's `lem:ar-construction`, `lem:ar-sampler-independence`,
`lem:typed-downsize`, `lem:lidt-effective`, and the precedent `planning/oracularization.md`. It was
written before any AR-3 Lean. Tracked by issue #198 (AR-3). AR-1 and AR-2 are done
(`formalization-plan.md`).

## What the construction is

The typed answer-reduced verifier `V̂^ar = (Ŝ^ar, D̂^ar)` of `sec:ar-verifier`, then detyped.

* **Types** `T^ar = Role × T^pcp`, where `T^pcp = {Point_i, ALine_i, DLine_i : i = 1..6}` has 18
  elements. So there are 54 types, on the complete type graph with loops (the product of two
  complete graphs).
* **The PCP sampler** `Ŝ^pcp` is over `F_q`, with `q = 2^k` from `pcpparams(n, T, Q, σ)`. Its
  ambient space is
  `V^pcp = ⊕_{i≤5} (V_{i,pt} ⊕ V_{i,coord} ⊕ V_{i,dir}) ⊕ V_{aux,pt} ⊕ V_{6,coord} ⊕ V_{aux,dir}`.
  * `V_{i,pt}` and `V_{i,dir}` are `F^m`, each `V_{·,coord}` is `F`, and the aux registers are
    `F^{5+s}`. The dimension is `10m + 2s + 16`.
  * Copy `i ≤ 5` is the seeded CL low-degree test on its own three registers, with `m`
    variables.
  * Copy 6 is the test with `m' = 5m + 5 + s` variables. Its point and direction registers are
    the *concatenations* `V_{6,pt} = ⊕_{i≤5} V_{i,pt} ⊕ V_{aux,pt}` (likewise for `dir`), and its
    seed is `V_{6,coord}`.
  * The overlap is the point of the construction: the `i`-th block of the `Point_6` question `z`
    is the `Point_i` question, which is what the consistency subtests compare.
* **The combined sampler** is the direct sum of the typed oracle sampler (O3,
  `Foundations/OracularSampler.lean`, over `𝔽₂`, `ℓ` levels) and the coordinate *downsizing* of
  `Ŝ^pcp` to `𝔽₂` (3 levels). It has `max(ℓ, 3)` levels, hence `max(ℓ + 2, 5)` after detyping.
* **The decider** is `fig:decider-pcp`: a format preamble (Table `tpcp`, with length bounds),
  then five steps.
  1. Global equality on equal types.
  2. Input consistency `α_v = α'_v` on (oracle, `v`) × (`Point_6`, `Point_v`).
  3. Input low-degree test `D^ld_{(q,m,d,1)}` on (`v`, `v`) × (`Point_v`, line_v).
  4. On (oracle, oracle): consistency `α_i = α'_i` for `i = 3, 4, 5`; the individual test
     `D^ld_{(q,m,d,1)}` for `i = 3, 4, 5`; and the simultaneous test `D^ld_{(q,m',d,m'+6)}` on
     copy 6.
  5. The game check: on an oracle `Point_6` question, `pcpverifier` at
     `(D, n, T, Q, σ, L^A(x_Q), L^B(x_Q))` with the view `(z, a)`.

  It runs in timeout-counter form.

## What exists

* **The oracle side, complete.** O2–O4: `Verifier.oracleTypedPred`, the typed oracle sampler with
  its programs and costs, the typed decider program and its running time, and the contract
  (`Foundations/Pipeline/Oracularization.lean`). The oracle roles, `parseAns`, `pairEnc` and
  `pairDec` are reused directly: the `Role` component of an AR type is exactly an O2 role.
* **The detyping compiler, complete.** `CL.Detyping.DeciderProgram.verifier E S D C` takes a
  `TypedSampler ℓ T`, a total `TypedDecider T` and a `CutoffProgram`. It provides completeness,
  same-state soundness at `16^|T|`, and cost and answer-cut transfer.
* **The PCP, complete.** `SAT.PcpDecider`, inhabited by `TM.CookLevin.Pad.classicalPcpDecider`:
  * `verify` is a `PolyTimeFun` with a time bound;
  * `params` comes with a program for them;
  * the field is `shoupAdmissibleField k`, a `BinField` whose `toBits` is additive (the xor
    lemma in `SAT/NormalElementProg.lean`), so its bits are coordinates in a polynomial basis;
  * `m ∣ q` and `m' ∣ q`, both powers of two.
* **The low-degree test, mathematically.** `LIDT.CL.clGame` (the question law, `Sample.question`,
  `accepts`) and its soundness at every `ldc` (AR-2, `LIDT.Simul.clSoundness`).
* **A seeded-line CL presentation, for the Pauli game.** `QLD.PauliCL.presentation`
  (`Background/QLD/CLPresentation.lean`) is a three-level presentation, with seed, then direction,
  then point and scalar registers, whose full evaluation is `Sample.question`
  (`questionOfVector_presentation`). The introspection sampler downsizes it with a self-dual basis
  and runs it by Shoup field programs (`Foundations/Introspection/PauliStageProg.lean` and
  neighbours). The PCP sampler is the same shape with six copies and an overlap. The
  presentation's pattern transfers, but its coordinate type is Pauli-specific (two point
  registers, a scalar), so it is a template, not a dependency.
* **Downsizing and reindexing of CL functions.** `CL.CLFun.downsize`, `CL.CLFun.reindex`, and
  `clDist_downsize` (`Foundations/CL/Downsize.lean`). There is no *typed sampler* downsizing
  (`lem:typed-downsize`); the introspection sampler presents its downsized functions directly,
  and so will this one.

## Findings before Lean

**1. The coordinates the sampler emits must be the ones the PCP verifier reads.** `pcpverifier`
reads `z` and the evaluations as lists of `fld.toBits` blocks (`SAT.PcpInput`). The downsized
sampler emits `𝔽₂`-coordinates in *some* basis of `F_q`, and the paper leaves the basis to
`lem:self-dual-basis`. Nothing in the PCP needs self-duality: that is for the Pauli trace form.
So take the downsizing basis to be the Shoup polynomial basis whose coordinates *are*
`fld.toBits`. The xor lemma makes that a basis. Then questions need no conversion before the
`pcpverifier` call, and answers are read by `fld.ofBits` with no change of basis. The AR sampler
does not have to go through the self-dual coordinates the introspection sampler uses.

**2. Levels.** The direct sum needs both summands at `max(ℓ, 3)` levels. That means a
level-extension of CL functions (append trivial levels, the `trivialOn` of O2) with `ExactlyOn`
and evaluation preserved. It also needs the direct sum of two CL functions on disjoint registers
at a common level count (R2's `k`-fold direct sum is the pattern).

**3. The consistency tests compare *field* answers across copies.** Step 2 compares the oracle's
`α'_v` with an isolated player's `α_v`, and step 4a compares `α_i` with `α'_i`. Both are
components of `F_q`-valued answers, parsed from bits. The format preamble must parse every answer
of every type, including those no step reads (the paper's round-12 note). Otherwise the honest
strategy is unconstrained there and completeness has no literal referent.

**4. The game check reads the oracle's question twice.** `L^A(x_Q)` and `L^B(x_Q)` are CL
evaluations of the *input* sampler inside the decider. O4's decider already does this, through
the sampler program, and its cost is what O4's runtime bound accounts for. AR-3's decider reuses
that call path.

## The pieces

**AR-3a: the PCP presentation over `F_q`** (pure mathematics).
* The coordinate type `PcpCoord m s`, with blocks ordered to match `SAT.PcpParams.block`, and
  `PcpTy = Fin 6 × LIDT.CL.Ty`.
* The 18 three-level presentations, with `ExactlyOn univ`.
* The decoders `pointOf` / `questionOf`, sending copy `i ≤ 5` to a `LIDT.CL.Question F m` and
  copy 6 to a `LIDT.CL.Question F m'`. Their full evaluations are `Sample.question` of the
  copy's sample.
* The overlap lemma: block `i` of the `Point_6` point is the `Point_i` point.
* Question laws: every type pair's law is the push-forward of the uniform content, and for the
  pairs the decider tests it is the corresponding `clGame` law. This is the input to AR-4 and
  AR-5.

**AR-3b: the typed answer-reduced game and predicate** (pure mathematics).
* Answers as bit strings, parsed by type: Table `tpcp` for the PCP component, `parseAns` for the
  role.
* `arPred`: the five steps, with the LD subtests as `LIDT.CL.accepts` at `(q, m, d, 1)` and
  `(q, m', d, m' + 6)`, and the game check as `PcpDecider.verify`.
* The typed game `Detyping.typedGame` on `T^ar` over the direct-sum content. The value
  transfers are AR-4 and AR-5, not here.

**AR-3c: the binary family.**
* Downsizing along the Shoup basis (finding 1).
* Reindexing to `Fin (dim · k)`.
* Level extension and direct sum with the oracle family (finding 2).
* The CL family and dimension function of a `TypedSampler (max ℓ 3) T^ar`.
* The typed game's law as the product of the oracle law and the PCP law.

**AR-3d: the sampler program.**
* A query router over `T^ar`: oracle queries go to O3's program, and PCP queries to Shoup-field
  stage programs for the seeded lines of six copies. The introspection stage programs are the
  template.
* The dimension query calls `paramsProg`, which is `lem:typed-downsize`'s field routine: the
  sampler depends only on `(S, λ, μ, σ)`.
* Runtime `poly(TIME_S, (λn)^μ, σ)`.

**AR-3e: the decider program.**
* The format preamble.
* `D^ld` as a `PolyTimeFun`, with runtime `poly(m, d, r, log q)`: `lem:lidt-effective`.
* The `pcpverifier` call, the oracle's CL evaluations (O4's path), and the timeout counter.
* Correctness: `Accepts ↔ arPred`.
* Runtime `poly((λn)^μ, σ)`.

**AR-3f: detyping and the ambient clauses.**
* `DeciderProgram.verifier` at `max(ℓ, 3)`, with the cutoff program.
* Levels `max(ℓ + 2, 5)`, the output budget and the answer cut.
* Sampler independence (`lem:ar-sampler-independence`). It is structural: the sampler program is
  built from `S`'s program and `(λ, μ, σ)` only.

AR-3a and AR-3b are what AR-4 and AR-5 consume, and need no programs. AR-3c to AR-3f are the
complexity half, and only they test the contract's time bounds.
