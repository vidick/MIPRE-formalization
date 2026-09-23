# Answer reduction: the construction (AR-3)

Status 2026-09-23. **AR-3, AR-4 and AR-5 are done** (AR-5: see "AR-5 as formalized" below). **Done: AR-3a, AR-3b, AR-3c** (the mathematics of the construction):
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

**Done: AR-3f, and with it AR-3** (`lem:ar-construction`, `lem:ar-sampler-independence`, and
the running times of `lem:ar-typed-sampler` and `lem:ar-typed-decider`). The output is
`AnswerReduction.arVerifier`, the typed verifier through the detyping compiler at the answer cut
`32 (k + 1)(m' + 7)^2` (`Construction.lean`); its programs are polynomial-time functions of the
input programs and `(λ, μ, σ)` (`arSamplerProg`, `arCompute`, by the program builders of
`Foundations/CL/ProgBuild.lean`); and `arVerifier_within` is the contract's `within` clause.
Findings on the way:

* **Two repairs of the contract** (`Foundations/Pipeline/AnswerReduction.lean`), both weakenings,
  both recorded in `def:answer-reduction-contract`. (1) `within` assumes `|𝒮| ≤ σ` as well as
  `|𝒟| ≤ σ`: the output runs the input sampler through the universal machine, whose overhead
  grows with the program simulated; compression's `σ` now also dominates the introspective
  sampler's size (`Compress.Csig`). The paper's `thm:ar` bounds only `|𝒟|`; its Turing machines
  can hard-wire `𝒮`, the ambient programs here run it as data. (2) The output bound's argument is
  `(λn + 1)^μ + σ + λ + n`: the added terms change nothing for `λ, μ ≥ 1` and `n ≥ 2`, the
  paper's regime, and they let the construction read `n` and `λ` at every index, so no special
  case at `λ = 0`, `μ = 0` or `n ≤ 1` is needed. Compression's `β` absorbs them.
* **A new hypothesis on the PCP decider**: its parameters `k, m, s` are polynomial in
  `(log n, log T, Q, σ)` (`ParamsBound`), as the paper's `pcpparams` are. The decider reads `k`
  and `m'` in unary, so this is what makes its time polynomial. It must be proved for the classical
  PCP decider before the `AnswerReduction` instance is assembled.
* **The accounting is `PDom`** (`Foundations/Pipeline/PowDom.lean`): bounds
  `(c (W + 1)^m X^e)^{μ + 1}`, closed under sums, products, fixed polynomials and one call to a
  degree-`μ` sampler on a query below an *unpowered* monomial (`ofCall`). Every call to the input
  sampler is on such a query: the oracularized sampler's forwarded query is linear in the typed
  query, and the typed decider's marginal queries are the oracle halves of questions, of length
  the input sampler's dimension once detyping has checked the question lengths. The unary loops'
  times are polynomial in the values they count (`toUnaryProg_time`, `powProg_time`).

**Done: AR-4, completeness** (`lem:ar-completeness`): `arVerifier_completeness` and
`arVerifier_hasPerfectPCC` (`Complete.lean`), from the typed game's completeness
(`exists_typedGame_perfectPCC`, `TypedComplete.lean`) and the combinatorial core
(`accepts_honestAns`, `Honest.lean`). The honest strategy is the oracularized game's honest
strategy read through the question map that keeps a question's role and oracle half, and answered
by a question-dependent classical post-processing (`SyncStrategy.pushQ`,
`Foundations/SyncPushQ.lean`): an oracle holds the PCP proof of its pair, an isolated player the
low-degree encoding of its answer at its own copy, and each answers the low-degree questions
honestly (`LIDT.CL.honest`, `Background/LIDT/CLHonest.lean`). Findings on the way:

* **The contract's completeness was false at `λ = 0` or `μ = 0`.** The PCP's validity asks
  `2 log n ≤ T`, and `T = 2^{(Q + 5)(μ + 1)}` with `Q = (λn + 1)^μ` is then a constant. The clause
  now asks `λ, μ ≥ 1`, the paper's regime; compression's `μ` comes from the margin claim called
  with `C + 1` (`Compress.one_le_mu`). A weakening.
* **The PCP's field must be the Shoup field** (`ShoupField`): the game check hands the PCP
  verifier the view in the Shoup representation, and `PcpDecider.completeness` is stated in the
  decider's own field. A second hypothesis on the PCP decider beside `ParamsBound`, to be
  discharged when the classical decider is plugged in (`shoupAdmissibleField` is the natural
  choice).
* **No truncation is needed.** `lem:oracle-timeout-pcc` coarse-grains the input strategy by
  prefix truncation so that the decider's answers fit its timeout. In the ambient form the input
  is already read at the answer cut `2^Q`, and an input within its budget runs within
  `2^Q (|d| + 1)^μ ≤ T` on every input, so an accepted pair is accepted within `T` by determinism
  (`acceptsWithin_of_accepts`).
* **The decider re-derives the base point.** It reads the sample off a question vector and
  recomputes the canonical base point; the presentation outputs an already canonical one, and the
  canonical map is a projection, so the two agree (`Regs.sampleOf_eval_question`).

AR-5 (soundness) is next.

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

## AR-5: soundness, the plan

Written after reading the paper's soundness proof (`ld_compiler.tex`, `sec:ar-soundness`: claims
`claim:ar-1` to `claim:ar-5`, `lem:ar-ar`, `lem:ar-ora` and the error computation) and the Lean
that exists for it. The target is the contract's `soundness` clause for `arVerifier`, with
`δ(ε, n) = σ^a((λn)^{μa} ε^b + (λn)^{-μb})` for universal `a, b`.

### The chain

1. **Detyping** (exists): a strategy of value `≥ 1 - ε` for the output game at the answer cut
   gives a typed strategy of value `≥ 1 - Kε`, `K = 16^{54}`, on the same state
   (`CL.Detyping.DeciderProgram.restrictAmbient_value_ge`), for the typed game with the
   decider's predicate, which is `typedPred` at the cut (`typedPredicate_eq`).
2. **No symmetrization.** The paper symmetrizes so that one family serves both players. The
   Lean keeps the two families `MA, MB` of a `TensorProductStrategy`: every relation the paper
   derives for `M ⊗ I` versus `I ⊗ M` is derived for `MA` against `MB` and for `MB` against
   `MA`, each from the ordered type pair that carries it (the type graph is complete, so both
   orders are sampled). Projectivity comes from a Naimark dilation (`Foundations/Dilation`)
   applied once, before anything else.
3. **Conditioning** (`claim:ar-1` to `claim:ar-4`): the typed game samples a uniform ordered
   pair of the 54 types and a uniform seed, so the failure conditioned on a type pair is at most
   `54² θ`. Each subtest is a set of type pairs; the per-seed failure is then averaged. The
   engine is `CrossConsistency.lean` (`condFail`, `sum_mul_condFail_le`).
4. **Copy isolation** (the per-seed low-degree games): for a seed `x` of the input sampler and a
   copy of the test, the AR strategy restricted to that copy's nine type pairs, at roles
   `(v, v)` or `(oracle, oracle)` and oracle half `x`, is a strategy for `clGame` of the copy's
   parameters. Two facts make this exact:
   * the presentation's output is supported on the copy's own registers and is a bijective
     function of the copy's sample (`Regs.sampleOf_eval_question` and its converse), so the CL
     question determines the AR question;
   * uniform content gives a uniform sample (`Regs.sum_sampleOf`), so the distributions agree;
   and the AR predicate on those pairs implies `CL.accepts` of the parsed answers (format
   preamble, step 1 for equal types, steps 3 and 4 for point against line).
   Answers are pushed forward along `parse` then `ans1`/`ans6`, a question-dependent map.
5. **Extraction** (`claim:ar-3`, `claim:ar-4`): `LIDT.Simul.clSoundness` per seed, with the
   measurements chosen by `Classical.choose`; the errors `deltaSim q m d r ε_x` are averaged over
   seeds by concavity of `ε ↦ ε^{clB}` (Jensen).
6. **Cross relations** (`claim:ar-2`, the first item of `claim:ar-4`, and the input side of
   `claim:ar-5`): consistency of the oracle's `Point_6` block with an isolated player's `Point_v`
   and with the copy-`i` point, chained with the extraction's relations into the sandwich
   lemma's hypothesis (`one_sub_sum_bornProb_ldSandwich_le`, `k = 6`, index = the full seed).
7. **The sandwich** (`claim:ar-5`): `Λ`, the giant sandwich of the five `G`'s around `J`'s
   constraint marginal; conclusion `Λ` consistent with `J` at a uniform point.
8. **Decoding** (`lem:ar-ar`, `lem:ar-ora`): the typed oracularized strategy measures `Λ` (an
   oracle) or `G_v` (an isolated player) and answers the decoded strings. No truncation is
   needed: the PCP's soundness gives accepted answers of length at most `T`, and an input within
   its budget rejects answers longer than `2^Q` (`RejectsLong`), so accepted answers already fit
   the input's answer alphabet. The game check goes through the PCP's soundness at `p = 1/2`.
   Then `Verifier.valStar_ge_of_typed` (oracularization soundness, one square root).
9. **Error assembly** (`lem:ar-error-assembly`): explicit, with `clA`, `clB`, `simA`.

### New hypothesis on the PCP decider

The LDT error has a field term `q^{-clB}` with prefactor `simA (7 m'(m' + 6))^{simA}`, which must
be at most `1/Q` for the error to have the contract's shape. `thm:pcp-decider` deliberately does
not carry the paper's lower bound on `q` (`eq:pcp-q-choice`); AR-5 states it as a hypothesis on
the decider (`FieldLarge`), beside `ParamsBound` and `ShoupField`, and AR-6 must make the
classical decider's `pcpParams` choose `k` large enough.

### Pieces

* **AR-5a** detyping and conditioning at the typed game; the soundness statement as a target.
* **AR-5b** copy isolation: the per-seed CL strategies and their values.
* **AR-5c** extraction and averaging.
* **AR-5d** cross relations and the sandwich hypothesis.
* **AR-5e** the sandwich and the decoded oracularized strategy's value.
* **AR-5f** error assembly, the contract clause, blueprint.

### AR-5 as formalized: no sandwich

Steps 1 to 6 are as planned (`SoundSetup`, `SoundIsolate`, `SoundExtract`, `SoundRelations`), with
one family of extracted measurements per player (`GA1`, `GB1` for copies 1 to 5, `JA`, `JB` for
the sixth) rather than a common one. Steps 7 and 8 changed: there is no sandwich.

* **The oracle measures `J`.** The decoded strategy (`SoundDecoded`, `MAo`, `MBo`) answers an
  oracle question with the pair decoded from the first two components of `J`'s outcome read on
  their blocks, and an isolated question with the decoded outcome of that copy's `G`.
* **Block locality by Schwartz--Zippel** (`SoundPoly`). The `i`-th component of `J`'s outcome
  agrees at a uniform point of the sixth copy with the placement on block `i` (`liftBlk`) of the
  other player's `G_i` outcome, except with probability `11 (E_6 + 2916 theta + E_1)` (the chains
  of `SoundRelations`); two distinct individual-degree-7 polynomials agree there with probability
  at most `m' d / q`. So `J`'s outcome equals the placed `G_i` outcome, hence is placed on its
  blocks, except with probability `errD` (`disPolyA_le`, `sum_disPolyA_le`).
* **The game check** (`SoundGameCheck`, `gcA_le`). An oracle's decoded pair fails the game check
  only if `J`'s outcome is not placed on its blocks, or the PCP check rejects its evaluations at
  half the points (`PcpSound`, the contrapositive of the PCP's soundness, discharged in `SoundPcp`
  with the decoder `decAns` and the PCP proof `pcpOf` an outcome carries). The rejected weight is
  at most twice the sixth copy's point-subtest failure.
* **Nine pairs of roles** (`condFail_OO_le` ... `condFail_ba_le`), summed over the seed:
  `1 - povmValue <= 6 errD` (`one_sub_povmValue_decoded_le`). A Naimark dilation makes it a
  `TensorProductStrategy`, and `Verifier.valStar_ge_of_typed` gives
  `val*(V_n) >= 1 - 24 sqrt(7 errD)` (`valStar_ge_decoded`).
* **Error assembly** (`SoundError`, `SoundFinal`). With `theta <= 16^{54} eps`,
  `errD <= 39204 K Z^{3A} eps^{clB} + (Q+1)^{-2} + 22 Z^{3A} 2^{-clB Q}`, `Z = 8 (Q + 1) m'`,
  `A = ceil(simA)` (`errE_le`), using `FieldLarge` for both field terms and `m >= Q` (from
  `2^m >= 2T`) for the last. `ParamsBound` gives `Z <= zC (Q sigma)^{zE}` (`z_le`), and
  `sqrt_le_delta` compares with `delta` for `n` past a threshold (`exists_threshold_clB`). At
  `mu = 0` or `eps >= 1` the loss is at least `1`.

The sandwich lemma (AR-1, `lem:ar-sandwich-support`) is therefore not consumed by soundness. It
stays, as the paper's statement. What the sandwich bought in the paper --- a single measurement
consistent with every `G_i` --- is here `J` itself, which the simultaneous test already provides.

`FieldLarge` is new: the prefactor of the field term `q^{-clB}` is `simA (7 m' (m'+6))^{simA}`, so
`q` must be at least a fixed power of `m'` and `Q`, a power of about `80000 simA`. The constants are
irreducible definitions (`simAN = ceil(simA)`, `fieldExp`), never evaluated. AR-6 must choose the
classical decider's `k` at least `fieldExp * size (8 (Q + 1) m')`, still logarithmic.
