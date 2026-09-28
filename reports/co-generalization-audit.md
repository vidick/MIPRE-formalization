# Audit: can the stage analyses be generalized to the commuting-operator model?

**Date: 2026-09-28. Tree: `main` at `7772312` (#236) plus the value-model layer of #239.**

The question, from `planning/mipco-track.md`: to prove `MIP^co = coRE` (Lin, arXiv:2510.07162)
the four stage analyses of compression — introspection, answer reduction, oracularization and
parallel repetition — need a soundness clause in the commuting-operator value `ω_co`. The
maintainer's requirement is that this be done **by generalizing the existing Lean, not by
writing it a second time**. This report records where the existing soundness proofs use
finite dimension essentially, where they only use facts that hold on any Hilbert space with
two commuting families of measurements, and what a generalization would have to replace. It
is the basis of Phases 1–6 of the plan.

Four read-only audits were run, one per stage (the fourth covering oracularization, repetition
and the composition together), each reading the soundness chain from the stage's `soundness`
field down to the vendored theorems, classifying every module reached, and listing the
finite-dimensional mechanisms with the line where each enters. Their classification:

* **A** — model-independent: programs, samplers, deciders, layouts, costs, real arithmetic,
  classical PCP and polynomial facts. Nothing to generalize.
* **B** — written against matrices, but using only what a Hilbert space with a unit vector
  and two commuting families of measurements provides: Born rule, positivity, Cauchy–Schwarz,
  `∑ F†F ≤ 1`, projectivity, commutation of the two sides. Generalizes by *restating* the
  carrier; the proofs re-run.
* **C** — essentially finite-dimensional: either in the fact used (basis completion, rank
  counting, purification, joint diagonalization, semidefinite duality, matrix Chernoff) or in
  the encoding (`Fin dA` registers, Kronecker vocabulary in a statement type).

Line counts are `wc -l`; classification is by module docstring, statement reading and a token
census of the five mechanisms, with the load-bearing files read in full and the rest not. The
four audits overlap on the shared `MIPRE/Foundations/*.lean` operator calculus, so their totals
do not add.

## 1. Short answer

**Nothing in the project's own Lean makes the generalization impossible; one vendored theorem
does, and it is exactly the one Lin's paper is thinnest on.**

1. All four stage interfaces state soundness in `Verifier.valStar` and completeness in
   `HasPerfectPCC`, and mention no strategy otherwise. The composition
   (`Pipeline.output_valStar_le`, `Compress.lean`) uses exactly one value-specific lemma,
   `Within.valStar_eq` (the value does not depend on the answer bound once long answers are
   rejected). With #239 that lemma is `Verifier.val_eq_of_rejects ω`, so the composition is
   generic in the value model as soon as the three stage clauses are.
2. The analytic cores of the four stages are, in the project's own code, **bipartite and
   vector-state**: a unit vector `ψ` on `ℂ^{dA} ⊗ ℂ^{dB}`, Alice's operators as `X ⊗ₖ 1`,
   Bob's as `1 ⊗ₖ Y`, estimates in `‖(M ⊗ 1)ψ‖`. They never use the tracial state, the
   synchronous value or maximal entanglement (those appear only in completeness and in the
   unused synchronous twin `OracularSound.lean`). So the natural common model is **a Hilbert
   space with a unit vector and two commuting families of projective measurements**, of which
   a tensor-product strategy is an instance (`TensorProductStrategy.toCommuting` exists) and
   which reaches the full `ω_co` (POVMs) through one dilation lemma (§4, mechanism 2).
3. Of the finite-dimensional mechanisms, all but one are either localized to a definitional
   layer, or live on a *finite ancilla* that stays finite in every model (the EPR register of
   introspection and of the Pauli basis test), or are removable by a local refactor (one use of
   de la Salle's orthogonalization). The one that is not: **the low-individual-degree test
   soundness** (`thm:lidt-cl-soundness-one`), which the project has only as the vendored,
   read-only, finite-dimensional `MIPStarRE.LDT.Test.mainFormal` (126,257 lines, spectral
   truncation, SDP duality, matrix Chernoff, SWAP symmetry throughout). Both the Pauli basis
   test and answer reduction consume it. A commuting-operator version is a new theorem.

Hence the plan (`planning/mipco-track.md` §5): generalize the operator calculus and the four
analyses over the abstract model, with the tensor case as an instance, and take the
commuting-operator LIDT soundness as the *single* hypothesis until it exists. Each phase
shrinks the hypothesis of `MIPRE.mipco_eq_core` from "the whole of `Sound .commuting`" to
that one theorem.

## 2. The interfaces and the composition (audit 4)

| structure | completeness | soundness |
|---|---|---|
| `Introspection ℓ` (`Pipeline/Introspection.lean`) | `HasPerfectPCC` | `1 - ε < (output …).valStar n … → 1 - δ ≤ V.valStar (2^n) …` |
| `AnswerReduction ℓ` (`Pipeline/AnswerReduction.lean`) | `HasPerfectPCC` | `1 - ε < (output …).valStar n … → 1 - δ ≤ V.valStar n …` |
| `Repetition ℓ` (`Pipeline/Repetition.lean`) | `HasPerfectPCC` | `V.valStar n … ≤ 1 - ε → (output …).valStar n … ≤ soundBound c ε …`, `soundBound` with `ε^13` |
| `Oracularization ℓ` (`Pipeline/Oracularization.lean`) | combinatorial fields; value transfers `typed_soundness`, `detyped_soundness` are theorems about every instance, in `valStar` |
| `GapCompression` | `HasPerfectPCC` | `valStar ≤ 1/2 → valStar ≤ 1/2`; #239: `Sound ω` |

`Margin.lean` (322 lines) is real arithmetic; `Compress.lean` outside the value chain
(lines 537–612 and 651–653) is parameter accounting; `Background/Pipeline.lean` plugs the two
supplied stages. The value chain applies the three stage clauses contrapositively and moves
between answer bounds with `Within.valStar_eq` three times. **Generic given
`val_eq_of_rejects ω` and stage clauses in `ω`.** Completeness is finite-dimensional by
definition (`HasPerfectPCC` is a `SyncStrategy`) and does not need generalizing: the nested
compressibility criterion consumes the tensor completeness in both shapes (plan §3).

## 3. Per-stage findings

### 3.1 Oracularization, repetition, composition (audit 4)

Totals, non-vendored: A ≈ 13,300 · B ≈ 5,000 · C ≈ 5,300, of which only ≈ 1,700 use a
genuinely finite-dimensional fact (purification by PSD factorization and finite Naimark in
`Repetition/Entangled.lean`, the Kronecker trace factorization of `TensorPower.lean` for
completeness, `maxEntangled`, `Fin` reindexing). The other ≈ 3,600 (`OracularTensor`,
`OpBound`, `Commutation`, `CrossConsistency`, `POVMValue`, `POVMMix`) are finite-dimensional
only in their carrier type.

* The bipartite proof `tensorSound_value_ge` (`OracularTensor.lean`) assumes nothing
  synchronous: its three consistencies are the oracularized game's own checks. Neither the
  paper's marginalization nor its commutation step, nor `thm:almost-sync` (#22/#23), nor
  `lem:tracial-le-co` (#29) is used. Those would be needed only on Lin's tracially-embeddable
  route, which the repository does not follow for oracularization.
* **The one real gap is projectivity.** `CommutingOperatorStrategy` has POVMs;
  `OracularTensor.lean` uses `IsPVM` at six places, and `oracleView_mul` (a product of two
  coarse-grainings is the coarse-graining along the pair) is false for POVMs. Either the
  abstract model is projective and `ω_co` is reached by a commutation-preserving dilation, or
  the argument is rewritten with `√E` via the continuous functional calculus. The plan takes
  the first (mechanism 2 below).
* `GameAdapt.succAt/failAt/adapt`, `Detyping.restrict := S.relabel`, `restrict_failure_le`,
  `quantumValue_typedGame_le` are relabel-and-average and transfer once the model has them.
* **Repetition needs no rounding, no density, no tracial anything**: the vendored
  `MIPRE.Repetition.commutingOperatorValue_repeat_le` is already stated in the bipartite
  `ω_co` (exponent `ε^7`, stronger than the interface's `ε^13` since `ε ≤ 1`), sorry-free and
  guarded. Missing: a `ValueModel`-generic `val_repVerifier ω` (≈ 30 lines; the
  verifier-to-game bridge `midGame`, `game_μ_eq`, `game_D_tuple` is value-independent) and an
  interface change, since `structure Repetition` carries one `soundness` in `valStar`.
* `TracialDensityHypothesis` (vendored) approximates every commuting correlation by a
  tracially embeddable one on *common* alphabets; the vendored `TraciallyEmbeddableCorrelation`
  has Alice **POVMs** in the algebra and Bob positive operators in the commutant, so density
  does not absorb the POVM question either. Not needed on the route below.

### 3.2 Answer reduction and the LIDT adapter (audit 3)

Totals: A 11,362 (plus 52,717 in the classical trees `SAT`, `LowDegree`, `CL`, `Cost`,
`TM/CookLevin`, confirmed by grep) · B ≈ 14,614 · C ≈ 2,111, of which ≈ 1,618 are on the
chain; **vendored `LIDT/MIPStarRE` 126,257, all C.**

* Every `Sound*` file mentions `Matrix` only as `Matrix (Fin T.dA) (Fin T.dA) ℂ` in types
  and `(1 : Matrix …)` in `bornProb` arguments. `SoundSetup` records that the Lean does *not*
  symmetrize; the analysis is bipartite with an arbitrary vector state.
* Finite Naimark is used **once**: `povmValue_le_quantumValue` (`SoundDecoded.lean`) dilates
  the decoded POVMs; but the decoded measurements `MAo`/`MBo` are coarse-grainings of PVMs,
  hence PVMs, so the decoded strategy can be packaged projectively and the step disappears.
* The chain enters the vendored tree through `Simul.clSoundness` (`Simultaneous.lean`) ←
  `clSoundness_ldc_one` (`Adapter/Reduction.lean`) ← `LIDT.lowIndividualDegree_soundness`
  (`LIDT/Soundness.lean`, `:= Bridge.soundness`) ← `Bridge/Main.lean` applying
  `MIPStarRE.LDT.Test.mainFormal`. The bridge packages a tensor strategy as a density
  `dim·|ψ⟩⟨ψ|` with the normalized trace (`Bridge/Strategy.lean`); the vendored statement
  quantifies over `Fintype ιA ιB` and density matrices. **What a commuting-operator version
  needs from it is a theorem of exactly the shape of `Simul.clSoundness`**: a projective
  commuting strategy passing the seeded test with probability `≥ 1 − ε` yields PVMs `GA` in
  Alice's algebra and `GB` in Bob's with the three inconsistency bounds and the error
  `deltaSim`. The five bridge files would be rewritten against it; the adapter (Reduction,
  Padding, Extraction, Simultaneous, all B) restates verbatim.
* Keyword census of the vendored proof (322 files): `sqrt`/PSD square roots in 117 files,
  Kronecker in 118, `PermInvState`/SWAP symmetry in 77, `Fintype.card` in 51, `spectral` in
  26, `eigenvalues`/`cfc` in 12; `MakingMeasurementsProjective` (10,138 lines: Naimark,
  orthogonalization, spectral truncation, SVD, rank reduction), `SelfImprovement` (20,215:
  "the paper's SDP witnesses", strong duality through `Quantum/FiniteConicDuality`),
  `Pasting/Bernoulli/MatrixChernoff` (CFC). Which of these have tracial analogues in the
  literature was not checked.

### 3.3 Introspection (audit 1)

Totals over `Foundations/Introspection` and `Background/Introspection` (42,875 lines):
A 16,365 · B 10,545 · C 9,614 on the soundness chain, plus 6,351 C in completeness
constructions that need no generalization.

The chain runs from `CompiledSoundness.output_soundness` through decoding, padding removal,
`QLDExtractionAdapter` (the `thm:qld` interface, `FieldExtraction`), `IsometricSoundness`,
`ExtractedStateSoundness`, `PrimitiveSoundness` (hypotheses: PVMs on `(ι → F) × H` and
`(ι → F) × K` against `registerState ξ` with `ξ : H × K → ℂ` **arbitrary**) and the hiding,
sampling and read rigidity inductions to `FinalExtraction.extractedStrategy`. Of 119 analytic
core files, 94 use the bipartite vector-state vocabulary and **0** the tracial one. The five
mechanisms:

1. the bipartite vector state and its norm (`stateSqNorm`, `bOp N = 1 ⊗ₖ N`, `xSqNorm`,
   `bornProb`; pervasive, definitional layer ≈ 1,755 lines): restate;
2. local isometries into `ℂ^d` with image completion and state error (the `thm:qld`
   interface, 5 + 8 Foundations files and 7 Background files): the interface theorem is
   restated in the model, not transported;
3. the EPR register and the switching trick (17 files, 2,218 lines: `registerEPR`,
   `stateVec_epr`, the mirror hypotheses `aOp P ψ = bOp R ψ`, exact by the char-2 symmetry
   `(w x)ᵀ = w x`): **lives on the concrete register factor `M_{q^n}` and survives with the
   ancilla `H`, `K` abstract** — which is exactly how the core is organized;
4. Naimark dilation against a fixed vector state (13 files, 2,057 lines; the adaptive
   induction re-projectivizes residual measurements at every stage): replaced by the
   commutation-preserving dilation lemma (mechanism 2 of §4), which keeps the ancilla vector
   fixed and gives the compression identity as an operator identity;
5. computational-basis entries, blocks and tensor-support identities on the register (21
   files, 3,180 lines): on the concrete register factor; survive.

No `finrank`, `FiniteDimensional`, eigenvalue, Schmidt or SVD use was found in either
directory; `PosSemidef` occurs as an order, not through the spectral theorem.

### 3.4 The Pauli basis test, `thm:qld` (audit 2)

Totals over the import closure of `QLD/Soundness.lean` (538 modules, 195,137 lines):
A 18,194 · B 33,048 · C 136,820, of which vendored 128,851 (`MIPStarRE` 126,257 +
`Orthogonalization` 2,594) and project-authored 7,969. Of the project-authored
operator-analytic core (≈ 42.4k lines) ≈ 32.5k is B, ≈ 4.6k C, ≈ 5.4k A. The statement is on
an unbundled bipartite POVM strategy (`ψ : dA × dB → ℂ`, `MA : Question → POVM Answer dA`),
never on `TensorProductStrategy` and never tracial.

| mechanism | where | replacement |
|---|---|---|
| M1 Naimark with unitary extension | `Dilation.lean` (basis completion, `finrank_euclideanSpace`); consumers `QLD/Soundness.lean` (`exists_legal_dilation`, before the chain), `Sandwich.lean` (joint measurement of the sandwich), `QLD/Anticomm.lean`, `LIDT/Adapter/Registers.lean` | the dilation lemma of §4 |
| M2 de la Salle orthogonalization in finite dimension | `QLD/Ortho.lean` → vendored `Orthogonalization.povm_orthogonalization_finDim`, consumed at **one** site, `QLD/Commutation.lean:587` (commuting half of `lem:qld-obs-commutation`) | the chain runs after `exists_legal_dilation`, and `swap_isometry` already takes projectivity, but `hatObs_commutation` and `comm_signed_commutation` are stated without it; with projectivity threaded through, `pairPOVM` is projective (`isPVM_povm_map`) and the corollary holds at zero cost — the dependency looks removable (inference, not built) |
| M3 the seeded LIDT soundness through the vendored proof | `QLD/PaddedLIDT.lean` → `Adapter/Registers` → … → `mainFormal` | the model hypothesis of §5; not localized |
| M4 statement shape | `∃ HA : Type, Fintype HA`, `Matrix (Anc F m × HA) dA ℂ` isometries | restate |
| M5 Kronecker vocabulary | `aOp`/`bOp`/`stateVec`/`bornProb`/`xSqNorm`/`Bnd` everywhere | restate (B) |

The EPR switching trick is **not** a players'-side mechanism here either: `stateVec_epr` and
all its uses are on the adjoined ancilla `(ℂ^q)^{⊗M}` indexed by `Anc F m`, finite in every
model. No `eigenvalues`, `spectral_theorem`, `cfc`, `PosSemidef.sqrt` or Schmidt use in any
project-authored chain file. Vendored orthogonalization tiers present: `finDim`, `B(H)`
(unconditional), II₁ factor (unconditional), general von Neumann algebra (conditional on the
unproved `MvNStructureTheory`); only the finite-dimensional tier is used.

## 4. The mechanisms, cross-cutting, and what replaces them

| # | mechanism | stages | replacement | status |
|---|---|---|---|---|
| 1 | Kronecker carrier: `Matrix (Fin dA)`, `X ⊗ₖ 1`, `1 ⊗ₖ Y`, `snorm`, `xSqNorm`, `bornProb`, `povmValue`, `condFail`, `dis`, `Bnd` | all | operators `H →L[ℂ] H` with `Commute` between the two families; the matrix layer becomes the instance `H = EuclideanSpace ℂ (Fin dA × Fin dB)` | restatement, ≈ 9–10k lines of `Foundations/*.lean` and their consumers |
| 2 | Naimark dilation with unitary extension (`Dilation.lean`, `StrategyDilation.lean`, `extVec2`), used at the top of QLD, inside the sandwich, in the introspection inductions, once in AR, and needed to make `ω_co` projective | all | **a commutation-preserving dilation on any Hilbert space**, proposed proof below | new lemma, elementary |
| 3 | EPR register and switching trick | introspection, QLD | unchanged: on a finite ancilla in every model | none |
| 4 | matrix entries, blocks, diagonal readouts on the register | introspection | unchanged: on the register factor | none |
| 5 | positivity of Born probabilities from `PosSemidef.kronecker`, Cauchy–Schwarz proved entrywise (`Closeness.lean`) | all | `⟨ψ|EF|ψ⟩ ≥ 0` for commuting positive `E`, `F` (projections need nothing; POVMs need a CFC square root); Cauchy–Schwarz from positivity | restatement |
| 6 | de la Salle orthogonalization at `QLD/Commutation.lean:587` | QLD | remove by threading projectivity (§3.4 M2) | local refactor, to verify |
| 7 | `Fin dA` register packaging (`RegisterReindex`, `Adapter/Registers`, `TensorProductStrategy.ofProjective`) | QLD, AR | disappears with an abstract carrier | deletion |
| 8 | purification and Kronecker trace factorization (`Repetition/Entangled.lean`, `TensorPower.lean`), `maxEntangled` | repetition (tensor identification, completeness) | not needed: the co side has its own vendored theorem | none |
| 9 | `HasPerfectPCC` completeness | all | not needed: the criterion consumes tensor completeness | none |
| 10 | **the vendored LIDT soundness** `mainFormal` | QLD, AR | a commuting-operator theorem of the shape of `Simul.clSoundness` | **the obstruction** |

**Proposed proof of mechanism 2**, to be checked in Lean before Phase 1 relies on it. Let
`E_a` (`a ∈ A`) be a POVM on `H` and `𝒞` a set of operators commuting with every `E_a`
(Bob's operators, or everything of Bob's and the rest of Alice's). Put `V := ∑_a √E_a ⊗ |a⟩`,
an isometry `H → H ⊗ ℂ^A` whose entries lie in the C*-algebra generated by the `E_a`, hence
commute with `𝒞` (`Commute.cfc` in Mathlib gives `Commute (cfc f a) b` from `Commute a b`;
`CFC.sqrt` with `sqrt_mul_self` gives the root). Let `w := V ⊗ ⟨a₀|`, a partial isometry on
`H ⊗ ℂ^A` with `w*w = 1 ⊗ |a₀⟩⟨a₀|`. In any unital C*-algebra a partial isometry `w` extends
to the unitary
```
U := [[ w , 1 − w w* ], [ 1 − w* w , w* ]]   on  (H ⊗ ℂ^A) ⊕ (H ⊗ ℂ^A),
```
(`U*U = UU* = 1` from `w*(1 − ww*) = 0` and `(1 − w*w)w* = 0`), and `U(ξ ⊕ 0) = wξ ⊕ 0` for
`ξ` in the initial space. Define `P_a := U*(1 ⊗ |a⟩⟨a| ⊗ 1)U`, a PVM on `H ⊗ ℂ^A ⊗ ℂ²` whose
entries lie in `M₂(M_A(C*(E)))`, so it commutes with `c ⊗ 1 ⊗ 1` for every `c ∈ 𝒞`; and its
compression to the slice `H ⊗ e_{a₀} ⊗ e₀` is `V*(1 ⊗ |a⟩⟨a|)V = √E_a √E_a = E_a` as an
operator identity, which is what every inner use (an estimate against a fixed state) needs.
For a question-indexed family, each question gets its own ancilla `ℂ^A ⊗ ℂ²` and the common
state `ψ ⊗ ⨂_x (e_{a₀} ⊗ e₀)`; the dilated Alice operators lie in `C*(E) ⊗ B(anc_A)` and the
dilated Bob operators in `C*(F) ⊗ B(anc_B)`, which commute. Finite ancillas are `ι → H` with
the `PiLp 2` structure. No von Neumann algebra theory and no comparison of projections is
needed — this is the point: the finite-dimensional proof's basis completion is replaced by a
2×2 trick, not by Murray–von Neumann equivalence. Consequences: `commutingOperatorValue G` is
the supremum over projective commuting strategies; every finite Naimark step above is the same
lemma in the abstract model.

## 5. What makes generalization impossible rather than laborious

* **The vendored LIDT theorem, and only it.** Its statement is finite-dimensional
  (`Fintype ιA ιB`, density matrices), its proof is finite-dimensional through and through
  (§3.2), the tree is read-only. A commuting-operator version cannot be obtained by changing
  bridges; it is a new theorem of the shape of `Simul.clSoundness`, to be proved for the
  abstract model — by a proof produced upstream and vendored, as the finite-dimensional one
  was, or written here. Lin's paper cites JNVWY's tensor-code soundness as "directly applied"
  to individual-degree polynomials, extended to tracially embeddable strategies by
  `Lin23` Corollary 4.4, and the appendix proving the simultaneous version is commented out
  in the source (plan §5, Phase 6). Density is no way around it: it approximates commuting
  correlations by tracially embeddable ones, which are still infinite-dimensional, and
  approximation by finite-dimensional strategies is exactly what fails.
* **A decision, not a blocker: which abstract model.** The analyses are bipartite with an
  arbitrary vector state and two families, never symmetrized and never tracial. Their direct
  generalization is the projective commuting-operator model, in which the tensor value is the
  instance `H = ℂ^{dA} ⊗ ℂ^{dB}` and `ω_co` is reached by mechanism 2. A single proof over a
  tracial `(𝒜, τ)` serving the synchronous `commValue` would additionally need
  symmetrization, synchronicity of every verifier game (no `IsSynchronousAt` lemma exists for
  the answer-reduction verifier), `thm:almost-sync` (#22/#23) and `lem:tracial-le-co` (#29),
  and would land in a value nothing in the co track uses. The repository's own precedent is
  two proofs (`OracularSound.lean` synchronous, `OracularTensor.lean` bipartite); the plan
  keeps the bipartite one and retires nothing of the synchronous one.
* **Infrastructure that does not exist yet, and is not needed on this route:** the standard
  form `L²(𝒜, τ)`, modular conjugation, commutant as the opposite algebra. Mathlib has GNS for
  C*-algebras (`Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`, a ⋆-homomorphism into the
  bounded operators on the completion, no cyclic vector yet) and `VonNeumannAlgebra` as a
  definition; the repository has its own GNS (`Foundations/GNS.lean`, from a state on a
  ⋆-algebra to a `CommutingOperatorStrategy`) and the vendored `StdTracialAlgebra`. None is
  on the critical path of the bipartite route.
* **Positivity for non-projective effects** in the bare `TracialState` layer is projections
  only; irrelevant once the model is projective.

## 6. Two things the audits also settled

* The synchronous tracial calculus (`Closeness.lean`, `Distances.lean`, `ntr`, `hsInner`) is
  in the import closure of every stage and **used by none of the soundness chains**; it
  serves `OracularSound.lean` and the completeness constructions.
* `Sandwich.lean` and `Pasting.lean` (2,513 lines) are imported by the answer-reduction chain
  and unused by it; `Foundations/Introspection` is imported by `QLD/RegisterForm.lean` for
  five files' worth of declarations and 7,075 lines are along for the ride. Import hygiene
  will matter when the generic layer is introduced, since these are the modules that fix the
  build time of the operator calculus.

## Not checked

The bodies of the vendored proofs beyond docstrings and the keyword census; the literature
on tracial analogues of orthogonalization, self-improvement and matrix Chernoff; whether the
M2 refactor compiles; whether the introspection inductions run at the same error rates with
the dilation lemma in place of the finite one (the lemma gives the same compression identity,
so they should, but this was not traced); `Complete.lean`/`TypedComplete.lean`; the
elaboration cost of `H →L[ℂ] H` against the matrix layer, which `OpBound.lean` says it avoids
Mathlib's operator norm for; the paper (`vidick/MIPRE-proof` was not attached; Lin's paper
has no chapter there).
