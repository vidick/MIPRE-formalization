# The commuting-operator class, `MIP^co = coRE`: plan

**Status: Phase 0 done (#235, #236), made generic in #239; Phases 1–6 planned around
generalizing the existing analyses (`reports/co-generalization-audit.md`).** The conditional
theorem — `MIP^co = coRE` given the commuting-operator soundness of gap compression — is in,
with all of its plumbing, written once for both values.

Written 2026-09-28, after the explicit separation (#222) and the paper's class (#230–#233).
Target: Lin's theorem `MIP^co = coRE` (`Lin25`, arXiv:2510.07162, STOC 2026), proved by
reusing the value-form compression architecture of this repository.

Sources read: Lin's LaTeX source (supplied by the maintainer; `Seqandcompression.tex`,
`CompressionCond.tex`, `Introspection.tex`, `Answerreduction.tex`, `ARsoundnessproof.tex`,
`QRsoundnessproof.tex`, `CondLineardist.tex`, `Parallelrepetition*.tex`, `Preliminary.tex`),
the statements of `Lin23` (arXiv:2304.01940) as Lin's paper cites them, and, here,
`Foundations/Compression.lean`, `Halting/*`, `ClassMIPStarComputable.lean`, `Tsirelson/*`,
`GapCompression.lean`, `GameTransport.lean`, chapters 5, 7 and 8 of the blueprint,
`planning/repetition-port.md` (D8) and `planning/next-steps.md` (items 5 and 6). The
companion `MIPRE-proof` repository has no `coRE` chapter: for this track the authority on the
mathematics is Lin's paper, cited at its arXiv version. Nothing from Lin's source is copied
here; his statements are paraphrased only where they are formalized.

## 1. Short answer

The *logical* architecture transfers unchanged, and it is written once: the halting
reduction, the classes and the class `MIP(ω)` are generic in a *value model* `ω`
(`MIPRE.ValueModel`, §4), of which `val*` and `ω_co` are the two instances, so `MIP* = RE`
and `MIP^co = coRE` are two readings of one proof. Phase 0 (§4) proves `MIP^co = coRE`
conditionally on **one** hypothesis, the commuting-operator soundness of gap compression
(`MIPRE.GapCompression.Sound ValueModel.commuting`), on top of what exists: the
compressibility criterion generalized to nested classes, the tabulation, the classical
layers, the trivially accepting and rejecting strings, and the upper semidecider for the
commuting-operator value (`MIPRE.commutingUpperRE`, through Positivstellensatz certificates)
in the role Lin gives to the NPA hierarchy. `MIP^co ⊆ coRE` is proved unconditionally.

Everything else is the proof of that hypothesis: the soundness analyses of introspection,
answer reduction and oracularization for commuting-operator strategies (Lin's model
`t = co`). Lin carries them out on *tracially embeddable* strategies and transfers by
density; that is not what is planned here. The audit in `reports/co-generalization-audit.md`
found the repository's own analyses to be bipartite and vector-state throughout, using no
fact of finite dimension except at a few identified places, so they are **generalized** over
an abstract projective commuting-operator model, with the tensor-product strategies as an
instance and both clauses proved by one proof — except for the low-individual-degree test,
whose only proof here is the vendored finite-dimensional one and which becomes the single
remaining hypothesis. It is still the largest item after the main theorem, and §5 sizes it
phase by phase, each phase ending with a sharper conditional theorem.

Two things do *not* have to be done. Co-completeness — preservation of perfect
commuting-operator strategies — is not needed at all (§3). Parallel repetition in the
commuting-operator model is already vendored and sorry-free (`thm:direct-repetition-co`).

## 2. Lin's proof, and where each piece already lives

Lin's argument has the same shape as the halting reduction here:

* **The criterion.** A decision problem whose *yes*-instances are in `coRE` is
  `coRE`-complete as soon as it is weakly compressible (`thm:compresscosRE`, dual to the
  `RE` criterion `thm:compressRE`, both in `CompressionCond.tex`). The reduction from a
  machine `M` is the verifier sequence of `pseu:verifiersequencemipco`: at level `n`, if `M`
  halts within `n` steps, play the rejecting game; else if the upper semidecider
  (`Searchfromabove_1`, the NPA hierarchy) on the level-`C₀` game of the sequence itself
  halts within `n − C₀` steps, play the accepting game; else play the compressed game at
  level `n + 1`.
* **Compression.** `thm:gappedcompression` holds for both models `t ∈ {*, co}`:
  completeness preserves *perfect oracularizable (synchronous) strategies*, soundness
  preserves `ω^t ≤ 1/2`. It is the composition of question reduction
  (`prop:QuestionReduction`), answer reduction (`prop:AnswerReduction`) and anchored
  parallel repetition (`prop:Parallelrepetition`), each stated for `t ∈ {*, co}`.
* **The upper bound.** `MIP^co ⊆ coRE` (`lem:MIPcoincoRE`) from the NPA hierarchy.
* **The commuting-operator analysis.** The `co` cases of the three stages are proved on
  tracially embeddable strategies (`Lin23`, Definition 3.1), whose correlations are
  `ℓ¹`-dense in `C_qc` (`Lin23`, Theorem 3.2; `thm:tracialembedding` in Lin's paper), with
  the rounding of almost-synchronous correlations (`thm:Rounding`: `Lin23` Theorem 4.1 and
  de la Salle 2023) for balanced games, the rigidity of the Pauli basis test for tracially
  embeddable strategies (`thm:soundnessPaulibasis`, from `Lin23` Theorem 6.4 with
  modifications that Lin describes in prose), and the soundness of the quantum
  low-individual-degree test for tracially embeddable strategies (`thm:soundnessQLDT`,
  cited as JNVWY Theorem 4.1 together with `Lin23` Corollary 4.4; the appendix proving
  Lin's simultaneous version is commented out in the source).

Piece by piece:

| Lin | this repository | status |
|---|---|---|
| criterion `thm:compresscosRE` | `Cost.compressibility_criterion_levels`, generalized to nested classes | Phase 0 |
| upper semidecider for `ω_co` (NPA) | `MIPRE.commutingUpperRE`, `lem:valco-upper-re` | done |
| `MIP^co ⊆ coRE` | `MIPRE.MIPCo.isCoRE` | Phase 0 |
| accepting and rejecting games | `Halting.yYes`, `Halting.yNo` (`Halting/Strings.lean`) | done; `ω_co` reading in Phase 0 |
| tabulation and semidecider plumbing | `tab`, `tab_computable`, `tab_match`; their `ω_co` readings | Phase 0 |
| compression completeness, model `co` | not needed (§3): the tensor completeness `GapCompression.completeness` is what the criterion consumes | — |
| compression soundness, model `co` | `GapCompression.Sound ValueModel.commuting`, a hypothesis | Phases 1–6 |
| parallel repetition, model `co` | `thm:direct-repetition-co`, vendored and sorry-free (`MIPRE.Repetition.commutingOperatorValue_repeat_le`); direct, not anchored (§6 item 8) | done |
| tracial density | `thm:tracial-density`, vendored (`MIPRE.Repetition.tracialDensity`) | done; not needed on the route of §5 |
| rounding, model `co` | not formalized; `thm:almost-sync` is #22 (finite dimension) and #23 (commuting) | not needed on the route of §5: the analyses assume nothing synchronous |
| tracial value at most bipartite value | `lem:tracial-le-co`, #29 | not on the critical path (§5); open for the Tsirelson chapter |
| Pauli basis rigidity, model `co` | `thm:qld`, finite-dimensional; generalized over the model | Phase 5 |
| introspection soundness, model `co` | `Introspection.seven`, finite-dimensional; generalized over the model | Phase 4 |
| low-individual-degree test soundness, model `co` | not formalized; the vendored proof is finite-dimensional through and through | Phase 6, the one new theorem |
| oracularization soundness, model `co` | `OracularTensor.lean`, finite-dimensional in its carrier only; generalized over the model | Phase 2 |

## 3. The dual criterion, and why co-completeness is not needed

`Cost.compressibility_criterion_levels` (`Foundations/Compression.lean`) takes two classes
`A` and `B` with distinguished elements `yYes ∈ A` and `yNo ∈ B`, a program `S` halting
exactly off `B`, and a compressor preserving `A` and `B`; it concludes `g e ∈ A` when `e`
halts and `g e ∈ B` when it does not. For `MIP* = RE` it is applied with `A` the strings
whose game has a perfect PCC strategy and `B` those with `val* ≤ 1/2`.

For `coRE ⊆ MIP^co` the verdicts are reversed: `ω_co ≤ 1/2` when `e` halts, `ω_co = 1` when
it does not. So the criterion's `A` is the small-value class, and its `B` must be a class
*whose complement is semidecidable*: `ω_co = 1`, since `ω_co < 1` is recursively
enumerable by the upper semidecider. But the compressor cannot be asked to preserve
`{ω_co = 1}`: that is completeness for arbitrary perfect commuting-operator strategies,
which Lin's theorem does not offer (its completeness clause is for perfect *oracularizable*,
synchronous, strategies), and which nothing in the proof supplies — no perfect
commuting-operator strategy is ever constructed, in Lin's proof or in
`thm:separation`, where the perfect correlation exists only by compactness.

The repair is a **nested** criterion: three classes `A`, `B₀ ⊆ B₁`, with `yNo ∈ B₀`, the
compressor preserving `A` and `B₀`, and the search semideciding the complement of `B₁`;
the conclusion is `g e ∈ B₁` for non-halting `e`. The proof is the old one unchanged: the
induction that propagates `B` down the levels runs inside `B₀` from `yNo`, and the
contradiction with a firing search uses `B₀ ⊆ B₁`. The old theorem is the case
`B₀ = B₁`.

The instantiation:

* `A := classB ω_co n` — `n`-bounded, rejects long answers, `ω_co(𝒱_n) ≤ 1/2`; preserved by
  the hypothesis `Sound ω_co`; contains `yNo` (its verifier accepts nothing, so `ω_co = 0`).
* `B₀ := classA n` — `n`-bounded, rejects long answers, has a perfect PCC strategy on the
  doubled game: **the tensor class of the main theorem**, preserved by the existing
  `GapCompression.completeness`; contains `yYes`.
* `B₁ := {x | ¬ (ω_co(tab x n) < 1)}` — defined on the tabulated game directly, so that no
  boundedness is needed to read the conclusion; `classA n ⊆ B₁ n` because a perfect PCC
  strategy gives `val* = 1` and `val* ≤ ω_co`; its complement is semidecided by
  `commutingUpperRE` composed with `tab_computable`.

So the only hypothesis that is new is co-soundness. Lin's construction uses the same idea
without naming it: his accepting game has a perfect strategy in both models, and his
completeness clause is the tensor-style one.

## 4. Phase 0: the conditional theorem, on a generic value model

Phase 0 was first written as a twin of the tensor-product halting layer (five `Co` modules,
#236). It was then folded back into that layer, so that there is one halting reduction and
one class, parametrized by the value functional, and nothing in the halting layer is written
twice.

**The value model.** `MIPRE.ValueModel` (`Foundations/ValueModel.lean`) is a value functional
`val` on finite games together with the properties the halting reduction consumes: at most
`1`, dominating `val*`, invariant under relabeling, monotone in the decision predicate, `0`
on a game that rejects everything, unchanged by padding with always-rejected answers and by
the doubling of the question set. Its two instances are `ValueModel.tensor` (`val*`) and
`ValueModel.commuting` (`ω_co`), both definitional. Two shapes of computability are defined
on it — `LowerRE`, the set `{(G, p/q) | p/q < ω(G)}` is r.e.; `UpperRE`, the set
`{(G, p/q) | ω(G) < p/q}` is r.e. — and two shapes of reduction — `HaltingReductionRE`,
halting ↦ `ω = 1` and non-halting ↦ `ω ≤ 1/2`; `HaltingReductionCoRE`, the reverse. `val*`
is `LowerRE` (`ValueModel.tensor_lowerRE`, from `lem:value-lower-approx`) and `ω_co` is
`UpperRE` (`ValueModel.commuting_upperRE`, from `commutingUpperRE`); neither is known to be
the other, and `thm:separation` says the two values differ.

| piece | where | what |
|---|---|---|
| nested criterion | `Foundations/Compression.lean` | `Cost.compressibility_criterion_nested`; `compressibility_criterion_levels` is its special case `B₀ = B₁` |
| `ω_co` under transport | `Foundations/CommutingTransport.lean` | `CommutingOperatorStrategy.relabel`, `extendAnswers`, `mergeAnswers`; `commutingOperatorValue_eq_of_equiv`, `_mono`, `_eq_zero_of_reject`, `_le_extendAnswers`, `_doubled` — the POVM counterparts of `GameTransport.lean` and `GameDouble.lean` (merging POVMs needs no orthogonality), and what `ValueModel.commuting` is built from |
| the value of a verifier's game | `Foundations/VerifierValue.lean` | `Verifier.val ω n T := ω.val (V.game n T)`, with `val_tensor : V.val .tensor n T = V.valStar n T` by `rfl`; `val_congr`, `val_le_of_le`, `val_eq_of_rejects`, `val_eq_zero_of_rejects_all`, `val_eq_one_of_hasPerfectPCC`, `val_doubledGame`, `valStar_le_val`; the `valStar_*` names are kept as the tensor instances |
| the hypothesis | `Foundations/VerifierValue.lean` | `GapCompression.Sound ω`: the soundness clause of `GapCompression` read in the value `ω`; `GapCompression.sound_tensor : G.Sound .tensor` is the structure's own field |
| the classes | `Halting/Classes.lean`, `Halting/Instantiation.lean`, `Halting/Strings.lean` | `Verifier.InClassB ω`, `freeze_val`, `freeze_inClassB`, `inClassB_of_rejects_all`; `classB ω`, `classOne ω` (the strings with `¬ ω(tab x n) < 1`), `classA_subset_classOne`, `tab_val`, `val_tab_eq_one_of_mem_classOne`, `yNo_mem` |
| the semideciders | `Halting/Semidecider.lean` | `exists_sem_of_tab ω hlow` and `exists_sem_lower`, off `classB ω` from `ω.LowerRE`; `exists_sem_upper`, off `classOne ω` from `ω.UpperRE`; `exists_sem` is the tensor instance |
| the reduction | `Halting/Reduction.lean`, `Halting/CompressorProgram.lean` | `Obligations ω`, `CompressorSpec.toObligations ω (hs : G.Sound ω)`; `halting_reduction_lower` (the `RE` shape, from `ω.LowerRE`) and `halting_reduction_upper` (the `coRE` shape, from `ω.UpperRE`, by the nested criterion), each with a `_strings` form and an `_of` form on the compressor program; `halting_reduction` is the tensor instance |
| the class | `Foundations/ClassMIPStarComputable.lean`, `Halting/Corollaries.lean` | `IsRE`, `IsCoRE`, `MIPClass ω`; `MIPStarComputable := MIPClass .tensor`, `MIPCo := MIPClass .commuting`; `MIPClass.isRE` from `LowerRE`, `MIPClass.isCoRE` from `UpperRE`; `re_subset_mipclass_of_reduction`, `mipclass_eq_re_of_reduction`, `core_subset_mipclass_of_reduction`, `mipclass_eq_core_of_reduction` |
| the co instances | `Foundations/ClassMIPCo.lean`, `MIPRE/MIPCo.lean` | `MIPCo.isCoRE` (unconditional), `halting_reduction_commuting_of`, `core_subset_mipco_of`, `mipco_eq_core_of`; `halting_reduction_commuting`, `core_subset_mipco`, `mipco_eq_core`, each with the single hypothesis `MIPRE.gapCompression.Sound ValueModel.commuting` |
| the Tsirelson chapter | `Foundations/Tsirelson/Conditional.lean` | `HaltingReductionQuantum` and `CommutingUpperRE` are `ValueModel.tensor.HaltingReductionRE` and `ValueModel.commuting.UpperRE` |
| blueprint | chapter 8 | `def:value-model`, `def:core`, `def:mipco`, `lem:mipco-sub-core`, `lem:compressible-criterion-nested` (chapter 4), `def:compression-co-sound`, `thm:halting-co`, `thm:mipco-eq-core`, `rem:mipco-route`; `thm:halting`, `lem:halting-semidecider`, `def:mipstar-computable`, `lem:mipstar-sub-re` and `thm:mipstar-eq-re` cite the generic declarations |

What is *not* generic, and why. `classA`, the perfect-PCC class, is the tensor class in
every instance, because the criterion consumes the tensor completeness of compression (§3).
The two semideciders are different programs, because `val*` is r.e. from below and `ω_co`
from above; that asymmetry is exactly what makes one class `RE` and the other `coRE`, and
`Halting.exists_sem_upper` needs `tab` made locally irreducible or elaboration times out.

The class is the computable one, as `MIPRE.MIPStarComputable` is (`def:mipstar-computable`): a
computable map from strings to game descriptions with `ω_co = 1` on the language and
`ω_co ≤ 1/2` off it. The paper's polynomial-time class is Phase 7.

## 5. Phases 1–6: the commuting-operator soundness of compression, by generalization

The hypothesis to discharge, stated in the bipartite value of `Verifier.game`:

```text
G.Sound ValueModel.commuting : ∀ V lam n, V.IsBounded lam → G.C₀ ≤ n →
  V.val .commuting (2 ^ n) ((2 ^ n) ^ lam) ≤ 1/2 →
  (G.output (V.sampler.prog, V.decider.prog) lam).val .commuting n (G.bound.eval (n + lam)) ≤ 1/2
```

for `G = MIPRE.gapCompression`, the pipeline of `Background/Pipeline.lean` with the soundness
clause of each stage read in `ω_co`.

**The principle: generalize, do not duplicate.** `reports/co-generalization-audit.md` read
the four soundness chains and found them bipartite and vector-state throughout — a unit
vector on `ℂ^{dA} ⊗ ℂ^{dB}`, Alice's operators as `X ⊗ₖ 1`, Bob's as `1 ⊗ₖ Y`, estimates in
`‖(M ⊗ 1)ψ‖` — using no fact of finite dimension except at a handful of identified places
(the report's §4: the Kronecker carrier, Naimark dilation, one use of de la Salle's
orthogonalization, `Fin` packaging, and the vendored low-individual-degree test). So the
analyses are not re-proved for the commuting model; they are restated over an abstract model
in which the tensor-product strategies are an instance, and then they prove both clauses at
once. The one exception is the low-individual-degree test, whose only proof here is the
vendored finite-dimensional `MIPStarRE.LDT.Test.mainFormal`; it becomes the single
hypothesis of the conditional theorem until a commuting-operator proof exists (Phase 6).
Lin's route — tracially embeddable strategies, rounding, density — is not followed: the
repository's proofs never symmetrize and never use the tracial state, and every tool of
that route (`thm:almost-sync` #22/#23, `lem:tracial-le-co` #29, the standard form
`L²(𝒜, τ)`) drops off the critical path. Where a generic lemma is written, its matrix version
is deleted or becomes the instance; nothing is kept in two copies.

**The model.** A *projective commuting-operator strategy*: a Hilbert space `H`, a unit
vector `ψ`, Alice's PVMs `A x a : H →L[ℂ] H`, Bob's PVMs `B y b`, with
`Commute (A x a) (B y b)`. `TensorProductStrategy.toCommuting` (`Foundations/Correlations.lean`)
is the tensor instance; `ω_co` is the supremum over these by the dilation lemma of Phase 1
(`commutingOperatorValue_eq_iSup_isProjective`);
Lin's tracially embeddable strategies (vendored `TraciallyEmbeddableCorrelation`, Alice in
the algebra, Bob in its commutant) are instances too, though nothing here needs them. Finite
ancillas are `ι → H` with the `PiLp 2` structure, so the EPR register of introspection and
of the Pauli basis test, and the Weyl operators on it, are unchanged.

**Phase 1 — the model and its operator calculus** (foundation; report §4 items 1, 2, 5, 7).
Three pieces.

(a) **Done (#241).** `Foundations/CommutingDilation.lean`, on `Foundations/HalmosDilation.lean`
(the algebra, over any ring with an involution) and `Foundations/OperatorMatrix.lean` (matrices
of operators acting on the ancilla `ι → H`, a unital `⋆`-homomorphism, and the embedding
`ξ ↦ ξ ⊗ e_{i₀}`); blueprint `def:co-projective`, `lem:co-dilation`, `thm:co-value-projective`;
940 lines. One question is dilated at a time and the others are amplified. For the first
player's question `x`: the square roots `√E^x_a` (`CFC.sqrt`, commuting with every `F^y_b` by
`Commute.cfcₙ_nnreal`); the Naimark matrix `w` whose column `a₀` is `(√E^x_a)_a`, a partial
isometry in the ring of operator matrices; its Halmos unitary
`U = [[w, 1 − ww*], [1 − w*w, w*]]`; and the projections `U* Q_a U` on `H ⊗ ℂ^(A ⊕ A)`, which
compress to `E^x_a` at `ψ ⊗ e_{inl a₀}` as an identity of matrix entries and commute entrywise
with `F^y_b ⊗ 1`. The second player's questions are dilated with the players exchanged. No von
Neumann algebra theory, no comparison of projections. The results are
`CommutingOperatorStrategy.exists_isProjective_correlation_eq`,
`commutingOperatorValue_eq_iSup_isProjective`, and `exists_isProjective_lt_value`, the form a
soundness proof consumes: a strategy beating `t` in `ω_co` may be taken projective.
`TensorProductStrategy.isProjective_toCommuting` places the tensor model inside.

(b) The operator calculus restated over `H →L[ℂ] H` with two commuting families: `snorm`,
`xSqNorm`, `bornProb`, `povmValue`, `condFail`, `dis`, `Bnd`, the Cauchy–Schwarz and
`∑ F†F ≤ 1` lemmas, PVM fibres and coarse-grainings, the sandwich and pasting chains,
`GameAdapt`'s `succAt`/`failAt`/`adapt` and the strategy transports — today `OpBound`,
`StateDistance`, `CrossConsistency`, `POVMValue`, `PVM`, `Commutation`, `POVMMix`,
`Disagreement`, `Sandwich`, `Pasting`, `Expanded`, `Swap`, `GameAdapt`, `GameTransport`
(≈ 9–10k lines). The matrix layer becomes the instance
`H = EuclideanSpace ℂ (Fin dA × Fin dB)`, `aOp X = toEuclideanCLM (X ⊗ₖ 1)`, so that
consumers migrate file by file and the main theorem keeps building throughout; where a
proof used matrix entries (the Cauchy–Schwarz of `Closeness.lean`, `PosSemidef.kronecker`)
it is re-proved from positivity. `Dilation`, `StrategyDilation`, `RegisterReindex` and
`LIDT/Adapter/Registers` are retired.

(c) The interfaces: the four stage structures carry their soundness clause in
`Verifier.val ω` for the two models — a `ValueModel`-indexed family, or two fields — and
`Pipeline.output_val_le ω` composes them (the value chain of `Compress.lean` is generic given
`val_eq_of_rejects ω`, already in #239).

Risk: elaboration cost. `OpBound.lean` avoids Mathlib's operator norm for elaboration time;
the generic layer must be profiled on the heaviest consumers (`QLD/Chain.lean`, 2.5k lines;
`Pasting.lean`) before the migration is committed to. New: 3–5k lines; restated: ≈ 10k.

**Phase 2 — oracularization, repetition and the composition** (validates the architecture;
report §3.1). `OracularTensor.lean` (771 lines) restated in the model — its six projectivity
uses are now legitimate by construction — with the detyping transports and
`quantumValue_typedGame_le`; `typed_soundness`/`detyped_soundness` of
`Pipeline/Oracularization.lean` in `Verifier.val ω`. Repetition: `val_repVerifier ω` (≈ 30
lines; the verifier-to-game bridge is value-independent), the co bound from the vendored
`commutingOperatorValue_repeat_le` (`ε^7 ≥ ε^13`), the `Repetition` interface with both
clauses, `Background/Repetition/Verifier.lean` instantiated twice. Then
`GapCompression.ofPipeline` yields `Sound ω` for both models from the three stage clauses in
`ω`. **After this phase `MIPRE.mipco_eq_core` is conditional on the introspection and
answer-reduction clauses in `ω_co`** instead of on the whole of `Sound .commuting`. No
rounding, balancedness, density or tracial embedding anywhere. New: 2–3k lines.

**Phase 3 — answer reduction, with the low-individual-degree test as a model hypothesis**
(report §3.2). The `Sound*` chain (≈ 4k B lines), the LIDT adapter (`Reduction`, `Padding`,
`Extraction`, `Simultaneous`, ≈ 3.8k), `Bridge/Measurement` and the Foundations chain
restated; the one finite Naimark step (`povmValue_le_quantumValue`) disappears, since the
decoded measurements are coarse-grainings of PVMs. The interface: a structure
`LIDTSoundness` for the model, in the exact shape of `Simul.clSoundness` — a projective
strategy passing the seeded `clGame` with probability `≥ 1 − ε` yields PVMs `GA` in Alice's
algebra and `GB` in Bob's with the three inconsistency bounds and error `deltaSim`. Its
tensor instance is the vendored `mainFormal` through the existing bridge; its commuting
instance is Phase 6. **After: conditional on the introspection clause and the commuting
LIDT soundness.** Touched: 8–10k lines.

**Phase 4 — introspection, with `thm:qld` as a model hypothesis** (report §3.3). The 10.5k
B lines restated; of the 9.6k C lines, the EPR register and the mirror, and the
entry/block/readout identities, stay on the concrete register factor `M_{q^n}` with the
ancilla abstract (which is how `PrimitiveSoundness` is already stated: PVMs on
`(ι → F) × H` against `registerState ξ`, `ξ` arbitrary); the Naimark-against-a-fixed-state
steps of the adaptive inductions become the Phase 1 lemma; the isometry layer
(`FieldExtraction`, `isometricImage`, `isometricState`) is restated with isometries
`H → ℂ^{register} ⊗ H'`. The interface: `QLDSoundness` for the model, in the shape of
`qld_soundness`'s conclusion. **After: conditional on the Pauli basis test and the LIDT
soundness in the commuting model.** Touched: ≈ 20k lines; check first that the inductions
run at the same error rates with the new dilation (they should: the compression identity is
the same).

**Phase 5 — the Pauli basis test, with the LIDT soundness as the hypothesis** (report §3.4).
The 23k B lines restated; M1 (the top-level `exists_legal_dilation`, the sandwich's joint
measurement, `Anticomm`) become the Phase 1 lemma; M2, the one use of de la Salle's
orthogonalization at `QLD/Commutation.lean:587`, is removed by threading projectivity to
`hatObs_commutation` and `comm_signed_commutation` (the audit's inference — verify before
relying on it; the fallback is the vendored `B(H)` tier, unconditional); M3:
`PaddedLIDT.lean` consumes `LIDTSoundness`; M4: the statement shape. The ancilla-side EPR
and Weyl material is unchanged. **After: `MIPRE.mipco_eq_core` is conditional on exactly one
named theorem, `thm:lidt-cl-soundness-one` in the commuting-operator model.** Touched:
≈ 25k lines.

**Phase 6 — the low-individual-degree test in the commuting-operator model.** The only new
mathematics, and the item on which the track can fail. What exists: the vendored
finite-dimensional proof (126k lines: spectral truncation and SVD in
`MakingMeasurementsProjective`, semidefinite duality in `SelfImprovement`, matrix Chernoff,
SWAP symmetry, `Fintype.card` throughout) and Lin's paper trail, which cites JNVWY's
tensor-code soundness as "directly applied" to individual-degree polynomials, extended to
tracially embeddable strategies by `Lin23` Corollary 4.4, with the appendix proving the
simultaneous version commented out in the source. Options, in order of preference: a
commuting-operator proof produced upstream and vendored through `scripts/vendor-*.py`, as
the finite-dimensional one was; a direct formalization on the model, after an audit of which
of the vendored proof's mechanisms have tracial analogues (not done). No transfer principle
applies: density approximates by tracially embeddable strategies, still
infinite-dimensional, and approximation by finite-dimensional ones is what fails.
Prerequisite: verify Lin's paper trail for `thm:soundnessQLDT` and `lem:simuQLID` before
anything else. Size: unknown; 40k–130k lines by analogy with the vendored proof.

**Phase 7 (optional) — the paper's class.** `MIP^co_{1,1/2}(2,1)` with a polynomial-time
sampler and decider, mirroring `MIPStarPoly` (#230–#233), and Lin's `k-CLMIP^co`. About 1k
lines.

Order: 1, 2, then 3 and 4 in either order (both need only Phase 1), 5, 6. Phases 2–5 each
end with a sharper conditional theorem, stated in `MIPRE/MIPCo.lean` and in blueprint
`thm:mipco-eq-core`, so the track has a checkable deliverable at every step.

## 6. Delicate points

1. **Two commuting values, never interchanged.** The bipartite `ω_co`
   (`MIPRE.commutingOperatorValue`: POVMs `E`, `F` on one Hilbert space, commuting) and the
   tracial `valco` (`MIPRE.commValue`: a `*`-algebra with a tracial state and one PVM family
   played by both players). The criterion, the classes, the semidecider,
   `Sound ValueModel.commuting`, `MIPCo` and the model of §5 are all in `ω_co`, so nothing
   is transferred at the criterion and nothing in the track uses `valco`. `valco ≤ ω_co` is
   #29 and unproved; the reverse fails in general and holds up to rounding for synchronous
   games with proportional diagonal weight (`thm:almost-sync`, #22/#23). Neither is on the
   critical path of §5; both stay open for the Tsirelson chapter.
2. **Projective versus POVM.** The model is projective because the analyses are
   (`OracularTensor` uses projectivity six times, `oracleView_mul` is false for POVMs, every
   measurement on the answer-reduction chain is a PVM or a coarse-graining of one). `ω_co` is
   defined with POVMs, and the vendored tracially embeddable correlations have POVMs too, so
   density does not close the gap; the dilation lemma of Phase 1 does, and it is the single
   lemma the whole architecture leans on. Its proof is elementary (a 2×2 unitary extension
   of a partial isometry in a C*-algebra, report §4), and it is in Lean: Phase 1(a), #241.
3. **Generic means replaced, not added.** A generic lemma replaces its matrix version, and
   the tensor statement is derived as an instance; the main theorem keeps building through
   the generic proof at every commit. If a phase leaves a matrix twin beside a generic
   lemma, the phase is not done. The `valStar_*` names of #239 are the pattern: one-line
   instances of the `val_*` lemmas.
4. **What stays finite-dimensional on purpose.** The EPR register and the Weyl operators of
   introspection and of the Pauli basis test (on a finite ancilla), the readouts and block
   identities on the register factor, `HasPerfectPCC` and every completeness construction,
   the tensor identification of repetition (`Entangled.lean`) and its 71k-line vendored
   proof. None of these is a duplicate; each is an instance, or on a side the model leaves
   concrete.
5. **The nested criterion.** The search must semidecide the complement of the *larger*
   class, the compressor must preserve the *smaller* one, and the "no" string must lie in
   the smaller. The Lean of Phase 0 is the check.
6. **The semidecider runs on the tabulation.** `tab x n` is total, and `tab_val` holds
   for `n`-bounded strings only, as `tab_value` does. `classOne` is defined on the
   tabulated game so that the non-halting conclusion needs no boundedness; the halting
   conclusion reads `ω_co(tab) ≤ 1/2` through `tab_val` from the boundedness that
   `classB ω_co` carries.
7. **`ω_co = 1` without a strategy.** It is `¬ (ω_co < 1)` and `ω_co ≤ 1`. No perfect
   commuting-operator strategy is constructed anywhere, consistent with `thm:separation`.
8. **Vendored orthonormalization is used at one site, in its finite-dimensional tier.**
   `QLD/Commutation.lean:587` is the only consumer, and the audit's reading is that
   projectivity, already available there, makes the call unnecessary; the vendored tree
   also carries the `B(H)` and II₁-factor tiers unconditionally, and the general von
   Neumann tier conditionally on the unproved `MvNStructureTheory`. Lin's
   `lem:orthogonalizationlemma` is the general version (de la Salle, Theorem 1.2); it is
   not needed on the route of §5.
9. **The vendored trees are untouchable** except through `scripts/vendor-*.py`; the
   commuting LIDT soundness therefore arrives either as a new vendored tree or as project
   Lean, never as an edit of `MIPStarRE`.
10. **Elaboration cost.** The finite-dimensional operator layer was tuned for it
    (`OpBound.lean` avoids Mathlib's operator norm on purpose); profile the generic layer on
    `QLD/Chain.lean` and `Pasting.lean` before migrating them.
11. **Anchored versus direct repetition.** Lin's `prop:Parallelrepetition` is anchored and
    proved in his appendices for both models; the repository's repetition is direct. The
    value-form pipeline (D8) needs only direct repetition, and its `co` form is vendored.
12. **Authority and the paper trail.** The companion proof repository has no `coRE`
    chapter. For Phases 1–5 the mathematics is the repository's own, and the paper of
    record is JNVWY through this blueprint; Lin's paper, cited at its arXiv version, is the
    authority for Phase 6 only, which is where its thin spots (`thm:soundnessQLDT`,
    `lem:simuQLID`) matter — the reason Phase 6 is last and its verification comes first.
    Disagreements between Lin's statements and the Lean are findings to report to Lin, not
    to the companion ledger.
13. **The class is the computable one.** As for `MIP*`, the Lean class quantifies over
    computable maps to game descriptions, and the polynomial-time class is a separate
    inclusion (Phase 7), as `lem:mipstar-poly-sub` is.

## 7. Milestones

| ID | Deliverable | Size | Status |
|---|---|---|---|
| C0 | Phase 0: the nested criterion, the `ω_co` transport, the value model and the generic halting layer, the conditional reduction, `MIPCo`, `MIPCo ⊆ coRE`, the blueprint | ~1k lines of Lean net | done: #236, then made generic in #239 |
| C1 | Phase 1: the projective commuting-operator model, the dilation lemma, the operator calculus restated with the matrix layer as its instance, the stage interfaces in `Verifier.val ω` | 3k–5k new, ≈ 10k restated | open (#240); (a), the dilation lemma, done (#241); next (b) |
| C2 | Phase 2: oracularization, repetition and the composition in the model; `mipco_eq_core` conditional on the introspection and answer-reduction clauses in `ω_co` | 2k–3k | open |
| C3 | Phase 3: answer reduction in the model with `LIDTSoundness` as the hypothesis | 8k–10k touched | open |
| C4 | Phase 4: introspection in the model with `QLDSoundness` as the hypothesis | ≈ 20k touched | open |
| C5 | Phase 5: the Pauli basis test in the model; `mipco_eq_core` conditional on the commuting LIDT soundness alone | ≈ 25k touched | open |
| C6 | Phase 6: the low-individual-degree test in the commuting-operator model | unknown; 40k–130k by analogy | open; verify Lin's paper trail first |
| C7 | Phase 7: the paper's class `MIP^co_{1,1/2}(2,1)` | ~1k | open |

C1 is the prerequisite of everything after it; C3 and C4 need only C1 and are independent
of each other; C5 needs C4's interface; C6 is independent of C3–C5 in its mathematics and is
what they all wait for. Each of C2–C5 ends with a sharper conditional theorem, so progress
is visible in `MIPRE/MIPCo.lean` at every milestone.
