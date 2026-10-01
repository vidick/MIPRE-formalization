# The commuting-operator class, `MIP^co = coRE`: plan

**Status: Phase 0 done (#235, #236), made generic in #239; Phase 1 done (#241, #243, #245);
Phase 2 done (#247); Phase 3 done (#249); Phase 4 done (#251); Phase 5 done (#253); Phase 6, the
one new theorem, open, its paper trail and the vendored proof audited (#255,
`reports/lidt-co-audit.md`).** The conditional theorem — `MIP^co = coRE` given the commuting-operator
soundness of gap compression — is in, with all of its plumbing, written once for both values.
Since Phase 5 it follows from the soundness of the low-individual-degree test in the
commuting-operator model alone (`MIPRE.mipco_eq_core_of_lidt`, hypothesis `LIDT.Simul.SoundCo`):
parallel repetition's clause is proved, answer reduction's is proved from that test, and
introspection's from the Pauli basis test, which is proved from it (`QLD.soundCo_of_lidt`). The
operator calculus of the stage analyses is proved once over a bipartite model, with the matrix
layer as its tensor-product instance, and so are the soundness of oracularization, of answer
reduction, of introspection and of the Pauli basis test. The audit finds no paper trail for
`LIDT.Simul.SoundCo` in its present generality, and recommends a weaker hypothesis that
suffices: soundness in the models whose two algebras carry faithful normal traces, reached from
`ω_co` through the vendored tracial density (§5, Phase 6).

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
remaining hypothesis. The Phase 6 audit (`reports/lidt-co-audit.md`) found no paper trail for
that hypothesis in its present generality, and recommends a weaker one that density makes
sufficient (§5, Phase 6). It is still the largest item after the main theorem, and §5 sizes it
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
  low-individual-degree test, which his answer reduction applies only to synchronous
  strategies, after rounding. That soundness is `thm:soundnessQLDT`, cited and not proved,
  together with `lem:simuQLID`, whose proof is incomplete. Its extension to tracially
  embeddable strategies rests on `Lin23` Corollary 4.4 (`reports/lidt-co-audit.md` §2).

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
| parallel repetition, model `co` | `thm:direct-repetition-co`, vendored and sorry-free (`MIPRE.Repetition.commutingOperatorValue_repeat_le`); direct, not anchored (§6 item 8); at the verifier level `MIPRE.repetitionCo_soundIn_commuting` (`thm:parallel-repetition-co`) | done (verifier level: Phase 2) |
| tracial density | `thm:tracial-density`, vendored (`MIPRE.Repetition.tracialDensity`) | done; not needed in Phases 1–5; Phase 6's recommended target uses it at the value level, through the vendored `strict_tracial_reduction` |
| rounding, model `co` | not formalized; `thm:almost-sync` is #22 (finite dimension) and #23 (commuting) | not needed on the route of §5: the analyses assume nothing synchronous |
| tracial value at most bipartite value | `lem:tracial-le-co`, #29 | not on the critical path (§5); open for the Tsirelson chapter |
| Pauli basis rigidity, model `co` | `thm:qld` in a bipartite model from the LIDT hypothesis (`QLD.soundIn_of_lidt`), `QLD.soundCo_of_lidt` | done (Phase 5) |
| introspection soundness, model `co` | `Introspection.seven`, finite-dimensional; generalized over the model | Phase 4 |
| low-individual-degree test soundness, model `co` | not formalized; no source proves it for an arbitrary vector state; the vendored proof is dimension-free except at three isolated steps (`reports/lidt-co-audit.md`) | Phase 6, the one new theorem; audited (#255) |
| oracularization soundness, model `co` | generalized over the model (`OracularModel.lean`, `SeededGame.povmValue_sound_ge`), with `OracularTensor.lean` its tensor instance; `SeededGame.commutingOperatorValue_ge_of_oracular` | done (Phase 2) |

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
`L²(𝒜, τ)`) drops off the critical path. Phase 6's recommended target takes the tracial
density back on, at the value level only; rounding (#22, #23) and #29 stay off the path.
Where a generic lemma is written, its matrix version
is deleted or becomes the instance; nothing is kept in two copies.

**The model.** A *projective commuting-operator strategy*: a Hilbert space `H`, a unit
vector `ψ`, Alice's PVMs `A x a : H →L[ℂ] H`, Bob's PVMs `B y b`, with
`Commute (A x a) (B y b)`. `TensorProductStrategy.toCommuting` (`Foundations/Correlations.lean`)
is the tensor instance; `ω_co` is the supremum over these by the dilation lemma of Phase 1
(`commutingOperatorValue_eq_iSup_isProjective`);
Lin's tracially embeddable strategies (vendored `TraciallyEmbeddableCorrelation`, Alice in
the algebra, Bob in its commutant) are instances too. Nothing in Phases 1–5 needs them, and
Phase 6's recommended route needs them only through the vendored density, at the value level. Finite
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
`LIDT/Adapter/Registers` are retired with their consumers, which are the matrix stage
analyses (Phases 3 and 5; see "What stays matrix-side" below).

**(b) Done (#243, #245).** `Foundations/StateModel.lean` and `Foundations/BipartiteModel.lean`:
a *state model* is a Hilbert space `H`, a state `ψ` and a `⋆`-algebra `𝒞` represented on `H` by
`π : 𝒞 →⋆ₐ[ℂ] (H →L[ℂ] H)`; a *bipartite model* adds the players' `⋆`-algebras `𝒜` and `ℬ`
and `πA : 𝒜 →⋆ₐ[ℂ] 𝒞`, `πB : ℬ →⋆ₐ[ℂ] 𝒞` with commuting images (blueprint
`def:bipartite-model`). The players' operators are elements of `𝒜` and `ℬ`, so products, sums
and adjoints of one player's operators stay on that player's side and commute with the other
player's for free, which is what the matrix analyses get from `aOp` and `bOp`. Two instances:

* `BipartiteModel.tensor ψ`: `𝒞 = M_{dA × dB}(ℂ)` acting through `Matrix.toEuclideanCLM`,
  `πA = aOp` and `πB = bOp` definitionally, so a model identity in `𝒞` *is* the matrix
  identity (`aOp_bOp_mul_aOp_bOp` is `πA_mul_πB_mul` at `tensor 0`);
* `CommutingOperatorStrategy.toModel S`: `𝒞 = B(H)`, `𝒜` the commutant of the second player's
  operators and `ℬ` the commutant of `𝒜`. They are ordered, since a commutant contains the
  square roots of its positive elements (`starOrderedRing_centralizer`), so positivity there is
  positivity in `B(H)`. The strategy's measurements are POVMs of the model, its value is the
  model's value of them, and `ω_co` is a supremum of model values
  (`commutingOperatorValue_eq_iSup_povmValue`, `lem:co-value-model`).

That `ψ` is a unit vector is a hypothesis, not a field, so that every matrix quantity is the
model's at `tensor ψ` with no side condition. The calculus restated, each lemma proved once and
the matrix statement of the same name derived at `tensor ψ` (consumers keep calling the matrix
names, and the main theorem built at every commit): the state calculus (`OpCalculus`,
`StateModel`, `OpBound`); POVMs and projective measurements in any `⋆`-ring (`POVMIn`,
`IsPVMIn`, coarse-graining, marginals) and the Born rule, `povmValue` and `condFail`
(`Measurement`, `POVMValue`, `PVM`); the state norms and `stateDist` (`StateDistance`); the
consistency engine `xSqNorm_sum_le_two_mul` and the conditional-failure bounds
(`CrossConsistency`); `commutation_analysis` (`Commutation`); mixtures and the agreement
triangles (`POVMMix`); disagreement and its data processing (`Disagreement`); the five-link
sandwich chain `one_sub_sum_bornProb_sand_le` and coarse-graining `sum_xSqNorm_map_le`
(`Sandwich`); the pasting chain (`Pasting`); the exchange of the players
(`povmValue_eq_of_bornProb_swap`, `Swap`); strategies in a model, adaptation and relabeling
(`condWin_adapt`, `povmValue_relabel`, `GameAdapt`; `GameTransport` was already generic in a
value model). Blueprint `rem:model-calculus` lists the headline declarations.

The finite ancillas are `Foundations/AncillaModel.lean`: `BipartiteModel.expand M e` adjoins
registers `α`, `β` in the state `e` on `OperatorMatrix.Ampl (α × β) H`, the players' algebras
becoming `M_α(𝒜)` and `M_β(ℬ)`. Born probabilities of product measurements factorize, an inert
ancilla changes nothing, and products of projective measurements are projective
(`lem:ancilla-extension`); the matrix expanded state of `Expanded.lean` is the instance at
`tensor ψ`, through the bridge `bornProb_expVec_eq` and `kronEquiv`.

What stays matrix-side, on purpose. The finite dilations — `Dilation` (finite Naimark),
`StrategyDilation`, `RegisterReindex`, `LIDT/Adapter/Registers`, and the sandwich's projective
joint measurement `exists_projective_joint` (a Naimark dilation on an `A × A` ancilla against
`extVec2`) — are consumed only by the matrix stage analyses, and retire with them: the finite
Naimark step of answer reduction (`povmValue_le_quantumValue`) in Phase 3, the joint measurement
and `exists_legal_dilation` in Phase 5, where the dilation of (a) replaces them. The coordinate
plumbing of the Kronecker representation (`aOp_mul`, `mulVec_kron_kron_expVec`, `extVec2` and
its compressions) is how the tensor instance is defined, not a twin of a generic lemma. The
model's Cauchy–Schwarz is the Hilbert space's (`StateModel.abs_qform_star_mul_le`), and its
positivity facts are proved on the represented operators (`Op.mul_self_le_self`,
`Commute.mul_nonneg`) rather than from matrix entries; `Closeness.lean`, the Hilbert–Schmidt
calculus of the orthonormalization stage, is tracial and stays matrix-side.

Elaboration cost, measured. A generic statement over an abstract model elaborates at the cost
of its matrix original (the cross-consistency engine: about 0.8 s either way), and the
operator order that `OpBound`'s docstring warns about is never needed; the instance route costs
about 100 ms of type-class search per `map_*` rewrite through `toEuclideanCLM`, so matrix lemmas
are derived once, in the layer file, and consumers keep calling them. Measured on the files of
this phase: `Sandwich.lean` elaborates in 7.7 s generic against 8.1 s before, `Pasting.lean` in
about 8 s against 5.6 s (most of the difference is its 41 matrix derivations; stating
`P² ≤ P` once for any ordered algebra with a functional calculus, instead of deriving the matrix
fact through `toEuclideanCLM`, took off 3 s), and the heaviest consumer, `QLD/Chain.lean`, builds
in 36 s against 41 s before (both inside a parallel full build). A full build that recompiles
everything downstream of these files, 423 modules, takes 12.5 minutes.

**(c) Done (#245).** `Introspection.SoundIn ω`, `AnswerReduction.SoundIn ω` and
`Repetition.SoundIn ω` (`Pipeline/{Introspection,AnswerReduction,Repetition}.lean`) are each
stage's soundness clause with `val*` replaced by `Verifier.val ω`, at the same parameters; the
structure's field is the case `ω = .tensor` (`soundIn_tensor`). The structures keep their tensor
field rather than a model-indexed family: a stage's clause in `ω_co` is a theorem of Phases 2–5,
not data every stage must supply. `Pipeline.output_val_le ω` is the soundness chain of
`Compress.lean` in `ω` — the same margins, the three clauses the only model-dependent input,
`Within.val_eq ω` passing between the stages' answer bounds — and the tensor chain is its
instance. `GapCompression.ofPipeline_sound` composes it, and `MIPRE.mipco_eq_core_of_stages`
proves `MIP^co = coRE` from the three clauses in `ω_co` (blueprint `def:stage-sound-in`,
`lem:compress-sound-in`, `thm:pipeline-sound-in`, `cor:mipco-from-stages`).

**Phase 2 — oracularization and repetition** (validates the architecture; report §3.1).
`OracularTensor.lean` (771 lines) restated in the model — its six projectivity
uses are now legitimate by construction — with the detyping transports and
`quantumValue_typedGame_le`; `typed_soundness`/`detyped_soundness` of
`Pipeline/Oracularization.lean` in `Verifier.val ω`. Repetition: `val_repVerifier ω` (≈ 30
lines; the verifier-to-game bridge is value-independent), the co bound from the vendored
`commutingOperatorValue_repeat_le` (`ε^7 ≥ ε^13`), the `Repetition` interface with both
clauses, `Background/Repetition/Verifier.lean` instantiated twice. The composition is done
(Phase 1(c): `GapCompression.ofPipeline_sound`). **After this phase
`MIPRE.mipco_eq_core_of_stages` loses its repetition hypothesis: `MIP^co = coRE` is conditional
on the introspection and answer-reduction clauses in `ω_co`.** No rounding, balancedness,
density or tracial embedding anywhere. New: 2–3k lines.

**Done (#247).** *Repetition.* The output's game is the repeated game in every value model
(`val_repVerifier ω`: the two relabelings are `ValueModel.extendAnswers` and `eq_of_equiv`), so
soundness in `ω` is the game-level bound in `ω` (`Repetition.GameSoundIn ω c`,
`val_repVerifier_le`). `ω_co` has it at `repConstCo`, from the vendored theorem through the
arithmetic the tensor bound already used (`Repetition.exp_le_soundBound`), and `val*` at
`repConst`. The structure `Repetition` has one constant, which the compression uses to choose
`τ`, and the two constants are unrelated `choose`s. So the co reading is
`repetitionCo := (repetition ℓ).withConst (min repConst repConstCo)`: the same verifier, sound in
both models (`repetitionCo_soundIn_commuting`). `MIPRE.gapCompressionCo` is the main theorem's
pipeline with `repetitionCo 7`. The main theorem keeps `repetition 7`, so `MIP* = RE` does not
import `CommutingRepetition` (56k lines) or depend on its constant.
`mipco_eq_core_of_stages hI hA` is the new statement. The "`Repetition` interface with both
clauses" of the plan is the structure's tensor field together with `SoundIn .commuting` for
`repetitionCo`. A model-indexed field would have forced every instance, `repetition` included,
to supply the co clause.

*Oracularization.* `OracularModel.lean` is `OracularTensor.lean` over a bipartite model with
projective families (`SeededGame.povmValue_sound_ge`). The six projectivity uses are
hypotheses: the front factors of the chain, the oracle's joint marginal, and the Born
probabilities as squared masses. `OracularTensor.lean` keeps `tensorSound`,
`tensorSound_value_ge` and `quantumValue_ge_of_oracular`, derived at `tensor N.ψ`; its matrix
intermediates are gone. `CommutingModel.lean` is the bridge the later phases will also use. A
POVM strategy in a model is a commuting-operator strategy of the same value
(`BipartiteModel.toCommuting`, `povmValue_le_commutingOperatorValue`). `ω_co` is approached by
strategies that are projective *in their own model* (`exists_isPVMIn_lt_povmValue`), because
projections summing to one are orthogonal in a C⋆-ring (`IsPVMIn.of_isStarProjection`) and
`IsPVMIn` pulls back along the injective inclusions (`IsPVMIn.of_map`). With it,
`SeededGame.commutingOperatorValue_ge_of_oracular` takes ten lines.

The two transports of the verifier-level statement are restated in a model as well:
question-dependent post-processing (`BipartiteModel.povmValue_le_postprocess`, the content of
`quantumValue_typedGame_le`), and the detyping restriction (`CL.Detyping.restrict_povmValue_ge`
in `CL/DetypingModel.lean`, with the tensor originals left in place). Each is read in both values,
the affine detyping bound passing through the supremum (`one_sub_mul_one_sub_iSup_le`).
The verifier level is written once. `ValueModel.OracularSound ω` bundles the three facts
(post-processing, game-level soundness, finite detyping), `tensor_oracularSound` and
`commuting_oracularSound` prove them, and `Oracularization.typed_soundness_val` and
`detyped_soundness_val` are the clauses in `Verifier.val ω`. The tensor clauses are the case
`.tensor`, and the ambient detyping goes through `ValueModel.eq_of_equiv` along the coordinate
numbering (`OracularSound.typedGame_ge_ambient`). `OracularSound` is a property of the model,
proved for each, and not a new field of `ValueModel`: the fields are what the halting reduction
uses, and adding one would rebuild every consumer of the class. Phase 3 consumes the
model-level statements (`povmValue_sound_ge`, `povmValue_le_postprocess`,
`restrict_povmValue_ge`), since the answer-reduction chain works at the level of strategies.

Measured: the whole library rebuilt downstream of these files in about 3 minutes, and a
replayed full build takes seconds. New: ≈ 1.4k lines of Lean in five files, most of it the model
restatement of the oracularization argument, against ≈ 0.7k matrix lines retired from
`OracularTensor.lean`; blueprint section `sec:ds-mipco-phase2`, 8 nodes.

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

**Done (#249).** `MIPRE.mipco_eq_core_of_stages` now takes the introspection clause in `ω_co`
and `LIDT.Simul.SoundCo`; answer reduction's clause in `ω_co` is a theorem
(`AnswerReduction.answerReduction_soundIn_commuting`), at the constants of the tensor clause.

*The model strategy.* `BipartiteModel.ProjStrat M G` (`Foundations/ModelStrategy.lean`) is
`TensorProductStrategy` with the tensor-product model replaced by any bipartite model: PVM
families in the two players' algebras and the unit state, with the operations the chain uses —
`value`, `failAt`, `adapt` (a coarse-graining of a PVM is a PVM, `POVMIn.isPVMIn_map`),
`relabel`, `restrict` — each a line over the model statements of `GameAdapt.lean`.
`BipartiteModel.inconsistency` is the matrix `inconsistency` in a model
(`inconsistency_eq_tensor`). The two readings: a `TensorProductStrategy` is a `ProjStrat` of its
tensor model (`TensorProductStrategy.toModel`) and a `ProjStrat` of the tensor model of a state
on `Fin a × Fin b` is a `TensorProductStrategy` (`ProjStrat.toTensor`), both of the same value;
`ω_co` is approached by `ProjStrat`s in the models of commuting-operator strategies
(`exists_projStrat_lt_commutingOperatorValue`, from Phase 2's `exists_isPVMIn_lt_povmValue`).
`ValueModel.Dominates ω M` — every `ProjStrat` of `M` has value at most `ω` — holds for `val*`
at a tensor model and for `ω_co` at every model on a Hilbert space.

*The interface.* `LIDT.Simul.SoundIn M` (`Background/LIDT/ModelSoundness.lean`; `LIDTSoundness`
above) is `clSoundness` with `TensorProductStrategy` replaced by `M.ProjStrat` and the extracted
`ProjectiveMeasurement Unit _ _` by a PVM `POVMIn _ 𝒜` (resp. `ℬ`); the three inconsistencies
keep their indices, the third on `Unit`. `soundIn_tensor` is `clSoundness` read through
`toTensor` and `inconsistency_eq_tensor`. `LIDT.Simul.SoundCo` is `SoundIn S.toModel` for every
commuting-operator strategy `S`: stated on the models whose algebras are commutants (von Neumann
algebras), not on all bipartite models, which would be a stronger and probably false demand.

*The chain.* The ten `Sound*` files keep their names and their proofs, with
`T : M.ProjStrat (typedGame …)` and, from `SoundExtract` on, `hL : LIDT.Simul.SoundIn M`
(`GA1 … := (exists_ext1 … hL …).choose`): the matrix POVMs become `POVMIn`, `dis T.ψ` becomes
`M.dis`, and every lemma the chain calls already existed in the model from Phase 1(b), except
`POVMIn.map_map` and the two event-relabelling lemmas of `SoundGameCheck`. `SoundSetup` reads
the compiled verifier's questions in the finite detyped game and restricts in the model
(`CL.Detyping.restrict_povmValue_ge`); the `Fintype` instance of that game's questions at
`ArTy` needs `synthInstance.maxSize 1024`, since the derived `DecidableEq` of the PCP types is
large. The decoded measurements (`MAo`, `MBo`) are coarse-grainings of the extracted PVMs
(`MAo_proj`), so the decoded strategy is a `ProjStrat` (`decoded`) and the Naimark step
`povmValue_le_quantumValue` is deleted: `val_ge_decoded` bounds `V.val ω` in every `ω` with
`OracularSound` that dominates `M`. `SoundFinal` states the assembly once
(`val_ge_of_arStrategy`) at explicit constants `soundA`, `clB / 2`, `soundC` — the witnesses of
the old existential were `Classical.choose`s, which a second model could not share — and reads
it in `val*` (`arVerifier_soundness_tensor`, `arVerifier_soundness` its existential form) and in
`ω_co` (`arVerifier_soundness_commuting`); `Instance.lean` defines `arA`, `arB`, `arC` as those
constants.

*What was not restated, and why.* The LIDT adapter (`Reduction`, `Padding`, `Extraction`,
`Simultaneous`, ≈ 3.8k) and `Bridge/Measurement` sit on the tensor side of the interface: since
the hypothesis has `clSoundness`'s shape, they are only used to prove `soundIn_tensor`, through
`clSoundness` itself. They move to Phase 6, where they are needed only if the commuting LIDT
soundness is proved in the shape of the single-codeword vendored `mainFormal` rather than of the
seeded test with `r` codewords. `StrategyDilation.lean` stays: introspection and the Pauli basis
test still use it (Phases 4–5).

Measured: each chain file elaborates in 8–30 s, as before, and a full build after the change
rebuilds the dependents of answer reduction in about a minute. New: ≈ 0.55k lines of Lean in two
files; the chain, ≈ 4k lines, restated in place (≈ 1k lines inserted, 0.85k removed, the Naimark
step among them); blueprint section `sec:ds-mipco-phase3`, 6 nodes, and the answer-reduction
nodes of chapter 6 updated.

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

*Done (#251).* The whole soundness analysis of introspection is stated for a strategy in a
bipartite model, and the matrix statements that remain (Pauli extraction, the quotient value) are
its tensor-product instance. What the setting changed:

- *Local isometries* (`BipartiteModel.LocalIsometry`): a linear isometry of the Hilbert spaces with
  a non-unital `⋆`-homomorphism for each player, intertwining the representations; `V_A X V_Aᴴ` is
  the tensor-product case. A projective measurement is transported with the complement of the
  image added at one outcome (`transportA`), and a strategy and its transport have the same value
  on the transported state (`povmValue_transport`). `isometricPOVM` and its completion error are
  this, in any model.
- *The register model* (`BipartiteModel.reg N I := N.expand (registerEPR I)`) replaces
  `registerState I ξ`, with the ancilla an arbitrary normalized auxiliary model; relabelling,
  splitting, extending and exchanging the register are local isometries (`regRelabel`,
  `regSplit`, `regExtend`, `regSwap`), and the tensor-product case is `tensorExpand` /
  `tensorUnexpand`. The players' algebras of an extension are matrices over theirs, ordered as a
  `⋆`-algebra (`MatrixStar.instPartialOrderStar`), which needs the algebras to be proper.
- *The dilation*: the Naimark steps of the adaptive inductions are Halmos dilations of a Kraus
  family in the first player's algebra (`exists_pvm_dilation`: a nonnegative element of a
  star-ordered ring is a finite sum of squares), with no square root and no finite dimension. The
  ancilla `DilationAncilla A K` has a size `K` chosen along the way, so each Alice stage changes
  the model's type: the iteration returns a model over the second player's algebra packed with its
  algebras (`ModelOver`), and every POVM strategy of it reduces to one of the original model
  (`BipartiteModel.POVMReduces`), which is how a value model dominating the original model
  dominates it. Bob's block is the Alice block on `Ξ.swap`. The inductions run at the same error
  rates.
- *The value*: the extracted strategy is a POVM strategy, so value models dominate POVM strategies
  (`ValueModel.DominatesPOVM`; `val*` through the Naimark dilation, `ω_co` directly).
- *The interface*: `QLD.SoundIn ω M` is `exists_le_qldErr`'s conclusion for the projective
  strategies of `M`, at the error `qldErr`, with `ω` dominating the ancilla model; `QLD.SoundCo`
  asks it in the model of every commuting-operator strategy; `QLD.soundIn_tensor` is
  `exists_le_qldErr`. The value level needs `QLD.ApproxSoundIn ω` (below `ω.val G`, a strategy in
  a model where the test is sound) and, for removing the source padding, `ValueModel.ProjApprox`;
  both hold for `val*` and, given `QLD.SoundCo`, for `ω_co`. The QLD constants are those of the
  closed form of `qldErr` (`QLD.exists_qldErr_le`), a fact about that function alone.
- *The compiler* `Introspection.seven` is defined explicitly (its constants by `Classical.choose`),
  so that `seven_soundIn ω` can be proved for every such `ω`; its `soundness` field is the
  instance at `val*`, and `seven_soundIn_commuting : QLD.SoundCo → seven.SoundIn .commuting`.

Deleted, as dead or without model meaning: the matrix iteration states (`introIterationState`,
`introBobIterationState`, `introTwoSidedState`, `introIterationAux`, `introIterationExtend`),
the ancilla numbering of the QLD adapter, the callback forms of conditional soundness in
`RestrictedProfileSoundness`, and `CanonicalSoundness.lean`. Kept for follow-up cleanups that
each rebuild much of the library: `POVMIn.map_map`, `POVMIn.map_equiv_op`,
`POVMIn.map_pushforward`, `ProjStrat.relabel_PA_op` and `ValueModel.ProjApprox` sit in the files
that first needed them rather than in `Measurement.lean`, `LocalIsometry.lean` and
`ModelStrategy.lean`; and `DecidableEq (DilationAncilla A K)` exceeds `synthInstance.maxSize` in
`open Classical` files, worked around by a local option on the three declarations that need it
until `KrausDilation.lean` provides the instance.

Measured: ≈ 3k lines of Lean in eleven new files and ≈ 110 introspection modules restated in
place (149 files, ≈ 10.7k lines inserted, 7k removed); blueprint section `sec:ds-mipco-phase4`,
17 nodes, and the introspection nodes of chapter 6 updated.

**Phase 5 — the Pauli basis test, with the LIDT soundness as the hypothesis** (report §3.4).
The 23k B lines restated; M1 (the top-level `exists_legal_dilation`, the sandwich's joint
measurement, `Anticomm`) become the Phase 1 lemma; M2, the one use of de la Salle's
orthogonalization at `QLD/Commutation.lean:587`, is removed by threading projectivity to
`hatObs_commutation` and `comm_signed_commutation` (the audit's inference — verify before
relying on it; the fallback is the vendored `B(H)` tier, unconditional); M3:
`PaddedLIDT.lean` consumes `LIDTSoundness`; M4: the statement shape. The ancilla-side EPR
and Weyl material is unchanged. **After: `MIPRE.mipco_eq_core` is conditional on exactly one
named theorem, `thm:lidt-cl-soundness-one` in the commuting-operator model.** Touched:
≈ 25k lines. (Corrected when it was done: the one theorem is the simultaneous contract
`LIDT.Simul.SoundCo`, the commuting form of `thm:lidt-cl-soundness`. The chain applies it at
`r = 1` in the padded model, and answer reduction already needed it at every `r`.)

*Done (#253).* `thm:qld` is proved for the projective strategies of a bipartite model
(`QLD.soundIn_of_lidt`) from two hypotheses on the model: the seeded LIDT test is sound
(`LIDT.Simul.SoundIn`) in every extension of the model by a unit vector, and the value model
dominates every such extension in every unit state. Its tensor-product instance
(`QLD.soundIn_tensor`) is what the main theorem now uses, through introspection; its
commuting-operator instance (`QLD.soundCo_of_lidt : LIDT.Simul.SoundCo → QLD.SoundCo`) gives
`MIPRE.mipco_eq_core_of_lidt`, `MIP^co = coRE` conditional on `LIDT.Simul.SoundCo` alone. What the
setting changed:

- *Models and their maps* (`Foundations/ModelIso.lean`, `ModelEmbedding.lean`,
  `ModelReading.lean`): isomorphisms of bipartite models (`BipartiteModel.Iso`), embeddings (local
  isometries carrying the state and both units), and recuts, which read one extended state as
  models with the finite registers distributed differently between the players. Every regrouping
  that the matrix chain did by `Matrix.reindex` on an explicit state vector is one of these, and no
  state is computed pointwise.
- *The hypothesis in extensions* (`LIDT/ModelTransport.lean`, `LIDT/CoExpand.lean`,
  `Foundations/AmplCommutant.lean`): `LIDT.Simul.SoundIn` passes along isomorphisms and along the
  exchange of the players (the seeded game is symmetric); it holds in every extension of a
  tensor-product model; and `LIDT.Simul.SoundCo` gives it in every extension of a
  commuting-operator model by a unit vector, which is again the model of a commuting-operator
  strategy (the commutant of an amplification is the amplified commutant).
- *The strategy is projective* throughout, as introspection's interface `QLD.SoundIn` asks. The de
  la Salle orthogonalization (M2: `Ortho.lean`, `cor:ortho-from-consistency`), the top-level
  Naimark dilation and the descent from the dilation back to the POVM are gone (M1), and so is the
  matrix statement for POVM strategies (`qld_soundness`), whose descent was matrix-specific and
  which nothing else used. The one dilation left, of the padded strategy in stage 4, is Phase 4's
  Halmos dilation (`exists_pvm_dilation_ge`).
- *The physical model* (`QLD/PhysModel.lean`): stage 5's padded and paired state is an extension of
  the model, read along two cuts, the second the mirror of the first on `M.swap` through
  `blockSwapIso`; `MirrorSimul` needs no field relating the two cuts' states. The swap isometry is a
  local isometry of the model into the register model over the padded extension in an auxiliary
  state (`MirrorSimul.swapPhi`), which is directly an extraction.
- *The errors*: the seeded theorem enters at `δ_sim(q, 4m, d, 1)` (`simA = 40·clA·4^clA`) instead of
  `δ_CL` (M3), and `qldBound` loses the descent's `8√η`; `qldErr` keeps its closed form
  (`exists_qldErr_le`), so introspection's constants do not move.

Deleted: `Descent.lean`, `PhysEmbed.lean`, `RegisterForm.lean`, `ValidAnswers.lean`,
`BinaryForm.lean`, `Introspection/PauliExtraction.lean`, `LIDT/Adapter/Registers.lean`,
`TwoPairs.lean`, `Consistency.lean` and `Ortho.lean`. The valid-answer and qubit forms of
`thm:qld` are the model ones introspection already used (`FieldExtraction.ofQLD`,
`FieldExtraction.toBinary`). Left for a follow-up: `LocalIsometry.withStates` is declared in
`QLD/Soundness.lean`, its one user, rather than beside `toWithState` in `ModelEmbedding.lean`.

Measured: ≈ 5.2k lines in eleven new files; ≈ 50 modules of the chain restated in place (71
files, ≈ 16k lines inserted, 15k removed, 3.2k of them in the ten deleted files); blueprint
section `sec:ds-mipco-phase5`, and the nodes of chapter 3 restated.

**Phase 6 — the low-individual-degree test in the commuting-operator model.** The only new
mathematics, and the item on which the track can fail. The paper-trail check and the audit of
the vendored proof are done (#255, `reports/lidt-co-audit.md`).

*The paper trail.*
- No source proves the soundness of any version of the test for commuting-operator strategies
  with an arbitrary vector state, so `LIDT.Simul.SoundCo` as stated has no paper trail.
- What is proved:
  - finite-dimensional bipartite strategies: JNVWY, machine-checked here as the vendored
    `mainFormal`;
  - synchronous strategies on any tracial von Neumann algebra, in the trace vector: tensor codes
    Theorem 4.1, for the subcube-pair test, one codeword and one bound;
  - tracially embeddable strategies, through `Lin23`'s rounding corollary, with one bound and a
    POVM.
- Lin's two thin spots are confirmed.
  - `thm:soundnessQLDT` is cited, under the wrong key, and asserted without proof to apply
    "directly" to his diagonal-line test.
  - The proof of `lem:simuQLID` is incomplete: its simulated strategy misanswers diagonal lines,
    and its bipartite clauses are commented out.
  - His answer reduction uses only the synchronous, one-sided forms, after rounding.

*A weaker hypothesis suffices.*
- The two consumers are generic in the model: answer reduction (`SoundFinal.lean`) and the Pauli
  basis test (`QLD/Soundness.lean`). Each needs only a near-optimal projective strategy in some
  model where the test is sound.
- So the target can be `SoundFin`: soundness in every model whose two algebras are mutual
  commutants carrying faithful normal tracial states, with an arbitrary vector state (class C).
- The vendored, sorry-free `CommutingRepetition.strict_tracial_reduction` gives the value lemma.
  C is closed under the extensions the consumers use. The plumbing is estimated at 0.75–1.25k
  lines.
- `SoundFin` and `SoundCo` are incomparable as statements. What `SoundFin` buys is a trace on
  both algebras.
- This reverses the earlier reading that "no transfer principle applies". Density does not
  remove infinite dimension, but at the value level it narrows the models in which a proof is
  needed to those with traces.

*The vendored proof on class C.* Everything is dimension-free except three isolated steps:
- **Swap symmetry.** An `H ⊕ H` doubling makes it dimension-free, but no source writes it.
- **The semidefinite program of JNVWY's Lemma 9.2.** It becomes dimension-free through the trace
  on class C, by a derivation not published in this operator form.
- **Orthonormalization.** de la Salle's Theorem 1.2 in finite von Neumann algebras replaces it.
  The vendored tier needs the type I measurable-selection field H5, which is research-grade,
  unless the class is restricted to type II₁ by amplification, at about 4–8k lines.

The earlier mechanism list had two errors. The role-register symmetrization is
tensor-product-specific, not finite-dimensional, and the matrix Chernoff bound is already
dimension-free. The vendored tree is 127,925 lines.

*Recommended route: port the vendored proof to class C.* About 70–120k new lines, mostly
mechanical restatement of machine-checked content, plus the orthonormalization tier. In order:
1. the conditional theorem `SoundFin → MIPCo = IsCoRE`, with the value lemma and the adapters
   that reduce `SoundFin` to the single-codeword core on C (2–3k lines, no new analysis);
2. paper proofs of the doubling and of the summed semidefinite form, and the choice of
   orthonormalization tier;
3. a prototype port of `LDT/CommutativityPoints` (3.5k lines), to measure the line ratio and the
   elaboration time (§6 item 10);
4. the port, with the scalar cascade re-derived into `lidtError`.

The alternatives are compared in the report's §5:
- tensor codes plus `Lin23`'s rounding;
- a synchronous core with value-level rounding (#22, #23);
- `SoundCo` itself, which stays open. It depends on an unreviewed operator-dual derivation and on
  the general orthonormalization tier.

*Decisions for the maintainer.*
- The target: `SoundFin` in place of `SoundCo`. This changes the blueprint statement of the main
  theorem's hypothesis.
- Where the port lives: under `MIPRE/Background/LIDT/`, the only directory that may name
  `MIPStarRE`, or upstream and then vendored.
- The orthonormalization tier.
- Whether to have the operator-dual derivation reviewed.
- The findings to report to Lin (report §5.2).

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
   `lem:orthogonalizationlemma` is the general version (de la Salle, Theorem 1.2). Phases
   1–5 do not need it; Phase 6's recommended route needs it in finite von Neumann algebras
   (`reports/lidt-co-audit.md` §4.3).
9. **The vendored trees are untouchable** except through `scripts/vendor-*.py`; the
   commuting LIDT soundness therefore arrives either as a new vendored tree or as project
   Lean, never as an edit of `MIPStarRE`.
10. **Elaboration cost.** The finite-dimensional operator layer was tuned for it
    (`OpBound.lean` avoids Mathlib's operator norm on purpose). Measured in Phase 1: a generic
    statement elaborates at the cost of its matrix original (`Sandwich.lean`, 7.7 s against
    8.1 s before; `Pasting.lean`, 8 s against 5.6 s; the heaviest consumer, `QLD/Chain.lean`,
    36 s against 41 s), and the matrix lemmas are derived once, in the layer files, so
    that consumers keep calling them rather than the operator form.
11. **Anchored versus direct repetition.** Lin's `prop:Parallelrepetition` is anchored and
    proved in his appendices for both models; the repository's repetition is direct. The
    value-form pipeline (D8) needs only direct repetition, and its `co` form is vendored.
12. **Authority and the paper trail.** The companion proof repository has no `coRE`
    chapter. For Phases 1–5 the mathematics is the repository's own, and the paper of
    record is JNVWY through this blueprint; Lin's paper, cited at its arXiv version, is the
    authority for Phase 6 only, which is where its thin spots (`thm:soundnessQLDT`,
    `lem:simuQLID`) matter — the reason Phase 6 is last and its verification comes first.
    Disagreements between Lin's statements and the Lean are findings to report to Lin, not
    to the companion ledger. The Phase 6 audit (#255) confirmed both thin spots and found
    others in `Lin23`'s Corollary 4.4. Its §5.2 lists what to report.
13. **The class is the computable one.** As for `MIP*`, the Lean class quantifies over
    computable maps to game descriptions, and the polynomial-time class is a separate
    inclusion (Phase 7), as `lem:mipstar-poly-sub` is.

## 7. Milestones

| ID | Deliverable | Size | Status |
|---|---|---|---|
| C0 | Phase 0: the nested criterion, the `ω_co` transport, the value model and the generic halting layer, the conditional reduction, `MIPCo`, `MIPCo ⊆ coRE`, the blueprint | ~1k lines of Lean net | done: #236, then made generic in #239 |
| C1 | Phase 1: the projective commuting-operator model, the dilation lemma, the operator calculus restated with the matrix layer as its instance, the stage interfaces in `Verifier.val ω` | 3k–5k new, ≈ 10k restated | done (#240): (a) #241; (b) #243, #245; (c) #245 |
| C2 | Phase 2: oracularization, repetition and the composition in the model; `mipco_eq_core` conditional on the introspection and answer-reduction clauses in `ω_co` | 2k–3k | done (#247) |
| C3 | Phase 3: answer reduction in the model with `LIDTSoundness` as the hypothesis | 8k–10k touched | done (#249): ≈ 0.55k new, the ≈ 4k-line chain restated; the LIDT adapter deferred to C6 |
| C4 | Phase 4: introspection in the model with `QLDSoundness` as the hypothesis | ≈ 20k touched | done (#251): ≈ 3k new, ≈ 110 modules restated; `mipco_eq_core` conditional on the Pauli basis and LIDT tests in the commuting model |
| C5 | Phase 5: the Pauli basis test in the model; `mipco_eq_core` conditional on the commuting LIDT soundness alone | ≈ 25k touched | done (#253): ≈ 5.2k new, ≈ 50 modules restated; `mipco_eq_core_of_lidt` conditional on `LIDT.Simul.SoundCo` alone |
| C6 | Phase 6: the low-individual-degree test in the commuting-operator model. C6a: `SoundFin → MIPCo = IsCoRE` with the adapters; C6b: the core theorem on class C | C6a 2–3k; C6b 70–120k new, plus an orthonormalization tier (4–8k with a II₁ restriction) | audit done (#255, `reports/lidt-co-audit.md`); the target, the port's location and the orthonormalization tier await the maintainer |
| C7 | Phase 7: the paper's class `MIP^co_{1,1/2}(2,1)` | ~1k | open |

C1 is the prerequisite of everything after it; C3 and C4 need only C1 and are independent
of each other; C5 needs C4's interface; C6 is independent of C3–C5 in its mathematics and is
what they all wait for. Each of C2–C5 ends with a sharper conditional theorem, so progress
is visible in `MIPRE/MIPCo.lean` at every milestone.
