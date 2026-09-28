# The commuting-operator class, `MIP^co = coRE`: plan

**Status: Phase 0 in progress (#235).** The conditional theorem — `MIP^co = coRE` given
the commuting-operator soundness of gap compression — with all of its plumbing.

Written 2026-09-28, after the explicit separation (#222) and the paper's class (#230–#233).
Target: Lin's theorem `MIP^co = coRE` (`Lin25`, arXiv:2510.07162, STOC 2026), proved by
reusing the value-form compression architecture of this repository.

Sources read: Lin's LaTeX source (supplied by the maintainer; `Seqandcompression.tex`,
`CompressionCond.tex`, `Introspection.tex`, `Answerreduction.tex`, `ARsoundnessproof.tex`,
`QRsoundnessproof.tex`, `CondLineardist.tex`, `Parallelrepetition*.tex`, `Preliminary.tex`),
the statements of `Lin23` (arXiv:2304.01940) as Lin's paper cites them, and, here,
`Foundations/Compression.lean`, `Halting/*`, `ClassMIPStar.lean`, `Tsirelson/*`,
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

Everything else is the proof of that hypothesis, and it is new mathematics for this
repository: the soundness analyses of introspection, answer reduction and oracularization
for commuting-operator strategies (Lin's model `t = co`), carried out on *tracially
embeddable* strategies. That re-proves most of the finite-dimensional analysis — about
240k lines here, vendored trees included — over tracial von Neumann algebras, and none of
the finite-dimensional lemma trees can be reused as they are, because the objects
(operators on `L²(𝒜, τ)`, the commutant, the standard form) are different. It is the largest
single item after the main theorem, and §5 sizes it phase by phase.

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
| compression soundness, model `co` | `GapCompression.Sound ValueModel.commuting`, a hypothesis | Phases 1–5 |
| parallel repetition, model `co` | `thm:direct-repetition-co`, vendored and sorry-free (`MIPRE.Repetition.commutingOperatorValue_repeat_le`); direct, not anchored (§6 item 8) | done |
| tracial density | `thm:tracial-density`, vendored (`MIPRE.Repetition.tracialDensity`) | done |
| rounding, model `co` | not formalized; `thm:almost-sync` is #22 (finite dimension) and #23 (commuting) | Phase 1 |
| tracial value at most bipartite value | `lem:tracial-le-co`, #29 | Phase 1 |
| Pauli basis rigidity, model `co` | not formalized | Phase 2 |
| introspection soundness, model `co` | not formalized | Phase 3 |
| low-individual-degree test soundness, model `co` | not formalized | Phase 4 |
| oracularization soundness, model `co` | not formalized | Phase 5 |

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
| the class | `Foundations/ClassMIPStar.lean`, `Halting/Corollaries.lean` | `IsRE`, `IsCoRE`, `MIPClass ω`; `MIPStar := MIPClass .tensor`, `MIPCo := MIPClass .commuting`; `MIPClass.isRE` from `LowerRE`, `MIPClass.isCoRE` from `UpperRE`; `re_subset_mipclass_of_reduction`, `mipclass_eq_re_of_reduction`, `core_subset_mipclass_of_reduction`, `mipclass_eq_core_of_reduction` |
| the co instances | `Foundations/ClassMIPCo.lean`, `MIPRE/MIPCo.lean` | `MIPCo.isCoRE` (unconditional), `halting_reduction_commuting_of`, `core_subset_mipco_of`, `mipco_eq_core_of`; `halting_reduction_commuting`, `core_subset_mipco`, `mipco_eq_core`, each with the single hypothesis `MIPRE.gapCompression.Sound ValueModel.commuting` |
| the Tsirelson chapter | `Foundations/Tsirelson/Conditional.lean` | `HaltingReductionQuantum` and `CommutingUpperRE` are `ValueModel.tensor.HaltingReductionRE` and `ValueModel.commuting.UpperRE` |
| blueprint | chapter 8 | `def:value-model`, `def:core`, `def:mipco`, `lem:mipco-sub-core`, `lem:compressible-criterion-nested` (chapter 4), `def:compression-co-sound`, `thm:halting-co`, `thm:mipco-eq-core`, `rem:mipco-route`; `thm:halting`, `lem:halting-semidecider`, `def:mipstar-computable`, `lem:mipstar-sub-re` and `thm:mipstar-eq-re` cite the generic declarations |

What is *not* generic, and why. `classA`, the perfect-PCC class, is the tensor class in
every instance, because the criterion consumes the tensor completeness of compression (§3).
The two semideciders are different programs, because `val*` is r.e. from below and `ω_co`
from above; that asymmetry is exactly what makes one class `RE` and the other `coRE`, and
`Halting.exists_sem_upper` needs `tab` made locally irreducible or elaboration times out.

The class is the computable one, as `MIPRE.MIPStar` is (`def:mipstar-computable`): a
computable map from strings to game descriptions with `ω_co = 1` on the language and
`ω_co ≤ 1/2` off it. The paper's polynomial-time class is Phase 6.

## 5. Phases 1–5: the commuting-operator soundness of compression

The hypothesis to discharge, stated in the bipartite value of `Verifier.game`:

```text
G.Sound ValueModel.commuting : ∀ V lam n, V.IsBounded lam → G.C₀ ≤ n →
  V.val .commuting (2 ^ n) ((2 ^ n) ^ lam) ≤ 1/2 →
  (G.output (V.sampler.prog, V.decider.prog) lam).val .commuting n (G.bound.eval (n + lam)) ≤ 1/2
```

for `G = MIPRE.gapCompression`, i.e. the pipeline of `Background/Pipeline.lean` with the
soundness clause of each stage read in `ω_co`. Lin proves each stage's `co` soundness on
tracially embeddable strategies and transfers to all commuting-operator strategies by
density. The phases follow his sections; each one is a campaign of the size of the
finite-dimensional one it mirrors, and the line counts below are of the finite-dimensional
Lean it would parallel, not estimates of the port, which cannot reuse them.

**Phase 1 — the vocabulary and the value dictionary** (`Preliminary.tex` §§ tracially
embeddable strategies, symmetric strategies, rounding). Tracially embeddable strategies
(`L²(𝒜, τ)`, the standard form, `σ|τ⟩`, Alice in `𝒜`, Bob in the commutant `𝒜'`, the
switching identity `A|τ⟩ = A^op|τ⟩`); their correlations and values; the density theorem
in a usable form (a bound on the value over tracially embeddable strategies is a bound on
`ω_co`, the value being `1`-Lipschitz in `ℓ¹`); the rounding theorem for the commuting
model (`Lin23` Theorem 4.1 / de la Salle 2023), which every stage that assumes synchronous
strategies needs through balancedness; and `lem:tracial-le-co` (#29). Mathlib has
`VonNeumannAlgebra` as a definition and nothing of the standard form; the repository has a
GNS construction for tracial states on `*`-algebras (`Foundations/GNS.lean`) and the
vendored tracial density theorem. New: 3k–6k lines, and the foundation of everything
after it.

**Phase 2 — rigidity of the Pauli basis test** for tracially embeddable strategies
(`Introspection.tex`, `thm:soundnessPaulibasis`; from `Lin23` Theorem 6.4). Lin's test is
de la Salle's commutation/anticommutation test, not the low-degree test the main theorem's
introspection uses, so the finite-dimensional `thm:qld` chain (`Background/QLD`, 35k lines;
`Foundations/LowDegree`, 12.6k) is not what gets ported; what gets proved is a
Gowers–Hatami-style stability statement over `L²(𝒜, τ)`, with the two isometries
`V_A, V_B` and the auxiliary state of Lin's statement. Lin's paper derives it from `Lin23`
by modifications described in prose ("a larger constant" in one inequality, two equations
"changed to incorporate the extra question labels"), which is the thinnest paper trail on
the introspection side. New: 15k–30k lines.

**Phase 3 — introspection soundness in the `co` model** (`prop:QuestionReduction`,
`thm:Introspectgame`, `QRsoundnessproof.tex`). The finite-dimensional analysis is
`Foundations/Introspection` (34.5k lines) and `Background/Introspection` (8.4k). The
sampler and decider programs, the typed presentation and the running-time accounting are
model-independent and reuse. New: 20k–40k lines.

**Phase 4 — answer reduction in the `co` model** (`prop:AnswerReduction`,
`ARsoundnessproof.tex`). The classical part — the PCP of proximity, the succinct 5-SAT
encoding, the low-degree encoding — is model-independent (`Background/AnswerReduction`,
10.6k lines; `Foundations/SAT`, `Foundations/CL`) and reuses. The quantum part needs the
soundness of the quantum low-individual-degree test for synchronous tracial strategies
(`thm:soundnessQLDT`) and its simultaneous version (`lem:simuQLID`). The vendored LIDT
(`Background/LIDT`, 136k lines) is finite-dimensional. This is where Lin's paper trail is
thinnest: the theorem is cited as JNVWY's tensor-code soundness "directly applied" to
individual-degree polynomials, extended to tracially embeddable strategies by `Lin23`
Corollary 4.4, and the appendix proving the simultaneous version is commented out in the
source. It needs its own verification before any formalization. New: the largest item;
40k–80k lines if it parallels the vendored proof, unknown otherwise.

**Phase 5 — oracularization, repetition and assembly** (`lem:oratransformation`, the
`co` clause of `prop:Parallelrepetition`, `Background/Pipeline.lean`). Oracularization
soundness in the `co` model through balancedness and rounding; repetition through the
vendored `commutingOperatorValue_repeat_le`, which is *direct* repetition — Lin's
proposition is anchored, but the value-form pipeline here already uses direct repetition
(D8 of `planning/repetition-port.md`), and the vendored theorem is sorry-free; then the
composition of the three `co` clauses into `Sound ValueModel.commuting` for
`MIPRE.gapCompression`, along the
existing `GapCompression.ofPipeline`. New: 5k–10k lines, plus a vendoring of the `co`
clause of the oracularization if it is done upstream.

**Phase 6 (optional) — the paper's class.** `MIP^co_{1,1/2}(2,1)` with a polynomial-time
sampler and decider, mirroring `MIPStarPoly` (#230–#233), and Lin's `k-CLMIP^co`. About
1k lines.

## 6. Delicate points

1. **Two commuting values, never interchanged.** The bipartite `ω_co`
   (`MIPRE.commutingOperatorValue`: POVMs `E`, `F` on one Hilbert space, commuting) and the
   tracial `valco` (`MIPRE.commValue`: a `*`-algebra with a tracial state and one PVM family
   played by both players). The criterion, the classes, the semidecider,
   `Sound ValueModel.commuting` and `MIPCo` are all in `ω_co`, so nothing is transferred at
   the criterion. `valco ≤ ω_co` is
   #29 and unproved; the reverse fails in general and holds up to rounding for synchronous
   games with proportional diagonal weight (`thm:almost-sync`, #22/#23). The transfers
   happen inside the stages' proofs, in Phases 1–5, where Lin makes them.
2. **The nested criterion.** The search must semidecide the complement of the *larger*
   class, the compressor must preserve the *smaller* one, and the "no" string must lie in
   the smaller. The Lean of Phase 0 is the check.
3. **The semidecider runs on the tabulation.** `tab x n` is total, and `tab_val` holds
   for `n`-bounded strings only, as `tab_value` does. `classOne` is defined on the
   tabulated game so that the non-halting conclusion needs no boundedness; the halting
   conclusion reads `ω_co(tab) ≤ 1/2` through `tab_val` from the boundedness that
   `classB ω_co` carries.
4. **`ω_co = 1` without a strategy.** It is `¬ (ω_co < 1)` and `ω_co ≤ 1`. No perfect
   commuting-operator strategy is constructed anywhere, consistent with `thm:separation`.
5. **Density is approximate.** Tracial density is an `ℓ¹`-closure statement, so a
   soundness bound proved for tracially embeddable strategies transfers to `ω_co` with an
   arbitrarily small loss; each stage's soundness has to be stated with slack (it is, in
   Lin's `1 − ε ⇒ 1 − s(ε)` form), and the final `1/2` comes from repetition.
6. **Vendored orthonormalization is finite-dimensional.**
   `Background/Orthonormalization/Orthogonalization` is de la Salle's orthogonalization
   lemma in finite dimension; Lin's `lem:orthogonalizationlemma` is the general von Neumann
   algebra version (de la Salle, Theorem 1.2), and `cor:orthogonalizationlemmasync` is
   `Lin23` Corollary A.7.
7. **Anchored versus direct repetition.** Lin's `prop:Parallelrepetition` is anchored and
   proved in his appendices for both models; the repository's repetition is direct. The
   value-form pipeline (D8) needs only direct repetition, and its `co` form is vendored.
8. **Authority.** The companion proof repository has no `coRE` chapter, so for this track
   the paper is Lin's, cited at its arXiv version; the blueprint nodes carry no
   `\ledgernode`, and disagreements between Lin's statements and the Lean are findings to
   report to Lin, not to the companion ledger.
9. **The class is the computable one.** As for `MIP*`, the Lean class quantifies over
   computable maps to game descriptions, and the polynomial-time class is a separate
   inclusion (Phase 6), as `lem:mipstar-poly-sub` is.

## 7. Milestones

| ID | Deliverable | Size | Status |
|---|---|---|---|
| C0 | Phase 0: the nested criterion, the `ω_co` transport, the value model and the generic halting layer, the conditional reduction, `MIPCo`, `MIPCo ⊆ coRE`, the blueprint | ~1k lines of Lean net | done: #236, then made generic |
| C1 | tracially embeddable strategies, `L²(𝒜, τ)`, density and rounding in usable form, `lem:tracial-le-co` | 3k–6k | open |
| C2 | Pauli basis test rigidity, model `co` | 15k–30k | open |
| C3 | introspection soundness, model `co` | 20k–40k | open |
| C4 | answer reduction soundness, model `co`, with the low-individual-degree test | 40k–80k | open; verify the paper trail first |
| C5 | oracularization soundness, model `co`; `Sound ValueModel.commuting` for `MIPRE.gapCompression` | 5k–10k | open |
| C6 | the paper's class `MIP^co_{1,1/2}(2,1)` | ~1k | open |

C1 is the prerequisite of C2–C5, which are otherwise independent of one another; C4
should not start before its paper trail has been checked against JNVWY and `Lin23`.
