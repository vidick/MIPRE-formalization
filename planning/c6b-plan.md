# C6b: the low-individual-degree test in II₁ finite pairs

Tracking: #259, and the C6 row of `planning/mipco-track.md` (Phase 6). Written 2026-10-01, after the
maintainer chose the II₁ orthonormalization tier, from a design round of six parts: four
surveys of the code and four paper proofs, each proof checked by three independent skeptics and
revised, most of the new steps prototyped in Lean. The proofs are recorded in
`reports/c6b-paper-proofs.md`; the audit that sized the port is `reports/lidt-co-audit.md`.

**Status (2026-10-02).** The orthonormalization tier is complete (T1–T5 below). De la Salle's
Theorem 1.2 holds unconditionally in every von Neumann algebra with no nonzero abelian projection
and a faithful tracial vector functional (T1), and in both algebras of every dyadic pair, a class
that excludes abelian projections by a trace estimate (T2;
`Orthonormalization.povm_orthogonalization_dyadicPair`, `…B`). `SoundFin` asks only for dyadic
pairs, and `ω_co` is approached in them through an amplification by the twisted Pauli algebra
(T3–T5), so `mipco_eq_core_of_lidtFin` holds with the narrowed hypothesis. In the port, M0 and
M1 are done: the base layer over a symmetric model `SymModel 𝔓 K` (18 modules, 5.7k lines) and
`CommutativityPoints` over it (7 modules, 3.0k lines; `Co.CommutativityPoints.commutativityPoints`
and its answer-valued form), together at 1.02× the vendored elaboration time. M1 meets the
acceptance rule of §4 item 3 in every file, M0 in all but the four recorded under "Port
conventions". The sizes of M2–M14 are re-estimated from them (§3). M2 and M9 are done too. M2 is
the doubling of a finite pair, `D(M)` as a symmetric model, a finite pair and, for a dyadic pair, a
dyadic pair, with the symmetric strategy and orthonormalization in it (8 modules, 2.75k lines). M9
is the summed semidefinite form, which replaces JNVWY Lemma 9.2, solved componentwise in `D(M)` and
pulled back to the players' algebras (3 modules, 0.93k lines). What M2 and M9 leave open is
recorded in their rows: unsymmetrization beyond its arithmetic goes to M13, the semidefinite
interface adapter to M10, and supplying `ζ > 0` at the in-core call site of orthonormalization, by
threading `1 ≤ params.d` from `SoundIn`, to M14 (the case `ζ = 0` itself is not proved, and that call
site does not need it once this is done). M3 and M5 are done as well (2026-10-02): the rest of
`Preliminaries` (23 modules, 3.37k lines), whose load-bearing results are the switch sandwich and
the self-consistency calculus (`Co.Preliminaries.switchSandwich`,
`twoNotionsOfSelfConsistency`, `selfConsistencyImpliesDataProcessing`, `completingToMeasurement`),
and `ExpansionHypercubeGraph` (5 modules, 0.85k lines), whose `localToGlobal` holds for every
family on every vector state by Gram positivity in place of the matrix realization; at 0.62× and
0.24× the vendored elaboration time, and well under their estimated sizes (§3). About 69–83k
lines remain (M4, M6–M8, M10–M14), not counting the three items above, and the port is 86–100k in
all. M4, M6–M8 and M10–M14 are open.

## 1. The target, and what the II₁ tier turned out to need

C6a reduced `MIP^co = coRE` to `LIDT.Simul.SoundFin`: the seeded CL test is sound
(`LIDT.Simul.SoundIn`) in every finite pair (`BipartiteModel.IsFinitePair`). C6b proves it, by a
port of the vendored finite-dimensional proof (`MIPRE/Background/LIDT/MIPStarRE/LDT`, the theorem
`mainFormal`) to finite pairs, with three steps replaced (audit §4): swap symmetry by an `H ⊕ H`
doubling, the semidefinite program of JNVWY Lemma 9.2 by a summed operator form proved with the
trace, and the finite-dimensional orthonormalization by de la Salle's Theorem 1.2.

The tier decision is what the orthonormalization can be applied to. The vendored development
proves Theorem 1.2 unconditionally only for II₁ *factors*; the algebras of a finite pair are not
factors, and type I pairs with diffuse centre are finite pairs (`FinitePair.lean`, module doc).
The design round found that the II₁ tier needs exactly three things, and no type decomposition:

1. **A centre-valued trace with comparison** (field H3 of the vendored interface, at the
   projection `1`) for an algebra with a faithful tracial vector functional, factor or not. With it
   the vendored II₁-factor proof goes through verbatim for any algebra without abelian
   projections. The construction is elementary: the centre-valued trace of `x` is the central
   element of minimal 2-norm with the pairings of `x`, and comparison is the vendored greedy
   argument with central supports in place of the factor step (report §2). **Done (T1).**
2. **No nonzero abelian projection**, from unital `2ⁿ×2ⁿ` matrix units for every `n` — a trace
   estimate, `|ι| · τ(p) ≤ 1` for an abelian projection `p` and a unital `ι×ι` system, with no
   comparison theory (report §3, Theorem K). The class becomes `M.IsDyadicPair`, a structure
   with the fields `isFinitePair`, `unitsA : HasDyadicUnits 𝒜` and `unitsB : HasDyadicUnits ℬ`,
   closed under the exchange of the players and ancilla extensions (**done, T2**); for the
   doubling only the algebra-level clause `HasDyadicUnits.prod` is done, and its `IsFinitePair`
   half belongs to M2.
3. **Amplification in the value lemma**: a tracial strategy on `M` lifts along `a ↦ a ⊗ 1` to the
   vendored tensor product `tensorStep M B` with the same correlation, and the standard form of
   `tensorStep M B` is a dyadic pair as soon as `B` has dyadic units (report §3, Theorems A and
   T). This needs a standard tracial algebra `B` with dyadic matrix units, which neither
   repository had: T4 constructs one, the twisted Pauli algebra. **Done (T3–T5).**

So `SoundFin` is narrowed to dyadic pairs (a weaker hypothesis, so a stronger conditional
theorem), and the port proves `SoundIn M` for every dyadic pair `M`.

## 2. Decisions

| # | decision | status |
|---|---|---|
| 1 | target `SoundFin` in place of `SoundCo` | taken (C6a, #258) |
| 2 | where the port lives | default taken: `MIPRE/Background/LIDT/Co/`, the only directory that may name `MIPStarRE`; asking upstream (`LionSR/MIPStarRE`) to generalize its base layer instead stays possible and changes the location only |
| 3 | orthonormalization tier | taken 2026-10-01: II₁, realized as items 1–3 of §1 |
| 4 | review of the operator-dual derivation (audit §4.2, route A1) | not on C6b's path: the summed form is proved with the trace (report §5); open for A1 only |
| 5 | findings to report to Lin (audit §5.2) | open |

## 3. Work packages

Sizes are new Lean lines. "Measured" means a prototype compiled against this tree during the
design round (not committed); everything else is an estimate with the basis given in the report.
In a row marked done, the status column gives the committed modules and their sizes, with
docstrings.

**The tier (T).**

| WP | content | location | size | status |
|---|---|---|---|---|
| T1 | centre-valued trace and comparison at `p = 1` (`exists_isCenterValuedTrace`); Theorem 1.2 without abelian projections (`povm_orthogonalization_of_isCenterValuedTrace`, `povm_orthogonalization_vecTrace`); the finite-pair form in model vocabulary (`povm_orthogonalization_finitePair`) | `MIPRE/Background/Orthonormalization/{CenterTrace,CenterTraceClauses,CenterComparison,NoAbelian,FinitePairOrtho}.lean` | ≈ 1.25k (measured) | done |
| T2 | matrix units: `IsMatUnits`, `HasDyadicUnits` and their transport (∗-homs, `ᵐᵒᵖ`, matrices, products); the trace bound and no abelian projections (Theorems K, K′); `IsDyadicPair` with `swap` and `expand` | `MIPRE/Foundations/` | 0.38–0.46k (measured, 0.4k) | done: `MIPRE/Foundations/MatUnits.lean` (the units and their transports, ≈ 0.15k) and `MIPRE/Foundations/DyadicPair.lean` (≈ 0.44k), ≈ 0.6k; more than the prototype for the docstrings, the trace functional as a linear map with named lemmas (`VecTrace.tr`) and `IsDyadicPair` as a structure. Blueprint `def:dyadic-units`, `lem:dyadic-units-closure`, `thm:no-abelian-dyadic`, `def:dyadic-pair`, `lem:dyadic-pair-closure` |
| T3 | amplification: `amplify T B` with `amplify_correlation`; the standard form of `tensorStep M B` is a dyadic pair, and so is its ancilla extension | `MIPRE/Background/Repetition/` | ≈ 0.1k (measured) | done: `MIPRE/Background/Repetition/Amplify.lean`, 157 lines, with the value consequence `exists_tracialStrategy_isDyadicPair`. Blueprint `lem:amplification-dyadic` |
| T4 | the algebra `B`: a `StdTracialAlgebra.{0}` with unital dyadic matrix units in `B.A` | `Foundations/MatUnits.lean` (≈ 0.25k) and `MIPRE/Background/Repetition/PauliAlgebra.lean` (≈ 0.5k) | 0.75–0.85k | done: `PauliSites` in `MatUnits.lean` (≈ 0.23k) and `MIPRE/Background/Repetition/PauliAlgebra.lean` (683 lines; `Pauli.pauliStd`, `Pauli.pauliStd_hasDyadicUnits`), ≈ 0.92k. Blueprint `lem:pauli-sites-units`, `lem:pauli-algebra`. Chosen 2026-10-01: the twisted Pauli (CAR) algebra (report §3). Both candidates were prototyped in Lean, sorry-free (Pauli 688 lines, the ultraproduct 426); Pauli's units are unital in `B.A` itself, so it gives `HasDyadicUnits B.A` as T2–T3 state it, while the ultraproduct's are unital only after representation and would need a second predicate and an adapter |
| T5 | restate C6a to the class: `SoundFin`, its `expand`, the value lemma on `amplify T B`, the three consumers, blueprint `def:finite-pair`, `lem:co-value-finite-pair`, `def:lidt-sound-fin`; `mipco_eq_core_of_lidtFin` keeps its text | C6a's files | 0.08–0.15k + blueprint | done: `MIPRE/Background/Repetition/DyadicApprox.lean` (50 lines, `commutingFinitePairApprox` on the amplified strategy) and `MIPRE/Background/Orthonormalization/DyadicOrtho.lean` (57 lines, the form the port's orthonormalization sites call); `CommutingFinitePairApprox` moved to `DyadicPair.lean`; about 0.1k lines changed in C6a's six files. Blueprint: the three nodes restated with their labels, and `cor:orthonormalization-dyadic-pair` |

**The port (M)**, under `MIPRE/Background/LIDT/Co/`, mirroring the vendored LDT tree file by file,
namespace `MIPRE.LIDT.Co`, vendored declaration names kept so that a script can pair them.

The sizes of M3–M14 were re-estimated after M1 (2026-10-01), with the earlier figure in
parentheses. Basis: ported lines ≈ r × (vendored quantum-declaration lines) + 58 × (files), the
classical declarations being imported at no cost. `scripts/port-classify.py` sorts each vendored
declaration as quantum (its text mentions the state, `ev`, measurements, placements, `ᴴ`,
strategies or matrices; the pattern and the line accounting are in its docstring) or classical,
lines counted by `wc -l`; on `CommutativityPoints` it finds 451 classical lines, against about
500 counted by hand. The quantum-line counts below are its output, for example
`python3 scripts/port-classify.py Commutativity Pasting`, and for M10
`python3 scripts/port-classify.py SelfImprovement --exclude SelfImprovement/MatrixRealization
--exclude SelfImprovement/Theorems/Results/SdpMatrixBridge.lean`. The ratio r is a ported file's
lines from its first declaration on, over its vendored file's quantum-declaration lines, headers
excluded on both sides (`python3 scripts/port-classify.py --ratio --per-file CommutativityPoints`).
It was measured at 0.95 on M1 (per file: `Defs` 0.88, `Approximation` 1.00, `SharedHelpers/Core`
0.82, `SharedHelpers/SharedLine` 0.94, `LiftBridges` 1.09, `DropBridges` 0.95, `AnswerTheorems`
0.92) and at 0.78 on M0, where it falls to 0.24–0.52 in the files whose matrix-entrywise proofs
became one-line model lemmas (`OperatorExpectations`, `TensorPlacement`, `ComparisonCore`,
`DistanceBounds`) and is 0.76–1.34 elsewhere (1.58 in the 24-line `MeasurementLift`, 6.0 in the
tactic file, which adds its `example`s); 58 lines is M1's header per file, with its `Not ported`
list (the vendored header is 38). The remaining directories have 25–40 matrix-token lines
per 1k lines, most of them `ᴴ`, which translates one to one (about 100 in
`MakingMeasurementsProjective`), and 8–22 swap uses each, so they resemble `CommutativityPoints`
and `Test/StrategyCore` rather than `OperatorExpectations`: r is 0.85–1.0 unless the row says
otherwise. The design round's probe ratios (§5) held only where matrix proofs collapse into
keystone lemmas: M0 came to 5.70k lines against 4.4–5.3k estimated, M1 to 3.01k against
1.9–2.7k.

| WP | content | depends | vendored → ported | status |
|---|---|---|---|---|
| M0 | base layer: the symmetric model `SymModel 𝔓 K` (unbundled; local C*-algebra `𝔓`, Hilbert space `K` a parameter, state `Ψ`, flip `J`), `ev = Op.qform`, the three swap facts as lemmas, generic `SubMeas`/`Measurement`/`ProjMeas`, placements as `map` along ∗-homs, the ev-level defects and relations, the `Preliminaries` slice CP needs, `SymStrat`, and the operator-valued `averageOperatorOverDistribution` | — | 6.06k → 4.0–4.6k, plus 0.4–0.7k for the operator averages | done: 18 modules under `Co/{Basic,Preliminaries,Test,Tactic}/`, 5,697 lines for 7,691 vendored (0.74), non-import elaboration 51.8 s against 53.0 s (0.98×), measured under "Port conventions". Blueprint `def:sym-model`, `lem:sym-model-swap` |
| M1 | prototype: `CommutativityPoints` → `Co.CommutativityPoints.commutativityPoints`, with a swap probe (CP never uses the flip) | M0 | 3.46k → 1.9–2.7k | done: 7 modules under `Co/CommutativityPoints/`, 3,008 lines for 3,464 vendored (0.87 overall; r = 0.95 on the ported declarations, net of headers, and 1.00 including them, the ≈ 0.45k classical lines being imported), elaboration 16.8 s against 14.2 s (1.19×); `commutativityPoints` and the answer-valued `answerCommutativityPoints`, both ported (§5); `port-pairing.py --check`: 0 missing in every file. The swap probe is recorded in §5. Blueprint `lem:co-commutativity-points` |
| M2 | the doubling: `D(M)` as a symmetric model and as a finite pair, no abelian projections in it, the role-average identity, the symmetric strategy, unsymmetrization at the vendored cut, orthonormalization in `D(M)` | M0, T1, T2 | new 0.95–1.45k; replaces about 3.96k vendored lines | done, except Theorem E beyond its arithmetic. 2,748 lines in 8 modules. `MIPRE/Foundations/FinitePairOrder.lean` (271) holds the ⋆-isomorphisms of a finite pair's algebras onto the commutants, `IsFinitePair.equivA`/`equivB`, and the order agreement `IsFinitePair.nonneg_iff_A`/`_B` (report §4 Lemma 10 = §5 Lemma 13), now the library's one order-agreement lemma. `MIPRE/Foundations/Doubling.lean` (473) holds block-diagonal operators on `H ⊕ H`, `VecTrace.diag2` and `NoAbelianProj`. Then `Co/Doubling/Model.lean` (219): `Doubling.model hM hψ : SymModel (Loc M) (Ampl (Fin 2) M.H)` over `Loc M = centralizer M.opsB × centralizer M.opsA`. `FinitePair.lean` (272): Theorems A and F, `isFinitePair`, `L_nonneg_iff`, `equiv : 𝒜 × ℬ ≃⋆ₐ Loc M`, `isDyadicPair`, `noAbelianProj_iff`. `Halving.lean` (257): Theorem C, `bornProb_model_eq`, `qBipartiteConsDefect_model`, `dis_model`, `inconsistency_model`. `Strategy.lean` (452): Theorem D, `symmStrat`, `symmStrat_isGood_three_mul`, and the arithmetic of E, `bipartiteConsError_components_le_two_mul`. `Orthonormalization.lean` (384): Theorem G for `ζ > 0`, stated over any symmetric model whose bipartite reading is a finite pair without abelian projections in its first player's operators (`SymModel.orthonormalization_of_isFinitePair` and its relational form `_sddRel`, the shape M8's ported `MakingMeasurementsProjective.orthonormalization` and M10's generic consumer need), with `Doubling.orthonormalization_model` its specialization to `D(M)`; and Proposition H, `SymModel.L_cfc`/`R_cfc` for an injective placement and `Doubling.cfc_mem_opsA`. And `Co/Test/StrategyBiProj/Measurements.lean` (420): the two-space surrogate `fail_M` (`ProjStrat.lowIndividualDegreeFailureProbability`), ported. Without the surrogate, which the estimate left to the port base, 2,328 new lines against 0.95–1.45k: the docstrings, both directions of every transport, the translation to the report's `𝒜 × ℬ` and the POVM transports were not in the estimate. Theorem B is M0's. Open: Theorem E itself, which needs the point consistency of the ported `mainInduction` (M12) and is M13's, with the two-space tail; supplying `ζ > 0` at the in-core call site of Theorem G, by threading `1 ≤ params.d` from `SoundIn` (M14), the case `ζ = 0` itself not being proved and not needed once this is done; Remarks R1–R2, off the route. Elaboration was measured with `-DElab.async=false` in one run per file at load 0.7–1.0, with a 1 s threshold, and was not compared with the vendored files. No declaration takes 3 s. The largest are the `equivHom`/`equivInv` definitions of `FinitePair.lean` at 2.5 and 2.6 s, `inconsistency_model` and `qBipartiteConsDefect_model` of `Halving.lean` at 2.3 s, and `cfc_mem_opsA` at 1.8–2.0 s; `orthonormalization_model` takes 1.1 s. (An earlier measurement put `L_cfc`, `R_cfc` and `cfc_L_mem_range` at 3.4–4.1 s when stated for `D(M)`, most of it synthesizing the functional calculus of `Ampl (Fin 2) M.H →L[ℂ] _` in the header; stated over a symmetric model they take under 1 s.) Blueprint `lem:finite-pair-order`, `def:doubled-model`, `lem:doubled-model-finite-pair`, `lem:doubled-model-role-average`, `lem:doubled-model-no-abelian`, `thm:doubled-symmetrization`, `thm:doubled-orthonormalization` |
| M3 | the rest of `Preliminaries` | M0 | 7.64k → 5.0–7.2k (6.0–7.0k): 6.17k quantum lines in 23 files, `Polynomials.lean` classical; r 0.6–0.95, `SwitchSandwich`, `Triangles` and `CauchySchwarz` being close kin of `ComparisonCore` and `DistanceBounds`, which ported at about 0.5 | done: 23 modules under `Co/Preliminaries/`, every vendored file but the classical `Polynomials.lean`, 3,421 lines for 7,505 vendored (0.46; r = 0.36 on the ported declarations, net of headers, 2,215 lines for 6,174 quantum lines before the review, whose shared expansion changed that by a few lines), below the estimate for the reasons under "Departures in M3 and M5"; non-import elaboration 38.1 s against 63.1 s (0.60×), every file within the 2× rule (largest `BipartiteSelfConsistency/Completion`, 1.03×), no declaration at 2 s (largest `globalVarianceTraceForm_eq_closedForm` of M5, 1.40 s, and `switchSandwich_rightTransfer`, 1.37 s asynchronously at load 1.0 and 1.47–1.72 s with `-DElab.async=false`, vendored 3.85 s; 1.86–2.20 s before the review's shared expansion); `port-pairing.py --check`: 0 missing, 10 classical declarations imported, 4 new. The switch sandwich (`switchSandwich`, `SwitchSandwichStmt`), the two notions of self-consistency (`twoNotionsOfSelfConsistency`, `bipartiteSSC_implies_localSSC_liftLeft`, `otherTwoNotionsOfSelfConsistency`), data processing (`selfConsistencyImpliesDataProcessing`) and completion (`completingToMeasurement`), with every swap and normalization hypothesis dropped. Blueprint `lem:co-switch-sandwich-self-consistency` |
| M4 | `Test` core and `MainInductionStep` definitions and statements | M0, M3 | 1.92k → 1.7–2.0k (1.5–1.8k): `MainInductionStep/{Defs,Statements}` and `Test/{SchwartzZippelStep,StrategyPolynomialFamilies}`, 1.64k quantum lines in 4 files, r 0.9–1.05 | open |
| M5 | `ExpansionHypercubeGraph`: the scalar part by import; `localToGlobal` by Gram positivity in place of its matrix realization | M0 | 3.8k → 1.0–1.9k (1.0–1.6k): M1 does not inform the Gram-positivity rewrite; the upper end ports every quantum declaration outside `MatrixRealization` (1.62k) at the M1 ratio | done: 5 modules under `Co/ExpansionHypercubeGraph/{Defs,Theorems}/`, `MatrixRealization/{Core,TraceForms}` not ported but replaced by Gram positivity (`re_combinedTraceForm_nonneg`), 852 lines for 3,808 vendored (0.22; r = 0.26), below the floor of the estimate; non-import elaboration 9.0 s against 37.6 s for the whole vendored directory (0.24×; 0.31× against its five counterparts alone), largest declaration `globalVarianceTraceForm_eq_closedForm`, 1.50 s. `localToGlobal params A V : globalVariance params A V ≤ m · localVariance params A V` for every `A : Point params → (K →L[ℂ] K)` and vector state `V`, and `localToGlobalBipartite` for `u ↦ S.L (A u)`; no swap fact and no new keystone positivity used. Blueprint `lem:co-local-to-global` |
| M6 | `GlobalVariance` | M0, M3, M5 | 5.3k → 4.3–4.9k (4.2–4.8k): 4.03k quantum lines in 15 files | open |
| M7 | `Commutativity` | M1, M3 | 13.4k → 12.1–13.8k, central 13.2k (10.5–12.5k): 11.29k quantum lines in 43 files, 2% classical; the largest revision, the directory being almost all quantum and `CommutativityPoints`, its closest relative, having ported at about 1.0 on content | open |
| M8 | `MakingMeasurementsProjective`: the dimension-free part, with the three orthonormalization sites calling T1 | M0, M3, T1 | ≈ 4.1k → 2.6–3.8k (3.3–3.8k) + adapter 0.8–1.5k: quantum share 0.82 and the highest matrix density of any directory, so r 0.6–0.95, about 10 files; about 2.5k further lines unassigned by the audit's partition, which would add 2.0–2.4k if ported | open |
| M9 | the summed semidefinite form: a maximizer by weak-operator compactness, first-order conditions giving `Z = Σ T_g A_g ≥ A_g`, solved componentwise in the doubled model; `MatrixRealization` and `SdpMatrixBridge` (3.98k) are not ported | M0, M2 | new 0.55–0.75k (core measured) + adapter 0.1–0.25k (unchanged: new code, no M1 basis) | done, except the adapter. 925 lines in 3 modules against 0.55–0.75k. `MIPRE/Foundations/SummedSdp.lean` (546) has the conclusion `SummedSdp.IsSummedSdp A T Z` over any ordered ⋆-ring, whose fields are those of the vendored `SdpOptimalPairWithSlackness`, and the core chain, Lemmas 1b–3 and 5–9, up to `isSummedSdp_of_isMaxOn` and the converse `isSummedSdp_of_le`. The setting (S) is the commutant `StarSubalgebra.centralizer ℂ t` of any set, with `IsFaithfulTrace`. `MIPRE/Background/Orthonormalization/SdpMaximizer.lean` (165) has Lemma 4, `exists_isMaxOn_obj`, by the vendored weak-operator compactness, and Theorem 10, `exists_isSummedSdp`, `exists_isSummedSdp_finitePairA`/`B`. `Co/Doubling/Sdp.lean` (214) has Corollary 12, `exists_isSummedSdp_loc` and `exists_isSummedSdp_model`, under `L` and `R`, and Lemma 13, `isSummedSdp_equivA_iff`, `exists_isSummedSdp_A`/`B` and `exists_isSummedSdp_prod` over the report's `𝒜 × ℬ`. Componentwise data is automatic, since `Loc M` is a product. Open: the interface adapter to `SdpStatementWithSlackness` (`Measurement`, `G = Polynomial params`, `A_g = averagedPointOperator`), which is M10's because the port's types for it do not exist yet; Remark 12′, not needed. Elaboration: `SummedSdp.le_of_firstOrder` takes 4.9 s (`-DElab.async=false`, load 1.0), just under the 5 s rule, and `isMeasIn_perturb` takes 4.0 s. Both are risks at higher load, and splitting them is worth doing. `exists_isSummedSdp_A` of `Co/Doubling/Sdp.lean` takes 3.9 s (`-DElab.async=false`, load 1.0); nothing else in the three files takes 3 s. Blueprint `thm:summed-sdp`, `cor:summed-sdp-doubled` |
| M10 | `SelfImprovement` theorems and definitions, + the summed-form interface adapter to `SdpStatementWithSlackness` (from M9, 0.1–0.25k) | M3–M6, M8, M9 | 16.44k → 13.1–15.1k (13–15.5k): without `MatrixRealization` and `SdpMatrixBridge`, 13.2k quantum lines in 32 files | open |
| M11 | `Pasting` | M1, M3, M4, M7 | 30.3k → 23.2–26.5k (24–28k): 22.07k quantum lines in 76 files, the 5.3k classical lines (`Bernoulli/Scalar` and others) imported; its 87 `try rfl` sites became plain `rfl` in M1 at no change in size | open |
| M12 | `MainInductionStep` theorems | M7, M10, M11 | 8.9k → 7.1–8.2k (6.5–8.5k): 7.04k quantum lines in 20 files | open |
| M13 | `Test/MainTheorem` → `Co.mainFormal` over a symmetric model, then over a dyadic pair through the doubling, + Theorem E, unsymmetrization with the two-space tail (from M2) | M2, M8, M12 | 5.06k → 2.5–3.5k (2.5–3.5k): `ScalarBounds` and `SourceScalars` classical and imported, 2.52k quantum lines in 6 files at 2.5–2.9k, plus the dyadic-pair restatement, which M1 does not measure | open |
| M14 | the error cascade into `deltaSim` and the adapters to `SoundIn`: `SoundIn M` for every dyadic pair `M`, hence `SoundFin`, + `ζ > 0` at the in-core call site of Theorem G, threading `1 ≤ params.d` from `SoundIn` (from M2) | M13, T5 | 1.5–3.5k (unchanged: new code, no M1 basis) | open |

Totals: re-estimated after M1, the remaining port M2–M14 about 77–94k new lines, and the whole
port 85–103k with the 8.7k of M0 and M1 (87–105k if the 2.5k unassigned lines of M8 are ported),
against 82–105k before: the total moves little, its floor rises, M7 rises by about 1.5k and M3
widens downward; consistent with the audit's 70–120k. At the two measured rates, 5.6 ms a line
(M1, proofs) and 9.1 ms a line (M0, with its definitions and the keystone), the remaining stages
cost about 7–14 CPU-minutes of non-import elaboration; the lower end assumes they behave like
`CommutativityPoints`, the upper like the base layer. Against their vendored counterparts that is
about 1.0–1.2× for the proof files (M0 0.98×, M1 1.19×), with the definition-heavy files expected
nearer 3× (§5). The tier is done,
about 3.0k lines committed (T1 1.25k, T2–T5 1.75k), within the 2.4–3.7k estimated. The audit put the summed semidefinite form at 0.5–4k; the
measured core puts it at 0.55–0.75k plus the adapter, because full weak-operator compactness of
norm balls is already vendored (`MvN/WOTCompact.lean:114`).

**Revised after M3 and M5** (2026-10-02). M3 came to 3.37k lines against 5.0–7.2k and M5 to 0.85k
against 1.0–1.9k, so about 69–83k lines remain (M4, M6–M8, M10–M14), and the port is 86–100k in
all, of which 16.6k are done (M0 5.70k, M1 3.01k, M2 2.75k, M9 0.93k, M3 3.37k, M5 0.85k). The
remaining rows are not re-estimated: M3's r = 0.36 comes from proofs whose matrix-entrywise steps
and restated placements collapse into keystone lemmas, the case of `OperatorExpectations` and
`TensorPlacement` in M0 (0.24–0.52), while `CommutativityPoints`, the closest relative of
`Commutativity`, `Pasting` and `MainInductionStep`, measured 0.95; were the remaining directories
to port at M3's rate, the remainder would be about half. M3 and M5 elaborate at 0.48× their
vendored files (11.6 and 10.6 ms a line, against 8.4 and 9.9 ms vendored), and M0, M1, M3 and M5
together at 0.70× ("Port conventions").

## 4. Order

1. **This pull request**: the plan, the paper proofs, and T1, with its blueprint nodes.
2. **The rest of the tier** (T2–T5), done: the class, the amplification, the algebra `B` and
   the restatement of C6a, with their blueprint nodes. `mipco_eq_core_of_lidtFin` now holds with
   `SoundFin` narrowed to dyadic pairs, and Theorem 1.2 is unconditional in that class.
3. **M0 and M1, the measured prototype: done.** Acceptance: non-import elaboration of each ported
   file at most twice the vendored file's, no declaration over 5 s, no raised heartbeat limit,
   measured as the minimum of three runs over all profiler categories (simp included). A file
   that holds declarations moved in from other vendored files is judged together with those files
   (the keystone with `OperatorExpectations` and `TensorPlacement`). **Verdict** (2026-10-01,
   "Elaboration, measured on M0 and M1" below): M1 passes in every file, the largest ratio being
   `SharedHelpers/Core` at 1.54× and M1 as a whole at 1.19×; M0 departs from the per-file rule in
   four files, recorded there with the reasons, and is at 0.98× as a layer (the keystone group at
   1.33×); M0 and M1 together are at 1.02×. No declaration of either takes 1.4 s even at load
   1.5, and none takes 1 s at load below 1, so the 5 s rule holds with a factor of about four to
   spare; none of the 25 files sets an option or raises a heartbeat limit. The line ratio and
   the elaboration time measured here have replaced the extrapolated sizes of §3.
4. **M2 and M9, done** (2026-10-01): the doubling and the summed semidefinite form, with their
   blueprint nodes and axiom guards (§3). Three of their open points move to later stages:
   Theorem E (unsymmetrization) to M13, the semidefinite interface adapter to M10, and supplying
   `ζ > 0` at the in-core call site of Theorem G, by threading `1 ≤ params.d` from `SoundIn`, to
   M14 (the case `ζ = 0` itself is not proved and is not needed once this is done). The remaining
   sizes of §3 do not include them.
5. **M3 and M5, done** (2026-10-02): the rest of `Preliminaries` and `ExpansionHypercubeGraph`,
   with their blueprint nodes and axiom guards (§3), at 0.62× and 0.24× the vendored elaboration
   time; the departures are recorded under "Port conventions".
6. Then M4, M6, M7, M8 → M10, M11 → M12 → M13 → M14, as the dependency column allows.

## 5. Things the design round settled, and things it did not

**Settled.**
- The doubling reproduces the vendored constants exactly (3ε, 2σ, 100ζ^{1/4}); the three swap facts
  are short lemmas of the symmetric model; every vendored swap-symmetry use outside `Test` is
  `strategy.permInvState` or `strategy.densityFixed` (report §4).
- The summed semidefinite form is what every consumer of `SdpStatementWithSlackness` uses, and a
  near-maximizer does not suffice: an explicit counterexample in `L^∞[0, 1]` (report §5).
- Order agreement: in a finite pair, `0 ≤ a` in `𝒜` iff `0 ≤ π(πA a)` (report §4, §5).
- The algebra `B` (T4) exists in Lean: the twisted Pauli algebra on `ℓ²(ℕ →₀ ℤ/2 × ℤ/2)` is a
  `StdTracialAlgebra.{0}` with unital dyadic units (`MIPRE/Background/Repetition/PauliAlgebra.lean`). The `StarOrderedRing`
  instance the design round named as a risk is not needed: `StdTracialAlgebra` asks only for a
  ∗-algebra over `ℂ`, and the order lives on the model's algebras, not on `B.A`.
- `CommutativityPoints` has no matrix-specific syntax and uses no swap symmetry, so it ports almost
  textually; the probe ratios were 0.25–0.65 on the base layer and about 0.9 on bridge proofs. M1
  measured 0.87 in lines overall and r = 0.95 on the ported declarations, net of headers, its
  classical half imported (§3).
- **The flip costs nothing per use** (M1's swap probe, 2026-10-01). Since `CommutativityPoints`
  never uses swap symmetry, a scratch module over `Co/Test/StrategyCore.lean` ported the vendored
  `qSDDCore_rightTensor_eq_leftTensor_of_permInv` and re-derived the `consRel_symm_of_density_fixed`
  chain under fresh names: 11 lines against 38 vendored for the first, with neither hypothesis and
  no matrix identity (the vendored `kronecker_sub_right` step is `S.rightTensor_sub`), and 18
  against 36 for the chain; elaboration 0.11 s against 0.11 s, and 0.15 s against 0.12 s. The swap
  lemmas themselves cost about 0.66 s once, in the keystone, against 0.18 s vendored in
  `Test/StrategyCore`. So each of the 57 vendored swap uses outside `Test` becomes one application
  of a keystone lemma, at the same or a lower line count.
- **The answer-valued duplication in `CommutativityPoints` is kept**, as the M1 measurement
  decided: the faithful port costs `AnswerTheorems` (921 lines, 4.7 s, 1.29×) and the answer half
  of `Approximation` (about 0.3k lines and 1.5 s), about 1.2k lines and 6 s together, both within
  the rule; nothing forces a proof generic over the diagonal answer type, which would diverge from
  upstream.

**Not settled.**
- **The vendored classical layer is not purely classical.** `Distribution.lean` imports
  `Quantum.FiniteMatrix` and defines the operator average used by every downstream directory, so
  the matrix layer stays in every port file's import closure and name collisions between ported
  and vendored declarations are certain: explicit `open … (…)` lists are mandatory, and the
  operator average must be ported (counted in M0).
- **`ζ = 0`** in the doubling's orthonormalization step needs `1 ≤ d` threaded from `SoundIn` to the
  core's parameters (report §4).
- **The semidefinite witness `Z`** must lie in the doubled local algebra; the componentwise
  solution needs the `A_g` to be componentwise (report §5). *Settled by M9:* the local algebra
  of `D(M)` is the product `Loc M`, so every `A_g` of it is a pair, and
  `Doubling.exists_isSummedSdp_model` gives `T` and `Z` in `Loc M`. What is left is the adapter
  (M10).
- **Elaboration time** is the main risk of the port: operator positivity on `K →L[ℂ] K` costs
  1–3 s per proof against 0.6 s for the matrix version, roughly doubling under the whole-Mathlib
  imports the vendored classical layer forces. Positivity lemmas go in a base file without those
  imports. Measured on M0 and M1, the port is at 1.02× the vendored files and no declaration takes
  1.4 s (§4 item 3); the remaining risk is the definition-heavy files, where typeclass inference on
  signatures over `K →L[ℂ] K` dominates, as in `Test/Defs` (2.97×). Expect the per-file rule to
  fail for that reason in `MainInductionStep/Defs`, `SelfImprovement/Defs`, `GlobalVariance/Defs/*`
  and the definitions of `Commutativity` and `Pasting`, unless a cheap fix for signature synthesis
  is found.
- **Upstream.** H3 could instead go to `vidick/commuting-repetition` and be vendored; the port's
  base layer could go to `LionSR/MIPStarRE`.

## Port conventions

Settled with the keystone of M0 (`MIPRE/Background/LIDT/Co/Basic/QuantumState.lean`,
`scripts/port-pairing.py`), 2026-10-01. Every stage M0–M14 follows them; a stage that has to
depart from one records the departure here.

**Paths, namespaces, names.**
- A ported file has the vendored file's relative path, under `MIPRE/Background/LIDT/Co/` in place
  of `MIPRE/Background/LIDT/MIPStarRE/LDT/`: `LDT/Basic/SubMeasurementCore.lean` →
  `Co/Basic/SubMeasurementCore.lean`. New files that have no vendored counterpart (the doubling of
  M2, the summed form of M9) get names of their own and are reported as new by the script.
- Namespaces mirror: `MIPStarRE.LDT` → `MIPRE.LIDT.Co`, `MIPStarRE.LDT.X` → `MIPRE.LIDT.Co.X`.
- Declarations keep their vendored names. Lemmas about the state become `SymModel` lemmas and are
  applied with dot notation, `S.leftTensor_mul_leftTensor`, stated with `S.L`; a lemma or
  definition that uses only the state vector, not the placements or the flip, is a `VecState`
  declaration (the parent structure of `SymModel`, below), reached by the same dot notation. The
  namespaces `QuantumState` and `PureState` become `SymModel` or `VecState`.
- Arguments keep their vendored explicitness, with the state as the receiver: the vendored
  `ev_mono ψ X Y h` is `S.ev_mono X Y h`. Named carrier arguments (`(ι₂ := ι)`, 72 sites in CP)
  are deleted: the model fixes both carriers.
- The header of a ported file credits the upstream authors and says it is a port, not a vendored
  file (see the keystone); it is an ordinary module of this repository, so `scripts/modularize.py`
  applies and the vendor scripts do not.

**The model and the translation.** `SymModel 𝔓 K` (keystone): a C*-algebra `𝔓` with its order (the
vendored `Op ι`), a Hilbert space `K`, and `extends VecState K`, the vector state with fields
`Ψ`, `Ψ_norm`; then the fields `L : 𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)`, `J : K ≃ₗᵢ[ℂ] K`, `J_J`, `J_Ψ`,
`commute`; derived `flip := J.conjStarAlgEquiv`, `R := flip ∘ L`, `opTensor A B := L A * R B`
(a `noncomputable abbrev`, as the vendored one is an `abbrev`), and `toBipartite`, the model as a
`MIPRE.BipartiteModel (K →L[ℂ] K) 𝔓 𝔓` with `H := K`, `π := id`, `πA := L`, `πB := R`, whose
`qform` is `ev` and whose `snorm X` is `‖X Ψ‖`, both by `rfl`. On the vector state:
`ev X := Op.qform Ψ X` (a `def`) and `VecState.toStateModel`, the state model with `H := K`,
`π := id` (`toBipartite` extends it). `S.ev X` is `S.toVecState.ev X` by dot notation through the
parent, and a `CoeOut` instance lets an explicit `(V : VecState K)` argument take `S`.

| vendored | port |
|---|---|
| `ψ : QuantumState (ι × ι)` | `S : SymModel 𝔓 K` |
| `ψ : QuantumState ι` (one space; reduced or tensored states) | `V : VecState K` |
| `Op ι` (local) | `𝔓` |
| `Op (ι × ι)` (joint) | `K →L[ℂ] K` |
| `ev ψ X` | `S.ev X` |
| `leftTensor A` | `S.L A` |
| `rightTensor A` | `S.R A` |
| `opTensor A B` | `S.opTensor A B` (`= S.L A * S.R B` by `rfl`) |
| `Xᴴ` | `star X` |
| `swapDensity` | `S.flip` |
| `Error` | `ℝ` (the vendored `Error` is `abbrev Error := ℝ`; either may be written) |
| `SubMeas.liftLeft (ιB := ι) A` | `A.map S.L` (`liftLeft S := map S.L`) |
| `SubMeas.liftRight (ιA := ι) A` | `A.map S.R` |

**Swap symmetry is a theorem.** `S.ev_flip`, `S.ev_L_eq_ev_R` (the vendored
`PermInvState.swap_ev`) and `S.ev_L_mul_R_comm`, with the vendored-named
`S.ev_swapDensity_of_density_fixed`, `S.ev_opTensor_swap_of_density_fixed` and
`S.swapDensity_opTensor`, all in the keystone. Ported statements drop the hypotheses
`hfix : swapDensity ψ.density = ψ.density`, `hperm : PermInvState ψ` and `hψ : ψ.IsNormalized`;
the fields `permInvState`, `densityFixed` and `isNormalized` of the vendored `SymStrat` are not
fields of the ported one (each is a theorem of its `state`), and are listed as not ported with that
reason. `S.ev_one_of_isNormalized : S.ev 1 = 1` takes no hypothesis; `S.IsNormalized` and
`S.isNormalized` exist for statements that still mention normalization. Each dropped field has
its own `Not ported` bullet in `Co/Test/StrategyCore.lean` (the pairing script reads fields).

**Measurements** (`SubMeas`, `Measurement`, `ProjMeas`, `IdxSubMeas`, `OpFamily`, …) are generic
over a ring `R` (`[Ring R] [StarRing R] [PartialOrder R]`, plus `[StarOrderedRing R]` for the
positivity lemmas, `[Algebra ℂ R]` for `map`, and C*-structure only where a proof needs it), with
the vendored field names verbatim; local families take `R = 𝔓`, joint ones `R = K →L[ℂ] K`;
placement is `map` along a ⋆-homomorphism.

**Same-space and bipartite quantities.** A defect or relation that uses only the state
(`qMatchMass`, `qConsDefect`, `qSDD`, `qSDDOp`, `qSSCDefect`, `consError`, `sddError`,
`sddErrorOp`, `sscError`, `subMeasMass`, `idxSubMeasMass`, `bndError`, `SDDRel`, `SDDOpRel`,
`SSCRel`, `CompletenessAtLeast`, `BoundedByOperator`, and the lemmas about them alone) is a
`VecState` declaration on joint operators: the vendored uses with a state on one space
(`SDDOpRel ψ` in `MakingMeasurementsProjective/QXPLayer/Core.lean`), a state tensored with an
ancilla (`MakingMeasurementsProjective/Statements.lean`) or a reduced state
(`LocalityPreservingRepair.lean`, where a local family is placed by `S.L` and measured against
`S`) port without building a symmetric model. A bipartite one (`qBipartiteMatchMass`,
`qBipartiteConsDefect`, `bipartiteConsError`, `ConsRel`, the bipartite SSC defects) needs `L`
and `R` and is a `SymModel` declaration. The two-space `ProjStrat` (state a
`MIPRE.BipartiteModel 𝒞 𝒜 ℬ`, algebras star-ordered as in `SoundIn`) therefore has no ported
`ConsRel`: its consistency is stated through the doubling (M2, M13) and, on `M` itself, as
`MIPRE.BipartiteModel.inconsistency` (`SymModel.bipartiteConsError_eq_inconsistency` relates the
two for measurements); the vendored `ConsRel strategy.state …` statements of
`Test/MainTheorem/MainFormal.lean` are replaced, not ported, by M13 and M14.

**The vendored classical layer is imported, never ported**, and named only through explicit lists,
`open MIPStarRE.LDT (Parameters Distribution avgOver …)`. A wholesale `open MIPStarRE.LDT` is
forbidden: the classical layer imports the vendored matrix layer (§5), so `SubMeas`, `ev`, … exist
under both namespaces. Only `MIPRE/Background/` may name `MIPStarRE`, which is where the port lives.

**Where positivity lives.** Every positivity fact on the joint operators `K →L[ℂ] K` is proved
once, in `Co/Basic/QuantumState.lean`, whose only import is `MIPRE.Foundations.Pasting`
(Foundations and the targeted Mathlib they import; no vendored module), and downstream files apply
it; positivity in the local algebra `𝔓` or in a generic ordered `⋆`-ring (the conjugation lemmas
of `Co/Basic/TensorPlacement.lean`, the projective lemmas of `Co/Basic/SubMeasurementCore.lean`)
stays with its vendored file. The keystone holds: `sq_le_self` (any C*-algebra),
`S.leftTensor_nonneg`, `S.rightTensor_nonneg`,
`S.leftTensor_mono`, `S.rightTensor_mono`, `S.leftTensor_le_one`, `S.rightTensor_le_one`,
`S.opTensor_nonneg`, `S.opTensor_mono_left`, `S.opTensor_mono_right`, `S.opTensor_le_leftTensor`,
`S.opTensor_le_one`, `S.ev_nonneg_of_psd`, `S.ev_mono`, `S.ev_adjoint_self_nonneg`,
`S.ev_adjoint_self_eq_norm_sq`. Reaching for `Commute.mul_nonneg` on `K →L[ℂ] K` again costs about
0.7 s a proof (the continuous functional calculus instances); a new positivity fact that the
keystone lacks goes into the keystone, not into the file that needs it.

**Moved declarations.** To keep positivity in one file, the keystone also holds declarations whose
vendored home is elsewhere: from `OperatorExpectations`, `ev_add`, `ev_sub`, `ev_scale`,
`ev_real_smul`, `ev_zero`, `ev_opTensor`, `ev_one_of_isNormalized`, `ev_adjoint_self_nonneg`,
`ev_finset_sum`, `ev_sum`, `ev_nonneg_of_psd`, `ev_mono`, `ev_conjTranspose`,
`ev_mul_comm_of_hermitian`, `ev_mul_comm_of_psd`, `ev_conjTranspose_mul_comm`; from
`TensorPlacement`, `leftTensor_finset_sum`, `rightTensor_finset_sum`, `leftTensor_nonneg`,
`rightTensor_nonneg`, `leftTensor_le_one`, `rightTensor_le_one`; from `Test/StrategyCore`, the three
swap lemmas above; `sq_le_self` from `Quantum/FiniteMatrix/Order`. The counterparts of those files
do not redeclare them (the names would clash in `MIPRE.LIDT.Co`); the pairing script reports them
as "ported elsewhere". The rest of `OperatorExpectations` (the triangle inequalities,
Cauchy–Schwarz, the sandwich lemmas) is ported in `Co/Basic/OperatorExpectations.lean`, through
`StateModel.abs_qform_star_mul_le` (`Foundations/Sandwich.lean`) on `V.toStateModel`, as
`ev_conjTranspose` goes through `StateModel.qform_star`.

**The positivity tactic is `sym_nonneg`**, in `Co/Tactic/QuantumNonneg.lean` (the mirrored path).
The name differs from the vendored `quantum_nonneg` as a precaution: no M0 file imports the
vendored syntax (only the vendored `Preliminaries/Defs.lean` does), but 228 of the 312 vendored
LDT modules have it in their import closure, so a later stage importing one of them for classical
content would get two `quantum_nonneg` syntaxes, the vendored one calling the matrix lemmas, and
ambiguous parses. It is the vendored macro with each lemma replaced by its fully qualified
`MIPRE.LIDT.Co` counterpart (`VecState`, `SymModel` or `SubMeas`), plus a `map_nonneg` fallback
for a positive operator pushed along any order-preserving map.

**Not ported, and the pairing script.** Every vendored declaration of a file has a counterpart of
the same name in the ported file, is ported elsewhere (above), or is listed in the ported file's
module docstring under a heading `Not ported`, one name per bullet with its reason:

    ## Not ported

    - `normalizedTrace_opTensor`: the model has no trace.

Matrix-only content (normalized trace, density, entrywise Kronecker identities, PSD-matrix facts)
is not ported but replaced by the model's lemmas. `python3 scripts/port-pairing.py <file or
directory>` pairs a ported file with its vendored one (names compared without the root and state
namespaces) and reports, per file, the ported, loosely paired, ported-elsewhere, listed and missing
vendored names, the new ported names (with the vendored file a moved one comes from) and stale
`Not ported` bullets; `--check` exits 1 if a vendored name is missing. Structure fields count as declarations
(`SymStrat.permInvState`), so a dropped field needs its bullet; a `private` ported declaration
never counts as the counterpart of a public vendored one and is reported on a `private` line. Each
stage runs it on its files and reports the output.

**Elaboration, measured on M0 and M1, and on M3 and M5.** Non-import elaboration of each file, `lake env lean
-Dprofiler=true`, the sum of every profiler category except `import`, minimum of three runs, in
seconds, against the vendored file measured the same way on the same machine. Lines are `wc -l`;
"tc" is the typeclass-inference part, ported / vendored. Measured 2026-10-01, 19:20–19:37 UTC,
on a 4-core machine at load 0.5–1.7, on the files of commit `9fea38a`. Every M0 file reproduces
the first M0 measurement (after the review round; the earlier figure of 2.4 s for the vendored
keystone did not reproduce) within 14%, the largest changes being the vendored
`SubMeasurementFamilies` (+14%), the ported `Test/StrategyCore` (+13%), the ported
`DistanceBounds` (+10%) and the vendored `TensorPlacement` (+10%); the layer totals reproduce
within 2% (51.8 s against 52.0 s ported, 53.0 s against 52.0 s vendored). So the move of the M0
ratio from 1.00× to 0.98× is within the reproducibility of the measurement, and the per-file
ratios are good to about ±15%. The line counts are those of `9fea38a`; the review after it added
docstrings and upstream-qualified references to `CommutativityPoints` (3,077 lines now, no proof
changed), which leaves the elaboration figures as they are and moves r from 0.95 to 0.97, the
docstrings being charged to the declarations.

| file | ported lines | vendored lines | ported (s) | vendored (s) | ratio | tc (s) |
|---|---|---|---|---|---|---|
| `Basic/Distribution.lean` | 279 | 571 | 2.17 | 4.38 | 0.49 | 1.16 / 1.64 |
| `Basic/DistributionAvg.lean` | 214 | 778 | 0.92 | 6.50 | 0.14 | 0.20 / 1.73 |
| `Basic/DistributionMapAverages.lean` | 104 | 158 | 0.61 | 4.24 | 0.14 | 0.02 / 2.23 |
| `Basic/DistributionPMF.lean` | 72 | 127 | 0.55 | 1.26 | 0.43 | 0.02 / 0.30 |
| `Basic/MeasurementLift.lean` | 83 | 52 | 1.19 | 0.52 | 2.27 | 0.39 / 0.02 |
| `Basic/OpFamily.lean` | 161 | 123 | 0.81 | 0.64 | 1.25 | 0.13 / 0.03 |
| `Basic/OperatorExpectations.lean` | 203 | 596 | 3.21 | 6.37 | 0.50 | 1.44 / 2.61 |
| `Basic/QuantumState.lean` (keystone) | 577 | 589 | 10.26 | 3.51 | 2.92 | 5.50 / 0.94 |
| `Basic/SubMeasurementCore.lean` | 513 | 466 | 2.45 | 4.20 | 0.58 | 0.75 / 2.05 |
| `Basic/SubMeasurementFamilies.lean` | 498 | 626 | 4.55 | 3.74 | 1.22 | 2.00 / 1.42 |
| `Basic/TensorPlacement.lean` | 290 | 487 | 4.16 | 3.34 | 1.25 | 2.22 / 1.76 |
| `Preliminaries/ComparisonCore.lean` | 376 | 676 | 3.19 | 3.61 | 0.88 | 1.16 / 1.21 |
| `Preliminaries/Defs.lean` | 392 | 392 | 3.61 | 2.18 | 1.66 | 1.53 / 0.54 |
| `Preliminaries/DistanceBounds.lean` | 245 | 402 | 2.36 | 2.54 | 0.93 | 0.77 / 0.80 |
| `Tactic/QuantumNonneg.lean` | 167 | 96 | 2.20 | 0.69 | 3.17 | 0.87 / 0.03 |
| `Test/Defs.lean` | 521 | 493 | 4.92 | 1.66 | 2.97 | 2.08 / 0.23 |
| `Test/StrategyCore.lean` | 777 | 827 | 3.48 | 2.50 | 1.39 | 0.98 / 0.33 |
| `Test/StrategyFailures.lean` | 225 | 232 | 1.19 | 1.06 | 1.12 | 0.29 / 0.19 |
| **all of M0** | 5697 | 7691 | 51.82 | 52.95 | 0.98 | 21.5 / 18.1 |
| `CommutativityPoints/Defs.lean` | 237 | 330 | 1.52 | 1.38 | 1.10 | 0.50 / 0.35 |
| `CommutativityPoints/Approximation.lean` | 683 | 822 | 3.10 | 2.96 | 1.05 | 0.83 / 0.69 |
| `CommutativityPoints/SharedHelpers/Core.lean` | 203 | 224 | 1.82 | 1.18 | 1.54 | 0.57 / 0.38 |
| `CommutativityPoints/SharedHelpers/SharedLine.lean` | 263 | 426 | 1.57 | 1.98 | 0.79 | 0.33 / 0.34 |
| `CommutativityPoints/BridgeTheorems/LiftBridges.lean` | 295 | 282 | 1.82 | 1.29 | 1.41 | 0.59 / 0.22 |
| `CommutativityPoints/BridgeTheorems/DropBridges.lean` | 406 | 408 | 2.28 | 1.72 | 1.33 | 0.70 / 0.33 |
| `CommutativityPoints/AnswerTheorems.lean` | 921 | 972 | 4.72 | 3.65 | 1.29 | 1.87 / 0.71 |
| **all of M1** | 3008 | 3464 | 16.82 | 14.16 | 1.19 | 5.38 / 3.03 |
| **M0 and M1** | 8705 | 11155 | 68.64 | 67.11 | 1.02 | 26.9 / 21.1 |
| `Preliminaries/BipartiteSelfConsistency/Completion.lean` | 149 | 262 | 2.42 | 2.35 | 1.03 | 1.02 / 0.60 |
| `Preliminaries/BipartiteSelfConsistency/Core.lean` | 136 | 338 | 1.54 | 1.67 | 0.92 | 0.35 / 0.32 |
| `Preliminaries/BipartiteSelfConsistency/Local.lean` | 72 | 189 | 0.81 | 1.45 | 0.56 | 0.12 / 0.37 |
| `Preliminaries/CauchySchwarz.lean` | 172 | 274 | 1.37 | 2.58 | 0.53 | 0.43 / 0.89 |
| `Preliminaries/ComparisonProjective.lean` | 158 | 393 | 2.00 | 2.54 | 0.79 | 0.62 / 0.60 |
| `Preliminaries/Completion.lean` | 76 | 86 | 0.99 | 3.85 | 0.26 | 0.30 / 2.72 |
| `Preliminaries/CompletionTransfer.lean` | 254 | 394 | 3.00 | 3.24 | 0.92 | 1.17 / 0.92 |
| `Preliminaries/ConsistencyBridges.lean` | 219 | 621 | 2.87 | 4.13 | 0.69 | 1.01 / 1.65 |
| `Preliminaries/PolynomialAgreement.lean` | 150 | 436 | 1.14 | 3.17 | 0.36 | 0.19 / 0.94 |
| `Preliminaries/SelfConsistency/Core.lean` | 170 | 304 | 1.82 | 2.75 | 0.66 | 0.55 / 0.92 |
| `Preliminaries/SelfConsistency/DataProcessing.lean` | 193 | 358 | 1.93 | 2.64 | 0.73 | 0.45 / 0.73 |
| `Preliminaries/SelfConsistency/Extensions.lean` | 175 | 368 | 1.41 | 2.65 | 0.53 | 0.33 / 0.96 |
| `Preliminaries/SwitchSandwichGapBounds/Core.lean` | 80 | 91 | 0.81 | 0.82 | 0.99 | 0.16 / 0.10 |
| `Preliminaries/SwitchSandwichGapBounds/Left.lean` | 84 | 273 | 1.36 | 1.57 | 0.87 | 0.35 / 0.45 |
| `Preliminaries/SwitchSandwichGapBounds/Middle.lean` | 89 | 317 | 1.50 | 2.08 | 0.72 | 0.35 / 0.78 |
| `Preliminaries/SwitchSandwichMain/Completeness.lean` | 136 | 222 | 1.28 | 1.94 | 0.66 | 0.34 / 0.63 |
| `Preliminaries/SwitchSandwichMain/LeftTransfer.lean` | 93 | 160 | 0.86 | 1.35 | 0.63 | 0.13 / 0.32 |
| `Preliminaries/SwitchSandwichMain/RightTransfer.lean` | 157 | 465 | 2.41 | 3.92 | 0.61 | 0.61 / 0.93 |
| `Preliminaries/SwitchSandwichPrep/ApproxDelta.lean` | 130 | 251 | 1.68 | 3.12 | 0.54 | 0.52 / 1.22 |
| `Preliminaries/SwitchSandwichPrep/Core.lean` | 120 | 234 | 1.47 | 2.12 | 0.69 | 0.50 / 0.88 |
| `Preliminaries/SwitchSandwichPrep/InnerProduct.lean` | 142 | 294 | 1.36 | 3.13 | 0.43 | 0.39 / 1.16 |
| `Preliminaries/Triangles/Core.lean` | 334 | 930 | 3.03 | 8.79 | 0.34 | 1.11 / 3.55 |
| `Preliminaries/Triangles/SimEq.lean` | 132 | 245 | 1.01 | 1.28 | 0.79 | 0.25 / 0.31 |
| **all of M3** | 3421 | 7505 | 38.08 | 63.14 | 0.60 | 11.2 / 21.9 |
| `ExpansionHypercubeGraph/Defs/Core.lean` | 122 | 325 | 0.79 | 2.17 | 0.37 | 0.15 / 0.42 |
| `ExpansionHypercubeGraph/Defs/Fourier.lean` | 163 | 657 | 1.06 | 6.86 | 0.16 | 0.32 / 2.07 |
| `ExpansionHypercubeGraph/Theorems/Foundations.lean` | 243 | 483 | 3.62 | 6.70 | 0.54 | 1.59 / 1.04 |
| `ExpansionHypercubeGraph/Theorems/Matrix.lean` | 139 | 809 | 1.75 | 10.27 | 0.17 | 0.47 / 2.38 |
| `ExpansionHypercubeGraph/Theorems/Results.lean` | 185 | 408 | 1.76 | 2.80 | 0.63 | 0.47 / 0.70 |
| `ExpansionHypercubeGraph/MatrixRealization/Core.lean` (not ported) | — | 964 | — | 6.51 | — | — / 1.79 |
| `ExpansionHypercubeGraph/MatrixRealization/TraceForms.lean` (not ported) | — | 162 | — | 2.29 | — | — / 0.45 |
| **all of M5** (vendored: the whole directory) | 852 | 3808 | 8.99 | 37.60 | 0.24 | 3.0 / 8.9 |
| **M3 and M5** | 4273 | 11313 | 47.07 | 100.73 | 0.47 | 14.2 / 30.8 |
| **M0, M1, M3 and M5** | 12978 | 22468 | 115.71 | 167.84 | 0.69 | 41.1 / 51.9 |

**The M3 and M5 rows** were measured the same way on 2026-10-02, 00:25–00:50 UTC, on the same
4-core machine at load 0.5–2.1, ported and vendored file alternating, three rounds; the line
counts are those of the working tree measured. One record is excluded: the first vendored run of
`SwitchSandwichPrep/Core` reported no typeclass-inference time at all (1.32 s, against 2.22 and
2.12 s with 0.97 and 0.88 s of it in the other two runs), a profiler artifact, so its minimum is
taken over the other two (with it the file would read 1.11×). After the review, the shared
expansion `ev_star_L_sub_R_mul_self` replaced three inline proofs of it, and the three files whose
proofs changed (`SwitchSandwichMain/RightTransfer`, `SelfConsistency/DataProcessing`,
`BipartiteSelfConsistency/Core`) were measured again the same way, ported side only, on
2026-10-02 at 01:52 UTC, load 1.0–1.1; their rows and the totals carry those figures. The review
also added `Not ported` sections to module docstrings, so the other line counts are those of the
working tree after it, their elaboration unchanged. Every M3 and M5 file passes the 2×
rule of §4 item 3: the largest ratios are `BipartiteSelfConsistency/Completion` at 1.03×, the file
with the narrowed `qBipartiteConsDefect_completeAtOutcome_right_le`, and
`SwitchSandwichGapBounds/Core` at 0.99×; everything else is at 0.16–0.92×
(`BipartiteSelfConsistency/Core`, 1.15× before the shared expansion, is at 0.92×). M3 as a whole is
at 0.60× and M5 at 0.24× (0.31× against its five
vendored counterparts alone, 28.8 s, the two `MatrixRealization` files having no counterpart). The
port costs 11.1 ms a line on M3 and 10.6 ms on M5, against 8.4 and 9.9 ms vendored. With
`-Dtrace.profiler.threshold=1000`, one run per ported file under the default asynchronous
elaboration, at load 1.0, after the review, six declarations reach 1 s:
`ExpansionHypercubeGraph.globalVarianceTraceForm_eq_closedForm` 1.40 s (vendored 1.63 s),
`switchSandwich_rightTransfer` 1.37 s (vendored 3.85 s), `wrongSideEstimate` 1.13 s (vendored
2.00 s), `two_questionConsistency_eq_questionSDD_of_projective` 1.08 s (vendored under 1 s),
`consSubMeas_sandwichControl` 1.02 s and `closenessAfterCompletion_core_local` 1.01 s. Before the
shared expansion, `switchSandwich_rightTransfer` measured 1.86–1.99 s asynchronously and
2.05–2.20 s with `-DElab.async=false` (load 0.7–1.0), and `wrongSideEstimate` 1.53–1.68 s; with
`-DElab.async=false` at load 0.7–1.0 they now take 1.47–1.72 s and 1.14–1.35 s, the expansion
itself 0.45–0.57 s once. The vendored maximum in these files is `trace_combined_tensor_eq` (M5
`Theorems/Foundations`, not ported), 3.88 s. So no declaration takes 2 s, and the 5 s rule holds
with a factor of about 3.5 to spare at that load; none of the
28 files sets an option or raises a heartbeat limit.

Declaration times depend on the machine's load, because under the default asynchronous
elaboration the profiler reports a proof's wall time (`Elab.async`), and they are recorded with
it. With `-Dtrace.profiler.threshold=500`, one run per file on either side of each of the 25
pairs, in the run above (load 0.5–1.7), no declaration of M0 or M1 took 1 s: the largest in M0
is `Preliminaries.questionSDD_le_two_questionConsistency`, 0.83 s (vendored 0.61), and in M1
`answerOrderedDropFromLineComparison`, 0.98 s (vendored 0.92). A review run on
`CommutativityPoints/AnswerTheorems` at load 1.4–1.7 found three proofs at or above 1 s,
`answerOrderedDropFromLineComparison` at 1.33–1.35 s (vendored 1.07),
`answerReversedDropToPointsComparison` at 1.05 s and `answerOrderedLiftToLineProduct` at 1.01 s;
at load below 0.6 the same file's maximum is 0.72 s asynchronously and 0.65 s with
`-DElab.async=false` (vendored 0.84 and 0.85). So no declaration takes 1 s at load below 1, none
takes 1.4 s at load 1.5, and the 5 s rule holds with a factor of about four to spare. The
vendored maxima are `ev_opTensor_sandwich_cauchy_schwarz`, 2.92 s, and
`ProjSubMeas.outcome_mul_total_eq_outcome`, 2.05 s. Four files of M0 exceed the 2× rule of §4 item 3, and this is recorded as a departure
from it:
- **the keystone** (2.92×) holds 28 declarations moved in from three other vendored files and the
  new model API (the vector state, the flip, `toBipartite`, the real-scalar placement lemmas);
  judged, as §4 says, together with the files whose declarations it absorbs, the group
  keystone + `OperatorExpectations` + `TensorPlacement` is 17.6 s against 13.2 s, 1.33×. Its cost
  is typeclass inference (5.5 s of the 10.3 s), the coercion classes of
  `𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)` and the C*-order classes of `K →L[ℂ] K`;
- **`Test/Defs`** (2.97×): typeclass inference 2.08 s against 0.23 s and type checking 0.94 s
  against 0.06 s, spread over about 50 signatures (the largest item `qBipartiteConsDefect_eq_sum_ne`,
  0.44 s; the declaration headers 0.1–0.19 s each), the instance synthesis that every signature on
  `K →L[ℂ] K` pays; adding `Ring`/`StarRing`/`PartialOrder`/`Module` shortcuts for it cut the file
  by about 5% in the review's Scratch measurement, so no cheap fix is known;
- **`Tactic/QuantumNonneg`** (3.17×): ten `example`s at 0.14–0.29 s each, where the vendored file
  has one;
- **`MeasurementLift`** (2.27×): two definition headers at 0.22 and 0.18 s on a 0.52 s vendored
  file.

M1 passes the rule in every file. Against the vendored files it spends 2.35 s more on typeclass
inference and 0.93 s more on type checking, and 1.70 s less on simp, the vendored `try rfl` and
`simp` steps having become `rfl` or keystone terms. The files closest to the limit:
- **`SharedHelpers/Core`** (1.54×, +0.64 s): almost all of it `qSDDOp_reindex`, 0.45 s against
  0.075 s, a single `Fintype.sum_equiv` term elaborating the finite sum and its instances on
  `K →L[ℂ] K`; stating the summand through `S.ev`, or giving the instance with an explicit
  `(R := K →L[ℂ] K)`, is an untested cleanup;
- **`LiftBridges`** (1.41×, +0.53 s): 0.41 s of it the two lemmas the file adds (below), which have
  no vendored counterpart; its two bridge proofs cost what the vendored ones do;
- **`DropBridges`** (1.33×, +0.56 s): `commutativityPoints`, about 0.65 s against 0.23 s, its
  triangle and monotonicity steps passing the state through the `CoeOut` coercion from `SymModel`
  to `VecState`; writing `strategy.state.toVecState`, as `AnswerTheorems` does, would probably
  recover 0.2–0.3 s;
- **`AnswerTheorems`** (1.29×, +1.07 s): typeclass inference 1.87 s against 0.71 s and type
  checking 0.52 s against 0.08 s, spread over its four bridge theorems at +0.05 to +0.22 s each.

Every file pays 0.4–0.7 s of constant overhead (the profiler's "interpretation") on both sides,
which is why small files such as `MeasurementLift` and `SharedHelpers/Core` look worse in ratio
than in time. The port costs 5.6 ms a line on `CommutativityPoints` and 9.1 ms on the base layer,
against 4.1 and 6.9 ms vendored, so about 1.3–1.4× the vendored files on the content actually
ported (the vendored files also elaborate the classical half the port imports). Proof files are
expected at 0.8–1.5×, as every M1 file is; definition-heavy files are expected to depart as
`Test/Defs` does (§5).

**Departures in M2 and M9.**
- The two-space `ProjStrat` needs a failure surrogate, and the vendored defect behind it is
  two-space. So `Co/Test/StrategyBiProj/Measurements.lean` adds the two-space defect over a
  `MIPRE.BipartiteModel`, with `bornProb` for `ev(A ⊗ B)`: `qBipartiteMatchMass`,
  `qBipartiteConsDefect` and `bipartiteConsError`, in the root namespace `MIPRE.LIDT.Co` with the
  state explicit, so that the vendored text `bipartiteConsError strategy.state 𝒟 A B` ports
  unchanged. This departs from "bipartite defects are `SymModel` declarations". It is used only for
  the surrogate, and `Doubling.bipartiteConsError_model` relates it to the `SymModel` defect of the
  doubled model. For measurements, `MIPRE.LIDT.Co.bipartiteConsError_eq_inconsistency`
  (`Co/Doubling/Strategy.lean`) equates it with `M.inconsistency`.
- `Loc M` has two sets of shortcut instances. The C⋆-algebra and order shortcuts are in
  `Co/Doubling/Model.lean`. The real-scalar and functional-calculus ones (`instNormedAlgebraRealLoc`,
  `instAlgebraRealLoc`, `instCFCLoc`) are in `Co/Doubling/Orthonormalization.lean`. Without the
  latter, `cfc` on `Loc M` fails, because `Algebra ℝ (Loc M)` is found through `Prod.algebra`.
  Moving them next to the others is a cleanup.
- `Co/Doubling/Orthonormalization.lean` declares the completion of a submeasurement and the
  restriction of a projective submeasurement on `Option Outcome` under their vendored names,
  `MakingMeasurementsProjective.optionCompletion` (with its two `@[simp]` outcome lemmas) and
  `MakingMeasurementsProjective.restrictSomeProjSubMeas`, generic over an ordered `⋆`-ring. M8's
  ports of `LDT/MakingMeasurementsProjective/Statements.lean` and
  `.../Orthonormalization/RestrictSome.lean` reuse them, and the pairing script reports them there
  as ported elsewhere; M8 may move them into those files. Theorem G and Proposition H are stated
  over any symmetric model (`SymModel.orthonormalization_of_isFinitePair`, `SymModel.L_cfc`), with
  the doubled model a one-line specialization.
- Vector traces of the doubled model are stated on `VecTrace.diag2Set`, not on
  `(model hM hψ).toBipartite.opsA`. Instance synthesis on `(model hM hψ).toBipartite.H`, which
  unfolds to `Ampl (Fin 2) M.H` only through `SymModel.toBipartite`, exceeds the synthesis budget.
  Downstream statements should be written in `Ampl (Fin 2) M.H`, `S.L` and `S.Ψ`, and passed by
  definitional equality.
- `isSummedSdp_prod_iff` and `isSummedSdp_map_iff_of_nonneg_iff` are generic but live in
  `MIPRE.LIDT.Co.Doubling` (`Co/Doubling/Sdp.lean`). Their home is `Foundations/SummedSdp.lean`.

**Departures in M3 and M5.**
- **Both came in under their estimates**: M3 at 3.37k lines against 5.0–7.2k (r = 0.36 against
  0.6–0.95), M5 at 0.85k against 1.0–1.9k (r = 0.26). In M3 the vendored switch-sandwich, gap
  and transfer proofs restate their long `leftTensor (ι₂ := ι) …` expressions in every `have`
  and `calc` step and prove Kronecker identities entrywise; here those are `S.L`, `S.L_comm_R`,
  `S.leftTensor_mul_leftTensor` and one rewrite with `S.ev_L_eq_ev_R` per swap use (the files
  `SwitchSandwichGapBounds/{Left,Middle}`, `SwitchSandwichMain/RightTransfer` and
  `BipartiteSelfConsistency/Local` port at r = 0.13–0.21). In M5 the matrix realization (two
  files, 1,126 lines) is replaced by Gram positivity, below.
- **Four new declarations factor out a computation the vendored files repeat**, each listed
  under `New here`: `Preliminaries.question_overlap_gap_aux` (`SwitchSandwichPrep/ApproxDelta`,
  the estimate `|∑ ev((A_a − B_a) E_a)| ≤ √qSDD(A, B)` of both overlap gaps),
  `Preliminaries.consRel_of_matchGap` (`Triangles/Core`, the max-0 estimate and averaging of
  four substitution proofs) and `Preliminaries.ev_adjoint_self_leftTensor_sub_rightTensor`
  (`BipartiteSelfConsistency/Core`, `‖(L X − R X) Ψ‖² = 2 (ev L(X²) − ev(L X R X))` with the
  swap, used by `Core` and `Local`) and `Preliminaries.ev_star_L_sub_R_mul_self`
  (`SwitchSandwichMain/RightTransfer`, `ev((L X − R Y)^*(L X − R Y)) = ev L(X²) + ev R(Y²) −
  2 ev(L X R Y)` for self-adjoint `X`, `Y`, used by `switchSandwich_rightTransfer`,
  `wrongSideEstimate` and, at `X = Y`, `ev_adjoint_self_leftTensor_sub_rightTensor`). The last was
  added after review: `switchSandwich_rightTransfer` and `wrongSideEstimate` had each proved it
  inline, with `abel` on `K →L[ℂ] K`, for about 0.6–0.7 s of their 2.0–2.1 s and 1.5–1.7 s; its
  proof rewrites to scalars and closes by `ring`, 0.3 s once. It lives in `RightTransfer`, the
  first file that needs it and one that `DataProcessing` and `BipartiteSelfConsistency/Core`
  import through `SwitchSandwichMain/Completeness`, rather than in the keystone, since it is an
  identity, not a positivity fact.
- **Statements changed by a dropped hypothesis.** The vendored
  `qSDDCore_rightTensor_eq_leftTensor_of_permInv` took its state implicitly, determined by
  `hperm`; with `hperm` dropped `S` is explicit. The vendored hypothesis of
  `twoNotionsOfSelfConsistency` is the conjunction `PermInvState ψ ∧ BipartiteSSCRel …`; it is
  now `BipartiteSSCRel` alone, so callers pass `hssc` for `⟨hperm, hssc⟩`.
  `bipartiteSSC_implies_localSSC_liftLeft` loses its `hperm` argument from between `ψ` and `𝒟`.
- **`qBipartiteConsDefect_completeAtOutcome_right_le` is narrowed** from local measurements on
  two different spaces to `A : Measurement Outcome 𝔓`, `B : SubMeas Outcome 𝔓` in a symmetric
  model, by the rule that bipartite quantities are `SymModel` declarations. Its three vendored
  uses (`Pasting/Bernoulli/DegreeZero.lean`, twice, and `Pasting/ComparisonLemmas/HAConsistency.lean`)
  apply it to the state of a `SymStrat`, with both measurements on one space, so the narrowed form
  serves them (M11).
- **`triangleSub_heterogeneous`, `triangleSub_right_heterogeneous` and
  `simeqTriangleInequality_heterogeneous` are narrowed to one carrier**: the vendored statements
  allow two tensor factors `ιA`, `ιB`, the ported ones fix both to `𝔓` in a `SymModel`, where the
  placements `placeLeft S`/`placeRight S` are `liftLeft S`/`liftRight S` by `rfl`, so each is its
  same-space sibling. Their only vendored callers apply them to the two-space `ProjStrat`
  (`Test/MainTheorem/SourceRoleRegister/Core.lean` and `Final.lean`, `simeqTriangleInequality_heterogeneous`
  and `triangleSub_heterogeneous`), which the ported lemmas cannot serve; those calls are left to
  M13/M14, as the two-space `ConsRel` rule ("Same-space and bipartite quantities") prescribes.
- **State-free lemmas are generic**: `projSubMeas_outcome_mul_total_eq_outcome`,
  `projSubMeas_total_proj`, `opBounded01_sq_le_one`, `opBounded01_hermitian`,
  `completeAtOutcomeProj` and `evaluateAt_completeAtOutcome` hold over any C⋆-algebra or ordered
  `⋆`-ring with its order, so they serve `𝔓` and `K →L[ℂ] K` alike. Single-state lemmas take
  `(V : VecState K)` with joint families, and lemmas on placements take `(S : SymModel 𝔓 K)` as an
  explicit first argument in the `Preliminaries` namespace, as M1's helpers do
  (`leftTensor_opBounded01 S hB`, `question_switchSandwich_left_gap S A B hB`); `sddError_self` is
  kept under its vendored name as `Preliminaries.sddError_self V`, delegating to M0's
  `VecState.sddError_self`, so that the pairing script matches it.
- **Classical content is imported from vendored modules** where a vendored file mixes it with
  quantum content: `Co/Preliminaries/{PolynomialAgreement, SwitchSandwichPrep/Core,
  SwitchSandwichPrep/InnerProduct, Triangles/Core}` import their vendored files for 10
  declarations (`polynomialAgreement_avg_le_mdq`, `weightedFinsetCauchySchwarz`,
  `avgOver_abs_le_sqrt_of_pointwise`, `max_zero_add_le`, …), listed as `classical, imported`, and
  `Polynomials.lean` is not ported. `MIPStarRE.LDT.Polynomial params` is written fully qualified,
  as in `Co/Test/Defs.lean`, against `_root_.Polynomial`. `ComparisonProjective` keeps an import
  of `Co/Preliminaries/SwitchSandwichPrep/Core` that its operator-level proof no longer uses, to mirror the
  vendored imports.
- **A pitfall for later stages**: `question_overlap_gap_left`/`_right` applied as
  `S.toVecState _ _`, with the expected type written in `S.L` form, exceeded 200000 heartbeats
  while unifying the two submeasurement arguments from it; passing the lifted submeasurements
  explicitly is fast (`CompletionTransfer.lean`).
- **M5: trace forms are sums, and Gram positivity replaces the matrix realization.** A vector
  state has no density, so the vendored `Re τ(A_combineᴴ (P ⊗ ρ) A_combine)` is the new
  `ExpansionHypercubeGraph.combinedTraceForm P A V = ∑ u v, P u v · ⟪Ψ, A_v† A_u Ψ⟫`, and
  `re_combinedTraceForm_nonneg` (a positive semidefinite scalar `P` is a sum of `star s * s`)
  replaces `MatrixRealization/{Core,TraceForms}` and the `matrix*` lemmas of `Theorems/Matrix`
  and `Theorems/Results`, each listed as not ported with its realization-free replacement
  (`globalVariance_eq_closedForm`, `localVariance_eq_closedForm`,
  `localVarianceTraceForm_eq_closedForm`, `traceForm_localToGlobal`). The variances are
  `VecState` quantities on `A : Point params → (K →L[ℂ] K)`; `bipartiteLocalVariance`,
  `bipartiteGlobalVariance` and `localToGlobalBipartite` take `(params) (A : Point params → 𝔓)
  (S : SymModel 𝔓 K)`. The scalar hypercube theory (the graph, the edge distribution, the
  Laplacian and adjacency matrices, the Fourier analysis, `laplacianRewrite`) is imported; the
  port imports the vendored `Defs/Core`, so no `Co/MakingMeasurementsProjective/Defs.lean` was
  created for its `FiniteHilbertSpace`, and M8 is untouched.
- **For M6**: the vendored point-conditioned variances evaluate on the weighted state `W ρ Wᴴ`,
  `W = rightTensor (sqrt G_g)`, which is not normalized; port them as the variance of the family
  `u ↦ S.L (A u) * S.R sqrtG` on `S` itself (`ev_{WρWᴴ}(X) = ev_ρ(Wᴴ X W)`), to which
  `localToGlobal` applies unchanged (`Theorems/Results.lean`, module docstring). Write
  `localVariance` qualified or through an explicit `open` list there, since the vendored
  namespace has the same names. The vendored matrices (`matrixLaplacianOperator`,
  `orthogonalModeProjectorMatrix`) are typed as `MatrixOperator (pointHilbertSpace params)`, whose
  `-` and `•` do not unify syntactically with `Matrix`'s: `Results.lean` passes `(n := Point
  params)`, `id (α := Matrix ..)` and `trans_eq`.

**Departures in M1.**
- Helpers that take the state keep the ported file's namespace, with the model or the vector
  state as an explicit first argument, rather than becoming `SymModel` or `VecState` lemmas, so
  that the pairing script matches them by name: `tensorProductSubMeas S A B` and its sum lemma
  (`CommutativityPoints/Defs.lean`; call it as `tensorProductSubMeas strategy.state A B`), the
  distance lemmas `sddOpRel_symm`, `qSDDOp_reindex`, `sddOpRel_reindex`, `sddOpRel_congr_outcome`
  (`(V : VecState K)`) and the four placement lemmas `liftLeft_mul_leftPlaced_outcome`, … (`(S :
  SymModel 𝔓 K)`) of `SharedHelpers/Core.lean`.
- `BridgeTheorems/LiftBridges.lean` adds `liftLeft_sum_adjoint_mul_le_one` and
  `liftRight_sum_adjoint_mul_le_one`. The vendored proofs discharge the `∑ star C * C ≤ 1` side
  condition of `cabApproxDelta_raw` with `subMeas_sum_adjoint_mul_le_one` on the lifted, joint
  submeasurement; the two lemmas derive it from the local one through the placement
  (`S.leftTensor_le_one`), and `DropBridges` uses them. `AnswerTheorems` instead applies the
  generic `subMeas_sum_adjoint_mul_le_one` at `K →L[ℂ] K`, as the vendored file does, since it
  does not import `LiftBridges`; switching its four sites is a cleanup worth about 0.3 s.
- Every vendored `try rfl -- vendoring` step became a plain `rfl` or a keystone term, and the
  file-wide `backward.isDefEq.respectTransparency false` of the vendored files is not needed.
- The classical half of `Defs`, `Approximation` and `SharedHelpers/SharedLine` (about 0.45k
  vendored lines) is imported from the vendored file and listed under `Not ported` as
  `classical, imported`; a ported file that names it adds it to its own `open` list.

Most of the cost is synthesizing the coercion classes of `𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)` (about 60 ms
per generic `map_*` lemma) and the real scalar structure of `K →L[ℂ] K`, so:
- use the structure's own lemmas (`S.L.map_add`, `S.L.map_mul`) **as terms** (`congrArg …`,
  `.trans`), where they match up to definitional equality: they are stated on
  `(↑S.L).toRingHom`, so as `rw` rules they fail ("did not find an occurrence of the pattern").
  For rewriting use the keystone's oriented placement lemmas (`leftTensor_sub`,
  `leftTensor_mul_leftTensor`, `opTensor_add_left_local`, `leftTensor_real_smul`, …) or
  `map_add S.L`; the term-mode form measured 2.5× faster than `rw [map_add]`;
- for real scalars on a placement use `S.leftTensor_real_smul` / `S.rightTensor_real_smul`
  (`@[simp high]`; Mathlib's `map_smul` does not fire on a real scalar for a `ℂ`-algebra
  homomorphism), proved as `map_smul S.L (c : ℂ) A` up to definitional equality; elsewhere
  rewrite with `← Complex.coe_smul` rather than `RCLike.real_smul_eq_coe_smul`;
- the real ordered-module shortcuts for `K →L[ℂ] K` (`SMul ℝ`, `SMulZeroClass ℝ`, `Module ℝ`,
  `Algebra ℝ`, `IsScalarTower ℝ`, `SMulCommClass ℝ`, `PosSMulMono ℝ`, `SMulPosMono ℝ`) are in
  `Co/Basic/Distribution.lean`, `scoped` to `MIPRE.LIDT.Co` so that they hold in every port file
  and leak to no importer outside it: reuse them, and add a new one there;
- do not mark `star (S.L A) = S.L (star A)` `@[simp]` (the vendored `leftTensor_conjTranspose` is
  `@[simp]`): it loops with `map_star`.
