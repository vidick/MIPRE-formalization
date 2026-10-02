# C6b: the low-individual-degree test in II₁ finite pairs

Tracking: #259, and the C6 row of `planning/mipco-track.md` (Phase 6). Written 2026-10-01, after the
maintainer chose the II₁ orthonormalization tier, from a design round of six parts: four
surveys of the code and four paper proofs, each proof checked by three independent skeptics and
revised, most of the new steps prototyped in Lean. The proofs are recorded in
`reports/c6b-paper-proofs.md`; the audit that sized the port is `reports/lidt-co-audit.md`.

**Status (2026-10-02): C6b is complete.** `MIPRE.LIDT.Simul.soundFin : SoundFin` is proved
(`Co/SoundFin.lean`, blueprint `thm:lidt-sound-fin`): the seeded low-individual-degree test is sound
in every dyadic pair. With it **`MIPRE.mipco_eq_core : MIPCo = IsCoRE` holds without hypothesis**
(`MIPRE/MIPCo.lean`, `thm:mipco-eq-core-unconditional`). The tier (T1–T5, about 3.0k lines) and the
port (M0–M14, 71.7k lines under `MIPRE/Background/LIDT/Co/`, at 0.54× the vendored elaboration time
on the files with a vendored counterpart) are done; what is left is off the route (§4 item 8). The
rest of this paragraph is the record of how it went. The orthonormalization tier is complete (T1–T5
below). De la Salle's
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
dyadic pair, with the symmetric strategy and orthonormalization in it (8 modules, 2.75k lines,
2.71k since M8 moved 41 of them to their mirrored homes). M9
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
0.24× the vendored elaboration time, and well under their estimated sizes (§3). M4, M6, M7 and
M8 are done too (2026-10-02): the definitions and statements of the main induction step with the
Schwartz–Zippel step of the main theorem (4 modules, 1,771 lines;
`Co.Test.mainFormalStep5_selfConsistency_ofExpansionBound`), `GlobalVariance` (15 modules, 3,558
lines; `Co.GlobalVariance.globalVarianceOfPoints`), `Commutativity` (43 modules, 8,025 lines;
`Co.Commutativity.comMain`) and the dimension-free part of `MakingMeasurementsProjective` (7
modules, 1,442 lines; `Co.MakingMeasurementsProjective.orthonormalization`), whose rounding to
projective measurements calls T1, T5 and M2's Theorem G in place of the vendored
finite-dimensional route, its 17 other vendored files being dropped or imported. Together 14,796
lines, at 0.65× the vendored elaboration time; M4 within its estimate and M6–M8 well under theirs.
M10 and M11 are done too (2026-10-02): `SelfImprovement` (30 modules, 11,411 lines;
`Co.SelfImprovement.selfImprovement`), whose semidefinite program is M9's summed form through a
two-part adapter and whose rounding is M8's orthonormalization, so that its top theorems take the
model hypotheses `hS hA` and `1 ≤ params.d`, its 8 matrix-realization files being dropped, and
`Pasting` (76 modules, 17,577 lines; `Co.Pasting.ldPasting`, with no new hypothesis); 28,988 lines,
at 0.78× and 0.40× the vendored elaboration time, every file within the 2× rule but the
statement file `SelfImprovement/Theorems/Statements` (2.19×). **M12–M14 are done too, and with them
C6b** (2026-10-02). M12 is the main induction (20 modules, 6,445 lines;
`Co.MainInductionStep.mainInduction`), which threads `hd : 1 ≤ params.d` beside `hS hA`. M13 is the
main theorem in a dyadic pair (7 modules, 2,715 lines; `Co.Test.mainFormal`): the main induction
runs in the doubled model `D(M)`, where M2 discharges `hS hA`, Theorem E unsymmetrizes its output,
and the vendored tail runs on `M` itself through a new two-space calculus. M14 is the model chain
(12 modules, 2,155 lines): the canonical-line theorem in a dyadic pair
(`Co.Bridge.soundLidtIn_of_isDyadicPair`), which supplies `hd` from the theorem's own `1 ≤ d`, and
the simultaneous contract from it in any model (`Co.Chain.soundIn_of_soundLidtIn`), which takes
`1 ≤ d` from `SoundIn`'s hypotheses. So `MIPRE.LIDT.Simul.soundFin : SoundFin` holds
(`Co/SoundFin.lean`), and **`MIPRE.mipco_eq_core : MIPCo = IsCoRE` holds without hypothesis**
(`MIPRE/MIPCo.lean`, blueprint `thm:mipco-eq-core-unconditional`). The port is 71.7k lines, M12 at
0.34× the vendored elaboration time and M13 at 1.07× on its paired files, every file within the 2×
rule but `MainInductionStep/Theorems/MainTheorems/Successor` (2.28×, signatures); the departures
are recorded under "Departures in M12, M13 and M14".

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
| M2 | the doubling: `D(M)` as a symmetric model and as a finite pair, no abelian projections in it, the role-average identity, the symmetric strategy, unsymmetrization at the vendored cut, orthonormalization in `D(M)` | M0, T1, T2 | new 0.95–1.45k; replaces about 3.96k vendored lines | done, except Theorem E beyond its arithmetic. 2,748 lines in 8 modules, 2,707 after M8 moved 41 of them to their mirrored homes. `MIPRE/Foundations/FinitePairOrder.lean` (271) holds the ⋆-isomorphisms of a finite pair's algebras onto the commutants, `IsFinitePair.equivA`/`equivB`, and the order agreement `IsFinitePair.nonneg_iff_A`/`_B` (report §4 Lemma 10 = §5 Lemma 13), now the library's one order-agreement lemma. `MIPRE/Foundations/Doubling.lean` (473) holds block-diagonal operators on `H ⊕ H`, `VecTrace.diag2` and `NoAbelianProj`. Then `Co/Doubling/Model.lean` (219): `Doubling.model hM hψ : SymModel (Loc M) (Ampl (Fin 2) M.H)` over `Loc M = centralizer M.opsB × centralizer M.opsA`. `FinitePair.lean` (272): Theorems A and F, `isFinitePair`, `L_nonneg_iff`, `equiv : 𝒜 × ℬ ≃⋆ₐ Loc M`, `isDyadicPair`, `noAbelianProj_iff`. `Halving.lean` (257): Theorem C, `bornProb_model_eq`, `qBipartiteConsDefect_model`, `dis_model`, `inconsistency_model`. `Strategy.lean` (452): Theorem D, `symmStrat`, `symmStrat_isGood_three_mul`, and the arithmetic of E, `bipartiteConsError_components_le_two_mul`. `Orthonormalization.lean` (384; 343 after M8 moved the completion and its restriction to their mirrored homes): Theorem G for `ζ > 0`, stated over any symmetric model whose bipartite reading is a finite pair without abelian projections in its first player's operators (`SymModel.orthonormalization_of_isFinitePair` and its relational form `_sddRel`, the shape M8's ported `MakingMeasurementsProjective.orthonormalization` and M10's generic consumer need), with `Doubling.orthonormalization_model` its specialization to `D(M)`; and Proposition H, `SymModel.L_cfc`/`R_cfc` for an injective placement and `Doubling.cfc_mem_opsA`. And `Co/Test/StrategyBiProj/Measurements.lean` (420): the two-space surrogate `fail_M` (`ProjStrat.lowIndividualDegreeFailureProbability`), ported. Without the surrogate, which the estimate left to the port base, 2,328 new lines against 0.95–1.45k: the docstrings, both directions of every transport, the translation to the report's `𝒜 × ℬ` and the POVM transports were not in the estimate. Theorem B is M0's. Open: Theorem E itself, which needs the point consistency of the ported `mainInduction` (M12) and is M13's, with the two-space tail; supplying `ζ > 0` at the in-core call site of Theorem G, by threading `1 ≤ params.d` from `SoundIn` (M14), the case `ζ = 0` itself not being proved and not needed once this is done; Remarks R1–R2, off the route. Elaboration was measured with `-DElab.async=false` in one run per file at load 0.7–1.0, with a 1 s threshold, and was not compared with the vendored files. No declaration takes 3 s. The largest are the `equivHom`/`equivInv` definitions of `FinitePair.lean` at 2.5 and 2.6 s, `inconsistency_model` and `qBipartiteConsDefect_model` of `Halving.lean` at 2.3 s, and `cfc_mem_opsA` at 1.8–2.0 s; `orthonormalization_model` takes 1.1 s. (An earlier measurement put `L_cfc`, `R_cfc` and `cfc_L_mem_range` at 3.4–4.1 s when stated for `D(M)`, most of it synthesizing the functional calculus of `Ampl (Fin 2) M.H →L[ℂ] _` in the header; stated over a symmetric model they take under 1 s.) Blueprint `lem:finite-pair-order`, `def:doubled-model`, `lem:doubled-model-finite-pair`, `lem:doubled-model-role-average`, `lem:doubled-model-no-abelian`, `thm:doubled-symmetrization`, `thm:doubled-orthonormalization` |
| M3 | the rest of `Preliminaries` | M0 | 7.64k → 5.0–7.2k (6.0–7.0k): 6.17k quantum lines in 23 files, `Polynomials.lean` classical; r 0.6–0.95, `SwitchSandwich`, `Triangles` and `CauchySchwarz` being close kin of `ComparisonCore` and `DistanceBounds`, which ported at about 0.5 | done: 23 modules under `Co/Preliminaries/`, every vendored file but the classical `Polynomials.lean`, 3,421 lines for 7,505 vendored (0.46; r = 0.36 on the ported declarations, net of headers, 2,215 lines for 6,174 quantum lines before the review, whose shared expansion changed that by a few lines), below the estimate for the reasons under "Departures in M3 and M5"; non-import elaboration 38.1 s against 63.1 s (0.60×), every file within the 2× rule (largest `BipartiteSelfConsistency/Completion`, 1.03×), no declaration at 2 s (largest `globalVarianceTraceForm_eq_closedForm` of M5, 1.40 s, and `switchSandwich_rightTransfer`, 1.37 s asynchronously at load 1.0 and 1.47–1.72 s with `-DElab.async=false`, vendored 3.85 s; 1.86–2.20 s before the review's shared expansion); `port-pairing.py --check`: 0 missing, 10 classical declarations imported, 4 new. The switch sandwich (`switchSandwich`, `SwitchSandwichStmt`), the two notions of self-consistency (`twoNotionsOfSelfConsistency`, `bipartiteSSC_implies_localSSC_liftLeft`, `otherTwoNotionsOfSelfConsistency`), data processing (`selfConsistencyImpliesDataProcessing`) and completion (`completingToMeasurement`), with every swap and normalization hypothesis dropped. Blueprint `lem:co-switch-sandwich-self-consistency` |
| M4 | `Test` core and `MainInductionStep` definitions and statements | M0, M3 | 1.92k → 1.7–2.0k (1.5–1.8k): `MainInductionStep/{Defs,Statements}` and `Test/{SchwartzZippelStep,StrategyPolynomialFamilies}`, 1.64k quantum lines in 4 files, r 0.9–1.05 | done: 4 modules, `Co/MainInductionStep/{Defs,Statements}` and `Co/Test/{SchwartzZippelStep,StrategyPolynomialFamilies}`, 1,771 lines for 1,915 vendored (0.92; r = 0.90 on the ported declarations, net of headers: `Defs` 0.90, `Statements` 1.01, `SchwartzZippelStep` 0.68, `StrategyPolynomialFamilies` 0.93), within the estimate; non-import elaboration 12.00 s against 7.94 s (1.51×), `MainInductionStep/Statements` at 5.08 s against 2.52 s (2.01×), a file of statement structures just over the 2× rule, recorded as a departure; `port-pairing.py --check`: 0 missing, the 10 classical declarations of `MainInductionStep/Defs` imported, the field `RestrictedSymStrat.isNormalized` a theorem. The checkable theorem is the Schwartz–Zippel step, `Co.Test.mainFormalStep5_selfConsistency_ofExpansionBound` (consistency `ζ` on points gives `ζ + md/q` on whole polynomials); the rest is what M10–M12 consume: `RestrictedSymStrat` and the restricted measurements, `IdxPolyFamily` with `Complete`, `ConsistentWithPoints`, `StronglySelfConsistent` and `SliceBoundednessInput`, `tensorFailureExpectation` (narrowed to one algebra; M12 calls it on `strategy.state`) and the statements of the induction step, `AnswerMainInductionHypothesis` quantifying over `𝔓` and `K`, restricted to strategies whose model is a finite pair without abelian projections in `L(𝔓)` (`strategy.state.toBipartite.IsFinitePair → NoAbelianProj strategy.state.toBipartite.opsA →`, the `hS hA` of M8's `orthonormalization`, which the induction's successor step reaches through self-improvement; M10–M12 thread `hS hA` beside `ζ > 0`, and M13 discharges them for `D(M)`; "Departures in M4, M6, M7 and M8"). Open: the two-space caller of the heterogeneous Step 5 lemma (M13, M14). Blueprint `lem:co-schwartz-zippel-step` |
| M5 | `ExpansionHypercubeGraph`: the scalar part by import; `localToGlobal` by Gram positivity in place of its matrix realization | M0 | 3.8k → 1.0–1.9k (1.0–1.6k): M1 does not inform the Gram-positivity rewrite; the upper end ports every quantum declaration outside `MatrixRealization` (1.62k) at the M1 ratio | done: 5 modules under `Co/ExpansionHypercubeGraph/{Defs,Theorems}/`, `MatrixRealization/{Core,TraceForms}` not ported but replaced by Gram positivity (`re_combinedTraceForm_nonneg`), 852 lines for 3,808 vendored (0.22; r = 0.26), below the floor of the estimate; non-import elaboration 9.0 s against 37.6 s for the whole vendored directory (0.24×; 0.31× against its five counterparts alone), largest declaration `globalVarianceTraceForm_eq_closedForm`, 1.50 s. `localToGlobal params A V : globalVariance params A V ≤ m · localVariance params A V` for every `A : Point params → (K →L[ℂ] K)` and vector state `V`, and `localToGlobalBipartite` for `u ↦ S.L (A u)`; no swap fact and no new keystone positivity used. Blueprint `lem:co-local-to-global` |
| M6 | `GlobalVariance` | M0, M3, M5 | 5.3k → 4.3–4.9k (4.2–4.8k): 4.03k quantum lines in 15 files | done: 15 modules under `Co/GlobalVariance/{Defs,Theorems}/`, 3,558 lines for 5,295 vendored (0.67; r = 0.64), below the estimate; non-import elaboration 25.86 s against 30.05 s (0.86×), every file within the 2× rule; `port-pairing.py --check`: 0 missing, 40 classical declarations imported (`Defs/Core` is classical throughout), 1 new. `Co.GlobalVariance.globalVarianceOfPoints`: for an `(ε, δ, γ)`-good strategy and any polynomial submeasurement `G`, the weighted family `u ↦ S.L (A^u_{g(u)}) * S.R √G_g` has edge deviation at most `6(4ε + 4δ + 2md/q)` (`localVarianceTransportChainBound`) and independent-points deviation at most `24m(ε + δ + md/q)`, with no swap or normalization hypothesis; the vendored weighted state is replaced by that family on `S` itself, as M5's note prescribed. Blueprint `lem:co-global-variance-of-points` |
| M7 | `Commutativity` | M1, M3 | 13.4k → 12.1–13.8k, central 13.2k (10.5–12.5k): 11.29k quantum lines in 43 files, 2% classical; the largest revision, the directory being almost all quantum and `CommutativityPoints`, its closest relative, having ported at about 1.0 on content | done: all 43 modules under `Co/Commutativity/`, 8,025 lines for 13,399 vendored (0.60; r = 0.50), well below the estimate ("Departures in M4, M6, M7 and M8"); non-import elaboration 74.20 s against 134.15 s (0.55×), every file within the 2× rule; `port-pairing.py --check`: 0 missing, 18 classical declarations imported, 4 new (with the arithmetic `commDataProcessedGError_to_comMainError_arith` split out of `Main/EvaluatedQuestions` after review). `Co.Commutativity.comMain` (`thm:com-main`): for an `(ε, δ, γ)`-good strategy in `m + 1` variables and a slice family `G^x` consistent with its points, strongly self-consistent and bounded, each at `ζ`, `E_{x,y} ∑_{g,h} ‖L(G^x_g G^y_h − G^y_h G^x_g)Ψ‖² ≤ 30m(γ^{1/4} + ζ^{1/4} + (d/q)^{1/4})`, through `commDataProcessedG`, the same on evaluated slices at `48m(√γ + √ζ)`; `hnorm` dropped from 45 lemmas, `permInvState` and `densityFixed` from all. Blueprint `lem:co-commutation-g` |
| M8 | `MakingMeasurementsProjective`: the dimension-free part, with the three orthonormalization sites calling T1 | M0, M3, T1 | ≈ 4.1k → 2.6–3.8k (3.3–3.8k) + adapter 0.8–1.5k: quantum share 0.82 and the highest matrix density of any directory, so r 0.6–0.95, about 10 files; about 2.5k further lines unassigned by the audit's partition, which would add 2.0–2.4k if ported | done, in a narrower scope than estimated: 7 of the 24 vendored files ported (`Statements`, `Orthonormalization/{RestrictSome,Completion}`, `Projectivization`, `ProjectivizationChain/Basic`, `LocalityPreservingRepair`, `Orthonormalization`), 1,442 lines for their 2,870 vendored (0.50; r = 0.37); the other 17 (7,398 lines: `Defs`, `Orthonormalization/ErrorBounds`, `NaimarkCore`, `QXPLayer/*`, `QXPLayerIdentities/*`, `SpectralTruncation/*`) dropped, their classical content imported and the finite-dimensional orthonormalization replaced by T1 ("Departures in M4, M6, M7 and M8"); the adapter is M2's Theorem G and two T5 calls. Non-import elaboration 18.97 s against 28.16 s (0.67×), `Orthonormalization` 5.11 s against 2.83 s (1.80×), within the rule while carrying new two-space content; `port-pairing.py --check`: 0 missing, 60 vendored declarations listed as not ported, 3 new. `Co.MakingMeasurementsProjective.orthonormalizationMainLemma` (`84 ζ^{1/4}`) and `orthonormalization` (`100 ζ^{1/4}`) in any symmetric model whose bipartite reading is a finite pair without abelian projections in `L(𝔓)`, for `ζ > 0`, and the two-space heterogeneous forms in a dyadic pair, for M13; M2's `optionCompletion` and `restrictSomeProjSubMeas` moved to their mirrored homes. Open: `ζ = 0`, not needed once M14 threads `1 ≤ params.d` (M2's row). Blueprint `lem:co-orthonormalization` |
| M9 | the summed semidefinite form: a maximizer by weak-operator compactness, first-order conditions giving `Z = Σ T_g A_g ≥ A_g`, solved componentwise in the doubled model; `MatrixRealization` and `SdpMatrixBridge` (3.98k) are not ported | M0, M2 | new 0.55–0.75k (core measured) + adapter 0.1–0.25k (unchanged: new code, no M1 basis) | done, except the adapter. 925 lines in 3 modules against 0.55–0.75k. `MIPRE/Foundations/SummedSdp.lean` (546) has the conclusion `SummedSdp.IsSummedSdp A T Z` over any ordered ⋆-ring, whose fields are those of the vendored `SdpOptimalPairWithSlackness`, and the core chain, Lemmas 1b–3 and 5–9, up to `isSummedSdp_of_isMaxOn` and the converse `isSummedSdp_of_le`. The setting (S) is the commutant `StarSubalgebra.centralizer ℂ t` of any set, with `IsFaithfulTrace`. `MIPRE/Background/Orthonormalization/SdpMaximizer.lean` (165) has Lemma 4, `exists_isMaxOn_obj`, by the vendored weak-operator compactness, and Theorem 10, `exists_isSummedSdp`, `exists_isSummedSdp_finitePairA`/`B`. `Co/Doubling/Sdp.lean` (214) has Corollary 12, `exists_isSummedSdp_loc` and `exists_isSummedSdp_model`, under `L` and `R`, and Lemma 13, `isSummedSdp_equivA_iff`, `exists_isSummedSdp_A`/`B` and `exists_isSummedSdp_prod` over the report's `𝒜 × ℬ`. Componentwise data is automatic, since `Loc M` is a product. Open: the interface adapter to `SdpStatementWithSlackness` (`Measurement`, `G = Polynomial params`, `A_g = averagedPointOperator`), which is M10's because the port's types for it do not exist yet; Remark 12′, not needed. Elaboration: `SummedSdp.le_of_firstOrder` takes 4.9 s (`-DElab.async=false`, load 1.0), just under the 5 s rule, and `isMeasIn_perturb` takes 4.0 s. Both are risks at higher load, and splitting them is worth doing. `exists_isSummedSdp_A` of `Co/Doubling/Sdp.lean` takes 3.9 s (`-DElab.async=false`, load 1.0); nothing else in the three files takes 3 s. Blueprint `thm:summed-sdp`, `cor:summed-sdp-doubled` |
| M10 | `SelfImprovement` theorems and definitions, + the summed-form interface adapter to `SdpStatementWithSlackness` (from M9, 0.1–0.25k) | M3–M6, M8, M9 | 16.44k → 13.1–15.1k (13–15.5k): without `MatrixRealization` and `SdpMatrixBridge`, 13.2k quantum lines in 32 files | done: 30 modules under `Co/SelfImprovement/`, every vendored file but the 7 of `MatrixRealization/` (3,667 lines) and `Theorems/Results/SdpMatrixBridge` (313), replaced by M9's summed form, and the classical `Theorems/Thresholds/{Helper,Final}` (1,210), imported; 11,411 lines for 15,227 vendored (0.75; r = 0.67 on the ported declarations, net of headers, with headers of 87 lines a file against 56 vendored), under the estimate and above the 8.4–10.5k that the rates of M6 and M7 gave ("Departures in M10 and M11"); non-import elaboration 84.18 s against 108.49 s (0.78×), every file within the 2× rule but `Theorems/Statements`, statement structures and the adapter, at 2.19×; `port-pairing.py --check`: 0 missing, 24 vendored declarations listed as not ported (`sdpPrimalObjective`, the real part of a matrix trace, and 23 classical, imported), 6 new, 9 private. The adapter is the two-part one prototyped in the design of M10, about 40 lines: `SdpStatementWithSlackness.of_isSummedSdp` (`Theorems/Statements`) and `sdp_statement_with_slackness params strategy hS` (`HelperCompleteness/Bracketed`), which applies `Doubling.exists_isSummedSdp_A hS` to the averaged point operators. `Co.SelfImprovement.selfImprovement` (`thm:self-improvement`): for an `(ε, δ, γ)`-good strategy and a polynomial measurement `G` with point consistency `ν`, a projective `H` and a witness `Z ≥ E_u A^u_{g(u)}` with completeness `1 − ν − σ`, point consistency, self-closeness and boundedness at `σ = 3000 m (ε^{1/32} + δ^{1/32} + (d/q)^{1/32})`, under `hS hA hd` (`hS` alone for the helper lemma and the SDP producer); the in-core orthonormalization is M8's Theorem G at `ζ = selfImprovementHelperError > 0` (`selfImprovementHelperError_pos`). Open: threading `hd` through M12, supplying it in M14 and discharging `hS hA` in M13. Blueprint `lem:co-self-improvement` |
| M11 | `Pasting` | M1, M3, M4, M7 | 30.3k → 23.2–26.5k (24–28k): 22.07k quantum lines in 76 files, the 5.3k classical lines (`Bernoulli/Scalar` and others) imported; its 87 `try rfl` sites became plain `rfl` in M1 at no change in size | done: all 76 modules under `Co/Pasting/`, 17,577 lines for 30,290 vendored (0.58; r = 0.59), within the 15.2–19.0k that the rates of M6 and M7 gave and well under the estimate; four files are a docstring and imports, their vendored counterparts being classical (`Bernoulli/Scalar`, `Core/DDistinct`, `Defs/Interpolation`, `LineInterpolation/Core`); non-import elaboration 162.15 s against 404.44 s (0.40×), every file within the 2× rule (largest `Sandwich/PastedFamilies` at 1.77× and `Sandwich/Switcheroo` at 1.72×, definitions); `port-pairing.py --check`: 0 missing, 190 classical declarations imported, 0 new (two scoped decidability instances in `LineInterpolation/BadMass`, which the script does not count), 7 private. `Co.Pasting.ldPasting` (`thm:ld-pasting`): for an `(ε, δ, γ)`-good strategy in `m + 1` variables and a slice family complete at `κ` and consistent with the points, strongly self-consistent and bounded at `ζ`, a measurement `H` with point consistency `κ(1 + 1/(100m)) + 2ν + e^{−k/(80000m²)}` for every `k ≥ 400md`, `ν = 100k²m(ε^{1/32} + δ^{1/32} + γ^{1/32} + ζ^{1/32} + (d/q)^{1/32})`; with `ldPastingNCompleteness`, `ldPastingSubMeas` and the matrix Chernoff estimate on a vector state, `chernoffBernoulliMatrix`, its `hnorm` dropped. No statement takes a model hypothesis, pasting neither orthonormalizing nor solving a semidefinite program. Blueprint `lem:co-ld-pasting` |
| M12 | `MainInductionStep` theorems | M7, M10, M11 | 8.9k → 7.1–8.2k (6.5–8.5k): 7.04k quantum lines in 20 files | done: all 20 modules under `Co/MainInductionStep/Theorems/`, 6,445 lines for 8,944 vendored (0.72), within the 5.4–6.5k that the rates of M10 and M11 gave and under the estimate; non-import elaboration 43.72 s against 128.48 s (0.34×, minimum of three runs), every file within the 2× rule but `MainTheorems/Successor` (2.28×, signatures; "Port conventions"); `port-pairing.py --check`: 0 missing. `Co.MainInductionStep.mainInduction` (and the answer-valued `answerMainInduction`, which proves M4's `AnswerMainInductionHypothesis`) over a symmetric model, under `hS hA` and `hd : 1 ≤ params.d`, threaded through the successor step to M10's self-improvement and M8's orthonormalization; the base case and the large-error branches take none of them. Blueprint `lem:co-main-induction`, which `thm:co-main-formal` uses |
| M13 | `Test/MainTheorem` → `Co.mainFormal` over a symmetric model, then over a dyadic pair through the doubling, + Theorem E, unsymmetrization with the two-space tail (from M2) | M2, M8, M12 | 5.06k → 2.5–3.5k (2.5–3.5k): `ScalarBounds` and `SourceScalars` classical and imported, 2.52k quantum lines in 6 files at 2.5–2.9k, plus the dyadic-pair restatement, which M1 does not measure | done, in a different shape ("Departures in M12, M13 and M14"): `Co.Test.mainFormal` is stated directly over the two-space strategy of a dyadic pair, not first over a symmetric model. 7 modules, 2,715 lines: the five ported files of `Test/MainTheorem/` (`MainFormal`, `ProjectiveConsistency/Evaluation`, `SourceRoleRegister/{Core,Completion,Final}`), 1,802 lines for 2,741 vendored (0.66); the new two-space calculus `Test/MainTheorem/TwoSpace.lean` (626); and Theorem E, `Co/Doubling/Unsymmetrization.lean` (287). The seven scalar files are classical and imported, with no Co file; the vendored `Test/StrategyBiProjRoleAverage/Final` and `Test/StrategyBiProjUnsymmetrization` are not ported, replaced by M2's `Doubling/Strategy` and by `Unsymmetrization`. Elaboration of the five paired files 25.46 s against 23.85 s (1.07×), the largest `SourceRoleRegister/Core` at 1.66×; `TwoSpace` 21.5 s and `Unsymmetrization` 10.2 s, new. `port-pairing.py --check`: 0 missing. `Co.Test.mainFormal` takes `hM : strategy.state.IsDyadicPair` and `hd : 1 ≤ params.d`, and `mainFormal_isPVMIn`/`mainFormal_inconsistency` read it in the vocabulary of `SoundIn`. Blueprint `thm:co-main-formal`, `lem:doubled-unsymmetrization` |
| M14 | the error cascade into `deltaSim` and the adapters to `SoundIn`: `SoundIn M` for every dyadic pair `M`, hence `SoundFin`, + `ζ > 0` at the in-core call site of Theorem G, threading `1 ≤ params.d` from `SoundIn` (from M2) | M13, T5 | 1.5–3.5k (unchanged: new code, no M1 basis) | done: 12 modules, 2,155 lines. `Co/Bridge/{Measurement,Strategy,Defect,Value,Consistency,Main}` (1,048 lines), the model forms of the repository's matrix bridge `LIDT/Bridge/*`: a projective strategy of a model for `lidtGame` as the port's `ProjStrat`, its failure surrogate at most `1 − value` (`failure_le`), and `Co.Bridge.soundness`, the canonical-line theorem in a dyadic pair, with `soundLidtIn_of_isDyadicPair`. `Co/Chain/{Defs,Extraction,Reduction,Padding,Simultaneous}` (1,058 lines), the model forms of the operator halves of `LIDT/{Adapter/Reduction,Padding,Extraction,Simultaneous}`: `SoundLidtIn M`, the canonical-line theorem in a model with `1 ≤ d` added, and `Co.Chain.soundIn_of_soundLidtIn : SoundLidtIn M → SoundIn M` for every model with `SoundIn`'s instance set. `Co/SoundFin.lean` (49): `MIPRE.LIDT.Simul.soundFin`. The matrix files stay, since they prove `soundIn_tensor`, and their classical halves are imported. Elaboration 30.95 s; 28.36 s for the ten files with a matrix counterpart against 95.71 s (0.30×). `MIPRE.mipco_eq_core : MIPCo = IsCoRE` (`MIPRE/MIPCo.lean`) is `mipco_eq_core_of_lidtFin LIDT.Simul.soundFin`. Blueprint `lem:co-lidt-canonical-line`, `lem:lidt-sound-in-of-model-lidt`, `thm:lidt-sound-fin`, `thm:mipco-eq-core-unconditional` |

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

**Revised after M4, M6, M7 and M8** (2026-10-02). M4 came to 1,771 lines against 1.7–2.0k, M6 to
3,558 against 4.3–4.9k, M7 to 8,025 against 12.1–13.8k and M8 to 1,442 against 3.4–5.3k with its
adapter: 14,796 lines in all against 21.5–26.0k. 31.4k lines are done (M0 5.70k, M1 3.01k, M2
2.71k, M3 3.37k, M4 1.77k, M5 0.85k, M6 3.56k, M7 8.03k, M8 1.44k, M9 0.93k). At the estimates
above, M10–M14 are 47–57k more and the port 79–88k. Those estimates take r = 0.85–1.0 from
`CommutativityPoints`, but `Commutativity`, the directory closest to `Pasting` and the
`MainInductionStep` theorems, measured r = 0.50, and `GlobalVariance` 0.64: their vendored proofs
restate placements in every step and prove Kronecker identities entrywise, as M3's did. At r =
0.50–0.64, with the 55–65-line headers of M6 and M7, M10 would be 8.4–10.5k, M11 15.2–19.0k and
M12 4.6–5.8k, so M10–M14 32–43k and the port 64–74k. M4–M8 elaborate at 0.65× their vendored files
(131.0 s against 200.3 s), and M0, M1 and M3–M8 together at 0.67× (246.7 s against 368.1 s;
"Port conventions").

**Revised after M10 and M11** (2026-10-02). M10 came to 11,411 lines against 13.1–15.1k (8.4–10.5k
at the rates of M6 and M7) and M11 to 17,577 against 23.2–26.5k (15.2–19.0k): 28,988 lines in all,
r = 0.67 and 0.59. 60.4k lines are done (M0 5.70k, M1 3.01k, M2 2.71k, M3 3.37k, M4 1.77k, M5 0.85k,
M6 3.56k, M7 8.03k, M8 1.44k, M9 0.93k, M10 11.41k, M11 17.58k). What remains is M12 (7.1–8.2k at
the estimate above; 5.4–6.5k at the rates M10 and M11 measured, r = 0.59–0.67 with headers of 59–87
lines a file on its 7.04k quantum lines in 20 files), M13 (2.5–3.5k) and M14 (1.5–3.5k): 11–15k, or
9–14k, and the port 71–76k in all, or 70–74k, against the 64–74k projected after M8. M10 and M11
elaborate at 0.48× their vendored files (246.3 s against 512.9 s), and M0, M1, M3–M8, M10 and M11
together at 0.56× (493.1 s against 881.1 s; "Port conventions").

**After M12–M14** (2026-10-02). M12 came to 6,445 lines against 7.1–8.2k (5.4–6.5k at the rates of
M10 and M11), M13 to 2,715 against 2.5–3.5k and M14 to 2,155 against 1.5–3.5k: 11,315 lines against
the 11–15k (9–14k) projected. **The port is complete at 71.7k lines** (M0 5.70k, M1 3.01k, M2 2.71k,
M3 3.37k, M4 1.77k, M5 0.85k, M6 3.56k, M7 8.03k, M8 1.44k, M9 0.93k, M10 11.41k, M11 17.58k, M12
6.45k, M13 2.72k, M14 2.16k), inside the 71–76k projected after M11 and at the low end of the
audit's 70–120k, with the tier's 3.0k beside it. M12 elaborates at 0.34× its vendored files and the
paired files of M13 at 1.07×; M0, M1, M3–M8 and M10–M13 together, on the files with a vendored
counterpart, at 0.54× (562.3 s against 1,033.4 s; "Port conventions").

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
6. **M4, M6, M7 and M8, done** (2026-10-02): the main induction step's definitions and statements
   with the Schwartz–Zippel step, `GlobalVariance`, `Commutativity` and the dimension-free part of
   `MakingMeasurementsProjective`, with their blueprint nodes and axiom guards (§3), at 0.65× the
   vendored elaboration time; the departures, M8's 17 dropped files among them, are recorded under
   "Port conventions". They leave to later stages the two-space callers of M4's heterogeneous Step
   5 lemma and of M8's heterogeneous orthonormalizations (M13), `tensorFailureExpectation` on
   `strategy.state` (M12), `ζ > 0` at the in-core orthonormalization (M14, as for M2), and the
   model hypotheses `hS : S.toBipartite.IsFinitePair` and `hA : NoAbelianProj
   S.toBipartite.opsA` of M8's `orthonormalization`, which M4's `AnswerMainInductionHypothesis`
   already carries and M10–M12 must thread beside `ζ > 0` (M13 discharging them for `D(M)`).
7. **M10 and M11, done** (2026-10-02): `SelfImprovement` and `Pasting`, with their blueprint nodes
   and axiom guards (§3), at 0.78× and 0.40× the vendored elaboration time; the departures,
   M10's eight dropped matrix-realization files and its three threaded hypotheses among them, are
   recorded under "Port conventions". M10 closes M9's open adapter and M2's and M8's `ζ > 0` at
   the in-core orthonormalization, by `hd : 1 ≤ params.d` on `selfImprovement`; of the model
   hypotheses only M10's top theorems take any, M11's statements none. They leave to later stages
   the threading of `hd` beside `hS hA` through the induction (M12; M4's
   `AnswerMainInductionHypothesis` carries `hS hA` but not `hd`), supplying `hd` from `SoundIn`
   (M14) and discharging `hS hA` for `D(M)` (M13), and a cleanup: the two scoped decidability
   instances of `LineInterpolation/BadMass` belong in an earlier shared `Pasting` file.
8. **M12, M13 and M14, done** (2026-10-02): the main induction, the main theorem in a dyadic pair
   with Theorem E, and the model chain to `SoundIn`, with their blueprint nodes
   (`lem:co-main-induction`, `lem:doubled-unsymmetrization`, `thm:co-main-formal`,
   `lem:co-lidt-canonical-line`, `lem:lidt-sound-in-of-model-lidt`, `thm:lidt-sound-fin`,
   `thm:mipco-eq-core-unconditional`) and axiom guards (§3). `MIPRE.LIDT.Simul.soundFin : SoundFin` (`Co/SoundFin.lean`, `thm:lidt-sound-fin`) closes
   C6b, and `MIPRE.mipco_eq_core : MIPCo = IsCoRE` holds without hypothesis
   (`thm:mipco-eq-core-unconditional`); the conditional theorem of that name is renamed
   `mipco_eq_core_of_compression`. The departures are recorded under "Departures in M12, M13 and
   M14".
   Left for later, off the route: the cleanup of M11 (the two scoped decidability instances of
   `LineInterpolation/BadMass`), the case `ζ = 0` of Theorem G, Remarks R1–R2, and the statement
   files over the 2× rule (`MainInductionStep/Statements`, `SelfImprovement/Theorems/Statements`,
   `MainInductionStep/Theorems/MainTheorems/Successor`).

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
  core's parameters (report §4). *M10*: `selfImprovement` takes `hd : 1 ≤ params.d`, which makes
  its orthonormalization error positive; M12 threads it and M14 supplies it.
- **The semidefinite witness `Z`** must lie in the doubled local algebra; the componentwise
  solution needs the `A_g` to be componentwise (report §5). *Settled by M9:* the local algebra
  of `D(M)` is the product `Loc M`, so every `A_g` of it is a pair, and
  `Doubling.exists_isSummedSdp_model` gives `T` and `Z` in `Loc M`. What is left is the adapter
  (M10). *Done in M10*: `SdpStatementWithSlackness.of_isSummedSdp` and
  `sdp_statement_with_slackness params strategy hS`, through `Doubling.exists_isSummedSdp_A`.
- **Elaboration time** is the main risk of the port: operator positivity on `K →L[ℂ] K` costs 1–3 s
  per proof against 0.6 s for the matrix version, roughly doubling under the whole-Mathlib imports
  the vendored classical layer forces. Positivity lemmas go in a base file without those imports.
  Measured on M0 and M1, the port is at 1.02× the vendored files and no declaration takes 1.4 s (§4
  item 3); the remaining risk is the definition-heavy files, where typeclass inference on signatures
  over `K →L[ℂ] K` dominates, as in `Test/Defs` (2.97×). The per-file rule was expected to fail for
  that reason in `MainInductionStep/Defs`, `SelfImprovement/Defs`, `GlobalVariance/Defs/*` and the
  definitions of `Commutativity` and `Pasting`. Measured on M4, M6 and M7, it held in the files
  named: `MainInductionStep/Defs` is at 2.31 s against 1.79 s (1.29×),
  `GlobalVariance/Defs/Families` at 3.20 s against 2.79 s (1.15×), the `Commutativity` definitions
  at most 1.10×; it failed, narrowly, only in `MainInductionStep/Statements`, the statement
  structures of the induction step, at 2.01×. Measured on M10 and M11, it held in
  `SelfImprovement/Defs` (3.59 s against 8.71 s, the vendored file elaborating its classical
  half) and in every `Pasting` file, the definitions included (at most 1.77×); it failed again only
  in a file of statement structures, `SelfImprovement/Theorems/Statements`, at 2.19×. No cheap fix
  for signature synthesis is known.
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

**Elaboration, measured on M0 and M1, on M3 and M5, on M4, M6, M7 and M8, on M10 and M11, and on M12–M14.** Non-import
elaboration of each file, `lake env lean -Dprofiler=true`, the sum of every profiler category except
`import`, minimum of three runs, in seconds, against the vendored file measured the same way on the
same machine. Lines are `wc -l`; "tc" is the typeclass-inference part, ported / vendored. Measured
2026-10-01, 19:20–19:37 UTC, on a 4-core machine at load 0.5–1.7, on the files of commit `9fea38a`.
Every M0 file reproduces the first M0 measurement (after the review round; the earlier figure of
2.4 s for the vendored keystone did not reproduce) within 14%, the largest changes being the vendored
`SubMeasurementFamilies` (+14%), the ported `Test/StrategyCore` (+13%), the ported `DistanceBounds`
(+10%) and the vendored `TensorPlacement` (+10%); the layer totals reproduce within 2% (51.8 s
against 52.0 s ported, 53.0 s against 52.0 s vendored). So the move of the M0 ratio from 1.00× to
0.98× is within the reproducibility of the measurement, and the per-file ratios are good to about
±15%. The line counts are those of `9fea38a`; the review after it added docstrings and
upstream-qualified references to `CommutativityPoints` (3,077 lines now, no proof changed), which
leaves the elaboration figures as they are and moves r from 0.95 to 0.97, the docstrings being
charged to the declarations.

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
| `MainInductionStep/Defs.lean` | 458 | 549 | 2.31 | 1.79 | 1.29 | 0.68 / 0.27 |
| `MainInductionStep/Statements.lean` | 708 | 681 | 5.08 | 2.52 | 2.01 | 1.03 / 0.36 |
| `Test/SchwartzZippelStep.lean` | 274 | 354 | 2.32 | 2.15 | 1.08 | 0.70 / 0.66 |
| `Test/StrategyPolynomialFamilies.lean` | 331 | 331 | 2.28 | 1.48 | 1.55 | 0.78 / 0.25 |
| **all of M4** | 1771 | 1915 | 12.00 | 7.94 | 1.51 | 3.2 / 1.5 |
| `GlobalVariance/Defs/Core.lean` | 59 | 179 | 0.47 | 1.07 | 0.44 | 0.00 / 0.06 |
| `GlobalVariance/Defs/Families.lean` | 337 | 396 | 3.20 | 2.79 | 1.15 | 1.50 / 1.09 |
| `GlobalVariance/Defs/Operators.lean` | 290 | 267 | 1.73 | 1.40 | 1.24 | 0.59 / 0.30 |
| `GlobalVariance/Theorems/AlgebraicIdentity.lean` | 334 | 427 | 2.56 | 2.58 | 0.99 | 0.94 / 0.64 |
| `GlobalVariance/Theorems/Averaging.lean` | 154 | 273 | 2.16 | 3.01 | 0.72 | 0.93 / 0.70 |
| `GlobalVariance/Theorems/CollisionExpansion.lean` | 321 | 564 | 1.51 | 2.09 | 0.72 | 0.40 / 0.47 |
| `GlobalVariance/Theorems/MainTheorems.lean` | 221 | 300 | 1.22 | 1.17 | 1.04 | 0.23 / 0.18 |
| `GlobalVariance/Theorems/PolynomialSumBounds.lean` | 162 | 321 | 1.21 | 1.60 | 0.75 | 0.26 / 0.34 |
| `GlobalVariance/Theorems/SelfConsistencyTransport/Point.lean` | 254 | 390 | 1.36 | 1.75 | 0.78 | 0.43 / 0.42 |
| `GlobalVariance/Theorems/SelfConsistencyTransport/PointLine.lean` | 351 | 381 | 2.12 | 1.88 | 1.13 | 0.64 / 0.41 |
| `GlobalVariance/Theorems/SelfConsistencyTransport/Utilities.lean` | 207 | 346 | 2.13 | 2.13 | 1.00 | 0.77 / 0.51 |
| `GlobalVariance/Theorems/SelfConsistencyTransportSum.lean` | 248 | 342 | 1.69 | 1.48 | 1.14 | 0.45 / 0.23 |
| `GlobalVariance/Theorems/Statements.lean` | 142 | 119 | 0.85 | 0.70 | 1.21 | 0.11 / 0.05 |
| `GlobalVariance/Theorems/TransportChain/Core.lean` | 263 | 520 | 1.96 | 3.20 | 0.61 | 0.42 / 0.65 |
| `GlobalVariance/Theorems/TransportChain/SumForm.lean` | 215 | 470 | 1.68 | 3.21 | 0.52 | 0.27 / 0.55 |
| **all of M6** | 3558 | 5295 | 25.86 | 30.05 | 0.86 | 7.9 / 6.6 |
| `Commutativity/Defs/Core.lean` | 228 | 276 | 1.72 | 1.56 | 1.10 | 0.63 / 0.48 |
| `Commutativity/Defs/Normalization.lean` | 197 | 230 | 1.52 | 5.57 | 0.27 | 0.51 / 4.09 |
| `Commutativity/Defs/Stability.lean` | 222 | 224 | 2.57 | 2.68 | 0.96 | 1.16 / 1.33 |
| `Commutativity/EvaluatedSliceBounds/PhaseOneThree.lean` | 146 | 248 | 1.39 | 2.53 | 0.55 | 0.27 / 0.58 |
| `Commutativity/EvaluatedSliceCommutation/Averages.lean` | 146 | 340 | 1.83 | 3.22 | 0.57 | 0.57 / 1.47 |
| `Commutativity/EvaluatedSliceCommutation/Consequences.lean` | 93 | 91 | 0.79 | 0.73 | 1.08 | 0.10 / 0.08 |
| `Commutativity/GCommStability/OverlapOne.lean` | 206 | 271 | 1.70 | 1.74 | 0.98 | 0.52 / 0.50 |
| `Commutativity/GCommStability/OverlapTwo.lean` | 216 | 310 | 1.74 | 3.09 | 0.56 | 0.36 / 1.39 |
| `Commutativity/GCommStability/Scalar/Common.lean` | 198 | 350 | 2.45 | 5.17 | 0.47 | 0.94 / 2.70 |
| `Commutativity/GCommStability/Scalar/First.lean` | 119 | 123 | 1.03 | 0.80 | 1.29 | 0.26 / 0.08 |
| `Commutativity/GCommStability/Scalar/RawSecond.lean` | 304 | 689 | 2.61 | 9.52 | 0.27 | 0.83 / 4.29 |
| `Commutativity/GCommStability/Scalar/Second.lean` | 129 | 133 | 1.06 | 0.82 | 1.28 | 0.25 / 0.09 |
| `Commutativity/Main/Auxiliary/HEvalTransport.lean` | 189 | 401 | 1.98 | 3.95 | 0.50 | 0.54 / 1.66 |
| `Commutativity/Main/Auxiliary/ScalarMarginalization.lean` | 239 | 428 | 2.05 | 2.08 | 0.99 | 0.50 / 0.52 |
| `Commutativity/Main/EvaluatedQuestions.lean` | 205 | 514 | 2.72 | 11.93 | 0.23 | 0.37 / 2.00 |
| `Commutativity/Main/Results.lean` | 138 | 163 | 0.86 | 1.05 | 0.82 | 0.11 / 0.22 |
| `Commutativity/Scaffold/Core.lean` | 107 | 106 | 0.73 | 0.64 | 1.14 | 0.07 / 0.04 |
| `Commutativity/Scaffold/Products.lean` | 280 | 441 | 3.52 | 5.04 | 0.70 | 1.54 / 2.18 |
| `Commutativity/Scaffold/Symmetry.lean` | 85 | 82 | 0.72 | 0.71 | 1.01 | 0.08 / 0.04 |
| `Commutativity/ScalarApproximation/Core.lean` | 77 | 213 | 1.07 | 2.14 | 0.50 | 0.12 / 0.48 |
| `Commutativity/ScalarApproximation/PaperChainBasic/Normalization.lean` | 264 | 627 | 3.69 | 6.02 | 0.61 | 1.58 / 2.79 |
| `Commutativity/ScalarApproximation/PaperChainBasic/PointSwap.lean` | 149 | 201 | 1.29 | 1.56 | 0.83 | 0.26 / 0.32 |
| `Commutativity/ScalarApproximation/PaperChainBasic/Reindexing.lean` | 95 | 113 | 0.94 | 0.80 | 1.17 | 0.15 / 0.05 |
| `Commutativity/ScalarApproximation/PaperChainPhaseFive.lean` | 356 | 569 | 2.52 | 3.32 | 0.76 | 0.64 / 0.77 |
| `Commutativity/ScalarApproximation/PaperChainPhaseSeven.lean` | 115 | 161 | 1.13 | 1.69 | 0.67 | 0.21 / 0.50 |
| `Commutativity/ScalarApproximation/PaperChainPhaseSix.lean` | 127 | 241 | 1.31 | 2.29 | 0.57 | 0.29 / 0.96 |
| `Commutativity/ScalarApproximation/PaperChainReverse.lean` | 95 | 103 | 0.77 | 0.81 | 0.95 | 0.09 / 0.11 |
| `Commutativity/ScalarApproximation/PaperChainTail.lean` | 154 | 254 | 1.43 | 2.04 | 0.70 | 0.29 / 0.37 |
| `Commutativity/ScalarApproximation/Pointwise.lean` | 283 | 553 | 2.82 | 3.96 | 0.71 | 0.80 / 1.52 |
| `Commutativity/ScalarApproximation/ProcessedG.lean` | 115 | 168 | 0.72 | 0.78 | 0.93 | 0.07 / 0.10 |
| `Commutativity/ScalarApproximation/ProcessedG/MainChain.lean` | 383 | 817 | 3.24 | 11.52 | 0.28 | 0.86 / 1.90 |
| `Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean` | 393 | 704 | 3.18 | 8.01 | 0.40 | 1.06 / 1.87 |
| `Commutativity/Transport/EvaluationSpecialization.lean` | 165 | 191 | 1.65 | 1.61 | 1.03 | 0.61 / 0.47 |
| `Commutativity/Transport/FullSlice/Averages.lean` | 308 | 427 | 1.73 | 1.78 | 0.97 | 0.45 / 0.36 |
| `Commutativity/Transport/FullSlice/Bridges/Closeness.lean` | 226 | 350 | 1.86 | 2.95 | 0.63 | 0.48 / 0.65 |
| `Commutativity/Transport/FullSlice/Bridges/ClosenessCore.lean` | 108 | 152 | 0.86 | 1.19 | 0.72 | 0.11 / 0.13 |
| `Commutativity/Transport/FullSlice/Bridges/ClosenessXEval.lean` | 116 | 200 | 1.01 | 1.47 | 0.69 | 0.15 / 0.23 |
| `Commutativity/Transport/FullSlice/Bridges/QSDD.lean` | 124 | 195 | 1.71 | 2.75 | 0.62 | 0.52 / 1.21 |
| `Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean` | 337 | 695 | 2.99 | 6.44 | 0.46 | 0.79 / 2.28 |
| `Commutativity/Transport/FullSlice/Machinery/Marginalization/Y.lean` | 151 | 318 | 1.45 | 2.26 | 0.64 | 0.28 / 0.29 |
| `Commutativity/Transport/FullSlice/Machinery/Normalization.lean` | 207 | 347 | 1.60 | 2.36 | 0.68 | 0.38 / 0.76 |
| `Commutativity/Transport/FullSlice/ZeroBounds.lean` | 148 | 273 | 1.56 | 2.80 | 0.56 | 0.49 / 1.35 |
| `Commutativity/Transport/Pullback.lean` | 82 | 107 | 0.69 | 0.77 | 0.90 | 0.08 / 0.07 |
| **all of M7** | 8025 | 13399 | 74.20 | 134.15 | 0.55 | 20.4 / 43.3 |
| `MakingMeasurementsProjective/LocalityPreservingRepair.lean` | 277 | 818 | 3.73 | 10.12 | 0.37 | 1.54 / 5.74 |
| `MakingMeasurementsProjective/Orthonormalization.lean` | 405 | 502 | 5.11 | 2.83 | 1.80 | 2.19 / 1.13 |
| `MakingMeasurementsProjective/Orthonormalization/Completion.lean` | 114 | 214 | 2.27 | 2.20 | 1.03 | 0.74 / 0.60 |
| `MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean` | 52 | 50 | 0.53 | 1.05 | 0.50 | 0.04 / 0.28 |
| `MakingMeasurementsProjective/Projectivization.lean` | 331 | 662 | 4.12 | 8.36 | 0.49 | 1.49 / 3.29 |
| `MakingMeasurementsProjective/ProjectivizationChain/Basic.lean` | 125 | 237 | 1.94 | 1.94 | 1.00 | 0.44 / 0.34 |
| `MakingMeasurementsProjective/Statements.lean` | 138 | 387 | 1.28 | 1.65 | 0.77 | 0.25 / 0.27 |
| **all of M8** | 1442 | 2870 | 18.97 | 28.16 | 0.67 | 6.7 / 11.6 |
| **M4, M6, M7 and M8** | 14796 | 23479 | 131.03 | 200.29 | 0.65 | 38.2 / 63.1 |
| **M0, M1, M3–M8** | 27774 | 45947 | 246.74 | 368.13 | 0.67 | 79.3 / 115.0 |
| `SelfImprovement/Defs.lean` | 268 | 397 | 3.59 | 8.71 | 0.41 | 1.88 / 5.70 |
| `SelfImprovement/Theorems/AddInUFullStatement.lean` | 161 | 198 | 0.80 | 0.96 | 0.84 | 0.12 / 0.11 |
| `SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Residual.lean` | 407 | 456 | 2.33 | 2.99 | 0.78 | 0.69 / 0.40 |
| `SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/ScalarChain.lean` | 371 | 511 | 2.28 | 2.82 | 0.81 | 0.71 / 1.14 |
| `SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Selection.lean` | 496 | 731 | 3.16 | 7.58 | 0.42 | 1.09 / 4.04 |
| `SelfImprovement/Theorems/Results/AddInUPointConsistency.lean` | 394 | 518 | 2.07 | 2.98 | 0.69 | 0.72 / 0.72 |
| `SelfImprovement/Theorems/Results/AddInUStep12/Algebra.lean` | 470 | 576 | 3.58 | 3.42 | 1.04 | 1.21 / 0.87 |
| `SelfImprovement/Theorems/Results/AddInUStep12/Raw.lean` | 368 | 663 | 4.06 | 3.76 | 1.08 | 1.66 / 0.91 |
| `SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean` | 389 | 804 | 5.26 | 7.47 | 0.70 | 2.28 / 3.33 |
| `SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Factored.lean` | 238 | 398 | 1.31 | 2.24 | 0.58 | 0.34 / 0.53 |
| `SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean` | 505 | 761 | 3.70 | 10.38 | 0.36 | 1.46 / 5.36 |
| `SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Transfer.lean` | 362 | 537 | 3.01 | 3.69 | 0.82 | 0.81 / 0.90 |
| `SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Variance.lean` | 542 | 653 | 2.81 | 2.95 | 0.95 | 0.95 / 0.69 |
| `SelfImprovement/Theorems/Results/BoundednessTransport/BoundednessGap.lean` | 506 | 648 | 3.12 | 3.67 | 0.85 | 0.95 / 0.96 |
| `SelfImprovement/Theorems/Results/BoundednessTransport/Decomposition.lean` | 231 | 337 | 1.83 | 1.76 | 1.04 | 0.49 / 0.28 |
| `SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistency.lean` | 412 | 548 | 2.53 | 2.20 | 1.15 | 0.79 / 0.59 |
| `SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistencyLiteral.lean` | 382 | 371 | 1.95 | 1.48 | 1.31 | 0.57 / 0.35 |
| `SelfImprovement/Theorems/Results/CommonHelpers.lean` | 134 | 166 | 1.33 | 1.29 | 1.03 | 0.47 / 0.30 |
| `SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean` | 527 | 580 | 2.75 | 2.08 | 1.32 | 0.97 / 0.52 |
| `SelfImprovement/Theorems/Results/HelperCompleteness/FiberBounds.lean` | 452 | 604 | 4.66 | 6.40 | 0.73 | 1.52 / 3.06 |
| `SelfImprovement/Theorems/Results/HelperCompleteness/InputSdp.lean` | 267 | 339 | 1.91 | 1.78 | 1.07 | 0.51 / 0.47 |
| `SelfImprovement/Theorems/Results/HelperCompleteness/Linearized.lean` | 400 | 504 | 2.72 | 2.58 | 1.06 | 0.87 / 0.63 |
| `SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean` | 588 | 819 | 2.43 | 4.75 | 0.51 | 0.92 / 1.23 |
| `SelfImprovement/Theorems/Results/HelperSSC/Core.lean` | 368 | 516 | 2.28 | 3.43 | 0.67 | 0.62 / 0.61 |
| `SelfImprovement/Theorems/Results/HelperSSC/PostDeleteA.lean` | 455 | 720 | 4.50 | 5.64 | 0.80 | 1.47 / 1.43 |
| `SelfImprovement/Theorems/Results/SelfImprovementTop/Completeness.lean` | 196 | 280 | 1.54 | 1.21 | 1.27 | 0.43 / 0.23 |
| `SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean` | 651 | 709 | 6.95 | 7.02 | 0.99 | 2.60 / 2.04 |
| `SelfImprovement/Theorems/Results/SelfImprovementTop/FinalFields.lean` | 145 | 132 | 0.94 | 0.74 | 1.26 | 0.20 / 0.07 |
| `SelfImprovement/Theorems/Results/SelfImprovementTop/SelfCloseness.lean` | 195 | 258 | 1.27 | 0.89 | 1.43 | 0.36 / 0.18 |
| `SelfImprovement/Theorems/Statements.lean` | 531 | 493 | 3.48 | 1.59 | 2.19 | 1.34 / 0.30 |
| **all of M10** | 11411 | 15227 | 84.18 | 108.49 | 0.78 | 29.0 / 37.9 |
| `Pasting/Bernoulli/DegreeZero.lean` | 381 | 969 | 3.16 | 13.19 | 0.24 | 1.02 / 4.42 |
| `Pasting/Bernoulli/Final.lean` | 603 | 819 | 3.67 | 9.07 | 0.40 | 0.95 / 2.83 |
| `Pasting/Bernoulli/FromHToG.lean` | 149 | 154 | 0.78 | 0.85 | 0.92 | 0.09 / 0.06 |
| `Pasting/Bernoulli/FromHToG/AdjacentStages/Chain/FinalMove.lean` | 145 | 210 | 1.79 | 3.71 | 0.48 | 0.38 / 0.34 |
| `Pasting/Bernoulli/FromHToG/AdjacentStages/Chain/HalfSandwich.lean` | 271 | 486 | 3.08 | 10.24 | 0.30 | 0.76 / 0.98 |
| `Pasting/Bernoulli/FromHToG/AdjacentStages/StageA0M1.lean` | 228 | 495 | 3.88 | 7.00 | 0.55 | 1.50 / 1.10 |
| `Pasting/Bernoulli/FromHToG/Core/AveragesAndOps.lean` | 193 | 323 | 2.86 | 2.29 | 1.25 | 1.21 / 0.36 |
| `Pasting/Bernoulli/FromHToG/Core/BernoulliTail.lean` | 131 | 169 | 1.42 | 2.65 | 0.54 | 0.52 / 1.42 |
| `Pasting/Bernoulli/FromHToG/Core/FactBundles.lean` | 96 | 286 | 0.90 | 18.98 | 0.05 | 0.09 / 3.23 |
| `Pasting/Bernoulli/FromHToG/Core/StageMass.lean` | 272 | 523 | 3.11 | 4.13 | 0.75 | 0.91 / 1.09 |
| `Pasting/Bernoulli/FromHToG/MoveLemmas/Basic.lean` | 255 | 569 | 3.14 | 5.19 | 0.61 | 1.26 / 1.68 |
| `Pasting/Bernoulli/FromHToG/MoveLemmas/TailStage.lean` | 156 | 271 | 1.48 | 2.13 | 0.69 | 0.34 / 0.41 |
| `Pasting/Bernoulli/FromHToG/PaperBounds.lean` | 192 | 484 | 2.02 | 3.14 | 0.64 | 0.52 / 0.68 |
| `Pasting/Bernoulli/FromHToG/PaperBounds/SandwichContext.lean` | 241 | 546 | 2.85 | 4.71 | 0.60 | 0.92 / 1.57 |
| `Pasting/Bernoulli/FromHToG/PaperMoveChain/Moves.lean` | 204 | 404 | 2.18 | 4.62 | 0.47 | 0.59 / 0.72 |
| `Pasting/Bernoulli/FromHToG/PaperMoveChain/Telescope.lean` | 329 | 643 | 4.10 | 9.26 | 0.44 | 1.43 / 2.40 |
| `Pasting/Bernoulli/MatrixChernoff.lean` | 159 | 170 | 3.74 | 8.74 | 0.43 | 1.58 / 1.92 |
| `Pasting/Bernoulli/Scalar.lean` | 55 | 527 | 0.55 | 11.38 | 0.05 | 0.00 / 2.96 |
| `Pasting/Bernoulli/ScalarBounds.lean` | 155 | 256 | 1.83 | 5.26 | 0.35 | 0.35 / 1.69 |
| `Pasting/Bernoulli/TruncatedSums.lean` | 192 | 409 | 2.47 | 4.78 | 0.52 | 0.81 / 1.75 |
| `Pasting/Bernoulli/Weights.lean` | 119 | 127 | 0.96 | 0.95 | 1.01 | 0.17 / 0.07 |
| `Pasting/CommutingWithG/Complete.lean` | 149 | 361 | 0.81 | 14.41 | 0.06 | 0.08 / 2.49 |
| `Pasting/CommutingWithG/Incomplete.lean` | 124 | 214 | 1.71 | 2.31 | 0.74 | 0.45 / 0.26 |
| `Pasting/ComparisonLemmas/Common.lean` | 159 | 380 | 1.20 | 8.85 | 0.14 | 0.22 / 2.68 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich.lean` | 88 | 85 | 0.75 | 0.72 | 1.03 | 0.08 / 0.03 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/BackChain.lean` | 155 | 255 | 1.43 | 2.05 | 0.70 | 0.25 / 0.31 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Base.lean` | 128 | 192 | 1.14 | 1.28 | 0.89 | 0.18 / 0.14 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Chain.lean` | 163 | 159 | 1.34 | 1.46 | 0.92 | 0.16 / 0.17 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Core.lean` | 133 | 225 | 1.30 | 4.30 | 0.30 | 0.25 / 0.95 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChain.lean` | 248 | 387 | 1.96 | 3.35 | 0.58 | 0.40 / 0.78 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/FlatChainStep.lean` | 268 | 531 | 1.89 | 3.34 | 0.56 | 0.23 / 0.77 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/MoveChain/Lifting.lean` | 304 | 661 | 2.64 | 3.84 | 0.69 | 0.78 / 0.87 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/Definitions.lean` | 423 | 683 | 2.54 | 3.91 | 0.65 | 0.83 / 0.70 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Move.lean` | 251 | 584 | 2.32 | 3.93 | 0.59 | 0.75 / 0.82 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/StepLemmas/Split.lean` | 215 | 299 | 1.80 | 3.01 | 0.60 | 0.36 / 0.84 |
| `Pasting/ComparisonLemmas/CommuteGHalfSandwich/Setup/SumBounds.lean` | 206 | 392 | 2.46 | 7.48 | 0.33 | 0.83 / 3.53 |
| `Pasting/ComparisonLemmas/HAConsistency.lean` | 490 | 612 | 2.90 | 3.05 | 0.95 | 0.87 / 0.80 |
| `Pasting/ComparisonLemmas/HBConsistency.lean` | 196 | 206 | 1.12 | 1.02 | 1.10 | 0.19 / 0.15 |
| `Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean` | 643 | 735 | 4.21 | 3.92 | 1.07 | 1.53 / 1.14 |
| `Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CauchySchwarz.lean` | 367 | 666 | 3.83 | 6.38 | 0.60 | 1.33 / 1.88 |
| `Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Core.lean` | 317 | 402 | 1.29 | 1.99 | 0.65 | 0.27 / 0.50 |
| `Pasting/ComparisonLemmas/LdSandwichLineOnePoint/Endpoint.lean` | 362 | 686 | 3.41 | 12.17 | 0.28 | 0.91 / 3.51 |
| `Pasting/ComparisonLemmas/LdSandwichLineOnePoint/EndpointEquivs.lean` | 65 | 273 | 0.64 | 2.24 | 0.29 | 0.01 / 0.23 |
| `Pasting/ComparisonLemmas/LdSandwichLineOnePoint/OutcomeLemmas.lean` | 277 | 582 | 3.37 | 21.28 | 0.16 | 0.66 / 3.58 |
| `Pasting/ComparisonLemmas/LdSandwichLineOnePoint/PrefixMoved.lean` | 371 | 418 | 4.10 | 5.41 | 0.76 | 1.01 / 1.76 |
| `Pasting/ComparisonLemmas/LineInterpolation/Averaging.lean` | 112 | 213 | 1.54 | 2.38 | 0.65 | 0.75 / 0.60 |
| `Pasting/ComparisonLemmas/LineInterpolation/BadLine.lean` | 88 | 133 | 1.07 | 2.24 | 0.48 | 0.19 / 0.27 |
| `Pasting/ComparisonLemmas/LineInterpolation/BadMass.lean` | 569 | 811 | 5.46 | 9.08 | 0.60 | 1.75 / 3.98 |
| `Pasting/ComparisonLemmas/LineInterpolation/Core.lean` | 55 | 456 | 0.46 | 3.71 | 0.12 | 0.00 / 0.86 |
| `Pasting/ComparisonLemmas/LineInterpolation/HBError.lean` | 281 | 442 | 1.83 | 6.13 | 0.30 | 0.75 / 1.67 |
| `Pasting/ComparisonLemmas/OverAllOutcomes/ErrorAndMass.lean` | 238 | 529 | 2.79 | 11.91 | 0.23 | 0.81 / 3.60 |
| `Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean` | 410 | 587 | 2.91 | 4.59 | 0.63 | 0.98 / 1.36 |
| `Pasting/ComparisonLemmas/OverAllOutcomes/NonglobalDecomposition.lean` | 379 | 510 | 3.39 | 4.06 | 0.84 | 1.18 / 1.19 |
| `Pasting/Core/CompletePart.lean` | 165 | 446 | 2.24 | 4.59 | 0.49 | 0.59 / 1.68 |
| `Pasting/Core/DDistinct.lean` | 40 | 179 | 0.58 | 4.15 | 0.14 | 0.00 / 1.36 |
| `Pasting/Core/LdGbcon.lean` | 365 | 642 | 2.56 | 4.86 | 0.53 | 0.88 / 1.91 |
| `Pasting/Defs/Families.lean` | 136 | 194 | 1.25 | 1.95 | 0.64 | 0.40 / 0.73 |
| `Pasting/Defs/Interpolation.lean` | 58 | 244 | 0.57 | 1.72 | 0.33 | 0.00 / 0.25 |
| `Pasting/Defs/Tuples.lean` | 139 | 258 | 1.75 | 1.84 | 0.95 | 0.64 / 0.45 |
| `Pasting/GHatFacts.lean` | 332 | 577 | 2.40 | 6.50 | 0.37 | 0.56 / 0.73 |
| `Pasting/Sandwich/GHatSandwich.lean` | 192 | 299 | 2.13 | 3.62 | 0.59 | 0.86 / 1.46 |
| `Pasting/Sandwich/PastedFamilies.lean` | 350 | 349 | 2.38 | 1.35 | 1.77 | 0.99 / 0.19 |
| `Pasting/Sandwich/Switcheroo.lean` | 270 | 330 | 2.92 | 1.70 | 1.72 | 1.13 / 0.29 |
| `Pasting/Statements.lean` | 481 | 540 | 2.96 | 1.88 | 1.58 | 0.63 / 0.43 |
| `Pasting/SwitcherooCompletion.lean` | 165 | 304 | 1.25 | 8.77 | 0.14 | 0.20 / 1.63 |
| `Pasting/SwitcherooCompletion/CompletePart.lean` | 98 | 302 | 0.82 | 18.02 | 0.05 | 0.09 / 2.97 |
| `Pasting/SwitcherooCompletion/Expansion.lean` | 168 | 370 | 2.10 | 3.87 | 0.54 | 0.47 / 1.01 |
| `Pasting/SwitcherooCompletion/FourthTermChain.lean` | 239 | 442 | 1.79 | 5.39 | 0.33 | 0.41 / 2.55 |
| `Pasting/SwitcherooCompletion/SecondTerm.lean` | 177 | 362 | 1.60 | 2.33 | 0.69 | 0.35 / 0.54 |
| `Pasting/SwitcherooCompletion/Utilities.lean` | 128 | 149 | 1.11 | 1.32 | 0.84 | 0.17 / 0.14 |
| `Pasting/SwitcherooContraction/Commuted.lean` | 129 | 264 | 1.51 | 5.45 | 0.28 | 0.32 / 3.24 |
| `Pasting/SwitcherooContraction/ScalarTerms.lean` | 201 | 202 | 1.72 | 2.67 | 0.64 | 0.41 / 1.00 |
| `Pasting/SwitcherooContraction/Split.lean` | 441 | 591 | 4.04 | 16.95 | 0.24 | 1.38 / 10.20 |
| `Pasting/SwitcherooSetup/Centers.lean` | 174 | 228 | 1.27 | 1.84 | 0.69 | 0.27 / 0.37 |
| `Pasting/SwitcherooSetup/Infrastructure.lean` | 211 | 308 | 2.27 | 4.02 | 0.56 | 0.77 / 2.07 |
| `Pasting/SwitcherooSetup/Terms.lean` | 158 | 201 | 1.35 | 1.61 | 0.84 | 0.29 / 0.44 |
| **all of M11** | 17577 | 30290 | 162.15 | 404.44 | 0.40 | 46.2 / 109.8 |
| **M10 and M11** | 28988 | 45517 | 246.33 | 512.92 | 0.48 | 75.2 / 147.7 |
| **M0, M1, M3–M8, M10 and M11** | 56762 | 91464 | 493.07 | 881.05 | 0.56 | 154.5 / 262.7 |
| `MainInductionStep/Theorems/AvgSliceErrors/Core.lean` | 442 | 819 | 3.82 | 17.42 | 0.22 | 0.99 / 4.58 |
| `MainInductionStep/Theorems/AvgSliceErrors/Successor.lean` | 382 | 526 | 2.95 | 7.59 | 0.39 | 0.83 / 2.44 |
| `MainInductionStep/Theorems/InductionParameterBounds/Averaging.lean` | 52 | 125 | 0.55 | 1.63 | 0.33 | 0.00 / 0.51 |
| `MainInductionStep/Theorems/InductionParameterBounds/MainError.lean` | 278 | 720 | 2.72 | 24.95 | 0.11 | 0.67 / 9.13 |
| `MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean` | 54 | 182 | 0.68 | 3.55 | 0.19 | 0.00 / 1.13 |
| `MainInductionStep/Theorems/InductionParameterBounds/SelfImprovement.lean` | 115 | 148 | 1.04 | 3.55 | 0.29 | 0.17 / 1.25 |
| `MainInductionStep/Theorems/MainTheorems/Base.lean` | 233 | 423 | 1.52 | 1.73 | 0.88 | 0.36 / 0.43 |
| `MainInductionStep/Theorems/MainTheorems/Successor.lean` | 373 | 343 | 2.63 | 1.15 | 2.28 | 1.36 / 0.17 |
| `MainInductionStep/Theorems/PastingAssembly/AnswerFields.lean` | 281 | 326 | 1.78 | 1.87 | 0.95 | 0.45 / 0.43 |
| `MainInductionStep/Theorems/PastingAssembly/Basic.lean` | 412 | 790 | 2.07 | 20.22 | 0.10 | 0.72 / 4.64 |
| `MainInductionStep/Theorems/PastingAssembly/ErrorBounds.lean` | 177 | 380 | 0.91 | 21.74 | 0.04 | 0.12 / 4.70 |
| `MainInductionStep/Theorems/PastingAssembly/Successor.lean` | 511 | 562 | 2.38 | 3.74 | 0.64 | 0.69 / 1.04 |
| `MainInductionStep/Theorems/RestrictedProbabilities/AnswerValued.lean` | 578 | 694 | 3.71 | 3.66 | 1.01 | 1.11 / 0.77 |
| `MainInductionStep/Theorems/RestrictedProbabilities/Axis.lean` | 196 | 265 | 1.54 | 1.59 | 0.97 | 0.35 / 0.31 |
| `MainInductionStep/Theorems/RestrictedProbabilities/Base.lean` | 73 | 222 | 0.67 | 1.87 | 0.35 | 0.07 / 0.49 |
| `MainInductionStep/Theorems/RestrictedProbabilities/Core.lean` | 97 | 97 | 0.78 | 0.74 | 1.06 | 0.08 / 0.05 |
| `MainInductionStep/Theorems/RestrictedProbabilities/Diagonal.lean` | 210 | 259 | 1.63 | 1.63 | 1.00 | 0.34 / 0.36 |
| `MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean` | 765 | 801 | 4.58 | 3.36 | 1.36 | 1.69 / 0.53 |
| `MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean` | 677 | 652 | 5.07 | 3.44 | 1.47 | 1.79 / 0.65 |
| `MainInductionStep/Theorems/StageDataConstructors.lean` | 539 | 610 | 2.69 | 3.04 | 0.89 | 0.75 / 0.86 |
| **all of M12** | 6445 | 8944 | 43.72 | 128.48 | 0.34 | 12.5 / 34.5 |
| `Doubling/Unsymmetrization.lean` (new) | 287 | — | 10.21 | — | — | 3.06 / — |
| `Test/MainTheorem/MainFormal.lean` | 337 | 348 | 2.93 | 4.28 | 0.68 | 0.77 / 1.05 |
| `Test/MainTheorem/ProjectiveConsistency/Evaluation.lean` | 166 | 234 | 1.65 | 1.59 | 1.04 | 0.46 / 0.40 |
| `Test/MainTheorem/SourceRoleRegister/Completion.lean` | 537 | 984 | 12.38 | 11.22 | 1.10 | 6.81 / 4.07 |
| `Test/MainTheorem/SourceRoleRegister/Core.lean` | 387 | 555 | 4.38 | 2.64 | 1.66 | 1.51 / 0.79 |
| `Test/MainTheorem/SourceRoleRegister/Final.lean` | 375 | 620 | 4.12 | 4.11 | 1.00 | 1.49 / 1.42 |
| `Test/MainTheorem/TwoSpace.lean` (new) | 626 | — | 21.52 | — | — | 12.40 / — |
| **M13, the five files with a vendored counterpart** | 1802 | 2741 | 25.46 | 23.85 | 1.07 | 11.0 / 7.7 |
| **all of M13 (the two new files included)** | 2715 | 2741 | 57.19 | 23.85 | — | 26.5 / 7.7 |
| **M0, M1, M3–M8 and M10–M13** (paired files) | 65009 | 103149 | 562.26 | 1033.38 | 0.54 | 178.1 / 304.9 |
| `Bridge/Consistency.lean` (against `LIDT/Bridge/Consistency.lean`) | 86 | 64 | 0.82 | 0.73 | 1.14 | 0.11 / 0.07 |
| `Bridge/Defect.lean` (against `LIDT/Bridge/Defect.lean`) | 149 | 139 | 2.05 | 1.77 | 1.16 | 0.67 / 0.51 |
| `Bridge/Main.lean` (against `LIDT/Bridge/Main.lean`) | 207 | 137 | 2.47 | 1.91 | 1.29 | 0.85 / 0.48 |
| `Bridge/Measurement.lean` (against `LIDT/Bridge/Measurement.lean`) | 197 | 353 | 1.45 | 4.73 | 0.31 | 0.38 / 1.31 |
| `Bridge/Strategy.lean` (against `LIDT/Bridge/Strategy.lean`) | 138 | 71 | 1.62 | 1.53 | 1.06 | 0.50 / 0.13 |
| `Bridge/Value.lean` (against `LIDT/Bridge/Value.lean`) | 271 | 346 | 5.72 | 10.88 | 0.53 | 1.36 / 1.64 |
| `Chain/Defs.lean` (new) | 166 | — | 2.01 | — | — | 0.68 / — |
| `Chain/Extraction.lean` (against `LIDT/Extraction.lean`) | 313 | 768 | 4.84 | 11.55 | 0.42 | 1.57 / 3.34 |
| `Chain/Padding.lean` (against `LIDT/Padding.lean`) | 123 | 919 | 1.95 | 37.09 | 0.05 | 0.69 / 3.91 |
| `Chain/Reduction.lean` (against `LIDT/Adapter/Reduction.lean`) | 261 | 307 | 3.57 | 3.65 | 0.98 | 1.45 / 1.10 |
| `Chain/Simultaneous.lean` (against `LIDT/Simultaneous.lean`) | 195 | 347 | 3.87 | 21.89 | 0.18 | 1.42 / 6.08 |
| `SoundFin.lean` (new) | 49 | — | 0.58 | — | — | 0.01 / — |
| **M14, the ten files with a matrix counterpart (the repository's own files, not vendored)** | 1940 | 3451 | 28.36 | 95.71 | 0.30 | 9.0 / 18.6 |
| **all of M14** | 2155 | 3451 | 30.95 | 95.71 | — | 9.7 / 18.6 |

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

**The M4, M6, M7 and M8 rows** were measured the same way on 2026-10-02, 04:52–05:59 UTC, on the
same 4-core machine at load 0.7–2.1, ported and vendored file alternating, three rounds, on the
files of commit `60f1c59` (lines by `wc -l`). Each file of M8 is set against the vendored file of
the same path only; the 17 vendored files M8 drops have no row. Every file passes the 2× rule of §4
item 3 but one, `MainInductionStep/Statements`, at 2.01×, a file of statement structures without
proofs ("Departures in M4, M6, M7 and M8"). The next largest are M8's `Orthonormalization` at 1.80×,
which carries new two-space content (the Cauchy–Schwarz core and the two T5 lemmas) that has no
vendored cost, and M4's `StrategyPolynomialFamilies` at 1.55×, definitions as well. M4 is at 1.51×,
M6 at 0.86×, M7 at 0.55× and M8 at 0.67×; the other proof files are at 0.23–1.29×, and the largest
savings are where the vendored proofs were slowest (`Main/EvaluatedQuestions` 0.23×,
`ProcessedG/MainChain` 0.28×, `Scalar/RawSecond` 0.27×, `Defs/Normalization` 0.27×). M4–M8 as a
whole are at 0.65×, and the port costs 8.9 ms a line on them against 8.5 ms vendored. With
`-Dtrace.profiler=true -Dtrace.profiler.threshold=1000`, one run per ported file under the default
asynchronous elaboration, at load 0.9–1.4 (06:00–06:11 UTC), seven declarations reached 1 s, all of
them proofs, and the review's run (load 1.1–2.2) found an eighth,
`Commutativity.fullSliceCommutation_qSDDOp_avg_expand_full` (`Transport/FullSlice/Bridges/QSDD`,
1.03 s at load 1.10). The largest, `Commutativity.fullSliceCommutation_of_evaluated_on_evaluated_questions`
(its vendored counterpart takes 13.1 s, over the 5 s rule), measured 2.42 s there and 2.99–3.17 s in
the review, 1.88 s of it the real arithmetic of its small-parameter case; that arithmetic is now the
standalone `commDataProcessedGError_to_comMainError_arith` (`New here`), and the two take 0.86–1.20 s
and 1.36–1.66 s. Measured again the same way after that split, at load 0.8–1.7 (07:57–08:09 UTC),
seven declarations reach 1 s: `Commutativity.evaluatedSlice_scalar_chain_bound` 2.00 s (2.07–2.20 s
in the earlier runs), `Commutativity.gCommStabilityTwo_raw_scalar_pointwise_bound` 1.47 s,
`Commutativity.commDataProcessedGError_to_comMainError_arith` 1.36 s,
`MakingMeasurementsProjective.Orthonormalization.Completion.optionCompletion_bipartiteSSCRel` 1.24 s
(vendored 1.39 s), `Commutativity.GCommStability.Scalar.scalar_pointwise_cauchy_schwarz_bound` 1.18
s, `Commutativity.stabilityDefect_ev_eq` 1.14 s and
`MakingMeasurementsProjective.leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul`
1.13 s; `fullSliceCommutation_qSDDOp_avg_expand_full` stays under 1 s at that load. So no
declaration takes 2.3 s at load up to 2.2, and the 5 s rule holds with a factor of two to spare.
`MainInductionStep/Statements` sits at the 2× boundary rather than clearly over it: 2.01× above,
1.94× in the review's minimum of three (4.97 s against 2.56 s), and 1.99× after M4's
`AnswerMainInductionHypothesis` gained its finite-pair hypotheses and the import of
`Foundations/Doubling` (5.52 s against 2.77 s, minimum of three, load 0.9–1.1, 08:10 UTC).
None of the 69 files sets an option or raises a heartbeat limit, and none needs the file-wide
`respectTransparency` that 85 of their vendored counterparts set.

**The M10 and M11 rows** were measured the same way on 2026-10-02, 14:09–15:05 UTC, on the same
4-core machine, three rounds with the ported and vendored file of each pair alternating, but two
pairs at a time, so at load 0.9–3.3 rather than the 0.5–2.1 of the earlier rows; the line counts
are those of the working tree measured (the files of `9e4b844` and the units finished after it).
Both sides of a pair ran under the same conditions, so the ratios compare as before, and the
absolute times are, if anything, high. Every file passes the 2× rule of §4 item 3 but one,
`SelfImprovement/Theorems/Statements`, at 2.19× (3.48–3.75 s against 1.59–2.00 s over the rounds),
a file of statement structures with M10's adapter, the case of `MainInductionStep/Statements`
("Departures in M10 and M11"). The next largest are M11's `Sandwich/PastedFamilies` at 1.77×,
`Sandwich/Switcheroo` at 1.72× and `Statements` at 1.58×, definitions all three, and M10's
`SelfImprovementTop/SelfCloseness` at 1.43×. M10 is at 0.78× and M11 at 0.40×, and the largest
savings are the files whose vendored counterparts elaborate classical lemmas that the port imports
prebuilt (`Bernoulli/FromHToG/Core/FactBundles`, `Bernoulli/Scalar`,
`SwitcherooCompletion/CompletePart` and `CommutingWithG/Complete`, 0.05–0.06×;
`LdSandwichLineOnePoint/OutcomeLemmas` 0.16×). The port costs 7.4 ms a line on M10 and 9.2 ms on
M11, against 7.1 and 13.4 ms vendored. With `-Dtrace.profiler=true -Dtrace.profiler.threshold=1000`,
one run per file on each side under the default asynchronous elaboration, two at a time at load
1.8–2.5 (15:05–15:24 UTC), 21 ported declarations reach 1 s, all of them proofs, and none 3 s: the
largest are `Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts` 2.82 s (2.03–2.15 s
in its unit's runs at load 0.5–0.7), `Pasting.chernoffBernoulliMatrix` 2.22 s (vendored 4.39 s), the
two private moves of `PaperMoveChain/Telescope` 1.96 and 1.84 s,
`SelfImprovement.helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta` 1.48 s and
`SelfImprovement.selfImprovementHelper` 1.42 s. On the vendored side 121 declarations reach 1 s and
twelve take more than 5 s, the largest 21.8 s. Eight of the twelve are classical lemmas the port
imports prebuilt (`firstSwitcherooError_le_eighth_stage` 21.8 s,
`ldSandwichLineOnePoint_endpoint_comm_error_le` 21.5 s, `fromHToGPaperTotalError_le` 20.6 s,
`secondSwitcherooError_le_commutingWithGCompleteError` 15.4 s, …); the other four are ported, and
take under 1 s here or are split: `commutativitySwitcheroo_ofCompleteSelfConsistency` (10.4 s),
`fromHToGAdjacentStage_paperMoveChain` (10.3 s, split into the two moves above),
`switcherooAggregateFourthTerm_once_commuted_contraction_left` (6.5 s) and
`switcherooAggregateFourthTerm_split_contraction` (6.1 s). So the 5 s rule holds with a factor of
about 1.8 to spare at load 2.5, and of more than 2 at the loads of the units' own runs; none of the
106 files sets an option or raises a heartbeat limit.

**The M12, M13 and M14 rows** were measured on 2026-10-02, 19:11–19:30 UTC, on the same 4-core
machine at load 0.4–3.3, with `lake env lean -Dprofiler=true -Dtrace.profiler=true
-Dtrace.profiler.threshold=1000`, two files at a time, three rounds, each round running every
ported file and then its counterpart, so that the two sides alternate; each row is the minimum of
the three runs on each side. They replace single-run figures taken by the units at load 0.3–4.3,
which they mostly lower, by as much as a third (the vendored
`InductionParameterBounds/MainError`, 36.2 s then and 25.0 s now). Line counts are those of the working tree. M12 and M13
are compared with their vendored files; M14 has no vendored counterpart, and its `Bridge` and
`Chain` files are compared with the repository's own matrix files whose model forms they are,
which stay because they prove `soundIn_tensor`. `TwoSpace`, `Unsymmetrization`, `Chain/Defs` and
`SoundFin` are new and have nothing to compare with.

M12 is at 0.34× its vendored files (43.7 s against 128.5 s), the largest savings again being files
whose vendored counterparts elaborate classical lemmas the port imports prebuilt
(`PastingAssembly/ErrorBounds` 0.04×, `PastingAssembly/Basic` 0.10×,
`InductionParameterBounds/MainError` 0.11×). One file departs from the 2× rule:
**`MainTheorems/Successor`, at 2.28×** (2.63 s against 1.15 s), whose cost is typeclass inference
(1.36 s against 0.17 s) on the signatures of the induction's successor step, which carry
`hS hA hd` and the stage records over `𝔓` and `K →L[ℂ] K`, the case of the statement files
`MainInductionStep/Statements` (2.01×) and `SelfImprovement/Theorems/Statements` (2.19×); it is
1.5 s in absolute terms. Next are `SelfImprovementAssembly/Core` (1.47×) and `/AnswerSlice`
(1.36×), for the same reason. M13's five files with a vendored counterpart are at 1.07× (25.5 s
against 23.8 s), the largest `SourceRoleRegister/Core` at 1.66× and `SourceRoleRegister/Completion`
at 1.10×; the new two-space calculus `TwoSpace` costs 21.5 s (626 lines, typeclass inference
12.4 s, the placements and completions over abstract star-ordered algebras and `M.H →L[ℂ] M.H`)
and `Unsymmetrization` 10.2 s (287 lines). M14 is at 0.30× its matrix counterparts (28.4 s against
95.7 s; `Chain/Padding` 0.05× and `Chain/Simultaneous` 0.18×, whose matrix files elaborate the
classical lemmas the chain imports), the largest ratio `Bridge/Main` at 1.29×. M12, M13 and M14
together cost 131.9 s. The port costs 6.8 ms a line on M12, 21.1 ms on M13 and 14.4 ms on M14,
against 14.4, 8.7 and 27.7 ms on their counterparts. M0, M1, M3–M8 and M10–M13 together, on the
files with a vendored counterpart, elaborate at 0.54× (562.3 s against 1,033.4 s).

Per declaration the record is a bound, since which declarations cross 1 s depends on the load:
no ported declaration reaches 3 s, the largest being `Co.Bridge.failure_eq_sum` at 2.73 s in one
run of a review re-profile at load 2.0–2.7 (matrix 2.00 s there; 1.81 s at load 0.7). That
re-profile (three runs, two files at a time) found at least 19 ported declarations reaching 1 s:
the 13 below, plus `Co.Chain.clSoundness_padded` (1.14–1.50 s) and
`Co.Chain.soundIn_of_soundLidtIn` (1.14–1.21 s), which crossed 1 s in every run there but in none
at load 0.9, and four that crossed it in some runs only: the private
`three_le_k_sq_mul_next_m_of_nonneg` (1.21, 1.28 s),
`le_one_of_mainInductionError_lt_one_of_nonneg` (1.07 s), `Co.Bridge.mdef_le` (1.06 s) and
`Co.Chain.clSoundness_ldc_one` (1.07 s). The first measurement, at a 1 s threshold and taking the
largest of three runs, found 13: `TwoSpace.two_questionConsistency_eq_questionSDD_of_projective`
2.29 s, `Co.Bridge.failure_eq_sum` 2.18 s (matrix 2.15 s), the definitions
`TwoSpace.completeAtOutcomeProjA` and `…B` 1.78 and 1.76 s and their `_toMeasurement` equations
1.41 and 1.34 s, `ProjStrat.qSDD_rightPlaced_completeAtOutcome_eq` and `…left…` 1.28 and 1.21 s (vendored 1.60
and 1.36 s),
`Doubling.pairMeasurement` 1.15 s, two private averaging lemmas of `AvgSliceErrors/{Core,Successor}`
1.13 and 1.01 s, `Test.mainFormalConclusion_ofRoleRegisterScalarBoundary` 1.06 s (vendored
3.42 s) and `Co.Chain.inconsistency_extract_left_le` 1.03 s; `pairMeasurement`, the
`AvgSliceErrors/Successor` lemma, `mainFormalConclusion_…` and `inconsistency_extract_left_le`
reached 1 s in one run of three only. On the other side 46 declarations reach 1 s and seven take more than 5 s, all classical
lemmas that the port imports prebuilt: four vendored
(`ldPastingInInductionError_le_mainInductionError_of_bounds` 21.2 s,
`ldPastingInInductionNu_le_fifth_mainInductionNu` 15.4 s, `average_sliceMainInductionNu_le` 5.9 s,
`average_answerSuccessorSliceMainInductionNu_le` 5.7 s) and three of the matrix chain
(`Simul.deltaCL_padded_le` 14.3 s, `accepts_sample_of` 11.6 s, `valAt_rmap` 11.3 s). So the 5 s
rule holds with a factor of two to spare at load 3; none of the 39 files sets an option or raises
a heartbeat limit, while every vendored counterpart of M12 and M13 sets the file-wide
`respectTransparency false`.

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
  Moving them next to the others was tried after M8 and not kept: it took `Orthonormalization.lean`
  from 20.6–20.9 s to 18.5–19.4 s of non-import elaboration but `Model.lean` from 18.5–19.1 s to
  20.8–21.5 s (two runs each, load 0.9–1.7), so the three instances cost about as much wherever they
  are declared, and the functional calculus on `Loc M` is not where `Orthonormalization.lean` spends
  its time.
- **`Co/Doubling/Orthonormalization.lean` and `Model.lean` are the most expensive files of the
  doubling**, which the M2 row records only per declaration. `Orthonormalization.lean` takes about
  20 s of non-import elaboration (20.6–20.9 s in two runs at load 0.9–1.1 on 2026-10-02, 19.7–21.7
  s in the six of the M4–M8 review, before and after M8 moved 41 lines out of it), half of it
  typeclass inference (10.1–11.0 s), and `Model.lean` 18.5–19.1 s, each about four times the most
  expensive file of M4–M8. Neither has a vendored counterpart, so the 2× rule does not apply, and
  the cost is spread: with a 1 s threshold the largest declarations of `Orthonormalization.lean`
  are `map_cfc_of_injective` (1.85–2.12 s), `cfc_mem_opsA` (1.40–1.56 s), `cfc_mem_opsB`
  (1.31–1.49 s), `one_sub_sum_norm_sq_completion_le` (1.23–1.26 s) and a statement whose
  `SubMeas.map` argument elaborates in 1.05–1.46 s.
- `Co/Doubling/Orthonormalization.lean` declared the completion of a submeasurement and the
  restriction of a projective submeasurement on `Option Outcome` under their vendored names,
  `MakingMeasurementsProjective.optionCompletion` (with its two `@[simp]` outcome lemmas) and
  `MakingMeasurementsProjective.restrictSomeProjSubMeas`, generic over an ordered `⋆`-ring. M8 moved
  them, unchanged, into its ports of `LDT/MakingMeasurementsProjective/Statements.lean` and
  `.../Orthonormalization/RestrictSome.lean`, which `Co/Doubling/Orthonormalization.lean` now
  imports. Theorem G and Proposition H are stated over any symmetric model
  (`SymModel.orthonormalization_of_isFinitePair`, `SymModel.L_cfc`), with the doubled model a
  one-line specialization.
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

**Departures in M4, M6, M7 and M8.**
- **Three of the four came in under their estimates, M8 far under**: M4 at 1.77k lines against
  1.7–2.0k (r = 0.90, the 1.0 expected of definition files), M6 at 3.56k against 4.3–4.9k
  (r = 0.64), M7 at 8.03k against 12.1–13.8k (r = 0.50) and M8 at 1.44k against 2.6–3.8k plus a
  0.8–1.5k adapter (r = 0.37 on the seven files ported). The cause is M3's: the vendored proofs
  restate long `leftTensor (ι₂ := ι) …` expressions in every step and prove Kronecker identities
  entrywise, and here those are `S.L`, `S.opTensor_mul`, `S.leftTensor_mul_leftTensor` and the
  keystone's positivity; the `Matrix.PosSemidef` self-adjointness arguments became
  `IsSelfAdjoint.of_nonneg`. `CommutativityPoints`, which measured r = 0.95, has none of that, so
  it was the wrong model for `Commutativity`. M8's estimate also assumed about ten files ported.
- **`MainInductionStep/Statements` departs from the per-file 2× rule of §4 item 3**, at 2.01×
  (5.08 s against 2.52 s, minimum of three runs; 5.08–5.28 s against 2.52–2.73 s over the rounds),
  or rather sits at its boundary: two later minimum-of-three measurements give 1.94× and 1.99×.
  It is a file of statement structures and their projections, without proofs, the case §5
  predicted: typeclass inference 1.03 s against 0.36 s and type checking 1.39 s against 0.42 s,
  spread over about thirty signatures on `K →L[ℂ] K` at 25–50 ms each, as in `Test/Defs` (2.97×).
  Writing `strategy.state.toVecState.X` in place of the `CoeOut` dot notation made no difference
  (4.71–4.90 s in a single-run comparison). M4 as a whole, three of whose four files are
  definitions, is at 1.51×.
- **M8 ports 7 of the 24 vendored files and drops 17** (7,398 vendored lines), each with its
  replacement, recorded in the module docstring of `Co/MakingMeasurementsProjective/Orthonormalization.lean`
  (the pairing script reads only ported files):
  - `Defs` (320) and `Orthonormalization/ErrorBounds` (142) get no Co file: their error functions
    are classical and imported, and the rest of `Defs` (`FiniteHilbertSpace`, `MatrixOperator`,
    `MatrixSubmeasurement`, the Naimark data) is matrix-only, consumed only by the not-ported
    `MatrixRealization`/`SdpMatrixBridge` and by M5's vendored imports of
    `ExpansionHypercubeGraph/{Defs/Core,Theorems/Foundations,Theorems/Matrix,Theorems/Results}`,
    whose matrix content M5 replaced by Gram positivity;
  - `NaimarkCore` (404), `QXPLayer/*` (six files, 2,478), `QXPLayerIdentities/*` (six files,
    3,140) and `SpectralTruncation/*` (two files, 914), the finite-dimensional orthonormalization
    (Naimark dilation, rank reduction, rectangular SVD, step-function functional calculus legal
    only on a finite spectrum), are replaced by T1: `povm_orthogonalization_finitePair` in the
    repair theorems, T5's `povm_orthogonalization_dyadicPair`/`…B` in the two heterogeneous
    lemmas, and M2's Theorem G for `orthonormalization`. No declaration of them is named outside
    the directory. The vendored `ProjectivizationChain/Basic` imports `ProjectorApprox`, so the Co
    file's classical import of it keeps that module in the import closure, prebuilt; no Co file
    names it. M10's `SelfImprovement/Defs` will import Co `Projectivization` and the vendored
    `Defs` in place of `NaimarkCore`.
  The adapter the estimate allowed for (0.8–1.5k) is Theorem G, done in M2, and two direct T5
  calls.
- **The repair theorems are re-proved from T1.** `LocalityPreservingRepair` keeps the vendored
  names of its four repair theorems and two `sddRel` bridges, proved through
  `povm_orthogonalization_finitePair` at `ε = 3 min(ζ, 1)`, with error
  `27 min(ζ, 1) ≤ 84 ζ^{1/4}` (`twentySeven_mul_min_le_orthonormalizationMainLemmaError`, new);
  its 17 reduced-density declarations (`diagBlock` … `leftMarginal_ev_eq` and the right
  counterparts) and the two used only by that route are not ported. Every T1-backed statement
  changes shape the same way: `ψ hψ` becomes `S hS hA` with `hS : S.toBipartite.IsFinitePair` and
  `hA : NoAbelianProj S.toBipartite.opsA`, and `0 ≤ ζ` becomes `0 < ζ`, because T1's hypothesis is
  strict; there is no large-`ζ` branch, `min ζ 1` covering every `ζ > 0`. The case `ζ = 0` is
  covered nowhere in M8: the in-core `orthonormalization` (vendored `SelfImprovementTop/Core:433`)
  needs `0 < selfImprovementHelperError`, which holds when `1 ≤ params.d` (M14), and M13's
  `SourceRoleRegister` errors contain `m·d/q`.
- **Two M8 lemmas are two-space**, as M2's surrogate is. The heterogeneous
  `orthonormalizationMeasurement_{,right_}of_consistency_from_projectivizationRepair_heterogeneous`
  are stated over `M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with `M.IsDyadicPair`, with M2's two-space
  `bipartiteConsError` as hypothesis and the T1 sum of norms `∑ ‖π(πA(Aₐ − Pₐ))ψ‖² ≤
  orthonormalizationError ζ` as conclusion, not an `SDDRel`; their consumer is M13
  (`SourceRoleRegister/Core:507,547`). Their Cauchy–Schwarz core is the new
  `one_sub_two_mul_le_sum_norm_sq_πA`/`_πB`.
- **M2's `optionCompletion` and `restrictSomeProjSubMeas` moved** from
  `Co/Doubling/Orthonormalization.lean` to their mirrored homes, `Co/MakingMeasurementsProjective/Statements.lean`
  and `Co/MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean`, byte for byte, with
  their fully qualified names unchanged; `Co/Doubling/Orthonormalization.lean` imports them
  (41 lines shorter), which makes no cycle. The ported `RestrictSome` does not import
  `Statements`, against the vendored file. `Orthonormalization/Completion` bounds the overlap of
  the totals by M2's step `∑ₐ b(Aₐ, Aₐ) ≤ b(T, T)` rather than
  `Preliminaries.qBipartiteSSCDefect_postprocess_le`.
- **Narrowed to one carrier**, by the rule of "Same-space and bipartite quantities" and as M3's
  heterogeneous triangle lemmas were: M4's `tensorFailureExpectation`, now `(S : SymModel 𝔓 K)
  (Z : 𝔓) (H : SubMeas Outcome 𝔓) : ℝ := S.ev (S.L Z * S.R (1 - H.total))`, every vendored use
  of which (`MainInductionStep/Theorems/{PastingAssembly,SelfImprovementAssembly,AvgSliceErrors}/…`)
  applies it to `strategy.state` of a `SymStrat`, so M12 calls it as `tensorFailureExpectation
  strategy.state Z H`; M4's `mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous`, now
  of the same type as its same-space sibling, whose vendored caller on the two-space `ProjStrat`
  (`Test/MainTheorem/SourceRoleRegister/Core.lean`) is left to M13 and M14; and M8's
  `Projectivization` lemmas, with `S` an explicit first argument.
- **Fields that became theorems.** `RestrictedSymStrat.isNormalized` (M4) is a theorem, listed
  under `Ported elsewhere`; `xRestrictedAnswerSymStrat` sets no `permInvState`, `densityFixed` or
  `isNormalized`, and `xRestrictedStrategy_isNormalized` and
  `xRestrictedAnswerSymStrat_isNormalized`, equalities of two proofs, lose `@[simp]`.
  `AnswerMainInductionHypothesis` carries the universe binder `.{u, v, w}` and quantifies over
  `𝔓 : Type v` and `K : Type w` with their instances, where the vendored one quantifies over a
  finite carrier `ι : Type v`, and only over strategies whose model is a finite pair without
  abelian projections in its first player's operators: `∀ strategy …,
  strategy.state.toBipartite.IsFinitePair → NoAbelianProj strategy.state.toBipartite.opsA →
  strategy.IsGood … → …`. These are the `hS hA` of M8's `orthonormalization`, which the
  successor step of the vendored `answerMainInduction` (`MainInductionStep/Theorems/MainTheorems/Successor.lean:50`)
  reaches through self-improvement (`SelfImprovementTop/Core.lean:433`); without them M12 could not
  prove the hypothesis, T1 supplying no orthonormalization in an arbitrary C*-algebra. They thread
  through the induction for free, restriction keeping the state (`xRestrictedAnswerSymStrat_state`
  and `xRestrictedStrategy_state` hold by `rfl`), so M10's `selfImprovement` statements and M11's
  and M12's induction-level theorems carry `hS hA` beside `ζ > 0`, and M13 discharges them for
  `D(M)` with M2's `Doubling.isFinitePair` and `Doubling.noAbelianProj_iff`. M12 instantiates it
  as `h 𝔓 K strategy … hS hA …`.
- **Dropped hypotheses.** `hnorm : strategy.state.IsNormalized` is dropped from the 45 M7
  lemmas, from M4's Step 5 theorems and from M8's `qSDD_*_zeroProjSubMeas_le_one`; `hperm`,
  `strategy.permInvState` and `strategy.densityFixed` from every lemma that had them (M7's
  `qBipartiteSSCDefect_eq_half_qSDD_of_proj` now takes `S P`; M8's
  `sddRel_liftRight_of_liftLeft_permInv` and `qSDD_liftRight_eq_liftLeft_of_permInv` take `S`
  first). The vendored uses became `S.ev_L_eq_ev_R`, `S.consRel_symm_of_density_fixed`,
  `Preliminaries.qSDDCore_rightTensor_eq_leftTensor_of_permInv S` and
  `S.ev_one_of_isNormalized`, and no ported statement carries a swap or normalization hypothesis.
- **Argument conventions**, M1's and M3's: placement lemmas and definitions that place without a
  strategy take `(S : SymModel 𝔓 K)` as an explicit first argument (M6's
  `weightedPolynomialOperator_pos`/`_le_one` and `rightPolynomialWeightSqrt_contraction`, M7's
  `leftOrderedProductOpFamily S`, `evaluatedPointFamilyLeft/Right S`, the normalization bounds,
  `evaluatedSlicePointSwapRightPrefix S`); single-state lemmas take `(V : VecState K)`, and M6's
  `ψbi` is a `VecState` in the same position, to which callers pass `strategy.state`; state-free
  ones are generic (`zeroFullSliceOpFamily`, `zeroEvaluatedSliceOpFamily` and M8's
  `zeroProjSubMeas`, written `(R := K →L[ℂ] K)` or `(R := 𝔓)` where the vendored text names
  `ι`; `singletonOpFamily`, `postprocess_proj_outcome`, `cfc_sqrt_outcome_le_one`).
- **M6: the weighted state is not ported**, as the M5 note prescribed. The vendored
  point-conditioned variances evaluate on `W ρ Wᴴ`, `W = 1 ⊗ √G_g`, which is not a unit vector
  state; here they are `ExpansionHypercubeGraph.localVariance`/`globalVariance` of the family
  `u ↦ S.L (A^u_{g(u)}) * S.R √G_g` on `strategy.state`. So `weightedPolynomialState` and
  `weightedPolynomialState_ev_leftTensor` are not ported,
  `weightedNormDeviation_eq_pointConditionedDifferenceAvg` holds by `rfl`, and
  `pointConditionedExpansionTransfer` is `localToGlobal`. `GlobalVariance/Defs/Core.lean` is a
  docstring and its imports, the vendored file being classical.
- **Proofs that take another route.** M6's `localVarianceDeviation_sum_le_localVarianceOfPointsError`
  (`TransportChain/SumForm`) runs the six-step chain through `Preliminaries.sddOpRel_chain` on a
  local operator family, as `TransportChain/Core` does, in place of the vendored pointwise
  telescoping (0.87 s against 2.50 s). M6's `pointConditionedEventSelfConsistency_weighted_point` is
  one summand of the sum form, so the two are declared in the reverse of the vendored order. M7's
  stability expansions share the new `stabilityDefect_ev_eq` (`Scaffold/Products`), which replaces a
  100-line calc the vendored file repeats; the four zero bounds of `Transport/FullSlice/ZeroBounds`
  and `Main/Auxiliary/HEvalTransport` share the new `sum_ev_adjoint_self_leftTensor_mul_le_one`;
  `ScalarApproximation/Core` proves the gap nonnegative as half of `qSDD` and imports Co
  `Preliminaries/BipartiteSelfConsistency/Core` for `ev_adjoint_self_leftTensor_sub_rightTensor`;
  `PaperChainBasic/Normalization` replaces the Kronecker calcs by six private theorems.
  M7's `fullSliceCommutation_of_evaluated_on_evaluated_questions` (`Main/EvaluatedQuestions`) takes
  13.1 s vendored, over the 5 s rule, and 2.55 s ported with `-DElab.async=false`: every `nlinarith`
  became an explicit product fact fed to `linarith only`. Its real arithmetic, about 1.9 s of that,
  is the separate `commDataProcessedGError_to_comMainError_arith`, so that neither half reaches 2 s.
- **New declarations**, each under `New here`: M6 `generalizeBLeftOutcome_base`; M7
  `sandwichByOuterSubMeas_sum_outcome`, `stabilityDefect_ev_eq`,
  `sum_ev_adjoint_self_leftTensor_mul_le_one` and `commDataProcessedGError_to_comMainError_arith`;
  M8 `twentySeven_mul_min_le_orthonormalizationMainLemmaError`, `one_sub_two_mul_le_sum_norm_sq_πA`
  and `_πB`. Two private helpers are duplicated across M7's
  `EvaluatedSliceCommutation/Averages` and `Transport/FullSlice/Averages` (`avg_sum_eq_of_swap`,
  `avg_pair_sum_eq_of_swap`), the first being private to its module.
- **Classical content imported from vendored modules**, listed as `classical, imported`: M4's
  `MainInductionStep/Defs` (10 declarations), M6's `GlobalVariance/Defs/{Core,Families}`,
  `Theorems/{Averaging,AlgebraicIdentity,CollisionExpansion,SelfConsistencyTransport/Utilities,TransportChain/Core}`,
  M7's `Commutativity/Defs/Core`, `Scaffold/Core`, `Transport/Pullback`,
  `Transport/FullSlice/Averages` and `Transport/FullSlice/Machinery/Marginalization/Core`, and M8's
  `Defs` (its error functions), `Projectivization`, `ProjectivizationChain/Basic`, `LocalityPreservingRepair` and
  `Orthonormalization/ErrorBounds`. Inside `MIPRE.LIDT.Co` the dotted name
  `MakingMeasurementsProjective.X` resolves to the Co namespace, so the vendored classical names
  of that directory are reached through explicit `open MIPStarRE.LDT.MakingMeasurementsProjective
  (…)` lists.
- **Pitfalls for later stages.** Several proofs exceeded 200000 heartbeats in a defeq check when
  an argument was left to unification and were instant once it was given: the distribution of an
  `avgOver_nonneg` inside a `rw` (`Marginalization/Y`), the binder type of `avgOver_uniform_snd`
  (`ClosenessXEval`), the operator of a closing `avgOver_congr` (`ScalarMarginalization`), and the
  outcome type of `qSDDCore_rightTensor_eq_leftTensor_of_permInv` against
  `orderedProductOpFamily`/`reversedProductOpFamily`, whose `fun | (a, b) =>` match has no
  `_outcome` lemma (`PaperChainBasic/PointSwap`); adding those two lemmas to
  `Co/CommutativityPoints/Defs` is a cleanup. A single `refine` with `le_of_eq_of_le
  (Finset.sum_congr …)` hit the limit in `SelfConsistencyTransportSum`, an explicit `have` and
  `calc` did not. In M4's `restrictDiagonalMeasurement_postprocess_zero`, `rw`/`simp` with
  `SubMeas.postprocess_comp` fails without the vendored `respectTransparency`, the instances for
  `Fq params.next` and `Fq params` not unifying at instance transparency; `refine
  (SubMeas.postprocess_comp _ _ _).trans …` works. No file sets `respectTransparency` or raises a
  heartbeat limit, the vendored file-wide options included.

**Departures in M10 and M11.**
- **Sizes.** M10 came to 11.41k lines against 13.1–15.1k (r = 0.67) and M11 to 17.58k against
  23.2–26.5k (r = 0.59), the cause being M3's and M7's: the vendored proofs restate placements in
  every step and prove Kronecker identities entrywise. Against the rates M6 and M7 measured, which
  put them at 8.4–10.5k and 15.2–19.0k, M11 is inside and M10 above, for two reasons: its headers
  (87 lines a file against 56 vendored; the module docstrings record the translation, the dropped
  files and the threaded hypotheses), and its definition and statement files, which port at about
  1.0 as M4's did (`Theorems/Statements` r = 1.02, with the adapter; `PointConsistencyLiteral`
  0.94, `SelfImprovementTop/FinalFields` 0.89). Both were ported in units of at most about 900
  vendored lines, in dependency order: 21 for M10 and 44 for M11.
- **`SelfImprovement/Theorems/Statements` departs from the per-file 2× rule of §4 item 3**, at 2.19×
  (3.48 s against 1.59 s, minimum of three runs; 3.48–3.75 s against 1.59–2.00 s over the rounds).
  It is a file of statement structures and definitions with almost no proofs, the case of
  `MainInductionStep/Statements` (2.01×) and `Test/Defs` (2.97×): typeclass inference 1.34 s
  against 0.30 s, spread over about thirty signatures on `K →L[ℂ] K` and `𝔓` at 0.08–0.19 s each
  (`SelfImprovementConclusion` and `SelfImprovementFinalFields` the largest), with M10's adapter,
  `of_isSummedSdp` and `isSummedSdp`, about 0.2 s of new content that has no vendored cost. M10 as
  a whole is at 0.78×.
- **M10 drops 8 vendored files, 3,980 lines, and replaces them by M9.** `MatrixRealization/` (7
  files, 3,667 lines: the canonical block semidefinite program, Slater strong duality and the
  saturation of the slack block) and `Theorems/Results/SdpMatrixBridge` (313 lines, the bridge to
  `SdpStatementWithSlackness`, the only importer of `MatrixRealization/Canonical/{Saturated,
  StrongDuality/Separation}`, and itself imported only by `HelperCompleteness/Bracketed`) are
  replaced by M9's summed form through a two-part adapter of about 40 lines:
  `SdpStatementWithSlackness.of_isSummedSdp` (Co `Theorems/Statements`, with its converse
  `SdpOptimalPairWithSlackness.isSummedSdp`) and `sdp_statement_with_slackness params strategy hS`
  (Co `HelperCompleteness/Bracketed`), which applies `Doubling.exists_isSummedSdp_A hS` to the
  averaged point operators `A_g = E_u A^u_{g(u)}`. The consumers use exactly the three fields
  `primalTotalOperator`, `dualFeasible` and `complementarySlackness`, per `g` (report §5.2,
  Lemma 0), so the vendored structures keep their fields and the two base uses of slackness are
  ported unchanged: (a) in `HelperCompleteness/InputSdp`, with `Z` on the left factor, and (c) in
  `HelperSSC/Assembly`, with `Z` on the right. The pairing script reads only ported files, so the
  dropped files and their declarations are recorded in the module docstring of Co `Bracketed`.
  `Theorems/Thresholds/{Helper,Final}` (1,210 lines) are wholly classical and imported with no Co
  file, as M3 imports `Polynomials.lean`, recorded in Co `SelfImprovement/Defs`.
- **`NaimarkCore`, which M8 dropped, is replaced as an import of `SelfImprovement/Defs`** by Co
  `MakingMeasurementsProjective/Projectivization` (the `ProjSubMeas` API and `zeroProjSubMeas`),
  which brings the vendored `MakingMeasurementsProjective/Defs` through Co `Statements`; no
  `NaimarkCore` declaration is named in `SelfImprovement` outside `MatrixRealization`. Of the
  ported files' own declarations only `sdpPrimalObjective`, the real part of a matrix trace, is
  not ported: the model has no trace and nothing consumes it. "Dropped" and "replaced" here and
  for `SdpMatrixBridge` and `MatrixRealization/` mean that no Co declaration uses these files, which
  a constant-closure walk over the built oleans confirms (no constant of these eight modules or of
  the vendored `Bracketed` under `Co.SelfImprovement.selfImprovement` or `Co.Pasting.ldPasting`,
  2026-10-02); all eight stay in the build's
  import closure through the classical imports: `NaimarkCore` by Co `SelfImprovement/Defs` →
  vendored `SelfImprovement/Defs` → `MakingMeasurementsProjective/NaimarkCore`, and `SdpMatrixBridge`
  with the seven `MatrixRealization` modules by Co `AddInUStep34AndTransfer/{Factored,Selected,
  Transfer,Variance}`, `AddInUPointConsistency` and `HelperSSC/Core`, each of which imports its
  vendored counterpart for classical lemmas, each of which reaches vendored
  `AddInUStep34AndTransfer/Factored` → vendored `HelperCompleteness/Bracketed` → `SdpMatrixBridge`
  → `MatrixRealization/Canonical/Saturated` → … → `MatrixRealization/Base`. A later cleanup can
  take them out of the closure by moving the classical declarations those imports serve
  (`addInU_le_sqrt_of_factor_bounds_*` and `addInU_weighted_cauchy_schwarz` of vendored `Factored`,
  `pointConsistencyAddInUSelection` of `AddInUPointConsistency`,
  `helperOffDiagonalVarianceSwapSelection` of `HelperSSC/Core`, the definitions of
  `SelfImprovement/Defs`, …) into modules that import neither `Bracketed` nor `NaimarkCore`.
- **The in-core orthonormalization, and three threaded hypotheses.** The vendored
  `MakingMeasurementsProjective.orthonormalization ψ permInvState isNormalized`
  (`SelfImprovementTop/Core.lean:433–436`, finite-dimensional, at any `ζ ≥ 0`) is M8's Theorem G,
  `MakingMeasurementsProjective.orthonormalization S hS hA Hhat ζ hζ`, at `ζ =
  selfImprovementHelperError params eps delta`, which is positive by the new
  `selfImprovementHelperError_pos` when `hd : 1 ≤ params.d`. So `selfImprovement` and
  `selfImprovement_of_axisParallel_selfConsistency` take `hS hA hd` right after `strategy`, as M8
  places `hS hA` right after `S`; `self_improvement_helper_with_slackness`,
  `selfImprovementHelper`, `sdp_statement_with_slackness` and `sdp_slackness_measurement` take
  `hS` alone, Theorem 10 needing the faithful trace of a finite pair and no orthonormalization.
  Only the main branch (`eps ≤ 1`, `delta ≤ 1`, `d ≤ q`) of `selfImprovement` uses `hd`; the
  large-error branches are the vendored ones. Nothing else in M10, and nothing in M11, takes a new
  hypothesis: pasting neither orthonormalizes nor solves a semidefinite program, so, against the
  expectation recorded under M4's departures, M11's statements carry neither `hS hA` nor `hd`. This
  settles M2's and M8's open point, `ζ > 0` at the in-core call site, up to threading: M4's
  `AnswerMainInductionHypothesis` carries `hS hA` but not `1 ≤ params.d`, so M12 threads `hd` as a
  hypothesis on `params` (constant along the induction, which changes only `m`), M14 supplies it
  from `SoundIn`, and M13 discharges `hS hA` for `D(M)`. The case `ζ = 0` is neither proved nor
  needed.
- **Swap and normalization uses.** All of them map to a keystone lemma or to an M3/M8 lemma that
  has already dropped the hypothesis: in M10, 21 `permInvState`/`swap_ev` sites, one
  `densityFixed` and about 30 `isNormalized`; in M11, the 17 vendored `permInvState`, `swap_ev`
  and `densityFixed` sites (in `GHatFacts`, `Bernoulli/{Final,DegreeZero}`,
  `CommutingWithG/Complete`, `SwitcherooCompletion`, `ComparisonLemmas/HAConsistency` and
  `Core/LdGbcon`) and the normalization
  arguments of `bipartiteConsError_uniform_le_one`, `bipartiteSSCError_uniform_le_one`,
  `triangleSub_right` and `consRel_symm_of_density_fixed`. The residual mass of `HAConsistency`
  and `DegreeZero`, a vendored entrywise Kronecker `ext` proof, is one rewrite with
  `S.ev_L_eq_ev_R`. `hnorm` is dropped from `chernoffBernoulliMatrix` (which takes a `V : VecState
  K` and `X : K →L[ℂ] K`, the matrix Chernoff estimate being a continuous-functional-calculus lift
  of the scalar Hoeffding bound with no dimension factor), from `fromHToG_ofGHatFactsAndHalfSandwich`
  and `fromHToG_ofGHatFacts`, and from the telescope they feed. No ported statement of either
  stage carries a swap, density or normalization hypothesis.
- **Narrowed to one carrier, or given the model**, by the rule of "Same-space and bipartite
  quantities": M11's `qBipartiteLinearConsDefect` and its three lemmas (`LdSandwichLineOnePoint/
  CSSetup`), the three bipartite lemmas of `LineInterpolation/Averaging`, the three bipartite
  helpers of `LineInterpolation/BadMass`, `subMeasMass_restrict_add_not`
  (`OverAllOutcomes/NonglobalDecomposition`) and `avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff`
  (`OverAllOutcomes/Final`) take `(S : SymModel 𝔓 K)` in the vendored `ψ` position, with
  local submeasurements; M10's `addInU_selected_filtered_tensor_sum_le_one` and
  `addInU_selected_sandwich_tensor_if_sum_le` (`AddInUStep34AndTransfer/Selected`), whose vendored
  statements name no state, take the model first, as `ψ` (`S` is the selection there). The
  families that place without a strategy take `S` as their first explicit argument: the sixteen
  of `Sandwich/Switcheroo`, the switcheroo and completion families, `fromHToGTailStageFamily`,
  the four adjoint and raw families of `CSSetup` with `ldSandwichLineOnePointCS_Aord`/`_Arot`,
  and M10's `helperUpperOperator S params Z` and `projectiveResidualOperator S params H Z`.
- **State-free declarations are generic**: `gHatTypeOperator` and `truncatedTypeSums` (`[Ring
  R]`), `bernoulliTailOperator` (`[Algebra ℂ R]`), `multiplyByTotalOn{Right,Left}`, the ring
  identities of `Bernoulli/TruncatedSums`, the two functional-calculus identities of
  `Bernoulli/MatrixChernoff` (any C*-algebra), `postprocessMeasurement` (`EndpointEquivs`), the two
  lemmas of `LineInterpolation/BadLine` and four of `BadMass`, so that they serve `𝔓` and
  `K →L[ℂ] K` alike; `bernoulliTailOperator_leftTensor` moves the Bernoulli tail through `S.L`.
- **New declarations.** M10 has six, each under `New here`: `selfImprovementHelperError_pos`,
  `SdpStatementWithSlackness.of_isSummedSdp` and `SdpOptimalPairWithSlackness.isSummedSdp` (the
  adapter), and `addInU_sum_projection_sandwich_le_one`, `addInU_sum_fiber_collapse` and
  `addInU_selected_sum_fiber_collapse`, steps the vendored `AddInUStep12` proofs repeat inline. M11
  has none that the script counts, but `LineInterpolation/BadMass` adds two scoped instances,
  `instDecidableEqFqFqNext` and `instDecidableEqFqNextFq` (priority low, each
  `instDecidableEqFin _ x y`), deciding the comparisons between `Fq params` and `Fq params.next`
  that the vendored files decide through their file-wide `respectTransparency`;
  `OverAllOutcomes/NonglobalDecomposition` gets them by importing `BadMass`, and their natural home
  is an earlier shared `Pasting` file, a cleanup. Private theorems: 9 in M10 and 7 in M11, among
  them the split of long proofs for elaboration time: `selfImprovement` into
  `selfImprovement_main`, `selfImprovement_totalDifference` and `helper_pointTransfer` (the last
  shared with `selfImprovementHelper`), and `fromHToGAdjacentStage_paperMoveChain`
  (`PaperMoveChain/Telescope`; 11.6 s vendored, over the 5 s rule, and 3.6 s ported before the
  split) into `fromHToGAdjacentStage_moveA0M1` and `_moveM1M2`.
- **Pitfalls for later stages.** Where `Fq params` and `Fq params.next` meet, `rw` fails with
  "motive is not type correct" or "target not type-correct at implicit transparency" without the
  vendored `respectTransparency`; write the step as an `Eq.trans`/`congrArg` term (`BadMass`,
  `DegreeZero`). `Preliminaries.sddRel_symm` needs its state as `strategy.state.toVecState` and
  both lifted families explicit (`HAConsistency`, `DegreeZero`); through the `CoeOut` the families
  stay metavariables. `fun_prop` on the continuity side conditions of the functional calculus took
  4–6.6 s a declaration in `MatrixChernoff`; explicit terms (`continuous_pow`,
  `continuous_finsetSum`, `.continuousOn`) take a fraction of it. None of the 106 files sets an
  option or raises a heartbeat limit, while every one of their vendored counterparts sets the
  file-wide `respectTransparency false`.

**Departures in M12, M13 and M14.**

M12, the main induction:
- **`hS hA hd` threading.** The successor step of the induction is where M10's self-improvement
  (its semidefinite program and M8's rounding) is called, and M4's `AnswerMainInductionHypothesis`
  quantifies only over symmetric models whose bipartite reading is a finite pair without abelian
  projections. So `hS : strategy.state.toBipartite.IsFinitePair`,
  `hA : NoAbelianProj strategy.state.toBipartite.opsA` and `hd : 1 ≤ params.d`, placed right after
  `strategy` as M10 places them, go on exactly the declarations that reach those calls:
  - `SelfImprovementAssembly/Core`: `selfImprovementInInductionSection`, its
    `_of_axisParallel_selfConsistency` form, `SelfImprovementData.slice_outputs_ofSliceStrategyTransport`
    and `SelfImprovementData.ofSliceStrategyTransport` (`hS hA hd`);
  - `SelfImprovementAssembly/AnswerSlice`: `AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport`,
    `.slice_outputs_ofAnswerCarrier`, `.ofSliceStrategyTransport` and `.ofAnswerCarrier` (`hS hA hd`);
  - `RestrictedProbabilities/AnswerValued`: `answerSuccessorRestrictedSliceConclusions` (`hS hA`,
    since it applies the hypothesis rather than proving it);
  - `StageDataConstructors`: `AnswerPerSliceInductionData.ofMainInductionHypothesis` (`hS hA`);
  - `AvgSliceErrors/Successor`: `answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis`
    (`hS hA`) and `answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis` (`hS hA hd`);
  - `PastingAssembly/AnswerFields`: `answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis`,
    and `PastingAssembly/Successor`:
    `answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting` (`hS hA hd`);
  - `MainTheorems/Successor`: `answerMainInduction` takes `hd` after the field model, `hS hA` coming
    from the hypothesis's own binder, and `mainInductionSuccessorNext_ofAnswerCarrier`, its
    `FromSuccessorBound` and `ofSmallErrorConstruction` forms, `mainInductionSuccessorNext`,
    `mainInductionSuccessor` and `mainInduction` take `hS hA hd`.

  A slice restriction keeps the model (`SliceStrategyTransport.state_eq`, or the carrier's state by
  definition), so `hS hA` pass to each slice unchanged or as `hstate ▸ hS`; `hd` is constant along
  the induction, since `Parameters.next` keeps `d`. `SliceStrategyTransport` keeps its five vendored
  fields. The base case, the large-error branches, restriction, pasting and the parameter bounds
  take none of the three.
- **Swap and normalization uses replaced (4); no hypothesis dropped**, since no vendored statement of
  M12 has one. `strongSelfConsistency_of_sddRel` used `strategy.permInvState`; it is M7's
  `Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj`. The boundedness field of
  `idxPolyFamily_sliceBoundednessInput_of_slice_bounds` used `ev_opTensor_swap_of_density_fixed`;
  it is `ev_L_mul_R_comm`. `answerComMainForCarrier_ofAnswerGood` passed `carrier.isNormalized`,
  which Co `comMain_of_commutativityPoints` does not take, and the base case's
  `bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized` is the model's
  `bipartiteConsError_uniform_le_one`. `answerSelfImprovementCarrier` and
  `xRestrictedAnswerSymStratOfAnswer` no longer set `permInvState`, `densityFixed` or
  `isNormalized`, which are theorems of the model; `xRestrictedAnswerSymStratOfAnswer_isNormalized`
  is kept, by `rfl`, without `@[simp]`, as M4's `xRestrictedAnswerSymStrat_isNormalized` is.
- **`dummyDiagonalCovariantMeasurement` is generic.** It is state-free, so its carrier argument
  `(ι : Type uι)` becomes any star-ordered ring `R`; it is called at `𝔓`.
- **One new public theorem**, `ldPastingInInductionError_le_of_averaged_bounds`
  (`PastingAssembly/Successor`): the scalar absorption that the vendored
  `assembleAveragedPastingData` and `mainInductionFromAnswerStageDataOfSmallErrorDirect` each prove
  by `nlinarith`, here once, by `linarith`. It cannot be private: the exposed definition
  `assembleAveragedPastingData` uses it. Nine private theorems (`port-pairing.py`) factor the
  vendored files' repeated scalar estimates and the base case written out twice.
- **Classical content imported.** 25 of the 194 vendored declarations are classical and imported,
  each listed as such. `InductionParameterBounds/{Preliminaries,Averaging}` are a docstring and
  imports, their vendored files being classical throughout; `InductionParameterBounds/{MainError,
  SelfImprovement}`, `AvgSliceErrors/Core`, `PastingAssembly/{Basic,ErrorBounds}` and
  `RestrictedProbabilities/Base` import their vendored module for its classical lemmas (M3's
  convention), which adds no operator content, and `MainTheorems/Base` imports the classical
  `Basic/LinePolynomialEmbedding`. These names live in `MIPStarRE.LDT.MainInductionStep`; inside
  `MIPRE.LIDT.Co` the dotted `MainInductionStep.X` resolves to the Co namespace, so they are reached
  through explicit `open` lists. A pitfall from `AvgSliceErrors`: state an `rpow` fact with
  `Real.rpow`, since `linarith` treats `Real.rpow x c` and `x ^ c` as different atoms.
- **Universes.** The vendored separate carriers `ι'` of the stage records are dropped for `𝔓` and
  `K`, their explicit universe instantiations left to unification; the induction hypothesis is
  `AnswerMainInductionHypothesis.{uF, uP, uK}` for the vendored `.{uF, uι}`, and
  `answerMainInduction.{uF, vP, vK}` proves it in any universes. Where the vendored file binds
  `.{uF}` (or `.{uι', uF}`) on a declaration, the port keeps a `.{uF}` binder, which
  `port-pairing.py` needs to pair the name.
- **Elaboration.** `MainTheorems/Successor` departs from the 2× rule, at 2.28× (2.63 s against
  1.15 s, minimum of three runs; "Port conventions"): typeclass inference on the signatures of the
  successor step, which carry `hS hA hd` and the stage records over `𝔓` and `K →L[ℂ] K`, as in the
  statement files of M4 and M10. A shortcut instance `Algebra ℂ (K →L[ℂ] K)`, tried in a scratch copy
  (`local instance … := ContinuousLinearMap.algebra`), saves only 0.1–0.4 s of the 1.0–1.4 s of
  typeclass inference and leaves the file at about 1.8–2.3×: most of that inference is the
  signatures over `𝔓` and `K →L[ℂ] K` carrying `hS hA hd`, of which `Algebra ℂ (K →L[ℂ] K)`
  (six syntheses, 0.66 s, with `MulAction ℂ K` nested in it) is only a part. The instance is not
  added, since the gain is within the variation between runs. None of the 20 files sets an option, while every
  vendored file of M12 sets the file-wide `respectTransparency false`.

M13 and M14:
- **The tail is two-space, over `M`; `D(M)` serves three steps only.** §3 planned `Co.mainFormal`
  over a symmetric model, restated afterwards over a dyadic pair through the doubling. It is
  instead stated once, over the port's two-space strategy `ProjStrat params 𝒞 𝒜 ℬ` whose state is
  the dyadic pair `M` itself, as the vendored theorem is over `ιA × ιB`. The doubled model
  `D(M)` (M2) appears inside the proof in three places: the main induction (M12's `mainInduction`
  on `Doubling.symmStrat`, `(3ε, 3ε, 3ε)`-good by Theorem D), Theorem E, and the step from points
  to whole polynomials (Step 5). The reason is the role average: `D(M)` gives only
  `bc_D(X, Y) = ½ (bc_M(X¹, Y²) + bc_M(Y¹, X²))`, so pulling a one-sided relation back from `D(M)`
  costs a factor two, which would break the vendored scalar cascade into `mainFormalError`. So the
  vendored `SourceRoleRegister/*` and `MainFormal` run on `M`, through the new two-space calculus
  `Co/Test/MainTheorem/TwoSpace.lean`. It holds the placements `placeA M = π ∘ πA`,
  `placeB M = π ∘ πB` into `B(M.H)`, the vector state `vecState M hψ`, and the two-space forms of the
  heterogeneous `Preliminaries` lemmas that M3 had narrowed to one carrier. The vendored `ConsRel ψ`
  becomes M2's `bipartiteConsError M ≤ δ`, and `SDDRel` is read on `TwoSpace.vecState`; no two-space
  `ConsRel` structure is defined. The two `_heterogeneous` theorems of
  `ProjectiveConsistency/Evaluation` are two-space for the same reason, as M8's heterogeneous
  orthonormalizations were.
- **Theorem E and the diagonal Step 5.** `Co/Doubling/Unsymmetrization.lean` replaces the vendored
  `Test/StrategyBiProjUnsymmetrization` (the role-register extractions, principal blocks and
  matrix-trace lemmas). It defines the components `measA`, `measB` of a measurement of the doubled
  local algebra `Loc M` and the pairing `pairMeasurement`. Theorem E
  (`symmStrat_pointConsistency_unsymmetrize`) says that `σ`-consistency of the paired points with
  `G` in `D(M)` gives `2σ`-consistency of each player's points with the other component of `G` in
  `M`, the vendored constants, by M2's `bipartiteConsError_components_le_two_mul`. Step 5 runs in
  `D(M)` on the pairing of the two polynomial measurements. The diagonal identity
  `bipartiteConsError_model_diag` (the defect of a family with itself in `D(M)` is the two-space
  defect of its components, exactly) makes this lossless, so M4's
  `mainFormalStep5_selfConsistency_ofExpansionBound` adds `md/q` with no factor two, and M4's
  heterogeneous Step 5 lemma needs no two-space caller.
- **Completion is transported along `equivA`.** Co `Preliminaries.completeAtOutcomeProj` and
  `ProjMeas.isPVMIn` need a C⋆-algebra, but the players' algebras of a model are only star-ordered
  `⋆`-rings. In a finite pair each is `⋆`-isomorphic to a commutant, which is a C⋆-algebra
  (`IsFinitePair.equivA`, `equivB`, `Foundations/FinitePairOrder.lean`). So
  `TwoSpace.completeAtOutcomeProjA`/`B` complete there and come back along the inverse, and
  `ProjMeas.isPVMIn_of_isFinitePair` (and its `B` form) transports projectivity the same way.
  Positivity transfers along any `⋆`-homomorphism of star-ordered rings, and projectivity and the
  total are algebraic, so the order agreement of a finite pair is not used. The lemmas that
  complete take `hM : M.IsFinitePair`. In M14, `Co/Bridge/Measurement` coarse-grains in the same
  setting through `IsPVMIn.coarse` (`postprocessMeas`), which is `ProjMeas.postprocess` by `rfl` in
  a C⋆-algebra.
- **`hd` threading.** `1 ≤ params.d` makes the in-core orthonormalization error positive (M10).
  - **M12** threads it beside `hS hA` through the successor step of the induction. It is a
    hypothesis on `params`, constant along the induction, since `Parameters.next` keeps `d`. The
    base case and the large-error branches take none of the three.
  - **M13**: `mainFormal` and its tail take `hM : strategy.state.IsDyadicPair` and `hd`. The
    induction's `hS hA` are `Doubling.isFinitePair` and
    `Doubling.noAbelianProj_opsA_of_isDyadicPair`, which discharges them for `D(M)` as M4–M12
    required. `hd` has one further use: `ζ₁ > 0` for the two-space orthonormalizations
    (`zeta₁_pos`, since `md/q > 0`), which replaces the vendored derivation of `0 ≤ ζ₁`.
    `mainFormal_trivial_witness` takes neither.
  - **M14**: `Co.Chain.SoundLidtIn M` is the canonical-line theorem with `1 ≤ d` added, and
    `Co.Bridge.soundness` takes `hM` and `hd`. `soundIn_of_soundLidtIn` takes `1 ≤ d` (and `ε ≥ 0`)
    from `SoundIn`'s own hypotheses. So neither `SoundIn` nor `SoundFin` changes, and the case
    `ζ = 0` of Theorem G stays unproved and unneeded.
- **The measurements of the model chain** are single `POVMIn`s with `IsPVMIn` stated separately,
  where the matrix bridge returns `ProjectiveMeasurement Unit`, and the error is `M.inconsistency`.
  `Co.Bridge.inconsistency_eq_bipartiteConsError` takes `hψ : ‖M.ψ‖ = 1` in place of the matrix
  argument `S : TensorProductStrategy`, which it used only for its state. The model chain is new
  code, the model forms of the repository's own matrix files (`LIDT/Bridge/*`, the operator halves
  of `LIDT/{Adapter/Reduction,Padding,Extraction,Simultaneous}`). Those files stay, because they
  prove `soundIn_tensor`, and their classical halves are imported through explicit `open` lists.
  `Co.Chain.soundLidtIn_tensor` checks `SoundLidtIn` against the matrix theorem. Its composition
  with `soundIn_of_soundLidtIn`, which would re-derive `soundIn_tensor`, is not stated.
- **Hypotheses added in M13 beyond `hd`.** `hM` comes right after `strategy`: as
  `strategy.state.IsDyadicPair` where the main induction or the two-space orthonormalization is
  called, and as `IsFinitePair` for Theorem E's wrapper, the full-polynomial self-consistency and
  the completions. The two orthonormalization theorems of `SourceRoleRegister/Core` take
  `hζ : 0 < ζ` right after `ζ`, in place of the vendored derivation of `0 ≤ ζ`, because M8's
  two-space orthonormalization asks for `ζ > 0`. `qBipartiteMatchMass_le_left_total_of_measurement_heterogeneous`
  and its right form take `hψ`, because their conclusion is read on `TwoSpace.vecState`.
  `mainFormal_trivial_witness` takes neither `hM` nor `hd`. `TwoSpace.consRel_of_matchGap` takes its
  families in the order `A A' B B'` (Co's is `A B A' B'`). `SourceRoleRegister/Completion` does not
  import `Core`, which it does not use, so `Final` imports both.
- **New declarations.** Beyond the two new files (`TwoSpace`, `Unsymmetrization`, every declaration
  listed under "New here"): `ProjStrat.bipartiteConsError_constFamily_unit` (the two-space
  `constFamily_sdd_unit`), and the readouts `Test.mainFormal_isPVMIn` and
  `Test.mainFormal_inconsistency`, which state `mainFormal` with `IsPVMIn` and `M.inconsistency` for
  M14; `ProjMeas.isPVMIn_of_isFinitePair` and its `B` form live at the root of `MIPRE.LIDT.Co` so
  that dot notation works. Three private theorems. In M14, `Co.Bridge.postprocessMeas` coarse-grains
  a projective family through `IsPVMIn.coarse`, because Co `ProjMeas.postprocess` asks for a
  C⋆-algebra; `ofProjMeas_isPVMIn`, `soundLidtIn_of_isDyadicPair`, `Co.Chain.inconsistency_uniform_comp`,
  `constPM`/`constPM_isPVMIn` (the field the matrix `ProjectiveMeasurement` carried) and
  `soundLidtIn_tensor`, the check of `SoundLidtIn` against the matrix theorem, are new.
- **Statements relaxed in M14**, each from a hypothesis the model proof does not use:
  `Co.Chain.inconsistency_map_le` drops `∑ μ = 1`; `clSoundness_ldc_one` has no `hε` (only its
  `_deltaCL` form does, as in the matrix file); `extracted_conclusions` takes the extracted
  measurements as plain `POVMIn`s, projectivity being the separate `extractPM_isPVMIn`.
- **The rename.** The conditional `MIPRE.mipco_eq_core (hco : gapCompression.Sound .commuting)` is
  now `mipco_eq_core_of_compression` (blueprint `thm:mipco-eq-core`, its guard renamed in
  `MIPRE/Axioms.lean`). The name `MIPRE.mipco_eq_core` is the unconditional theorem
  `mipco_eq_core_of_lidtFin LIDT.Simul.soundFin` (`thm:mipco-eq-core-unconditional`). The mentions
  in `planning/mipco-track.md` and `planning/formalization-plan.md` say so; `reports/` is left as
  written.
- **`SoundFin` has a module of its own**, `Co/SoundFin.lean`, because the consumers of the
  hypothesis import `LIDT/FinModel.lean` and do not need the port. `MIPRE/MIPCo.lean` imports it.
  This creates no cycle, since nothing under `Co/` imports `MIPCo`.
- **Elaboration.** Every file of M13 and M14 is within the 2× rule (largest `SourceRoleRegister/Core`
  at 1.66×; "Port conventions"), and the one departure of the three milestones is M12's
  `MainTheorems/Successor` (2.28×). None of the 39 files sets an option or raises a heartbeat limit,
  although every vendored file of M12 and M13 sets the file-wide `respectTransparency false`.

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
