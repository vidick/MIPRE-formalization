# C6b: the low-individual-degree test in II₁ finite pairs

Tracking: #259, and the C6 row of `planning/mipco-track.md` (Phase 6). Written 2026-10-01, after the
maintainer chose the II₁ orthonormalization tier, from a design round of six parts: four
surveys of the code and four paper proofs, each proof checked by three independent skeptics and
revised, most of the new steps prototyped in Lean. The proofs are recorded in
`reports/c6b-paper-proofs.md`; the audit that sized the port is `reports/lidt-co-audit.md`.

**Status (2026-10-01).** The orthonormalization tier is complete (T1–T5 below). De la Salle's
Theorem 1.2 holds unconditionally in every von Neumann algebra with no nonzero abelian projection
and a faithful tracial vector functional (T1), and in both algebras of every dyadic pair, a class
that excludes abelian projections by a trace estimate (T2;
`Orthonormalization.povm_orthogonalization_dyadicPair`, `…B`). `SoundFin` asks only for dyadic
pairs, and `ω_co` is approached in them through an amplification by the twisted Pauli algebra
(T3–T5), so `mipco_eq_core_of_lidtFin` holds with the narrowed hypothesis. The port (M0–M14) is
open.

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

| WP | content | depends | vendored → ported |
|---|---|---|---|
| M0 | base layer: the symmetric model `SymModel 𝔓 K` (unbundled; local C*-algebra `𝔓`, Hilbert space `K` a parameter, state `Ψ`, flip `J`), `ev = Op.qform`, the three swap facts as lemmas, generic `SubMeas`/`Measurement`/`ProjMeas`, placements as `map` along ∗-homs, the ev-level defects and relations, the `Preliminaries` slice CP needs, `SymStrat`, and the operator-valued `averageOperatorOverDistribution` | — | 6.06k → 4.0–4.6k, plus 0.4–0.7k for the operator averages |
| M1 | prototype: `CommutativityPoints` → `Co.CommutativityPoints.commutativityPoints`, with a swap probe (CP never uses the flip) | M0 | 3.46k → 1.9–2.7k |
| M2 | the doubling: `D(M)` as a symmetric model and as a finite pair, no abelian projections in it, the role-average identity, the symmetric strategy, unsymmetrization at the vendored cut, orthonormalization in `D(M)` | M0, T1, T2 | new 0.95–1.45k; replaces about 3.96k vendored lines |
| M3 | the rest of `Preliminaries` | M0 | 7.64k → 6.0–7.0k |
| M4 | `Test` core and `MainInductionStep` definitions and statements | M0, M3 | 1.92k → 1.5–1.8k |
| M5 | `ExpansionHypercubeGraph`: the scalar part by import; `localToGlobal` by Gram positivity in place of its matrix realization | M0 | 3.8k → 1.0–1.6k |
| M6 | `GlobalVariance` | M0, M3, M5 | 5.3k → 4.2–4.8k |
| M7 | `Commutativity` | M1, M3 | 13.4k → 10.5–12.5k |
| M8 | `MakingMeasurementsProjective`: the dimension-free part, with the three orthonormalization sites calling T1 | M0, M3, T1 | ≈ 4.1k → 3.3–3.8k + adapter 0.8–1.5k; about 2.5k further lines unassigned by the audit's partition |
| M9 | the summed semidefinite form: a maximizer by weak-operator compactness, first-order conditions giving `Z = Σ T_g A_g ≥ A_g`, solved componentwise in the doubled model; `MatrixRealization` and `SdpMatrixBridge` (3.98k) are not ported | M0, M2 | new 0.55–0.75k (core measured) + adapter 0.1–0.25k |
| M10 | `SelfImprovement` theorems and definitions | M3–M6, M8, M9 | 16.75k → 13–15.5k |
| M11 | `Pasting` | M1, M3, M4, M7 | 30.3k → 24–28k |
| M12 | `MainInductionStep` theorems | M7, M10, M11 | 8.9k → 6.5–8.5k |
| M13 | `Test/MainTheorem` → `Co.mainFormal` over a symmetric model, then over a dyadic pair through the doubling | M2, M8, M12 | 5.06k → 2.5–3.5k |
| M14 | the error cascade into `deltaSim` and the adapters to `SoundIn`: `SoundIn M` for every dyadic pair `M`, hence `SoundFin` | M13, T5 | 1.5–3.5k |

Totals: the port about 82–105k new lines, consistent with the audit's 70–120k; the tier is done,
about 3.0k lines committed (T1 1.25k, T2–T5 1.75k), within the 2.4–3.7k estimated. The audit put the summed semidefinite form at 0.5–4k; the
measured core puts it at 0.55–0.75k plus the adapter, because full weak-operator compactness of
norm balls is already vendored (`MvN/WOTCompact.lean:114`).

## 4. Order

1. **This pull request**: the plan, the paper proofs, and T1, with its blueprint nodes.
2. **The rest of the tier** (T2–T5), done: the class, the amplification, the algebra `B` and
   the restatement of C6a, with their blueprint nodes. `mipco_eq_core_of_lidtFin` now holds with
   `SoundFin` narrowed to dyadic pairs, and Theorem 1.2 is unconditional in that class.
3. **M0 and M1, the measured prototype.** Acceptance: non-import elaboration of each ported file at
   most twice the vendored file's, no declaration over 5 s, no raised heartbeat limit, measured
   as the minimum of three runs over all profiler categories (simp included). The line ratio and
   the elaboration time measured here replace the extrapolated sizes of §3 before M3 starts.
4. **M2 and M9**, independent of M1 and of each other.
5. Then M3 → M4, M5 → M6, M7, M8 → M10, M11 → M12 → M13 → M14, as the dependency column allows.

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
  textually; the probe ratios were 0.25–0.65 on the base layer and about 0.9 on bridge proofs.

**Not settled.**
- **The vendored classical layer is not purely classical.** `Distribution.lean` imports
  `Quantum.FiniteMatrix` and defines the operator average used by every downstream directory, so
  the matrix layer stays in every port file's import closure and name collisions between ported
  and vendored declarations are certain: explicit `open … (…)` lists are mandatory, and the
  operator average must be ported (counted in M0).
- **`ζ = 0`** in the doubling's orthonormalization step needs `1 ≤ d` threaded from `SoundIn` to the
  core's parameters (report §4).
- **The semidefinite witness `Z`** must lie in the doubled local algebra; the componentwise
  solution needs the `A_g` to be componentwise (report §5).
- **Elaboration time** is the main risk of the port: operator positivity on `K →L[ℂ] K` costs
  1–3 s per proof against 0.6 s for the matrix version, roughly doubling under the whole-Mathlib
  imports the vendored classical layer forces. Positivity lemmas go in a base file without those
  imports.
- **The answer-valued duplication in `CommutativityPoints`**: a faithful port doubles that work;
  one proof generic over the diagonal answer type saves about 1k lines but diverges from upstream.
  To be decided by the M1 measurement.
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
  applied with dot notation, `S.leftTensor_mul_leftTensor`, stated with `S.L`. The namespaces
  `QuantumState` and `PureState` become `SymModel`.
- Arguments keep their vendored explicitness, with the state as the receiver: the vendored
  `ev_mono ψ X Y h` is `S.ev_mono X Y h`. Named carrier arguments (`(ι₂ := ι)`, 72 sites in CP)
  are deleted: the model fixes both carriers.
- The header of a ported file credits the upstream authors and says it is a port, not a vendored
  file (see the keystone); it is an ordinary module of this repository, so `scripts/modularize.py`
  applies and the vendor scripts do not.

**The model and the translation.** `SymModel 𝔓 K` (keystone): a C*-algebra `𝔓` with its order (the
vendored `Op ι`), a Hilbert space `K`, fields `Ψ`, `Ψ_norm`, `L : 𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)`,
`J : K ≃ₗᵢ[ℂ] K`, `J_J`, `J_Ψ`, `commute`; derived `flip := J.conjStarAlgEquiv`,
`R := flip ∘ L`, `opTensor A B := L A * R B` (a `noncomputable abbrev`, as the vendored one is an
`abbrev`), `ev X := Op.qform Ψ X` (a `def`), and `toBipartite`, the model as a
`MIPRE.BipartiteModel (K →L[ℂ] K) 𝔓 𝔓` with `H := K`, `π := id`, `πA := L`, `πB := R`, whose
`qform` is `ev` and whose `snorm X` is `‖X Ψ‖`, both by `rfl`.

| vendored | port |
|---|---|
| `ψ : QuantumState (ι × ι)` | `S : SymModel 𝔓 K` |
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
`S.isNormalized` exist for statements that still mention normalization.

**Measurements** (`SubMeas`, `Measurement`, `ProjMeas`, `IdxSubMeas`, `OpFamily`, …) are generic
over a ring `R` (`[Ring R] [StarRing R] [PartialOrder R]`, C*-structure only where a proof needs
it), with the vendored field names verbatim; local families take `R = 𝔓`, joint ones
`R = K →L[ℂ] K`; placement is `map` along a ⋆-homomorphism.

**The vendored classical layer is imported, never ported**, and named only through explicit lists,
`open MIPStarRE.LDT (Parameters Distribution avgOver …)`. A wholesale `open MIPStarRE.LDT` is
forbidden: the classical layer imports the vendored matrix layer (§5), so `SubMeas`, `ev`, … exist
under both namespaces. Only `MIPRE/Background/` may name `MIPStarRE`, which is where the port lives.

**Where positivity lives.** Every operator-positivity fact is proved once, in
`Co/Basic/QuantumState.lean`, whose only import is `MIPRE.Foundations.Pasting` (Foundations and the
targeted Mathlib they import; no vendored module), and downstream files apply it. The keystone
holds: `sq_le_self` (any C*-algebra), `S.leftTensor_nonneg`, `S.rightTensor_nonneg`,
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
as "ported elsewhere". The rest of `OperatorExpectations` (Cauchy–Schwarz, the sandwich lemmas) is
its own stage's, through `StateModel.abs_qform_star_mul_le` (`Foundations/Sandwich.lean`) on
`S.toBipartite`, as `ev_conjTranspose` goes through `StateModel.qform_star`.

**The positivity tactic is `sym_nonneg`**, in `Co/Tactic/QuantumNonneg.lean` (the mirrored path):
the vendored `quantum_nonneg` syntax is in every port file's import closure and keeps calling the
vendored matrix lemmas, so the port's macro needs a name of its own. It is the vendored macro with
each lemma replaced by its fully qualified `MIPRE.LIDT.Co.SymModel` counterpart.

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
`Not ported` bullets; `--check` exits 1 if a vendored name is missing. Each stage runs it on its
files and reports the output.

**Elaboration, measured on the keystone.** 86 declarations, about 8 s of non-import elaboration
(minimum of three runs, all profiler categories; typeclass inference 4.9 s of it), against 2.4 s for
the vendored file's 58; no declaration over 1 s, the largest `S.opTensor_nonneg` (0.67 s). Most of
the cost is synthesizing the coercion classes of `𝔓 →⋆ₐ[ℂ] (K →L[ℂ] K)` (about 60 ms per generic
`map_*` lemma), so:
- prefer the structure's own lemmas (`S.L.map_add`, `S.L.map_mul`) and term-mode `congrArg`
  proofs to `rw [map_add]` (measured 2.5× faster);
- for real scalars rewrite with `← Complex.coe_smul` rather than `RCLike.real_smul_eq_coe_smul`;
- do not mark `star (S.L A) = S.L (star A)` `@[simp]` (the vendored `leftTensor_conjTranspose` is
  `@[simp]`): it loops with `map_star`.
