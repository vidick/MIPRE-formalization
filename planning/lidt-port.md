# Low individual degree test — port plan (copy-and-integrate from MIPStarRE)

Status: **plan only, nothing ported yet.** Written 2026-09-08 after inspecting a local
clone of `LionSR/MIPStarRE` at commit `507e8122` (2026-08-25). The authors (Sirui Lu and
collaborators) have agreed to the reuse of their code in this repository; the upstream
repository carries no license file, so that agreement is the basis for redistribution
under this repository's Apache 2.0 license and must be recorded in the vendored tree
(decision D5).

## Context

Goal: make the soundness theorem of the classical low individual degree test (LDT;
Ji, Natarajan, Vidick, Wright, Yuen, arXiv:2009.12982) available in this repository as a
theorem **stated entirely in this repository's own vocabulary** (`MIPRE.Game`,
`MIPRE.TensorProductStrategy`, `MIPRE.ProjectiveMeasurement`, `MIPRE.POVM`, Mathlib
`MvPolynomial`), with the proof delegated to the vendored MIPStarRE development through
an explicit bridge. The blueprint currently lists this result as the hard imported
theorem `thm:qld` (Section `sec:rr-qld`), tagged "should certainly be axiomatized at
first". After this port it becomes a proved node.

Approach chosen (not a git merge): copy the Lean sources into a subfolder, seal them
behind a bridge, and never let MIPStarRE's own foundational types (`SubMeas`,
`QuantumState`, `Distribution`, `FieldModel`, …) leak into the rest of this repository.
The audit surface for "what was proved" moves from MIPStarRE's definitions to ours.

### Verified facts this plan relies on (checked 2026-09-08 against the local clone)

1. **Toolchain match.** Both repositories pin `leanprover/lean4:v4.32.0` and Mathlib
   `v4.32.0`, and both manifests resolve Mathlib to the *same commit*
   `81a5d257c8e410db227a6665ed08f64fea08e997`. No porting across Mathlib versions.
2. **Size.** MIPStarRE Lean sources: 337 files, 125,853 lines, under `MIPStarRE/Quantum/`
   (10 files, 1,679 lines) and `MIPStarRE/LDT/` (325 files), plus two aggregators. 2,113 theorems/lemmas,
   ~1,000 definitions, 151 structures. Zero `sorry` (one grep hit is inside a docstring).
3. **Main theorem.** `MIPStarRE.LDT.Test.mainFormal`
   (`MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:300`). Checked-in axiom audit
   (`results/axioms.json`) and the `AxiomAudit.lean` regression file show it depends only
   on `propext`, `Classical.choice`, `Quot.sound`. Statement shape:
   ```
   theorem mainFormal (params : Parameters) [FieldModel params.q]
       {ιA ιB} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
       (strategy : ProjStrat params ιA ιB) (eps : Error)
       (hpass : strategy.lowIndividualDegreeFailureProbability ≤ eps)
       (k : ℕ) (hk : 400 * params.m * params.d ≤ k) (hk0 : 0 < k) :
       ∃ G_A : ProjMeas (Polynomial params) ιA, ∃ G_B : ProjMeas (Polynomial params) ιB,
         ConsRel state (uniform Point) (pointMeasurementA) (eval G_B) δ ∧
         ConsRel state (uniform Point) (eval G_A) (pointMeasurementB) δ ∧
         ConsRel state (uniform Unit) (const G_A) (const G_B) δ
   where δ = mainFormalError params k eps
           = 100000 · k² · m⁴ · (eps^(1/40000) + (d/q)^(1/40000) + exp(−k/(2560000 m²)))
   ```
   Two documented deviations from the paper: `400·m·d ≤ k` (paper prints `m·d ≤ k`) and
   `0 < k`. Note that the `exp` term does **not** vanish at the minimal `k = 400·m·d`
   (it equals `exp(−d/(6400 m))`), so `k` must stay a free parameter in our statement
   too; collapsing it into a single `δ(ε, m, d, q)` is a separate, later lemma.
4. **MIPStarRE's foundational types** (all under namespace `MIPStarRE.LDT` unless noted):
   - `MIPStarRE.Quantum.Op d := Matrix d d ℂ`; `normalizedTrace A = trace A / card d`.
   - `QuantumState ι` = a PSD **density matrix** `density : Op ι` (not a vector);
     `IsNormalized` ↔ normalized trace `= 1`. Strategies use `QuantumState (ιA × ιB)`.
   - `SubMeas α ι` = `outcome : α → Op ι`, `total`, PSD, `∑ = total`, `total ≤ 1`;
     `Measurement` adds `total = 1`; `ProjMeas` adds idempotence.
     `IdxProjMeas Q α ι := Q → ProjMeas α ι`.
   - `Distribution α` = finite support + nonnegative weights (a *weighted* distribution;
     `IsProbability` is a separate predicate). `uniformDistribution α`.
   - `Parameters` = `m q d : ℕ`, `0 < m`, `0 < q`, `q` a prime power.
     `class FieldModel q` bundles a finite field `K` with `K ≃ Fin q`.
     `Fq params := Fin params.q`; `Point params := Fin m → Fq params`. Field arithmetic
     is transported through the `Fin q` coding (`encodeScalar`/`decodePoint`).
   - `Polynomial params` = `MvPolynomial (Fin m) K` with `∀ i, degreeOf i ≤ d`
     (Mathlib polynomials, good). `AxisLinePolynomial params` = univariate
     `Polynomial K` with `natDegree ≤ d`; similarly `DiagonalLinePolynomial`.
   - `AxisParallelLine params` = `(base : Point, direction : Fin m)`;
     `DiagonalLine params` = `(base direction : Point)`. Both carry **all**
     parametrizations, and `ProjStrat` requires *reparametrization invariance*
     (`StrategyCore.lean:166-182`): `(M (ℓ.rebaseAt t)).outcome (f.reparamAt t) =
     (M ℓ).outcome f`.
   - `ProjStrat params ιA ιB` = state + for each prover: point / axis-line / diagonal-line
     projective measurement families + the two invariance proofs.
   - Consistency `ConsRel ψ 𝒟 A B δ` ↔ `bipartiteConsError ψ 𝒟 A B ≤ δ`, where the
     per-question defect is `max 0 (⟨A_total ⊗ B_total⟩ − ∑_a ⟨A_a ⊗ B_a⟩)`, i.e. the
     off-diagonal mass `∑_{a≠b} ⟨ψ|A_a ⊗ B_b|ψ⟩` for complete measurements
     (`Test/Defs.lean:191-250`).
   - `lowIndividualDegreeFailureProbability` (`Test/StrategyBiProj/Measurements.lean:464`)
     = `(axis + point + diagonal) / 3`, where `axis` averages the two role orders
     (line to A / point to B and vice versa) over uniform `(point, direction)` with the
     line answer evaluated at parameter `0`; `point` is point-agreement over uniform
     points; `diagonal` averages over the two role orders and over `j : Fin m` a
     *restricted* diagonal sample whose direction has coordinates `> j` zeroed.
     **This exact distribution is what our game must reproduce.**
5. **Build configuration differences** (`lakefile.toml`):

   | option | MIPStarRE | this repo |
   |---|---|---|
   | `autoImplicit` | unset (default `true`) | `false` |
   | `relaxedAutoImplicit` | `false` | `false` |
   | `maxSynthPendingDepth` | `3` | unset |
   | `weak.linter.mathlibStandardSet` | `true` | unset |
   | `checkdecls` | local `lean_exe` in `scripts/` | dependency `PatrickMassot/checkdecls` |
   | doc-gen4 | `docbuild/` subproject | direct `require` |

   Five files use `import Mathlib` (full). Top-level `set_option` in sources: only
   `linter.style.header` (2×) and `linter.unusedFintypeInType` (1×). No
   `set_option autoImplicit` anywhere, so whether the code *relies* on auto-bound
   implicits is unknown until compiled under our options (Phase 0).
6. **MIPStarRE side infrastructure not to be imported**: 14 GitHub workflows (several
   drive Claude Code with issue/PR write permissions), 29 Python audit scripts + tests,
   131 docs, 68 dated audits, a `texra_blueprint` plasTeX plugin with a
   `texra-blueprint.toml`, `AGENTS.md`/`CLAUDE.md`, `.claude/settings.json` (installs
   a third-party skills plugin), `home_page/`, `docbuild/`, `references/ldt-paper/`
   (the paper's TeX), `scripts/comparator/` (generates a Mathlib-only
   `Challenge.lean.expected`, 41 KB, restating the closure of `mainFormal`'s statement —
   useful as an *audit aid*, see D6).
7. **Blueprint.** MIPStarRE's blueprint is 10 chapters, 7,981 TeX lines, 786 `\lean{}`
   references, 333 `\leanok`, laid out as `blueprint/src/chapter/chNN_*.tex` with the
   `texra_blueprint` plugin in `plastex.cfg`. Ours is `blueprint/src/content/NN_*.tex`
   with stock `leanblueprint`.
8. **This repo's conventions that constrain the port**: single `lean_lib` `MIPRE` with
   root `MIPRE.lean` regenerated by `lake exe mk_all` (CI checks `mk_all --check`); CI
   `build-project.yml` runs `lake build MIPRE` with `.lake/build` cached by
   toolchain+manifest hash; the existing precedent for imported background results is
   `MIPRE/Background/GowersHatami/`; vendored third-party code precedent is `MIPRE/LCS/`
   (Sean Perazzolo, with copyright header naming the author) and `MIPRE/Cslib/`.

## Decisions

**D1 — Location: `MIPRE/Background/LIDT/`, not a top-level `background/LIDT/`.**
Lean module names must be valid identifiers rooted at a `lean_lib`; ours is `MIPRE`, so
sources must live under `MIPRE/`. A top-level `background/` would need a second
`lean_lib` with `srcDir`, would escape `mk_all` and the single CI build target, and would
break the `MIPRE.Background.*` convention already used for Gowers–Hatami. Layout:

```
MIPRE/Background/LIDT/
├── MIPStarRE/                 # vendored, read-only (D3, D4, D5)
│   ├── README.md              # provenance, permission, commit hash, sync procedure
│   ├── Challenge.lean.expected# upstream Mathlib-only statement closure (audit aid)
│   ├── Quantum.lean, LDT.lean # upstream aggregators (import lists rewritten)
│   ├── Quantum/…              # 10 files
│   └── LDT/…                  # 293 files
├── Game.lean                  # OUR definitions: the LDT game, answer/question types,
│                              #   low-individual-degree polynomials, evaluation family
├── Soundness.lean             # OUR statement of the theorem (initially `sorry`)
└── Bridge/
    ├── Field.lean             # our finite field F  ⇄  Parameters + FieldModel instance
    ├── Polynomial.lean        # our LowIndDegPoly / line polynomials  ⇄  theirs
    ├── State.lean             # vector state ψ  ⇄  density matrix QuantumState
    ├── Measurement.lean       # ProjectiveMeasurement/POVM  ⇄  ProjMeas/SubMeas;
    │                          #   coarse-graining of ill-typed answers; reparametrization
    ├── Strategy.lean          # TensorProductStrategy (lidtGame)  →  ProjStrat
    ├── Consistency.lean       # our bipartite consistency  ⇄  ConsRel
    ├── Value.lean             # failure probability ≤ 1 − S.value
    └── Main.lean              # assembles: mainFormal  ⇒  our theorem
```
Module prefix for vendored files: `MIPRE.Background.LIDT.MIPStarRE.` replacing
`MIPStarRE.` — a pure prefix substitution on `import` lines, so re-syncing with upstream
is mechanical.

**D2 — Keep MIPStarRE's namespaces unchanged inside the vendored tree.** Namespaces are
independent of module paths in Lean. Renaming `MIPStarRE.LDT.*` → `MIPRE.*` would touch
126k lines, risk collisions with our `MIPRE.Measurement`-style names, and destroy
one-command re-syncing. The odd top-level namespace `MIPStarRE` is acceptable because
nothing outside `Bridge/` may refer to it (enforced by review; optionally by a grep in
CI). Revisit only if upstream goes dormant and we start editing the code ourselves.
Phase 0 must check the three `namespace Matrix` blocks in the vendored code for
collisions with our own `Matrix`-namespace lemmas (collisions with Mathlib are excluded:
same Mathlib commit).

**D3 — Vendored code is read-only except for (a) import rewrites, (b) the provenance
header, (c) minimal compile fixes under our lake options.** Fixes of type (c) go
upstream as PRs where possible; the local README lists every deviation. We do not
add the upstream linter set; we do add `maxSynthPendingDepth = 3` globally in our
`lakefile.toml` if Phase 0 shows it is needed (harmless for our code). We do **not**
relax `autoImplicit = false`: if vendored files need auto-bound implicits, we add
explicit binders (type-(c) fix), which is also the upstream-preferred style.

**D4 — What is copied.** `MIPStarRE/Quantum/**`, `MIPStarRE/LDT/**`, and the two
aggregators `Quantum.lean`, `LDT.lean`. Kept although not in the proof closure:
`LDT/Test/AxiomAudit.lean` (cheap; it is the sorry-freedom regression) and
`LDT/Test/Classical.lean` (the classical overview theorem with the explicit
Polishchuk–Spielman hypothesis; documents the paper's Section 2 and is small).
Not copied: everything in fact 6, the upstream root `MIPStarRE.lean`, `scripts/`,
the blueprint (D7), `references/ldt-paper/`. Docstrings in vendored files cite upstream
paths (`blueprint/src/chapter/…`, `references/ldt-paper/…`, `docs/paper-gaps/…`); the
README explains that these resolve in the upstream repository at the recorded commit.

**D5 — Provenance and attribution.** Each vendored file gets a header prepended by the
vendoring script:
```
/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
-/
```
`MIPRE/Background/LIDT/MIPStarRE/README.md` records: upstream URL, commit, date, the
names of the contributors as listed by GitHub at vendoring time, the permission
statement (who agreed, when), the list of local deviations, and the re-sync procedure.
Top-level `README.md` gets a bullet under "Repository layout" mirroring the LCS one.

**D6 — Vendoring is done by a script, not by hand.** `scripts/vendor-lidt.py <clone>
<commit>`: verifies the clone is at `<commit>`, copies the file set of D4, rewrites
imports, prepends headers, copies `scripts/comparator/expected/Challenge.lean.expected`,
writes the README stanza, then the operator runs `lake exe mk_all`. Idempotent; a
re-sync is "re-run, `git diff`, re-apply type-(c) fixes, rebuild". The
`Challenge.lean.expected` copy is the compact reading list for anyone auditing what
`mainFormal` asserts *before* the bridge exists; once Phase 3 lands, our
`Soundness.lean` is the audit surface and the challenge file is only historical.

**D7 — Blueprint: do not import the MIPStarRE chapters (for now).** Instead, in
`03_background_results.tex`, add a new subsection *"The classical low individual degree
test"* before `sec:rr-qld` with one theorem node `thm:lidt-soundness` stating our
`Soundness.lean` theorem in prose (with the `k` parameter and the two paper
corrections), `\lean{MIPRE.LIDT.lowIndividualDegree_soundness}`, `\leanok` on the
statement in Phase 2 and on the proof in Phase 3, a *Source* paragraph crediting
MIPStarRE, and `\uses{def:game,def:tensor-strategy,def:distance}`. Make `thm:qld`
`\uses{thm:lidt-soundness}` and rewrite its *Comments* paragraph (the "axiomatize at
first" advice no longer applies to the classical test). Importing the 10 upstream
chapters as an appendix part is a possible Phase 4 item; it needs the `texra_blueprint`
plugin or a de-texra pass and ~8k lines of review, and adds nothing to the trusted
statement.

**D8 — Our statement uses a *game*, not a bespoke strategy container.** The blueprint
and the rest of this repository phrase everything as `Game` + `TensorProductStrategy` +
value; `thm:qld` is stated for the game `G^pauli`. So `Game.lean` defines an honest
`lidtGame F m d : Game Q Q A A` whose `μ` and `D` reproduce MIPStarRE's failure
probability exactly (fact 4, last bullet), and the theorem's hypothesis is
`1 − ε ≤ S.value`. Consequences that the bridge must absorb (all standard, none deep):

- *Single answer type.* `Game` has one answer alphabet per player, so
  `A := F ⊕ LinePoly F d ⊕ LinePoly F (m·d)` (field element, axis-line polynomial of
  degree ≤ d, or diagonal-line polynomial of degree ≤ m·d). The decision predicate
  rejects ill-typed answers. The bridge coarse-grains ill-typed
  outcomes of the strategy's projective measurement on a question into a fixed
  default well-typed outcome; this preserves projectivity (outcomes of a
  `ProjectiveMeasurement` are mutually orthogonal, a lemma we add to
  `Foundations/Games.lean`) and can only *increase* acceptance, which is the direction
  we need.
- *Canonical line questions.* `ProjStrat` demands reparametrization invariance over all
  `(base, direction)` presentations. Our question type uses canonical representatives
  (axis line: base with coordinate `i` zeroed; diagonal line: a canonical base on the
  line, to be fixed after reading `rebaseAt`/`reparamAt` in Phase 2a). The bridge
  *defines* the measurement at a non-canonical presentation by reading the canonical
  one and shifting the polynomial answer, so invariance holds by construction
  (`reparamAt` composition lemma).
- *Restricted diagonal directions.* MIPStarRE's diagonal branch samples, for
  `j : Fin m`, directions with coordinates above `j` zeroed, with weight `1/m` on `j`.
  Our `μ` encodes the same mixture explicitly. This is the paper's test (definition of
  the LDT in `test_definition.tex`), not a MIPStarRE artefact; the blueprint prose
  should say so.
- *Distribution type.* Our `μ : Q → Q → ℝ` (summing to 1) vs their weighted
  `Distribution`. The bridge relates `bipartiteConsError` under their
  `uniformDistribution` to our sums; only uniform distributions appear in
  `mainFormal`, so one lemma per uniform sample space suffices.
- *Consistency notion.* We need a bipartite consistency measure in our vocabulary:
  `MIPRE.inconsistency ψ μ A B := ∑_x μ x ∑_{a≠b} Re ⟨ψ| A^x_a ⊗ B^x_b |ψ⟩` for
  `A : X → POVM α (Fin dA)`, `B : X → POVM α (Fin dB)`. This is general (the paper's
  Definition 4.8, also needed for `thm:qld`) and belongs in
  `MIPRE/Foundations/Distances.lean` next to `povmDistance`, with a blueprint
  definition node. The bridge lemma is: for pure states `ψ` with density
  `vecMulVec ψ (star ψ)`, `trace (ρ * M) = star ψ ⬝ᵥ (M *ᵥ ψ)`, plus
  `max 0 (…) = ∑_{a≠b} …` for complete measurements.
- *Field.* Our statement quantifies over an arbitrary finite field `F` (`[Field F]
  [Fintype F] [DecidableEq F]`), with `q := Fintype.card F`. The bridge builds
  `Parameters` (prime-power witness from `FiniteField.card`) and a `FieldModel q`
  instance from `Fintype.equivFin F`, then transports `Fq params = Fin q` ⇄ `F`.
- *Low individual degree polynomials.* `MIPRE.LIDT.LowIndDegPoly F m d :=
  {p : MvPolynomial (Fin m) F // ∀ i, p.degreeOf i ≤ d}`, with a `Fintype` instance
  (needed for `POVM`/`ProjectiveMeasurement` outcome alphabets; via the finite set of
  monomials of bounded individual degree). Line answers
  `LinePoly F d := {p : Polynomial F // p.natDegree ≤ d}` with `Fintype` via
  `Polynomial.degreeLTEquiv`. Both are essentially MIPStarRE's `Polynomial params` /
  `AxisLinePolynomial params` once `K := F`, so the bridge equivalences are
  near-definitional.

Sketch of `Soundness.lean` (names indicative):
```lean
namespace MIPRE.LIDT
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d : ℕ)

/-- Soundness of the classical low individual degree test, in the form proved in
`MIPStarRE` (arXiv:2009.12982, Theorem `thm:main-formal`, with the corrections
`400 m d ≤ k` and `0 < k`). -/
theorem lowIndividualDegree_soundness (hm : 0 < m)
    (S : TensorProductStrategy (lidtGame F m d)) (ε : ℝ) (hS : 1 - ε ≤ S.value)
    (k : ℕ) (hk : 400 * m * d ≤ k) (hk0 : 0 < k) :
    ∃ GA : ProjectiveMeasurement Unit (LowIndDegPoly F m d) (Matrix (Fin S.dA) (Fin S.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (LowIndDegPoly F m d) (Matrix (Fin S.dB) (Fin S.dB) ℂ),
      inconsistency S.ψ (uniformOn (Fin m → F)) S.pointPOVMA GB.evalAt ≤ δ ∧
      inconsistency S.ψ (uniformOn (Fin m → F)) GA.evalAt S.pointPOVMB ≤ δ ∧
      inconsistency S.ψ (uniformOn Unit) GA.povm GB.povm ≤ δ
  where δ := lidtError m d (Fintype.card F) k ε := by
  sorry
end MIPRE.LIDT
```
`lidtError` is *our* transcription of `mainFormalError` (the bridge proves the two
agree, `rfl` modulo casts). `S.pointPOVMA` is the coarse-grained point measurement of
player A viewed as a `POVM F (Fin S.dA)` family over points; `GB.evalAt u` is the
push-forward of `GB` along `p ↦ p.eval u`. All of these are our definitions in
`Game.lean`.

## Phases

**Phase 0 — feasibility spike (no PR; a throwaway branch).** Run the vendoring script
into `MIPRE/Background/LIDT/MIPStarRE/`, `lake exe mk_all`, `lake build MIPRE`.
Record: (i) wall-clock build time on the development machine, (ii) every error under
`autoImplicit = false`, (iii) whether `maxSynthPendingDepth = 3` is required and where,
(iv) `Matrix`-namespace or other name collisions with existing `MIPRE` code,
(v) linter noise volume. Deliverable: a short section appended to this file with the
numbers and the go/no-go on D3's "minimal fixes" assumption. Also measure CI impact: if
a cold `lake build` exceeds the runner budget, plan the cache warm-up (the existing
`.lake/build` cache key is toolchain+manifest, so incremental CI builds should be fine
after the first green run on `main`).

**Phase 1 — vendor (PR "Vendor the MIPStarRE low individual degree test development").**
Contents: `scripts/vendor-lidt.py`, the vendored tree with headers, the provenance
README, `Challenge.lean.expected`, `lakefile.toml` option additions if any (D3),
regenerated `MIPRE.lean`, top-level `README.md` bullet, `CONTRIBUTING.md` note that
`MIPRE/Background/LIDT/MIPStarRE/` is not edited directly. No blueprint change, no
bridge. Acceptance: CI green; `#print axioms MIPStarRE.LDT.Test.mainFormal` (run
locally, recorded in the PR) shows only the three standard axioms; `git grep MIPStarRE
-- ':!MIPRE/Background/LIDT'` returns nothing.

**Phase 2 — our statement (PR "State the low individual degree test soundness
theorem").** Prerequisite reading (Phase 2a, no code): `Test/StrategyBiProj/
Measurements.lean` in full, `Basic/AxisParallelLine.lean`, `Basic/DiagonalLine.lean`
(`rebaseAt`, `reparamAt`, `pointAt`, `zeroCoord`), `Test/Defs.lean` §"Consistency", and
the paper's `test_definition.tex` — to fix the canonical line representatives and confirm
`μ`. Then: `Foundations/Distances.lean` gains `inconsistency` (+ blueprint
`def:inconsistency`, `\leanok`); `Foundations/Games.lean` gains the orthogonality lemma
for `ProjectiveMeasurement` outcomes and the coarse-graining construction (generic,
reusable); `Background/LIDT/Game.lean`; `Background/LIDT/Soundness.lean` with `sorry`;
blueprint node `thm:lidt-soundness` per D7 with `\leanok` on the statement only;
`thm:qld` updated. Acceptance: CI green; the statement file imports nothing from
`Bridge/` or the vendored tree; a reviewer can check the statement against the paper
using only this repository's definitions.

**Phase 3 — bridge (one PR per file in `Bridge/`, in dependency order: Field →
Polynomial → State → Measurement → Strategy → Consistency → Value → Main).** Each PR
states its lemmas in the docstring of the file and lands `sorry`-free. The last PR
replaces the `sorry` in `Soundness.lean` by `exact Bridge.main …` (adding the import),
flips `\leanok` on the proof, and adds a CI-visible `#print axioms` guard (either a
`guard_msgs` test file or a line in the build workflow) for
`MIPRE.LIDT.lowIndividualDegree_soundness`. Expected hard spots, in decreasing order:
`Value.lean` (matching our `μ`/`D` sums to their three-branch average, including the
`1/m` restricted-diagonal mixture and the evaluation at parameter `0`),
`Measurement.lean` (coarse-graining + reparametrization by construction),
`Consistency.lean` (density-vs-vector and `max 0` bookkeeping). Everything else is
transport along equivalences.

**Phase 4 — optional follow-ups.** (a) A corollary collapsing `k` into a single
`δ_lidt(ε, m, d, q)` in the blueprint's `a (md)^a (ε^b + q^{-b} + …)` style, to feed
`thm:qld`. (b) Pruning vendored files outside the import closure of `mainFormal` (use
`lake exe graph` / import analysis) if build time matters; keep `AxiomAudit.lean`.
(c) Importing the upstream blueprint chapters as an appendix (D7). (d) A re-sync to a
newer upstream commit if upstream keeps moving (last upstream push 2026-08-25).

## Risks and open questions

- **Compile under `autoImplicit = false`** — unknown until Phase 0; worst case is a
  mechanical but large binder-adding pass (type-(c) fix, upstreamable).
- **Build time.** 126k lines plus five `import Mathlib` files. Local measurement in
  Phase 0 decides whether Phase 4(b) pruning is needed before Phase 1.
- **Statement fidelity is now our responsibility.** The value of this port is that
  `Soundness.lean` is checkable against the paper without reading MIPStarRE. The
  bridge must not weaken the statement (e.g. by choosing a convenient coarse-graining
  default that makes acceptance trivially high — it does not, since the game's `D`
  rejects ill-typed answers regardless; but review should check this explicitly).
- **Canonical representatives for diagonal lines** interact with the restricted
  direction pattern; settle in Phase 2a before writing `Game.lean`.
- **Upstream drift.** Any type-(c) fix we make locally is a merge conflict at re-sync
  time unless upstreamed. Policy: upstream first, vendor second.
- **Do not commit the scratch clone.** The inspection clone at `MIPStarRE/` in the repo
  root is untracked; it should be excluded via `.git/info/exclude` (local) and removed
  once Phase 1 lands (the vendoring script takes the clone path as an argument, so it
  can live anywhere).

## Phase 2a reading notes (2026-09-08)

Read: `references/ldt-paper/test_definition.tex` (the test, Fig. 1; strategies;
`thm:main-formal`), `LDT/Basic/AxisParallelLine.lean`, `LDT/Basic/DiagonalLine.lean`,
`LDT/Basic/LinePolynomials.lean` (`reparamAt`), `LDT/Test/StrategyCore.lean`
(invariance), `LDT/Test/StrategyBiProj/Measurements.lean` (failure probability).

- **The paper's test** (Fig. 1): with probability 1/3 each — *axis-parallel lines test*
  (random role r, uniform point u, uniform direction i ∈ {1..m}, ℓ = u + t·e_i; player
  r gets ℓ and answers a degree-≤d univariate polynomial f on ℓ, player r̄ gets u and
  answers a ∈ F_q; accept iff f(u) = a); *self-consistency test* (both get the same
  uniform u; accept iff a = b); *diagonal lines test* (random role, uniform u, uniform
  i ∈ {1..m}, uniform v with the last m−i coordinates 0 — **v = 0 is allowed**, giving a
  singleton "line" — ℓ = u + t·v; player r answers a degree-≤md polynomial on ℓ;
  accept iff f(u) = a). MIPStarRE's `lowIndividualDegreeFailureProbability` is exactly
  this (its `j : Fin m` with free coordinates `0..j` is the paper's `i = j+1`).
- **Line questions in the paper are geometric lines (sets)**; answers are functions on
  the line of bounded degree in any affine parametrization. MIPStarRE indexes line
  measurements by *all* parametrizations `(base, direction)` and imposes invariance
  under `rebaseAt`/`reparamAt` (translation of the parameter only; direction is never
  rescaled — MIPStarRE's `DiagonalLine.direction` is kept as sampled). It already
  provides canonical representatives, which our `Game.lean` should adopt verbatim in
  our own vocabulary:
  - axis line through `u` in direction `i`: `throughPoint u i` = base `u` with
    coordinate `i` set to `0`, direction `i`; sample parameter of `u` is `u i`.
  - diagonal line through `u` in direction `v`: `throughPointDirection u v` = if
    `v = 0` then `(u, 0)`, else with `j` the first nonzero coordinate of `v`,
    `w := v / v_j` (so `w_j = 1`) and base `u − u_j·w` (so `base_j = 0`); sample
    parameter of `u` is `u j` (and `0` when `v = 0`). Lemma
    `throughPointDirection_pointAt_sampleParameter : pointAt (canonical) (param) = u`.
  So our question type is: `point u` | `axisLine i u` with `u i = 0` |
  `diagLine u w` with `w = 0 ∨ (w_j = 1 ∧ u_j = 0 for j = first nonzero index of w)`.
  Decision: encode these as subtypes with decidable predicates (concrete, `Fintype` for
  free), not as quotients.
- **Answers**: `F ⊕ LinePoly F d ⊕ LinePoly F (m·d)` (three summands, since axis and
  diagonal answers have different degree bounds — the plan's earlier two-summand
  sketch was wrong). The decision predicate evaluates the polynomial at the sample
  parameter of the sampled point. MIPStarRE's `DiagonalLineAnswer := Fq → Fq` (a bare
  function alphabet) is internal to its pasting argument and does not surface in
  `mainFormal`; we never need it.
- **Degenerate diagonal lines (`v = 0`)** interact with invariance: for a singleton line
  `rebaseAt t` is the identity, so invariance forces the measurement to be invariant
  under all shifts `f ↦ f(·+t)`; the only projective measurements with that property
  are supported on constant polynomials. The bridge therefore builds, for `v = 0`, the
  line measurement as the coarse-graining `f ↦ f(0)` of the strategy's answer, embedded
  as constants. This is consistent with the game's acceptance rule (only `f(0)` is
  tested) and can only increase acceptance. Record this in `Bridge/Measurement.lean`.
- **Reparametrization by construction**: for a non-canonical `(base, direction)` the
  bridge defines `M ℓ` outcome `f` := canonical-measurement outcome
  `f.reparamAt (−t)` where `t` is the parameter of `base` on the canonical line;
  `reparamAt_reparamAt` (composition) and `reparamAtEquiv` (bijection on outcomes, so
  projectivity/completeness transport) are already in `LinePolynomials.lean`.

## Phase 0 findings (2026-09-08, in progress)

- Vendoring script `scripts/vendor-lidt.py` written and run: 337 files, 782 import lines
  rewritten, headers added, README generated. `lake exe mk_all` added 337 modules to
  `MIPRE.lean`.
- No `Matrix`-namespace collisions with our code (our code declares nothing in `Matrix`).
- `lake exe cache get` on a fresh checkout: 13.5 min, dominated by cloning Mathlib.
- Full `lake build MIPRE` on a 12-core machine at default parallelism: **72 min** for 285
  modules (241 of the 337 vendored ones; the slowest single modules take ~5 min, the
  `import Mathlib` ones among them). Two vendored modules
  (`LDT/CommutativityPoints/BridgeTheorems/LiftBridges.lean`,
  `LDT/MakingMeasurementsProjective/QXPLayerIdentities/RectangularSvd.lean`) died with
  `std::bad_alloc` (out of memory), not a Lean error — 12 concurrent Lean processes each
  importing Mathlib exhaust RAM — which blocked their 96 dependents. This Lake has no
  `--jobs` flag; **cap parallelism locally with `LEAN_NUM_THREADS=4 lake build`**. CI
  runners have 2 cores, so this does not affect CI. With the cap, the two modules and
  their 96 dependents built without incident (15 min + 112 min), so **all 337 vendored
  modules compile unchanged**: no local deviations from upstream were needed, and D3's
  list of allowed edits is currently empty. Total cold build ≈ 3.5 h locally.
- `#print axioms MIPStarRE.LDT.Test.mainFormal` in *our* build:
  `[propext, Classical.choice, Quot.sound]`. The vendored theorem is axiom-clean here,
  matching the upstream audit.
- **No Lean errors at all** in the 241 vendored modules that built, in particular none
  from `autoImplicit = false`; no warnings from vendored files either (the 34 warnings are
  our own `sorry`s). D3's "minimal compile fixes" assumption holds so far.

### Statement drafts (Phase 2, drafted early for review)

- `MIPRE/Foundations/Distances.lean`: added `POVM.map`, `ProjectiveMeasurement.toPOVM`,
  `uniform`, `inconsistency` (type-checked).
- `MIPRE/Background/LIDT/Game.lean` (≈185 lines, type-checked, **sorry-free**; the game
  requires `[NeZero m]`, since with `m = 0` there are no directions and the question
  weights do not sum to one — the diagonal direction is sampled as its first `j+1`
  coordinates, `Sample.diag … (j : Fin m) (v : Fin (j+1) → F)`, extended by zeros via
  `Sample.extend`, which makes the total-probability lemma `Sample.sum_weight` a direct
  computation): after a first ≈330-line draft was judged too long, simplified by (i)
  representing polynomials by coefficient vectors/tables (`LinePoly F n := Fin (n+1) → F`,
  `LowIndDegPoly := (Fin m → Fin (d+1)) → F`) instead of subtypes of Mathlib polynomials,
  which removed all `Fintype`/`DecidableEq` proofs — the correspondence with
  `Polynomial`/`MvPolynomial` becomes a bridge lemma; (ii) representing lines as plain
  pairs `(base, direction)` with a proof-free canonical-form function `Line.through`, the
  game asking only canonical presentations (non-canonical pairs are zero-probability
  questions); (iii) dropping the separate axis-line type (axis-parallel lines are
  `Line.through u (Pi.single i 1)`). D8 above is superseded on these points.
- `MIPRE/Background/LIDT/Soundness.lean` (≈100 lines, builds; one `sorry`, the theorem
  itself): statement plus the statement vocabulary (`pointPOVMA/B`, `evalPOVM`,
  `LowIndDegPoly.eval`, `lidtError`).
- Blueprint: `def:inconsistency` in `02_foundations.tex` (`\leanok`), and a new
  subsection `sec:rr-lidt` in `03_background_results.tex` with `def:lidt` (`\leanok`) and
  `thm:lidt-soundness` (`\leanok` on the statement; the proof is not yet marked).
  `thm:qld` now `\uses{thm:lidt-soundness}` and its "axiomatize at first" advice is
  rewritten; the background-results table splits the classical and Pauli rows.
  `leanblueprint pdf` compiles with no undefined references (29 pages).

## Non-goals

- Reproducing MIPStarRE's agentic workflow, CI, audit scripts, or documentation tree.
- Renaming or refactoring the vendored code.
- Proving the *quantum* low individual degree test (`thm:qld`, Pauli basis test); this
  port supplies its classical ingredient only.
