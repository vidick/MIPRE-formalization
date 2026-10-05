# The Aldous–Lyons track: `TMIP* = RE` (Bowen–Chapman–Vidick, paper II): estimate and plan

**Status: Phase 0 done (#273; tracking #272); Phase 1 in progress (#279).** The statement and
the interface are in (`MIPRE/TailoredGameValue.lean`, `MIPRE/Tailored/*`), the two checks that
Route A rests on both passed (§4.2, "Phase 0 verdict"), and the blueprint chapter is
`blueprint/src/content/09_tailored.tex`. Four of Phase 1's five slices are done (§5 "Phase 1
slices"): P1a, the toolbox of permutation strategies
(`MIPRE/Tailored/{SignedPerm,Fourier,ZPC,MagicSquare}.lean`); P1b, a tailored verifier as a
normal form verifier with the same games (`MIPRE/Tailored/{Canonical,OfTNFV}.lean`); P1c, the
halting protocol at a fixed level (`MIPRE/Tailored/Halting/*`); and P1d, the tabulation, the
search program, `tailored_halting_reduction_of` and the computable class
(`MIPRE/Tailored/Data/*`, `MIPRE/Tailored/Halting/{Tabulate,Search,Reduction}.lean`,
`MIPRE/Tailored/Class.lean`). So `TailoredHaltingReduction` and `TMIP* = RE` (computable
class) are proved from a `TailoredGapCompression`. P1e, the polynomial-time class, is next.
Phase 2 (#280) is done: P2a, the tailored product with its completeness and soundness for
programs meeting a specification, and P2b, the programs themselves with their running times, so
`TailoredRepetition` is inhabited (`MIPRE.Tailored.tailoredRepetition`, §5 "Phase 2 slices").
Phase 3 (#281) is in progress on Route A, planned in seven slices (§5 "Phase 3 slices"); P3a,
the closure toolbox for the honest strategy, is done (`MIPRE/Tailored/Intro/*`).
Written 2026-10-05, after `MIP* = RE` (`Halting.mipstar_eq_re`), the explicit separation
(#224) and Phases 0–5 of the commuting-operator track (`planning/mipco-track.md`).

Target: the main theorem of *The Aldous–Lyons Conjecture II: Undecidability* (L. Bowen,
M. Chapman, T. Vidick, arXiv:2501.00173, "paper II"): `TMIP* = RE`, a polynomial-time reduction
from the halting problem to *tailored* non-local games, with a perfect *Z-aligned permutation
strategy commuting along edges* (ZPC) as the completeness clause and value at most `1/2` as
the soundness clause. Together with paper I (*The Aldous–Lyons Conjecture I: Subgroup Tests*,
L. Bowen, M. Chapman, A. Lubotzky, T. Vidick, arXiv:2408.00110) it refutes the Aldous–Lyons
conjecture; §9 sizes that corollary separately.

Sources read: the LaTeX sources of paper II (`A-TailoredMIP-main.tex`, 11,911 lines) and of
paper I (`Subgroup_Tests.tex`, 2,783 lines), fetched from arXiv once the maintainer opened
`arxiv.org`. Paper II §2, §6 and §7 were read in full here; §3, §4 and §5, and paper I's
interface, by five readers who compared each statement with the repository (their reports,
about 50k words, are kept with the session's scratch files, `scratchpad/al2/reports/`).
Repository side: `Foundations/{Games,Verifier,GapCompression,Compression}.lean`, `Pipeline/*`,
`Halting/Paper/*`, `Repeat/*`, the `LCS` tree, `WeylBinary.lean`, `GowersHatami/*`, the stage
interfaces, chapters 2–8 of the blueprint. Both papers are public, so their statements may be
quoted here, unlike `MIPRE-proof`'s; there is no adversarial-verification ledger for them, so
the paper itself is the authority, and §8 lists where its text is a sketch or in error.

Line numbers `II:n` and `I:n` refer to the two LaTeX sources.

## 1. Short answer

**The main theorem of paper II is formalizable in this repository as an extension of what is
here, not as a second library, at roughly 50–80k lines of new Lean** — a fifth to a third of
the 241k lines this project has written — plus one blueprint chapter; **80–135k** if one of
its two reusable pieces turns out not to be reusable (§4.2). At this project's cadence that is
of the order of six to ten weeks of the kind of work that produced the repository (§6.3). Two
decisions make the number that small, and both are decisions the repository already took for
`MIP* = RE`:

1. **Value form, bipartite value, direct repetition.** Paper II states compression in
   *entanglement form* over *synchronous* strategies — `Ent(V'_n, 1/2) ≥ max{Ent(V_{2^n}, 1/2),
   2^{2^{λn}-1}}` (II:1865) — and proves its halting theorem by a tower of such bounds. That
   form rests on the anchored parallel repetition theorem of Bavarian–Vidick–Yuen in a
   dimension-preserving reading (II:11425, cited, not proved) and on a rounding of general
   strategies to synchronous ones (`Fact` II:3227, "proof idea" only, citing Vidick 2022).
   Neither is formalized anywhere; the blueprint's `thm:almost-sync` is rated hard, issues
   #22/#23 are open, and anchoring was removed from this blueprint on purpose (#40). The
   paper's own Remark II:1876 says that what its proofs establish is the *value-form*
   soundness — a strategy of value `1 − ε` for `V'_n` gives one of value `1 − f(ε)` with
   `f(ε) < 1/2` for `V_{2^n}` — and the repository's halting route (`Halting/Paper/*`: the
   Kleene fixed point, Lin's search branch, the downward induction) is the value-form proof of
   II:2021–2066 with the paper's linear-constraints processor in the role of the decider. So
   the plan proves soundness for *all* finite-dimensional strategies in the bipartite value
   `val*`, which implies the paper's synchronous `val* ≤ 1/2` through
   `syncValue_le_quantumValue`, uses the vendored direct repetition theorem, and never touches
   anchoring or almost-synchronicity. `rem:bipartite-route` and `rem:direct-vs-anchored`
   already record this choice for JNVWY.
2. **The soundness components are reused; the constructions are rebuilt.** Paper II's three
   transformations must output *tailored* verifiers — checks `F₂`-linear in the unreadable
   answers, selected by the readable ones, decided by a fixed canonical decider — and their
   honest strategies must be signed permutations. So the repository's `Introspection 7`,
   `AnswerReduction 5` and `Repetition 7` cannot be instantiated as they stand. But the
   theorems their soundness rests on are the same ones: the Pauli basis test (`thm:qld`,
   proved here in a bipartite model from the low-individual-degree test), the quantum
   soundness of that test (vendored, 126k lines), oracularization, the closeness and
   data-processing calculus of the bipartite model, the uniform exponential repetition
   theorem (vendored, 71k lines), the Cost/TM toolkit with its universal and clocked machines,
   s-m-n and the fixed point, the succinct Cook–Levin layer and the conditionally linear
   samplers. What is new is the *tailored shape* of every verifier, the *completeness*
   analysis (perfect ZPC strategies survive every transformation — Z-alignment, signed
   permutations, Kronecker products, the affine data processing of `cor:encodings` — which no
   existing proof tracks), and the glue from each tailored construction to the component
   theorems. For question reduction the paper says itself (II:5228–5233) that its combinatorial
   game is JNVWY's and that JNVWY's soundness proof covers it; the repository's typed
   introspection game *is* that game, so a tailored presentation of the repository's own
   introspection verifier is the recommended route, subject to a one-week check (§4.2).

The result is **stronger** than the paper's statement (soundness against all strategies,
not only synchronous ones) and **weaker in one letter**: clause (3) of II:1505 says
`val* < 1/2`, but its proof shows `Ent(G_M, 1/2) = ∞`, that is, every finite-dimensional
strategy has value `< 1/2`, which gives only `val* ≤ 1/2` for the supremum. Paper I's
Theorem 7.4 (I:2140) and the repository both say `≤ 1/2`, and so should the Lean.

Where the lines go (§6.2): roughly a tenth to the tailored foundations and a tenth to the
halting protocol, class statement and assembly; a twentieth to repetition; a quarter to
question reduction; and about half to answer reduction, whose tailored PCP (§5 of the paper,
2,800 live lines) is the paper's longest and least reusable part. The two risks that move the
estimate are whether the repository's introspection verifier and seeded low-degree test can be
*re-presented* as tailored verifiers (expected yes; Phase 0 checks it; 30–50k lines hang on
it) and the
decoupled Cook–Levin for the paper's output-indicator machine, which the paper only sketches
(II:8757).

**Paper I's corollary** — the Aldous–Lyons conjecture is false — needs, on top of
`TMIP* = RE`, the subgroup test associated with a tailored game and its value-preservation
theorem (finitary: permutations, stabilizers, finite-dimensional linear algebra; I:2074–2704)
and, for the conjecture itself rather than "approximating the sofic value is undecidable",
Main Theorem I with a weak-* compactness argument on probability measures on the space of
subgroups. The reader's estimate is 10–20k lines, with the measure-free theorem available
first. It is a separate phase (§5, Phase 6), recommended after the main theorem is in.

## 2. The theorem, in this repository's terms

### 2.1 Paper II's objects (II:940–1512)

- A **game** (II:1073) is a finite graph `G = (V, E)` with loops allowed, lengths `ℓ : V → ℕ`,
  disjoint formal generator sets `S_x` with `|S_x| = ℓ(x)`, a distribution `μ` on `E`, and
  decision predicates `D_xy : F₂^{S_x ⊔ S_y} → {0,1}`. A **strategy** (II:1088) is one PVM per
  vertex with outcomes `F₂^{S_x}`, all on one finite-dimensional space; its value is
  `Σ μ(xy) Σ_{a,b} τ(P^x_a P^y_b) D_xy(ab)` with `τ` the normalized trace (II:1136), and
  **`val*(G)` is the supremum over these synchronous strategies** (II:1141). In the
  repository: `SynchronousGame X A`, `SyncStrategy`, `syncValue`; and `entRequirement G ν`
  is exactly `Ent(G, ν)` of II:1839 (defined, so far used by nothing).
- A **tailored game** (II:1243) splits `S_x = S_x^R ⊔ S_x^L` (readable, linear) and replaces
  `D_xy` by *controlled linear constraints*: a function `L_xy` of the readable answers `γ^R`
  returning a list of vectors `c ∈ F₂^{S_x ⊔ S_y ⊔ {J}}`, accepted by the **canonical decider**
  iff `⟨c, (γ, 1)⟩ = 0` for every `c` (`J` is the affine coordinate, `γ(J) = 1`; the list
  `{J}` alone rejects, the empty list accepts). Linear constraint system games are the
  all-unreadable case (II:1291); the Magic Square is the running example (II:1326–1362).
- **Signed permutations** (II:1008–1070): `Ω_± = {±} × Ω`, `Sym_±(Ω) ≅ Sym(Ω) ⋉ F₂^Ω`, acting on
  the anti-symmetric functions `W⁻ ≅ ℂ^Ω` as the `{0, ±1}` matrices with one non-zero entry
  per row and column. A **permutation strategy** assigns to each generator `X ∈ S_x` an
  involution `U(X) ∈ Sym_±(Ω)`, commuting within `S_x`; its PVM is the Fourier transform
  `P^x_a = ∏_i (Id + (−1)^{a_i} U(X_i))/2`. It is **Z-aligned** if `U(X)` is diagonal for every
  readable `X`, and **commutes along edges** if `U(X)U(Y) = U(Y)U(X)` for `X ∈ S_x`, `Y ∈ S_y`,
  `xy ∈ E` (II:1279–1283). Paper I's permutation strategies (I:1722) are the same data with a
  fixed-point-free central involution `J` (II:1115). Classical (deterministic) strategies
  are the case `|Ω| = 1`, so an always-accepting game has a perfect ZPC strategy.
- A **tailored normal form verifier** (TNFV, II:1758) is `V = (S, L, LP, D)`: a conditionally
  linear sampler `S` (II:5584; with a `Perpendicular` query the repository's `CL.Sampler`
  lacks), an **answer-length calculator** `L(n, x, κ)` returning `ℓ^κ(x)` in unary, a
  **linear-constraints processor** `LP(n, x, y, a^R, b^R)` returning the constraints as a
  sequence of vectors of length `Δ = ℓ^R(x) + ℓ^L(x) + ℓ^R(y) + ℓ^L(y) + 1`, and the fixed
  canonical decider `D` (9 inputs, linear time, II:1757–1787). `V_n` is the game whose edges
  are the outputs of `S(n)`. **λ-bounded** (II:1800): the three running times are at most
  `n^λ` for `n ≥ 2` and the description length is at most `λ`.

### 2.2 The main theorem (II:1505) and the Lean deliverable

> **Theorem (`thm:tailored_MIP*=RE`).** There is a polynomial-time algorithm `M ↦ G_M`, `G_M` a
> tailored game, such that (1) sampling `xy ∼ μ` and evaluating `D_xy` from the encoding of
> `G_M` takes time `poly(|M|)`; (2) if `M` halts, `G_M` has a perfect ZPC strategy; (3) if `M`
> never halts, `val*(G_M) < 1/2` [read `≤ 1/2`, §1].

Paper I consumes exactly this (I:2135–2142, as its Theorem 7.4), in the synchronous value,
plus the computability of `Λ = max_x ℓ(x)` from `M` (I:2156), which an explicit description
gives for free. The class reading `TMIP* = RE` (II:787, II:6997) is the reduction plus the
easy half `TMIP* ⊆ RE` (II:1838): a perfect ZPC strategy is a finite combinatorial object
whose value is an exact rational, so its existence is semidecidable by enumeration — easier
than `MIP* ⊆ RE`, which needs the value approximated from below.

The Lean target mirrors `MIPRE/HaltingGameValue.lean`, which states the reduction behind
`MIP* = RE` with Mathlib imports only:

```lean
/-- A tailored game, explicitly: vertices, the two length functions, rational edge weights,
and the table of controlled constraints `L_xy(γ^R)`; `toGame` applies the canonical decider
and rejects answers of the wrong length. -/
structure TailoredGameData ...

/-- A Z-aligned signed-permutation action whose Fourier-transform `SyncStrategy` commutes
along the edges of positive weight and has value `1`. -/
def TailoredGameData.HasPerfectZPC (g : TailoredGameData) : Prop := ...

def TailoredHaltingReduction : Prop :=
  ∃ g : Nat.Partrec.Code → TailoredGameData, Computable g ∧
    ∀ c, (HaltsOnEmptyInput c → (g c).HasPerfectZPC) ∧
         (¬ HaltsOnEmptyInput c → syncValue (g c).toGame ≤ 1 / 2)
```

Inside the library the soundness clause is proved in the stronger form
`quantumValue (g c).toGame.toGame ≤ 1/2` (bipartite, all strategies), from which the
synchronous clause is `syncValue_le_quantumValue`. Around it: the class statements
`TMIPStarComputable = IsRE` and, through the paper route's polynomial-time class verifier,
`TMIPStar = IsRE`, as `Halting/Paper/ClassMain.lean` does for `MIPStar`; and the halting
protocol's family `V^{M,λ}_C` as the witness, so that clause (1) is the polynomial-time class
verifier rather than a separate statement (the repository already relaxed "polynomial time"
to "computable" in `HaltingGameValue` and recovered the polynomial-time form in
`Halting/Paper/ClassVerifier.lean`; the same two layers apply here).

Paper fidelity, to be recorded in the blueprint chapter: the Lean soundness is stated in the
bipartite value and *implies* the paper's; `≤ 1/2` replaces `< 1/2`; the completeness class
is the paper's; the compression theorem is stated in value form with ZPC completeness, which
the paper calls its proofs' actual content (II:1876) but never states as a theorem; no
entanglement bound is tracked (as `rem:entanglement-form` records for JNVWY).

## 3. The proof, section by section, and where each piece already lives

Paper II's proof is JNVWY's: the halting protocol (II:§2.7) from a compression theorem
(II:1852, proved as `thm:h_level_compression`, II:5643), and compression as question
reduction, then answer reduction, then parallel repetition (II:§7), with a toolbox (II:§3).
The table gives, for each part, the live LaTeX (comment blocks removed: a third of §5 and all
of §6.2 are commented out), what the repository has, and the verdict for the recommended
route. Estimates are new Lean lines by analogy with measured parts of the repository; §6 has
the totals and the calibration.

| Paper | Live lines | Content | Repository counterpart | Verdict | New Lean |
|---|---|---|---|---|---|
| §2.1–2.5 (946–1512) | ≈560 | measurements, three forms of an `F₂^S`-PVM, signed permutations, games, tailored games, ZPC, Magic Square | `Games.lean` (sync strategies, `IsPCC`, `syncValue`, `entRequirement`), `Measurement/PVM` (`pvmObs`), `Weyl.lean` (`wX`/`wZ` are a shift and a `±1` diagonal: signed permutations in all but name), `Linearity.lean` (Fourier transform of an `F₂^n` representation), `LCS/*` (observable↔projector dictionary, solution group; its Magic Square strategy uses `Y` and is not a signed-permutation strategy), `HonestMagicSquare` (one that is) | **new** notions on existing vocabulary | 3–5k |
| §2.6 (1514–1832) | ≈320 | encodings, TNFV, canonical decider, λ-bounded, `Ent` | `Verifier ℓ` (sampler + decider), `IsBounded`, `Cost/*` (programs, `PolyTimeFun`, s-m-n), `Halting/Wrapper*.lean` (a decider program with cost, 1.1k) | **new**: the four-machine verifier with `Verifier.ofTNFV`; the canonical decider as a costed program | 2–3k |
| §2.7 (1833–2072) | ≈240 | halting protocol `F`, `V^{M,λ}`, `lem:dhalt-values`, `lem:lambda` (sketch), proof of the main theorem | `Halting/Paper/*` (3,177 lines): `kleeneFix`, `Vhalt`, `accepts_iff`, `Induction.lean`, `Cost.lean` (`lem:lambda` in the fine form), `ClassVerifier/ClassMain` | **adapt**, nearly verbatim; LP in the role of the decider; "reject" is the constraint list `{J}` | 2–4k incl. class |
| §3.1–3.3 (2079–2886) | ≈800 | normalized `p`-norms, partial isometries, near bijections, corners, distances and inconsistency, data processing | `Distances`, `Closeness`, `CrossConsistency`, `Disagreement`, `POVMMix`, `Pasting` (bipartite, state form); `Dilation.lean` (Naimark, isometry form); vendored `Orthonormalization` | **mostly not needed** on the bipartite route; the repository's calculus is used instead; near bijections only arise on Route B | 0.5–1k |
| §3.4 (2887–2983) | ≈100 | data processing of permutation strategies, `cor:encodings` | nothing (`SyncPushQ.lean` keeps PCC under any classical post-processing) | **new**; the engine of every ZPC-completeness proof | 1–2k |
| §3.5 (2984–3163) | ≈180 | product, sum, augmentation, double cover, `lem:sum-zpc` | `TensorPower.lean` (`tensorPow`, `isPCC_tensorPow`), `GameAdapt`, `GameDouble` (the bipartite reading, not the paper's double cover) | **new** for binary products/sums and ZPC closure; the double cover is not needed on the bipartite route | 1–1.5k |
| §3.6 (3164–3238) | ≈75 | general strategies, `Fact` 3227 (almost-synchronous rounding) | blueprint `thm:almost-sync` (hard, #22/#23 open) | **not needed** | 0 |
| §3.7–3.8 (3239–3965) | ≈730 | Pauli group over `F₂`, codes (Justesen), de la Salle's semi-stability (`Fact` 3495, cited), the generalized Pauli basis game and its analysis | `Weyl*.lean` at `F = ZMod 2`, `GowersHatami` (without dimension control), `LCS/MagicSquare`, `QLD/Anticomm` (Magic Square anticommutation in a bipartite model), `commutation_analysis` | **not needed on Route A**; on Route B 10–18k, including two cited results | 0 / 10–18k |
| §4 (3966–6878) | ≈2,900 | question reduction: introspection game, conditionally linear maps, `QueRed_h`, typed schemes, detyping, padding, `TypedQR_h`, `thm:h_level_question_reduciton` | `Foundations/Introspection` (36.8k; `Types`, `TypeGraph`, `Honest*`, `HidingRigidityIteration`, `AuxiliaryDualKernel`, programs), `Background/Introspection` (7.9k, `Introspection.seven`), `CL/*` (9.2k; typed sampler, detyping 4.6k), `thm:qld` (34k + 126k vendored) | **Route A: re-present** the repository's introspection verifier as a TNFV; soundness transported; ZPC completeness new. **Route B**: the paper's construction on its own Pauli basis game | 13–22k / 45–75k (with §3.7–3.8) |
| §5 (6878–11078) | ≈2,800 | answer reduction: purification, oracularization, triangulation, decoupling, the output indicator `L*`, a 6-decoupled Cook–Levin for it (sketch), the 23-block degree-9 PCP, the seeded low-degree game and its soundness (cited), `AnsRed`, `PartialAnsRed`, `thm:main_ans_red` | `TM/CookLevin` (13k, tableau and describers), `SAT/*` (8.6k: zero basis, Schwartz–Zippel, encodings, circuits), `LIDT.CL.clGame` = the paper's `LowDegree(d,q,m,k)`, `LIDT.Simul.clSoundness` = `thm:ldc-soundness`, `thm:oracularization` (seeded, 24√ε), `CL/Product`, the AR construction/cost patterns (4.5k) | **new construction**, components reused; the one large sketched step is the Cook–Levin for `L*` | 25–40k |
| §6 (11078–11661) | ≈400 | anchoring, `k`-fold tailored product, `claim:alg_parallel_repetition`, BVY (cited), `thm:repetition` | vendored `quantumValue_repeat_le`, `Repetition ℓ` structure, `Repeat/*` programs (4.8k), `TensorPower` | **adapt**: tailored product, ZPC completeness, LP^rep program; no anchoring | 2.5–3.5k |
| §7 (11661–11899) | ≈240 | the compression theorem from the three stages: parameters, accounting, value chain | `Pipeline/Compress.lean` + `Margin.lean` (1k), `PolyBounded` | **adapt**; a third machine in every accounting line | 1.5–2.5k |

## 4. The design decisions

### 4.1 Value form, bipartite value, direct repetition

What the paper's text supports. Its compression theorem (II:1852, II:5643) and parallel
repetition theorem (II:11103) state soundness as entanglement bounds; its question reduction
(II:5712) and answer reduction (II:6883) state both a value clause and an entanglement
clause; §7 uses only the entanglement clauses. Remark II:1876 says the value-form
statements are what the proofs give. The entanglement form needs (a) `thm:bvy` (II:11425,
Bavarian–Vidick–Yuen Theorem 6.1), cited with a "same dimension" reading that the paper notes
is "not immediate at all" (footnote II:11431); (b) `Fact` II:3227, the rounding of an
`n`-dimensional general strategy to an `n`-dimensional synchronous one on games with
proportional loop mass, given as a proof idea citing Vidick 2022 — the live form of the
almost-synchronous theorem, since §6.2 (II:11293–11371), which quoted Vidick's Corollary 3.3
as `thm:synchronous`, is inside a `comment` block; (c) dimension bookkeeping through every
extraction, including de la Salle's near bijections.

What the repository has instead. Every soundness clause of its pipeline is stated and proved
in the bipartite value for all tensor-product strategies (since Phase 1 of the `MIP^co`
track, for the projective strategies of a bipartite model, with matrices as an instance), the
repetition theorem is the vendored uniform exponential one (`thm:direct-repetition-q`, value
form, no dimension control, no anchoring), and the halting fixed point has Lin's search
branch (`Halting/Paper/Decider.lean`, branch 2: the lower semidecider of `val* > 1/2` run on
the verifier's own description) in place of the paper's base case `2^{2^{λn}−1}`.

The decision: **state and prove the tailored pipeline in the bipartite value, with ZPC
completeness.** Consequences:

- Nothing of §3.6, §6.1–6.2 or `thm:bvy` is needed; #22/#23 stay off the critical path, as
  they are for JNVWY.
- No entanglement bound is tracked; `entRequirement` stays unused. The blueprint records the
  deviation as `rem:entanglement-form` does, and the paper's Remark II:1876 is cited as the
  authority that the value form is the proofs' content.
- The double cover disappears: a bipartite game is its own double cover, so the paper's
  answer-reduction clause "then `DoubleCover(V_n)` has value `≥ 1 − δ`" (II:6930) becomes a
  clause about `V_n`'s bipartite game, which is what the repository's answer reduction
  concludes already. The halting layer's completeness slot, "a perfect PCC strategy of the
  doubled game" (`Verifier.HasPerfectPCC`), becomes "a perfect ZPC strategy of the doubled
  game", and `SyncStrategy.double`/`isPCC_double` get ZPC versions.
- The main theorem's soundness is the general value's; the synchronous clause of II:1505 and
  paper I's hypothesis follow by one lemma.
- The *soundness proofs* of the new tailored constructions are written in the repository's
  bipartite calculus, not transcribed from the paper's tracial one (§3.1–3.3). Where a
  construction is a re-presentation of a repository construction (Route A for question
  reduction, the seeded low-degree test in answer reduction), the soundness is transported
  through the identification of games rather than re-proved.

### 4.2 Which Pauli basis test, and whether the repository's introspection can be re-presented

This is the decision that moves the estimate, and Phase 0 settles it.

Paper II's question reduction uses its own Pauli basis game (II:§3.8): `O(n²)` constant-size
commutation and Magic Square gadgets glued to two `k`-bit Pauli vertices through the rows of
an `[n, k, d]` binary code, sound by de la Salle's semi-stability of the Pauli group
(`Fact` II:3495, cited; its proof needs a dimension-controlled Gowers–Hatami theorem, a
spectral gap of the Cayley graph of `F₂^k` and a finite Stone–von Neumann identification —
none in the repository, whose `gowers_hatami` has no dimension control), with a
polynomial-time asymptotically good code (`Fact` II:3486, Justesen). The repository's Pauli
basis test is JNVWY's `qldGame` over `F_q`, `q = 2^t`, sound by `thm:qld`
(`QLD.soundIn_of_lidt`, 34k lines on 126k vendored). The paper says (II:5228–5233) that the
combinatorial game of `QueRed` is JNVWY's question reduction and that JNVWY's soundness proof
covers it; the §4 reader confirmed that the repository's typed introspection game — types
`introspect | sample | read | hide k`, the edge list of `TypeGraph.oriented`, the hiding
chain of `HidingRigidityIteration`, the in-decider perpendicular map of
`AuxiliaryDualKernel`, the honest strategy `Σ_z F^Z_z ⊗ P^{S(z)}` of `Honest*` — is that
game, differing from the paper's only in the Pauli sub-game and in the presentation.

**Route A (recommended).** Define the tailored question reduction as a *tailored
presentation* of the repository's introspection verifier: the same introspective sampler
`S^intro_λ` (depends on `λ` only, as the paper's `S^λ_qr` must), an answer-length calculator
reading the type, and a linear-constraints processor `LP^intro` whose output, decided by the
canonical decider, accepts exactly when the repository's introspective decider accepts with
the input's canonical decider in the role of `D`. Then soundness is `Introspection.seven`'s
clause transported through the equality of games (one lemma per level), and what is new is
(i) the two programs and their correctness against the existing typed predicate
(`TypedPredicate`, `Decision*`), (ii) their cost and description bounds, (iii) ZPC
completeness: the repository's honest strategy is a signed-permutation strategy with the
introspected questions and the `Z`-basis outcomes diagonal — `wX` is a permutation matrix,
`wZ` a `±1` diagonal, the low-degree answers are linear data processing of `Z`/`X` outcomes
(`cor:linear_data_processed_PVM_is_ZPC_and_left_multiplication`, II:2938), and commutation
along edges is the existing `HasPerfectPCC` completeness. Two facts must hold for this, and
Phase 0 checked them before anything was built (the verdict follows the list):

- every check of the repository's introspective typed predicate is `F₂`-linear in the
  unreadable answers once the readable ones are fixed, where "readable" is the introspected
  questions, the sampled seeds and the `Z`-basis outcomes, and "unreadable" the `X`-basis
  outcomes and the input's linear answers. Expected: the low-degree checks are `F_q`-linear in
  coefficient vectors (hence `F₂`-linear under the self-dual basis of `WeylBinary.lean`), the
  Pauli consistency and Magic Square checks are linear, the sampling check `x = S^A(z)` has
  both sides readable (the paper's own device, II:5081), and the hiding checks
  `ν = (S^x)^⊥(χ)` are linear in `ν, χ` with coefficients computed from the readable `x`
  (`registerDual`), which is exactly the paper's controlled-linear structure;
- the honest strategy's readable observables are diagonal and all of its observables are
  signed permutations. Expected from the formulas in `HonestPauli*` and `HonestCore`.

If both hold, question reduction costs 13–22k lines (§6.2) and §3.7–3.8 of the paper are not
formalized at all; the blueprint says that the Pauli basis test is JNVWY's and cites the
paper's remark II:5228 for the equivalence of the combinatorial games.

**Phase 0 verdict (2026-10-05): both hold, so Route A stands.** Read from the Lean, not the
paper, by two readers whose reports cite file and line for every claim:

- *Controlled-linear: yes.* The compiled introspective decider
  (`DecisionCompiler.decider` → `untypedKernel` → `DecisionKernel.program`) is tied to the typed
  predicate in quotient form (`AuxiliaryQuotient.check`, `TypedQuotientPredicate.lean:104`; the
  legacy `TypedPredicate.check` follows from it after `decodeAnswer`, `check_sound`) in two
  directions, not by an equality: `program_sound` (`DecisionKernelSoundness.lean:31`, kernel
  acceptance gives the quotient check on the decoded answers) and `program_complete`
  (`DecisionKernelComplete.lean:195`, the converse under `PrefixGuard.holds` on both answers,
  `sourceOutput`, `PauliFormatted` and the question lengths). The kernel's extra checks — the
  canonical and length checks, the prefix guard (`GuardedAuxiliaryProgram.lean:28`), and the
  router's unconditional acceptance off the edges (`DecisionCompilerRoute.lean:47`) — read only
  readable fields and lengths, so `LP^intro` reproduces them, emitting `rejectConstraint` where
  they fail. Every check of it is either a predicate
  on readable fields and the questions alone, or `F₂`-affine equations on the linear fields
  whose coefficients are computed from readable fields and the questions. The nonlinear maps —
  the sampler's `CLFun.eval`, `outputPrefix`, `prefixRegister`, `factorOfPrefix`,
  `stageLinear`, the Pauli test's `γ`, `lineParam`, `χ`, `rep` — are applied only to readable
  fields or to questions; the maps applied to linear fields are `proj`, `registerDual`,
  `stageDual`, `dualReadout`, `project`, evaluation of `ldEnc`, `LinePoly.eval`, `x ↦ tr(x·r)`
  and the identity. The readable fields: the question field `y` of Introspect, Read and Hide
  answers, the seed `z` of Sample answers, and the `Z`-basis Pauli answers; the linear ones: the
  duals `yp` (Read, Hide), the tail `x` (Hide), the `X`-basis answers. Every rule of the Pauli
  basis test (`QLD.accepts`) is a system of `F₂`-affine equations over all answer bits with
  coefficients from the questions, so it is controlled-linear under any split.
- *Signed permutations: yes, given that the input strategy is one.* `wX a` is the permutation
  matrix of the translation by `a` (`Weyl.lean:159`), `wZ b` a `±1` diagonal (`:163`); the
  `X`-basis projectors are Fourier averages of translations, never a field Fourier matrix; the
  only nonlinear post-processing (`CLFun.eval`, `truncate`) acts on `Z`-basis outcomes, which
  keeps them diagonal; the input enters as controlled direct sums `Σ_z |z⟩⟨z| ⊗ U^{x(z)}`
  (`HonestCore.lean:126`); and the Magic Square extension `HonestMagicSquare` uses `I, X, Z`
  and `ZX = [[0,1],[-1,0]]` on the added qubit, all signed permutations. Commutation along
  edges is already proved (`auxStrategy_isPCC`, `HonestCompleteGame.lean:95`, and the
  `strategy_isPCC` of `SourceReindex`, `SourcePadding` and `HonestMagicSquareGame`). The repository
  states none of this: Phase 3 supplies the closure lemmas (Kronecker products, products of
  commuting elements, `submatrix e e`, linear data processing `Σ_e sgn(φ e) proj w e = w(c_φ)`,
  diagonality under any function, controlled direct sums, constants).

Four refinements the readers found, which Phase 3 must respect:

1. **The input's answers must be padded to constant lengths first**, as the paper does
   (`Padding`, II:6219–6294): the introspective decider reads the input's answer `a` as a
   variable-length, self-delimiting string (`|a| ≤ R`), while a tailored question has a fixed
   answer length. The padded `a` has a readable and a linear part whose split is keyed to the
   introspected question (`y` for Introspect and Read, `L_w(z)` for Sample), which sits in
   readable answer fields, so the linear-constraints processor computes it by running the
   input's answer-length calculator on readable data.
2. **The Magic Square and Pair answers must be unreadable**: six of the nine Magic Square cells
   (`A⊗1, 1⊗X, A⊗X, B⊗X, A⊗Z, (AB)⊗(ZX)`) are not diagonal. The readable set is a subset of the
   `Z`-type outputs.
3. **The repository's other Magic Square strategy is not a ZPC strategy.** The Mermin–Peres
   grid of `LCS/MagicSquare/Strategy.lean` uses `Pauli.Y = [[0,-i],[i,0]]`, not a signed
   permutation; the non-vacuity witness of Phase 1 is built from `HonestMagicSquare`'s grid or
   the paper's 8-point strategy (II:1351), not from it.
4. **Only the Pauli test is over `F_q`.** The introspection registers are already over `F₂`
   (`ι = Fin Q`, `F = CL.𝔽₂` in `DecisionKernelInput.lean`); the Pauli answers are over
   `shoupBinField` and reach the hiding checks through `project` (the self-dual coordinates,
   `registerVector`). So the `F_q → F₂` matrices are needed for `QLD.accepts` and `project`
   only, and a dual equality `stageDual (k+1) y u = stageDual (k+1) y v` becomes one row per
   generator of `ker (stageLinear P k y)` (`registerDual_eq_iff_dot`,
   `AuxiliaryDualKernel.lean:74`), the generators computed by the existing
   `kernelGeneratorsProg` (`LowDegree/BinaryKernel.lean:96`).

And for Phase 4: the seeded low-degree game `LIDT.CL.clGame` is `F_q`-linear in the answers given
the questions (its only non-answer data are `χ(s)`, the line direction, the base point delivered
in the question and `lineParam`), so it is tailored as it stands; the repository's answer
reduction is linear in its steps 1–4 and nonlinear only in step 5, the PCP identity
`A₅ = φ(z)·∏_{i<5}(A_i − z_{5m+i})` (`PcpAlgebra.TypedAccepts`), which is exactly what the
paper's tailored PCP replaces.

**Route B.** Formalize the paper's game: `Sym_±` and `WH_k` over `F₂` (`Weyl.lean` at
`ZMod 2`), an explicit code family (a Reed–Solomon ∘ Hadamard concatenation is the cheap
choice, since only `n = poly(k)` and constant relative distance are used), `Fact` 3495
(5–10k: dimension-controlled Gowers–Hatami, the spectral gap, the isotypic identification),
the game and its analysis (3–5k), then the paper's `QueRed_h` construction, programs and
soundness in the paper's near-bijection vocabulary (45–75k in total for §4 with its §3
inputs). Route B is
also what one would do if the paper's test were wanted for its own sake (its soundness error
`cε^{1/16}` has no `n`-dependence, unlike the low-degree test's).

Either route keeps the repository's sampler interface (`dimension | marginal | linear |
factor`) and computes perpendicular maps inside the decider, as JNVWY does; adding the
paper's `Perpendicular` query would touch every stage of the existing pipeline for no gain.

### 4.3 Answer reduction: a new construction on reused components

The repository's answer reduction cannot be re-presented as the question reduction can,
because its PCP is nonlinear in the answers: the players compute a Cook–Levin tableau of the
decider's run on *all* their answer bits, and the AND of two commuting permutation
observables is not a permutation (II:2893, II:8342–8348). Paper II's §5 is designed around
this: the readable answers carry everything nonlinear (`Π^R`, including the Tseitin factors
and the witness `O` of the decoupled linear system), and the linear answers enter only
through one identity whose left side is affine in `g^L_i(p)` with coefficients read from
`g_0(p)` (II:9040); the assignment checks `g(g+1) = Σ zero_X β` are linear because Frobenius
is `F₂`-linear. The construction is new: purification (II:7762), oracularization of a
tailored game (II:7813), triangulation (II:7952) and 5-decoupling (II:8190) of the *linear
system*, the output indicator `L*` (II:8381), a 6-decoupled Cook–Levin for `L*` with three
answer blocks of different sizes (II:8618, a sketch deferring to JNVWY §§10.2–10.3), the
23-block degree-9 PCP with its `F₂`-affinity statement (II:9112–9155), the `AnsRed` typed
game with four checks (II:10285), `PartialAnsRed` (II:10760) and the parameter chain
(II:10846–11074).

What it reuses: the seeded low-degree game `LowDegree(d, q, m, k)` (II:9793) *is*
`LIDT.CL.clGame` (same three types, same conditionally linear maps, same canonical line
representatives; the selector and the type-pair distribution differ by constants), and
`thm:ldc-soundness` (II:9885, cited to JNVWY's tensor-codes paper and NW19) *is*
`LIDT.Simul.clSoundness` in a bipartite model — the two steps the paper's one-sentence proof
waves at (the seeded distribution with its non-uniform diagonal lines, the multi-codeword
extension) are the repository's `Adapter/` and `Simultaneous/Padding/Extraction.lean`,
already done. The paper's extra conclusions on line answers (II:eq:eval_L_is_close_to_line)
must be derived from the point conclusion (a few hundred lines). The seeded oracularization
whose soundness the paper asserts "works (essentially) the same" (II:7876) is exactly
`thm:oracularization` (24√ε, `OracularModel.lean`). The Cook–Levin tableau, describers with
link conditions (`Link.lean`, `Decoupled.lean`, for two equal answer blocks), the zero basis,
Schwartz–Zippel, the encodings `Ind`/`Res`, the circuit arithmetization, the self-dual basis,
the CL product samplers and the construction/cost patterns of `Background/AnswerReduction`
all transfer. The soundness proof is written in the bipartite model (two perturbations, the
indifference pruning, Schwartz–Zippel for consistency), the paper's shape being close to the
repository's `SoundPoly` route.

### 4.4 The verifier type

A `TailoredVerifier ℓ` is a `CL.Sampler ℓ` plus two programs, the answer-length calculator
and the linear-constraints processor; the canonical decider is one fixed costed program
(by analogy with `Halting/Wrapper*.lean`, about 1k lines with its cost). `Verifier.ofTNFV`
packages it as a `Verifier ℓ` so that `Verifier.game n T`, `valStar`, `IsBounded`,
`freeze`, the tabulation and the whole halting layer are inherited; the answer alphabet
stays `Answers T` with the canonical decider rejecting wrong lengths, which is the
repository's established reading of per-vertex alphabets. (As built in P1b, §5: the program,
`canonProg`, and its acceptance law are in, its cost is deferred, nothing planned consuming it;
and the halting layer is not inherited but paralleled, P1c.) The paper's answer-length bound
`Λ(n) = TIME(L; n)` (unary output) becomes an explicit parse-length parameter, as
`Repetition.parseBound`. λ-boundedness keeps the repository's relative-cost reading
(`n^λ (|d|+1)^λ`, `n ≥ 2`), which `defn:h-level_NFV` (II:5626) needs anyway (its "all `n`"
is unsatisfiable at `n = 1`). The paper's "never decodes to `error`" clause of the
answer-length calculator (II:1863) is a new field, spent once, in `lem:VMLn`(3).

A `TailoredGapCompression` is `GapCompression` with the second λ-only component (the
length calculator, with its program, time and no-error fields), completeness in
`HasPerfectZPC` and soundness unchanged; `TailoredIntrospection`, `TailoredAnswerReduction`
and `TailoredRepetition` are the three stage structures in the same vocabulary, and
`ofTailoredPipeline` their composition.

### 4.5 `F₂` against `F_q`

The paper works over `F₂`; the repository's Pauli and low-degree machinery over `F_q`,
`q = 2^t`. Under a self-dual basis (`WeylBinary.lean`, `lem:pauli-binary`;
`SAT/EffectiveSelfDual.lean`) an `F_q`-linear check on field elements is `t` `F₂`-linear rows
on their bit representations, which is how the paper itself presents its low-degree game
(II:9870, `fact:basis_F_q_over_F_2`). So the tailored presentations of the repository's
constructions write their constraints bit by bit through `BinField`, and no construction is
moved to `F₂`.

### 4.6 Synchronous against bipartite

The paper's strategies are synchronous (`SyncStrategy`); the repository's analyses are
bipartite. The seams: `SyncStrategy.toTensorProductStrategy` (maximally entangled state,
transposed second measurement) and `syncValue_le_quantumValue` carry completeness and the
final soundness clause across; `Game.doubled` is the bipartite reading of a synchronous
verifier game and is where `HasPerfectZPC` lives. Nothing synchronous is needed on the
soundness side.

## 5. Phases and work packages

Each phase ends in a merged pull request and a sharper conditional theorem, as the `MIP^co`
track did: the main theorem is stated and proved from a hypothesis structure in Phase 1, and
each later phase discharges one stage. Sizes are new Lean lines, Route A; PR counts are by
analogy with the stage campaigns of September 2026 (`AR-1`…`AR-6`, `O1`…`O5`).

**Phase 0 — the two checks and the statements (one week, no Lean merged).**
(a) Read the repository's introspective typed predicate and honest strategy against the two
Route A conditions of §4.2; record the verdict in this file. (b) Read `clGame` and the AR
output format the same way (the seeded low-degree game is all-unreadable and linear;
expected trivial). (c) Fix the interface: `TailoredVerifier`, `Verifier.ofTNFV`, the
canonical decider's format, `TailoredGapCompression` and the three stage structures, written
as a statements file compiled against the library. (d) Write the blueprint chapter's
skeleton (`09_tailored.tex`): the definitions and theorems in the forms to be formalized,
with the paper's statements quoted and the deviations of §2.2 and §4.1 said in remarks.
(e) Open the tracking issue and the sub-issues per phase.

**Phase 1 — tailored foundations and the conditional main theorem (9–15k; 3–4 PRs).**
Signed permutations as combinatorial data with a matrix interpretation (`Equiv.Perm Ω`
with signs; Kronecker, products, `−Id`, diagonal `±1`), the three forms of an `F₂^S`-PVM and
the Fourier transform between them (on `pvmObs`, `Linearity.lean` and `LCS/Strategy`),
`IsZAligned`, ZPC, `ZPC → IsPCC`, the data-processing corollaries of II:§3.4; tailored
games, `TailoredGameData` and `toGame`, the canonical decider as a costed program,
`TailoredVerifier`, `ofTNFV`, λ-boundedness, the `n`-th game; binary products and sums with
`lem:sum-zpc`; the Magic Square as a ZPC strategy (the paper's 8-point strategy, II:1351, or
`HonestMagicSquare`'s grid — not the Mermin–Peres grid of `LCS/MagicSquare/Strategy.lean`,
which uses `Y`) as the non-vacuity witness. Then the halting protocol from
`TailoredGapCompression`: `Halting/Paper/*` with the linear-constraints processor as the
fixed point, `{J}` for "reject" and the empty list for "accept", `lem:dhalt-values` as
`accepts_iff`, the downward induction with Lin's branch, `lem:lambda` for three machines, the
class verifier; `TMIP* ⊆ RE` (done through the quantum value, not by enumeration; see P1d);
`tailored_halting_reduction_of : TailoredGapCompression → TailoredHaltingReduction` and the
class theorems conditional on it. Deliverable: the whole logical skeleton, with the
compression theorem as the one hypothesis.

A correction to §3's reading of the halting layer, found in Phase 0: the headline
`HaltingGameValue.halting_reduces_to_gameValue` is proved through the *criterion* route
(`Halting/CompressorProgram.lean`, `Halting/Reduction.lean`'s obligations, the tabulation
`tab`), and `Halting/Paper/*` proves only the polynomial-time class theorems
(`re_subset_mipstar`, `mipstar_eq_re`, through `ClassMain.lean`). Either route reaches
`TailoredHaltingReduction` only through a tabulation of tailored verifiers — a
`TailoredGameData` from a tailored verifier at a fixed index: the weights by enumerating the
sampler's seeds, the lengths by running the answer-length calculator on every question, the
constraint table by running the linear-constraints processor on every readable assignment —
which is new work in Phase 1. The paper route stays the choice, as it also gives the
polynomial-time class theorem; its files `Build.lean`, `Size.lean`, `Cost.lean` and
`ClassVerifier.lean` are hard-wired to the shape of `F` and `body`, so the tailored halting
protocol is a parallel set of files, not an edit of these.

**Phase 1 slices.** Five, in this order; P1a–c landed together (#286).

- **P1a — permutation strategies (done, 1.4k lines).** `SignedPerm Ω`, the group
  `Sym(Ω) ⋉ F₂^Ω`, with an injective matrix homomorphism into the unitaries: the sign flip,
  `±1` diagonals, products of signed sets as Kronecker products, relabellings as reindexing;
  an involutive signed permutation matrix is self-adjoint, a diagonal one a `±1` diagonal. The
  three forms of an `F₂^k`-measurement in any complex `⋆`-algebra (`MIPRE.IsPVMIn`): the Fourier
  transform is a projective measurement, by induction on `k` from products of commuting
  measurements; the eigenvalue relations and the inverse transforms in observable and
  representation form; commutation and diagonality pass from observables to projections; affine
  and diagonal data processing (Claims II:2902, II:2918). The perfect-strategy criterion and the
  constraint lemma (Claim II:2870), with the canonical decider's `Satisfies` read as
  `⟨α, a⟩ + ⟨β, b⟩ = γ`. `lem:zpc-pcc`, on the doubled games, with doubling of strategies. And
  the non-vacuity witness: the Magic Square, tailored with every variable linear, has a perfect
  ZPC strategy, the paper's 8-point one; its group identities are checked by `decide` in
  `SignedPerm (Fin 4)` and transported by the matrix homomorphism. `lem:sum-zpc` moves to
  Phase 2: it is the binary case of the completeness of the tailored product, which Phase 2
  defines directly in its `k`-fold form, as `Game.repeat` is.
- **P1b — tailored verifiers as verifiers (done, 0.7k lines; its cost deferred).** The outputs
  of the answer-length calculator and of the linear-constraints processor are read totally — a
  length as the length of the output's spine, in unary as the paper writes it (II:1781), a
  constraint list elementwise — so that the canonical decider never meets a malformed output.
  The canonical decider is a program, `canonProg L LP`: four runs of `L`, one of `LP` and a
  polynomial-time check, as steps that push their outputs onto a state. `canonProg_accepts` is
  its acceptance law and `tgame_accepts_iff` says that it decides the `n`-th game.
  `TailoredVerifier.ofTNFV` is `Verifier.ofSamplerDecider` at it. Identifying
  `(V.ofTNFV U).game n T` with `(V.tgame n).toGame` for `T` above the answer lengths
  (`ValueModel.extendAnswers`) gives `valStar_ofTNFV`, and the doubled games, with
  `lem:zpc-pcc` and zero extension, `hasPerfectPCC_ofTNFV`. **Deferred: the canonical decider's
  cost.** Its one consumer would be `Verifier.IsBounded (V.ofTNFV U)`, through
  `Verifier.ofSamplerDecider_isBounded`, which wants `canonProg L LP` to have polynomial cost on
  every input, malformed ones included, so with a total parsing of the input in front of it. No
  planned statement uses that: the track's λ-boundedness (`TailoredVerifier.IsBounded`), the
  stage contracts, the halting protocol of P1c and the class statements of P1d bound the three
  programs `S`, `L`, `LP`, as the paper's II:1800 does. The cost is added if a later phase
  applies a theorem about bounded `MIPRE.Verifier`s to `ofTNFV`.
- **P1c — the halting protocol (done, 1.2k lines).** `MIPRE/Tailored/Halting/*`, parallel to
  `Halting/Paper/{Decider,Induction,Size,Cost,Main}.lean`, from a `TailoredGapCompression`. The
  linear-constraints processor of `V^{M,λ}` is the Kleene fixed point (`lpProg`): `[]` once `M`
  has halted, `[rejectConstraint 0]` once the search has, otherwise the compressed processor of
  its own programs through the universal machine. `lem:dhalt-values` is `lp_runs_iff`, and
  then, by level: a perfect ZPC strategy from `hasPerfectZPC_of_accepts_zero` (where
  `len_total` is spent), value `0`, or the compressed verifier's games (through the new
  congruence lemmas `TailoredVerifier.hasPerfectZPC_congr`, `valStar_congr`: same sampler and
  answer-length calculator, same constraints). The downward induction with the search branch
  needs no answer bound, a tailored game's answers having the lengths its calculator gives
  them. `lem:lambda` for three programs (`exists_lamBound`, `Lam0`): the processor is run as it
  is, so there is no wrapper layer. `halting_tailored`: for `λ ≥ Λ₀ + 4|M|`, at the level
  `C = max C₀ 2`, a perfect ZPC strategy if `M` halts and value at most `1/2` if not. **The
  search program is a hypothesis**, `SearchSpec`: on the description of a `λ`-bounded tailored
  verifier `(S^λ, L^λ, P)` it halts exactly when the value at level `C` exceeds `1/2`. The
  existing halting layer gets its program from its tabulation (`exists_semL`); here it comes
  from the tabulation of P1d.
- **P1d — tabulation, transports, the conditional theorems (done, 2.2k lines).**
  - *The bridge* (`Tailored/Data/Bridge.lean`). A `TailoredGameData`'s synchronous game is one
    of the foundations, with `gameValue = syncValue ≤ val*`; a ZPC strategy of a description is
    a synchronous strategy of the same value, so a perfect one gives value `1`.
  - *The conversion* (`Data/Convert.lean`). A description is a `GameData` whose answers are the
    numbers below `2^Λ`, read bitwise; the map is primitive recursive and keeps the quantum
    value.
  - *Presentations* (`Data/Presents.lean`). A description presenting a tailored game with no
    weight on its loops (a doubled game) has its quantum value: the two read answers
    differently (vectors padded with zeros, strings of exact length) and the description also
    rejects unequal answers at a loop, neither of which matters off the support. A perfect ZPC
    strategy of the game, padded with identities, is one of the description.
  - *The tabulation* (`Halting/Tabulate.lean`). The doubled questions are the vertices; the
    weights are those of `Halting.tabOf`; the lengths and constraints come from running the
    calculator and the processor under the budget `n^λ (|d|+1)^λ`. It is primitive recursive,
    and it presents the doubled game of a `λ`-bounded verifier at every `n ≥ 2`. The marginals
    are queried at the sampler's own level and normalized to the dimension. The normalization
    matters only at level `0`, where the questions are empty and `runs_marginal` says nothing.
  - *The search program* (`Halting/Search.lean`), from the lower semicomputability of the
    value, so `halting_tailored` holds with no hypothesis beyond the compression.
  - *The reduction* (`Halting/Reduction.lean`). `tailored_halting_reduction_of`, with soundness
    even in the quantum value (`tailored_halting_reduction_quantum_of`). The processor's
    description is built in polynomial time from the three shapes of `Halting/Paper/Build.lean`,
    which are generic in the body.
  - *The computable class* (`Tailored/Class.lean`). `TMIPStarComputable`; `TMIP* ⊆ MIP* ⊆ RE`
    unconditionally; `TMIP* = RE` from a compression.
  - **`TMIP* ⊆ RE` changed route.** It does not enumerate signed-permutation strategies. The
    class's soundness clause is in `val*`, so membership is `val* > 1/2`, which is r.e. by
    `lem:value-lower-approx`; no new semidecider is needed.
  - **The statement got a definition node.** In the blueprint `TailoredHaltingReduction` moved
    from `thm:tmip-re` to `def:tailored-halting-reduction`. `thm:tailored-halting` uses the
    proposition, and `thm:tmip-re` is not proved yet; citing it from a proved node would mark the
    proved node as resting on an unproved one.
- **P1e — the polynomial-time class (next).** The second layer of §2.2: `TMIPStar`, with a
  polynomial-time tailored verifier (the paper's clause (1), sampling and evaluation in
  `poly(|z|)`), its tabulation into the computable class, and the class verifier from
  `V^{M,λ}` at the level `C`. Together they give `TMIPStar = IsRE` from a compression, as
  `Halting/Paper/{ClassVerifier,ClassMain}.lean` and `ClassMIPStarTab.lean` do for `MIPStar`.

**Phase 2 — repetition (2.5–3.5k; 1–2 PRs).** `lem:sum-zpc` (II:3086), moved from Phase 1, as
the case `k = 2` of what follows. The `k`-fold tailored product (constraints
zero-padded to the global length and concatenated, II:11377), ZPC completeness on
`tensorPow`/`isPCC_tensorPow` with the Kronecker closure, the repeated linear-constraints
processor as a program with its cost (the sampler and the parsing are `Repeat/*`), the
identification with `(V.game n B).repeat k`, soundness from
`quantumValue_repeat_le_soundBound`. `TailoredRepetition` inhabited.

**Phase 2 slices.** Two pull requests.

- **P2a — the product and its two clauses, from a specification of the programs (done,
  1.5k lines).** `MIPRE/Tailored/Repeat/{Game,Strategy,Verifier}.lean` and
  `MIPRE/Background/Tailored/Repetition/Soundness.lean`. `TailoredGame.repeat`: the variables
  of `x⃗` are the coordinates' readable variables in order, then their linear ones
  (`varEquiv`), and each coordinate's constraints are padded with zeros over all the variables
  (`padCons`: the constraint cut by `take`/`drop` into its five blocks and each put at its
  place, with no length test, so a malformed constraint pads to a vector of the wrong length and
  the program can compute the definition literally); `repeat_accepts_iff` is the acceptance law,
  through `satisfies_pad_blocks` on thirteen blocks.
  `PermStrategy.repeat`, the tensor power through slot embeddings `1 ⊗ ⋯ ⊗ M ⊗ ⋯ ⊗ 1` (algebra
  maps preserving signed permutations and diagonality, on `ℂ^{m^k}` after reindexing), whose
  measurement is the tensor product of the coordinates' (`proj_repeat`, the commuting Fourier
  factors regrouped by coordinate); a perfect strategy never produces a rejected pair on an edge
  (`proj_mul_eq_zero_of_value_eq_one`), so the power is perfect; `PermStrategy.comap` pulls a
  strategy back along a map of questions that keeps lengths, edges and acceptance, with identity
  observables where it does not, which gives the doubled product (`repeat_doubled`) and the
  repeated verifier. `lem:sum-zpc` is not needed as a separate node: it is `k = 2`. The
  repeated verifier `repTV` has the existing `Repeat.repSampler` and two programs; `RepSpec`
  states what they must output (at a question whose coordinates all have their lengths, the
  sums; nothing elsewhere; the product's constraints exactly when every coordinate's processor
  halts), and from it `RepSpec.hasPerfectZPC` and `RepSpec.valStar_le`, the latter through
  `quantumValue_le_of_coarse` (merge the answers at each question along a map that may depend on
  the question) onto `(V.tgame n).toGame.repeat k` and `quantumValue_repeat_le_soundBound`, the
  factor `2` between the two lengths and the answer length absorbed into the constant
  (`c = repConst / 2`). Blueprint `def:tailored-product`, `lem:tailored-product-accepts`,
  `lem:tensor-power-zpc`, `def:tailored-rep-spec`, `thm:tailored-rep-from-spec`.
- **P2b — the programs (done, about 3.3k lines).** `MIPRE/Tailored/Repeat/{Calls,Lists,LenProg,
  LenCost,DomTools,LpLists,LpProg,LpSpec,LpCost}.lean` and
  `MIPRE/Background/Tailored/Repetition/Stage.lean`. Each program is a chain of `Calls.seq`
  stages: `PolyTimeFun`s, the existing `dimProg` and `toUnaryProg` for `k` and `s` in unary
  (`k = 2^{τ(|λ|+|n|)}` has no fixed-polynomial unary form), and `Calls.mapCall`, the generic loop
  running a stored program on every query through the universal machine, with its run
  (`mapCall_runs`) and inversion (`mapCall_inv`). Each core has a run lemma with an explicit
  stage-by-stage cost and an inversion lemma; `repSpec` gives `RepSpec` at every index;
  `repLen_timeBound`/`repLp_timeBound` dominate the costs (`DomTools`: `dom_poly` for the
  polynomial-time stages, `dom_powK` for a size linear in `|d|` to the power `R.k` once
  `10^{R.k} ≤ W`); `tailoredRepetition` inhabits the contract. Blueprint
  `def:tailored-rep-programs`, `lem:tailored-rep-programs`, `lem:tailored-rep-programs-time`,
  `thm:tailored-rep`. The plan as written: the repeated answer-length calculator (on `(n, x, κ)`: the dimension
  query, `k` in unary, the blocks of `x`, the input's calculator on each through the universal
  machine, the sum in unary) and the repeated linear-constraints processor (the four lengths of
  every coordinate, the blocks of `a^R` and `b^R` by the readable lengths, the input's processor
  on every coordinate, then the padding of each coordinate's constraints), total on malformed
  inputs, with `RepSpec` at every index and their running times in the shape of
  `repDecider_timeBound`; then `TailoredRepetition` inhabited (`thm:tailored-rep`). Everything
  between the calls to the input's programs is pure list manipulation, which the closure
  library's `PolyTimeFun` combinators (`Cost/Fold.lean`) give with their bounds; the calls go
  through one generic loop running a stored program on every element of a list.

**Phase 3 — question reduction (13–22k on Route A; 5–8 PRs).** The tailored presentation of
the repository's introspection verifier: `L^intro` by type; `LP^intro` as the constraint
lists of each check family (the low-degree, Pauli and Magic Square checks bit by bit through
`BinField`; the sampling, reading and hiding checks with their readable selectors; the input's
constraints re-indexed); correctness against the existing typed predicate; costs and
description bounds in the shape of `Introspection.budget`; ZPC completeness of the honest
strategy; soundness transported from `Introspection.seven`; padding (II:6223) and the
tailored detyping bookkeeping on `CL/Detyping*`. `TailoredIntrospection` inhabited. On
Route B this phase is 45–75k and starts with II:§3.7–3.8.

**Phase 3 slices.** Seven slices, eight or nine pull requests. The design comes from three readings of the Lean
(2026-10-05, recorded in §4.2 and below); the paper's §4 was not reread for them (arXiv was not
reachable from the session), so every slice that formalizes a paper statement checks it first.

What the readings settled. The completeness of `seven` (`CanonicalComplete.output_hasPerfectPCC`)
builds its strategy explicitly, as a chain of named constructions on the input's strategy `R`:
`SourcePadding.strategy` (questions pulled back along `firstEmbedding`), `SourceReindex.strategy`,
`BinaryComplete.strategy` (`op` on `Space = (Seed × Fin R.d) × Fin 2`, conjugated by the
permutation `Fintype.equivFin`), the relabellings `pccToExplicit` and `originalPCC`,
`mergeAnswersByQuestion` along `encodeAnswer`, then `Detyping.complete` (a constant answer on the
questions that do not decode), a relabelling by `vectorEquiv` and a zero-extension of the answers.
At a question that decodes, the final measurement is therefore *the sum over the parsed answers
whose encoding is the string* of `registerOp e (op …)`, and every base operator is one of: an
eigenbasis measurement of `wX`/`wZ` coarse-grained along a label (`synOf`, `fibSum`, `proj`), a
computational-basis readout, a controlled sum `readout f z ⊗ R.M(…)` of the input's measurements,
a Magic Square `grid` observable on the ancilla, or a product of these. The input's answers are
variable-length strings in `seven`'s game (`Answers ((2^n)^lam)`, no padding anywhere on the
chain), so the tailored output game, whose answer lengths are fixed per question, is not `seven`'s
game itself but a padded presentation of it: an answer is the readable fields, then the input's
readable answer bits padded to the maximum, then the linear fields, then the input's linear answer
bits padded; `dec` strips the padding and re-encodes with `encodeAnswer`.

- **P3a — the closure toolbox (done, 0.3k lines).** `Tailored/Intro/Encoded.lean`: the bit
  observables `encObs P enc i = ∑_λ (-1)^{enc(λ)_i} P_λ` of an encoded measurement are commuting
  self-adjoint involutions whose Fourier transform is the push-forward of `P` along `enc`
  (`fourierProj_encObs`), commuting with those of any measurement commuting with `P`.
  `Tailored/Intro/Closure.lean`: `wX` is a permutation matrix and `wZ` a `±1` diagonal; the trace
  form is nondegenerate, so an `F₂`-linear bit of an `X`- or `Z`-basis outcome has observable
  `wX c` or `wZ c` (linear data processing, II:2938); any bit of a `Z`-basis outcome is a `±1`
  diagonal; block-diagonal and controlled sums of signed permutations are signed permutations,
  diagonal when the blocks are.
- **P3b₀ — the transports and the base cases (done, 0.5k lines).** `Tailored/Intro/Transport.lean`
  proves the two directions once, for any game `H` presented by a tailored game `G` on the same
  questions: `valStar_le_of_dec` (post-processing along `dec`), and `hasPerfectZPC_of_sync`, a
  perfect PCC strategy of `H` charging only encodable answers, with signed-permutation bit
  observables along `enc` diagonal at the readable bits, being a perfect permutation strategy
  of `G` (`permOfSync`). `Encoded.lean` and `Closure.lean` gain the transports the honest strategy
  goes through (merging along a map, zero-extension, relabelling, an ancilla, control),
  `Input.lean` the input's answer bits (a copied bit is `U(x, j)`, a padding bit `±1`), and
  `Binary.lean` the probe and Magic Square measurements (`½(1 ± O)` read out, `X`, `Z`, the grid).
  What the reading of `seven`'s parsing (2026-10-05) adds to P3b: the questions whose graph view
  does not decode — almost all the weight under the graph sampler — are accepted after length
  checks (`selectedEdge = none`), so they get length `0` and no constraints; the auxiliary
  payload of a question is never read; the Pauli answers have fixed lengths by type (`k`,
  `2k`, `(m+1)k`, `2^m k = Q`, `1`, `2`, `3`); in an auxiliary answer each field is
  self-delimiting (`doubleBits` and a `10` terminator) and the input's answer is the last field,
  of length at most `R = (2^n)^λ`; the same-type check is raw equality, so the re-encoding must
  be injective on formatted answers — `encodeAnswer` is not injective on malformed Pauli answers
  when `k = 3`, so every round-trip lemma carries `fmtOk`/`fits`.
- **P3b₁ — tailored detyping and the layout (done, 0.5k lines).** `Tailored/Detyping.lean` and
  `Tailored/Intro/Layout.lean` below, generic in the labels, the register length `Q`, the
  original cutoff `R` and the input's split. One finding for P3d: a λ-bounded tailored input
  bounds its readable and its linear answer lengths by `(2^n)^λ` *separately*, so its answers
  reach `2·(2^n)^λ`, beyond `seven`'s original cutoff `R = (2^n)^λ` at the same λ; the input
  enters `seven` at a larger λ' (λ + 1 suffices for `n ≥ 1`), which the canonical decider's cost
  needs anyway, and the contract's `δ(ε, n)` at λ is then `seven`'s at λ'.
- **P3b₂ — the instance (in progress).** Read from the Lean (2026-10-05): `seven`'s output is
  compared with the `reference` verifier (`AmbientVerifierTransport.lean:38`), a
  `CL.Detyping.DeciderProgram.verifier` with graph `TypeGraph.Adj QLD.adj (.pauli .X) (.pauli .Z)`
  on `QuestionType QLD.Ty 7`, typed sampler `typedSampler 7 (PauliSampler.sampler …)`, typed
  decider `typedDecider c U (clamp (source, λ))` and the constant cutoff
  `answerBound (registerBits) (originalBound)`; `output_val_eq_reference` and
  `hasPerfectPCC_reference` carry value and completeness across, and `verifier_game_D` is the
  game identity on pushed questions. The source decider is called only on the edge
  `(introspect false, introspect true)`, at index `2^n`, on `toBits (pull (firstEmbedding hs) y)`
  of the two registers; Read and Sample are tied to it by `reading` (`y = z`, equal answers)
  and `sampling` (`y = L_w(z)`, equal answers); and the honest strategy measures the input's at
  the same question (the numbering of `CanonicalGame` cancels). `Tailored/Intro/Source.lean`:
  `srcQuestion`, `srcSplitR`, `srcSplitL`; `Background/Tailored/Intro/Pauli.lean`: the Pauli
  labels' lengths `count · width` and readability (`.pauli .Z` only).
- **P3b — the tailored presentation as a game (2–3k).** Structure, settled 2026-10-05: `seven`'s
  output verifier is `CL.Detyping.DeciderProgram.verifier` over a typed sampler and a typed
  decider, so the presentation is typed tailored data on the labels (`Tailored/Detyping.lean`,
  `TypedData`: lengths by label, constraints on typed questions), detyped generically
  (`TypedData.detype`: a question's lengths are those of the label its graph view decodes to,
  zero when none; a pair's constraints are the typed ones on an edge, none off the edges), with
  soundness and completeness reduced to the edges once (`detype_accepts_dec`,
  `detype_accepts_enc`), then relabelled along `vectorEquiv` to the output verifier's questions
  (`PermStrategy.comap` of Phase 2). The typed layout per label, readable fields first: Pauli `Z`,
  its `Q` bits readable; the other Pauli labels, their fixed lengths linear; Introspect and
  Sample, `y` (or `z`) and the input's readable answer bits padded to `R` readable, its linear
  bits padded to `R` linear; Read, `y` and the padded readable bits readable, `yp` and the padded
  linear bits linear; Hide, `y` readable, `yp` and `x` linear. The input's split of its answer is
  `V.lenOf` at the input question, a function of the readable `y` (or `z`). Then `encPad` from
  parsed answers to bits and `dec` back, and the acceptance specification the processor must meet: (⇒) the tailored game accepts
  `(a, b)` only if `seven`'s decider accepts `(dec a, dec b)`; (⇐) it accepts
  `(encPad a', encPad b')` whenever `seven`'s decider accepts `(encode a', encode b')`. Stated as a
  structure `IntroSpec` on a candidate `(L, LP)`, so that P3c and P3d can be written against it
  before P3e exists.
- **P3c — ZPC completeness from the specification (3–5k).** The chain above restated as
  definitions (its constructions are named; only the existentials wrapping them need unfolding),
  so that the honest measurement at each question is an explicit formula. The permutation
  strategy is `U x i = encObs (honest x) encPad i`: involutions, commutation at a question and
  along edges (from `auxStrategy`-style `IsPCC` through `commute_encObs_encObs`) are P3a; the
  signed-permutation and `Z`-alignment clauses go type by type through P3a's closure lemmas,
  with the input entering as `S.U` through `pvmObs_fourierProj_bit` and its readable bits
  diagonal; the conjugation by `equivFin` is `IsSignedPerm.reindex`. Perfection: a rejected
  encoded pair has a rejected decoded pair (⇐ of P3b), whose honest projections multiply to
  zero by PCC and value `1`; non-encoded answers carry zero projections.
- **P3d — soundness from the specification (1–2k).** A strategy for the tailored game,
  coarse-grained along `dec`, is a strategy for `seven`'s game at least as good (⇒ of P3b,
  `mergeAnswersByQuestion`), then `seven.soundness` and `valStar_ofTNFV`. **Dependency:**
  `seven.soundness` takes `Verifier.IsBounded lam` of the input, here `V.ofTNFV U`, which is the
  canonical decider's cost that P1b deferred; either that cost is supplied (its only consumer
  so far) or the slice checks whether `CompiledSoundness.output_soundness` uses boundedness beyond
  the answer bound `(2^n)^lam`, and restates it without.
  *Progress (2026-10-05):* the canonical decider's cost, deferred in P1b, is in
  (`Tailored/CanonicalCost.lean`, `lem:canonical-decider-cost`): with a total parse in front
  (`canonProgT`, the same acceptance on encodings), it halts on every input `(n, d)` within
  `c (T + 10^k + |n| + 1)^m (|d| + 1)^{e (k + 1)}` when `L` and `LP` run within `T (|d| + 1)^k`,
  and its description is `4 |L| + |LP|` plus a constant. What remains for `IsBounded λ'` of the
  presented verifier is the wrapper of `Verifier.ofSamplerDecider` at a `λ'` linear in `λ`
  (`wrapCore_cost'` is explicit, but asks for the sampler's bound at every index, which
  tailored λ-boundedness gives only from `n = 2`), and `ofTNFV` with `canonProgT` in place of
  `canonProg`. The loss is harmless: `δ(a, b, Cλ, n, ε) ≤ δ(a C^a, b, λ, n, ε)` for `a ≥ 1`, and
  the contract chooses `a`.
- **P3e — the two programs and their correctness (5–9k, 2–3 PRs).** `L^intro` by type, the padding
  split computed by running the input's `L` on the readable `y` (Introspect, Read) or `L_w(z)`
  (Sample). `LP^intro` as constraint lists per check family, with `rejectConstraint` wherever a
  readable-only check fails (formats, lengths, the prefix guard, `sourceOutput`, the router's
  off-edge acceptance becoming the empty list): (i) the Pauli basis test `QLD.accepts`, rules
  2a–7, bit by bit through the self-dual coordinates of `shoupBinField` (`BinaryLinear`,
  `shoupMulProg_encoding`); (ii) the sampling, reading and hiding checks, a dual equality becoming
  one row per generator of `ker (stageLinear P k y)` (`kernelGeneratorsProg`); (iii) the source
  check `D`, the input's own `LP` run on the decoded readable answers and its constraints
  re-indexed into the padded layout, plus the padding-is-zero rows. Correctness is `IntroSpec`.
- **P3f — costs and description bounds (2–3k).** `within` in the shape of
  `Introspection.budget`, `lp_size ≤ C λ^C`, `len_total`; the sampler's clauses are `seven`'s.
- **P3g — `TailoredIntrospection` inhabited (0.3k).** Assembly, blueprint `thm:tailored-qr`,
  `Closes #281`.

**Phase 4 — answer reduction (25–40k; 8–12 PRs).** In the order of the paper's §5.2–5.6:
purification and the tailored oracularization with its ZPC completeness and the reuse of
`thm:oracularization` (1.5–2.5k); triangulation, decoupling and the affine `Extend`
(1.5–2k); the output indicator `L*` with its time bound (2.5–3.5k); the 6-decoupled
Cook–Levin for `L*` on the existing tableau, generalizing `Link.lean`/`Decoupled.lean` from
two equal answer blocks to three unequal ones (2–4k; the paper's sketch, II:8618); the
23-block PCP, `Induce_C`, completeness with the `F₂`-affinity of `Π^L`, soundness by
Schwartz–Zippel (5–7k); the tailored low-degree game as `clGame` with bit-level rows, the
bridge to `clSoundness` with the line conclusions, and its algorithmic form (3–4.5k); the
`AnsRed` typed game, its ZPC completeness by affine data processing, its soundness in the
bipartite model (7.5–11.5k); `PartialAnsRed` with times and descriptions (4–6k); the parameter
chain `Λ, Q, Δ, T, D, FE` and the constants (1.5–2.5k). `TailoredAnswerReduction` inhabited.

**Phase 5 — assembly (1.5–2.5k; 1–2 PRs).** `TailoredGapCompression.ofTailoredPipeline`:
levels, parameters `K(n)`, the thresholds collected into `C₀`, the accounting with a third
machine in every line, the no-error propagation, the value chain through margins
(`Margin.lean` with the paper's exponents). The main theorem and the class theorems become
unconditional; the blueprint chapter is completed with every `\lean{}`, `\leanok` and
guard; `blueprint-edges`, `blueprint-colours`, `lean-coverage` clean.

**Phase 6 — paper I (10–20k; optional, §9).** The associated subgroup test, Main Theorem II
(finitary), the measure-free undecidability of approximating the sofic value, then Main
Theorem I and `aldous_lyons_false` for some finite generating set.

## 6. The estimate

### 6.1 Calibration, measured in this repository

| Quantity | Value |
|---|---|
| Lean written by this project (non-vendored, 2026-07-22 → 2026-10-05) | 241k lines (175k outside `Background/`, 66k project-written inside it) |
| Vendored | 270k lines (LIDT 126k, repetition 71k + 56k, orthogonalization 13k, Liehr–Tsirelson) |
| Merges to `main` | 210, in six active weeks (W30: 13, W32: 4, W37: 16, W38: 75, W39: 87, W40: 15) |
| JNVWY introspection (the stage Route A re-presents) | 36.8k + 7.9k lines, plus `CL/` 9.2k |
| JNVWY answer reduction (the stage §5 replaces) | ≈48k lines all told (`AnswerReduction` 10.9k, `SAT` 8.6k, `CookLevin` 13k, `LIDT` adapter 10k, oracularization 5.6k) |
| Repetition at verifier level | 4.8k + 1.4k |
| Halting layer | 9.4k (criterion route) + 3.2k (paper route) |
| `MIP^co` Phases 1–5 (restatement over a bipartite model) | ≈20k new lines, ≈160 modules restated, four calendar days |
| Answer reduction campaign `AR-1`…`AR-6` | two calendar days, six PRs |

### 6.2 New Lean, by phase

| Phase | Route A | Route B | Of which the paper only sketches |
|---|---|---|---|
| 1. Foundations, halting protocol, class | 9–15k | 9–15k | `lem:lambda` (II:2002, cites JNVWY Lemma 12.5) |
| 2. Repetition | 2.5–3.5k | 2.5–3.5k | — |
| 3. Question reduction | 13–22k | 45–75k | Route B: `Fact` 3495, `Fact` 3486, `claim:completeness_PB_k`, claims 2–3 of II:5324–5545 |
| 4. Answer reduction | 25–40k | 25–40k | the Cook–Levin for `L*` (II:8618), seeded oracularization (II:7876) |
| 5. Assembly | 1.5–2.5k | 1.5–2.5k | — |
| **Paper II total** | **51–83k** | **83–136k** | |
| 6. Paper I corollary | 10–20k | 10–20k | — |

The paper-faithful entanglement-form route (synchronous strategies, anchoring, `Ent` clauses)
would add BVY's theorem in dimension-preserving form (30–70k by analogy with the vendored
direct theorem), the almost-synchronous rounding (5–15k; #22), the tracial near-bijection
toolbox of II:§3.1–3.2 (3–5k) and `Ent` bookkeeping through every extraction: 45–100k more,
and two theorems with no formalization anywhere. It is not recommended unless the
entanglement clauses are themselves the goal.

Blueprint: one chapter of 3–5k LaTeX lines (chapter 6, for JNVWY's four stages, is 7.5k),
plus bibliography entries.

### 6.3 Calendar

The repository's own rate was about 40k lines a week at peak, on material with a verified
ledger and proofs already shaped by two months of formalization; restating over the bipartite
model ran at 20k lines of new Lean in four days. New constructions with their own
completeness proofs and programs run slower; 15–25k lines a week of finished, merged Lean is
the right expectation. On Route A that is three to five weeks of production; with Phase 0, the
statement repairs that every stage so far has needed (the formalization plan records seven
for the time bounds alone), and the paper's sketched steps to fill, **six to ten weeks** of
calendar time; **ten to sixteen** on Route B; two to four more for paper I.

### 6.4 Confidence, and what moves the number

- Phase 0's verdict on Route A: 30–50k lines, the largest single swing.
- The 6-decoupled Cook–Levin for `L*`: the repository's own took 13k lines from scratch; the
  2–4k here assumes the tableau and describer machinery generalize. If they do not, +8k.
- Cost accounting in the ambient model: the paper states running times as suprema over all
  other inputs (`TIME(L; n, ·)`), the reading the repository found unsatisfiable and replaced
  by `T·(|input|+1)^k`; the same repairs recur for three machines instead of two. Budgeted in
  the ranges; the risk is to calendar, not to lines.
- Everything else is bookkeeping with a template in the repository.

## 7. Risks and open points

1. **Route A's two conditions** (§4.2). If the repository's introspective predicate has a
   check that is not `F₂`-linear in the `X`-basis outcomes given the `Z`-basis ones, or if an
   honest observable is not a signed permutation, question reduction falls back to Route B.
   Phase 0 decides it from the existing files before any Lean is written.
2. **The Cook–Levin for `L*`** (II:8618) is the one large step the paper does not prove
   ("adapt [JNVWY] §§10.2–10.3", II:8757); the generalization from two equal answer blocks to
   three unequal ones (`a^R`, `b^R`, `O`) is the work.
3. **Ambient cost model.** As in 6.4; expect to restate `TIME` clauses in relative form and to
   introduce explicit parse lengths where the paper uses unary outputs.
4. **The `F₂`/`F_q` seam** (§4.5) is bookkeeping, but it is in every tailored presentation of
   a repository check; a general lemma "an `F_q`-linear check is `t` `F₂`-linear rows under
   `BinField`" should come first.
5. **Zero-weight edges.** The paper's "commutes along edges" quantifies over `E`, which may
   contain zero-probability edges; `IsPCC` quantifies over `0 < μ x y`, which is what every
   proof uses. State ZPC over the support and say so.
6. **Build regime.** Phases 3–5 import `thm:qld`, the LIDT adapter and the repetition
   theorem: the slow regime of `CLAUDE.md` (30–45 minutes without prebuilt oleans). Keep
   `MIPRE/Tailored/` (foundations, halting, class) free of `Background/` imports so that
   Phases 1–2 and all iteration on statements stay in the fast regime; the stage
   constructions go under `MIPRE/Background/Tailored/`. The session environment's Lean
   toolchain mismatch (4.33 on PATH against 4.35.0-rc3 oleans) needs the cloud setup script
   re-saved before this track starts.
7. **Statement-level corrections** in the paper (§8) are many but none fatal; each becomes a
   blueprint remark and an upstream note. There is no ledger for paper II; a notes file
   `reports/aldous-lyons-paper-notes.md`, appended as the Lean finds things, is the minimum.
8. **Paper I** (§9): the measure-theoretic side is thin in Mathlib (no Chabauty space, no
   invariant random subgroups, no linear programming), and the transfer of the refutation
   from the game's generating set to the free group of rank 2 is in neither the paper nor
   Mathlib.

## 8. Findings in the papers, for the blueprint and for upstream

Collected by the readers; line numbers in the LaTeX sources. None blocks the formalization;
each is to be recorded where the Lean meets it.

- II:1510: clause (3) `val* < 1/2`; the proof (II:2046–2065) gives `≤ 1/2`. Paper I (I:2140)
  and II:677 say `≤`. Formalize `≤`.
- II:11293–11371: §6.2, with `lem:sync-game` and `thm:synchronous` (Vidick 2022, Cor. 3.3), is
  inside a `comment` block; the live almost-synchronous statement is `Fact` II:3227 with a
  proof idea. II:11517–11580 (`prop:par-rep`) is also dead. §5 holds about 1,390 commented
  lines in fourteen blocks, among them a second `thm:ldc-soundness` (II:10088), the whole
  JNVWY-style two-verifier PCP design (II:9348–9762, with an author's note that one polynomial
  is "a placeholder") and `thm:oracle-completeness/soundness` (II:10190–10240). The live
  mathematics of §5 is about 2,800 lines.
- II:11586: the anchored repetition theorem for TNFVs has no label and is a near-duplicate of
  `thm:repetition` (II:11103), whose statement lacks the all-self-loops hypothesis its proof
  (via `thm:parrep-comp-sound`, II:11397) needs; §7 applies it to answer reduction's 9-type
  output.
- II:5746 and II:3998: the completeness clauses of `thm:h_level_question_reduciton` and
  `thm:informal_question_reduciton` say "Z-aligned permutation strategy" without "commuting
  along edges"; the proof (II:6840–6843) produces ZPC and `thm:h_level_compression`
  (II:5696) requires it.
- II:5750 and II:6858: the entanglement factor `(1 − cε)` of `thm:h_level_question_reduciton`
  is derivable only as `(1 − c√ε)·2^{2^{λn}}` (detyping turns `ε` into `O_h(√ε)` first), and the
  chain at II:6858 drops the `2^{2^{λn}}` factor. Irrelevant on the value-form route.
- II:5626: `defn:h-level_NFV`'s λ-bound quantifies over all `n`; at `n = 1` it is
  unsatisfiable; `def:lambda` (II:1804) has `n ≥ 2`.
- II:11822: `eq:time_bounds_V1` has `λ^{c_2}` for `λ^{c_1}`; `eq:bound_on_description_V1`
  (II:§7) assumes `c_1 ≥ |D|` silently; `lem:VMLn_and_its_compression`(3) (II:1957–1976) says
  "halts in less than `n` steps" where `F` (II:1900) runs `M` "for `n` steps".
- II:5442 `=x` for `=ν`; II:6558 the Introspection edge calls `linproc(n, …)` where `2^n` is
  meant; `claim:completeness_PB_k` (II:3884) needs `k ≥ 2` while `thm:complet_sound_quered`
  allows any positive `k`, and writes `ρ^X` for both Pauli vertices (II:3886);
  `claim:completeness_soundness_double_cover` (II:3116) states `ε/c²` where its
  `eq:eps_x_lower_bound` gives `2ε/c²`; the corollary at II:3945 omits the `[n, k, d]`
  hypothesis on which its `d` depends; II:3027 is a definition labelled `claim`; the constant
  rate of `Fact` II:3486 is unused.
- II:7257 "total degree at most 1" should be "individual degree at most 1"; II:≈9100 builds
  `α^L_X` from `Ψ^R` instead of `Ψ^L`; II:10689, 10704, 10711 read `1 − 63m/1` for `1 − 63m/q`;
  `eq:def_Delta_proof_ans_red` is used twice (II:10970, 10975) and the second display says
  `|Λ| = O(|Λ|)` for `|Δ|`; the no-error clause of `A_ar` in `thm:main_ans_red` is not
  discharged in its proof (it follows from II:10795); the constants `1/2, 3/10, 2/5, 1/25,
  8/25` of the soundness proof (II:10622–10733) depend on §4's typed sampling convention,
  which §5 does not restate.
- Sketched or cited on the main path: `lem:lambda` (II:2002, "a complete proof of the
  analogous claim appears in [JNVWY, Lemma 12.5]"); `prop:explicit-padded-succinct-deciders`
  (II:8618, sketch); `rem:sampling_scheme_underlying_oracularization` (II:7876, "works
  (essentially) the same"); `cor:comp_sound_combi_detyping` (II:6026, sketch); `fact:padding_properties`
  (II:6246, no proof); `claim:DeTyping_NFV` (player B "similar, omitted"); `thm:ldc-soundness`
  (II:9885, "a standard reduction"); claims 2 and 3 of question reduction's soundness ("for
  the rest it is essentially the same", II:5379). On Route A the last three are inherited from
  proofs the repository already has.
- Paper I: I:2161 treats the supremum in `val_sof` as attained (harmless once stated per
  action); the loop convention for the vertex marginal `μ(x)` differs between I:2264 and
  II:3232; the soundness constant of Main Theorem II is explicit from the proof,
  `C = 4·370·2·4 = 11840`.

## 9. Paper I: the corollary

What paper I adds (I:439–560, I:1138–1220, I:2074–2704), in the reader's summary. A
*subgroup test* over a finite set `S` is finitely many challenges `(K_i, D_i)` (finite
`K_i ⊆ F(S)`, `D_i : 2^{K_i} → {0,1}`) with weights; a strategy is a probability measure on
the space of subgroups `Sub(F(S)) ⊆ {0,1}^{F(S)}`; `val_sof` is the supremum over the finitely
described measures `Φ(σ) = E_x 1_{Stab(σ,x)}` of finite actions `σ : S → Sym(X)`, `val_erg`
over all conjugation-invariant measures; the Aldous–Lyons conjecture (I:528) is that the
former are weak-* dense, so that `val_sof = val_erg` for every test (I:550).

- **Main Theorem I** (I:594, proof I:1170–1220): `val_sof` is approximable from below by
  enumerating finite actions (trivial), `val_erg` from above by a decreasing computable
  sequence (`val_B` over finite "pseudo-subgroup" polytopes, converging by weak-* compactness
  of `Prob({0,1}^F)`). Under Aldous–Lyons, `val_sof` is therefore computable to any precision.
  Mathlib has `CompactSpace (ProbabilityMeasure E)` for compact `E` and the product topology;
  it has no space of subgroups, no invariant random subgroups, no Stallings foldings and no
  linear programming. The reader found both can be avoided: the polytope constraint can be
  the decidable "locally closed in `B`" one (which is all the paper's own proof of its
  Lemma I:941(2) uses), and the LP optimum can be a grid enumeration with slack. Estimate:
  2–4k lines for the measure side, 2–4k for the computability plumbing (`Computable`/`Partrec`
  statements are expensive here, as `Halting/*` shows).
- **The associated test and Main Theorem II** (I:2086, I:2126): the test `T̃(G)` of a tailored
  game `G` has one challenge per edge with four checks (involutions and commutations within
  a vertex, readable generators or their `J`-twist in `H`, and the controlled constraints as
  words); completeness: a perfect ZPC strategy for `G` gives a perfect finite action for
  `T̃(G)`; soundness: a finite action of value `1 − ε` gives a quantum strategy for `G` of value
  `≥ 1 − C Λ⁴ 2^{6Λ} ε`, `C = 11840`. **The proof is finitary** (I:2177–2704): finite
  permutation actions, stabilizers, the Fourier basis of an `F₂^m`-action, an elementary
  stability interlude for almost-involutions and almost-commuting involutions (I:2559–2649),
  and edit distance. Estimate: tailored games and permutation strategies 1.5–3k (shared with
  Phase 1), completeness 2–4k, soundness 3–6k.
- **The corollary** (I:2144–2168): under Aldous–Lyons, `val_sof(T̃(G_M))` is computable to
  within `λ(M)/2`, which decides halting. Assembly 0.5–1k.

Lean shape: `SubgroupTestData` over a finite `S` with `valSof` as a supremum over finite
actions (no measure theory), the computable `TailoredGameData → SubgroupTestData`, Main
Theorem II's two clauses, and first the measure-free milestone *"no computable function
approximates `valSof` to within `1/k` on every test"* from `TailoredHaltingReduction`; then
`valErg`, the conjecture as `Dense (range Φ_S)` on `ProbabilityMeasure (Sub (FreeGroup S))`,
Main Theorem I, and `aldous_lyons_false : ∃ S, ¬ Dense (range Φ_S)` — for the generating set
of `T̃(G_M)`, which is what the paper proves; the transfer to rank 2 is extra.

## 10. Housekeeping

- **Where it lives.** `MIPRE/Tailored/` for the Foundations-regime files (games, signed
  permutations, ZPC, the verifier type, the canonical decider, the halting protocol, the
  classes; imports Mathlib and `MIPRE/Foundations` only); `MIPRE/Background/Tailored/
  {Introspection,AnswerReduction,Repetition}/` for the stage constructions, which import
  `Background/QLD`, `Background/LIDT` and `Background/Repetition`; `MIPRE/TailoredGameValue.lean`
  for the Mathlib-only statement, `MIPRE/TailoredMIP.lean` for the main theorem (as
  `HaltingGameValue.lean`/`MainTheorem.lean` and `MIPCo.lean`). Every file under the module
  system; `lake exe mk_all` after each addition; guards in `MIPRE/Axioms.lean`.
- **Blueprint.** A new chapter `blueprint/src/content/09_tailored.tex`: paper II's
  definitions and theorems in the forms formalized, each deviation of §2.2, §4.1 and §4.4 as
  a remark citing the paper's own text, `\uses` edges checked by `blueprint-edges.py`, colours
  by `blueprint-colours.py`. Bibliography entries to add: BCV25 (arXiv:2501.00173), BCLV24
  (arXiv:2408.00110), dlS22a (de la Salle, orthogonalization, C. R. Math. 360, 2022;
  arXiv:2103.14126, already the source of the vendored tree), dlS22b (de la Salle, spectral
  gap and stability, 2022), CVY23 (Chapman–Vidick–Yuen, efficiently stable presentations),
  BVY17 and Vid22 (present), GH17 (present through `thm:gowers-hatami`), JNVWY's tensor-codes
  paper (present), Justesen 1972 and Akhtiamov–Dogon if Route B is taken.
- **Paper notes.** `reports/aldous-lyons-paper-notes.md`, seeded from §8, appended as the Lean
  finds more; the maintainer forwards to the authors as they see fit.
- **Tracking.** One issue for the track with the phase list above as sub-issues; PRs
  `Closes #N`, `awaiting-review`, squash merge, as for every other track. The first PR is
  Phase 0's statements file and the blueprint skeleton, so that the shape is reviewed before
  the volume arrives.
- **Not planned**: anchoring, `thm:bvy`, `thm:almost-sync` (#22/#23), de la Salle's
  semi-stability and the generalized Pauli basis game (unless Route B), Justesen codes,
  the `Perpendicular` sampler query, entanglement clauses, the h-level family (the
  fixed point lives at one level, as `rem:LevelConstant` II:5706 says and as the repository's
  level-7 pipeline does), the trace-norm and near-bijection toolbox of II:§3.1–3.2.

## Appendix: map of paper II

| Section | Lines | Live | Notes |
|---|---|---|---|
| 1 Introduction | 673–939 | | proof ideas 802; notation 887 |
| 2 Tailored games, `TMIP* = RE` from compression | 940–2071 | all | measurements 946; signed permutations 1008; games 1071; tailored games 1177 (main theorem 1505); encodings 1514 (TNFV 1758, λ-bounded 1800, `Ent` 1839, compression 1852); halting protocol 1833 (`F` 1900, `V^{M,λ}` 1925, `lem:dhalt-values` 1978, `lem:lambda` 2002, proof 2021) |
| 3 Compression toolbox | 2072–3965 | all but 2655 | §3.1 2079; §3.2 2176; §3.3 2804; §3.4 2887; §3.5 2984; §3.6 3164; §3.7 3239; §3.8 3532 |
| 4 Question reduction | 3966–6877 | all | introspection game 4036; baby case 4179 (illustrative); CLMs 4656; `QueRed_h` 4871 (theorem 5215); TNFV level 5559 (h-level sampler 5584, compression 5643, QR 5712, typed schemes 5764, detyping 5985, padding 6219); proof 6302 (`TypedQR_h` 6308) |
| 5 Answer reduction | 6878–11077 | ≈2,800 of 4,200 | theorem 6883; prelude 6958; prerequisites 7736; polynomial equations 8319 (`L*` 8381, Cook–Levin 8618, PCP 8988–9155); low-degree test 9769 (game 9793, soundness 9885); combinatorial/algorithmic 10269 (game 10285, soundness 10487, `PartialAnsRed` 10760); proof 10846 |
| 6 Parallel repetition | 11078–11660 | §6.2 dead | theorem 11103; anchoring 11219; `k`-fold game 11377; `thm:parrep-comp-sound` 11397 (BVY 11425); `PR` 11464; TNFV theorem 11586 |
| 7 Proof of compression | 11661–11899 | all | parameters 11711; accounting 11732; value properties 11810 |
