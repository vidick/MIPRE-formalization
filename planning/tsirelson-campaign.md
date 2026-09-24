# Tsirelson's problem: implementation plan

Tracking issue: #214. First written 2026-09-23 (PR #201); revised 2026-09-24 after a review of
five independent passes (code interfaces, Mathlib, mathematics, paper and ledger, cheaper
routes), a completeness critic, and a four-way check of the replacement route with compiled
prototypes. The target is the negative answer to Tsirelson's problem, `Cqa ⊊ Cqc`, in a
finite bipartite scenario (blueprint `cor:tsirelson`, ledger 1.8.5).

## 1. What changed in the revision, and why

- **Answer reduction is done.** `MIPRE.Halting.halting_reduction_quantum` is proved
  unconditionally in `MIPRE/MainTheorem.lean`, so the ladder of conditional milestones
  (`tsirelson_of_compression`, `tsirelson_of_answerReduction`, the `(G) (U)` parameters) is
  gone. The final theorem is unconditional. It lives in a small root module next to
  `MainTheorem.lean`, since `MIPRE/Foundations/` cannot import it.
- **The route changed.** The first version built the NPA hierarchy level by level, took a
  diagonal limit, reconstructed a projective representation, dilated commuting POVMs to
  commuting projections on an arbitrary Hilbert space, and refuted each level by a dyadic grid
  of affine and PSD witnesses. Tsirelson needs none of the level structure. The revision works
  with a single object: the quadratic module `M` of the measurement relations in the free
  `*`-algebra, with POVM generators. Every step follows from it.
  - Closedness of `Cqc` becomes compactness of the state space.
  - Upper semidecision becomes an Archimedean Positivstellensatz with exact
    sum-of-squares certificates, proved with Mathlib's `riesz_extension`.
  - POVMs enter as generators, so no dilation is needed.
  - The review estimated the NPA-level plan at 5.5k–10k lines; this route at about 3k.
- **Tooling is the cloud workflow** of `CLAUDE.md`, not the Windows scripts.
- **Reuse the plan missed:** `TensorProductStrategy.copy`, the `GameData` payoff semantics
  `wt`/`W`/`Draw` with `game_μ_eq`/`game_D_eq` and their primitive recursiveness
  (`ValueApprox/RawStrategy.lean`, `RawSemantics.lean`, `RawPrimrec.lean`), `PInt`/`GInt`
  (`RawInt.lean`), `MIPRE.REPred.of_computable_exists`, and Mathlib's
  `ComputablePred.halting_problem_not_re`.

The NPA-level material (`thm:npa-convergence` as stated, `lem:npa-dilation`, `lem:npa-levels`,
`lem:npa-moment-bound`, `lem:npa-diagonal`) is not on the Tsirelson path. §7 lists it among the
follow-ups, together with the review's corrections to its blueprint text.

## 2. Targets, and what is already proved

**Done** (`MIPRE/Foundations/Correlations.lean`, `MIPRE/Foundations/Tsirelson/Conditional.lean`,
blueprint `def:correlation-sets`, `lem:correlation-sets-basic`, `lem:tsirelson-conditional`,
all guarded):

- `Cq`, `Cqa := closure Cq`, `Cqc`; `Game.payoff`, linear and continuous.
- Commuting correlations are nonnegative and sum to one, so `0 ≤ commutingOperatorValue ≤ 1`.
- `TensorProductStrategy.toCommuting` (via `ofTensor`, `Matrix.toEuclideanCLM`), with
  `Cq ⊆ Cqc` and `quantumValue ≤ commutingOperatorValue`.
- Payoffs on `Cqa` are bounded by `quantumValue`, and on `Cqc` by `commutingOperatorValue`.
- `HaltingReductionQuantum`, which is the statement of `halting_reduction_quantum`.
- `CommutingUpperRE`: `REPred` of `commutingOperatorValue d.game < p/q` over
  `GameData × ℕ × ℕ`, with `p/0 = 0`, the encoding of `ValueApprox.rePred_lt_quantumValue`.
- `exists_quantumValue_lt_commutingOperatorValue`, `exists_mem_Cqc_not_mem_Cqa`,
  `exists_Cqa_ne_Cqc`, `tsirelson_of_upperRE_of_isClosed`.

**Remaining inputs:** `CommutingUpperRE`, and `IsClosed (Cqc …)` for the `Fin (n+1)`
scenarios. The headline is the strict inclusion `⊂`. `≠` is only an intermediate lemma, and
`cor:tsirelson` is never marked on it. The witness scenario has common alphabets
`Fin (nX+1)` and `Fin (nA+1)` for both players, which is the paper's `C(n,k)` form.

## 3. The route

All of it is stated for `X Y A B : Type`. `CommutingOperatorStrategy.H : Type`, and the GNS
space lives in the universe of the generators. Every consumer uses `Fin` alphabets.

### 3.1 Polynomials, relations, the cone

- `NCPoly G := MonoidAlgebra ℂ (FreeMonoid G)`, with its own star: conjugate the
  coefficients, reverse the words.
  - Mathlib's `FreeAlgebra` star is `ℂ`-linear, so it is unusable here, and `MonoidAlgebra`
    has no star.
  - At the pinned Mathlib, `MonoidAlgebra` is a structure (`ofCoeff`/`coeff`).
- Generators `Gen := (X × A) ⊕ (Y × B)` are self-adjoint.
- Relations: `Σ_a e_xa − 1`, `Σ_b f_yb − 1`, `[e_xa, f_yb]`. `I` is the complex span of
  `u ρ v`, a two-sided ideal. `Anti` is the anti-Hermitian elements.
- `M := PointedCone.hull ℝ ({s⋆ g s : g ∈ {1} ∪ gens} ∪ I ∪ Anti)`. Here
  `PointedCone.span` has been renamed `hull`.
- **Facts about `M`:**
  - `a⋆ M a ⊆ M`.
  - `1 − g² ∈ M`, from `1 − e = Σ_{a'≠a} e_{a'} − (Σ e − 1)` and
    `e − e² = e(1−e)e + (1−e)e(1−e)`.
  - `1 − w⋆w ∈ M` for every word, by telescoping.
  - **Archimedean:** `∀ y, ∃ N, N·1 + y ∈ M`, by monomial induction with
    `(1 + |α|²)·1 + αw + (αw)⋆ = (1+αw)⋆(1+αw) + |α|²(1 − w⋆w)` and the anti-Hermitian part
    in `Anti`.
- **Evaluation:** a commuting strategy gives `π_S : NCPoly →⋆ₐ[ℂ] (H →L[ℂ] H)` that kills
  `I`, with `0 ≤ Re⟨ψ, π_S(m) ψ⟩` for `m ∈ M`. As a corollary, `r·1 − W_G ∈ M` implies that
  every strategy has value `≤ r`, where `W_G := Σ μ(x,y)[D] e_xa f_yb`.

### 3.2 States and GNS

A *state* is a `ℂ`-linear `L` with `L 1 = 1`, `L(z⋆) = conj L(z)`, `0 ≤ Re L(s⋆ g s)` and
`L(I) = 0`. From a state the construction produces a `CommutingOperatorStrategy` whose
correlation is `Re L(e_xa f_yb)`:

- the pre-inner product is `⟨a, b⟩ := L(a⋆ b)` on a `def` synonym, through
  `PreInnerProductSpace.Core`, `InnerProductSpace.ofCore` and `UniformSpace.Completion`;
- each generator acts by left multiplication, which is a contraction because
  `Re L(a⋆(1 − g²)a) ≥ 0`; it is built with `LinearMap.mkContinuousOfExistsBound` and then
  `ContinuousLinearMap.completion`;
- positivity, `Σ = 1` and commutation are checked on the dense image, the last two through
  null vectors (`‖coe x − coe y‖ = ‖x − y‖ = 0`). `Completion.coe_injective` needs `T0Space`,
  which the synonym lacks;
- `ψ := coe 1`, of norm 1;
- extensions go through `Completion.induction_on`.

When restating the correlation, unfold it with `change` to the standard inner-product
instance, because `correlation` elaborates through the C*-module instance.

### 3.3 Compactness: `Cqc` is closed

- A state is determined by its values on words, `φ : FreeMonoid Gen → ℂ`.
- Each state condition is closed in `φ`. Positivity is required for every polynomial `s`,
  not only for words.
- `|φ w| ≤ 1`, from `2 + αw + ᾱw⋆ ∈ M` with `|α| = 1`, or from the GNS contraction bound.
- So the state set is closed in a product of closed disks, hence compact
  (`isCompact_univ_pi`, `IsCompact.of_isClosed_subset`).
- `Cqc` is its image under `φ ↦ Re φ(e_xa f_yb)`: GNS gives one inclusion, `π_S` the
  other.
- Hence `Cqc` is compact, so closed, and `Cqa ⊆ Cqc`.

### 3.4 Positivstellensatz

If `commutingOperatorValue G < r` then `r·1 − W_G ∈ M`.

1. Suppose `h := r·1 − W_G ∉ M`.
2. `riesz_extension` applied to `M ⊔ hull{−h}` with `f(t·1) = t` gives `L₀ ≥ 0` on `M`,
   with `L₀ 1 = 1` and `L₀ h ≤ 0`. Nonnegativity of `f` uses the Archimedean property and
   `h ∉ M`; density uses Archimedean.
3. Complexify: `L z := L₀ z − i L₀(i z)`. `L₀` vanishes on `Anti` and `I`, so `L` is a state.
4. GNS gives a strategy of value `L₀(W_G) ≥ r`, which contradicts
   `value ≤ commutingOperatorValue`.

The prototype `Scratch/SosAlgebra.lean` compiles steps 1–2 (`exists_separating_functional`)
and the Archimedean lemma, with no `sorry`.

### 3.5 Exact certificates

**Certificate.** For `d : GameData` and `p q : ℕ`, a certificate consists of:

- `D ≥ 1`;
- terms `(c_i : ℕ, g_i ∈ {1} ∪ gens, s_i)` with Gaussian-integer coefficients;
- ideal terms `(u_k, ρ_k, v_k)`, with `ρ_k` built from a validated index.

**Test.** Let `R := D·(p·W_d·1 − q·Σ wt(x,y)[Draw] e_xa f_yb) − Σ c_i s_i⋆ g_i s_i −
Σ u_k ρ_k v_k` and `R_h := R + R⋆`. Accept iff `q > 0` and
`Re(R_h)_∅ > Σ_{w ≠ ∅} (|Re (R_h)_w| + |Im (R_h)_w|)`, with coefficients merged per word.

**Soundness.** Every word acts as a contraction (`0 ≤ E ≤ 1`), so every strategy satisfies
`2DqW_d(p/q − value) ≥ δ ≥ 1`. This margin is uniform, so the supremum is `< p/q` by
`ciSup_le`. That step needs `Nonempty (CommutingOperatorStrategy …)`, which the
one-dimensional deterministic strategy supplies for `Fin (n+1)` alphabets.

**Completeness.**

- Take `commutingOperatorValue < r' < p/q`. §3.4 at `r'` gives
  `r'·1 − W = Σ σ_i⋆ g_i σ_i + j + a'`.
- Symmetrizing kills `a'` exactly.
- Approximate the `σ_i`, `u_k`, `v_k` by Gaussian rationals, with an ℓ¹ estimate:
  `‖z‖ := Σ_w (|Re z_w| + |Im z_w|)` is submultiplicative and star-invariant. No topology on
  `NCPoly` is needed.
- Clear denominators with `D = N²`, `c_i = 1`.

**Pitfalls, both refuted-if-ignored:**

- the checker must reject `q = 0`: otherwise `(d, 1, 0)` is accepted, while `p/0 = 0` makes
  the target false;
- the test must run on per-word merged coefficients: unmerged it stays sound but is never
  complete.

### 3.6 The checker

Coded polynomials are lists of `(List ℕ, GInt)`, built with `flatMap`, `map`, `append`,
reverse, and conjugation. `W_d` comes from `wt`/`W`/`Draw`.

- **Merged coefficients:** `coeff(l, w)` is the `GInt` sum over entries with word `w`. Iterate
  over distinct words via `Primrec.list_idxOf` or a seen-list fold, and prove
  `coeff(code z, w) = z.coeff (decode w)`.
- **Letter validation:** relation and generator indices are range-checked. Alternatively,
  letters decode through a monoid hom with out-of-range letters sent to `0`.

The result is `PrimrecRel`, via `ValueApprox.REPred.of_primrecRel_exists`, or a computable
`Bool` test via `MIPRE.REPred.of_computable_exists`.

## 4. Milestones

Each row is a PR. Every declaration a blueprint proof-level `\leanok` claims is guarded in
`MIPRE/Axioms.lean` in the same PR; `scripts/lean-coverage.py` fails otherwise.

| ID | Deliverable | Module(s) | Lines | Status |
|---|---|---|---|---|
| R1 | Correlation sets, conditional consumer, blueprint nodes, guards, this plan | `Foundations/Correlations.lean`, `Foundations/Tsirelson/Conditional.lean` | 450 | done, PR for #214 |
| R2 | `NCPoly` and star; evaluation; cone `M`; `a⋆Ma ⊆ M`; Archimedean; strategy positivity; `value ≤ r` from `r − W ∈ M` | `Foundations/NCPoly/{Basic,Cone}.lean`, `Foundations/Tsirelson/Algebra.lean` | 500–700 | prototype compiles |
| R3 | States and GNS: a state gives a commuting strategy with correlation `Re L(e f)` | `Foundations/Tsirelson/GNS.lean` | 500–700 | prototype compiles |
| R4 | Positivstellensatz (§3.4); compact state space; `IsClosed Cqc`, `Cqa ⊆ Cqc`, `Cqa ⊊ Cqc` given upper RE | `Foundations/Tsirelson/{Separation,Closed}.lean` | 300–500 | separation step prototyped |
| R5 | Integer certificates: semantic checker, soundness, completeness by ℓ¹ approximation | `Foundations/Tsirelson/Certificate.lean` | 400–700 | |
| R6 | Coded checker, primitive recursiveness, semantic equivalence, `CommutingUpperRE` | `Foundations/Tsirelson/{Coded,UpperRE}.lean` | 1200–2000 | |
| R7 | Root `MIPRE/Tsirelson.lean`; `cor:tsirelson` repair; fidelity audit | `MIPRE/Tsirelson.lean` | 50–150 | |

R6 carries the volume risk. The lower semidecider's coded side, for a simpler checker, is
1468 lines.

## 5. Blueprint accounting

- **New nodes, each with `\lean{}` and marks together with its guard:**
  - the `NCPoly` cone and its Archimedean property;
  - states and GNS;
  - the compact state space with `Cqc` closed;
  - the Positivstellensatz;
  - the certificates;
  - none of these carries a `\ledgernode`.
- **`lem:valco-upper-re`:**
  - restate in the `lem:value-lower-approx` form (`GameData`, `p q : ℕ`, `p/0 = 0`);
  - move the RCF method into a remark;
  - drop `lem:rcf-decision` and `lem:tracial-le-co` from its `\uses`;
  - keep `\ledgernode{1.8.4, 1.8.4.1}` with a proof-route note: the correspondence is at the
    level of the conclusion; the ledger's proof rests on the admitted 1.8.3, this one on the
    Positivstellensatz;
  - move the `r < 1` dovetailing and the succinct-description clauses to where
    `thm:separation` consumes them.
- **`cor:tsirelson`:**
  - set its `\uses` to `def:correlation-sets`, `lem:tsirelson-conditional`,
    `cor:main-quantum`, `lem:valco-upper-re` and the closedness node;
  - drop `thm:separation`, `lem:value-lower-approx` and `cor:value-uncomputable`;
  - rewrite "Immediate from Theorem thm:separation";
  - delete the unsupported claim that Slofstra's non-closure "also follows, with quantitative
    bounds, from the machinery here";
  - keep `\ledgernode{1.8.5}` with a note: the ledger's proof dovetails a lower and an upper
    semidecider into a promise decider; the Lean proof uses only the upper one.
- **Admitted node 1.8.3 in `rem:admitted-nodes`, `rem:downstream-nodes` and
  `planning/paper-correspondence.md`:** the Lean Tsirelson does not rest on it, but
  `scripts/ledger-sync.py`'s import reach will keep listing it, since ledger
  1.8.5 → 1.8.4 → 1.8.3. That listing is expected, not an error. File an upstream proposal
  for a reviewed ledger node for the certificate argument, rather than editing the snapshot.
- **The paragraph on the non-explicit route after `rem:separation-which-value`:** it says the
  semideciders contradict `cor:value-uncomputable`, which fails in the total-function Lean form
  at a single threshold. Repair it with overlapping thresholds, or use the RE/co-RE argument.

## 6. Workflow

- Iterate with the lean-lsp MCP tools on `Scratch/` files that import exact modules.
- Build with `lake build MIPRE.Foundations.Tsirelson.<Module>`.
- After adding files, run `lake exe mk_all`.
- Before pushing, run `python3 scripts/lean-coverage.py --check` and
  `python3 scripts/ledger-sync.py`.
- Everything except `MIPRE/Tsirelson.lean` stays in Foundations, out of the `MainTheorem`
  import closure.

Known API facts:

- `ContinuousLinearMap.{add,mul,one,zero,sum}_apply` are deprecated in favour of the root
  lemmas.
- `push_neg` is deprecated in favour of `push Not`.
- `PointedCone.smul_mem` takes `0 ≤ c`.
- `noncomm_ring` closes the `NCPoly` identities.

## 7. After Tsirelson

1. **`thm:npa-convergence` as stated**, with its level presentation, the moment-bound
   induction, the reduced-presentation clause (keeping the behaviour constraints on both
   sides, as the independent review requires) and `lem:npa-dilation`.
   - The dilation uses the block unitary `U = [[0, V*], [V, 1 − VV*]]`, with the first summand
     absorbed into a fixed outcome `a₀` so that the projections form a PVM, and the ancilla
     indexed by `Fin (card A)`.
   - Square-root commutation is `Commute.cfc_nnreal`.
   - It does *not* extend `Dilation.lean`'s finite-dimensional basis completion.
   - The blueprint's `lem:npa-dilation` needs the `a₀` repair, and `lem:npa-levels` needs
     `lem:npa-dilation` in its `\uses`.
   - Most of the GNS and compactness work above carries over.
2. **The full `lem:valco-upper-re` clauses:** rational `r < 1` dovetailing and succinct
   descriptions.
3. **The explicit `thm:separation`:** it needs the Schmidt-rank compression premises of
   `rem:separation-premises`.
4. **Connes' embedding problem (`cor:cep`)** and `cor:qwep`: they rest on the admitted
   Kirchberg node 1.8.6.1.
5. **Value uncomputability for every `c < 1/2`,** via repetition.
