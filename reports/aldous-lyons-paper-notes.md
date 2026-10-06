# The Aldous–Lyons papers: notes from the formalization

**Date: 2026-10-06. Tree: `main` at 8540cbb, after Phase 4 of `planning/aldous-lyons-track.md`
(PR #323), with every phase of the track done. Tracking: #272 (the track), #284 (paper I).**

The track formalizes two papers, both public:

- **Paper I.** L. Bowen, M. Chapman, A. Lubotzky, T. Vidick, *The Aldous–Lyons Conjecture I:
  Subgroup Tests*, arXiv:2408.00110v1 (`Subgroup_Tests.tex`, 2,783 lines). Lines are cited
  `I:n`.
- **Paper II.** L. Bowen, M. Chapman, T. Vidick, *The Aldous–Lyons Conjecture II:
  Undecidability*, arXiv:2501.00173 (`A-TailoredMIP-main.tex`, 11,911 lines). Lines are cited
  `II:n`.

The track planned this file (`planning/aldous-lyons-track.md` §10, "Paper notes"): seeded from
the readers' findings in §8 of the plan, and extended as the Lean meets the text. The maintainer
forwards it to the authors as they see fit.

Each item has one of three statuses:

- **met in the Lean**: the formalization ran into it and resolved it as described;
- **formalized differently**: the Lean proves the statement by another route, which may interest
  the authors;
- **reader finding**: found on reading, and not yet at a place the Lean has reached.

Nothing here is an error that breaks a main result. Where a statement is wrong as written, the
proof gives a correct one, and the Lean proves that.

Both main results are proved in the Lean with no hypothesis left:

- paper II's main theorem, with `≤ 1/2` (§2.1, item 1), is
  `TailoredGameValue.tailored_halting_reduction`, with the class theorems
  `MIPRE.Tailored.tmipStarComputable_eq_re` and `MIPRE.Tailored.tmipStar_eq_re`;
- paper I's corollary is `SubgroupTestValue.aldous_lyons_false : ¬ AldousLyons`.

They are in `MIPRE/TailoredMIP.lean`, and each depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The statements they prove, `TailoredHaltingReduction` and
`AldousLyons`, are in Mathlib-only files (`MIPRE/TailoredGameValue.lean`,
`MIPRE/SubgroupTestValue.lean`) and can be read without the rest of the library.

## 1. Paper I

### 1.1 Statements

1. **Completeness of Main Theorem II does not need commutation along edges** (met in the Lean).
   Theorem I:2126 (1) assumes a perfect Z-aligned permutation strategy *that commutes along
   edges*. Its proof (I:2248) uses commutation to make `σ_{xy}` an `F₂`-action on the
   orbit `O_{xy}`. The Lean proves the conclusion without it. Readable variables act at each
   point as the identity or as `J`, so the trace identity of §1.2 applies point by point. At
   value 1 that identity says that every constraint word of the point's readable class fixes the
   point. This is `exists_value_one_of_hasPerfectZPC`
   (`MIPRE/Tailored/Sofic/TraceComplete.lean`), whose proof never uses the hypothesis.
   Commutation is still part of `HasPerfectZPC`, so the statement matches the paper's.

2. **The supremum in `val_sof` is treated as attained** (met in the Lean; reader finding I:2161).
   The proof of Corollary I:2144 applies Theorem I:2126 (2), a statement about a single
   strategy of value `≥ 1 − ε`, with `ε = 1 − val_sof`. The supremum need not be attained.
   This is harmless: apply the theorem with `ε + δ` for every `δ > 0`, then let `δ → 0`. The
   Lean does exactly this in `gameValue_ge_of_valSof` (`MIPRE/Tailored/Sofic/MainII.lean`).

3. **Corollary I:605 is stated for a fixed precision, but used with a precision that varies with
   the machine** (met in the Lean). As stated, Corollary I:605 says: for every `θ > 0` there is a
   Turing machine computing `val_sof` to within `θ`. The proof of Corollary I:2144 then takes
   `θ = λ(M)/2`, which depends on the input `M`. That step needs the uniform statement: one
   machine that takes `θ` (or `k`) as an input. The proof of I:605 gives the uniform statement,
   since both sequences of Main Theorem I are uniform in the test. The Lean states and proves
   the uniform one (`SubgroupTestValue.SofValueApproximable`: one computable `f(T, k)` within
   `1/(k+1)`; `sofValueApproximable_of_aldousLyons`).

4. **The case `Λ = 0`** (met in the Lean). Theorem I:2126 and Propositions I:2267–2283 assume
   `Λ > 0`. The Lean writes every bound in `Λ + 1`, so `Λ = 0` needs no separate treatment.
   With the paper's form `C Λ⁴ 2^{6Λ}`, the bound would be vacuous at `Λ = 0`.

5. **The proof of Corollary I:2144 states the decision the wrong way round** (minor). The
   proof says that one can "deduce whether `val_sof < 1` or `val_sof > 1 − λ(M)`" (I:2153).
   The two alternatives are `val_sof = 1`, when `M` halts, and `val_sof ≤ 1 − λ(M)`, when it
   does not. The approximation at precision `λ(M)/2` separates those. The Lean's decision is
   `le_iff_of_gap` (`MIPRE/Tailored/Sofic/Undecidable.lean`).

6. **Explicit constants** (met in the Lean). The Lean's constants, all explicit:
   - perturbation (Propositions I:2267 and I:2283 through the robustness claim I:1480):
     `1 − 300 (Λ+1)⁴ 2^{4(Λ+1)} ε` (`exists_checks_of_value`, `Cp = 300`);
   - Proposition I:2279: `1 − 2 · 2^{2(Λ+1)} ε` (`gameValue_ge_of_checks`, `Cq = 2`);
   - Main Theorem II: `1 − 600 (Λ+1)⁴ 2^{6(Λ+1)} ε` (`CII = 600`).

   The readers derived `C = 4 · 370 · 2 · 4 = 11840` from the paper's proof (reader finding).
   The two are in different variables (`Λ + 1` against `Λ`), so neither is "better".

7. **The vertex marginal `μ(x)`** (reader finding). Paper I (I:2264) defines
   `μ(x) = ½ Σ_{xy ∈ E} μ(xy)`. Paper II (II:3232) uses a different convention for loops. The
   Lean avoids the question: it uses the unnormalized weight
   `m(x) = Σ_y (w(x, y) + w(y, x))`, which counts a loop twice, and divides by the total
   weight where needed (`sig_genX_le`).

### 1.2 Proofs formalized differently

1. **Proposition I:2279 by a trace identity, with no Fourier analysis.** Let the strategy be
   Z-aligned with signed-permutation observables. Let `M_w` be the signed permutation induced by
   a constraint word `w`, and `R_r` the basis points whose readable value is `r`. Then

   `P[readable value r and constraint c violated] = (1/m) Σ_{j ∈ R_r} (1 − (M_c)_{jj}) / 2`.

   So `(M_c)_{jj} = 1` exactly when the word fixes the point with sign `+`, that is, when that
   point passes the challenge's Check 4 for `c`. A union bound over the at most `2^{2(Λ+1)}`
   distinct constraint words gives Proposition I:2279. This replaces the Fourier bases of the
   `F₂^k`-actions, the orbit intersections and Claim I:2389. The same identity at value 1 gives
   completeness, item 1 of §1.1. The files are `MIPRE/Tailored/Sofic/{TraceIdentity,Passes,
   Quotient,TraceSound}.lean`.

2. **Doubling instead of padding** (Claim I:2582, the proof of Proposition I:2267). The paper
   pads an odd set by one point and matches the fixed points of an almost fixed-point-free
   involution. The Lean first replaces the action by its double `σ ⊕ σ`, which has the same value
   (`value_double`). The doubled action carries a fixed-point-free involution commuting with
   every letter, the swap of the two copies. A fixed point is then sent along the swap
   (`fpfFix`), and every distance is measured on one point set
   (`MIPRE/Tailored/Sofic/{Double,Stability}.lean`).

3. **One repair instead of Glebsky–Rivera** (Claims I:2600 and I:2643). The paper repairs the
   involution relations, commutation with `J` and readability separately, then applies
   Glebsky–Rivera to the `F₂^ℓ`-action, losing `4^ℓ`. The Lean makes one repair (`commFix`).
   Take the set `U` of points from which every ordered product of the variables, at the point
   and at its `J`-image, only reaches points where all of Checks 1–3's relations hold. Keep the
   variables on `U` and set them to the identity elsewhere. `U` is invariant, so the result
   satisfies the relations everywhere, and at most `2^{ℓ+1}` times the number of bad points
   change.

4. **A coarser significance count** (Proposition I:2283). The paper bounds the significance by
   `4 · 2^{2Λ}`. The Lean counts the words of a challenge directly, giving
   `(2Λ + 4)(3 + 8Λ + 2Λ² + 2 · 4^Λ)` (`sig_le`, `sig_genX_le`). This is coarser, and enough.

5. **Main Theorem I (2) without linear programming** (I:927–1137, I:1138–1220). Main Theorem I
   (2) needs a computable decreasing sequence converging to `val_erg`. The paper obtains it from
   the pseudo-IRS polytopes `Q_B` and the optimum of a linear program over them. The Lean
   searches a grid exhaustively. At stage `t` it takes:
   - the words of length at most `t + 2` in the first `n + t` letters;
   - the grid points of weight `P · 2^t` on the stage's `P` patterns.

   A grid point is feasible when two conditions hold:
   - every pattern of positive weight is *locally closed*: it contains the empty word, and it is
     closed under cancelling an inverse pair, under deleting a letter beyond the test's `n`
     generators, and under `u, v ↦ u v⁻¹` within the stage;
   - conjugation by each generator moves the point by at most `4P` in `ℓ¹`, which absorbs the
     rounding.

   The stage's value is the best feasible value plus `2/2^t`, rounded up. The lower bound
   comes from rounding the restriction of an IRS. Convergence comes from compactness of the
   probability measures on the space of word indicators (Prokhorov in Mathlib). A limit point is
   carried by the indicators that respect free reduction and the subgroup axioms, and is
   invariant, because the cylinder sets form a generating `π`-system. That limit is then
   transferred to an IRS on `Sub(F)` (`irs_of_good`).

   The running minimum makes the sequence monotone. No linear programming, Chabauty space or
   Stallings folding is needed. Files: `MIPRE/Tailored/Sofic/Measure/*.lean`.

## 2. Paper II

### 2.1 Met in the Lean

1. **Clause (3) of the main theorem** (II:1510): `val* < 1/2`. The proof (II:2046–2065) gives
   every finite-dimensional strategy value below `1/2`. That bounds the supremum by `≤ 1/2`, not
   `< 1/2`. Paper I (I:2140) and II:677 say `≤`. The Lean states `≤ 1/2`
   (`TailoredGameValue.TailoredHaltingReduction`; the module docstring of
   `MIPRE/TailoredGameValue.lean` records why).
2. **ZPC in the completeness clauses of question reduction** (II:5746 and II:3998). These say
   "Z-aligned permutation strategy" without "commuting along edges". The proof (II:6840–6843)
   produces a ZPC strategy, and `thm:h_level_compression` (II:5696) requires one. The Lean's
   contract `TailoredIntrospection` takes a perfect ZPC strategy and returns one.
3. **`n = 1` in the λ-bound** (II:5626). `defn:h-level_NFV`'s bound quantifies over every `n`;
   at `n = 1` it cannot be satisfied. `def:lambda` (II:1804) has `n ≥ 2`, and so does the Lean
   (`TailoredVerifier.IsBounded`).
4. **`lem:lambda`** (II:2002) refers to JNVWY Lemma 12.5 for "a complete proof of the analogous
   claim". It is proved in the Lean for the tailored halting verifier
   (`MIPRE/Tailored/Halting/Cost.lean`, blueprint `lem:tailored-lambda`).
5. **The 6-decoupled Cook–Levin describer** (`prop:explicit-padded-succinct-deciders`, II:8618,
   proof sketched at II:8757). It is proved in the Lean for any decider, with three windows of
   the tableau's input region tied to the answers. The third window starts at a power of two,
   because the closure library has no binary addition (`MIPRE.SAT.windowDescriber`; blueprint
   `lem:ar-window-describer`).
6. **The no-error clause of answer reduction's length calculator** (`thm:main_ans_red`, II:6908).
   The readers found it not discharged in the proof; it follows from II:10795. Its Lean form,
   that the output's calculator halts with a length on every question of the sampler, is the
   contract's `len_total`. It is proved for the answer-reduced verifier
   (`ArRoutine.lenD_total`).

### 2.2 Formalized differently

These are design choices of the formalization, recorded so that the Lean can be compared with
the paper. They are not findings against the paper.

1. **Value form and the bipartite value.** Soundness is proved in the value form for every
   finite-dimensional strategy, not in the paper's entanglement form. Remark II:1876 calls the
   value form the content of the proofs. This avoids the dimension-preserving reading of
   Bavarian–Vidick–Yuen (II:11425, footnote II:11431) and the rounding `Fact` II:3227
   (`planning/aldous-lyons-track.md` §4.1).
2. **Answer reduction's game** (Phase 4, done). It departs from the paper in three ways:
   - the type graph is complete on the nine types, not the tensor product of two paths
     (II:10313);
   - soundness is proved in the bipartite model through the repository's oracularization;
   - the input is neither padded nor purified as a verifier (II:8377); the output indicator
     purifies on the fly.

   The Lean's PCP formula polynomial has degree at most 17, counting each factor separately,
   where the paper has 9. The soundness bound is unaffected in form.

   Because of the first two departures, the soundness proof of §5 (II:10622–10733), with its
   constants `1/2, 3/10, 2/5, 1/25, 8/25`, is not formalized. Soundness is instead `24√ε` from
   oracularization, composed with the low individual degree test. The contract's loss
   `σ^a((λn)^{μa} ε^b + (λn)^{-μb})` is proved with `b` half the test's exponent.
3. **The honest PCP's certificates** (II:7257, II:9103). The paper builds the certificates of
   vanishing on the cube explicitly, by `Div` and `Mod`. The Lean needs only that they can be
   chosen linearly in the polynomial, and takes any linear right inverse of
   `c ↦ Σ_i c_i X_i(1 − X_i)` on the vanishing polynomials
   (`MIPRE/Foundations/LowDegree/ZeroCertificate.lean`).
4. **The answer reduction's parameters** (II:10846–11074). The Lean's parameters are its own,
   chosen to fit its PCP and window describer. With `Q = (λn + 1)^μ`, the windows have width
   `Q`, the description time is `2^K` with `K = E₁(μ + 1)(oW + Q + 4)` (`oW` the third window's
   width), the formula polynomial's degree bound is `17`, and the field has `2^t` elements with
   `t = E₂(j + r + Q + 1)` (`j` the bit size of the PCP's dimension, `r` the describer's)
   (`MIPRE/Tailored/AnsRed/ArParams.lean`). The parameters grow like a power of `(λn + 1)^μ`,
   and the programs read them in unary, so they are computed by a separate parameter program
   whose running time is bounded on its own. The paper's §5.6 was not re-read against them.

### 2.3 Reader findings, not yet met

These are from the readers' pass (plan §8). Phase 4 met only one of the §5 items, the no-error
clause (§2.1, item 6). The rest lie on parts of §5 that the Lean goes around (§2.2, items 2 and
3). Two of them were checked again against the source: the `Ψ^R` at II:9103, where `Ψ^L` is
meant, and the `1 − 63m/1` at II:10701, 10716 and 10721.

- II:11293–11371: §6.2, with `lem:sync-game` and `thm:synchronous`, is inside a `comment`
  block. The live almost-synchronous statement is `Fact` II:3227, which has only a proof idea.
  II:11517–11580 (`prop:par-rep`) is also commented out. §5 holds about 1,390 commented lines
  in fourteen blocks, among them:
  - a second `thm:ldc-soundness` (II:10088);
  - a two-verifier PCP design (II:9348–9762);
  - `thm:oracle-completeness/soundness` (II:10190–10240).
- II:11586: the anchored repetition theorem for TNFVs has no label and nearly duplicates
  `thm:repetition` (II:11103). The statement of `thm:repetition` lacks the all-self-loops
  hypothesis its proof needs (via `thm:parrep-comp-sound`, II:11397).
- II:5750 and II:6858: the entanglement factor `(1 − cε)` of `thm:h_level_question_reduciton`
  is derivable only as `(1 − c√ε) · 2^{2^{λn}}`, and the chain at II:6858 drops the
  `2^{2^{λn}}`. This is irrelevant on the value-form route.
- In §7 and around the halting lemma:
  - II:11822: `eq:time_bounds_V1` has `λ^{c_2}` where `λ^{c_1}` is meant;
  - `eq:bound_on_description_V1` assumes `c_1 ≥ |D|` without saying so;
  - `lem:VMLn_and_its_compression` (3) (II:1957–1976) says "halts in less than `n` steps",
    while `F` (II:1900) runs `M` "for `n` steps".
- In §3 and §4:
  - II:5442 `=x` for `=ν`;
  - II:6558 the introspection edge calls `linproc(n, …)` where `2^n` is meant;
  - `claim:completeness_PB_k` (II:3884) needs `k ≥ 2`, while `thm:complet_sound_quered` allows
    any positive `k`, and it writes `ρ^X` for both Pauli vertices (II:3886);
  - `claim:completeness_soundness_double_cover` (II:3116) states `ε/c²` where its
    `eq:eps_x_lower_bound` gives `2ε/c²`;
  - the corollary at II:3945 omits the `[n, k, d]` hypothesis its `d` depends on;
  - II:3027 is a definition labelled `claim`;
  - the constant rate of `Fact` II:3486 is unused.
- In §5:
  - II:7257 "total degree at most 1" should be "individual degree at most 1";
  - around II:9100, `α^L_X` is built from `Ψ^R` instead of `Ψ^L`;
  - II:10689, 10704 and 10711 read `1 − 63m/1` for `1 − 63m/q`;
  - `eq:def_Delta_proof_ans_red` is used twice (II:10970, 10975), and the second display says
    `|Λ| = O(|Λ|)` for `|Δ|`;
  - the constants `1/2, 3/10, 2/5, 1/25, 8/25` of the soundness proof (II:10622–10733) depend
    on §4's typed sampling convention, which §5 does not restate.
- Sketched or cited on the main path, besides the two in §2.1:
  - `rem:sampling_scheme_underlying_oracularization` (II:7876, "works (essentially) the same");
  - `cor:comp_sound_combi_detyping` (II:6026, sketch);
  - `fact:padding_properties` (II:6246, no proof);
  - `claim:DeTyping_NFV` (player B "similar, omitted");
  - `thm:ldc-soundness` (II:9885, "a standard reduction");
  - claims 2 and 3 of question reduction's soundness (II:5379).

  On the route the Lean takes, the last three come from proofs the repository already has.
