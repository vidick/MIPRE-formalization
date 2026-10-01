# Audit: the low-individual-degree test in the commuting-operator model

**Date: 2026-10-01. Tree: `main` at `33800f1`, after Phase 5 (#254). Tracking issue: #255.**

After Phase 5 the only open hypothesis of `MIPRE.mipco_eq_core_of_lidt` (`MIPRE/MIPCo.lean:91-92`)
is `MIPRE.LIDT.Simul.SoundCo` (`MIPRE/Background/LIDT/ModelSoundness.lean:151-153`): the seeded,
conditionally linear low-individual-degree test with `r` codewords is sound, with error `deltaSim`,
in the model `S.toModel` of every commuting-operator strategy. That model has an arbitrary unit
vector as state, the first player's algebra is the commutant of the second player's operators, and
the second player's algebra is the commutant of the first (`MIPRE/Foundations/BipartiteModel.lean:259-267`).
The conclusion asks for PVMs `GA` and `GB` in the two algebras, with three inconsistency bounds
(`ModelSoundness.lean:84-96`). `planning/mipco-track.md` (§5, Phase 6; §6, item 12) asked two things
before any Lean is written:

1. **The paper trail.** Is there a complete, checkable argument in the literature that this test is
   sound against commuting-operator strategies, and for which class of strategies?
2. **Formalization.** Which route to a Lean proof of `SoundCo`, or of a weaker hypothesis that
   still gives `MIP^co = coRE`, is feasible, and how large is it?

What was read:

* **Lin.** Lin's *MIP^co = coRE* (arXiv:2510.07162v1, "Lin25"; source in the companion repository
  `vidick/MIPRE-proof` at `ed27cb0`, `paper/external/lin25-mipco/`, added by vidick/MIPRE-proof#4;
  the other companion sources below are read at the same commit). Lin's *tracially embeddable
  strategies* (arXiv:2304.01940v3, "Lin23"; source in `vidick/commuting-repetition` at `8ff85e2`,
  `manuscript/external/Lin2304.01940v3/`).
* **The low-degree literature** (from `paper/external/` of the companion repository unless noted):
  - *Quantum soundness of testing tensor codes* ("TC"): the journal (DAJ) source of arXiv:2111.08131;
  - the companion repository's annotated source of MIP*=RE (arXiv:2001.04383), `paper/ldt.tex`;
  - the low-individual-degree paper of Ji, Natarajan, Vidick, Wright and Yuen ("JNVWY"),
    arXiv:2009.12982;
  - Natarajan–Wright ("NW19"), arXiv:1904.05870;
  - de la Salle's orthogonalization paper ("dlS21"), arXiv:2103.14126;
  - Vidick's almost-synchronous correlations ("Vid21"), arXiv:2103.02468;
  - Chapman–Vidick–Yuen (Discrete Analysis 2026:1).
* **The repository.** The chain from `SoundCo` to the vendored `MIPStarRE.LDT.Test.mainFormal`,
  and the vendored tree `MIPRE/Background/LIDT/MIPStarRE` itself (322 files, 127,925 lines by
  `wc -l` on this tree).

How it was read. Eight readers covered the paper trail and the repository chain; each finding
was checked by an adversarial verifier. Five unverified audits covered the vendored tree by
directory. A critic then compared the route evaluations, and four follow-up checks settled the
critic's main items:
- whether a restricted-class hypothesis suffices;
- whether the semidefinite step blocks a general proof;
- the cost of orthonormalization in finite von Neumann algebras;
- the dimension-free classification of the vendored core.

Every load-bearing citation below was reopened by the writer. Nothing was built.

`vidick/MIPRE-proof` is private. Its contents are paraphrased here, never quoted, and its
review notes are described only by their effect. Mechanisms are classified as follows:

* **D**: dimension-free and state-free. The mechanism holds verbatim for projective measurements
  in two commuting algebras on any Hilbert space, with any vector state.
* **TS**: needs a trace on the relevant algebra, or a synchronous or symmetric strategy, but not
  finite dimension.
* **F**: genuinely finite-dimensional.
* **TP**: needs a tensor-product structure but not finite dimension. This class is added here
  because one mechanism (§4) fits none of the other three.

## 1. Short answer

**No source proves the soundness of any version of the test for commuting-operator strategies
with an arbitrary vector state, so `SoundCo` as stated has no paper trail. A weaker hypothesis
does suffice, and it has a feasible route.**

What the literature does prove:
* JNVWY prove soundness, and the vendored Lean checks it, for **finite-dimensional bipartite**
  strategies with an arbitrary state.
* TC Theorem 4.1 proves soundness for **synchronous strategies on any tracial von Neumann
  algebra, in the trace vector**. That theorem is for a different test (subcube pairs, not
  diagonal lines), for one codeword, and with one consistency bound.
* Lin23 Corollary 4.4 extends this to **tracially embeddable** strategies (state `σ|τ⟩`). It is a
  one-paragraph instantiation of a rounding corollary, Corollary 4.2, which is proved for that
  class. Corollary 4.4 itself gives one bound with a POVM, and its displayed inequality is reversed.
* Lin25 cites these results. Without proof, it asserts that they transfer to the diagonal-line
  test and that they hold for "general" strategies; its proof of the `r`-codeword version is
  incomplete. Lin23 itself leaves arbitrary vector states open.

The weaker hypothesis is `SoundFin`: soundness in every model whose two algebras are mutual
commutants that both carry faithful normal tracial states, with an arbitrary vector state (the
class C of §3.4). A follow-up check of the code finds that `SoundFin` suffices for
`MIP^co = coRE`: the vendored, proved tracial density theorem supplies the analytic input, and the
plumbing is roughly 0.75–1.25k lines. This is an analysis of the code, not yet a Lean proof; the
first step of the recommended route turns it into one.

On class C, the vendored JNVWY proof transfers almost entirely. Everything is D except three
isolated steps:
* swap symmetry, which a direct-sum doubling makes D;
* the semidefinite program of JNVWY Lemma 9.2, which becomes TS through the trace;
* orthonormalization, which becomes de la Salle's Theorem 1.2 on finite algebras.

**The recommended route** is this port (Route A2 of §5). It needs roughly 70–120k new lines,
mostly mechanical restatement of machine-checked content, plus an orthonormalization tier. That
tier is about 4–8k lines if the class is restricted to type II₁ algebras; otherwise it needs a
measurable-selection step that has no complete written argument.

Proving `SoundCo` itself (Route A1) is not ruled out. It depends on two things: an operator-dual
construction for arbitrary von Neumann algebras, which exists only as an unreviewed derivation
made during this audit, and the general orthonormalization tier, which is unformalized and partly
research-grade.

## 2. The paper trail

| link | what it covers | status | defects (severity) |
|---|---|---|---|
| Lin25 `thm:soundnessQLDT` (CondLineardist.tex:337-346) | synchronous strategy on `L²(𝒜,τ)` in the trace vector; one PVM `G ⊂ 𝒜′`; one point bound | **cited** (header: "Theorem 4.1" of MIP*=RE; text :348: TC Theorem 4.1) | header key wrong (major); "directly applied" to diagonal lines asserted (major); extension to tracially embeddable strategies by one sentence citing Lin23 Cor 4.4 (blocker for `SoundCo`) |
| Lin25 `lem:simuQLID` (Answerreduction.tex:257-274) | `r` codewords, CL-sampled; synchronous in the statement, `σ\|τ⟩` written, `\|τ⟩` used; one bound | **proof in text, incomplete** | simulated strategy misanswers diagonal lines (:318-321, major); its success is asserted (:324, major); union bound written as product (:328, minor); random default makes `G` a POVM (:330, minor); the measurement `P` is defined only in commented-out lines (:300-305); the "general strategy" remark (:347) cites a clause the lemma does not have |
| MIP*=RE "Theorem 4.1" | in the companion source 4.1 is a Definition (`paper/linear.tex:35`); low-degree soundness is Theorem 7.8 (`paper/ldt.tex:450-482`): finite-dimensional tensor-product, arbitrary pure state, three bounds | **proved** in the companion source, by reduction to TC Theorem 4.7 | F through TC Theorem 4.7; the reduction itself is D. The companion source replaces an identification of the two games, made in the version Lin cites, with that explicit reduction (`ldt.tex:506-520`, `521-781`) |
| TC `thm:main` = Thm 4.1 (mainloop.tex:124-134) | synchronous strategy, normal tracial state, any von Neumann algebra; augmented test (axis lines + subcube **pairs**); one codeword; one PVM `G ⊂ 𝒜`, one bound | **proved**, TS + D | the companion repository records corrections, all repairable in the tracial setting and none using dimension; test differs from the diagonal-line test (major) |
| TC `thm:main-bipartite` = Thm 4.7 (extensions.tex:67-79) | **finite-dimensional** tensor-product strategies, arbitrary state; three bounds, PVMs | **proved**, F | commuting-operator strategies explicitly set aside (:18); Schmidt decomposition (:139); the companion repository records corrections to its transfer step, all made in finite dimension |
| Lin23 Cor 4.2 (Rounding.tex:24-41; proof RoundingProof.tex:329-387) | transfer from synchronous tracial soundness to `δ`-synchronous **tracially embeddable** strategies | **proved**, TS | POVMs passed to the projective case (minor); per-`λ` choices integrated without measurability (minor); Lemma A.3's C*-algebra proof invalid, statement true in von Neumann algebras (minor); `κ` quantified per strategy but used uniformly (minor); value comparison cites Thm 4.1 for what it does not state (minor) |
| Lin23 Thm 4.3 (Rounding.tex:48-55) | synchronous tensor-code soundness | **recalled, not proved**; attributed to MIP*=RE, matches TC Thm 4.1 | misattribution; displayed inequality reversed (:53) |
| Lin23 Cor 4.4 (Rounding.tex:57-63) | tracially embeddable strategies, pair test, one codeword | **no proof environment**; one paragraph (:56) plugs Thm 4.3 into Cor 4.2 | one bound only, `G` a POVM though called projective (RoundingProof.tex:338-343), inequality reversed (:60) (major for `SoundIn`'s shape) |
| Lin23 Thm 3.2, density (Tracialemb.tex:10-16) | `ℓ¹`-closure of tracially embeddable correlations = `C_qc`, common alphabets, POVMs | **proved**, and proved again in vendored Lean | one justification wrong in the source, repaired in Lean |
| NW19 Thm 4.43 (`nw19/main_combined.tex:3024-3039`) | simultaneous plane-vs-point, **total** degree; symmetric tensor-product strategies; one POVM | **proved** by reduction to Thm 4.40 (itself cited) | the reduction is D; the companion repository records corrections up to constants; Lin25's own commented remark (CondLineardist.tex:352) says it works only for tensor products |
| dlS21 Thm 1.2, Prop 7.1 (`delasalle/orthogonalization.tex:126-128`, `:364-411`) | any von Neumann algebra, any normal state; Prop 7.1 for normal positive functionals | **proved** (Prop 7.1 cites Pisier's minimax lemma; Thm 1.2 cites Takesaki for the type and center-valued-trace structure) | Borel selection in the type I case asserted "by inspection" (:236, minor) |
| Marrakchi–de la Salle, arXiv:2307.08129 | a "type III" Connes lemma and rounding for infinite-dimensional strategies, per its abstract (Lin23 `Bibfile.bib:428-437`) | **not read**: no source in any repository here | whether it transfers operators (not just correlations) for arbitrary vector states is undetermined |

### 2.1 Lin25

`thm:soundnessQLDT` is stated for a synchronous strategy `(L²(𝒜,τ), |τ⟩, {A})` and concludes a
single PVM `G` in `𝒜′` whose evaluations agree with the point measurements in the trace vector
(CondLineardist.tex:337-346). It carries no proof.

**Citations.** The header cites "Theorem 4.1" of MIP*=RE, while the following paragraph (:348)
cites Theorem 4.1 of TC and says it can be "directly applied" because individual-degree
polynomials form a tensor code. Lin's other pinpoints into MIP*=RE place its tests in Section 7,
and his own commented-out remark (:352) cites the MIP*=RE theorem as 7.8. So the header key is
very likely a slip for TC; the arXiv numbering of MIP*=RE itself was not available offline.

**What is asserted without proof.** The same paragraph asserts the extension to "general
tracially embeddable strategies" by citing Lin23 Corollary 4.4. In the source version of TC read
here, the test analysed has subcube pair questions, not diagonal lines (TC mainloop.tex:49-90).
Lin credits the diagonal-line test to TC (CondLineardist.tex:333), which does not hold for this
version. A commented-out passage in TC's introduction (intro.tex:344-348) suggests an earlier
formulation with lines through two points; the arXiv version Lin cites was not available.

**`lem:simuQLID`.** The lemma (Answerreduction.tex:257-274) calls the strategy synchronous but
writes its state as `σ|τ⟩`; its conclusion and proof use `|τ⟩` and one family. The two
statements that `SoundIn` would need, a second PVM against the other player's points and the
mutual bound, survive only as commented-out lines (:271-272). The proof is described as a
"slightly modified" NW19 Theorem 4.43 (:294), and the author's comment just before it (:296)
flags a possible problem. Its defects are listed in the table above. The appendix that was to
prove the parallel version is commented out of the main file (`MIPco=core.tex:464`) and absent
from the source, and a commented note at :342-345 says the write-up is unfinished. The closing
remark (:347) extends the lemma to general strategies by substituting Lin23 Corollary 4.4.

**Where the forms are used.** Lin's answer reduction first rounds to a synchronous strategy at
the value level (ARsoundnessproof.tex:16-20, citing the rounding theorem restated at
Preliminary.tex:563-572). It then uses only the synchronous, one-sided forms, together with
op-switching in the trace vector (:114-146). Lin's compiled introduction says the same: the
test's soundness is known only for synchronous strategies, and rounding handles the rest
(Introduction.tex:305).

In the synchronous trace-vector case the one-sided conclusion does yield all three of `SoundIn`'s
bounds. Take `GB := G` and `GA` its op-preimage: the second bound follows by traciality, and the
third is zero for a PVM. This requires `𝒜` to be a double commutant (verified from
Preliminary.tex:281-286, :523). No source does the same for `σ|τ⟩` or for arbitrary states.

**The Pauli basis test.** Lin's Pauli basis test does not use the low-individual-degree test
(Introduction.tex:268, :292; Introspection.tex:206, via Lin23 Theorem 6.4). The repository
instead derives `QLD.SoundCo` from `LIDT.Simul.SoundCo`.

### 2.2 Lin23

`thm:soundnesstensorcode` is Corollary 4.4 in v3; all of Lin25's citations of Lin23 match v3's
numbering. Lin25's bibliography, however, points to a January 2024 version, which was not
available.

**Corollary 4.4.** It is Corollary 4.2 instantiated with Theorem 4.3 (Rounding.tex:56), and it
has no proof environment.

**Corollary 4.2.** Its proof (RoundingProof.tex:329-387) is TS. It proceeds in three steps:
1. cut `σ` by its spectral projections `P_λ`;
2. round to synchronous strategies on the corners `P_λ𝒜P_λ`, and apply the synchronous hypothesis
   on each corner, where the corners are general tracial von Neumann algebras;
3. glue the per-corner measurements into a POVM `H` with `σHσ = ∫P_λG^λP_λ dλ`.

Its inputs are de la Salle's Theorem 1.2 and Connes' joint-distribution lemma, both cited, plus
a Douglas-type factorization.

**Scope.** Only tracially embeddable strategies (Definition 3.1, Tracialemb.tex:3-5): state `σ|τ⟩`
with `σ ∈ 𝒜⁺`, the first player in `𝒜`, the second in `𝒜′`. Lin23 itself asks, as an open
question, whether the state may be an arbitrary vector of `L²(𝒜,τ)` (Introduction.tex:72). Lin23
mentions that Marrakchi and de la Salle obtained the commuting-operator rounding independently,
through a type III version of Connes' lemma (Introduction.tex:30); that paper was read by no one.

### 2.3 MIP*=RE, tensor codes, NW19

**MIP*=RE.** The companion source proves its simultaneous low-degree soundness (Theorem 7.8) in
three steps (`paper/ldt.tex`):
1. an explicit D reduction from the seeded game at one codeword to the two-prover tensor-code test
   (:521-781);
2. TC Theorem 4.7, which is F;
3. for `r` codewords, a D combine reduction that imports nothing (:809-1526).

The repository's adapters (`Padding`, `Extraction`, `Simultaneous`) implement the third step, and
the `r = 1` case goes through the vendored JNVWY proof instead.

**Tensor codes.** TC Theorem 4.1 is the only literature theorem that covers infinite-dimensional
strategies. Its mechanisms are TS or D:
- τ-norm calculus and prover switching by cyclicity;
- de la Salle's Theorem 1.2 for orthogonalization, and Proposition 7.1 in place of semidefinite
  duality;
- a Bernoulli-tail bound through the spectral measure of one operator (pasting2.tex:704-810);
- an expander lemma valid for any positive functional.

Two TS steps resist a non-tracial rewrite, at pasting2.tex:692 and at the projectivity rotation
(self-improvement.tex:326-333; §4.2).

TC Theorem 4.7 is stated for finite-dimensional tensor-product strategies (extensions.tex:9). It
sets commuting-operator strategies aside (:18), and its transfer step is SWAP symmetrization,
Vid21 Corollary 4.1 and a Schmidt decomposition (:95-139). Vid21 is finite-dimensional by
convention (`vid21/prelim.tex:7`); an author's comment there notes that an infinite-dimensional
version would need an infinite-dimensional orthonormalization lemma (`vid21/me.tex:169`), which
dlS21 Theorem 1.2 now provides.

**NW19 Theorem 4.43.** Its combine-and-extract reduction is D. The theorem is therefore valid for
whatever class the single-polynomial theorem covers, and that bounds what Lin's remark at
Answerreduction.tex:347 can reach: tracially embeddable strategies, not arbitrary ones.

### 2.4 Answer to question (1)

A complete argument exists in two models:
* **Finite-dimensional bipartite strategies with any state:** JNVWY, machine-checked here, and
  MIP*=RE through TC Theorem 4.7.
* **Synchronous strategies on any tracial von Neumann algebra, in the trace vector:** TC Theorem
  4.1, for the pair test and one codeword.

For tracially embeddable strategies, the argument is complete up to repairable gaps for the pair
test and one bound (Lin23 Corollary 4.2 combined with TC Theorem 4.1). It is incomplete for the
diagonal-line test, for `r` codewords, and for the three-bound PVM shape (§5, gaps G1 and G2).

For arbitrary commuting-operator strategies with an arbitrary vector state, `SoundCo`'s class,
there is no argument in any source read. The one candidate that might give an operator-level
transfer, arXiv:2307.08129, is unread.

## 3. The repository's hypothesis and its minimal core

### 3.1 From `SoundCo` to `mainFormal`

| link | file:line | mechanism |
|---|---|---|
| `SoundCo` = `SoundIn S.toModel` for every `S` | `ModelSoundness.lean:151-153` | — |
| `SoundIn` has only its tensor instance `soundIn_tensor` | `ModelSoundness.lean:129-143` | — |
| `clSoundness`: trivial branch when `m + r > q`, else padding | `Simultaneous.lean:306-341` | D |
| padding is `S.adapt`, seed fixed by averaging | `Padding.lean:868-886` | D |
| `r` → 1 extraction (Schwartz–Zippel, Born bookkeeping) | `Extraction.lean:409-768` | D |
| seeded game → canonical-line `lidtGame`, coordinate reversal | `Adapter/Reduction.lean:126-130`, `223-303` | D |
| `lowIndividualDegree_soundness` = `Bridge.soundness` | `LIDT/Soundness.lean:47-60` | F container (pure state as `dim·\|ψ⟩⟨ψ\|`), 1,471 lines |
| `mainFormal` | `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:315-342` | §4 |

Every link above `mainFormal` is classical post-processing inside one fixed model. Each one
already has a model counterpart (`ProjStrat.adapt`, `exists_one_sub_povmValue_adapt_le`,
`inconsistency_map_equiv`), but is written for `TensorProductStrategy` and matrices (the
repo-chain reader's finding, confirmed by its verifier). Restating the operator parts over
`BipartiteModel` is estimated at 1–1.5k lines. The classical parts (about 2.8k lines in
`Adapter/{Geometry,Parameters,Reparam,Weights}`) are reused unchanged.

`mainFormal` is more general than JNVWY's statement:
* the strategy is two-space and non-symmetric;
* the state is any mixed density, read as `Re tr(ρX)/|ι|` (`LDT/Basic/QuantumState.lean:40-47`,
  `189-191`);
* the conclusion is two PVMs with three bounds at `10^5 k² m⁴(ε^{1/40000} + (d/q)^{1/40000} +
  e^{-k/(2.56·10^6 m²)})`, for `k ≥ 400md`.

### 3.2 The minimal core

**`T(M)`**: the model form of `lowIndividualDegree_soundness`. It covers the canonical-line
`lidtGame` with one codeword and no seed: for `M.ProjStrat (lidtGame F m d)` with value at least
`1 − ε` and `k ≥ 400md`, `k > 0`, it gives PVMs `GA ∈ 𝒜` and `GB ∈ ℬ` with the three bounds at
`lidtError`.

All adapters act inside the same model (`Padding.lean:868-870`, `Reduction.lean:126-130` are
`S.adapt`), so `T(M) ⇒ SoundIn(M)` holds model by model, with no closure assumption. The bridge
is not needed if `T` is proved on the model directly.

### 3.3 Where the hypothesis is consumed

There are exactly two sites, and neither has a tracial state.

* **Answer reduction.** `val_ge_of_arStrategy` (`AnswerReduction/SoundFinal.lean:195-205`) is
  generic in the model: it needs `SoundIn M`, `ω.OracularSound` and `ω.Dominates M`. The only tie
  to `S.toModel` is at :333-336, through `exists_projStrat_lt_commutingOperatorValue`
  (`Foundations/ModelStrategy.lean:358-363`). That lemma projectivizes a near-optimal strategy
  with one-sided basis-vector ancillas: state `ψ ⊗ e_{inl a₀}`
  (`Foundations/CommutingDilation.lean:175-209`).
* **Pauli basis test.** `QLD.soundIn_of_lidt` (`QLD/Soundness.lean:360-371`) asks for `SoundIn`
  in every unit-vector expansion `M.expand e`. It uses only `padE = |t₀t₀⟩ ⊗ EPR` and its swap
  (`QLD/PhysModel.lean:125-128`, `:150-151`). `QLD.ApproxSoundIn` (`QLD/ModelSoundness.lean:185-195`)
  quantifies over models, and `approxSoundIn_commuting` (:197-200) is again the only tie to
  `S.toModel`.

### 3.4 Sufficiency of a restricted class

The class **C**, for "finite pairs", contains every model `(H, ψ, 𝒜, 𝒜′)` where:
* `𝒜 ⊆ B(H)` with `𝒜 = 𝒜″`, and `H : Type`;
* both `𝒜` and `𝒜′` carry faithful normal tracial states. In Lean, "normal" is best given as a
  finite sum of vector functionals, since a single vector state does not survive amplification;
* `ψ` is any unit vector.

The proposed hypothesis is `SoundFin := ∀ M ∈ C, SoundIn M`. A follow-up check of the code
answered the critic's first item: **`SoundFin` suffices for `MIP^co = coRE`**. This settles what
the repo-chain and alternatives verifiers had left "unclear". The argument has four parts.

* **The value lemma.** For finite `X, Y, A, B : Type` and `0 ≤ t < ω_co(G)`, some projective
  strategy in some model of C has value above `t`. (The "`ω_co − η`" form fails when an alphabet
  is empty.) The analytic content is the vendored, sorry-free
  `CommutingRepetition.strict_tracial_reduction`
  (`Repetition/CommutingRepetition/Tracial/Reduction.lean:335-357`). It combines Lin23's density
  theorem with tagging to common alphabets, `ℓ¹` continuity of the winning probability and
  detagging, and returns an exact `TracialStrategy.{0}`. Earlier readers had listed tagging and
  continuity as missing; they are not.
* **The tracial model lies in C.**
  - Take `𝒜 := vnAlg = R(A)′` and `ℬ := R(A)″` (`VN/ConcreteVN.lean:150-151`). Both are
    centralizers, so their order structure comes from `starOrderedRing_centralizer`, and the
    bicommutant theorem, which Mathlib lacks, is not needed.
  - Traciality on `R(A)′` is vendored (`traceState_mul_comm_vn`, `ConcreteVN.lean:194-201`).
  - Traciality on `R(A)″` follows from `J R(a) J = L(a*)`, and faithfulness on both from
    cyclicity of the trace vector. Both are new, about 200–300 lines.
* **Projectivization and closure.**
  - `exists_pvm_dilation_ge` (`Foundations/KrausDilation.lean:113-121`) dilates POVMs in any
    star-ordered ring into `M_K(𝒜)`.
  - The commutant of an amplification is formalized generically
    (`Foundations/AmplCommutant.lean:360-391`). The correct one-sided identity is
    `(𝒜 ⊗ M_k)′ = 𝒜′ ⊗ 1`.
  - C is closed under `M.expand e` for every unit `e`, with traces amplified as
    `|α|⁻¹ Σ_i φ(X_ii)`; this is about 300–500 lines. It is also closed under the player swap and
    under one-sided basis-vector ancillas, so the consumers need no narrowed binder.
* **Consumers.** At `SoundFinal.lean:333-334` only the call to the value lemma changes, and
  `soundIn_of_lidt`'s binder is discharged by closure. In `MIPCo.lean` only the hypothesis type
  changes. Total: roughly 0.75–1.25k lines, all under `MIPRE/Background` because it names
  `CommutingRepetition`. Confidence in the size is low; confidence in the structure is high.

**Lin's class B** (standard form `L²(𝒜,τ)`, state `σ|τ⟩`) is contained in C. Using B instead adds
roughly 0.6–1.25k lines of plumbing:
* a matched two-sided dilation, because answer-reduction games have different answer alphabets;
* density bookkeeping `σ ⊗ √K E_{t₀t₀}` through the expansions;
* a narrowed binder in `soundIn_of_lidt`;
* `J` for the swap.

**A tracial-state class** (`σ = 1`, the class of TC Theorem 4.1 and of `thm:soundnessQLDT`) does
**not** suffice as the code stands. It is closed neither under the `|t₀t₀⟩` pad nor under any
basis-vector ancilla, and density does not deliver it.

`SoundFin` and `SoundCo` are incomparable as statements. `SoundCo` returns `GA` in `{F}′`, which
can be all of `B(H)` (`BipartiteModel.lean:259-267`), while C contains pairs that are not of the
form `S.toModel`. What `SoundFin` buys is that a proof may use traces on both algebras.

## 4. The vendored proof

Counts are `wc -l` from one run on this tree. Classifications come from the five directory
audits and the follow-up check of their D classification: a keyword census of every file,
inspection of every hit, and an inventory of every definition that produces an operator. They
are not a line-by-line reading.

| directory | lines | role | D / TS / F | blocks transfer | replacement |
|---|---:|---|---|---|---|
| `LDT/Basic` | 8,188 | states, `ev`, placements, measurements; classical field/line/polynomial layer (≈5.2k) | D; F only in form (density with `tr/\|ι\|`) | matrix carrier | vector state on a model; classical layer reused |
| `Quantum` | 1,852 | finite matrices; `ProjectorONB`, `FiniteHilbert`, `TracePairing`, `FiniteConicDuality` | ≈1.1k F (feeds only orthonormalization and the semidefinite program) | — | dropped with those two |
| `LDT/Test` | 11,256 | role-register symmetrization (≈4k), unsymmetrization, final completion and triangle steps, scalar cascade (2.3k) | role register TP; rest D; `PermInvState` swap symmetry | tensor role register | `H ⊕ H` doubling (below) |
| `LDT/Preliminaries` | 9,114 | state-dependent distance and consistency calculus | D; 12 declarations use swap symmetry | matrix carrier | overlaps `Foundations` calculus (≈6.4k) |
| `LDT/MainInductionStep` | 10,174 | induction on `m`; assembly; ≈2.5k scalar arithmetic | D; 2 swap uses; consumes the slice witness `Z^x` | the semidefinite interface | — |
| `LDT/Pasting` | 30,290 | pasting, Bernoulli tails | D; "matrix Chernoff" is a CFC lift of a scalar Hoeffding bound with no dimension factor (`Pasting/Bernoulli/MatrixChernoff.lean:93-167`); 9 swap uses | output is a POVM | — |
| `LDT/Commutativity`, `CommutativityPoints` | 13,399 + 3,464 | commutation of `G` | D; ≈10 swap uses | — | — |
| `LDT/GlobalVariance` | 5,295 | global variance | D; 4 swap uses | — | — |
| `LDT/ExpansionHypercubeGraph` | 3,808 | hypercube spectral gap (scalar, ≈2.3k); `localToGlobal` | D in content; local-to-global proved with (Laplacian ⊗ density) and a trace | matrix proof | Gram positivity, est. 200–400 lines |
| `LDT/SelfImprovement` | 20,417 | `Theorems` 16,353 (D, 17 swap uses); `MatrixRealization` 3,667 + `SdpMatrixBridge` 313 (the semidefinite program) | **F** (semidefinite program) | the program (§4.2) | TS via a trace on C; open for A1 |
| `LDT/MakingMeasurementsProjective` | 10,268 | orthonormalization: ≈4.1k D (consistency ⇒ almost projective, CFC completeness); ≈3.7k F core | **F** (rank, SVD, finite spectrum) | the F core | dlS21 Thm 1.2 (§4.3) |
| `LDT/Tactic` | 400 | automation keyed to matrix lemma names | — | — | retarget |

### 4.1 Representation-only finiteness and swap symmetry

The vendored state is a general mixed state, never a tracial one. Trace cyclicity is used only to
move `ρ` or a conjugation (`LDT/Basic/OperatorExpectations.lean:288-306`). `Fintype.card` of a
Hilbert carrier appears only to normalize. The tree also has 116 entrywise `ext` proofs, which
must be rewritten as `*`-homomorphism identities rather than translated.

**Swap symmetry.** About 50 uses of `PermInvState` (`LDT/Test/StrategyCore.lean:168`) need only
three facts, never the swap of an arbitrary joint operator outside `Test`:
* `ev(X ⊗ Y) = ev(Y ⊗ X)`;
* `ev(M ⊗ 1) = ev(1 ⊗ M)`;
* symmetry of consistency relations.

The role-register symmetrization (`LDT/Test/StrategyBiProj/*`) builds on `C² ⊗ H` role registers
and is **tensor-product-specific (TP), not finite-dimensional**. This corrects the ji2021
reader's F, which its verifier refuted (JNVWY `ji2021-low_degree.tex:4102-4135`). The plan lists
it among the F mechanisms (`planning/mipco-track.md:604-609`).

**The commuting replacement** is the doubled model: `K = H ⊕ H`, state `(ψ ⊕ ψ)/√2`, local algebra
`𝒜 ⊕ ℬ` placed as `a ⊕ b` on the left and `b ⊕ a` on the right, and the flip `J`. It is D:
* `(𝒜 ⊕ ℬ)′ = ℬ ⊕ 𝒜` when `𝒜′ = ℬ` and `ℬ′ = 𝒜`;
* `J` fixes the state;
* the role-average identity is the two-line computation
  `⟨Ψ, L(x)R(y)Ψ⟩ = ½(⟨ψ, x₁y₂ψ⟩ + ⟨ψ, x₂y₁ψ⟩)`;
* extraction to `𝒜` and `ℬ` is by components, which preserves projections.

Four readers proposed it independently, but **it appears in no source and needs a written proof**.
The core must then be stated for an algebra pair: symmetrizing `S.toModel` itself would enlarge
the first algebra. The doubled model of a C-model is again in C, with trace `(τ_𝒜 + τ_ℬ)/2`.

**Membership.** Every operator the symmetric core constructs lies in `𝒜 ⊕ ℬ` once its inputs do:
sums, products, adjoints, averages, completion by `1 − total`, CFC square roots and polynomials.
The exceptions are three external inputs:
* the semidefinite pair `(T, Z)`, with `Z` carried into pasting as the slice witness
  (`LDT/Test/StrategyPolynomialFamilies.lean:257-275`);
* the orthonormalized measurement inside self-improvement (`SelfImprovementTop/Core.lean:433-436`);
* the final heterogeneous orthonormalization (`SourceRoleRegister/Core.lean:482-547`).

The core's output is a POVM (`MainInductionStep/Theorems/MainTheorems/Successor.lean:323-337`), so
a final projectivization is needed in every model.

### 4.2 The semidefinite program (JNVWY Lemma 9.2)

JNVWY's Lemma 9.2 (`ji2021-low_degree.tex:5174-5180`) is a strong duality in the dimension of the
local space. The finite steps are compactness through `Fintype.card` of the carrier with a
convergent subsequence (`LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Separation.lean:144-190`),
and an objective in the unnormalized trace.

It enters only through `SdpStatementWithSlackness` (`LDT/SelfImprovement/Theorems/Statements.lean:112-118`):
a measurement `T` and an operator `Z ≥ A_g` with `T_g Z = T_g A_g`. Every consumer uses only the
summed form: a measurement `T` in the player's algebra with `Z := Σ_g T_g A_g` self-adjoint and
`Z ≥ A_g` for all `g`.

* **On class C (TS).** Maximize `Σ_g τ(T_g A_g)` over measurements in `𝒜 ⊕ ℬ` with its faithful
  normal trace. A maximizer exists by σ-weak compactness, and first-order (Holevo-type)
  optimality conditions give the summed form. Equivalently, apply Prop 7.1 with
  `φ_g = τ(· A_g)`. Two readers derived this independently; it is not published in this operator
  form. Mathlib lacks the inputs: weak-operator compactness of measurement tuples (the vendored
  `VN/Modular/WOTCompact.lean` gives a cluster point for one sequence only) and an API for
  normal traces. Estimate 0.5–4k lines.
* **Functional duality alone fails at one step.** dlS21 Proposition 7.1 holds for normal positive
  functionals on any von Neumann algebra without a trace. Applied to `φ_g = ⟨ψ, · B_g ψ⟩` it
  supplies completeness, boundedness and both pasting uses, but not JNVWY's step at
  `ji2021-low_degree.tex:5674-5676`. That step tests `Z ≥ A_{h′}` against a weight
  `H^u_{h′} = A^u T_{h′} A^u` built from `T` itself, while Proposition 7.1 dominates only
  functionals fixed in advance. The natural substitute reintroduces the inconsistency `ν` into the
  self-consistency error and collapses the induction (`ji2021-low_degree.tex:4393`, `:4605`, `:4650`). TC's own
  self-improvement closes the corresponding step only by cyclicity of `τ` (self-improvement.tex:326-333),
  so a "trace-free Proposition 7.1" does not rescue a native bipartite tensor-codes proof either.
  This is a follow-up's analysis at medium confidence.
* **For arbitrary von Neumann algebras (A1).** A follow-up derived, outside any source, that the
  summed operator form exists in every von Neumann algebra:
  1. solve the problem in Haagerup's tracial subalgebras of the crossed product;
  2. take a weak-operator cluster point;
  3. pass the inequalities to the limit on a dense set;
  4. compress back by a bimodular map;
  5. in a commuting-operator model, compress first to `[M′ψ]`.

  The hard ingredients (crossed product, `ℛ_n`, `Φ_n`, the convergence `Φ_n(x)Ω̂ → xΩ̂`) are
  already proved in the vendored `CommutingRepetition/VN/Haagerup/*`. The bimodular compression
  is new. Estimate 1.5–3.5k lines, **unreviewed**: it needs an operator algebraist's check before
  anything relies on it.

### 4.3 Orthonormalization

The F core is a rank count, an SVD-style coisometry and a step-function CFC legal only on finite
spectrum (`MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean:43-66`, `:736-746`;
`SpectralTruncation/ProjectiveNonMeasurement.lean:60-77`). The replacement is dlS21 Theorem 1.2:
in any von Neumann algebra with any normal state, a POVM with `φ(Σ a_i²) > 1 − ε` is within `9ε`
of a PVM in the same algebra. That linear error is no worse than the vendored `100ζ^{1/4}` on
`[0, 1]`, but the scalar cascade must be re-derived.

The vendored Lean (`MIPRE/Background/Orthonormalization/Axioms.lean`) proves it unconditionally in
three cases: every algebra on a finite-dimensional space, `B(H)`, and II₁ factors with trace-class
trace and state. In general it proves it only conditionally on `MvNStructureTheory`
(`Orthogonalization/MvN/Interface.lean:47-108`). The finite case,
`orthAtN_fin_of_isFiniteProj` (`MvN/Finite.lean:322-339`), uses five fields:

| field | content | status | upstream tier (`commuting-repetition/orthogonalization/PLAN.md:121-134`) |
|---|---|---|---|
| H0 | normal ⇒ trace-class form | **not needed** for vector states (one vector suffices) | none |
| H1′ | finite = type I ⊕ type II₁ | open; est. ≤ 1k | none |
| H3 | center-valued trace with comparison | proved only for II₁ factors; non-factor tracial case est. 2–4k | T4a (factors only; built in 1,443 lines against an 8–12k estimate) |
| H5 | type I selection with diffuse center | open; the source asserts the Borel selection "by inspection" (`orthogonalization.tex:236`) | T4c: "?", research-grade |
| H6 | polar decomposition | **proved** (`exists_polar`, `MvN/PolarDecomp.lean:288-293`) | — |

H1, H2 and H4 (type decomposition, semifinite nets, type III halving) are used only by the general
case. They are tier T4b, estimated at 15–30k lines; that figure belongs to Route A1, not to the
finite tier. Earlier route evaluations attached it to the finite tier and counted H6 as open; both
are corrected here. Upstream's built tiers came out 2–8 times smaller than estimated, so no
upstream number is a measurement.

There are three ways to avoid H5 on class C:
* **(i) Prove it.** Research-grade; no complete written argument exists.
* **(ii) Restrict to type II₁.** Amplify by a II₁ factor `R` in the value lemma. This keeps
  correlations and C-membership, removes type I parts, and leaves H3 for non-factors. It needs a
  constructed II₁ factor, which neither repository has, plus the center of the tensor product.
  Estimate 4–8k lines in total.
* **(iii) Embed into a II₁ factor.** Then the unconditional tier applies, but the embedding is in no
  source and cannot be sized.

Orthonormalization in `𝒜 ⊕ ℬ` reduces to each summand separately.

The blueprint's `rem:orthonormalization-scope` announced seven classical fields but listed six,
omitting polar decomposition, which is proved; and it called the II₁-factor tier the case a tracial
strategy lives in, which holds only for II₁ factors. Both are repaired in the pull request that
adds this report.

## 5. Routes

| route | target | verdict | main blockers | size (new Lean lines; basis) |
|---|---|---|---|---|
| **A2** port JNVWY to class C | `T(M)` for `M ∈ C`, hence `SoundFin` | **feasible; recommended** | `H ⊕ H` doubling unsourced; semidefinite replacement unpublished in operator form; orthonormalization tier | 70–120k + tier (4–8k via II₁ restriction; unbounded via H5). Basis: ≈90–100k touched vendored lines restated at 0.65–1.0 (Phase 5 restated in place at ≈1:1, `mipco-track.md:598-602`; not measured on vendored code) + 1–2k doubling + 0.5–4k semidefinite program + ≈1k orthonormalization adapter + 0.5–2k cascade + 1–1.5k adapters + 0.75–1.25k plumbing |
| **A1** port to every `S.toModel` | `SoundCo` itself | **open**; not research-blocked at the semidefinite step if §4.2's derivation survives review | operator dual in arbitrary algebras (unreviewed); general orthonormalization tier (H1, H2, H4, general H3, H5) | A2 − plumbing + 1.5–3.5k + 15–30k (T4b estimate) + H5 (unsized) |
| **A3** synchronous tracial port | standard form, trace vector | dominated by A2 | as A2, plus rounding and consumer redesign; the right action `J·*J` reverses products | > A2 |
| **B** Lin's architecture | `SoundIn` on class B (`σ\|τ⟩`) | feasible but no better than A2 with the same core; natural only with core C1 | as the chosen core, plus B-only plumbing | core + 1.4–2.5k plumbing |
| **C1** tensor codes, tracial | TC Thm 4.1 + Lin23 Cor 4.2 → class B | conditional | G1: one-sided POVM → two PVMs and three bounds for `σ\|τ⟩`, in no source; G2: synchronous diagonal-line → pair-test reduction, unwritten (tensor-model D version at `ldt.tex:521-781`); Prop 7.1 unformalized (Jordan decomposition, predual, Pisier minimax); Connes' lemma unformalized; recorded errata | 55–80k + unknowns: core ≈40k (25–55k; TeX ratio 2,758 non-comment lines against 8,296 for 128k Lean, or a byte ratio of 0.34), 3–5k reduction, 5–10k rounding, 1–3k Connes, Prop 7.1 and G1 unsized |
| **C2** tensor codes, native bipartite | `SoundCo` | **not viable** as written | fails at the projectivity rotation (self-improvement.tex:326-333) and at pasting2.tex:692 without cyclicity | — |
| **D** synchronous core + value-level rounding | rounded games only | dominated | rounding theorem (#23) unformalized; no synchronicity lemma for the answer-reduction game (`reports/co-generalization-audit.md:262-268`); the Pauli-basis consumer applies the hypothesis in a non-tracial pad (`PhysModel.lean:125-128`) | 70–190k |
| **E** Lin's LIDT-free Pauli basis test | removes the QLD consumer | unexplored | Lin23 Thm 6.4 covers only tracially embeddable strategies; its appendix and de la Salle's arXiv:2204.07084 were not read | unknown |
| **F** POVM-valued `SoundIn` | drops the final orthonormalization | unexplored | consumers build projective decoded strategies (`AnswerReduction/SoundDecoded.lean:104-123`); dilation keeps `≃` but not `≈` (`ji2021-low_degree.tex:2862-2884`); the orthonormalization inside self-improvement stays | small if it works |

### 5.1 Notes

**Why A2 and not C1.** On paper the tensor-codes core is two to three times shorter. The A2 port,
however, transfers a proof that is already machine-checked, natively two-family, three-bound and
PVM-valued, with every new mathematical step isolated as one standalone lemma:
* the doubling;
* the summed semidefinite form;
* orthonormalization in a finite algebra.

C1 adds a rounding layer, one unsourced step (G1), a written-but-unported reduction (G2), an
unformalized Proposition 7.1, and a paper with recorded errata. No size here has a measured basis,
and the critic was right that the routes' estimates are heuristic ratios that disagree.

**What A2 does not settle.** `SoundFin` replaces `SoundCo` as the hypothesis of the main theorem.
`SoundCo` as stated remains open (A1).

**Issues on the tracker.**
- #23 (the rounding lemma for almost-synchronous correlations, commuting case) is Route D's
  rounding input; #22 is its finite-dimensional case. Route A2 needs neither.
- #29 (the tracial value is at most the commuting-operator value) is not on A2's path either. The
  value lemma of §3.4 approximates `ω_co` from below by tracially embeddable strategies, through
  `strict_tracial_reduction`.

**Error constants.** `SoundIn` hard-wires `deltaSim` with exponent `clB = 1/40000`
(`LIDT/Simultaneous.lean:115-120`, `Adapter/Parameters.lean:49-60`). A2 preserves the vendored
cascade, and dlS21's linear error only improves it. C1 and D have unknown exponents (TC's core
gives 1/16 before rounding) and may need the stage constants re-chosen, following the `withConst`
precedent of `repetitionCo`.

### 5.2 Recommendation

Take Route A2, in this order.

1. **The conditional theorem** (≈2–3k lines, no new analysis):
   - define class C and `SoundFin`;
   - prove the value lemma from `strict_tracial_reduction`, closure under expansion, and the
     consumer restatements, giving `mipco_eq_core_of_lidtFin : SoundFin → MIPCo = IsCoRE`;
   - restate the adapters, so that `SoundFin` reduces to `T(M)` on C.

   This de-risks the architecture before any port.
2. **Three paper proofs, before porting:**
   - the doubling, over an algebra pair, with extraction and projectivity;
   - the summed semidefinite form on a finite von Neumann algebra with a faithful normal trace;
   - the choice of orthonormalization tier.
3. **A prototype.** Port `LDT/CommutativityPoints` (3,464 lines, pure D) over an abstract symmetric
   model, and measure the line ratio and elaboration time (`mipco-track.md` §6 item 10).
4. **The port**, then the cascade re-derived into `lidtError`.

**Decisions for the maintainer:**

1. Accept `SoundFin` (class C) in place of `SoundCo` as the target hypothesis of Phase 6. This
   changes the blueprint statement of the main theorem's hypothesis.
2. Decide where the port lives. It must be under `MIPRE/Background/LIDT/`, since only that
   directory may name `MIPStarRE` (`MIPStarRE/README.md:27`). Alternatively, ask upstream
   (`LionSR/MIPStarRE`) to generalize its base layer so the result can be vendored through
   `scripts/vendor-lidt.py`.
3. Choose the orthonormalization tier: II₁ restriction (ii) or H5 (i), and whether to fund it
   upstream in `vidick/commuting-repetition`.
4. Decide whether to have §4.2's operator-dual derivation reviewed (de la Salle is the natural
   reader). That review decides whether A1 is a formalization task.
5. Report upstream to Lin:
   - the mis-keyed citation and the unproved "directly applied";
   - the defects of `lem:simuQLID` and its nonexistent general clause;
   - Lin23 Corollary 4.4's reversed inequality and POVM/PVM gap, and the missing three-bound
     transfer.

## 6. Not checked

* **Unread sources.**
  - Marrakchi–de la Salle (arXiv:2307.08129), read by no one. It is the only cited candidate for
    an operator-level rounding with arbitrary vector states.
  - The January 2024 Lin23 version that Lin25 cites; numbering was verified for v3 only.
  - The arXiv version of TC, whose numbering, per the companion repository, differs from the
    journal source read here. Counting environments in the journal source gives Theorems 4.1 and
    4.7, consistent with both Lin's and MIP*=RE's citations, but the arXiv number of `thm:main`
    and whether that version uses diagonal lines are unverified.
  - NV18b, to which NW19 Theorem 4.40 is cited.
  - The commuting-repetition manuscript (`03_tracial_reduction.tex`) that `strict_tracial_reduction`
    cites; that result was checked only as Lean.
* **Unverified by any verifier.**
  - The five directory audits of the vendored tree. The follow-up D check was a census plus an
    inventory, not a line-by-line reading; an F argument stated without any searched keyword
    could be missed.
  - The `H ⊕ H` doubling, the summed semidefinite form on finite algebras, the operator dual for
    arbitrary algebras (§4.2), trace amplification, and the randomized-rounding alternative to
    Krein–Milman: derivations only.
* **Critic items left open.**
  - Whether functional duality can prove JNVWY's step at `ji2021-low_degree.tex:5674-5676` by some other argument.
  - A synchronous version of the `ldt.tex:521-781` reduction (G2).
  - G1 for `σ|τ⟩`. In the trace-vector case op-switching gives the three bounds (the lin25
    verifier confirmed this, caveat a double commutant); the repo-chain and tensor-codes verifiers
    say no source supplies it beyond that.
  - Lin23 Corollary 4.2's quantifier and value-comparison repairs, re-derived nowhere.
  - The diagonal weight of the answer-reduction game (needed only by Route D).
  - Whether density approximants have type I parts with diffuse center: if they never do, H5 is
    avoidable without amplification.
  - Whether `SoundIn` should be generalized over its constants, and at what cost.
* **Sizes.** Every size is an extrapolation; none was prototyped.
* **Blueprint findings.** Repaired with this report: `rem:orthonormalization-scope` (§4.3), and
  the sentence of the chapter on downstream results that said Lin proves the low-individual-degree
  step in the tracially embeddable setting (he cites it, §2.1). Not repaired:
  `03_background_results.tex:560` cites JNVWY "Theorem 1.3 (`thm:main-formal`)" and
  `02_foundations.tex:1240` cites "Definition 4.8". Under the counter of the source held in the
  companion repository, which agrees with de la Salle's citations of that paper, these are Theorem
  3.10 and Definition 4.17. The numbers 1.3 and 4.8 come from the upstream formalization's
  docstrings (`LDT/Test/Defs.lean:201`, `:253`), which may follow another arXiv version; the
  bibliography entry pins none, and the arXiv versions could not be compared offline. Pinning the
  version, or citing by label, would settle it.
* **Off the low-degree chain.** The companion repository records a defect in an NW19 definition
  that Lin's answer reduction imports. It was not examined.
