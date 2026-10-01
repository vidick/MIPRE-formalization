# C6b: the paper proofs

**Date: 2026-10-01. Tree: branch `claude/mipre-proof-repo-0z4oee`, after C6a (#258). Tracking
issue: #259.**

C6b of `planning/mipco-track.md` proves the one hypothesis left by C6a, `LIDT.Simul.SoundFin`
(`MIPRE/Background/LIDT/FinModel.lean`): the seeded low-individual-degree test is sound in every
finite pair. The route, its work packages and their sizes are in `planning/c6b-plan.md`; the audit
that sized the port of the vendored finite-dimensional proof is `reports/lidt-co-audit.md` ("the
audit"). This report records the mathematics that route needs and that no source provides:
proofs derived for C6b, each checked by three independent readers (logic, infinite-dimensional
analysis, fit with the code) and then revised. Where a statement has been compiled, the section
says so and names the Lean.

## 1. What is proved here, and where it is used

The audit found the vendored proof dimension-free except at three steps: orthonormalization, the
symmetrization of the strategy, and the semidefinite program behind self-improvement. C6b replaces
each, and adds the restriction to a class of finite pairs on which the first can be done without
type-I structure theory (the II₁ tier, chosen 2026-10-01).

| section | result | replaces | plan | status |
|---|---|---|---|---|
| §2 | a centre-valued trace for any von Neumann algebra with a faithful tracial vector functional; with it, de la Salle's orthonormalization (`< 9ε`) without abelian projections, and in a finite pair | the factor hypothesis of the vendored II₁ tier | T1 | formalized, guarded (`lem:center-valued-trace`, `thm:orthonormalization-no-abelian`, `cor:orthonormalization-finite-pair`) |
| §3 | dyadic matrix units and a faithful vector trace exclude abelian projections; the class `IsDyadicPair` is closed under the model operations; amplification by an algebra `B` with such units keeps the correlation and lands in the class | the restriction to factors | T2–T4 | prototyped in Lean, including `B` (the twisted Pauli algebra) |
| §4 | the doubled model on `H ⊕ H` supplies the swap symmetry the vendored core assumes, at the vendored constants (3ε, 2σ, 100ζ^{1/4}) | the role-register symmetrization (tensor products only) | M2 | proved; the model and its basic lemmas prototyped in Lean |
| §5 | the summed semidefinite form `Σ_g T_g A_g` with slackness, by compactness, in a finite pair | JNVWY Lemma 9.2 and finite-dimensional strong duality | M9 | proved; the core chain prototyped in Lean |

Conventions shared by the sections:
- citations `path:line` are to the tree named above; paths under the vendored trees are
  abbreviated where a section says so;
- "prototyped in Lean" means compiled sorry-free with `lake env lean` against this tree, with
  axioms `propext`, `Classical.choice` and `Quot.sound` only, but not committed;
- each section ends with its status and open points.

## 2. The centre-valued trace of an algebra with a vector trace

This section proves that every von Neumann algebra `M` with a faithful tracial functional
`τ = Σ_k ⟪g_k, · g_k⟫` of finitely many vectors has a centre-valued trace, in the sense of the
vendored `IsCenterValuedTrace M 1 E`. This is field H3 of the orthonormalization interface at the
projection `1`. It needs no factor, type or separability hypothesis (Theorem H3₁, Lemmas 1–16).

In C6b this is the one input that the vendored II₁ tier of de la Salle's Theorem 1.2 lacks for a
non-factor. With it, take any such algebra with no nonzero abelian projection, and a functional
`φ` that is positive on `M`, has `φ(1) = 1` and is of trace-class form. Then a POVM `(a_i)` with
`Re φ(Σ a_i²) > 1 − ε` is within `< 9ε` of a PVM (§2.7). In particular this holds at the model's
vector state in the first algebra of a finite pair without abelian projections (§2.8). The lemmas
and these two consequences are formalized (§2.9).

Paths:

- `O/` abbreviates `MIPRE/Background/Orthonormalization/Orthogonalization/`, the vendored de la
  Salle tree; `MvN/…` and `Blocks/…` are under `O/`.
- The new modules are
  `MIPRE/Background/Orthonormalization/{CenterTrace,CenterTraceClauses,CenterComparison,NoAbelian,FinitePairOrtho}.lean`.
  The text cites them by declaration name; §2.9 gives file:line.

### 2.1 Setting and statements

`H` is a complex Hilbert space and `M : VonNeumannAlgebra H`.

- **`M″ = M` costs nothing.** Mathlib's `VonNeumannAlgebra` carries `M″ = M` as a structure field.
  When `M = S′` for a self-adjoint set `S`, that field is `S‴ = S′`
  (`Set.centralizer_centralizer_centralizer`), which is pure algebra. The vendored
  `matrixAlgebra` is built this way (`MvN/Defs.lean:108-117`), and so is the algebra of a finite
  pair (`vnA`, §2.8).
- **No bicommutant theorem is used anywhere below.** The vendored one
  (`Blocks/Bicommutant.lean:243-252`) is finite-dimensional only.

**The trace.** Fix `g : Fin d → H` and put `τ(a) := Σ_k ⟪g_k, a g_k⟫` for every `a ∈ B(H)`.
This is a `ℂ`-linear map `B(H) → ℂ` (`vecFunctional` in `CenterTrace.lean`). The hypotheses are
those of `VecTrace` (`MIPRE/Foundations/FinitePair.lean:61-73`):

- **tracial on `M`:** `τ(xy) = τ(yx)` for `x, y ∈ M` (field `trace_mul_comm`, `:70`);
- **separating:** `x ∈ M` and `x g_k = 0` for all `k` imply `x = 0` (field `separating`, `:73`).

The normalization `Σ_k ‖g_k‖² = 1` (`:68`) is never used.

**Notation.**

- `B := B(H)`. `W := H →WOT[ℂ] H` is `B` with the weak operator topology, and `ofCLM`, `toCLM`
  are the two mutually inverse maps between them. They are multiplicative by definition:
  `isClosed_setOf_mul_eq` (`MvN/WOTCompact.lean:263`) uses
  `toCLM (ofCLM a * T * ofCLM b) = a * toCLM T * b` as a definitional equality (`:271`).
- **Centre.** `Z := {c ∈ M : cy = yc for all y ∈ M}`. At `p = 1`, `IsCentralIn M 1 c`
  (`MvN/Defs.lean:159-160`) says exactly that `c ∈ Z`, since `1·c·1 = c` and `1·y·1 = y`.
- **2-norm.** `q(y) := Σ_k ‖y g_k‖² = Re τ(y*y)`, and `‖y‖₂ := q(y)^{1/2}`.

**Theorem H3₁.** There is a `ℂ`-linear map `E : B → B` with `IsCenterValuedTrace M 1 E`
(`MvN/Defs.lean:169-201`). The table gives its ten clauses at `p = 1`, with their side
conditions.

| clause | line | statement at `p = 1` |
|---|---|---|
| `mem_center` | `:172` | `x ∈ M`, `1·x·1 = x` ⇒ `IsCentralIn M 1 (E x)` |
| `nonneg` | `:174` | `x ∈ M`, `1·x·1 = x`, `0 ≤ x` ⇒ `0 ≤ E x` |
| `trace` | `:176` | `x, y ∈ M` with `1·x·1 = x`, `1·y·1 = y` ⇒ `E(xy) = E(yx)` |
| `center_fixed` | `:178` | `IsCentralIn M 1 c` ⇒ `E c = c` |
| `center_mul` | `:180` | `IsCentralIn M 1 c`, `x ∈ M`, `1·x·1 = x` ⇒ `E(cx) = c·E x` |
| `faithful` | `:182` | `x ∈ M`, `1·x·1 = x`, `E(x*x) = 0` ⇒ `x = 0` |
| `normal` | `:184-186` | for every `κ : Type u`, filter `l`, `T : κ → B` with `T k ∈ M`, `1·T k·1 = T k`, and `L ∈ M` with `1·L·1 = L`: `TendstoWeakBdd l T L` ⇒ `TendstoWeakBdd l (E ∘ T) (E L)` |
| `equiv_of_eq` (**B1**) | `:188-189` | projections `q, q' ∈ M`, `q·1 = q`, `q'·1 = q'`, `E q = E q'` ⇒ `MvNEquiv M q q'` |
| `div` | `:192-193` | `r ∈ M` a projection, `r·1 = r`, `b ∈ M`, `0 ≤ b ≤ r` ⇒ some `z` has `IsCentralIn M 1 z`, `0 ≤ z ≤ 1`, `E b = z·E r` |
| `equiv_of_eq_matrix` (**B2**) | `:197-201` | for every `n` and projections `P, Q ∈ matrixAlgebra M n` with `P·amplify n 1 = P`, `Q·amplify n 1 = Q` and `Σ_i E(P_ii) = Σ_i E(Q_ii)`: `MvNEquiv (matrixAlgebra M n) P Q` |

Notes on the table:

- `X_ij` is the block entry `entry X i j` of an operator on `H^n`.
- `TendstoWeakBdd` (`MvN/Defs.lean:154-155`) is a uniform norm bound together with convergence
  of every coefficient `⟪ξ, T k η⟫`.
- `MvNEquiv M p q` (`:46-47`) asks for `v ∈ M` with `v*v = p` and `vv* = q`.
- The `amplify` side conditions are vacuous: `amplify n 1 = 1` (`MvN/Matrix.lean:66`).

**Additional facts proved** (Lemma 6):

- `τ ∘ E = τ` on `M`;
- `‖E x‖ ≤ ‖x‖` for `x ∈ M`;
- `E|_M` is the unique map `F : M → Z` that is `Z`-linear (`F(cx) = c F(x)`) and `τ`-preserving.
  Uniqueness does not need `F` to be the identity on `Z`.

**Lemma C (generalized comparison; used for B1 and B2).** Let `N : VonNeumannAlgebra K`, and let
`τ_N : B(K) → ℂ` be linear. Assume the hypotheses of the vendored `mvNEquiv_of_trace_eq`
(`MvN/Comparison.lean:590-598`) except the factor hypothesis, that is, for `x, y ∈ N`:

- `hτ0`: `0 ≤ τ_N(x*x)`;
- `hτtr`: `τ_N(xy) = τ_N(yx)`;
- `hτf`: `τ_N(x*x) = 0` implies `x = 0`;
- `hpolar`: polar decomposition in `N`.

Let `V` be any `ℂ`-module, and let `Φ : B(K) → V` be `ℂ`-linear with three properties:

- **(Φ1)** `Φ(xy) = Φ(yx)` for `x, y ∈ N`;
- **(Φ2)** for every projection `c ∈ N` commuting with `N`, there is a map `L_c : V → V` with
  `Φ(cx) = L_c(Φ x)` for all `x ∈ N`;
- **(Φ3)** a projection `e ∈ N` with `Φ e = 0` is `0`.

Then any two projections `p, q ∈ N` with `Φ p = Φ q` satisfy `MvNEquiv N p q`.

**Formal counterparts.**

- Theorem H3₁ is `exists_isCenterValuedTrace` (`CenterComparison.lean`). It is built from the
  expectation `IsCenterExpectation` / `exists_isCenterExpectation` (`CenterTrace.lean`).
- Lemma C is `mvNEquiv_of_map_eq` (`CenterComparison.lean`). Its formal statement drops two of
  the hypotheses above:
  - `hpolar`, because `exists_polar` (`MvN/PolarDecomp.lean:291-293`) proves polar
    decomposition in every `VonNeumannAlgebra`;
  - `hτtr`, which the proof below never uses: (Φ1) takes its place in the endgame.

### 2.2 The toolkit, and facts about τ

**Vendored weak-operator facts** (`MvN/WOTCompact.lean`):

| lemma | line | content |
|---|---|---|
| `continuous_inner_apply` | `:61` | `A ↦ ⟪ξ, A η⟫` is continuous on `W` |
| `tendsto_ofCLM_iff` | `:102` | convergence in `W` is convergence of every coefficient |
| `isCompact_setOf_norm_le` | `:114` | norm balls are compact in `W` |
| `isCompact_of_isClosed_of_norm_le` | `:193` | closed and norm-bounded is compact |
| `exists_clusterPt_of_norm_le` | `:198` | a bounded family has a cluster point along an `l` with `l.NeBot` |
| `isClosed_setOf_nonneg` | `:226` | `{A : 0 ≤ A}` is closed |
| `isClosed_setOf_le` | `:239` | `{A : A ≤ a}` is closed |
| `isClosed_setOf_commute` | `:281` | `{A : Commute A a}` is closed |
| `isClosed_setOf_mem` | `:298` | `{A : A ∈ M}` is closed; uses only the field `M″ = M` |
| `convex_setOf_nonneg` | `:388` | the positive cone is convex |

**From Mathlib:**

- multiplication by a fixed operator, on either side, is continuous on `W`
  (`continuous_mul_const`, `continuous_const_mul`, used this way at
  `MvN/WOTCompact.lean:276,294`);
- the identity `B → W` is continuous from the norm topology (`continuous_ofCLM`,
  `Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:432`);
- `W` is Hausdorff (`instT3Space`, same file, `:363`).

**Lemma 1 (facts about τ).**

- **(a)** `τ(x*x) = Σ_k ‖x g_k‖² = q(x)`, a nonnegative real, since `⟪g, x*x g⟫ = ⟪xg, xg⟫`. In
  particular `0 ≤ τ(x*x)` in the order of `ℂ`.
- **(b)** If `x ∈ M` and `q(x) = 0`, then every `x g_k = 0`, so `x = 0` by separation.
- **(c)** For fixed `c ∈ B`, the map `A ↦ τ(Ac) = Σ_k ⟪g_k, A (c g_k)⟫` is continuous on `W`,
  being a finite sum of coefficient maps.
- **(d)** For `y ∈ M`, `c ∈ Z` and a unitary `u ∈ M`: `τ(u y u* c) = τ(y c)`.
  - `τ(u·(y u* c)) = τ((y u* c)·u)` by traciality, since `u, y u* c ∈ M`;
  - this equals `τ(y u* u c)`, since `cu = uc`;
  - and `u*u = 1`.
- **(e)** For `y ∈ M` and a unitary `u ∈ M`: `q(u y u*) = q(y)`.
  - `(uyu*)*(uyu*) = u y*y u*`;
  - `τ(u·(y*y u*)) = τ(y*y u* u) = τ(y*y)` by traciality, since `u, y*y u* ∈ M`;
  - then apply (a).
- **(f)** `Z ⊆ M`, `1 ∈ Z`, and `Z` is closed under sums, scalars, products and adjoints. For
  adjoints: if `c` commutes with every `y ∈ M`, it commutes with every `y*` because `M` is
  `*`-closed. Taking the adjoint of `c y* = y* c` gives `y c* = c* y`.
- **(g)** For a unitary `u ∈ B`: `‖u y u*‖ = ‖y‖`. This is Mathlib's
  `CStarRing.norm_coe_unitary_mul` and `CStarRing.norm_mul_coe_unitary`
  (`Mathlib/Analysis/CStarAlgebra/Basic.lean:243,255`), which need no nontriviality hypothesis.

Formalized in `CenterTrace.lean` as `vecFunctional_star_mul_self` (a),
`eq_zero_of_sum_norm_sq_eq_zero` (b), `continuous_vecFunctional_mul` (c), two private lemmas for
(d) and (e), and `isCentralIn_one_iff` with the closure lemmas `isCentralIn_one_*` (f).

### 2.3 The centre-valued expectation (Lemmas 2–6)

**Lemma 2 (lower semicontinuity).** `Q(A) := q(toCLM A) = Σ_k ‖A g_k‖²` is lower semicontinuous on
`W`.

*Proof.* A finite sum of lower semicontinuous functions is lower semicontinuous. So it suffices to
treat one vector `g` and show that each sublevel set `S_t := {A : ‖A g‖² ≤ t}` is closed.

- If `t < 0`, then `S_t = ∅`.
- If `t ≥ 0`, then `S_t = ⋂_{ξ ∈ H} {A : |⟪ξ, A g⟫| ≤ √t ‖ξ‖}`.
  - The inclusion ⊆ is Cauchy–Schwarz.
  - For ⊇, take `ξ = A g`. Then `‖Ag‖² ≤ √t ‖Ag‖`, so `‖Ag‖ ≤ √t`: trivially if `Ag = 0`, and
    otherwise by dividing.
  - Each set in the intersection is the preimage of a closed set under the continuous map
    `A ↦ |⟪ξ, A g⟫|`. ∎

The formalization (`lowerSemicontinuous_sum_norm_sq`, `CenterTrace.lean`) argues differently.
At each `A`, the continuous function `A′ ↦ Σ_k (2 Re ⟪A g_k, A′ g_k⟫ − ‖A g_k‖²)` lies below `Q`,
since `‖A′g_k − Ag_k‖² ≥ 0`, and it equals `Q(A)` at `A′ = A`.

**Lemma 3 (commuting with the unitaries of `M`).** If `z ∈ B` commutes with every unitary of `M`,
then `z` commutes with every `x ∈ M`.

*Proof.*

- **(i) Self-adjoint contractions.** Let `a ∈ M` be self-adjoint with `‖a‖ ≤ 1`.
  - `b := 1 − a²` lies in `M`, and `b ≥ 0`. Mathlib proves this positivity inline, with no
    separate lemma, at `Mathlib/Analysis/CStarAlgebra/Unitary/Span.lean:42-44`.
  - So `s := √b ∈ M` (`sqrt_mem`, `Blocks/StateOnM.lean:42`).
  - `u := a + i s` is a unitary of `M`
    (`IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary`, `Span.lean:36`).
  - Its adjoint `u* = a − i s` is also a unitary of `M`, and `a = (u + u*)/2`. So `za = az`.

  The positivity of `b` is genuinely needed: the square root of an element that is not positive
  is a junk value, and `√b ∈ M` is proved only for `b ≥ 0`.
- **(ii) Self-adjoint elements.** Let `a ∈ M` be self-adjoint. If `a = 0` there is nothing to
  prove. Otherwise write `a = ‖a‖·(‖a‖⁻¹ a)` and apply (i) to the second factor.
- **(iii) Arbitrary elements.** For `x ∈ M`, put `a := (x + x*)/2` and `b := (x − x*)/(2i)`. Both
  are self-adjoint elements of `M`, and `x = a + i b`. ∎

Formalized as `commute_of_forall_unitary` (`CenterTrace.lean`).

**Lemma 4 (a central point of minimal 2-norm).** Let `x ∈ M` and `D ⊆ B` satisfy:

- `x ∈ D`;
- `{A ∈ W : toCLM A ∈ D}` is closed;
- `D` is closed under midpoints;
- `u y u* ∈ D` for every `y ∈ D ∩ M` and every unitary `u ∈ M`.

Then some `z ∈ Z ∩ D` has `‖z‖ ≤ ‖x‖` and `τ(zc) = τ(xc)` for all `c ∈ Z`.

*Proof.* Let `C` be the set of `A ∈ W` for which `y := toCLM A` satisfies `y ∈ M`, `y ∈ D`,
`‖y‖ ≤ ‖x‖`, and `τ(yc) = τ(xc)` for all `c ∈ Z`.

1. **`C` is closed.** It is the intersection of four closed sets:
   - `{toCLM A ∈ M}` (`isClosed_setOf_mem`);
   - the `D`-set, by hypothesis;
   - the norm ball, which is compact (`isCompact_setOf_norm_le`) and hence closed, since `W` is
     Hausdorff;
   - `⋂_{c ∈ Z} {A : τ((toCLM A) c) = τ(xc)}`, closed by Lemma 1(c).
2. **`C` is compact and nonempty.** It is compact by `isCompact_of_isClosed_of_norm_le`, and
   `ofCLM x ∈ C`.
3. **A minimizer.** By Lemma 2, `Q` restricted to `C` is lower semicontinuous. So it attains its
   minimum on the nonempty compact set `C` (Mathlib `LowerSemicontinuousOn.exists_isMinOn`), at
   some `A₀`. Write `y₀ := toCLM A₀` and `m := q(y₀)`.
4. **The minimizer is unique.**
   - `C` is closed under midpoints: `M` is a subspace, the ball is convex, the constraints
     `τ(yc) = τ(xc)` are affine in `y`, and `D` is closed under midpoints by hypothesis.
   - Let `y₁` correspond to a point of `C` with `q(y₁) = m`. For each `k`, the parallelogram law
     applied to `a = y₀g_k` and `b = y₁g_k` gives `‖½(a + b)‖² = ½‖a‖² + ½‖b‖² − ¼‖a − b‖²`.
   - Summing over `k`: `m ≤ q(½(y₀ + y₁)) = m − ¼ q(y₀ − y₁)`. So `q(y₀ − y₁) = 0`, and
     `y₀ = y₁` by Lemma 1(b), since `y₀ − y₁ ∈ M`.
5. **The minimizer is invariant.** Let `u ∈ M` be unitary. Then `u y₀ u*` corresponds to a point
   of `C`:
   - it lies in `M`, as a product of elements of `M`;
   - it lies in `D`, by hypothesis;
   - its norm is `‖y₀‖ ≤ ‖x‖`, by Lemma 1(g);
   - it satisfies the constraints, by Lemma 1(d).

   By Lemma 1(e), `q(u y₀ u*) = m`, so `u y₀ u* = y₀` by step 4. Multiplying on the right by `u`
   gives `u y₀ = y₀ u`.
6. **Conclusion.** By Lemma 3, `y₀` commutes with `M`, so `y₀ ∈ Z`. Take `z := y₀`. ∎

Formalized as `exists_isCentralIn_mem_of_conj_invariant` (`CenterTrace.lean`).

**Lemma 5 (uniqueness).** If `z, z′ ∈ Z` and `τ(zc) = τ(z′c)` for all `c ∈ Z`, then `z = z′`.

*Proof.*

- Put `w := z − z′ ∈ Z`. By Lemma 1(f), `c := w*` lies in `Z`, so `τ(w w*) = 0`.
- By Lemma 1(a) applied to `w*`: `τ(w w*) = τ((w*)* w*) = q(w*)`.
- So `q(w*) = 0`, and `w* = 0` by Lemma 1(b), since `w* ∈ M`. Therefore `w = 0`. ∎

Formalized as `eq_of_isCentralIn_of_pairing` (`CenterTrace.lean`).

**Lemma 6 (definition of `E`; characterization; consequences).**

*Definition on `M`.* For `x ∈ M`, let `E₀ x ∈ Z` be the `z` of Lemma 4 with `D = B`, for which
all four hypotheses on `D` are trivial. By Lemma 5, `E₀ x` is the unique `z ∈ Z` with
`τ(zc) = τ(xc)` for all `c ∈ Z`.

*Linearity.* `E₀` is `ℂ`-linear on the subspace `M`. Indeed `E₀(αx + βy)` and `αE₀x + βE₀y` both
lie in `Z` (Lemma 1(f)) and have the same pairings `c ↦ τ(·c)`, so they are equal by Lemma 5.

*Extension to `B(H)`.* Let `E : B → B` be any linear extension of `E₀ : M → B` (Mathlib
`LinearMap.exists_extend`, over the field `ℂ`). Its values off `M` are arbitrary. This is
harmless, for two reasons:

- every clause of `IsCenterValuedTrace` (`MvN/Defs.lean:172-201`) has one of three hypotheses:
  `x ∈ M`; `IsCentralIn`, which contains `c ∈ M`; or membership in `matrixAlgebra M n`, whose
  entries lie in `M`;
- the consumers of §2.7 use `E` only through these clauses (`NoAbelian.lean`; in the vendored
  original, `MvN/II1Factor.lean:244-261`).

*(Char).* For `x ∈ M`:

- `E x ∈ Z`;
- `τ((Ex)c) = τ(xc)` for all `c ∈ Z`;
- any `z ∈ Z` with the same pairings equals `E x`.

*Consequences.*

- **(6a)** `τ(Ex) = τ(x)`: take `c = 1 ∈ Z`.
- **(6b)** `‖Ex‖ ≤ ‖x‖`: the `z` produced by Lemma 4 has `‖z‖ ≤ ‖x‖`, and `z = Ex` by (Char).
- **(6c) Positivity.** If `0 ≤ x`, apply Lemma 4 with `D := {y : 0 ≤ y}`:
  - `D` is closed (`isClosed_setOf_nonneg`);
  - `D` is closed under midpoints (`½a + ½b ≥ 0`);
  - `D` is invariant, since `0 ≤ u y u*` (Mathlib `star_right_conjugate_nonneg`,
    `Mathlib/Algebra/Order/Star/Basic.lean:245`, with `c = u`).

  This gives `z ∈ Z` with `0 ≤ z`, and `z = Ex` by (Char).
- **(6d) Monotonicity on `M`.** `Ey − Ex = E(y − x)`, so for `x ≤ y` in `M`, (6c) gives
  `Ex ≤ Ey`.
- **(6e) Uniqueness of the conditional expectation** (not used downstream). Let `F : M → Z`
  satisfy `F(cx) = cF(x)` for `c ∈ Z`, `x ∈ M`, and `τ ∘ F = τ`. For `c ∈ Z`,
  `τ(F(x)c) = τ(cF(x)) = τ(F(cx)) = τ(cx) = τ(xc)`. The first equality holds because `F(x) ∈ Z`
  commutes with `c`, and the last because `c ∈ Z`. So `F x = E x` by (Char). The argument never
  uses that `F` is the identity on `Z`.

Formalized as `exists_isCenterExpectation` (`CenterTrace.lean`):

- the fields of the structure `IsCenterExpectation` are the first two parts of (Char)
  (`mem_center`, `pairing`), (6b) (`norm_le`) and (6c) (`nonneg`); the third part of (Char) is
  Lemma 5;
- (6a) is `IsCenterExpectation.vecFunctional_eq` (`CenterTraceClauses.lean`);
- (6e) is not formalized.

### 2.4 The remaining non-comparison clauses (Lemmas 7–9)

**Lemma 7 (the algebraic clauses).** In each case (Char) closes the argument. The side conditions
`1·x·1 = x` follow from `1·x = x·1 = x`; where they appear as hypotheses they are ignored. The
side-condition-free forms are proved first, and the structure's fields are filled from them.

- **`mem_center`.** `E x ∈ Z`, which is `IsCentralIn M 1 (E x)`.
- **`nonneg`.** This is (6c).
- **`trace`.** For `c ∈ Z`: `τ(xy·c) = τ(x·(yc)) = τ((yc)·x) = τ(y·(cx)) = τ(y·(xc)) = τ(yx·c)`.
  This uses `yc ∈ M`, traciality and `cx = xc`. So `E(xy)` and `E(yx)` lie in `Z` with the same
  pairings, and they are equal by Lemma 5.
- **`center_fixed`.** `IsCentralIn M 1 c₀` gives `c₀ ∈ Z`, and `c₀` trivially has the same
  pairings as itself, so `E c₀ = c₀` by (Char).
- **`center_mul`.** `c₀·E x ∈ Z` by Lemma 1(f). For `c ∈ Z`:
  `τ(c₀ (Ex) c) = τ((Ex) c₀ c) = τ(x c₀ c) = τ((c₀ x) c)`. The steps use `c₀(Ex) = (Ex)c₀`,
  then `c₀c ∈ Z` with (Char), then `x c₀ = c₀ x`.
- **`faithful`.** If `E(x*x) = 0`, then by (6a) and Lemma 1(a), `q(x) = τ(x*x) = τ(E(x*x)) = 0`.
  So `x = 0` by Lemma 1(b).

Formalized as `IsCenterExpectation.trace`, `.center_fixed`, `.center_mul` and `.faithful`
(`CenterTraceClauses.lean`). `mem_center` and `nonneg` are fields of `IsCenterExpectation`.

**Lemma 8 (`normal`).** Let `T k ∈ M`, `L ∈ M` and `TendstoWeakBdd l T L`, with bound `C₀`.

*Proof.*

1. **Bound.** `‖E(T k)‖ ≤ ‖T k‖ ≤ C₀` by (6b). This is the first conjunct of the conclusion.
2. **Reduction to cluster points.** Put `f k := ofCLM(E(T k))`. It lies in the compact set
   `s := {A : ‖toCLM A‖ ≤ C₀}`. By Mathlib `IsCompact.tendsto_nhds_of_unique_mapClusterPt`, it
   suffices to show that every cluster point `A ∈ s` of `f` along `l` equals `ofCLM(E L)`. No
   `NeBot` hypothesis is needed: if `l = ⊥` there is no cluster point.
3. **`A ∈ Z`.** The set `Z_W := {A : toCLM A ∈ M} ∩ ⋂_{y ∈ M} {A : Commute (toCLM A) y}` is closed
   (`isClosed_setOf_mem`, `isClosed_setOf_commute`), and it contains every `f k`. A cluster point
   of a map with values in a closed set lies in that set.
4. **`A` has the pairings of `L`.** Fix `c ∈ Z` and put `φ(A) := τ((toCLM A) c)`, which is
   continuous by Lemma 1(c).
   - `φ(f k) = τ(E(T k) c) = τ(T k c)`, by (Char).
   - `τ(T k c) = Σ_j ⟪g_j, T k (c g_j)⟫ → Σ_j ⟪g_j, L (c g_j)⟫ = τ(Lc)`. This is a finite sum of
     coefficients, each converging by the second conjunct of `TendstoWeakBdd`.
   - `φ(A)` is a cluster point of `φ ∘ f` along `l` (Mathlib `MapClusterPt.continuousAt_comp`),
     and `φ ∘ f → τ(Lc)` in the Hausdorff space `ℂ`. Hence `φ(A) = τ(Lc)`.
5. **Conclusion.** By (Char), `toCLM A = E L`. So `f → ofCLM(E L)` in `W`. By
   `tendsto_ofCLM_iff`, this means `⟪ξ, E(T k) η⟫ → ⟪ξ, E(L) η⟫` for all `ξ, η`. ∎

Formalized as `IsCenterExpectation.normal`, with the closedness of `Z_W` as
`isClosed_setOf_isCentralIn_one` (`CenterTraceClauses.lean`).

**Lemma 9 (division in the centre; the `div` clause).**

- **(9a)** If `a, c ∈ Z` and `0 ≤ a ≤ c`, then `a = zc` for some `z ∈ Z` with `0 ≤ z ≤ 1`.
- **(9b) `div`.** Let `r ∈ M` be a projection and `b ∈ M` with `0 ≤ b ≤ r`. Put `a := E b` and
  `c := E r`.
  - Both lie in `Z`.
  - `0 ≤ a` by (6c), and `a ≤ c` by (6c) and (6d), since `r − b ≥ 0`.
  - The `z` of (9a) satisfies `IsCentralIn M 1 z`, `0 ≤ z ≤ 1` and `E b = z·E r`.

*Proof of (9a).* For `ε > 0`, let `w := (c + ε)⁻¹`, the continuous functional calculus of
`t ↦ (t + ε)⁻¹` at `c`, and put `z_ε := a w`. Note that `c ≥ 0`, since `0 ≤ a ≤ c`.

1. **`w ∈ M`**, by `CommutingRepetition.VN.cfc_real_mem`
   (`MIPRE/Background/Repetition/CommutingRepetition/VN/Generated.lean:116`).
2. **`w ∈ Z`.** `w` commutes with every `y ∈ M` because `c` does (Mathlib `Commute.cfc_real`).
   Then `z_ε ∈ Z` by Lemma 1(f).
3. **`w ≥ 0`**: the spectrum of `c` lies in `[0, ∞)`, where `(t + ε)⁻¹ > 0`.
4. **`cw + εw = 1`**, from `(t + ε)(t + ε)⁻¹ = 1` on the spectrum of `c`.
5. **`0 ≤ z_ε`**: `a` and `w` are commuting nonnegative elements (Mathlib `Commute.mul_nonneg`).
6. **`z_ε ≤ 1`**: by step 4, `1 − z_ε = (c − a)w + εw`. Both summands are nonnegative, the first
   again by `Commute.mul_nonneg`.
7. **`‖z_ε‖ ≤ 1`**, from `0 ≤ z_ε ≤ 1` (Mathlib `CStarAlgebra.norm_le_norm_of_le_of_nonneg`).
8. **`‖z_ε c − a‖ ≤ ε`.** By step 4, `z_ε c − a = a(wc − 1) = −ε a w = −ε z_ε`. So
   `‖z_ε c − a‖ = ε‖z_ε‖ ≤ ε` by step 7.
9. **The limit.** Take `ε_j := 1/(j + 1)` and `z_j := z_{ε_j}`. Since `‖z_j‖ ≤ 1`,
   `exists_clusterPt_of_norm_le` gives a cluster point `ofCLM z` of `j ↦ ofCLM z_j` in `W`, with
   `‖z‖ ≤ 1`; the filter is `atTop` on `ℕ`, which is `NeBot`.
   - `z ∈ Z` and `0 ≤ z ≤ 1`: the sets `Z_W` (Lemma 8, step 3), `isClosed_setOf_nonneg` and
     `isClosed_setOf_le 1` are closed and contain every `ofCLM z_j`.
   - `zc = a`. Right multiplication by `ofCLM c` is continuous on `W`, so `ofCLM(zc)` is a
     cluster point of `ofCLM(z_j c)`. By step 8, `z_j c → a` in norm, hence in `W`
     (`continuous_ofCLM`). Since `W` is Hausdorff, `zc = a`. ∎

Formalized in `CenterTraceClauses.lean`:

- steps 1–8 as `exists_isCentralIn_norm_mul_sub_le`;
- step 9 as `exists_isCentralIn_eq_mul_of_le`;
- (9b) as `IsCenterExpectation.div`.

*Remark (a second route to step 8, not needed).* Even without the bound `‖z_ε‖ ≤ 1`,
`a(1 − cw) → 0` in norm.

- Put `d := 1 − cw = εw`. It is central, with `0 ≤ d ≤ 1`, so `‖εw‖ ≤ 1`.
- `‖cw‖ ≤ 1`, by `mul_cfc_inv_add` and `norm_cfc_mul_inv_add_le`
  (`MvN/PolarDecomp.lean:140,153`).
- `a(c − a) ≥ 0` and `a ≤ ‖a‖·1`, with all factors commuting. Hence
  `(ad)*(ad) = d a² d ≤ d c a d ≤ ‖a‖·d c d = ‖a‖ ε (cw)(εw)`.
- So `‖ad‖² ≤ ‖a‖ ε → 0`.

The shorter route of step 8 is the one formalized.

### 2.5 Comparison (Lemmas 10–15)

**Lemma 10 (central support).** Let `N` be a von Neumann algebra on `K` and `f ∈ N` a projection.
Then there is a projection `c ∈ N` such that:

- `c` commutes with `N`;
- `cf = f`;
- for every `e ∈ B(K)`, if `e y f = 0` for all `y ∈ N`, then `ec = 0`.

*Proof.* This is the vendored corner lemma `exists_mul_mul_ne_zero_of_factor`
(`MvN/Comparison.lean:233-296`) with its factor step removed (`:269-285`, which identifies the
central support with `1`).

1. Let `𝒦` be the closed span of `{y(fξ) : y ∈ N, ξ ∈ K}`, and `c` its orthogonal projection.
2. `𝒦` is invariant under `N` and under `N′`; these are the factor-free steps `hinvM` and `hinvC`
   (`:254-261`).
   - So `c` commutes with `N` and with `N′` (`starProjection_commute_of_invariant'`,
     `Blocks/Bicommutant.lean:48`).
   - Since `c` commutes with `N′`, `c ∈ N` (`mem_of_commute_commutant`,
     `MIPRE/Background/Repetition/CommutingRepetition/VN/Generated.lean:73`).
3. `fξ ∈ 𝒦` (take `y = 1`), so `cf = f`.
4. If `e y f = 0` for all `y ∈ N`, then `e` vanishes on the generators of `𝒦`. Its kernel is a
   closed subspace, so `e` vanishes on all of `𝒦` (`:287-292`). Since `cξ ∈ 𝒦` for every `ξ`,
   `ec = 0`. ∎

Formalized as `exists_centralSupport` (`CenterComparison.lean`). The formal statement asks only
`f ∈ N`, not that `f` be a projection; the proof does not use it.

**Lemma 11 (extension from a nonzero corner).** Let `p′, q′ ∈ N` be projections and `y ∈ N` with
`x := q′ y p′ ≠ 0`. Then some `u` satisfies `IsPartialBetween N p′ q′ u`
(`MvN/Comparison.lean:85`) and `0 < Re τ_N(u*u)`.

*Proof.* This is the vendored `exists_extension_of_ne` (`MvN/Comparison.lean:303-345`), except
that the nonzero corner is a hypothesis here. There it comes from the factor corner lemma
`exists_mul_mul_ne_zero_of_factor` (`:323`).

- **Polar decomposition.** `hpolar x` gives `u ∈ N` with `u*u` the right support of `x`, `uu*`
  its left support, and `x = u (x*x)^{1/2}`.
- **Supports.**
  - `x p′ = x`, so the right support lies below `p′` (`rightSupport_mul_eq_self_of`,
    `MvN/BlockCalc.lean:465`);
  - `q′ x = x`, so the left support lies below `q′` (`leftSupport_mul_eq_self_of`, `:475`).
- **Positivity.** `u ≠ 0`, since `x = u (x*x)^{1/2} ≠ 0`. So `Re τ_N(u*u) > 0` by `hτ0` and
  `hτf`. ∎

Formalized as `exists_extension_of_mul_ne_zero` (`CenterComparison.lean`). Like the vendored
original, it is stated for the case Lemma 12 uses: `p′ = p − w*w` and `q′ = q − ww*` for a partial
isometry `w` with `IsPartialBetween N p q w`.

**Lemma 12 (proof of Lemma C).** The hypotheses are those of Lemma C.

*Proof.*

1. **Greedy chain.** This is the chain of `mvNEquiv_of_trace_eq` (`MvN/Comparison.lean:599-621`),
   copied verbatim. It uses `exists_good_extension` (`:349`), `IsPartialBetween.add` (`:177`),
   `IsChain.exists_limit` (`:504`) and `eq_star_of_tendsto` (`:574`), all of them factor-free.
   - The greedy step extends a partial isometry `w` by some `U(w)` between the complements. The
     trace `Re τ_N(U(w)*U(w))` is at least half that of any other such extension.
   - Put `w₀ := 0` and `w_{n+1} := w_n + U(w_n)`.
   - The strong limit is some `W ∈ N` with `IsPartialBetween N p q W`, and `w_n*w_n ≤ W*W`,
     `w_n w_n* ≤ WW*` for all `n`.
2. **Maximality.** Put `p′ := p − W*W` and `q′ := q − WW*`, which are projections of `N`. Claim:
   `q′ y p′ = 0` for all `y ∈ N`.
   - Otherwise Lemma 11 gives some `u′` with `δ := Re τ_N(u′*u′) > 0`.
   - `u′` is also an extension between the complements of every `w_n` (`IsPartialBetween.mono`
     and `sub_mul_sub_of_le`, `:124` and `:72`).
   - So `δ ≤ 2 Re τ_N(U(w_n)*U(w_n))` for every `n`. Hence `nδ/2 ≤ Re τ_N(w_n*w_n) ≤ Re τ_N(p)`
     (`re_map_le_of_mem`, `Blocks/StateOnM.lean:67`; `init_le_loewner`,
     `MvN/Comparison.lean:145`).
   - This contradicts the Archimedean property.

   The argument is that of `:626-651`, with `exists_extension_of_ne` replaced by Lemma 11.
3. **Central support.** Lemma 10 with `f = p′` gives a central projection `c ∈ N` with
   `cp′ = p′`. By step 2, `q′ y p′ = 0` for all `y ∈ N`, so `q′c = 0`, and hence
   `cq′ = q′c = 0`.
4. **`Φ(p′) = Φ(q′)`.** We have `Φ(p′) = Φ(p) − Φ(W*W)` and `Φ(q′) = Φ(q) − Φ(WW*)`. Now
   `Φ(W*W) = Φ(WW*)` by (Φ1), with `W, W* ∈ N`, and `Φ p = Φ q`.
5. **Both complements vanish.**
   `Φ(p′) = Φ(cp′) = L_c(Φ p′) = L_c(Φ q′) = Φ(cq′) = Φ(0) = 0`, so `p′ = 0` by (Φ3). Then
   `Φ(q′) = Φ(p′) = 0`, so `q′ = 0` by (Φ3).
6. **Conclusion.** `W*W = p` and `WW* = q`, so `MvNEquiv N p q`. ∎

Steps 3–5 replace the vendored endgame (`:622` and `:652-668`), which used the traciality of
`τ_N` and the factor dichotomy. Formalized in `CenterComparison.lean` as
`exists_maximal_isPartialBetween` (steps 1–2) and `mvNEquiv_of_map_eq`.

**Lemma 13 (`equiv_of_eq`).** Apply Lemma C with `N = M`, `τ_N = τ` and `Φ = E`.

- **Hypotheses on `τ`:** `hτ0` is Lemma 1(a); `hτtr` is traciality; `hτf` is Lemma 1(a, b);
  `hpolar` is `exists_polar M`.
- **(Φ1)** The side-condition-free `trace` of Lemma 7.
- **(Φ2)** A central projection `c` lies in `Z`. Take `L_c := (c ·)`, by the side-condition-free
  `center_mul` of Lemma 7.
- **(Φ3)** If `E e = 0` for a projection `e`, then `q(e) = τ(e*e) = τ(e) = τ(Ee) = 0`, by
  Lemma 1(a) and (6a). So `e = 0` by Lemma 1(b).

**Lemma 14 (the centre of `M_n(M)`).** If `X ∈ matrixAlgebra M n` commutes with all of
`matrixAlgebra M n`, then `X = amplify n c₀` for some `c₀ ∈ Z`.

*Proof.* For `n = 0`, take `c₀ = 0`: any two operators on the zero space are equal (`ext_entry`,
`MvN/BlockCalc.lean:60`, vacuously). For `n ≥ 1`, follow the vendored `matrixAlgebra_factor`
(`MvN/MatrixFactor.lean:101-122`) through `:115`, and stop before its factor hypothesis is used
(`:116`):

- `X` commutes with the matrix units `e_ij ∈ M_n(M)` (`matrixUnit_mem`, `:89`). So
  `X_ki = δ_ki X_00`, that is, `X = amplify n X_00`.
- `X_00 ∈ M` (`entry_mem`, `MvN/Matrix.lean:253`).
- `X` commutes with `amplify n y` for each `y ∈ M` (`amplify_mem`, `MvN/Matrix.lean:144`). So
  `X_00` commutes with `y` (`entry_mul_amplify`, `MvN/BlockCalc.lean:72`). ∎

Formalized as `exists_eq_amplify_of_commute` (`CenterComparison.lean`).

**Lemma 15 (`equiv_of_eq_matrix`).** Apply Lemma C with:

- `N = matrixAlgebra M n`;
- `τ_N = diagTrace τ n`, the map `X ↦ Σ_i τ(X_ii)` (`MvN/MatrixFactor.lean:139`);
- `Φ(X) := Σ_i E(X_ii)`, a linear map (`entryₗ`, `:127`).

The checks:

- **Hypotheses on `τ_N`.** Positivity, traciality and faithfulness are `diagTrace_nonneg`,
  `diagTrace_trace` and `diagTrace_faithful` (`:151`, `:160`, `:171`). These need only `hτ0`,
  `hτtr` and `hτf` on `M`. Polar decomposition is `exists_polar (matrixAlgebra M n)`.
- **(Φ1)** This is `sum_entry_mul_eq` (`MvN/Matrix.lean:319-323`). Its hypothesis is the
  side-condition-free trace property `E(xy) = E(yx)` for `x, y ∈ M` (`:320`), which Lemma 7
  supplies. The entries lie in `M` by `entry_mem`.
- **(Φ2)** By Lemma 14, a central projection `C` is `amplify n c₀` with `c₀ ∈ Z`. Then
  `(CX)_ii = c₀ X_ii` (`entry_amplify_mul`, `MvN/BlockCalc.lean:66`), so
  `Φ(CX) = Σ_i E(c₀ X_ii) = c₀ Φ(X)` by `center_mul`. Take `L_C := (c₀ ·)`.
- **(Φ3)** Let `e` be a projection with `Φ e = 0`. Then
  `diagTrace τ n (e*e) = diagTrace τ n e = Σ_i τ(e_ii) = Σ_i τ(E e_ii) = τ(Φ e) = 0`
  (`diagTrace_apply`, `:144`, and (6a)). So `e = 0` by `diagTrace_faithful`. This avoids having to
  show that a sum of nonnegative operators in `B(H)` that equals zero has zero summands. ∎

Lemmas 13 and 15 are `IsCenterExpectation.equiv_of_eq` and
`IsCenterExpectation.equiv_of_eq_matrix` (`CenterComparison.lean`).

**Lemma 16 (assembly).** The ten fields of `IsCenterValuedTrace M 1 E` come from Lemmas 7, 8, 9b,
13 and 15. Each side condition (`1·x·1 = x`, `q·1 = q`, `P·amplify n 1 = P`) is either a
hypothesis that is ignored, or follows from `1·x = x·1 = x` and `amplify n 1 = 1`
(`MvN/Matrix.lean:66`). ∎

Formalized as `IsCenterExpectation.isCenterValuedTrace` and `exists_isCenterValuedTrace`
(`CenterComparison.lean`).

### 2.6 Remarks on the proof

- **Scope.** H3 at `p = 1` holds for every `VonNeumannAlgebra` that carries a faithful tracial
  vector functional of finitely many vectors. No II₁, factor or separability hypothesis enters.
- **No textbook result is assumed.** Two devices replace Dixmier averaging and generalized
  comparability:
  - the point of minimal 2-norm in a weak-operator compact, unitarily invariant constraint set
    (Lemma 4);
  - a central-support argument inside the vendored greedy proof (Lemmas 10–12).

  For orientation only, and not relied on, the classical counterparts are:
  - the centre-valued trace of a finite von Neumann algebra (Kadison–Ringrose Theorem 8.2.8;
    Takesaki V.2.6);
  - comparability (Kadison–Ringrose Theorem 6.2.7).

  These theorem numbers were given from memory and have not been checked.
- **General `p`.** The interface field H3 (`MvN/Interface.lean:76-78`) asks for every finite
  projection `p`; only `p = 1` is proved. A corner `pMp` carries the vector functional
  `Σ_k ⟪p g_k, · p g_k⟫`, which is tracial and separating on `pMp`, so the argument would
  transfer. But the corner is not a `VonNeumannAlgebra H` as stated. The II₁ tier needs only
  `p = 1` (§2.7).

### 2.7 How H3₁ feeds the vendored finite case

The vendored chain for the finite case ends at `exists_pvm_bound_of_selection`. `OrthAtN` and
`orthAtN_fin_of_isFiniteProj` are not on this chain, because both need field H0 (see "Why not
`OrthAtN`" below).

**`exists_selection_typeII₁`** (`MvN/Finite.lean:77-106`). This is de la Salle's Lemma 3.1 on the
type II₁ part. Hypotheses:

- `M`, a projection `p ∈ M`, and a projection `c` with `IsCentralIn M p c`;
- `hII : ∀ r, IsAbelianProj M r → r * c = r → r = 0`. Here `IsAbelianProj` (`MvN/Defs.lean:58-60`)
  means a projection `r ∈ M` with `rMr` commutative;
- `E` with `hE : IsCenterValuedTrace M p E`;
- `a : Fin n → B` with `a i ∈ M`, `0 ≤ a i` and `Σ_i a i = c`;
- a linear `φ : B → ℂ` of trace-class form on `M`: `φ x = Σ'_k ⟪g_k, x g_k⟫` for `x ∈ M`, for
  some `g : ℕ → H` with `Σ_k ‖g_k‖²` summable.

Conclusion: projections `q i ∈ M` with:

- each `q i` commuting with `a i`;
- `q i·c = q i`;
- `Σ_i E(q i) = c`;
- `Re φ(Σ_i a_i²) ≤ Re φ(Σ_i q_i a_i)`.

The proof rests on two further vendored theorems:

- `exists_extreme_maximizer` (`MvN/Selection.lean:472`). Through its lemmas
  `ofCLM_mem_selectionSet` and `isClosed_selectionSet`, it reads `hE.center_fixed` (`:229`) and
  `hE.normal` (`:294`);
- `exists_perturbation` (`MvN/Perturb.lean:584`), which uses `hII` once (`:608`) and reads
  `hE.div` (`:615`) and `hE.center_mul` (`:640`).

**`selection_of_split`** (`MvN/Finite.lean:113`) is used with the type I part `c = 0`.

- The type I branch is trivial, since a POVM summing to `0` is `0`.
- The type II₁ branch is `exists_selection_typeII₁` with `c := 1 − 0`.

**`exists_pvm_bound_of_selection`** (`MvN/Finite.lean:254-293`). This is de la Salle's Lemma 3.2 in
`M_n(M)`, together with the three-term estimate. Hypotheses:

- the projection `p` with `E p = p` (from `hE.center_fixed`);
- the trace property of `E` (from `hE.trace`);
- comparison in `matrixAlgebra M n` (from `hE.equiv_of_eq_matrix n`);
- polar decomposition in `matrixAlgebra M n` (`exists_polar`);
- `φ` positive on `M` (`0 ≤ φ(x*x)` for `x ∈ M`), with `φ p = 1`;
- the POVM `a` with `Σ_i a i = p`, and `ε` with **`1 − ε < Re φ(Σ_i a_i a_i)`**;
- `q` from the selection step.

Conclusion: projections `p′ i ∈ M` with `Σ_i p′ i = p` and
**`Re φ(Σ_i (a_i − p′_i)*(a_i − p′_i)) < 9ε`**. Both inequalities are strict.

**Which clauses are read.** Along this path, six clauses of `hE` are read:

- `center_fixed` and `normal` inside `exists_extreme_maximizer`, and `div` and `center_mul` inside
  `exists_perturbation` (above);
- `center_fixed`, `trace` and `equiv_of_eq_matrix`, which the caller extracts from `hE` to feed
  `exists_pvm_bound_of_selection` (`MvN/II1Factor.lean:260`, and the same call in
  `NoAbelian.lean`; the general-interface caller does the same at `MvN/Finite.lean:331`).

No code in the vendored tree reads `mem_center`, `nonneg`, `faithful` or `equiv_of_eq`. They must
still be supplied, because `hE` is passed whole to `exists_extreme_maximizer` and
`exists_perturbation`.

**Where the factor hypothesis went.** The vendored `povm_orthogonalization_II₁Factor`
(`MvN/II1Factor.lean:219`) uses its factor hypothesis only to build the scalar centre-valued trace
`x ↦ τ(x)·1` (`isCenterValuedTrace_scalarTrace`, `:112`). Its proof reads the state `φ` only
through:

- its linear map, its positivity and `φ 1 = 1` (`:244`, `:256`, `:261`);
- its trace-class form `hφg`.

Normality is never used. Replacing the scalar trace by the `E` of Theorem H3₁ therefore gives two
theorems, both in `NoAbelian.lean`.

- **`povm_orthogonalization_of_isCenterValuedTrace`.** Assume `M` has no nonzero abelian
  projection and `IsCenterValuedTrace M 1 E` holds. Take:
  - a linear `φ`, positive on `M`, with `φ 1 = 1` and of trace-class form;
  - a finite POVM `(a_i)_{i ∈ ι}` in `M`;
  - a real `ε` with `1 − ε < Re φ(Σ_i a_i a_i)`.

  Then there is a PVM `(p_i)` in `M` with `Re φ(Σ_i (a_i − p_i)*(a_i − p_i)) < 9ε`. The output
  set `ι` is reached from `Fin n` along `Fintype.equivFin`.
- **`povm_orthogonalization_vecTrace`.** Assume moreover that `M` carries a faithful tracial
  vector functional of finitely many vectors. Then for every unit vector `ψ`,
  `Σ_i ‖a_i ψ‖² > 1 − ε` implies `Σ_i ‖(a_i − p_i) ψ‖² < 9ε` for some PVM `(p_i)` in `M`. The
  vector state `x ↦ ⟪ψ, xψ⟫` has trace-class form, with `g_0 = ψ` and `g_k = 0` for `k ≥ 1`.

**Why not `OrthAtN`.** `OrthAtN M z ι` (`MvN/Local.lean:44`) is `OrthAtP`
(`Blocks/Glue.lean:54-61`) for the functionals normal on `M` (`IsNormalOn`,
`MvN/Defs.lean:145-148`), so it quantifies over every such `φ`. `orthAtN_fin_of_hasSelection`
(`MvN/Finite.lean:297`) needs the selection step for every normal `φ`, and that needs field H0
(normal functionals are of trace-class form). The II₁ tier gives instead the pointwise form above:
one `φ` of trace-class form, with no normality assumption.

### 2.8 The finite-pair form

C6b consumes the theorem in the model vocabulary of `MIPRE/Foundations/FinitePair.lean`, so that
code outside `MIPRE/Background/Orthonormalization/` can use it. `FinitePairOrtho.lean` transports
`povm_orthogonalization_vecTrace` in five steps.

1. **The algebra.** `vnA M` is the `VonNeumannAlgebra` on `M.H` whose carrier is the commutant of
   the second player's operators `M.opsB`. Its field `M″ = M` is `S‴ = S′`, as for
   `matrixAlgebra`. `mem_vnA_iff` says that in a finite pair, `T ∈ vnA M ↔ T ∈ M.opsA`:
   - one direction is `commutantA` (`FinitePair.lean:98`);
   - the other is the commutation of the two players' operators.
2. **The trace.** The `VecTrace` of `traceA` (`FinitePair.lean:102`) gives the vector functional.
   Its fields `trace_mul_comm` and `separating` are the two hypotheses of §2.1.
3. **The POVM.** For `P : POVMIn Λ 𝒜`, `a_i := π(πA(P_i))` is a POVM in `vnA M`. Positivity needs
   `StarOrderedRing 𝒜`.
4. **The PVM back.** Each output `p_i` lies in `M.opsA`, so `p_i = π(πA(Q_i))`. Injectivity
   (`injA`, `FinitePair.lean:94`) makes `Q` a PVM in `𝒜`.
5. **No abelian projection**, stated on the operators: if `r ∈ M.opsA` is a projection with
   `(rxr)(ryr) = (ryr)(rxr)` for all `x, y ∈ M.opsA`, then `r = 0`.

The result is `povm_orthogonalization_finitePair`. Assume `M.IsFinitePair`, `‖M.ψ‖ = 1` and the
condition of item 5, and take `P : POVMIn Λ 𝒜` and a real `ε`. Then

`1 − ε < Σ_a ‖π(πA(P_a)) ψ‖²`  implies  `Σ_a ‖π(πA(P_a − Q_a)) ψ‖² < 9ε`

for some `Q : Λ → 𝒜` with `IsPVMIn Q`. The second player's version is the same theorem for the
model with the players exchanged.

**The strict inequalities.** Suppose a caller knows only `1 − ε ≤ Σ_a ‖π(πA(P_a)) ψ‖²`. For each
`ε′ > ε`, it gets a PVM `Q` (depending on `ε′`) with error `< 9ε′`; it never gets `≤ 9ε` exactly.
The scalar cascade of the port must budget for this.

### 2.9 Status and open points

**Formalized.** Lemmas 1–16 (except the unused (6e)), §2.7 and §2.8 are proved in Lean in the five
modules named at the head of this section, about 1.25k lines in all, sorry-free and guarded in
`MIPRE/Axioms.lean`. The main declarations:

| result | declaration | location |
|---|---|---|
| the trace `τ` | `vecFunctional` | `CenterTrace.lean:57` |
| Lemma 1 | `vecFunctional_star_mul_self`, `eq_zero_of_sum_norm_sq_eq_zero`, `continuous_vecFunctional_mul`, `isCentralIn_one_iff` | `CenterTrace.lean:130,145,305,86` |
| Lemma 2 | `lowerSemicontinuous_sum_norm_sq` | `CenterTrace.lean:217` |
| Lemma 3 | `commute_of_forall_unitary` | `CenterTrace.lean:268` |
| Lemma 4 | `exists_isCentralIn_mem_of_conj_invariant` | `CenterTrace.lean:317` |
| Lemma 5 | `eq_of_isCentralIn_of_pairing` | `CenterTrace.lean:161` |
| Lemma 6 | `IsCenterExpectation`, `exists_isCenterExpectation`; (6a) `IsCenterExpectation.vecFunctional_eq` | `CenterTrace.lean:69,384`; `CenterTraceClauses.lean:123` |
| Lemma 7 | `IsCenterExpectation.trace`, `.center_fixed`, `.center_mul`, `.faithful` | `CenterTraceClauses.lean:128,141,147,160` |
| Lemma 8 | `IsCenterExpectation.normal`, `isClosed_setOf_isCentralIn_one` | `CenterTraceClauses.lean:168,45` |
| Lemma 9 | `exists_isCentralIn_norm_mul_sub_le`, `exists_isCentralIn_eq_mul_of_le`, `IsCenterExpectation.div` | `CenterTraceClauses.lean:56,95,196` |
| Lemma 10 | `exists_centralSupport` | `CenterComparison.lean:59` |
| Lemma 11 | `exists_extension_of_mul_ne_zero` | `CenterComparison.lean:115` |
| Lemma 12 (Lemma C) | `exists_maximal_isPartialBetween`, `mvNEquiv_of_map_eq` | `CenterComparison.lean:155,217` |
| Lemmas 13, 15 | `IsCenterExpectation.equiv_of_eq`, `.equiv_of_eq_matrix` | `CenterComparison.lean:284,300` |
| Lemma 14 | `exists_eq_amplify_of_commute` | `CenterComparison.lean:254` |
| Lemma 16, Theorem H3₁ | `IsCenterExpectation.isCenterValuedTrace`, `exists_isCenterValuedTrace` | `CenterComparison.lean:337,355` |
| §2.7 | `povm_orthogonalization_of_isCenterValuedTrace`, `povm_orthogonalization_vecTrace` | `NoAbelian.lean:44,99` |
| §2.8 | `vnA`, `mem_vnA_iff`, `povm_orthogonalization_finitePair` | `FinitePairOrtho.lean:41,51,65` |

During the design, some Lean names could be checked only by search:
`LowerSemicontinuousOn.exists_isMinOn`, `LinearMap.exists_extend` on `M`'s submodule,
`MapClusterPt.continuousAt_comp` and `eq_of_nhds_neBot`. All of them are now compiled as part of
these modules. For cluster points in closed sets, the modules use Mathlib's
`IsClosed.mem_of_mapClusterPt` (`Mathlib/Topology/ClusterPt.lean:179`).

**Recorded.**

- The axiom guards are in `MIPRE/Axioms.lean:3317-3329`.
- The blueprint has three nodes:
  - `lem:center-valued-trace` (`blueprint/src/content/03_background_results.tex:305`);
  - `thm:orthonormalization-no-abelian` (`:342`);
  - `cor:orthonormalization-finite-pair` (`blueprint/src/content/08_downstream.tex:2944`).
- `rem:orthonormalization-scope` (`03_background_results.tex:268-303`) now records the new case.
  It says that a type I part with diffuse centre still needs the general case.

**Open.**

- **H3 for general `p`.** The interface field (`MvN/Interface.lean:76-78`) is not proved; only
  `p = 1` is. That is enough for the II₁ tier, but not to instantiate the full interface.
- **The class must lack abelian projections.** `IsFinitePair` (`FinitePair.lean:92-104`) has no
  such field, and type I pairs with diffuse centre are finite pairs (`FinitePair.lean:47-51`). So
  the hypothesis of §2.8 item 5 has to come from somewhere. The C6b plan takes it from unital
  dyadic matrix units, by restricting the class and amplifying in the value lemma
  (`planning/c6b-plan.md:34-46`; §3 of this report). This section proves none of that.
- **A trace on an amplified algebra.** Suppose the class is made type II₁ by amplifying `M` by a
  II₁ factor `R`. Then H3₁ has to be applied to the amplified algebra, which needs a faithful
  tracial vector functional of its own. This section does not provide one.
  - *Faithfulness is elementary.* The `g_k` jointly separate `M`. So the projection onto the
    closure of `span(M′ g_k)` lies in `M″ = M` and fixes each `g_k`, hence is `1`. Therefore the
    vectors `g_k ⊗ Ω` are jointly cyclic for the commutant of `M ⊗ R`.
  - *Traciality on the weak-operator closed algebra is not elementary.* If the amplified algebra
    is `(M ⊗_alg R)″`, traciality extends from the algebraic tensor product by separate
    continuity: for fixed `y`, both `x ↦ τ(xy)` and `x ↦ τ(yx)` are finite sums of vector
    functionals. But that extension needs the algebraic tensor product to be dense in its
    bicommutant.
  - If the amplified algebra is instead the commutant `(M′ ⊗ 1 ∪ 1 ⊗ R′)′`, the commutation
    theorem for tensor products is needed.
  - The vendored density theorem for vector functionals may suffice for the first kind of
    extension; this was not checked. It is `inner_ampl_eq_zero_of_mem_wstar`
    (`MIPRE/Background/Repetition/CommutingRepetition/VN/Density.lean:102`), with a one-vector
    form at `:210`.
  - The C6b plan avoids the question by amplifying at the level of the standard tracial algebra
    (`tensorStep M B`, `planning/c6b-plan.md:38-43`). Its standard model is a finite pair by
    `isFinitePair_stdModel` (`MIPRE/Background/Repetition/TracialApprox.lean:148`), which carries
    a `VecTrace`; see §3.

  This item has not been sized here.
- **Textbook numbers.** Nothing in the proof relies on any of the textbook theorem numbers, and
  none has been checked. They are those of §2.6, and Kadison–Ringrose Theorem 5.3.1 and Takesaki
  IV.5.9 for the two tensor-product facts above.

## 3. The II₁ class: dyadic matrix units, no abelian projections, amplification

This section proves that a set of operators closed under products and adjoints has no nonzero
abelian projection if it carries a faithful tracial vector functional and contains unital matrix
units of every size `2ⁿ`. The proof is a trace estimate that uses no comparison theory
(Theorems K, K′). It then shows two things:

- the class of finite pairs with such units on both sides is closed under the model operations
  that C6b uses (Theorem Cl);
- amplifying the value lemma's tracial strategy by an algebra `B` with such units keeps its
  correlation and lands in the class (Theorems T and A).

In C6b these results are work packages T2 and T3 of `planning/c6b-plan.md`. They supply the
hypothesis `hII` of `povm_orthogonalization_finitePair`
(`MIPRE/Background/Orthonormalization/FinitePairOrtho.lean:65-71`, `hII` at `:67-68`) and narrow
`SoundFin` to the class. The algebra `B` itself (T4) is not constructed; §3.8 compares the
candidates.

### 3.1 Conventions

`H` is a complex Hilbert space.

* An **abelian projection** of `N : VonNeumannAlgebra H` is `IsAbelianProj N p`
  (`MIPRE/Background/Orthonormalization/Orthogonalization/MvN/Defs.lean:58-60`): `p` is a
  projection in `N` and `(pxp)(pyp) = (pyp)(pxp)` for all `x, y ∈ N`. **NA(N)** means that every
  abelian projection of `N` is `0`.
* For a set `s` of operators, **NA(s)** means that the following element `r` is `0`: any `r ∈ s`
  with `IsStarProjection r` and `(rxr)(ryr) = (ryr)(rxr)` for all `x, y ∈ s`. For `s = M.opsA`
  this is, verbatim, the hypothesis `hII` of `povm_orthogonalization_finitePair`
  (`FinitePairOrtho.lean:67-68`).
* **Matrix units.** Let `A` be a ∗-ring and `ι` a finite type. A family `e : ι → ι → A` is a
  *unital system* (`IsMatUnits e`) when
  - `eᵢⱼ eₗₘ = [j = l] eᵢₘ`,
  - `eᵢⱼ* = eⱼᵢ`,
  - `∑ᵢ eᵢᵢ = 1`.
* **`HasDyadicUnits A`**: for every `n` there is a unital system indexed by `Fin n → Fin 2`. Such a
  system has `2ⁿ` elements, and the index type needs no `Fin (2ⁿ)` casts.
* **The class.** For a bipartite model `M` with algebras `𝒜` and `ℬ`, the class is
  `IsDyadicPair M := M.IsFinitePair ∧ HasDyadicUnits 𝒜 ∧ HasDyadicUnits ℬ`. It is a condition on
  the abstract algebras of the model. `IsFinitePair` is defined at
  `MIPRE/Foundations/FinitePair.lean:92-104`.
* **The trace functional.** Let `τ : VecTrace s` (`FinitePair.lean:61-73`) have vectors
  `g₁, …, g_d`. Put `tr T := ∑ₖ ⟪gₖ, T gₖ⟫`. It is defined for every operator `T`, and `Re`
  denotes the real part.

*Short paths.* After its first full citation, a file is cited by a short path:
- `VN/…`, `Tracial/…` and `OTQCS/…` are under `MIPRE/Background/Repetition/CommutingRepetition/`;
- `MvN/…` is under `MIPRE/Background/Orthonormalization/Orthogonalization/MvN/`;
- `TracialApprox.lean` is `MIPRE/Background/Repetition/TracialApprox.lean`;
- under `MIPRE/Foundations/`: `FinitePair.lean`, `FinitePairExpand.lean`, `AncillaModel.lean` and
  `AmplCommutant.lean`;
- `FinModel.lean` is under `MIPRE/Background/LIDT/`;
- under `MIPRE/Background/Orthonormalization/`: `FinitePairOrtho.lean`, `NoAbelian.lean`,
  `CenterTrace.lean`, `CenterTraceClauses.lean` and `CenterComparison.lean`. These five modules
  are proved (§2.9);
- `Mathlib/…` is under `.lake/packages/mathlib/`;
- "the audit" is `reports/lidt-co-audit.md`.

### 3.2 Statements

**Theorem K (the key lemma; no comparison theory).** Assume:
- `s` is a set of operators closed under products and adjoints, and `τ : VecTrace s`;
- `ι` is a nonempty finite type, and `f` is a unital `ι×ι` system of operators with every
  `fᵢⱼ ∈ s`;
- `p ∈ s` is a projection that is abelian in the set sense of §3.1.

Then:
- **(K1)** `|ι| · Re tr p ≤ 1`;
- **(K2)** if `s` contains such a system for every index `Fin n → Fin 2`, then `p = 0`, that is,
  NA(s). In particular NA(N) holds for a von Neumann algebra `N` with a `VecTrace` on `N` and
  dyadic units in `N`.

**Theorem K′ (finite pairs).** If `M.IsFinitePair` and `HasDyadicUnits 𝒜`, then NA(`M.opsA`)
holds, in exactly the form of the hypothesis `hII` of `povm_orthogonalization_finitePair`.
Likewise NA(`M.opsB`) holds if `HasDyadicUnits ℬ`.

**Theorem Cl (closure of the class).**
- `HasDyadicUnits` is preserved by:
  - ∗-algebra homomorphisms;
  - passing to `Aᵐᵒᵖ`;
  - `Matrix α α A` (scalar diagonal);
  - `A × B` (componentwise).
- Hence `IsDyadicPair` is closed under:
  - `M.swap`;
  - `M.expand e` for nonempty registers. This covers every model operation at the `SoundFin`
    boundary: basis-vector ancillas, the `|t₀t₀⟩` pad and the `M_K` dilation all enter through
    `expand` (`MIPRE/Background/Repetition/TracialApprox.lean:249-256`,
    `MIPRE/Background/LIDT/FinModel.lean:50-57`);
  - at the level of the algebras, the `H ⊕ H` doubling of §4. Its algebras are `𝒜 × ℬ` and
    `ℬ × 𝒜` (audit §4.1).

**Theorem A (amplified standard form).** Let `M, B : StdTracialAlgebra.{0}` with
`HasDyadicUnits B.A`, and put `T := tensorStep M B`.
- **(A1)** For every `ψ`, `IsDyadicPair (stdModel T ψ)`. So NA holds for `R(M⊗B)′ = T.vnAlg` and
  for `R(M⊗B)″ = rightVN T`, both as operator sets and as `VonNeumannAlgebra`s.
- **(A2)** For all nonempty `α, β` and every `e`, NA holds on both sides of
  `(stdModel T ψ).expand e`. This is the shape of model that the value lemma produces
  (`TracialApprox.lean:251-256`).

**Theorem T (value transport).** Let `T : TracialStrategy.{0} X Y A₀ B₀` be a tracial strategy
with answer sets `A₀` and `B₀`, and let `B : StdTracialAlgebra.{0}`. The strategy `amplify T B` on
`tensorStep T.M B` is built from `σ ⊗ 1`, `E ⊗ 1` and `F ⊗ 1`. It is a tracial strategy with the
same correlation as `T`, hence the same winning probability in every game.

**Theorem B1 (matrix algebras).** NA(N) implies NA(`matrixAlgebra N n`) (`MvN/Defs.lean:108`).

**Theorem B1′ (the extension's representation; not proved).** NA for the extension's operator
sets `{X ⊗ 1_β}` and `{1_α ⊗ Y}` follows from NA of the base. These sets are given at
`MIPRE/Foundations/FinitePairExpand.lean:180` and `:187`. The theorem is not needed under
`IsDyadicPair`, because Theorem Cl replaces it.

**Theorem B2 (direct sums).** For `D = {a ⊕ b}` on `H ⊕ H`, NA(𝒜) and NA(ℬ) imply NA(D). Its
dyadic counterpart is the product clause of Theorem Cl.

**Theorem C (the two sides of the standard form).** For `M : StdTracialAlgebra.{0}`,
NA(`R(M)′`) ⇔ NA(`R(M)″`), through the modular conjugation `J`.
- The version for a general finite pair is **not** proved.
- Theorem C is optional under the two-sided class, since Theorem A already gives both sides.

**Lemma 15 (obstruction for `B`).** If a ∗-ring `A` has a unital ring homomorphism to `ℂ`, it has
no unital `k×k` system for `k ≥ 2`. So `B.A` cannot be a group algebra, because of the augmentation
character.

### 3.3 Proofs

Lean names are those of the prototypes described in §3.9. They were compiled sorry-free against
the repository, with axioms `propext`, `Classical.choice` and `Quot.sound` only, and they are not
committed.

**Lemma 1 (Cauchy–Schwarz in a commuting corner; `cs_eps`, `cs_comm`).** Let `x, y ∈ B(H)` and
put `α = x*x`, `β = y*y`, `γ = x*y`. If `αβ = βα` and `βγ = γβ`, then `γγ* ≤ αβ`.

*Proof.*
1. Taking adjoints of `βγ = γβ` gives `βγ* = γ*β`; also `y*x = γ*`.
2. Fix `ε > 0` and put `b = β + ε`. Then `b` is strictly positive (Mathlib's
   `isStrictlyPositive_algebraMap` and `IsStrictlyPositive.add_nonneg`). It commutes with `α`,
   `γ` and `γ*`.
3. Put `z = xb − yγ*`. Expanding with these commutations gives `z*z = αb² − 2bγγ* + βγγ*`.
4. Let `D = αb − γγ*`. Since `b − β = ε`, we get `bD = z*z + εγγ*`. The right side is `≥ 0`,
   because `εγγ*` is a commuting product of positive elements (`Commute.mul_nonneg`,
   `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean:291`).
5. `b⁻¹ ≥ 0` (`IsStrictlyPositive.ringInverse`), and `b⁻¹` commutes with `bD`. Hence
   `D = b⁻¹(bD) ≥ 0`.
6. The map `ε ↦ αβ + εα − γγ*` is norm-continuous, and the positive cone is closed
   (`CStarAlgebra.isClosed_nonneg`). Letting `ε → 0` gives `αβ − γγ* ≥ 0`. ∎

No finite-dimensional fact is used. A direct argument would split `H` into the kernel of `α` and
the closure of its range; the regularization by `ε` avoids that split.

**Lemma 2 (trace calculus).** For `τ : VecTrace s`:
- `tr` is ℂ-linear and commutes with finite sums;
- `tr 1 = ∑ₖ ‖gₖ‖² = 1`;
- `T ≥ 0` implies `Re tr T ≥ 0`, hence `T ≤ S` implies `Re tr T ≤ Re tr S`;
- `tr(T*T) = ∑ₖ ‖T gₖ‖²`;
- `tr(ST) = tr(TS)` for `S, T ∈ s` (the field `trace_mul_comm`). ∎

**Lemma 3 (= K1; `card_mul_re_tr_le_one`).**

*Hypotheses.*
- `s` is closed under products and adjoints, and `τ : VecTrace s`;
- `i₀ ∈ ι`, and `f` is a unital `ι×ι` system with every `fᵢⱼ ∈ s`;
- `p ∈ s` is a projection with `(pxp)(pyp) = (pyp)(pxp)` for all `x, y ∈ s`.

*Conclusion.* `|ι| · Re tr p ≤ 1`.

*Proof.*
1. Put `wᵢ = f_{i₀i} p ∈ s`. Then `wᵢ* = p f_{ii₀} ∈ s`.
2. Put `aᵢⱼ := wᵢ*wⱼ = p fᵢⱼ p`, using `f_{ii₀} f_{i₀j} = fᵢⱼ`. Then:
   - the `aᵢⱼ` commute pairwise, by the abelian hypothesis applied to `fᵢⱼ, fₗₘ ∈ s`;
   - `aᵢⱼ* = aⱼᵢ`;
   - `∑ᵢ aᵢᵢ = p`.
3. Lemma 1 with `x = wᵢ` and `y = wⱼ` gives `aᵢⱼ aᵢⱼ* ≤ aᵢᵢ aⱼⱼ`.
4. Let `X = ∑ᵢ wᵢwᵢ*`. Then `X* = X` and `f_{i₀i₀} X = X = X f_{i₀i₀}`.
5. *Trace of `X`.* By traciality on `wᵢ, wᵢ* ∈ s`, `tr X = ∑ᵢ tr aᵢᵢ = tr p`.
6. *Trace of `X²`.* Traciality on `wᵢ` and `wᵢ*wⱼwⱼ* ∈ s` gives
   `tr X² = ∑ᵢⱼ tr(aᵢⱼ aᵢⱼ*)`. By step 3 and monotonicity,
   `Re tr X² ≤ ∑ᵢⱼ Re tr(aᵢᵢ aⱼⱼ) = Re tr(p²) = Re tr p`.
7. *Trace of `f_{i₀i₀}`.* Traciality on `f_{ii₀}, f_{i₀i} ∈ s` gives `tr fᵢᵢ = tr f_{i₀i₀}`.
   Summing over `i` gives `|ι| · tr f_{i₀i₀} = tr 1 = 1`.
8. Put `t = Re tr p ≥ 0`. For real `c`,
   `(X − c f_{i₀i₀})*(X − c f_{i₀i₀}) = X² − 2cX + c² f_{i₀i₀} ≥ 0`.
   Hence `0 ≤ t − 2ct + c²/|ι|`.
9. Take `c = |ι| t`. This gives `t(1 − |ι| t) ≥ 0`, so `|ι| t ≤ 1` when `t > 0`. The case
   `t = 0` is trivial. ∎

The bound is tight: a rank-one projection in `M_k(ℂ)` has normalized trace exactly `1/k`.

**Lemma 4 (= K2, Theorem K; `eq_zero_of_dyadic`, and `eq_zero_of_isAbelianProj` for the
`VonNeumannAlgebra` form).**
1. Lemma 3 with `ι = Fin n → Fin 2` gives `2ⁿ t ≤ 1` for every `n`, so `t = 0`.
2. `tr p = tr(p*p) = ∑ₖ ‖p gₖ‖²`, so every `p gₖ = 0`.
3. `p = 0` by `VecTrace.separating`, since `p ∈ s`.

The `VonNeumannAlgebra` form takes `s = N`, which is closed under products and adjoints
(`mul_mem`, `star_mem`). Weak closure is never used. ∎

**Lemma 5 (transport of matrix units).**
1. A ∗-algebra homomorphism `φ : A →⋆ₐ[ℂ] B` maps unital systems to unital systems (`map_mul`,
   `map_star`, `map_sum`, `map_one`).
2. `fᵢⱼ := op(eⱼᵢ)` is a unital system in `Aᵐᵒᵖ`:
   `op(eⱼᵢ) op(eₘₗ) = op(eₘₗ eⱼᵢ) = [j = l] op(eₘᵢ)`. Adjoints and sums are similar.
3. `Fᵢⱼ := diagonal (fun _ => eᵢⱼ)` is a unital system in `Matrix α α A`. This uses
   `diagonal_mul_diagonal` and `diagonal_conjTranspose`, and the sum is computed entrywise.
4. `(eᵢⱼ, fᵢⱼ)` is a unital system in `A × B` when `e` and `f` have the same index. The common
   index `Fin n → Fin 2` is what makes this possible.

Each item lifts to `HasDyadicUnits`. ∎

**Lemma 6 (= Theorem K′; `hII_of_hasDyadicUnits`, `hII_B_of_hasDyadicUnits`).**
1. `M.opsA` is the range of the ∗-homomorphism `π ∘ πA` (`FinitePair.lean:81-82`), so it is
   closed under products and adjoints.
2. `hM.traceA` supplies a `VecTrace M.opsA` (`FinitePair.lean:102`).
3. Dyadic units `e` in `𝒜` map to units `π(πA eᵢⱼ) ∈ M.opsA` (Lemma 5.1).
4. Lemma 4 then gives NA(`M.opsA`), in exactly the binder form of `FinitePairOrtho.lean:67-68`.
5. The second side is the same theorem for `M.swap`, through `IsFinitePair.swap`
   (`FinitePairExpand.lean:172`). ∎

No `VonNeumannAlgebra` packaging is needed.

The composition with the consumer was checked against the built `FinitePairOrtho.lean` when this
report was written. The check, not committed, elaborates the term
`povm_orthogonalization_finitePair M hM hψ (hII_of_hasDyadicUnits hM hU) P ε hε`, with axioms
`propext`, `Classical.choice` and `Quot.sound` only. The consumer also needs
`[PartialOrder 𝒜] [StarOrderedRing 𝒜]`, which `SoundFin` already carries (`FinModel.lean:40-43`).

**Lemma 7 (= Theorem Cl; `IsDyadicPair.swap`, `IsDyadicPair.expand`).**
- *Swap.* Exchange the two components and use `IsFinitePair.swap`.
- *Expand.* `M.expand e` has algebras `Matrix α α 𝒜` and `Matrix β β ℬ`
  (`MIPRE/Foundations/AncillaModel.lean:287-293`). Use `IsFinitePair.expand`
  (`FinitePairExpand.lean:219`) and Lemma 5.3.
- *Doubling.* Apply Lemma 5.4 to `𝒜 × ℬ` and to `ℬ × 𝒜`. The `IsFinitePair` half of the doubled
  model belongs to the doubling (§4). ∎

*Why `expand` suffices at the boundary.* The C6a consumers apply `SoundFin` only to a model `M`
handed over by `CommutingFinitePairApprox` and to `M.expand e`:
- `FinModel.lean:50-57` and `:94-98`;
- `MIPRE/Background/QLD/FinSoundness.lean:31-36`;
- `MIPRE/Background/AnswerReduction/Instance.lean:184-186`.

The value lemma's model is itself `(stdModel …).expand (basisVec …)`, with the `M_K` dilation
inside the matrix algebra (`TracialApprox.lean:249-256`). So pads, one-sided ancillas and
dilations are all instances of `expand`.

**Lemma 8 (= Theorem A; `isDyadicPair_stdModel_tensorStep`, `hII_expand_stdModel_tensorStep`).**
1. `HasDyadicUnits B.A` gives `HasDyadicUnits T.A` through `stepInclRight M B`
   (`MIPRE/Background/Repetition/CommutingRepetition/VN/TensorPower.lean:59-67`). This map is
   `b ↦ 1 ⊗ b`, a unital ∗-homomorphism.
2. The corestriction of `T.L` to `T.vnAlg` gives `HasDyadicUnits T.vnAlg`. The corestriction exists
   by `L_mem_vnAlg` (`VN/ConcreteVN.lean:167`).
3. The corestriction of `T.R` to `rightVN T` exists by `Rop_mem_rightVN` (`TracialApprox.lean:77`).
   Applied to the units of `T.Aᵐᵒᵖ` given by Lemma 5.2, it gives `HasDyadicUnits (rightVN T)`.
4. The algebras of `stdModel T ψ` are `T.vnAlg` and `rightVN T` (`TracialApprox.lean:125-132`).
   With `isFinitePair_stdModel` (`TracialApprox.lean:148`), this gives A1.
5. A2 is Lemma 7 (expand) followed by Lemma 6 on both sides.
6. *`VonNeumannAlgebra` form.* NA of `T.vnAlg` and `rightVN T`, packaged as `VonNeumannAlgebra`s,
   is Lemma 4 with the restricted `VecTrace` (`VecTrace.mono`, `FinitePairExpand.lean:61`).
   The packaging needs no bicommutant theorem: both sets are commutants, and `S‴ = S′`. It was
   compiled in an earlier prototype with units indexed by `Fin (2ⁿ)` (§3.9). ∎

**Lemma 9 (= Theorem T; `amplify`, `amplify_correlation`).**
1. Let `inclL := stepInclLeft T.M B` (`VN/TensorPower.lean:48-56`, `a ↦ a ⊗ 1`), into
   `(tensorStep T.M B).A`. Then `τ(inclL a) = τ(a) · τ_B(1) = τ(a)`, by
   `stepτ_inclLeft_mul_inclRight` (`VN/TensorPower.lean:77`) with `b = 1`.
2. `IsPosElem` (`Tracial/Interface.lean:44-45`, a finite sum of elements `c*c`) is preserved by
   ∗-homomorphisms. The prototype proves this directly (`isPosElem_map`). The vendored tree already
   has it as `IsPosElem.starAlgHom_map` (`OTQCS/Compile.lean:109`).
3. Normalization follows from step 1 and multiplicativity:
   `τ(inclL(σ)* inclL(σ)) = τ(inclL(σ*σ)) = τ(σ*σ) = 1`.
4. `E_sum` and `F_sum` follow from `map_sum` and `map_one`.
5. The correlation is `Re τ(σ*(Eₓᵃ σ F_yᵇ))` (`Tracial/Strategy.lean:60-62`). It is preserved,
   because `inclL` is multiplicative and ∗-preserving and `τ ∘ inclL = τ`. ∎

So `povmValue_stdModel` (`TracialApprox.lean:213`) gives `amplify T B` the same winning
probability. `commutingFinitePairApprox` can be rerun on `amplify T B` unchanged, except for its
class-membership proof, which is Lemma 8.

**Lemma 10 (subprojections; `isAbelianProj_of_le`).** Let `P` be abelian in `N`, and let `r ∈ N`
be a projection with `rP = r`.
1. Taking adjoints gives `Pr = r`.
2. Hence `P(rxr)P = rxr`.
3. Abelianness of `P`, applied to `rxr, ryr ∈ N`, gives that of `r`. ∎

**Lemma 11 (equivalent projections; `isAbelianProj_of_equiv`).** If `r` is abelian, `u ∈ N` and
`u*u = r`, then `uu*` is abelian.

*Proof.*
1. `uu*` is a projection (`MvN/TypeIIINet.lean:63`), and `ur = u` (`:45`).
2. `uu* z uu* = u(r(u*zu)r)u*`, and `(u(rar)u*)(u(rbr)u*) = u((rar)(rbr))u*`.
3. Apply abelianness of `r` to `u*xu` and `u*yu`. ∎

**Lemma 12 (localization; `eq_zero_of_local`).** Let `Eᵢ ∈ N` be projections with
`∑ᵢ Eᵢ = 1`. Suppose that for every `i`, every abelian `l` with `lEᵢ = l` is `0`. Then NA(N).

*Proof.*
1. Let `P ≠ 0` be abelian. For some `i`, `x = EᵢP ≠ 0`.
2. `exists_polar` (`MvN/PolarDecomp.lean:291`) gives `u ∈ N` with `u*u = rightSupport x =: r`
   and `uu* = leftSupport x =: l`.
3. `rP = r` (`MvN/BlockCalc.lean:465`), so `r` is abelian by Lemma 10.
4. `lEᵢ = l` (`MvN/BlockCalc.lean:475`), and `l` is abelian by Lemma 11. So `l = 0` by
   hypothesis.
5. Then `u = 0`, so `r = 0`, and `x = xr = 0` (`MvN/BlockCalc.lean:453`). This contradicts
   step 1. ∎

**Lemma 13 (corner of `M_n(N)`; `corner_eq_zero`).** If `l` is abelian in `matrixAlgebra N n`,
`l · matrixUnit i i = l`, and NA(N) holds, then `l = 0`.

*Proof.*
1. By `entry_mul_matrixUnit` (`MvN/MatrixFactor.lean:71`), `entry_star` (`MvN/Matrix.lean:221`)
   and `l* = l`, only the entry `l_{ii}` can be nonzero.
2. `q := l_{ii} ∈ N` (`MvN/Matrix.lean:253`). From `entry_mul` (`MvN/Matrix.lean:212`),
   `(lXl)_{ii} = q X_{ii} q`, and the other entries in row and column `i` vanish.
3. `q` is a projection. It is abelian: test with the amplifications of `x` and `y`.
4. So `q = 0` by NA(N), and `l = 0` by `ext_entry` (`MvN/BlockCalc.lean:60`). ∎

**Proof of Theorem B1 (`matrixAlgebra_noAbelian`).** Apply Lemma 12 with `Eᵢ = matrixUnit i i`
(`MvN/MatrixFactor.lean:53`, `:89`). The localization hypothesis is Lemma 13. ∎

Theorem B1′ would need Lemma 13 redone for the extension's representations:
- `toCLM ∘ liftLeft ∘ map` on the first side (`FinitePairExpand.lean:180`);
- `toCLM ∘ liftRight ∘ map` on the second (`:187`).

Lemmas 10–12 are representation-free. Under `IsDyadicPair`, Lemma 7 supersedes B1′.

**Proof of Theorem B2.** Let `P = p₁ ⊕ p₂ ∈ D` be an abelian projection, so each `pᵢ` is a
projection in its summand.
1. For `a, a' ∈ 𝒜`, the elements `a ⊕ 0` and `a' ⊕ 0` lie in `D`, and
   `P(a ⊕ 0)P = p₁ap₁ ⊕ 0`. Hence `p₁` is abelian in `𝒜`, and `p₁ = 0`.
2. Symmetrically `p₂ = 0`, so `P = 0`.

Equivalently, apply Lemma 12 with the central projections `1 ⊕ 0` and `0 ⊕ 1`. ∎

The dyadic version (Lemma 5.4) is compiled. The NA version is not, because the doubled model has
no Lean representation yet.

**Lemma 14 (`J R′ J ⊆ R″`; `conjJ_mem_rightVN`).** Write `R′ = M.vnAlg`, `R″ = rightVN M`, and
`Ω` for the trace vector.
1. For `x, y ∈ R′`: `JxJ(yΩ) = yx*Ω` (`J_apply_traceVector`, `VN/ConcreteVN.lean:184`).
2. Hence for `g ∈ R′`: `(JxJ)g(yΩ) = g(JxJ)(yΩ)`.
3. The vectors `L(a)Ω = ι a` are dense (`L_traceVector`, `TracialApprox.lean:86`; `ι_induction`,
   `VN/ConcreteVN.lean:47`). So `JxJ` commutes with `R′`, that is, it lies in `R″`
   (`mem_rightVN_iff`, `TracialApprox.lean:72`). ∎

**Proof of Theorem C (`noAbelian_iff`).** `conjJ` is involutive, additive, multiplicative and
∗-preserving: `conjJ_conjJ`, `conjJ_add`, `conjJ_mul` and `conjJ_star` (`VN/ConjJCalc.lean:47`,
`:55`, `:60`, `:72`). It maps
- `R″ → R′`, by `conjJ_mem_vnAlg` (`Tracial/CommutantPullback.lean:99`) together with
  `L_mul_eq_of_mem_rightVN` (`TracialApprox.lean:81`);
- `R′ → R″`, by Lemma 14.

So if `q` is abelian in one algebra, `JqJ` is abelian in the other, and `q = J(JqJ)J`. ∎

*By-product* (`mem_rightVN_of_commute_L`). If `T` commutes with every `L(m)`, then `JTJ ∈ R′`, so
`T ∈ R″`. That is `L(M)′ ⊆ R″`; the reverse inclusion is `L_mul_eq_of_mem_rightVN`.

*Why the general finite-pair version of Theorem C is not proved.* The classical route needs:
- `(𝒜q)′ = q𝒜′q`, which is elementary;
- `(𝒜q)″ = 𝒜q`, through central supports and induction;
- "an abelian algebra with a cyclic vector is maximal abelian" (Kadison–Ringrose, Vol. II, §9.1).

The last two are in neither Mathlib nor the vendored trees. They are estimated at 1–2k lines, by
analogy and not by measurement. The two-sided class makes them unnecessary, since Lemma 8 gives
units on both sides.

**Lemma 15 (obstruction for `B`).** Let `χ : A → ℂ` be a unital ring homomorphism and `e` a
unital `k×k` system in `A`. Then `k ≤ 1`.

*Proof.* Suppose `k ≥ 2` and put `cᵢⱼ = χ(eᵢⱼ)`.
1. `c₁₁ = c₁₂c₂₁ = c₂₁c₁₂ = c₂₂`, by commutativity of `ℂ`.
2. `c₁₁ = c₁₁² = c₁₁c₂₂ = χ(e₁₁e₂₂) = 0`. Likewise every `cᵢᵢ = 0`.
3. Then `1 = χ(∑ᵢ eᵢᵢ) = 0`, a contradiction. ∎

So a group algebra, with its augmentation character, cannot be `B.A`.

### 3.4 Where the amplification happens

The lift of Theorem T is made at the level of `StdTracialAlgebra`, not at the level of models. It
goes through the vendored `tensorStep` (`VN/TensorStep.lean:640-654`). Its carrier is
`M.A ⊗[ℂ] B.A` and its trace is `stepτ`, with `stepτ (a ⊗ b) = τ(a) τ_B(b)` (`:55-57`).
- After the lift, the rest of `commutingFinitePairApprox` (`TracialApprox.lean:224-263`) runs
  unchanged: the standard model, `isFinitePair_stdModel` (`:148`), the Halmos dilation
  (`:249-250`) and `IsFinitePair.expand`. So the finite-pair property of the amplified model costs
  nothing.
- A model-level tensor product would instead need the commutation theorem for tensor products.
- `tensorStep` needs both factors in the same universe (`VN/TensorStep.lean:44-46`). The
  reduction's strategy lives in `TracialStrategy.{0}` (`TracialApprox.lean:180`, `:247`). So
  `B : StdTracialAlgebra.{0}`, and `B` must be built in `Type`.

### 3.5 Why a trace estimate rather than comparison

Theorem K uses no fact of field H3 (§2). The comparison route would be strictly more work, because
the fields of `IsCenterValuedTrace` (`MvN/Defs.lean:169`) do not suffice for it:
- It needs generalized comparability: a central `z` with `zp ≾ z e₁₁` and
  `(1 − z)e₁₁ ≾ (1 − z)p`. The field `equiv_of_eq` gives equivalence only at *equal* centre-valued
  traces. Finding a subprojection with a prescribed centre-valued trace is divisibility, which is
  what is being proved.
- The argument would then run as follows:
  - `(1 − z)e₁₁` is equivalent to a subprojection of an abelian projection, hence abelian;
  - its corner holds the next level of nested matrix units, so `(1 − z)e₁₁ = 0`;
  - so `z = 1` and `p ≾ e₁₁`, and iterating gives `τ(p) ≤ 2⁻ᵏ`.
- Rerunning the trace argument with the centre-valued trace `E` in place of `τ` would need a
  Kadison–Schwarz inequality `E(h)² ≤ E(h²)`, which is not a field of H3.

The trace argument also avoids the "centre of the tensor product" that the audit listed for the
II₁ restriction (`reports/lidt-co-audit.md:488-491`).

### 3.6 What the results assume

- Nothing from H3: no centre-valued trace and no comparison theory.
- Polar decomposition is used only in Theorem B1, through the vendored `exists_polar`
  (`MvN/PolarDecomp.lean:291`).
- The orthonormalization tier as a whole still needs H3. `exists_selection_typeII₁` consumes
  `hE : IsCenterValuedTrace M p E` beside `hII` (`MvN/Finite.lean:77-82`), and Theorem K supplies
  only `hII`. The centre-valued trace at `p = 1` (§2) comes from three modules:
  - `CenterTrace.lean` (`exists_isCenterExpectation`, `:384`);
  - `CenterTraceClauses.lean`;
  - `CenterComparison.lean` (`exists_isCenterValuedTrace`, `:355`).

  `povm_orthogonalization_vecTrace` consumes it (`NoAbelian.lean:99`, used at `:106`). So
  `povm_orthogonalization_finitePair` asks the caller for `hII` alone.
- NA passes to corners and `HasDyadicUnits` does not. Corners need no predicate of their own,
  though:
  - the `hII` of `exists_selection_typeII₁` is quantified over the whole algebra
    (`MvN/Finite.lean:80`), and it is used as `fun r hr _ => hII r hr` at `NoAbelian.lean:75`;
  - so NA of the ambient algebra, which Theorem K′ gives, suffices at every corner.

  The cost of the dyadic predicate is that NA must be derived through a `VecTrace` on the same
  set, and every member of the class has one.

### 3.7 Consequence for the class

The class predicate is to be `IsDyadicPair`:
- `SoundFin` becomes `∀ M, IsDyadicPair M → SoundIn M`. The class is smaller, so this is a weaker
  hypothesis and the conditional theorem is stronger.
- The value lemma amplifies by a fixed `B` with `HasDyadicUnits B.A` (Theorems T and A).
- C6b's use of de la Salle's theorem gets `hII` from Theorem K′.

The C6a declarations to restate are:
- `SoundFin` and `SoundFin.expand` (`FinModel.lean:40-57`);
- `approxSoundIn_commuting_of_fin` (`FinModel.lean:94-98`);
- `CommutingFinitePairApprox` (`FinitePair.lean:111-119`);
- `commutingFinitePairApprox`, now on `amplify T B` (`TracialApprox.lean:224-263`);
- `QLD.approxSoundIn_commuting_of_fin` (`MIPRE/Background/QLD/FinSoundness.lean:31-36`);
- `answerReduction_soundIn_commuting_fin`
  (`MIPRE/Background/AnswerReduction/Instance.lean:184-186`).

What else changes, and what does not:
- Their guards keep their names (`MIPRE/Axioms.lean:3298`, `:3301-3302`, `:3305`).
- The blueprint nodes `def:finite-pair`, `lem:finite-pair-expand`, `lem:co-value-finite-pair` and
  `def:lidt-sound-fin` change (`blueprint/src/content/08_downstream.tex:2788`, `:2816`, `:2841`,
  `:2868`).
- `mipco_eq_core_of_lidtFin` (`MIPRE/MIPCo.lean:115-121`) keeps its text.
- Each consumer proof is 3–10 lines and gains one closure call (Lemma 7).
- Until `B` exists, `commutingFinitePairApprox` gains a hypothesis `∃ B, HasDyadicUnits B.A`. Its
  proof changes only in `T ↦ amplify T B` (Lemma 9) and in the membership witness (Lemma 8).

Estimate: 80–150 Lean lines plus the blueprint edits, not compiled.

### 3.8 The algebra `B`

**Resolution.** Candidate (b), the twisted Pauli algebra, was chosen (plan, T4). Both candidates
were then prototyped in Lean, sorry-free and with the standard axioms only:
- (a), 426 lines: the instance-elaboration risk materialized and was worked around (a
  field-by-field `CStarAlgebra` instance on `lp Fib ∞`, registered through a semireducible
  definition), and its units are unital only after representation, `B.L (Σ e_ii) = 1`;
- (b), 688 lines, on `ℓ²(ℕ →₀ ℤ/2 × ℤ/2)`: its units `e_ij = Π_k X_k^{i_k} p_k X_k^{j_k}`, with
  `p_k = (1 + Z_k)/2`, satisfy `Σ e_ii = 1` in `B.A` itself, so it gives `HasDyadicUnits B.A` as
  Theorems A and T state it. The `StarOrderedRing` risk below does not arise: `StdTracialAlgebra`
  asks only for a ∗-algebra over `ℂ`.

The rest of this subsection is the analysis that preceded the choice.


Every use of Theorems A and T is conditional on some `B : StdTracialAlgebra.{0}` with dyadic
units. `B` need not be a factor or a II₁ algebra. Neither Mathlib nor the vendored trees provide
one.

**What a `StdTracialAlgebra` needs** (`Tracial/Interface.lean:102-123`):
- a ring, star ring and `Algebra ℂ` with `StarModule ℂ`;
- a linear `τ` with `τ_one`, `τ_mul_comm` and `τ_star`;
- a complete Hilbert space `H` and a dense `ι : A →ₗ[ℂ] H` with `⟪ι a, ι b⟫ = τ(a* b)`;
- ∗-homomorphisms `L : A → B(H)` and `R : Aᵐᵒᵖ → B(H)` with `L_apply`, `R_apply` and
  `LR_commute`.

Faithfulness of `τ` is **not** required.

**The reduction to a C*-algebra.** The vendored `Density.ofTracialState`
(`Tracial/Density/TracialGNS.lean:188`) takes:
- a unital `CStarAlgebra 𝒞 : Type` with `[PartialOrder 𝒞] [StarOrderedRing 𝒞]` (`:36`);
- a state `τ : 𝒞 →ₚ[ℂ] ℂ` with `τ 1 = 1` that is tracial.

It returns a `StdTracialAlgebra.{0}` with `A := 𝒞` and `H := τ.GNS` (`:190`, `:197`). It already
provides the GNS space, the left action, the right action (`rightMul`, `:76`, bounded by
traciality) and density. So `B` reduces to a C*-algebra in `Type` with a tracial state and dyadic
units. Both candidates below can go through it.

**What the units must give.** For each `k`, the units must give a (possibly non-unital)
∗-homomorphism `φ_k : M_{2ᵏ}(ℂ) → B.A` with `B.L (φ_k 1) = 1` and `B.R (op (φ_k 1)) = 1`. If
`φ_k 1 = 1` in `B.A` itself, this is `HasDyadicUnits B.A`, and Theorem A applies as stated.

**Candidate (a): the ultraproduct GNS.**
- *Algebra.* `B.A := lp Fib ∞` with `Fib n := CStarMatrix (Fin 2ⁿ) (Fin 2ⁿ) ℂ`.
  - Mathlib gives `CStarMatrix.instCStarAlgebra`
    (`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:824`, which needs
    `open scoped ComplexOrder`).
  - For `lp _ ∞` it gives only `NonUnitalCStarAlgebra`, `NormedRing` and the commutative instance
    (`Mathlib/Analysis/CStarAlgebra/lpSpace.lean:24-35`).
  - The order comes from `CStarAlgebra.spectralOrder` and `spectralOrderedRing`.
- *Trace.* `τ(x) := lim_U tr(xₙ)/2ⁿ` along a free ultrafilter `U` (`Filter.hyperfilter`).
  - The sequence is bounded by `‖x‖`, so the limit exists by compactness. It is linear by
    uniqueness of limits.
  - Positivity holds fibrewise and passes to the limit.
  - Traciality is `Matrix.trace_mul_comm`, and `τ 1 = 1`.
  - This `τ` is not faithful, which is allowed.
- *Units.* In fibre `n ≥ k`, `φ_k x := reindex (blockDiagonal (fun _ => x))` along
  `Fin 2ᵏ × Fin 2ⁿ⁻ᵏ ≃ Fin 2ⁿ`. Fibres `n < k` get `0`.
- *Unital only after representation.*
  - `1 − φ_k 1` vanishes on the fibres `n ≥ k`, a set in `U`.
  - So `‖ι((1 − φ_k 1) b)‖² = 0` for every `b`. Hence `L(1 − φ_k 1) = 0` by density, and the
    same holds for `R`.
  - In `B.A` itself `φ_k 1 ≠ 1`, so `HasDyadicUnits B.A` fails.
- *Size.* The survey put this candidate at 550–800 lines: the trace about 150, the units about
  150, unitality about 60, and a right action about 100–150, which `ofTracialState` now supplies.
  That estimate rests on an elaboration premise that did not reproduce:
  - the one-line instance `CStarAlgebra (lp Fib ∞)` fails at default heartbeats and compiles
    only with them raised to 1,000,000 (about 30 s);
  - with it in place, `InnerProductSpace ℂ f.GNS` timed out at 1,000,000 heartbeats, for a
    positive functional `f` on `lp Fib ∞`;
  - a wrapper type or explicit instances may be needed throughout;
  - whether instantiating `ofTracialState` at this algebra avoids the timeout is untested.

  The figure should be budgeted higher, or the instance strategy prototyped first.

**Candidate (b): a twisted Pauli (CAR) algebra.**
- *Algebra.* Take `Γ = ℕ →₀ (ZMod 2 × ZMod 2)`, with twisted left-regular unitaries `u_g` on
  `ℓ²(Γ)` (the Pauli strings). Let `𝒞` be the norm closure of their span. A closed
  `StarSubalgebra` is a C*-algebra by `StarSubalgebra.cstarAlgebra` (used at
  `Mathlib/Analysis/CStarAlgebra/Classes.lean:109`).
- *Trace.* `τ = ⟨δ₀, · δ₀⟩`. It is tracial on the span, where `τ(u_g) = [g = 0]`, and it extends
  to the closure by continuity.
- *Units.* Take products over the first `n` sites of the Pauli matrix units `(1 ± Z)/2`,
  `X(1 ± Z)/2`, …, indexed by `Fin n → Fin 2` (Jordan–Wigner style, in the CAR form). They are
  genuinely unital in `B.A`, so `HasDyadicUnits B.A` holds and Theorem A applies as stated.
- *Size.* Built entirely by hand, the survey put it at 0.9–1.2k lines, covering:
  - the 2-cocycle and its identity;
  - weighted-permutation unitaries on both sides;
  - an antiunitary `J` for `R`;
  - density of `span {δ_s}`;
  - the units.

  Through `ofTracialState` the right action and density come for free. The re-estimate is
  600–1500 lines, unmeasured; the comparators are `VN/Amplify.lean` (486 lines) and
  `VN/TensorStep.lean` (666 lines).
- *Risk.* `ofTracialState` needs `[PartialOrder 𝒞] [StarOrderedRing 𝒞]` on the closed
  subalgebra. Whether these instances are available for `StarSubalgebra.cstarAlgebra` is
  unchecked.

**Rejected.**
- *Group algebras `ℂ[G]`, even of ICC groups.* Estimate: at least 3–5k lines.
  - By Lemma 15 they never contain unital matrix units: the augmentation character would compose
    to a unital ∗-homomorphism `M_N(ℂ) → ℂ`.
  - The II₁ property would then exist only in `L(G)`. That needs factoriality from ICC, absence of
    abelian projections in a diffuse factor, and a transfer to `R(M ⊗ ℂ[G])′` — essentially the
    tensor commutation theorem.
  - Mathlib also has no `StarRing` instance on `MonoidAlgebra`.
- *The complex Clifford algebra of `ℂ^(ℕ)`.* Estimate: at least 1.5k lines.
  - Mathlib's star on `CliffordAlgebra` is `reverse ∘ involute`. It is ℂ-*linear* (`star_smul`,
    `Mathlib/LinearAlgebra/CliffordAlgebra/Star.lean:55-56`) and sends `ι m` to `−ι m` (`:50`).
  - So it is not a `StarModule ℂ` structure, and a conjugate-linear star would have to be built.
  - Mathlib gives neither a basis nor a trace for it, nor `Cl(ℂ²ⁿ) ≅ M_{2ⁿ}(ℂ)`, and the GNS would
    still be needed.
- *Iterating vendored constructions.*
  - `amplify` (`VN/Amplify.lean:382`) and `tensorStep`/`tensorPow` (`VN/TensorPower.lean:89`)
    give only finite `M_{2ⁿ}(ℂ)`. One fixed `n` bounds `τ(r)` by `2⁻ⁿ` but does not force
    `r = 0`.
  - The vendored tree has no infinite tensor product or direct limit.
  - `TracialSub.model` (`VN/SubModel.lean:43`, `:441`) needs an existing standard algebra whose
    `B(H)` already holds the infinite system.

**What the class predicate must then say.**
- *With candidate (b)*, the units are unital in the abstract algebra. Theorem A's hypothesis
  `HasDyadicUnits B.A` and the class `IsDyadicPair` stand as stated and prototyped.
- *With candidate (a)*, the units are unital only in the images `B.L(B.A)` and `B.R(B.Aᵐᵒᵖ)`.
  - The hypothesis on `B` must then be the represented form above.
  - Step 1 of Lemma 8 cannot use `stepInclRight`; the units must be transported through the
    representation instead.
  - On the left, `stepL = tensorRep M.L B.L` (`VN/TensorStep.lean:510-512`) sends `1 ⊗ b` to
    `extendStep (mapL 1 (B.L b))` (`tensorRep0_tmul`, `:400`; `tensorRep`, `:446`). That is `1`
    when `B.L b = 1` (`extendStep_one`, `:376`).
  - The right side goes through `stepR` (`:515`) and `opDistrib_op_tmul` (`:502`).
  - The model-level predicate is unaffected for the value lemma's model, whose algebras are the
    operator algebras `T.vnAlg` and `rightVN T` themselves.
- *A class stated on operators* (`M.opsA`, `M.opsB`) instead of the abstract algebras would need
  the closure under `expand` redone for the representations `toCLM ∘ liftLeft` and
  `toCLM ∘ liftRight` (`FinitePairExpand.lean:180`, `:187`). The key step is
  `liftLeft_diagonal_const` (`MIPRE/Foundations/AmplCommutant.lean:142`, used at
  `FinitePairExpand.lean:252`).

None of this is compiled; the survey sized the transports at 200–300 lines.

**Not evaluated.**
- The algebraic direct limit `⋃ₖ M_{2ᵏ}(ℂ)`, realized concretely: for example, the subalgebra of
  `lp Fib ∞` generated by the images of the `φ_k`. Its normalized trace is eventually constant,
  so it needs no ultrafilter.
- `VN/StandardFormOf.lean`, which builds a `VonNeumannAlgebra` standard form from a faithful vector
  state (not a `StdTracialAlgebra`).
- The vendored pattern `TensorPowerData` (`OTQCS/Compile.lean:62`), as an alternative way to state
  the lift of Theorem T.

### 3.9 Prototype and sizes

None of the prototypes is committed. All were compiled with `lake env lean` against the
repository, sorry-free, with axioms `propext`, `Classical.choice` and `Quot.sound` only.
- **Theorems K, K′, Cl, A and T (Lemmas 1–9).** One file of 494 lines, importing only
  `TracialApprox`, `VN/TensorPower` and `MvN/Defs`. The axioms were checked for
  `hII_expand_stdModel_tensorStep`, `amplify_correlation`, `eq_zero_of_isAbelianProj`,
  `IsDyadicPair.expand` and `HasDyadicUnits.prod`.
- **Theorems B1 and C (Lemmas 10–14).** Two earlier prototype files of 178 and 82 lines, each
  each recompiled independently three times during the review.
- **The `VonNeumannAlgebra` form of A1 (Lemma 8.6).** A third earlier file of 365 lines, with units
  indexed by `Fin (2ⁿ)`.

| item | lines | status |
|---|---|---|
| `IsMatUnits`, `HasDyadicUnits` and transports (Lemma 5) | 75–90 | compiled, 76; goes to `MIPRE/Foundations/` |
| Lemma 1 (`cs_eps`, `cs_comm`) | 72–90 | compiled, 72 |
| Lemma 2 (trace calculus) | 45–60 | compiled, 47 |
| Lemma 3 (`card_mul_re_tr_le_one`, on a set, any index) | 105–120 | compiled, 106 |
| Lemma 4 (`eq_zero_of_dyadic`, `eq_zero_of_isAbelianProj`) | 35–40 | compiled, 34 |
| Lemmas 6–7 (`hII_of_hasDyadicUnits`, both sides; `IsDyadicPair` with `swap`, `expand`) | 45–55 | compiled, 45; `Foundations` side |
| Lemma 8 (Theorem A) | 35–45 | compiled, 33; `Background` side (names `CommutingRepetition`) |
| Lemma 9 (Theorem T) | 50–60 | compiled, about 50 |
| restatement of C6a to the class (§3.7) | 80–150 + blueprint | not compiled |
| the algebra `B` (§3.8) | 750–850 | prototyped (twisted Pauli algebra, 688) |
| Theorem B1 with Lemmas 10–13 | 125–140 | compiled; optional under `IsDyadicPair` |
| Theorem C, `mem_rightVN_of_commute_L` | 60–80 | compiled; optional |
| Theorem B1′ and the NA form of B2 | 150–250 + 40–60 | not compiled; not needed under `IsDyadicPair` |
| general finite-pair Theorem C | 1000–2000 (analogy) | not attempted; not needed under the two-sided class |

### 3.10 Status and open points

Compiled in prototypes: Theorems K, K′, A, T, B1 and C, and Theorem Cl except the doubling's
`IsFinitePair` half. Proved on paper only: Lemma 15 and the NA form of Theorem B2.

The composition of Theorem K′ with `povm_orthogonalization_finitePair` now elaborates (Lemma 6).
At design time, before the consumer module was built, it could be checked only as a textual match
of the hypothesis. H3 at `p = 1`, which the tier also needs, is supplied by the
modules `CenterTrace.lean`, `CenterTraceClauses.lean` and `CenterComparison.lean` (§2, §3.6).

Open:
- **The construction of `B`.** Chosen and prototyped, not yet in the repository: the twisted
  Pauli algebra (§3.8), about 0.75–0.85k lines once split into `MIPRE/Foundations/MatUnits.lean`
  and a `Background` module that names `CommutingRepetition`.
- **The restatement of C6a** to `IsDyadicPair` (§3.7): not done.
- **The `IsFinitePair` half of the doubled `H ⊕ H` model.** It belongs to the doubling (§4); only
  the algebra-level closure (Lemma 5.4) is done.
- **Universe.** Theorems A and T are stated at universe `0`, because `stdModel`, `rightVN` and
  `isFinitePair_stdModel` live in a section with `M : StdTracialAlgebra.{0}`
  (`TracialApprox.lean:55-57`). So `B` must be built in `Type`.
- **Theorem B1′ and the general finite-pair Theorem C.** Not proved. Both are unnecessary under
  the two-sided class `IsDyadicPair`; under a one-sided or NA-only class they would be needed.
- **Confidence.**
  - High for Theorems K, K′, Cl, A and T, and for B1 and C (compiled).
  - Medium for the uncompiled NA form of B2, which is elementary and not needed.
  - Medium for the size of `B` (prototyped, not yet modularized).

## 4. The H ⊕ H doubling

This section shows that a doubled model `D(M)` on `H ⊕ H` can supply, for any finite pair `M`, the
swap symmetry that the vendored core assumes. `D(M)` is again a finite pair, and it has no abelian
projections when `M` has none. It carries a flip that fixes its state and exchanges the players, and
every vendored use of swap symmetry is one of three facts that hold in it. Entering and leaving
`D(M)` costs exactly the vendored constants: 3ε for goodness, 2σ for unsymmetrization and
100ζ^{1/4} for orthonormalization. So the error cascade into `mainFormalError` and `deltaSim` is
unchanged.

In C6b this is work package M2 of `planning/c6b-plan.md`. The port's main theorem (M13) and the
semidefinite step (M9, §5) both use it. It replaces the vendored role-register symmetrization,
which works only for tensor products (audit §4.1).

Path conventions in this section:
- `LDT/` stands for `MIPRE/Background/LIDT/MIPStarRE/LDT/`;
- `Foundations/` stands for `MIPRE/Foundations/`;
- `Ortho/` stands for `MIPRE/Background/Orthonormalization/`;
- `Mathlib/` is the pinned Mathlib.

### 4.1 Setting and notation

`M = (H, ψ, 𝒞, π, 𝒜, πA, ℬ, πB)` is a bipartite model (`Foundations/BipartiteModel.lean:57-65`).
It is built over the state model of `Foundations/StateModel.lean:46-55`. It has these properties:
- `‖ψ‖ = 1`.
- `𝒜` and `ℬ` are partially ordered, as `POVMIn` requires (`Foundations/Measurement.lean:260`), and
  are star-ordered rings, as `SoundFin` assumes (`MIPRE/Background/LIDT/FinModel.lean:40-43`).
- Where stated, `M` is a finite pair (`Foundations/FinitePair.lean:92-104`), with the fields
  `injA`, `injB`, `commutantA`, `commutantB`, `traceA` and `traceB`. `VecTrace` is at
  `FinitePair.lean:61-73`, and `opsA` and `opsB` are at `:81-86`.

Write `ā := π(πA a)` for `a ∈ 𝒜` and `b̄ := π(πB b)` for `b ∈ ℬ`. Further:
- `qform(T) = Re⟪ψ, π(T)ψ⟫` (`Foundations/StateModel.lean:70`);
- `bornProb(a, b) = qform(πA a · πB b)` (`Foundations/POVMValue.lean:148`).

**The local algebra** is `𝒩 := 𝒜 × ℬ`, with componentwise operations. `Prod.instStarOrderedRing`
makes it star-ordered (`Mathlib/Algebra/Order/Star/Prod.lean:20-35`). Write `x = (x¹, x²)`.

**The doubled model `D(M) : BipartiteModel (𝒞 × 𝒞) 𝒩 𝒩`.**
- Space: `H_D = Ampl (Fin 2) H = H ⊕ H` (`Foundations/OperatorMatrix.lean:50`).
- State: `Ψ = (ψ/√2, ψ/√2)`.
- Representation: `π_D = toCLMStarAlgHom ∘ mapMatrixStarAlgHom π ∘ pairDiag`, so
  `π_D(c₁, c₂) = π c₁ ⊕ π c₂`. Here `pairDiag : R × R →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) R` sends `c` to
  `diagonal ![c.1, c.2]`.
- First player: `πA_D x = (πA x¹, πB x²)`, so `L(x) := π_D(πA_D x) = x̄¹ ⊕ x̄²`.
- Second player: `πB_D x = (πB x², πA x¹)`, so `R(x) := x̄² ⊕ x̄¹`. For `x = (a, b)` this is
  `R(a, b) = b̄ ⊕ ā`.
- Both players share the abstract algebra `𝒩`.

**Flips.**
- On the space: `J(ξ, η) = (η, ξ)`.
- On the joint algebra: `σ = Prod.swap`, a ⋆-automorphism of `𝒞 × 𝒞`.

**Definition (symmetric model, `SymModel`).** A symmetric model is a model
`N : BipartiteModel 𝒦 𝒩 𝒩` together with a ⋆-endomorphism `σ` of `𝒦` such that:
- `σ ∘ πA = πB` and `σ ∘ πB = πA`;
- `qform(σk) = qform(k)` for every `k ∈ 𝒦`.

This replaces the fields `permInvState` and `densityFixed` of the vendored `SymStrat`
(`LDT/Test/StrategyCore.lean:519-527`).

**Definition (`NoAb`).** For a set `s` of operators, `NoAb(s)` means: every star projection
`r ∈ s` whose corner `r s r` is commutative is `0`. This is the hypothesis `hII` of the
orthonormalization tier `povm_orthogonalization_finitePair` (`Ortho/FinitePairOrtho.lean:67-68`).

### 4.2 Statements

**Theorem A (`D(M)` is a symmetric finite pair with the right order).**
1. `D(M)` is a bipartite model, and `‖Ψ‖ = 1`.
2. `J` is a self-adjoint unitary. It satisfies `JΨ = Ψ`, `J π_D(c) J = π_D(σc)` and
   `J L(x) J = R(x)`. `(D(M), σ)` is a `SymModel`.
3. If `M` is a finite pair, so is `D(M)`:
   - injectivity holds;
   - `opsA(D)′ = opsB(D)` and `opsB(D)′ = opsA(D)`;
   - both algebras carry a `VecTrace`, with `τ_D(L(a, b)) = ½(τ_𝒜(a) + τ_ℬ(b))`.
4. **Order agreement.** For a finite pair `M` and `a ∈ 𝒜`, `0 ≤ a` if and only if `0 ≤ ā` in
   `B(H)`, and likewise for `ℬ`. Hence, in `D(M)`, `0 ≤ x ⟺ 0 ≤ L(x) ⟺ 0 ≤ R(x)`. Also, `𝒩` is
   `StarProper` (the class of `Foundations/BlockOrder.lean:43`) and a `StarModule` (see §4.7 for
   the second).

**Theorem B (the swap facts).** In any `SymModel`, for all `x, y ∈ 𝒩`:
- (F2) `qform(πA x) = qform(πB x)`;
- (F1) `bornProb(x, y) = bornProb(y, x)`;
- (F3) every vendored consistency quantity is symmetric: the match mass, the
  `max(0, total − match)` defect, `bipartiteConsError`, `ConsRel`, `dis` and `inconsistency`;
- (F0) `qform ∘ σ = qform`.

Every swap use in the vendored core is an instance of F1, F2 or F3 at the state `strategy.state`.
This is a type-level fact, established by the audit of §4.4.

**Theorem C (role average).** For `x, y ∈ 𝒩`:
- `⟪Ψ, L(x)R(y)Ψ⟫ = ½(⟪ψ, x̄¹ȳ²ψ⟫ + ⟪ψ, ȳ¹x̄²ψ⟫)`;
- hence `bornProb_D(x, y) = ½(bornProb_M(x¹, y²) + bornProb_M(y¹, x²))`.

The submeasurement defect `max(0, total − match)`, `dis` and `inconsistency` all halve in the same
way, exactly.

**Theorem D (symmetrization, placed after the bridge).** Let `S` be a model two-space `ProjStrat`
in `M`, the model analogue of `LDT/Test/StrategyCore.lean:789-823`. Its fields are:
- point, axis-parallel and diagonal PVM families for each player;
- the four covariance fields;
- the failure surrogate `fail_M`, the model analogue of `lowIndividualDegreeFailureProbability`
  (`LDT/Test/StrategyBiProj/Measurements.lean:479`, decomposed at `:538-544`).

Then:
- `S_D` is a model `SymStrat` of `(D(M), σ)`. Every family of `S_D` is the componentwise pairing
  `⊠` of the A- and B-families, and covariance holds componentwise.
- Its surrogates satisfy:
  - `axis(S_D) = axisParallelRoleAverage(S)`;
  - `selfCons(S_D) = pointAgreement(S)`;
  - `diag(S_D) = diagonalRoleAverage(S)`.
- So `fail_M(S) ≤ ε` implies that `S_D` is `(3ε, 3ε, 3ε)`-good. These are the constants of
  `roleRegisterSymmStrategy_is_good_three_mul`
  (`LDT/Test/StrategyBiProjRoleAverage/Final.lean:147-180`).

**Theorem E (unsymmetrization at the vendored cut).** `mainInduction`
(`LDT/MainInductionStep/Theorems/MainTheorems/Successor.lean:323-338`) returns one POVM `G` on the
symmetric local space. Suppose that `G ∈ 𝒩` and that the D-point inconsistency
`ConsRel_D(P_D, eval G)` is at most `σ`. Then:
- `G¹` is a POVM in `𝒜` and `G²` is a POVM in `ℬ`;
- `ConsRel_M(PA, eval G²) ≤ 2σ` and `ConsRel_M(eval G¹, PB) ≤ 2σ`.

These are the constants of `sourceRoleRegisterPointConsistency_ofSymConsistency`, whose statement
is at `LDT/Test/MainTheorem/SourceRoleRegister/Core.lean:97-121`. The rest of the tail is
two-space, in `M`.

**Theorem F (abelian projections).** For a finite pair `M`:
- `NoAb(opsA M) ∧ NoAb(opsB M)` implies `NoAb(opsA D(M)) ∧ NoAb(opsB D(M))`;
- the converse also holds.

**Theorem G (in-core orthonormalization in `D(M)`, same constant).** Let `M` be a finite pair with
`NoAb(opsA M)` and `NoAb(opsB M)`. Let `X` be a submeasurement in `𝒩` whose bipartite
strong-self-consistency defect in `D(M)` is at most `ζ`, where `ζ > 0`. Then there is a projective
submeasurement `P` in `𝒩` with

  `Σ_a ‖(L X_a − L P_a)Ψ‖² ≤ 100 ζ^{1/4} = orthonormalizationError ζ`

(`LDT/MakingMeasurementsProjective/Defs.lean:289-290`). This is the model form of the vendored
`MakingMeasurementsProjective.orthonormalization`
(`LDT/MakingMeasurementsProjective/Orthonormalization.lean:424-437`). Its only in-core call is at
`LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean:433-436`. There
`ζ = selfImprovementHelperError`, which is positive whenever `1 ≤ params.d`.

The proof uses the tier `povm_orthogonalization_finitePair` (`Ortho/FinitePairOrtho.lean:65-71`)
as a black box. When the derivation was made the tier was an unproved interface. It is now proved:
- the modules are `Ortho/{CenterTrace,CenterTraceClauses,CenterComparison,NoAbelian,FinitePairOrtho}.lean`,
  §2 of this report, T1 of `planning/c6b-plan.md`;
- `#guard_sorry_free` guards it at `MIPRE/Axioms.lean:3328-3329`.

So Theorem G holds unconditionally under its stated hypotheses. Supplying the hypothesis `ζ > 0` at
the call site is an open point (§4.7).

**Proposition H (membership).**
- Ring operations stay in `𝒩` by typing.
- Every continuous functional calculus of a local self-adjoint operator stays in `opsA(D)`, which is
  a commutant.
- Concrete order facts pull back to `𝒩` by Theorem A.4.
- Two external inputs must be supplied in `𝒩`:
  - the semidefinite witness `Z`;
  - the orthonormalized measurement, which Theorem G supplies.

**Remarks (off the route).**
- (R1) For a game that is symmetric under swapping questions and answers,
  `value_D(S.PA ⊠ S.PB) = value_M(S)`. `lidtGame` is such a game.
- (R2) Generic extraction: three D-bounds `≤ δ` give three M-bounds `≤ 2δ`.

Neither remark is needed once the doubling is placed after the bridge and the vendored cut is used.

### 4.3 Proofs

**Lemma 1 (`D(M)` is a bipartite model).** `pairDiag` is a ⋆-algebra hom:
- it is multiplicative by `diagonal_mul_diagonal` and additive by `diagonal_add`;
- it is unital and commutes with `algebraMap`;
- it preserves the star by `diagonal_conjTranspose`.

The maps are then:
- `π_D = toCLMStarAlgHom.comp ((mapMatrixStarAlgHom M.π).comp pairDiag)`
  (`Foundations/OperatorMatrix.lean:116`, `Foundations/AncillaModel.lean:254`);
- `πA_D = (πA ∘ fst).prod (πB ∘ snd)` and `πB_D = (πB ∘ snd).prod (πA ∘ fst)`
  (`Mathlib/Algebra/Star/StarAlgHom.lean:585-597`).

The field `commute` holds by `Prod.ext`:
- the first component is `M.commute x¹ y²`;
- the second is `(M.commute y¹ x²).symm`.

**Lemma 2 (state formula).** `⟪Ψ, π_D(c)Ψ⟫ = ½(⟪ψ, π c₁ ψ⟫ + ⟪ψ, π c₂ ψ⟫)`.

*Proof.* Entry by entry, `π_D(c) = toCLM(diagonal ![π c₁, π c₂])`. Then apply, in order:
- `PiLp.inner_apply` and `Fin.sum_univ_two`;
- `toCLM_diagonal_apply` (`Foundations/OperatorMatrix.lean:67`);
- `inner_smul_left` and `inner_smul_right`;
- `conj(1/√2) · (1/√2) = 1/2`.

With `c = 1` this gives `‖Ψ‖² = ‖ψ‖² = 1`.

In Lean the identity is first stated for `Ampl` and then specialized to the doubled model. In the
prototype, stating it directly on the doubled model's space failed: the inner-product instances
arrive by different paths (`WithCStarModule…toInner` against `PiLp`). The repository uses the same
pattern for `inner_toLp_smul` (`Foundations/AncillaModel.lean:342`, used at `:368`).

**Lemma 3 (flip).** `J` is linear, isometric and involutive, so `J* = J⁻¹ = J`. `JΨ = Ψ` because the
two coordinates of `Ψ` are equal. Moreover:
- `J π_D(c) J (ξ, η) = (π c₂ ξ, π c₁ η) = π_D(σc)(ξ, η)`.
- `σ(πA_D x) = πB_D x` holds definitionally, so `J L(x) J = R(x)`.
- `qform_D(σc) = qform_D(c)` follows from Lemma 2 and `add_comm`.

Hence `(D(M), σ)` is a `SymModel`.

**Lemma 4 (F0–F3 in a `SymModel`).**
- **F2.** `qform(πB x) = qform(σ πA x) = qform(πA x)`.
- **F1.** `σ(πA x · πB y) = πB x · πA y = πA y · πB x`, by `commute`. Hence
  `bornProb(x, y) = bornProb(y, x)`.
- **F3.** Each listed quantity is built from three kinds of term: `bornProb` of outcome pairs,
  `bornProb` of total pairs, and `qform(πA ·)` or `qform(πB ·)`. The definitions are:
  - match mass and defect: `LDT/Test/Defs.lean:192-212`;
  - `bipartiteConsError` and `ConsRel`: `LDT/Test/Defs.lean:215-266`;
  - `dis`: `Foundations/Disagreement.lean:56-57`;
  - `inconsistency`: `Foundations/ModelStrategy.lean:231-232`.

  F1 and F2 swap each term. This mirrors the vendored chain
  `ev_opTensor_swap_of_density_fixed → qBipartiteConsDefect_symm_of_density_fixed →
  consRel_symm_of_density_fixed` (`LDT/Test/StrategyCore.lean:109-157`).
- **F0** is the axiom.

§4.4 proves that every vendored use is one of these.

**Lemma 5 (role average and exact halving).**
`πA_D x · πB_D y = (πA x¹ · πB y², πB x² · πA y¹)`. Lemma 2 and `M.commute y¹ x²` give the
role-average identity of Theorem C. Taking real parts gives the identity for `bornProb`.

*Defect.* For submeasurements `X, Y` in `𝒩`, let:
- `u = bornProb_M(X¹.tot, Y².tot) − Σ_a bornProb_M(X¹_a, Y²_a)`;
- `v = bornProb_M(Y¹.tot, X².tot) − Σ_a bornProb_M(Y¹_a, X²_a)`.

Since `tot = Σ_a` of the outcomes (`LDT/Basic/SubMeasurementCore.lean:37`), we have
`u = Σ_{a≠b} bornProb_M(X¹_a, Y²_b)`. This is `≥ 0` by `bornProb_nonneg`
(`Foundations/POVMValue.lean:184-190`). Likewise `v ≥ 0`. So

  `defect_D = max(0, ½(u + v)) = ½(defect_M(X¹, Y²) + defect_M(Y¹, X²))`.

*`dis` and `inconsistency`.* Using `1 = ½ + ½`:
- `dis_D(P, Q) = ½(dis_M(P¹, Q²) + dis_M(Q¹, P²))`;
- `inconsistency_D(μ, P, Q) = ½(inc_M(μ, P¹, Q²) + inc_M(μ, Q¹, P²))`, after renaming `a ↔ b` in
  the second sum.

*Consistency check.* The identity agrees with the vendored
`ev_roleRegisterSymmState_roleRegisterProjMeas_arbitrary_outcome`
(`LDT/Test/StrategyBiProjUnsymmetrization.lean:603-627`):
- `roleRegisterSymmState` is defined at `LDT/Test/StrategyBiProj/DirectSum.lean:441-458`;
- its blocks `localPairABBlock` and `localPairBABlock` are at `:65-80`;
- `D(M)` corresponds to its two occupied sectors.

This is a sanity check only; nothing rests on it.

**Lemma 6 (injectivity).** `L(a, b) = toCLM(diagonal ![ā, b̄])`. `toCLM` is injective
(`Foundations/AmplCommutant.lean:110`), and `diagonal` is injective in its entries. Then `injA` and
`injB` finish the proof. The same argument works for `R`.

**Lemma 7 (2×2 commutant).**
- If `E` commutes with `diag(1, 0)`, then `E` is diagonal: the `(0,1)` entry gives `E₀₁ = 0`, and
  the `(1,0)` entry gives `E₁₀ = 0`.
- If `E` commutes with `diag(f, g)`, then `E₀₀` commutes with `f` and `E₁₁` commutes with `g`.

**Lemma 8 (commutants).** Let `T` commute with every `R(y)`, and let `E = entries T`. By
`commute_toCLM_iff` (`Foundations/AmplCommutant.lean:114`), `E` commutes with every `diag(ȳ², ȳ¹)`.
- `y = (0, 1)` gives `diag(1, 0)`, so `E` is diagonal (Lemma 7).
- `y = (0, b)` gives `E₀₀ ∈ opsA M`, by `commutantA`.
- `y = (a', 0)` gives `E₁₁ ∈ opsB M`, by `commutantB`.
- So `T = toCLM E = L(a, b)` (`toCLM_entries`, `Foundations/AmplCommutant.lean:92`).

`commutantB` of `D(M)` follows by the mirror argument, with `x = (1, 0)`.

**Lemma 9 (traces).** Let `τ_𝒜 = (g_k)_{k<n}` and `τ_ℬ = (h_l)_{l<n'}` (`VecTrace`,
`Foundations/FinitePair.lean:61-73`). On `opsA D`, take the vectors `emb₀(g_k/√2)` and
`emb₁(h_l/√2)`, indexed by `Fin n ⊕ Fin n'`, through `VecTrace.ofFintype`
(`Foundations/FinitePairExpand.lean:45`).
- **Normalization:** `½ + ½ = 1`.
- **The functional:** `Σ⟪v, L(a, b)v⟫ = ½τ_𝒜(a) + ½τ_ℬ(b)`, by `inner_emb_toCLM_emb`
  (`Foundations/OperatorMatrix.lean:220`).
- **Traciality:** use `L(x)L(y) = L(xy)` and the traciality of `τ_𝒜` and of `τ_ℬ`.
- **Separation:** `L(a, b) emb₀ ξ = emb₀(āξ)` and `L(a, b) emb₁ ξ = emb₁(b̄ξ)`, by
  `toCLM_diagonal_apply` (`Foundations/OperatorMatrix.lean:67`); `toCLM_diagonal_emb` (`:239`) is
  the constant-diagonal case. So if `L(a, b)` vanishes at every vector, then `ā = 0` and `b̄ = 0`,
  by the `separating` field of each trace (`Foundations/FinitePair.lean:73`).

On `opsB D`, swap the roles of the two families.

**Lemma 10 (order agreement; Theorem A.4).**

*(⇐)* Let `T := ā ≥ 0`.
- `T` commutes with every `b̄`, by `M.commute` under `π`.
- So `CFC.sqrt T` commutes with every `b̄` (`Commute.cfcₙ_nnreal`).
- Then `CFC.sqrt T ∈ opsA` by `commutantA`; write `CFC.sqrt T = s̄`.
- `star s = s` by `injA`, since `CFC.sqrt T` is self-adjoint.
- `π πA(star s · s) = CFC.sqrt T · CFC.sqrt T = T`. So `a = star s · s ≥ 0`, by `injA` and
  `star_mul_self_nonneg`.

*(⇒)* `π ∘ πA` is a ⋆-ring hom between star-ordered rings, hence monotone
(`StarRingHomClass.instOrderHomClass`, `Mathlib/Algebra/Order/Star/Basic.lean:460`). In the
repository this is `π_πA_nonneg` (`Foundations/POVMValue.lean:173`).

*For `D(M)`.* There are two routes. One is to apply the lemma to `D(M)`, which is a finite pair by
Lemmas 6–9. The other is to combine `Prod.le_def` with the lemma for `M` in each diagonal block.

*`StarProper 𝒩`.* Suppose `star x * x = 0`. Then `L(star x * x) = L(x)*L(x) = 0`, so `L(x) = 0` by
the C*-identity, and `x = 0` by Lemma 6.

**Lemma 11 (Theorem F, abelian projections).** Let `r ∈ opsA D` be a star projection with
commutative corner. Write `r = L(x) = toCLM(diag(x̄¹, x̄²))`. By `toCLM_injective`
(`Foundations/AmplCommutant.lean:110`), `toCLM_mul` (`Foundations/OperatorMatrix.lean:83`) and
`toCLM_conjTranspose` (`:100`), `x̄¹` is a star projection in `opsA M` and `x̄²` is one in `opsB M`.

Take `y = (a, 0)` and `y' = (a', 0)`:
- `r L(y) r = toCLM(diag(x̄¹ ā x̄¹, 0))`;
- so commutativity of the corner in `D` gives commutativity of the corners of `x̄¹`, for all `ā`
  and `ā'`.

`NoAb(opsA M)` then gives `x̄¹ = 0`. The tests `y = (0, b)` and `y' = (0, b')` give commutativity of
the corners of `x̄²` in the same way, and `NoAb(opsB M)` then gives `x̄² = 0`. So `r = 0`.

For `opsB D = {diag(ȳ², ȳ¹)}`, use `NoAb(opsB M)` in the first block and `NoAb(opsA M)` in the
second. For the converse, embed a projection `p̄` of `opsA M` as `L(p, 0)`, and a projection of
`opsB M` as `L(0, q)`.

Theorem F is applied with the hypothesis imposed on both algebras of `M`. In C6b's class, both
algebras get it from dyadic matrix units (§3, Theorem K). So the fact that having no type I summand
passes to commutants (Kadison–Ringrose 9.1) is not used.

**Lemma 12 (Theorem D, symmetrization after the bridge).**

*The pairing.* `(P ⊠ Q)_a := (P_a, Q_a)`. It inherits the properties of its components:
- positivity holds by `Prod.le_def`;
- the sum is `(1, 1) = 1`;
- idempotence and self-adjointness hold componentwise.

Conversely, the components `fst` and `snd` of a POVM, PVM or submeasurement in `𝒩` are again of
that kind, since `fst` and `snd` are monotone unital ⋆-homs. This needs new code: `POVMIn.map`
(`Foundations/Measurement.lean:298-308`) coarse-grains outcomes and does not transport along a hom.

*The strategy `S_D`.*
- state `Ψ`, with the `SymModel` of Lemma 3 and the normalization of Lemma 2;
- `pointMeasurement u := PA u ⊠ PB u`;
- axis-parallel family `ℓ ↦ axisA ℓ ⊠ axisB ℓ`, and the diagonal family likewise.

*Covariance.* The rebasing statements are fields of `ProjStrat`:
- `AxisParallelMeasurementReparamInvariant` (`LDT/Test/StrategyCore.lean:181-185`);
- its diagonal analogue (`:192-196`).

`SymStrat` bundles the transport-level form instead. That is
`AxisParallelMeasurementTransportInvariant` (`:287-292`, carried by
`AxisParallelCovariantMeasurement` at `:408-413`), with the diagonal analogue at `:297-302`. All of
these are equalities of outcome operators or of measurements. They hold componentwise, so they hold
for `⊠` by `Prod.ext`.

*Branch identities.*
- By Lemma 5, `axis_D = avg ½(defect_M(PA, lineB) + defect_M(lineA, PB))`. This is
  `axisParallelRoleAverage` (`LDT/Test/StrategyBiProj/Measurements.lean:427-431`).
- The diagonal branch gives `diagonalRoleAverage` in the same way (`:465-468`).
- `selfCons_D = bipartiteSSCError_D(P_D) = avg(1 − Σ_a bornProb_M(PA_a, PB_a))`, because the totals
  are `1`. This is `pointAgreementFailureProbability` (`:434-439`).

The `SymStrat` surrogates are those of `LDT/Test/StrategyFailures.lean:36-72`. Then
`fail_M = (axisAvg + point + diagAvg)/3` (`Measurements.lean:538-544`), and all three terms are
nonnegative. So `fail_M ≤ ε` bounds each term by `3ε`.

*Placement.* The port links "passes `lidtGame`" to `fail_M ≤ ε` in `M`. This is the model port of
`failure_le` (`MIPRE/Background/LIDT/Bridge/Value.lean:337`) and of `Bridge.soundness`
(`MIPRE/Background/LIDT/Bridge/Main.lean:96`, consumed as `lowIndividualDegree_soundness` at
`MIPRE/Background/LIDT/Soundness.lean:47-60`). The doubling consumes `fail_M`, not the game value.

**Lemma 13 (Theorem E).** Apply Lemma 5 to `ConsRel_D(P_D, eval G)`, using
`(eval_u G)ⁱ = eval_u Gⁱ`:

  `σ ≥ avg_u ½(defect_M(PA u, eval_u G²) + defect_M(eval_u G¹, PB u))`.

Both terms are nonnegative, so each average is at most `2σ`. `G¹` and `G²` are POVMs by Lemma 12.

From `LDT/Test/MainTheorem/SourceRoleRegister/Core.lean:253` on, the tail never uses symmetry. Its
heterogeneous orthonormalizations run in `M`:
- they are `LDT/MakingMeasurementsProjective/Orthonormalization.lean:246,287`, called at
  `SourceRoleRegister/Core.lean:507,547`;
- they go through `povm_orthogonalization_finitePair` for `M`, and for `M` with the players
  exchanged (`IsFinitePair.swap`, `Foundations/FinitePairExpand.lean:172`).

**Lemma 14 (Theorem G).** Write:
- `b := bornProb_D`;
- `qA(s) := qform_D(πA_D s)`;
- `t := X.tot`;
- `ζ_X := max(0, qA(t) − Σ_a b(X_a, X_a))`.

Then `ζ_X ≤ ζ`, since `ζ_X` is `qBipartiteSSCDefect` (`LDT/Test/Defs.lean:293-299`).

1. **Completion.** Let `X̃` be indexed by `Option Outcome`, with `X̃(some a) = X_a` and
   `X̃(none) = 1 − t`. It is a POVM in `𝒩`: `1 − t ≥ 0` because `t ≤ 1`.
2. **The bipartite defect of `X̃` is at most `2ζ`.**
   - By bilinearity and `b(1, 1) = 1`:
     `1 − Σ_ã b(X̃_ã, X̃_ã) = qA(t) + qform(πB t) − b(t, t) − Σ_a b(X_a, X_a)`.
   - By F2 this equals `2qA(t) − b(t, t) − Σ_a b(X_a, X_a)`.
   - `b(t, t) = Σ_{a,a'} b(X_a, X_{a'}) ≥ Σ_a b(X_a, X_a)`, by `bornProb_nonneg`.
   - So the defect is at most `2ζ_X ≤ 2ζ`.
3. **The one-sided defect is at most the bipartite one.** For self-adjoint `y`:
   - `b(y, y) = Re⟪L(y)Ψ, R(y)Ψ⟫ ≤ ½(‖L(y)Ψ‖² + ‖R(y)Ψ‖²)`;
   - `‖R(y)Ψ‖² = qform(πB y²) = qform(πA y²) = ‖L(y)Ψ‖²`, by F2.

   So `1 − Σ_ã ‖L(X̃_ã)Ψ‖² ≤ 2ζ`.
4. **The tier.** The tier's hypotheses hold for `D(M)`:
   - `D(M)` is a finite pair (Theorem A);
   - `‖Ψ‖ = 1`;
   - `NoAb(opsA D)` holds (Lemma 11).

   Apply `povm_orthogonalization_finitePair` (`Ortho/FinitePairOrtho.lean:65-71`) with `ε := 3ζ`.
   Its strict hypothesis `1 − 3ζ < Σ_ã ‖L(X̃_ã)Ψ‖²` holds, because `1 − Σ ≤ 2ζ < 3ζ` and `ζ > 0`.
   This gives a PVM `Q̃` in `𝒩` with `Σ_ã ‖L(X̃_ã − Q̃_ã)Ψ‖² < 9 · 3ζ = 27ζ`.
5. **Dropping the extra outcome.** Set `P_a := Q̃(some a)`. These are projections, and their total
   is `1 − Q̃(none) ≤ 1`. They are mutually orthogonal: this is the `orthogonal` field of
   `IsPVMIn` (`Foundations/Measurement.lean:41-49`), which the tier returns, so nothing has to be
   pulled back. So `Σ_a ‖L(X_a − P_a)Ψ‖² < 27ζ`.
6. **Comparing constants.**
   - If `0 < ζ ≤ 1`: `27ζ ≤ 27ζ^{1/4} ≤ 100ζ^{1/4}`.
   - If `ζ > 1`: `‖L(X_a − P_a)Ψ‖² ≤ 2‖L(X_a)Ψ‖² + 2‖L(P_a)Ψ‖²`. Here
     `‖L(X_a)Ψ‖² = ⟪Ψ, L(X_a)²Ψ⟫ ≤ ⟪Ψ, L(X_a)Ψ⟫`, since `T² ≤ T` for a positive contraction, and
     these sum to at most `1`. Also `Σ_a ‖L(P_a)Ψ‖² ≤ 1`. So the sum is at most `4 ≤ 100 < 100ζ^{1/4}`.

   The conclusion matches `orthonormalizationError` exactly, so the downstream cascade is unchanged.
   This includes `hprojectiveUpperGap`
   (`LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean:437-440`), which uses only F2
   and F1.
7. **`ζ > 0` at the call site.** The error is
   `selfImprovementHelperError = 100·m·(√eps + √delta + √(d/q))`
   (`LDT/SelfImprovement/Defs.lean:366-372`):
   - `m > 0` and `q > 0` are fields of `Parameters` (`LDT/Basic/ParametersBase.lean:55,58`);
   - `heps` and `hdelta` (nonnegativity) are already in scope at `SelfImprovementTop/Core.lean:432`.

   So `ζ > 0` as soon as `1 ≤ d`. That hypothesis is supplied as follows:
   - `SoundIn` assumes `1 ≤ d` (`MIPRE/Background/LIDT/ModelSoundness.lean:86`);
   - `Parameters.previous` keeps `d` (`LDT/Basic/ParametersBase.lean:138-144`).

   So the ported core carries `1 ≤ params.d` as a hypothesis.

**Lemma 15 (Proposition H, membership).**
- **Ring operations** stay in `𝒩` by typing.
- **Functional calculus.** The local CFC sites are:
  - `LDT/GlobalVariance/Defs/Operators.lean:33-36`, `LDT/GlobalVariance/Defs/Families.lean:40-79`,
    `LDT/GlobalVariance/Theorems/AlgebraicIdentity.lean:81-98`;
  - `LDT/Commutativity/Defs/Stability.lean:102-218`, `LDT/Commutativity/Scaffold/Products.lean:64,99,247`,
    `LDT/Commutativity/GCommStability/Scalar/Common.lean:125-318`;
  - `LDT/Basic/OperatorExpectations.lean:518-548`;
  - `LDT/Pasting/Bernoulli/MatrixChernoff.lean:39-160`.

  At every one of these sites, the CFC of a local self-adjoint `x` commutes with everything that
  commutes with `x`. So it stays in `opsA(D) = opsB(D)′` (Lemma 8). This is the argument of
  `starOrderedRing_centralizer` (`Foundations/BipartiteModel.lean:232-249`). By Lemma 6 the result
  is `L` of a unique element of `𝒩`.

  Order facts proved spectrally pull back to `𝒩` by Lemma 10. An example is `CFC.sqrt G ≤ 1`
  (`cfc_sqrt_outcome_le_one`, `Families.lean:43-54`). Joint operators occur only inside `ev`, as
  `π_D(k)`, and need no membership.
- **CFC in `MakingMeasurementsProjective`.** The CFC there (`SpectralTruncation`, `NaimarkCore`,
  `QXPLayer*`) belongs to the finite-dimensional repair route behind `orthonormalization`:
  `LDT/MakingMeasurementsProjective/Orthonormalization.lean:9` imports `LocalityPreservingRepair`.
  Lemma 14 replaces that route.
- **External inputs.** `Z` must lie in `𝒩`, because F1 is applied to it at
  `LDT/MainInductionStep/Theorems/PastingAssembly/Basic.lean:775`. The orthonormalized measurement
  comes from Lemma 14.

**Remarks (off the route).**
- **(R1)** Suppose `D(x, y, a, b) = D(y, x, b, a)`. Then `condWin_D(x, y) = ½(cw_M(x, y) + cw_M(y, x))`,
  and with `μ` symmetric, `value_D = value_M`. `lidtGame` is symmetric
  (`MIPRE/Background/LIDT/Game.lean:109-201`):
  - the weight does not depend on the swap bit;
  - flipped questions are swapped;
  - `accepts` is mirror-closed.
- **(R2)** For PVMs `Ĝ_L` and `Ĝ_R` in `𝒩`, Lemma 5 halves each of the three inconsistencies. So
  `GA = Ĝ_L¹` and `GB = Ĝ_R²` satisfy each bound with `2δ`. Discharging `SoundIn` this way would
  require the core to deliver `δ/2`. The route of Lemma 13 avoids that.

### 4.4 Audit of the vendored swap-symmetry uses

This subsection proves the type-level claim of Theorem B: every swap use is an instance of F1, F2
or F3 at `strategy.state`.

**The grep.** Search for
`PermInvState|permInvState|densityFixed|density_swap|swap_ev|swapDensity|_of_density_fixed`
over `LDT/`, excluding `LDT/Test/`. It gives 92 lines in 39 files; the search was re-run for this
report. Every swap operand has type `Op ι`, so it is local. The direct uses fall into three
classes.

**F2 (`PermInvState.swap_ev`, `ev(M ⊗ 1) = ev(1 ⊗ M)`), 17 lines:**
- `MakingMeasurementsProjective/Orthonormalization/Completion.lean:101`;
- `Preliminaries/BipartiteSelfConsistency/Core.lean:91,261`;
- `Preliminaries/BipartiteSelfConsistency/Local.lean:161`;
- `Preliminaries/SelfConsistency/DataProcessing.lean:122`;
- `Commutativity/ScalarApproximation/Core.lean:188`;
- `Commutativity/ScalarApproximation/Pointwise.lean:541`;
- `Pasting/Bernoulli/DegreeZero.lean:729,881`;
- `Pasting/Bernoulli/Final.lean:225`;
- `Pasting/ComparisonLemmas/HAConsistency.lean:506`;
- `SelfImprovement/Theorems/Results/BoundednessTransport/BoundednessGap.lean:216`;
- `SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean:473,474,515,516`;
- `SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean:419`.

The other three `swap_ev` matches are in comments.

**F1 (`ev_opTensor_swap_of_density_fixed`, `ev(X ⊗ Y) = ev(Y ⊗ X)`), 3 sites:**
- `MainInductionStep/Theorems/PastingAssembly/Basic.lean:775`, on `family.witness x`, the
  semidefinite witness `Z`;
- `Pasting/SwitcherooCompletion.lean:68`;
- `SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean:388`.

**F3 (`consRel_symm_of_density_fixed`), 7 sites:**
- `GlobalVariance/Theorems/SelfConsistencyTransportSum.lean:162`;
- `GlobalVariance/Theorems/SelfConsistencyTransport/PointLine.lean:143`;
- `Commutativity/Scaffold/Symmetry.lean:73`;
- `Pasting/Bernoulli/DegreeZero.lean:413,656`;
- `Pasting/ComparisonLemmas/HAConsistency.lean:216`;
- `Pasting/Core/LdGbcon.lean:469`.

**Pass-through lemmas.** These take the symmetry as a hypothesis and reduce to F2, or to F1 through
`hfix`. There are 23 such hypotheses: 22 binders and one premise of an implication.
- 21 `PermInvState` hypotheses:
  - `MakingMeasurementsProjective/ProjectivizationChain/Basic.lean:163,177`;
  - `MakingMeasurementsProjective/Orthonormalization.lean:339,428`;
  - `MakingMeasurementsProjective/Orthonormalization/Completion.lean:47`;
  - `Preliminaries/BipartiteSelfConsistency/Core.lean:62,98,310` (the last is the premise of an
    implication);
  - `Preliminaries/BipartiteSelfConsistency/Local.lean:53`;
  - `Preliminaries/CompletionTransfer.lean:180,252`;
  - `Preliminaries/SelfConsistency/DataProcessing.lean:56,297`;
  - `Preliminaries/SelfConsistency/Core.lean:52,91`;
  - `Preliminaries/SelfConsistency/Extensions.lean:102,208`;
  - `Commutativity/ScalarApproximation/Core.lean:45`;
  - `Pasting/Core/CompletePart.lean:315,333,438`; the first two (`_hperm`) are unused;
- the two `hfix` binders of `Pasting/SwitcherooCompletion.lean:39,90`.

**F0 in general.** The general form, `ev(swapDensity Z) = ev Z`
(`ev_swapDensity_of_density_fixed`, `LDT/Test/StrategyCore.lean:94`), is reached only through
`ev_opTensor_swap_of_density_fixed`, which is F1. Outside `LDT/Test/`, `swapDensity` occurs only in
the two `hfix` binders.

**Which state.** Outside `LDT/Test/`, the symmetry terms are:
- `strategy.permInvState`, 39 occurrences;
- `strategy.densityFixed`, 14 occurrences.

These counts include three structural copies, each of which sets `state := strategy.state`:
- `MainInductionStep/Defs.lean:352-354`;
- `MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean:72-74`;
- `MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean:164-166`.

`PermInvState ψ` (`LDT/Test/StrategyCore.lean:168`) is a predicate on `ψ`. So every swap lemma that
consumes one of these terms is applied at `strategy.state`.

The point-conditioned state of `weightedPolynomialState_ev_leftTensor`
(`GlobalVariance/Theorems/AlgebraicIdentity.lean:247`) is not a new state. The lemma is the
operator identity `Wᴴ L W = opTensor X G_g`, evaluated in that same state. Its model form is
`⟪Ψ, R(√G)L(X)R(√G)Ψ⟫ = ⟪Ψ, L(X)R(G)Ψ⟫`, which holds by `commute`, with `√G ∈ 𝒩` by Proposition H.
So no swap fact is ever needed at a state that `J` does not fix.

**Conclusion.** The doubled model supplies F0–F3 at its one state, for all local operands. The port
retargets the 27 direct uses (17 + 3 + 7) and the 23 hypotheses to `SymModel` lemmas, one call per
site.

### 4.5 Constants

| step | vendored constant | doubling |
|---|---|---|
| goodness of the symmetric strategy (Theorem D) | `(3ε, 3ε, 3ε)`, `roleRegisterSymmStrategy_is_good_three_mul` | `(3ε, 3ε, 3ε)` |
| unsymmetrization (Theorem E) | `2σ`, `sourceRoleRegisterPointConsistency_ofSymConsistency` | `2σ` |
| in-core orthonormalization (Theorem G) | `orthonormalizationError ζ = 100ζ^{1/4}` | `27ζ`, bounded by `100ζ^{1/4}` for `ζ > 0` |

So the doubling leaves `mainFormalError` and `deltaSim` unchanged.

### 4.6 What has been prototyped in Lean

The following were prototyped in Lean (not committed) against `MIPRE.Foundations.FinitePairExpand`
on Lean 4.35. During the design they compiled with no errors:
- `pairDiag` and the doubled model `double`, with `commute` (Lemma 1);
- the state formula for `Ampl`, its instance on the doubled model, and the formula
  `π_D(c) = toCLM(diagonal ![π c₁, π c₂])` (Lemma 2);
- `σ(πA_D x) = πB_D x`, by `rfl`, and the flip invariance of the state functional (Lemma 3);
- the role-average identity (Lemma 5);
- the order-agreement lemma, `0 ≤ π(πA a) → 0 ≤ a` in a finite pair, in about 20 lines, with its
  converse from `π_πA_nonneg` (Lemma 10);
- instance synthesis of `StarOrderedRing (𝒜 × ℬ)`.

`commutantA` of `D(M)` (Lemma 8) was prototyped in an earlier design round, in 52 lines with
helpers, and was not re-run. Everything else in §4.3 exists on paper only (§4.7). For this report,
two product instances were synthesized again against the same module:
- `StarOrderedRing (𝒜 × ℬ)`;
- `StarModule ℂ (𝒜 × ℬ)`, given `StarModule ℂ` on both factors.

Work package M2 is estimated at 0.95–1.45k new lines. The estimate is calibrated on about 90
prototype lines and on `Foundations/FinitePairExpand.lean`, which has 275 lines; one trace
construction there, `VecTrace.ampl` (`:106-135`), is a comparable piece. The estimate excludes the
port-base containers and the model bridge.

### 4.7 Status and open points

**Resolved since the design.** The orthonormalization tier that Theorem G calls,
`povm_orthogonalization_finitePair`, is proved and guarded (`MIPRE/Axioms.lean:3328-3329`). It
goes through `povm_orthogonalization_vecTrace` (`Ortho/NoAbelian.lean:99-105`) and the
centre-valued trace `exists_isCenterValuedTrace` (`Ortho/CenterComparison.lean:355`). The doubling
reduces in-core orthonormalization to that one interface, which T1 of `planning/c6b-plan.md`
provides.

**Open.**
- **`ζ = 0`.** Theorem G needs `ζ > 0`, because the tier's hypothesis is strict. The case `ζ = 0`
  is not proved. Positivity at the call site needs `1 ≤ params.d` to be threaded from `SoundIn` to
  the core's `Parameters`, through the `clGame` → `lidtGame` adapters
  `MIPRE/Background/LIDT/Padding.lean` and `MIPRE/Background/LIDT/Adapter/Reduction.lean` (audit
  §3.1). That threading has not been traced. Inside the induction, `d` is preserved
  (`LDT/Basic/ParametersBase.lean:138-144`).
- **The two-space tail.** Its heterogeneous orthonormalizations
  (`LDT/MakingMeasurementsProjective/Orthonormalization.lean:246,287`) run in `M`. They need the
  same handling of the strict hypothesis, and the positivity of their `ζ` has not been checked. This
  is outside the doubling but on the route.
- **The semidefinite witness `Z ∈ 𝒩`.** It is needed because F1 is applied to `family.witness x`
  at `LDT/MainInductionStep/Theorems/PastingAssembly/Basic.lean:775` (audit §4.2; §5 of this
  report).
- **The port base.** These items are not part of the doubling and not in the estimate of §4.6:
  - the model containers: `ProjStrat`, `SymStrat`, `SubMeas`, `ConsRel` and the surrogates;
  - the model bridge: the port of `Bridge.soundness` (`MIPRE/Background/LIDT/Bridge/Main.lean:96`,
    about 1,471 matrix lines, audit §3.1) and of `failure_le`
    (`MIPRE/Background/LIDT/Bridge/Value.lean:337`);
  - CFC transport onto the abstract `𝒩`.
- **Not yet compiled:**
  - the `VecTrace`s of `D(M)` (Lemma 9);
  - `commutantB` of `D(M)`;
  - the `NoAb` closure (Lemma 11);
  - the covariance of `⊠`;
  - Lemmas 12–14.

  The covariance predicates were read for this report. They are equalities of outcome operators or
  of measurements (§4.3, Lemma 12). The componentwise argument has not been written in Lean.
- **`StarModule ℂ 𝒩`.** It follows from Mathlib's product instance
  (`Mathlib/Algebra/Star/Prod.lean:46-48`) once `𝒜` and `ℬ` are `StarModule ℂ`, and that inference
  has been checked. The factor instances are not available, though. `SoundFin`
  (`MIPRE/Background/LIDT/FinModel.lean:40-43`) does not assume them, unlike
  `CommutingFinitePairApprox` (`Foundations/FinitePair.lean:117`). They must be either added as
  hypotheses or derived, for instance from `injA` and `injB`; neither option has been checked.
- **CFC classification.** `LDT/MakingMeasurementsProjective/ProjectivizationChain/Basic.lean:11`
  imports `QXPLayerIdentities.ProjectorApprox`. Whether that module applies CFC to retained operands
  has not been checked. The centralizer argument of Lemma 15 covers any local use regardless.

## 5. The summed semidefinite form on a finite pair

This section proves that each player's algebra in a finite pair contains a measurement `T` such
that `Z := Σ_g T_g A_g` is self-adjoint, `A_g ≤ Z` for all `g`, and `T_g Z = T_g A_g` for all `g`
(Theorem 10). That is exactly the data of the vendored `SdpStatementWithSlackness`. So Theorem 10
replaces JNVWY Lemma 9.2 and its finite-dimensional strong duality (audit §4.2). In C6b it is item
M9 of `planning/c6b-plan.md`. The program is solved componentwise in the doubled model
(Corollary 12), and the solution is pulled back to the abstract algebras (Lemma 13). The
approximate forms analysed in §5.7 were not chosen.

The proof uses only the trace and the weak-operator compactness of norm balls, which is already
vendored. It needs no σ-weak topology, no normal-trace API and no predual.

### 5.1 Setting

**Setting (S).**

- `H` is a complex Hilbert space, and `t ⊆ B(H)` is any set.
- `M := {x ∈ B(H) : xy = yx and xy* = y*x for all y ∈ t}` is the commutant of `t ∪ t*`. In Lean
  it is `StarSubalgebra.centralizer ℂ t`, a unital ⋆-subalgebra whether or not `t` is
  star-closed.
- Fix `g_1, …, g_n ∈ H`. Put `τ(x) := Σ_k ⟪g_k, x g_k⟫`, a linear functional on all of `B(H)`,
  and `ρ := Re ∘ τ`.
- **(Tr)** `τ(xy) = τ(yx)` for `x, y ∈ M`.
- **(F)** If `x ∈ M` and `x g_k = 0` for every `k`, then `x = 0`.
- Only Propositions 14 and 15 use the normalization `Σ_k ‖g_k‖² = 1`.
- `G` is a finite nonempty set, and each `A_g` (`g ∈ G`) is a self-adjoint element of `M`. The
  proof never uses positivity of `A_g`.
- `𝒯 := {(T_g)_{g∈G} : T_g ∈ M, T_g ≥ 0, Σ_g T_g = 1}`, and `f(T) := Σ_g ρ(T_g A_g)`.
- `≤` is the operator order of `B(H)`.

**Finite pairs satisfy (S), on both sides.** Let `M` be a finite pair
(`MIPRE/Foundations/FinitePair.lean:92-104`).

- Take `t := opsB` (`FinitePair.lean:85-86`). `opsB` is star-closed, because it is the range of
  the ⋆-homomorphism `π ∘ πB` (`MIPRE/Foundations/BipartiteModel.lean:63`,
  `MIPRE/Foundations/StateModel.lean:55`).
- So `StarSubalgebra.centralizer ℂ opsB = opsA` as sets. The inclusion `⊆` is `commutantA`
  (`FinitePair.lean:98`), and `⊇` is `commute` (`BipartiteModel.lean:65`). This equality is
  proved as `mem_vnA_iff` (`MIPRE/Background/Orthonormalization/FinitePairOrtho.lean:51-59`).
  There `vnA` (`:41-46`) is the first player's algebra as a Mathlib `VonNeumannAlgebra`.
- (Tr) and (F) are the fields `trace_mul_comm` and `separating` (`FinitePair.lean:70-73`) of
  `traceA` (`:102`).
- Symmetrically, `t := opsA` gives `M = opsB`, using `commutantB` (`:100`) and `traceB` (`:104`).
  Alternatively, apply the first player's result to `M.swap` (`IsFinitePair.swap`,
  `MIPRE/Foundations/FinitePairExpand.lean:172`).
- The II₁ tier changes nothing here. Theorem 10 needs only (S), so it applies to any amplified
  pair that is again a finite pair. The docstring at `FinitePair.lean:41-46` says that
  amplification by a II₁ factor stays in the class, but no lemma in the repository proves this.

### 5.2 What the consumers use (Lemma 0)

**Lemma 0 (consumer inventory).** The vendored consumers of the semidefinite program use:

- a measurement `T` with `T.total = 1`;
- `Z ≥ A_g` for all `g`, as an exact operator inequality, and `Z ≥ 0`, which follows from it
  because each `A_g ≥ 0`;
- slackness only through `Σ_h T_h A_h = Z`, that is, `Σ_h T_h(A_h − Z) = 0`. The operators sit on
  the left factor (`leftTensor`) or on the right factor (`opTensor X ·`, `rightTensor`), and they
  are evaluated in the strategy's arbitrary state `ψ`.

So the pair `(T, Z)` must lie in the symmetric model's local algebra (Corollary 12). The evidence
follows. All paths in this subsection are under `MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/`,
and `R/` abbreviates `Theorems/Results/`.

**The interface.**

- `SdpStatementWithSlackness` (`Theorems/Statements.lean:112-116`) holds a `T : Measurement` and a
  `Z` that satisfy `SdpOptimalPairWithSlackness` (`:87-94`). Its fields are:
  - `T.total = 1` (`primalTotalOperator`, `:57-58`);
  - `0 ≤ Z − A_g` for all `g` (`dualFeasible`, `:59-61`, through `sdpDualSlackOperator`,
    `Defs.lean:182-187`);
  - `T_g Z = T_g A_g` for all `g` (`complementarySlackness`, `:92-94`, through
    `sdpComplementarySlacknessEquation`, `Defs.lean:208-215`).
- Here `A_g` is `averagedPointOperator` (`Defs.lean:138-143`), which is positive
  (`Defs.lean:145-153`).
- The docstring of `SdpOptimalPair` (`Statements.lean:42-53`) says that no optimality is
  recorded.
- `Z ≥ 0` follows from dual feasibility (`sdpDualPositive_of_dualFeasible`, `Defs.lean:189-206`).
- The only producer is `sdp_statement_with_slackness`
  (`R/HelperCompleteness/Bracketed.lean:520-526`), through `R/SdpMatrixBridge.lean:239-248`. It is
  called at `R/SelfImprovementTop/Core.lean:112-114` and at `Bracketed.lean:537-547`. The
  hypothesis is unpacked in `Core.lean:66-94`, which supplies the slackness field at `:93-94`.

**Base uses of slackness.** Search `LDT/`, excluding `MatrixRealization`, for
`complementarySlackness`, `hslack` and `sdpComplementarySlacknessEquation`. Slackness is actually
used in exactly two places:

- **(a)** `R/HelperCompleteness/InputSdp.lean:297-336` proves
  `Σ_h ev(leftTensor(T_h A_h)) = ev(leftTensor Z)`. It rewrites `T_h A_h ↦ T_h Z` and then
  collapses the sum with `Σ_h T_h = 1` (`T.total`). Here `Z` is on the **left** factor.
- **(c)** `R/HelperSSC/Assembly.lean:137` (hypothesis `hslack`, `:145-148`). At `:291` it rewrites
  `T_h A_h ↦ T_h Z` inside `Σ_{h'} Σ_h ev(opTensor (Hu u h') ·)`, and at `:292-299` it collapses
  `Σ_h T_h Z = Z`. Here `Z` is on the **right** factor and is tested against `X = Hu(u,h') ≥ 0`.

**Pass-through sites.** Every other site takes the per-`h` hypothesis and forwards it, and the
chain ends at (a) or (c). At each site only the forwarding call was checked, not the full proof:

- `R/HelperCompleteness/Linearized.lean:59-163` (b), which reduces to (a), and also `:167-182`,
  `:186-204`, `:374-394` and `:487-501`;
- `Bracketed.lean:292-355`, `:365-451` (call at `:396-398`), `:459-475` and `:484-506`
  (forwarding at `:505`);
- `R/BoundednessTransport/BoundednessGap.lean:198-261` and `:561-585`. The `hslack` at `:64-75`
  is unrelated: it is the local result of
  `helper_boundedness_slack_average_ev_eq_off_diagonal_avg`;
- `Assembly.lean:681-713`;
- `R/SelfImprovementTop/Core.lean:260`, `:415-426` and `:591`;
- `R/SelfImprovementTop/FinalFields.lean:71-128`.

**What slackness is used for.** Every use is summed over `h` and needs exactly
`Σ_h T_h A_h = Z`. Given `Σ_h T_h = 1`, the identity `Σ_h T_h Z = Z` holds for every `Z`, so it is
*not* equivalent to slackness. What the consumers use is the composite rewrite.

**Dual feasibility** is used as an exact operator inequality:

- in `sdp_overlap_le_dual_mass` (`R/HelperCompleteness/InputSdp.lean:216`, used at `:259-287`);
- in `sliceDominatesAveragedPoint`, together with the slice witness `Z^x` on the right factor
  (`LDT/Test/StrategyPolynomialFamilies.lean:257-273`, where `rightTensor (family.witness x)` is
  at `:269`). One consumer, for example, is
  `LDT/Commutativity/GCommStability/Scalar/RawSecond.lean:409-427`.

**Conclusion.** The vendored strategy is symmetric, so one pair `(T, Z)` is placed on **both**
tensor factors. In the port, `(T, Z)` must therefore lie in the symmetric model's local algebra.
In the doubled model (`reports/lidt-co-audit.md:392-402`, §4.1) that algebra is `𝒜 × ℬ`, written
`𝒜 ⊕ ℬ` there. It is placed by `L(a,b) = a ⊕ b` and `R(a,b) = b ⊕ a`. Corollary 12 supplies such
a pair. Theorem 10 supplies the per-`g` fields exactly, so no consumer needs to change.

### 5.3 The theorem

**Theorem 10 (summed semidefinite form; replaces JNVWY Lemma 9.2).** In (S) there is `T ∈ 𝒯` such
that `Z := Σ_g T_g A_g` satisfies:

- (i) `Z ∈ M` and `Z = Z*`;
- (ii) `A_h ≤ Z` for all `h`;
- (iii) `T_h Z = T_h A_h` for all `h`.

Any maximizer of `f` on `𝒯` works (Lemmas 7′–9), and one exists (Lemma 4). More generally,
(i)–(iii) hold for every `T ∈ 𝒯` that satisfies the first-order condition

> `FO(T, A)`: `ρ(P A_h) ≤ ρ(P Z)` for all `h` and all `P ∈ M` with `0 ≤ P ≤ 1`.

**Corollary 11 (interface).** Restated over `M`, (i)–(iii) are, field for field, the data of the
vendored `SdpOptimalPairWithSlackness` and `SdpStatementWithSlackness`
(`Theorems/Statements.lean:87-94`, `:112-116`):

- `primalTotalOperator`: `T.total = 1` (`:57-58`);
- `dualFeasible`: `0 ≤ Z − A_g` (`:59-61`, `Defs.lean:182-187`);
- `complementarySlackness`: `T_g Z = T_g A_g` (`:92-94`, `Defs.lean:208-215`).

Conversely, in (S), (i) and (ii) imply (iii). This is Lemma 9 in the case `W = Z`.

### 5.4 Proof of Theorem 10

**Lemma 1 (algebra of `M`).**
(a) `M` is a unital ⋆-subalgebra of `B(H)`.
(b) For `x ∈ M` and continuous real `f`, `cfcₙ f x ∈ M`. In particular `x⁺, x⁻ ∈ M`, and
`√x ∈ M` when `x ≥ 0`.

*Proof.*

- (a) If `x` commutes with `y` and `y*`, then taking adjoints shows that `x*` commutes with `y*`
  and `y`. Closure under sums and products is clear.
- (b) For `y ∈ t`, both `y` and `y*` commute with `x`. Anything that commutes with `x` also
  commutes with `cfcₙ f x`, by `Commute.cfcₙ_real` and `Commute.cfcₙ_nnreal`
  (`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean:188`, `:200`).
  `CFC.sqrt` is `cfcₙ NNReal.sqrt`
  (`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:235`). ∎

**Lemma 2 (trace facts).** For all `x ∈ B(H)`:

- `τ(x*) = Σ_k ⟪g_k, x* g_k⟫ = Σ_k ⟪x g_k, g_k⟫ = conj τ(x)`, hence `ρ(x*) = ρ(x)`;
- `ρ(x* x) = Σ_k ‖x g_k‖² ≥ 0`;
- if `x ∈ M` and `ρ(x* x) ≤ 0`, then every `x g_k = 0`, so `x = 0` by (F). ∎

**Lemma 3 (positivity of the pairing).** Let `T, D ∈ M` with `T, D ≥ 0`. Then `ρ(TD) ≥ 0`, and
`ρ(TD) ≤ 0` implies `DT = 0`.

*Proof.*

1. Let `s := √T` and `r := √D`. Both lie in `M` (Lemma 1b) and are self-adjoint.
2. By (Tr) with `x = s` and `y = s r r`: `τ(TD) = τ(s · (s r r)) = τ(s r r s) = τ((rs)*(rs))`.
3. By Lemma 2 this equals `Σ_k ‖rs g_k‖² ≥ 0`.
4. If it is `≤ 0`, then `rs = 0` (Lemma 2, since `rs ∈ M`). Hence `DT = r(rs)s = 0`. ∎

**Lemma 4 (a maximizer exists, by weak-operator compactness).** Work in `G → (H →WOT[ℂ] H)` with
the product of the weak operator topologies. The vendored lemmas cited below are in
`MIPRE/Background/Orthonormalization/Orthogonalization/MvN/WOTCompact.lean`.

1. **The set.** `𝒯` corresponds to the set `S` of all `T` such that:
   - for all `g` and all `y ∈ t`, `toCLM(T_g)` commutes with `y` and with `y*`;
   - for all `g`, `0 ≤ toCLM(T_g)`;
   - for all `ξ, η`, `Σ_g ⟪ξ, T_g η⟫ = ⟪ξ, η⟫`.

   By `ext_inner_left`, the last condition says `Σ_g T_g = 1`.
2. **Closed.** `S` is an *intersection* of closed sets. Because `t` may be infinite, the
   intersection need not be finite, but any intersection of closed sets is closed
   (`isClosed_iInter`, `isClosed_biInter`, `Mathlib/Topology/Basic.lean:159`, `:162`). The sets
   are:
   - commutation with each `y` and each `y*`: `Orthogonalization.MvN.isClosed_setOf_commute`
     (`WOTCompact.lean:281`), composed with `continuous_apply g`;
   - positivity: `isClosed_setOf_nonneg` (`:226`);
   - each sum identity: `isClosed_eq`, applied to a finite sum of the WOT-continuous coefficients
     `continuous_inner_apply` (`:61`).
3. **Bounded.** For `T ∈ S`, `0 ≤ T_g ≤ Σ_g T_g = 1` (`Finset.single_le_sum`), so `‖T_g‖ ≤ 1`
   (`CStarAlgebra.norm_le_one_iff_of_nonneg`,
   `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:247`).
4. **Compact.** `S` lies in `Π_g {‖·‖ ≤ 1}`, which is compact by `isCompact_setOf_norm_le`
   (`WOTCompact.lean:114`) and `isCompact_univ_pi`. Hence `S` is compact
   (`IsCompact.of_isClosed_subset`).
5. **Nonempty.** Fix `g₀ ∈ G`. The tuple with `T_{g₀} = 1` and `T_g = 0` for `g ≠ g₀` lies in `S`.
6. **Continuous objective.** `f(T) = Σ_g Re Σ_k ⟪g_k, T_g(A_g g_k)⟫` is a finite sum of WOT matrix
   coefficients, so it is continuous.
7. `IsCompact.exists_isMaxOn` gives a maximizer. ∎

A finite sum of vector functionals is already WOT-continuous. So the proof uses no σ-weak
topology, no normality and no predual.

*Placement.* Lemma 4 uses the vendored namespace `Orthogonalization.MvN`, and
`WOTCompact.lean:42` does `public import Mathlib`. Under the repository's rule (nothing outside
`MIPRE/Background/` may name a vendored namespace), Lemma 4 must live under `MIPRE/Background/`.

- `MIPRE/Background/Orthonormalization/Statement.lean:7` already imports that tree.
- `MIPRE/Background/Orthonormalization/CenterTrace.lean:8` imports `MvN.WOTCompact` itself. At
  `CenterTrace.lean:335-339` it makes an argument of the same shape, using
  `isCompact_setOf_norm_le` and `isCompact_of_isClosed_of_norm_le` (`WOTCompact.lean:193`).
- The core chain (Lemmas 1–3 and 5–9, and Theorem 10 given a maximizer) does not need the vendored
  tree. It can stay in `MIPRE/Foundations` and take the maximizer as a hypothesis, so that only
  Lemma 4 lives under `MIPRE/Background`.
- Alternatively, norm-ball compactness could be re-proved locally in about 80 lines (compare
  `WOTCompact.lean:114-190`). Lemma 4 could then live in `MIPRE/Foundations` too.
- Mathlib has WOT continuity of matrix coefficients
  (`ContinuousLinearMapWOT.continuous_inner_apply`,
  `Mathlib/Analysis/InnerProductSpace/WeakOperatorTopology.lean:80`), but it does not have
  compactness of norm balls.

**Lemma 5 (the perturbed measurement).** Let `T ∈ 𝒯`, `h ∈ G`, `P ∈ M` with `0 ≤ P ≤ 1`, and
`0 ≤ ε ≤ 1`. Put `K := 1 − εP` and `T'_g := K T_g K + δ_{gh}(1 − K²)`. Then `T' ∈ 𝒯`.

*Proof.*

- **Membership.** `K ∈ M`, so `T'_g ∈ M` (Lemma 1a).
- **`K = K*`**, because `P = P*` and `ε` is real.
- **`K ≥ 0`**, because `εP ≤ ε · 1 ≤ 1`.
- **First term.** `K T_g K = K* T_g K ≥ 0`.
- **Second term.** Let `p := √P ∈ M`, so that `pp = P`. Then `1 − K² = εP + ε(p* K p)`, since
  both sides equal `2εP − ε²P²`. Both summands are `≥ 0`.
- **Sum.** `Σ_g T'_g = K(Σ_g T_g)K + 1 − K² = 1`. ∎

**Lemma 6 (exact expansion).** Let `T_g`, `A_g` and `P` be self-adjoint elements of `M` with
`T_g ≥ 0`, and let `Z := Σ_g T_g A_g`. Define `T'` as in Lemma 5. Then for every real `ε`,

> `f(T') = f(T) + 2ε[ρ(P A_h) − ρ(P Z)] + ε² c`, where `c := Σ_g ρ(P T_g P A_g) − ρ(P² A_h)`.

*Proof.*

1. **Expand.** `K T_g K A_g = T_g A_g − ε(P T_g A_g + T_g P A_g) + ε² P T_g P A_g`, and
   `(1 − K²) A_h = 2ε P A_h − ε² P² A_h`. Apply `ρ`.
2. **Swap.** `ρ(T_g P A_g) = ρ((A_g · P T_g)*) = ρ(A_g · P T_g) = ρ(P T_g · A_g)`. The middle
   step is Lemma 2, and the last is (Tr) with `x = A_g` and `y = P T_g ∈ M`.
3. Hence `Σ_g [ρ(P T_g A_g) + ρ(T_g P A_g)] = 2ρ(P Z)`. ∎

**Lemma 7 (a quadratic first-order lemma).** Let `a, C ∈ ℝ` and `q : ℝ → ℝ` with `|q(ε)| ≤ Cε²`
for `ε ∈ [0,1]`. If `2εa + q(ε) ≤ 0` for all `ε ∈ [0,1]`, then `a ≤ 0`.

*Proof.*

1. Taking `ε = 1` gives `C ≥ |q(1)| ≥ 0`.
2. Suppose `a > 0`, and put `ε := min(1, a/(C+1)) ∈ (0,1]`. Then `εC ≤ a`.
3. So `2εa + q(ε) ≥ 2εa − Cε² = ε(2a − εC) ≥ εa > 0`, a contradiction. ∎

**Lemma 7′ (a maximizer satisfies FO).** If `T` maximizes `f` on `𝒯`, then `FO(T, A)` holds.

*Proof.* Fix `h` and `P ∈ M` with `0 ≤ P ≤ 1`. For `ε ∈ [0,1]` we have `T' ∈ 𝒯` (Lemma 5), so
`f(T') ≤ f(T)`. By Lemma 6 this reads `2εa + ε²c ≤ 0`, with `a = ρ(P A_h) − ρ(P Z)`. Apply
Lemma 7 with `q(ε) = ε²c` and `C = |c|`. ∎

**Lemma 8 (domination by `W`).** Let `T ∈ 𝒯` satisfy `FO(T, A)`, and put `W := (Z + Z*)/2`. Then
`W ∈ M`, `W = W*`, and `A_h ≤ W` for every `h`.

*Proof.*

1. **`ρ(PW) = ρ(PZ)` for self-adjoint `P ∈ M`.** By Lemma 2 and then (Tr),
   `ρ(P Z*) = ρ((Z P)*) = ρ(Z P) = ρ(P Z)`.
2. **Setup.** `Y := W − A_h` is self-adjoint and lies in `M`. Then `N := Y⁻ ∈ M` (Lemma 1b) and
   `N ≥ 0`. Let `P := (1 + ‖N‖)⁻¹ N`. Then `0 ≤ P` and `‖P‖ ≤ 1`, so `P ≤ 1`.
3. **Apply FO.** With step 1, `0 ≤ ρ(PY) = (1 + ‖N‖)⁻¹ ρ(NY)`.
4. **Compute `NY`.** `NY = N(Y⁺ − Y⁻) = −N²`, by `CFC.negPart_mul_posPart` and
   `CFC.posPart_sub_negPart`
   (`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/PosPart/Basic.lean:68`,
   `:77`).
5. **Conclude.** So `ρ(N* N) ≤ 0`, hence `N = 0` (Lemma 2), and `Y = Y⁺ ≥ 0`. ∎

**Lemma 9 (slackness and self-adjointness).** Under the hypotheses of Lemma 8, `Z = W`. Hence
`Z = Z*`, `A_h ≤ Z`, and `T_h Z = T_h A_h`.

*Proof.*

1. **The slacks.** `D_h := W − A_h ≥ 0` and `D_h ∈ M`.
2. **The sum vanishes.** Since `ρ(Z*) = ρ(Z)`,
   `Σ_h ρ(T_h D_h) = ρ((Σ_h T_h) W) − Σ_h ρ(T_h A_h) = ρ(W) − ρ(Z) = 0`.
3. **Each slack annihilates `T_h`.** Each term is `≥ 0` (Lemma 3), so each is `0`. Lemma 3 then
   gives `D_h T_h = 0`, that is, `W T_h = A_h T_h`.
4. **`W = Z*`.** `W = W Σ_h T_h = Σ_h A_h T_h = (Σ_h T_h A_h)* = Z*`.
5. **Conclude.** `Z = (Z*)* = W* = W`, and `T_h Z = (W T_h)* = (A_h T_h)* = T_h A_h`.

*Converse in Corollary 11.* If (i) and (ii) hold, then `W = Z`. Steps 1–3 use only
`Σ_h T_h = 1`, Lemma 3 and `Z ≥ A_h`, and they give `Z T_h = A_h T_h`. Taking adjoints yields
(iii). ∎

**Proof of Theorem 10.** Lemma 4 gives a maximizer and Lemma 7′ gives `FO(T, A)`. Lemmas 8 and 9
then give (i)–(iii). Corollary 11 is the field-by-field match in §5.3. ∎

### 5.5 The doubled model (Corollary 12)

**Corollary 12 (the symmetric model's local algebra).** By Lemma 0, the consumers place one
`(T, Z)` on both tensor factors. In the doubled model of `reports/lidt-co-audit.md:392-402`, the
local algebra is `𝒜 × ℬ`, placed as `L(a,b) = a ⊕ b` and `R(a,b) = b ⊕ a`.

Suppose `A_g = (A_g^A, A_g^B)`, where `A_g^A ∈ opsA` and `A_g^B ∈ opsB` are self-adjoint. Take
`(T^A, Z^A)` from Theorem 10 in `opsA` and `(T^B, Z^B)` from Theorem 10 in `opsB`. Then
`T_g := (T^A_g, T^B_g)` and `Z := (Z^A, Z^B)` satisfy (i)–(iii) in `𝒜 × ℬ`, and so do their
images under `L` and under `R`.

The corollary needs neither (S) for the doubled algebra nor a doubled trace. (S) for the doubled
algebra does hold, by an elementary argument (Remark 12′), but it is not used.

*Proof.*

1. **Setting.** By (S) on each side (§5.1), Theorem 10 applies in `opsA` with `t = opsB`, and in
   `opsB` with `t = opsA`.
2. **Componentwise data.** In `𝒜 × ℬ`, the operations and the order are componentwise. Mathlib's
   `Prod.instStarOrderedRing` (`Mathlib/Algebra/Order/Star/Prod.lean:21-24`) gives the
   star-ordered structure with the componentwise order. Under `L(a,b) = a ⊕ b` on `H ⊕ H`, a
   block-diagonal operator is positive exactly when each block is, and the same holds under `R`.
   So:
   - `T_g := (T^A_g, T^B_g)` is a measurement;
   - `Z := (Z^A, Z^B)` is self-adjoint;
   - `A_g ≤ Z` and `T_g Z = T_g A_g` hold componentwise.
3. **Images.** `L` and `R` are ⋆-homomorphisms that preserve and reflect the order, so they carry
   (i)–(iii) over.
4. **Hypothesis on `A_g`.** `A_g` is componentwise, `A_g = (E_u A^u_{g(u)}, E_u B^u_{g(u)})`, by
   construction once the doubled strategy's point measurements are pairs `(A^u_a, B^u_a)`. The
   doubled model of audit §4.1 is to provide this, and it is part of the doubling task. ∎

**Remark 12′ ((S) for the doubled algebra; elementary, not needed).** Let
`t := R(𝒜 × ℬ) = {π(b) ⊕ π(a)}`. It contains `R(1,0) = 0 ⊕ 1`.

- A block operator `[[X₁₁, X₁₂], [X₂₁, X₂₂]]` that commutes with `0 ⊕ 1` has `X₁₂ = X₂₁ = 0`.
- `X₁₁` commutes with `opsB`, so it lies in `opsA`. `X₂₂` commutes with `opsA`, so it lies in
  `opsB`. Hence `t′ = L(𝒜 × ℬ)`.
- (Tr) holds componentwise. The vectors `(g_k, 0)` and `(0, h_l)` separate block-diagonal
  operators, where the `h_l` are the trace vectors of `opsB`.

### 5.6 Order agreement and pull-back (Lemma 13)

**Lemma 13 (order agreement in a finite pair).** If `𝒜` is a `StarOrderedRing`, then
`0 ≤ a ↔ 0 ≤ π(πA a)` for `a ∈ 𝒜`. Consequently:

- a measurement in `opsA` (in the operator order) pulls back uniquely to a measurement in `𝒜`, by
  `injA`;
- `Z^A` pulls back as well, together with the inequalities `A_g ≤ Z^A`.

The `ℬ` side follows by `swap`.

*Proof.*

1. **(⇒)** `0 ≤ a` means that `a` lies in the additive closure of `{s* s}`. Induct on the
   closure: `π(πA(s* s)) = (π πA s)*(π πA s) ≥ 0`, and sums of positive operators are positive.
   This is Mathlib's `StarRingHomClass.instOrderHomClass`
   (`Mathlib/Algebra/Order/Star/Basic.lean:460`). The repository already states it as
   `π_πA_nonneg` (`MIPRE/Foundations/POVMValue.lean:173`).
2. **(⇐)** Let `x := π(πA a) ≥ 0`.
   - `x` commutes with every `π(πB b)` (`commute`), so `√x` does too (`Commute.cfcₙ_nnreal`).
     Hence `√x = π(πA c)` for some `c ∈ 𝒜` (`commutantA`, `FinitePair.lean:98`).
   - `π(πA c) = √x` is self-adjoint, so `π(πA(c* c)) = √x √x = x = π(πA a)`.
   - `injA` (`FinitePair.lean:94`) gives `a = c* c ≥ 0`.
3. **Pull-back.** Each `T_g ∈ opsA` is `π(πA a_g)` for a unique `a_g`. By step 2, `a_g ≥ 0`, and
   `Σ_g a_g = 1` by injectivity. The same argument applies to `Z` and to `Z − A_g ≥ 0`. ∎

This settles the order question left open at `FinitePair.lean:33-36`. That docstring says the
orders agree, but that "no lemma here states this yet".

### 5.7 Approximate forms (not chosen)

The exact route dominates the approximate one, and the approximate route is not recommended. This
subsection records why.

**Proposition 14 (near-maximizers are insufficient).** A near-maximizer (`f(T) ≥ sup f − η`)
gives only trace bounds: `τ((A_h − W)₊) ≤ √(ηC)`, with `W = (Z + Z*)/2`. That is not enough. There
is a finite pair such that, for every `η > 0`, some `η`-near-maximizer has the following property:
every `Z ≥ A_g` satisfies `‖Z − Σ_g T_g A_g‖ ≥ 1`, and in fact `⟨ψ, (Z − Σ_g T_g A_g)ψ⟩ ≥ 1` for
some unit vector `ψ`.

*The bound.* Let `τ(1) = 1` and `C := 2Σ_g ‖A_g‖`, and suppose `f(T) ≥ sup f − η` with
`0 < η ≤ C`.

1. `|ρ(x)| ≤ ‖x‖`. Hence, in Lemma 6, `|c| ≤ Σ_g ‖A_g‖ + ‖A_h‖ ≤ C`.
2. So `2εa ≤ η + ε²C`. Take `ε = √(η/C)`. With Lemma 8, step 1, this gives
   `ρ(P(A_h − W)) ≤ √(ηC)` for all `P ∈ M` with `0 ≤ P ≤ 1`.
3. Put `Y := A_h − W` and `P := φ_m(Y) ∈ M`, where `φ_m(x) = min(1, m x₊)`. Since
   `x φ_m(x) ≥ x₊ − 1/(4m)`, we get `τ(Y₊) ≤ √(ηC) + 1/(4m)` for every `m`, hence
   `τ(Y₊) ≤ √(ηC)`. This is only an `L¹(τ)` bound.

*The counterexample.*

- Take `M = L^∞[0,1]` acting on `L²[0,1]`, with trace vector `1`. `M` is maximal abelian, so it is
  its own commutant, and `1` is a separating trace vector. It is the type I example of a finite
  pair given in the docstring at `FinitePair.lean:47-49`.
- Let `0 < η ≤ 1`, `G = {1, 2}`, `A_1 = 1_{[0,η]}` and `A_2 = 0`. Then `sup f = τ(A_1) = η`.
- Take `T = (0, 1)`. Then `f(T) = 0 ≥ sup f − η`, and `Σ_g T_g A_g = 0`.
- Let `ψ = η^{-1/2} 1_{[0,η]}`, a unit vector. Every `Z ≥ A_1` satisfies
  `⟨ψ, Zψ⟩ ≥ ⟨ψ, A_1 ψ⟩ = 1`, so `‖Z − Σ_g T_g A_g‖ ≥ 1`.
- For `η > 1`, the example with `η = 1` is already an `η`-near-maximizer.

The consumers evaluate in the strategy's arbitrary unit vector `ψ` (Lemma 0), not in `τ`. So no
τ-approximate form transfers. ∎

**Proposition 15 (the norm-approximate route).** The slack is written `κ`, to avoid a clash with
the vendored `delta`.

- (a) A norm-approximate form would be enough downstream: `T ∈ 𝒯`, `Z = Z* ∈ M`, `A_g ≤ Z`
  exactly, and `‖Σ_g T_g A_g − Z‖ ≤ 2κ`. It costs `+2κ` at each of the two base uses of
  slackness. It also requires replacing the per-`g` interface field and re-signing about
  15 pass-through theorems.
- (b) A proof without compactness gives this form with `κ = η`, for every `η > 0`, together with
  the per-`h` slack bound `‖T_h Z − T_h A_h‖ ≤ η/2`. The method is to maximize the regularized
  objective `f(T) − η Σ_g τ(T_g²)`. That is a nearest-point problem in
  `PiLp 2 (G × Fin n → H)` over `ℝ`.

*Proof of (a): tolerance downstream.* Suppose `T ∈ 𝒯`, `Z = Z* ∈ M`, `A_g ≤ Z` exactly, and
`E := Σ_g T_g A_g − Z` has `‖E‖ ≤ 2κ`.

- In base use (a), `|Σ_h ev(L(T_h A_h)) − ev(L(Z))| = |ev(L(E))| ≤ 2κ`.
- In base use (c), `|Σ_{h'} ev(Hu(u,h') ⊗ E)| = |ev((Σ_{h'} Hu(u,h')) ⊗ E)| ≤ 2κ`, since
  `0 ≤ Σ_{h'} Hu(u,h') ≤ 1`.
- Dual feasibility, `sliceDominatesAveragedPoint` and `Z ≥ 0` are unchanged.

The cost is not only a scalar error, however:

- The per-`g` field `complementarySlackness` (`Statements.lean:92-94`) can no longer be
  inhabited, so it must be replaced by an approximate field.
- Every pass-through site listed in Lemma 0 must be re-signed, about 15 theorems.
- The `+2κ` must be threaded through the fixed closed-form errors, for example
  `selfImprovementHelperError`.
- It has not been verified that the two base sites are the only places where the change matters
  (§5.9).

*Proof of (b): regularized objective, no compactness.* Fix `η > 0`, assume `τ(1) = 1`, and let
`f_η(T) := f(T) − η Σ_g τ(T_g²)`.

1. **Nearest-point form.** Let `𝓗 := PiLp 2 (fun _ : G × Fin n ↦ H)`, viewed as a real inner
   product space through `InnerProductSpace.rclikeToReal`
   (`Mathlib/Analysis/InnerProductSpace/Basic.lean:956`). Its inner product is `Re⟪·,·⟫`, and its
   norm is unchanged. Put `Φ(T) := (T_g g_k)_{g,k}` and `a := (A_g g_k)_{g,k}`. Then
   `‖Φ(T)‖² = Σ_g τ(T_g²)` and `Re⟪Φ(T), a⟫ = f(T)`, so
   `f_η(T) = −η ‖Φ(T) − a/(2η)‖² + ‖a‖²/(4η)`.
2. **`Φ(𝒯)` is nonempty, ℝ-convex and closed.** Let `Φ(T^j) → u`.
   - Let `D := span{y g_k : y ∈ M′}`. `M′` is a star-closed algebra, so the projection `Q` onto
     the closure of `D` lies in `M″ = (t ∪ t*)‴ = M`.
   - `(1 − Q) g_k = 0` for all `k`, so `Q = 1` by (F). Hence `D` is dense.
   - On `D`, `T^j_g (y g_k) = y T^j_g g_k → y u_{g,k}`. Since also `‖T^j_g‖ ≤ 1`, an ε/3 argument
     gives strong convergence `T^j_g → T_g` on `H`.
   - Strong limits preserve commutation with `t ∪ t*`, self-adjointness, positivity and
     `Σ_g T_g = 1`. So `T ∈ 𝒯` and `Φ(T) = u`.
   - `Φ(𝒯)` is closed in a complete space, so it is complete.
3. **Maximizer.** `exists_norm_eq_iInf_of_complete_convex`
   (`Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean:36`) gives a point of `Φ(𝒯)`
   nearest to `a/(2η)`. That point maximizes `f_η`.
4. **First-order conditions.**
   - With `T'` from Lemma 5, `f_η(T') = f_η(T) + 2ε[ρ(P B_h) − ρ(P Z_B)] + R(ε)`. Here
     `B_g := A_g − 2η T_g`, which is self-adjoint and in `M`, and `Z_B := Σ_g T_g B_g`.
   - The linear coefficient follows from `ρ(T_g P T_g) = ρ(P T_g²)` (by (Tr)) and the swap of
     Lemma 6.
   - `R` is a polynomial in `ε` of degree at most 4, with no constant or linear term. Its
     coefficients are bounded in terms of `‖A_g‖`, `η` and `|G|`, because `‖T_g‖, ‖P‖, ‖K‖ ≤ 1`.
     So `|R(ε)| ≤ C′ε²` on `[0,1]`.
   - Lemma 7, in its general form, gives `FO(T, B)`.
   - Lemmas 8 and 9 use only `FO`, `T ∈ 𝒯`, and that each `B_g` is self-adjoint and in `M`. So
     they give `Z_B = Z_B*`, `Z_B ≥ B_h ≥ A_h − 2η`, and `T_h Z_B = T_h B_h`.
5. **Result.**
   - Put `Z := Z_B + 2η`. Then `A_h ≤ Z`.
   - `Σ_g T_g A_g − Z = 2η(Σ_g T_g² − 1)`, which lies in `[−2η, 0]` because `0 ≤ T_g² ≤ T_g`.
     So `κ = η`.
   - For each `h`, `T_h Z − T_h A_h = 2η T_h(1 − T_h)`, so `‖T_h Z − T_h A_h‖ ≤ η/2`. ∎

### 5.8 Lean plan, sizes, and the correction to audit §4.2

The exact route was prototyped in Lean (not committed) in three pieces. For each,
`#print axioms` showed dependence only on `propext`, `Classical.choice` and `Quot.sound`:

- **The core chain.** Lemmas 1b–3 and 5–9, and Theorem 10 given a maximizer, with (S) phrased as
  `M = StarSubalgebra.centralizer ℂ t`: 344 lines, importing only
  `MIPRE.Foundations.BipartiteModel`. Lemma 3 was proved in both forms, with and without the
  equality case.
- **Lemma 4.** 66 lines over the vendored `WOTCompact`.
- **Lemma 13 (order agreement).** 42 lines over `MIPRE.Foundations.FinitePair`.

One elaboration pitfall came up. Closing `IsSelfAdjoint.smul` for a real scalar with `by simp`
timed out at 200k heartbeats. An explicit
`rw [star_sub, star_smul, Complex.star_def, Complex.conj_ofReal]` fixed it.

| Piece | Lines | Basis |
|---|---|---|
| Trace API for `τ` (add, sub, smul, finite sum, `τ(x*) = conj τ(x)`, `Re τ(x*x) = Σ_k ‖x g_k‖²`), faithfulness, Lemma 1b in the centralizer | 70–90 | measured, about 70 |
| Lemma 3, with its equality case | 30–40 | measured, about 35 |
| Lemmas 8–9 under the first-order hypothesis | 90–110 | measured, about 95 |
| Lemmas 5, 6, 7, 7′ and Theorem 10 given a maximizer | 140–170 | measured, about 145; placement `MIPRE/Foundations` |
| Lemma 4, plus glue from the WOT set to the centralizer form of `𝒯` | 90–110 | 66 measured; glue 20–40 estimated (`mem_centralizer_iff`, `toCLM_ofCLM`, `Σ` through `ext_inner_left`); placement `MIPRE/Background` |
| Finite-pair instantiation: centralizer equals `opsA`, `VecTrace` to (Tr) and (F), the `ℬ` side by `IsFinitePair.swap` | 30–50 | estimate |
| Lemma 13 and the pull-back of measurements and of `Z` to `𝒜`; the `ℬ` side by `swap` | 60–100 | order agreement measured at 42; pull-back 20–50 estimated |
| Corollary 12 in the doubled local algebra | 30–60 | estimate |
| Interface adapter: `SdpStatementWithSlackness` over the port's `Measurement` and operator types, with `G = Polynomial params` and `A_g = averagedPointOperator` | 100–250 | not measured; the vendored `SdpMatrixBridge.lean` it replaces is 313 lines |
| Not ported: `SelfImprovement/MatrixRealization` (3667 lines) and `SdpMatrixBridge.lean` (313 lines) | −3980 | `wc -l`. Apart from the root `MIPRE.lean`, `MatrixRealization` is imported only by `SdpMatrixBridge.lean:9-10`, and `SdpMatrixBridge` only by `Bracketed.lean:10` |
| Optional, not recommended: Proposition 15b, the interface change, re-signing about 15 theorems, the `+2κ` cascade | 400–600 plus an unsized cascade | by analogy with the measured pieces |

Without the adapter, the total is about 0.55–0.75k lines.

Some of these pieces already exist in `MIPRE/Background/Orthonormalization`:

- `vecFunctional`, with `vecFunctional_star_mul_self` and
  `eq_zero_of_vecFunctional_star_mul_self_eq_zero` (`CenterTrace.lean:57-64`, `:130-157`), is the
  trace API of Lemma 2;
- `mem_vnA_iff` (`FinitePairOrtho.lean:51-59`) is the centralizer equality of §5.1.

`MIPRE/Foundations` never imports `MIPRE/Background`. So if the core chain is placed in
Foundations, it has to restate these short proofs rather than import them.

**Correction to `reports/lidt-co-audit.md` §4.2 (`:427-433`).** The audit's "On class C" bullet
says that Mathlib lacks two inputs:

- weak-operator compactness of measurement tuples, citing the vendored
  `VN/Modular/WOTCompact.lean` as giving a cluster point for one sequence only;
- an API for normal traces.

It estimates 0.5–4k lines. Both premises are now out of date:

- Full WOT compactness of norm balls is vendored at `Orthogonalization/MvN/WOTCompact.lean:114`,
  and Lemma 4 builds compactness of measurement tuples from it.
- `τ` is a finite sum of vector functionals and is already WOT-continuous. So neither a
  normal-trace API nor the σ-weak topology is needed.

The estimate becomes about 0.55–0.75k lines plus a 100–250-line adapter. `planning/c6b-plan.md`
uses this figure in row M9.

### 5.9 Status and open points

**Settled.**

- Theorem 10 and the exact route, with high confidence. The core chain, Lemma 4 and Lemma 13 were
  prototyped in Lean and compiled with no axioms beyond the standard three. Every step was also
  checked by hand in the adversarial verification.
- The near-maximizer route fails. The explicit `L^∞[0,1]` example of Proposition 14 settles this.
- `𝒜 × ℬ` carries the componentwise star-ordered structure in Mathlib (`Prod.instStarOrderedRing`,
  `Mathlib/Algebra/Order/Star/Prod.lean:21-24`). So Corollary 12 can be stated over `𝒜 × ℬ`
  rather than over block operators on `H ⊕ H`.
- The amplified pair is a finite pair: it is the standard-form model of the standard tracial
  algebra `tensorStep M B`, and `isFinitePair_stdModel`
  (`MIPRE/Background/Repetition/TracialApprox.lean:148`) applies to every such model. What the
  amplification adds, the absence of abelian projections, is Theorem A of §3, and Theorem T
  there keeps the correlation.

**Open.**

- **The doubled model is unproved.** This covers the placements `L` and `R` and point
  measurements given componentwise (audit §4.1). Corollary 12 needs the `A_g` to be
  componentwise, which belongs to the doubling task.
- **The interface adapter is not sized** (estimated at 100–250 lines). The port's `Measurement`
  and operator types are not yet fixed.
- **The per-`h` slackness inventory of Lemma 0 was checked only at the call lines.** The bodies
  were not read in full. Of the roughly 25 files that consume `SliceBoundednessInput`, only
  `RawSecond.lean` was read. This does not affect Theorem 10, which supplies the exact per-`g`
  fields. It does limit Proposition 15a: the claim that the approximate route costs only `+2κ` at
  the two base sites, plus re-signing, is unverified. That matters only if the approximate route
  is ever chosen.
- **Proposition 15b's closedness argument (step 2) was not prototyped in Lean.**
- **The prototypes are not committed.** The measured line counts can be reproduced from the
  statements, but they cannot be checked against the tree.
- **The cost accounting of Proposition 15a and the adapter sizes** carry only medium confidence,
  because both depend on the port's types.
