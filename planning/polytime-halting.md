# The polynomial-time halting reduction and the paper's class: plan

Written 2026-09-28 (#230). Target: the efficiency clause of the paper's `thm:halting` and the
class `MIP*_{1,1/2}(2,1)` of its `def:mipstar` (`paper/games.tex`, `paper/recursive.tex` at
`a459dee`), so that `thm:mipstar-eq-re` is proved for the class the paper defines rather than
for the computable class the Lean currently uses. Ledger nodes 1.1.7, 1.1.7.1 (the class) and
1.6.5 (`lem:lambda`).

## 1. What is proved today, and what the paper says

`HaltingReducesToGameValue` (`MIPRE/HaltingGameValue.lean`) and `MIPStar`
(`MIPRE/Foundations/ClassMIPStar.lean`) ask for a Mathlib-`Computable` map from machines, or
strings, to explicit `GameData`. The blueprint records this in `def:mipstar` ("there is no
polynomial-time bound on `g` in this definition"), in `rem:source-mipstar`, and in the
introduction's paragraph "Computable rather than polynomial-time, where possible".

The paper's `def:mipstar` asks for two Turing machines `S` and `D` such that on input `z` the
sampler runs in time `poly(|z|)` and returns a question pair distributed as `μ_z`, and the
decider on `(z, x, y, a, b)` runs in time `poly(|z|)` and returns `D_z(x, y, a, b)`, with a
footnote: the decider returns `0` whenever `x, y, a, b` are too long. Its `thm:halting` is a
polynomial-time map from machines to games "that satisfies the efficiency requirement". So the
Lean's `MIPStar = IsRE` is a theorem about a class that contains the paper's, and the
inclusion of the paper's class in it, the paper's `RE ⊆ MIP*`, has not been formalized.

## 2. Why a time bound cannot simply be added to the existing map

The Lean proves `thm:halting` through Lin's compressibility criterion
(`Cost.compressibility_criterion_levels`, `MIPRE/Foundations/Compression.lean`). Its output is
a description `g e` at level `R e = 2 ^ (K + 1 + |e|)`, tabulated at that level
(`Halting.halting_reduction`, `MIPRE/Foundations/Halting/Reduction.lean`). The level is forced:
the criterion's compressor reads the string it compresses through a succinct description, which
needs `2|c| ≤ n` and `|x| ≤ n + 1` at level `n`, and boundedness is "n-bounded at level n"
(`Verifier.InClassA`, `InClassB`). The compressed sampler's questions at level `n` have length up
to `G.bound.eval (n + λ)`, so at level `R e` they are exponential in `|e|`, and the tabulated
game is doubly exponential. No `poly(|e|)`-time verifier can write down a question of that game.

The paper outputs the verifier `V^halt = (S^compr_λ, D^halt)` at the fixed level `C_0` and
puts the machine's size into the parameter, `λ = poly(|M|)` (`lem:lambda`): the decider
`D^halt` has `M` and `λ` hard-coded, runs `M` for `n` steps, and otherwise runs the compressed
decider of its own verifier. That route needs the fine accounting `TIME(n) = poly(n, |M|)`,
which the Lean route replaced by the level-tied boundedness (blueprint, comments after
`lem:lambda`). So the polynomial-time statement is a second derivation of `thm:halting`, along
the paper's own construction, next to the existing one; the existing one stays as the proof of
`lem:compressible-criterion`, a result of its own.

## 3. What is reusable

- `GapCompression` (`MIPRE/Foundations/GapCompression.lean`) already carries running times
  `bound.eval (n + λ)` at a uniform degree `deg`, `compress : PolyTimeFun`, and
  `samplerProg : PolyTimeFun ℕ Prog`. Nothing about the compression pipeline changes.
- The costed toolkit: `UniversalMachine` (`time_le`, a polynomial overhead),
  `ClockedUniversalMachine` (total budgeted simulation), `hardcode` (s-m-n, linear),
  `efficient_fixed_point` (`Cost/Kleene.lean`), `PolyTimeFun` with its closure library.
- `lem:lambda-bound` (`Halting/LambdaBound.lean`): `C (C' λ n)^C ≤ n^λ` for
  `λ ≥ 4 max((4C)^(8C), C log C')`, exactly the arithmetic `lem:lambda` needs.
- The wrapper decider and its explicit cost (`Halting/Wrapper.lean`, `WrapperCost.lean`);
  the compressor's decider program `haltProg` (`Halting/Compressor.lean`), which is the paper's
  `F` minus the `M`-run branch and with the description read by bit queries rather than
  hard-coded; `PolyBounded` and its absorption lemmas (`Halting/PolyBounded.lean`, `Absorb.lean`).
- `Verifier.valStar_congr`, `hasPerfectPCC_congr`, `hasPerfectPCC_of_le`,
  `valStar_eq_of_rejects`, `hasPerfectPCC_of_accepts_diagonal`, `Verifier.IsBounded`.
- The tabulation (`Halting/Tabulate.lean`): budgeted runs (`runForD`, `accepts_iff_runForD`),
  string indexing (`answerEquiv`, `bitsToIdx`), the doubled question set (`tagEquiv`,
  `accListW`) and `quantumValue_doubled`, which is what lets a bipartite game be a `GameData`
  without losing value.
- The search branch of the criterion's decider (`decFunV` in `Compression.lean`): the
  value-form compression has no base case for soundness (the paper's uses entanglement
  divergence), so the paper-route decider keeps Lin's branch, "the semidecider for
  `val* > 1/2` on the verifier's own description at level `C_0` halted within `n` steps: reject
  everything", with `exists_semidecider_lt_quantumValue` supplying the semidecider.

## 4. The plan

### PR 1: the class, and its inclusion in the computable one

**Done (PR after #231):** `MIPRE/Foundations/ClassMIPStarPoly.lean` (`PolyVerifier`, `Efficient`,
`game`, `MIPStarPoly`), `ClassMIPStarPolyTab.lean` (`tab`, `tab_computable`, `quantumValue_tab`,
`MIPStarPoly.toMIPStar`, `MIPStarPoly.isRE`), `Cost/Kleene.lean` (`kleeneFix`, `kleeneFix_runs_of`),
`Cost/ManyOne.lean` (`haltingReduction`, `exists_polyTime_reduction`); blueprint `def:mipstar`,
`def:mipstar-computable`, `lem:mipstar-poly-sub`, `rem:source-mipstar`.

`MIPRE/Foundations/ClassMIPStarPoly.lean` (name indicative):

- `PolyVerifier`: a closed sampler program, a closed decider program, one polynomial `P`.
  Write `B z = P.eval |z|`. On input `z`:
  - **sampler**: on `encode (z, r)` for every seed `r` of length `B z`, halts within cost `B z`
    with output `encode (x, y)` for strings `x, y` of length at most `B z` (the paper's "returns
    a pair in `X × Y`"; the randomness of a randomized machine is an explicit seed of the length
    of its time bound);
  - **decider**: on `encode (z, x, y, a, b)` halts within cost
    `P.eval (|z| + |x| + |y| + |a| + |b|)`, and accepts only when all four strings have length at
    most `B z` (the paper's footnote).
- `PolyVerifier.game z : Game (Answers (B z)) (Answers (B z)) (Answers (B z)) (Answers (B z))`,
  with `μ_z (x, y)` the fraction of seeds mapped to `(x, y)` and `D_z` acceptance.
- `MIPStarPoly L`: some `PolyVerifier` with both clauses at every `z`, `val*(game z) = 1` on
  `L` and `≤ 1/2` off it.
- `MIPStarPoly.toMIPStar : MIPStarPoly L → MIPStar L`: the map `z ↦ tab z : GameData` is
  computable, with questions doubled by a tag bit and indexed among the strings of length at
  most `B z`, weights one per seed, and the acceptance table by budgeted runs;
  `quantumValue (tab z).game = quantumValue (game z)` by `quantumValue_doubled` and
  `quantumValue_eq_of_equiv`. Hence `MIPStarPoly L → IsRE L` from `MIPStar.isRE`.
- Two pieces of infrastructure the next PR needs and that stand alone: a version of
  `efficient_fixed_point` with an explicit overhead polynomial in `esize (F e)` (the current
  statement is existential in the polynomial; its proof already exhibits it), and a costed
  many-one reduction from an r.e. language to halting on the empty input,
  `z ↦ hardcode S_L (encode z)` for the semidecider `S_L` of `Cost.exists_semidecider`, which
  is linear time where `Halting.exists_code_halts_of_isRE` goes through Mathlib's `curry` with
  no time tracked.
- Blueprint: `def:mipstar` becomes the paper's class, marked with `MIPStarPoly`; the computable
  class becomes `def:mipstar-computable` (the current text, relabelled), with
  `lem:mipstar-poly-sub` for the inclusion; `rem:source-mipstar` rewritten to record the one
  deviation (§5).

### PR 2: the halting verifier along the paper's route

**Done (on #231, second commit):** `MIPRE/Foundations/Halting/Paper/` -- `TabulateL.lean`
(the tabulation of `Vof G U x` at a fixed level and its semidecider `exists_semL`),
`Decider.lean` (`prep`, `body`, `F`, `dec = kleeneFix U F`, `Vhalt`, `accepts_iff`),
`Induction.lean` (the downward induction at level `C = max C_0 2`: `hasPerfectPCC_of_halts`,
`valStar_le_of_not_halts`, under `IsBounded lam` and `poly(n, lam) <= n^lam`), `Size.lean`
(`esize_dec = 2(|M| + |lam|) + const`), `Cost.lean` (`dec_cost`, the polynomial form
`decCostPoly`/`dec_cost_spec`, the wrapped decider's `Vhalt_decider_cost`, and `lem:lambda`
as `exists_lamBound`: `IsBounded lam` for `lam >= Lam0 + 4|M|`), `Main.lean`
(`halting_paper`). Three deviations from the text below, all recorded in the module
docstrings and the blueprint: the budgets of branches 1 and 2 are `Nat.size n` rather than
`n` (the criterion's reading; the levels `n, 2^n, ...` make `Nat.size` unbounded, and it
saves the unary-to-binary conversion); the search branch is present, since the value form of
compression has no base case for soundness; and `lambda(M) = Lam0 + 4|M|` with `Lam0`
existential (from `PolyBounded.absorb`, not `lambda_bound`), which is affine and so
trivially polynomial-time -- its computation by a program is PR 3's, where it is needed.
The fine bound `Q(n + |M| + lam) (|d| + 1)^k` on `dec` is `dec_cost_spec`; PR 3 consumes it
at `n = C`.

`MIPRE/Foundations/Halting/Paper/` (name indicative):

- **Construction** (`lem:halt-construction`, paper form). For `M : Prog`, `λ : ℕ` and a
  candidate decider `d`, the program `F_{M,λ} d`, on `(n, x, y, a, b)`:
  1. run `M` on the empty input for budget `n` through the clocked universal machine; if it
     halts, accept;
  2. run the semidecider for `val* > 1/2` on the description of `(S^compr_λ, wrap d)` at level
     `C_0`, for budget `n`; if it halts, reject;
  3. otherwise compute `compress ((S^compr_λ.prog, (wrap d).prog), λ)` and run it on the input
     through the universal machine.
  `F_{M,λ}` is a `PolyTimeFun Prog Prog` (hard-coding by `hardcode`, `wrap` by
  `wrapBuildProg`, `compress.code`); `e_{M,λ}` is its efficient fixed point, and
  `V^halt_{M,λ} = Verifier.ofSamplerDecider (G.sampler λ) (wrap e_{M,λ})`.
- **Values** (`lem:dhalt-values`): at every `n`, `(wrap e).Accepts n x y a b` is "M halts within
  `n`, and the questions have the sampler's dimension", or "the search halted within `n`: never",
  or `(G.output (S.prog, (wrap e).prog) λ).decider.Accepts n x y a b`. Hence: if `M` halts
  within `n`, a value-`1` PCC strategy (`hasPerfectPCC_of_accepts_diagonal`); if the search
  halted, value `0`; otherwise `V^halt_n` and `V^compr_n` agree (`valStar_congr`,
  `hasPerfectPCC_congr`, `RejectsLong` from `output_rejects_long`).
- **Accounting** (`lem:lambda`, paper form): an explicit polynomial `Q` with the cost of
  `wrap e_{M,λ}` on `(n, d)` at most `Q(n + |M| + λ) · (|d| + 1)^k`, from the wrapper cost, the
  clocked simulation (`ClockedUniversalMachine.bound`), the fixed cost of the two hard-coded
  computations, the universal machine's overhead on the compressed decider
  (`UniversalMachine.time_le` at `GapCompression.decider_time`), and the uniform fixed-point
  overhead of PR 1. Then `λ(M)`, computable in polynomial time and `poly(|M|)`, with
  `V^halt_{M,λ(M)}.IsBounded (λ(M))` by `lambda_bound`, the size clause included.
- **Induction** (`thm:halting`, paper form, at level `C_0`). Halting `M`, at time `T`: for
  `n ≥ T` the trivial strategy; for `C_0 ≤ n < T`, `GapCompression.completeness` from
  `V^halt_{2^n}` (answer bound raised to `(2^n)^λ` by `hasPerfectPCC_of_le` and
  `lambda_bound`) to `V^compr_n`, then `lem:dhalt-values`; the search branch never fires because
  `val* = 1` at every level. Non-halting `M`: if `val*(V^halt_{C_0}) > 1/2` the search halts at
  some `n_1`, levels `n ≥ n_1` have value `0`, and `GapCompression.soundness` carries `≤ 1/2`
  down to `C_0`, a contradiction. This is the criterion's argument at a fixed level, with the
  succinct description replaced by the hard-coded one.

### PR 3: the class verifier, `RE ⊆ MIP*`, the blueprint

**Done (on #232, third commit):** `Halting/Paper/Stages.lean` (sequencing and the universal
calls as program stages), `Build.lean` (`decBuild`, `lamF`, `cutF`, `exists_cut_ge`),
`ClassVerifier.lean` (`sampProg`, `decProg`, `sampProg_runs`, `decProg_accepts`,
`decProg_runs`, with explicit costs `sampB`, `decB`), `Count.lean` (seeds counted by their
prefix), `Foundations/GameRestrict.lean` (`quantumValue_restrictQuestions`),
`ClassMain.lean` (`classV`, `classV_efficient`, `classV_value`, `re_subset_mipstarPoly_of`,
`mipstarPoly_eq_re_of`); unconditional `re_subset_mipstarPoly`, `mipstarPoly_eq_re` in
`MIPRE/MainTheorem.lean`. One repair to PR 1's definition, recorded in the blueprint after
`def:mipstar`: the sampler's time is bounded by `P(|z| + |r|)`, not `B`, since a program reads
its seed of length `B` only by walking it and so cannot halt within `B` on it (with `|r| = B`
polynomial in `|z|` the bound is still `poly(|z|)`, and the class is unchanged in substance).
The cutoff of the decider is `2^(K + deg |lambda|)` rather than the compressor's bound itself:
a power of two is what the toolkit can compute from `|lambda|` in unary, and it is polynomial
in `lambda`. The ledger nodes 1.1.7, 1.1.7.1 stay on `rem:source-mipstar`, whose text now
records the two forms.

- The two programs on input `z`: `S_univ (z, r)` computes `λ(z)` and runs `G.samplerProg` on
  it, then the sampler at index `C_0` on the first `s(C_0)` bits of `r` for each player;
  `D_univ (z, x, y, a, b)` computes `λ(z)` and the description `e_{z, λ(z)}` (the fixed point is
  `hardcode (kleeneProg U F) (encode (kleeneProg U F))`, data manipulation on the program of
  `F` with `z` hard-coded) and runs `wrap e` at index `C_0` through the universal machine. Both
  polynomial, with the bounds of PR 2 at `n = C_0`. The game they define at `z` is
  `V^halt_{z,λ(z)}` at index `C_0` up to the identification of alphabets
  (`quantumValue_eq_of_equiv`; the seed-prefix pushforward is `clDist`).
- `re_subset_mipstarPoly`: `z ∈ L ↔ M_z` halts on the empty input, with `M_z` the costed
  reduction of PR 1, composed with the verifier above (`hardcode` of `M_z` into `F`).
- `mipstarPoly_eq_re : MIPStarPoly = IsRE`, and the polynomial-time `thm:halting` as a
  statement about `Nat.Partrec.Code` through `compile`, if a corollary in that form is wanted.
- Blueprint: `thm:halting` recovers its efficiency clause with the new declarations beside
  the old; `lem:lambda`'s statement is the paper's again, with the level-tied version moved to
  its comments; `thm:mipstar-eq-re` is stated for the paper's class; `cor:main-quantum` gains
  the polynomial-time form; the introduction's paragraph is rewritten; ledger nodes 1.1.7,
  1.1.7.1 and 1.6.5 get their `\ledgernode{}` on the statements that now discharge them.

If the accounting of PR 2 grows past what one review can hold, it splits into the
construction with `lem:dhalt-values`, and the accounting with the induction.

## 5. Deviations to record

- **Time in the total input length.** The paper's decider runs in time `poly(|z|)` "even for
  long inputs", which the ambient cost model cannot express: a program reads a list only by
  walking it (blueprint, the discussion under `def:decider`). The class is stated with the
  decider's time polynomial in `|z| + |x| + |y| + |a| + |b|` and the paper's own footnote
  clause, rejection of overlong messages, as a separate requirement. The game `G_z` on strings
  of length at most `B z` is then the paper's finite game, and the two definitions describe the
  same languages.
- **Seeds.** A randomized machine is a deterministic program with an explicit uniform seed of
  the length of its time bound. This is the standard reading and changes nothing.
- **The search branch.** The paper's soundness at level `C_0` uses the entanglement form of
  compression; the value form used here needs Lin's search branch in the decider, as the
  existing route does. The output game is still the paper's `V^halt_{C_0}` in every other
  respect, and `lem:dhalt-values` gains one clause.
- **Levels.** `GapCompression` is stated for `Verifier 7`, the paper's `9`-level premise being
  the pipeline's own count; unchanged here.

## 6. Done when

`MIPRE.MIPStarPoly` is `def:mipstar` in the blueprint with the inclusion in the computable
class checked; `MIPRE.mipstarPoly_eq_re` carries `thm:mipstar-eq-re` with a proof-level
`\leanok` and a guard in `MIPRE/Axioms.lean`; `thm:halting` and `lem:lambda` are marked with the
paper-route declarations; `scripts/lean-coverage.py --check`, `ledger-sync.py`,
`blueprint-edges.py --check` and `blueprint-colours.py --check` report no problems; and
`planning/formalization-plan.md` records the change of class.
