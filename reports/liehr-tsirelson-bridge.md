# The `lukasliehr/MIPRE` statements, proved from ours

Written 2026-09-25 (#228). `lukasliehr/MIPRE` is an independent Lean 4 formalization whose
goal is the negative resolution of Tsirelson's problem along the route of MIP* = RE. Its
terminal file `Tsirelson/MainStatement.lean` states three propositions and proves none of
them; upstream's own bridge derives the second and third from the first, and the first is
its open obligation. This repository proves all three from `MIPRE.separation`
(`thm:separation`), in `MIPRE/Background/LiehrTsirelson/Main.lean`, with only `propext`,
`Classical.choice` and `Quot.sound` (`MIPRE/Background/LiehrTsirelson/Axioms.lean`):

| upstream proposition | proved by | from |
|---|---|---|
| `QuantitativeSeparationStatement` (a game with `valStar ≤ 1/2`, `valCo = 1`) | `MIPRE.Liehr.quantitativeSeparation` | the game of `MIPRE.separation` |
| `NegativeTsirelsonStatement` (`Cqa n k ⊂ Cqc n k`, `n, k ≥ 1`) | `MIPRE.Liehr.negativeTsirelson` | its correlation in `Cqc \ Cqa` |
| `GameValueSeparationStatement` (a square game, `valStar < valCo = 1`) | `MIPRE.Liehr.gameValueSeparation` | the same game |

The point of the exercise was the one the maintainer named: a separation stated without
reference to this repository's definitions is a test of those definitions. It passed, and
the identification of the two vocabularies (`Bridge.lean`) is short enough to read in one
sitting. What it showed is below.

## 1. Where the two vocabularies differ, and which way the inclusions go

| notion | upstream (`Tsirelson.*`) | this repository (`MIPRE.*`) | relation proved |
|---|---|---|---|
| game | `NonlocalGame X Y A B`: nonemptiness of the four alphabets as fields, a `FiniteProbability (X × Y)`, `accept : ... → Bool` | `Game X Y A B`: `μ : X → Y → ℝ` with nonnegativity and sum one, `D : ... → Bool`; nothing about nonemptiness | `toLiehr` embeds ours into theirs on nonempty alphabets; payoffs agree on every correlation (`payoff_toLiehr`) |
| payoff | `∑ q, μ q * ∑ a b, D * p` | `∑ x y a b, μ x y * D * p` | equal, by `Finset.mul_sum` |
| commuting-operator strategy | `H : Type` with inner-product-space and completeness instances, unit `ψ`, one `POVM H A` per question on each side, global commutation | the same fields under other names | the two structures are the same data: both transfer maps are definitional and `Tsirelson.CommutingCorrelations = Cqc` (`commutingCorrelations_eq_Cqc`), hence `valCo (toLiehr G) = commutingOperatorValue G` |
| tensor-product strategy | `ψ : EuclideanSpace ℂ (Fin dA × Fin dB)`, one **POVM** on `EuclideanSpace ℂ (Fin d)` per question on each side, correlation through `kronCLM` | `ψ : Fin dA × Fin dB → ℂ`, one **projective** measurement of matrices per question on each side, Kronecker product | `Tsirelson.TensorCorrelations ⊆ Cq` by Naimark dilation of both sides (`exists_projective_dilation_povm`) on the twice-extended state, then a reindexing of `Fin d × A` to `Fin (d * card A)`; hence `Tsirelson.Cqa ⊆ Cqa` and `valStar (toLiehr G) ≤ quantumValue G` |
| values | `sSup` of the payoff image of the correlation set | `⨆` over strategies of the strategy value | equal for the commuting value; one inequality for the finite-dimensional value, which is all the statements need |

Two remarks on the table.

- **The tensor-product inclusion is an equality, but only one direction is proved.** A
  projective measurement is a POVM, so `Cq ⊆ Tsirelson.TensorCorrelations` is immediate;
  it is not needed for any of the three propositions and was not written. Anyone wanting
  `valStar (toLiehr G) = quantumValue G` needs that direction plus the `sSup`/`⨆` bookkeeping.
- **Upstream states its finite-dimensional value with POVMs and ours with projective
  measurements, and the two are the same value.** That is Naimark's theorem, and this
  repository already had it in the form needed (`MIPRE/Foundations/StrategyDilation.lean`,
  written for the Pauli basis test). The bridge is where it was first used to compare two
  *definitions* of the value rather than two strategies.

## 2. What the statements needed that ours did not have on the surface

- **Nonemptiness.** Upstream's `NonlocalGame` carries `Nonempty` proofs of all four
  alphabets and its terminal statements ask for `1 ≤ n ∧ 1 ≤ k`. Our `GameData` of
  `MIPRE.separation` has alphabets `Fin (nX + 1)` and `Fin (nA + 1)`, so nonemptiness is
  free, and the bridge to `Tsirelson.Game n k` is at `n = nX + 1`, `k = nA + 1`.
- **Square games.** Upstream's `Game n k` has one question alphabet and one answer alphabet
  shared by the two players. `MIPRE.separation` is already stated in that shape (it comes
  from the halting reduction, whose games are square), so nothing had to be symmetrized.
- **Value `1` versus value `≥ 1`.** Upstream's `QuantitativeSeparationStatement` wants
  `valCo = 1` exactly, and `MIPRE.separation` gives `commutingOperatorValue = 1` exactly;
  `GameValueSeparationStatement` wants the strict `valStar < valCo`, which is
  `valStar ≤ 1/2 < 1`.

## 3. Provenance caveats

- The upstream archive (a zip of the `main` branch supplied by the maintainer on
  2026-09-25) contains **no license file**, and no commit hash is recorded. The vendored
  headers and `Upstream/README.md` say so; the terms should be settled with upstream before
  the tree is relied on for anything but this check.
- Only the import closure of `MainStatement.lean` is vendored (nine files, 1628 lines), with
  one redirected import: `MainStatement.lean` imports upstream's facade
  `Tsirelson.Operational`, which re-exports the core together with a bridge tree the
  statements do not use, and `scripts/vendor-liehr.py` redirects it to `Tsirelson.Core`.
  Nothing else is changed. Four upstream lines exceed 100 characters and are left as they
  are.
- Upstream's own conditional bridge `tsirelson_of_separation` (its `Nodes/B30`) was not
  vendored; `negativeTsirelson` and `gameValueSeparation` are proved directly from
  `MIPRE.separation` instead, which is shorter than transporting its hypotheses.
