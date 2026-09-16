/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Enumerate
import MIPRE.Foundations.Halting.Tabulate
import MIPRE.Foundations.SyncTransport
import MIPRE.Foundations.Cost.ProgData
import MIPRE.Foundations.Compression

/-!
# The halting reduction, assembled

Blueprint `thm:halting`: the computable map from machines to game descriptions whose game has
value `1` when the machine halts and value at most `1/2` when it does not. It is proved here
from gap-preserving compression as a hypothesis (`MIPRE.GapCompression`, blueprint
`thm:compression`) through the per-level compressibility criterion
(`MIPRE.Cost.compressibility_criterion_levels`, blueprint `lem:compressible-criterion`),
along the dictionary of blueprint `rem:compression-abstract`.

## What a string denotes

A string is a *description*, never a game: a pair `(λ, 𝒟)` of a compression parameter and a
decider program, serialized by `Data.toBitsPost` and read back by `Data.parse`. Every string
names such a pair — `descLam` normalizes the parameter (`Data.natOf`), `descDec` reads the
decider and falls back on the program `nil` — so no validity condition on strings appears
anywhere. The verifier it denotes is

  `Vof x = (S^compr_{descLam x}, wrap (descDec x))`   (`Verifier.ofSamplerDecider`),

the compressed sampler at the string's own parameter (which depends on `λ` alone, blueprint
`lem:compress-sampler-indep`, the field `GapCompression.sampler`) together with the string's
decider wrapped in the question-length check of `def:normal-verifier` (`Decider.wrap`). The
two classes of the criterion are then

  `classA n = {x | Vof x is n-bounded and 𝒱_n has a value-1 PCC strategy}`,
  `classB n = {x | Vof x is n-bounded and val*(𝒱_n) ≤ 1/2}`,

with answers cut at `ansBound x n = bound (n + descLam x)`, the length beyond which a
compressed decider with parameter `descLam x` rejects (`GapCompression.output_rejects_long`);
`Vof x` is not literally an output of `Compress`, so that field does not apply to it directly
— `ansBound` is the answer alphabet the classes are read with, and relating it to the
compressor's output is part of `Obligations.compr_spec`. Tying the boundedness parameter to
the level (`n`-bounded at level `n`) is what replaces the paper's choice of `λ` along the
recursion (blueprint `rem:compression-abstract`, item 1, and `lem:lambda`).

## Where the assembly is

`halting_reduction`, and the structure `MIPRE.Halting.Obligations` of what it still owes, are
in `Halting/Reduction.lean`, which sits below this file, `Halting/Strings.lean` and
`Halting/Semidecider.lean` in the import order, so that the two distinguished strings (O1) and
the semidecider (O3) are applied there as theorems rather than assumed as fields. What this
file contributes to it, beyond the objects above, is the tabulation:

* **O2** — the tabulation of `𝒱_n` as a game description matching it along relabelings of
  the two alphabets: `tab`, `tab_computable`, `tab_match`, `tab_value` and
  `gameValue_tab_eq_one`, in the last section of this file, which `halting_reduction` uses
  directly; the relabelings are `Verifier.tagEquiv` and
  `answerEquiv`, transported across the two sizes. Three features of their shape are
  deliberate and each is explained where it is stated: the match and the value hold of an
  `n`-bounded verifier and could not hold of every string, acceptance being `Σ₁` — while
  `dimOf_eq` and `margOf_eq`, budgeted from the compressed sampler's own time bound, hold at
  every string and every level; `tab_match` delivers the relabelings rather than only the
  value they equate, because `synval ≤ val*` points the wrong way for item 1 of `thm:halting`;
  and the game it matches is the *doubled* one, `(Vof G U x).doubledGame`, so that the
  diagonal a `GameData` vetoes carries no weight and no synchronicity is asked of the
  verifier. That last one is what makes the tabulation usable by O3, and the paragraph below
  the list says how.

O3 was recorded in `planning/h4-assembly.md` as "O2 plus a disjunction"; it is not, and the
reason is worth naming, because it shaped the tabulation.
`Halting.exists_sem_of_tab` needs the tabulation to have the value of `𝒱_n` at every
`n`-bounded string, in both directions, because `sem_spec` is an equivalence — while a match
against `(Vof G U x).game` gives that only where the verifier is also *synchronous* at `n`,
a `GameData` describing a synchronous game by construction
(`Verifier.isSynchronousAt_of_game_matches`), and `classB n` does not ask for synchronicity.
Three repairs were on the record in blueprint `lem:halting-semidecider`: tabulate on a doubled
question set so that the distribution avoids the diagonal, make `Decider.wrap` reject unequal
answers to equal questions so that every string names a synchronous verifier, or put
synchronicity into `classB` and pay for it in `compr_spec`. **The first is the one made**
(`Foundations/GameDouble.lean`, `Verifier.doubledGame`): it is the cheapest and the only one
that changes nothing outside the tabulation. So `tab_match` and `tab_value` below ask the
verifier's decider for nothing beyond `n`-boundedness, and `exists_sem_of_tab`'s `hval` is
`tab_value` itself.
-/

namespace MIPRE.Halting

open Cost
open HaltingGameValue (GameData)

/-! ## What a string denotes -/

/-- The compression parameter a string denotes: the left component of the data it parses to,
normalized to a canonical binary numeral (`Data.natOf`), so that every string names one. -/
def descLam (x : BitStr) : ℕ := Data.natOf (Data.parse x).left

/-- The decider program a string denotes: the right component of the data it parses to, or the
program `nil` when that is not the encoding of a program. Every string names one. -/
def descDec (x : BitStr) : Prog :=
  ((SizedEncoding.decode (Data.parse x).right : Option Prog)).getD .nil

/-- The string denoting a parameter and a decider: the postorder serialization of the pair. -/
def descOf (lam : ℕ) (dec : Prog) : BitStr :=
  (Data.cons (encode lam) (encode dec)).toBitsPost

@[simp] theorem descLam_descOf (lam : ℕ) (dec : Prog) : descLam (descOf lam dec) = lam := by
  simp [descLam, descOf]

@[simp] theorem descDec_descOf (lam : ℕ) (dec : Prog) : descDec (descOf lam dec) = dec := by
  simp [descDec, descOf, SizedEncoding.decode_encode]

/-! ## The verifier a string denotes, and the two classes -/

variable (G : GapCompression) (U : UniversalMachine)

/-- **The verifier a string denotes**: the compressed sampler at the string's own parameter,
and the string's decider wrapped in the question-length check. Every string denotes one,
well formed or not. -/
def Vof (x : BitStr) : Verifier 7 :=
  Verifier.ofSamplerDecider U (G.sampler (descLam x)) (descDec x)

/-- The answer-length budget the classes are read with at level `n`: the bound a compressed
decider with the string's parameter obeys at index `n`. -/
def ansBound (x : BitStr) (n : ℕ) : ℕ := G.bound.eval (n + descLam x)

/-! ### The answer budget of a short description

What obligation O4 needs of `ansBound`: on a string short enough to have come out of the
compressibility criterion, the budget the classes are read with at level `2n + 1` is below the
budget `GapCompression.completeness` supplies strategies at. Both bounds are exponential in
`n`; the point is which exponent, and the string's own parameter is what could have broken it.
-/

/-- **A string denotes a parameter exponential in its length at worst.** The parameter is the
number the left component of the parsed datum denotes, and parsing a string of length `L`
yields a datum of size at most `L` (`Data.size_parse_le`), which denotes a number below
`2 ^ L` (`Data.natOf_lt`). -/
theorem descLam_lt (x : BitStr) : descLam x < 2 ^ max 1 x.length :=
  lt_of_lt_of_le (Data.natOf_lt _)
    (Nat.pow_le_pow_right (by norm_num)
      ((Machine.size_left_le _).trans (Data.size_parse_le x)))

/-- The form the criterion's length bound is used in: `compr_spec`'s hypothesis
`x.length ≤ n + 1` caps the denoted parameter at `2 ^ (n + 1)`. -/
theorem descLam_lt_of_length_le {x : BitStr} {n : ℕ} (h : x.length ≤ n + 1) :
    descLam x < 2 ^ (n + 1) :=
  lt_of_lt_of_le (descLam_lt x) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The answer budget of level `2n + 1` fits under the compression theorem's.** For `λ` and
`n` above thresholds depending only on `G.bound`, a string of length at most `n + 1` has
`ansBound G x (2n+1) ≤ (2 ^ n) ^ λ` --- the budget at which `GapCompression.completeness`
takes its hypothesis. With `Verifier.hasPerfectPCC_of_le` this is what carries a value-`1` PCC
strategy from membership in `classA G U (2 * n + 1)` into that clause, and it is why
`Obligations.compr_spec` carries the length bound: `ansBound` grows with the string's own
parameter, so without it no pair of thresholds would do.

The thresholds are `λ ≥ 2 · deg(bound) + 1` and `n ≥ log₂(‖bound‖) + 2 · deg(bound) + 1`,
where `‖bound‖` is the sum of its coefficients; note they are set by the *polynomial* `bound`,
not by `G.deg`, which grades running times in the input size instead. -/
theorem exists_ansBound_le (G : GapCompression) :
    ∃ lam₀ n₀ : ℕ, ∀ (x : BitStr) (lam n : ℕ), lam₀ ≤ lam → n₀ ≤ n → x.length ≤ n + 1 →
      ansBound G x (2 * n + 1) ≤ (2 ^ n) ^ lam := by
  obtain ⟨D, hD⟩ : ∃ D, D = G.bound.natDegree := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i ∈ Finset.range (G.bound.natDegree + 1), G.bound.coeff i :=
    ⟨_, rfl⟩
  have hQ : ∀ y, 1 ≤ y → G.bound.eval y ≤ A * y ^ D := fun y hy => by
    rw [hA, hD]; exact polynomial_eval_le_sum_coeff_mul_pow G.bound hy
  refine ⟨2 * D + 1, Nat.size A + 2 * D + 1, fun x lam n hlam hn hx => ?_⟩
  have hdl : descLam x < 2 ^ (n + 1) := descLam_lt_of_length_le hx
  have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have h3 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
  have hm : 2 * n + 1 + descLam x ≤ 2 ^ (n + 2) := by omega
  have hev : G.bound.eval (2 * n + 1 + descLam x) ≤ A * (2 ^ (n + 2)) ^ D :=
    (polynomial_eval_mono G.bound hm).trans (hQ _ Nat.one_le_two_pow)
  have key : Nat.size A + (n + 2) * D ≤ n * lam := by
    have h : Nat.size A + 2 * D ≤ n := by omega
    have e1 : Nat.size A + (n + 2) * D = Nat.size A + 2 * D + n * D := by ring
    have e2 : n * (2 * D + 1) = n + (n * D + n * D) := by ring
    refine le_trans ?_ (Nat.mul_le_mul_left n hlam)
    rw [e1, e2]
    exact Nat.add_le_add h (Nat.le_add_right _ _)
  calc ansBound G x (2 * n + 1) ≤ A * (2 ^ (n + 2)) ^ D := hev
    _ ≤ 2 ^ Nat.size A * (2 ^ (n + 2)) ^ D :=
        Nat.mul_le_mul_right _ (Nat.lt_size_self A).le
    _ = 2 ^ (Nat.size A + (n + 2) * D) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (n * lam) := Nat.pow_le_pow_right (by norm_num) key
    _ = (2 ^ n) ^ lam := by rw [← pow_mul]

/-- **The class `A` at level `n`**: the strings whose verifier is `n`-bounded and whose `n`-th
game has a value-`1` PCC strategy. -/
def classA (n : ℕ) : Set BitStr := {x | (Vof G U x).InClassA n (ansBound G x n)}

/-- **The class `B` at level `n`**: the strings whose verifier is `n`-bounded and whose `n`-th
game has quantum value at most `1/2`. -/
def classB (n : ℕ) : Set BitStr := {x | (Vof G U x).InClassB n (ansBound G x n)}

theorem mem_classA_iff {n : ℕ} {x : BitStr} :
    x ∈ classA G U n ↔ (Vof G U x).InClassA n (ansBound G x n) := Iff.rfl

theorem mem_classB_iff {n : ℕ} {x : BitStr} :
    x ∈ classB G U n ↔ (Vof G U x).InClassB n (ansBound G x n) := Iff.rfl

/-- The two classes are disjoint at every level: a perfect PCC strategy gives `val* = 1`. -/
theorem notMem_classB_of_mem_classA {n : ℕ} {x : BitStr} (h : x ∈ classA G U n) :
    x ∉ classB G U n :=
  (Vof G U x).not_inClassB_of_inClassA h

/-! ## The tabulation of the verifier a string denotes

`tab x n` is the `GameData` for `(Vof G U x)`'s `n`-th game, and it is computable because it
is `Tabulate`'s `tabOf` — a function of two encoded programs and five numbers — fed what the
string and the level supply: the two programs, the sampler's dimension, the answer cut
`ansBound G x n`, and that same `ansBound` with `G.deg` as the budget of the sampler runs.
Two of the seven take work:

* `sampData x`, the encoded sampler program, is `G.samplerProg (descLam x)` encoded. A
  `PolyTimeFun` is not a Mathlib-computable function of its argument in any direct sense; what
  makes this go through is that it is run by the ambient machine on an encoded input
  (`Cost.PolyTimeFun.computable_encode_comp`).
* `decProgData x`, the encoded decider program, is the *wrapper* around the string's own
  decider (`Decider.wrap`, through `Verifier.ofSamplerDecider`). Encoding it means building
  `Cost.Prog.wrapCore`'s syntax tree directly in `Data` (`Cost.Prog.ProgD.dWrapCore`), because
  `Prog` is not a `Primcodable` and so no `Primrec` statement can mention it. The string's
  decider arrives through `Cost.progNorm`, which is `descDec` read off the data and re-encoded
  — the same program, in the normal form a `Primrec` proof can reach.

The three bridges at the end — `accOf_iff`, `dimOf_eq`, `margOf_eq` — are what the rest of O2
rests on: the tabulated numbers *are* the verifier's own sampler and decider. `dimOf_eq` and
`margOf_eq` say so at every string and every level, their budget being the compressed
sampler's own (`sampler_timeBound`, from `GapCompression.sampler_time`); `accOf_iff` says so
on an `n`-bounded verifier, whose budget is the only one the string's own decider has.
-/

/-- The encoded sampler program of the verifier a string denotes. -/
def sampData (x : BitStr) : Data := encode (G.samplerProg (descLam x))

/-- The encoded decider program of the verifier a string denotes: the question-length wrapper
around the string's decider, built in `Data` rather than in `Prog`. -/
noncomputable def decProgData (x : BitStr) : Data :=
  Prog.ProgD.dWrapCore (encode U.univ) (sampData G x) (progNorm (Data.parse x).right)

/-! The two concrete instantiations of `Tabulate`'s generic `Primrec` statements. `s` and `B`
are paired so that `n` stays at the depth it has in the tuple today: that is what keeps this
one instantiation cheap, and what lets `tabOf`'s argument list grow without re-running the
expensive `primrec_accOf`. -/

theorem primrec_dimOf_tuple (k : ℕ) :
    Primrec fun q : (Data × ℕ) × ℕ => dimOf q.1.1 q.2 k q.1.2 :=
  primrec_dimOf k (Primrec.fst.comp Primrec.fst) Primrec.snd (Primrec.snd.comp Primrec.fst)

theorem primrec_tabOf_tuple (k : ℕ) :
    Primrec fun q : (Data × Data) × (ℕ × ℕ) × ℕ × ℕ =>
      tabOf q.1.1 q.1.2 q.2.1.1 q.2.2.1 q.2.1.2 k q.2.2.2 :=
  primrec_tabOf k (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

/-- **The tabulation of `(Vof G U x)`'s `n`-th game**, doubled and re-budgeted.  The sampler
runs under the budget the *compressed sampler's own* time bound supplies — coefficient
`ansBound G x n = G.bound.eval (n + descLam x)`, degree `G.deg` — neither of which needs
`(Vof G U x).IsBounded n`. -/
noncomputable def tab (x : BitStr) (n : ℕ) : GameData :=
  tabOf (sampData G x) (decProgData G U x)
    (dimOf (sampData G x) (ansBound G x n) G.deg n) (ansBound G x n) (ansBound G x n) G.deg n

/-! ### The tabulation is computable -/

theorem primrec_descLam : Primrec descLam :=
  Data.primrec_natOf.comp (Data.primrec_left.comp Data.primrec_parse)

theorem computable_sampData : Computable fun x : BitStr => sampData G x :=
  PolyTimeFun.computable_encode_comp G.samplerProg descLam
    (Data.primrec_encode_nat.comp primrec_descLam).to_comp

theorem computable_decProgData : Computable fun x : BitStr => decProgData G U x :=
  (Prog.ProgD.primrec_dWrapCore (encode U.univ)).to_comp.comp (computable_sampData G)
    (primrec_progNorm.comp (Data.primrec_right.comp Data.primrec_parse)).to_comp

theorem computable_ansBound : Computable fun p : BitStr × ℕ => ansBound G p.1 p.2 :=
  ((primrec_poly_eval G.bound).comp
    (Primrec.nat_add.comp Primrec.snd (primrec_descLam.comp Primrec.fst))).to_comp

/-! The seven arguments of `tabOf` are assembled one declaration at a time. Inlining them into
a single term is not a stylistic choice: the tuple is nested four deep and elaborating it in
one go does not terminate within any heartbeat budget worth setting. -/

theorem computable_sampData_fst : Computable fun p : BitStr × ℕ => sampData G p.1 :=
  (computable_sampData G).comp Computable.fst

theorem computable_decProgData_fst : Computable fun p : BitStr × ℕ => decProgData G U p.1 :=
  (computable_decProgData G U).comp Computable.fst

theorem computable_dimOf_fst : Computable fun p : BitStr × ℕ =>
    dimOf (sampData G p.1) (ansBound G p.1 p.2) G.deg p.2 :=
  ((primrec_dimOf_tuple G.deg).to_comp.comp
    (((computable_sampData_fst G).pair Computable.snd).pair (computable_ansBound G))).of_eq
    fun _ => rfl

theorem computable_tabArgs : Computable fun p : BitStr × ℕ =>
    ((sampData G p.1, decProgData G U p.1),
      ((dimOf (sampData G p.1) (ansBound G p.1 p.2) G.deg p.2, ansBound G p.1 p.2),
        (ansBound G p.1 p.2, p.2))) :=
  ((computable_sampData_fst G).pair (computable_decProgData_fst G U)).pair
    (((computable_dimOf_fst G).pair (computable_ansBound G)).pair
      ((computable_ansBound G).pair Computable.snd))

/-- **O2, computability.** -/
theorem tab_computable : Computable fun p : BitStr × ℕ => tab G U p.1 p.2 :=
  ((primrec_tabOf_tuple G.deg).to_comp.comp (computable_tabArgs G U)).of_eq fun _ => rfl

/-! ### The tabulated numbers are the verifier's own

`sampData_eq` and `decProgData_eq` only unfold the two encodings, and hold at every `n`. The
other three — `accOf_iff`, `dimOf_eq`, `margOf_eq` — are the same shape: rewrite the budgeted
run into `CL.Sampler.queryUnder` or `Verifier.accepts_iff_runForD`, which a time bound then
evaluates. Which bound differs, and that is the point of the re-budget. The two sampler runs
take `sampler_timeBound` — `GapCompression.sampler_time` at the string's own parameter, a
bound at *every* index — so `dimOf_eq` and `margOf_eq` carry no hypothesis. `accOf_iff` has
only `IsBounded n` to draw on, and `IsBounded.two_le` supplies the `2 ≤ n` it needs — see the
warning there: at `n = 0, 1` the time clauses say nothing and no budget exists. -/

theorem sampData_eq (x : BitStr) : sampData G x = encode ((G.sampler (descLam x)).prog) := by
  rw [sampData, G.samplerProg_eq]

theorem decProgData_eq (x : BitStr) : decProgData G U x = encode ((Vof G U x).decider.prog) := by
  rw [decProgData, sampData_eq, progNorm_eq, Prog.ProgD.dWrapCore_eq]
  rfl

/-- The tabulated acceptance test **is** the verifier's acceptance, on an `n`-bounded
verifier. -/
theorem accOf_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) (x' y' a b : BitStr) :
    accOf (decProgData G U x) n x' y' a b = true ↔
      (Vof G U x).decider.Accepts n x' y' a b := by
  rw [accOf, decide_eq_true_iff, decProgData_eq,
    ← (Vof G U x).accepts_iff_runForD hb hb.two_le x' y' a b]

/-- The sampler's time bound at the string's own compression parameter, with no hypothesis. -/
theorem sampler_timeBound (x : BitStr) (n : ℕ) :
    (G.sampler (descLam x)).TimeBoundAt n (ansBound G x n) G.deg :=
  G.sampler_time (descLam x) n

/-- **The tabulated dimension is the sampler's, at every string and every level** — `n = 0`
and `n = 1` included, which the `n ^ n` budget could never reach. -/
theorem dimOf_eq (x : BitStr) (n : ℕ) :
    dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n := by
  have hS := sampler_timeBound G x n
  rw [dimOf, sampData_eq,
    show Machine.runForD (encode ((G.sampler (descLam x)).prog))
        (encode (n, CL.Sampler.Query.dimension))
        (ansBound G x n * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg)
      = (G.sampler (descLam x)).queryUnder (ansBound G x n) G.deg n CL.Sampler.Query.dimension
      from rfl,
    (G.sampler (descLam x)).queryUnder_dimension hS]
  simp [SizedEncoding.decode_encode]
  rfl

/-- **The tabulated marginal is the sampler's, at every string and every level.**  The only
remaining hypothesis is the length condition on the point, which is not a boundedness one. -/
theorem margOf_eq (x : BitStr) (n : ℕ) (w : Player) (z : BitStr)
    (hz : z.length = (Vof G U x).sampler.dim n) :
    margOf (sampData G x) (ansBound G x n) G.deg n w z
      = CL.toBits (((Vof G U x).sampler.cl n w).eval
          (CL.ofBits ((Vof G U x).sampler.dim n) z)) := by
  have hS := sampler_timeBound G x n
  rw [margOf, sampData_eq,
    show Machine.runForD (encode ((G.sampler (descLam x)).prog))
        (encode (n, CL.Sampler.Query.marginal w 7 z))
        (ansBound G x n * ((encode (CL.Sampler.Query.marginal w 7 z) : Data).size + 1) ^ G.deg)
      = (G.sampler (descLam x)).queryUnder (ansBound G x n) G.deg n
          (CL.Sampler.Query.marginal w 7 z) from rfl,
    (G.sampler (descLam x)).queryUnder_marginal hS (by norm_num) w z hz]
  simp [SizedEncoding.decode_encode]
  rfl

/-! ## The tabulation matches the verifier, doubled

What remains is the dictionary between the two namings of each alphabet. A `GameData` names
its questions `Fin (nX + 1)` and its answers `Fin (nA + 1)`; the doubled game names them
`Bool × 𝔽₂^{s(n)}` and the bit strings of length at most `T`. `Verifier.tagEquiv` and
`Verifier.answerEquiv` are the two bijections, and `eXof`/`eAof` are them transported across
the arithmetic of `tab`'s two sizes (`tab_nX`, `tab_nA`) — `nX + 1 = 2 ^ (s(n) + 1)`, the
extra bit being the tag.

The two clauses are then separate pieces of work. The `μ` clause (`mu_clause`) is a counting
argument: the tabulated weight of a question pair is the number of points of `𝔽₂^{s(n)}` whose
two tagged marginals land on it, and the total weight is still `2 ^ s(n)`, which is exactly
the quotient `CL.clDist` is — the weight list enumerates `𝔽₂^{s(n)}` once, not the strings of
length `s(n) + 1`. The `D` clause is the acceptance table read back (`acc_mem_iff`), and the
one place where the two notions of game differ has stopped costing anything: a `GameData`
rejects unequal answers to equal questions by construction, and the doubled game puts no
weight there and rejects there too, so `tab_match` is a *total* match and needs nothing of the
decider beyond `n`-boundedness.
-/

theorem tab_nX (x : BitStr) (n : ℕ) :
    (tab G U x n).nX + 1 = 2 ^ ((Vof G U x).sampler.dim n + 1) := by
  show 2 ^ (dimOf (sampData G x) (ansBound G x n) G.deg n + 1) - 1 + 1 = _
  rw [dimOf_eq G U x n]
  exact Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)

theorem tab_nA (x : BitStr) (n : ℕ) :
    (tab G U x n).nA + 1 = (Verifier.answerList (ansBound G x n)).length := by
  show (Data.bitStrsLE (ansBound G x n)).length - 1 + 1 = _
  rw [Verifier.answerList, List.length_map]
  exact Nat.succ_pred_eq_of_pos (Data.length_bitStrsLE_pos _)

/-- The question relabeling: a tabulated question index is a *tag* and a point of `𝔽₂^{s(n)}`. -/
noncomputable def eXof (x : BitStr) (n : ℕ) :
    Fin ((tab G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n :=
  (finCongr (tab_nX G U x n)).trans (Verifier.tagEquiv _).symm

/-- The answer relabeling: a tabulated answer index is a bit string of length at most the
answer bound. Only the questions are doubled, so this is unchanged by it. -/
noncomputable def eAof (x : BitStr) (n : ℕ) :
    Fin ((tab G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n) :=
  (finCongr (tab_nA G U x n)).trans (Verifier.answerEquiv _)

theorem eXof_apply (x : BitStr) (n : ℕ)
    (i : Fin ((tab G U x n).nX + 1)) :
    Verifier.bitsToIdx ((eXof G U x n i).1 :: CL.toBits (eXof G U x n i).2) = (i : ℕ) := by
  rw [eXof, Equiv.trans_apply, Verifier.bitsToIdx_tagEquiv_symm]
  simp

theorem eAof_apply (x : BitStr) (n : ℕ) (k : Fin ((tab G U x n).nA + 1)) :
    (Data.bitStrsLE (ansBound G x n)).idxOf (eAof G U x n k).1 = (k : ℕ) := by
  rw [← Verifier.answerEquiv_symm_val, eAof]
  simp

/-- The dictionary the `μ` clause runs on, with the tag: a tagged marginal lands on the index
`i` exactly when the tag is `i`'s tag and the verifier's own marginal is `i`'s point. -/
theorem marg_idx_eq (x : BitStr) (n : ℕ) (w : Player)
    (tg : Bool) (z : BitStr) (hz : z.length = (Vof G U x).sampler.dim n)
    (i : Fin ((tab G U x n).nX + 1)) :
    Verifier.bitsToIdx (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z) = (i : ℕ)
      ↔ (tg = (eXof G U x n i).1 ∧
          ((Vof G U x).sampler.cl n w).eval (CL.ofBits ((Vof G U x).sampler.dim n) z)
            = (eXof G U x n i).2) := by
  rw [margOf_eq G U x n w z hz, ← eXof_apply G U x n i,
    Verifier.bitsToIdx_cons_toBits_eq_iff]

/-- **The `μ` clause, doubled.** The tabulated distribution is the sampler's on the block
`(false, ·) × (true, ·)` and zero everywhere else — which is exactly the doubled game's. -/
theorem mu_clause (x : BitStr) (n : ℕ)
    (i j : Fin ((tab G U x n).nX + 1)) :
    (tab G U x n).game.μ i j
      = ((Vof G U x).doubledGame n (ansBound G x n)).μ
          (eXof G U x n i) (eXof G U x n j) := by
  classical
  have hdim : dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n := dimOf_eq G U x n
  have hlen : ∀ (w : Player) (z : BitStr), z.length = (Vof G U x).sampler.dim n →
      (margOf (sampData G x) (ansBound G x n) G.deg n w z).length = (Vof G U x).sampler.dim n := by
    intro w z hz
    rw [margOf_eq G U x n w z hz, CL.length_toBits]
  have hmem : ∀ z ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n),
      z.length = (Vof G U x).sampler.dim n := by
    intro z hz
    rw [← hdim]; exact (Data.mem_bitStrsOfLen _ _).1 hz
  have hrange : ∀ (tg : Bool) (w : Player),
      ∀ z ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n),
        Verifier.bitsToIdx (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z) < (tab G U x n).nX + 1 := by
    intro tg w z hz
    have hlt := Verifier.bitsToIdx_lt (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z)
    rw [List.length_cons, hlen w z (hmem z hz)] at hlt
    rw [tab_nX G U x n]
    exact hlt
  have htot : (tab G U x n).totalWeight = 2 ^ dimOf (sampData G x) (ansBound G x n) G.deg n :=
    Verifier.totalWeight_weightList _ _ _ _ _ _ (hrange false .alice) (hrange true .bob)
  have hqw : ∀ a b : ℕ, (tab G U x n).questionWeight a b
      = ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter fun z =>
          decide (Verifier.bitsToIdx (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = a
            ∧ Verifier.bitsToIdx (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = b)).length :=
    fun a b => Verifier.questionWeight_weightList _ _ _ _ _ _ a b
  rw [GameData.game_μ, htot, if_neg (Nat.two_pow_pos _).ne', hqw,
    show ((Vof G U x).doubledGame n (ansBound G x n)).μ
        (eXof G U x n i) (eXof G U x n j)
      = if (eXof G U x n i).1 = false ∧ (eXof G U x n j).1 = true then
          (Vof G U x).sampler.dist n (eXof G U x n i).2 (eXof G U x n j).2 else 0 from rfl]
  by_cases htag : (eXof G U x n i).1 = false ∧ (eXof G U x n j).1 = true
  · rw [if_pos htag]
    have hnum : ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter fun z =>
          decide (Verifier.bitsToIdx (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
            ∧ Verifier.bitsToIdx (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ))).length
        = (Finset.univ.filter fun v : (Vof G U x).Questions n =>
            ((Vof G U x).sampler.cl n .alice).eval v = (eXof G U x n i).2
              ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXof G U x n j).2).card := by
      rw [hdim]
      rw [show ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
          decide (Verifier.bitsToIdx (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
            ∧ Verifier.bitsToIdx (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ)))
          = ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
            (fun v : (Vof G U x).Questions n =>
              decide (((Vof G U x).sampler.cl n .alice).eval v = (eXof G U x n i).2
                ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXof G U x n j).2))
              (CL.ofBits ((Vof G U x).sampler.dim n) z)) from ?_]
      · rw [Verifier.length_filter_bitStrsOfLen (s := (Vof G U x).sampler.dim n)
          (fun v => decide (((Vof G U x).sampler.cl n .alice).eval v = (eXof G U x n i).2
            ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXof G U x n j).2))]
        congr 1
        ext v
        simp
      · refine List.filter_congr fun z hz => ?_
        have hz' : z.length = (Vof G U x).sampler.dim n :=
          (Data.mem_bitStrsOfLen _ _).1 hz
        simp only [decide_eq_decide]
        rw [marg_idx_eq G U x n .alice false z hz' i,
          marg_idx_eq G U x n .bob true z hz' j, htag.1, htag.2]
        simp
    rw [hnum,
      show (Vof G U x).sampler.dist n (eXof G U x n i).2 (eXof G U x n j).2
        = ((Finset.univ.filter fun v : (Vof G U x).Questions n =>
            ((Vof G U x).sampler.cl n .alice).eval v = (eXof G U x n i).2
              ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXof G U x n j).2).card : ℝ)
          / (Fintype.card ((Vof G U x).Questions n) : ℝ) from rfl]
    congr 1
    rw [hdim]
    simp [Verifier.Questions]
  · rw [if_neg htag]
    have hnil : ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter fun z =>
        decide (Verifier.bitsToIdx (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
          ∧ Verifier.bitsToIdx (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ))) = [] := by
      refine List.filter_eq_nil_iff.2 fun z hz => ?_
      simp only [decide_eq_true_eq, not_and]
      intro h1 h2
      exact htag ⟨((marg_idx_eq G U x n .alice false z (hmem z hz) i).1 h1).1.symm,
        ((marg_idx_eq G U x n .bob true z (hmem z hz) j).1 h2).1.symm⟩
    rw [hnil]
    simp

/-- **The acceptance table read back, doubled.** A tuple of indices is in the table exactly
when the tags are Alice's and Bob's *and* the verifier's decider accepts. -/
theorem acc_mem_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (i j : Fin ((tab G U x n).nX + 1)) (k l : Fin ((tab G U x n).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (tab G U x n).acc
      ↔ ((eXof G U x n i).1 = false ∧ (eXof G U x n j).1 = true ∧
          (Vof G U x).decider.Accepts n (CL.toBits (eXof G U x n i).2)
            (CL.toBits (eXof G U x n j).2) (eAof G U x n k).1 (eAof G U x n l).1) := by
  have hdim : dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n := dimOf_eq G U x n
  have hqmem : ∀ (m : Fin ((tab G U x n).nX + 1)),
      CL.toBits (eXof G U x n m).2 ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n) := by
    intro m
    rw [Data.mem_bitStrsOfLen, CL.length_toBits, hdim]
  have hamem : ∀ (m : Fin ((tab G U x n).nA + 1)),
      (eAof G U x n m).1 ∈ Data.bitStrsLE (ansBound G x n) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (eAof G U x n m).2
  rw [show (tab G U x n).acc = Verifier.accListW (dimOf (sampData G x) (ansBound G x n) G.deg n) (ansBound G x n)
      (fun u => Verifier.bitsToIdx (false :: u)) (fun v => Verifier.bitsToIdx (true :: v))
      (accOf (decProgData G U x) n) from rfl, Verifier.mem_accListW_iff]
  constructor
  · rintro ⟨u, hu, v, hv, a, ha, b, hb', hacc, hi, hj, hk, hl⟩
    have hu' : (eXof G U x n i).1 = false ∧ CL.toBits (eXof G U x n i).2 = u :=
      List.cons_eq_cons.mp (Verifier.bitsToIdx_injOn
        (s := (Vof G U x).sampler.dim n + 1) (by simp)
        (by rw [List.length_cons, (Data.mem_bitStrsOfLen _ _).1 hu, hdim])
        (by rw [eXof_apply G U x n i, hi]))
    have hv' : (eXof G U x n j).1 = true ∧ CL.toBits (eXof G U x n j).2 = v :=
      List.cons_eq_cons.mp (Verifier.bitsToIdx_injOn
        (s := (Vof G U x).sampler.dim n + 1) (by simp)
        (by rw [List.length_cons, (Data.mem_bitStrsOfLen _ _).1 hv, hdim])
        (by rw [eXof_apply G U x n j, hj]))
    have ha' : a = (eAof G U x n k).1 := (List.idxOf_inj ha).1 (by rw [← hk, eAof_apply])
    have hb'' : b = (eAof G U x n l).1 := (List.idxOf_inj hb').1 (by rw [← hl, eAof_apply])
    refine ⟨hu'.1, hv'.1, ?_⟩
    rw [hu'.2, hv'.2, ← ha', ← hb'']
    exact (accOf_iff G U x n hb _ _ _ _).1 hacc
  · rintro ⟨ht1, ht2, h⟩
    refine ⟨_, hqmem i, _, hqmem j, _, hamem k, _, hamem l,
      (accOf_iff G U x n hb _ _ _ _).2 h, ?_, ?_,
      (eAof_apply G U x n k).symm, (eAof_apply G U x n l).symm⟩
    · rw [← ht1, eXof_apply G U x n i]
    · rw [← ht2, eXof_apply G U x n j]

/-- **O2, the match — doubled, and with no synchronicity hypothesis.** On an `n`-bounded
verifier the doubled tabulation matches the *doubled* game of `𝒱_n` along `eXof` and `eAof`.
The forced rejections of a `GameData` sit on the diagonal, which the doubled distribution
avoids; and the doubled game rejects off the tag block, which is what the table omits. -/
theorem tab_match (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    ∃ (eX : Fin ((tab G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n)
      (eA : Fin ((tab G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n)),
      (∀ i j, (tab G U x n).game.μ i j
        = ((Vof G U x).doubledGame n (ansBound G x n)).μ (eX i) (eX j)) ∧
      (∀ i j k l, (tab G U x n).game.D i j k l
        = ((Vof G U x).doubledGame n (ansBound G x n)).D (eX i) (eX j) (eA k) (eA l)) := by
  classical
  refine ⟨eXof G U x n, eAof G U x n, mu_clause G U x n, fun i j k l => ?_⟩
  refine Bool.eq_iff_iff.2 ?_
  rw [GameData.game_D,
    show ((Vof G U x).doubledGame n (ansBound G x n)).D
        (eXof G U x n i) (eXof G U x n j) (eAof G U x n k) (eAof G U x n l)
      = if (eXof G U x n i).1 = false ∧ (eXof G U x n j).1 = true then
          ((Vof G U x).game n (ansBound G x n)).D (eXof G U x n i).2
            (eXof G U x n j).2 (eAof G U x n k) (eAof G U x n l) else false from rfl]
  by_cases hc : i = j ∧ k ≠ l
  · rw [if_pos hc, if_neg (by rw [hc.1]; exact fun h => by simp_all)]
  · rw [if_neg hc, decide_eq_true_iff, acc_mem_iff G U x n hb]
    by_cases ht : (eXof G U x n i).1 = false ∧ (eXof G U x n j).1 = true
    · rw [if_pos ht]
      show _ ↔ (decide ((Vof G U x).decider.Accepts n _ _ _ _) = true)
      rw [decide_eq_true_iff]
      exact ⟨fun h => h.2.2, fun h => ⟨ht.1, ht.2, h⟩⟩
    · rw [if_neg ht]
      simp only [Bool.false_eq_true, iff_false]
      exact fun h => ht ⟨h.1, h.2.1⟩

/-- **O2, the value — doubled**: the tabulated game has the value of `𝒱_n` at *every*
`n`-bounded string, with no synchronicity hypothesis. This is `Halting.exists_sem_of_tab`'s
`hval`. -/
theorem tab_value (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    quantumValue (tab G U x n).game = (Vof G U x).valStar n (ansBound G x n) := by
  obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U x n hb
  exact Verifier.quantumValue_toGame_eq_valStar_doubled _ _ _ _ eX eA hμ hD

/-- The completeness branch, in the value of `HaltingGameValue`. -/
theorem gameValue_tab_eq_one (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (hV : (Vof G U x).HasPerfectPCC n (ansBound G x n)) :
    HaltingGameValue.gameValue (tab G U x n).toGame = 1 := by
  obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U x n hb
  exact Verifier.gameValue_toGame_eq_one_doubled _ _ _ _ eX eA hμ hD hV

end MIPRE.Halting
