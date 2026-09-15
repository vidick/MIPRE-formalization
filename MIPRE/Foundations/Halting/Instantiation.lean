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

## What is proved and what is assumed

`halting_reduction` is complete: no `sorry`, and its only hypotheses are a `GapCompression`,
a `UniversalMachine` (`exists_efficient_universal` provides one) and an `Obligations`
structure. The remaining pieces of work are exactly the fields of `Obligations`, so that what
is open can be enumerated rather than searched for:

* **O1** (`yYes`, `yYes_mem`, `yNo`, `yNo_mem`) — the two distinguished strings. The
  verifier-level statements are `Verifier.inClassA_of_accepts_diagonal` and
  `inClassB_of_rejects_all`; what is owed is the wrapper's time bound, hence the two concrete
  decider programs realizing them.
* **O2** — **done**, and so no longer a field of `Obligations`. The tabulation of `𝒱_n` as a
  game description matching it along relabelings of the two alphabets is `tab`,
  `tab_computable`, `tab_match`, `tab_value` and `gameValue_tab_eq_one` in the section above,
  which `halting_reduction` uses directly; the relabelings are `Verifier.tagEquiv` and
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
* **O3** (`sem`, `sem_closed`, `sem_spec`) — a program halting on `(x, n)` exactly off
  `classB n`. Its shape is `Verifier.not_inClassB_iff`: a boundedness violation, or the
  `val*` half of `lem:value-lower-approx` on a tabulation. Both disjuncts are proved
  recursively enumerable in `Halting/Semidecider.lean`
  (`Verifier.rePred_not_isBounded`, `MIPRE.rePred_lt_quantumValue_comp`), merged there by
  dovetailing and turned into a program by `Cost.exists_semidecider_prod_nat`. The two
  hypotheses of `Halting.exists_sem_of_tab` were O2's and are now discharged — the computable
  presentation of the family `Vof` (`Verifier.ComputablyPresented`) by
  `Halting.computablyPresented_Vof`, the computable tabulation of the right value by
  `tab_computable` and `tab_value` — so `Halting.exists_sem` proves all three fields with no
  hypotheses. They remain fields here only because `Halting/Semidecider.lean` imports this
  file; removing them is a module move rather than mathematics.
* **O4** (`compr`, `compr_spec`) — the compressor: the decider that reads its description by
  bit queries, freezes the verifier at index `2n + 1` (`Verifier.freeze`), runs `Compress`,
  and its time accounting.

O4 is the substance that is left, and `planning/h4-assembly.md` has the order of work. O3 was
recorded there as "O2 plus a disjunction"; it is not, and the reason is worth naming.
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

## What this is not

`halting_reduction` concludes in `val*`: the quantum value of the game is `1`, respectively at
most `1/2`. The blueprint's item 1 says more — the witness is a value-`1` *PCC* strategy, so
`synval = val* = 1` — and the headline `HaltingGameValue.halting_reduces_to_gameValue` is
stated in `synval`. The two steps that carry the conclusion there are in Lean and neither is
part of this assembly: a synchronous strategy transports along a relabeling of the alphabets
(`MIPRE.syncValue_eq_of_equiv`), and `MIPRE.syncValue` and `HaltingGameValue.gameValue` are the
same number on the same description (`HaltingGameValue.GameData.gameValue_eq_syncValue`).
`MIPRE.Verifier.gameValue_toGame_eq_one` is the two composed, in `Foundations/SyncTransport.lean`.

Both take the tabulation's agreement with `𝒱_n` as the *matching data* — the two alphabet
equivalences with `hμ` and `hD` — rather than the equality of `val*` it implies, which is why
`tab_match` has the shape it has. The soundness half needs neither step, only
`synval ≤ val*` (`MIPRE.syncValue_le_quantumValue`, blueprint `lem:sync-le-valstar`);
`Verifier.gameValue_toGame_le_of_valStar_le` is it in that vocabulary.

So what stands between `halting_reduction` and the headline is an inhabitant of `Obligations`
and nothing else.
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

/-! ## The obligations -/

/-- **What the halting reduction still owes.** Each field is a piece of work identified in
blueprint `rem:compression-abstract` and tracked in `planning/h4-assembly.md`; nothing else is
assumed, and `halting_reduction` below is proved outright from an inhabitant of this
structure. The grouping is O1 (the two distinguished strings), O3 (the semidecider) and O4
(the compressor); O2, the tabulation, is discharged above and is not a field here. -/
structure Obligations (G : GapCompression) (U : UniversalMachine) where
  /-- The level above which the guarantees hold. -/
  n₀ : ℕ
  /-- **O1.** A string in the class `A` at every level above `n₀`: a verifier that accepts one
  fixed answer on every question pair (`Verifier.inClassA_of_accepts_diagonal`). -/
  yYes : BitStr
  yYes_mem : ∀ n, n₀ ≤ n → yYes ∈ classA G U n
  /-- **O1.** A string in the class `B` at every level above `n₀`: a verifier that accepts
  nothing (`Verifier.inClassB_of_rejects_all`). -/
  yNo : BitStr
  yNo_mem : ∀ n, n₀ ≤ n → yNo ∈ classB G U n
  /-- **O3.** A semidecider for the complement of `B`: a closed program halting on `(x, n)`
  exactly when `x` is not in the class `B` at level `n` (`Verifier.not_inClassB_iff`,
  `Halting.exists_sem_of_tab`). Note that this field precedes `tab`, so `sem_spec` cannot
  mention the tabulation; the tabulation enters through the theorem that inhabits the field,
  not through its statement. -/
  sem : Prog
  sem_closed : sem.WellScoped 1
  sem_spec : ∀ (x : BitStr) (n : ℕ), Halts sem (encode (x, n)) ↔ x ∉ classB G U n
  /-- **O4.** The compressor: a polynomial-time map on `(description, level)` pairs. -/
  compr : PolyTimeFun (Prog × ℕ) BitStr
  /-- **O4.** On a succinct description of a string at level `2n + 1`, with the size slack the
  criterion provides, the compressor preserves both classes down to level `n`. -/
  compr_spec : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x →
      (x ∈ classA G U (2 * n + 1) → compr (c, n) ∈ classA G U n) ∧
      (x ∈ classB G U (2 * n + 1) → compr (c, n) ∈ classB G U n)

/-! ## The reduction -/

/-- `2 ^ ·` is primitive recursive: the level at which the recursion of the criterion runs is
`2 ^ (K + 1 + esize e)`, and the reduction has to compute it. -/
private theorem two_pow_iterate (n : ℕ) : (fun b : ℕ => 2 * b)^[n] 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring

private theorem primrec_two_pow : Primrec fun n : ℕ => 2 ^ n :=
  (Primrec.nat_iterate Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂).of_eq fun n => two_pow_iterate n

-- The tabulation is opaque from here on. `halting_reduction` only ever feeds it to
-- `tab_computable` and `tab_value` (once as an equality, once through `.le`); letting
-- unification unfold it into `tabOf` and the two budgeted runs instead costs more heartbeats
-- than any budget worth setting.
attribute [local irreducible] tab

/-- **The halting reduction** (blueprint `thm:halting`), in `val*` form: from gap-preserving
compression, the tabulation above and the remaining obligations, a computable map from
`Nat.Partrec.Code` to game descriptions whose game has quantum value `1` when the machine halts
on the empty input and at most `1/2` when it does not.

The proof is the per-level compressibility criterion at the classes `classA`, `classB`,
followed by the value agreement of the tabulation: the criterion produces a description at
level `2 ^ (K + 1 + esize e)` lying in `A` or in `B` according to whether `e` halts, a value-`1`
PCC strategy gives `val* = 1` (`Verifier.valStar_eq_one_of_hasPerfectPCC`), and `tab_value`
carries both verdicts to the tabulated game — the same equality in both branches, the
doubled question set having removed the synchronicity hypothesis that once split them. -/
theorem halting_reduction (O : Obligations G U) :
    ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → quantumValue (g pc).game = 1) ∧
        (¬ (pc.eval 0).Dom → quantumValue (g pc).game ≤ 1 / 2) := by
  obtain ⟨g, K, hg⟩ := Cost.compressibility_criterion_levels
    (classA G U) (classB G U) O.n₀ O.yYes O.yYes_mem O.yNo O.yNo_mem
    O.sem O.sem_closed O.sem_spec O.compr O.compr_spec
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  have hsize : Computable fun pc : Nat.Partrec.Code => esize (compile pc) :=
    Data.primrec_size.to_comp.comp hc
  have hlevel : Computable fun pc : Nat.Partrec.Code => 2 ^ (K + 1 + esize (compile pc)) :=
    (primrec_two_pow.comp (Primrec.nat_add.comp (Primrec.const (K + 1)) Primrec.id)).to_comp.comp
      hsize
  refine ⟨fun pc => tab G U (g (compile pc)) (2 ^ (K + 1 + esize (compile pc))),
    (tab_computable G U).comp
      ((PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp).pair hlevel),
    fun pc => ⟨fun hdom => ?_, fun hdom => ?_⟩⟩
  · have hx := (hg (compile pc)).2.1 ((hspec pc).2 hdom)
    rw [tab_value G U _ _ hx.1, (Vof G U _).valStar_eq_one_of_hasPerfectPCC hx.2]
  · have hx := (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)
    exact (tab_value G U _ _ hx.1).le.trans hx.2

end MIPRE.Halting
