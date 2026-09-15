/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Enumerate
import MIPRE.Foundations.Halting.Tabulate
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
  `tab_computable`, `tab_match`, `tab_le` and `tab_value` in the section above, which
  `halting_reduction` uses directly; the relabelings are `Verifier.questionEquiv` and
  `answerEquiv`, transported across the two sizes. Three features of their shape are
  deliberate and each is explained where it is stated: they hold only of an `n`-bounded
  verifier, and could not hold of every string, acceptance being `Σ₁`; `tab_match` delivers
  the relabelings rather than only the value they equate, because `synval ≤ val*` points the
  wrong way for item 1 of `thm:halting`; and the match itself is asked only of a verifier
  synchronous at `n`, a `GameData` describing a synchronous game by construction, with
  `tab_le` carrying the soundness branch instead. That last one is the piece O3 cannot use as
  it stands, and the paragraph below the list says what is owed.
* **O3** (`sem`, `sem_closed`, `sem_spec`) — a program halting on `(x, n)` exactly off
  `classB n`. Its shape is `Verifier.not_inClassB_iff`: a boundedness violation, or the
  `val*` half of `lem:value-lower-approx` on a tabulation. Both disjuncts are proved
  recursively enumerable in `Halting/Semidecider.lean`
  (`Verifier.rePred_not_isBounded`, `MIPRE.rePred_lt_quantumValue_comp`), merged there by
  dovetailing and turned into a program by `Cost.exists_semidecider_prod_nat`; what
  `Halting.exists_sem_of_tab` still takes as hypotheses is a computable presentation of the
  family `Vof` (`Verifier.ComputablyPresented`) and a computable tabulation, both of which
  are O2's.
* **O4** (`compr`, `compr_spec`) — the compressor: the decider that reads its description by
  bit queries, freezes the verifier at index `2n + 1` (`Verifier.freeze`), runs `Compress`,
  and its time accounting.

O2 and O4 are the substance, and `planning/h4-assembly.md` has the order of work. O3 was
recorded there as "O2 plus a disjunction"; it is not, and the reason is worth naming.
`Halting.exists_sem_of_tab` needs the tabulation to have the value of `𝒱_n` at every
`n`-bounded string, in both directions, because `sem_spec` is an equivalence — while
`tab_match` gives that only where the verifier is also *synchronous* at `n`, a `GameData`
describing a synchronous game by construction (see `tab_le`), and `classB n` does not ask
for synchronicity. So the two do not compose as they stand. Three repairs are on the
record in blueprint `lem:halting-semidecider`: tabulate on a doubled question set so that
the distribution avoids the diagonal, make `Decider.wrap` reject unequal answers to equal
questions so that every string names a synchronous verifier, or put synchronicity into
`classB` and pay for it in `compr_spec`. The first is the cheapest and is the tabulation's
to make; until it is made, `tab_value` is the conditional statement below and
`exists_sem_of_tab`'s `hval` is not yet in hand.

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
is `Tabulate`'s `tabOf` — a function of five *numbers* — fed the three the string supplies.
Two of them take work:

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
rests on: on an `n`-bounded verifier the tabulated numbers *are* the verifier's own sampler
and decider, budget or no budget.
-/

/-- The encoded sampler program of the verifier a string denotes. -/
def sampData (x : BitStr) : Data := encode (G.samplerProg (descLam x))

/-- The encoded decider program of the verifier a string denotes: the question-length wrapper
around the string's decider, built in `Data` rather than in `Prog`. -/
noncomputable def decProgData (x : BitStr) : Data :=
  Prog.ProgD.dWrapCore (encode U.univ) (sampData G x) (progNorm (Data.parse x).right)

/-- **The tabulation of `(Vof G U x)`'s `n`-th game.** -/
noncomputable def tab (x : BitStr) (n : ℕ) : GameData :=
  tabOf (sampData G x) (decProgData G U x) (dimOf (sampData G x) n) (ansBound G x n) n

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

/-! The five arguments of `tabOf` are assembled one declaration at a time. Inlining them into a
single term is not a stylistic choice: the tuple is nested four deep and elaborating it in one
go does not terminate within any heartbeat budget worth setting. -/

theorem computable_sampData_fst : Computable fun p : BitStr × ℕ => sampData G p.1 :=
  (computable_sampData G).comp Computable.fst

theorem computable_decProgData_fst : Computable fun p : BitStr × ℕ => decProgData G U p.1 :=
  (computable_decProgData G U).comp Computable.fst

theorem computable_dimOf_fst : Computable fun p : BitStr × ℕ => dimOf (sampData G p.1) p.2 :=
  (primrec_dimOf.to_comp.comp ((computable_sampData_fst G).pair Computable.snd)).of_eq fun _ => rfl

theorem computable_tabArgs : Computable fun p : BitStr × ℕ =>
    ((sampData G p.1, decProgData G U p.1),
      (dimOf (sampData G p.1) p.2, ansBound G p.1 p.2, p.2)) :=
  ((computable_sampData_fst G).pair (computable_decProgData_fst G U)).pair
    ((computable_dimOf_fst G).pair ((computable_ansBound G).pair Computable.snd))

/-- **O2, computability.** The tabulation is computable in the string and the level. -/
theorem tab_computable : Computable fun p : BitStr × ℕ => tab G U p.1 p.2 :=
  (primrec_tabOf.to_comp.comp (computable_tabArgs G U)).of_eq fun _ => rfl

/-! ### The tabulated numbers are the verifier's own

`sampData_eq` and `decProgData_eq` only unfold the two encodings, and hold at every `n`. The
other three — `accOf_iff`, `dimOf_eq`, `margOf_eq` — are the same shape: rewrite the budgeted
run into `CL.Sampler.queryUnder` or `Verifier.accepts_iff_runForD`, which `IsBounded` then
evaluates. `IsBounded.two_le` supplies the `2 ≤ n` those need — see the warning there: at
`n = 0, 1` the time clauses say nothing and no budget exists. -/

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

/-- The tabulated dimension **is** the sampler's, on an `n`-bounded verifier. -/
theorem dimOf_eq (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    dimOf (sampData G x) n = (Vof G U x).sampler.dim n := by
  have hS : (G.sampler (descLam x)).TimeBoundAt n (n ^ n) n := (hb.1 n hb.two_le).2.1
  rw [dimOf, sampData_eq,
    show Machine.runForD (encode ((G.sampler (descLam x)).prog))
        (encode (n, CL.Sampler.Query.dimension))
        (n ^ n * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ n)
      = (G.sampler (descLam x)).queryUnder (n ^ n) n n CL.Sampler.Query.dimension from rfl,
    (G.sampler (descLam x)).queryUnder_dimension hS]
  simp [SizedEncoding.decode_encode]
  rfl

/-- The tabulated marginal **is** the sampler's conditional linear function evaluated at the
point, on an `n`-bounded verifier. -/
theorem margOf_eq (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) (w : Player) (z : BitStr)
    (hz : z.length = (Vof G U x).sampler.dim n) :
    margOf (sampData G x) n w z
      = CL.toBits (((Vof G U x).sampler.cl n w).eval
          (CL.ofBits ((Vof G U x).sampler.dim n) z)) := by
  have hS : (G.sampler (descLam x)).TimeBoundAt n (n ^ n) n := (hb.1 n hb.two_le).2.1
  rw [margOf, sampData_eq,
    show Machine.runForD (encode ((G.sampler (descLam x)).prog))
        (encode (n, CL.Sampler.Query.marginal w 7 z))
        (n ^ n * ((encode (CL.Sampler.Query.marginal w 7 z) : Data).size + 1) ^ n)
      = (G.sampler (descLam x)).queryUnder (n ^ n) n n (CL.Sampler.Query.marginal w 7 z) from rfl,
    (G.sampler (descLam x)).queryUnder_marginal hS (by norm_num) w z hz]
  simp [SizedEncoding.decode_encode]
  rfl

/-! ## The tabulation matches the verifier

What remains is the dictionary between the two namings of each alphabet. A `GameData` names
its questions `Fin (nX + 1)` and its answers `Fin (nA + 1)`; the verifier names them
`𝔽₂^{s(n)}` and the bit strings of length at most `T`. `Verifier.questionEquiv` and
`Verifier.answerEquiv` are the two bijections, and `eXof`/`eAof` are them transported across
the arithmetic of `tab`'s two sizes (`tab_nX`, `tab_nA`).

The two clauses are then separate pieces of work. The `μ` clause is a counting argument: the
tabulated weight of a question pair is the number of points of `𝔽₂^{s(n)}` whose two marginals
land on it, and the total weight is `2 ^ s(n)`, which is exactly the quotient `CL.clDist` is.
The `D` clause is the acceptance table read back (`acc_mem_iff`), plus the one place where the
two notions of game differ: a `GameData` rejects unequal answers to equal questions by
construction, which is why `tab_match` asks for synchronicity and `tab_le` settles for an
inequality.
-/

theorem tab_nX (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    (tab G U x n).nX + 1 = 2 ^ ((Vof G U x).sampler.dim n) := by
  show 2 ^ dimOf (sampData G x) n - 1 + 1 = _
  rw [dimOf_eq G U x n hb]
  exact Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)

theorem tab_nA (x : BitStr) (n : ℕ) :
    (tab G U x n).nA + 1 = (Verifier.answerList (ansBound G x n)).length := by
  show (Data.bitStrsLE (ansBound G x n)).length - 1 + 1 = _
  rw [Verifier.answerList, List.length_map]
  exact Nat.succ_pred_eq_of_pos (Data.length_bitStrsLE_pos _)

/-- The question relabeling: a tabulated question index is a point of `𝔽₂^{s(n)}`. -/
noncomputable def eXof (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    Fin ((tab G U x n).nX + 1) ≃ (Vof G U x).Questions n :=
  (finCongr (tab_nX G U x n hb)).trans (Verifier.questionEquiv _)

/-- The answer relabeling: a tabulated answer index is a bit string of length at most the
answer bound. -/
noncomputable def eAof (x : BitStr) (n : ℕ) :
    Fin ((tab G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n) :=
  (finCongr (tab_nA G U x n)).trans (Verifier.answerEquiv _)

theorem eXof_apply (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (i : Fin ((tab G U x n).nX + 1)) :
    Verifier.bitsToIdx (CL.toBits (eXof G U x n hb i)) = (i : ℕ) := by
  rw [eXof]
  simp [Verifier.bitsToIdx_toBits_questionEquiv]

theorem eAof_apply (x : BitStr) (n : ℕ) (k : Fin ((tab G U x n).nA + 1)) :
    (Data.bitStrsLE (ansBound G x n)).idxOf (eAof G U x n k).1 = (k : ℕ) := by
  rw [← Verifier.answerEquiv_symm_val, eAof]
  simp

/-- The dictionary the `μ` clause runs on: a tabulated marginal lands on the index `i` exactly
when the verifier's own marginal lands on the question `eXof i`. -/
theorem marg_idx_eq (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) (w : Player)
    (z : BitStr) (hz : z.length = (Vof G U x).sampler.dim n)
    (i : Fin ((tab G U x n).nX + 1)) :
    Verifier.bitsToIdx (margOf (sampData G x) n w z) = (i : ℕ)
      ↔ ((Vof G U x).sampler.cl n w).eval (CL.ofBits ((Vof G U x).sampler.dim n) z)
          = eXof G U x n hb i := by
  rw [margOf_eq G U x n hb w z hz, ← Verifier.questionEquiv_symm_val, eXof]
  constructor
  · intro h
    have h' : (Verifier.questionEquiv _).symm
        (((Vof G U x).sampler.cl n w).eval (CL.ofBits ((Vof G U x).sampler.dim n) z))
        = finCongr (tab_nX G U x n hb) i := Fin.ext h
    rw [Equiv.trans_apply, ← h', Equiv.apply_symm_apply]
  · intro h
    rw [Equiv.trans_apply] at h
    have h' : (Verifier.questionEquiv ((Vof G U x).sampler.dim n)).symm
        (((Vof G U x).sampler.cl n w).eval (CL.ofBits ((Vof G U x).sampler.dim n) z))
        = finCongr (tab_nX G U x n hb) i := by rw [h, Equiv.symm_apply_apply]
    exact (congrArg Fin.val h').trans (by simp)

/-- **The `μ` clause.** The tabulated distribution is the sampler's, along `eXof`. -/
theorem mu_clause (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (i j : Fin ((tab G U x n).nX + 1)) :
    (tab G U x n).game.μ i j
      = (Vof G U x).sampler.dist n (eXof G U x n hb i) (eXof G U x n hb j) := by
  classical
  have hdim : dimOf (sampData G x) n = (Vof G U x).sampler.dim n := dimOf_eq G U x n hb
  have hlen : ∀ (w : Player) (z : BitStr), z.length = (Vof G U x).sampler.dim n →
      (margOf (sampData G x) n w z).length = (Vof G U x).sampler.dim n := by
    intro w z hz
    rw [margOf_eq G U x n hb w z hz, CL.length_toBits]
  have hrange : ∀ (w : Player), ∀ z ∈ Data.bitStrsOfLen (dimOf (sampData G x) n),
      Verifier.bitsToIdx (margOf (sampData G x) n w z) < (tab G U x n).nX + 1 := by
    intro w z hz
    have hz' : z.length = (Vof G U x).sampler.dim n := by
      rw [← hdim]; exact (Data.mem_bitStrsOfLen _ _).1 hz
    have hlt := Verifier.bitsToIdx_lt (margOf (sampData G x) n w z)
    rw [hlen w z hz'] at hlt
    rw [tab_nX G U x n hb]
    exact hlt
  have htot : (tab G U x n).totalWeight = 2 ^ dimOf (sampData G x) n :=
    Verifier.totalWeight_weightList _ _ _ _ _ _ (hrange .alice) (hrange .bob)
  have hqw : ∀ a b : ℕ, (tab G U x n).questionWeight a b
      = ((Data.bitStrsOfLen (dimOf (sampData G x) n)).filter fun z =>
          decide (Verifier.bitsToIdx (margOf (sampData G x) n .alice z) = a
            ∧ Verifier.bitsToIdx (margOf (sampData G x) n .bob z) = b)).length :=
    fun a b => Verifier.questionWeight_weightList _ _ _ _ _ _ a b
  rw [GameData.game_μ, htot, if_neg (Nat.two_pow_pos _).ne', hqw]
  have hnum : ((Data.bitStrsOfLen (dimOf (sampData G x) n)).filter fun z =>
        decide (Verifier.bitsToIdx (margOf (sampData G x) n .alice z) = (i : ℕ)
          ∧ Verifier.bitsToIdx (margOf (sampData G x) n .bob z) = (j : ℕ))).length
      = (Finset.univ.filter fun v : (Vof G U x).Questions n =>
          ((Vof G U x).sampler.cl n .alice).eval v = eXof G U x n hb i
            ∧ ((Vof G U x).sampler.cl n .bob).eval v = eXof G U x n hb j).card := by
    rw [hdim]
    rw [show ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
        decide (Verifier.bitsToIdx (margOf (sampData G x) n .alice z) = (i : ℕ)
          ∧ Verifier.bitsToIdx (margOf (sampData G x) n .bob z) = (j : ℕ)))
        = ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
          (fun v : (Vof G U x).Questions n =>
            decide (((Vof G U x).sampler.cl n .alice).eval v = eXof G U x n hb i
              ∧ ((Vof G U x).sampler.cl n .bob).eval v = eXof G U x n hb j))
            (CL.ofBits ((Vof G U x).sampler.dim n) z)) from ?_]
    · rw [Verifier.length_filter_bitStrsOfLen (s := (Vof G U x).sampler.dim n)
        (fun v => decide (((Vof G U x).sampler.cl n .alice).eval v = eXof G U x n hb i
          ∧ ((Vof G U x).sampler.cl n .bob).eval v = eXof G U x n hb j))]
      congr 1
      ext v
      simp
    · refine List.filter_congr fun z hz => ?_
      have hz' : z.length = (Vof G U x).sampler.dim n := (Data.mem_bitStrsOfLen _ _).1 hz
      simp only [decide_eq_decide]
      rw [marg_idx_eq G U x n hb .alice z hz' i, marg_idx_eq G U x n hb .bob z hz' j]
  rw [hnum]
  rw [show (Vof G U x).sampler.dist n (eXof G U x n hb i) (eXof G U x n hb j)
      = ((Finset.univ.filter fun v : (Vof G U x).Questions n =>
          ((Vof G U x).sampler.cl n .alice).eval v = eXof G U x n hb i
            ∧ ((Vof G U x).sampler.cl n .bob).eval v = eXof G U x n hb j).card : ℝ)
        / (Fintype.card ((Vof G U x).Questions n) : ℝ) from rfl]
  congr 1
  rw [hdim]
  simp [Verifier.Questions]

/-- **The acceptance table read back.** A tuple of indices is in the table exactly when the
verifier's decider accepts the tuple of strings they name. -/
theorem acc_mem_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (i j : Fin ((tab G U x n).nX + 1)) (k l : Fin ((tab G U x n).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (tab G U x n).acc
      ↔ (Vof G U x).decider.Accepts n (CL.toBits (eXof G U x n hb i))
          (CL.toBits (eXof G U x n hb j)) (eAof G U x n k).1 (eAof G U x n l).1 := by
  have hdim : dimOf (sampData G x) n = (Vof G U x).sampler.dim n := dimOf_eq G U x n hb
  have hqmem : ∀ (m : Fin ((tab G U x n).nX + 1)),
      CL.toBits (eXof G U x n hb m) ∈ Data.bitStrsOfLen (dimOf (sampData G x) n) := by
    intro m
    rw [Data.mem_bitStrsOfLen, CL.length_toBits, hdim]
  have hamem : ∀ (m : Fin ((tab G U x n).nA + 1)),
      (eAof G U x n m).1 ∈ Data.bitStrsLE (ansBound G x n) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (eAof G U x n m).2
  rw [show (tab G U x n).acc = Verifier.accList (dimOf (sampData G x) n) (ansBound G x n)
      (accOf (decProgData G U x) n) from rfl, Verifier.mem_accList_iff]
  constructor
  · rintro ⟨u, hu, v, hv, a, ha, b, hb', hacc, hi, hj, hk, hl⟩
    have hu' : u = CL.toBits (eXof G U x n hb i) :=
      Verifier.bitsToIdx_injOn ((Data.mem_bitStrsOfLen _ _).1 hu)
        (by rw [CL.length_toBits, hdim]) (by rw [← hi, eXof_apply])
    have hv' : v = CL.toBits (eXof G U x n hb j) :=
      Verifier.bitsToIdx_injOn ((Data.mem_bitStrsOfLen _ _).1 hv)
        (by rw [CL.length_toBits, hdim]) (by rw [← hj, eXof_apply])
    have ha' : a = (eAof G U x n k).1 := (List.idxOf_inj ha).1 (by rw [← hk, eAof_apply])
    have hb'' : b = (eAof G U x n l).1 := (List.idxOf_inj hb').1 (by rw [← hl, eAof_apply])
    subst hu'; subst hv'; subst ha'; subst hb''
    exact (accOf_iff G U x n hb _ _ _ _).1 hacc
  · intro h
    exact ⟨_, hqmem i, _, hqmem j, _, hamem k, _, hamem l,
      (accOf_iff G U x n hb _ _ _ _).2 h,
      (eXof_apply G U x n hb i).symm, (eXof_apply G U x n hb j).symm,
      (eAof_apply G U x n k).symm, (eAof_apply G U x n l).symm⟩

theorem game_D_true_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (i j : Fin ((tab G U x n).nX + 1)) (k l : Fin ((tab G U x n).nA + 1)) :
    ((Vof G U x).game n (ansBound G x n)).D (eXof G U x n hb i) (eXof G U x n hb j)
        (eAof G U x n k) (eAof G U x n l) = true
      ↔ (Vof G U x).decider.Accepts n (CL.toBits (eXof G U x n hb i))
          (CL.toBits (eXof G U x n hb j)) (eAof G U x n k).1 (eAof G U x n l).1 := by
  classical
  exact decide_eq_true_iff

/-- **O2, the match.** On an `n`-bounded, `n`-synchronous verifier the tabulation matches
`𝒱_n` along `eXof` and `eAof`. -/
theorem tab_match (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (hs : (Vof G U x).IsSynchronousAt n) :
    ∃ (eX : Fin ((tab G U x n).nX + 1) ≃ (Vof G U x).Questions n)
      (eA : Fin ((tab G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n)),
      (∀ i j, (tab G U x n).game.μ i j = (Vof G U x).sampler.dist n (eX i) (eX j)) ∧
      (∀ i j k l, (tab G U x n).game.D i j k l =
        ((Vof G U x).game n (ansBound G x n)).D (eX i) (eX j) (eA k) (eA l)) := by
  refine ⟨eXof G U x n hb, eAof G U x n, mu_clause G U x n hb, fun i j k l => ?_⟩
  refine Bool.eq_iff_iff.2 ?_
  rw [GameData.game_D, game_D_true_iff G U x n hb]
  by_cases hc : i = j ∧ k ≠ l
  · rw [if_pos hc]
    obtain ⟨rfl, hkl⟩ := hc
    simp only [Bool.false_eq_true, false_iff]
    exact hs _ _ _ (fun h => hkl ((eAof G U x n).injective (Subtype.ext h)))
  · rw [if_neg hc, decide_eq_true_iff]
    exact acc_mem_iff G U x n hb i j k l

/-- **O2, the soundness bound.** Without synchronicity the tabulation still does not
overshoot: the tuples a `GameData` forces to reject are exactly the ones whose rejection can
only lower the value (`quantumValue_mono`). -/
theorem tab_le (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) :
    quantumValue (tab G U x n).game ≤ (Vof G U x).valStar n (ansBound G x n) := by
  classical
  obtain ⟨Gs, hGsμ, hGsD⟩ : ∃ Gs : Game ((Vof G U x).Questions n) ((Vof G U x).Questions n)
      (Verifier.Answers (ansBound G x n)) (Verifier.Answers (ansBound G x n)),
      (∀ a b, Gs.μ a b = ((Vof G U x).game n (ansBound G x n)).μ a b) ∧
      (∀ a b c d, Gs.D a b c d
        = if a = b ∧ c ≠ d then false else ((Vof G U x).game n (ansBound G x n)).D a b c d) :=
    ⟨{ (Vof G U x).game n (ansBound G x n) with
        D := fun a b c d => if a = b ∧ c ≠ d then false
          else ((Vof G U x).game n (ansBound G x n)).D a b c d },
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  have hDs : ∀ (i j : Fin ((tab G U x n).nX + 1)) (k l : Fin ((tab G U x n).nA + 1)),
      (tab G U x n).game.D i j k l
        = Gs.D (eXof G U x n hb i) (eXof G U x n hb j) (eAof G U x n k) (eAof G U x n l) := by
    intro i j k l
    rw [GameData.game_D, hGsD]
    by_cases hc : i = j ∧ k ≠ l
    · rw [if_pos hc, if_pos ⟨by rw [hc.1], fun h => hc.2 ((eAof G U x n).injective h)⟩]
    · have hc' : ¬((eXof G U x n hb) i = (eXof G U x n hb) j
          ∧ (eAof G U x n) k ≠ (eAof G U x n) l) :=
        fun h => hc ⟨(eXof G U x n hb).injective h.1, fun h' => h.2 (by rw [h'])⟩
      rw [if_neg hc, if_neg hc']
      refine Bool.eq_iff_iff.2 ?_
      rw [decide_eq_true_iff, game_D_true_iff G U x n hb]
      exact acc_mem_iff G U x n hb i j k l
  have h1 : quantumValue (tab G U x n).game = quantumValue Gs :=
    quantumValue_eq_of_equiv Gs (tab G U x n).game (eXof G U x n hb) (eXof G U x n hb)
      (eAof G U x n) (eAof G U x n) (fun i j => (mu_clause G U x n hb i j).trans (hGsμ _ _).symm)
      hDs
  have h2 : quantumValue Gs ≤ quantumValue ((Vof G U x).game n (ansBound G x n)) := by
    refine quantumValue_mono Gs _ (fun a b => (hGsμ a b).symm) ?_
    intro a b c d hD
    rw [hGsD] at hD
    by_cases hc : a = b ∧ c ≠ d
    · rw [if_pos hc] at hD; exact absurd hD (by simp)
    · rwa [if_neg hc] at hD
  exact h1.trans_le h2

/-- The equality of values the matching data implies: on a bounded, synchronous verifier the
tabulated game has the value it tabulates. -/
theorem tab_value (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (hs : (Vof G U x).IsSynchronousAt n) :
    quantumValue (tab G U x n).game = (Vof G U x).valStar n (ansBound G x n) := by
  obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U x n hb hs
  exact Verifier.quantumValue_toGame_eq_valStar _ _ _ _ eX eA hμ hD

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
-- `tab_computable`, `tab_value` and `tab_le`; letting unification unfold it into `tabOf` and
-- the two budgeted runs instead costs more heartbeats than any budget worth setting.
attribute [local irreducible] tab

/-- **The halting reduction** (blueprint `thm:halting`), in `val*` form: from gap-preserving
compression, the tabulation above and the remaining obligations, a computable map from
`Nat.Partrec.Code` to game descriptions whose game has quantum value `1` when the machine halts
on the empty input and at most `1/2` when it does not.

The proof is the per-level compressibility criterion at the classes `classA`, `classB`,
followed by the value agreement of the tabulation: the criterion produces a description at
level `2 ^ (K + 1 + esize e)` lying in `A` or in `B` according to whether `e` halts, a value-`1`
PCC strategy gives `val* = 1` (`Verifier.valStar_eq_one_of_hasPerfectPCC`), and the two
verdicts reach the tabulated game by different routes: `tab_value` in the halting branch,
where the verifier is synchronous, and `tab_le` in the other, where it need not be. -/
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
    obtain ⟨hsync, -⟩ := hx.2
    rw [tab_value G U _ _ hx.1 hsync, (Vof G U _).valStar_eq_one_of_hasPerfectPCC hx.2]
  · have hx := (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)
    exact (tab_le G U _ _ hx.1).trans hx.2

end MIPRE.Halting
