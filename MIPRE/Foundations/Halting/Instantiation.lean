/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Enumerate
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
structure. The four remaining pieces of work are exactly the fields of `Obligations`, so that
what is open can be enumerated rather than searched for:

* **O1** (`yYes`, `yYes_mem`, `yNo`, `yNo_mem`) — the two distinguished strings. The
  verifier-level statements are `Verifier.inClassA_of_accepts_diagonal` and
  `inClassB_of_rejects_all`; what is owed is the wrapper's time bound, hence the two concrete
  decider programs realizing them.
* **O2** (`tab`, `tab_computable`, `tab_match`) — the tabulation of `𝒱_n` as a game
  description matching it along relabelings of the two alphabets, which are
  `Verifier.answerEquiv` and `questionEquiv`; `Obligations.tab_value` reads the equality of
  values off it (`Verifier.quantumValue_toGame_eq_valStar`). What is owed is the computation —
  the sampler run over every point of `𝔽₂^{s(n)}` for the question weights, and the decider run
  under its budget for the acceptance table. Three features of the fields' shape are deliberate
  and each is explained in its own docstring: they hold only of an `n`-bounded verifier (and
  cannot hold of every string); `tab_match` delivers the relabelings rather than only the value
  they equate, because `synval ≤ val*` points the wrong way for item 1 of `thm:halting`; and
  the match itself is asked only of a verifier synchronous at `n`, a `GameData` describing a
  synchronous game by construction, with `tab_le` carrying the soundness branch instead.
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
for synchronicity. So the two fields as stated do not compose. Three repairs are on the
record in blueprint `lem:halting-semidecider`: tabulate on a doubled question set so that
the distribution avoids the diagonal, make `Decider.wrap` reject unequal answers to equal
questions so that every string names a synchronous verifier, or put synchronicity into
`classB` and pay for it in `compr_spec`. Which one is right is not O3's to decide.

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
`Obligations.tab_match` has the shape it has. The soundness half needs neither step, only
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

/-! ## The obligations -/

/-- **What the halting reduction still owes.** Each field is a piece of work identified in
blueprint `rem:compression-abstract` and tracked in `planning/h4-assembly.md`; nothing else is
assumed, and `halting_reduction` below is proved outright from an inhabitant of this
structure. The grouping is O1 (the two distinguished strings), O2 (the tabulation), O3 (the
semidecider) and O4 (the compressor). -/
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
  /-- **O2.** The `n`-th game of the verifier a string denotes, as a game description. -/
  tab : BitStr → ℕ → GameData
  /-- **O2.** The tabulation is computable. -/
  tab_computable : Computable fun p : BitStr × ℕ => tab p.1 p.2
  /-- **O2.** For an `n`-bounded verifier, the tabulation *matches* `𝒱_n`: there are
  relabelings of the two alphabets along which its distribution and its decision predicate are
  those of `𝒱_n`. `Obligations.tab_value` derives the equality of values from it
  (`Verifier.quantumValue_toGame_eq_valStar`).

  Two things about the shape. The hypothesis is not slack: without it the field is
  *unsatisfiable*, since whether the decider a string denotes accepts a given tuple is `Σ₁`, so
  a computable `tab` correct at every string would decide the halting problem — take two
  strings whose deciders differ only in how long they run before accepting, and no fixed budget
  separates them. Boundedness is what turns acceptance into a decidable question, by supplying
  the budget; both uses in `halting_reduction` have it, membership in either class carrying
  `IsBounded n`.

  And the *matching data* is what is required, not merely the equality of values it implies.
  `thm:halting` item 1 claims a value-`1` PCC strategy, so `synval = 1` and not only
  `val* = 1`, and `synval ≤ val*` points the wrong way: from an equality of `val*` alone a
  perfect PCC strategy of `𝒱_n` cannot be pushed onto the tabulation. The relabelings can carry
  it (`MIPRE.Verifier.exists_perfectPCC_syncGame`), and O2 has them in hand anyway, building
  `tab` from `Verifier.answerEquiv` and `questionEquiv`. -/
  tab_match : ∀ (x : BitStr) (n : ℕ), (Vof G U x).IsBounded n →
      (Vof G U x).IsSynchronousAt n →
    ∃ (eX : Fin ((tab x n).nX + 1) ≃ (Vof G U x).Questions n)
      (eA : Fin ((tab x n).nA + 1) ≃ Verifier.Answers (ansBound G x n)),
      (∀ i j, (tab x n).game.μ i j = (Vof G U x).sampler.dist n (eX i) (eX j)) ∧
      (∀ i j k l, (tab x n).game.D i j k l =
        ((Vof G U x).game n (ansBound G x n)).D (eX i) (eX j) (eA k) (eA l))
  /-- **O2.** Without synchronicity the tabulation still does not *overshoot*.

  A `GameData` describes a synchronous game by construction — `GameData.toGame` forces
  `D x x a b` to `false` for `a ≠ b` — whereas `Verifier.game` does no such thing, so no
  tabulation can match a verifier that accepts unequal answers to equal questions. That is not
  a defect of the tabulation but of demanding a match unconditionally: `classB n` does not ask
  for synchronicity, only for `val* ≤ 1/2`, and the reduction's soundness branch needs only an
  upper bound. Forcing those tuples to reject can only lower the value
  (`MIPRE.quantumValue_mono`), which is the right direction. -/
  tab_le : ∀ (x : BitStr) (n : ℕ), (Vof G U x).IsBounded n →
    quantumValue (tab x n).game ≤ (Vof G U x).valStar n (ansBound G x n)

/-- The equality of values the matching data implies: the tabulated game has the value it
tabulates. -/
theorem Obligations.tab_value {G : GapCompression} {U : UniversalMachine} (O : Obligations G U)
    (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) (hs : (Vof G U x).IsSynchronousAt n) :
    quantumValue (O.tab x n).game = (Vof G U x).valStar n (ansBound G x n) := by
  obtain ⟨eX, eA, hμ, hD⟩ := O.tab_match x n hb hs
  exact Verifier.quantumValue_toGame_eq_valStar _ _ _ _ eX eA hμ hD

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

/-- **The halting reduction** (blueprint `thm:halting`), in `val*` form: from gap-preserving
compression and the four obligations, a computable map from `Nat.Partrec.Code` to game
descriptions whose game has quantum value `1` when the machine halts on the empty input and at
most `1/2` when it does not.

The proof is the per-level compressibility criterion at the classes `classA`, `classB`,
followed by the value agreement of the tabulation: the criterion produces a description at
level `2 ^ (K + 1 + esize e)` lying in `A` or in `B` according to whether `e` halts, a value-`1`
PCC strategy gives `val* = 1` (`Verifier.valStar_eq_one_of_hasPerfectPCC`), and `tab_value`
carries both verdicts to the tabulated game. -/
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
  refine ⟨fun pc => O.tab (g (compile pc)) (2 ^ (K + 1 + esize (compile pc))),
    O.tab_computable.comp
      ((PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp).pair hlevel),
    fun pc => ⟨fun hdom => ?_, fun hdom => ?_⟩⟩
  · have hx := (hg (compile pc)).2.1 ((hspec pc).2 hdom)
    obtain ⟨hsync, -⟩ := hx.2
    rw [O.tab_value _ _ hx.1 hsync, (Vof G U _).valStar_eq_one_of_hasPerfectPCC hx.2]
  · have hx := (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)
    exact (O.tab_le _ _ hx.1).trans hx.2

end MIPRE.Halting
