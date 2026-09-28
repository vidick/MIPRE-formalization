/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Semidecider
public import MIPRE.Foundations.Halting.Strings

@[expose] public section

/-!
# The halting reduction, assembled, in any value model

Blueprint `thm:halting` and `thm:halting-co`: the computable map from machines to game
descriptions whose game has value `1` when the machine halts and value at most `1/2` when it
does not — or the reverse — proved from gap-preserving compression as a hypothesis
(`MIPRE.GapCompression`, blueprint `thm:compression`) through the compressibility criterion
(`MIPRE.Cost.compressibility_criterion_levels` and its nested form
`compressibility_criterion_nested`, blueprint `lem:compressible-criterion`), along the
dictionary of blueprint `rem:compression-abstract`. The objects — the verifier a string
denotes, the classes, the tabulation — are in `Halting/Instantiation.lean`. This module sits
below that file, below `Halting/Strings.lean` and below `Halting/Semidecider.lean` in the import
order, which is what lets `Obligations` say exactly what is left.

Everything is written once in a value model `ω` (`ValueModel`, `Foundations/ValueModel.lean`).
The two theorems differ only in which direction the value is semidecidable:

* **`RE` shape** (`halting_reduction_lower`): halting machines go to value `1`, the others to
  value at most `1/2`. It needs the value r.e. from *below* (`ValueModel.LowerRE`), and runs the
  criterion with `A` the class of perfect PCC strategies (`classA`, preserved by the tensor
  completeness of compression) and `B` the class of small value (`classB ω`, preserved by
  soundness in the model). At `ValueModel.tensor` this is `thm:halting`
  (`halting_reduction`).
* **`coRE` shape** (`halting_reduction_upper`): halting machines go to value at most `1/2`, the
  others to value `1`. It needs the value r.e. from *above* (`ValueModel.UpperRE`), and runs the
  nested criterion with `A := classB ω`, `B₀ := classA` and `B₁ := classOne ω`, the class of
  value `1` read on the tabulation, whose complement the upper semidecider recognizes and which
  contains `classA` because a perfect PCC strategy gives value `1` in every model. No perfect
  strategy of the model is ever constructed: the non-halting conclusion is `¬ (value < 1)`.
  At `ValueModel.commuting` this is `thm:halting-co`, and the tensor completeness is all the
  completeness it uses (`planning/mipco-track.md` §3).

Both come in a *strings* form (`halting_reduction_lower_strings`, `_upper_strings`) — the
reduction's map to strings and levels, with the class memberships — from which the value
statements follow by the tabulation (`tab_val`); `halting_reduction_both_of`
(`Halting/CompressorProgram.lean`) reads the synchronous value off the same map.

## What is proved and what is assumed

`halting_reduction_lower` and `halting_reduction_upper` are complete: no `sorry`, and their only
hypotheses are a `GapCompression`, a `UniversalMachine` (`exists_efficient_universal` provides
one), the semidecidability of the value in the model, and an `Obligations` structure. Of the
four obligations of `rem:compression-abstract`, three are theorems that the proofs apply
directly, and the structure's content is the fourth:

* **O1** — the two distinguished strings, `yYes_mem` and `yNo_mem` (`Halting/Strings.lean`),
  on the wrapper's time bound (`Halting/WrapperCost.lean`) and the verifier-level statements
  `Verifier.inClassA_of_accepts_diagonal` and `inClassB_of_rejects_all`. Each comes with its
  own threshold; the proof takes the larger.
* **O2** — the tabulation of `𝒱_n` as a game description matching it along relabelings of the
  two alphabets: `tab`, `tab_computable`, `tab_match`, `tab_val` and `gameValue_tab_eq_one`
  (`Halting/Instantiation.lean`). The game it matches is the *doubled* one,
  `(Vof G U x).doubledGame`, so that the diagonal a `GameData` vetoes carries no weight and no
  synchronicity is asked of the verifier; that is what lets O3 use it, and the module docstring
  of `Instantiation.lean` says how.
* **O3** — a program halting on `(x, n)` exactly off `classB ω n`, respectively off
  `classOne ω n`: `exists_sem_lower` and `exists_sem_upper` (`Halting/Semidecider.lean`), from
  the semidecider of the model.
* **O4** (`compr`, `compr_spec`) — the compressor: the decider that reads its description by
  bit queries, freezes the verifier at index `2n + 1` (`Verifier.freeze`), runs `Compress`,
  and its time accounting. Its `λ` is chosen by `lem:lambda-bound`
  (`MIPRE.Halting.lambda_bound`), which turns the output's `poly(n, λ)` running times into the
  `n ^ λ` that `IsBounded` asks for. The field's fourth hypothesis, `x.length ≤ n + 1`, is what
  makes it satisfiable at all; its docstring says why, and
  `Cost.compressibility_criterion_levels` supplies it from a bound its own proof already had,
  and `exists_ansBound_le` (`Halting/Instantiation.lean`, checked) is the step that consumes
  it: it puts the answer budget of level `2n + 1` under the one `GapCompression.completeness`
  supplies strategies at.

`CompressorSpec` says what the compressor's program has to satisfy — the parameter it carries,
the agreement of its decider with the compressed decider of the frozen verifier, its
boundedness, the growth of the parameter — and `CompressorSpec.toObligations` is the class
transfer from those fields alone, in any model in which compression is sound
(`GapCompression.Sound ω`), so that the construction (`Halting/CompressorProgram.lean`) owes the
fields and nothing that would come out in a proof later.

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
equivalences with `hμ` and `hD` — rather than the equality of values it implies, which is why
`tab_match` has the shape it has. The soundness half needs neither step, only
`synval ≤ val*` (`MIPRE.syncValue_le_quantumValue`, blueprint `lem:sync-le-valstar`);
`Verifier.gameValue_toGame_le_of_valStar_le` is it in that vocabulary.
-/

namespace MIPRE.Halting

open Cost
open HaltingGameValue (GameData)

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The obligation -/

/-- **What the halting reduction still owes: obligation O4, the compressor**, in a value model
`ω`. The other three obligations of blueprint `rem:compression-abstract` are theorems —
`yYes_mem` and `yNo_mem` (O1), the tabulation `tab` with `tab_computable` and `tab_val` (O2),
`exists_sem_lower` and `exists_sem_upper` (O3) — and the reductions below apply them; this
structure holds what is not a theorem of this module, so that what is open can be enumerated
rather than searched for. `CompressorSpec.toObligations` inhabits it from the compressor's
specification and soundness of compression in the model. -/
structure Obligations (ω : ValueModel) (G : GapCompression) (U : UniversalMachine) where
  /-- The level above which the guarantees hold. -/
  n₀ : ℕ
  /-- **O4.** The compressor: a polynomial-time map on `(description, level)` pairs. -/
  compr : PolyTimeFun (Prog × ℕ) BitStr
  /-- **O4.** On a succinct description of a string at level `2n + 1`, with the size slack and
  the length bound the criterion provides, the compressor preserves both classes down to level
  `n`.

  The clause `x.length ≤ n + 1` is not slack either, and it is what makes the field
  *satisfiable*. `classA G U (2n+1)` asks for a value-`1` PCC strategy at the answer bound
  `ansBound G x (2n+1) = G.bound.eval (2n+1 + descLam x)`, while the only source of such a
  strategy for a compressed verifier is `GapCompression.completeness`, which takes its input at
  the bound `(2 ^ n) ^ λ` with `λ` the parameter the compressor writes into its output — so `λ`
  is bounded by the compressor's own output size and cannot be made arbitrarily large. Without a
  bound on `descLam x` the two cannot be related: nothing in `IsBounded` constrains a string's
  compression parameter (for a `G` whose compressed sampler does not vary with `λ`, membership
  in either class is insensitive to it), while `ansBound` grows with it. With
  `x.length ≤ n + 1` we get `descLam x < 2 ^ (n+1)`, hence
  `ansBound G x (2n+1) ≤ G.bound.eval (2n+1 + 2^(n+1)) ≤ (2 ^ n) ^ λ` already for
  `λ ≥ 2 · deg(G.bound) + 1` and `n` above a threshold read off `G.bound` too, and
  `hasPerfectPCC_of_le` carries the hypothesis across. `exists_ansBound_le`
  (`Halting/Instantiation.lean`) is that step, checked; note the threshold is set by the
  polynomial `G.bound`, not by `G.deg`.

  **Both directions close from these hypotheses, and the second needs the rejection clause of
  the classes.** The `classA` direction is the argument above, `hasPerfectPCC_of_le` raising the
  answer bound. The `classB` direction runs the other way: soundness in the model wants
  `val ω (2 ^ n) ((2 ^ n) ^ λ) ≤ 1/2`, membership in `classB G U ω (2n+1)` gives it at
  `ansBound G x (2n+1)`, and `val_le_of_le` only *raises* a value with its bound. What
  carries it is `val_eq_of_rejects`: membership carries `Verifier.RejectsLong`, the decider
  rejecting every answer longer than `ansBound G x (2n+1)` at index `2n + 1`, so raising the
  bound to `(2 ^ n) ^ λ` does not move the value. In return the output has to reject beyond
  `ansBound G (compr (c, n)) n` to be in either class, which `GapCompression.output_rejects_long`
  supplies once the output's decider is a compressed decider. The paper's `V^halt` has both by
  construction, Step 6 of its decider `F` being an explicit length check spent in the amended
  proof of `lem:dhalt-values`; `planning/h4-assembly.md` §4 item 4 has the argument and the
  choice to put the clause in the classes rather than through the criterion. -/
  compr_spec : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 →
      (x ∈ classA G U (2 * n + 1) → compr (c, n) ∈ classA G U n) ∧
      (x ∈ classB G U ω (2 * n + 1) → compr (c, n) ∈ classB G U ω n)

/-! ## What the compressor must supply

The consumer of obligation O4, written before its construction (`planning/h4-assembly.md` §1,
"write the consumer first"): a structure `CompressorSpec` of the properties the compressor's
program has to have, and the definition `CompressorSpec.toObligations` turning one into an
`Obligations`. It is the class transfer of `rem:compression-abstract` item 2 done once, against
named hypotheses, so that what the construction owes is exactly the fields below and nothing
that comes out in a proof later.

The reading. On a succinct description `c` of a short string `x` at level `n`, the output
`compr (c, n)` is a string denoting the parameter `lam n` and a decider that, at every index,
accepts what the compressed decider of *the verifier of `x` frozen at index `2n + 1`* accepts
(`accepts_compr`); its verifier is `n`-bounded (`isBounded_compr`, the accounting); and `lam n`
grows fast enough for the frozen verifier to be `lam n`-bounded (`lam_ge`, consumed by
`Verifier.freeze_isBounded`) and for the answer budget of level `2n + 1` to fit under the one
`GapCompression.completeness` takes its hypothesis at (`ansBound_le`, from `exists_ansBound_le`
with `n₀` past its threshold). -/

/-- **The specification of the compressor.** What obligation O4's construction has to prove of
its program; `toObligations` is the class transfer on top. -/
structure CompressorSpec (G : GapCompression) (U : UniversalMachine) where
  /-- The level above which everything holds; at least `G.C₀`. -/
  n₀ : ℕ
  C₀_le : G.C₀ ≤ n₀
  /-- The compressor. -/
  compr : PolyTimeFun (Prog × ℕ) BitStr
  /-- The parameter the output carries at level `n`. -/
  lam : ℕ → ℕ
  /-- The output at level `n` denotes the parameter `lam n`. -/
  descLam_compr : ∀ (c : Prog) (n : ℕ), descLam (compr (c, n)) = lam n
  /-- **Acceptance agreement.** The output's decider accepts, at every index, exactly what the
  compressed decider of the verifier of `x` frozen at `2n + 1` accepts. -/
  accepts_compr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 →
    ∀ (m : ℕ) (x' y' a b : BitStr),
      (Vof G U (compr (c, n))).decider.Accepts m x' y' a b ↔
        (G.output (((Vof G U x).freeze (2 * n + 1)).sampler.prog,
          ((Vof G U x).freeze (2 * n + 1)).decider.prog) (lam n)).decider.Accepts m x' y' a b
  /-- **The accounting.** The output's verifier is `n`-bounded, given that the described
  verifier is `(2n + 1)`-bounded. -/
  isBounded_compr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 → (Vof G U x).IsBounded (2 * n + 1) →
    (Vof G U (compr (c, n))).IsBounded n
  /-- **Growth of the parameter**, as `Verifier.freeze_isBounded` consumes it: the running
  times and dimension of a `(2n + 1)`-bounded verifier at index `2n + 1`, shifted by the cost
  of freezing, fit under `2 ^ lam n`, and the index and the size fit under `lam n`. -/
  lam_ge : ∀ n, n₀ ≤ n →
    (2 * n + 1) ^ (2 * n + 1) + esize (2 * n + 1) + 4 ≤ 2 ^ lam n ∧
    2 * n + 1 + esize (2 * n + 1) + 53 ≤ lam n
  /-- **The answer budget fits**: `exists_ansBound_le` with `n₀` past its threshold and `lam n`
  past `lam₀`. -/
  ansBound_le : ∀ (x : BitStr) (n : ℕ), n₀ ≤ n → x.length ≤ n + 1 →
    ansBound G x (2 * n + 1) ≤ (2 ^ n) ^ lam n

namespace CompressorSpec

variable {G U} (S : CompressorSpec G U)

/-- The verifier of `x` frozen at `2n + 1` is `lam n`-bounded, from its `(2n + 1)`-boundedness
and the growth of `lam`. -/
theorem frozen_isBounded {x : BitStr} {n : ℕ} (hn : S.n₀ ≤ n)
    (hb : (Vof G U x).IsBounded (2 * n + 1)) :
    ((Vof G U x).freeze (2 * n + 1)).IsBounded (S.lam n) := by
  obtain ⟨h1, h2⟩ := S.lam_ge n hn
  obtain ⟨hdim, hS, hD⟩ := hb.1 (2 * n + 1) hb.two_le
  exact (Vof G U x).freeze_isBounded (2 * n + 1) (S.lam n) _ _ _ _ hS hD
    (hdim.trans (by omega)) h1 h1 (by omega) (by omega) (by have := hb.2; omega)

/-- The output's verifier has the compressed sampler at `lam n`, as the compression theorem's
output does. -/
theorem sampler_eq (c : Prog) (n : ℕ) (V : Prog × Prog) :
    (G.output V (S.lam n)).sampler = (Vof G U (S.compr (c, n))).sampler := by
  rw [G.output_sampler, Vof, Verifier.ofSamplerDeciderD_sampler, S.descLam_compr]

/-- The answer budget the output's class is read with is the one the compression theorem's
output is judged at. -/
theorem ansBound_compr (c : Prog) (n : ℕ) :
    ansBound G (S.compr (c, n)) n = G.bound.eval (n + S.lam n) := by
  rw [ansBound, S.descLam_compr]

/-- **The class transfer.** A compressor meeting the specification inhabits `Obligations` in
every value model in which compression is sound: the `classA` clause by the tensor completeness
of compression, and the `classB` clause by soundness in the model — the described verifier
rejects beyond its answer bound, so raising the bound keeps the value
(`Verifier.val_eq_of_rejects`); freezing keeps it (`Verifier.freeze_val`); soundness carries it
through compression; and the output's decider accepts what the compressed decider accepts
(`Verifier.val_congr`). -/
def toObligations (ω : ValueModel) (hs : G.Sound ω) : Obligations ω G U where
  n₀ := S.n₀
  compr := S.compr
  compr_spec := by
    intro c x n hn hc hsd hlen
    -- the objects: the described verifier, frozen; the compression theorem's output
    set V := Vof G U x with hV
    set W := G.output ((V.freeze (2 * n + 1)).sampler.prog, (V.freeze (2 * n + 1)).decider.prog)
      (S.lam n) with hW
    have hacc := S.accepts_compr c x n hn hc hsd hlen
    have hS : (Vof G U (S.compr (c, n))).sampler = W.sampler := (S.sampler_eq c n _).symm
    have hC₀ : G.C₀ ≤ n := S.C₀_le.trans hn
    have hans := S.ansBound_le x n hn hlen
    -- the output rejects long answers, as every compressed decider does
    have hrej : (Vof G U (S.compr (c, n))).RejectsLong n (ansBound G (S.compr (c, n)) n) := by
      intro x' y' a b hl h
      rw [S.ansBound_compr] at hl
      exact G.output_rejects_long _ (S.lam n) n x' y' a b hl ((hacc n x' y' a b).1 h)
    refine ⟨fun hA => ?_, fun hB => ?_⟩
    · obtain ⟨hb, -, hpcc⟩ := hA
      refine ⟨S.isBounded_compr c x n hn hc hsd hlen hb, hrej, ?_⟩
      -- raise the answer bound, freeze, compress, and read the result on the output's verifier
      have h1 : V.HasPerfectPCC (2 * n + 1) ((2 ^ n) ^ S.lam n) :=
        V.hasPerfectPCC_of_le hans hpcc
      have h2 : (V.freeze (2 * n + 1)).HasPerfectPCC (2 ^ n) ((2 ^ n) ^ S.lam n) :=
        (V.freeze_hasPerfectPCC (2 * n + 1) (2 ^ n) _).2 h1
      have h3 : W.HasPerfectPCC n (G.bound.eval (n + S.lam n)) :=
        G.completeness _ (S.lam n) n (S.frozen_isBounded hn hb) hC₀ h2
      rw [S.ansBound_compr]
      exact (Verifier.hasPerfectPCC_congr hS fun x' y' a b => (hacc n x' y' a b).symm).1 h3
    · obtain ⟨hb, hrejx, hval⟩ := hB
      refine ⟨S.isBounded_compr c x n hn hc hsd hlen hb, hrej, ?_⟩
      -- the described verifier rejects beyond its answer bound, so raising it keeps the value
      have h1 : V.val ω (2 * n + 1) ((2 ^ n) ^ S.lam n) ≤ 1 / 2 := by
        rw [V.val_eq_of_rejects ω hans hrejx]; exact hval
      have h2 : (V.freeze (2 * n + 1)).val ω (2 ^ n) ((2 ^ n) ^ S.lam n) ≤ 1 / 2 := by
        rw [V.freeze_val]; exact h1
      have h3 : W.val ω n (G.bound.eval (n + S.lam n)) ≤ 1 / 2 :=
        hs _ (S.lam n) n (S.frozen_isBounded hn hb) hC₀ h2
      rw [S.ansBound_compr, ← Verifier.val_congr ω hS fun x' y' a b => (hacc n x' y' a b).symm]
      exact h3

end CompressorSpec

/-! ## The reduction -/

/-- `2 ^ ·` is primitive recursive: the level at which the recursion of the criterion runs is
`2 ^ (K + 1 + esize e)`, and the reduction has to compute it. -/
theorem two_pow_iterate (n : ℕ) : (fun b : ℕ => 2 * b)^[n] 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring

theorem primrec_two_pow : Primrec fun n : ℕ => 2 ^ n :=
  (Primrec.nat_iterate Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂).of_eq fun n => two_pow_iterate n

-- The tabulation is opaque from here on. The reductions only ever feed it to
-- `tab_computable` and `tab_val` (once as an equality, once through `.le`); letting
-- unification unfold it into `tabOf` and the two budgeted runs instead costs more heartbeats
-- than any budget worth setting.
attribute [local irreducible] tab

/-- **The halting reduction, `RE` shape, on strings**: from the two distinguished strings, the
lower semidecider, and the obligation, a computable map from `Nat.Partrec.Code` to strings and
a computable level, such that the string lies in `classA` at its level when the machine halts
on the empty input and in `classB ω` when it does not. This is the compressibility criterion
at the classes `classA`, `classB ω`; the value statements read it through the tabulation. -/
theorem halting_reduction_lower_strings (ω : ValueModel) (hlow : ω.LowerRE)
    (O : Obligations ω G U) :
    ∃ (s : Nat.Partrec.Code → BitStr) (lvl : Nat.Partrec.Code → ℕ),
      Computable s ∧ Computable lvl ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → s pc ∈ classA G U (lvl pc)) ∧
        (¬ (pc.eval 0).Dom → s pc ∈ classB G U ω (lvl pc)) := by
  obtain ⟨nY, hyes⟩ := yYes_mem G U
  obtain ⟨nN, hno⟩ := yNo_mem G U ω
  obtain ⟨sem, hsem_closed, hsem⟩ := exists_sem_lower G U ω hlow
  -- the criterion's threshold: the two strings' and the compressor's, whichever is larger
  obtain ⟨g, K, hg⟩ := Cost.compressibility_criterion_levels
    (classA G U) (classB G U ω) (max (max nY nN) O.n₀)
    yYes (fun n hn => hyes n (by omega)) yNo (fun n hn => hno n (by omega))
    sem hsem_closed hsem O.compr (fun c x n hn => O.compr_spec c x n (by omega))
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  have hsize : Computable fun pc : Nat.Partrec.Code => esize (compile pc) :=
    Data.primrec_size.to_comp.comp hc
  refine ⟨fun pc => g (compile pc), fun pc => 2 ^ (K + 1 + esize (compile pc)),
    PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp,
    (primrec_two_pow.comp (Primrec.nat_add.comp (Primrec.const (K + 1)) Primrec.id)).to_comp.comp
      hsize,
    fun pc => ⟨fun hdom => (hg (compile pc)).2.1 ((hspec pc).2 hdom),
      fun hdom => (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)⟩⟩

/-- **The halting reduction, `RE` shape** (blueprint `thm:halting` at `ValueModel.tensor`), in
any value model r.e. from below: from gap-preserving compression sound in the model, the two
distinguished strings, the semidecider, the tabulation and the one remaining obligation, a
computable map from `Nat.Partrec.Code` to game descriptions whose game has value `1` when the
machine halts on the empty input and at most `1/2` when it does not.

The proof is `halting_reduction_lower_strings` followed by the value agreement of the
tabulation: a value-`1` PCC strategy gives value `1` in the model
(`Verifier.val_eq_one_of_hasPerfectPCC`), and `tab_val` carries both verdicts to the tabulated
game — the same equality in both branches, the doubled question set having removed the
synchronicity hypothesis that once split them. -/
theorem halting_reduction_lower (ω : ValueModel) (hlow : ω.LowerRE) (O : Obligations ω G U) :
    ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → ω.val (g pc).game = 1) ∧
        (¬ (pc.eval 0).Dom → ω.val (g pc).game ≤ 1 / 2) := by
  obtain ⟨s, lvl, hs, hlvl, hcls⟩ := halting_reduction_lower_strings G U ω hlow O
  refine ⟨fun pc => tab G U (s pc) (lvl pc), (tab_computable G U).comp (hs.pair hlvl),
    fun pc => ⟨fun hdom => ?_, fun hdom => ?_⟩⟩
  · have hx := (hcls pc).1 hdom
    rw [tab_val G U ω _ _ hx.1]
    exact (Vof G U _).val_eq_one_of_hasPerfectPCC ω hx.2.2
  · have hx := (hcls pc).2 hdom
    exact (tab_val G U ω _ _ hx.1).le.trans hx.2.2

/-- **The halting reduction** (blueprint `thm:halting`), in `val*` form: the `RE` shape at the
tensor-product model, whose value is r.e. from below by `lem:value-lower-approx`. -/
theorem halting_reduction (O : Obligations .tensor G U) :
    ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → quantumValue (g pc).game = 1) ∧
        (¬ (pc.eval 0).Dom → quantumValue (g pc).game ≤ 1 / 2) :=
  halting_reduction_lower G U .tensor ValueModel.tensor_lowerRE O

/-- **The halting reduction, `coRE` shape, on strings**: from the two distinguished strings, the
upper semidecider, and the obligation, a computable map from `Nat.Partrec.Code` to strings and
a computable level, such that the string lies in `classB ω` at its level when the machine halts
on the empty input and in `classOne ω` when it does not. This is the nested compressibility
criterion (`Cost.compressibility_criterion_nested`) at `A := classB ω`, `B₀ := classA`,
`B₁ := classOne ω`: the compressor preserves the two former, by soundness in the model and by
the tensor completeness of compression, and the upper semidecider recognizes the complement of
the latter, which contains `classA` (`classA_subset_classOne`). -/
theorem halting_reduction_upper_strings (ω : ValueModel) (hup : ω.UpperRE)
    (O : Obligations ω G U) :
    ∃ (s : Nat.Partrec.Code → BitStr) (lvl : Nat.Partrec.Code → ℕ),
      Computable s ∧ Computable lvl ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → s pc ∈ classB G U ω (lvl pc)) ∧
        (¬ (pc.eval 0).Dom → s pc ∈ classOne G U ω (lvl pc)) := by
  obtain ⟨nY, hyes⟩ := yYes_mem G U
  obtain ⟨nN, hno⟩ := yNo_mem G U ω
  obtain ⟨sem, hsem_closed, hsem⟩ := exists_sem_upper G U ω hup
  obtain ⟨g, K, hg⟩ := Cost.compressibility_criterion_nested
    (classB G U ω) (classA G U) (classOne G U ω) (max (max nY nN) O.n₀)
    (classA_subset_classOne G U ω)
    yNo (fun n hn => hno n (by omega)) yYes (fun n hn => hyes n (by omega))
    sem hsem_closed hsem O.compr
    (fun c x n hn hc hsd hlen => (O.compr_spec c x n (by omega) hc hsd hlen).symm)
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  have hsize : Computable fun pc : Nat.Partrec.Code => esize (compile pc) :=
    Data.primrec_size.to_comp.comp hc
  refine ⟨fun pc => g (compile pc), fun pc => 2 ^ (K + 1 + esize (compile pc)),
    PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp,
    (primrec_two_pow.comp (Primrec.nat_add.comp (Primrec.const (K + 1)) Primrec.id)).to_comp.comp
      hsize,
    fun pc => ⟨fun hdom => (hg (compile pc)).2.1 ((hspec pc).2 hdom),
      fun hdom => (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)⟩⟩

/-- **The halting reduction, `coRE` shape** (blueprint `thm:halting-co` at
`ValueModel.commuting`), in any value model r.e. from above: a computable map from
`Nat.Partrec.Code` to game descriptions whose game has value at most `1/2` when the machine
halts on the empty input and `1` when it does not. From `halting_reduction_upper_strings`: for
a halting machine the string lies in `classB ω`, so its tabulated game has value at most `1/2`
(`tab_val`); for a non-halting one it lies in `classOne ω`, so its tabulated game does not have
value below `1`. No perfect strategy of the model is constructed. -/
theorem halting_reduction_upper (ω : ValueModel) (hup : ω.UpperRE) (O : Obligations ω G U) :
    ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → ω.val (g pc).game ≤ 1 / 2) ∧
        (¬ (pc.eval 0).Dom → ω.val (g pc).game = 1) := by
  obtain ⟨s, lvl, hs, hlvl, hcls⟩ := halting_reduction_upper_strings G U ω hup O
  refine ⟨fun pc => tab G U (s pc) (lvl pc), (tab_computable G U).comp (hs.pair hlvl),
    fun pc => ⟨fun hdom => ?_, fun hdom => ?_⟩⟩
  · have hx := (hcls pc).1 hdom
    rw [tab_val G U ω _ _ hx.1]
    exact hx.2.2
  · exact val_tab_eq_one_of_mem_classOne G U ((hcls pc).2 hdom)

end MIPRE.Halting

end
