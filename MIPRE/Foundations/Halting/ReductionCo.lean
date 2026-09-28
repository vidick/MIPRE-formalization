/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ClassMIPCo
import MIPRE.Foundations.Halting.CompressorProgram
import MIPRE.Foundations.Halting.InstantiationCo

/-!
# The halting reduction to the commuting-operator value, from co-soundness

Blueprint `thm:halting-co` (`planning/mipco-track.md`, Phase 0): a computable map from machines
to game descriptions whose game has commuting-operator value at most `1/2` when the machine
halts on the empty input and `1` when it does not, proved from the commuting-operator soundness
of gap compression (`GapCompression.CoSound`, a hypothesis) through the nested compressibility
criterion (`Cost.compressibility_criterion_nested`), with everything else reused from the
halting reduction of the main theorem (`Halting/Reduction.lean`):

* **O1** — the distinguished strings: `yNo` in `classBCo` (`yNo_memCo`, the same string as for
  `RE`, read in `ω_co`) and `yYes` in `classA` (`yYes_mem`, unchanged);
* **O2** — the tabulation, `tab`, `tab_computable`, and its value in `ω_co` (`tab_valCo`);
* **O3** — the semidecider: `exists_semCo`, a program halting on `(x, n)` exactly off
  `classOne n`, from the upper semidecider `commutingUpperRE` at the threshold `1`, composed
  with the computable tabulation — the role Lin's proof gives to the NPA hierarchy;
* **O4** — the compressor: the specification `CompressorSpec` of the main theorem, with the
  `classA` clause of its class transfer reused verbatim and the `classBCo` clause proved as
  the `classB` clause was, with `valCo` in place of `valStar` and `CoSound` in place of
  `GapCompression.soundness` (`CompressorSpec.toObligationsCo`).

The criterion is run with `A := classBCo` (preserved by co-soundness), `B₀ := classA`
(preserved by the *tensor* completeness of compression) and `B₁ := classOne` (its complement
semidecided by `exists_semCo`; contains `classA` by `classA_subset_classOne`). No perfect
commuting-operator strategy is ever constructed: the non-halting conclusion is
`¬ (ω_co < 1)`, and `ω_co ≤ 1`.
-/

namespace MIPRE.Halting

open Cost
open HaltingGameValue (GameData)

variable (G : GapCompression) (U : UniversalMachine)

-- The tabulation is opaque here as in `halting_reduction`, and for the same reason: the
-- semidecider and the reduction only ever feed it to `tab_computable`, `tab_valCo` and the
-- class `classOne`.
attribute [local irreducible] tab

/-! ## The semidecider -/

/-- **Obligation O3 of the co reduction**: a closed program halting on `encode (x, n)` exactly
off `classOne n`, that is, when `ω_co(tab x n) < 1`: the upper semidecider for the
commuting-operator value (`commutingUpperRE`, blueprint `lem:valco-upper-re`) at the threshold
`1/1`, composed with the computable tabulation. -/
theorem exists_semCo :
    ∃ S : Prog, S.WellScoped 1 ∧
      ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ classOne G U n := by
  have hre : REPred fun q : BitStr × ℕ =>
      commutingOperatorValue (tab G U q.1 q.2).game < ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) :=
    Partrec.comp commutingUpperRE ((tab_computable G U).pair (Computable.const ((1, 1) : ℕ × ℕ)))
  refine Cost.exists_semidecider_prod_nat (p := fun x n => x ∉ classOne G U n)
    (hre.of_eq fun q => ?_)
  simp only [Nat.cast_one, div_one, mem_classOne_iff, not_not]

/-! ## The obligation, and its discharge from the compressor's specification -/

/-- **The obligation of the co reduction**: the compressor of `Obligations`, preserving the
class `B^co` and the class `A` down the levels. The `classA` clause is that of `Obligations`;
the `classBCo` clause is the one commuting-operator soundness of compression supplies. -/
structure ObligationsCo (G : GapCompression) (U : UniversalMachine) where
  /-- The level above which the guarantees hold. -/
  n₀ : ℕ
  /-- The compressor. -/
  compr : PolyTimeFun (Prog × ℕ) BitStr
  /-- On a succinct description of a short string at level `2n + 1`, the compressor preserves
  `classBCo` and `classA` down to level `n`. -/
  compr_spec : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 →
      (x ∈ classBCo G U (2 * n + 1) → compr (c, n) ∈ classBCo G U n) ∧
      (x ∈ classA G U (2 * n + 1) → compr (c, n) ∈ classA G U n)

namespace CompressorSpec

variable {G U} (S : CompressorSpec G U)

/-- **The class transfer, co side.** A compressor meeting the specification inhabits
`ObligationsCo` as soon as compression is sound for the commuting-operator value: the
`classA` clause is that of `toObligations`, and the `classBCo` clause is its `classB` clause
with `valCo` in place of `valStar` — the described verifier rejects beyond its answer bound,
so raising the bound keeps `ω_co` (`Verifier.valCo_eq_of_rejects`); freezing keeps it
(`Verifier.freeze_valCo`); `CoSound` carries it through compression; and the output's decider
accepts what the compressed decider accepts (`Verifier.valCo_congr`). -/
def toObligationsCo (hco : G.CoSound) : ObligationsCo G U where
  n₀ := S.n₀
  compr := S.compr
  compr_spec := by
    intro c x n hn hc hsd hlen
    have hA := (S.toObligations.compr_spec c x n hn hc hsd hlen).1
    refine ⟨fun hB => ?_, hA⟩
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
    obtain ⟨hb, hrejx, hval⟩ := hB
    refine ⟨S.isBounded_compr c x n hn hc hsd hlen hb, hrej, ?_⟩
    have h1 : V.valCo (2 * n + 1) ((2 ^ n) ^ S.lam n) ≤ 1 / 2 := by
      rw [V.valCo_eq_of_rejects hans hrejx]; exact hval
    have h2 : (V.freeze (2 * n + 1)).valCo (2 ^ n) ((2 ^ n) ^ S.lam n) ≤ 1 / 2 := by
      rw [V.freeze_valCo]; exact h1
    have h3 : W.valCo n (G.bound.eval (n + S.lam n)) ≤ 1 / 2 :=
      hco _ (S.lam n) n (S.frozen_isBounded hn hb) hC₀ h2
    rw [S.ansBound_compr, ← Verifier.valCo_congr hS fun x' y' a b => (hacc n x' y' a b).symm]
    exact h3

end CompressorSpec

/-! ## The reduction -/

/-- **The halting reduction to the commuting-operator value** (blueprint `thm:halting-co`),
from an inhabitant of `ObligationsCo`: a computable map from `Nat.Partrec.Code` to game
descriptions whose game has commuting-operator value at most `1/2` when the machine halts on
the empty input and `1` when it does not.

The proof is the nested compressibility criterion at the classes `classBCo`, `classA`,
`classOne`, followed by the value agreement of the tabulation: for a halting machine the
description lies in `classBCo`, so its tabulated game has `ω_co(𝒱_n) ≤ 1/2` (`tab_valCo`); for
a non-halting one it lies in `classOne`, so its tabulated game does not have `ω_co < 1`. -/
theorem halting_reduction_co (O : ObligationsCo G U) :
    ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → commutingOperatorValue (g pc).game ≤ 1 / 2) ∧
        (¬ (pc.eval 0).Dom → commutingOperatorValue (g pc).game = 1) := by
  obtain ⟨nY, hyes⟩ := yYes_mem G U
  obtain ⟨nN, hno⟩ := yNo_memCo G U
  obtain ⟨sem, hsem_closed, hsem⟩ := exists_semCo G U
  -- the criterion's threshold: the two strings' and the compressor's, whichever is larger
  obtain ⟨g, K, hg⟩ := Cost.compressibility_criterion_nested
    (classBCo G U) (classA G U) (classOne G U) (max (max nY nN) O.n₀)
    (classA_subset_classOne G U)
    yNo (fun n hn => hno n (by omega)) yYes (fun n hn => hyes n (by omega))
    sem hsem_closed hsem O.compr (fun c x n hn => O.compr_spec c x n (by omega))
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
    rw [tab_valCo G U _ _ hx.1]
    exact hx.2.2
  · have hx := (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)
    exact commutingOperatorValue_tab_eq_one_of_mem_classOne G U hx

include U in
/-- **The halting reduction to the commuting-operator value, from co-soundness alone**: the
compressor's specification is inhabited (`exists_compressorSpec'`), and its class transfer
needs nothing but `CoSound`. -/
theorem halting_reduction_commuting_of (hco : G.CoSound) : HaltingReductionCommuting :=
  let ⟨S⟩ := exists_compressorSpec' G U
  halting_reduction_co G U (S.toObligationsCo hco)

end MIPRE.Halting
