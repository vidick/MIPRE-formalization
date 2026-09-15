/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ClassMIPStar
import MIPRE.Foundations.Halting.CostBudget
import MIPRE.Foundations.Halting.Instantiation
import MIPRE.Foundations.Halting.Semidecide

/-!
# The semidecider of the halting reduction (obligation O3)

`MIPRE.Halting.Obligations.sem_spec` asks for a closed program halting on `encode (x, n)`
exactly when the string `x` lies outside the class `B` at level `n`. By
`Verifier.not_inClassB_iff` that is a disjunction of two `Σ₁` statements — the verifier `x`
denotes is not `n`-bounded, or its `n`-th game has value more than `1/2` — and the obligation
is an *equivalence*, so both disjuncts have to be recognized exactly.

The second disjunct is the tabulation's, and is O2's to supply: with a computable game
description whose value is that of `𝒱_n`, `lem:value-lower-approx`
(`MIPRE.ValueApprox.rePred_lt_quantumValue`) enumerates the strategies. The first is proved
here, and it is the part of O3 that O2 does not contain:

* `Verifier.BoundViolation` is a witness that `λ`-boundedness fails: an index and one input of
  the sampler or the decider at that index. The index is carried as a *datum*, not a number,
  so that the encoding `encode m` under which `Decider.TimeBoundAt` reads its input is
  primitive recursive in the witness (`Data.encode_natOf`); every index arises this way
  (`Data.natOf_encode`), so nothing is lost.
* `Verifier.not_isBounded_iff_exists` is the characterization: `λ`-boundedness fails exactly
  when some witness works. Each clause of `def:lambda-bounded` is a `∀`, over indices and over
  inputs, so its negation is a search — and what makes the search effective is that
  `Prog.HaltsWithin` is decidable (`Halting/CostBudget.lean`), which needs the *cost* of a run
  and not only its length.
* `Verifier.rePred_not_isBounded`: hence, **for a computably presented family of verifiers
  (`Verifier.ComputablyPresented`), the boundedness violation is recursively enumerable**.
* `Halting.exists_sem_of_tab` merges the two disjuncts (`REPred.or`, by `Partrec.merge'`) and
  hands the result to `Cost.exists_semidecider_prod_nat`, which is `Cost.exists_semidecider`
  on pair-encoded inputs. Out comes `sem`, `sem_closed` and `sem_spec`.

## What is assumed, and why

`exists_sem_of_tab` takes the tabulation and the presentation of the family as hypotheses. Both
are O2's, and are exactly what `Obligations.tab_computable` will have to produce on the way to
itself: a `GameData` for `𝒱_n` cannot be computed without the sampler's dimension and the two
programs. Stating them rather than proving them keeps this file out of O2's way; the
mathematical content here — that the *violation* of a `∀`-clause over an infinite index set is
enumerable — is proved outright.

Two things found in the writing, both recorded in `planning/h4-assembly.md`:

1. **O3 is not "O2 plus a disjunction"**, as the plan and `Obligations`' docstring said. The
   hypothesis `hval` below asks the tabulation to have the value of `𝒱_n` for every
   `n`-bounded verifier, and `Obligations.tab_match` gives that only for a verifier
   *synchronous* at `n` — because a `GameData` describes a synchronous game by construction
   (`Obligations.tab_le`). Membership in `B` does not carry synchronicity, so the equivalence
   `sem_spec` demands is not available from `tab_match` as it stands. Three ways out are on
   the record; none is O3's to choose.
2. `Primrec fun n : ℕ => (encode n : Data)` — natural numbers encode in binary
   (`Nat.bits`) — is missing and is a prerequisite of `ComputablyPresented` for the verifier a
   string denotes, hence of O2's `tab_computable` too. The witness trick above is what keeps
   *this* file from needing it.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)

/-! ## Two closure properties of recursively enumerable predicates -/

/-- **A union of two r.e. predicates is r.e.**, by dovetailing (`Partrec.merge'`). Mathlib has
the dovetailing but not this corollary of it. -/
theorem REPred.or {α : Type*} [Primcodable α] {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∨ q a := by
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp hq
  refine hk.dom_re.of_eq fun a => ?_
  rw [(H a).2]
  exact or_congr ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩
    ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

/-- **A `Σ₁` predicate is r.e.**: an unbounded search for a witness passing a computable test.
`MIPRE.ValueApprox.REPred.of_primrecRel_exists` is the same statement for a primitive recursive
test; the tests here are only computable, the dimension of a compressed sampler being read off
a run of its program. -/
theorem REPred.of_computable_exists {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {test : α → β → Bool} (h : Computable fun q : α × β => test q.1 q.2) :
    REPred fun a => ∃ b, test a b = true := by
  have hdefault : Computable fun n : ℕ => ((Encodable.decode n : Option β).getD default) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const default)).to_comp
  have hq : Computable fun x : α × ℕ =>
      test x.1 ((Encodable.decode x.2 : Option β).getD default) :=
    h.comp (Computable.fst.pair (hdefault.comp Computable.snd))
  have hpart : Partrec fun a : α => Nat.rfind fun n =>
      (Part.some (test a ((Encodable.decode n : Option β).getD default)) : Part Bool) :=
    Partrec.rfind hq.partrec
  refine hpart.dom_re.of_eq fun a => ?_
  refine (Nat.rfind_dom' (p := fun n =>
    (Part.some (test a ((Encodable.decode n : Option β).getD default)) : Part Bool))).trans ?_
  constructor
  · rintro ⟨n, hn, _⟩
    exact ⟨_, (Part.mem_some_iff.1 hn).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨Encodable.encode b, Part.mem_some_iff.2 ?_, fun _ => trivial⟩
    rw [Encodable.encodek, Option.getD_some, hb]

/-! ## The boundedness violation -/

/-- `≤` on naturals as a primitive recursive `Bool`-valued function. `Primrec.nat_le` is a
`PrimrecRel`, which hides the `Decidable` instance behind an existential and so does not
compose with `Computable` arguments; this is the same fact in usable form. -/
theorem Cost.primrec_natLeB : Primrec fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
  obtain ⟨_, h⟩ := Primrec.nat_le
  exact h.of_eq fun p => by rw [Bool.eq_iff_iff]; simp

namespace Verifier

/-- A family of verifiers is **computably presented** when the two programs of `V a` and the
dimension of its sampler are computable in `a` — the programs as the data that encode them,
which is the form every computability statement of the ambient model takes.

This is what a computable tabulation of the games of the family needs anyway
(`MIPRE.Halting.Obligations.tab_computable`): the question weights come from running the
sampler over `𝔽₂^{s(n)}`, so `s(n)` has to be computed before anything else can be. -/
structure ComputablyPresented {α : Type*} [Primcodable α] {ℓ : ℕ} (V : α → Verifier ℓ) :
    Prop where
  /-- The sampler's program, as data. -/
  samplerProg : Computable fun a : α => (encode (V a).sampler.prog : Data)
  /-- The decider's program, as data. -/
  deciderProg : Computable fun a : α => (encode (V a).decider.prog : Data)
  /-- The dimension `s(n)` of the sampler's ambient space, uniformly in `a` and `n`. -/
  dim : Computable fun q : α × ℕ => (V q.1).sampler.dim q.2

section

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The budget the time bounds of `def:lambda-bounded` allow at index `m` on the input `d`:
`m ^ λ · (|d| + 1) ^ λ`, read off the shape of `Decider.TimeBoundAt`. -/
def boundBudget (lam m : ℕ) (d : Data) : ℕ := m ^ lam * (d.size + 1) ^ lam

/-- **A witness that `λ`-boundedness fails.** The index at which a clause of
`def:lambda-bounded` breaks is carried as a datum `w.1` — read as the number `Data.natOf w.1`,
so that the encoding `encode (Data.natOf w.1)` the two time bounds prepend to their input is
`Data.normBin w.1`, primitive recursive in the witness — and `w.2` is an input of the sampler
or of the decider at that index on which the time bound fails. -/
def BoundViolation (lam : ℕ) (w : Data × Data) : Prop :=
  ¬ V.size ≤ lam ∨
    (2 ≤ Data.natOf w.1 ∧
      (¬ V.sampler.dim (Data.natOf w.1) ≤ Data.natOf w.1 ^ lam ∨
        ¬ HaltsWithin V.sampler.prog (.cons (encode (Data.natOf w.1)) w.2)
            (boundBudget lam (Data.natOf w.1) w.2) ∨
        ¬ HaltsWithin V.decider.prog (.cons (encode (Data.natOf w.1)) w.2)
            (boundBudget lam (Data.natOf w.1) w.2)))

/-- The witness test, as a `Bool`: every clause of `BoundViolation` is decidable, the two time
bounds by `Machine.haltsWithinB` (`Halting/CostBudget.lean`). -/
def boundViolationB (lam : ℕ) (w : Data × Data) : Bool :=
  !decide (V.size ≤ lam) ||
    (decide (2 ≤ Data.natOf w.1) &&
      (!decide (V.sampler.dim (Data.natOf w.1) ≤ Data.natOf w.1 ^ lam) ||
        !Machine.haltsWithinB (encode V.sampler.prog)
            (.cons (encode (Data.natOf w.1)) w.2) (boundBudget lam (Data.natOf w.1) w.2) ||
        !Machine.haltsWithinB (encode V.decider.prog)
            (.cons (encode (Data.natOf w.1)) w.2) (boundBudget lam (Data.natOf w.1) w.2)))

theorem boundViolationB_iff (lam : ℕ) (w : Data × Data) :
    V.boundViolationB lam w = true ↔ V.BoundViolation lam w := by
  have key : ∀ (p : Prog) (x : Data) (k : ℕ),
      (Machine.haltsWithinB (encode p) x k = false) ↔ ¬ HaltsWithin p x k := fun p x k => by
    rw [← Machine.haltsWithinB_iff, Bool.not_eq_true]
  simp only [boundViolationB, BoundViolation, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, key, or_assoc]

/-- **`λ`-boundedness fails exactly when some witness works.** Each clause of
`def:lambda-bounded` is a universal statement — over indices, and over the inputs of the two
programs — so its negation is a search, and `BoundViolation` is what the search looks for. -/
theorem not_isBounded_iff_exists (lam : ℕ) :
    ¬ V.IsBounded lam ↔ ∃ w : Data × Data, V.BoundViolation lam w := by
  constructor
  · intro h
    by_cases hsize : V.size ≤ lam
    · have hmain : ¬ ∀ m, 2 ≤ m → V.sampler.dim m ≤ m ^ lam ∧
          V.sampler.TimeBoundAt m (m ^ lam) lam ∧
          V.decider.TimeBoundAt m (m ^ lam) lam := fun hm => h ⟨hm, hsize⟩
      obtain ⟨m, hm⟩ := not_forall.1 hmain
      have hm2 : 2 ≤ m := by
        by_contra hc
        exact hm fun h2 => absurd h2 hc
      have hbad : ¬ (V.sampler.dim m ≤ m ^ lam ∧ V.sampler.TimeBoundAt m (m ^ lam) lam ∧
          V.decider.TimeBoundAt m (m ^ lam) lam) := fun hb => hm fun _ => hb
      by_cases hd : V.sampler.dim m ≤ m ^ lam
      · by_cases hS : V.sampler.TimeBoundAt m (m ^ lam) lam
        · have hD : ¬ V.decider.TimeBoundAt m (m ^ lam) lam := fun hD => hbad ⟨hd, hS, hD⟩
          obtain ⟨d, hdd⟩ := not_forall.1 hD
          refine ⟨(encode m, d), Or.inr ?_⟩
          rw [Data.natOf_encode]
          exact ⟨hm2, Or.inr (Or.inr hdd)⟩
        · obtain ⟨d, hdd⟩ := not_forall.1 hS
          refine ⟨(encode m, d), Or.inr ?_⟩
          rw [Data.natOf_encode]
          exact ⟨hm2, Or.inr (Or.inl hdd)⟩
      · refine ⟨(encode m, .nil), Or.inr ?_⟩
        rw [Data.natOf_encode]
        exact ⟨hm2, Or.inl hd⟩
    · exact ⟨(.nil, .nil), Or.inl hsize⟩
  · rintro ⟨w, hw | ⟨hm2, hor⟩⟩ hb
    · exact hw hb.2
    · obtain ⟨hd, hS, hD⟩ := hb.1 (Data.natOf w.1) hm2
      rcases hor with h | h | h
      · exact h hd
      · exact h (hS _)
      · exact h (hD _)

end

/-- **The boundedness violation is recursively enumerable** for a computably presented family:
`Verifier.not_isBounded_iff_exists` turns it into a search, `Verifier.boundViolationB` runs the
test, and `REPred.of_computable_exists` does the searching. -/
theorem rePred_not_isBounded {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
    (hV : ComputablyPresented V) :
    REPred fun q : α × ℕ => ¬ (V q.1).IsBounded q.2 := by
  -- the pieces of the test, as functions of `((a, lam), w)`
  have ha : Computable fun z : (α × ℕ) × (Data × Data) => z.1.1 :=
    Computable.fst.comp Computable.fst
  have hlam : Computable fun z : (α × ℕ) × (Data × Data) => z.1.2 :=
    Computable.snd.comp Computable.fst
  have hidx : Computable fun z : (α × ℕ) × (Data × Data) => Data.natOf z.2.1 :=
    (Data.primrec_natOf.comp Primrec.fst).to_comp.comp Computable.snd
  have hinp : Computable fun z : (α × ℕ) × (Data × Data) => z.2.2 :=
    (Primrec.snd.to_comp).comp Computable.snd
  have hsize : Computable fun z : (α × ℕ) × (Data × Data) => (V z.1.1).size :=
    Primrec.nat_max.to_comp.comp (Data.primrec_size.to_comp.comp (hV.samplerProg.comp ha))
      (Data.primrec_size.to_comp.comp (hV.deciderProg.comp ha))
  have hdim : Computable fun z : (α × ℕ) × (Data × Data) =>
      (V z.1.1).sampler.dim (Data.natOf z.2.1) := hV.dim.comp (ha.pair hidx)
  have hpow : Computable fun z : (α × ℕ) × (Data × Data) => Data.natOf z.2.1 ^ z.1.2 :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp.comp hidx hlam
  have hbudget : Computable fun z : (α × ℕ) × (Data × Data) =>
      boundBudget z.1.2 (Data.natOf z.2.1) z.2.2 :=
    Primrec.nat_mul.to_comp.comp hpow
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp.comp
        (Primrec.succ.to_comp.comp ((Data.primrec_size.to_comp).comp hinp)) hlam)
  have hcfg : Computable fun z : (α × ℕ) × (Data × Data) =>
      (Data.cons (encode (Data.natOf z.2.1)) z.2.2 : Data) := by
    refine (Data.primrec_cons.to_comp.comp
      (((Data.primrec_normBin.comp Primrec.fst).to_comp).comp Computable.snd) hinp).of_eq
      fun z => ?_
    rw [Data.encode_natOf]
  have htest : Computable fun z : (α × ℕ) × (Data × Data) =>
      (V z.1.1).boundViolationB z.1.2 z.2 := by
    have hS : Computable fun z : (α × ℕ) × (Data × Data) =>
        Machine.haltsWithinB (encode (V z.1.1).sampler.prog)
          (Data.cons (encode (Data.natOf z.2.1)) z.2.2)
          (boundBudget z.1.2 (Data.natOf z.2.1) z.2.2) :=
      Computable.comp (f := fun q : (Data × Data) × ℕ => Machine.haltsWithinB q.1.1 q.1.2 q.2)
        (g := fun z : (α × ℕ) × (Data × Data) =>
          (((encode (V z.1.1).sampler.prog : Data),
            (Data.cons (encode (Data.natOf z.2.1)) z.2.2 : Data)),
            boundBudget z.1.2 (Data.natOf z.2.1) z.2.2))
        Machine.primrec_haltsWithinB.to_comp
        (((hV.samplerProg.comp ha).pair hcfg).pair hbudget)
    have hD : Computable fun z : (α × ℕ) × (Data × Data) =>
        Machine.haltsWithinB (encode (V z.1.1).decider.prog)
          (Data.cons (encode (Data.natOf z.2.1)) z.2.2)
          (boundBudget z.1.2 (Data.natOf z.2.1) z.2.2) :=
      Computable.comp (f := fun q : (Data × Data) × ℕ => Machine.haltsWithinB q.1.1 q.1.2 q.2)
        (g := fun z : (α × ℕ) × (Data × Data) =>
          (((encode (V z.1.1).decider.prog : Data),
            (Data.cons (encode (Data.natOf z.2.1)) z.2.2 : Data)),
            boundBudget z.1.2 (Data.natOf z.2.1) z.2.2))
        Machine.primrec_haltsWithinB.to_comp
        (((hV.deciderProg.comp ha).pair hcfg).pair hbudget)
    have hle1 : Computable fun z : (α × ℕ) × (Data × Data) => decide ((V z.1.1).size ≤ z.1.2) :=
      Cost.primrec_natLeB.to_comp.comp (hsize.pair hlam)
    have hle2 : Computable fun z : (α × ℕ) × (Data × Data) =>
        decide (2 ≤ Data.natOf z.2.1) :=
      (Cost.primrec_natLeB.comp ((Primrec.const 2).pair
        (Data.primrec_natOf.comp Primrec.fst))).to_comp.comp Computable.snd
    have hle3 : Computable fun z : (α × ℕ) × (Data × Data) =>
        decide ((V z.1.1).sampler.dim (Data.natOf z.2.1) ≤ Data.natOf z.2.1 ^ z.1.2) :=
      Cost.primrec_natLeB.to_comp.comp (hdim.pair hpow)
    unfold boundViolationB
    exact Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hle1)
      (Primrec.and.to_comp.comp hle2
        (Primrec.or.to_comp.comp
          (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hle3)
            (Primrec.not.to_comp.comp hS))
          (Primrec.not.to_comp.comp hD)))
  refine (REPred.of_computable_exists (β := Data × Data)
    (test := fun (q : α × ℕ) (w : Data × Data) => (V q.1).boundViolationB q.2 w)
    htest).of_eq fun q => ?_
  rw [not_isBounded_iff_exists]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, ((V q.1).boundViolationB_iff q.2 w).1 hw⟩,
    fun ⟨w, hw⟩ => ⟨w, ((V q.1).boundViolationB_iff q.2 w).2 hw⟩⟩


end Verifier

/-! ## The semidecider -/

namespace Halting

variable {G : GapCompression} {U : UniversalMachine}

/-- **Obligation O3 from the tabulation of O2.** For a computably presented family of
verifiers and a computable tabulation whose game has the value of `𝒱_n` at every `n`-bounded
string, a closed program halts on `encode (x, n)` exactly off the class `B` at level `n`:
`Obligations.sem`, `sem_closed` and `sem_spec`.

The two disjuncts of `Verifier.not_inClassB_iff` are enumerated separately — the boundedness
violation by `Verifier.rePred_not_isBounded`, the value by `lem:value-lower-approx` on the
tabulation — and merged by dovetailing (`REPred.or`). -/
theorem exists_sem_of_tab (hV : Verifier.ComputablyPresented (Vof G U))
    (tab : BitStr → ℕ → GameData) (htab : Computable fun q : BitStr × ℕ => tab q.1 q.2)
    (hval : ∀ (x : BitStr) (n : ℕ), (Vof G U x).IsBounded n →
      quantumValue (tab x n).game = (Vof G U x).valStar n (ansBound G x n)) :
    ∃ S : Prog, S.WellScoped 1 ∧
      ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ classB G U n := by
  have hre : REPred fun q : BitStr × ℕ => q.1 ∉ classB G U q.2 := by
    refine (REPred.or (Verifier.rePred_not_isBounded hV)
      (rePred_lt_quantumValue_comp htab 1 2)).of_eq fun q => ?_
    rw [Halting.mem_classB_iff, Verifier.not_inClassB_iff]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    by_cases hb : (Vof G U q.1).IsBounded q.2
    · rw [hval q.1 q.2 hb]
    · simp [hb]
  exact Cost.exists_semidecider_prod_nat (p := fun x n => x ∉ classB G U n) hre

/-- **The family `Vof` is computably presented.** All three fields, and all three are O2's:
the two programs by `computable_sampData`/`sampData_eq` and
`computable_decProgData`/`decProgData_eq`, and the third — the sampler's dimension,
*unconditionally* in the string and the level — by the re-budgeted `dimOf` read back by
`dimOf_eq`. That `dimOf_eq` carries no hypothesis is the whole point: `ComputablyPresented`
asks for the true dimension at every string and every level, including `n = 0` and `n = 1`,
and the budget `IsBounded n` supplies cannot reach those. What supplies it instead is
`GapCompression.sampler_time`, which holds for every parameter and every index. -/
theorem computablyPresented_Vof (G : GapCompression) (U : UniversalMachine) :
    Verifier.ComputablyPresented (Vof G U) where
  samplerProg := (computable_sampData G).of_eq fun x => sampData_eq G x
  deciderProg := (computable_decProgData G U).of_eq fun x => decProgData_eq G U x
  dim := (computable_dimOf_fst G).of_eq fun q => dimOf_eq G U q.1 q.2

/-- **Obligation O3, with no hypotheses left.** Both arguments of `exists_sem_of_tab` are
discharged by O2: the computable presentation by the re-budgeted sampler runs, and `hval` —
the value equality at every `n`-bounded string, in both directions and with no synchronicity
— by the doubled question set of `Foundations/GameDouble.lean`.

This is the repair blueprint `lem:halting-semidecider` records as the first of three, and the
only one that changes nothing outside the tabulation: the two alternatives were to make
`Decider.wrap` reject unequal answers at equal questions, which changes what a string
*denotes* and so reopens `accOf_iff`, the classes and `thm:compression`; or to put
synchronicity into `classB`, which moves the cost into `compr_spec`, a field of the one
obligation still open. -/
theorem exists_sem (G : GapCompression) (U : UniversalMachine) :
    ∃ S : Prog, S.WellScoped 1 ∧
      ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ classB G U n :=
  exists_sem_of_tab (computablyPresented_Vof G U) (tab G U) (tab_computable G U) (tab_value G U)

end Halting

end MIPRE
