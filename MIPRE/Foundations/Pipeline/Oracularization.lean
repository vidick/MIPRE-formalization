/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularDeciderCost
import MIPRE.Foundations.CL.DetypingDeciderTransport

/-!
# Oracularization

Blueprint `thm:oracularization` (paper `oracularization.tex`, `sec:orac-def`,
`thm:oracle-completeness` and `thm:oracle-soundness`; ledger node `1.3.5`): the structure
`Oracularization ℓ`, the specification of the typed oracularized verifier of an `ℓ + 1`-level
normal form verifier, and its inhabitant `Oracularization.construction`, which is the theorem.

The structure was first stated as an untyped, level-preserving transformation with value
transfers as fields. That statement was vacuous (`planning/oracularization.md`, finding 1): the
identity transformation with a length check satisfies it, because no field sees the *oracle
form* of the output — that one player's answer alone decides the game check, and the other's must
equal one of its components — which is the only property of oracularization answer reduction
uses. So it is restated as the specification of the construction itself:

* the sampler is `oracleSampler` (`lem:oracle-typed-sampler`): the identity for the oracle and the
  input's CL functions for the isolated players, the oracle form of the sampler being definitional;
* the decider is a total typed decider of the input programs and an index routine, computable in
  polynomial time, whose acceptance implies O2's predicate `oraclePred` at the routine's parse
  cut (`sound`: the oracle form of the decider), which accepts what `oraclePred` accepts once the
  routine's budget covers the input verifier's running time at the index (`complete`), and which
  runs within a polynomial of the budget, the cut and its input (`time`).

The index routine replaces the paper's timeout-counter form, which the ambient model does not
have (`Foundations/OracularDecider.lean`). Completeness therefore carries the budget hypothesis:
it is the input verifier's running time at the index, which the paper's timeout bound supplies.

The value transfers are theorems about every instance: for the typed game
(`typed_soundness`, `typed_completeness`), with the soundness loss `24√ε` of
`lem:oracular-soundness-tensor`; and for the detyped verifier with `ℓ + 3` levels
(`detyped`, `detyped_completeness`, `detyped_soundness`), with the loss `1536√ε` — the factor
`16³` of the detyping compiler on three types under the square root. In the paper oracularization
is not detyped on its own (finding 3): it is internal to answer reduction, whose single detyping
is at its exterior. The composition `MIPRE.GapCompression.ofPipeline` does not consume this
structure.
-/

namespace MIPRE

open Cost

namespace Oracularization

/-- The size of the core's input at the index, construction-independent: the description
lengths of the input programs, the parse cut, the index, the dimension and the answer cut. -/
def inputSize {ℓ : ℕ} (V : Verifier (ℓ + 1)) (B n T : ℕ) : ℕ :=
  esize V.sampler.prog + esize V.decider.prog + esize B + esize n + V.sampler.dim n + T

end Oracularization

/-- **Oracularization** (blueprint `thm:oracularization`), for `ℓ + 1`-level inputs: the
specification of the typed oracularized decider, the sampler being `oracleSampler`. An instance
is the theorem (`Oracularization.construction`). -/
structure Oracularization (ℓ : ℕ) where
  /-- The typed decider, of the input sampler's and decider's programs and an index routine. -/
  decider : Prog → Prog → OracleDecider.Index → CL.Detyping.TypedDecider Role
  /-- Its program, a polynomial-time function of the three programs. -/
  compute : PolyTimeFun (Prog × Prog × Prog) Prog
  compute_eq : ∀ (sp dp : Prog) (I : OracleDecider.Index),
    compute (sp, dp, I.prog) = (decider sp dp I).prog
  /-- It halts on every input, whatever the input programs do. -/
  total : ∀ (sp dp : Prog) (I : OracleDecider.Index), (decider sp dp I).Total
  /-- **The oracle form**: it accepts only what `oraclePred` accepts at the routine's cut. -/
  sound : ∀ (V : Verifier (ℓ + 1)) (I : OracleDecider.Index) (n : ℕ) (t u : Role)
    (x y : V.Questions n) (a b : BitStr),
    (decider V.sampler.prog V.decider.prog I).Accepts n t (CL.toBits x) u (CL.toBits y) a b →
    oraclePred (V.seeded n (I.cut n)) (t, x) (u, y) a b = true
  /-- The constants of the budget. -/
  budgetCoeff : ℕ
  budgetDeg : ℕ
  budgetExp : ℕ
  /-- **Completeness of the acceptance law**: it accepts what `oraclePred` accepts, on answers
  within an answer cut `T`, once the budget covers the input verifier's running time. -/
  complete : ∀ (V : Verifier (ℓ + 1)) (I : OracleDecider.Index) (T n TS TD k W : ℕ),
    V.sampler.TimeBoundAt n TS k → V.decider.TimeBoundAt n TD k → TS ≤ W → TD ≤ W →
    budgetCoeff * (W + 1) ^ budgetDeg *
      (Oracularization.inputSize V (I.cut n) n T + 1) ^ (budgetExp * (k + 1)) ≤ I.budget n →
    ∀ (t u : Role) (x y : V.Questions n) (a b : BitStr), a.length ≤ T → b.length ≤ T →
      oraclePred (V.seeded n (I.cut n)) (t, x) (u, y) a b = true →
      (decider V.sampler.prog V.decider.prog I).Accepts n t (CL.toBits x) u (CL.toBits y) a b
  /-- The constants of the running time. -/
  timeCoeff : ℕ
  timeDeg : ℕ
  timeExp : ℕ
  /-- **The running time**: within a polynomial of the budget, the cut, the index routine's time,
  the description lengths and the index, at a degree in the input that does not depend on the
  input verifier. -/
  time : ∀ (sp dp : Prog) (I : OracleDecider.Index) (n TI W : ℕ),
    HaltsWithin I.prog (encode n) TI → esize sp ≤ W → esize dp ≤ W → esize I.prog ≤ W →
    n ≤ W → I.budget n ≤ W → I.cut n ≤ W → TI ≤ W → ∀ d : Data,
      HaltsWithin (decider sp dp I).prog (.cons (encode n) d)
        (timeCoeff * (W + 1) ^ timeDeg * (d.size + 1) ^ timeExp)

namespace Oracularization

variable {ℓ : ℕ} (O : Oracularization ℓ)

/-! ## The typed game -/

section Typed

open CL.Detyping.DeciderProgram (typedPredicate)

variable (V : Verifier (ℓ + 1)) (I : OracleDecider.Index) (C : CL.Detyping.CutoffProgram)

/-- The typed game of the oracularized verifier of `𝒱` at index `n`: the detyping compiler's
typed game of `oracleSampler` and the decider, on the complete graph over the roles. -/
noncomputable abbrev typedGame (n : ℕ) :=
  CL.Detyping.typedGame roleGraph roleGraph_nonempty (fun _ => roleFamily (V.sampler.cl n))
    (typedPredicate (oracleSampler V.sampler) (O.decider V.sampler.prog V.decider.prog I) C n)

/-- **Soundness of the typed oracularized verifier**: its typed game's quantum value above `1 - ε`
puts `val*(𝒱_n)` at the parse cut at least `1 - 24√ε`, whatever the budget. -/
theorem typed_soundness (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue (O.typedGame V I C n)) : 1 - 24 * √ε ≤ V.valStar n (I.cut n) :=
  V.valStar_ge_of_typed n (I.cut n) _ (fun p a => (parseAns (I.cut n) p.1 a.1).getD default)
    (fun p q a b hD => by
      simp only [typedPredicate, decide_eq_true_eq] at hD
      exact oaccepts_of_oraclePred (O.sound V I n p.1 q.1 p.2 q.2 a.1 b.1 hD.2.2)) hε h

/-- **Completeness of the typed oracularized verifier**: a value-`1` PCC strategy of `𝒱_n` at the
parse cut gives one of the doubled typed game, with identical operators for the two players (the
synchronous framework's), when the inner cut holds every honest encoding and the budget covers
the input verifier's running time. -/
theorem typed_completeness (n TS TD k W : ℕ) (hS : V.sampler.TimeBoundAt n TS k)
    (hD : V.decider.TimeBoundAt n TD k) (hTS : TS ≤ W) (hTD : TD ≤ W)
    (hin : 8 * I.cut n + 3 ≤ C.inner n) (hout : C.inner n ≤ C.outer n)
    (hK : O.budgetCoeff * (W + 1) ^ O.budgetDeg *
      (inputSize V (I.cut n) n (C.inner n) + 1) ^ (O.budgetExp * (k + 1)) ≤ I.budget n)
    (hV : V.HasPerfectPCC n (I.cut n)) :
    ∃ R : SyncStrategy (O.typedGame V I C n).doubled, R.IsPCC ∧ R.value = 1 :=
  V.exists_typed_perfectPCC n (I.cut n) hV _
    (fun U => ⟨encAns U, ((length_encAns_le U).trans hin).trans hout⟩)
    (fun p q U W' h => by
      have hU := (length_encAns_le U).trans hin
      have hW := (length_encAns_le W').trans hin
      simp only [typedPredicate, decide_eq_true_eq]
      exact ⟨hU, hW, O.complete V I (C.inner n) n TS TD k W hS hD hTS hTD hK p.1 q.1 p.2 q.2 _ _
        hU hW (oraclePred_encAns h)⟩)

end Typed

/-! ## The detyped verifier -/

section Detyped

variable (V : Verifier (ℓ + 1)) (I : OracleDecider.Index) (C : CL.Detyping.CutoffProgram)

/-- **The detyped oracularized verifier**, with `ℓ + 3` levels: the typed oracularized verifier
through the detyping compiler (`lem:detype-compiler`) at the cutoff program `C`. -/
noncomputable def detyped : Verifier (ℓ + 1 + 2) :=
  CL.Detyping.DeciderProgram.verifier roleGraph (oracleSampler V.sampler)
    (O.decider V.sampler.prog V.decider.prog I) C (Nat.succ_pos ℓ) (O.total _ _ _)

/-- **Completeness of the detyped oracularized verifier.** -/
theorem detyped_completeness (n TS TD k W : ℕ) (hS : V.sampler.TimeBoundAt n TS k)
    (hD : V.decider.TimeBoundAt n TD k) (hTS : TS ≤ W) (hTD : TD ≤ W)
    (hin : 8 * I.cut n + 3 ≤ C.inner n) (hout : C.inner n ≤ C.outer n)
    (hK : O.budgetCoeff * (W + 1) ^ O.budgetDeg *
      (inputSize V (I.cut n) n (C.inner n) + 1) ^ (O.budgetExp * (k + 1)) ≤ I.budget n)
    (hV : V.HasPerfectPCC n (I.cut n)) :
    (O.detyped V I C).HasPerfectPCC n (C.outer n) := by
  obtain ⟨R, hR, hv⟩ := O.typed_completeness V I C n TS TD k W hS hD hTS hTD hin hout hK hV
  exact CL.Detyping.DeciderProgram.verifier_hasPerfectPCC roleGraph (oracleSampler V.sampler)
    (O.decider V.sampler.prog V.decider.prog I) C roleGraph_symm roleGraph_nonempty
    (Nat.succ_pos ℓ) (O.total _ _ _) n R hR hv

theorem card_role : Fintype.card Role = 3 := rfl

/-- **Soundness of the detyped oracularized verifier**: `val*` above `1 - ε` at the outer cut puts
`val*(𝒱_n)` at the parse cut at least `1 - 1536√ε`, whatever the budget — the detyping factor
`16³` on the three roles, under the square root, times the `24` of the typed game. -/
theorem detyped_soundness (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < (O.detyped V I C).valStar n (C.outer n)) :
    1 - 1536 * √ε ≤ V.valStar n (I.cut n) := by
  by_contra hcon
  rw [not_le] at hcon
  have hsq : √(4096 * ε) = 64 * √ε := by
    rw [Real.sqrt_mul (by norm_num), show (4096 : ℝ) = 64 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  by_cases hε1 : ε ≤ 1
  · have hall : ∀ R : TensorProductStrategy ((O.detyped V I C).game n (C.outer n)),
        R.value ≤ 1 - ε := by
      intro R
      by_contra hR
      rw [not_le] at hR
      obtain ⟨δ, hδ⟩ : ∃ δ, δ = 1 - R.value := ⟨_, rfl⟩
      have h1 := CL.Detyping.DeciderProgram.restrictAmbient_value_ge roleGraph
        (oracleSampler V.sampler) (O.decider V.sampler.prog V.decider.prog I) C roleGraph_symm
        roleGraph_nonempty (Nat.succ_pos ℓ) (O.total _ _ _) n R (ε := δ)
        (by rw [hδ]; exact le_of_eq (sub_sub_cancel _ _))
      rw [card_role] at h1
      have h2 : (CL.Detyping.DeciderProgram.restrictAmbient roleGraph (oracleSampler V.sampler)
          (O.decider V.sampler.prog V.decider.prog I) C roleGraph_nonempty (Nat.succ_pos ℓ)
          (O.total _ _ _) n R).value ≤ quantumValue (O.typedGame V I C n) :=
        le_ciSup (TensorProductStrategy.bddAbove_range_value _) _
      have h3 : 1 - 4096 * ε < quantumValue (O.typedGame V I C n) := by
        norm_num at h1
        nlinarith
      have h4 := O.typed_soundness V I C n (by positivity : 0 < 4096 * ε) h3
      rw [hsq] at h4
      linarith
    have h5 : (O.detyped V I C).valStar n (C.outer n) ≤ 1 - ε :=
      Real.iSup_le hall (by linarith)
    linarith
  · rw [not_le] at hε1
    have h1 : 1 < √ε := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt zero_le_one hε1
    have h2 := quantumValue_nonneg (V.game n (I.cut n))
    change quantumValue (V.game n (I.cut n)) < _ at hcon
    linarith

end Detyped

/-! ## The construction -/

/-- The core's input bound is below a power of the construction-independent one. -/
theorem coreInputBound_le {ℓ : ℕ} (V : Verifier (ℓ + 1)) (B n T : ℕ) :
    OracleDecider.coreInputBound V B n T + 1 ≤ (inputSize V B n T + 1) ^ 28 := by
  have h1 : 1 ≤ esize V.sampler.prog := Data.size_pos _
  have h := OracleDecider.affine_le_pow (a := 8) (b := 20)
    (show 2 ≤ inputSize V B n T + 1 by unfold inputSize; omega)
  have hlin : OracleDecider.coreInputBound V B n T + 1 ≤ 8 * (inputSize V B n T + 1) + 20 := by
    unfold OracleDecider.coreInputBound inputSize; omega
  exact hlin.trans h

/-- **Oracularization** (blueprint `thm:oracularization`): the typed oracularized decider of
`Foundations/OracularDecider.lean`, with the running times of
`Foundations/OracularDeciderCost.lean`, inhabits the specification. -/
noncomputable def construction (ℓ : ℕ) : Oracularization ℓ where
  decider := OracleDecider.oracleDecider (ℓ + 1)
  compute := OracleDecider.deciderProgFun (ℓ + 1)
  compute_eq := OracleDecider.deciderProgFun_apply (ℓ + 1)
  total := OracleDecider.oracleDecider_total (ℓ + 1)
  sound V I n t u x y a b h := OracleDecider.accepts_sound V I n t u x y a b h
  budgetCoeff := (OracleDecider.budget_sufficient ℓ).choose
  budgetDeg := (OracleDecider.budget_sufficient ℓ).choose_spec.choose
  budgetExp := 28 * (OracleDecider.budget_sufficient ℓ).choose_spec.choose_spec.choose
  complete V I T n TS TD k W hS hD hTS hTD hK t u x y a b ha hb h :=
    OracleDecider.accepts_complete V I n t u x y a b h
      ((OracleDecider.budget_sufficient ℓ).choose_spec.choose_spec.choose_spec V I T n TS TD k W
        hS hD hTS hTD (le_trans (Nat.mul_le_mul_left _ (le_trans
          (Nat.pow_le_pow_left (coreInputBound_le V (I.cut n) n T) _)
          (le_of_eq (by rw [← pow_mul, mul_assoc])))) hK) t u x y a b ha hb)
  timeCoeff := (OracleDecider.oracleDecider_timeBound (ℓ + 1)).choose
  timeDeg := (OracleDecider.oracleDecider_timeBound (ℓ + 1)).choose_spec.choose
  timeExp := (OracleDecider.oracleDecider_timeBound (ℓ + 1)).choose_spec.choose_spec.choose
  time := (OracleDecider.oracleDecider_timeBound (ℓ + 1)).choose_spec.choose_spec.choose_spec

end Oracularization

end MIPRE
