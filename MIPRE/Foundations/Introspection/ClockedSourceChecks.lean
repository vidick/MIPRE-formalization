/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockedQueryProgram
import MIPRE.Foundations.Introspection.AuxiliarySamplingCorrect
import MIPRE.Foundations.Introspection.SourceCompilerCorrect

/-! # Source-game checks using the shared explicit clock

The final decision kernel receives the exponential index and unary clock
once. These polynomial-time checks reuse that resource for Sample and
cross-Introspect, with precisely the guards of the earlier source compiler.
-/

noncomputable section
namespace MIPRE.Introspection.ClockedSourceChecks
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram SourceCompiler

abbrev SampleInput := Unary × Prog × SamplingInput
abbrev CrossInput := Unary × Prog × GuardInput

/-- The sampling query uses the already reindexed source input. -/
def sampling (U : ClockedUniversalMachine) : PolyTimeFun SampleInput Bool :=
  let fields : PolyTimeFun SampleInput SamplingInput := snd.comp snd
  let run := (ClockedQuery.run U).comp
    (fst.pair ((fst.comp snd).pair (samplingCall.comp fields)))
  andCheck (samplingReady.comp fields) (equal run (samplingExpected.comp fields))

theorem sampling_iff (U : ClockedUniversalMachine) (b : Unary) (S : Prog)
    (x : SamplingInput) :
    sampling U (b, S, x) = true ↔ SamplingReady x ∧
      clockedResult S (samplingCall x) b.length = samplingExpected x := by
  simp only [sampling, andCheck_iff, equal_iff, comp_apply, pair_apply,
    fst_apply, snd_apply, ClockedQuery.run_apply, samplingReady_iff]

/-- A source decision call checks both canonical padded questions and all
original answer cutoffs before evaluating the bounded source program. -/
def cross (U : ClockedUniversalMachine) : PolyTimeFun CrossInput Bool :=
  let fields : PolyTimeFun CrossInput GuardInput := snd.comp snd
  let run := (ClockedQuery.run U).comp
    (fst.pair ((fst.comp snd).pair (projectedCall.comp fields)))
  andCheck (guardCheck.comp fields) (equal run (const (.cons (encode true) (encode true))))

theorem cross_iff (U : ClockedUniversalMachine) (b : Unary) (D : Prog)
    (x : GuardInput) :
    cross U (b, D, x) = true ↔ GuardReady x ∧
      clockedResult D (projectedCall x) b.length = .cons (encode true) (encode true) := by
  simp only [cross, andCheck_iff, equal_iff, comp_apply, pair_apply,
    fst_apply, snd_apply, const_apply, ClockedQuery.run_apply, guardCheck_iff]

/-- The shared-clock sampling check is exactly the previously verified
clock-computing program, after moving index preparation outside the kernel. -/
theorem sampling_eq_program (U : ClockedUniversalMachine) (k lam n j Q R s : ℕ)
    (S : Prog) (w : Bool) (a b : BitStr) :
    sampling U (unary (ansBound k lam n), S, j, w, 2 ^ n, Q, R, s, a, b) = true ↔
      ∃ t, (samplingProg k lam U S).Runs (encode (j,w,n,Q,R,s,a,b)) (encode true) t := by
  rw [sampling_iff, samplingProg_accepts_iff]
  simp only [SamplingRawReady, readSamplingInput_encode, true_and, length_unary]
  have hr : SamplingReady (j,w,2 ^ n,Q,R,s,a,b) = SamplingReady (j,w,n,Q,R,s,a,b) := rfl
  rw [hr]
  apply and_congr_right
  intro _
  rw [samplingResult, samplingCall_apply, samplingCall_apply]
  have hi : ClockSimulation.indexReader
      (encode (n,CL.Sampler.Query.marginal (Player.ofBool w) j
        ((rightParts (n,Q,R,s,a,b)).1.take s))) = n := readNat_encode n
  change clockedResult S (encode (2 ^ n,CL.Sampler.Query.marginal (Player.ofBool w) j
      ((rightParts (n,Q,R,s,a,b)).1.take s))) (ansBound k lam n) = _ ↔ _
  simp only [inputIndex, inputDim, comp_apply, fst_apply, snd_apply]
  have he : ClockSimulation.reindexed (encode (n,CL.Sampler.Query.marginal (Player.ofBool w) j
      ((rightParts (n,Q,R,s,a,b)).1.take s))) = encode (2 ^ n,
      CL.Sampler.Query.marginal (Player.ofBool w) j ((rightParts (n,Q,R,s,a,b)).1.take s)) :=
    ClockSimulation.reindexed_cons n _
  rw [hi, he]
  rfl

/-- Exact full-register Sample semantics for the actual padded source. -/
theorem sampling_depthFamily {ℓ lam n Q R : ℕ} (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓR : Nat.size ℓ ≤ (2 ^ n) ^ lam) (hs : V.sampler.dim (2 ^ n) ≤ Q)
    (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q) (w : Bool)
    (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    sampling U (unary (ansBound 5 lam n), V.sampler.prog, ℓ, w, 2 ^ n, Q, R,
      V.sampler.dim (2 ^ n), AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.pairBits (CL.toBits z) b) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧
      CLChecks.sampling (SourcePadding.depthFamily (firstEmbedding hs)
        (fun w => V.sampler.cl (2 ^ n) (Player.ofBool w)) w) (y,a) (z,b) := by
  rw [sampling_eq_program]
  exact samplingProg_depthFamily U V hV hn hℓ hℓR hs hQ hR w y z a b

/-- Exact source-game acceptance on the original legal alphabet. -/
theorem cross_original {ℓ lam n Q : ℕ} (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (s : ℕ) (a b : BitStr) :
    let x : GuardInput := (2 ^ n,Q,(2 ^ n)^lam,s,a,b)
    cross U (unary (ansBound 5 lam n), V.decider.prog, x) = true ↔
      GuardReady x ∧ V.decider.Accepts (2 ^ n)
        ((leftParts x).1.take s) ((rightParts x).1.take s)
        (leftParts x).2 (rightParts x).2 := by
  dsimp only
  rw [cross_iff, length_unary, projectedCall_apply, CL.Detyping.ClockProgram.clockedResult_eq_iff]
  constructor
  · rintro ⟨hg,t,_,hr⟩
    exact ⟨hg,t,hr⟩
  · rintro ⟨hg,t,hr⟩
    obtain ⟨hx,hy,ha,hb⟩ := GuardReady_cutoffs hg
    obtain ⟨r,time,ht,hout⟩ := original_decider_haltsWithin V hV hn _ _ _ _ hx hy ha hb
    exact ⟨hg,t,(hout.deterministic hr).2 ▸ ht,hr⟩

end MIPRE.Introspection.ClockedSourceChecks
end
