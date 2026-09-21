/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourceCompiler

/-! # Exact acceptance of the cross-introspection compiler

For a bounded original verifier the actual dimension query fits the clock.
Acceptance is precisely the complete format/cutoff/projection guard followed
by acceptance of the original decider at the exponential index.
-/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program

def preparedData (c k lam : ℕ) (S : Prog) (x : Data) : Data :=
  .cons (.cons x (encode (registerBits c lam (ClockSimulation.indexReader x),
    originalBound lam (ClockSimulation.indexReader x))))
    (dimensionResult k lam S (ClockSimulation.indexReader x))

theorem crossProg_run_final (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    (x r : Data) (t : ℕ) (hr : (finalStage k lam U D).Runs (preparedData c k lam S x) r t) :
    ∃ time, (crossProg c k lam U S D).Runs x r time := by
  obtain ⟨t₁,h₁⟩ := parameterStage_runs c lam x
  obtain ⟨t₂,h₂⟩ := dimensionStage_runs k lam U S x
    (encode (registerBits c lam (ClockSimulation.indexReader x),
      originalBound lam (ClockSimulation.indexReader x)))
  exact ⟨_,Eval.let_ h₁ (Eval.append_of_wellScoped
    (Eval.let_ h₂ (Eval.append_of_wellScoped hr (finalStage_closed k lam U D) _))
    ⟨dimensionStage_closed k lam U S,(finalStage_closed k lam U D).mono (by omega) _⟩ _)⟩

theorem crossProg_accepts_final (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    (x : Data) : (∃ t, (crossProg c k lam U S D).Runs x (encode true) t) ↔
      ∃ t, (finalStage k lam U D).Runs (preparedData c k lam S x) (encode true) t := by
  obtain ⟨r,t,hr⟩ := finalStage_halts k lam U D (preparedData c k lam S x)
  obtain ⟨time,ht⟩ := crossProg_run_final c k lam U S D x r t hr
  constructor
  · rintro ⟨ta,ha⟩
    exact ⟨t,(ht.deterministic ha).1 ▸ hr⟩
  · rintro ⟨ta,ha⟩
    exact ⟨time,(hr.deterministic ha).1 ▸ ht⟩

theorem finalStage_accepts_iff (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog)
    (x : Data) : (∃ t, (finalStage k lam U D).Runs x (encode true) t) ↔
      Prepared x ∧ GuardReady (finalInput x) ∧ ∃ t,
        (ClockSimulation.decider k lam U D).prog.Runs (projectedCall (finalInput x)) (encode true) t := by
  have hp := projectedProg_accepts_iff (ClockSimulation.decider k lam U D).closed
    (ClockSimulation.decider_halts k lam U D) (encode (finalInput x))
  simp only [RawReady, readInput_encode, true_and] at hp
  by_cases h : Prepared x
  · obtain ⟨r,t,hr⟩ := projectedProg_halts (ClockSimulation.decider k lam U D).closed
      (ClockSimulation.decider_halts k lam U D) (encode (finalInput x))
    obtain ⟨time,ht⟩ := routeOneCall_indirect finalRoute
      (projectedProg_closed (ClockSimulation.decider k lam U D).closed) snd x _ .nil r t
      (by rw [finalRoute_apply,if_pos h]) hr
    constructor
    · rintro ⟨ta,ha⟩
      exact ⟨h,hp.mp ⟨t,(ht.deterministic ha).1 ▸ hr⟩⟩
    · rintro ⟨_,hh⟩
      obtain ⟨ta,ha⟩ := hp.mpr hh
      exact ⟨time,(hr.deterministic ha).1 ▸ ht⟩
  · obtain ⟨time,ht⟩ := routeOneCall_direct finalRoute
      (projectedProg (ClockSimulation.decider k lam U D).prog) snd x (encode false)
      (by rw [finalRoute_apply,if_neg h])
    constructor
    · rintro ⟨ta,ha⟩
      cases encode_injective (ht.deterministic ha).1
    · rintro ⟨hh,_⟩
      exact (h hh).elim

/-- The actual sampler query, rather than an assumed dimension subroutine, fits exponent five. -/
theorem bounded_dimensionResult {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) : dimensionResult 5 lam V.sampler.prog n =
      .cons (encode true) (encode (V.sampler.dim (2^n))) := by
  have hl : 1 ≤ lam := by have := hV.two_le; omega
  have hR : 1 ≤ (2^n)^lam := Nat.one_le_pow _ _ (by positivity)
  have hsize : esize CL.Sampler.Query.dimension + 1 ≤
      esize (([false] : BitStr),([false] : BitStr),([false] : BitStr),([false] : BitStr)) + 1 := by decide
  have hb := legal_query_cost_le hl hn [false] [false] [false] [false] hR hR hR hR
  obtain ⟨r,t,ht,hr⟩ := (hV.1 (2^n) ((two_le_exp_index_iff n).mpr hn)).2.1
    (encode CL.Sampler.Query.dimension)
  obtain ⟨td,hd⟩ := V.sampler.runs_dimension (2^n)
  rw [dimensionResult, ClockProgram.clockedResult_eq_iff]
  refine ⟨t,ht.trans (?_ : (2^n)^lam * (esize CL.Sampler.Query.dimension+1)^lam ≤ ansBound 5 lam n),
    (hr.deterministic hd).1 ▸ hr⟩
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize lam)).trans hb

theorem finalInput_canonical (n Q R s : ℕ) (a b : BitStr) :
    finalInput (.cons (.cons (encode (n,a,b)) (encode (Q,R))) (.cons (encode true) (encode s))) =
      (n,Q,R,s,a,b) := by
  simp [finalInput, originalInput, returnedDimension, AnswerParser.guardIndex,
    AnswerParser.guardLeft, AnswerParser.guardRight, encode_prod, readNat_encode, readBits_encode]

theorem prepared_canonical (n Q R s : ℕ) (a b : BitStr) :
    Prepared (.cons (.cons (encode (n,a,b)) (encode (Q,R))) (.cons (encode true) (encode s))) := by
  simp [Prepared, originalInput, returnedDimension, AnswerParser.guardIndex,
    AnswerParser.guardLeft, AnswerParser.guardRight, encode_prod, readNat_encode, readBits_encode]

/-- Exact source-game interpretation, including the internal original-answer cutoff.
The sole verifier hypothesis is its existing boundedness definition. -/
theorem crossProg_original_iff {ℓ lam n : ℕ} (c : ℕ) (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (a b : BitStr) :
    (∃ t, (crossProg c 5 lam U V.sampler.prog V.decider.prog).Runs (encode (n,a,b)) (encode true) t) ↔
      let x : GuardInput := (n,registerBits c lam n,originalBound lam n,V.sampler.dim (2^n),a,b)
      GuardReady x ∧ V.decider.Accepts (2^n)
        ((leftParts x).1.take (inputDim x)) ((rightParts x).1.take (inputDim x))
        (leftParts x).2 (rightParts x).2 := by
  let x : GuardInput := (n,registerBits c lam n,originalBound lam n,V.sampler.dim (2^n),a,b)
  have hi : ClockSimulation.indexReader (encode (n,a,b)) = n := readNat_encode n
  rw [crossProg_accepts_final,finalStage_accepts_iff]
  simp only [preparedData,hi,bounded_dimensionResult V hV hn,finalInput_canonical,
    prepared_canonical,true_and]
  change (GuardReady x ∧ ∃ t, (ClockSimulation.decider 5 lam U V.decider.prog).prog.Runs
    (projectedCall x) (encode true) t) ↔ _
  rw [projectedCall_apply]
  constructor
  · rintro ⟨h,ha⟩
    obtain ⟨hx,hy,ha',hb⟩ := GuardReady_cutoffs h
    simp only [inputR, comp_apply, fst_apply, snd_apply, x, originalBound_eq] at hx hy ha' hb
    exact ⟨h,(ClockSimulation.original_decider_preserved U V hV hn _ _ _ _ hx hy ha' hb).mp ha⟩
  · rintro ⟨h,ha⟩
    obtain ⟨hx,hy,ha',hb⟩ := GuardReady_cutoffs h
    simp only [inputR, comp_apply, fst_apply, snd_apply, originalBound_eq] at hx hy ha' hb
    exact ⟨h,(ClockSimulation.original_decider_preserved U V hV hn _ _ _ _ hx hy ha' hb).mpr ha⟩

end MIPRE.Introspection.SourceCompiler

end
