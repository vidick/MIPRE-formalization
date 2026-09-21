/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourceCompilerParams
import MIPRE.Foundations.Introspection.SourceCompilerGuard
import MIPRE.Foundations.Introspection.ParserGuard
import MIPRE.Foundations.Introspection.ClockCompiler

/-! # Actual cross-introspection source compiler

The program computes the canonical register parameters, calls the original
sampler's dimension query at `2^n`, validates and unpads both Introspect
answers, then calls the original decider at `2^n`. Both source calls are
clocked. It is total on every raw input, for arbitrary source program texts.
This is the cross-Introspect edge component, not the remaining typed dispatch.
-/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program

def parameterStage (c lam : ℕ) : Prog :=
  routeOneCall ClockProgram.clockRoute (hardcode (boundsProg c) (encode lam)) treePair

theorem parameterStage_closed (c lam : ℕ) : (parameterStage c lam).WellScoped 1 :=
  routeOneCall_closed _ (hardcode_wellScoped (boundsProg_closed c) _) _

theorem parameterStage_runs (c lam : ℕ) (x : Data) : ∃ t,
    (parameterStage c lam).Runs x (.cons x
      (encode (registerBits c lam (ClockSimulation.indexReader x),
        originalBound lam (ClockSimulation.indexReader x)))) t := by
  obtain ⟨t,ht⟩ := boundsProg_runs c lam (ClockSimulation.indexReader x)
  exact routeOneCall_indirect _ (hardcode_wellScoped (boundsProg_closed c) _) treePair
    x _ x _ _ rfl (hardcode_time (boundsProg_closed c) ht)

def dimensionRoute : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair
    (encoded.comp ((ClockSimulation.indexReader.comp treeHead).pair
      (const CL.Sampler.Query.dimension))) (PolyTimeFun.id Data))

def dimensionStage (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) : Prog :=
  routeOneCall dimensionRoute (ClockSimulation.prog k lam U S) treePair

theorem dimensionStage_closed (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) :
    (dimensionStage k lam U S).WellScoped 1 :=
  routeOneCall_closed _ (ClockSimulation.prog_closed k lam U S) _

def dimensionResult (k lam : ℕ) (S : Prog) (n : ℕ) : Data :=
  clockedResult S (encode (2^n,CL.Sampler.Query.dimension)) (ansBound k lam n)

theorem dimensionStage_runs (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog)
    (x bounds : Data) : ∃ t, (dimensionStage k lam U S).Runs (.cons x bounds)
      (.cons (.cons x bounds) (dimensionResult k lam S (ClockSimulation.indexReader x))) t := by
  obtain ⟨t,ht⟩ := ClockSimulation.prog_runs k lam U S
    (encode (ClockSimulation.indexReader x,CL.Sampler.Query.dimension))
  have he : ClockSimulation.indexReader (encode
      (ClockSimulation.indexReader x,CL.Sampler.Query.dimension)) = ClockSimulation.indexReader x :=
    readNat_encode _
  rw [he] at ht
  rw [show encode (ClockSimulation.indexReader x,CL.Sampler.Query.dimension) =
      Data.cons (encode (ClockSimulation.indexReader x)) (encode CL.Sampler.Query.dimension) from rfl,
    ClockSimulation.reindexed_cons] at ht
  exact routeOneCall_indirect _ (ClockSimulation.prog_closed k lam U S) treePair
    (.cons x bounds) _ (.cons x bounds) _ t (by simp [dimensionRoute, encode_prod]) ht

def originalInput : PolyTimeFun Data Data := treeHead.comp treeHead
def returnedDimension : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp treeTail)

def finalInput : PolyTimeFun Data GuardInput :=
  (AnswerParser.guardIndex.comp originalInput).pair
    ((readNat.comp (treeHead.comp (treeTail.comp treeHead))).pair
      ((readNat.comp (treeTail.comp (treeTail.comp treeHead))).pair
        (returnedDimension.pair ((AnswerParser.guardLeft.comp originalInput).pair
          (AnswerParser.guardRight.comp originalInput)))))

def Prepared (x : Data) : Prop :=
  originalInput x = encode (AnswerParser.guardIndex (originalInput x),
    AnswerParser.guardLeft (originalInput x),AnswerParser.guardRight (originalInput x)) ∧
  treeTail x = .cons (encode true) (encode (returnedDimension x))

instance (x : Data) : Decidable (Prepared x) := inferInstanceAs (Decidable (_ ∧ _))

def finalRoute : PolyTimeFun Data (Bool × Data) :=
  let orig := originalInput
  let canonical := encoded.comp ((AnswerParser.guardIndex.comp orig).pair
    ((AnswerParser.guardLeft.comp orig).pair (AnswerParser.guardRight.comp orig)))
  let success := ap₂ treePair (const (encode true)) (encoded.comp returnedDimension)
  let call := (const true).pair (ap₂ treePair (encoded.comp finalInput) (const Data.nil))
  let reject := const (false,encode false)
  ite (ap₂ treeEq orig canonical) (ite (ap₂ treeEq treeTail success) call reject) reject

theorem finalRoute_apply (x : Data) : finalRoute x = if Prepared x then
    (true,.cons (encode (finalInput x)) .nil) else (false,encode false) := by
  simp only [finalRoute, PolyTimeFun.ite_apply, ap₂_apply, comp_apply, treeEq_apply,
    encoded_apply, pair_apply, const_apply, treePair_apply, decide_eq_true_eq]
  by_cases hc : originalInput x = encode (AnswerParser.guardIndex (originalInput x),
      AnswerParser.guardLeft (originalInput x),AnswerParser.guardRight (originalInput x))
  · rw [if_pos hc]
    by_cases hr : treeTail x = .cons (encode true) (encode (returnedDimension x))
    · rw [if_pos hr,if_pos (show Prepared x from ⟨hc,hr⟩)]
    · rw [if_neg hr,if_neg (show ¬ Prepared x from fun h => hr h.2)]
  · rw [if_neg hc,if_neg (show ¬ Prepared x from fun h => hc h.1)]

def finalStage (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog) : Prog :=
  routeOneCall finalRoute (projectedProg (ClockSimulation.decider k lam U D).prog) snd

theorem finalStage_closed (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog) :
    (finalStage k lam U D).WellScoped 1 :=
  routeOneCall_closed _ (projectedProg_closed (ClockSimulation.decider k lam U D).closed) _

theorem finalStage_halts (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog) (x : Data) :
    Halts (finalStage k lam U D) x := by
  by_cases h : Prepared x
  · obtain ⟨r,t,ht⟩ := projectedProg_halts (ClockSimulation.decider k lam U D).closed
      (ClockSimulation.decider_halts k lam U D) (encode (finalInput x))
    obtain ⟨time,hr⟩ := routeOneCall_indirect finalRoute
      (projectedProg_closed (ClockSimulation.decider k lam U D).closed) snd x _ .nil r t
      (by rw [finalRoute_apply,if_pos h]) ht
    exact ⟨r,time,hr⟩
  · obtain ⟨t,ht⟩ := routeOneCall_direct finalRoute _ snd x (encode false)
      (by rw [finalRoute_apply,if_neg h])
    exact ⟨_,t,ht⟩

/-- The actual three-stage cross-Introspect component. -/
def crossProg (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog) : Prog :=
  .let_ (parameterStage c lam) (.let_ (dimensionStage k lam U S) (finalStage k lam U D))

theorem crossProg_closed (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog) :
    (crossProg c k lam U S D).WellScoped 1 :=
  ⟨parameterStage_closed c lam, (dimensionStage_closed k lam U S).mono (by omega) _,
    (finalStage_closed k lam U D).mono (by omega) _⟩

theorem crossProg_halts (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog) (x : Data) :
    Halts (crossProg c k lam U S D) x := by
  obtain ⟨t₁,h₁⟩ := parameterStage_runs c lam x
  obtain ⟨t₂,h₂⟩ := dimensionStage_runs k lam U S x
    (encode (registerBits c lam (ClockSimulation.indexReader x),
      originalBound lam (ClockSimulation.indexReader x)))
  obtain ⟨r,t₃,h₃⟩ := finalStage_halts k lam U D _
  exact ⟨r,_,Eval.let_ h₁ (Eval.append_of_wellScoped
    (Eval.let_ h₂ (Eval.append_of_wellScoped h₃ (finalStage_closed k lam U D) _))
    ⟨dimensionStage_closed k lam U S,(finalStage_closed k lam U D).mono (by omega) _⟩ _)⟩

end MIPRE.Introspection.SourceCompiler

end
