/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourceCompilerCorrect
import MIPRE.Foundations.Introspection.SourceCompilerParamsCost

/-! # Composed execution cost of the actual source component

This accounts for parameter generation, the clocked sampler dimension query,
format checks, source-question unpadding, and the clocked original decider.
The bound applies to all raw inputs and arbitrary source program texts.
-/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program

def callCost (route : PolyTimeFun Data (Bool × Data)) (post : PolyTimeFun (Data × Data) Data)
    (x a ctx : Data) (T : ℕ) : ℕ :=
  route.timeBound.eval x.size + 3*a.size + 3*ctx.size + T+T +
    post.timeBound.eval (ctx.size+T+1) + 18

theorem call_runs_cost (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) {p : Prog} (hp : p.WellScoped 1)
    (x a ctx r : Data) (T t : ℕ) (ht : t ≤ T)
    (hroute : route x = (true,.cons a ctx)) (hr : p.Runs a r t) :
    ∃ time ≤ callCost route post x a ctx T,
      (routeOneCall route p post).Runs x (post (ctx,r)) time := by
  obtain ⟨time,hb,hh⟩ := routeOneCall_indirect_cost route hp post x a ctx r t hroute hr
  have hs : r.size ≤ T := hr.size_le.trans ht
  have hm := polynomial_eval_mono post.timeBound (Nat.add_le_add_right (Nat.add_le_add_left hs ctx.size) 1)
  refine ⟨time,hb.trans ?_,hh⟩
  dsimp only [callCost]
  omega

def conditionalCost (route : PolyTimeFun Data (Bool × Data)) (x a : Data) (T : ℕ) : ℕ :=
  callCost route snd x a .nil T + 5

theorem conditional_haltsWithin (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (x a : Data) (T : ℕ)
    (ready : Prop) [Decidable ready]
    (hroute : route x = if ready then (true,.cons a .nil) else (false,encode false))
    (hr : HaltsWithin p a T) :
    HaltsWithin (routeOneCall route p snd) x (conditionalCost route x a T) := by
  by_cases h : ready
  · obtain ⟨r,t,ht,hh⟩ := hr
    obtain ⟨time,hb,hout⟩ := call_runs_cost route snd hp x a .nil r T t ht
      (by rw [hroute,if_pos h]) hh
    exact ⟨r,time,hb.trans (Nat.le_add_right _ _),hout⟩
  · obtain ⟨time,hb,hout⟩ := routeOneCall_direct_cost route p snd x (encode false)
      (by rw [hroute,if_neg h])
    refine ⟨_,time,hb.trans ?_,hout⟩
    change _ + 1 + 4 ≤ _
    dsimp only [conditionalCost,callCost]
    omega

def projectedCost (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog) (x : Data) : ℕ :=
  conditionalCost projectedRoute x (projectedCall (readInput x))
    (ClockSimulation.simulationCost k lam U D (projectedCall (readInput x)))

theorem projectedProg_haltsWithin (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog) (x : Data) :
    HaltsWithin (projectedProg (ClockSimulation.decider k lam U D).prog) x (projectedCost k lam U D x) :=
  conditional_haltsWithin projectedRoute (ClockSimulation.decider k lam U D).closed x _ _
    (RawReady x) (projectedRoute_apply x) (ClockSimulation.decider_haltsWithin k lam U D _)

def finalCost (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog) (x : Data) : ℕ :=
  conditionalCost finalRoute x (encode (finalInput x))
    (projectedCost k lam U D (encode (finalInput x)))

theorem finalStage_haltsWithin (k lam : ℕ) (U : ClockedUniversalMachine) (D : Prog) (x : Data) :
    HaltsWithin (finalStage k lam U D) x (finalCost k lam U D x) :=
  conditional_haltsWithin finalRoute (projectedProg_closed (ClockSimulation.decider k lam U D).closed)
    x _ _ (Prepared x) (finalRoute_apply x) (projectedProg_haltsWithin k lam U D _)

def rawSimulationCost (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) : ℕ :=
  ClockSimulation.clockStageCost k lam x +
    ClockSimulation.reindexStageCost S x (ansBound k lam (ClockSimulation.indexReader x)) +
    U.bound.eval (ansBound k lam (ClockSimulation.indexReader x) + esize S +
      (ClockSimulation.reindexed x).size) + 2

theorem rawSimulation_runs_cost (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) :
    ∃ time ≤ rawSimulationCost k lam U S x, (ClockSimulation.prog k lam U S).Runs x
      (clockedResult S (ClockSimulation.reindexed x) (ansBound k lam (ClockSimulation.indexReader x))) time := by
  obtain ⟨tc,htc,hc⟩ := ClockSimulation.clockStage_runs_cost k lam x
  obtain ⟨tr,htr,hr⟩ := ClockSimulation.reindexStage_runs_cost S x
    (ansBound k lam (ClockSimulation.indexReader x))
  obtain ⟨tu,htu,hu⟩ := U.run S (ClockSimulation.reindexed x)
    (ansBound k lam (ClockSimulation.indexReader x))
  refine ⟨_,?_,Eval.let_ hc (Eval.append_of_wellScoped
    (Eval.let_ hr (Eval.append_of_wellScoped hu U.closed _))
    ⟨ClockSimulation.reindexStage_closed S,U.closed.mono (by omega) _⟩ _)⟩
  dsimp only [rawSimulationCost]
  omega

def parameterCost (c lam : ℕ) (x : Data) : ℕ :=
  callCost ClockProgram.clockRoute treePair x (encode (ClockSimulation.indexReader x)) x
    (boundsCost c lam (ClockSimulation.indexReader x) + esize lam + esize (ClockSimulation.indexReader x) + 3)

theorem parameterStage_runs_cost (c lam : ℕ) (x : Data) : ∃ t ≤ parameterCost c lam x,
    (parameterStage c lam).Runs x (.cons x
      (encode (registerBits c lam (ClockSimulation.indexReader x),
        originalBound lam (ClockSimulation.indexReader x)))) t := by
  obtain ⟨t,ht,hr⟩ := boundsProg_runs_cost c lam (ClockSimulation.indexReader x)
  exact call_runs_cost ClockProgram.clockRoute treePair (hardcode_wellScoped (boundsProg_closed c) _)
    x _ x _ _ _ (by change t + esize lam + esize (ClockSimulation.indexReader x) + 3 ≤ _; omega)
      rfl (hardcode_time (boundsProg_closed c) hr)

def dimensionCost (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x bounds : Data) : ℕ :=
  callCost dimensionRoute treePair (.cons x bounds)
    (encode (ClockSimulation.indexReader x,CL.Sampler.Query.dimension)) (.cons x bounds)
    (rawSimulationCost k lam U S (encode (ClockSimulation.indexReader x,CL.Sampler.Query.dimension)))

theorem dimensionStage_runs_cost (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog)
    (x bounds : Data) : ∃ t ≤ dimensionCost k lam U S x bounds,
      (dimensionStage k lam U S).Runs (.cons x bounds)
        (.cons (.cons x bounds) (dimensionResult k lam S (ClockSimulation.indexReader x))) t := by
  obtain ⟨t,ht,hr⟩ := rawSimulation_runs_cost k lam U S
    (encode (ClockSimulation.indexReader x,CL.Sampler.Query.dimension))
  obtain ⟨time,hb,hout⟩ := call_runs_cost dimensionRoute treePair
    (ClockSimulation.prog_closed k lam U S) (.cons x bounds) _ (.cons x bounds) _ _ t ht
      (by simp [dimensionRoute,encode_prod]) hr
  refine ⟨time,hb,?_⟩
  have hi : ClockSimulation.indexReader (encode
      (ClockSimulation.indexReader x,CL.Sampler.Query.dimension)) = ClockSimulation.indexReader x := readNat_encode _
  have he : ClockSimulation.reindexed (encode (ClockSimulation.indexReader x,CL.Sampler.Query.dimension)) =
      encode (2^ClockSimulation.indexReader x,CL.Sampler.Query.dimension) := ClockSimulation.reindexed_cons _ _
  simpa only [treePair_apply,hi,he,dimensionResult,dimensionStage] using hout

def crossCost (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog) (x : Data) : ℕ :=
  parameterCost c lam x + dimensionCost k lam U S x
    (encode (registerBits c lam (ClockSimulation.indexReader x),originalBound lam (ClockSimulation.indexReader x))) +
    finalCost k lam U D (preparedData c k lam S x) + 2

/-- A compositional cost bound for every raw input, without source halting assumptions. -/
theorem crossProg_haltsWithin (c k lam : ℕ) (U : ClockedUniversalMachine) (S D : Prog) (x : Data) :
    HaltsWithin (crossProg c k lam U S D) x (crossCost c k lam U S D x) := by
  obtain ⟨t₁,ht₁,h₁⟩ := parameterStage_runs_cost c lam x
  obtain ⟨t₂,ht₂,h₂⟩ := dimensionStage_runs_cost k lam U S x
    (encode (registerBits c lam (ClockSimulation.indexReader x),originalBound lam (ClockSimulation.indexReader x)))
  obtain ⟨r,t₃,ht₃,h₃⟩ := finalStage_haltsWithin k lam U D (preparedData c k lam S x)
  refine ⟨r,_,?_,Eval.let_ h₁ (Eval.append_of_wellScoped
    (Eval.let_ h₂ (Eval.append_of_wellScoped h₃ (finalStage_closed k lam U D) _))
    ⟨dimensionStage_closed k lam U S,(finalStage_closed k lam U D).mono (by omega) _⟩ _)⟩
  dsimp only [crossCost]
  omega

end MIPRE.Introspection.SourceCompiler

end
