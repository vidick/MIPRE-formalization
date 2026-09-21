/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockCompiler

/-! # Runtime of the complete clocked exponential-index simulation -/

noncomputable section

namespace MIPRE.Introspection.ClockSimulation

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program ClockArithmetic Polynomial

def reindexCost (x : Data) : ℕ :=
  let n := indexReader x
  indexReader.timeBound.eval x.size + unaryCost n + (n + 2) * (4 * n + 20) +
    esize (2 ^ n) + x.size + treeTail.timeBound.eval x.size + 10

theorem reindexProg_runs_cost (x : Data) :
    ∃ time ≤ reindexCost x, reindexProg.Runs x (reindexed x) time := by
  obtain ⟨ti, hti, hi⟩ := indexReader.computes x
  obtain ⟨tu, htu, hu⟩ := toUnaryProg_runs (indexReader x)
  obtain ⟨te, hte, he⟩ := expBitsProg_runs (indexReader x)
  obtain ⟨td, htd, hd⟩ := treeTail.computes x
  refine ⟨_, ?_, Eval.let_ hi (Eval.let_ (Eval.append_of_wellScoped hu toUnaryProg_wellScoped _)
    (Eval.let_ (Eval.append_of_wellScoped he expBitsProg_wellScoped _)
      (Eval.cons (Eval.var_of_get (i := 0) (by simp))
        (callVar_eval (i := 3) treeTail.closed (by simp) hd))))⟩
  change tu ≤ unaryCost (indexReader x) at htu
  change te ≤ (indexReader x + 2) * (4 * indexReader x + 20) at hte
  simp only [esize_data, encode_data] at *
  change ti + (tu + (te + ((esize (2 ^ indexReader x) + 1) + (x.size + 1 + td + 1) + 1) + 1) + 1) + 1 ≤ _
  dsimp only [reindexCost]
  omega

def clockStageCost (k lam : ℕ) (x : Data) : ℕ :=
  let n := indexReader x
  let B := ansBound k lam n
  ClockProgram.clockRoute.timeBound.eval x.size + 3 * esize n + 3 * x.size + (2 * B + 1) +
    (uniformCost k lam n + esize lam + esize n + 3) +
    treePair.timeBound.eval (x.size + (2 * B + 1) + 1) + 18

theorem clockStage_runs_cost (k lam : ℕ) (x : Data) :
    ∃ time ≤ clockStageCost k lam x,
      (clockStage k lam).Runs x (.cons x (.ofNat (ansBound k lam (indexReader x)))) time := by
  obtain ⟨tc, htc, hc⟩ := growingClock_runs k lam (indexReader x)
  obtain ⟨t, ht, hr⟩ := routeOneCall_indirect_cost ClockProgram.clockRoute
    (growingClock k lam).closed treePair x (encode (indexReader x)) x
      (.ofNat (ansBound k lam (indexReader x))) tc rfl hc
  refine ⟨t, ht.trans ?_, hr⟩
  simp only [Data.size_ofNat]
  dsimp only [clockStageCost]
  change _ + tc + _ + _ ≤ _
  have he : (encode (indexReader x)).size = esize (indexReader x) := rfl
  omega

def reindexStageCost (source : Prog) (x : Data) (B : ℕ) : ℕ :=
  2 * x.size + 2 * (2 * B + 1) + (reindexed x).size + reindexCost x +
    ((2 * B + 1) + (reindexed x).size + 1 + (esize source + 4)) + 12

theorem reindexStage_runs_cost (source : Prog) (x : Data) (B : ℕ) :
    ∃ time ≤ reindexStageCost source x B, (reindexStage source).Runs (.cons x (.ofNat B))
      (.cons (.ofNat B) (.cons (encode source) (reindexed x))) time := by
  obtain ⟨tr, htr, hr⟩ := reindexProg_runs_cost x
  obtain ⟨t, ht, hout⟩ := callWithContext_cost reindexProg_closed (simulationInput source)
    x (.ofNat B) (reindexed x) tr hr
  refine ⟨t, ht.trans ?_, hout⟩
  simp only [Data.size_ofNat, simulationInput, eval_add, eval_X, eval_C]
  dsimp only [reindexStageCost]
  omega

def simulationCost (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) (x : Data) : ℕ :=
  let B := ansBound k lam (indexReader x)
  let G := U.bound.eval (B + esize source + (reindexed x).size)
  clockStageCost k lam x + reindexStageCost source x B + G +
    ClockProgram.checkResult.timeBound.eval G + 3

/-- An explicit bound for every input, including malformed indices and queries. -/
theorem decider_haltsWithin (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) (x : Data) :
    HaltsWithin (decider k lam U source).prog x (simulationCost k lam U source x) := by
  let B := ansBound k lam (indexReader x)
  let G := U.bound.eval (B + esize source + (reindexed x).size)
  obtain ⟨tc, htc, hc⟩ := clockStage_runs_cost k lam x
  obtain ⟨tr, htr, hr⟩ := reindexStage_runs_cost source x B
  obtain ⟨tu, htu, hu⟩ := U.run source (reindexed x) B
  obtain ⟨tp, htp, hp⟩ := ClockProgram.checkResult.computes (clockedResult source (reindexed x) B)
  have hres : (clockedResult source (reindexed x) B).size ≤ G := hu.size_le.trans htu
  have htpG : tp ≤ ClockProgram.checkResult.timeBound.eval G :=
    htp.trans (polynomial_eval_mono _ hres)
  refine ⟨_, _, ?_, Eval.let_ (Eval.let_ hc (Eval.append_of_wellScoped
    (Eval.let_ hr (Eval.append_of_wellScoped hu U.closed _))
      ⟨reindexStage_closed source, U.closed.mono (by omega) _⟩ _))
    (Eval.append_of_wellScoped hp ClockProgram.checkResult.closed _)⟩
  change tu ≤ G at htu
  change _ ≤ clockStageCost k lam x + reindexStageCost source x B + G +
    ClockProgram.checkResult.timeBound.eval G + 3
  omega

def reindexCostPoly : Polynomial ℕ :=
  let L := 64 * X
  indexReader.timeBound.comp L + unaryCostPoly + (X + 2) * (4 * X + 20) +
    L + L + treeTail.timeBound.comp L + 10

def clockStageCostPoly (k : ℕ) : Polynomial ℕ :=
  let L := 64 * X
  ClockProgram.clockRoute.timeBound.comp L + 3 * (4 * X + 1) + 3 * L + (2 * X + 1) +
    clockCostPoly k + treePair.timeBound.comp (L + (2 * X + 1) + 1) + 18

def reindexStageCostPoly : Polynomial ℕ :=
  let L := 64 * X
  2 * L + 2 * (2 * X + 1) + L + reindexCostPoly +
    ((2 * X + 1) + L + 1 + (X + 4)) + 12

def simulationCostPoly (k : ℕ) (U : ClockedUniversalMachine) : Polynomial ℕ :=
  let G := U.bound.comp (X + X + 64 * X)
  clockStageCostPoly k + reindexStageCostPoly + G +
    ClockProgram.checkResult.timeBound.comp G + 3

theorem reindexCost_le {x : Data} {B : ℕ} (hn : indexReader x ≤ B)
    (hx : x.size ≤ 64 * B) (hout : (reindexed x).size ≤ 64 * B) :
    reindexCost x ≤ reindexCostPoly.eval B := by
  have hi := polynomial_eval_mono indexReader.timeBound hx
  have ht := polynomial_eval_mono treeTail.timeBound hx
  have hu := unaryCost_le hn
  have he := Nat.mul_le_mul (Nat.add_le_add_right hn 2)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hn) 20)
  have hp : esize (2 ^ indexReader x) ≤ 64 * B := by
    change esize (2 ^ indexReader x) + (treeTail x).size + 1 ≤ 64 * B at hout
    omega
  simp only [reindexCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_comp]
  dsimp only [reindexCost]
  omega

theorem clockStageCost_le {k lam : ℕ} {x : Data}
    (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ indexReader x)
    (hx : x.size ≤ 64 * ansBound k lam (indexReader x)) :
    clockStageCost k lam x ≤ (clockStageCostPoly k).eval (ansBound k lam (indexReader x)) := by
  obtain ⟨_, hnB, _, _⟩ := clock_arguments_le hk hl hn
  have hi := polynomial_eval_mono ClockProgram.clockRoute.timeBound hx
  have he := esize_le_value hnB
  have hc := growingClock_cost_le hk hl hn
  have hp := polynomial_eval_mono treePair.timeBound
    (Nat.add_le_add_right (Nat.add_le_add_right hx (2 * ansBound k lam (indexReader x) + 1)) 1)
  simp only [clockStageCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one, eval_comp]
  dsimp only [clockStageCost]
  omega

/-- Uniform polynomial overhead in the budget, once it dominates the source and inputs. -/
theorem simulationCost_le {k lam : ℕ} (U : ClockedUniversalMachine) (source : Prog) (x : Data)
    (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ indexReader x)
    (hcode : esize source ≤ ansBound k lam (indexReader x))
    (hx : x.size ≤ 64 * ansBound k lam (indexReader x))
    (hout : (reindexed x).size ≤ 64 * ansBound k lam (indexReader x)) :
    simulationCost k lam U source x ≤ (simulationCostPoly k U).eval (ansBound k lam (indexReader x)) := by
  let B := ansBound k lam (indexReader x)
  obtain ⟨_, hnB, _, _⟩ := clock_arguments_le hk hl hn
  have hri := reindexCost_le hnB hx hout
  have hclock := clockStageCost_le hk hl hn hx
  have hstage : reindexStageCost source x B ≤ reindexStageCostPoly.eval B := by
    simp only [reindexStageCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
    dsimp only [reindexStageCost]
    change (reindexed x).size ≤ 64 * B at hout
    change x.size ≤ 64 * B at hx
    change esize source ≤ B at hcode
    change reindexCost x ≤ reindexCostPoly.eval B at hri
    omega
  have hU : U.bound.eval (B + esize source + (reindexed x).size) ≤
      U.bound.eval (B + B + 64 * B) := polynomial_eval_mono _ (by omega)
  have hcheck := polynomial_eval_mono ClockProgram.checkResult.timeBound hU
  simp only [simulationCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_comp]
  dsimp only [simulationCost]
  change clockStageCost k lam x ≤ (clockStageCostPoly k).eval B at hclock
  change _ ≤ (clockStageCostPoly k).eval B + reindexStageCostPoly.eval B +
    U.bound.eval (B + B + 64 * B) + ClockProgram.checkResult.timeBound.eval
      (U.bound.eval (B + B + 64 * B)) + 3
  dsimp only [B] at *
  omega

theorem legal_input_sizes {k lam n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (x y a b : BitStr)
    (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
    (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
    esize (n, x, y, a, b) ≤ 64 * ansBound k lam n ∧
      esize (2 ^ n, x, y, a, b) ≤ 64 * ansBound k lam n := by
  obtain ⟨_, hnB, _, _⟩ := clock_arguments_le hk hl hn
  have hR : (2 ^ n) ^ lam ≤ ansBound k lam n := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have hm : lam * n + 1 ≤ (lam * n + 1) ^ k := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ lam * n + 1) hk
    nlinarith
  have hs := legal_query_size_le _ x y a b hx hy ha hb
  have hi := esize_le_value hnB
  have he := esize_nat_le (2 ^ n)
  rw [Nat.size_pow] at he
  have hB : 1 ≤ ansBound k lam n := Nat.one_le_pow _ _ (by decide)
  simp only [esize_prod] at hs ⊢
  omega

/-- A uniform absolute runtime for the entire compiled clocked decider, including
clock generation, index conversion, simulation and the final result check. -/
theorem decider_ansBound_time (k : ℕ) (hk : 1 ≤ k) (U : ClockedUniversalMachine) :
    ∃ C, ∀ (lam n : ℕ) (source : Prog), 1 ≤ lam → 1 ≤ n → esize source ≤ lam →
      ∀ x y a b : BitStr,
      x.length ≤ (2 ^ n) ^ lam → y.length ≤ (2 ^ n) ^ lam →
      a.length ≤ (2 ^ n) ^ lam → b.length ≤ (2 ^ n) ^ lam →
      HaltsWithin (decider k lam U source).prog (encode (n, x, y, a, b)) (ansBound C lam n) := by
  obtain ⟨C, hC⟩ := polynomial_ansBound (simulationCostPoly k U) k
  refine ⟨C, fun lam n source hl hn hsource x y a b hx hy ha hb => ?_⟩
  have hi : indexReader (encode (n, x, y, a, b)) = n := readNat_encode n
  have he : reindexed (encode (n, x, y, a, b)) = encode (2 ^ n, x, y, a, b) :=
    reindexed_cons n (encode (x, y, a, b))
  obtain ⟨hs, hr⟩ := legal_input_sizes hk hl hn x y a b hx hy ha hb
  have hlB := (clock_arguments_le hk hl hn).1
  have hbnd := simulationCost_le U source (encode (n, x, y, a, b)) hk hl
    (by simpa only [hi] using hn) (by simpa only [hi] using hsource.trans hlB)
    (by simpa only [hi, esize] using hs) (by simpa only [hi, he, esize] using hr)
  rw [hi] at hbnd
  obtain ⟨r, time, ht, hrun⟩ := decider_haltsWithin k lam U source (encode (n, x, y, a, b))
  exact ⟨r, time, ht.trans (hbnd.trans (hC lam n hl hn)), hrun⟩

theorem original_decider_ansBound_time (U : ClockedUniversalMachine) :
    ∃ C, ∀ {ℓ lam n : ℕ} (V : Verifier ℓ), V.IsBounded lam → 1 ≤ n →
      ∀ x y a b : BitStr,
      x.length ≤ (2 ^ n) ^ lam → y.length ≤ (2 ^ n) ^ lam →
      a.length ≤ (2 ^ n) ^ lam → b.length ≤ (2 ^ n) ^ lam →
      HaltsWithin (decider 5 lam U V.decider.prog).prog (encode (n, x, y, a, b))
        (ansBound C lam n) := by
  obtain ⟨C, hC⟩ := decider_ansBound_time 5 (by decide) U
  refine ⟨C, fun V hV hn => hC _ _ _ (by have := hV.two_le; omega) hn ?_⟩
  exact (le_max_right V.sampler.size V.decider.size).trans hV.2

end MIPRE.Introspection.ClockSimulation
