/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.DecisionPreparation

/-! # Uniform costs for one shared introspection resource preparation -/

noncomputable section
namespace MIPRE.Introspection.DecisionPreparation
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial

theorem esize_two_pow_le (n : ℕ) : esize (2 ^ n) ≤ 4 * n + 5 := by
  have h := esize_nat_le (2 ^ n)
  rw [Nat.size_pow] at h
  omega

def boundsMajorant (c v : ℕ) : ℕ :=
  let h := PauliSamplerParameters.widthBound c v
  2 * PauliSamplerParameters.unaryMajorant v + 2 * (4*v+1) + 4*v+20 +
    ClockArithmetic.mulCost v v + (parameterSeed c).timeBound.eval (2*v+1) +
    (14*h+9 + (exponentBitsCost h + PauliSamplerParameters.unaryMajorant h+1) +
      parameterPost.timeBound.eval (6*h+5)+12) +
    (16*h+13 + exponentBitsCost h + boundsPost.timeBound.eval (8*h+9)+12)+4

theorem boundsCost_le_majorant {c lam n v : ℕ} (hc : 1 ≤ c)
    (hl : lam ≤ v) (hn : n ≤ v) (hu : lam*n ≤ v) :
    boundsCost c lam n ≤ boundsMajorant c v := by
  obtain ⟨hk,hj,hm⟩ := PauliSamplerParameters.parameters_le_widthBound hc hu
  have hv : v ≤ PauliSamplerParameters.widthBound c v := by
    have := Nat.mul_le_mul_right (v+2) hc
    unfold PauliSamplerParameters.widthBound
    omega
  have hul := PauliSamplerParameters.unaryCost_le hl
  have hun := PauliSamplerParameters.unaryCost_le hn
  have hel := ClockArithmetic.esize_le_value hl
  have hen := ClockArithmetic.esize_le_value hn
  have hmul := ClockArithmetic.mulCost_le hl hn
  have hseed := polynomial_eval_mono (parameterSeed c).timeBound
    (show 2*(lam*n)+1 ≤ 2*v+1 by omega)
  have hpower : powerUnaryCost (PauliSamplerParameters.selectorBits c lam n) ≤
      exponentBitsCost (PauliSamplerParameters.widthBound c v) +
        PauliSamplerParameters.unaryMajorant (PauliSamplerParameters.widthBound c v) + 1 := by
    have hexp : exponentBitsCost (PauliSamplerParameters.selectorBits c lam n) ≤
        exponentBitsCost (PauliSamplerParameters.widthBound c v) := by unfold exponentBitsCost; gcongr
    have hconv := PauliSamplerParameters.unaryCost_le hm
    change ClockArithmetic.unaryCost (2 ^ PauliSamplerParameters.selectorBits c lam n) ≤ _ at hconv
    unfold powerUnaryCost
    omega
  have hparam := polynomial_eval_mono parameterPost.timeBound
    (show 2*(lam*n)+1+(2*fieldBits c lam n+1)+1+(2*registerPower c lam n+1)+1 ≤
      6*PauliSamplerParameters.widthBound c v+5 by omega)
  have htwo := esize_two_pow_le (lam*n)
  have hbound := polynomial_eval_mono boundsPost.timeBound
    (show 2*registerPower c lam n+1+(2*fieldBits c lam n+1)+1+esize (2^(lam*n))+1 ≤
      8*PauliSamplerParameters.widthBound c v+9 by omega)
  have hexp : exponentBitsCost (lam*n) ≤ exponentBitsCost (PauliSamplerParameters.widthBound c v) := by
    unfold exponentBitsCost
    gcongr <;> omega
  have hmul' : ClockArithmetic.mulCost lam n ≤ ClockArithmetic.mulCost v v := by
    unfold ClockArithmetic.mulCost
    gcongr
  unfold boundsCost boundsMajorant contextCost
  change (encode (2^(lam*n))).size ≤ 4*(lam*n)+5 at htwo
  change boundsPost.timeBound.eval
    (2*registerPower c lam n+1+(2*fieldBits c lam n+1)+1+(encode (2^(lam*n))).size+1) ≤ _ at hbound
  simp only [Data.size_cons, Data.size_ofNat]
  change _ + _ + _ + _ + _ + _ + _ + _ + _ ≤ _
  dsimp only [PauliSamplerParameters.selectorBits] at hj hpower
  omega

theorem boundsMajorant_polyBounded (c : ℕ) : PolyBounded (boundsMajorant c) := by
  unfold boundsMajorant PauliSamplerParameters.widthBound PauliSamplerParameters.unaryMajorant
    ClockArithmetic.mulCost exponentBitsCost
  repeat' first
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.eval
    | apply PolyBounded.const
    | exact PolyBounded.id

/-- Cost of appending a result, with input and subroutine costs bounded by
fixed polynomials of the same resource parameter. -/
def appendPoly (arg : PolyTimeFun Data Data) (p q : Polynomial ℕ) : Polynomial ℕ :=
  (appendRoute arg).timeBound.comp p + 3 * arg.timeBound.comp p + 3 * p + q + q +
    treePair.timeBound.comp (p+q+1) + 18

theorem appendStage_runs_poly (arg : PolyTimeFun Data Data) {code : Prog}
    (hcode : code.WellScoped 1) (p q : Polynomial ℕ) (v : ℕ) (x r : Data)
    (hx : x.size ≤ p.eval v) (t : ℕ) (ht : t ≤ q.eval v) (hr : code.Runs (arg x) r t) :
    ∃ time ≤ (appendPoly arg p q).eval v,
      (appendStage arg code).Runs x (.cons x r) time := by
  obtain ⟨s, hs, hout⟩ := call_runs_cost (appendRoute arg) treePair hcode x (arg x) x r
    (q.eval v) t ht rfl hr
  have harg := arg.esize_apply_le x
  have hmarg := polynomial_eval_mono arg.timeBound hx
  have hmroute := polynomial_eval_mono (appendRoute arg).timeBound hx
  have hmpost := polynomial_eval_mono treePair.timeBound
    (Nat.add_le_add_right (Nat.add_le_add_right hx (q.eval v)) 1)
  refine ⟨s, hs.trans ?_, hout⟩
  simp only [appendPoly, eval_add, eval_mul, eval_comp, eval_ofNat, eval_one]
  change (arg x).size ≤ arg.timeBound.eval x.size at harg
  dsimp only [callCost]
  omega

def clockPoly : Polynomial ℕ := ClockArithmetic.clockCostPoly 5
def pauliPoly (c : ℕ) : Polynomial ℕ := (PauliSamplerParameters.costMajorant_polyBounded c).poly
def boundsPoly (c : ℕ) : Polynomial ℕ := (boundsMajorant_polyBounded c).poly
def firstPoly : Polynomial ℕ := appendPoly parameterInput X clockPoly
def secondPoly : Polynomial ℕ := firstPoly +
  appendPoly (inputRaw.comp treeHead) firstPoly ClockSimulation.reindexCostPoly + 1
def thirdPoly (c : ℕ) : Polynomial ℕ := secondPoly +
  appendPoly (parameterInput.comp (treeHead.comp treeHead)) secondPoly (pauliPoly c) + 1
def fourthPoly (c : ℕ) : Polynomial ℕ := thirdPoly c +
  appendPoly (parameterInput.comp (treeHead.comp (treeHead.comp treeHead)))
    (thirdPoly c) (boundsPoly c) + 1
def preparationPoly (c : ℕ) : Polynomial ℕ := fourthPoly c + finish.timeBound.comp (fourthPoly c) + 1

theorem finish_boundsResult (c : ℕ) (z : Data) :
    finish (boundsResult c z) = encode (resources c z) := by
  simp [boundsResult, pauliResult, indexResult, clockResult, finish, origin,
    preparedClock, preparedIndex, preparedParameters, ClockSimulation.reindexed,
    inputIndex, resources, encode_prod, encode_unary]

set_option backward.isDefEq.respectTransparency false in
/-- All preparation work is polynomial in a common bound for the original
input and the one shared clock. The theorem keeps zero parameters separate. -/
theorem prog_runs_poly {c v : ℕ} (hc : 1 ≤ c) (z : Data)
    (hl : 1 ≤ inputLambda z) (hn : 1 ≤ inputIndex z)
    (hz : z.size ≤ v) (hB : ansBound 5 (inputLambda z) (inputIndex z) ≤ v) :
    ∃ time ≤ (preparationPoly c).eval v,
      (prog c).Runs z (encode (resources c z)) time := by
  obtain ⟨hlB, hnB, huB, _⟩ := ClockArithmetic.clock_arguments_le (by decide : 1 ≤ 5) hl hn
  have hlv := hlB.trans hB
  have hnv := hnB.trans hB
  have huv : inputLambda z * inputIndex z ≤ v := by omega
  have hv : 1 ≤ v := hl.trans hlv
  obtain ⟨t₁, ht₁, h₁⟩ := ClockArithmetic.uniformProg_runs 5 (inputLambda z) (inputIndex z)
  have hc₁ := ClockArithmetic.growingClock_cost_le (by decide : 1 ≤ 5) hl hn
  have hc₂ := polynomial_eval_mono (ClockArithmetic.clockCostPoly 5) hB
  have htc : t₁ ≤ clockPoly.eval v := by unfold clockPoly; omega
  obtain ⟨s₁, hts₁, hs₁⟩ := appendStage_runs_poly parameterInput
    (ClockArithmetic.uniformProg_closed 5) X clockPoly v z _
      (by simpa using hz) t₁ htc h₁
  change (clockStage).Runs z (clockResult z) s₁ at hs₁
  change s₁ ≤ firstPoly.eval v at hts₁
  have hz₁ : (clockResult z).size ≤ firstPoly.eval v := hs₁.size_le.trans hts₁
  have hx : (inputRaw z).size ≤ v := (Machine.size_right_le z).trans hz
  have htail : (treeTail (inputRaw z)).size ≤ v :=
    (Machine.size_right_le (inputRaw z)).trans hx
  have hpow := esize_two_pow_le (inputIndex z)
  have hout : (ClockSimulation.reindexed (inputRaw z)).size ≤ 64*v := by
    change esize (2^inputIndex z) + (treeTail (inputRaw z)).size + 1 ≤ 64*v
    omega
  obtain ⟨t₂, ht₂, h₂⟩ := ClockSimulation.reindexProg_runs_cost (inputRaw z)
  have hri := ClockSimulation.reindexCost_le hnv (show (inputRaw z).size ≤ 64*v by omega) hout
  obtain ⟨s₂, hts₂, hs₂⟩ := appendStage_runs_poly (inputRaw.comp treeHead)
    ClockSimulation.reindexProg_closed firstPoly ClockSimulation.reindexCostPoly v
    (clockResult z) _ hz₁ t₂ (ht₂.trans hri) h₂
  change indexStage.Runs (clockResult z) (indexResult z) s₂ at hs₂
  have hz₂ : (indexResult z).size ≤ secondPoly.eval v := by
    have := hs₂.size_le
    simp only [secondPoly, eval_add, eval_one]
    omega
  obtain ⟨t₃, ht₃, h₃⟩ := PauliSamplerParameters.prog_runs_cost c (inputLambda z) (inputIndex z)
  have hp₃ := PauliSamplerParameters.cost_le_majorant hc hlv hnv huv
  have hq₃ := (PauliSamplerParameters.costMajorant_polyBounded c).le_poly_eval v
  obtain ⟨s₃, hts₃, hs₃⟩ := appendStage_runs_poly
    (parameterInput.comp (treeHead.comp treeHead)) (PauliSamplerParameters.prog_closed c)
    secondPoly (pauliPoly c) v (indexResult z) _ hz₂ t₃ (ht₃.trans (hp₃.trans hq₃)) h₃
  change (pauliStage c).Runs (indexResult z) (pauliResult c z) s₃ at hs₃
  have hz₃ : (pauliResult c z).size ≤ (thirdPoly c).eval v := by
    have := hs₃.size_le
    simp only [thirdPoly, eval_add, eval_one]
    omega
  obtain ⟨t₄, ht₄, h₄⟩ := boundsProg_runs_cost c (inputLambda z) (inputIndex z)
  have hp₄ := boundsCost_le_majorant hc hlv hnv huv
  have hq₄ := (boundsMajorant_polyBounded c).le_poly_eval v
  obtain ⟨s₄, hts₄, hs₄⟩ := appendStage_runs_poly
    (parameterInput.comp (treeHead.comp (treeHead.comp treeHead))) (boundsProg_closed c)
    (thirdPoly c) (boundsPoly c) v (pauliResult c z) _ hz₃ t₄ (ht₄.trans (hp₄.trans hq₄)) h₄
  change (boundsStage c).Runs (pauliResult c z) (boundsResult c z) s₄ at hs₄
  have hz₄ : (boundsResult c z).size ≤ (fourthPoly c).eval v := by
    have := hs₄.size_le
    simp only [fourthPoly, eval_add, eval_one]
    omega
  obtain ⟨s₅, hts₅, hs₅⟩ := finish.computes (boundsResult c z)
  have hfin := polynomial_eval_mono finish.timeBound hz₄
  rw [finish_boundsResult] at hs₅
  refine ⟨_, ?_, sequence_runs
    (sequence_closed (appendStage_closed _ ClockSimulation.reindexProg_closed)
      (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
        (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed))) hs₁
      (sequence_runs (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
        (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed)) hs₂
        (sequence_runs (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed) hs₃
          (sequence_runs finish.closed hs₄ hs₅)))⟩
  simp only [preparationPoly, fourthPoly, thirdPoly, secondPoly,
    eval_add, eval_one, eval_comp] at hts₂ hts₃ hts₄ hfin ⊢
  change s₅ ≤ finish.timeBound.eval (boundsResult c z).size at hts₅
  omega

theorem resources_size_le {c v : ℕ} (hc : 1 ≤ c) (z : Data)
    (hl : 1 ≤ inputLambda z) (hn : 1 ≤ inputIndex z)
    (hz : z.size ≤ v) (hB : ansBound 5 (inputLambda z) (inputIndex z) ≤ v) :
    esize (resources c z) ≤ (preparationPoly c).eval v := by
  obtain ⟨t, ht, hr⟩ := prog_runs_poly hc z hl hn hz hB
  exact hr.size_le.trans ht

def kernelPoly (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : Polynomial ℕ :=
  preparationPoly c + kernel.timeBound.comp (preparationPoly c) + 1

def compiledPoly (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : Polynomial ℕ :=
  kernelPoly c kernel + X + 2

theorem kernelProg_runs_poly {c v : ℕ} (hc : 1 ≤ c)
    (kernel : PolyTimeFun KernelInput Bool) (M : Metadata) (x : Data)
    (hl : 1 ≤ M.2) (hn : 1 ≤ ClockSimulation.indexReader x)
    (hz : esize M + x.size + 1 ≤ v)
    (hB : ansBound 5 M.2 (ClockSimulation.indexReader x) ≤ v) :
    ∃ time ≤ (kernelPoly c kernel).eval v,
      (kernelProg c kernel).Runs (.cons (encode M) x)
        (encode (kernel (kernelInput c M x))) time := by
  have hmeta : inputLambda (.cons (encode M) x) = M.2 := by
    rcases M with ⟨⟨S,D⟩,lam⟩
    exact inputLambda_canonical S D lam x
  obtain ⟨s, hs, hr⟩ := prog_runs_poly hc (.cons (encode M) x)
    (by simpa only [hmeta] using hl) hn hz
      (by simpa only [hmeta, inputIndex_canonical] using hB)
  rw [← encode_kernelInput] at hr
  obtain ⟨t, ht, htRun⟩ := kernel.computes (kernelInput c M x)
  have hsize : esize (kernelInput c M x) ≤ (preparationPoly c).eval v := hr.size_le.trans hs
  have he := polynomial_eval_mono kernel.timeBound hsize
  refine ⟨_, ?_, sequence_runs kernel.closed hr htRun⟩
  simp only [kernelPoly, eval_add, eval_comp, eval_one]
  omega

/-- The actual binary compiler has only additive metadata-specialization
overhead beyond the prepared, fixed polynomial-time kernel. -/
theorem compiler_runs_poly {c v : ℕ} (hc : 1 ≤ c)
    (kernel : PolyTimeFun KernelInput Bool) (M : Metadata) (x : Data)
    (hl : 1 ≤ M.2) (hn : 1 ≤ ClockSimulation.indexReader x)
    (hz : esize M + x.size + 1 ≤ v)
    (hB : ansBound 5 M.2 (ClockSimulation.indexReader x) ≤ v) :
    ∃ time ≤ (compiledPoly c kernel).eval v,
      (compiler c kernel M).Runs x (encode (kernel (kernelInput c M x))) time := by
  obtain ⟨t, ht, hr⟩ := kernelProg_runs_poly hc kernel M x hl hn hz hB
  refine ⟨_, ?_, hardcode_time (kernelProg_closed c kernel) hr⟩
  change t + (encode M).size + x.size + 3 ≤ _
  simp only [compiledPoly, eval_add, eval_X, eval_ofNat]
  change (encode M).size + x.size + 1 ≤ v at hz
  omega

/-- Any larger fixed exponential input budget absorbs both preparation and
kernel work. The clock generated by the implementation remains exponent five. -/
theorem compiler_ansBound_time {c : ℕ} (hc : 1 ≤ c)
    (kernel : PolyTimeFun KernelInput Bool) (k : ℕ) (hk : 5 ≤ k) :
    ∃ C, ∀ (M : Metadata) (x : Data),
      1 ≤ M.2 → 1 ≤ ClockSimulation.indexReader x →
      esize M + x.size + 1 ≤ ansBound k M.2 (ClockSimulation.indexReader x) →
      ∃ time ≤ ansBound C M.2 (ClockSimulation.indexReader x),
        (compiler c kernel M).Runs x (encode (kernel (kernelInput c M x))) time := by
  obtain ⟨C, hC⟩ := polynomial_ansBound (compiledPoly c kernel) k
  refine ⟨C, fun M x hl hn hz => ?_⟩
  have hB : ansBound 5 M.2 (ClockSimulation.indexReader x) ≤
      ansBound k M.2 (ClockSimulation.indexReader x) := by
    unfold ansBound
    exact Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_right (by omega) hk)
  obtain ⟨t, ht, hr⟩ := compiler_runs_poly hc kernel M x hl hn hz hB
  exact ⟨t, ht.trans (hC _ _ hl hn), hr⟩

end MIPRE.Introspection.DecisionPreparation
