/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram
import MIPRE.Foundations.Introspection.SourceCompilerCost

/-! # A total clocked full-register sampling check

The program reads `(level, role, n, Q, R, s, left, right)` with binary
parameters. Both answers contain Q-bit registers; only the Introspect
register must vanish past s. The Sample seed is freely supported on the
full register. The actual source marginal query receives its first s bits
at index 2^n. A timeout or malformed source result rejects.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryProgram
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight
  leftParts rightParts readInput)

abbrev SamplingInput := ℕ × Bool × GuardInput

def samplingLevel : PolyTimeFun SamplingInput ℕ := fst
def samplingRole : PolyTimeFun SamplingInput Bool := fst.comp snd
def samplingFields : PolyTimeFun SamplingInput GuardInput := snd.comp snd

def readRole : PolyTimeFun Data Bool := equal (PolyTimeFun.id Data) (const (encode true))

@[simp] theorem readRole_encode (w : Bool) : readRole (encode w) = w := by
  cases w <;> simp [readRole,equal]

def readSamplingInput : PolyTimeFun Data SamplingInput :=
  (readNat.comp treeHead).pair (((readRole.comp treeHead).comp treeTail).pair
    (readInput.comp (treeTail.comp treeTail)))

@[simp] theorem readSamplingInput_encode (x : SamplingInput) :
    readSamplingInput (encode x) = x := by
  rcases x with ⟨j,w,x⟩
  simp [readSamplingInput,encode_prod,readNat_encode]
  exact readRole_encode w

def SamplingReady (x : SamplingInput) : Prop :=
  1 ≤ x.1 ∧ inputDim x.2.2 ≤ inputQ x.2.2 ∧
  outerCheck x.2.2 = true ∧ pairLeft x.2.2 = true ∧ pairRight x.2.2 = true ∧
  SourceCompiler.InSource (inputDim x.2.2) (leftParts x.2.2).1 ∧
  (leftParts x.2.2).2 = (rightParts x.2.2).2

instance (x : SamplingInput) : Decidable (SamplingReady x) := inferInstanceAs (Decidable (_ ∧ _))

def samplingReady : PolyTimeFun SamplingInput Bool :=
  andCheck (ap₂ leNat (const 1) samplingLevel) <|
  (andCheck (ap₂ leNat inputDim inputQ) <|
    andCheck outerCheck <| andCheck pairLeft <| andCheck pairRight <|
      andCheck (SourceCompiler.sourceCheck.comp ((fst.comp leftParts).pair inputDim))
        (equal (snd.comp leftParts) (snd.comp rightParts))).comp samplingFields

theorem samplingReady_iff (x : SamplingInput) : samplingReady x = true ↔ SamplingReady x := by
  simp only [samplingReady,andCheck_iff,ap₂_apply,const_apply,leNat_apply,decide_eq_true_eq,
    comp_apply,samplingLevel,samplingFields,fst_apply,snd_apply,SourceCompiler.sourceCheck_iff,
    pair_apply,equal_iff,SamplingReady]

def SamplingRawReady (x : Data) : Prop :=
  x = encode (readSamplingInput x) ∧ SamplingReady (readSamplingInput x)

instance (x : Data) : Decidable (SamplingRawReady x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The marginal query contains the original seed length, not the padded length. -/
def samplingCall : PolyTimeFun SamplingInput Data :=
  let fields := samplingFields
  let z := DynamicParser.takeBits.comp (((fst.comp rightParts).comp fields).pair (inputDim.comp fields))
  encoded.comp ((inputIndex.comp fields).pair
    ((const (1 : ℕ)).pair (samplingRole.pair (samplingLevel.pair (z.pair (const ([] : BitStr)))))))

theorem samplingCall_apply (x : SamplingInput) : samplingCall x =
    encode (inputIndex x.2.2, CL.Sampler.Query.marginal (Player.ofBool x.2.1) x.1
      ((rightParts x.2.2).1.take (inputDim x.2.2))) := by
  cases hw : x.2.1 <;>
    simp [samplingCall,samplingFields,samplingRole,samplingLevel,DynamicParser.takeBits_apply,
      Player.ofBool,hw,encode_prod]
  <;> rfl

def samplingRoute : PolyTimeFun Data (Bool × Data) :=
  let call := (const true).pair (ap₂ treePair (samplingCall.comp readSamplingInput) (PolyTimeFun.id Data))
  ite (andCheck (equal (PolyTimeFun.id Data) (encoded.comp readSamplingInput))
      (samplingReady.comp readSamplingInput)) call (const (false,encode false))

theorem samplingRoute_apply (x : Data) : samplingRoute x = if SamplingRawReady x then
    (true,.cons (samplingCall (readSamplingInput x)) x) else (false,encode false) := by
  simp only [samplingRoute,PolyTimeFun.ite_apply,andCheck_iff,equal_iff,id_apply,comp_apply,
    encoded_apply,samplingReady_iff,SamplingRawReady,pair_apply,const_apply,ap₂_apply,treePair_apply]
  congr 1

def samplingExpected : PolyTimeFun SamplingInput Data :=
  ap₂ treePair (const (encode true)) (encoded.comp (DynamicParser.takeBits.comp
    (((fst.comp leftParts).comp samplingFields).pair (inputDim.comp samplingFields))))

theorem samplingExpected_apply (x : SamplingInput) : samplingExpected x =
    .cons (encode true) (encode ((leftParts x.2.2).1.take (inputDim x.2.2))) := by
  simp [samplingExpected,samplingFields,DynamicParser.takeBits_apply]

def samplingPost : PolyTimeFun (Data × Data) Data :=
  encoded.comp (equal snd (samplingExpected.comp (readSamplingInput.comp fst)))

theorem samplingPost_apply (x r : Data) : samplingPost (x,r) =
    encode (decide (r = samplingExpected (readSamplingInput x))) := by
  simp [samplingPost,equal]

def samplingProg (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) : Prog :=
  routeOneCall samplingRoute (ClockSimulation.prog k lam U S) samplingPost

theorem samplingProg_closed (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) :
    (samplingProg k lam U S).WellScoped 1 :=
  routeOneCall_closed _ (ClockSimulation.prog_closed k lam U S) _

def samplingResult (k lam : ℕ) (S : Prog) (x : SamplingInput) : Data :=
  clockedResult S (ClockSimulation.reindexed (samplingCall x))
    (ansBound k lam (ClockSimulation.indexReader (samplingCall x)))

set_option backward.isDefEq.respectTransparency false in
theorem samplingProg_run (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) :
    ∃ t, (samplingProg k lam U S).Runs x
      (if SamplingRawReady x then encode (decide
        (samplingResult k lam S (readSamplingInput x) = samplingExpected (readSamplingInput x)))
       else encode false) t := by
  by_cases h : SamplingRawReady x
  · obtain ⟨t,hr⟩ := ClockSimulation.prog_runs k lam U S (samplingCall (readSamplingInput x))
    obtain ⟨time,ht⟩ := routeOneCall_indirect samplingRoute (ClockSimulation.prog_closed k lam U S)
      samplingPost x _ x _ t (by rw [samplingRoute_apply,if_pos h]) hr
    refine ⟨time,?_⟩
    simpa only [samplingProg,if_pos h,samplingPost_apply,samplingResult] using ht
  · obtain ⟨t,ht⟩ := routeOneCall_direct samplingRoute (ClockSimulation.prog k lam U S)
      samplingPost x (encode false) (by rw [samplingRoute_apply,if_neg h])
    exact ⟨t,by simpa only [samplingProg,if_neg h] using ht⟩

/-- Totality does not require the source program to terminate. -/
theorem samplingProg_halts (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) :
    Halts (samplingProg k lam U S) x := by
  obtain ⟨t,hr⟩ := samplingProg_run k lam U S x
  exact ⟨_,t,hr⟩

theorem samplingProg_accepts_iff (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) :
    (∃ t, (samplingProg k lam U S).Runs x (encode true) t) ↔
      SamplingRawReady x ∧ samplingResult k lam S (readSamplingInput x) =
        samplingExpected (readSamplingInput x) := by
  obtain ⟨t,ht⟩ := samplingProg_run k lam U S x
  by_cases h : SamplingRawReady x
  · rw [if_pos h] at ht
    constructor
    · rintro ⟨ta,ha⟩
      exact ⟨h,of_decide_eq_true (encode_injective (ht.deterministic ha).1)⟩
    · rintro ⟨_,hr⟩
      exact ⟨t,by simpa only [hr,decide_true] using ht⟩
  · rw [if_neg h] at ht
    constructor
    · rintro ⟨ta,ha⟩
      cases encode_injective (ht.deterministic ha).1
    · rintro ⟨hr,_⟩
      exact (h hr).elim

def samplingCost (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) : ℕ :=
  SourceCompiler.callCost samplingRoute samplingPost x (samplingCall (readSamplingInput x)) x
    (SourceCompiler.rawSimulationCost k lam U S (samplingCall (readSamplingInput x))) + 5

/-- Explicit compositional runtime on arbitrary raw inputs and arbitrary source code. -/
theorem samplingProg_haltsWithin (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) :
    HaltsWithin (samplingProg k lam U S) x (samplingCost k lam U S x) := by
  by_cases h : SamplingRawReady x
  · obtain ⟨t,hb,hr⟩ := SourceCompiler.rawSimulation_runs_cost k lam U S
      (samplingCall (readSamplingInput x))
    obtain ⟨time,ht,hout⟩ := SourceCompiler.call_runs_cost samplingRoute samplingPost
      (ClockSimulation.prog_closed k lam U S) x _ x _ _ t hb
      (by rw [samplingRoute_apply,if_pos h]) hr
    exact ⟨_,time,ht.trans (Nat.le_add_right _ _),hout⟩
  · obtain ⟨time,ht,hout⟩ := routeOneCall_direct_cost samplingRoute (ClockSimulation.prog k lam U S)
      samplingPost x (encode false) (by rw [samplingRoute_apply,if_neg h])
    refine ⟨_,time,ht.trans ?_,hout⟩
    change _ + 1 + 4 ≤ _
    dsimp only [samplingCost,SourceCompiler.callCost]
    omega

end MIPRE.Introspection.AuxiliaryProgram
end
