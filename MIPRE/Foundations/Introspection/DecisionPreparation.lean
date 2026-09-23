/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliSamplerParamsCost
import MIPRE.Foundations.Introspection.SourceCompilerCost

/-! # Preparing shared resources for the introspection decision kernel

The uniform program receives `cons (encode ((S,D),λ)) raw`. It generates the
single unary clock, exponential source index, canonical unary Pauli parameters
and binary register bounds. The raw decision input and source metadata are
retained verbatim. A fixed polynomial-time kernel then consumes these resources.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionPreparation
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler

abbrev Metadata := (Prog × Prog) × ℕ
abbrev Resources := Data × Data × Unary × ℕ × PauliSamplerParameters.Parameters × ℕ × ℕ
abbrev KernelInput := Data × Metadata × Unary × ℕ × PauliSamplerParameters.Parameters × ℕ × ℕ

def inputMetadata : PolyTimeFun Data Data := treeHead
def inputRaw : PolyTimeFun Data Data := treeTail
def inputLambda : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp inputMetadata)
def inputIndex : PolyTimeFun Data ℕ := ClockSimulation.indexReader.comp inputRaw
def parameterInput : PolyTimeFun Data Data := encoded.comp (inputLambda.pair inputIndex)

/-- The output format, before any kernel-specific conversion. -/
def resources (c : ℕ) (z : Data) : Resources :=
  (inputRaw z, inputMetadata z, unary (ansBound 5 (inputLambda z) (inputIndex z)),
    2 ^ inputIndex z, PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z),
    registerBits c (inputLambda z) (inputIndex z), originalBound (inputLambda z) (inputIndex z))

/-- The same prepared layout with canonically supplied source programs typed. -/
def kernelInput (c : ℕ) (M : Metadata) (x : Data) : KernelInput :=
  let n := ClockSimulation.indexReader x
  (x, M, unary (ansBound 5 M.2 n), 2 ^ n, PauliSamplerParameters.parameters c M.2 n,
    registerBits c M.2 n, originalBound M.2 n)

/-- Getters are total even on malformed output trees. Program metadata is
retained as data; its canonical sampler/decider projections are named below. -/
def raw : PolyTimeFun Data Data := treeHead
def rest : PolyTimeFun Data Data := treeTail
def metadata : PolyTimeFun Data Data := treeHead.comp rest
def resourceTail : PolyTimeFun Data Data := treeTail.comp rest
def budget : PolyTimeFun Data Unary := readUnary.comp (treeHead.comp resourceTail)
def sourceIndex : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp (treeTail.comp resourceTail))
def parameterTail : PolyTimeFun Data Data := treeTail.comp (treeTail.comp resourceTail)
def parameters : PolyTimeFun Data PauliSamplerParameters.Parameters :=
  (readUnary.comp (treeHead.comp (treeHead.comp parameterTail))).pair
    ((readUnary.comp (treeHead.comp (treeTail.comp (treeHead.comp parameterTail)))).pair
      (readUnary.comp (treeTail.comp (treeTail.comp (treeHead.comp parameterTail)))))
def registerWidth : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp (treeTail.comp parameterTail))
def originalCutoff : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp (treeTail.comp parameterTail))
def samplerData : PolyTimeFun Data Data := treeHead.comp (treeHead.comp metadata)
def deciderData : PolyTimeFun Data Data := treeTail.comp (treeHead.comp metadata)
def lambda : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp metadata)

def decodeResources : PolyTimeFun Data Resources :=
  raw.pair (metadata.pair (budget.pair (sourceIndex.pair
    (parameters.pair (registerWidth.pair originalCutoff)))))

theorem decodeResources_encode (c : ℕ) (z : Data) :
    decodeResources (encode (resources c z)) = resources c z := by
  simp [decodeResources, raw, metadata, rest, resourceTail, budget, sourceIndex,
    parameterTail, parameters, registerWidth, originalCutoff, resources,
    PauliSamplerParameters.parameters, encode_prod, encode_unary, readUnary_ofNat,
    readNat_encode]

@[simp] theorem inputLambda_canonical (S D : Prog) (lam : ℕ) (x : Data) :
    inputLambda (.cons (encode ((S,D),lam)) x) = lam := by
  simp [inputLambda, inputMetadata, encode_prod, readNat_encode]

@[simp] theorem inputIndex_canonical (M : Data) (x : Data) :
    inputIndex (.cons M x) = ClockSimulation.indexReader x := rfl

theorem encode_kernelInput (c : ℕ) (M : Metadata) (x : Data) :
    encode (kernelInput c M x) = encode (resources c (.cons (encode M) x)) := by
  rcases M with ⟨⟨S,D⟩,lam⟩
  simp [kernelInput, resources, inputRaw, inputMetadata, inputLambda, encode_prod, readNat_encode]

theorem source_metadata (c : ℕ) (S D : Prog) (lam : ℕ) (x : Data) :
    samplerData (encode (resources c (.cons (encode ((S,D),lam)) x))) = encode S ∧
    deciderData (encode (resources c (.cons (encode ((S,D),lam)) x))) = encode D ∧
    lambda (encode (resources c (.cons (encode ((S,D),lam)) x))) = lam := by
  simp [samplerData, deciderData, lambda, metadata, rest, resources, inputMetadata,
    encode_prod, readNat_encode]

/-- Append a subroutine result while retaining its entire input as context. -/
def appendRoute (arg : PolyTimeFun Data Data) : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair arg (PolyTimeFun.id Data))

def appendStage (arg : PolyTimeFun Data Data) (p : Prog) : Prog :=
  routeOneCall (appendRoute arg) p treePair

theorem appendStage_closed (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1) :
    (appendStage arg p).WellScoped 1 := routeOneCall_closed _ hp _

theorem appendStage_runs (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1)
    (x r : Data) (t : ℕ) (hr : p.Runs (arg x) r t) :
    ∃ time, (appendStage arg p).Runs x (.cons x r) time :=
  routeOneCall_indirect (appendRoute arg) hp treePair x (arg x) x r t rfl hr

def clockStage : Prog := appendStage parameterInput (ClockArithmetic.uniformProg 5)
def indexStage : Prog := appendStage (inputRaw.comp treeHead) ClockSimulation.reindexProg
def pauliStage (c : ℕ) : Prog :=
  appendStage (parameterInput.comp (treeHead.comp treeHead)) (PauliSamplerParameters.prog c)
def boundsStage (c : ℕ) : Prog :=
  appendStage (parameterInput.comp (treeHead.comp (treeHead.comp treeHead))) (boundsProg c)

def origin : PolyTimeFun Data Data := treeHead.comp (treeHead.comp (treeHead.comp treeHead))
def preparedClock : PolyTimeFun Data Data := treeTail.comp (treeHead.comp (treeHead.comp treeHead))
def preparedIndex : PolyTimeFun Data Data := treeHead.comp (treeTail.comp (treeHead.comp treeHead))
def preparedParameters : PolyTimeFun Data Data := treeTail.comp treeHead

def finish : PolyTimeFun Data Data :=
  ap₂ treePair (inputRaw.comp origin) (ap₂ treePair (inputMetadata.comp origin)
    (ap₂ treePair preparedClock (ap₂ treePair preparedIndex
      (ap₂ treePair preparedParameters treeTail))))

/-- Sequence closed programs, retaining the ambient input discipline. -/
def sequence (p q : Prog) : Prog := .let_ p q

theorem sequence_closed {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
    (sequence p q).WellScoped 1 := ⟨hp, hq.mono (by omega) _⟩

theorem sequence_runs {p q : Prog} (hq : q.WellScoped 1) {x y z : Data} {s t : ℕ}
    (hp : p.Runs x y s) (hr : q.Runs y z t) : (sequence p q).Runs x z (s+t+1) :=
  Eval.let_ hp (Eval.append_of_wellScoped hr hq _)

/-- The budget appears once in the program; all later stages only retain it. -/
def prog (c : ℕ) : Prog := sequence clockStage (sequence indexStage
  (sequence (pauliStage c) (sequence (boundsStage c) finish.code)))

theorem prog_closed (c : ℕ) : (prog c).WellScoped 1 :=
  sequence_closed (appendStage_closed _ (ClockArithmetic.uniformProg_closed 5))
    (sequence_closed (appendStage_closed _ ClockSimulation.reindexProg_closed)
      (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
        (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed)))

def clockResult (z : Data) : Data := .cons z (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))
def indexResult (z : Data) : Data := .cons (clockResult z) (ClockSimulation.reindexed (inputRaw z))
def pauliResult (c : ℕ) (z : Data) : Data :=
  .cons (indexResult z) (encode (PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z)))
def boundsResult (c : ℕ) (z : Data) : Data :=
  .cons (pauliResult c z) (encode (registerBits c (inputLambda z) (inputIndex z),
    originalBound (inputLambda z) (inputIndex z)))

set_option backward.isDefEq.respectTransparency false in
/-- Exact resource preparation is total for every input tree, including zero
parameters and malformed raw decision inputs. -/
theorem prog_runs (c : ℕ) (z : Data) :
    ∃ time, (prog c).Runs z (encode (resources c z)) time := by
  obtain ⟨t₁, _, h₁⟩ := ClockArithmetic.uniformProg_runs 5 (inputLambda z) (inputIndex z)
  obtain ⟨s₁, hs₁⟩ := appendStage_runs parameterInput (ClockArithmetic.uniformProg_closed 5)
    z _ t₁ h₁
  obtain ⟨t₂, h₂⟩ := ClockSimulation.reindexProg_runs (inputRaw z)
  obtain ⟨s₂, hs₂⟩ := appendStage_runs (inputRaw.comp treeHead) ClockSimulation.reindexProg_closed
    (.cons z (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))) _ t₂ h₂
  obtain ⟨t₃, h₃⟩ := PauliSamplerParameters.prog_runs c (inputLambda z) (inputIndex z)
  obtain ⟨s₃, hs₃⟩ := appendStage_runs (parameterInput.comp (treeHead.comp treeHead))
    (PauliSamplerParameters.prog_closed c) (indexResult z) _ t₃ h₃
  obtain ⟨t₄, h₄⟩ := boundsProg_runs c (inputLambda z) (inputIndex z)
  obtain ⟨s₄, hs₄⟩ := appendStage_runs (parameterInput.comp (treeHead.comp (treeHead.comp treeHead)))
    (boundsProg_closed c) (pauliResult c z) _ t₄ h₄
  obtain ⟨s₅, _, hs₅⟩ := finish.computes (.cons (.cons (.cons (.cons z
    (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))) (ClockSimulation.reindexed (inputRaw z)))
      (encode (PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z))))
        (encode (registerBits c (inputLambda z) (inputIndex z),
          originalBound (inputLambda z) (inputIndex z))))
  have hout : finish (.cons (.cons (.cons (.cons z
    (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))) (ClockSimulation.reindexed (inputRaw z)))
      (encode (PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z))))
        (encode (registerBits c (inputLambda z) (inputIndex z),
          originalBound (inputLambda z) (inputIndex z)))) = encode (resources c z) := by
    simp [finish, origin, preparedClock, preparedIndex, preparedParameters,
      ClockSimulation.reindexed, inputIndex, resources, encode_prod, encode_unary]
  rw [hout] at hs₅
  exact ⟨_, sequence_runs (sequence_closed (appendStage_closed _ ClockSimulation.reindexProg_closed)
    (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
      (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed))) hs₁
      (sequence_runs (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
        (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed)) hs₂
        (sequence_runs (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed) hs₃
          (sequence_runs finish.closed hs₄ hs₅)))⟩

def kernelProg (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : Prog :=
  sequence (prog c) kernel.code

theorem kernelProg_closed (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) :
    (kernelProg c kernel).WellScoped 1 := sequence_closed (prog_closed c) kernel.closed

theorem kernelProg_runs (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) (M : Metadata) (x : Data) :
    ∃ time, (kernelProg c kernel).Runs (.cons (encode M) x)
      (encode (kernel (kernelInput c M x))) time := by
  obtain ⟨s, hs⟩ := prog_runs c (.cons (encode M) x)
  rw [← encode_kernelInput] at hs
  obtain ⟨t, _, ht⟩ := kernel.computes (kernelInput c M x)
  exact ⟨_, sequence_runs kernel.closed hs ht⟩

/-- The compiler specializes only the binary source metadata. -/
def compiler (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : PolyTimeFun Metadata Prog :=
  (smn Metadata).comp ((const (kernelProg c kernel)).pair (PolyTimeFun.id Metadata))

@[simp] theorem compiler_apply (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) (M : Metadata) :
    compiler c kernel M = hardcode (kernelProg c kernel) (encode M) := rfl

theorem compiler_closed (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) (M : Metadata) :
    (compiler c kernel M).WellScoped 1 := hardcode_wellScoped (kernelProg_closed c kernel) _

theorem compiler_runs (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) (M : Metadata) (x : Data) :
    ∃ time, (compiler c kernel M).Runs x
      (encode (kernel (kernelInput c M x))) time := by
  obtain ⟨t, ht⟩ := kernelProg_runs c kernel M x
  exact ⟨_, hardcode_time (kernelProg_closed c kernel) ht⟩

end MIPRE.Introspection.DecisionPreparation
