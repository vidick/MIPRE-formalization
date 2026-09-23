/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionKernelInput
import MIPRE.Foundations.Introspection.GuardedAuxiliaryProgram

/-! # The actual introspection decision kernel

The preparer supplies one shared clock, the source programs, the exponential
index, and the canonical Pauli parameters. This kernel parses the raw typed
input, runs the actual Pauli predicate and endpoint parsers, and composes them
with both orientations of the guarded auxiliary predicate.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)

/-- The ambient question dimension is polynomial in the explicit unary parameters. -/
def questionDimension : PolyTimeFun Input ℕ :=
  ap₂ addUnary (const 0) ((LowDegree.DegreeArithmetic.mulUnaryProg).comp
    ((QLD.PauliBinaryProgram.coordinateCount.comp parameters).pair (fst.comp parameters)))

theorem questionDimension_apply (z : Input) :
    questionDimension z = (3 * (parameters z).2.2.length + 3) * (parameters z).1.length := by
  have he := QLD.PauliBinaryProgram.coordinateCount_apply
    (parameters z).1 (parameters z).2.1 (parameters z).2.2
  simp only [questionDimension, ap₂_apply, comp_apply, pair_apply, fst_apply, const_apply,
    LowDegree.DegreeArithmetic.mulUnaryProg_apply, addUnary_apply, length_unary, Nat.zero_add]
  rw [he, length_unary]

def questionLengths : PolyTimeFun Input Bool :=
  andCheck (equal (lengthNat.comp leftQuestion) questionDimension)
    (equal (lengthNat.comp rightQuestion) questionDimension)

/-- Allocate only as many dummy prefix bits as the input already supplies.
Every formatted auxiliary endpoint supplies at least one full register. -/
def zeroPrefix : PolyTimeFun Input BitStr :=
  (map (const false)).comp
    (DynamicParser.takeBits.comp ((ap₂ append leftBits rightBits).pair registerWidth))

theorem zeroPrefix_apply (z : Input) :
    zeroPrefix z = List.replicate (min (registerWidth z) ((leftBits z).length + (rightBits z).length))
      false := by
  simp only [zeroPrefix, comp_apply, map_apply, pair_apply, ap₂_apply, append_apply,
    DynamicParser.takeBits_apply]
  change (((leftBits z) ++ (rightBits z)).take (registerWidth z)).map
    (fun _ : Bool => false) = _
  have he (l : List Bool) : l.map (fun _ => false) = List.replicate l.length false := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simpa only [List.map_cons, List.length_cons, List.replicate_succ] using
        (congrArg (List.cons false) ih)
  rw [he, List.length_take, List.length_append]

theorem zeroPrefix_of_length (z : Input)
    (h : registerWidth z ≤ (leftBits z).length + (rightBits z).length) :
    zeroPrefix z = List.replicate (registerWidth z) false := by
  rw [zeroPrefix_apply, Nat.min_eq_left h]

def sourceContext : PolyTimeFun Input AuxiliarySource.Context :=
  budget.pair (sourceSampler.pair (sourceIndex.pair
    ((const false).pair ((const 1).pair zeroPrefix))))

def sourceDimension (U : ClockedUniversalMachine) : PolyTimeFun Input ℕ :=
  (SourcePadding.Program.dimension U).comp sourceContext

def auxiliaryInput (U : ClockedUniversalMachine) :
    PolyTimeFun Input (AuxiliaryDecision.Input QLD.Ty 7) :=
  (sourceContext.pair
    ((registerWidth.pair (originalCutoff.pair ((sourceDimension U).pair sourceDecider))).pair
      parameters)).pair ((leftType.pair leftBits).pair (rightType.pair rightBits))

/-- Full Pauli answer bytes are converted to the same self-dual register
coordinates used by the source checks. -/
def project : PolyTimeFun (AuxiliaryDecision.Input QLD.Ty 7) BitStr :=
  (snd.comp QLD.PauliBinaryProgram.fullAnswer).comp
    (AuxiliaryDecision.pauliParameters.pair AuxiliaryDecision.leftBits)

def auxiliary (U : ClockedUniversalMachine) : PolyTimeFun Input Bool :=
  (AuxiliaryDecision.guarded U (.pauli .X) (.pauli .Z) project).comp (auxiliaryInput U)

def isPauli : Label → Bool
  | .inl _ => true
  | .inr _ => false

def pauliLabel : Label → QLD.Ty
  | .inl t => t
  | .inr _ => .pauli .X

def leftIsPauli : PolyTimeFun Input Bool := (finiteFunction isPauli).comp leftType
def rightIsPauli : PolyTimeFun Input Bool := (finiteFunction isPauli).comp rightType
def leftPauliPayload : PolyTimeFun Input QLD.PauliBinaryProgram.Payload :=
  ((finiteFunction pauliLabel).comp leftType).pair (leftQuestion.pair leftBits)
def rightPauliPayload : PolyTimeFun Input QLD.PauliBinaryProgram.Payload :=
  ((finiteFunction pauliLabel).comp rightType).pair (rightQuestion.pair rightBits)

def leftPauliFormat : PolyTimeFun Input Bool :=
  ite leftIsPauli (QLD.PauliBinaryProgram.endpointValid.comp (parameters.pair leftPauliPayload))
    (const true)
def rightPauliFormat : PolyTimeFun Input Bool :=
  ite rightIsPauli (QLD.PauliBinaryProgram.endpointValid.comp (parameters.pair rightPauliPayload))
    (const true)

def pauli : PolyTimeFun Input Bool :=
  ite (andCheck leftIsPauli rightIsPauli)
    (QLD.PauliBinaryProgram.program.comp
      (parameters.pair (leftPauliPayload.pair rightPauliPayload))) (const true)

/-- One polynomial-time kernel handles every raw input. -/
def program (U : ClockedUniversalMachine) : PolyTimeFun Input Bool :=
  andCheck canonical (andCheck questionLengths
    (andCheck leftPauliFormat (andCheck rightPauliFormat (andCheck pauli (auxiliary U)))))

theorem program_iff (U : ClockedUniversalMachine) (z : Input) :
    program U z = true ↔ canonical z = true ∧ questionLengths z = true ∧
      leftPauliFormat z = true ∧ rightPauliFormat z = true ∧
      pauli z = true ∧ auxiliary U z = true := by
  simp only [program, andCheck_iff]

theorem auxiliaryInput_apply (U : ClockedUniversalMachine) (z : Input) :
    auxiliaryInput U z =
      ((sourceContext z,
        ((registerWidth z, originalCutoff z, sourceDimension U z, sourceDecider z), parameters z)),
        (leftType z, leftBits z), (rightType z, rightBits z)) := rfl

theorem sourceContext_apply (z : Input) :
    sourceContext z = (budget z, sourceSampler z, sourceIndex z, false, 1, zeroPrefix z) := rfl

theorem project_apply (z : AuxiliaryDecision.Input QLD.Ty 7) :
    project z = (QLD.PauliBinaryProgram.fullAnswer
      (AuxiliaryDecision.pauliParameters z, AuxiliaryDecision.leftBits z)).2 := rfl

set_option maxRecDepth 4096 in
theorem pauli_apply (z : Input) :
    pauli z = if andCheck leftIsPauli rightIsPauli z then
      QLD.PauliBinaryProgram.program
        (parameters z, leftPauliPayload z, rightPauliPayload z) else true := rfl

theorem program_runs (U : ClockedUniversalMachine) (z : Input) :
    ∃ t ≤ (program U).timeBound.eval (esize z),
      (program U).code.Runs (encode z) (encode (program U z)) t := (program U).computes z

end MIPRE.Introspection.DecisionKernel
end
