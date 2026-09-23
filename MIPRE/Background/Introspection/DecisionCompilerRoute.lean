/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionCompilerCutoff
import MIPRE.Background.Introspection.DecisionKernel
import MIPRE.Foundations.CL.DetypingDeciderRoute

/-! # Detyping the prepared decision kernel

The graph router consumes the original untyped input and the already prepared
dimension and answer cutoff. A genuine edge is checked by the typed kernel
using those same resources. No second clock or parameter preparation occurs.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost Cost.PolyTimeFun CL.Detyping.Program DecisionKernel

abbrev graph := TypeGraph.Adj (ℓ := 7) QLD.adj (.pauli .X) (.pauli .Z)

def cutoffField : PolyTimeFun Input ℕ := cutoff.comp (registerWidth.pair originalCutoff)

def routeContext : PolyTimeFun Input Data :=
  ap₂ treePair (ap₂ treePair raw (encoded.comp questionDimension))
    (encoded.comp (cutoffField.pair cutoffField))

theorem routeContext_apply (z : Input) : routeContext z =
    CL.Detyping.DeciderProgram.context (raw z) (questionDimension z)
      (answerBound (registerWidth z) (originalCutoff z))
      (answerBound (registerWidth z) (originalCutoff z)) := by
  simp only [routeContext, ap₂_apply, encoded_apply, comp_apply, pair_apply,
    treePair_apply, cutoffField, cutoff_apply]
  rfl

def router : PolyTimeFun Input (Bool × Data) :=
  (CL.Detyping.DeciderProgram.route graph).comp routeContext

def withRaw (z : Input) (x : Data) : Input := (x,z.2)

def routedInput : PolyTimeFun Input Input :=
  (treeHead.comp (snd.comp router)).pair snd

def untypedKernel (U : ClockedUniversalMachine) : PolyTimeFun Input Bool :=
  ite (fst.comp router) ((DecisionKernel.program U).comp routedInput)
    (ap₂ treeEq (snd.comp router) (const (encode true)))

theorem untypedKernel_apply (U : ClockedUniversalMachine) (z : Input) :
    untypedKernel U z =
      if (router z).1 then
        DecisionKernel.program U (withRaw z (treeHead (router z).2))
      else decide ((router z).2 = encode true) := by
  simp only [untypedKernel, PolyTimeFun.ite_apply, comp_apply, fst_apply,
    routedInput, pair_apply, snd_apply, ap₂_apply, const_apply, treeEq_apply, withRaw]
  rfl

theorem router_context (n : ℕ) (x y a b : BitStr)
    (M : DecisionPreparation.Metadata) (clock : Unary) (N Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) :
    router (encode (n,x,y,a,b),M,clock,N,p,Q,R) =
      if x.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
          y.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
          a.length ≤ answerBound Q R ∧ b.length ≤ answerBound Q R then
        match CL.Detyping.DeciderProgram.selectedEdge graph
            (CL.Detyping.graphOfBits x) (CL.Detyping.graphOfBits y) with
        | none => (false,encode true)
        | some uv => (true,.cons (encode (n,uv.1,x.drop (CL.Detyping.graphDim Label),
            uv.2,y.drop (CL.Detyping.graphDim Label),a,b)) .nil)
      else (false,encode false) := by
  rw [router, comp_apply, routeContext_apply, questionDimension_apply]
  change CL.Detyping.DeciderProgram.route graph
    (CL.Detyping.DeciderProgram.context (encode (n,x,y,a,b))
      ((3*p.2.2.length+3)*p.1.length) (answerBound Q R) (answerBound Q R)) = _
  rw [CL.Detyping.DeciderProgram.route_context]
  by_cases h : x.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
      y.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
      a.length ≤ answerBound Q R ∧ b.length ≤ answerBound Q R
  · simp only [if_pos h]
    cases CL.Detyping.DeciderProgram.selectedEdge graph
      (CL.Detyping.graphOfBits x) (CL.Detyping.graphOfBits y) <;>
      simp only [if_pos h.2.2] <;> rfl
  · simp only [if_neg h]

/-- Canonical untyped inputs use exactly the graph router's edge convention,
with the global answer cutoff enforced also on nonedge views. -/
theorem untypedKernel_iff (U : ClockedUniversalMachine) (n : ℕ) (x y a b : BitStr)
    (M : DecisionPreparation.Metadata) (clock : Unary) (N Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) :
    untypedKernel U (encode (n,x,y,a,b),M,clock,N,p,Q,R) = true ↔
      x.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
      y.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
      a.length ≤ answerBound Q R ∧ b.length ≤ answerBound Q R ∧
      (match CL.Detyping.DeciderProgram.selectedEdge graph
          (CL.Detyping.graphOfBits x) (CL.Detyping.graphOfBits y) with
      | none => True
      | some uv => DecisionKernel.program U
          (encode (n,uv.1,x.drop (CL.Detyping.graphDim Label),uv.2,
            y.drop (CL.Detyping.graphDim Label),a,b),M,clock,N,p,Q,R) = true) := by
  rw [untypedKernel_apply, router_context]
  by_cases h : x.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
      y.length = CL.Detyping.graphDim Label + (3*p.2.2.length+3)*p.1.length ∧
      a.length ≤ answerBound Q R ∧ b.length ≤ answerBound Q R
  · rcases h with ⟨hx,hy,ha,hb⟩
    cases hedge : CL.Detyping.DeciderProgram.selectedEdge graph
      (CL.Detyping.graphOfBits x) (CL.Detyping.graphOfBits y) <;>
      simp [hx,hy,ha,hb,withRaw,hedge]
  · simp only [if_neg h, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    have hf : encode false ≠ encode true := fun he => Bool.noConfusion (encode_injective he)
    simp only [hf, false_iff, not_and]
    intro hx hy ha hb
    exact False.elim (h ⟨hx,hy,ha,hb⟩)

end MIPRE.Introspection.DecisionCompiler
