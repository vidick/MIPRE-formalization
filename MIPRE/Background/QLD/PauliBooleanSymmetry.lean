/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliBooleanPrograms

/-! # Orientation symmetry of the actual Pauli decision program -/

noncomputable section
namespace MIPRE.QLD.PauliBooleanProgram
open Cost Cost.PolyTimeFun

def swapInput (input : Input) : Input := (input.1, input.2.2, input.2.1)

theorem route_kind_symm (T U : Ty) :
    (PauliBranchProgram.route U T).1 = (PauliBranchProgram.route T U).1 := by
  revert T U
  decide

theorem route_metadata_symm (T U : Ty) :
    (PauliBranchProgram.route U T).2.2 = (PauliBranchProgram.route T U).2.2 := by
  revert T U
  decide

theorem route_flip (T U : Ty) (h0 : 0 < (PauliBranchProgram.route T U).1)
    (h8 : (PauliBranchProgram.route T U).1 < 8) :
    (PauliBranchProgram.route U T).2.1 = !(PauliBranchProgram.route T U).2.1 := by
  revert T U
  decide

theorem route_default_orientation (T U : Ty) (h : (PauliBranchProgram.route T U).1 = 8) :
    (PauliBranchProgram.route T U).2.1 = false := by
  revert T U
  decide

theorem route_kind_swap (input : Input) : (route (swapInput input)).1 = (route input).1 :=
  route_kind_symm _ _

theorem basis_swap (input : Input) : basis (swapInput input) = basis input :=
  congrArg Prod.fst (route_metadata_symm _ _)

theorem oriented_swap (input : Input) (h0 : 0 < (route input).1) (h8 : (route input).1 < 8) :
    oriented (swapInput input) = oriented input := by
  rcases input with ⟨p, ⟨T, x, a⟩, ⟨U, y, b⟩⟩
  have hf := route_flip T U h0 h8
  simp only [oriented, comp_apply, pair_apply, fst_apply, snd_apply,
    route, endpointTypes, endpoints, swapInput, PauliBranchProgram.routeProg_apply,
    PauliBranchProgram.orientProg_apply, hf]
  cases (PauliBranchProgram.route T U).2.1 <;> rfl

theorem checks_swap (input : Input) (h0 : 0 < (route input).1) (h8 : (route input).1 < 8) :
    checks (swapInput input) = checks input := by
  have ho := oriented_swap input h0 h8
  have hb := basis_swap input
  have hp : params (swapInput input) = params input := rfl
  simp only [checks, cons_apply, const_apply, consistency, axisCheck, diagonalCheck,
    tableCheck, pairCheck, probeCheck, magicCheck, magicProbeCheck,
    ap₂_apply, comp_apply, pair_apply, leftParser, rightParser, leftRows, rightRows,
    leftBits, rightBits, leftFields, rightFields, leftValue, leftBit, rightBit,
    gamma, probe, point, origin, scalar, axis, width, dim, magicMetadata, magicTypes,
    leftParity, left, right, fst_apply, snd_apply, ho, hb, hp]

theorem parsers_swap (input : Input) (h0 : 0 < (route input).1) (h8 : (route input).1 < 8) :
    leftParser (swapInput input) = leftParser input ∧
      rightParser (swapInput input) = rightParser input := by
  have ho := oriented_swap input h0 h8
  have hp : params (swapInput input) = params input := rfl
  simp only [leftParser, rightParser, comp_apply, pair_apply, leftBits, rightBits,
    left, right, width, dim, fst_apply, snd_apply, ho, hp, const_apply]
  trivial

theorem program_swap_handled (input : Input)
    (h0 : 0 < (route input).1) (h8 : (route input).1 < 8) :
    program (swapInput input) = program input := by
  have hp := parsers_swap input h0 h8
  simp only [program, comp_apply, pair_apply, fst_apply,
    PauliBranchProgram.formatGuard_apply, PauliBranchProgram.selectProg_apply,
    hp.1, hp.2, checks_swap input h0 h8, route_kind_swap]

def Forward (T U : Ty) : Prop :=
  (∃ W, T = .point W ∧ U = .aline W) ∨
  (∃ W, T = .point W ∧ U = .dline W) ∨
  (∃ W, T = .point W ∧ U = .pauli W) ∨
  (∃ W, T = .pairB W ∧ U = .pair) ∨
  (∃ W, T = .point W ∧ U = .pairB W) ∨
  (∃ i v, T = .con i ∧ U = .var v) ∨
  (∃ W v, T = .point W ∧ U = .var v)

theorem forward_or_reverse (T U : Ty) (h0 : 0 < (PauliBranchProgram.route T U).1)
    (h8 : (PauliBranchProgram.route T U).1 < 8) : Forward T U ∨ Forward U T := by
  unfold Forward
  revert T U
  decide

theorem route_default_unhandled (T U : Ty) (h : (PauliBranchProgram.route T U).1 = 8) :
    handled T U = false := by
  revert T U
  decide

end MIPRE.QLD.PauliBooleanProgram
end
