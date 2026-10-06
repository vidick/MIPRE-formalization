/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.SAT.GatePadding
public import MIPRE.Foundations.SAT.Decoupled6
public import MIPRE.Foundations.LowDegree.UnaryDegreeArithmetic

@[expose] public section

/-!
# Padding a circuit to an exact gate count

A circuit with at most `s` gates is padded to exactly `s` gates by copying gates
(`Circuit.padGates`); a larger one is replaced by a trivial circuit of `s` gates with the same
inputs, so that the gate count is `s` on every input (`Circuit.padTo`). On the circuits that fit,
padding preserves well-formedness, the function computed, the formula the circuit describes, and
the succinct description of a decider through three windows (`describesWindows_padTo`); the
padding is computed in polynomial time from the circuit and `s` in unary (`padToProg`). The
answer reduction's circuit function pads the window describer's circuits to its gate bound
(slice P4i).
-/

namespace MIPRE.SAT.Circuit

open Cost Cost.PolyTimeFun

/-- The trivial circuit on `i` inputs: one constant gate. -/
def trivial (i : ℕ) : Circuit := ⟨i, [Gate.const false]⟩

theorem wellFormed_trivial (i : ℕ) : (trivial i).WellFormed where
  refs_lt k h u hu := by
    simp only [trivial, List.length_singleton, Nat.lt_one_iff] at h
    subst h
    simp [trivial, Gate.refs] at hu
  inputs_lt j hj := by simp [trivial] at hj
  fanout_le u := by simp [fanout, trivial, Gate.refs]
  output_terminal := by simp [fanout, trivial, Gate.refs]
  nonempty := by simp [trivial]

/-- **A circuit padded to exactly `s` gates**: copying gates when it has at most `s`, else the
trivial circuit padded. -/
def padTo (C : Circuit) (s : ℕ) : Circuit :=
  if C.size ≤ s then padGates C (s - C.size) else padGates (trivial C.inputs) (s - 1)

@[simp] theorem padTo_inputs (C : Circuit) (s : ℕ) : (padTo C s).inputs = C.inputs := by
  unfold padTo; split_ifs <;> rfl

theorem padTo_size (C : Circuit) {s : ℕ} (hs : 1 ≤ s) : (padTo C s).size = s := by
  unfold padTo
  split_ifs with h
  · rw [padGates_size]; omega
  · rw [padGates_size]; simp [trivial, size]; omega

theorem wellFormed_padTo {C : Circuit} (hC : C.WellFormed) (s : ℕ) : (padTo C s).WellFormed := by
  unfold padTo
  split_ifs
  · exact wellFormed_padGates hC _
  · exact wellFormed_padGates (wellFormed_trivial _) _

theorem padTo_of_le (C : Circuit) {s : ℕ} (h : C.size ≤ s) : padTo C s = padGates C (s - C.size) :=
  ite_eq_left_iff.mpr fun h' => absurd h h'

theorem evalBits_padTo {C : Circuit} (hC : C.WellFormed) {s : ℕ} (h : C.size ≤ s)
    (l : List Bool) : (padTo C s).evalBits l = C.evalBits l := by
  rw [padTo_of_le C h, evalBits, evalBits, eval_padGates hC]

theorem formula6_padTo {C : Circuit} (hC : C.WellFormed) {s : ℕ} (h : C.size ≤ s)
    (ℓa ℓb ℓc r : ℕ) : (padTo C s).formula6 ℓa ℓb ℓc r = C.formula6 ℓa ℓb ℓc r := by
  ext c
  simp only [formula6, Set.mem_ofPred_eq, evalBits_padTo hC h]

/-- **Padding preserves a description through three windows.** -/
theorem describesWindows_padTo {C : Circuit} (hC : C.WellFormed) {s : ℕ} (h : C.size ≤ s)
    {ℓa ℓb ℓc r : ℕ} {D : Decider} {n : ℕ} {x y : Cost.BitStr} {T : ℕ}
    (hD : C.DescribesWindows ℓa ℓb ℓc r D n x y T) :
    (padTo C s).DescribesWindows ℓa ℓb ℓc r D n x y T := by
  unfold DescribesWindows at hD ⊢
  rw [formula6_padTo hC h]
  exact hD

/-- The trivial circuit, from the input count. -/
noncomputable def trivialProg : PolyTimeFun ℕ Circuit :=
  PolyTimeFun.cast ((PolyTimeFun.id ℕ).pair (const [Gate.const false])) trivial (fun _ => rfl)

@[simp] theorem trivialProg_apply (i : ℕ) : trivialProg i = trivial i := rfl

/-- **Exact padding in polynomial time**, from the circuit and `s` in unary. -/
noncomputable def padToProg : PolyTimeFun (Circuit × Unary) Circuit :=
  let gs : PolyTimeFun (Circuit × Unary) (List Gate) := snd.comp (partsProg.comp fst)
  ite (LowDegree.DegreeArithmetic.leUnaryProg.comp ((length.comp gs).pair snd))
    (padGatesProg.comp (fst.pair (drop.comp (snd.pair (length.comp gs)))))
    (padGatesProg.comp ((trivialProg.comp (fst.comp (partsProg.comp fst))).pair
      (tail.comp snd)))

@[simp] theorem padToProg_apply (C : Circuit) (u : Unary) : padToProg (C, u) = padTo C u.length := by
  by_cases h : C.gates.length ≤ u.length
  · have e : padToProg (C, u) = padGates C (u.length - C.gates.length) := by
      simp [padToProg, h, partsProg, ofEncodeEq_apply]
    rw [e, padTo_of_le C (by simpa [size] using h)]
    rfl
  · have e : padToProg (C, u) = padGates (trivial C.inputs) (u.length - 1) := by
      simp [padToProg, h, partsProg, ofEncodeEq_apply]
    rw [e, padTo, ite_eq_right_iff.mpr fun h' => absurd (by simpa [size] using h') h]

end MIPRE.SAT.Circuit

end
