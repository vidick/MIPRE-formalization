/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/GatePadding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin

/-!
# Exact gate-count padding

Our circuit representation designates its last gate as the output. To add any
number of gates while retaining that convention, append copying OR gates, each
reading the previous output twice. Every former output has fan-out two; the new
output is terminal. This realizes the exact-size padding required by
`prop:explicit-padded-succinct-deciders`, without a separate output-wire index.
-/

namespace MIPRE.SAT.Circuit

open Cost Cost.PolyTimeFun

/-- Append one gate copying the previous output. -/
def copyOutput (C : Circuit) : Circuit :=
  ⟨C.inputs, C.gates ++ [Gate.or (C.gates.length - 1) (C.gates.length - 1)]⟩

theorem terminal_of_refsLt (C : Circuit) (h : C.RefsLt) :
    C.fanout (C.gates.length - 1) = 0 := by
  have hz : ∀ g ∈ C.gates, g.refs.count (C.gates.length - 1) = 0 := by
    intro g hg
    apply List.count_eq_zero.mpr
    intro hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have := h i hi _ hmem
    omega
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
  exact hz g hg

/-- Append exactly `k` copying gates. -/
def padGates (C : Circuit) (k : ℕ) : Circuit :=
  ⟨C.inputs, C.gates ++ (List.range' (C.gates.length - 1) k).map (fun i => Gate.or i i)⟩

@[simp] theorem padGates_inputs (C : Circuit) (k : ℕ) : (padGates C k).inputs = C.inputs := rfl

@[simp] theorem padGates_size (C : Circuit) (k : ℕ) : (padGates C k).size = C.size + k := by
  simp [padGates, size]

@[simp] theorem padGates_zero (C : Circuit) : padGates C 0 = C := by cases C; simp [padGates]

theorem padGates_succ (C : Circuit) (hne : C.gates ≠ []) (k : ℕ) :
    padGates C (k + 1) = copyOutput (padGates C k) := by
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
  have he : C.gates.length - 1 + k = C.gates.length + k - 1 := by omega
  simp [padGates, copyOutput, List.range'_concat, he, List.append_assoc]

/-- The pair representation of a circuit has the same encoding. -/
noncomputable def partsProg : PolyTimeFun Circuit (ℕ × List Gate) :=
  ofEncodeEq (fun C => (C.inputs, C.gates)) (fun _ => rfl)

/-- Construct exact gate padding in polynomial time in the original circuit and
the number of padding gates, supplied in unary. -/
noncomputable def padGatesProg : PolyTimeFun (Circuit × Unary) Circuit :=
  let parts := partsProg.comp fst
  let gs := snd.comp parts
  let start := unaryToBin.comp (tail.comp (length.comp gs))
  let extra := (map (Gate.orF.comp ((PolyTimeFun.id _).pair (PolyTimeFun.id _)))).comp
    (ap₂ range'P start snd)
  PolyTimeFun.cast ((fst.comp parts).pair (ap₂ append gs extra))
    (fun p => padGates p.1 p.2.length) (by
      intro p
      simp only [parts, gs, extra, start, partsProg, pair_apply, comp_apply, fst_apply,
        ap₂_apply, append_apply, snd_apply,
        map_apply, range'P_apply, unaryToBin_apply, tail_apply, length_apply,
        List.length_tail, length_unary, Gate.orF]
      rfl)

@[simp] theorem padGatesProg_apply (p : Circuit × Unary) :
    padGatesProg p = padGates p.1 p.2.length := rfl

end MIPRE.SAT.Circuit
