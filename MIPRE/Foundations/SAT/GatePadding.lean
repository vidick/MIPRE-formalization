/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.ArrayProg
import MIPRE.Foundations.SAT.Tseitin

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

private theorem terminal_of_refsLt (C : Circuit) (h : C.RefsLt) :
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

/-- A copying gate preserves the circuit's value. -/
theorem eval_copyOutput (C : Circuit) (hne : C.gates ≠ []) (x : ℕ → Bool) :
    (copyOutput C).eval x = C.eval x := by
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
  have hne' : (copyOutput C).gates ≠ [] := by simp [copyOutput]
  rw [Circuit.eval, if_neg hne', Circuit.eval, if_neg hne]
  change (copyOutput C).valueAt x ((C.gates ++ [_]).length - 1) = _
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [Circuit.valueAt_eq]
  change ((C.gates ++ [_]).getD C.gates.length (.const false)).eval x _ = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some, Gate.eval]
  rw [Fml.Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), Bool.or_self]
  exact Fml.Circuit.valueAt_append _ _ _ _ _ (by omega)

/-- A copying gate preserves topological order, fan-out two, and a terminal output. -/
theorem wellFormed_copyOutput {C : Circuit} (hC : C.WellFormed) : (copyOutput C).WellFormed := by
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hC.nonempty
  have href : (copyOutput C).RefsLt := by
    intro k hk u hu
    change k < (C.gates ++ [Gate.or (C.gates.length - 1) (C.gates.length - 1)]).length at hk
    change u ∈ (C.gates ++ [_])[k].refs at hu
    by_cases hold : k < C.gates.length
    · rw [List.getElem_append_left hold] at hu
      exact hC.refs_lt k hold u hu
    · have he : k = C.gates.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst k
      rw [List.getElem_append_right (by omega)] at hu
      simp only [Nat.sub_self, List.getElem_cons_zero, Gate.refs, List.mem_cons,
        List.not_mem_nil, or_false, or_self] at hu
      omega
  refine ⟨href, ?_, ?_, terminal_of_refsLt _ href, by simp [copyOutput]⟩
  · intro i hi
    have hi' : Gate.input i ∈ C.gates := by simpa [copyOutput] using hi
    exact hC.inputs_lt i hi'
  · intro u
    have hbase := hC.fanout_le u
    change (C.gates.map (fun g => g.refs.count u)).sum ≤ 2 at hbase
    by_cases hu : u = C.gates.length - 1
    · subst u
      have ht := hC.output_terminal
      change (C.gates.map (fun g => g.refs.count (C.gates.length - 1))).sum = 0 at ht
      simp only [copyOutput, fanout, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil]
      rw [ht]
      simp [Gate.refs]
    · simpa [copyOutput, fanout, Gate.refs, hu, Ne.symm hu] using hbase

/-- Append exactly `k` copying gates. -/
def padGates (C : Circuit) (k : ℕ) : Circuit :=
  ⟨C.inputs, C.gates ++ (List.range' (C.gates.length - 1) k).map (fun i => Gate.or i i)⟩

@[simp] theorem padGates_inputs (C : Circuit) (k : ℕ) : (padGates C k).inputs = C.inputs := rfl

@[simp] theorem padGates_size (C : Circuit) (k : ℕ) : (padGates C k).size = C.size + k := by
  simp [padGates, size]

@[simp] theorem padGates_zero (C : Circuit) : padGates C 0 = C := by cases C; simp [padGates]

private theorem padGates_succ (C : Circuit) (hne : C.gates ≠ []) (k : ℕ) :
    padGates C (k + 1) = copyOutput (padGates C k) := by
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
  have he : C.gates.length - 1 + k = C.gates.length + k - 1 := by omega
  simp [padGates, copyOutput, List.range'_concat, he, List.append_assoc]

/-- Exact gate padding preserves well-formedness. -/
theorem wellFormed_padGates {C : Circuit} (hC : C.WellFormed) (k : ℕ) :
    (padGates C k).WellFormed := by
  induction k with
  | zero => simpa using hC
  | succ k ih => rw [padGates_succ C hC.nonempty]; exact wellFormed_copyOutput ih

/-- Exact gate padding preserves the function on every input. -/
theorem eval_padGates {C : Circuit} (hC : C.WellFormed) (k : ℕ) (x : ℕ → Bool) :
    (padGates C k).eval x = C.eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [padGates_succ C hC.nonempty, eval_copyOutput _ (wellFormed_padGates hC k).nonempty, ih]

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
