/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Formula

/-!
# Every Boolean function has a circuit

The formula of a Boolean function on `N` bits from its truth table (`Fml.table`): a mux tree
on the bits, of size at most `7 · 2^N`. Its circuit is well-formed (`Fml.toCircuit_wellFormed`)
and computes the function (`Fml.eval_table`). This is how the check circuit of the
Cook–Levin tableau of the interpreter machine is obtained: from the truth table of the
local check predicate, as in the paper's `lem:pack-check-size`
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.SAT

namespace Fml

/-- The formula of a Boolean function on `N` bits: a mux tree on the bits, the leaves being
the entries of the truth table. -/
def table : (N : ℕ) → ((Fin N → Bool) → Bool) → Fml
  | 0, f => const (f Fin.elim0)
  | N + 1, f =>
    or (and (inp N) (table N fun x => f (Fin.snoc x true)))
      (and (not (inp N)) (table N fun x => f (Fin.snoc x false)))

theorem eval_table : ∀ (N : ℕ) (f : (Fin N → Bool) → Bool) (x : ℕ → Bool),
    (table N f).eval x = f fun i => x i
  | 0, f, x => by
    simp only [table, eval]
    congr
    funext i
    exact i.elim0
  | N + 1, f, x => by
    simp only [table, eval, eval_table N]
    have hsnoc : ∀ b : Bool, x N = b →
        (Fin.snoc (fun i : Fin N => x i) b : Fin (N + 1) → Bool) = fun i : Fin (N + 1) => x i := by
      intro b hb
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp [Fin.snoc_castSucc]
      · simp [Fin.snoc_last, hb]
    cases hx : x N with
    | false => simp [hsnoc false hx]
    | true => simp [hsnoc true hx]

theorem table_inputsLt : ∀ (N : ℕ) (f : (Fin N → Bool) → Bool), (table N f).InputsLt N
  | 0, _ => trivial
  | N + 1, f => by
    refine ⟨⟨Nat.lt_succ_self N, (table_inputsLt N _).mono (Nat.le_succ N)⟩,
      Nat.lt_succ_self N, (table_inputsLt N _).mono (Nat.le_succ N)⟩

theorem size_table : ∀ (N : ℕ) (f : (Fin N → Bool) → Bool), (table N f).size + 6 ≤ 7 * 2 ^ N
  | 0, _ => by simp [table, size]
  | N + 1, f => by
    simp only [table, size]
    have h1 := size_table N fun x => f (Fin.snoc x true)
    have h2 := size_table N fun x => f (Fin.snoc x false)
    rw [Nat.pow_succ]
    omega

/-- **Every Boolean function on `N` bits is computed by a well-formed circuit on `N` inputs**
of at most `7 · 2^N` gates. -/
theorem exists_circuit (N : ℕ) (f : (Fin N → Bool) → Bool) :
    ∃ C : Circuit, C.WellFormed ∧ C.inputs = N ∧ C.size ≤ 7 * 2 ^ N ∧
      ∀ x : Fin N → Bool, C.evalBits (List.ofFn x) = f x := by
  refine ⟨(table N f).toCircuit N, toCircuit_wellFormed _ (table_inputsLt N f), rfl,
    by rw [toCircuit_size]; have := size_table N f; omega, fun x => ?_⟩
  rw [evalBits_toCircuit, eval_table]
  congr
  funext i
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
  rfl

end Fml

end MIPRE.SAT
