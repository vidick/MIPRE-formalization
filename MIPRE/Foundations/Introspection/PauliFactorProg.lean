/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliStageProg
import MIPRE.Foundations.Introspection.BinaryBlockProg

/-! # The executable Pauli factor query

The field registers are fixed across all types and prefixes. Stage one reads
the seed, stage two the direction, and stage three the points and scalars.
Each field flag is repeated for all of its binary basis coordinates. Invalid
stages return the all-zero mask of the same ambient length.
-/

noncomputable section
namespace MIPRE.Introspection.PauliStageProgram
open Cost Cost.PolyTimeFun SAT

def factorFlags (m r : ℕ) : BitStr :=
  List.replicate m (decide (r = 3)) ++ List.replicate m (decide (r = 3)) ++
    [decide (r = 1)] ++ List.replicate m (decide (r = 2)) ++
    [decide (r = 3), decide (r = 3)]

def factorFlagsProg : PolyTimeFun (Parameters × ℕ) BitStr :=
  let m := snd.comp (snd.comp fst)
  let flag (r : ℕ) := ap₂ ArrayProg.eqNat snd (const r)
  let copies (r : ℕ) := replicate.comp (m.pair (flag r))
  ap₂ append (copies 3) (ap₂ append (copies 3)
    (cons (flag 1) (ap₂ append (copies 2) (cons (flag 3) (cons (flag 3) (const []))))))

theorem factorFlagsProg_apply (p : Parameters) (r : ℕ) :
    factorFlagsProg (p, r) = factorFlags p.2.2.length r := by
  simp [factorFlagsProg, factorFlags, List.append_assoc]
  rw [List.replicate_add]
  simp only [List.append_assoc]

/-- A single total program prints the factor mask for arbitrary unary widths
and dimensions. The selector width is retained in the common parameter tuple. -/
def factorBits : PolyTimeFun (Parameters × ℕ) BitStr :=
  BinaryBlock.flattenProg.comp ((mapWith (replicate.comp (snd.pair fst))).comp
    (factorFlagsProg.pair (fst.comp fst)))

theorem factorBits_apply (p : Parameters) (r : ℕ) :
    factorBits (p, r) =
      ((factorFlags p.2.2.length r).map (fun b => List.replicate p.1.length b)).flatten := by
  simp [factorBits, BinaryBlock.flattenProg_apply, factorFlagsProg_apply]

theorem factorFlags_length (m r : ℕ) : (factorFlags m r).length = 3 * m + 3 := by
  simp [factorFlags]
  omega

theorem factorBits_length (p : Parameters) (r : ℕ) :
    (factorBits (p, r)).length = (3 * p.2.2.length + 3) * p.1.length := by
  rw [factorBits_apply]
  have he (l : BitStr) :
      (l.map (fun b => List.replicate p.1.length b)).flatten.length = l.length * p.1.length := by
    induction l with
    | nil => simp
    | cons b l ih => simp [ih, Nat.add_mul, Nat.add_comm]
  rw [he, factorFlags_length]

theorem factorBits_runs (x : Parameters × ℕ) :
    ∃ r ≤ factorBits.timeBound.eval (esize x),
      factorBits.code.Runs (encode x) (encode (factorBits x)) r := factorBits.computes x

end MIPRE.Introspection.PauliStageProgram
end
