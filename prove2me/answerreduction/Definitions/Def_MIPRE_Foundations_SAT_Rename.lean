/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Rename.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
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
import Theorems.Thm_MIPRE_SAT_Fml_encode_fml

/-!
# Renaming formula inputs in polynomial time

The padding construction changes the offsets of the five index blocks and their
sign bits. Renaming scans the post-order serialization, applying an ambient program
only at input nodes. `renameBy` uses a finite table and the binary-indexed lookup
program, so its cost does not assume that all input indices are small.
-/

namespace MIPRE.SAT.Fml

open Cost Cost.PolyTimeFun

/-- Rename the input bits without changing the formula's tree. -/
def rename (ρ : ℕ → ℕ) : Fml → Fml
  | .inp i => .inp (ρ i)
  | .const b => .const b
  | .and f g => .and (rename ρ f) (rename ρ g)
  | .or f g => .or (rename ρ f) (rename ρ g)
  | .not f => .not (rename ρ f)

@[simp] theorem eval_rename (ρ : ℕ → ℕ) (f : Fml) (x : ℕ → Bool) :
    (rename ρ f).eval x = f.eval (x ∘ ρ) := by
  induction f <;> simp_all [rename, eval, Function.comp_def]

@[simp] theorem size_rename (ρ : ℕ → ℕ) (f : Fml) : (rename ρ f).size = f.size := by
  induction f <;> simp_all [rename, size]

/-- The serialization-level action of a renaming. -/
def Node.rename (ρ : ℕ → ℕ) : Node → Node
  | .inp i => .inp (ρ i)
  | .const b => .const b
  | .and => .and
  | .or => .or
  | .not => .not

theorem rpn_rename (ρ : ℕ → ℕ) (f : Fml) :
    (rename ρ f).rpn = f.rpn.map (Node.rename ρ) := by
  induction f <;> simp_all [rename, rpn, Node.rename]

variable {α : Type*} [SizedEncoding α]

noncomputable def renameNodeProg (R : PolyTimeFun (α × ℕ) ℕ) :
    PolyTimeFun (α × Node) Node :=
  MIPRE.SAT.PolyTimeFun.casesNode ((tagged 0 Node.inp Node.encode_inp).comp R)
    ((tagged 1 Node.const Node.encode_const).comp snd)
    (PolyTimeFun.const Node.and) (PolyTimeFun.const Node.or) (PolyTimeFun.const Node.not)

theorem renameNodeProg_apply (R : PolyTimeFun (α × ℕ) ℕ) (a : α) (nd : Node) :
    renameNodeProg R (a, nd) = Node.rename (fun i => R (a, i)) nd := by
  cases nd <;> rfl

/-- Any polynomial-time index transformation gives a polynomial-time formula renaming. -/
noncomputable def renameProg (R : PolyTimeFun (α × ℕ) ℕ) : PolyTimeFun (α × Fml) Fml :=
  PolyTimeFun.cast ((mapWith ((renameNodeProg R).comp (snd.pair fst))).comp
    ((rpnF.comp snd).pair fst)) (fun p => rename (fun i => R (p.1, i)) p.2) (by
      intro p
      simp only [comp_apply, mapWith_apply, pair_apply, fst_apply, snd_apply, rpnF_apply,
        renameNodeProg_apply, encode_fml, rpn_rename])

@[simp] theorem renameProg_apply (R : PolyTimeFun (α × ℕ) ℕ) (p : α × Fml) :
    renameProg R p = rename (fun i => R (p.1, i)) p.2 := rfl

/-- Rename inputs using the supplied table; an out-of-range index maps to zero. -/
noncomputable def renameBy : PolyTimeFun (List ℕ × Fml) Fml :=
  renameProg ((ArrayProg.getD 0).comp (snd.pair fst))

@[simp] theorem renameBy_apply (ρ : List ℕ) (f : Fml) :
    renameBy (ρ, f) = rename (fun i => ρ.getD i 0) f := rfl

end MIPRE.SAT.Fml
