/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.ArrayProg

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

/-- Only the input positions used by a bounded formula affect its value. -/
theorem eval_congr_of_inputsLt {n : ℕ} {f : Fml} (hf : f.InputsLt n)
    (x y : ℕ → Bool) (hxy : ∀ i < n, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | inp i => exact hxy i hf
  | const b => rfl
  | and f g ihf ihg => simp only [eval, ihf hf.1, ihg hf.2]
  | or f g ihf ihg => simp only [eval, ihf hf.1, ihg hf.2]
  | not f ih => simp only [eval, ih hf]

theorem InputsLt.rename {n m : ℕ} {f : Fml} (hf : f.InputsLt n)
    (ρ : ℕ → ℕ) (hρ : ∀ i < n, ρ i < m) : (rename ρ f).InputsLt m := by
  induction f with
  | inp i => exact hρ i hf
  | const b => trivial
  | and f g ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | or f g ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | not f ih => exact ih hf

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

private noncomputable def renameNodeProg (R : PolyTimeFun (α × ℕ) ℕ) :
    PolyTimeFun (α × Node) Node :=
  MIPRE.SAT.PolyTimeFun.casesNode ((tagged 0 Node.inp Node.encode_inp).comp R)
    ((tagged 1 Node.const Node.encode_const).comp snd)
    (PolyTimeFun.const Node.and) (PolyTimeFun.const Node.or) (PolyTimeFun.const Node.not)

private theorem renameNodeProg_apply (R : PolyTimeFun (α × ℕ) ℕ) (a : α) (nd : Node) :
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
