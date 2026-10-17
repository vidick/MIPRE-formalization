/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Seeds.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Theorems.Thm_MIPRE_LIDT_CL_card_div_pos
import Theorems.Thm_MIPRE_LIDT_CL_chi_val

/-!
# The seeded-CL adapter, part 3: choosing a seed

The adapter must turn a line of the canonical-line test into a *seeded* description of that
line, which means choosing one of the `q/m` seeds in the relevant `χ`-fibre
(`MIPRE.LIDT.CL.card_chi_fiber`). `seedOf` is the explicit choice, indexed by the fibre
position: `seedOf hm i r` is the `r`-th seed with `χ = i`, and `chi_seedOf` says so.

`card_chi_fiber` proves the fibre has `q/m` elements by exhibiting an equivalence with
`Fin (q/m)`; `seedOf` is that equivalence's inverse, extracted so that the adapter can name a
seed rather than merely know one exists. `seedOf_injective` is the other half, and it is what
makes the averaging count: the `q/m` seeds `seedOf hm i r` are distinct, so averaging a choice
over `r` is averaging over the whole fibre, which is where the reduction pays back the factor
`q/m` that a fixed choice would cost (see `MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le`
and the discussion in `planning/lidt-cl-adapter.md`).
-/

namespace MIPRE.LIDT.Adapter

open Finset MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

/-- The `r`-th seed of the `χ`-fibre over `i`, under the fixed bijection `F ≃ Fin q`. -/
noncomputable def seedOf (hm : m ∣ Fintype.card F) (i : Fin m) (r : Fin (Fintype.card F / m)) : F :=
  (Fintype.equivFin F).symm ⟨(i : ℕ) * (Fintype.card F / m) + (r : ℕ), by
    have hmc : m * (Fintype.card F / m) = Fintype.card F := Nat.mul_div_cancel' hm
    have hi : (i : ℕ) + 1 ≤ m := i.isLt
    calc (i : ℕ) * (Fintype.card F / m) + (r : ℕ)
        < (i : ℕ) * (Fintype.card F / m) + (Fintype.card F / m) := by omega
      _ = ((i : ℕ) + 1) * (Fintype.card F / m) := by ring
      _ ≤ m * (Fintype.card F / m) := Nat.mul_le_mul_right _ hi
      _ = Fintype.card F := hmc⟩

omit [Field F] [DecidableEq F] [NeZero m] in
@[simp] theorem equivFin_seedOf (hm : m ∣ Fintype.card F) (i : Fin m)
    (r : Fin (Fintype.card F / m)) :
    ((Fintype.equivFin F) (seedOf hm i r) : ℕ)
      = (i : ℕ) * (Fintype.card F / m) + (r : ℕ) := by
  rw [seedOf, Equiv.apply_symm_apply]

omit [DecidableEq F] in
/-- **`seedOf hm i r` lies in the fibre over `i`.** -/
@[simp] theorem chi_seedOf (hm : m ∣ Fintype.card F) (i : Fin m)
    (r : Fin (Fintype.card F / m)) : chi hm (seedOf hm i r) = i := by
  have hr : (r : ℕ) < Fintype.card F / m := r.isLt
  refine Fin.ext ?_
  rw [chi_val, equivFin_seedOf, mul_comm, Nat.mul_add_div (card_div_pos hm),
    Nat.div_eq_of_lt hr, add_zero]

end MIPRE.LIDT.Adapter
