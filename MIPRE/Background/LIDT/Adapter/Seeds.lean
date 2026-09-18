/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.CLGame

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

omit [Field F] [DecidableEq F] [NeZero m] in
/-- The `q/m` seeds of a fibre are distinct, so averaging a choice over `r` averages over the
whole fibre. -/
theorem seedOf_injective (hm : m ∣ Fintype.card F) (i : Fin m) :
    Function.Injective (seedOf hm i) := by
  intro r r' h
  have h' := congrArg (fun s => ((Fintype.equivFin F) s : ℕ)) h
  simp only [equivFin_seedOf] at h'
  exact Fin.ext (by omega)

omit [DecidableEq F] in
/-- Conversely every seed is one of the `seedOf`, at its own fibre position. -/
theorem exists_seedOf (hm : m ∣ Fintype.card F) (s : F) :
    ∃ r : Fin (Fintype.card F / m), seedOf hm (chi hm s) r = s := by
  have hc0 : 0 < Fintype.card F / m := card_div_pos hm
  refine ⟨⟨((Fintype.equivFin F) s : ℕ) % (Fintype.card F / m), Nat.mod_lt _ hc0⟩, ?_⟩
  rw [seedOf, Equiv.symm_apply_eq]
  refine Fin.ext ?_
  show (chi hm s : ℕ) * (Fintype.card F / m)
      + ((Fintype.equivFin F) s : ℕ) % (Fintype.card F / m)
    = ((Fintype.equivFin F) s : ℕ)
  rw [chi_val, mul_comm]
  exact Nat.div_add_mod _ _

end MIPRE.LIDT.Adapter
