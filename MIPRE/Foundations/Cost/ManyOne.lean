/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Cost.Semidecide
public import MIPRE.Foundations.Cost.Kleene

@[expose] public section

/-!
# The many-one reduction of an r.e. language to halting, in polynomial time

`Cost.exists_semidecider` turns an r.e. predicate on strings into a well-scoped program `S`
halting on `encode z` exactly on its members. The reduction to halting *on the empty input*
hard-codes `z` into `S` — the s-m-n theorem — and `hardcode` is linear time, so the map
`z ↦ M_z` is a `PolyTimeFun`. `Halting.exists_code_halts_of_isRE` is the same reduction on
Mathlib's `Nat.Partrec.Code` through `Code.curry`, with no time tracked; the polynomial-time
halting reduction (`planning/polytime-halting.md`) needs this one.

`hardcode p d` runs `p` on `cons d v` where `v` is the input, so on the empty input `nil` it
runs `p` on `cons d nil`; `Prog.onLeft p` is the program running `p` on the left component of
its input, and `M_z = hardcode (onLeft S) (encode z)`.
-/

namespace MIPRE.Cost

/-- On the input `cons d v`, run `p` on `d`; on `nil`, halt with `nil`. -/
def Prog.onLeft (p : Prog) : Prog := .elim 0 .nil (Prog.callVar 0 p)

theorem Prog.onLeft_wellScoped {p : Prog} (hp : p.WellScoped 1) : (Prog.onLeft p).WellScoped 1 :=
  ⟨by decide, trivial, Prog.callVar_wellScoped (by decide) hp⟩

/-- The reduction: `z ↦ hardcode (onLeft S) (encode z)`, in linear time. -/
noncomputable def haltingReduction (S : Prog) : PolyTimeFun BitStr Prog :=
  (PolyTimeFun.smn BitStr).comp ((PolyTimeFun.const (Prog.onLeft S)).pair (PolyTimeFun.id BitStr))

@[simp] theorem haltingReduction_apply (S : Prog) (z : BitStr) :
    haltingReduction S z = hardcode (Prog.onLeft S) (encode z) := rfl

theorem haltingReduction_wellScoped {S : Prog} (hS : S.WellScoped 1) (z : BitStr) :
    (haltingReduction S z).WellScoped 1 :=
  hardcode_wellScoped (Prog.onLeft_wellScoped hS) _

/-- **The reduction halts on the empty input exactly when `S` halts on `encode z`.** -/
theorem halts_haltingReduction_iff {S : Prog} (hS : S.WellScoped 1) (z : BitStr) :
    Halts (haltingReduction S z) .nil ↔ Halts S (encode z) := by
  have hw := Prog.onLeft_wellScoped hS
  constructor
  · rintro ⟨r, t, h⟩
    obtain ⟨t', -, h'⟩ := hardcode_time_rev hw h
    change Eval [Data.cons (encode z) .nil] (.elim 0 .nil _) r t' at h'
    cases h' with
    | elim_nil hget _ => simp at hget
    | elim_cons hget h₁ =>
      rw [Env.get_cons_zero] at hget
      obtain ⟨rfl, rfl⟩ := Data.cons.inj hget
      obtain ⟨t'', -, hp⟩ := Prog.callVar_runs_rev hS h₁
      rw [Env.get_cons_zero] at hp
      exact ⟨r, t'', hp⟩
  · rintro ⟨r, t, h⟩
    have h₁ := Prog.callVar_eval (env := [encode z, .nil, Data.cons (encode z) .nil]) (i := 0) hS
      (v := encode z) (by simp) h
    have h₂ := Eval.elim_cons (env := [Data.cons (encode z) .nil]) (i := 0) (n := .nil)
      (a := encode z) (b := .nil) (by simp) h₁
    exact ⟨r, _, hardcode_time hw h₂⟩

/-- **Every r.e. predicate on strings many-one reduces to halting on the empty input, in
polynomial time.** -/
theorem exists_polyTime_reduction {p : BitStr → Prop} (hp : REPred p) :
    ∃ R : PolyTimeFun BitStr Prog,
      (∀ z, (R z).WellScoped 1) ∧ ∀ z, Halts (R z) .nil ↔ p z := by
  obtain ⟨S, hS, hSp⟩ := exists_semidecider hp
  exact ⟨haltingReduction S, haltingReduction_wellScoped hS,
    fun z => (halts_haltingReduction_iff hS z).trans (hSp z)⟩

end MIPRE.Cost

end
