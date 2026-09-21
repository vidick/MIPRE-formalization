/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestCore

/-! # Perfect PCC completeness of the four-type introspection core

This is the actual induced subgraph on the two Introspect and two Sample
types, with the restriction of the parsed typed predicate. The constructed
strategy is a concrete seed-register extension of the original PCC strategy.
Read, Hide, and Pauli vertices are not part of this intermediate theorem.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] {ℓ : ℕ}

def CoreAdj (t u : CoreType) : Prop := t.2 = u.2 ∨ t.1 = false ∧ u.1 = false

theorem coreAdj_iff {P : Type*} [DecidableEq P] (E : P → P → Bool) (X Z : P)
    (t u : CoreType) :
    TypeGraph.Adj E X Z (coreType (ℓ := ℓ) t) (coreType u) ↔ CoreAdj t u := by
  rcases t with ⟨s, w⟩; rcases u with ⟨t, v⟩
  cases s <;> cases t <;> cases w <;> cases v <;>
    simp [CoreAdj, coreType, TypeGraph.Adj, TypeGraph.adj, TypeGraph.oriented]

variable (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)

/-- Restrict the actual parsed predicate to core types and pair-format answers. -/
def coreCheck (t u : CoreType) (a b : (ι → F) × A) : Bool :=
  TypedPredicate.check L () () (fun _ : Unit => 0) D (fun _ _ _ _ => true)
    (coreType t) (coreType u) (.pair a.1 a.2) (.pair b.1 b.2)

/-- The Pauli parameters have no effect on this restriction. -/
theorem coreCheck_eq {P PA : Type*} (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (t u : CoreType) (a b : (ι → F) × A) :
    coreCheck L D t u a b = TypedPredicate.check L X Z projectPauli D DP
      (coreType t) (coreType u) (.pair a.1 a.2) (.pair b.1 b.2) := by
  rcases t with ⟨s, w⟩; rcases u with ⟨t, v⟩
  cases s <;> cases t <;> cases w <;> cases v <;>
    simp [coreCheck, coreType, TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed]

variable (R : SyncStrategy (sourceGame L D).doubled)

/-- A nonzero honest seed block always produces an accepted core answer pair. -/
theorem coreCheck_common (hR : R.IsPCC) (hval : R.value = 1)
    (t u : CoreType) (z : ι → F) (a b : A)
    (hNZ : R.P.M (t.2, (L t.2).eval z) a * R.P.M (u.2, (L u.2).eval z) b ≠ 0) :
    coreCheck L D t u (displayed L t z, a) (displayed L u z, b) = true := by
  have hab : t.2 = u.2 → a = b := by
    intro hw
    by_contra hn
    apply hNZ
    rw [hw]
    exact R.orthogonal _ hn
  have hforward : t.2 = false → u.2 = true →
      D ((L false).eval z) ((L true).eval z) a b = true := by
    intro ht hu
    cases hd : D ((L false).eval z) ((L true).eval z) a b with
    | true => rfl
    | false => exact False.elim (hNZ (by simpa [ht, hu] using source_reject_zero L D R hR hval z a b hd))
  have hreverse : t.2 = true → u.2 = false →
      D ((L false).eval z) ((L true).eval z) b a = true := by
    intro ht hu
    cases hd : D ((L false).eval z) ((L true).eval z) b a with
    | true => rfl
    | false =>
      apply False.elim
      apply hNZ
      rw [(source_commute L D R hR t.2 u.2 z a b).eq]
      simpa [ht, hu] using source_reject_zero L D R hR hval z b a hd
  rcases t with ⟨s, w⟩; rcases u with ⟨t, v⟩
  cases w <;> cases v
  · have he := hab rfl; subst b
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, CLChecks.sampling]
  · have hd := hforward rfl rfl
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, hd]
  · have hd := hreverse rfl rfl
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, hd]
  · have he := hab rfl; subst b
    cases s <;> cases t <;> simp [coreCheck, coreType, displayed, TypedPredicate.check,
      TypedPredicate.fits, TypedPredicate.directed, CLChecks.sampling]

/-- Rejected answers have zero operator product, for every core question pair. -/
theorem coreOp_reject_zero (hR : R.IsPCC) (hval : R.value = 1)
    (t u : CoreType) (ya zb : (ι → F) × A) (hD : coreCheck L D t u ya zb = false) :
    coreOp L D R t ya * coreOp L D R u zb = 0 := by
  ext ⟨s, i⟩ ⟨s', j⟩
  rw [coreOp_mul_apply]
  split_ifs with h
  · by_cases hz : R.P.M (t.2, (L t.2).eval s) ya.2 * R.P.M (u.2, (L u.2).eval s) zb.2 = 0
    · simp [hz]
    · have hc := coreCheck_common L D R hR hval t u s ya.2 zb.2 hz
      rw [h.2.1, h.2.2] at hc
      have hh : coreCheck L D t u ya zb = true := hc
      rw [hD] at hh
      cases hh
  · rfl

/-- The uniform ordered-edge game on the induced core graph. -/
def coreGame : Game CoreType CoreType ((ι → F) × A) ((ι → F) × A) := by
  let Edge := {p : CoreType × CoreType // CoreAdj p.1 p.2}
  letI : Nonempty Edge := ⟨⟨((false, false), (false, false)), Or.inl rfl⟩⟩
  exact SampledGame.game (fun e : Edge => e.val.1) (fun e : Edge => e.val.2) (coreCheck L D)

/-- A concrete synchronous honest strategy; the outer doubling tag is ignored. -/
def coreStrategy : SyncStrategy (coreGame L D).doubled where
  d := Fintype.card ((ι → F) × Fin R.d)
  d_pos := by
    let : Nonempty (Fin R.d) := Fin.pos_iff_nonempty.mp R.d_pos
    exact Fintype.card_pos
  P :=
    { M := fun p a => registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm (coreOp L D R p.2 a)
      selfAdjoint := fun p a => by
        rw [Matrix.star_eq_conjTranspose]
        exact (registerOp_isPVM _ (coreOp_isPVM L D R p.2)).isSelfAdjoint a
      projective := fun p a => (registerOp_isPVM _ (coreOp_isPVM L D R p.2)).idem a
      normalized := fun p => (registerOp_isPVM _ (coreOp_isPVM L D R p.2)).sum_eq_one }

theorem coreStrategy_dimension : (coreStrategy L D R).d = Fintype.card (ι → F) * R.d := by
  simp [coreStrategy, Fintype.card_prod]

set_option backward.isDefEq.respectTransparency false in
theorem coreStrategy_isPCC (hR : R.IsPCC) : (coreStrategy L D R).IsPCC := by
  intro p q _ a b
  have h := congrArg (registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm)
    (coreOp_commute L D R hR p.2 q.2 a b).eq
  simpa only [coreStrategy, registerOp_mul] using h

set_option backward.isDefEq.respectTransparency false in
theorem coreStrategy_value (hR : R.IsPCC) (hval : R.value = 1) :
    (coreStrategy L D R).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro p q hμ a b hrej
  have htags : p.1 = false ∧ q.1 = true := by
    by_contra hn
    simp only [Game.doubled_μ, if_neg hn] at hμ
    exact (lt_irrefl 0) hμ
  have hd : coreCheck L D p.2 q.2 a b = false := by
    change (if p.1 = false ∧ q.1 = true then coreCheck L D p.2 q.2 a b else false) = false at hrej
    simpa only [if_pos htags] using hrej
  have hz : (coreStrategy L D R).P.M p a * (coreStrategy L D R).P.M q b = 0 := by
    have h := congrArg (registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm)
      (coreOp_reject_zero L D R hR hval p.2 q.2 a b hd)
    rw [show registerOp (Fintype.equivFin ((ι → F) × Fin R.d)).symm
      (0 : Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ) = 0 from rfl] at h
    simpa only [coreStrategy, registerOp_mul] using h
  rw [hz, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

/-- Perfect PCC completeness for all four honest core types and every source CL depth. -/
theorem exists_corePerfectPCC (hR : R.IsPCC) (hval : R.value = 1) :
    ∃ Q : SyncStrategy (coreGame L D).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = Fintype.card (ι → F) * R.d :=
  ⟨coreStrategy L D R, coreStrategy_isPCC L D R hR, coreStrategy_value L D R hR hval,
    coreStrategy_dimension L D R⟩

end MIPRE.Introspection.Honest
