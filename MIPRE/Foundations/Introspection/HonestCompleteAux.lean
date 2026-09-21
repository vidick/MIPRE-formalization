/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestCoreGame
import MIPRE.Foundations.Introspection.HonestParsedHiding

/-! # The complete honest auxiliary measurement family

All auxiliary vertices use one common register/source space. The graph and
predicate are the actual restrictions of the typed introspection construction,
including every Hide level, Read, Sample, Introspect, and consistency loops.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {F ι A PA P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
  [Fintype PA] [DecidableEq P] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

abbrev AuxQuestion (ℓ : ℕ) := AuxType ℓ × Bool

def auxOp (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t : AuxQuestion ℓ) : ParsedAnswer (ι → F) A PA →
      Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ :=
  match t.1 with
  | .introspect => parsedCoreOp L D R (false, t.2)
  | .sample => parsedCoreOp L D R (true, t.2)
  | .read => parsedReadOp L D R t.2 (hL t.2)
  | .hide k => parsedHideOp L D R t.2 k.val (hL t.2)

theorem auxOp_isPVM (hL : ∀ w, (L w).SupportedOn Finset.univ) (t : AuxQuestion ℓ) :
    IsPVM (auxOp (PA := PA) L D R hL t) := by
  rcases t with ⟨t, w⟩
  cases t
  · exact parsedCoreOp_isPVM L D R _
  · exact parsedCoreOp_isPVM L D R _
  · exact parsedReadOp_isPVM L D R _ _
  · exact parsedHideOp_isPVM L D R _ _ _

theorem parsedCore_core_commute (hR : R.IsPCC) (t u : CoreType)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (parsedCoreOp L D R t a) (parsedCoreOp L D R u b) := by
  cases a <;> cases b <;> simp only [parsedCoreOp, Commute.zero_left, Commute.zero_right]
  exact coreOp_commute L D R hR t u _ _

theorem parsedCore_core_reject_zero (hR : R.IsPCC) (hval : R.value = 1)
    (X Z : P) (projectPauli : PA → ι → F) (DP : P → P → PA → PA → Bool)
    (t u : CoreType) (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP (coreType t) (coreType u) a b = false) :
    parsedCoreOp L D R t a * parsedCoreOp L D R u b = 0 := by
  cases a <;> cases b <;> simp only [parsedCoreOp, zero_mul, mul_zero]
  apply coreOp_reject_zero L D R hR hval t u
  rwa [coreCheck_eq L D X Z projectPauli DP]

private theorem auxCheck_swap (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (t u : AuxQuestion ℓ)
    (a b : ParsedAnswer (ι → F) A PA) :
    TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr u) a b =
      TypedPredicate.check L X Z projectPauli D DP (.inr u) (.inr t) b a := by
  by_cases ht : t = u <;> by_cases hab : a = b <;>
    simp [TypedPredicate.check, ht, hab, eq_comm, Bool.and_comm, Bool.and_left_comm]

private theorem auxOp_nonzero_fits (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (t : AuxQuestion ℓ) (a : ParsedAnswer (ι → F) A PA)
    (ha : auxOp L D R hL t a ≠ 0) : TypedPredicate.fits (.inr t : QuestionType P ℓ) a = true := by
  rcases t with ⟨t, w⟩
  cases t <;> cases a <;>
    simp_all only [auxOp, parsedCoreOp, parsedReadOp, parsedHideOp, ne_eq,
      not_true_eq_false, TypedPredicate.fits]

private theorem auxCheck_self (X Z : P) (projectPauli : PA → ι → F)
    (DP : P → P → PA → PA → Bool) (t : AuxQuestion ℓ)
    (a : ParsedAnswer (ι → F) A PA)
    (ha : TypedPredicate.fits (.inr t : QuestionType P ℓ) a = true) :
    TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr t) a a = true := by
  rcases t with ⟨t, w⟩
  cases t <;> cases w <;> cases a <;>
    simp_all [TypedPredicate.check, TypedPredicate.fits, TypedPredicate.directed]

theorem auxOp_self_reject_zero (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (X Z : P) (projectPauli : PA → ι → F) (DP : P → P → PA → PA → Bool)
    (t : AuxQuestion ℓ) (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr t) a b = false) :
    auxOp L D R hL t a * auxOp L D R hL t b = 0 := by
  by_cases hab : a = b
  · subst b
    have hz : auxOp L D R hL t a = 0 := by
      by_contra hn
      have hh := auxCheck_self L D X Z projectPauli DP t a (auxOp_nonzero_fits L D R hL t a hn)
      rw [hr] at hh
      cases hh
    rw [hz, zero_mul]
  · exact (auxOp_isPVM L D R hL t).orthogonal hab

theorem auxOp_oriented_commute (hL : ∀ w, (L w).SupportedOn Finset.univ) (hR : R.IsPCC)
    (E : P → P → Bool) (X Z : P) (t u : AuxQuestion ℓ)
    (he : TypeGraph.oriented E X Z (.inr t) (.inr u) = true)
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (auxOp L D R hL t a) (auxOp L D R hL u b) := by
  rcases t with ⟨t, w⟩
  rcases u with ⟨u, v⟩
  cases t <;> cases u <;> simp only [TypeGraph.oriented, decide_eq_true_eq, Bool.false_eq_true] at he
  · exact parsedCore_core_commute L D R hR _ _ a b
  · subst v
    exact parsedCore_read_commute L D R w (hL w) a b
  · subst v
    exact parsedCore_core_commute L D R hR _ _ a b
  · rcases he with ⟨rfl, hk⟩
    exact parsedHide_read_commute L D R _ _ (by omega) (hL _) a b
  · rcases he with ⟨rfl, hk⟩
    dsimp only [auxOp]
    rw [← hk]
    exact parsedHide_next_commute L D R _ _ (hL _) a b

theorem auxOp_oriented_reject_zero (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (hR : R.IsPCC) (hval : R.value = 1) (E : P → P → Bool) (X Z : P)
    (projectPauli : PA → ι → F) (DP : P → P → PA → PA → Bool) (t u : AuxQuestion ℓ)
    (he : TypeGraph.oriented E X Z (.inr t) (.inr u) = true)
    (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr u) a b = false) :
    auxOp L D R hL t a * auxOp L D R hL u b = 0 := by
  rcases t with ⟨t, w⟩
  rcases u with ⟨u, v⟩
  cases t <;> cases u <;> simp only [TypeGraph.oriented, decide_eq_true_eq, Bool.false_eq_true] at he
  · exact parsedCore_core_reject_zero L D R hR hval X Z projectPauli DP _ _ a b hr
  · subst v
    exact parsedCore_read_reject_zero L D R X Z projectPauli DP w (hL w) a b hr
  · subst v
    exact parsedCore_core_reject_zero L D R hR hval X Z projectPauli DP _ _ a b hr
  · rcases he with ⟨rfl, hk⟩
    exact parsedHide_read_reject_zero L D R X Z projectPauli DP _ _ hk (hL _) a b hr
  · rcases he with ⟨rfl, hk⟩
    exact parsedHide_next_reject_zero L D R X Z projectPauli DP _ _ _ hk (hL _) a b hr

theorem auxOp_commute (hL : ∀ w, (L w).SupportedOn Finset.univ) (hR : R.IsPCC)
    (E : P → P → Bool) (X Z : P) (t u : AuxQuestion ℓ)
    (he : TypeGraph.Adj E X Z (.inr t) (.inr u))
    (a b : ParsedAnswer (ι → F) A PA) :
    Commute (auxOp L D R hL t a) (auxOp L D R hL u b) := by
  simp only [TypeGraph.Adj, TypeGraph.adj, Bool.or_eq_true, decide_eq_true_eq, Sum.inr.injEq] at he
  rcases he with (he | he) | he
  · subst u; exact pvm_commute (auxOp_isPVM L D R hL t) a b
  · exact auxOp_oriented_commute L D R hL hR E X Z t u he a b
  · exact (auxOp_oriented_commute L D R hL hR E X Z u t he b a).symm

theorem auxOp_reject_zero (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (hR : R.IsPCC) (hval : R.value = 1) (E : P → P → Bool) (X Z : P)
    (projectPauli : PA → ι → F) (DP : P → P → PA → PA → Bool) (t u : AuxQuestion ℓ)
    (he : TypeGraph.Adj E X Z (.inr t) (.inr u))
    (a b : ParsedAnswer (ι → F) A PA)
    (hr : TypedPredicate.check L X Z projectPauli D DP (.inr t) (.inr u) a b = false) :
    auxOp L D R hL t a * auxOp L D R hL u b = 0 := by
  have hc := auxOp_commute L D R hL hR E X Z t u he a b
  simp only [TypeGraph.Adj, TypeGraph.adj, Bool.or_eq_true, decide_eq_true_eq, Sum.inr.injEq] at he
  rcases he with (he | he) | he
  · subst u; exact auxOp_self_reject_zero L D R hL X Z projectPauli DP t a b hr
  · exact auxOp_oriented_reject_zero L D R hL hR hval E X Z projectPauli DP t u he a b hr
  · rw [hc.eq]
    apply auxOp_oriented_reject_zero L D R hL hR hval E X Z projectPauli DP u t he b a
    rwa [auxCheck_swap L D X Z projectPauli DP]

end MIPRE.Introspection.Honest
