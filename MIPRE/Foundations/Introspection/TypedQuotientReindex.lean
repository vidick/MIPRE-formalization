/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AuxiliaryQuotientReindex
public import MIPRE.Foundations.Introspection.TypedQuotientGame
public import MIPRE.Foundations.Introspection.PrefixGuardGame

@[expose] public section

/-! # Exact game and PCC transport of quotient answers between coordinate types

The strategy transport of the soundness direction, `reindexedStrategy`, is stated in a bipartite
model (Phase 4 of `planning/mipco-track.md`): it relabels the answers of a projective strategy of
the quotient game along the answer equivalence (`BipartiteModel.ProjStrat.relabel`), in the same
model, and keeps its value (`reindexedStrategy_value`). Each of its effects is the original effect
at the pulled-back answer (`reindexedStrategy_PA_op`, `reindexedStrategy_PB_op`), through
`POVMIn.map_equiv_op` and `BipartiteModel.ProjStrat.relabel_PA_op`/`relabel_PB_op`.
-/

noncomputable section

namespace MIPRE

/-! ## Effects of a relabelled strategy

These belong with `POVMIn.map` (`MIPRE/Foundations/Measurement.lean`) and `ProjStrat.relabel`
(`MIPRE/Foundations/ModelStrategy.lean`), and are here until those modules are next rebuilt. -/

/-- **Relabelling a POVM along an equivalence of its outcomes**: the effect of an outcome is the
original effect of its preimage. -/
theorem POVMIn.map_equiv_op {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] (e : X ≃ Y)
    (M : POVMIn X R) (y : Y) : (M.map e).op y = M.op (e.symm y) := by
  have h : Finset.univ.filter (fun x => e x = y) = {e.symm y} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Equiv.eq_symm_apply]
  rw [POVMIn.map_op, h, Finset.sum_singleton]

namespace BipartiteModel.ProjStrat

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {X Y A B X' Y' A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B'] [DecidableEq A'] [DecidableEq B']
  {G : Game X Y A B}

/-- A relabelled first-player effect is the original effect at the relabelled question and
answer. -/
theorem relabel_PA_op (S : M.ProjStrat G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B) (x' : X') (a' : A') :
    ((S.relabel G' eX eY eA eB).PA x').op a' = (S.PA (eX x')).op (eA a') :=
  POVMIn.map_equiv_op eA.symm (S.PA (eX x')) a'

/-- A relabelled second-player effect is the original effect at the relabelled question and
answer. -/
theorem relabel_PB_op (S : M.ProjStrat G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B) (y' : Y') (b' : B') :
    ((S.relabel G' eX eY eA eB).PB y').op b' = (S.PB (eY y')).op (eB b') :=
  POVMIn.map_equiv_op eB.symm (S.PB (eY y')) b'

end BipartiteModel.ProjStrat

end MIPRE

namespace MIPRE.Introspection.AuxiliaryQuotient
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

theorem prefix_attained_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (∃ x, ((P.reindex e).truncate k).eval x =
      (P.reindex e).outputPrefix k (reindexEquiv e y)) ↔
      ∃ x, (P.truncate k).eval x = P.outputPrefix k y := by
  rw [CLFun.truncate_reindex, outputPrefix_reindex]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨(reindexEquiv e).symm x, ?_⟩
    rw [CLFun.eval_reindex'] at hx
    exact (reindexEquiv e).injective hx
  · rintro ⟨x,hx⟩
    exact ⟨reindexEquiv e x, by rw [CLFun.eval_reindex, hx]⟩

theorem prefixGuard_reindex (e : ι ≃ κ) (L : Bool → CLFun F ι ℓ)
    (t : QuestionType PT ℓ) (a : ParsedAnswer (ι → F) A PA) :
    PrefixGuard.holds (fun w => (L w).reindex e) t (answerEquiv e a) ↔
      PrefixGuard.holds L t a := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> rfl
  · cases t <;> cases a <;> try rfl
    all_goals exact prefix_attained_reindex e _ _ _

variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)

abbrev reindexedGame := game E X Z P (fun w => (L w).reindex e)
  (fun a => reindexEquiv e (project a))
  (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y)) DP

theorem reindexedGame_D (q r : CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a b : ParsedAnswer (ι → F) A PA) :
    (reindexedGame e E X Z P L project D DP).D q r (answerEquiv e a) (answerEquiv e b) =
      (game E X Z P L project D DP).D q r a b :=
  check_reindex e L X Z project D _ _ _ _ _

/-- Return to the original coordinate type by an exact answer relabeling. -/
abbrev originalStrategy (S : TensorProductStrategy (reindexedGame e E X Z P L project D DP)) :
    TensorProductStrategy (game E X Z P L project D DP) :=
  S.relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e) (answerEquiv e)

theorem originalStrategy_value
    (S : TensorProductStrategy (reindexedGame e E X Z P L project D DP)) :
    (originalStrategy e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e) (answerEquiv e) (fun _ _ => rfl)
  intro q r a b
  exact (reindexedGame_D e E X Z P L project D DP q r a b).symm

theorem reindexedGame_quantumValue :
    quantumValue (reindexedGame e E X Z P L project D DP) =
      quantumValue (game E X Z P L project D DP) := by
  symm
  apply quantumValue_eq_of_equiv _ _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e) (answerEquiv e)
    (fun _ _ => rfl)
  intro q r a b
  exact (reindexedGame_D e E X Z P L project D DP q r a b).symm

section Model

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {Ψ : BipartiteModel 𝒞 𝒜 ℬ}

/-- Carry a projective strategy to the concrete coordinate numbering, in the same model: its
answers relabelled along the answer equivalence. -/
abbrev reindexedStrategy (S : Ψ.ProjStrat (game E X Z P L project D DP)) :
    Ψ.ProjStrat (reindexedGame e E X Z P L project D DP) :=
  S.relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e).symm (answerEquiv e).symm

theorem reindexedStrategy_value (S : Ψ.ProjStrat (game E X Z P L project D DP)) :
    (reindexedStrategy e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e).symm (answerEquiv e).symm
    (fun _ _ => rfl)
  intro q r a b
  obtain ⟨a,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective a
  obtain ⟨b,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective b
  simpa only [Equiv.refl_apply, Equiv.symm_apply_apply] using
    reindexedGame_D e E X Z P L project D DP q r a b

/-- A reindexed first-player effect is the original effect at the pulled-back answer. -/
theorem reindexedStrategy_PA_op (S : Ψ.ProjStrat (game E X Z P L project D DP))
    (q : CL.Detyping.Question (QuestionType PT ℓ) Q) (a : ParsedAnswer (κ → F) A PA) :
    ((reindexedStrategy e E X Z P L project D DP S).PA q).op a =
      (S.PA q).op ((answerEquiv e).symm a) :=
  S.relabel_PA_op _ _ _ _ _ q a

/-- A reindexed second-player effect is the original effect at the pulled-back answer. -/
theorem reindexedStrategy_PB_op (S : Ψ.ProjStrat (game E X Z P L project D DP))
    (q : CL.Detyping.Question (QuestionType PT ℓ) Q) (a : ParsedAnswer (κ → F) A PA) :
    ((reindexedStrategy e E X Z P L project D DP S).PB q).op a =
      (S.PB q).op ((answerEquiv e).symm a) :=
  S.relabel_PB_op _ _ _ _ _ q a

end Model

variable [DecidableEq A] [DecidableEq PA]

abbrev originalPCC (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    SyncStrategy (game E X Z P L project D DP).doubled :=
  S.relabel _ (Equiv.refl _) (answerEquiv e)

theorem originalPCC_isPCC
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) (hS : S.IsPCC) :
    (originalPCC e E X Z P L project D DP S).IsPCC :=
  SyncStrategy.isPCC_relabel hS _ _ _ (fun _ _ => rfl)

theorem originalPCC_value
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    (originalPCC e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (answerEquiv e) (fun _ _ => rfl)
  intro q r a b
  simp only [Game.doubled_D, Equiv.refl_apply, reindexedGame_D]

@[simp] theorem originalPCC_dimension
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    (originalPCC e E X Z P L project D DP S).d = S.d := rfl

theorem originalPCC_prefixGuard
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 →
      PrefixGuard.holds (fun w => (L w).reindex e) q.2.1 a)
    (q : Bool × CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a : ParsedAnswer (ι → F) A PA)
    (ha : (originalPCC e E X Z P L project D DP S).P.M q a ≠ 0) :
    PrefixGuard.holds L q.2.1 a :=
  (prefixGuard_reindex e L q.2.1 a).mp (hS q (answerEquiv e a) ha)

/-- Carry the same honest operators to the concrete coordinate numbering. -/
abbrev reindexedPCC (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    SyncStrategy (reindexedGame e E X Z P L project D DP).doubled :=
  S.relabel _ (Equiv.refl _) (answerEquiv e).symm

theorem reindexedPCC_isPCC (S : SyncStrategy (game E X Z P L project D DP).doubled)
    (hS : S.IsPCC) : (reindexedPCC e E X Z P L project D DP S).IsPCC :=
  SyncStrategy.isPCC_relabel hS _ _ _ (fun _ _ => rfl)

theorem reindexedPCC_value (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    (reindexedPCC e E X Z P L project D DP S).value = S.value := by
  apply S.value_relabel _ (Equiv.refl _) (answerEquiv e).symm (fun _ _ => rfl)
  intro q r a b
  obtain ⟨a,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective a
  obtain ⟨b,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective b
  simp only [Game.doubled_D, Equiv.refl_apply, Equiv.symm_apply_apply, reindexedGame_D]

@[simp] theorem reindexedPCC_dimension
    (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    (reindexedPCC e E X Z P L project D DP S).d = S.d := rfl

set_option backward.isDefEq.respectTransparency false in
theorem reindexedPCC_prefixGuard (S : SyncStrategy (game E X Z P L project D DP).doubled)
    (hS : ∀ q a, S.P.M q a ≠ 0 → PrefixGuard.holds L q.2.1 a)
    (q : Bool × CL.Detyping.Question (QuestionType PT ℓ) Q)
    (a : ParsedAnswer (κ → F) A PA)
    (ha : (reindexedPCC e E X Z P L project D DP S).P.M q a ≠ 0) :
    PrefixGuard.holds (fun w => (L w).reindex e) q.2.1 a := by
  obtain ⟨a,rfl⟩ := (answerEquiv (F := F) (A := A) (PA := PA) e).surjective a
  apply (prefixGuard_reindex e L q.2.1 a).mpr
  apply hS q a
  simpa only [reindexedPCC, SyncStrategy.relabel_P_M, Equiv.refl_apply,
    Equiv.symm_apply_apply, SyncStrategy.relabel_d] using ha

end MIPRE.Introspection.AuxiliaryQuotient
end

end
