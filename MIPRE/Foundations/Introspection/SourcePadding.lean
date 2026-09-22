/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HonestCore
import MIPRE.Foundations.CL.Embedding
import MIPRE.Foundations.CL.Detyping

/-! # Padding the original CL source game without changing its strategy

Unused seed coordinates are ignored. On every sampled padded question pair,
the pulled-back questions have one common original seed. This suffices to
preserve perfect PCC play with exactly the original Hilbert-space dimension.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F I J A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J) (L : Bool → CL.CLFun F I ℓ)
  (D : (I → F) → (I → F) → A → A → Bool)

def family (w : Bool) : CL.CLFun F J ℓ := (L w).embed e
def decider (x y : J → F) : A → A → Bool := D (CL.pull e x) (CL.pull e y)

theorem supported_embed {k : ℕ} (P : CL.CLFun F I k) (S : Finset I)
    (hP : P.SupportedOn S) : (P.embed e).SupportedOn (S.map e) := by
  induction P generalizing S with
  | zero => trivial
  | cons U M next ih =>
    refine ⟨Finset.map_subset_map.mpr hP.1, fun x => ?_⟩
    rw [← Finset.map_sdiff]
    exact ih _ _ (hP.2 _)

theorem family_supported (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) :
    (family e L w).SupportedOn univ :=
  (supported_embed e (L w) univ (hL w)).mono (Finset.subset_univ _)

theorem pull_family (w : Bool) (x : J → F) :
    CL.pull e ((family e L w).eval x) = (L w).eval (CL.pull e x) := by
  rw [family, CL.CLFun.eval_embed, CL.pull_push]

/-- A final zero stage consumes every remaining coordinate. -/
theorem lift_exact {k : ℕ} (P : CL.CLFun F J k) (S : Finset J)
    (hP : P.SupportedOn S) : (P.lift S).ExactlyOn S := by
  induction P generalizing S with
  | zero => exact ⟨Finset.Subset.refl S, fun _ => Finset.sdiff_self S⟩
  | cons U M next ih => exact ⟨hP.1, fun x => ih _ _ (hP.2 x)⟩

def fullFamily (w : Bool) : CL.CLFun F J (ℓ+1) := (family e L w).lift univ

theorem fullFamily_exactlyOn (hL : ∀ w, (L w).SupportedOn univ) (w : Bool) :
    (fullFamily e L w).ExactlyOn univ :=
  lift_exact (family e L w) univ (family_supported e L hL w)

theorem fullFamily_eval (w : Bool) (x : J → F) :
    (fullFamily e L w).eval x = (family e L w).eval x :=
  CL.CLFun.eval_lift univ _ x

theorem sourceGame_fullFamily :
    Honest.sourceGame (fullFamily e L) (decider e D) =
      Honest.sourceGame (family e L) (decider e D) := by
  have hf (w : Bool) : (fullFamily e L w).eval = (family e L w).eval :=
    funext (fullFamily_eval e L w)
  change SampledGame.game (fullFamily e L false).eval (fullFamily e L true).eval _ = _
  rw [hf, hf]

/-- Consume unused coordinates by the zero part of the existing first factor.
Unlike `fullFamily`, this construction preserves the original depth. -/
def depthFamily (w : Bool) : CL.CLFun F J ℓ :=
  (family e L w).directSum (CL.CLFun.zeroOn (univ.map e)ᶜ ℓ)

theorem depthFamily_exactlyOn (hℓ : 0 < ℓ) (hL : ∀ w, (L w).ExactlyOn univ) (w : Bool) :
    (depthFamily e L w).ExactlyOn univ := by
  have hz := CL.CLFun.zeroOn_exactlyOn (F := F) (univ.map e)ᶜ ℓ (by omega)
  have hh := ((hL w).embed e).directSum hz (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi)
  simpa [depthFamily, family] using hh

theorem depthFamily_eval (hℓ : 0 < ℓ) (hL : ∀ w, (L w).SupportedOn univ)
    (w : Bool) (x : J → F) : (depthFamily e L w).eval x = (family e L w).eval x := by
  have hz := (CL.CLFun.zeroOn_exactlyOn (F := F) (univ.map e)ᶜ ℓ (by omega)).supportedOn
  rw [depthFamily, family, (supported_embed e (L w) univ (hL w)).eval_directSum hz
    (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi), CL.CLFun.eval_zeroOn, add_zero]

theorem sourceGame_depthFamily (hℓ : 0 < ℓ) (hL : ∀ w, (L w).SupportedOn univ) :
    Honest.sourceGame (depthFamily e L) (decider e D) =
      Honest.sourceGame (family e L) (decider e D) := by
  have hf (w : Bool) : (depthFamily e L w).eval = (family e L w).eval :=
    funext (depthFamily_eval e L hℓ hL w)
  change SampledGame.game (depthFamily e L false).eval (depthFamily e L true).eval _ = _
  rw [hf, hf]

variable (R : SyncStrategy (Honest.sourceGame L D).doubled)

/-- The common source measurement rule just restricts question coordinates. -/
def strategy : SyncStrategy (Honest.sourceGame (family e L) (decider e D)).doubled where
  d := R.d
  d_pos := R.d_pos
  P :=
    { M := fun q a => R.P.M (q.1, CL.pull e q.2) a
      selfAdjoint := fun q a => R.P.selfAdjoint (q.1, CL.pull e q.2) a
      projective := fun q a => R.P.projective (q.1, CL.pull e q.2) a
      normalized := fun q => R.P.normalized (q.1, CL.pull e q.2) }

set_option backward.isDefEq.respectTransparency false in
private theorem positive_seed (q r : Bool × (J → F))
    (h : 0 < (Honest.sourceGame (family e L) (decider e D)).doubled.μ q r) :
    ∃ x : J → F, q = (false,(family e L false).eval x) ∧
      r = (true,(family e L true).eval x) := by
  have ht : q.1 = false ∧ r.1 = true := by
    by_contra hn
    simp only [Game.doubled_μ, if_neg hn] at h
    exact (lt_irrefl 0 h).elim
  have hs : 0 < SampledGame.dist (family e L false).eval (family e L true).eval q.2 r.2 := by
    simpa only [Game.doubled_μ, if_pos ht, Honest.sourceGame, SampledGame.game] using h
  rw [SampledGame.dist_eq_card, div_pos_iff_of_pos_right
    (by exact_mod_cast (Fintype.card_pos (α := J → F)))] at hs
  simp only [Nat.cast_pos, Finset.card_pos, Finset.nonempty_def, Finset.mem_filter,
    Finset.mem_univ, true_and] at hs
  obtain ⟨x,hx,hy⟩ := hs
  exact ⟨x,Prod.ext ht.1 hx.symm,Prod.ext ht.2 hy.symm⟩

theorem strategy_isPCC (hR : R.IsPCC) : (strategy e L D R).IsPCC := by
  intro q r h a b
  obtain ⟨x,rfl,rfl⟩ := positive_seed e L D q r h
  change R.P.M (false,CL.pull e ((family e L false).eval x)) a *
    R.P.M (true,CL.pull e ((family e L true).eval x)) b = _
  simp only [strategy, pull_family]
  exact (Honest.source_commute L D R hR false true (CL.pull e x) a b).eq

set_option backward.isDefEq.respectTransparency false in
theorem strategy_value (hR : R.IsPCC) (hv : R.value = 1) :
    (strategy e L D R).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro q r h a b hr
  obtain ⟨x,rfl,rfl⟩ := positive_seed e L D q r h
  have hd : D ((L false).eval (CL.pull e x)) ((L true).eval (CL.pull e x)) a b = false := by
    simpa only [Game.doubled_D, Bool.false_eq_true, and_self, ↓reduceIte,
      Honest.sourceGame, SampledGame.game, decider, pull_family] using hr
  have hz : (strategy e L D R).P.M (false,(family e L false).eval x) a *
      (strategy e L D R).P.M (true,(family e L true).eval x) b = 0 := by
    simpa only [strategy, pull_family] using
      Honest.source_reject_zero L D R hR hv (CL.pull e x) a b hd
  rw [hz, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

/-- Padding does not cost auxiliary dimension or perfect PCC value. -/
theorem exists_perfectPCC (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (Honest.sourceGame (family e L) (decider e D)).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = R.d :=
  ⟨strategy e L D R, strategy_isPCC e L D R hR, strategy_value e L D R hR hv, rfl⟩

end MIPRE.Introspection.SourcePadding
end
