/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Converge
public import MIPRE.Tailored.Sofic.AssocPrimrec

@[expose] public section

/-!
# The upper approximation is primitive recursive

`primrec_upperSeq`: the numerators `upperSeq T t` of the upper approximation of the ergodic value
are a primitive recursive function of the test and the stage — the polytope optimum over the grid
is a finite list computation (Lemma I:1105, with linear programming replaced by enumeration).
Each construction of `Stage.lean` is a composition of list operations; `List.all`, `List.any`
and `List.sum` are folds (`primrec_all`, `primrec_any`, `primrec_sum_map`), and `List.zip` is a
map over the indices (`zip_eq_range`).
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue Primrec

/-! ## Folds -/

section Folds

variable {α β : Type} [Primcodable α] [Primcodable β]

theorem primrec_all {L : α → List β} {f : α → β → Bool} (hL : Primrec L) (hf : Primrec₂ f) :
    Primrec fun a => (L a).all (f a) :=
  (list_foldr hL (const true) (Primrec.and.comp (hf.comp fst (fst.comp snd))
    (snd.comp snd)).to₂).of_eq fun a => by rw [all_eq_foldr]

theorem primrec_any {L : α → List β} {f : α → β → Bool} (hL : Primrec L) (hf : Primrec₂ f) :
    Primrec fun a => (L a).any (f a) :=
  (list_foldr hL (const false) (Primrec.or.comp (hf.comp fst (fst.comp snd))
    (snd.comp snd)).to₂).of_eq fun a => by rw [any_eq_foldr]

theorem primrec_sum_map {L : α → List β} {f : α → β → ℕ} (hL : Primrec L) (hf : Primrec₂ f) :
    Primrec fun a => ((L a).map (f a)).sum :=
  (list_foldr (list_map hL hf) (const 0) (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
    fun _ => (sum_eq_foldr _).symm

theorem primrec_sum : Primrec (List.sum : List ℕ → ℕ) :=
  (primrec_sum_map (f := fun _ (a : ℕ) => a) Primrec.id snd.to₂).of_eq fun _ => by simp

end Folds

theorem zip_eq_range {α β : Type} (l₁ : List α) (l₂ : List β) (d₁ : α) (d₂ : β) :
    l₁.zip l₂ = (List.range (min l₁.length l₂.length)).map fun i => (l₁.getD i d₁, l₂.getD i d₂) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_zip] at h1
    simp [List.getElem_zip, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (lt_of_lt_of_le h1
      (min_le_left _ _)), List.getElem?_eq_getElem (lt_of_lt_of_le h1 (min_le_right _ _))]

theorem primrec_zip {α β : Type} [Primcodable α] [Primcodable β] [Inhabited α] [Inhabited β] :
    Primrec₂ (@List.zip α β) :=
  (list_map (list_range.comp (nat_min.comp (list_length.comp fst) (list_length.comp snd)))
    (((list_getD default).comp (fst.comp fst) snd).pair
      ((list_getD default).comp (snd.comp fst) snd)).to₂).to₂.of_eq
    fun l₁ l₂ => (zip_eq_range l₁ l₂ default default).symm

/-! ## Words -/

theorem primrec_letters : Primrec letters :=
  list_flatMap list_range (list_cons.comp (snd.pair (const false))
    (list_cons.comp (snd.pair (const true)) (const []))).to₂

theorem primrec_wordsStep : Primrec₂ wordsStep :=
  (list_flatMap snd (list_map (primrec_letters.comp (fst.comp fst))
    (list_cons.comp snd (snd.comp fst)).to₂).to₂).to₂

theorem primrec_wordsLen : Primrec₂ wordsLen :=
  (nat_iterate snd (const [[]]) (primrec_wordsStep.comp (fst.comp fst) snd).to₂).to₂

theorem primrec_wordsUpTo : Primrec₂ wordsUpTo :=
  (list_flatMap (list_range.comp (succ.comp snd)) (primrec_wordsLen.comp (fst.comp fst) snd).to₂).to₂

/-- The arguments `(T, t)`. -/
abbrev TT := SubgroupTestData × ℕ

theorem primrec_stageW : Primrec fun x : TT => stageW x.1 x.2 :=
  primrec_wordsUpTo.comp (nat_add.comp (primrec_nGen.comp fst) snd) (nat_add.comp snd (const 2))

theorem primrec_stageD : Primrec fun x : TT => stageD x.1 x.2 :=
  primrec_wordsUpTo.comp (nat_add.comp (primrec_nGen.comp fst) snd) snd

theorem primrec_stagePt : Primrec fun x : TT => stagePt x.1 x.2 :=
  primrec_allBits.comp (list_length.comp primrec_stageW)

theorem primrec_stageP : Primrec fun x : TT => stageP x.1 x.2 :=
  list_length.comp primrec_stagePt

theorem primrec_stageM : Primrec fun x : TT => stageM x.1 x.2 :=
  nat_mul.comp primrec_stageP (primrec_two_pow.comp snd)

/-! ## Patterns -/

theorem primrec_extW : Primrec fun x : List Word × List Bool × Word => extW x.1 x.2.1 x.2.2 :=
  ((list_getD false).comp (fst.comp snd) (list_idxOf.comp (snd.comp snd) fst)).of_eq fun x => by
    simp only [extW, idxOf_word]

/-- `extW` with its arguments given by primitive recursive functions. -/
theorem primrec_extW' {γ : Type} [Primcodable γ] {W : γ → List Word} {p : γ → List Bool}
    {u : γ → Word} (hW : Primrec W) (hp : Primrec p) (hu : Primrec u) :
    Primrec fun c => extW (W c) (p c) (u c) :=
  primrec_extW.comp (hW.pair (hp.pair hu))

theorem primrec_litW_ext :
    Primrec fun x : (List Word × List Bool) × List Word × (ℕ × Bool) =>
      litW x.2.1 (extW x.1.1 x.1.2) x.2.2 := by
  refine (option_casesOn (list_getElem?.comp (fst.comp snd) (fst.comp (snd.comp snd))) (const false)
      (Primrec.beq.comp (primrec_extW' (fst.comp (fst.comp fst)) (snd.comp (fst.comp fst)) snd)
        (snd.comp (snd.comp (snd.comp fst)))).to₂).of_eq fun x => ?_
  unfold litW
  cases x.2.1[x.2.2.1]? <;> rfl

theorem primrec_passW_ext :
    Primrec fun x : (List Word × List Bool) × List Word × List (List (ℕ × Bool)) =>
      passW x.2.1 x.2.2 (extW x.1.1 x.1.2) := by
  have hl : Primrec₂ fun (q : ((List Word × List Bool) × List Word × List (List (ℕ × Bool))) ×
      List (ℕ × Bool)) (lit : ℕ × Bool) => litW q.1.2.1 (extW q.1.1.1 q.1.1.2) lit :=
    (primrec_litW_ext.comp ((fst.comp (fst.comp fst)).pair
      ((fst.comp (snd.comp (fst.comp fst))).pair snd))).to₂
  have hc : Primrec₂ fun (x : (List Word × List Bool) × List Word × List (List (ℕ × Bool)))
      (c : List (ℕ × Bool)) => c.all fun lit => litW x.2.1 (extW x.1.1 x.1.2) lit :=
    (primrec_all (L := fun q : ((List Word × List Bool) × List Word × List (List (ℕ × Bool))) ×
      List (ℕ × Bool) => q.2) snd hl).to₂
  exact primrec_any (snd.comp snd) hc

theorem primrec_memW : Primrec₂ memW :=
  (Primrec.nat_lt.decide.comp (list_idxOf.comp snd fst) (list_length.comp fst)).to₂.of_eq
    fun W u => by simp only [memW, idxOf_word]

theorem primrec_cancel2 : Primrec₂ cancel2 := by
  have hj : Primrec fun x : Word × ℕ => (x.1.getD x.2 (0, false)) :=
    (list_getD _).comp fst snd
  have hj1 : Primrec fun x : Word × ℕ => (x.1.getD (x.2 + 1) (0, false)) :=
    (list_getD _).comp fst (succ.comp snd)
  exact (Primrec.and.comp (Primrec.and.comp (nat_lt.decide.comp (succ.comp snd)
    (list_length.comp fst)) (Primrec.beq.comp (fst.comp hj) (fst.comp hj1)))
      (Primrec.beq.comp (snd.comp hj1) (Primrec.not.comp (snd.comp hj)))).to₂

theorem primrec_drop1 : Primrec fun x : ℕ × Word × ℕ => drop1 x.1 x.2.1 x.2.2 :=
  Primrec.and.comp (nat_lt.decide.comp (snd.comp snd) (list_length.comp (fst.comp snd)))
    (nat_le.decide.comp fst (fst.comp ((list_getD _).comp (fst.comp snd) (snd.comp snd))))

/-- The arguments `(s, W, p)` of `goodP`. -/
abbrev GArgs := ℕ × List Word × List Bool

set_option maxHeartbeats 1000000 in
theorem primrec_goodP : Primrec fun x : GArgs => goodP x.1 x.2.1 x.2.2 := by
  have hW : Primrec fun x : GArgs => x.2.1 := fst.comp snd
  have hp : Primrec fun x : GArgs => x.2.2 := snd.comp snd
  -- the local conditions, in context `((x, u), j)`
  have hloc : Primrec₂ fun (xu : GArgs × Word) (j : ℕ) =>
      (!cancel2 xu.2 j || (extW xu.1.2.1 xu.1.2.2 xu.2 ==
        extW xu.1.2.1 xu.1.2.2 (xu.2.take j ++ xu.2.drop (j + 2)))) &&
      (!drop1 xu.1.1 xu.2 j || (extW xu.1.2.1 xu.1.2.2 xu.2 ==
        extW xu.1.2.1 xu.1.2.2 (xu.2.take j ++ xu.2.drop (j + 1)))) := by
    have hx : Primrec fun q : (GArgs × Word) × ℕ => q.1.1 := fst.comp fst
    have hu : Primrec fun q : (GArgs × Word) × ℕ => q.1.2 := snd.comp fst
    have hj : Primrec fun q : (GArgs × Word) × ℕ => q.2 := snd
    have he : ∀ {w : (GArgs × Word) × ℕ → Word}, Primrec w →
        Primrec fun q => extW q.1.1.2.1 q.1.1.2.2 (w q) :=
      fun hw => primrec_extW' (hW.comp hx) (hp.comp hx) hw
    have htd : ∀ k : ℕ, Primrec fun q : (GArgs × Word) × ℕ => q.1.2.take q.2 ++ q.1.2.drop (q.2 + k) :=
      fun k => list_append.comp (list_take.comp hj hu) (list_drop.comp (nat_add.comp hj (const k)) hu)
    exact (Primrec.and.comp
      (Primrec.or.comp (Primrec.not.comp (primrec_cancel2.comp hu hj))
        (Primrec.beq.comp (he hu) (he (htd 2))))
      (Primrec.or.comp (Primrec.not.comp (primrec_drop1.comp ((fst.comp hx).pair (hu.pair hj))))
        (Primrec.beq.comp (he hu) (he (htd 1))))).to₂
  have hall1 : Primrec fun x : GArgs => x.2.1.all fun u =>
      (List.range u.length).all fun j =>
        (!cancel2 u j || (extW x.2.1 x.2.2 u == extW x.2.1 x.2.2 (u.take j ++ u.drop (j + 2)))) &&
        (!drop1 x.1 u j || (extW x.2.1 x.2.2 u == extW x.2.1 x.2.2 (u.take j ++ u.drop (j + 1)))) :=
    primrec_all hW (primrec_all (list_range.comp (list_length.comp snd)) hloc).to₂
  -- the closure condition, in context `((x, u), v)`
  have hmul : Primrec₂ fun (xu : GArgs × Word) (v : Word) =>
      !(memW xu.1.2.1 (xu.2 ++ invW v) && extW xu.1.2.1 xu.1.2.2 xu.2 &&
        extW xu.1.2.1 xu.1.2.2 v) || extW xu.1.2.1 xu.1.2.2 (xu.2 ++ invW v) := by
    have hx : Primrec fun q : (GArgs × Word) × Word => q.1.1 := fst.comp fst
    have hu : Primrec fun q : (GArgs × Word) × Word => q.1.2 := snd.comp fst
    have hv : Primrec fun q : (GArgs × Word) × Word => q.2 := snd
    have he : ∀ {w : (GArgs × Word) × Word → Word}, Primrec w →
        Primrec fun q => extW q.1.1.2.1 q.1.1.2.2 (w q) :=
      fun hw => primrec_extW' (hW.comp hx) (hp.comp hx) hw
    have huv := list_append.comp hu (primrec_invW.comp hv)
    exact (Primrec.or.comp (Primrec.not.comp (Primrec.and.comp (Primrec.and.comp
      (primrec_memW.comp (hW.comp hx) huv) (he hu)) (he hv))) (he huv)).to₂
  have hall2 : Primrec fun x : GArgs => x.2.1.all fun u => x.2.1.all fun v =>
      !(memW x.2.1 (u ++ invW v) && extW x.2.1 x.2.2 u && extW x.2.1 x.2.2 v) ||
        extW x.2.1 x.2.2 (u ++ invW v) :=
    primrec_all hW (primrec_all (hW.comp fst) hmul).to₂
  exact Primrec.and.comp (Primrec.and.comp (primrec_extW' hW hp (const [])) hall1) hall2

/-! ## Grid points -/

theorem primrec_vecsStep : Primrec₂ vecsStep :=
  (list_flatMap snd (list_map (list_range.comp (succ.comp (fst.comp fst)))
    (list_cons.comp snd (snd.comp fst)).to₂).to₂).to₂

theorem primrec_allVecs : Primrec₂ allVecs :=
  (nat_iterate fst (const [[]]) (primrec_vecsStep.comp (snd.comp fst) snd).to₂).to₂

/-- `cntR` with its arguments given by primitive recursive functions. -/
theorem primrec_cntR {γ : Type} [Primcodable γ] {n : γ → List ℕ} {Pt : γ → List (List Bool)}
    {f : γ → List Bool → Bool} (hn : Primrec n) (hPt : Primrec Pt) (hf : Primrec₂ f) :
    Primrec fun c => cntR (n c) (Pt c) (f c) :=
  primrec_sum_map (primrec_zip.comp hn hPt)
    (Primrec.ite (Primrec.eq.comp (hf.comp fst (snd.comp snd)) (const true))
      (fst.comp snd) (const 0)).to₂

theorem primrec_ndist : Primrec₂ ndist :=
  (nat_add.comp (nat_sub.comp fst snd) (nat_sub.comp snd fst)).to₂

theorem listBool_beq (a b : List Bool) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

attribute [local irreducible] stageW stageD stagePt stageP stageM

/-- The arguments `((T, t), g, n)` of `invErr`. -/
abbrev IArgs := TT × Letter × List ℕ

set_option maxHeartbeats 300000 in
theorem primrec_invErr : Primrec fun x : IArgs => invErr x.1.1 x.1.2 x.2.1 x.2.2 := by
  -- in context `(x, q)`, then `((x, q), p)`, then `(((x, q), p), u)`
  have hx : Primrec fun c : (IArgs × List Bool) × List Bool => c.1.1 := fst.comp fst
  have hq : Primrec fun c : (IArgs × List Bool) × List Bool => c.1.2 := snd.comp fst
  have hp : Primrec fun c : (IArgs × List Bool) × List Bool => c.2 := snd
  have hD : Primrec fun c : (IArgs × List Bool) × List Bool => stageD c.1.1.1.1 c.1.1.1.2 :=
    primrec_stageD.comp (fst.comp hx)
  have hWc : Primrec fun c : ((IArgs × List Bool) × List Bool) × Word =>
      stageW c.1.1.1.1.1 c.1.1.1.1.2 :=
    primrec_stageW.comp (fst.comp (hx.comp fst))
  have hpc : Primrec fun c : ((IArgs × List Bool) × List Bool) × Word => c.1.2 := hp.comp fst
  have hu : Primrec fun c : ((IArgs × List Bool) × List Bool) × Word => c.2 := snd
  have hg : Primrec fun c : ((IArgs × List Bool) × List Bool) × Word => c.1.1.1.2.1 :=
    fst.comp (snd.comp (hx.comp fst))
  have hf1 : Primrec₂ fun (xq : IArgs × List Bool) (p : List Bool) =>
      decide ((stageD xq.1.1.1 xq.1.1.2).map (extW (stageW xq.1.1.1 xq.1.1.2) p) = xq.2) :=
    (Primrec.eq.decide.comp (list_map hD (primrec_extW' hWc hpc hu).to₂) hq).to₂
  have hcj : Primrec fun c : ((IArgs × List Bool) × List Bool) × Word =>
      invW [c.1.1.1.2.1] ++ c.2 ++ [c.1.1.1.2.1] :=
    list_append.comp (list_append.comp (primrec_invW.comp (list_cons.comp hg (const []))) hu)
      (list_cons.comp hg (const []))
  have hf2 : Primrec₂ fun (xq : IArgs × List Bool) (p : List Bool) =>
      decide ((stageD xq.1.1.1 xq.1.1.2).map (conjW xq.1.2.1 (extW (stageW xq.1.1.1 xq.1.1.2) p)) =
        xq.2) :=
    (Primrec.eq.decide.comp (list_map hD (primrec_extW' hWc hpc hcj).to₂) hq).to₂
  have hn : Primrec fun c : IArgs × List Bool => c.1.2.2 := snd.comp (snd.comp fst)
  have hPt : Primrec fun c : IArgs × List Bool => stagePt c.1.1.1 c.1.1.2 :=
    primrec_stagePt.comp (fst.comp fst)
  refine (primrec_sum_map (primrec_allBits.comp (list_length.comp (primrec_stageD.comp fst)))
    (primrec_ndist.comp (primrec_cntR hn hPt hf1) (primrec_cntR hn hPt hf2)).to₂).of_eq
      fun x => ?_
  simp only [invErr, listBool_beq]

attribute [local irreducible] invErr goodP

/-- The arguments `((T, t), n)`. -/
abbrev NArgs := TT × List ℕ

theorem primrecRel_good : PrimrecRel fun (y : ℕ × List Bool) (x : NArgs) =>
    ¬0 < y.1 ∨ goodP x.1.1.nGen (stageW x.1.1 x.1.2) y.2 = true :=
  PrimrecPred.or (PrimrecPred.not (nat_lt.comp (const 0) (fst.comp fst)))
    (Primrec.eq.comp (primrec_goodP.comp ((primrec_nGen.comp (fst.comp (fst.comp snd))).pair
      ((primrec_stageW.comp (fst.comp snd)).pair (snd.comp fst)))) (const true))

theorem primrecPred_feas2 : PrimrecPred fun x : NArgs => ∀ y ∈ x.2.zip (stagePt x.1.1 x.1.2),
    ¬0 < y.1 ∨ goodP x.1.1.nGen (stageW x.1.1 x.1.2) y.2 = true :=
  (PrimrecRel.forall_mem_list primrecRel_good).comp
    (primrec_zip.comp snd (primrec_stagePt.comp fst)) Primrec.id

theorem primrecRel_inv : PrimrecRel fun (g : Letter) (x : NArgs) =>
    invErr x.1.1 x.1.2 g x.2 ≤ 4 * stageP x.1.1 x.1.2 := by
  have h1 : Primrec fun a : Letter × NArgs => invErr a.2.1.1 a.2.1.2 a.1 a.2.2 :=
    primrec_invErr.comp ((fst.comp snd).pair (fst.pair (snd.comp snd)))
  have h2 : Primrec fun a : Letter × NArgs => 4 * stageP a.2.1.1 a.2.1.2 :=
    nat_mul.comp (const 4) (primrec_stageP.comp (fst.comp snd))
  exact nat_le.comp h1 h2

theorem primrecPred_feas3 : PrimrecPred fun x : NArgs => ∀ g ∈ letters x.1.1.nGen,
    invErr x.1.1 x.1.2 g x.2 ≤ 4 * stageP x.1.1 x.1.2 :=
  (PrimrecRel.forall_mem_list primrecRel_inv).comp
    (primrec_letters.comp (primrec_nGen.comp (fst.comp fst))) Primrec.id

theorem primrecPred_feas1 : PrimrecPred fun x : NArgs => x.2.sum = stageM x.1.1 x.1.2 :=
  Primrec.eq.comp (primrec_sum.comp snd) (primrec_stageM.comp fst)

theorem primrecPred_feasible : PrimrecPred fun x : NArgs => Feasible x.1.1 x.1.2 x.2 := by
  refine (PrimrecPred.and primrecPred_feas1 (PrimrecPred.and primrecPred_feas2
    primrecPred_feas3)).of_eq fun x => ?_
  unfold Feasible
  simp only [Nat.not_lt, Nat.le_zero, imp_iff_not_or]

theorem primrec_numG : Primrec fun x : NArgs => numG x.1.1 x.1.2 x.2 := by
  have hc : Primrec₂ fun (x : NArgs) (ch : ℕ × List Word × List (List (ℕ × Bool))) =>
      ch.1 * cntR x.2 (stagePt x.1.1 x.1.2) fun p =>
        passW ch.2.1 ch.2.2 (extW (stageW x.1.1 x.1.2) p) := by
    have hw : Primrec fun q : NArgs × (ℕ × List Word × List (List (ℕ × Bool))) => q.2.1 :=
      fst.comp snd
    have hn : Primrec fun q : NArgs × (ℕ × List Word × List (List (ℕ × Bool))) => q.1.2 :=
      snd.comp fst
    have hPt : Primrec fun q : NArgs × (ℕ × List Word × List (List (ℕ × Bool))) =>
        stagePt q.1.1.1 q.1.1.2 := primrec_stagePt.comp (fst.comp fst)
    refine (nat_mul.comp hw (primrec_cntR (f := fun q p =>
      passW q.2.2.1 q.2.2.2 (extW (stageW q.1.1.1 q.1.1.2) p)) hn hPt ?_)).to₂
    exact (primrec_passW_ext.comp (((primrec_stageW.comp (fst.comp (fst.comp fst))).pair snd).pair
      ((fst.comp (snd.comp (snd.comp fst))).pair (snd.comp (snd.comp (snd.comp fst)))))).to₂
  exact primrec_sum_map (primrec_challenges.comp (fst.comp fst)) hc

theorem primrec_maxNum : Primrec fun x : TT => maxNum x.1 x.2 := by
  have hfilt : Primrec fun x : TT =>
      (allVecs (stageP x.1 x.2) (stageM x.1 x.2)).filter fun n => decide (Feasible x.1 x.2 n) :=
    (PrimrecRel.listFilter (R := fun (n : List ℕ) (x : TT) => Feasible x.1 x.2 n)
      (primrecPred_feasible.comp (snd.pair fst))).comp
      (primrec_allVecs.comp primrec_stageP primrec_stageM) Primrec.id
  exact list_foldr (list_map hfilt (primrec_numG.comp (fst.pair snd)).to₂) (const 0)
    (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂

theorem primrecPred_covers : PrimrecPred fun x : TT => Covers x.1 x.2 := by
  have hR : PrimrecRel fun (k : Word) (x : TT) => k ∈ stageW x.1 x.2 :=
    (Primrec.eq.comp (primrec_memW.comp (primrec_stageW.comp snd) fst) (const true)).of_eq
      fun _ => memW_iff
  have hR' : PrimrecRel fun (ch : ℕ × List Word × List (List (ℕ × Bool))) (x : TT) =>
      ∀ k ∈ ch.2.1, k ∈ stageW x.1 x.2 :=
    (PrimrecRel.forall_mem_list hR).comp (fst.comp (snd.comp fst)) snd
  exact (PrimrecRel.forall_mem_list hR').comp (primrec_challenges.comp fst) Primrec.id

theorem primrec_ceilDiv : Primrec₂ ceilDiv :=
  (nat_div.comp (nat_sub.comp (nat_add.comp fst snd) (const 1)) snd).to₂

/-- **The upper approximation is primitive recursive.** -/
theorem primrec_upperSeq : Primrec₂ upperSeq := by
  have hW := primrec_totalWeight.comp (fst : Primrec fun x : TT => x.1)
  exact (Primrec.ite primrecPred_covers (primrec_ceilDiv.comp (nat_mul.comp
    (primrec_two_pow.comp snd) (nat_add.comp primrec_maxNum (nat_mul.comp (nat_mul.comp (const 2)
      primrec_stageP) hW))) (nat_mul.comp primrec_stageM hW)) (primrec_two_pow.comp snd)).to₂

end MIPRE.Tailored.Sofic.Measure

end
