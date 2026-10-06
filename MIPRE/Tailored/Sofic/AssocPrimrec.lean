/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Assoc
public import MIPRE.Tailored.Data.Convert

@[expose] public section

/-!
# The associated test is primitive recursive

`primrec_assocTest`: the map from a tailored game description to the description of its
associated subgroup test (`assocTest`, Definition I:2086) is primitive recursive, so it composes
with the halting reduction. Each of its constructions is a composition of list operations with a
`Primrec` lemma in Mathlib; three are rewritten first into a form those lemmas cover:
`allBits` as an iterate (`allBits_eq_iterate`), `List.dedup` as a fold (`dedup_eq_foldr`), and the
enumeration of the fixed literals by `List.range` (`zipIdx_map_eq`).
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue TailoredGameData

/-! ## Rewritings -/

/-- One step of `allBits`. -/
def allBitsStep (acc : List (List Bool)) : List (List Bool) :=
  acc.flatMap fun r => [false :: r, true :: r]

theorem allBits_eq_iterate (n : ℕ) : allBits n = allBitsStep^[n] [[]] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- Deduplication as a fold: keep an element unless it occurs later. -/
def dedupStep {α : Type*} [DecidableEq α] (a : α) (acc : List α) : List α :=
  if acc.idxOf a < acc.length then acc else a :: acc

theorem dedup_eq_foldr {α : Type*} [DecidableEq α] (l : List α) :
    l.dedup = l.foldr dedupStep [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ← ih, dedupStep]
    by_cases h : a ∈ l
    · rw [List.dedup_cons_of_mem h, if_pos (List.idxOf_lt_length_iff.2 (List.mem_dedup.2 h))]
    · rw [List.dedup_cons_of_notMem h,
        if_neg (fun h' => h (List.mem_dedup.1 (List.idxOf_lt_length_iff.1 h')))]

theorem zipIdx_map_eq {α : Type*} (l : List (α × Bool)) (d : α × Bool) :
    l.zipIdx.map (fun p => (p.2, p.1.2)) =
      (List.range l.length).map fun i => (i, (l.getD i d).2) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_zipIdx] at h1
    simp [List.getElem_zipIdx, List.getD, List.getElem?_eq_getElem h1]

theorem filter_eq_filterMap {α : Type*} (p : α → Bool) (l : List α) :
    l.filter p = l.filterMap fun a => if p a then some a else none := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-! ## Primitive recursion -/

section Primrec

open Primrec

/-- The arguments `(g, x, y)` of the per-pair constructions. -/
abbrev Q := TailoredGameData × ℕ × ℕ

theorem primrec_ansLen : Primrec fun g : TailoredGameData => g.ansLen :=
  primrec_ansLenL.of_eq fun g => g.ansLenL_eq

theorem primrec_genW : Primrec genW :=
  (list_cons.comp (Primrec.id.pair (const false)) (const [])).of_eq fun _ => rfl

theorem primrec_invW : Primrec invW :=
  (list_reverse.comp (list_map Primrec.id
    ((fst.comp snd).pair (Primrec.not.comp (snd.comp snd))).to₂)).of_eq fun _ => rfl

theorem primrec_commW : Primrec₂ commW :=
  (list_append.comp (list_append.comp (list_append.comp fst snd) (primrec_invW.comp fst))
    (primrec_invW.comp snd)).to₂.of_eq fun _ _ => rfl

theorem primrec_wJ : Primrec fun _ : Q => wJ := const _

/-- `genX`, on `(g, x, i)`. -/
theorem primrec_genX : Primrec fun q : Q => genX q.1 q.2.1 q.2.2 :=
  (nat_add.comp (nat_add.comp (const 1) (nat_mul.comp (fst.comp snd)
    (primrec_ansLen.comp fst))) (snd.comp snd)).of_eq fun _ => rfl

theorem primrec_wX : Primrec fun q : Q => wX q.1 q.2.1 q.2.2 :=
  primrec_genW.comp primrec_genX

/-- `wX g x` applied to `i`, with `(g, x)` in context. -/
theorem primrec_wX₂ : Primrec₂ fun (q : TailoredGameData × ℕ) (i : ℕ) => wX q.1 q.2 i :=
  (primrec_wX.comp ((fst.comp fst).pair ((snd.comp fst).pair snd))).to₂

theorem primrec_varsAt : Primrec₂ fun (g : TailoredGameData) (x : ℕ) => varsAt g x :=
  (list_map (list_range.comp primrec_lenAt) primrec_wX₂).to₂.of_eq fun _ _ => rfl

/-- `g` of the arguments. -/
theorem pg : Primrec fun q : Q => q.1 := fst
/-- `x` of the arguments. -/
theorem px : Primrec fun q : Q => q.2.1 := fst.comp snd
/-- `y` of the arguments. -/
theorem py : Primrec fun q : Q => q.2.2 := snd.comp snd

theorem primrec_varsX : Primrec fun q : Q => varsAt q.1 q.2.1 := primrec_varsAt.comp pg px
theorem primrec_varsY : Primrec fun q : Q => varsAt q.1 q.2.2 := primrec_varsAt.comp pg py

set_option maxHeartbeats 1000000 in
theorem primrec_fixedLits : Primrec fun q : Q => fixedLits q.1 q.2.1 q.2.2 := by
  have hV := list_append.comp primrec_varsX primrec_varsY
  have h1 : Primrec fun q : Q => (varsAt q.1 q.2.1 ++ varsAt q.1 q.2.2).map
      (fun X => (commW wJ X, true)) :=
    list_map hV ((primrec_commW.comp (const wJ) snd).pair (const true)).to₂
  have h2 : Primrec fun q : Q => (varsAt q.1 q.2.1 ++ varsAt q.1 q.2.2).map
      (fun X => (X ++ X, true)) :=
    list_map hV ((list_append.comp snd snd).pair (const true)).to₂
  have hsq : ∀ v : Q → ℕ, Primrec v → Primrec fun q : Q =>
      (varsAt q.1 (v q)).flatMap (fun X => (varsAt q.1 (v q)).map fun X' => (commW X X', true)) :=
    fun v hv => list_flatMap (primrec_varsAt.comp pg hv)
      (list_map (primrec_varsAt.comp (fst.comp fst) (hv.comp fst))
        ((primrec_commW.comp (snd.comp fst) snd).pair (const true)).to₂).to₂
  exact (list_append.comp (list_append.comp (list_append.comp (list_append.comp
    (const [(wJ, false), (wJ ++ wJ, true)]) h1) h2) (hsq _ px)) (hsq _ py)).of_eq fun _ => rfl

theorem primrec_readVars : Primrec fun q : Q => readVars q.1 q.2.1 q.2.2 :=
  (list_append.comp (list_map (list_range.comp (primrec_lenRAt.comp pg px))
      (primrec_wX₂.comp (pg.pair px |>.comp fst) snd).to₂)
    (list_map (list_range.comp (primrec_lenRAt.comp pg py))
      (primrec_wX₂.comp (pg.pair py |>.comp fst) snd).to₂)).of_eq fun _ => rfl

theorem primrec_readWords : Primrec fun q : Q => readWords q.1 q.2.1 q.2.2 :=
  (list_flatMap primrec_readVars (list_cons.comp snd (list_cons.comp
    (list_append.comp (const wJ) snd) (const []))).to₂).of_eq fun _ => rfl

theorem primrec_consAt : Primrec fun q : Q => consAt q.1 q.2.1 q.2.2 := by
  have hp : PrimrecPred fun p : Q × (ℕ × ℕ × List Bool × List Bool) =>
      p.2.1 = p.1.2.1 ∧ p.2.2.1 = p.1.2.2 :=
    PrimrecPred.and (Primrec.eq.comp (fst.comp snd) (px.comp fst))
      (Primrec.eq.comp (fst.comp (snd.comp snd)) (py.comp fst))
  refine (listFilterMap (primrec_cons.comp pg)
    (Primrec.ite hp (option_some.comp snd) (const none)).to₂).of_eq fun q => ?_
  rw [consAt, filter_eq_filterMap]
  congr 1
  funext e
  by_cases h : e.1 = q.2.1 ∧ e.2.1 = q.2.2 <;> simp [h]

/-- `(g, x, y)` of a pair whose first component is the arguments. -/
abbrev Q₂ (β : Type) := Q × β

set_option maxHeartbeats 1000000 in
theorem primrec_consWord : Primrec₂ fun (q : Q) (c : List Bool) => consWord q.1 q.2.1 q.2.2 c := by
  have hlx : Primrec fun p : Q × List Bool => lenAt p.1.1 p.1.2.1 :=
    primrec_lenAt.comp (pg.comp fst) (px.comp fst)
  have hly : Primrec fun p : Q × List Bool => lenAt p.1.1 p.1.2.2 :=
    primrec_lenAt.comp (pg.comp fst) (py.comp fst)
  have hlen : PrimrecPred fun p : Q × List Bool =>
      p.2.length = lenAt p.1.1 p.1.2.1 + lenAt p.1.1 p.1.2.2 + 1 :=
    Primrec.eq.comp (list_length.comp snd) (succ.comp (nat_add.comp hlx hly))
  have hbJ : PrimrecPred fun p : Q × List Bool =>
      p.2.getD (lenAt p.1.1 p.1.2.1 + lenAt p.1.1 p.1.2.2) false = true :=
    Primrec.eq.comp ((list_getD false).comp snd (nat_add.comp hlx hly)) (const true)
  have hJ : Primrec fun p : Q × List Bool =>
      if p.2.getD (lenAt p.1.1 p.1.2.1 + lenAt p.1.1 p.1.2.2) false = true then wJ else [] :=
    Primrec.ite hbJ (const wJ) (const [])
  -- the selected variables at `x`, then at `y`
  have hsel : ∀ (v : Q × List Bool → ℕ) (off : Q × List Bool → ℕ), Primrec v → Primrec off →
      Primrec fun p : Q × List Bool => ((List.range (lenAt p.1.1 (v p))).filterMap fun i =>
        if p.2.getD (off p + i) false = true then some i else none).flatMap (wX p.1.1 (v p)) :=
    fun v off hv hoff => list_flatMap (listFilterMap (list_range.comp (primrec_lenAt.comp
      (pg.comp fst) hv)) (Primrec.ite (Primrec.eq.comp ((list_getD false).comp (snd.comp fst)
        (nat_add.comp (hoff.comp fst) snd)) (const true)) (option_some.comp snd)
          (const none)).to₂) (primrec_wX₂.comp ((pg.comp fst).comp fst |>.pair (hv.comp fst))
            snd).to₂
  have hX := hsel (fun p => p.1.2.1) (fun _ => 0) (px.comp fst) (const 0)
  have hY := hsel (fun p => p.1.2.2) (fun p => lenAt p.1.1 p.1.2.1) (py.comp fst) hlx
  refine (Primrec.ite hlen (list_append.comp (list_append.comp hJ hX) hY)
    (const wJ)).to₂.of_eq fun q c => ?_
  simp only [consWord, filter_eq_filterMap, zero_add]

theorem primrec_dedupStep {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec₂ (dedupStep (α := α)) := by
  have h : PrimrecPred fun p : α × List α => p.2.idxOf p.1 < p.2.length :=
    Primrec.nat_lt.comp (list_idxOf.comp fst snd) (list_length.comp snd)
  exact (Primrec.ite h snd (list_cons.comp fst snd)).to₂

/-- `List.idxOf` on words, with the structural `BEq` of lists, is the one with the `BEq` of
decidable equality, which Mathlib's `Primrec.list_idxOf` is stated for. -/
theorem idxOf_word (l : List Word) (w : Word) :
    l.idxOf w = @List.idxOf _ instBEqOfDecidableEq w l := by
  unfold List.idxOf
  congr 1
  funext v
  by_cases h : v = w <;> simp [h]

theorem primrec_consWords : Primrec fun q : Q => consWords q.1 q.2.1 q.2.2 := by
  have hmap : Primrec fun q : Q => (consAt q.1 q.2.1 q.2.2).map fun e =>
      consWord q.1 q.2.1 q.2.2 e.2.2.2 :=
    list_map primrec_consAt (primrec_consWord.comp fst (snd.comp (snd.comp (snd.comp snd)))).to₂
  have hstep : Primrec₂ fun (_ : Q) (p : Word × List Word) => dedupStep p.1 p.2 :=
    ((primrec_dedupStep (α := Word)).comp fst snd).comp₂ (Primrec₂.right)
  refine (list_foldr hmap (const []) hstep).of_eq fun q => ?_
  rw [consWords, dedup_eq_foldr]

theorem primrec_words : Primrec fun q : Q => words q.1 q.2.1 q.2.2 :=
  (list_append.comp (list_append.comp (list_map primrec_fixedLits (fst.comp snd).to₂)
    primrec_readWords) primrec_consWords).of_eq fun _ => rfl

theorem primrec_fixedLen : Primrec fun p : Q × List Bool =>
    (fixedLits p.1.1 p.1.2.1 p.1.2.2).length :=
  list_length.comp (primrec_fixedLits.comp fst)

theorem primrec_readLen : Primrec fun p : Q × List Bool =>
    (readWords p.1.1 p.1.2.1 p.1.2.2).length :=
  list_length.comp (primrec_readWords.comp fst)

/-- The fixed literals of a clause, enumerated. -/
def clauseFixed (p : Q × List Bool) : List (ℕ × Bool) :=
  (List.range (fixedLits p.1.1 p.1.2.1 p.1.2.2).length).map fun i =>
    (i, ((fixedLits p.1.1 p.1.2.1 p.1.2.2).getD i ([], false)).2)

/-- The readable literals of a clause. -/
def clauseRead (p : Q × List Bool) : List (ℕ × Bool) :=
  (List.range (readVars p.1.1 p.1.2.1 p.1.2.2).length).map fun t =>
    ((fixedLits p.1.1 p.1.2.1 p.1.2.2).length + 2 * t +
      (if p.2.getD t false = true then 1 else 0), true)

/-- The constraint literals of a clause. -/
def clauseCons (p : Q × List Bool) : List (ℕ × Bool) :=
  ((consAt p.1.1 p.1.2.1 p.1.2.2).filterMap fun e => if e.2.2.1 = p.2 then some e else none).map
    fun e => ((fixedLits p.1.1 p.1.2.1 p.1.2.2).length + (readWords p.1.1 p.1.2.1 p.1.2.2).length +
      @List.idxOf _ instBEqOfDecidableEq (consWord p.1.1 p.1.2.1 p.1.2.2 e.2.2.2)
        (consWords p.1.1 p.1.2.1 p.1.2.2), true)

theorem clause_eq (q : Q) (r : List Bool) :
    clause q.1 q.2.1 q.2.2 r = clauseFixed (q, r) ++ clauseRead (q, r) ++ clauseCons (q, r) := by
  simp only [clause, clauseFixed, clauseRead, clauseCons, filter_eq_filterMap,
    zipIdx_map_eq _ ([], false), decide_eq_true_eq, idxOf_word]

set_option maxHeartbeats 1000000 in
theorem primrec_clauseFixed : Primrec clauseFixed :=
  list_map (list_range.comp primrec_fixedLen) (snd.pair (snd.comp ((list_getD ([], false)).comp
    (primrec_fixedLits.comp (fst.comp fst)) snd))).to₂

set_option maxHeartbeats 1000000 in
theorem primrec_clauseRead : Primrec clauseRead :=
  list_map (list_range.comp (list_length.comp (primrec_readVars.comp fst)))
    ((nat_add.comp (nat_add.comp (primrec_fixedLen.comp fst) (nat_mul.comp (const 2) snd))
      (Primrec.ite (Primrec.eq.comp ((list_getD false).comp (snd.comp fst) snd) (const true))
        (const 1) (const 0))).pair (const true)).to₂

set_option maxHeartbeats 1000000 in
theorem primrec_clauseCons : Primrec clauseCons :=
  list_map (listFilterMap (primrec_consAt.comp fst) (Primrec.ite (Primrec.eq.comp
    (fst.comp (snd.comp (snd.comp snd))) (snd.comp fst)) (option_some.comp snd)
      (const none)).to₂)
    ((nat_add.comp (nat_add.comp (primrec_fixedLen.comp fst) (primrec_readLen.comp fst))
      (list_idxOf.comp (primrec_consWord.comp (fst.comp fst) (snd.comp (snd.comp (snd.comp snd))))
        (primrec_consWords.comp (fst.comp fst)))).pair (const true)).to₂

theorem primrec_clause : Primrec₂ fun (q : Q) (r : List Bool) => clause q.1 q.2.1 q.2.2 r :=
  (list_append.comp (list_append.comp primrec_clauseFixed primrec_clauseRead)
    primrec_clauseCons).to₂.of_eq fun q r => (clause_eq q r).symm

theorem primrec_allBitsStep : Primrec allBitsStep :=
  (list_flatMap Primrec.id (list_cons.comp (list_cons.comp (const false) snd)
    (list_cons.comp (list_cons.comp (const true) snd) (const []))).to₂).of_eq fun _ => rfl

theorem primrec_allBits : Primrec allBits :=
  (nat_iterate Primrec.id (const [[]]) (primrec_allBitsStep.comp snd).to₂).of_eq
    fun n => (allBits_eq_iterate n).symm

theorem primrec_clauses : Primrec fun q : Q => clauses q.1 q.2.1 q.2.2 :=
  (list_map (primrec_allBits.comp (nat_add.comp (primrec_lenRAt.comp pg px)
    (primrec_lenRAt.comp pg py))) primrec_clause).of_eq fun _ => rfl

theorem primrec_challenge : Primrec fun p : ℕ × Q => challenge p.2.1 p.1 p.2.2.1 p.2.2.2 :=
  (fst.pair ((primrec_words.comp snd).pair (primrec_clauses.comp snd))).of_eq fun _ => rfl

theorem primrec_questionWeight : Primrec fun q : Q => (wts q.1).questionWeight q.2.1 q.2.2 := by
  have hf : Primrec fun q : Q => (q.1.w.filterMap fun t =>
      if t.1 = q.2.1 ∧ t.2.1 = q.2.2 then some t else none).map fun t => t.2.2 :=
    list_map (listFilterMap (primrec_w.comp pg) (Primrec.ite (PrimrecPred.and
      (Primrec.eq.comp (fst.comp snd) (px.comp fst))
      (Primrec.eq.comp (fst.comp (snd.comp snd)) (py.comp fst))) (option_some.comp snd)
        (const none)).to₂) (snd.comp (snd.comp snd)).to₂
  refine (list_foldr hf (const 0) (nat_add.comp (fst.comp snd)
    (snd.comp snd)).to₂).of_eq fun q => ?_
  rw [← List.sum_eq_foldr]
  simp only [HaltingGameValue.GameData.questionWeight, wts, filter_eq_filterMap,
    decide_eq_true_eq]

/-- The total weight, as a sum over lists. -/
def totalWeightL (g : TailoredGameData) : ℕ :=
  ((List.range (g.nV + 1)).flatMap fun x => (List.range (g.nV + 1)).map fun y =>
    (wts g).questionWeight x y).sum

theorem sum_fin_eq_sum_range (n : ℕ) (f : ℕ → ℕ) :
    ∑ x : Fin (n + 1), f x = ((List.range (n + 1)).map f).sum := by
  rw [Fin.sum_univ_eq_sum_range f, ← List.toFinset_range,
    List.sum_toFinset _ (List.nodup_range)]

theorem sum_flatMap_nat {α : Type*} (L : List α) (f : α → List ℕ) :
    (L.flatMap f).sum = (L.map fun x => (f x).sum).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem totalWeight_eq (g : TailoredGameData) : (wts g).totalWeight = totalWeightL g := by
  rw [HaltingGameValue.GameData.totalWeight, totalWeightL, sum_flatMap_nat]
  have : (wts g).nX = g.nV := rfl
  rw [this, sum_fin_eq_sum_range g.nV (fun x => ∑ y : Fin (g.nV + 1),
    (wts g).questionWeight x y)]
  congr 1
  apply List.map_congr_left
  intro x _
  exact sum_fin_eq_sum_range g.nV _

theorem primrec_totalWeightL : Primrec totalWeightL := by
  have hl : Primrec fun g : TailoredGameData =>
      (List.range (g.nV + 1)).flatMap fun x => (List.range (g.nV + 1)).map fun y =>
        (wts g).questionWeight x y :=
    list_flatMap (list_range.comp (succ.comp primrec_nV))
      (list_map (list_range.comp (succ.comp (primrec_nV.comp fst)))
        (primrec_questionWeight.comp ((fst.comp fst).pair ((snd.comp fst).pair snd))).to₂).to₂
  exact (list_foldr hl (const 0) (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
    fun g => (List.sum_eq_foldr).symm

theorem primrec_nGen : Primrec nGen :=
  (nat_add.comp (const 1) (nat_mul.comp (succ.comp primrec_nV) primrec_ansLen)).of_eq
    fun _ => rfl

set_option maxHeartbeats 1000000 in
/-- **The associated test is primitive recursive.** -/
theorem primrec_assocTest : Primrec assocTest := by
  have hgrid : Primrec fun g : TailoredGameData =>
      (List.range (g.nV + 1)).flatMap fun x => (List.range (g.nV + 1)).map fun y =>
        challenge g ((wts g).questionWeight x y) x y :=
    list_flatMap (list_range.comp (succ.comp primrec_nV))
      (list_map (list_range.comp (succ.comp (primrec_nV.comp fst)))
        (primrec_challenge.comp ((primrec_questionWeight.comp ((fst.comp fst).pair
          ((snd.comp fst).pair snd))).pair ((fst.comp fst).pair ((snd.comp fst).pair
            snd)))).to₂).to₂
  have hch : Primrec fun g : TailoredGameData =>
      if totalWeightL g = 0 then [challenge g 1 0 0] else
        (List.range (g.nV + 1)).flatMap fun x => (List.range (g.nV + 1)).map fun y =>
          challenge g ((wts g).questionWeight x y) x y :=
    Primrec.ite (Primrec.eq.comp primrec_totalWeightL (const 0))
      (list_cons.comp (primrec_challenge.comp ((const 1).pair (Primrec.id.pair
        ((const 0).pair (const 0))))) (const [])) hgrid
  refine ((Primrec.of_equiv_symm (e := SubgroupTestData.equivTuple)).comp
    (primrec_nGen.pair hch)).of_eq fun g => ?_
  simp only [assocTest, totalWeight_eq]
  rfl

end Primrec

end MIPRE.Tailored.Sofic

end
