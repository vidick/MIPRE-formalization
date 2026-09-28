/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ClassMIPStar
public import MIPRE.Foundations.Halting.Tabulate
public import MIPRE.Foundations.Halting.Arith

@[expose] public section

/-!
# The paper's class is contained in the computable one: tabulation

Blueprint `lem:mipstar-poly-sub`: `MIPStar L → MIPStarComputable L`, hence `MIPStar L → IsRE L`
through `MIPStarComputable.isRE`. A polynomial-time verifier is in particular a computable map from
strings to explicit games: on the input `z`, run the sampler on every seed of length `B z` and
the decider on every tuple of strings of length at most `B z`, each under the budget the
efficiency clause supplies, and write the result down as a `GameData`.

Two things about the table, both inherited from `Halting/Tabulate.lean`:

* **The questions are doubled.** A `GameData` is read as a synchronous game, where unequal
  answers to equal questions lose by fiat, and `G_z` is a general bipartite game; tagging
  Alice's questions with `false` and Bob's with `true` puts no weight on the diagonal and
  `quantumValue_doubled` says the value is unchanged (`Foundations/GameDouble.lean`).
* **Budgeted runs decide everything.** `Machine.runForD` under the bound of
  `PolyVerifier.Efficient` returns the sampler's pair and the decider's verdict
  (`Machine.runForD_eq_some_iff`), so the table is primitive recursive in `z` and, on an
  efficient verifier, correct (`quantumValue_tab`).

The indexing: questions and answers are both indexed among the strings of length at most `B z`
(`Data.bitStrsLE`), a tagged question `(tg, x)` at `idxOf x + N · tg` with `N` the number of
such strings (`qIdx`, `qEquiv`), an answer at `idxOf a` (`aEquiv`).
-/

namespace MIPRE

open MIPRE.Cost Verifier
open HaltingGameValue (GameData)

namespace PolyVerifier

/-! ## Indexing the tagged strings of length at most `T` -/

/-- The number of strings of length at most `T`. -/
abbrev N (T : ℕ) : ℕ := (Data.bitStrsLE T).length

theorem length_answerList_eq (T : ℕ) : (answerList T).length = N T := List.length_map ..

/-- The index of the tagged question `(tg, x)`. -/
def qIdx (T : ℕ) (tg : Bool) (x : BitStr) : ℕ :=
  (Data.bitStrsLE T).idxOf x + N T * (if tg then 1 else 0)

/-- The tagged question alphabet, indexed. -/
noncomputable def qEquiv (T : ℕ) : Fin (2 * N T) ≃ Bool × Answers T :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr finTwoEquiv ((finCongr (length_answerList_eq T).symm).trans (answerEquiv T)))

/-- The answer alphabet, indexed among the strings of length at most `T`. -/
noncomputable def aEquiv (T : ℕ) : Fin (N T) ≃ Answers T :=
  (finCongr (length_answerList_eq T).symm).trans (answerEquiv T)

theorem aEquiv_apply (T : ℕ) (k : Fin (N T)) :
    (Data.bitStrsLE T).idxOf (aEquiv T k).1 = (k : ℕ) := by
  rw [← answerEquiv_symm_val, aEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem finTwoEquiv_ite (a : Fin 2) : (if finTwoEquiv a then 1 else 0) = (a : ℕ) := by
  fin_cases a <;> rfl

theorem qEquiv_apply (T : ℕ) (i : Fin (2 * N T)) :
    qIdx T (qEquiv T i).1 (qEquiv T i).2.1 = (i : ℕ) := by
  obtain ⟨⟨a, b⟩, h⟩ : ∃ p : Fin 2 × Fin (N T), finProdFinEquiv.symm i = p :=
    ⟨_, rfl⟩
  have hi : i = finProdFinEquiv (a, b) := by rw [← h, Equiv.apply_symm_apply]
  have h1 : (qEquiv T i).1 = finTwoEquiv a := by
    simp only [qEquiv, Equiv.trans_apply, h, Equiv.prodCongr_apply, Prod.map_fst]
  have h2 : (qEquiv T i).2 = aEquiv T b := by
    simp only [qEquiv, aEquiv, Equiv.trans_apply, h, Equiv.prodCongr_apply, Prod.map_snd]
  rw [qIdx, h1, h2, aEquiv_apply, finTwoEquiv_ite, hi]
  rfl

theorem qIdx_lt (T : ℕ) (tg : Bool) {x : BitStr} (hx : x ∈ Data.bitStrsLE T) :
    qIdx T tg x < 2 * N T := by
  have := List.idxOf_lt_length_iff.2 hx
  unfold qIdx N
  cases tg <;> simp <;> omega

theorem qIdx_inj (T : ℕ) {tg tg' : Bool} {x x' : BitStr} (hx : x ∈ Data.bitStrsLE T)
    (hx' : x' ∈ Data.bitStrsLE T) (h : qIdx T tg x = qIdx T tg' x') : tg = tg' ∧ x = x' := by
  have h1 := List.idxOf_lt_length_iff.2 hx
  have h2 := List.idxOf_lt_length_iff.2 hx'
  unfold qIdx N at h
  have htg : tg = tg' := by
    cases tg <;> cases tg' <;> simp at h ⊢ <;> omega
  subst htg
  refine ⟨rfl, (List.idxOf_inj hx).1 ?_⟩
  cases tg <;> simp at h <;> omega

theorem qIdx_eq_iff (T : ℕ) (tg : Bool) {x : BitStr} (hx : x ∈ Data.bitStrsLE T)
    (i : Fin (2 * N T)) :
    qIdx T tg x = (i : ℕ) ↔ tg = (qEquiv T i).1 ∧ x = (qEquiv T i).2.1 := by
  constructor
  · intro h
    exact qIdx_inj T hx ((Data.mem_bitStrsLE _ _).2 (qEquiv T i).2.2)
      (h.trans (qEquiv_apply T i).symm)
  · rintro ⟨rfl, rfl⟩
    exact qEquiv_apply T i

/-! ## The table -/

/-- The sampler's pair on `(z, r)` under the budget `T`, read off a budgeted run; `([], [])`
if the run does not finish or its result is not a pair of strings. -/
def sampleC (sd : Data) (T : ℕ) (z r : BitStr) : BitStr × BitStr :=
  ((Machine.runForD sd (encode (z, r)) T).bind fun d =>
    (SizedEncoding.decode d.left : Option BitStr).bind fun x =>
      (SizedEncoding.decode d.right : Option BitStr).map fun y => (x, y)).getD ([], [])

/-- The decider's verdict on `(z, x, y, a, b)` under the budget `P(|z| + |x| + |y| + |a| + |b|)`. -/
def accC (pd : Data) (P : Polynomial ℕ) (z x y a b : BitStr) : Bool :=
  decide (Machine.runForD pd (encode (z, x, y, a, b))
    (P.eval (z.length + x.length + y.length + a.length + b.length)) = some (encode true))

/-- The acceptance table over four copies of the strings of length at most `T`. -/
def accListLE (T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) : List (ℕ × ℕ × ℕ × ℕ) :=
  (Data.bitStrsLE T).flatMap fun x =>
    (Data.bitStrsLE T).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).filterMap fun b =>
          if acc? x y a b then
            some (fA x, fB y, (Data.bitStrsLE T).idxOf a, (Data.bitStrsLE T).idxOf b)
          else none

theorem mem_accListLE_iff {T : ℕ} {fA fB : BitStr → ℕ}
    {acc? : BitStr → BitStr → BitStr → BitStr → Bool} {i j k l : ℕ} :
    (i, j, k, l) ∈ accListLE T fA fB acc? ↔
      ∃ x ∈ Data.bitStrsLE T, ∃ y ∈ Data.bitStrsLE T,
        ∃ a ∈ Data.bitStrsLE T, ∃ b ∈ Data.bitStrsLE T,
          acc? x y a b = true ∧ i = fA x ∧ j = fB y ∧
            k = (Data.bitStrsLE T).idxOf a ∧ l = (Data.bitStrsLE T).idxOf b := by
  simp only [accListLE, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, h⟩
    by_cases hc : acc? x y a b
    · rw [if_pos hc] at h
      obtain ⟨hi, hj, hk, hl⟩ : fA x = i ∧ fB y = j ∧
          (Data.bitStrsLE T).idxOf a = k ∧ (Data.bitStrsLE T).idxOf b = l := by simpa using h
      exact ⟨x, hx, y, hy, a, ha, b, hb, hc, hi.symm, hj.symm, hk.symm, hl.symm⟩
    · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, hc, rfl, rfl, rfl, rfl⟩
    exact ⟨x, hx, y, hy, a, ha, b, hb, by rw [if_pos hc]⟩

/-- The four-fold product of the enumeration, as one flat list. -/
def tuplesLE (T : ℕ) : List (BitStr × BitStr × BitStr × BitStr) :=
  (Data.bitStrsLE T).flatMap fun x =>
    (Data.bitStrsLE T).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).map fun b => (x, y, a, b)

theorem primrec_tuplesLE : Primrec tuplesLE := by
  have h4 : Primrec fun q : (((ℕ × BitStr) × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1.1).map fun b => (q.1.1.2, q.1.2, q.2, b) := by
    refine Primrec.list_map
      (Data.primrec_bitStrsLE.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) ?_
    have hx : Primrec fun r : (((ℕ × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hy : Primrec fun r : (((ℕ × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have ha : Primrec fun r : (((ℕ × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.2 := Primrec.snd.comp Primrec.fst
    exact (hx.pair (hy.pair (ha.pair Primrec.snd))).to₂
  have h3 : Primrec fun q : ((ℕ × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1).flatMap fun a =>
        (Data.bitStrsLE q.1.1).map fun b => (q.1.2, q.2, a, b) :=
    Primrec.list_flatMap
      (Data.primrec_bitStrsLE.comp (Primrec.fst.comp Primrec.fst)) h4.to₂
  have h2 : Primrec fun q : (ℕ × BitStr) =>
      (Data.bitStrsLE q.1).flatMap fun y =>
        (Data.bitStrsLE q.1).flatMap fun a =>
          (Data.bitStrsLE q.1).map fun b => (q.2, y, a, b) :=
    Primrec.list_flatMap (Data.primrec_bitStrsLE.comp Primrec.fst) h3.to₂
  exact Primrec.list_flatMap Data.primrec_bitStrsLE h2.to₂

theorem accListLE_eq_filterMap (T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) :
    accListLE T fA fB acc? = (tuplesLE T).filterMap fun q =>
      if acc? q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA q.1, fB q.2.1,
          (Data.bitStrsLE T).idxOf q.2.2.1, (Data.bitStrsLE T).idxOf q.2.2.2)
      else none := by
  simp only [accListLE, tuplesLE, List.filterMap_flatMap, List.filterMap_map, Function.comp_def]

theorem primrec_accListLE {α : Type*} [Primcodable α] {T : α → ℕ}
    {fA fB : α → BitStr → ℕ}
    {acc? : α → BitStr → BitStr → BitStr → BitStr → Bool}
    (hT : Primrec T) (hfA : Primrec₂ fA) (hfB : Primrec₂ fB)
    (hacc : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :
    Primrec fun a => accListLE (T a) (fA a) (fB a) (acc? a) := by
  have hbl : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Data.bitStrsLE (T q.1) := Data.primrec_bitStrsLE.comp (hT.comp Primrec.fst)
  have hbody : Primrec₂ fun (a : α) (q : BitStr × BitStr × BitStr × BitStr) =>
      (if acc? a q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA a q.1, fB a q.2.1,
          (Data.bitStrsLE (T a)).idxOf q.2.2.1, (Data.bitStrsLE (T a)).idxOf q.2.2.2)
        else none) := by
    refine Primrec.ite ⟨inferInstance, hacc.of_eq fun q => by
        cases h : acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 <;> simp [h]⟩ ?_ (Primrec.const none)
    refine Primrec.option_some.comp
      ((hfA.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
        ((hfB.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
          ((Cost.primrec_idxOf_bitStr.comp
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl).pair
            (Cost.primrec_idxOf_bitStr.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl))))
  exact (Primrec.listFilterMap (primrec_tuplesLE.comp hT) hbody).of_eq fun a =>
    (accListLE_eq_filterMap (T a) (fA a) (fB a) (acc? a)).symm

/-- **The table of `G_z`**, from the two programs and the polynomial: doubled questions indexed
by `qIdx`, one unit of weight per seed, and the acceptance table by budgeted runs. -/
def tabOf (sd pd : Data) (P : Polynomial ℕ) (z : BitStr) : GameData where
  nX := 2 * N (P.eval z.length) - 1
  nA := N (P.eval z.length) - 1
  w := weightList (P.eval z.length)
        (fun r => qIdx (P.eval z.length) false
          (sampleC sd (P.eval (z.length + P.eval z.length)) z r).1)
        (fun r => qIdx (P.eval z.length) true
          (sampleC sd (P.eval (z.length + P.eval z.length)) z r).2)
  acc := accListLE (P.eval z.length) (qIdx (P.eval z.length) false) (qIdx (P.eval z.length) true)
        (accC pd P z)

/-! ## The table is primitive recursive in the input -/

theorem primrec_qIdx (tg : Bool) : Primrec₂ fun (T : ℕ) (x : BitStr) => qIdx T tg x := by
  have hbl : Primrec fun q : ℕ × BitStr => Data.bitStrsLE q.1 :=
    Data.primrec_bitStrsLE.comp Primrec.fst
  exact (Primrec.nat_add.comp (Cost.primrec_idxOf_bitStr.comp Primrec.snd hbl)
    (Primrec.nat_mul.comp (Primrec.list_length.comp hbl)
      (Primrec.const (if tg then 1 else 0)))).to₂

theorem primrec_sampleC (sd : Data) :
    Primrec fun q : (ℕ × BitStr) × BitStr => sampleC sd q.1.1 q.1.2 q.2 := by
  have hin : Primrec fun q : (ℕ × BitStr) × BitStr => (encode (q.1.2, q.2) : Data) :=
    Data.primrec_cons.comp (primrec_encode_bitStr.comp (Primrec.snd.comp Primrec.fst))
      (primrec_encode_bitStr.comp Primrec.snd)
  have hrun : Primrec fun q : (ℕ × BitStr) × BitStr =>
      Machine.runForD sd (encode (q.1.2, q.2)) q.1.1 :=
    Machine.primrec_runForD.comp (((Primrec.const sd).pair hin).pair (Primrec.fst.comp Primrec.fst))
  have hinner : Primrec₂ fun (_ : (ℕ × BitStr) × BitStr) (d : Data) =>
      (SizedEncoding.decode d.left : Option BitStr).bind fun x =>
        (SizedEncoding.decode d.right : Option BitStr).map fun y => (x, y) := by
    refine Primrec.option_bind
      (Data.primrec_decode_bitStr.comp (Data.primrec_left.comp Primrec.snd)) ?_
    refine Primrec.option_map
      (Data.primrec_decode_bitStr.comp (Data.primrec_right.comp (Primrec.snd.comp Primrec.fst))) ?_
    exact (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  exact Primrec.option_getD.comp (Primrec.option_bind hrun hinner) (Primrec.const ([], []))

set_option maxHeartbeats 1000000 in
theorem primrec_accC (pd : Data) (P : Polynomial ℕ) :
    Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      accC pd P q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have hz : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.1 := Primrec.fst
  have hx : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hy : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hebs : Primrec fun l : BitStr => (encode l : Data) := primrec_encode_bitStr
  have hinput : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      (encode (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2) : Data) :=
    Data.primrec_cons.comp (hebs.comp hz)
      (Data.primrec_cons.comp (hebs.comp hx)
        (Data.primrec_cons.comp (hebs.comp hy)
          (Data.primrec_cons.comp (hebs.comp ha) (hebs.comp hb))))
  have hlen : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      q.1.length + q.2.1.length + q.2.2.1.length + q.2.2.2.1.length + q.2.2.2.2.length :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp hz) (Primrec.list_length.comp hx))
      (Primrec.list_length.comp hy)) (Primrec.list_length.comp ha)) (Primrec.list_length.comp hb)
  have hbudget : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      P.eval (q.1.length + q.2.1.length + q.2.2.1.length + q.2.2.2.1.length + q.2.2.2.2.length) :=
    (Cost.primrec_poly_eval P).comp hlen
  have hfin : PrimrecPred fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      Machine.runForD pd (encode (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2))
        (P.eval (q.1.length + q.2.1.length + q.2.2.1.length + q.2.2.2.1.length + q.2.2.2.2.length))
        = some (encode true) :=
    Primrec.eq.comp (Machine.primrec_runForD.comp (((Primrec.const pd).pair hinput).pair hbudget))
      (Primrec.const (some (encode true) : Option Data))
  exact (Primrec.ite hfin (Primrec.const true) (Primrec.const false)).of_eq fun q => by
    simp only [accC]; split <;> simp_all

-- The `Primrec` composition below exceeds the default heartbeat budget under Mathlib
-- v4.35 (the unifier unfolds the encodings); it elaborates in seconds with a larger one.
set_option maxHeartbeats 1000000 in
theorem primrec_tabOf (sd pd : Data) (P : Polynomial ℕ) : Primrec (tabOf sd pd P) := by
  have hT : Primrec fun z : BitStr => P.eval z.length :=
    (Cost.primrec_poly_eval P).comp Primrec.list_length
  have hN : Primrec fun z : BitStr => N (P.eval z.length) :=
    Primrec.list_length.comp (Data.primrec_bitStrsLE.comp hT)
  have hnX : Primrec fun z : BitStr => 2 * N (P.eval z.length) - 1 :=
    Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) hN) (Primrec.const 1)
  have hnA : Primrec fun z : BitStr => N (P.eval z.length) - 1 :=
    Primrec.nat_sub.comp hN (Primrec.const 1)
  have hT' : Primrec fun z : BitStr => P.eval (z.length + P.eval z.length) :=
    (Cost.primrec_poly_eval P).comp (Primrec.nat_add.comp Primrec.list_length hT)
  have hsamp : Primrec fun q : BitStr × BitStr =>
      sampleC sd (P.eval (q.1.length + P.eval q.1.length)) q.1 q.2 :=
    (primrec_sampleC sd).comp (((hT'.comp Primrec.fst).pair Primrec.fst).pair Primrec.snd)
  have hw : Primrec fun z : BitStr => weightList (P.eval z.length)
      (fun r => qIdx (P.eval z.length) false
        (sampleC sd (P.eval (z.length + P.eval z.length)) z r).1)
      (fun r => qIdx (P.eval z.length) true
        (sampleC sd (P.eval (z.length + P.eval z.length)) z r).2) := by
    refine Primrec.list_map (Data.primrec_bitStrsOfLen.comp hT) ?_
    exact (((primrec_qIdx false).comp (hT.comp Primrec.fst) (Primrec.fst.comp hsamp)).pair
      (((primrec_qIdx true).comp (hT.comp Primrec.fst) (Primrec.snd.comp hsamp)).pair
        (Primrec.const 1))).to₂
  have hacc : Primrec fun z : BitStr => accListLE (P.eval z.length) (qIdx (P.eval z.length) false)
      (qIdx (P.eval z.length) true) (accC pd P z) := by
    refine primrec_accListLE hT ((primrec_qIdx false).comp (hT.comp Primrec.fst) Primrec.snd)
      ((primrec_qIdx true).comp (hT.comp Primrec.fst) Primrec.snd) ?_
    exact (primrec_accC pd P).of_eq fun q => rfl
  refine ((Primrec.of_equiv_symm (e := GameData.equivTuple)).comp
    (hnX.pair (hnA.pair (hw.pair hacc)))).of_eq ?_
  intro z
  rfl

/-! ## The table of a verifier, and its correctness on an efficient input -/

variable (V : PolyVerifier)

/-- The table of `G_z`. -/
def tab (z : BitStr) : GameData := tabOf (encode V.sampler) (encode V.decider) V.bound z

theorem tab_computable : Computable V.tab :=
  (primrec_tabOf (encode V.sampler) (encode V.decider) V.bound).to_comp

theorem tab_nX (z : BitStr) : (V.tab z).nX + 1 = 2 * N (V.B z) := by
  show 2 * N (V.B z) - 1 + 1 = _
  have := Data.length_bitStrsLE_pos (V.B z)
  unfold N at this ⊢
  omega

theorem tab_nA (z : BitStr) : (V.tab z).nA + 1 = N (V.B z) := by
  show N (V.B z) - 1 + 1 = _
  have := Data.length_bitStrsLE_pos (V.B z)
  unfold N at this ⊢
  omega

/-- The question relabeling. -/
noncomputable def eX (z : BitStr) : Fin ((V.tab z).nX + 1) ≃ Bool × Answers (V.B z) :=
  (finCongr (V.tab_nX z)).trans (qEquiv (V.B z))

/-- The answer relabeling. -/
noncomputable def eA (z : BitStr) : Fin ((V.tab z).nA + 1) ≃ Answers (V.B z) :=
  (finCongr (V.tab_nA z)).trans (aEquiv (V.B z))

theorem eX_apply (z : BitStr) (i : Fin ((V.tab z).nX + 1)) :
    qIdx (V.B z) (V.eX z i).1 (V.eX z i).2.1 = (i : ℕ) := by
  rw [eX, Equiv.trans_apply, qEquiv_apply]
  rfl

theorem eA_apply (z : BitStr) (k : Fin ((V.tab z).nA + 1)) :
    (Data.bitStrsLE (V.B z)).idxOf (V.eA z k).1 = (k : ℕ) := by
  rw [eA, Equiv.trans_apply, aEquiv_apply]
  rfl

theorem qIdx_eq_iff' (z : BitStr) (tg : Bool) {x : BitStr} (hx : x ∈ Data.bitStrsLE (V.B z))
    (i : Fin ((V.tab z).nX + 1)) :
    qIdx (V.B z) tg x = (i : ℕ) ↔ tg = (V.eX z i).1 ∧ x = (V.eX z i).2.1 := by
  constructor
  · intro h
    exact qIdx_inj _ hx ((Data.mem_bitStrsLE _ _).2 (V.eX z i).2.2)
      (h.trans (V.eX_apply z i).symm)
  · rintro ⟨rfl, rfl⟩
    exact V.eX_apply z i

/-- **The budgeted sample is the question pair**, on an efficient input and a seed of the right
length. -/
theorem sampleC_eq {z : BitStr} (h : V.Efficient z) {r : BitStr} (hr : r.length = V.B z) :
    sampleC (encode V.sampler) (V.bound.eval (z.length + V.B z)) z r =
      ((V.questions z r).1.1, (V.questions z r).2.1) := by
  obtain ⟨x, y, t, ht, hrun, hx, hy⟩ := V.questions_eq_of_efficient h hr
  rw [hr] at ht
  have hrf : Machine.runForD (encode V.sampler) (encode (z, r))
      (V.bound.eval (z.length + V.B z)) = some (encode (x, y)) :=
    (Machine.runForD_eq_some_iff ⟨_, t, ht, hrun⟩).2 ⟨t, hrun⟩
  rw [hx, hy]
  simp only [sampleC, hrf, Option.bind_some]
  show ((SizedEncoding.decode (Data.cons (encode x) (encode y)).left : Option BitStr).bind
    fun x' => (SizedEncoding.decode (Data.cons (encode x) (encode y)).right : Option BitStr).map
      fun y' => (x', y')).getD ([], []) = (x, y)
  rw [Data.left_cons, Data.right_cons, SizedEncoding.decode_encode, SizedEncoding.decode_encode]
  rfl

/-- **The budgeted verdict is acceptance**, on an efficient input. -/
theorem accC_eq {z : BitStr} (h : V.Efficient z) (x y a b : BitStr) :
    accC (encode V.decider) V.bound z x y a b = true ↔ V.Accepts z x y a b := by
  rw [accC, decide_eq_true_iff, Machine.runForD_eq_some_iff (h.decider_time x y a b)]
  rfl

theorem sampleC_fst_mem {z : BitStr} (h : V.Efficient z) {r : BitStr}
    (hr : r ∈ Data.bitStrsOfLen (V.B z)) :
    (sampleC (encode V.sampler) (V.bound.eval (z.length + V.B z)) z r).1 ∈
      Data.bitStrsLE (V.B z) := by
  rw [V.sampleC_eq h ((Data.mem_bitStrsOfLen _ _).1 hr)]
  exact (Data.mem_bitStrsLE _ _).2 (V.questions z r).1.2

theorem sampleC_snd_mem {z : BitStr} (h : V.Efficient z) {r : BitStr}
    (hr : r ∈ Data.bitStrsOfLen (V.B z)) :
    (sampleC (encode V.sampler) (V.bound.eval (z.length + V.B z)) z r).2 ∈
      Data.bitStrsLE (V.B z) := by
  rw [V.sampleC_eq h ((Data.mem_bitStrsOfLen _ _).1 hr)]
  exact (Data.mem_bitStrsLE _ _).2 (V.questions z r).2.2

/-- **The `μ` clause, doubled**: the tabulated distribution is `μ_z` on the block
`(false, ·) × (true, ·)` and zero elsewhere. -/
theorem mu_clause {z : BitStr} (h : V.Efficient z) (i j : Fin ((V.tab z).nX + 1)) :
    (V.tab z).game.μ i j = (V.game z).doubled.μ (V.eX z i) (V.eX z j) := by
  classical
  set T := V.B z with hT
  have hrange : ∀ (tg : Bool) (f : BitStr × BitStr → BitStr),
      (∀ r ∈ Data.bitStrsOfLen T,
        f (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r) ∈ Data.bitStrsLE T) →
      ∀ r ∈ Data.bitStrsOfLen T,
        qIdx T tg (f (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r)) <
          (V.tab z).nX + 1 := by
    intro tg f hf r hr
    rw [V.tab_nX z]
    exact qIdx_lt T tg (hf r hr)
  have htot : (V.tab z).totalWeight = 2 ^ T :=
    totalWeight_weightList _ _ _ _ _ _
      (hrange false Prod.fst fun r hr => V.sampleC_fst_mem h hr)
      (hrange true Prod.snd fun r hr => V.sampleC_snd_mem h hr)
  have hqw : ∀ a b : ℕ, (V.tab z).questionWeight a b
      = ((Data.bitStrsOfLen T).filter fun r =>
          decide (qIdx T false (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).1 = a
            ∧ qIdx T true (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).2
              = b)).length :=
    fun a b => questionWeight_weightList _ _ _ _ _ _ a b
  rw [GameData.game_μ, htot, if_neg (Nat.two_pow_pos _).ne', hqw,
    show (V.game z).doubled.μ (V.eX z i) (V.eX z j)
      = if (V.eX z i).1 = false ∧ (V.eX z j).1 = true then
          (V.game z).μ (V.eX z i).2 (V.eX z j).2 else 0 from rfl]
  by_cases htag : (V.eX z i).1 = false ∧ (V.eX z j).1 = true
  · rw [if_pos htag, V.game_μ, seedCount]
    push_cast
    congr 2
    apply congrArg List.length
    refine List.filter_congr fun r hr => ?_
    have hr' : r.length = T := (Data.mem_bitStrsOfLen _ _).1 hr
    rw [V.sampleC_eq h hr']
    simp only [decide_eq_decide]
    rw [V.qIdx_eq_iff' z false ((Data.mem_bitStrsLE _ _).2 (V.questions z r).1.2) i,
      V.qIdx_eq_iff' z true ((Data.mem_bitStrsLE _ _).2 (V.questions z r).2.2) j,
      ← htag.1, ← htag.2]
    simp only [true_and]
    rw [Prod.ext_iff]
    exact and_congr Subtype.ext_iff.symm Subtype.ext_iff.symm
  · rw [if_neg htag]
    have hnil : ((Data.bitStrsOfLen T).filter fun r =>
        decide (qIdx T false (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).1
            = (i : ℕ)
          ∧ qIdx T true (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).2
            = (j : ℕ))) = [] := by
      refine List.filter_eq_nil_iff.2 fun r hr => ?_
      simp only [decide_eq_true_eq, not_and]
      intro h1 h2
      exact htag ⟨((V.qIdx_eq_iff' z false (V.sampleC_fst_mem h hr) i).1 h1).1.symm,
        ((V.qIdx_eq_iff' z true (V.sampleC_snd_mem h hr) j).1 h2).1.symm⟩
    rw [hnil]
    simp

/-- **The acceptance table read back, doubled.** -/
theorem acc_mem_iff {z : BitStr} (h : V.Efficient z) (i j : Fin ((V.tab z).nX + 1))
    (k l : Fin ((V.tab z).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (V.tab z).acc
      ↔ ((V.eX z i).1 = false ∧ (V.eX z j).1 = true ∧
          V.Accepts z (V.eX z i).2.1 (V.eX z j).2.1 (V.eA z k).1 (V.eA z l).1) := by
  have hqmem : ∀ m : Fin ((V.tab z).nX + 1), (V.eX z m).2.1 ∈ Data.bitStrsLE (V.B z) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (V.eX z m).2.2
  have hamem : ∀ m : Fin ((V.tab z).nA + 1), (V.eA z m).1 ∈ Data.bitStrsLE (V.B z) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (V.eA z m).2
  rw [show (V.tab z).acc = accListLE (V.B z) (qIdx (V.B z) false) (qIdx (V.B z) true)
      (accC (encode V.decider) V.bound z) from rfl, mem_accListLE_iff]
  constructor
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, hacc, hi, hj, hk, hl⟩
    obtain ⟨hti, hxi⟩ := (V.qIdx_eq_iff' z false hx i).1 hi.symm
    obtain ⟨htj, hyj⟩ := (V.qIdx_eq_iff' z true hy j).1 hj.symm
    have ha' : a = (V.eA z k).1 := (List.idxOf_inj ha).1 (by rw [← hk, V.eA_apply])
    have hb' : b = (V.eA z l).1 := (List.idxOf_inj hb).1 (by rw [← hl, V.eA_apply])
    refine ⟨hti.symm, htj.symm, ?_⟩
    rw [← hxi, ← hyj, ← ha', ← hb']
    exact (V.accC_eq h x y a b).1 hacc
  · rintro ⟨ht1, ht2, hacc⟩
    refine ⟨_, hqmem i, _, hqmem j, _, hamem k, _, hamem l, (V.accC_eq h _ _ _ _).2 hacc,
      ?_, ?_, (V.eA_apply z k).symm, (V.eA_apply z l).symm⟩
    · rw [← ht1, V.eX_apply z i]
    · rw [← ht2, V.eX_apply z j]

/-- **The `D` clause, doubled.** -/
theorem D_clause {z : BitStr} (h : V.Efficient z) (i j : Fin ((V.tab z).nX + 1))
    (k l : Fin ((V.tab z).nA + 1)) :
    (V.tab z).game.D i j k l
      = (V.game z).doubled.D (V.eX z i) (V.eX z j) (V.eA z k) (V.eA z l) := by
  classical
  refine Bool.eq_iff_iff.2 ?_
  rw [GameData.game_D,
    show (V.game z).doubled.D (V.eX z i) (V.eX z j) (V.eA z k) (V.eA z l)
      = if (V.eX z i).1 = false ∧ (V.eX z j).1 = true then
          (V.game z).D (V.eX z i).2 (V.eX z j).2 (V.eA z k) (V.eA z l) else false from rfl]
  by_cases hc : i = j ∧ k ≠ l
  · rw [if_pos hc, if_neg (by rw [hc.1]; exact fun h => by simp_all)]
  · rw [if_neg hc, decide_eq_true_iff, V.acc_mem_iff h]
    by_cases ht : (V.eX z i).1 = false ∧ (V.eX z j).1 = true
    · rw [if_pos ht, V.game_D, decide_eq_true_iff]
      exact ⟨fun h => h.2.2, fun h => ⟨ht.1, ht.2, h⟩⟩
    · rw [if_neg ht]
      simp only [Bool.false_eq_true, iff_false]
      exact fun h => ht ⟨h.1, h.2.1⟩

/-- **The table has the value of `G_z`**, on an efficient input. -/
theorem quantumValue_tab {z : BitStr} (h : V.Efficient z) :
    quantumValue (V.tab z).game = quantumValue (V.game z) := by
  rw [← quantumValue_doubled (V.game z)]
  exact quantumValue_eq_of_equiv (V.game z).doubled.toGame (V.tab z).game (V.eX z) (V.eX z)
    (V.eA z) (V.eA z) (V.mu_clause h) (V.D_clause h)

end PolyVerifier

/-- **`lem:mipstar-poly-sub`: the paper's class is contained in the computable one.** -/
theorem MIPStar.toComputable {L : Set BitStr} (h : MIPStar L) : MIPStarComputable L := by
  obtain ⟨V, heff, hgap⟩ := h
  refine ⟨V.tab, V.tab_computable, fun z => ?_⟩
  rw [V.quantumValue_tab (heff z)]
  exact hgap z

/-- The paper's class is contained in `RE`. -/
theorem MIPStar.isRE {L : Set BitStr} (h : MIPStar L) : IsRE L :=
  h.toComputable.isRE

end MIPRE

end
