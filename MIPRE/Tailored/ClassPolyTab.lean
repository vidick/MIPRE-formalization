/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.ClassPoly
public import MIPRE.Tailored.Class
public import MIPRE.Tailored.Halting.Tabulate
public import MIPRE.Foundations.ClassMIPStarTab

@[expose] public section

/-!
# The paper's class `TMIP*` is contained in the computable one: tabulation

`TMIPStar L → TMIPStarComputable L`, hence `TMIPStar ⊆ RE` through `TMIPStarComputable.isRE`, as
`Foundations/ClassMIPStarTab.lean` gives it for `MIP*`. On the input `z`, run the three programs
of a polynomial-time tailored verifier under the budgets `Efficient` supplies and write the
doubled game `(V.tgame z).doubled` down as a `TailoredGameData` (`tabOfP`):

* the vertices and the weights are those of `PolyVerifier.tabOf`: a tagged question `(tg, x)` at
  `qIdx T tg x = idxOf x + N · tg`, and one unit of weight per seed at the pair of tagged questions
  it produces;
* the lengths at a vertex are what the calculator outputs on its question (`lenRunP`), the question
  of the vertex `v` being the `(v mod N)`-th string (`qOfIdx`);
* the constraints at a pair of vertices and a readable part of the right length are what the
  processor outputs there (`lpRunP`).

`presents_tabOfP`: on an efficient input the tabulation presents the doubled game, so it has a
perfect ZPC strategy when the doubled game does and the value of the game
(`MIPRE.Tailored.Presents`).
-/

namespace MIPRE.Tailored

open Cost Verifier TailoredGameValue
open PolyVerifier (N qIdx qEquiv)

/-! ## The table -/

/-- The question at the vertex `v`: the `(v mod N)`-th string of length at most `T`, the vertex of
the tagged question `(tg, x)` being `qIdx T tg x = idxOf x + N · tg`. -/
def qOfIdx (T v : ℕ) : BitStr := (Data.bitStrsLE T).getD (v % N T) []

/-- The length the calculator outputs on `(z, x, κ)` under the budget `P(|z| + |x|)`, read in
unary; `0` when the budget is missed. -/
def lenRunP (ld : Data) (P : Polynomial ℕ) (z x : BitStr) (κ : Bool) : ℕ :=
  ((Machine.runForD ld (encode (z, x, κ)) (P.eval (z.length + x.length))).map
    Data.unaryToNat).getD 0

/-- The constraints the processor outputs on `(z, x, y, a^R, b^R)` under the budget
`P(|z| + |x| + |y| + |a^R| + |b^R|)`; `[]` when the budget is missed. -/
def lpRunP (pd : Data) (P : Polynomial ℕ) (z x y aR bR : BitStr) : List BitStr :=
  ((Machine.runForD pd (encode (z, x, y, aR, bR))
      (P.eval (z.length + x.length + y.length + aR.length + bR.length))).map
    Data.bitsListD).getD []

/-- The lengths at the vertices. -/
def lenListP (ld : Data) (P : Polynomial ℕ) (z : BitStr) (κ : Bool) : List ℕ :=
  (List.range (2 * N (P.eval z.length))).map fun v =>
    lenRunP ld P z (qOfIdx (P.eval z.length) v) κ

/-- The constraint entries at a pair of vertices and a readable part. -/
def consAtP (pd : Data) (P : Polynomial ℕ) (z : BitStr) (lR : List ℕ) (v v' : ℕ) (γ : BitStr) :
    List (ℕ × ℕ × BitStr × BitStr) :=
  (lpRunP pd P z (qOfIdx (P.eval z.length) v) (qOfIdx (P.eval z.length) v')
    (γ.take (lR.getD v 0)) (γ.drop (lR.getD v 0))).map fun c => (v, v', γ, c)

/-- The constraint entries. -/
def consTP (pd : Data) (P : Polynomial ℕ) (z : BitStr) (lR : List ℕ) :
    List (ℕ × ℕ × BitStr × BitStr) :=
  (List.range (2 * N (P.eval z.length))).flatMap fun v =>
    (List.range (2 * N (P.eval z.length))).flatMap fun v' =>
      (Data.bitStrsOfLen (lR.getD v 0 + lR.getD v' 0)).flatMap fun γ => consAtP pd P z lR v v' γ

/-- **The table of the doubled game** of a polynomial-time tailored verifier, from its three
programs and its polynomial: the vertices and weights of `PolyVerifier.tabOf`, the lengths and
constraints by budgeted runs. -/
def tabOfP (sd ld pd : Data) (P : Polynomial ℕ) (z : BitStr) : TailoredGameData where
  nV := 2 * N (P.eval z.length) - 1
  lenR := lenListP ld P z false
  lenL := lenListP ld P z true
  w := weightList (P.eval z.length)
        (fun r => qIdx (P.eval z.length) false
          (PolyVerifier.sampleC sd (P.eval (z.length + P.eval z.length)) z r).1)
        (fun r => qIdx (P.eval z.length) true
          (PolyVerifier.sampleC sd (P.eval (z.length + P.eval z.length)) z r).2)
  cons := consTP pd P z (lenListP ld P z false)

/-! ## The table is primitive recursive in the input -/

section Primrec

variable (sd ld pd : Data) (P : Polynomial ℕ)

theorem primrec_qOfIdx : Primrec₂ qOfIdx := by
  have hbl : Primrec fun q : ℕ × ℕ => Data.bitStrsLE q.1 :=
    Data.primrec_bitStrsLE.comp Primrec.fst
  exact ((Primrec.list_getD []).comp hbl
    (Primrec.nat_mod.comp Primrec.snd (Primrec.list_length.comp hbl))).to₂

set_option maxHeartbeats 1000000 in
theorem primrec_lenRunP (κ : Bool) :
    Primrec fun q : BitStr × BitStr => lenRunP ld P q.1 q.2 κ := by
  have hxk : Primrec fun q : BitStr × BitStr => (encode (q.2, κ) : Data) :=
    Data.primrec_cons.comp (primrec_encode_bitStr.comp Primrec.snd)
      (Primrec.const (encode κ : Data))
  have hinput : Primrec fun q : BitStr × BitStr => (encode (q.1, q.2, κ) : Data) :=
    Data.primrec_cons.comp (primrec_encode_bitStr.comp Primrec.fst) hxk
  have hbudget : Primrec fun q : BitStr × BitStr => P.eval (q.1.length + q.2.length) :=
    (Cost.primrec_poly_eval P).comp (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd))
  exact Primrec.option_getD.comp
    (Primrec.option_map (Machine.primrec_runForD.comp (((Primrec.const ld).pair hinput).pair
      hbudget)) (Data.primrec_unaryToNat.comp Primrec.snd).to₂)
    (Primrec.const 0)

set_option maxHeartbeats 1000000 in
theorem primrec_lpRunP {α : Type*} [Primcodable α] {z x y aR bR : α → BitStr}
    (hz : Primrec z) (hx : Primrec x) (hy : Primrec y) (haR : Primrec aR) (hbR : Primrec bR) :
    Primrec fun a => lpRunP pd P (z a) (x a) (y a) (aR a) (bR a) := by
  have hebs : Primrec fun l : BitStr => (encode l : Data) := primrec_encode_bitStr
  have hinput : Primrec fun a => (encode (z a, x a, y a, aR a, bR a) : Data) :=
    Data.primrec_cons.comp (hebs.comp hz) (Data.primrec_cons.comp (hebs.comp hx)
      (Data.primrec_cons.comp (hebs.comp hy)
        (Data.primrec_cons.comp (hebs.comp haR) (hebs.comp hbR))))
  have hlen : Primrec fun a => (z a).length + (x a).length + (y a).length + (aR a).length +
      (bR a).length :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp hz) (Primrec.list_length.comp hx))
      (Primrec.list_length.comp hy)) (Primrec.list_length.comp haR))
      (Primrec.list_length.comp hbR)
  have hbudget := (Cost.primrec_poly_eval P).comp hlen
  exact Primrec.option_getD.comp
    (Primrec.option_map (Machine.primrec_runForD.comp (((Primrec.const pd).pair hinput).pair
      hbudget)) (primrec_bitsListD.comp Primrec.snd).to₂)
    (Primrec.const [])

theorem primrec_T : Primrec fun z : BitStr => P.eval z.length :=
  (Cost.primrec_poly_eval P).comp Primrec.list_length

theorem primrec_lenListP (κ : Bool) : Primrec fun z => lenListP ld P z κ := by
  have hT := primrec_T P
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.list_length.comp (Data.primrec_bitStrsLE.comp hT)))) ?_
  exact ((primrec_lenRunP ld P κ).comp (Primrec.fst.pair
    (primrec_qOfIdx.comp (hT.comp Primrec.fst) Primrec.snd))).to₂

set_option maxHeartbeats 1000000 in
theorem primrec_consAtP :
    Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr =>
      consAtP pd P q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2 := by
  have hz : Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hlR : Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr => q.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hv : Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hv' : Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr => q.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hγ : Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr => q.2 := Primrec.snd
  have hT : Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr => P.eval q.1.1.1.length :=
    (primrec_T P).comp hz
  have hlv : Primrec fun q : ((BitStr × List ℕ) × ℕ × ℕ) × BitStr => q.1.1.2.getD q.1.2.1 0 :=
    (Primrec.list_getD 0).comp hlR hv
  have hrun := primrec_lpRunP pd P hz (primrec_qOfIdx.comp hT hv) (primrec_qOfIdx.comp hT hv')
    (Primrec.list_take.comp hlv hγ) (Primrec.list_drop.comp hlv hγ)
  exact Primrec.list_map hrun
    ((hv.comp Primrec.fst).pair ((hv'.comp Primrec.fst).pair
      ((hγ.comp Primrec.fst).pair Primrec.snd))).to₂

set_option maxHeartbeats 1000000 in
theorem primrec_consTP_params :
    Primrec fun q : BitStr × List ℕ => consTP pd P q.1 q.2 := by
  have hγ : Primrec₂ fun (q : (BitStr × List ℕ) × ℕ × ℕ) (γ : BitStr) =>
      consAtP pd P q.1.1 q.1.2 q.2.1 q.2.2 γ := (primrec_consAtP pd P).to₂
  have hlen : Primrec fun q : (BitStr × List ℕ) × ℕ × ℕ =>
      Data.bitStrsOfLen (q.1.2.getD q.2.1 0 + q.1.2.getD q.2.2 0) :=
    Data.primrec_bitStrsOfLen.comp (Primrec.nat_add.comp
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
  have hV' : Primrec₂ fun (q : (BitStr × List ℕ) × ℕ) (v' : ℕ) =>
      (Data.bitStrsOfLen (q.1.2.getD q.2 0 + q.1.2.getD v' 0)).flatMap
        fun γ => consAtP pd P q.1.1 q.1.2 q.2 v' γ :=
    (Primrec.list_flatMap (hlen.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
      (hγ.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)))
        Primrec.snd).to₂).to₂
  have hrange : Primrec fun q : BitStr × List ℕ => List.range (2 * N (P.eval q.1.length)) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.list_length.comp (Data.primrec_bitStrsLE.comp ((primrec_T P).comp Primrec.fst))))
  have hV : Primrec₂ fun (q : BitStr × List ℕ) (v : ℕ) =>
      (List.range (2 * N (P.eval q.1.length))).flatMap fun v' =>
        (Data.bitStrsOfLen (q.2.getD v 0 + q.2.getD v' 0)).flatMap
          fun γ => consAtP pd P q.1 q.2 v v' γ :=
    (Primrec.list_flatMap (hrange.comp Primrec.fst) (hV'.comp Primrec.fst Primrec.snd).to₂).to₂
  exact (Primrec.list_flatMap hrange hV).of_eq fun q => rfl

set_option maxHeartbeats 1000000 in
/-- **The table is primitive recursive** in the input. -/
theorem primrec_tabOfP : Primrec (tabOfP sd ld pd P) := by
  have hT := primrec_T P
  have hN : Primrec fun z : BitStr => N (P.eval z.length) :=
    Primrec.list_length.comp (Data.primrec_bitStrsLE.comp hT)
  have hnV : Primrec fun z : BitStr => 2 * N (P.eval z.length) - 1 :=
    Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) hN) (Primrec.const 1)
  have hT' : Primrec fun z : BitStr => P.eval (z.length + P.eval z.length) :=
    (Cost.primrec_poly_eval P).comp (Primrec.nat_add.comp Primrec.list_length hT)
  have hsamp : Primrec fun q : BitStr × BitStr =>
      PolyVerifier.sampleC sd (P.eval (q.1.length + P.eval q.1.length)) q.1 q.2 :=
    (PolyVerifier.primrec_sampleC sd).comp (((hT'.comp Primrec.fst).pair Primrec.fst).pair
      Primrec.snd)
  have hw : Primrec fun z : BitStr => weightList (P.eval z.length)
      (fun r => qIdx (P.eval z.length) false
        (PolyVerifier.sampleC sd (P.eval (z.length + P.eval z.length)) z r).1)
      (fun r => qIdx (P.eval z.length) true
        (PolyVerifier.sampleC sd (P.eval (z.length + P.eval z.length)) z r).2) := by
    refine Primrec.list_map (Data.primrec_bitStrsOfLen.comp hT) ?_
    exact (((PolyVerifier.primrec_qIdx false).comp (hT.comp Primrec.fst)
      (Primrec.fst.comp hsamp)).pair
      (((PolyVerifier.primrec_qIdx true).comp (hT.comp Primrec.fst)
        (Primrec.snd.comp hsamp)).pair (Primrec.const 1))).to₂
  have hlR := primrec_lenListP ld P false
  have hlL := primrec_lenListP ld P true
  have hcons0 := (primrec_consTP_params pd P).comp (Primrec.id.pair hlR)
  have hcons : Primrec fun z => consTP pd P z (lenListP ld P z false) :=
    hcons0.of_eq fun z => rfl
  have htup := hnV.pair (hlR.pair (hlL.pair (hw.pair hcons)))
  have h2 := (Primrec.of_equiv_symm (e := TailoredGameData.equivTuple)).comp htup
  exact h2.of_eq fun z => rfl

end Primrec

/-! ## The vertices -/

/-- The question of the vertex `i` of `qEquiv` is the string it names. -/
theorem qOfIdx_qEquiv (T : ℕ) (i : Fin (2 * N T)) : qOfIdx T i = (qEquiv T i).2.1 := by
  have hi := PolyVerifier.qEquiv_apply T i
  have hmem : (qEquiv T i).2.1 ∈ Data.bitStrsLE T := (Data.mem_bitStrsLE _ _).2 (qEquiv T i).2.2
  have hlt : (Data.bitStrsLE T).idxOf (qEquiv T i).2.1 < N T := List.idxOf_lt_length_iff.2 hmem
  have hmod : (i : ℕ) % N T = (Data.bitStrsLE T).idxOf (qEquiv T i).2.1 := by
    rw [← hi, qIdx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [qOfIdx, hmod, List.getD_eq_getElem _ _ hlt, List.getElem_idxOf]

/-! ## The runs, under the efficiency bounds -/

namespace TPolyVerifier

variable (V : TPolyVerifier)

theorem lenIs_lenRunP {z x : BitStr} {κ : Bool}
    (hb : HaltsWithin V.len (encode (z, x, κ)) (V.bound.eval (z.length + x.length))) :
    V.LenIs z x κ (lenRunP (encode V.len) V.bound z x κ) := by
  obtain ⟨r, t, ht, h⟩ := hb
  refine ⟨t, r, h, ?_⟩
  rw [lenRunP, Machine.runForD_eq_some h ht]
  simp [unaryToNat_eq_length]

theorem lpIs_lpRunP {z x y aR bR : BitStr}
    (hb : HaltsWithin V.lp (encode (z, x, y, aR, bR))
      (V.bound.eval (z.length + x.length + y.length + aR.length + bR.length))) :
    V.LpIs z x y aR bR (lpRunP (encode V.lp) V.bound z x y aR bR) := by
  obtain ⟨r, t, ht, h⟩ := hb
  refine ⟨t, r, h, ?_⟩
  rw [lpRunP, Machine.runForD_eq_some h ht]
  rfl

theorem lenOf_eq_lenRunP {z : BitStr} (h : V.Efficient z) (x : BitStr) (κ : Bool) :
    V.lenOf z x κ = lenRunP (encode V.len) V.bound z x κ :=
  V.lenOf_eq (V.lenIs_lenRunP (h.len_time x κ))

theorem consOf_eq_lpRunP {z : BitStr} (h : V.Efficient z) (x y aR bR : BitStr) :
    V.consOf z x y aR bR = lpRunP (encode V.lp) V.bound z x y aR bR :=
  V.consOf_eq (fun κ => ⟨_, V.lenIs_lenRunP (h.len_time x κ)⟩)
    (fun κ => ⟨_, V.lenIs_lenRunP (h.len_time y κ)⟩) (V.lpIs_lpRunP (h.lp_time x y aR bR))

/-! ## The presentation -/

/-- The table of `V` on `z`. -/
def tabP (z : BitStr) : TailoredGameData :=
  tabOfP (encode V.sampler) (encode V.len) (encode V.lp) V.bound z

theorem computable_tabP : Computable V.tabP :=
  (primrec_tabOfP (encode V.sampler) (encode V.len) (encode V.lp) V.bound).to_comp

theorem tabP_nV (z : BitStr) : (V.tabP z).nV + 1 = 2 * N (V.B z) := V.toPoly.tab_nX z

/-- The vertices of the table, as the doubled questions: `PolyVerifier.eX`. -/
noncomputable def eP (z : BitStr) : Fin ((V.tabP z).nV + 1) ≃ Bool × Answers (V.B z) :=
  V.toPoly.eX z

theorem qOfIdx_eP (z : BitStr) (i : Fin ((V.tabP z).nV + 1)) :
    qOfIdx (V.B z) i = (V.eP z i).2.1 :=
  qOfIdx_qEquiv (V.B z) (finCongr (V.toPoly.tab_nX z) i)

theorem lenList_getD_eP (z : BitStr) (κ : Bool) (i : Fin ((V.tabP z).nV + 1)) :
    (lenListP (encode V.len) V.bound z κ).getD i 0 =
      lenRunP (encode V.len) V.bound z (V.eP z i).2.1 κ := by
  have hlt : (i : ℕ) < 2 * N (V.bound.eval z.length) := lt_of_lt_of_eq i.isLt (V.tabP_nV z)
  refine (Data.getD_range_map (fun v => lenRunP (encode V.len) V.bound z
    (qOfIdx (V.bound.eval z.length) v) κ) hlt).trans ?_
  show lenRunP (encode V.len) V.bound z (qOfIdx (V.B z) i) κ = _
  rw [qOfIdx_eP]

theorem mem_consTP (pd : Data) (P : Polynomial ℕ) (z : BitStr) (lR : List ℕ) (v v' : ℕ)
    (γ c : BitStr) :
    (v, v', γ, c) ∈ consTP pd P z lR ↔ v < 2 * N (P.eval z.length) ∧
      v' < 2 * N (P.eval z.length) ∧ γ.length = lR.getD v 0 + lR.getD v' 0 ∧
      c ∈ lpRunP pd P z (qOfIdx (P.eval z.length) v) (qOfIdx (P.eval z.length) v')
        (γ.take (lR.getD v 0)) (γ.drop (lR.getD v 0)) := by
  simp only [consTP, consAtP, List.mem_flatMap, List.mem_map, List.mem_range,
    Data.mem_bitStrsOfLen, Prod.mk.injEq]
  constructor
  · rintro ⟨v₀, hv₀, v₀', hv₀', γ₀, hγ₀, c₀, hc₀, rfl, rfl, rfl, rfl⟩
    exact ⟨hv₀, hv₀', hγ₀, hc₀⟩
  · rintro ⟨hv, hv', hγ, hc⟩
    exact ⟨v, hv, v', hv', γ, hγ, c, hc, rfl, rfl, rfl, rfl⟩

/-- **The table presents the doubled game**, on an efficient input. -/
theorem presents_tabP {z : BitStr} (h : V.Efficient z) :
    Presents (V.tabP z) (V.tgame z).doubled (V.eP z) := by
  have hR : ∀ (κ : Bool) (i : Fin ((V.tabP z).nV + 1)),
      (lenListP (encode V.len) V.bound z κ).getD i 0 = V.lenOf z (V.eP z i).2.1 κ := by
    intro κ i
    rw [lenList_getD_eP, V.lenOf_eq_lenRunP h]
  refine ⟨fun i j => ?_, fun i => hR false i, fun i => hR true i, fun i j γ c hγ => ?_⟩
  · exact V.toPoly.mu_clause h.sampler_runs i j
  · have hi : (i : ℕ) < 2 * N (V.B z) := lt_of_lt_of_eq i.isLt (V.tabP_nV z)
    have hj : (j : ℕ) < 2 * N (V.B z) := lt_of_lt_of_eq j.isLt (V.tabP_nV z)
    show (↑i, ↑j, γ, c) ∈ consTP (encode V.lp) V.bound z (lenListP (encode V.len) V.bound z false)
      ↔ c ∈ V.consOf z (V.eP z i).2.1 (V.eP z j).2.1
        (γ.take (V.lenOf z (V.eP z i).2.1 false)) (γ.drop (V.lenOf z (V.eP z i).2.1 false))
    rw [mem_consTP, hR false i, hR false j, V.consOf_eq_lpRunP h]
    show _ ∧ _ ∧ _ ∧ c ∈ lpRunP _ _ z (qOfIdx (V.B z) i) (qOfIdx (V.B z) j) _ _ ↔ _
    rw [qOfIdx_eP, qOfIdx_eP]
    exact ⟨fun h => h.2.2.2, fun h' => ⟨hi, hj, hγ, h'⟩⟩

end TPolyVerifier

/-- **`TMIP* ⊆ TMIP*_computable`**: the table of the doubled game is a computable map with a
perfect ZPC strategy on the members and the value of the game off them. -/
theorem TMIPStar.toComputable {L : Set BitStr} (h : TMIPStar L) : TMIPStarComputable L := by
  obtain ⟨V, heff, hgap⟩ := h
  refine ⟨V.tabP, V.computable_tabP, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · exact (V.presents_tabP (heff z)).hasPerfectZPC (TailoredGame.doubled_μ_self _)
      ((hgap z).1 hz)
  · rw [(V.presents_tabP (heff z)).quantumValue_eq (TailoredGame.doubled_μ_self _),
      TailoredGame.quantumValue_doubled_eq_valStar]
    exact (hgap z).2 hz

/-- **`TMIP* ⊆ RE`** (II:1838), for the paper's class. -/
theorem TMIPStar.isRE {L : Set BitStr} (h : TMIPStar L) : IsRE L :=
  h.toComputable.isRE

end MIPRE.Tailored

end
