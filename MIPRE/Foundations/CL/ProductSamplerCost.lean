/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.ProductSamplerProg
import MIPRE.Foundations.Pipeline.PowDomRun

/-!
# The running time of the product sampler

`CL.TypedSampler.prodDirect` runs the parameter routine of its direct half through the universal
machine, then routes the query: at most one call to the typed half's program, again through the
universal machine, on a query at most linearly larger than the typed query (`route_call_size`),
and polynomial-time work on the parameters around it. So its running time is dominated, in the
sense of `MIPRE.Pipeline.PDom`, as soon as the parameter routine's is and the typed half runs
within a monomial coefficient at degree `e (K + 1)` (`prog_time`), on every input, well formed
or not.
-/

namespace MIPRE.CL.ProductSampler

open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline

theorem size_treeHead_le (d : Data) : (treeHead d).size ≤ d.size := by
  cases d with
  | nil => exact le_refl _
  | cons a b => simp only [treeHead_cons, Data.size_cons]; omega

theorem size_treeTail_le (d : Data) : (treeTail d).size ≤ d.size := by
  cases d with
  | nil => exact le_refl _
  | cons a b => simp only [treeTail_cons, Data.size_cons]; omega

theorem length_rawList_le (d : Data) : (rawList d).length ≤ d.size := by
  induction d with
  | nil => simp [rawList]
  | cons a b _ ihb => simp only [rawList, List.length_cons, Data.size_cons]; omega

theorem length_readBits_le (d : Data) : (readBits d).length ≤ d.size := by
  change ((rawList d).map rawTruth).length ≤ _
  rw [List.length_map]
  exact length_rawList_le d

variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)

/-- `A`'s half of a vector read off the query is no longer than the query. -/
theorem length_leftBits_le (l : PolyTimeFun Data BitStr) (x : Data) :
    (leftBits D l x).length ≤ (l x).length := by
  simp only [leftBits, comp_apply, pair_apply, reverse_apply, drop_apply, List.length_reverse,
    List.length_drop]
  omega

/-- The vectors of the parsed query are no longer than the typed query. -/
theorem length_uD_le (pdn H nD' q : Data) :
    (uD (.cons pdn (.cons H (.cons nD' q)))).length ≤ q.size := by
  simp only [uD, parsedQ, pU, comp_apply, parse, pair_apply, ap₂_apply, treePair_apply, nD, qD,
    queryD, treeTail_cons, treeHead_cons, fst_apply, snd_apply]
  refine (length_readBits_le _).trans ?_
  have h1 := size_treeHead_le (treeTail (treeTail (treeTail (treeTail q))))
  have h2 := size_treeTail_le (treeTail (treeTail (treeTail q)))
  have h3 := size_treeTail_le (treeTail (treeTail q))
  have h4 := size_treeTail_le (treeTail q)
  have h5 := size_treeTail_le q
  omega

theorem length_yD_le (pdn H nD' q : Data) :
    (yD (.cons pdn (.cons H (.cons nD' q)))).length ≤ q.size := by
  simp only [yD, parsedQ, pY, comp_apply, parse, pair_apply, ap₂_apply, treePair_apply, nD, qD,
    queryD, treeTail_cons, treeHead_cons, snd_apply]
  refine (length_readBits_le _).trans ?_
  have h1 := size_treeTail_le (treeTail (treeTail (treeTail (treeTail q))))
  have h2 := size_treeTail_le (treeTail (treeTail (treeTail q)))
  have h3 := size_treeTail_le (treeTail (treeTail q))
  have h4 := size_treeTail_le (treeTail q)
  have h5 := size_treeTail_le q
  omega

/-- The size of `A`'s query at a level `j`, when `j ≤ ℓa`. -/
theorem size_queryA_le (j : PolyTimeFun Data ℕ) (ap pp : Prog) (ℓa n : ℕ) (pdn q : Data)
    (hj : j (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) ≤ ℓa) :
    (queryA D j (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q)))).size ≤
      esize n + 12 * q.size + 4 * ℓa + 20 := by
  set x : Data := .cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))
  have hu := (esize_bitStr_le (leftBits D uD x)).trans
    (by
      have := length_leftBits_le D uD x
      have : (uD x).length ≤ q.size := length_uD_le pdn _ _ q
      omega :
      4 * (leftBits D uD x).length + 1 ≤ 4 * q.size + 1)
  have hy := (esize_bitStr_le (leftBits D yD x)).trans
    (by
      have := length_leftBits_le D yD x
      have : (yD x).length ≤ q.size := length_yD_le pdn _ _ q
      omega :
      4 * (leftBits D yD x).length + 1 ≤ 4 * q.size + 1)
  have hjs := (esize_nat_le_four (j x)).trans (by omega : 4 * j x + 1 ≤ 4 * ℓa + 1)
  have h1 := size_treeHead_le (treeHead q)
  have h2 := size_treeHead_le q
  have h3 := size_treeHead_le (treeTail q)
  have h4 := size_treeTail_le q
  have h5 := size_treeHead_le (treeTail (treeTail q))
  have h6 := size_treeTail_le (treeTail q)
  simp only [queryA, ap₂_apply, treePair_apply, comp_apply, encoded_apply, nD, tagD, qD,
    queryD, treeTail_cons, treeHead_cons, Data.size_cons, x] at hu hy hjs ⊢
  change esize n + ((treeHead (treeHead q)).size + ((treeHead (treeTail q)).size +
    ((treeHead (treeTail (treeTail q))).size + (esize (j _) + (esize (leftBits D uD _) +
      esize (leftBits D yD _) + 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  omega

/-- **A forwarded query is linear in the typed query**: the router calls `A`'s program on the
index and a query at most linearly larger than the typed query, whatever the input. -/
theorem route_call_size (ap pp : Prog) (ℓa n : ℕ) (pdn q payload : Data)
    (h : route B D (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) =
      (true, payload)) :
    ∃ a ctx, payload = .cons (.cons (encode ap) a) ctx ∧
      a.size ≤ esize n + 12 * q.size + 4 * ℓa + 20 := by
  set x : Data := .cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q)) with hx
  have hlev : levelA x = ℓa := by
    simp only [levelA, comp_apply, x, treeTail_cons, treeHead_cons, encode_prod, readNat_encode]
  have hprog : progD x = encode ap := by
    simp only [progD, comp_apply, x, treeTail_cons, treeHead_cons, encode_prod]
  simp only [route, PolyTimeFun.ite_apply] at h
  split_ifs at h with h1 h2 h3
  · have hp := (Prod.mk.inj h).2
    simp only [ap₂_apply, treePair_apply, hprog, const_apply] at hp
    subst hp
    refine ⟨_, _, rfl, ?_⟩
    simp only [nD, x, comp_apply, treeHead_cons, treeTail_cons, Data.size_cons, Data.size_nil]
    change esize n + 1 + 1 ≤ _
    omega
  · have hp := (Prod.mk.inj h).2
    simp only [ap₂_apply, treePair_apply, hprog] at hp
    subst hp
    refine ⟨_, _, rfl, size_queryA_le D levA ap pp ℓa n pdn q ?_⟩
    show levA x ≤ ℓa
    have : levA x ≤ levelA x := by
      simp only [levA, PolyTimeFun.ite_apply, ap₂_apply, leNat_apply, decide_eq_true_eq]
      split_ifs with h4
      · exact h4
      · exact le_rfl
    rwa [hlev] at this
  · have hp := (Prod.mk.inj h).2
    simp only [ap₂_apply, treePair_apply, hprog] at hp
    subst hp
    refine ⟨_, _, rfl, size_queryA_le D lev ap pp ℓa n pdn q ?_⟩
    simpa [ap₂_apply, leNat_apply, hlev] using h3
  · simp [direct] at h

/-- The explicit bound on the routed stage: the router, one call through the universal machine to
`A`'s program on a query of size at most `esize n + 12 |q| + 4 ℓa + 20`, and the post-processing. -/
noncomputable def stageBound (ap : Prog) (ℓa n : ℕ) (xs qs BA k : ℕ) : ℕ :=
  let Rt := (route B D).timeBound.eval xs
  let tU := selfUniversal.bound.eval
    (esize ap + (esize n + 12 * qs + 4 * ℓa + 20) + BA * (esize n + 12 * qs + 4 * ℓa + 21) ^ k)
  4 * Rt + 3 * (esize ap + esize n + 12 * qs + 4 * ℓa + 21) + 2 * tU +
    post.timeBound.eval (Rt + tU + 1) + 22

/-- **The routed stage halts within `stageBound`** on every input, when `A`'s program runs within
`BA (|d| + 1)^k` at the index. -/
theorem stage_time (ap pp : Prog) (ℓa n : ℕ) (pdn q : Data) (BA k : ℕ)
    (hA : ∀ d, HaltsWithin ap (.cons (encode n) d) (BA * (d.size + 1) ^ k)) :
    ∃ r t, t ≤ stageBound B D ap ℓa n
        (Data.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))).size q.size BA k ∧
      (stage B D).Runs (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) r t := by
  set x : Data := .cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q)) with hx
  have hRt := (route B D).esize_apply_le x
  simp only [esize_data] at hRt
  cases h : route B D x with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_direct_cost (route B D) selfUniversal.univ post x
        payload h
      refine ⟨payload, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_false, esize_data] at hRt ht
      simp only [stageBound]
      omega
    | true =>
      obtain ⟨a, ctx, rfl, ha⟩ := route_call_size B D ap pp ℓa n pdn q _ h
      obtain ⟨d, ctx', hshape⟩ := route_call_shape B D pdn (encode (ap, ℓa, pp)) (encode n) q _ h
      simp only [treeHead, encode_prod] at hshape
      have hshape' := Data.cons.inj hshape
      obtain ⟨hl, rfl⟩ := hshape'
      obtain ⟨_, rfl⟩ := Data.cons.inj hl
      obtain ⟨r, tA, htA, hArun⟩ := hA d
      obtain ⟨tU, htU, hU⟩ := selfUniversal.time_le ap _ r tA hArun
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_indirect_cost (route B D) selfUniversal.closed post
        x _ ctx r tU h hU
      refine ⟨_, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_true, esize_data, Data.size_cons] at hRt ht ha
      have e1 : (encode ap : Data).size = esize ap := rfl
      have e2 : (encode n : Data).size = esize n := rfl
      have hd : d.size + 1 ≤ esize n + 12 * q.size + 4 * ℓa + 21 := by omega
      have htA' : tA ≤ BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ k :=
        htA.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd k))
      have hrs : r.size ≤ tU := hU.size_le
      have htU' := htU.trans (polynomial_eval_mono selfUniversal.bound (show esize ap +
        (Data.cons (encode n) d).size + tA ≤ esize ap + (esize n + 12 * q.size + 4 * ℓa + 20) +
          BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ k by
        simp only [Data.size_cons]; omega))
      have hpost := polynomial_eval_mono post.timeBound
        (show ctx.size + r.size + 1 ≤ (route B D).timeBound.eval x.size +
          selfUniversal.bound.eval (esize ap + (esize n + 12 * q.size + 4 * ℓa + 20) +
            BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ k) + 1 by omega)
      simp only [stageBound]
      omega

/-- **The running time of the product sampler's program**, on every input: dominated as soon as
the parameter routine runs within a dominated time, the two programs have dominated sizes, and
`A`'s program runs within a monomial coefficient at degree `eA (K + 1)`. -/
theorem prog_time (ℓa cp mp ep cs ms es cA mA eA : ℕ) : ∃ C M E, ∀ {W K : ℕ} (ap pp : Prog)
    (n : ℕ) (pdn : Data) (BA : ℕ), n ≤ W →
    (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cp mp ep pp (encode n) pdn) →
    (∀ {X : ℕ}, 1 ≤ X → PDom W X K cs ms es (esize ap + esize pp)) →
    BA ≤ cA * (W + 1) ^ mA →
    (∀ d, HaltsWithin ap (.cons (encode n) d) (BA * (d.size + 1) ^ (eA * (K + 1)))) →
    ∀ q : Data, ∃ r t, PDom W (q.size + 1) K C M E t ∧
      (prog B D ap ℓa pp).Runs (.cons (encode n) q) r t := by
  exact ⟨_, _, _, fun {W K} ap pp n pdn BA hn hpp hsz hBA hA q => by
    have hX : 1 ≤ q.size + 1 := by omega
    obtain ⟨tp, htp, hprun⟩ := hpp hX
    have hs := hsz hX
    have en := esize_nat_le_four n
    have el := esize_nat_le_four ℓa
    have hpdn : PDom W (q.size + 1) K cp mp ep pdn.size := htp.of_le hprun.size_le
    have hnW : PDom W (q.size + 1) K _ _ _ (esize n) := PDom.ofAffine (a := 4) (b := 1) (by omega)
    have hq : PDom W (q.size + 1) K _ _ _ q.size := PDom.ofLeX (by omega)
    -- stage 0: the parameters
    set x0 : Data := .cons (encode (ap, ℓa, pp)) (.cons (encode n) q) with hx0def
    have hx0 : x0.size = esize ap + esize ℓa + esize pp + esize n + q.size + 4 := by
      simp only [x0, Data.size_cons, encode_prod]
      change esize ap + (esize ℓa + esize pp + 1) + 1 + (esize n + q.size + 1) + 1 = _
      omega
    have hX0 := (((hs.add hX hnW).add hX hq).add hX (PDom.const (esize ℓa + 4))).of_le
      (show x0.size ≤ esize ap + esize pp + esize n + q.size + (esize ℓa + 4) by omega)
    obtain ⟨tU0, htU0, hU0⟩ := selfUniversal.time_le pp (encode n) pdn tp hprun
    obtain ⟨t0, ht0, h0⟩ := Prog.routeOneCall_indirect_cost route0 selfUniversal.closed post0 x0
      (.cons (encode pp) (encode n)) x0 pdn tU0 rfl hU0
    have hpost0 : post0 (x0, pdn) = .cons pdn x0 := rfl
    rw [hpost0] at h0
    -- the routed stage
    obtain ⟨r, t1, ht1, h1⟩ := stage_time B D ap pp ℓa n pdn q BA (eA * (K + 1)) hA
    rw [← hx0def] at ht1 h1
    refine ⟨r, _, ?_, hardcode_time (core_closed B D)
      (show (core B D).Runs _ _ _ from seqProg_runs (stage_closed B D) h0 h1)⟩
    -- the accounting
    have hU0' : PDom W (q.size + 1) K _ _ _
        (selfUniversal.bound.eval (esize ap + esize pp + esize n + 1 + tp)) :=
      (((hs.add hX hnW).add hX (PDom.const 1)).add hX htp).poly hX selfUniversal.bound
    have hR0 := hX0.poly hX route0.timeBound
    have hP0 := ((hX0.add hX hpdn).add hX (PDom.const 1)).poly hX post0.timeBound
    have hx1 : PDom W (q.size + 1) K _ _ _ (pdn.size + x0.size + 1) :=
      (hpdn.add hX hX0).add hX (PDom.const 1)
    have hRt := hx1.poly hX (route B D).timeBound
    have hA' : PDom W (q.size + 1) K _ _ _
        (BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ (eA * (K + 1))) :=
      PDom.ofCallPow (c₁ := 4 * ℓa + 37) (m₁ := 1) (e₁ := 1) hBA
        (by
          simp only [pow_one]
          have h37 : 37 * (W + 1) * (q.size + 1) ≤ (4 * ℓa + 37) * (W + 1) * (q.size + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
          have hWq : W + q.size + 1 ≤ (W + 1) * (q.size + 1) := by nlinarith
          have h4l : 4 * ℓa ≤ 4 * ℓa * ((W + 1) * (q.size + 1)) :=
            Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
          have := Nat.mul_le_mul_left 37 hWq
          nlinarith) le_rfl
    have hlin : PDom W (q.size + 1) K _ _ _ (esize n + 12 * q.size + 4 * ℓa + 21) :=
      ((hnW.add hX ((PDom.const 12).mul hq)).add hX (PDom.const (4 * ℓa + 21)))
    have hU1 := (((hs.add hX hlin).add hX hA')).poly hX selfUniversal.bound
    have hP1 := ((hRt.add hX hU1).add hX (PDom.const 1)).poly hX post.timeBound
    have htot := (((((((((((PDom.const 3).mul hR0).add hX ((PDom.const 12).mul hX0)).add hX
      ((PDom.const 3).mul hpdn)).add hX ((PDom.const 3).mul hU0')).add hX
      ((PDom.const 3).mul hP0)).add hX ((PDom.const 4).mul hRt)).add hX
      ((PDom.const 3).mul hs)).add hX ((PDom.const 3).mul hlin)).add hX
      ((PDom.const 2).mul hU1)).add hX ((PDom.const 3).mul hP1)).add hX (PDom.const 200)
    refine htot.of_le ?_
    have hU0le : tU0 ≤ selfUniversal.bound.eval (esize ap + esize pp + esize n + 1 + tp) := by
      refine htU0.trans (polynomial_eval_mono _ ?_)
      change esize pp + (esize n) + tp ≤ _
      omega
    have hpdn_le : pdn.size ≤ tU0 := hU0.size_le
    have e1 : (encode pp : Data).size = esize pp := rfl
    have e2 : (encode n : Data).size = esize n := rfl
    have hP0le := polynomial_eval_mono post0.timeBound
      (show x0.size + pdn.size + 1 ≤ x0.size + pdn.size + 1 from le_rfl)
    simp only [stageBound, Data.size_cons] at ht1
    have hUm := polynomial_eval_mono selfUniversal.bound (show esize ap +
      (esize n + 12 * q.size + 4 * ℓa + 20) + BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^
        (eA * (K + 1)) ≤ esize ap + esize pp + (esize n + 12 * q.size + 4 * ℓa + 21) +
      BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ (eA * (K + 1)) by omega)
    have hPm := polynomial_eval_mono post.timeBound (show
      (route B D).timeBound.eval (pdn.size + x0.size + 1) + selfUniversal.bound.eval (esize ap +
        (esize n + 12 * q.size + 4 * ℓa + 20) + BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^
          (eA * (K + 1))) + 1 ≤
      (route B D).timeBound.eval (pdn.size + x0.size + 1) + selfUniversal.bound.eval (esize ap +
        esize pp + (esize n + 12 * q.size + 4 * ℓa + 21) +
          BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ (eA * (K + 1))) + 1 by omega)
    simp only [Data.size_cons] at ht0
    have hH : (encode (ap, ℓa, pp) : Data).size = esize ap + esize ℓa + esize pp + 2 := by
      simp only [encode_prod, Data.size_cons]
      change esize ap + (esize ℓa + esize pp + 1) + 1 = _
      omega
    simp only [Data.size_cons]
    rw [hH]
    omega⟩

end MIPRE.CL.ProductSampler
