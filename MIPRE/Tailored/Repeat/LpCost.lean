/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.LpSpec
public import MIPRE.Tailored.Repeat.LenCost

@[expose] public section

/-!
# The running time of the repeated linear-constraints processor

`repLp_timeBound`: with the input sampler, calculator and processor within `R` at index `n`, the
repeated processor halts on every input `(n, d)` within `c (W + 1)^m (|d| + 1)^{e (R.k + 1)}`,
along the stages of `lpCore_runsLe`, as `repLen_timeBound` does for the calculator. Every query
to the input programs is of size linear in `|d|` (`mem_lpLenQs`, `mem_lpPQs`): the blocks of the
questions and the readable answers are pieces of the input.
-/

namespace MIPRE.Tailored.RepProg

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL Calls Repeat

/-! ## Sizes -/

theorem size_treeTail_le (d : Data) : (treeTail d).size ≤ d.size := by
  cases d with
  | nil => exact le_rfl
  | cons a b => simp only [treeTail_cons, size_cons]; omega

theorem length_readBits_le (d : Data) : (Detyping.Program.readBits d).length ≤ d.size := by
  unfold Detyping.Program.readBits
  simp only [comp_apply, map_apply, ofEncodeEq_apply, List.length_map]
  exact length_rawList_le _

theorem length_readX_le (d : Data) : (readX d).length ≤ d.size :=
  (length_readBits_le _).trans (size_treeHead_le d)

theorem length_readY_le (d : Data) : (readY d).length ≤ d.size :=
  (length_readBits_le _).trans ((size_treeHead_le _).trans (size_treeTail_le d))

theorem length_readAR_le (d : Data) : (readAR d).length ≤ d.size :=
  (length_readBits_le _).trans ((size_treeHead_le _).trans ((size_treeTail_le _).trans
    (size_treeTail_le d)))

theorem length_readBR_le (d : Data) : (readBR d).length ≤ d.size :=
  (length_readBits_le _).trans ((size_treeTail_le _).trans ((size_treeTail_le _).trans
    (size_treeTail_le d)))

theorem esize_block_le {l : List Bool} {s k : ℕ} {xi : BitStr} (h : xi ∈ blocks l s k) :
    esize xi ≤ 4 * l.length + 1 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 h
  refine (esize_bitStr_le _).trans ?_
  have : (Cost.Data.chunk s i l).length ≤ l.length := by
    simp only [Cost.Data.chunk, List.length_take, List.length_drop]; omega
  omega

/-- Every query to the input calculator is `(n, xᵢ, κ)` with `xᵢ` of size linear in the input. -/
theorem mem_lpLenQs {st : LpSt} {q : Data} (hq : q ∈ lpLenQs st) :
    ∃ (xi : BitStr) (b : Bool), q = encode (st.1.1.2.1, xi, b) ∧
      esize xi ≤ 4 * st.1.1.2.2.size + 1 := by
  rcases List.mem_append.1 hq with h | h <;>
  · obtain ⟨xi, hxi, b, rfl⟩ := mem_lenQueries h
    refine ⟨xi, b, rfl, ?_⟩
    first
      | exact (esize_block_le hxi).trans (by have := length_readX_le st.1.1.2.2; omega)
      | exact (esize_block_le hxi).trans (by have := length_readY_le st.1.1.2.2; omega)

/-- Every query to the input processor is `(n, xᵢ, yᵢ, a^R_i, b^R_i)` with every component of size
linear in the input. -/
theorem mem_lpPQs {st : LpSt} {rs : List Data} {q : Data} (hq : q ∈ lpPQs st rs) :
    ∃ xi yi a b : BitStr, q = encode (st.1.1.2.1, xi, yi, a, b) ∧
      esize xi ≤ 4 * st.1.1.2.2.size + 1 ∧ esize yi ≤ 4 * st.1.1.2.2.size + 1 ∧
      esize a ≤ 4 * st.1.1.2.2.size + 1 ∧ esize b ≤ 4 * st.1.1.2.2.size + 1 := by
  unfold lpPQs lpQueries at hq
  obtain ⟨⟨⟨xi, yi⟩, p⟩, hmem, rfl⟩ := List.mem_map.1 hq
  have h1 := List.of_mem_zip hmem
  have h2 := List.of_mem_zip h1.1
  have hA := length_readAR_le st.1.1.2.2
  have hB := length_readBR_le st.1.1.2.2
  have hX := length_readX_le st.1.1.2.2
  have hY := length_readY_le st.1.1.2.2
  have ex := esize_block_le h2.1
  have ey := esize_block_le h2.2
  refine ⟨xi, yi, _, _, rfl, by omega, by omega, (esize_bitStr_le _).trans ?_,
    (esize_bitStr_le _).trans ?_⟩
  · simp only [List.length_take, List.length_drop]; omega
  · simp only [List.length_take, List.length_drop]; omega

@[simp] theorem length_lpLenQs (st : LpSt) : (lpLenQs st).length = 4 * st.2.length := by
  simp [lpLenQs, lenQueries, blocksX, blocksY]; omega

theorem length_lpPQs_le (st : LpSt) (rs : List Data) : (lpPQs st rs).length ≤ st.2.length := by
  simp [lpPQs, lpQueries, blocksX]

/-! ## The cost of the core, dominated -/

theorem esize_lpPads_le (rs : List Data) (k : ℕ) :
    esize (lpPads rs k) ≤ lpPadsF.timeBound.eval (esize (rs, unary k)) := by
  have := lpPadsF.esize_apply_le (rs, unary k)
  simpa using this

/-- **The cost of the core is dominated.** -/
theorem dom_lpCoreCost (cd md ed cT₁ mT₁ eT₁ cZ₁ mZ₁ eZ₁ cT₂ mT₂ eT₂ cZ₂ mZ₂ eZ₂ : ℕ) :
    ∃ c m e, ∀ (W X K : ℕ) {sp lp pp : Prog} {lam tau n : ℕ} {d : Data} {s Td T₁ Z₁ T₂ Z₂ : ℕ}
      {rs₁ rs₂ : List Data},
    1 ≤ X → 1 ≤ W → d.size + 1 ≤ X → esize sp ≤ W → esize lp ≤ W → esize pp ≤ W → lam ≤ W →
    tau ≤ W → n ≤ W → s ≤ W → Repetition.reps lam tau n ≤ W →
    Dom W X K cd md ed Td → Dom W X K cT₁ mT₁ eT₁ T₁ → Dom W X K cZ₁ mZ₁ eZ₁ Z₁ →
    Dom W X K cT₂ mT₂ eT₂ T₂ → Dom W X K cZ₂ mZ₂ eZ₂ Z₂ →
    (list (lpLenQs (lpSt sp lp pp lam tau n d s))).size ≤ Z₁ → (list rs₁).size ≤ Z₁ →
    (list (lpPQs (lpSt sp lp pp lam tau n d s) rs₁)).size ≤ Z₂ → (list rs₂).size ≤ Z₂ →
    Dom W X K c m e (lpCoreCost sp lp pp lam tau n d s Td T₁ Z₁ T₂ Z₂ rs₁ rs₂) := by
  obtain ⟨cA, mA, eA, hA⟩ := dom_poly lpA.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cB, mB, eB, hB⟩ := dom_poly lpB.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cC, mC, eC, hC⟩ := dom_poly lpC.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cD, mD, eD, hD⟩ := dom_poly lpD.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cE, mE, eE, hE⟩ := dom_poly lpE.timeBound (30 + 10 + 30 + cZ₁) (max 1 mZ₁) (max 1 eZ₁)
  obtain ⟨cP, mP, eP, hP⟩ := dom_poly lpPadsF.timeBound (30 + 10 + 30 + cZ₁) (max 1 mZ₁)
    (max 1 eZ₁)
  obtain ⟨cF, mF, eF, hF⟩ := dom_poly lpF.timeBound (cP + cZ₂ + 1) (max (max mP mZ₂) 0)
    (max (max eP eZ₂) 0)
  obtain ⟨cu, mu, eu, hu⟩ := dom_toUnaryCost
  obtain ⟨cdm, mdm, edm, hdm⟩ := dom_dimCost
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_mapCallCost 1 0 0 cd md ed (30 + 10 + 30) 1 1 (30 + 10 + 30) 1 1
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_mapCallCost (30 + 10 + 30) 1 1 cT₁ mT₁ eT₁ (30 + 10 + 30) 1 1
    cZ₁ mZ₁ eZ₁
  obtain ⟨c₃, m₃, e₃, h₃⟩ := dom_mapCallCost (30 + 10 + 30) 1 1 cT₂ mT₂ eT₂ (30 + 10 + 30) 1 1
    cZ₂ mZ₂ eZ₂
  exact ⟨_, _, _, fun W X K {sp lp pp lam tau n d s Td T₁ Z₁ T₂ Z₂ rs₁ rs₂} hX hW1 hd hsp hlp hpp
      hlam htau hn hs hk hTd hT₁ hZ₁ hT₂ hZ₂ hq₁ hr₁ hq₂ hr₂ => by
    have small : ∀ {y : ℕ}, y ≤ 30 * W + 10 * X + 30 → Dom W X K (30 + 10 + 30) 1 1 y :=
      fun hy => Dom.ofLin hX hy
    have elam := esize_nat_le' lam
    have etau := esize_nat_le' tau
    have en := esize_nat_le' n
    have es := esize_nat_le' s
    have ek := esize_nat_le' (Repetition.reps lam tau n)
    have e1 : esize (1 : ℕ) ≤ 5 := by decide
    have edim := esize_dimension
    have es' : (encode s : Data).size ≤ 4 * W + 1 := by change esize s ≤ _; omega
    have ek' : (encode (Repetition.reps lam tau n) : Data).size ≤ 4 * W + 1 := by change esize (Repetition.reps lam tau n) ≤ _; omega
    have hsp' : (encode sp : Data).size ≤ W := hsp
    have hlp' : (encode lp : Data).size ≤ W := hlp
    have hpp' : (encode pp : Data).size ≤ W := hpp
    have eqd : (encode (n, CL.Sampler.Query.dimension) : Data).size ≤ 4 * W + 22 := by
      change esize (n, CL.Sampler.Query.dimension) ≤ _
      simp only [esize_prod]; omega
    have ea : esize ((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn) ≤ 15 * W + X + 10 := by
      simp only [esize_prod, esize_data]; omega
    have eus : esize (((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn), unary s) ≤
        17 * W + X + 12 := by
      rw [esize_prod, esize_unary]; omega
    have est : esize (lpSt sp lp pp lam tau n d s) ≤ 19 * W + X + 14 := by
      rw [lpSt, esize_prod, esize_unary]; omega
    have hlen₁ : (lpLenQs (lpSt sp lp pp lam tau n d s)).length = 4 * Repetition.reps lam tau n :=
      (length_lpLenQs _).trans (by simp)
    have hlen₂ : (lpPQs (lpSt sp lp pp lam tau n d s) rs₁).length ≤ Repetition.reps lam tau n :=
      (length_lpPQs_le _ rs₁).trans (by simp)
    have hrs₁ : esize rs₁ ≤ Z₁ := hr₁
    have hrs₂ : esize rs₂ ≤ Z₂ := hr₂
    have dpads := hP W X K hX (y := esize (rs₁, unary (Repetition.reps lam tau n)))
      (((small (y := 2 * (Repetition.reps lam tau n) + 2) (by omega)).add hX hZ₁).of_le
        (by simp only [esize_prod, esize_unary]; omega))
    have epads := esize_lpPads_le rs₁ (Repetition.reps lam tau n)
    -- the terms
    have t1 := hA W X K hX (small (y := esize ((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn))
      (by omega))
    have t2a := small (y := (encode ((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn) : Data).size)
      (by change esize _ ≤ _; omega)
    have t2b := small (y := (Data.cons (encode sp)
      (list [(encode (n, CL.Sampler.Query.dimension) : Data)])).size)
      (by simp only [size_cons, size_list_cons, list_nil, size_nil]; omega)
    have t2c := h₁ W X K (M := 1) (T := Td) (C := (encode sp : Data).size)
      (Z := (list [(encode (n, CL.Sampler.Query.dimension) : Data)]).size +
        (list [(encode s : Data)]).size + 1) hX (Dom.const 1) hTd (small (by omega))
      (small (by simp only [size_list_cons, list_nil, size_nil]; omega))
    have t3 := hB W X K hX (small (y := esize ((((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn)),
      [(encode s : Data)])) (by
        simp only [esize_prod, esize_data]
        change _ + (list [(encode s : Data)]).size + 1 ≤ _
        simp only [size_list_cons, list_nil, size_nil]; omega))
    have t4a := small (y := (encode s : Data).size) (by omega)
    have t4b := hu W X K hX hs
    have t5 := hC W X K hX (small (y := esize (((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn),
      unary s)) (by omega))
    have t6a := small (y := (encode (((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn), unary s) :
      Data).size) (by change esize _ ≤ _; omega)
    have t6b := small (y := (encode ((1 : ℕ), lam, n, tau) : Data).size)
      (by change esize _ ≤ _; simp only [esize_prod]; omega)
    have t6c := hdm W X K hX htau (L := Nat.size lam + Nat.size n) (Λ := esize lam) (N := esize n)
      (Ssz := esize (1 : ℕ)) (by have := nat_size_le_self lam; have := nat_size_le_self n; omega)
      (by omega) (by omega) (by omega)
    have t7a := small (y := (encode (Repetition.reps lam tau n) : Data).size) (by omega)
    have t7b := hu W X K hX hk
    have t8 := hD W X K hX (small (y := esize (lpSt sp lp pp lam tau n d s)) (by omega))
    have t9a := small (y := (encode (lpSt sp lp pp lam tau n d s) : Data).size)
      (by change esize _ ≤ _; omega)
    have t9b : Dom W X K _ _ _ (Data.cons (encode lp)
        (list (lpLenQs (lpSt sp lp pp lam tau n d s)))).size :=
      ((small (y := esize lp + 1) (by omega)).add hX hZ₁).of_le
        (by simp only [size_cons]; have : (encode lp : Data).size = esize lp := rfl; omega)
    have t9c := h₂ W X K (M := (lpLenQs (lpSt sp lp pp lam tau n d s)).length) (T := T₁)
      (C := (encode lp : Data).size) (Z := Z₁) hX (small (by omega)) hT₁
      (small (by omega)) hZ₁
    have t10 := hE W X K hX (y := esize (lpSt sp lp pp lam tau n d s, rs₁))
      (((small (y := esize (lpSt sp lp pp lam tau n d s) + 1) (by omega)).add hX hZ₁).of_le
        (by simp only [esize_prod] at *; omega))
    have t11a : Dom W X K _ _ _ (encode (lpPads rs₁ (Repetition.reps lam tau n)) : Data).size := dpads.of_le epads
    have t11b : Dom W X K _ _ _ (Data.cons (encode pp)
        (list (lpPQs (lpSt sp lp pp lam tau n d s) rs₁))).size :=
      ((small (y := esize pp + 1) (by omega)).add hX hZ₂).of_le
        (by simp only [size_cons]; have : (encode pp : Data).size = esize pp := rfl; omega)
    have t11c := h₃ W X K (M := (lpPQs (lpSt sp lp pp lam tau n d s) rs₁).length) (T := T₂)
      (C := (encode pp : Data).size) (Z := Z₂) hX (small (by omega)) hT₂ (small (by omega)) hZ₂
    have t12 := hF W X K hX (y := esize (lpPads rs₁ (Repetition.reps lam tau n), rs₂))
      (((dpads.add hX hZ₂).add hX (Dom.const 1)).of_le (by rw [esize_prod]; omega))
    have u2 := ((t2a.add hX t2b).add hX t2c).add hX (Dom.const 5)
    have u4 := ((t2a.add hX t4a).add hX t4b).add hX (Dom.const 5)
    have u6 := ((t6a.add hX t6b).add hX (t6c.add hX (Dom.const 3))).add hX (Dom.const 5)
    have u7 := ((t6a.add hX t7a).add hX t7b).add hX (Dom.const 5)
    have u9 := ((t9a.add hX t9b).add hX t9c).add hX (Dom.const 5)
    have u11 := ((t11a.add hX t11b).add hX t11c).add hX (Dom.const 5)
    have v1 := (((t1.add hX u2).add hX t3).add hX u4).add hX t5
    have v2 := (((v1.add hX u6).add hX u7).add hX t8).add hX u9
    refine ((((v2.add hX t10).add hX u11).add hX t12).add hX (Dom.const 11)).of_le ?_
    dsimp only [lpCoreCost]
    omega⟩

/-! ## The time bound -/

/-- The parameters of the repeated processor at index `n`, bounded by `W`. -/
structure LpDom {ℓ : ℕ} (S : CL.Sampler ℓ) (L P : Decider) (lam tau n : ℕ) (R : Budget)
    (W : ℕ) : Prop extends LenDom S L lam tau n R W where
  sizeP_le : esize P.prog ≤ W

/-- The calls to the input calculator, within a common bound. -/
theorem lp_len_calls_le (L : Decider) (n : ℕ) (R : Budget) (hL : L.TimeBoundAt n R.D R.k)
    (st : LpSt) (hn : st.1.1.2.1 = n) : ∀ q ∈ lpLenQs st, ∃ r, RunsLe selfUniversal.univ
      (.cons (encode L.prog) q) r (selfUniversal.bound.eval (esize L.prog +
        (esize n + 4 * st.1.1.2.2.size + 6) + R.D * (4 * st.1.1.2.2.size + 6) ^ R.k)) := by
  intro q hq
  obtain ⟨xi, b, rfl, hxi⟩ := mem_lpLenQs hq
  rw [hn]
  obtain ⟨r, t, ht, hrun⟩ := hL (encode (xi, b))
  obtain ⟨t', ht', hu⟩ := selfUniversal.time_le _ _ _ _ hrun
  refine ⟨r, t', ht'.trans (polynomial_eval_mono _ ?_), hu⟩
  have hb := esize_bool_le b
  have h1 : (encode (xi, b) : Data).size + 1 ≤ 4 * st.1.1.2.2.size + 6 := by
    change esize xi + esize b + 1 + 1 ≤ _; omega
  have h2 : t ≤ R.D * (4 * st.1.1.2.2.size + 6) ^ R.k :=
    ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _))
  have h3 : (Data.cons (encode n) (encode (xi, b))).size ≤ esize n + 4 * st.1.1.2.2.size + 6 := by
    simp only [size_cons]; change esize n + _ + 1 ≤ _; omega
  omega

/-- The calls to the input processor, within a common bound. -/
theorem lp_p_calls_le (P : Decider) (n : ℕ) (R : Budget) (hP : P.TimeBoundAt n R.D R.k)
    (st : LpSt) (hn : st.1.1.2.1 = n) (rs : List Data) : ∀ q ∈ lpPQs st rs, ∃ r,
      RunsLe selfUniversal.univ (.cons (encode P.prog) q) r (selfUniversal.bound.eval
        (esize P.prog + (esize n + 16 * st.1.1.2.2.size + 12) +
          R.D * (16 * st.1.1.2.2.size + 12) ^ R.k)) := by
  intro q hq
  obtain ⟨xi, yi, a, b, rfl, h1, h2, h3, h4⟩ := mem_lpPQs hq
  rw [hn]
  obtain ⟨r, t, ht, hrun⟩ := hP (encode (xi, yi, a, b))
  obtain ⟨t', ht', hu⟩ := selfUniversal.time_le _ _ _ _ hrun
  refine ⟨r, t', ht'.trans (polynomial_eval_mono _ ?_), hu⟩
  have e1 : (encode (xi, yi, a, b) : Data).size + 1 ≤ 16 * st.1.1.2.2.size + 12 := by
    change esize xi + (esize yi + (esize a + esize b + 1) + 1) + 1 + 1 ≤ _; omega
  have e2 : t ≤ R.D * (16 * st.1.1.2.2.size + 12) ^ R.k :=
    ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e1 _))
  have e3 : (Data.cons (encode n) (encode (xi, yi, a, b))).size ≤
      esize n + 16 * st.1.1.2.2.size + 12 := by
    simp only [size_cons]; change esize n + _ + 1 ≤ _; omega
  omega

/-- The argument of the processor calls' bound, dominated. -/
theorem dom_yCallP : ∃ c m e, ∀ (W X K : ℕ) {p n D : ℕ} {d : Data}, 1 ≤ X → 10 ^ K ≤ W →
    p ≤ W → n ≤ W → D ≤ W → d.size + 1 ≤ X →
    Dom W X K c m e (p + (esize n + 16 * d.size + 12) + D * (16 * d.size + 12) ^ K) := by
  exact ⟨_, _, _, fun W X K {p n D d} hX hW hp hn hD hd => by
    have en := esize_nat_le' n
    exact ((Dom.ofLin hX (a := 5) (b := 16) (c := 13) (by omega)).add hX
      ((Dom.ofLeW hD).mul (dom_powK hX hW (a := 28) (j := 2) (by norm_num) (by omega))))⟩

/-- A bound on the queries and results of a loop of at most `M` calls, queries of size at most
`Q`, results of size at most `T`. -/
def zB (M Q T : ℕ) : ℕ := M * Q + M + 1 + (M * T + M + 1) + 1

theorem dom_zB (cM mM eM cQ mQ eQ cT mT eT : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {M Q T : ℕ}, 1 ≤ X →
    Dom W X K cM mM eM M → Dom W X K cQ mQ eQ Q → Dom W X K cT mT eT T →
    Dom W X K c m e (zB M Q T) := by
  exact ⟨_, _, _, fun W X K {M Q T} hX hM hQ hT => by
    unfold zB
    exact ((((hM.mul hQ).add hX hM).add hX (Dom.const 1)).add hX
      (((hM.mul hT).add hX hM).add hX (Dom.const 1))).add hX (Dom.const 1)⟩

theorem size_list_le_zB {l : List Data} {M Q : ℕ} (hl : l.length ≤ M)
    (h : ∀ q ∈ l, q.size ≤ Q) : (list l).size ≤ M * Q + M + 1 :=
  Machine.size_list_le_of_forall l hl h

/-- **The running time of the repeated processor.** -/
theorem repLp_timeBound : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (L P : Decider) (lam tau n : ℕ)
    (R : Budget) (W : ℕ), LpDom S L P lam tau n R W → S.TimeBoundAt n R.S R.k →
    L.TimeBoundAt n R.D R.k → P.TimeBoundAt n R.D R.k →
    (repLp S L P lam tau).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1)) := by
  obtain ⟨cy, my, ey, hy⟩ := dom_yd
  obtain ⟨cd, md, ed, hd⟩ := dom_univ_bound cy my ey
  obtain ⟨cc₁, mc₁, ec₁, hc₁⟩ := dom_yCall
  obtain ⟨cT₁, mT₁, eT₁, hT₁⟩ := dom_univ_bound cc₁ mc₁ ec₁
  obtain ⟨cc₂, mc₂, ec₂, hc₂⟩ := dom_yCallP
  obtain ⟨cT₂, mT₂, eT₂, hT₂⟩ := dom_univ_bound cc₂ mc₂ ec₂
  obtain ⟨cZ₁, mZ₁, eZ₁, hZ₁⟩ := dom_zB (4 + 0) 1 0 (4 + 4 + 7) 1 1 cT₁ mT₁ eT₁
  obtain ⟨cZ₂, mZ₂, eZ₂, hZ₂⟩ := dom_zB 1 1 0 (4 + 16 + 13) 1 1 cT₂ mT₂ eT₂
  obtain ⟨cL, mL, eL, hLc⟩ := dom_lpCoreCost cd md ed cT₁ mT₁ eT₁ cZ₁ mZ₁ eZ₁ cT₂ mT₂ eT₂
    cZ₂ mZ₂ eZ₂
  exact ⟨_, _, _, fun {ℓ} S L P lam tau n R W hW hS hL hP d => by
    classical
    have hX : 1 ≤ d.size + 1 := by omega
    have hW1 : 1 ≤ W := le_trans (Nat.one_le_pow _ _ (by norm_num)) hW.pow_le
    have en := esize_nat_le' n
    have elam := esize_nat_le' lam
    have etau := esize_nat_le' tau
    have hcalls₁ := lp_len_calls_le L n R hL (lpSt S.prog L.prog P.prog lam tau n d (S.dim n)) rfl
    let f₁ : Data → Data := fun q => if h : ∃ r, RunsLe selfUniversal.univ
      (.cons (encode L.prog) q) r (selfUniversal.bound.eval (esize L.prog +
        (esize n + 4 * d.size + 6) + R.D * (4 * d.size + 6) ^ R.k)) then h.choose else .nil
    have hf₁ : ∀ q ∈ lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n)),
        RunsLe selfUniversal.univ (.cons (encode L.prog) q) (f₁ q)
          (selfUniversal.bound.eval (esize L.prog + (esize n + 4 * d.size + 6) +
            R.D * (4 * d.size + 6) ^ R.k)) := by
      intro q hq
      simp only [f₁, dite_eq_left (hcalls₁ q hq)]
      exact (hcalls₁ q hq).choose_spec
    have hcalls₂ := lp_p_calls_le P n R hP (lpSt S.prog L.prog P.prog lam tau n d (S.dim n)) rfl
      ((lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))).map f₁)
    let f₂ : Data → Data := fun q => if h : ∃ r, RunsLe selfUniversal.univ
      (.cons (encode P.prog) q) r (selfUniversal.bound.eval (esize P.prog +
        (esize n + 16 * d.size + 12) + R.D * (16 * d.size + 12) ^ R.k)) then h.choose else .nil
    have hf₂ : ∀ q ∈ lpPQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))
        ((lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))).map f₁),
        RunsLe selfUniversal.univ (.cons (encode P.prog) q) (f₂ q)
          (selfUniversal.bound.eval (esize P.prog + (esize n + 16 * d.size + 12) +
            R.D * (16 * d.size + 12) ^ R.k)) := by
      intro q hq
      simp only [f₂, dite_eq_left (hcalls₂ q hq)]
      exact (hcalls₂ q hq).choose_spec
    -- the sizes of the loops
    have hk := hW.reps_le
    have hlen₁ : (lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))).length ≤ 4 * W := by
      rw [length_lpLenQs]; simp only [length_unary]; omega
    have hlen₂ : (lpPQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))
        ((lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))).map f₁)).length ≤ W :=
      (length_lpPQs_le _ _).trans (by simp; omega)
    have hq₁ := size_list_le_zB hlen₁ (M := 4 * W) (Q := esize n + 4 * d.size + 6) fun q hq => by
      obtain ⟨xi, b, rfl, hxi⟩ := mem_lpLenQs hq
      have hb := esize_bool_le b
      change esize n + (esize xi + esize b + 1) + 1 ≤ _
      simp only [lpSt] at hxi
      omega
    have hr₁ := size_list_le_zB (l := (lpLenQs (lpSt S.prog L.prog P.prog lam tau n d
        (S.dim n))).map f₁) (M := 4 * W) (Q := selfUniversal.bound.eval (esize L.prog +
          (esize n + 4 * d.size + 6) + R.D * (4 * d.size + 6) ^ R.k))
        (by rw [List.length_map]; exact hlen₁) fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact (hf₁ q hq).size_le
    have hq₂ := size_list_le_zB hlen₂ (M := W) (Q := esize n + 16 * d.size + 12) fun q hq => by
      obtain ⟨xi, yi, a, b, rfl, h1, h2, h3, h4⟩ := mem_lpPQs hq
      change esize n + (esize xi + (esize yi + (esize a + esize b + 1) + 1) + 1) + 1 ≤ _
      simp only [lpSt] at h1 h2 h3 h4
      omega
    have hr₂ := size_list_le_zB (l := (lpPQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))
        ((lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))).map f₁)).map f₂) (M := W)
      (Q := selfUniversal.bound.eval (esize P.prog + (esize n + 16 * d.size + 12) +
          R.D * (16 * d.size + 12) ^ R.k))
      (by rw [List.length_map]; exact hlen₂) fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact (hf₂ q hq).size_le
    obtain ⟨t, ht, hr⟩ := lpCore_runsLe selfUniversal.closed S.prog L.prog P.prog lam tau n d
      (S.dim n) (dim_univ_le S n R hS) f₁ f₂ _ (zB (4 * W) (esize n + 4 * d.size + 6)
        (selfUniversal.bound.eval (esize L.prog + (esize n + 4 * d.size + 6) +
          R.D * (4 * d.size + 6) ^ R.k))) _ (zB W (esize n + 16 * d.size + 12)
        (selfUniversal.bound.eval (esize P.prog + (esize n + 16 * d.size + 12) +
          R.D * (16 * d.size + 12) ^ R.k))) hf₁ (by unfold zB; omega) hf₂ (by unfold zB; omega)
    have hr' : (lpCore selfUniversal.univ).Runs
        (.cons (encode ((S.prog, L.prog, P.prog, lam, tau) : LpPar)) (.cons (encode n) d)) _ t := hr
    have hh := hardcode_time (lpCore_wellScoped selfUniversal.closed) hr'
    refine ⟨_, _, ?_, hh⟩
    have dTd := hd W (d.size + 1) R.k hX (by omega)
      (hy W (d.size + 1) R.k hX hW.sizeS_le hW.n_le hW.S_le hW.pow_le)
    have dT₁ := hT₁ W (d.size + 1) R.k hX (by omega)
      (hc₁ W (d.size + 1) R.k hX hW.pow_le hW.sizeL_le hW.n_le hW.D_le le_rfl)
    have dT₂ := hT₂ W (d.size + 1) R.k hX (by omega)
      (hc₂ W (d.size + 1) R.k hX hW.pow_le hW.sizeP_le hW.n_le hW.D_le le_rfl)
    have dM₁ : Dom W (d.size + 1) R.k (4 + 0) 1 0 (4 * W) := Dom.ofAffine (by omega)
    have dM₂ : Dom W (d.size + 1) R.k 1 1 0 W := Dom.ofLeW le_rfl
    have dQ₁ : Dom W (d.size + 1) R.k (4 + 4 + 7) 1 1 (esize n + 4 * d.size + 6) :=
      Dom.ofLin hX (by have := hW.n_le; omega)
    have dQ₂ : Dom W (d.size + 1) R.k (4 + 16 + 13) 1 1 (esize n + 16 * d.size + 12) :=
      Dom.ofLin hX (by have := hW.n_le; omega)
    have dZ₁ := hZ₁ W (d.size + 1) R.k hX dM₁ dQ₁ dT₁
    have dZ₂ := hZ₂ W (d.size + 1) R.k hX dM₂ dQ₂ dT₂
    have dL := hLc W (d.size + 1) R.k (sp := S.prog) (lp := L.prog) (pp := P.prog) (d := d)
      (s := S.dim n) (rs₁ := (lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))).map f₁)
      (rs₂ := (lpPQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))
        ((lpLenQs (lpSt S.prog L.prog P.prog lam tau n d (S.dim n))).map f₁)).map f₂) hX hW1 le_rfl hW.sizeS_le hW.sizeL_le hW.sizeP_le hW.lam_le hW.tau_le
      hW.n_le hW.dim_le hW.reps_le dTd dT₁ dZ₁ dT₂ dZ₂ (by unfold zB; omega) (by unfold zB; omega)
      (by unfold zB; omega) (by unfold zB; omega)
    have dP := Dom.ofLin (W := W) (K := R.k) hX (a := 15) (b := 0) (c := 7)
      (v := (encode ((S.prog, L.prog, P.prog, lam, tau) : LpPar) : Data).size) (by
        change esize S.prog + (esize L.prog + (esize P.prog + (esize lam + esize tau + 1) + 1) + 1)
          + 1 ≤ _
        have := hW.sizeS_le; have := hW.sizeL_le; have := hW.sizeP_le; have := hW.lam_le
        have := hW.tau_le
        omega)
    have dI := Dom.ofLin (W := W) (K := R.k) hX (a := 4) (b := 1) (c := 1)
      (v := (Data.cons (encode n) d).size) (by
        simp only [size_cons]; change esize n + _ + 1 ≤ _; have := hW.n_le; omega)
    exact (((dL.add hX dP).add hX dI).add hX (Dom.const 3)).le.trans' (by omega)⟩

end MIPRE.Tailored.RepProg

end
