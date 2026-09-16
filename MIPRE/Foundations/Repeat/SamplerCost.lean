/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.RepSampler
import MIPRE.Foundations.Repeat.Dom
import MIPRE.Foundations.Cost.Growth

/-!
# The running time of the repeated sampler

`repSampler_timeBound`: when the input sampler runs within `R.S (|d| + 1)^{R.k}` at index `n`
and has dimension at most `R.d` there, the repeated sampler on `(λ, τ)` runs within
`c (W + 1)^m (|d| + 1)^{e (R.k + 1)}` for constants `c, m, e` independent of everything, `W`
any number dominating `R.S`, `R.d`, `λ`, `τ`, `n`, the description length of the input
sampler, the repetition count and `10^{R.k}` (the input's time on the dimension query). The
cost is the explicit one of `repSampCore_runs_any`, each of whose pieces is a sum and product
of quantities below `W`, below `|d| + 1`, or of the cost of a call to the input sampler
through the universal machine, bounded by `Dom` combinators.
-/

namespace MIPRE.Repeat

open Cost Cost.Data Cost.Prog CL

/-- The constants of the self-interpreter's overhead polynomial. -/
noncomputable def cU : ℕ :=
  ∑ i ∈ Finset.range (selfUniversal.bound.natDegree + 1), selfUniversal.bound.coeff i

/-- The degree of the self-interpreter's overhead polynomial. -/
noncomputable def dU : ℕ := selfUniversal.bound.natDegree

theorem univ_bound_le {y : ℕ} (hy : 1 ≤ y) : selfUniversal.bound.eval y ≤ cU * y ^ dU :=
  polynomial_eval_le_sum_coeff_mul_pow _ hy

/-- The size of every block query is at most the size of the query datum. -/
theorem size_le_of_mem_blockQueries (s : ℕ) (d q : Data) (hq : q ∈ blockQueries s d) :
    q.size ≤ d.size := by
  unfold blockQueries at hq
  split at hq
  · rename_i k₀ k₁ wD jD uD yD
    split at hq
    · rename_i hs
      rw [List.mem_map] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      obtain ⟨h1, h2⟩ := size_le_of_mem_chunkPairs s hs (toList uD) (toList yD) p hp
      rw [list_toList] at h1 h2
      simp only [size_cons]
      omega
    · simp at hq
  · simp at hq

/-- The hypotheses on the dominating number `W`. -/
structure SampDom {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ) : Prop where
  S_le : R.S ≤ W
  d_le : R.d ≤ W
  lam_le : lam ≤ W
  tau_le : tau ≤ W
  n_le : n ≤ W
  size_le : esize S.prog ≤ W
  pow_le : 10 ^ R.k ≤ W
  reps_le : Repetition.reps lam tau n ≤ W
  dim_le : S.dim n ≤ W

variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)

theorem nat_size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

theorem esize_nat_le' (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := nat_size_le_self x; omega)

/-- The time of the dimension query through the universal machine. -/
theorem dim_call_time (hS : S.TimeBoundAt n R.S R.k) :
    ∃ td, td ≤ selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k) ∧
      Eval [Data.cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension))]
        selfUniversal.univ (encode (S.dim n)) td := by
  obtain ⟨t, h⟩ := S.runs_dimension n
  obtain ⟨r', t', ht', h'⟩ := hS (encode CL.Sampler.Query.dimension)
  obtain ⟨rfl, rfl⟩ := h.deterministic h'
  obtain ⟨t'', ht'', h''⟩ := selfUniversal.time_le _ _ _ _ h
  refine ⟨t'', ht''.trans (polynomial_eval_mono _ ?_), h''⟩
  have hd : (encode (n, CL.Sampler.Query.dimension) : Data).size = esize n + 9 + 1 := rfl
  simp only [size_encode_dimension, show (9 : ℕ) + 1 = 10 from rfl] at ht'
  rw [hd]
  omega

/-- The block queries through the universal machine, within a uniform bound. -/
theorem block_calls_time (hS : S.TimeBoundAt n R.S R.k) (d : Data) :
    ∃ fq : Data → Data, ∀ q ∈ blockQueries (S.dim n) d,
      ∃ t ≤ selfUniversal.bound.eval (esize S.prog + (esize n + d.size + 1) + R.S * (d.size + 1) ^ R.k),
        Eval [Data.cons (encode S.prog) (.cons (encode n) q)] selfUniversal.univ (fq q) t := by
  classical
  refine ⟨fun q => (hS q).choose, fun q hq => ?_⟩
  obtain ⟨t, ht, h⟩ := (hS q).choose_spec
  obtain ⟨t', ht', h'⟩ := selfUniversal.time_le _ _ _ _ h
  refine ⟨t', ht'.trans (polynomial_eval_mono _ ?_), h'⟩
  have hq' := size_le_of_mem_blockQueries (S.dim n) d q hq
  have hk : (q.size + 1) ^ R.k ≤ (d.size + 1) ^ R.k := Nat.pow_le_pow_left (by omega) _
  have := Nat.mul_le_mul_left R.S hk
  have he : (encode n : Data).size = esize n := rfl
  simp only [size_cons, he]
  omega

/-- **The repeated sampler halts within `anyCost`** plus the s-m-n overhead. -/
theorem repSampler_halts_within (hS : S.TimeBoundAt n R.S R.k) (d : Data) :
    ∃ r t, t ≤ anyCost lam tau n (encode S.prog) (S.dim n) d.size
        (selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k))
        (selfUniversal.bound.eval (esize S.prog + (esize n + d.size + 1) + R.S * (d.size + 1) ^ R.k)) +
        (esize S.prog + esize lam + esize tau + 2) + (esize n + d.size + 1) + 3 ∧
      (repSamplerProg S.prog lam tau).Runs (.cons (encode n) d) r t := by
  obtain ⟨td, htd, hdim⟩ := dim_call_time S n R hS
  obtain ⟨fq, hfq⟩ := block_calls_time S n R hS d
  set Tu := selfUniversal.bound.eval (esize S.prog + (esize n + d.size + 1) + R.S * (d.size + 1) ^ R.k)
    with hTu
  obtain ⟨r, t, ht, run⟩ := repSampCore_runs_any selfUniversal.closed (encode S.prog) lam tau n
    (S.dim n) d hdim fq Tu hfq
  refine ⟨r, _, ?_, repSamplerProg_runs S.prog lam tau n d run⟩
  have hmono : anyCost lam tau n (encode S.prog) (S.dim n) d.size td Tu ≤
      anyCost lam tau n (encode S.prog) (S.dim n) d.size
        (selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k)) Tu := by
    unfold anyCost
    omega
  have hP : (encode (S.prog, lam, tau) : Data).size = esize S.prog + esize lam + esize tau + 2 := by
    simp only [encode_prod, size_cons, esize]; omega
  have hin : (Data.cons (encode n) d).size = esize n + d.size + 1 := by
    simp only [size_cons, esize]
  rw [hP, hin]
  omega

/-! ## The domination chain

Each lemma below produces constants `c, m, e` that are uniform in everything, as the
existential outside the universal quantifiers records; the proofs are the `Dom` combinators
applied in the shape of the cost expression, and Lean assembles the constants. -/

section Chain

variable {W X K : ℕ}

theorem dom_esize {x : ℕ} (hx : x ≤ W) : Dom W X K (4 + 1) 1 0 (esize x) :=
  Dom.ofAffine (by have := esize_nat_le' x; omega)

/-! The constants of each lemma are natural metavariables assigned by the final `exact`, so
they must be closed terms; `exact ⟨_, _, _, fun … => by …⟩` rather than `refine ⟨?c, …⟩`, whose
synthetic goals the unifier will not assign and instead reduces `max` chains against. -/

theorem dom_toUnaryCost : ∃ c m e, ∀ (W X K : ℕ) {x : ℕ}, 1 ≤ X → x ≤ W →
    Dom W X K c m e (toUnaryCost x) := by
  exact ⟨_, _, _, fun W X K {x} hX hx => by
    unfold toUnaryCost
    have h1 : Dom W X K (1 + 2) 1 0 (Nat.size x + 2) :=
      Dom.ofAffine (by have := nat_size_le_self x; omega)
    have h2 : Dom W X K (1 + 1) 1 0 (x + 1) := Dom.ofAffine (by omega)
    have h3 : Dom W X K (4 + 14) 1 0 (4 * x + 14) := Dom.ofAffine (by omega)
    have h5 : Dom W X K (8 + 0) 1 0 (8 * x) := Dom.ofAffine (by omega)
    exact h1.mul ((((h2.mul h3).add hX ((Dom.const 7).mul (dom_esize hx))).add hX h5).add hX
      (Dom.const 90))⟩

theorem dom_powCost : ∃ c m e', ∀ (W X K : ℕ) {e L sz : ℕ}, 1 ≤ X → e ≤ W → L ≤ 2 * W →
    sz ≤ 12 * W + 3 → Dom W X K c m e' (powCost e L sz) := by
  exact ⟨_, _, _, fun W X K {e L sz} hX he hL hsz => by
    unfold powCost
    have h1 : Dom W X K (1 + 1) 1 0 (e + 1) := Dom.ofAffine (by omega)
    have h2 : Dom W X K (2 + 1) 1 0 (L + 1) := Dom.ofAffine (by omega)
    have h3 : Dom W X K (12 + 3) 1 0 sz := Dom.ofAffine hsz
    have h4 : Dom W X K (2 + 0) 1 0 L := Dom.ofAffine (by omega)
    exact h1.mul (((Dom.const 8).mul h2).mul (((h3.add hX (((Dom.const 2).mul (Dom.ofLeW he)).mul
      h4)).add hX (Dom.ofLeW he)).add hX (Dom.const 14)))⟩

theorem dom_dimCost : ∃ c m e, ∀ (W X K : ℕ) {tau L Λ N Ssz : ℕ}, 1 ≤ X → tau ≤ W →
    L ≤ 2 * W → Λ ≤ 4 * W + 1 → N ≤ 4 * W + 1 → Ssz ≤ 4 * W + 1 →
    Dom W X K c m e (dimCost tau L Λ N Ssz) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_toUnaryCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_powCost
  exact ⟨_, _, _, fun W X K {tau L Λ N Ssz} hX ht hL hΛ hN hS => by
    unfold dimCost
    have hsz : Λ + N + Ssz ≤ 12 * W + 3 := by omega
    have hΛ' : Dom W X K (4 + 1) 1 0 Λ := Dom.ofAffine hΛ
    have hN' : Dom W X K (4 + 1) 1 0 N := Dom.ofAffine hN
    have hS' : Dom W X K (4 + 1) 1 0 Ssz := Dom.ofAffine hS
    exact ((((((h₁ W X K hX ht).add hX (dom_esize ht)).add hX (h₂ W X K hX ht hL hsz)).add hX
      ((Dom.const 2).mul (Dom.ofLeW ht))).add hX hΛ').add hX hN').add hX hS' |>.add hX
      (Dom.const 20)⟩

theorem dom_mapIter (cZ mZ eZ : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {Z : ℕ}, 1 ≤ X →
    Dom W X K cZ mZ eZ Z → Dom W X K c m e (mapIter Z) := by
  exact ⟨_, _, _, fun W X K {Z} hX hZ => by
    unfold mapIter
    exact (Dom.const 22).mul ((hZ.add hX (Dom.const 30)).pow 2)⟩

theorem dom_zBound (cT mT eT : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {sD : Data} {n s D Tu : ℕ},
    1 ≤ X → Dom W X K cT mT eT Tu → sD.size ≤ W → n ≤ W → s ≤ W → D + 1 ≤ X →
    Dom W X K c m e (zBound sD n s D Tu) := by
  exact ⟨_, _, _, fun W X K {sD n s D Tu} hX hT hsD hn hs hD => by
    unfold zBound
    have hD' : Dom W X K 1 0 1 D := Dom.ofLeX hX (by omega)
    exact (((((Dom.ofLeW hs).add hX ((Dom.const 3).mul hD')).add hX
      ((((Dom.ofLeW hsD).add hX (dom_esize hn)).add hX hD').add hX (Dom.const 4))).add hX
      (Dom.const 1)).add hX (hD'.mul (hT.add hX (Dom.const 1)))).add hX hT⟩

theorem dom_lockCost (cC mC eC cZ mZ eZ : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {s C U Y Z : ℕ},
    1 ≤ X → s ≤ W → Dom W X K cC mC eC C → U + 1 ≤ X → Y + 1 ≤ X → Dom W X K cZ mZ eZ Z →
    Dom W X K c m e (lockCost s C U Y Z) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_toUnaryCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_mapIter cZ mZ eZ
  exact ⟨_, _, _, fun W X K {s C U Y Z} hX hs hC hU hY hZ => by
    unfold lockCost
    have hU' : Dom W X K 1 0 1 U := Dom.ofLeX hX (by omega)
    have hY' : Dom W X K 1 0 1 Y := Dom.ofLeX hX (by omega)
    exact ((((((((dom_esize hs).add hX (h₁ W X K hX hs)).add hX ((Dom.const 4).mul hC)).add hX
      ((Dom.const 4).mul (Dom.ofLeW hs))).add hX ((Dom.const 4).mul hU')).add hX
      ((Dom.const 4).mul hY')).add hX ((Dom.ofLeX hX hU).mul (h₂ W X K hX hZ))).add hX
      ((hZ.add hX (Dom.const 2)).mul (hZ.add hX (Dom.const 13)))).add hX
      ((Dom.const 3).mul hZ) |>.add hX (Dom.const 60)⟩

theorem dom_anyCost (cd md ed cT mT eT : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {lam tau n : ℕ}
    {sD : Data} {s D td Tu : ℕ}, 1 ≤ X → Dom W X K cd md ed td → Dom W X K cT mT eT Tu →
    sD.size ≤ W → lam ≤ W → tau ≤ W → n ≤ W → s ≤ W → D + 1 ≤ X →
    Dom W X K c m e (anyCost lam tau n sD s D td Tu) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_dimCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_zBound cT mT eT
  obtain ⟨c₃, m₃, e₃, h₃⟩ := dom_lockCost (1 + (4 + 1) + 1 + 4) 1 1 c₂ m₂ e₂
  exact ⟨_, _, _, fun W X K {lam tau n sD s D td Tu} hX htd hTu hsD hlam htau hn hs hD => by
    unfold anyCost
    have hD' : Dom W X K 1 0 1 D := Dom.ofLeX hX (by omega)
    have hC : Dom W X K (1 + (4 + 1) + 1 + 4) 1 1 (sD.size + esize n + D + 4) := by
      have := (((Dom.ofLeW hsD).add hX (dom_esize hn)).add hX hD').add hX (Dom.const 4)
      simpa using this
    have hL : Nat.size lam + Nat.size n ≤ 2 * W := by
      have := nat_size_le_self lam; have := nat_size_le_self n; omega
    have hlam' : esize lam ≤ 4 * W + 1 := (esize_nat_le' lam).trans (by omega)
    have hn' : esize n ≤ 4 * W + 1 := (esize_nat_le' n).trans (by omega)
    have hs' : esize s ≤ 4 * W + 1 := (esize_nat_le' s).trans (by omega)
    have b1 := ((htd.add hX ((Dom.const 2).mul ((Dom.ofLeW hsD).add hX (dom_esize hn)))).add hX
      (Dom.const 40))
    have b2 := (((Dom.const 2).mul ((((dom_esize hs).add hX (dom_esize hlam)).add hX
      (dom_esize hn)).add hX (dom_esize htau))).add hX (Dom.const 20)).add hX
      (h₁ W X K hX htau hL hlam' hn' hs')
    have b3 := ((((((((Dom.const 2).mul ((((Dom.ofLeW hsD).add hX (dom_esize hn)).add hX
      (dom_esize hs)).add hX hD')).add hX (Dom.const 40)).add hX
      (h₃ W X K hX hs hC hD hD (h₂ W X K hX hTu hsD hn hs hD))).add hX
      (Dom.const (esize 0))).add hX (Dom.const (toUnaryCost 0))).add hX (Dom.ofLeW hsD)).add hX
      (dom_esize hn)).add hX ((Dom.const 3).mul hD')
    exact (b1.add hX b2).add hX b3⟩

/-- The self-interpreter's overhead polynomial at a dominated argument. -/
theorem dom_univ_bound (cy my ey : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X → 1 ≤ y →
    Dom W X K cy my ey y → Dom W X K c m e (selfUniversal.bound.eval y) := by
  exact ⟨_, _, _, fun W X K {y} _ hy h => ((Dom.const cU).mul (h.pow dU)).of_le (univ_bound_le hy)⟩

/-- The argument of the dimension query's bound. -/
theorem dom_yd : ∃ c m e, ∀ (W X K : ℕ) {p n RS pk : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → RS ≤ W →
    pk ≤ W → Dom W X K c m e (p + (esize n + 10) + RS * pk) := by
  exact ⟨_, _, _, fun W X K {p n RS pk} hX hp hn hRS hpk =>
    ((Dom.ofLeW hp).add hX ((dom_esize hn).add hX (Dom.const 10))).add hX
      ((Dom.ofLeW hRS).mul (Dom.ofLeW hpk))⟩

/-- The argument of the block queries' bound. -/
theorem dom_yT : ∃ c m e, ∀ (W X K : ℕ) {p n RS D : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → RS ≤ W →
    D + 1 = X → Dom W X K c m e (p + (esize n + D + 1) + RS * (D + 1) ^ K) := by
  exact ⟨_, _, _, fun W X K {p n RS D} hX hp hn hRS hD => by
    subst hD
    exact ((Dom.ofLeW hp).add hX (((dom_esize hn).add hX (Dom.ofLeX hX (by omega))).add hX
      (Dom.const 1))).add hX ((Dom.ofLeW hRS).mul (Dom.powK hX))⟩

end Chain

/-- **The running time of the repeated sampler**: constants `c, m, e` uniform in everything
such that, whenever `W` dominates the parameters at `n` and the input sampler runs within
`R.S (|d| + 1)^{R.k}` there, the repeated sampler runs within
`c (W + 1)^m (|d| + 1)^{e (R.k + 1)}`. -/
theorem repSampler_timeBound : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ)
    (R : Budget) (W : ℕ), SampDom S lam tau n R W → S.TimeBoundAt n R.S R.k →
    (repSampler S lam tau).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1)) := by
  obtain ⟨cd, md, ed, hd⟩ := dom_yd
  obtain ⟨cd', md', ed', hd'⟩ := dom_univ_bound cd md ed
  obtain ⟨cT, mT, eT, hT⟩ := dom_yT
  obtain ⟨cT', mT', eT', hT'⟩ := dom_univ_bound cT mT eT
  obtain ⟨cA, mA, eA, hA⟩ := dom_anyCost cd' md' ed' cT' mT' eT'
  exact ⟨_, _, _, fun {ℓ} S lam tau n R W hW hS d => by
    obtain ⟨r, t, ht, run⟩ := repSampler_halts_within S lam tau n R hS d
    refine ⟨r, t, ?_, run⟩
    have hX : 1 ≤ d.size + 1 := by omega
    have hsD : (encode S.prog : Data).size ≤ W := hW.size_le
    have hD' : Dom W (d.size + 1) R.k 1 0 1 d.size := Dom.ofLeX hX (by omega)
    have h1 := hA W (d.size + 1) R.k hX
      (hd' W _ R.k hX (by omega) (hd W _ R.k hX hW.size_le hW.n_le hW.S_le hW.pow_le))
      (hT' W _ R.k hX (by omega) (hT W _ R.k hX hW.size_le hW.n_le hW.S_le rfl))
      hsD hW.lam_le hW.tau_le hW.n_le hW.dim_le le_rfl
    have h2 := ((h1.add hX ((((Dom.ofLeW hW.size_le).add hX (dom_esize hW.lam_le)).add hX
      (dom_esize hW.tau_le)).add hX (Dom.const 2))).add hX
      (((dom_esize hW.n_le).add hX hD').add hX (Dom.const 1))).add hX (Dom.const 3)
    exact (h2.of_le ht).le⟩

end MIPRE.Repeat
