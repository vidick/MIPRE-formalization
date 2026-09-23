/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Params
import MIPRE.Foundations.Pipeline.PowDomRun

/-!
# The running time of the parameter routine

Piece AR-3f of `planning/answer-reduction.md`. The routine `parProg` of answer reduction computes
the PCP's parameters `pd n` by loops whose lengths are the *values* `λ`, `n`, `μ`, `Q = (λn + 1)^μ`
and the parameters `k, m, s`; so its time is polynomial in those values, and dominated in the
sense of `MIPRE.Pipeline.PDom` by any `W ≥ Q, λ, σ, n` at `K = μ` (`parProg_time`), provided the
PCP's parameters are polynomial in `(log n, log T, Q, σ)` (`ParamsBound`), as the paper's
`pcpparams` are. The bit length of `T = 2^{(Q + 5)(μ + 1)}` is `(Q + 5)(μ + 1) + 1`, a product of a
quantity below `W` and one below `K + 1`.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg

/-- **The PCP's parameters are polynomial** in `(log n, log T, Q, σ)`, by the polynomial `R`. -/
def ParamsBound (PD : PcpDecider) (R : Polynomial ℕ) : Prop :=
  ∀ n T Q σ, (PD.params n T Q σ).k + (PD.params n T Q σ).m + (PD.params n T Q σ).s ≤
    R.eval (Nat.size n + Nat.size T + Q + σ)

/-- The constant dominating the routine's linear quantities. -/
abbrev linC : ℕ := 40 + 2 * 40 + 40 + 3

theorem pdLin {W X K v : ℕ} (hX : 1 ≤ X) (h : v ≤ 40 * W + 40 * (K + 1) + 40) :
    PDom W X K linC 1 0 v :=
  PDom.ofLin hX h

/-- A linear function of `W` and `K + 1` plus a square in `W`: the routine's quantities, `λn + 1`
among them. -/
theorem pdQ {W X K v : ℕ} (hX : 1 ≤ X)
    (h : v ≤ 40 * W + 40 * (K + 1) + 40 + 4 * (W + 1) ^ 2) : PDom W X K (linC + 4) 2 0 v := by
  have h1 : PDom W X K linC 1 0 (40 * W + 40 * (K + 1) + 40) := pdLin hX le_rfl
  have h2 : PDom W X K 4 2 0 (4 * (W + 1) ^ 2) := PDom.ofMono (by simp)
  exact ((h1.add hX h2).mono hX le_rfl (by simp) (by simp)).of_le h

theorem lam_mul_add_one_le (lam n W : ℕ) (hl : lam ≤ W) (hn : n ≤ W) :
    lam * n + 1 ≤ (W + 1) ^ 2 := by
  have := Nat.mul_le_mul hl hn
  nlinarith

theorem size_X0 (lam mu sigma n : ℕ) :
    (Data.cons (encode (lam, mu, sigma)) (encode n)).size =
      esize lam + esize mu + esize sigma + esize n + 3 := by
  simp only [Data.size_cons, encode_prod]
  change esize lam + (esize mu + esize sigma + 1) + 1 + esize n + 1 = _
  omega

open ParRoutine in
/-- **The running time of the budgets' routine.** -/
theorem budCore_time : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W →
    PRuns W X mu c m e budCore (.cons (encode (lam, mu, sigma)) (encode n))
      (encode (arQ lam mu n, tPcp lam mu n)) := by
  obtain ⟨cu, mu', eu, hu⟩ := PRuns.toUnary (linC + 4) 2 0
  obtain ⟨cp, mp, ep, hp⟩ := PRuns.pow (linC + 4) 2 0
  obtain ⟨c1, m1, e1, h1⟩ := PRuns.stage pre1 post1 (linC + 4) 2 0 cu mu' eu
  obtain ⟨c2, m2, e2, h2⟩ := PRuns.stage pre2 post2 (linC + 4) 2 0 cu mu' eu
  obtain ⟨c3, m3, e3, h3⟩ := PRuns.stage pre3 postKeep (linC + 4) 2 0 cp mp ep
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.stage preMu postBud (linC + 4) 2 0 cu mu' eu
  exact ⟨_, _, _, fun {W X} lam mu sigma n hX hQ hl hs hn => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    have en := esize_nat_le_four n
    have hb := lam_mul_add_one_le lam n W hl hn
    let X0 : Data := .cons (encode (lam, mu, sigma)) (encode n)
    have hX0 : X0.size = esize lam + esize mu + esize sigma + esize n + 3 := size_X0 _ _ _ _
    let lam' : ℕ := if n = 0 then 0 else lam
    have hl' : lam' ≤ lam := by by_cases h : n = 0 <;> simp [lam', h]
    have hlm : lam' * n = lam * n := by by_cases hn : n = 0 <;> simp [lam', hn]
    -- stage 1: `λ'` in unary
    have S1 := h1 (W := W) (K := mu) toUnaryProg_closed X0 (encode lam') X0 _ hX
      (by
        by_cases hn : n = 0
        · subst hn
          have h0 : (encode (0 : ℕ) : Data) = .nil := rfl
          simp [pre1, X0, lam', encode_prod, treeEq_apply, h0]
        · have : (encode n : Data) ≠ .nil := by
            intro h
            exact hn (encode_injective (h.trans rfl : (encode n : Data) = encode (0 : ℕ)))
          simp [pre1, hD, X0, lam', hn, encode_prod, treeEq_apply, this])
      (pdQ hX (by omega)) (hu (W := W) (K := mu) lam' hX (pdQ hX (by omega)))
    let X1 : Data := .cons (encode (unary lam')) X0
    have hX1 : X1.size = 2 * lam' + 1 + X0.size + 1 := by
      simp only [X1, Data.size_cons]; rw [show (encode (unary lam') : Data).size =
        esize (unary lam') from rfl, esize_unary]
    have hp1 : post1 (X0, encode (unary lam')) = X1 := by
      simp [post1, X1]
    rw [hp1] at S1
    -- stage 2: `n` in unary
    have S2 := h2 (W := W) (K := mu) toUnaryProg_closed X1 (encode n) X1 _ hX rfl
      (pdQ hX (by omega))
      (hu (W := W) (K := mu) n hX (pdQ hX (by omega)))
    have hpost2 : post2 (X1, encode (unary n)) =
        .cons (encode (unary (lam * n + 1), mu)) X0 := by
      simp only [post2, ap₂_apply, treePair_apply, comp_apply, fst_apply, snd_apply,
        treeHead_cons, treeTail_cons, readUnary_encode, cons_apply, const_apply, pair_apply,
        LowDegree.DegreeArithmetic.mulUnaryProg_apply, length_unary, encoded_apply,
        unary_mul_succ, X1, X0, encode_prod, hlm]
    rw [hpost2] at S2
    -- stage 3: `Q = (λn + 1)^μ` in unary
    let X2 : Data := .cons (encode (unary (lam * n + 1), mu)) X0
    have hX2 : X2.size = 2 * (lam * n + 1) + 1 + esize mu + 1 + X0.size + 1 := by
      simp only [X2, Data.size_cons, encode_prod]
      rw [show (encode (unary (lam * n + 1)) : Data).size = esize (unary (lam * n + 1)) from rfl,
        esize_unary]
      rfl
    have S3 := h3 (W := W) (K := mu) powProg_closed X2 (encode (unary (lam * n + 1), mu)) X0 _
      hX rfl
      (pdQ hX (by omega))
      (hp (W := W) (K := mu) (unary (lam * n + 1)) mu hX (by simp) (pdQ hX (by simp; omega))
        (pdQ hX (by omega))
        (pdQ hX (by simp only [length_unary]; change arQ lam mu n ≤ _; omega)))
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply, length_unary] at S3
    -- stage 4: `μ` in unary, then `(Q, T)`
    let X3 : Data := .cons (encode (unary (arQ lam mu n))) X0
    have hX3 : X3.size = 2 * arQ lam mu n + 1 + X0.size + 1 := by
      simp only [X3, Data.size_cons]
      rw [show (encode (unary (arQ lam mu n)) : Data).size = esize (unary (arQ lam mu n)) from rfl,
        esize_unary]
    have S4 := h4 (W := W) (K := mu) toUnaryProg_closed X3 (encode mu) X3 _ hX
      (by simp [preMu, X3, X0, encode_prod]) (pdQ hX (by omega))
      (hu (W := W) (K := mu) mu hX (pdQ hX (by omega)))
    have hpost4 : postBud (X3, encode (unary mu)) = encode (arQ lam mu n, tPcp lam mu n) := by
      simp only [postBud, comp_apply, pair_apply, fst_apply, snd_apply, treeHead_cons,
        readUnary_encode, map_apply, ap₂_apply, append_apply, const_apply, addUnary_apply,
        length_unary, encoded_apply, X3, cons_apply, LowDegree.DegreeArithmetic.mulUnaryProg_apply,
        List.length_append, List.length_cons]
      rw [map_const_toFun, length_unary, PolyTimeFun.bitsValue_apply, bitsVal_pow, zero_add]
    rw [hpost4] at S4
    exact PRuns.seq hX (seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
        seqProg_closed (stageProg_closed _ powProg_closed _)
          (stageProg_closed _ toUnaryProg_closed _)) S1 <|
      PRuns.seq hX (seqProg_closed (stageProg_closed _ powProg_closed _)
        (stageProg_closed _ toUnaryProg_closed _)) S2 <|
      PRuns.seq hX (stageProg_closed _ toUnaryProg_closed _) S3 S4⟩

/-- The argument of the parameter bound, `|n| + |T| + Q + σ`. -/
theorem size_tPcp (lam mu n : ℕ) :
    Nat.size (tPcp lam mu n) = (arQ lam mu n + 5) * (mu + 1) + 1 := by
  rw [tPcp, Nat.size_pow]

/-- **The PCP's parameters are dominated**, with the contexts that hold them. -/
theorem params_pdom (PD : PcpDecider) (R : Polynomial ℕ) : ∃ c m e, ∀ {W X : ℕ},
    ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X → arQ lam mu n ≤ W → sigma ≤ W → n ≤ W →
    PDom W X mu c m e (20 * ((arPar PD lam mu sigma n).k + (arPar PD lam mu sigma n).m +
      (arPar PD lam mu sigma n).s) + 20) := by
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hs hn => by
    have hsn : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have h1 : PDom W X mu _ _ _ (Nat.size n + arQ lam mu n + sigma + 1) := pdLin hX (by omega)
    have h2 : PDom W X mu _ _ _ ((arQ lam mu n + 5) * (mu + 1)) :=
      (pdLin hX (by omega : arQ lam mu n + 5 ≤ 40 * W + 40 * (mu + 1) + 40)).mul
        (pdLin hX (by omega : mu + 1 ≤ 40 * W + 40 * (mu + 1) + 40))
    have h3 := (h1.add hX h2).poly hX R
    have hk := hR n (tPcp lam mu n) (arQ lam mu n) sigma
    rw [size_tPcp] at hk
    have h4 : R.eval (Nat.size n + ((arQ lam mu n + 5) * (mu + 1) + 1) + arQ lam mu n + sigma) ≤
        R.eval (Nat.size n + arQ lam mu n + sigma + 1 + (arQ lam mu n + 5) * (mu + 1)) :=
      polynomial_eval_mono _ (by omega)
    exact (((PDom.const 20).mul (h3.of_le (hk.trans h4))).add hX (PDom.const 20)).of_le
      (by simp only [arPar]; omega)⟩

/-- The context after the budgets, `((Q, T), (λ, μ, σ), n)`, is dominated. -/
theorem ctxQT_pdom : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X → arQ lam mu n ≤ W →
    lam ≤ W → sigma ≤ W → n ≤ W →
    PDom W X mu c m e (Data.cons (encode (arQ lam mu n, tPcp lam mu n))
      (.cons (encode (lam, mu, sigma)) (encode n))).size := by
  exact ⟨_, _, _, fun {W X} lam mu sigma n hX hQ hl hs hn => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    have en := esize_nat_le_four n
    have eQ := esize_nat_le_four (arQ lam mu n)
    have eT := esize_nat_le (tPcp lam mu n)
    rw [size_tPcp] at eT
    have h2 : PDom W X mu _ _ _ ((arQ lam mu n + 5) * (mu + 1)) :=
      (pdLin hX (by omega : arQ lam mu n + 5 ≤ 40 * W + 40 * (mu + 1) + 40)).mul
        (pdLin hX (by omega : mu + 1 ≤ 40 * W + 40 * (mu + 1) + 40))
    have hsz : (Data.cons (encode (arQ lam mu n, tPcp lam mu n))
        (.cons (encode (lam, mu, sigma)) (encode n))).size =
        esize (arQ lam mu n) + esize (tPcp lam mu n) + 1 +
          (esize lam + esize mu + esize sigma + esize n + 3) + 1 := by
      rw [← size_X0]; simp only [Data.size_cons, encode_prod]; rfl
    rw [hsz]
    exact (((PDom.const 4).mul h2).add hX (pdLin hX
      (by omega : 4 * arQ lam mu n + 1 + 5 + 1 + (4 * lam + 1 + (4 * mu + 1) + (4 * sigma + 1) +
        (4 * n + 1) + 3) + 1 ≤ 40 * W + 40 * (mu + 1) + 40))).of_le (by omega)⟩

open ParRoutine in
/-- **The running time of the routine's core**, on `((λ, μ, σ), n)`. -/
theorem parCore_time (PD : PcpDecider) (R : Polynomial ℕ) : ∃ c m e, ∀ {W X : ℕ},
    ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W →
    PRuns W X mu c m e (core PD) (.cons (encode (lam, mu, sigma)) (encode n))
      ((family PD lam mu sigma).pd n) := by
  obtain ⟨cb, mb, eb, hb⟩ := budCore_time
  obtain ⟨cA, mA, eA, hA⟩ := PRuns.stage (ap₂ treePair (PolyTimeFun.id Data)
    (PolyTimeFun.id Data)) postKeep linC 1 0 cb mb eb
  obtain ⟨cx, mx, ex, hx⟩ := ctxQT_pdom
  obtain ⟨cq, mq, eq, hq⟩ := params_pdom PD R
  obtain ⟨cP, mP, eP, hP⟩ := PRuns.ptf (paramsP PD) cx mx ex
  obtain ⟨cu, mu', eu, hu⟩ := PRuns.toUnary cq mq eq
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.stage pre4 postKeep cq mq eq cu mu' eu
  obtain ⟨c5, m5, e5, h5⟩ := PRuns.stage pre5 postKeep cq mq eq cu mu' eu
  obtain ⟨c6, m6, e6, h6⟩ := PRuns.stage pre6 post6 cq mq eq cu mu' eu
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hl hs hn => by
    set P := arPar PD lam mu sigma n with hPdef
    have hq' := hq (W := W) hR lam mu sigma n hX hQ hs hn
    rw [← hPdef] at hq'
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    have en := esize_nat_le_four n
    let X0 : Data := .cons (encode (lam, mu, sigma)) (encode n)
    have hX0 : X0.size = esize lam + esize mu + esize sigma + esize n + 3 := size_X0 _ _ _ _
    have SA := hA (W := W) (K := mu) budCore_closed X0 X0 X0 _ hX (by simp)
      (pdLin hX (by omega)) (hb (W := W) lam mu sigma n hX hQ hl hs hn)
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at SA
    let X1 : Data := .cons (encode (arQ lam mu n, tPcp lam mu n)) X0
    have SP := hP (W := W) (K := mu) X1 hX (hx lam mu sigma n hX hQ hl hs hn)
    have hp : paramsP PD X1 = encode (P.k, P.m, P.s) := by
      simp only [paramsP, comp_apply, pair_apply, treeHead_cons, treeTail_cons, readNat_encode,
        encoded_apply, X1, X0, encode_prod, PD.paramsProg_eq]
      rfl
    rw [encode_data, hp, encode_data] at SP
    have ek := esize_nat_le_four P.k
    have emm := esize_nat_le_four P.m
    have ess := esize_nat_le_four P.s
    let X3 : Data := encode (P.k, P.m, P.s)
    have hX3 : X3.size = esize P.k + esize P.m + esize P.s + 2 := by
      simp only [X3, encode_prod, Data.size_cons]
      change esize P.k + (esize P.m + esize P.s + 1) + 1 = _
      omega
    have S4 := h4 (W := W) (K := mu) toUnaryProg_closed X3 (encode P.k) X3 _ hX rfl
      (hq'.of_le (by omega)) (hu (W := W) (K := mu) P.k hX (hq'.of_le (by omega)))
    let X4 : Data := .cons (encode (unary P.k)) X3
    have hX4 : X4.size = 2 * P.k + 1 + X3.size + 1 := by
      simp only [X4, Data.size_cons]
      rw [show (encode (unary P.k) : Data).size = esize (unary P.k) from rfl, esize_unary]
    have S5 := h5 (W := W) (K := mu) toUnaryProg_closed X4 (encode P.m) X4 _ hX rfl
      (hq'.of_le (by omega)) (hu (W := W) (K := mu) P.m hX (hq'.of_le (by omega)))
    let X5 : Data := .cons (encode (unary P.m)) X4
    have hX5 : X5.size = 2 * P.m + 1 + X4.size + 1 := by
      simp only [X5, Data.size_cons]
      rw [show (encode (unary P.m) : Data).size = esize (unary P.m) from rfl, esize_unary]
    have S6 := h6 (W := W) (K := mu) toUnaryProg_closed X5 (encode P.s) X5 _ hX rfl
      (hq'.of_le (by omega)) (hu (W := W) (K := mu) P.s hX (hq'.of_le (by omega)))
    rw [post6_apply] at S6
    exact PRuns.seq hX (seqProg_closed (PolyTimeFun.closed _) <|
        seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
        seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
          (stageProg_closed _ toUnaryProg_closed _)) SA <|
      PRuns.seq hX (seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
        seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
          (stageProg_closed _ toUnaryProg_closed _)) SP <|
      PRuns.seq hX (seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
          (stageProg_closed _ toUnaryProg_closed _)) S4 <|
      PRuns.seq hX (stageProg_closed _ toUnaryProg_closed _) S5 S6⟩

/-- **The running time of the parameter routine** `parProg`, on the index `n`. -/
theorem parProg_time (PD : PcpDecider) (R : Polynomial ℕ) : ∃ c m e, ∀ {W X : ℕ},
    ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W →
    PRuns W X mu c m e (parProg PD lam mu sigma) (encode n) ((family PD lam mu sigma).pd n) := by
  obtain ⟨c, m, e, h⟩ := parCore_time PD R
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hl hs hn => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    have en := esize_nat_le_four n
    exact PRuns.hardcode hX (ParRoutine.core_closed PD)
      (h (W := W) hR lam mu sigma n hX hQ hl hs hn)
      (pdLin hX (by
        simp only [encode_prod, Data.size_cons]
        change esize lam + (esize mu + esize sigma + 1) + 1 ≤ _
        omega))
      (pdLin hX (by change esize n ≤ _; omega))⟩

end MIPRE.AnswerReduction

end
