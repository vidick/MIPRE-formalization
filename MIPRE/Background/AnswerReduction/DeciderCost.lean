/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.ArDecider
import MIPRE.Background.AnswerReduction.ParamsCost
import MIPRE.Foundations.CL.ProductSamplerCost

/-!
# The running time of the typed answer-reduced decider

Piece AR-3f of `planning/answer-reduction.md`, for `lem:ar-typed-decider`. The decider's eight
stages (`MIPRE/Background/AnswerReduction/ArDecider`) are, in cost: the parameter routine and the
budgets' routine (`parCore_time`, `budCore_time`); four calls to the input sampler through the
universal machine, each on a marginal query no larger than the input by more than a constant
(`size_margQuery_le`), so that one call costs `Q (c |d|)^μ` (`PDom.ofCall`); two runs of the PCP
verifier and the final verdict, polynomial-time functions of the context. So the decider's time on
`(n, d)` is dominated by `(C (W + 1)^M (|d| + 1)^E)^{μ + 1}` (`typedDecider_time`), for any `W`
above `Q = (λn + 1)^μ`, `λ`, `σ`, `n` and both input programs' sizes, when the input sampler runs
within `Q (|d| + 1)^μ`, on every input — no answer is ever handed to the input decider.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine

/-! ## Sizes -/

theorem size_treeHead_le (d : Data) : (treeHead d).size ≤ d.size :=
  ProductSampler.size_treeHead_le d

theorem size_treeTail_le (d : Data) : (treeTail d).size ≤ d.size :=
  ProductSampler.size_treeTail_le d

theorem size_tails_le (k : ℕ) (d : Data) : (tails k d).size ≤ d.size := by
  induction k generalizing d with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [tails, comp_apply]
    exact (ih _).trans (size_treeTail_le d)

/-- A marginal query's oracle half is no longer than the question field it is read from. -/
theorem length_oBits_le (j i : ℕ) (X : Data) : (oBits j i X).length ≤ (inp j i X).size := by
  simp only [oBits, comp_apply, pair_apply, leftBP_apply, qBits, List.length_take]
  exact (min_le_right _ _).trans (ProductSampler.length_readBits_le _)

/-- A question field of the input is part of the input. -/
theorem size_inp_le (j i : ℕ) (hi : 1 ≤ i) (r : Data) (n : ℕ) (d : Data)
    (hX : tails j r = .cons (treeHead (tails j r)) (.cons (encode n) d)) :
    (inp j i r).size ≤ d.size := by
  simp only [inp, comp_apply]
  rw [hX, treeTail_cons]
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [tails_cons]
  exact (size_treeHead_le _).trans (size_tails_le i' d)

/-- **A marginal query is linear in the input.** -/
theorem size_margQuery_le (ℓ : ℕ) (w : Player) (ob : BitStr) (d : Data) (hob : ob.length ≤ d.size) :
    (encode ((1 : ℕ), w, ℓ + 1, ob, ([] : BitStr)) : Data).size ≤ 4 * d.size + 4 * ℓ + 40 := by
  have h1 := esize_bitStr_le ob
  have h2 := esize_nat_le_four (ℓ + 1)
  have h3 : esize w ≤ 3 := by cases w <;> decide
  have h4 : esize (1 : ℕ) ≤ 5 := by decide
  have h5 : esize ([] : BitStr) = 1 := rfl
  simp only [encode_prod, Data.size_cons]
  change esize (1 : ℕ) + (esize w + (esize (ℓ + 1) + (esize ob + esize ([] : BitStr) + 1) + 1) +
    1) + 1 ≤ _
  omega

/-- The cost of one marginal call through the universal machine, before the machine's overhead:
the input sampler's program, the query, and the input sampler's time on it. -/
theorem margCall_pdom (ℓ : ℕ) : ∃ c m e, ∀ {W X K : ℕ} (sp : Prog) (n Q : ℕ) (q : Data)
    (t : ℕ), 1 ≤ X → esize sp ≤ W → n ≤ W → Q ≤ W → q.size + 1 ≤ (4 * ℓ + 44) * (W + 1) →
    t ≤ Q * (q.size + 1) ^ K →
    PDom W X K c m e (esize sp + (Data.cons (encode n) q).size + t) := by
  exact ⟨_, _, _, fun {W X K} sp n Q q t hX hsp hn hQ hq ht => by
    have en := esize_nat_le_four n
    have hq' : q.size + 1 ≤ (4 * ℓ + 44) * (W + 1) ^ 1 * X ^ 0 := by
      simpa only [pow_zero, pow_one, Nat.mul_one] using hq
    have hcall := PDom.ofCall hQ hq' ht
    have hlin : PDom W X K _ _ _ (esize sp + esize n + 1) :=
      PDom.ofAffine (a := 5) (b := 2) (by omega)
    have hqs : PDom W X K _ _ _ q.size :=
      PDom.ofAffine (a := 4 * ℓ + 44) (b := 4 * ℓ + 44) (by nlinarith)
    refine ((hlin.add hX hqs).add hX hcall).of_le ?_
    simp only [Data.size_cons]
    change esize sp + (esize n + q.size + 1) + t ≤ _
    omega⟩

/-- A context grows by one result. -/
theorem next_pdom (c m e c' m' e' : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (x r : Data), 1 ≤ X →
    PDom W X K c m e x.size → PDom W X K c' m' e' r.size → PDom W X K C M E (Data.cons r x).size :=
  ⟨_, _, _, fun x r hX hx hr => by
    simpa only [Data.size_cons, Nat.add_comm r.size] using (hx.add hX hr).add hX (PDom.const 1)⟩

/-- The hardcoded data `(S̄, D̄, λ, μ, σ)`, at `K = μ`. -/
theorem hdat_pdom : ∃ c m e, ∀ {W X K : ℕ} (sp dp : Prog) (lam sigma : ℕ), 1 ≤ X →
    esize sp ≤ W → esize dp ≤ W → lam ≤ W → sigma ≤ W →
    PDom W X K c m e (encode (sp, dp, lam, K, sigma) : Data).size := by
  exact ⟨_, _, _, fun {W X K} sp dp lam sigma hX hsp hdp hl hs => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four K
    have es := esize_nat_le_four sigma
    refine (pdLin hX (by omega : esize sp + esize dp + (4 * lam + 1) + (4 * K + 1) +
      (4 * sigma + 1) + 4 ≤ 40 * W + 40 * (K + 1) + 40)).of_le ?_
    simp only [encode_prod, Data.size_cons]
    change esize sp + (esize dp + (esize lam + (esize K + esize sigma + 1) + 1) + 1) + 1 ≤ _
    omega⟩

/-- The index and the rest of the input. -/
theorem input_pdom (cd md ed : ℕ) : ∃ c m e, ∀ {W X K : ℕ} (n : ℕ) (d : Data), 1 ≤ X →
    n ≤ W → PDom W X K cd md ed d.size → PDom W X K c m e (Data.cons (encode n) d).size := by
  exact ⟨_, _, _, fun {W X K} n d hX hn hd => by
    have en := esize_nat_le_four n
    refine ((PDom.ofAffine (a := 4) (b := 2) (by omega : esize n + 1 ≤ 4 * W + 2)).add hX
      hd).of_le ?_
    simp only [Data.size_cons]
    change esize n + d.size + 1 ≤ _
    omega⟩

/-- **The running time of the typed answer-reduced decider**, on every input `(n, d)` whose size is
dominated and whose two question fields have oracle halves no longer than `W` — as the detyped
decider's inputs have: their oracle halves are the input sampler's questions. -/
theorem typedDecider_time (ℓ : ℕ) (PD : PcpDecider) (R : Polynomial ℕ) (cd md ed : ℕ) :
    ∃ C M E, ∀ {W X : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ), ParamsBound PD R →
    1 ≤ X → 1 ≤ mu → arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W → esize V.sampler.prog ≤ W →
    esize V.decider.prog ≤ W → V.sampler.TimeBoundAt n (arQ lam mu n) mu →
    ∀ d : Data, PDom W X mu cd md ed d.size →
    (readBits (treeHead (treeTail d))).length ≤ W + (dB PD lam mu sigma n).length →
    (readBits (treeHead (treeTail (treeTail (treeTail d))))).length ≤
      W + (dB PD lam mu sigma n).length →
    ∃ r t, PDom W X mu C M E t ∧
      (typedDecider PD V lam mu sigma).prog.Runs (.cons (encode n) d) r t := by
  obtain ⟨cH, mH, eH, hH⟩ := hdat_pdom
  obtain ⟨cI, mI, eI, hI⟩ := input_pdom cd md ed
  obtain ⟨c0, m0, e0, h0⟩ := next_pdom cI mI eI cH mH eH
  obtain ⟨cp, mp, ep, hp⟩ := parCore_time PD R
  obtain ⟨c1, m1, e1, h1⟩ := PRuns.stage (ap₂ treePair (argPar 0) (PolyTimeFun.id Data))
    postKeep c0 m0 e0 cp mp ep
  obtain ⟨x1c, x1m, x1e, hx1⟩ := next_pdom c0 m0 e0 cp mp ep
  obtain ⟨cb, mb, eb, hb⟩ := budCore_time
  obtain ⟨c2, m2, e2, h2⟩ := PRuns.stage (ap₂ treePair (argPar 1) (PolyTimeFun.id Data))
    postKeep x1c x1m x1e cb mb eb
  obtain ⟨x2c, x2m, x2e, hx2⟩ := next_pdom x1c x1m x1e cb mb eb
  obtain ⟨cm, mm, em, hm⟩ := margCall_pdom ℓ
  obtain ⟨cu, mu', eu, hu⟩ := PRuns.univ cm mm em
  obtain ⟨c3, m3, e3, h3⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 2 2 .alice) (PolyTimeFun.id Data))
    postKeep x2c x2m x2e cu mu' eu
  obtain ⟨x3c, x3m, x3e, hx3⟩ := next_pdom x2c x2m x2e cu mu' eu
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 3 2 .bob) (PolyTimeFun.id Data))
    postKeep x3c x3m x3e cu mu' eu
  obtain ⟨x4c, x4m, x4e, hx4⟩ := next_pdom x3c x3m x3e cu mu' eu
  obtain ⟨c5, m5, e5, h5⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 4 4 .alice) (PolyTimeFun.id Data))
    postKeep x4c x4m x4e cu mu' eu
  obtain ⟨x5c, x5m, x5e, hx5⟩ := next_pdom x4c x4m x4e cu mu' eu
  obtain ⟨c6, m6, e6, h6⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 5 4 .bob) (PolyTimeFun.id Data))
    postKeep x5c x5m x5e cu mu' eu
  obtain ⟨x6c, x6m, x6e, hx6⟩ := next_pdom x5c x5m x5e cu mu' eu
  obtain ⟨a7c, a7m, a7e, ha7⟩ := PRuns.ptf_size (argVer 6 2 1 5 3 2) x6c x6m x6e
  obtain ⟨v7c, v7m, v7e, hv7⟩ := PRuns.ptf PD.verify a7c a7m a7e
  obtain ⟨c7, m7, e7, h7⟩ := PRuns.stage (ap₂ treePair (argVer 6 2 1 5 3 2) (PolyTimeFun.id Data))
    postKeep x6c x6m x6e v7c v7m v7e
  obtain ⟨x7c, x7m, x7e, hx7⟩ := next_pdom x6c x6m x6e v7c v7m v7e
  obtain ⟨a8c, a8m, a8e, ha8⟩ := PRuns.ptf_size (argVer 7 4 3 6 2 1) x7c x7m x7e
  obtain ⟨v8c, v8m, v8e, hv8⟩ := PRuns.ptf PD.verify a8c a8m a8e
  obtain ⟨c8, m8, e8, h8⟩ := PRuns.stage (ap₂ treePair (argVer 7 4 3 6 2 1) (PolyTimeFun.id Data))
    postKeep x7c x7m x7e v8c v8m v8e
  obtain ⟨x8c, x8m, x8e, hx8⟩ := next_pdom x7c x7m x7e v8c v8m v8e
  obtain ⟨cf, mf, ef, hf⟩ := PRuns.ptf (verdictP.comp readV) x8c x8m x8e
  exact ⟨_, _, _, fun {W X} V lam mu sigma n hR hX hmu hQ hl hs hn hsp hdp hS d hd hxd hyd => by
    have hu' := selfUniversal.closed
    have hv' := PD.verify.closed
    set H : Data := encode (V.sampler.prog, V.decider.prog, lam, mu, sigma) with hHdef
    have pH : PDom W X mu cH mH eH H.size :=
      hH V.sampler.prog V.decider.prog lam sigma hX hsp hdp hl hs
    have pI : PDom W X mu cI mI eI (Data.cons (encode n) d).size :=
      hI n d hX hn hd
    set X0 : Data := .cons H (.cons (encode n) d) with hX0def
    have pX0 : PDom W X mu c0 m0 e0 X0.size := h0 _ _ hX pI pH
    -- stage 1
    have hpre1 : (ap₂ treePair (argPar 0) (PolyTimeFun.id Data)) X0 =
        .cons (.cons (encode (lam, mu, sigma)) (encode n)) X0 := by
      simp [argPar, lmsD, hdat, inp, X0, H, encode_prod]
    have P1 := hp (W := W) (X := X) hR lam mu sigma n hX hmu hQ hl hs hn
    have S1 := h1 (ParRoutine.core_closed PD) X0 _ X0 _ hX hpre1 pX0 P1
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S1
    set X1 : Data := .cons ((family PD lam mu sigma).pd n) X0 with hX1def
    have pX1 : PDom W X mu x1c x1m x1e X1.size := hx1 _ _ hX pX0 P1.size_le
    -- stage 2
    have hpre2 : (ap₂ treePair (argPar 1) (PolyTimeFun.id Data)) X1 =
        .cons (.cons (encode (lam, mu, sigma)) (encode n)) X1 := by
      simp [argPar, lmsD, hdat, inp, X1, X0, H, encode_prod]
    have P2 := hb (W := W) (X := X) lam mu sigma n hX hmu hQ hl hs hn
    have S2 := h2 budCore_closed X1 _ X1 _ hX hpre2 pX1 P2
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S2
    set X2 : Data := .cons (encode (arQ lam mu n, tPcp lam mu n)) X1 with hX2def
    have pX2 : PDom W X mu x2c x2m x2e X2.size := hx2 _ _ hX pX1 P2.size_le
    -- stages 3 to 6: the marginals
    have marg : ∀ (j i : ℕ) (w : Player) (Xj : Data),
        spD j Xj = encode V.sampler.prog → inp j 0 Xj = encode n →
        pdD j Xj = (family PD lam mu sigma).pd n →
        (readBits (inp j i Xj)).length ≤ W + (dB PD lam mu sigma n).length →
        ∃ r, PRuns W X mu cu mu' eu selfUniversal.univ (argMarg ℓ j i w Xj) r := by
      intro j i w Xj hspj hnj hpdj hlen
      rw [argMarg_general V n j i w Xj hspj hnj]
      set q : Data := encode ((1 : ℕ), w, ℓ + 1, oBits j i Xj, ([] : BitStr))
      have hob : (oBits j i Xj).length ≤ W := by
        obtain ⟨-, -, hdim⟩ := pdD_eq PD lam mu sigma n Xj hpdj
        simp only [oBits, comp_apply, pair_apply, hdim, leftBP_apply, qBits, List.length_take]
        omega
      have hq : q.size + 1 ≤ (4 * ℓ + 44) * (W + 1) := by
        have : q.size ≤ 4 * W + 4 * ℓ + 40 := by
          have h := esize_bitStr_le (oBits j i Xj)
          have h2 := esize_nat_le_four (ℓ + 1)
          have h3 : esize w ≤ 3 := by cases w <;> decide
          have h4 : esize (1 : ℕ) ≤ 5 := by decide
          have h5 : esize ([] : BitStr) = 1 := rfl
          simp only [q, encode_prod, Data.size_cons]
          change esize (1 : ℕ) + (esize w + (esize (ℓ + 1) + (esize (oBits j i Xj) +
            esize ([] : BitStr) + 1) + 1) + 1) + 1 ≤ _
          omega
        nlinarith
      obtain ⟨r, t, ht, hr⟩ := hS q
      exact ⟨r, hu V.sampler.prog (.cons (encode n) q) r t hX hr
        (hm V.sampler.prog n (arQ lam mu n) q t hX hsp hn hQ hq ht)⟩
    obtain ⟨rxA, P3⟩ := marg 2 2 .alice X2
      (by simp [spD, hdat, X2, X1, X0, H, encode_prod]) (by simp [inp, X2, X1, X0])
      (by simp [pdD, res, X2, X1]) (by simpa [inp, X2, X1, X0, tails, comp_apply] using hxd)
    have S3 := h3 hu' X2 _ X2 _ hX (by simp) pX2 P3
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S3
    set X3 : Data := .cons rxA X2 with hX3def
    have pX3 : PDom W X mu x3c x3m x3e X3.size := hx3 _ _ hX pX2 P3.size_le
    obtain ⟨rxB, P4⟩ := marg 3 2 .bob X3
      (by simp [spD, hdat, X3, X2, X1, X0, H, encode_prod]) (by simp [inp, X3, X2, X1, X0])
      (by simp [pdD, res, X3, X2, X1]) (by simpa [inp, X3, X2, X1, X0, tails, comp_apply] using hxd)
    have S4 := h4 hu' X3 _ X3 _ hX (by simp) pX3 P4
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S4
    set X4 : Data := .cons rxB X3 with hX4def
    have pX4 : PDom W X mu x4c x4m x4e X4.size := hx4 _ _ hX pX3 P4.size_le
    obtain ⟨ryA, P5⟩ := marg 4 4 .alice X4
      (by simp [spD, hdat, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [inp, X4, X3, X2, X1, X0]) (by simp [pdD, res, X4, X3, X2, X1])
      (by simpa [inp, X4, X3, X2, X1, X0, tails, comp_apply] using hyd)
    have S5 := h5 hu' X4 _ X4 _ hX (by simp) pX4 P5
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S5
    set X5 : Data := .cons ryA X4 with hX5def
    have pX5 : PDom W X mu x5c x5m x5e X5.size := hx5 _ _ hX pX4 P5.size_le
    obtain ⟨ryB, P6⟩ := marg 5 4 .bob X5
      (by simp [spD, hdat, X5, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [inp, X5, X4, X3, X2, X1, X0]) (by simp [pdD, res, X5, X4, X3, X2, X1])
      (by simpa [inp, X5, X4, X3, X2, X1, X0, tails, comp_apply] using hyd)
    have S6 := h6 hu' X5 _ X5 _ hX (by simp) pX5 P6
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S6
    set X6 : Data := .cons ryB X5 with hX6def
    have pX6 : PDom W X mu x6c x6m x6e X6.size := hx6 _ _ hX pX5 P6.size_le
    -- stages 7 and 8: the game checks
    obtain ⟨c7i, e7⟩ : ∃ c : PcpInput, argVer 6 2 1 5 3 2 X6 = encode c :=
      ⟨_, argVer_general V 6 2 1 5 3 2 X6
        (by simp [dpD, hdat, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])⟩
    have pa7 : PDom W X mu a7c a7m a7e (esize c7i) := by
      have := ha7 (W := W) (K := mu) X6 hX pX6
      rw [e7] at this
      exact this
    have P7 := hv7 (W := W) (X := X) (K := mu) c7i hX pa7
    rw [← e7] at P7
    have S7 := h7 hv' X6 _ X6 _ hX (by simp) pX6 P7
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S7
    set X7 : Data := .cons (encode (PD.verify c7i)) X6 with hX7def
    have pX7 : PDom W X mu x7c x7m x7e X7.size := hx7 _ _ hX pX6 P7.size_le
    obtain ⟨c8i, e8⟩ : ∃ c : PcpInput, argVer 7 4 3 6 2 1 X7 = encode c :=
      ⟨_, argVer_general V 7 4 3 6 2 1 X7
        (by simp [dpD, hdat, X7, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])⟩
    have pa8 : PDom W X mu a8c a8m a8e (esize c8i) := by
      have := ha8 (W := W) (K := mu) X7 hX pX7
      rw [e8] at this
      exact this
    have P8 := hv8 (W := W) (X := X) (K := mu) c8i hX pa8
    rw [← e8] at P8
    have S8 := h8 hv' X7 _ X7 _ hX (by simp) pX7 P8
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S8
    set X8 : Data := .cons (encode (PD.verify c8i)) X7 with hX8def
    have pX8 : PDom W X mu x8c x8m x8e X8.size := hx8 _ _ hX pX7 P8.size_le
    -- the verdict
    have P9 := hf (W := W) (X := X) (K := mu) X8 hX pX8
    rw [encode_data] at P9
    have hc := PolyTimeFun.closed (verdictP.comp readV)
    have Pcore := PRuns.seq hX (seqProg_closed (stg_closed _ budCore_closed) <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S1 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S2 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hv') <|
        seqProg_closed (stg_closed _ hv') hc) S3 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S4 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hv') <|
        seqProg_closed (stg_closed _ hv') hc) S5 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S6 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hv') hc) S7 <|
      PRuns.seq hX hc S8 P9
    obtain ⟨t, ht, hr⟩ := PRuns.hardcode hX (core_closed PD ℓ) (show PRuns _ _ _ _ _ _ (core PD ℓ)
      (.cons H (.cons (encode n) d)) _ from Pcore) pH pI
    exact ⟨_, t, ht, hr⟩⟩

end MIPRE.AnswerReduction

end
