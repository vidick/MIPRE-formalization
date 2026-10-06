/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArCost

@[expose] public section

/-!
# The running time of the answer-reduced linear-constraints processor

Slice P4h of `planning/aldous-lyons-track.md`, for the complexity clause of
`TailoredAnswerReduction`. The processor's nine stages (`ArRoutine.lpCore`) are, in cost: the
parameter program (`ArRoutine.ParTime`); four calls to the input sampler through the universal
machine, each on a marginal query of a constant-size header and a question's seed bits, at most
linear in the input (`AnswerReduction.size_margQuery_le`), so that one call costs
`(λn + 1)^μ (c W X)^μ` (`margCallX_pdom`); two runs of the circuit function and two of the proof
check, polynomial-time functions run on encodings (`argCircL_eq`, `argPrfL_eq`: the stages'
arguments are encodings on every input, the input sampler's questions and the readable answers
read as bit strings); and the last stage, a polynomial-time function of the context. So the
processor's time on `(n, d)` is dominated by `(C (W + 1)^M X^E)^{μ + 1}` with `X = |d| + 1`
(`lpD_time`), for every `W` above `(λn + 1)^μ + σ + λ + n`, when `|𝒱| ≤ σ` and the input sampler
runs within `(λn + 1)^μ (|d| + 1)^μ`. Neither the input's calculator nor its processor is ever run:
they enter the circuit function's input as data.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.CL.Detyping MIPRE.SAT MIPRE.Pipeline

/-! ## The stages' arguments are encodings -/

/-- **A circuit stage's argument is the encoding of the circuit function's input**, as soon as the
hardcoded data, the index and the parameters are encodings. -/
theorem argCircL_eq (k rA rB : ℕ) (X : Data) (P : Prog × Prog × Prog) (lms : ℕ × ℕ × ℕ) (n : ℕ)
    (prm : ArParams) (hP : progsL k X = encode P) (hl : lmsL k X = encode lms)
    (hn : nL k X = encode n) (hp : AnswerReduction.res (k - 1) X = encode prm) :
    argCircL k rA rB X = encode ((P, lms, n, prm, Program.readBits (AnswerReduction.res rA X),
      Program.readBits (AnswerReduction.res rB X)) : CircIn) := by
  simp only [argCircL, ap₂_apply, treePair_apply, comp_apply, Program.encoded_apply, hP, hl, hn,
    hp, encode_prod]

/-- **A proof stage's argument is the encoding of the proof check's input**, as soon as the
parameters and the circuit are encodings. -/
theorem argPrfL_eq (k rC : ℕ) (o : PolyTimeFun LpIn Unary) (q : PolyTimeFun LpIn BitStr)
    (a : ℕ → PolyTimeFun Data Data) (X : Data) (prm : ArParams) (C : Circuit)
    (hp : AnswerReduction.res (k - 1) X = encode prm) (hC : AnswerReduction.res rC X = encode C) :
    argPrfL k rC o q a X = encode ((prm, o (preL k X), nF (preL k X), ptsF q (preL k X),
      Program.readBits (a k X), C.gates) : PrfIn) := by
  have hg : treeTail (encode C) = encode C.gates := by
    change treeTail (encode (C.inputs, C.gates)) = _
    rw [encode_prod, treeTail_cons]
  simp only [argPrfL, ap₂_apply, treePair_apply, comp_apply, Program.encoded_apply, hp, hC, hg,
    encode_prod]

/-! ## Sizes -/

/-- A question's seed bits are no longer than its field. -/
theorem length_seedL_le (k : ℕ) (q : ℕ → PolyTimeFun Data Data) (X : Data) :
    (seedL k q X).length ≤ (q k X).size := by
  simp only [seedL, comp_apply, pair_apply, ap₂_apply, const_apply, drop_apply,
    AnswerReduction.leftBP_apply, List.length_take, List.length_drop]
  have := ProductSampler.length_readBits_le (q k X)
  omega

/-- The hardcoded data `(V.progs, λ, μ, σ)`, at `K = μ`. -/
theorem lpHdat_pdom : ∃ c m e, ∀ {W X : ℕ} (P : Prog × Prog × Prog) (lam mu sigma : ℕ), 1 ≤ X →
    esize P.1 ≤ W → esize P.2.1 ≤ W → esize P.2.2 ≤ W → lam ≤ W → sigma ≤ W →
    PDom W X mu c m e (encode (P, lam, mu, sigma) : Data).size :=
  ⟨_, _, _, fun {W X} P lam mu sigma hX h1 h2 h3 hl hs => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    refine (AnswerReduction.pdLin hX (by omega : esize P.1 + esize P.2.1 + esize P.2.2 +
      (4 * lam + 1) + (4 * mu + 1) + (4 * sigma + 1) + 5 ≤ 40 * W + 40 * (mu + 1) + 40)).of_le ?_
    obtain ⟨p1, p2, p3⟩ := P
    simp only [encode_prod, Data.size_cons]
    change esize p1 + (esize p2 + esize p3 + 1) + 1 + (esize lam + (esize mu + esize sigma + 1) +
      1) + 1 ≤ _
    omega⟩

/-- **One marginal call through the universal machine**, before the machine's overhead: the input
sampler's program, the query, and the input sampler's time on it, for a query linear in `X`. -/
theorem margCallX_pdom (ℓ : ℕ) : ∃ c m e, ∀ {W X K : ℕ} (sp : Prog) (n Q : ℕ) (q : Data)
    (t : ℕ), 1 ≤ X → esize sp ≤ W → n ≤ W → Q ≤ W → q.size + 1 ≤ (4 * ℓ + 44) * (W + 1) * X →
    t ≤ Q * (q.size + 1) ^ K →
    PDom W X K c m e (esize sp + (Data.cons (encode n) q).size + t) := by
  exact ⟨_, _, _, fun {W X K} sp n Q q t hX hsp hn hQ hq ht => by
    have en := esize_nat_le_four n
    have hq' : q.size + 1 ≤ (4 * ℓ + 44) * (W + 1) ^ 1 * X ^ 1 := by
      simpa only [pow_one] using hq
    have hcall := PDom.ofCall hQ hq' ht
    have hlin : PDom W X K _ _ _ (esize sp + esize n + 1) :=
      PDom.ofAffine (a := 5) (b := 2) (by omega)
    have hqs : PDom W X K _ _ _ q.size := PDom.ofMono (c := 4 * ℓ + 44) (m := 1) (e := 1)
      (by simp only [pow_one]; omega)
    refine ((hlin.add hX hqs).add hX hcall).of_le ?_
    simp only [Data.size_cons]
    change esize sp + (esize n + q.size + 1) + t ≤ _
    omega⟩

namespace ArRoutine

variable {R : ArRoutine}

/-- **The running time of the linear-constraints processor**, on every input `(n, d)`: dominated
by `(C (W + 1)^M X^E)^{μ + 1}` for `X > |d|` and `W ≥ (λn + 1)^μ + σ + λ + n`, when `|𝒱| ≤ σ`
and the input sampler runs within `(λn + 1)^μ (|d| + 1)^μ`. -/
theorem lpD_time (ℓ : ℕ) (hR : R.ParTime) : ∃ C M E, ∀ {W X : ℕ} (V : TailoredVerifier (ℓ + 1))
    (lam mu sigma n : ℕ) (d : Data), 1 ≤ X → AnswerReduction.arg lam mu sigma n ≤ W →
    V.size ≤ sigma → V.sampler.TimeBoundAt n ((lam * n + 1) ^ mu) mu → d.size + 1 ≤ X →
    ∃ r t, PDom W X mu C M E t ∧
      (R.lpD ℓ V.progs lam mu sigma).prog.Runs (.cons (encode n) d) r t := by
  obtain ⟨cH, mH, eH, hH⟩ := lpHdat_pdom
  obtain ⟨cI, mI, eI, hI⟩ := PDom.indexInput
  obtain ⟨c0, m0, e0, h0⟩ := AnswerReduction.next_pdom cI mI eI cH mH eH
  obtain ⟨cp, mp, ep, hp⟩ := hR
  obtain ⟨c1, m1, e1, h1⟩ := PRuns.stage (ap₂ treePair argParL (PolyTimeFun.id Data))
    AnswerReduction.ParRoutine.postKeep c0 m0 e0 cp mp ep
  obtain ⟨x1c, x1m, x1e, hx1⟩ := AnswerReduction.next_pdom c0 m0 e0 cp mp ep
  obtain ⟨cm, mm, em, hm⟩ := margCallX_pdom ℓ
  obtain ⟨cu, mu', eu, hu⟩ := PRuns.univ cm mm em
  obtain ⟨c2, m2, e2, h2⟩ := PRuns.stage (ap₂ treePair (argMgL ℓ 1 xL .alice)
    (PolyTimeFun.id Data)) AnswerReduction.ParRoutine.postKeep x1c x1m x1e cu mu' eu
  obtain ⟨x2c, x2m, x2e, hx2⟩ := AnswerReduction.next_pdom x1c x1m x1e cu mu' eu
  obtain ⟨c3, m3, e3, h3⟩ := PRuns.stage (ap₂ treePair (argMgL ℓ 2 xL .bob)
    (PolyTimeFun.id Data)) AnswerReduction.ParRoutine.postKeep x2c x2m x2e cu mu' eu
  obtain ⟨x3c, x3m, x3e, hx3⟩ := AnswerReduction.next_pdom x2c x2m x2e cu mu' eu
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.stage (ap₂ treePair (argMgL ℓ 3 yL .alice)
    (PolyTimeFun.id Data)) AnswerReduction.ParRoutine.postKeep x3c x3m x3e cu mu' eu
  obtain ⟨x4c, x4m, x4e, hx4⟩ := AnswerReduction.next_pdom x3c x3m x3e cu mu' eu
  obtain ⟨c5, m5, e5, h5⟩ := PRuns.stage (ap₂ treePair (argMgL ℓ 4 yL .bob)
    (PolyTimeFun.id Data)) AnswerReduction.ParRoutine.postKeep x4c x4m x4e cu mu' eu
  obtain ⟨x5c, x5m, x5e, hx5⟩ := AnswerReduction.next_pdom x4c x4m x4e cu mu' eu
  obtain ⟨a6c, a6m, a6e, ha6⟩ := PRuns.ptf_size (argCircL 5 3 2) x5c x5m x5e
  obtain ⟨v6c, v6m, v6e, hv6⟩ := PRuns.ptf R.circF a6c a6m a6e
  obtain ⟨c6, m6, e6, h6⟩ := PRuns.stage (ap₂ treePair (argCircL 5 3 2) (PolyTimeFun.id Data))
    AnswerReduction.ParRoutine.postKeep x5c x5m x5e v6c v6m v6e
  obtain ⟨x6c, x6m, x6e, hx6⟩ := AnswerReduction.next_pdom x5c x5m x5e v6c v6m v6e
  obtain ⟨a7c, a7m, a7e, ha7⟩ := PRuns.ptf_size (argCircL 6 2 1) x6c x6m x6e
  obtain ⟨v7c, v7m, v7e, hv7⟩ := PRuns.ptf R.circF a7c a7m a7e
  obtain ⟨c7, m7, e7, h7⟩ := PRuns.stage (ap₂ treePair (argCircL 6 2 1) (PolyTimeFun.id Data))
    AnswerReduction.ParRoutine.postKeep x6c x6m x6e v7c v7m v7e
  obtain ⟨x7c, x7m, x7e, hx7⟩ := AnswerReduction.next_pdom x6c x6m x6e v7c v7m v7e
  obtain ⟨a8c, a8m, a8e, ha8⟩ := PRuns.ptf_size (argPrfL 7 1 (const (unary 0)) lX aL) x7c x7m x7e
  obtain ⟨v8c, v8m, v8e, hv8⟩ := PRuns.ptf proofConsF a8c a8m a8e
  obtain ⟨c8, m8, e8, h8⟩ := PRuns.stage (ap₂ treePair (argPrfL 7 1 (const (unary 0)) lX aL)
    (PolyTimeFun.id Data)) AnswerReduction.ParRoutine.postKeep x7c x7m x7e v8c v8m v8e
  obtain ⟨x8c, x8m, x8e, hx8⟩ := AnswerReduction.next_pdom x7c x7m x7e v8c v8m v8e
  obtain ⟨a9c, a9m, a9e, ha9⟩ := PRuns.ptf_size (argPrfL 8 1 nAF lY bL) x8c x8m x8e
  obtain ⟨v9c, v9m, v9e, hv9⟩ := PRuns.ptf proofConsF a9c a9m a9e
  obtain ⟨c9, m9, e9, h9⟩ := PRuns.stage (ap₂ treePair (argPrfL 8 1 nAF lY bL)
    (PolyTimeFun.id Data)) AnswerReduction.ParRoutine.postKeep x8c x8m x8e v9c v9m v9e
  obtain ⟨x9c, x9m, x9e, hx9⟩ := AnswerReduction.next_pdom x8c x8m x8e v9c v9m v9e
  obtain ⟨cf, mf, ef, hf⟩ := PRuns.ptf (lpFinal.comp finRead) x9c x9m x9e
  exact ⟨_, _, _, fun {W X} V lam mu sigma n d hX hW hsz hS hd => by
    obtain ⟨hQ, hs, hl, hn⟩ := le_of_arg_le hW
    have hS1 : esize V.sampler.prog ≤ W :=
      ((le_max_left _ _).trans hsz).trans hs
    have hS2 : esize V.len.prog ≤ W :=
      (((le_max_left _ _).trans (le_max_right _ _)).trans hsz).trans hs
    have hS3 : esize V.lp.prog ≤ W :=
      (((le_max_right _ _).trans (le_max_right _ _)).trans hsz).trans hs
    have hu' := selfUniversal.closed
    have hc' := R.circF.closed
    have hpf := proofConsF.closed
    set H : Data := encode (V.progs, lam, mu, sigma) with hHdef
    have pH : PDom W X mu cH mH eH H.size := hH V.progs lam mu sigma hX hS1 hS2 hS3 hl hs
    have pI : PDom W X mu cI mI eI (Data.cons (encode n) d).size := hI n d hX hn hd
    set X0 : Data := .cons H (.cons (encode n) d) with hX0def
    have pX0 : PDom W X mu c0 m0 e0 X0.size := h0 _ _ hX pI pH
    -- stage 1: the parameters
    have hpre1 : (ap₂ treePair argParL (PolyTimeFun.id Data)) X0 =
        .cons (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ)) X0 := by
      simp [argParL, lmsL, nL, hdL, inL, X0, H, encode_prod]
    have P1 := hp lam mu sigma n hX hW
    have S1 := h1 R.closed X0 _ X0 _ hX hpre1 pX0 P1
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S1
    set prm := R.params lam mu sigma n with hprm
    set X1 : Data := .cons (encode prm) X0 with hX1def
    have pX1 : PDom W X mu x1c x1m x1e X1.size := hx1 _ _ hX pX0 P1.size_le
    -- stages 2 to 5: the marginal calls
    have marg : ∀ (k : ℕ) (q : ℕ → PolyTimeFun Data Data) (w : Player) (Xk : Data),
        treeHead (progsL k Xk) = encode V.sampler.prog → nL k Xk = encode n →
        (q k Xk).size ≤ d.size →
        ∃ r, PRuns W X mu cu mu' eu selfUniversal.univ (argMgL ℓ k q w Xk) r := by
      intro k q w Xk hsp hnk hqk
      set z := seedL k q Xk
      set qd : Data := encode ((1 : ℕ), w, ℓ + 1, z, ([] : BitStr)) with hqd
      have harg : argMgL ℓ k q w Xk = .cons (encode V.sampler.prog) (.cons (encode n) qd) := by
        simp only [argMgL, ap₂_apply, treePair_apply, comp_apply, pair_apply, const_apply,
          Program.encoded_apply, hsp, hnk, hqd, z]
      have hz : z.length ≤ d.size := (length_seedL_le k q Xk).trans hqk
      have hqs : qd.size ≤ 4 * d.size + 4 * ℓ + 40 := AnswerReduction.size_margQuery_le ℓ w z d hz
      have hq' : qd.size + 1 ≤ (4 * ℓ + 44) * (W + 1) * X := by
        have h1 : 4 * d.size + 4 * ℓ + 41 ≤ (4 * ℓ + 44) * X := by nlinarith
        have h2 : (4 * ℓ + 44) * X ≤ (4 * ℓ + 44) * (W + 1) * X :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
        omega
      obtain ⟨r, t, ht, hr⟩ := hS qd
      rw [harg]
      exact ⟨r, hu V.sampler.prog (.cons (encode n) qd) r t hX hr
        (hm V.sampler.prog n ((lam * n + 1) ^ mu) qd t hX hS1 hn hQ hq' ht)⟩
    have hxd : (treeHead d).size ≤ d.size := ProductSampler.size_treeHead_le d
    have hyd : (treeHead (treeTail d)).size ≤ d.size :=
      (ProductSampler.size_treeHead_le _).trans (ProductSampler.size_treeTail_le d)
    obtain ⟨rAx, P2⟩ := marg 1 xL .alice X1
      (by simp [progsL, hdL, X1, X0, H, encode_prod]; rfl) (by simp [nL, inL, X1, X0])
      (by simpa [xL, inL, X1, X0] using hxd)
    have S2 := h2 hu' X1 _ X1 _ hX (by simp) pX1 P2
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S2
    set X2 : Data := .cons rAx X1 with hX2def
    have pX2 : PDom W X mu x2c x2m x2e X2.size := hx2 _ _ hX pX1 P2.size_le
    obtain ⟨rBx, P3⟩ := marg 2 xL .bob X2
      (by simp [progsL, hdL, X2, X1, X0, H, encode_prod]; rfl) (by simp [nL, inL, X2, X1, X0])
      (by simpa [xL, inL, X2, X1, X0] using hxd)
    have S3 := h3 hu' X2 _ X2 _ hX (by simp) pX2 P3
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S3
    set X3 : Data := .cons rBx X2 with hX3def
    have pX3 : PDom W X mu x3c x3m x3e X3.size := hx3 _ _ hX pX2 P3.size_le
    obtain ⟨rAy, P4⟩ := marg 3 yL .alice X3
      (by simp [progsL, hdL, X3, X2, X1, X0, H, encode_prod]; rfl)
      (by simp [nL, inL, X3, X2, X1, X0]) (by simpa [yL, inL, X3, X2, X1, X0] using hyd)
    have S4 := h4 hu' X3 _ X3 _ hX (by simp) pX3 P4
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S4
    set X4 : Data := .cons rAy X3 with hX4def
    have pX4 : PDom W X mu x4c x4m x4e X4.size := hx4 _ _ hX pX3 P4.size_le
    obtain ⟨rBy, P5⟩ := marg 4 yL .bob X4
      (by simp [progsL, hdL, X4, X3, X2, X1, X0, H, encode_prod]; rfl)
      (by simp [nL, inL, X4, X3, X2, X1, X0]) (by simpa [yL, inL, X4, X3, X2, X1, X0] using hyd)
    have S5 := h5 hu' X4 _ X4 _ hX (by simp) pX4 P5
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S5
    set X5 : Data := .cons rBy X4 with hX5def
    have pX5 : PDom W X mu x5c x5m x5e X5.size := hx5 _ _ hX pX4 P5.size_le
    -- stages 6 and 7: the circuits
    have e6 := argCircL_eq 5 3 2 X5 V.progs (lam, mu, sigma) n prm
      (by simp [progsL, hdL, X5, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [lmsL, hdL, X5, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [nL, inL, X5, X4, X3, X2, X1, X0])
      (by simp [AnswerReduction.res, X5, X4, X3, X2, X1])
    set c6 : CircIn := (V.progs, (lam, mu, sigma), n, prm,
      Program.readBits (AnswerReduction.res 3 X5), Program.readBits (AnswerReduction.res 2 X5))
    have pa6 : PDom W X mu a6c a6m a6e (esize c6) := by
      have := ha6 (W := W) (K := mu) X5 hX (by simpa only [esize_data] using pX5)
      rw [esize_data, e6] at this
      exact this
    have P6 := hv6 (W := W) (X := X) (K := mu) c6 hX pa6
    rw [← e6] at P6
    have S6 := h6 hc' X5 _ X5 _ hX (by simp) pX5 P6
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S6
    set X6 : Data := .cons (encode (R.circF c6)) X5 with hX6def
    have pX6 : PDom W X mu x6c x6m x6e X6.size := hx6 _ _ hX pX5 P6.size_le
    have e7 := argCircL_eq 6 2 1 X6 V.progs (lam, mu, sigma) n prm
      (by simp [progsL, hdL, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [lmsL, hdL, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [nL, inL, X6, X5, X4, X3, X2, X1, X0])
      (by simp [AnswerReduction.res, X6, X5, X4, X3, X2, X1])
    set c7 : CircIn := (V.progs, (lam, mu, sigma), n, prm,
      Program.readBits (AnswerReduction.res 2 X6), Program.readBits (AnswerReduction.res 1 X6))
    have pa7 : PDom W X mu a7c a7m a7e (esize c7) := by
      have := ha7 (W := W) (K := mu) X6 hX (by simpa only [esize_data] using pX6)
      rw [esize_data, e7] at this
      exact this
    have P7 := hv7 (W := W) (X := X) (K := mu) c7 hX pa7
    rw [← e7] at P7
    have S7 := h7 hc' X6 _ X6 _ hX (by simp) pX6 P7
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S7
    set X7 : Data := .cons (encode (R.circF c7)) X6 with hX7def
    have pX7 : PDom W X mu x7c x7m x7e X7.size := hx7 _ _ hX pX6 P7.size_le
    -- stages 8 and 9: the proof checks
    have e8 := argPrfL_eq 7 1 (const (unary 0)) lX aL X7 prm (R.circF c6)
      (by simp [AnswerReduction.res, X7, X6, X5, X4, X3, X2, X1])
      (by simp [AnswerReduction.res, X7, X6])
    set c8 : PrfIn := (prm, (const (unary 0)) (preL 7 X7), nF (preL 7 X7), ptsF lX (preL 7 X7),
      Program.readBits (aL 7 X7), (R.circF c6).gates)
    have pa8 : PDom W X mu a8c a8m a8e (esize c8) := by
      have := ha8 (W := W) (K := mu) X7 hX (by simpa only [esize_data] using pX7)
      rw [esize_data, e8] at this
      exact this
    have P8 := hv8 (W := W) (X := X) (K := mu) c8 hX pa8
    rw [← e8] at P8
    have S8 := h8 hpf X7 _ X7 _ hX (by simp) pX7 P8
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S8
    set X8 : Data := .cons (encode (proofConsF c8)) X7 with hX8def
    have pX8 : PDom W X mu x8c x8m x8e X8.size := hx8 _ _ hX pX7 P8.size_le
    have e9 := argPrfL_eq 8 1 nAF lY bL X8 prm (R.circF c7)
      (by simp [AnswerReduction.res, X8, X7, X6, X5, X4, X3, X2, X1])
      (by simp [AnswerReduction.res, X8, X7])
    set c9 : PrfIn := (prm, nAF (preL 8 X8), nF (preL 8 X8), ptsF lY (preL 8 X8),
      Program.readBits (bL 8 X8), (R.circF c7).gates)
    have pa9 : PDom W X mu a9c a9m a9e (esize c9) := by
      have := ha9 (W := W) (K := mu) X8 hX (by simpa only [esize_data] using pX8)
      rw [esize_data, e9] at this
      exact this
    have P9 := hv9 (W := W) (X := X) (K := mu) c9 hX pa9
    rw [← e9] at P9
    have S9 := h9 hpf X8 _ X8 _ hX (by simp) pX8 P9
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S9
    set X9 : Data := .cons (encode (proofConsF c9)) X8 with hX9def
    have pX9 : PDom W X mu x9c x9m x9e X9.size := hx9 _ _ hX pX8 P9.size_le
    -- the last stage
    have P10 := hf (W := W) (X := X) (K := mu) X9 hX (by simpa only [esize_data] using pX9)
    rw [encode_data] at P10
    have hc := PolyTimeFun.closed (lpFinal.comp finRead)
    have Pcore := PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S1 <|
      PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S2 <|
      PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S3 <|
      PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hu') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S4 <|
      PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S5 <|
      PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hc') <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S6 <|
      PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S7 <|
      PRuns.seq hX (seqProg_closed (AnswerReduction.stg_closed _ hpf) hc) S8 <|
      PRuns.seq hX hc S9 P10
    obtain ⟨t, ht, hr⟩ := PRuns.hardcode hX (R.lpCore_closed ℓ)
      (show PRuns _ _ _ _ _ _ (R.lpCore ℓ) (.cons H (.cons (encode n) d)) _ from Pcore) pH pI
    exact ⟨_, t, ht, hr⟩⟩

end ArRoutine

end MIPRE.Tailored.AnsRed.Typed

end
