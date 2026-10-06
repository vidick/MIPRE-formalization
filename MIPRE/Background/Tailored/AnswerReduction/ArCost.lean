/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLp
public import MIPRE.Background.AnswerReduction.DeciderCost
public import MIPRE.Foundations.CL.DetypingDeciderCost
public import MIPRE.Foundations.OracularSampler

@[expose] public section

/-!
# The running times of the answer-reduced sampler and calculator

Slice P4h of `planning/aldous-lyons-track.md`, for the complexity clause of
`TailoredAnswerReduction`. The output verifier's programs run the routine's parameter program as a
stage; everything else they run is a polynomial-time function or, in the processor, the input
sampler. So one hypothesis on the routine suffices, `ArRoutine.ParTime`: its parameter program
runs within `(c (W + 1)^m X^e)^{μ + 1}` (`MIPRE.Pipeline.PRuns`) for every `W` above
`(λn + 1)^μ + σ + λ + n` (`AnswerReduction.arg`), as the MIP* answer reduction's does
(`MIPRE.AnswerReduction.parProg_time`). Under it:

* `params_pdom`: the parameters' encoding is dominated, and with it every parameter
  (`le_size_arParams`);
* `arSampler_time`: the sampler, the product of the oracularized input sampler and the low-degree
  half, detyped (`CL.ProductSampler.prog_time`, `CL.Detyping.sampler_time`);
* `arSampler_dim_pdom`: its dimension;
* `lenD_time` and `lenD_len_pdom`: the calculator, and the lengths it outputs;
* `lenD_total`: the calculator halts on every input — the contract's `len_total`, which needs no
  hypothesis.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.CL.Detyping MIPRE.SAT MIPRE.Pipeline

/-- The four bounds `W ≥ (λn + 1)^μ + σ + λ + n` gives. -/
theorem le_of_arg_le {lam mu sigma n W : ℕ} (h : AnswerReduction.arg lam mu sigma n ≤ W) :
    (lam * n + 1) ^ mu ≤ W ∧ sigma ≤ W ∧ lam ≤ W ∧ n ≤ W := by
  simp only [AnswerReduction.arg] at h
  omega

/-- **Every parameter is below the size of the parameters' encoding.** -/
theorem le_size_arParams (t j d : ℕ) (L : PcpDims) (e : Data) :
    t + j + d + L.ℓ + L.dm + L.r + L.s ≤ (encode (arParams t j d L e) : Data).size ∧
      2 ^ j ≤ (encode (arParams t j d L e) : Data).size := by
  have h : ∀ k, (encode (unary k) : Data).size = 2 * k + 1 := esize_unary
  simp only [arParams, encode_prod, Data.size_cons, h]
  generalize 2 ^ j = M
  omega

/-- `(λ, μ, σ)`, at `K = μ`. -/
theorem lms_pdom : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma : ℕ), 1 ≤ X → lam ≤ W → sigma ≤ W →
    PDom W X mu c m e (encode ((lam, mu, sigma) : ℕ × ℕ × ℕ) : Data).size :=
  ⟨_, _, _, fun {W X} lam mu sigma hX hl hs => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    refine (AnswerReduction.pdLin hX (by omega : (4 * lam + 1) + (4 * mu + 1) + (4 * sigma + 1) +
      2 ≤ 40 * W + 40 * (mu + 1) + 40)).of_le ?_
    simp only [encode_prod, Data.size_cons]
    change esize lam + (esize mu + esize sigma + 1) + 1 ≤ _
    omega⟩

namespace ArRoutine

variable (R : ArRoutine)

/-- **The parameter program runs in polynomial time**: for every `W` above
`(λn + 1)^μ + σ + λ + n`, within `(c (W + 1)^m X^e)^{μ + 1}`. The one cost hypothesis on a
routine; the routine P4i fixes satisfies it. -/
def ParTime : Prop :=
  ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X → AnswerReduction.arg lam mu sigma n ≤ W →
    PRuns W X mu c m e R.parCore (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ))
      (encode (R.params lam mu sigma n))

variable {R}

/-- **The parameters' encoding is dominated.** -/
theorem params_pdom (hR : R.ParTime) : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X →
    AnswerReduction.arg lam mu sigma n ≤ W →
    PDom W X mu c m e (encode (R.params lam mu sigma n) : Data).size :=
  let ⟨c, m, e, h⟩ := hR
  ⟨c, m, e, fun lam mu sigma n hX hW => (h lam mu sigma n hX hW).size_le⟩

/-! ## The sampler -/

/-- The parameter program projected to the low-degree half's parameters. -/
theorem ldCore_time (hR : R.ParTime) : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X →
    AnswerReduction.arg lam mu sigma n ≤ W →
    PRuns W X mu c m e R.ldCore (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ))
      ((R.fam lam mu sigma).pd n) := by
  obtain ⟨c, m, e, h⟩ := hR
  obtain ⟨cf, mf, ef, hf⟩ := PRuns.ptf (ldPdF.comp readParams) c m e
  exact ⟨_, _, _, fun {W X} lam mu sigma n hX hW => by
    have P1 := h lam mu sigma n hX hW
    have P2 := hf (W := W) (K := mu) (encode (R.params lam mu sigma n) : Data) hX
      (by simpa only [esize_data] using P1.size_le)
    rw [encode_data, encode_data, comp_apply, readParams_encode, params, ldPdF_arParams] at P2
    exact PRuns.seq hX (PolyTimeFun.closed _) P1 P2⟩

/-- **The low-degree half's parameter program**, `(λ, μ, σ)` hardcoded. -/
theorem ldPar_time (hR : R.ParTime) : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X →
    AnswerReduction.arg lam mu sigma n ≤ W →
    PRuns W X mu c m e (R.toLd.parPF (lam, mu, sigma)) (encode n) ((R.fam lam mu sigma).pd n) := by
  obtain ⟨c, m, e, h⟩ := ldCore_time hR
  obtain ⟨cl, ml, el, hl⟩ := lms_pdom
  exact ⟨_, _, _, fun {W X} lam mu sigma n hX hW => by
    obtain ⟨-, hs, hlam, hn⟩ := le_of_arg_le hW
    have en := esize_nat_le_four n
    have P := h lam mu sigma n hX hW
    rw [encode_prod] at P
    exact PRuns.hardcode hX R.ldCore_closed P (hl lam mu sigma hX hlam hs)
      (PDom.ofAffine (a := 4) (b := 1) (by change esize n ≤ 4 * W + 1; omega))⟩

/-- The sizes of the two programs the product hardcodes are dominated. -/
theorem arProgs_size_pdom : ∃ c m e, ∀ {W X : ℕ} (sp : Prog) (lam mu sigma : ℕ), 1 ≤ X →
    esize sp ≤ W → lam ≤ W → sigma ≤ W →
    PDom W X mu c m e (esize (OracleSampler.prog sp) + esize (R.toLd.parPF (lam, mu, sigma))) := by
  obtain ⟨cl, ml, el, hl⟩ := lms_pdom
  exact ⟨_, _, _, fun {W X} sp lam mu sigma hX hsp hlam hs => by
    have h1 : esize (OracleSampler.prog sp) = esize OracleSampler.core + esize sp + 35 :=
      esize_hardcode _ _
    have h2 : esize (R.toLd.parPF (lam, mu, sigma)) =
        esize R.ldCore + (encode ((lam, mu, sigma) : ℕ × ℕ × ℕ) : Data).size + 35 :=
      esize_hardcode _ _
    rw [h1, h2]
    have hp := hl lam mu sigma hX hlam hs
    refine ((((PDom.const (esize OracleSampler.core + esize R.ldCore + 70)).add hX
      (PDom.ofLeW hsp)).add hX hp)).of_le ?_
    omega⟩

/-- **The running time of the typed answer-reduced sampler**: the product's accounting with the
oracularized sampler's and the low-degree half's parameter program's. -/
theorem arTyped_time (hR : R.ParTime) (ℓ : ℕ) : ∃ C M E, ∀ {W : ℕ} (S : Sampler (ℓ + 1))
    (lam mu sigma n : ℕ), AnswerReduction.arg lam mu sigma n ≤ W → esize S.prog ≤ W →
    S.TimeBoundAt n ((lam * n + 1) ^ mu) mu →
    (R.toLd.arTyped lam mu sigma S).TimeBoundAt n ((C * (W + 1) ^ M) ^ (mu + 1))
      (E * (mu + 1)) := by
  obtain ⟨cp, mp, ep, hpp⟩ := ldPar_time hR
  obtain ⟨cs, ms, es, hsz⟩ := arProgs_size_pdom (R := R)
  obtain ⟨cO, mO, eO, hO⟩ := OracleSampler.oracleSampler_timeBound
  obtain ⟨C, M, E, hP⟩ := ProductSampler.prog_time ldAnswerProg ldDimProg (ℓ + 1) cp mp ep cs ms es
    cO mO eO
  exact ⟨C, M, E, fun {W} S lam mu sigma n hW hSz hS d => by
    obtain ⟨hQ, hs, hl, hn⟩ := le_of_arg_le hW
    obtain ⟨r, t, hPD, hrun⟩ := hP (W := W) (K := mu) (OracleSampler.prog S.prog)
      (R.toLd.parPF (lam, mu, sigma)) n ((R.fam lam mu sigma).pd n) (cO * (W + 1) ^ mO) hn
      (fun hX => hpp lam mu sigma n hX hW) (fun hX => hsz S.prog lam mu sigma hX hSz hl hs) le_rfl
      (hO S n ((lam * n + 1) ^ mu) mu W hQ hSz hn hS) d
    exact ⟨r, t, hPD.le_final, hrun⟩⟩

/-- **The running time of the answer-reduced sampler**, detyped. -/
theorem arSampler_time (hR : R.ParTime) (ℓ : ℕ) : ∃ C M E, ∀ {W : ℕ} (S : Sampler (ℓ + 1))
    (lam mu sigma n : ℕ), AnswerReduction.arg lam mu sigma n ≤ W → esize S.prog ≤ W →
    S.TimeBoundAt n ((lam * n + 1) ^ mu) mu →
    (R.toLd.arSampler lam mu sigma S).TimeBoundAt n ((C * (W + 1) ^ M) ^ (mu + 1))
      (E * (mu + 1)) := by
  obtain ⟨cT, mT, eT, hT⟩ := arTyped_time hR ℓ
  obtain ⟨c, m, e, hD⟩ := CL.Detyping.sampler_time arGraph cT mT eT
  exact ⟨c, m, e, fun {W} S lam mu sigma n hW hSz hS =>
    hD (W := W) (K := mu) (R.toLd.arTyped lam mu sigma S) (by omega) n (le_of_arg_le hW).2.2.2
      (hT S lam mu sigma n hW hSz hS)⟩

/-- **The dimension of the answer-reduced sampler is dominated**: the graph view's bits, the input
sampler's dimension and `(2M + 1) t` bits of the low-degree half. -/
theorem arSampler_dim_pdom (hR : R.ParTime) (ℓ : ℕ) : ∃ c m e, ∀ {W X : ℕ} (S : Sampler (ℓ + 1))
    (lam mu sigma n : ℕ), 1 ≤ X → AnswerReduction.arg lam mu sigma n ≤ W → S.dim n ≤ W →
    PDom W X mu c m e ((R.toLd.arSampler lam mu sigma S).dim n) := by
  obtain ⟨c, m, e, h⟩ := params_pdom hR
  exact ⟨_, _, _, fun {W X} S lam mu sigma n hX hW hd => by
    have P := h lam mu sigma n hX hW
    obtain ⟨hle, hM⟩ := le_size_arParams ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
      (R.d lam mu sigma n) (R.L lam mu sigma n) (R.extra lam mu sigma n)
    set p := (encode (R.params lam mu sigma n) : Data).size
    have hp : (encode (arParams ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
        (R.d lam mu sigma n) (R.L lam mu sigma n) (R.extra lam mu sigma n)) : Data).size = p := rfl
    rw [hp] at hle hM
    refine ((PDom.const (graphDim (Role × LIDT.CL.Ty))).add hX ((PDom.ofLeW hd).add hX
      ((((PDom.const 2).mul P).add hX (PDom.const 1)).mul P))).of_le ?_
    change graphDim (Role × LIDT.CL.Ty) + (S.dim n + (2 * 2 ^ (R.fam lam mu sigma).j n + 1) *
      (R.fam lam mu sigma).t n) ≤ _
    have h1 : 2 * 2 ^ (R.fam lam mu sigma).j n + 1 ≤ 3 * p + 1 := by omega
    have h2 : (R.fam lam mu sigma).t n ≤ p := by omega
    have := Nat.mul_le_mul h1 h2
    nlinarith⟩

/-! ## The calculator -/

/-- **The running time of the answer-length calculator**, on every input: the parameter stage,
then the polynomial-time function `lenF`. -/
theorem lenD_time (hR : R.ParTime) : ∃ C M E, ∀ {W X : ℕ} (lam mu sigma n : ℕ) (d : Data),
    1 ≤ X → AnswerReduction.arg lam mu sigma n ≤ W → d.size + 1 ≤ X →
    ∃ r t, PDom W X mu C M E t ∧ (R.lenD lam mu sigma).prog.Runs (.cons (encode n) d) r t := by
  obtain ⟨cl, ml, el, hl⟩ := lms_pdom
  obtain ⟨cI, mI, eI, hI⟩ := PDom.indexInput
  obtain ⟨c0, m0, e0, h0⟩ := AnswerReduction.next_pdom cI mI eI cl ml el
  obtain ⟨cp, mp, ep, hp⟩ := hR
  obtain ⟨c1, m1, e1, h1⟩ := PRuns.stage (ap₂ treePair parArg (PolyTimeFun.id Data))
    AnswerReduction.ParRoutine.postKeep c0 m0 e0 cp mp ep
  obtain ⟨x1c, x1m, x1e, hx1⟩ := AnswerReduction.next_pdom c0 m0 e0 cp mp ep
  obtain ⟨cf, mf, ef, hf⟩ := PRuns.ptf (lenF.comp lenRead) x1c x1m x1e
  exact ⟨_, _, _, fun {W X} lam mu sigma n d hX hW hd => by
    obtain ⟨-, hs, hlam, hn⟩ := le_of_arg_le hW
    set H : Data := encode ((lam, mu, sigma) : ℕ × ℕ × ℕ)
    have pH : PDom W X mu cl ml el H.size := hl lam mu sigma hX hlam hs
    have pI : PDom W X mu cI mI eI (Data.cons (encode n) d).size := hI n d hX hn hd
    set X0 : Data := .cons H (.cons (encode n) d)
    have pX0 : PDom W X mu c0 m0 e0 X0.size := h0 _ _ hX pI pH
    have P1 := hp lam mu sigma n hX hW
    have hpre : (ap₂ treePair parArg (PolyTimeFun.id Data)) X0 =
        .cons (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ)) X0 := by
      simp [parArg, X0, H, encode_prod]
    have S1 := h1 R.closed X0 _ X0 _ hX hpre pX0 P1
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at S1
    set X1 : Data := .cons (encode (R.params lam mu sigma n)) X0
    have pX1 : PDom W X mu x1c x1m x1e X1.size := hx1 _ _ hX pX0 P1.size_le
    have P2 := hf (W := W) (K := mu) X1 hX (by simpa only [esize_data] using pX1)
    rw [encode_data] at P2
    have Pc := PRuns.seq hX (PolyTimeFun.closed _) S1 P2
    obtain ⟨t, ht, hr⟩ := PRuns.hardcode hX R.lenCore_closed (show PRuns _ _ _ _ _ _ R.lenCore
      (.cons H (.cons (encode n) d)) _ from Pc) pH pI
    exact ⟨_, t, ht, hr⟩⟩

/-- **The lengths the calculator outputs are dominated**: products of a codeword count, a number
of coefficients and the field width, each below a power of the parameters' size. -/
theorem lenD_len_pdom (hR : R.ParTime) : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X →
    AnswerReduction.arg lam mu sigma n ≤ W →
    ∀ x κ k, LenIs (R.lenD lam mu sigma) n x κ k → PDom W X mu c m e k := by
  obtain ⟨c, m, e, h⟩ := params_pdom hR
  exact ⟨_, _, _, fun {W X} lam mu sigma n hX hW x κ k hk => by
    have P := h lam mu sigma n hX hW
    obtain ⟨hle, hM⟩ := le_size_arParams ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
      (R.d lam mu sigma n) (R.L lam mu sigma n) (R.extra lam mu sigma n)
    set p := (encode (R.params lam mu sigma n) : Data).size
    have hp : (encode (arParams ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
        (R.d lam mu sigma n) (R.L lam mu sigma n) (R.extra lam mu sigma n)) : Data).size = p := rfl
    rw [hp] at hle hM
    rw [hk.unique (R.lenD_lenIs lam mu sigma n x κ)]
    set L := R.L lam mu sigma n
    set t := (R.fam lam mu sigma).t n
    set j := (R.fam lam mu sigma).j n
    set dd := R.d lam mu sigma n
    have P1 : PDom W X mu _ _ _ (p + 1) := P.add hX (PDom.const 1)
    refine ((PDom.const (100 * 3)).mul (P1.pow 4)).of_le ?_
    obtain ⟨i, i'⟩ := idxAt (graphOfBits x) κ
    have hA : [(rOf L .oracle).length, (lOf L .oracle).length, 1].getD i 0 ≤ 100 * (p + 1) := by
      have hr : (rOf L .oracle).length ≤ 100 * (p + 1) := by
        simp only [rOf, length_rSlots, PcpDims.m, PcpDims.nIn, PcpDims.oW]
        omega
      have hl : (lOf L .oracle).length ≤ 100 * (p + 1) := by
        simp only [lOf, length_lSlots, PcpDims.oW]
        omega
      rcases i with _ | _ | _ | i <;> simp <;> omega
    have hj : 2 ^ j * dd ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
    have hB : [1, dd + 1, 2 ^ j * dd + 1].getD i' 0 ≤ 3 * (p + 1) * (p + 1) := by
      rcases i' with _ | _ | _ | i' <;> simp <;> nlinarith
    have ht : t ≤ p + 1 := by omega
    simp only [lenOfIdx, lenPar, length_unary]
    calc [(rOf L .oracle).length, (lOf L .oracle).length, 1].getD i 0 *
          [1, dd + 1, 2 ^ j * dd + 1].getD i' 0 * t
        ≤ (100 * (p + 1)) * (3 * (p + 1) * (p + 1)) * (p + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul hA hB) ht
      _ = 100 * 3 * (p + 1) ^ 4 := by ring⟩

/-- **The calculator halts on every input** (`TailoredAnswerReduction.len_total`). -/
theorem lenD_total (R : ArRoutine) (lam mu sigma n s : ℕ) : LenTotal (R.lenD lam mu sigma) n s :=
  fun x _ κ => ⟨_, R.lenD_lenIs lam mu sigma n x κ⟩

end ArRoutine

end MIPRE.Tailored.AnsRed.Typed

end
