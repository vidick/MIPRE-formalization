/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SamplerCost
import MIPRE.Background.AnswerReduction.DeciderCost
import MIPRE.Foundations.CL.DetypingDeciderCost
import MIPRE.Foundations.CL.ProgBuild

/-!
# The answer-reduced verifier

Piece AR-3f of `planning/answer-reduction.md`, concluded: the output of answer reduction as a
normal form verifier (`arVerifier`), the typed answer-reduced verifier through the detyping
compiler at the answer cut `cutVal` (`arCut`); its programs as polynomial-time functions of the
input programs and `(λ, μ, σ)` (`arSamplerProg`, `arCompute`), the sampler's of the input sampler's
alone; and its complexity clause (`arVerifier_within`), the `within` field of the
`AnswerReduction` contract.

The answer cut `32 (k + 1)(m' + 7)^2` is above the length `4 (k + 1) cnt + 1` of the encoding of
every well-formed answer, `cnt ≤ (m' + 6)(7 m' + 1)` field elements of `k` bits
(`MIPRE/Background/AnswerReduction/AnswerFormat`), which completeness (AR-4) needs; and it is
polynomial in the PCP's parameters, which the complexity clause needs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg

/-! ## The answer cut -/

/-- The answer cut, `32 (k + 1)(m' + 7)^2`. -/
def cutVal (P : PcpParams) : ℕ := 32 * ((P.k + 1) * (P.m' + 7) * (P.m' + 7))

/-- The answer cut, from the parameters `pd n`, twice. -/
def cutP : PolyTimeFun Data (ℕ × ℕ) :=
  let k1 : PolyTimeFun Data Unary := (const ()).cons (readU.comp treeHead)
  let m7 : PolyTimeFun Data Unary :=
    ap₂ append (readU.comp (treeHead.comp treeTail)) (const (unary 7))
  let L : PolyTimeFun Data Unary := (ParRoutine.timesU 32).comp
    (LowDegree.DegreeArithmetic.mulUnaryProg.comp
      ((LowDegree.DegreeArithmetic.mulUnaryProg.comp (k1.pair m7)).pair m7))
  let Ln : PolyTimeFun Data ℕ := addUnary.comp ((const 0).pair L)
  Ln.pair Ln

variable (PD : PcpDecider) (lam mu sigma : ℕ)

theorem cutP_pd (n : ℕ) :
    cutP ((family PD lam mu sigma).pd n) =
      (cutVal (arPar PD lam mu sigma n), cutVal (arPar PD lam mu sigma n)) := by
  obtain ⟨h1, h2, -⟩ := pd_heads PD lam mu sigma n
  simp only [cutP, pair_apply, comp_apply, addUnary_apply, const_apply, cons_apply, h1, h2,
    ap₂_apply, append_apply, ParRoutine.timesU_apply, LowDegree.DegreeArithmetic.mulUnaryProg_apply,
    length_unary, List.length_cons, List.length_append, cutVal]
  simp [unary]

/-- The cutoff program: the parameter routine, then `cutP`. -/
def cutProg : Prog := seqProg (parProg PD lam mu sigma) cutP.code

/-- **The cutoff program of answer reduction**: both cuts `cutVal`. -/
def arCut : CL.Detyping.CutoffProgram where
  inner n := cutVal (arPar PD lam mu sigma n)
  outer n := cutVal (arPar PD lam mu sigma n)
  prog := cutProg PD lam mu sigma
  closed := seqProg_closed (parProg_closed PD lam mu sigma) cutP.closed
  runs n := by
    obtain ⟨t, h⟩ := parProg_runs PD lam mu sigma n
    obtain ⟨t', -, h'⟩ := cutP.computes ((family PD lam mu sigma).pd n)
    rw [encode_data, cutP_pd] at h'
    exact ⟨_, seqProg_runs cutP.closed h h'⟩

/-! ## The verifier -/

/-- **The answer-reduced verifier** of `V` at `(λ, μ, σ)`: the typed answer-reduced verifier
through the detyping compiler, at the cutoff `arCut`. -/
def arVerifier {ℓ : ℕ} (V : Verifier (ℓ + 1)) : Verifier (level ℓ + 2) :=
  CL.Detyping.DeciderProgram.verifier graph (typedSampler V.sampler PD lam mu sigma)
    (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) (by unfold level; omega)
    (total PD V lam mu sigma)

/-! ## The programs, in polynomial time -/

/-- The parameter routine's program, from `(λ, μ, σ)`. -/
def parPF : PolyTimeFun (ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (ℕ × ℕ × ℕ)).comp ((const (ParRoutine.core PD)).pair (PolyTimeFun.id _))

theorem parPF_apply : parPF PD (lam, mu, sigma) = parProg PD lam mu sigma := rfl

/-- The typed sampler's program, from the input sampler's and `(λ, μ, σ)`. -/
def typedPF (ℓ : ℕ) : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (Prog × ℕ × Prog)).comp
    ((const (ProductSampler.core answerProg dimProg)).pair
      ((OracleSampler.samplerProgFun.comp fst).pair ((const (ℓ + 1)).pair ((parPF PD).comp snd))))

theorem typedPF_apply {ℓ : ℕ} (S : Sampler (ℓ + 1)) :
    typedPF PD ℓ (S.prog, lam, mu, sigma) = (typedSampler S PD lam mu sigma).prog := rfl

/-- **The answer-reduced sampler's program**, from the input sampler's and `(λ, μ, σ)`. -/
def arSamplerProg (ℓ : ℕ) : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog :=
  (ProgBuild.routeOneCallF (CL.Detyping.Program.route graph)
    (CL.Detyping.Program.post (CL.Detyping.graphDim ArTy))).comp (typedPF PD ℓ)

theorem arSamplerProg_eq {ℓ : ℕ} (V : Verifier (ℓ + 1)) :
    arSamplerProg PD ℓ (V.sampler.prog, lam, mu, sigma) =
      (arVerifier PD lam mu sigma V).sampler.prog := rfl

/-- The typed decider's program, from the input programs and `(λ, μ, σ)`. -/
def typedDPF (ℓ : ℕ) : PolyTimeFun ((Prog × Prog) × ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (Prog × Prog × ℕ × ℕ × ℕ)).comp ((const (core PD ℓ)).pair
    ((fst.comp fst).pair ((snd.comp fst).pair snd)))

/-- The cutoff program, from `(λ, μ, σ)`. -/
def cutPF : PolyTimeFun (ℕ × ℕ × ℕ) Prog :=
  ProgBuild.letF.comp ((parPF PD).pair (const cutP.code))

/-- **The answer-reduced decider's program** (`ComputeAnsVerifier`), from the input programs and
`(λ, μ, σ)`. -/
def arCompute (ℓ : ℕ) : PolyTimeFun ((Prog × Prog) × ℕ × ℕ × ℕ) Prog :=
  ProgBuild.letF.comp
    (((ProgBuild.routeOneCallF CL.Detyping.DeciderProgram.dimensionRoute
        CL.Detyping.DeciderProgram.pairPost).comp ((typedPF PD ℓ).comp ((fst.comp fst).pair snd))).pair
      (ProgBuild.letF.comp
        (((ProgBuild.routeOneCallF CL.Detyping.DeciderProgram.cutoffRoute
            CL.Detyping.DeciderProgram.pairPost).comp ((cutPF PD).comp snd)).pair
          ((ProgBuild.routeOneCallF (CL.Detyping.DeciderProgram.route graph)
            CL.Detyping.DeciderProgram.post).comp (typedDPF PD ℓ)))))

theorem arCompute_eq {ℓ : ℕ} (V : Verifier (ℓ + 1)) :
    arCompute PD ℓ ((V.sampler.prog, V.decider.prog), lam, mu, sigma) =
      (arVerifier PD lam mu sigma V).decider.prog := rfl

/-- **The sampler depends only on the input sampler** and `(λ, μ, σ)`
(`lem:ar-sampler-independence`). -/
theorem arVerifier_sampler {ℓ : ℕ} (V V' : Verifier (ℓ + 1)) (h : V.sampler = V'.sampler) :
    (arVerifier PD lam mu sigma V).sampler = (arVerifier PD lam mu sigma V').sampler := by
  simp only [arVerifier, CL.Detyping.DeciderProgram.verifier, h]

/-! ## The complexity clause -/

section Within

variable (R : Polynomial ℕ)

/-- The cutoff program's time. -/
theorem arCut_time : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W →
    PRuns W X mu c m e (arCut PD lam mu sigma).prog (encode n)
      (encode ((arCut PD lam mu sigma).inner n, (arCut PD lam mu sigma).outer n)) := by
  obtain ⟨cp, mp, ep, hp⟩ := parProg_time PD R
  obtain ⟨cc, mc, ec, hc⟩ := PRuns.ptf cutP cp mp ep
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hl hs hn => by
    have P1 := hp (W := W) (X := X) hR lam mu sigma n hX hQ hl hs hn
    have P2 := hc (W := W) (X := X) (K := mu) ((family PD lam mu sigma).pd n) hX P1.size_le
    rw [encode_data, cutP_pd] at P2
    exact PRuns.seq hX cutP.closed P1 P2⟩

/-- The PCP's parameters, in the form the cut and the dimension use. -/
theorem parA_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → sigma ≤ W → n ≤ W →
    PDom W X mu c m e (20 * ((arPar PD lam mu sigma n).k + (arPar PD lam mu sigma n).m +
      (arPar PD lam mu sigma n).s) + 20) := by
  obtain ⟨c, m, e, h⟩ := params_pdom PD R
  exact ⟨c, m, e, fun hR lam mu sigma n hX hQ hs hn => h hR lam mu sigma n hX hQ hs hn⟩

/-- The answer cut is dominated. -/
theorem cutVal_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → sigma ≤ W → n ≤ W → PDom W X mu c m e (cutVal (arPar PD lam mu sigma n)) := by
  obtain ⟨c, m, e, h⟩ := parA_pdom PD R
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hs hn => by
    have hA := h (W := W) (X := X) hR lam mu sigma n hX hQ hs hn
    set P := arPar PD lam mu sigma n
    have h1 : P.k + 1 ≤ 20 * (P.k + P.m + P.s) + 20 := by omega
    have h2 : P.m' + 7 ≤ 20 * (P.k + P.m + P.s) + 20 := by simp only [PcpParams.m']; omega
    refine ((PDom.const 32).mul (hA.pow 3)).of_le ?_
    simp only [cutVal]
    refine Nat.mul_le_mul_left _ ?_
    calc (P.k + 1) * (P.m' + 7) * (P.m' + 7)
        ≤ (20 * (P.k + P.m + P.s) + 20) * (20 * (P.k + P.m + P.s) + 20) *
          (20 * (P.k + P.m + P.s) + 20) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h2
      _ = _ := by ring⟩

/-- The PCP half's width is dominated. -/
theorem pcpWidth_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → sigma ≤ W → n ≤ W →
    PDom W X mu c m e (pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k) := by
  obtain ⟨c, m, e, h⟩ := parA_pdom PD R
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hs hn => by
    have hA := h (W := W) (X := X) hR lam mu sigma n hX hQ hs hn
    set P := arPar PD lam mu sigma n
    refine (hA.pow 2).of_le ?_
    rw [pcpDim_eq]
    calc (10 * P.m + 2 * P.s + 16) * P.k
        ≤ (20 * (P.k + P.m + P.s) + 20) * (20 * (P.k + P.m + P.s) + 20) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring⟩

/-- A bound on the size of the answer-reduced types' encodings. -/
theorem exists_esize_arTy_le : ∃ c, ∀ u : ArTy, esize u ≤ c :=
  ⟨Finset.univ.sup (fun u : ArTy => esize u), fun u => Finset.le_sup (Finset.mem_univ u)⟩

/-- The typed inputs the router hands the typed decider are dominated. -/
theorem typedArg_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n s : ℕ),
    1 ≤ X → arQ lam mu n ≤ W → sigma ≤ W → n ≤ W →
    s ≤ W + pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k →
    ∀ (u v : ArTy) (x y a b : BitStr), x.length = s → y.length = s →
    a.length ≤ cutVal (arPar PD lam mu sigma n) → b.length ≤ cutVal (arPar PD lam mu sigma n) →
    PDom W X mu c m e (encode (u, x, v, y, a, b) : Data).size := by
  obtain ⟨cA, hA⟩ := exists_esize_arTy_le
  obtain ⟨cw, mw, ew, hw⟩ := pcpWidth_pdom PD R
  obtain ⟨cc, mc, ec, hc⟩ := cutVal_pdom PD R
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n s hX hQ hs hn hsw u v x y a b hx hy ha hb => by
    have pw := hw (W := W) (X := X) hR lam mu sigma n hX hQ hs hn
    have pc := hc (W := W) (X := X) hR lam mu sigma n hX hQ hs hn
    have pW : PDom W X mu 1 1 0 W := PDom.ofLeW le_rfl
    have e1 := esize_bitStr_le x
    have e2 := esize_bitStr_le y
    have e3 := esize_bitStr_le a
    have e4 := esize_bitStr_le b
    have hu := hA u
    have hv := hA v
    refine ((((PDom.const 8).mul (pW.add hX pw)).add hX ((PDom.const 8).mul pc)).add hX
      (PDom.const (2 * cA + 10))).of_le ?_
    simp only [encode_prod, Data.size_cons]
    change esize u + (esize x + (esize v + (esize y + (esize a + esize b + 1) + 1) + 1) + 1) + 1 ≤ _
    omega⟩

/-- The detyped sampler's dimension is dominated. -/
theorem dim_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n d : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → sigma ≤ W → n ≤ W → d ≤ W →
    PDom W X mu c m e (CL.Detyping.graphDim ArTy + (d +
      pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k)) := by
  obtain ⟨cw, mw, ew, hw⟩ := pcpWidth_pdom PD R
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n d hX hQ hs hn hd => by
    have pw := hw (W := W) (X := X) hR lam mu sigma n hX hQ hs hn
    exact ((PDom.const (CL.Detyping.graphDim ArTy)).add hX ((PDom.ofLeW hd).add hX pw))⟩

/-- A monomial bound below the output bound. -/
theorem pow_le_pow_of_le {W K c m C M : ℕ} (hc : c ≤ C) (hm : m ≤ M) :
    (c * (W + 1) ^ m) ^ (K + 1) ≤ (C * (W + 1) ^ M) ^ (K + 1) :=
  Nat.pow_le_pow_left (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm)) _

/-- **The complexity clause of answer reduction** (`within` of the `AnswerReduction` contract):
an input within `inBudget λ μ n` with `|𝒮|, |𝒟| ≤ σ` gives an output within
`outBound bound λ μ σ n` at degree `outDegree deg μ`, rejecting longer answers, for a polynomial
`bound` and a degree `deg` depending only on the PCP. -/
theorem arVerifier_within (ℓ : ℕ) (hR : ParamsBound PD R) : ∃ (bound : Polynomial ℕ) (deg : ℕ),
    ∀ (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ), V.Within n (inBudget lam mu n) →
      V.size ≤ sigma → (arVerifier PD lam mu sigma V).Within n
        (Budget.uniform (outBound bound lam mu sigma n) (outDegree deg mu)) := by
  obtain ⟨cT, mT, eT, hT⟩ := typedSampler_time ℓ PD R
  obtain ⟨cs, ms, ds, hs⟩ := CL.Detyping.sampler_time graph cT mT eT
  obtain ⟨cC, mC, eC, hC⟩ := arCut_time PD R
  obtain ⟨cd, md, ed, hd⟩ := typedArg_pdom PD R
  obtain ⟨cD, mD, eD, hD⟩ := typedDecider_time ℓ PD R cd md ed
  obtain ⟨cP, mP, eP, hP⟩ := CL.Detyping.DeciderProgram.prog_time graph cT mT eT cC mC eC cD mD eD
  obtain ⟨cm, mm, em, hdim⟩ := dim_pdom PD R
  obtain ⟨cc, mc, ec, hcut⟩ := cutVal_pdom PD R
  refine ⟨Polynomial.C (cs + cP + cm + cc) * (Polynomial.X + 1) ^ (ms + mP + mm + mc), ds + eP,
    fun V lam mu sigma n hV hsz => ?_⟩
  set W := arg lam mu sigma n with hWdef
  have hQ : arQ lam mu n ≤ W := by simp only [hWdef, arg, arQ]; omega
  have hl : lam ≤ W := by simp only [hWdef, arg]; omega
  have hs' : sigma ≤ W := by simp only [hWdef, arg]; omega
  have hn : n ≤ W := by simp only [hWdef, arg]; omega
  have hSz : esize V.sampler.prog ≤ W :=
    ((le_max_left _ _).trans hsz).trans hs'
  have hDz : esize V.decider.prog ≤ W :=
    ((le_max_right _ _).trans hsz).trans hs'
  have hS : V.sampler.TimeBoundAt n (arQ lam mu n) mu := hV.sampler_time
  have hVd : V.sampler.dim n ≤ W := hV.sampler_dim.trans hQ
  have hbd : outBound (Polynomial.C (cs + cP + cm + cc) * (Polynomial.X + 1) ^ (ms + mP + mm + mc))
      lam mu sigma n = ((cs + cP + cm + cc) * (W + 1) ^ (ms + mP + mm + mc)) ^ (mu + 1) := by
    simp [outBound, hWdef]
  have hTS := hT (W := W) V.sampler lam mu sigma n hR hQ hl hs' hn hSz hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the sampler's time
    simp only [Budget.uniform_S, Budget.uniform_k, hbd, outDegree]
    exact (hs (W := W) (K := mu) (typedSampler V.sampler PD lam mu sigma) (by unfold level; omega)
      n hn hTS).mono (pow_le_pow_of_le (by omega) (by omega))
      (Nat.mul_le_mul_right _ (by omega))
  · -- the dimension
    simp only [Budget.uniform_d, hbd]
    have h := (hdim (W := W) (X := 1) hR lam mu sigma n (V.sampler.dim n) le_rfl hQ hs' hn
      hVd).le_final
    simp only [one_pow, Nat.mul_one] at h
    exact h.trans (pow_le_pow_of_le (by omega) (by omega))
  · -- the decider's time
    simp only [Budget.uniform_D, Budget.uniform_k, hbd, outDegree]
    have hsdim : (typedSampler V.sampler PD lam mu sigma).dim n ≤
        W + pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k := by
      rw [typedSampler_dim]; omega
    refine (hP (W := W) (K := mu) (typedSampler V.sampler PD lam mu sigma)
      (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) n hn hTS
      (fun hX => hC hR lam mu sigma n hX hQ hl hs' hn)
      (fun {X} hX u v x y a b hx hy ha hb => ?_)).mono
      (pow_le_pow_of_le (by omega) (by omega)) (Nat.mul_le_mul_right _ (by omega))
    have hxl : (readBits (treeHead (treeTail (encode (u, x, v, y, a, b) : Data)))).length ≤
        W + (dB PD lam mu sigma n).length := by
      simp only [encode_prod, treeTail_cons, treeHead_cons, readBits_encode, length_unary, dB]
      omega
    have hyl : (readBits (treeHead (treeTail (treeTail (treeTail
        (encode (u, x, v, y, a, b) : Data)))))).length ≤ W + (dB PD lam mu sigma n).length := by
      simp only [encode_prod, treeTail_cons, treeHead_cons, readBits_encode, length_unary, dB]
      omega
    obtain ⟨r, t, ht, hr⟩ := hD (W := W) (X := X) V lam mu sigma n hR hX hQ hl hs' hn hSz hDz hS
      (encode (u, x, v, y, a, b)) (hd hR lam mu sigma n _ hX hQ hs' hn hsdim u v x y a b hx hy ha hb)
      hxl hyl
    exact ⟨r, t, ht, hr⟩
  · -- the answer cut
    simp only [Budget.uniform_B, hbd]
    refine Verifier.RejectsLong.mono ?_ (CL.Detyping.DeciderProgram.verifier_rejectsLong graph
      (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
      (arCut PD lam mu sigma) _ (total PD V lam mu sigma) n)
    have h := (hcut (W := W) (X := 1) hR lam mu sigma n le_rfl hQ hs' hn).le_final
    simp only [one_pow, Nat.mul_one] at h
    exact h.trans (pow_le_pow_of_le (by omega) (by omega))

end Within

end MIPRE.AnswerReduction

end
