/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.ArParams
public import MIPRE.Tailored.AnsRed.HonestPair
public import MIPRE.Tailored.AnsRed.IndicatorConst
public import MIPRE.Foundations.SAT.GatePaddingExact
public import MIPRE.Foundations.Pipeline.AnswerReduction
public import MIPRE.Foundations.Pipeline.PowDomRun

@[expose] public section

/-!
# The honest PCPs' hypotheses at the parameters of the answer reduction

Slice P4i of `planning/aldous-lyons-track.md`. At the parameters of `ArParams.lean`, the circuit of
a seed is the window describer's description of the output indicator `L*` through its three
windows, padded to the gate count `s` (`arCirc`); `L*` reads the parameters `(ℓ, ◇)` from the
constant function `arPrm`. For an input verifier within the answer reduction's input budget
`inBudget λ μ n`, with `|𝒱| ≤ σ` and `λ, μ ≥ 1`, these circuits satisfy the hypotheses of the
honest PCPs (`HonestHyp`), at the description time `T = 2^K` (`honestHyp_ar`):

* the window and copy widths fit the input's lengths (at most `2^Q`) and the constraints its
  processor outputs on readable answers (fewer than `2^{◇ - Q - 2}`, from its running time);
* each circuit is well formed with the PCP's inputs, and describes `L*` within `T`: the
  describer's validity holds since `Q, 2 log n ≤ T`, `L*`'s program is at most `σ'` long, and the
  questions have at most `Q` bits; the windows fit `T` and the witness width `r ≥ K + 2`;
* `L*` accepts the honest strings within `T`.

Two facts about `L*` at constant parameters are hypotheses here, discharged where they are
proved: its running time on accepted inputs (`hTime`, at a universal constant `E` with
`2E ≤ E₁`) and the size of its program (`hSize`, at the constant `c₀` of `σ'`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Params

open Cost Cost.PolyTimeFun MIPRE.SAT

/-! ## Lengths of outputs -/

theorem length_spineList_le (d : Data) : (Data.spineList d).length ≤ d.size := by
  induction d with
  | nil => simp
  | cons a d _ ih => simp only [Data.spineList, List.length_cons, Data.size_cons]; omega

theorem length_bitsListD_le (d : Data) : (Data.bitsListD d).length ≤ d.size := by
  rw [Data.bitsListD, List.length_map]
  exact length_spineList_le d

/-- The length a calculator outputs is at most its bound. -/
theorem lenOf_le {ℓ : ℕ} {V : TailoredVerifier ℓ} {n B : ℕ} (hB : LenBound V.len n B)
    (x : BitStr) (κ : Bool) : V.lenOf n x κ ≤ B := by
  unfold TailoredVerifier.lenOf
  split_ifs with h
  · exact hB x κ _ h.choose_spec
  · exact Nat.zero_le _

/-- **The constraints a processor outputs are at most its running time.** -/
theorem consOf_length_le {ℓ : ℕ} {V : TailoredVerifier ℓ} {n T k : ℕ}
    (hP : V.lp.TimeBoundAt n T k) (x y aR bR : BitStr) :
    (V.consOf n x y aR bR).length ≤
      max 1 (T * ((encode (x, y, aR, bR) : Data).size + 1) ^ k) := by
  unfold TailoredVerifier.consOf
  split_ifs with h
  · obtain ⟨t, d, hrun, hd⟩ := h.2.2.choose_spec
    obtain ⟨r, t', ht', hr⟩ := hP (encode (x, y, aR, bR))
    obtain ⟨rfl, rfl⟩ := Eval.deterministic hrun hr
    rw [← hd]
    exact (length_bitsListD_le d).trans ((Eval.size_le hrun).trans ht') |>.trans (le_max_right _ _)
  · simp

/-! ## Arithmetic -/

theorem two_mul_le_two_pow {K : ℕ} (h : 1 ≤ K) : 2 * K ≤ 2 ^ K := by
  induction K with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have := ih hk
      rw [pow_succ]
      omega

variable (κ : ArConsts) (lam mu sigma n : ℕ)

theorem pOW_add_le_pK (h : 1 ≤ κ.E₁) : pOW lam mu n + pQ lam mu n + 4 ≤ pK κ lam mu n := by
  unfold pK
  have : 1 ≤ κ.E₁ * (mu + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc pOW lam mu n + pQ lam mu n + 4 = 1 * (pOW lam mu n + pQ lam mu n + 4) := (one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ this

theorem le_pQ (hlam : 1 ≤ lam) (hmu : 1 ≤ mu) : n + 1 ≤ pQ lam mu n := by
  calc n + 1 ≤ lam * n + 1 := by nlinarith
    _ = (lam * n + 1) ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hmu

theorem pQ_lt_two_pow : pQ lam mu n < 2 ^ pQ lam mu n := Nat.lt_two_pow_self

/-- The windows fit the description time: `2^ℓ + 2^oW ≤ 2^K`. -/
theorem two_pow_ell_add_le (h : 1 ≤ κ.E₁) :
    2 ^ (pEll lam mu n + 1) + 2 ^ (pOW lam mu n + 1) ≤ 2 * pT κ lam mu n := by
  have hK := pOW_add_le_pK κ lam mu n h
  have h1 : 2 ^ (pEll lam mu n + 1) ≤ 2 ^ (pOW lam mu n + 1) :=
    Nat.pow_le_pow_right (by omega) (by unfold pOW pEll; omega)
  have h2 : 2 ^ (pOW lam mu n + 2) ≤ 2 ^ (pK κ lam mu n + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  unfold pT
  rw [pow_succ] at h2
  rw [pow_succ 2 (pK κ lam mu n)] at h2
  omega

/-- The witness width: `K + 2 ≤ r`. -/
theorem pK_add_two_le_pR : pK κ lam mu n + 2 ≤ pR κ lam mu sigma n := by
  have h := windowDescriber.four_mul_le (pT κ lam mu n) (pSig κ lam mu sigma n)
  have h' : 2 ^ (pK κ lam mu n + 2) ≤ 2 ^ pR κ lam mu sigma n := by
    rw [pow_add]; unfold pT at h; linarith
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h'

/-! ## The parameter function and the circuits -/

/-- **The parameters of `L*` at the index**: `(ℓ, ◇)`, as a constant function. -/
def arPrm : PolyTimeFun ℕ (Unary × Unary) := const (unary (pEll lam mu n), unary (pDm lam mu n))

@[simp] theorem arPrm_apply (m : ℕ) :
    arPrm lam mu n m = (unary (pEll lam mu n), unary (pDm lam mu n)) := rfl

/-- The input of the window describer at a seed: the three windows `ℓ + 1, ℓ + 1, oW + 1`, the
program of `L*`, the index, `T`, `Q`, `σ'`, and the two questions. -/
def arDescIn (L P : Prog) (x y : BitStr) : Desc6Input :=
  ((unary (pEll lam mu n + 1), unary (pEll lam mu n + 1), unary (pOW lam mu n + 1)),
    (lstarProg (arPrm lam mu n) L P, n, pT κ lam mu n, pQ lam mu n, pSig κ lam mu sigma n), x, y)

/-- **The circuit of a seed**: the description of `L*` through its windows, padded to `s` gates. -/
def arCirc (L P : Prog) (x y : BitStr) : Circuit :=
  (windowDescriber.describe (arDescIn κ lam mu sigma n L P x y)).padTo (pS κ lam mu sigma n)

theorem one_le_pS : 1 ≤ pS κ lam mu sigma n := by
  unfold pS
  show 1 ≤ TM.CookLevin.Desc.roundUp _ _ _ _ _
  exact Nat.one_le_two_pow

theorem arCirc_wf (L P : Prog) (x y : BitStr) : (arCirc κ lam mu sigma n L P x y).WellFormed :=
  Circuit.wellFormed_padTo (windowDescriber.wellFormed _) _

theorem arCirc_inputs (L P : Prog) (x y : BitStr) :
    (arCirc κ lam mu sigma n L P x y).inputs = (pL κ lam mu sigma n).nIn := by
  rw [arCirc, Circuit.padTo_inputs, arDescIn, windowDescriber.inputs_eq]
  simp only [length_unary, PcpDims.nIn, pL_ℓ, pL_r, pL_oW]

theorem arCirc_size (L P : Prog) (x y : BitStr) :
    (arCirc κ lam mu sigma n L P x y).size = (pL κ lam mu sigma n).s :=
  Circuit.padTo_size _ (one_le_pS κ lam mu sigma n)

/-! ## The honest PCPs' hypotheses -/

variable {κ lam mu sigma n}

/-- The circuits at the seeds of an input verifier. -/
def arCc {ℓV : ℕ} (V : TailoredVerifier ℓV) (z : V.Questions n) : Circuit :=
  arCirc κ lam mu sigma n V.len.prog V.lp.prog (CL.toBits ((V.sampler.cl n .alice).eval z))
    (CL.toBits ((V.sampler.cl n .bob).eval z))

/-- `tableSize (2^ℓ) (2^◇) = 2^oW`. -/
theorem tableSize_pow : tableSize (2 ^ pEll lam mu n) (2 ^ pDm lam mu n) = 2 ^ pOW lam mu n := by
  unfold tableSize pOW
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
  simp only [← pow_add]
  congr 1
  ring

/-- An encoded bit string is at most `4 · 2^w` once its length is at most `2^w`. -/
theorem esize_bitStr_le_pow {x : BitStr} {w : ℕ} (h : x.length ≤ 2 ^ w) :
    esize x + 1 ≤ 4 * 2 ^ w + 2 := by
  have := esize_bitStr_le x
  omega

/-- **The constraint bound of the honest PCPs.** -/
theorem cons_le_ar {ℓV : ℕ} {V : TailoredVerifier ℓV}
    (hV : V.Within n (AnswerReduction.inBudget lam mu n)) (x y : V.Questions n) (aR bR : BitStr)
    (haR : aR.length ≤ (V.tgame n).lenR x) (hbR : bR.length ≤ (V.tgame n).lenR y) :
    ((V.tgame n).cons x y aR bR).length * (2 ^ pEll lam mu n + 2 ^ pEll lam mu n) +
      (2 ^ pEll lam mu n + 2 ^ pEll lam mu n) ≤ 2 ^ pDm lam mu n := by
  set Q := pQ lam mu n with hQ
  have hQ1 : 1 ≤ Q := one_le_pQ lam mu n
  have hQlt : Q < 2 ^ Q := Nat.lt_two_pow_self
  have hlx : (V.tgame n).lenR x ≤ 2 ^ Q := lenOf_le hV.2.2.2.2 _ _
  have hly : (V.tgame n).lenR y ≤ 2 ^ Q := lenOf_le hV.2.2.2.2 _ _
  have hdim : V.sampler.dim n ≤ Q := hV.2.1
  have hcs := consOf_length_le hV.2.2.2.1 (CL.toBits x) (CL.toBits y) aR bR
  have hX := esize_bitStr_le (CL.toBits x)
  have hY := esize_bitStr_le (CL.toBits y)
  have hA := esize_bitStr_le aR
  have hB := esize_bitStr_le bR
  rw [CL.length_toBits] at hX hY
  have hsize : (encode (CL.toBits x, CL.toBits y, aR, bR) : Data).size + 1 ≤ 2 ^ (Q + 4) := by
    simp only [encode_prod, Data.size_cons]
    change esize (CL.toBits x) + (esize (CL.toBits y) + (esize aR + esize bR + 1) + 1) + 1 + 1 ≤ _
    rw [pow_add]
    norm_num
    nlinarith
  have hpow : 2 ^ Q * ((encode (CL.toBits x, CL.toBits y, aR, bR) : Data).size + 1) ^ mu ≤
      2 ^ (Q + (Q + 4) * mu) := by
    rw [pow_add, pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize mu)
  have hlen : ((V.tgame n).cons x y aR bR).length ≤ 2 ^ (Q + (Q + 4) * mu) := by
    refine hcs.trans (max_le (Nat.one_le_two_pow) ?_)
    simpa [AnswerReduction.inBudget, AnswerReduction.inAns] using hpow
  have key : (2 ^ (Q + (Q + 4) * mu) + 1) * (2 ^ Q + 2 ^ Q) ≤ 2 ^ pDm lam mu n := by
    have h1 : 2 ^ (Q + (Q + 4) * mu) + 1 ≤ 2 ^ (Q + (Q + 4) * mu + 1) := by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := Q + (Q + 4) * mu); omega
    have h2 : 2 ^ Q + 2 ^ Q = 2 ^ (Q + 1) := by rw [pow_succ]; ring
    calc (2 ^ (Q + (Q + 4) * mu) + 1) * (2 ^ Q + 2 ^ Q)
        ≤ 2 ^ (Q + (Q + 4) * mu + 1) * 2 ^ (Q + 1) := by rw [h2]; exact Nat.mul_le_mul_right _ h1
      _ = 2 ^ (Q + (Q + 4) * mu + 1 + (Q + 1)) := (pow_add _ _ _).symm
      _ ≤ 2 ^ pDm lam mu n := Nat.pow_le_pow_right (by norm_num) (by unfold pDm; rw [← hQ]; nlinarith)
  calc ((V.tgame n).cons x y aR bR).length * (2 ^ pEll lam mu n + 2 ^ pEll lam mu n) +
        (2 ^ pEll lam mu n + 2 ^ pEll lam mu n)
      = (((V.tgame n).cons x y aR bR).length + 1) * (2 ^ Q + 2 ^ Q) := by ring
    _ ≤ (2 ^ (Q + (Q + 4) * mu) + 1) * (2 ^ Q + 2 ^ Q) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := key

/-- `L*`'s running time on accepted inputs at constant parameters, at a constant `E`: the form
in which the honest PCPs' time hypothesis is discharged. -/
def LstarTime (E : ℕ) : Prop :=
  ∀ (p : Unary × Unary) {ℓ : ℕ} (V : TailoredVerifier ℓ) {n T k τ ρ : ℕ} {x y a b : BitStr},
    V.len.TimeBoundAt n T k → V.lp.TimeBoundAt n T k → T ≤ 2 ^ τ →
    esize ((n, x, y, a, b) : DIn) + 1 ≤ 2 ^ ρ → esize p ≤ 2 ^ ρ →
    (lstar (const p) V).Accepts n x y a b →
    (lstar (const p) V).AcceptsWithin n x y a b (2 ^ (E * (k + 1) * (τ + ρ + 1)))

/-- The size of `L*`'s program at constant parameters, at the constant `c₀`. -/
def LstarSize (c₀ : ℕ) : Prop :=
  ∀ (p : Unary × Unary) (L P : Prog),
    esize (lstarProg (const p) L P) ≤ c₀ + 4 * esize L + esize P + 2 * esize p

/-- **`L*`'s running time at constant parameters**, at a universal constant
(`lstar_const_acceptsWithin_pow`). -/
theorem exists_lstarTime : ∃ E : ℕ, 1 ≤ E ∧ LstarTime E := lstar_const_acceptsWithin_pow

/-- **The size of `L*`'s program at constant parameters** (`esize_lstarProg_const`). -/
theorem lstarSize_lstarProgSize₀ : LstarSize lstarProgSize₀ := fun p L P => by
  rw [esize_lstarProg_const]
  omega

theorem acceptsWithin_mono {D : Decider} {m : ℕ} {x y a b : BitStr} {T T' : ℕ}
    (h : D.AcceptsWithin m x y a b T) (hT : T ≤ T') : D.AcceptsWithin m x y a b T' :=
  let ⟨t, ht, hr⟩ := h
  ⟨t, ht.trans hT, hr⟩

theorem esize_arPrm_pair :
    esize ((unary (pEll lam mu n), unary (pDm lam mu n)) : Unary × Unary) =
      (2 * pEll lam mu n + 1) + (2 * pDm lam mu n + 1) + 1 := by
  simp only [esize_prod, esize_unary]

set_option maxRecDepth 10000 in
/-- **The honest PCPs' hypotheses hold at the parameters of the answer reduction**, for an input
within the input budget with `|𝒱| ≤ σ` and `λ, μ ≥ 1`. -/
theorem honestHyp_ar {E : ℕ} (hE₁ : 2 * E ≤ κ.E₁) (hE : 1 ≤ E) (hTime : LstarTime E)
    (hSize : LstarSize κ.c₀) {ℓV : ℕ} (V : TailoredVerifier ℓV) (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hV : V.Within n (AnswerReduction.inBudget lam mu n)) (hsz : V.size ≤ sigma) :
    HonestHyp (pL κ lam mu sigma n) V n (arPrm lam mu n)
      (arCc (κ := κ) (lam := lam) (mu := mu) (sigma := sigma) V)
      (pT κ lam mu n) := by
  have hE₁' : 1 ≤ κ.E₁ := by omega
  set Q := pQ lam mu n with hQ
  have hQ1 : 1 ≤ Q := one_le_pQ lam mu n
  have hnQ : n + 1 ≤ Q := le_pQ lam mu n hlam hmu
  have hKbig := pOW_add_le_pK κ lam mu n hE₁'
  have hrK := pK_add_two_le_pR κ lam mu sigma n
  have hdim : V.sampler.dim n ≤ Q := hV.2.1
  -- the describer's validity at every seed
  have hvalid : ∀ z : V.Questions n, Valid (lstar (arPrm lam mu n) V).prog n (pT κ lam mu n) Q
      (pSig κ lam mu sigma n) (CL.toBits ((V.sampler.cl n .alice).eval z))
      (CL.toBits ((V.sampler.cl n .bob).eval z)) := by
    intro z
    have hT : Q ≤ pT κ lam mu n :=
      ((pQ_le_pK κ lam mu n hE₁').trans Nat.lt_two_pow_self.le)
    refine ⟨hT, ?_, ?_, ?_, ?_⟩
    · have hsn : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
      have := two_mul_le_two_pow (K := pK κ lam mu n) (by omega)
      unfold pT; omega
    · have h := hSize (unary (pEll lam mu n), unary (pDm lam mu n)) V.len.prog V.lp.prog
      have hl : esize V.len.prog ≤ sigma :=
        (le_max_left _ _ |>.trans (le_max_right _ _)).trans hsz
      have hp : esize V.lp.prog ≤ sigma :=
        (le_max_right _ _ |>.trans (le_max_right _ _)).trans hsz
      rw [esize_arPrm_pair] at h
      change esize (lstarProg (arPrm lam mu n) V.len.prog V.lp.prog) ≤ _
      unfold pSig
      unfold arPrm
      omega
    · rw [CL.length_toBits]; exact hdim
    · rw [CL.length_toBits]; exact hdim
  have hwin := two_pow_ell_add_le κ lam mu n hE₁'
  have hQK := pQ_le_pK κ lam mu n hE₁'
  have hr : pK κ lam mu n + 2 ≤ windowDescriber.r₀ (pT κ lam mu n) (pSig κ lam mu sigma n) := hrK
  have hw1 : (unary (pEll lam mu n + 1)).length ≤
      windowDescriber.r₀ (pT κ lam mu n) (pSig κ lam mu sigma n) := by
    rw [length_unary]; change Q + 1 ≤ _; omega
  have hw3 : (unary (pOW lam mu n + 1)).length ≤
      windowDescriber.r₀ (pT κ lam mu n) (pSig κ lam mu sigma n) := by
    rw [length_unary]; omega
  have hwac : 2 ^ (unary (pEll lam mu n + 1)).length + 2 ^ (unary (pOW lam mu n + 1)).length ≤
      2 * pT κ lam mu n := by
    rw [length_unary, length_unary]; exact hwin
  have hwb : 2 ^ (unary (pEll lam mu n + 1)).length ≤ 2 * pT κ lam mu n := by
    have := Nat.one_le_two_pow (n := pOW lam mu n + 1)
    rw [length_unary]; omega
  have hfit : ∀ z : V.Questions n,
      (windowDescriber.describe (arDescIn κ lam mu sigma n V.len.prog V.lp.prog
        (CL.toBits ((V.sampler.cl n .alice).eval z)) (CL.toBits ((V.sampler.cl n .bob).eval z)))).size
        ≤ pS κ lam mu sigma n := fun z =>
    windowDescriber.size_le (unary (pEll lam mu n + 1)) (unary (pEll lam mu n + 1))
      (unary (pOW lam mu n + 1)) (lstar (arPrm lam mu n) V).prog n (pT κ lam mu n) Q
      (pSig κ lam mu sigma n) (CL.toBits ((V.sampler.cl n .alice).eval z))
      (CL.toBits ((V.sampler.cl n .bob).eval z)) (hvalid z) hw1 hw1 hw3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro z; exact arCirc_wf κ lam mu sigma n _ _ _ _
  · intro z; exact arCirc_inputs κ lam mu sigma n _ _ _ _
  · intro z
    have h := windowDescriber.describes (unary (pEll lam mu n + 1)) (unary (pEll lam mu n + 1))
      (unary (pOW lam mu n + 1)) (lstar (arPrm lam mu n) V) n (pT κ lam mu n) Q
      (pSig κ lam mu sigma n) (CL.toBits ((V.sampler.cl n .alice).eval z))
      (CL.toBits ((V.sampler.cl n .bob).eval z)) (hvalid z) hwac hwb hw1 hw1 hw3
    rw [length_unary, length_unary] at h
    exact Circuit.describesWindows_padTo (windowDescriber.wellFormed _) (hfit z) h
  · intro z aR bR hacc
    obtain ⟨lRx, lLx, lRy, lLy, cs, -, -, -, -, -, hok⟩ :=
      (lstar_accepts_iff _ V n _ _ _ _).mp hacc
    simp only [arPrm_apply, length_unary] at hok
    have hb := hok.2.2.2.2.1
    have ha := hok.2.2.2.2.2.1
    rw [tableSize_pow] at ha
    set A := honestA (pL κ lam mu sigma n) V n ((V.sampler.cl n .alice).eval z)
      ((V.sampler.cl n .bob).eval z) aR bR
    set B := honestB (pL κ lam mu sigma n) V n ((V.sampler.cl n .bob).eval z) bR
    have hEll : 2 ^ pEll lam mu n ≤ 2 ^ pOW lam mu n :=
      Nat.pow_le_pow_right (by norm_num) (by unfold pOW pEll; omega)
    have hQpow : Q < 2 ^ Q := Nat.lt_two_pow_self
    have hOW1 : 1 ≤ 2 ^ pOW lam mu n := Nat.one_le_two_pow
    have hesz : esize ((n, CL.toBits ((V.sampler.cl n .alice).eval z),
        CL.toBits ((V.sampler.cl n .bob).eval z), A, B) : DIn) + 1 ≤ 2 ^ (pOW lam mu n + 5) := by
      have h1 := Pipeline.esize_nat_le_four n
      have h2 := esize_bitStr_le (CL.toBits ((V.sampler.cl n .alice).eval z))
      have h3 := esize_bitStr_le (CL.toBits ((V.sampler.cl n .bob).eval z))
      have h4 := esize_bitStr_le A
      have h5 := esize_bitStr_le B
      rw [CL.length_toBits] at h2 h3
      simp only [esize_prod]
      rw [pow_add]
      have hQe : 2 ^ Q ≤ 2 ^ pOW lam mu n := hEll
      norm_num
      omega
    have hp : esize ((unary (pEll lam mu n), unary (pDm lam mu n)) : Unary × Unary) ≤
        2 ^ (pOW lam mu n + 5) := by
      rw [esize_arPrm_pair]
      have : pOW lam mu n < 2 ^ pOW lam mu n := Nat.lt_two_pow_self
      rw [pow_add]
      unfold pOW at this ⊢
      omega
    have hw := hTime (unary (pEll lam mu n), unary (pDm lam mu n)) V hV.2.2.1 hV.2.2.2.1
      (τ := Q) le_rfl hesz hp hacc
    refine acceptsWithin_mono hw (Nat.pow_le_pow_right (by norm_num) ?_)
    unfold pK
    have : E * (mu + 1) * (Q + (pOW lam mu n + 5) + 1) ≤
        2 * E * (mu + 1) * (pOW lam mu n + Q + 4) := by
      have : Q + (pOW lam mu n + 5) + 1 ≤ 2 * (pOW lam mu n + Q + 4) := by omega
      calc E * (mu + 1) * (Q + (pOW lam mu n + 5) + 1)
          ≤ E * (mu + 1) * (2 * (pOW lam mu n + Q + 4)) := Nat.mul_le_mul_left _ this
        _ = 2 * E * (mu + 1) * (pOW lam mu n + Q + 4) := by ring
    exact this.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hE₁))
  · have h1 : 2 ^ pEll lam mu n ≤ 2 ^ pOW lam mu n :=
      Nat.pow_le_pow_right (by norm_num) (by unfold pOW pEll; omega)
    have h2 : 2 ^ (pOW lam mu n + 1) ≤ 2 ^ pK κ lam mu n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at h2
    simp only [pL_ℓ, pL_oW]
    unfold pT
    omega
  · intro x; exact lenOf_le hV.2.2.2.2 _ _
  · intro x; exact lenOf_le hV.2.2.2.2 _ _
  · intro x y aR bR haR hbR; exact cons_le_ar hV x y aR bR haR hbR

end MIPRE.Tailored.AnsRed.Params

end

end
