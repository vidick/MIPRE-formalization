/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArRoutine
public import MIPRE.Background.AnswerReduction.Params
public import MIPRE.Tailored.AnsRed.ArParams

@[expose] public section

/-!
# The parameter program of the answer-reduced verifier

Slice P4i of `planning/aldous-lyons-track.md`: the closed program `arParCore κ` that, on
`((λ, μ, σ), n)`, writes the parameters of `MIPRE.Tailored.AnsRed.Params` in unary
(`arParCore_runs`), the routine's `parCore`. Its running time is `ArParCoreCost`.

The parameters grow like a power of `Q = (λn + 1)^μ`, so no polynomial-time function of the
binary input writes them in unary; as the MIP* answer reduction's parameter routine
(`MIPRE.AnswerReduction.ParRoutine.core`), the program is a sequence of loops, each writing one
number in unary in front of the data, and polynomial-time functions of the unary data between
them. In order:

* the MIP* budgets' routine `budCore`, kept in front of the input: `Q` in binary (with the MIP*
  time bound, unused), `λ` replaced by `0` at the index `0`, so that no loop runs longer than `Q`;
* `Q`, `μ` and `σ` in unary (`pushU`);
* a polynomial-time function of the unary `Q, μ, σ` and the binary `n` (`f6`): `◇`, `oW`, `K`,
  `σ'` in unary, `T = 2^K` in binary from `K` (the bits `0^K 1`), and `(r, s)` from the window
  describer's parameter function at `(n, T, Q, σ')`;
* `r`, `s` in unary;
* `2^j` in unary, `j = size m` and `m = nIn + s` computed from the unary `Q, ◇, r, s`;
* a polynomial-time function assembling `arParams t j 17 L (K, σ')` (`f10`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.Pipeline CL.Detyping.Program
open MIPRE.AnswerReduction.ParRoutine (timesU timesU_apply bitsVal_pow map_const_toFun)

namespace ArPar

/-! ## Pushing a number in unary -/

/-- **A loop stage**: write the number `g x` in unary in front of the data `x`. -/
def pushU (g : PolyTimeFun Data ℕ) : Prog :=
  stageProg (ap₂ treePair (encoded.comp g) (PolyTimeFun.id Data)) toUnaryProg
    AnswerReduction.ParRoutine.postKeep

theorem pushU_closed (g : PolyTimeFun Data ℕ) : (pushU g).WellScoped 1 :=
  stageProg_closed _ toUnaryProg_closed _

theorem pushU_runs (g : PolyTimeFun Data ℕ) (x : Data) :
    ∃ t, (pushU g).Runs x (.cons (encode (unary (g x))) x) t := by
  obtain ⟨t, h⟩ := toUnaryProg_runs (g x)
  obtain ⟨t', h'⟩ := stageProg_runs (ap₂ treePair (encoded.comp g) (PolyTimeFun.id Data))
    toUnaryProg_closed AnswerReduction.ParRoutine.postKeep x (encode (g x)) x _ t (by simp) h
  unfold pushU
  exact ⟨t', by simpa [AnswerReduction.ParRoutine.postKeep] using h'⟩

/-! ## The unary arithmetic -/

/-- `2^{|u|}` in binary: the bits `0^{|u|} 1`. -/
def pow2F : PolyTimeFun Unary ℕ :=
  bitsValue.comp (ap₂ append (map (const false)) (const [true]))

theorem pow2F_apply (k : ℕ) : pow2F (unary k) = 2 ^ k := by
  simp only [pow2F, comp_apply, ap₂_apply, map_apply, const_apply, append_apply,
    PolyTimeFun.bitsValue_apply]
  rw [map_const_toFun, length_unary, bitsVal_pow]

/-- A unary number in binary. -/
def binF : PolyTimeFun Unary ℕ := addUnary.comp ((const 0).pair (PolyTimeFun.id Unary))

theorem binF_apply (k : ℕ) : binF (unary k) = k := by
  simp [binF]

/-- `size m` in unary, from `m` in unary. -/
def jF : PolyTimeFun Unary Unary := (map (const ())).comp (readBits.comp (encoded.comp binF))

theorem jF_apply (k : ℕ) : jF (unary k) = unary (Nat.size k) := by
  change List.map (fun _ => ()) (readBits (encode (binF (unary k)).bits)) = _
  rw [readBits_encode, binF_apply, List.map_const', Nat.size_eq_bits_len]
  rfl

/-- The input of `G6`: `σ, μ, Q` in unary and `n`. -/
abbrev I6 : Type := Unary × Unary × Unary × ℕ

/-- `◇ = (μ + 2)(Q + 4)`. -/
def dmF : PolyTimeFun I6 Unary :=
  LowDegree.DegreeArithmetic.mulUnaryProg.comp
    ((ap₂ append (fst.comp snd) (const (unary 2))).pair
      (ap₂ append (fst.comp (snd.comp snd)) (const (unary 4))))

/-- `oW = 2Q + 3◇ + 6`. -/
def oWF : PolyTimeFun I6 Unary :=
  ap₂ append (ap₂ append (ap₂ append (fst.comp (snd.comp snd)) (fst.comp (snd.comp snd)))
    ((timesU 3).comp dmF)) (const (unary 6))

/-- `K = E₁ (μ + 1)(oW + Q + 4)`. -/
def kF (κ : Params.ArConsts) : PolyTimeFun I6 Unary :=
  LowDegree.DegreeArithmetic.mulUnaryProg.comp
    (((timesU κ.E₁).comp (ap₂ append (fst.comp snd) (const (unary 1)))).pair
      (ap₂ append (ap₂ append oWF (fst.comp (snd.comp snd))) (const (unary 4))))

/-- `σ' = c₀ + 5σ + 4(Q + ◇) + 8`. -/
def sigF (κ : Params.ArConsts) : PolyTimeFun I6 Unary :=
  ap₂ append (ap₂ append (ap₂ append (const (unary κ.c₀)) ((timesU 5).comp fst))
    ((timesU 4).comp (ap₂ append (fst.comp (snd.comp snd)) dmF))) (const (unary 8))

/-- The window describer's `(r, s)` at `(n, T, Q, σ')`, `T = 2^K`. -/
def rsF (κ : Params.ArConsts) : PolyTimeFun I6 (ℕ × ℕ) :=
  windowDescriber.params.comp ((snd.comp (snd.comp snd)).pair ((pow2F.comp (kF κ)).pair
    ((binF.comp (fst.comp (snd.comp snd))).pair (binF.comp (sigF κ)))))

/-- The output of `G6`: `(r, s)` in binary, then `K`, `σ'`, `Q`, `◇` in unary. -/
abbrev Z6 : Type := (ℕ × ℕ) × Unary × Unary × Unary × Unary

/-- **The middle function**: `(σ, μ, Q, n) ↦ ((r, s), K, σ', Q, ◇)`. -/
def G6 (κ : Params.ArConsts) : PolyTimeFun I6 Z6 :=
  (rsF κ).pair ((kF κ).pair ((sigF κ).pair ((fst.comp (snd.comp snd)).pair dmF)))

section Apply

variable (κ : Params.ArConsts) (lam mu sigma n : ℕ)

theorem dmF_apply : dmF (unary sigma, unary mu, unary (Params.pQ lam mu n), n) =
    unary (Params.pDm lam mu n) := by
  apply unary_ext
  simp [dmF]

theorem oWF_apply : oWF (unary sigma, unary mu, unary (Params.pQ lam mu n), n) =
    unary (Params.pOW lam mu n) := by
  apply unary_ext
  simp only [oWF, ap₂_apply, append_apply, comp_apply, fst_apply, snd_apply, const_apply,
    timesU_apply, dmF_apply, List.length_append, length_unary]

theorem kF_apply : kF κ (unary sigma, unary mu, unary (Params.pQ lam mu n), n) =
    unary (Params.pK κ lam mu n) := by
  apply unary_ext
  simp only [kF, comp_apply, pair_apply, ap₂_apply, append_apply, fst_apply, snd_apply,
    const_apply, timesU_apply, oWF_apply, LowDegree.DegreeArithmetic.mulUnaryProg_apply,
    List.length_append, length_unary]

theorem sigF_apply : sigF κ (unary sigma, unary mu, unary (Params.pQ lam mu n), n) =
    unary (Params.pSig κ lam mu sigma n) := by
  apply unary_ext
  simp only [sigF, comp_apply, ap₂_apply, append_apply, fst_apply, snd_apply,
    const_apply, timesU_apply, dmF_apply, List.length_append, length_unary]

theorem rsF_apply : rsF κ (unary sigma, unary mu, unary (Params.pQ lam mu n), n) =
    (Params.pR κ lam mu sigma n, Params.pS κ lam mu sigma n) := by
  simp only [rsF, comp_apply, pair_apply, fst_apply, snd_apply, kF_apply, sigF_apply,
    pow2F_apply, binF_apply, windowDescriber.params_eq]

/-- The value of the middle function. -/
abbrev z6 : Z6 :=
  ((Params.pR κ lam mu sigma n, Params.pS κ lam mu sigma n), unary (Params.pK κ lam mu n),
    unary (Params.pSig κ lam mu sigma n), unary (Params.pQ lam mu n), unary (Params.pDm lam mu n))

theorem G6_apply : G6 κ (unary sigma, unary mu, unary (Params.pQ lam mu n), n) =
    z6 κ lam mu sigma n := by
  simp only [G6, pair_apply, rsF_apply, kF_apply, sigF_apply, dmF_apply, comp_apply, fst_apply,
    snd_apply]

end Apply

/-- `m = nIn + s` in unary, from `(Q, ◇, r, s)` in unary. -/
def mF : PolyTimeFun (Unary × Unary × Unary × Unary) Unary :=
  let uQ := fst
  let udm := fst.comp snd
  let ur := fst.comp (snd.comp snd)
  let us := snd.comp (snd.comp snd)
  let uoW := ap₂ append (ap₂ append (ap₂ append uQ uQ) ((timesU 3).comp udm)) (const (unary 6))
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append uQ (const (unary 1)))
    (ap₂ append uQ (const (unary 1)))) (ap₂ append uoW (const (unary 1)))) ((timesU 3).comp ur))
    (const (unary 6))) us

theorem mF_apply (L : PcpDims) : mF (unary L.ℓ, unary L.dm, unary L.r, unary L.s) = unary L.m := by
  apply unary_ext
  simp only [mF, ap₂_apply, append_apply, comp_apply, fst_apply, snd_apply, const_apply,
    timesU_apply, List.length_append, length_unary, PcpDims.m, PcpDims.nIn, PcpDims.oW]

/-- The input of the last function: `2^j, s, r, K, σ', Q, ◇` in unary. -/
abbrev I10 : Type := Unary × Unary × Unary × Unary × Unary × Unary × Unary

/-- **The last function**: the parameters, from `(2^j, s, r, K, σ', Q, ◇)` in unary. -/
def G10 (κ : Params.ArConsts) : PolyTimeFun I10 ArParams :=
  let u2j := fst
  let us := fst.comp snd
  let ur := fst.comp (snd.comp snd)
  let uK := fst.comp (snd.comp (snd.comp snd))
  let uS := fst.comp (snd.comp (snd.comp (snd.comp snd)))
  let uQ := fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
  let udm := snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
  let uj := jF.comp (mF.comp (uQ.pair (udm.pair (ur.pair us))))
  let ut := (timesU κ.E₂).comp (ap₂ append (ap₂ append (ap₂ append uj ur) uQ) (const (unary 1)))
  ut.pair (uj.pair (u2j.pair ((const (unary Params.pD)).pair (uQ.pair (udm.pair (ur.pair
    (us.pair (encoded.comp (uK.pair uS)))))))))

/-- `mF` at the PCP's dimensions, with `ℓ = Q`. -/
theorem mF_pL (κ : Params.ArConsts) (lam mu sigma n : ℕ) :
    mF (unary (Params.pQ lam mu n), unary (Params.pDm lam mu n), unary (Params.pR κ lam mu sigma n),
      unary (Params.pS κ lam mu sigma n)) = unary (Params.pL κ lam mu sigma n).m := by
  have h := mF_apply (Params.pL κ lam mu sigma n)
  rw [Params.pL_ℓ, Params.pL_dm, Params.pL_r, Params.pL_s] at h
  exact h

theorem G10_apply (κ : Params.ArConsts) (lam mu sigma n : ℕ) :
    G10 κ (unary (2 ^ Params.pJ κ lam mu sigma n), unary (Params.pS κ lam mu sigma n),
      unary (Params.pR κ lam mu sigma n), unary (Params.pK κ lam mu n),
      unary (Params.pSig κ lam mu sigma n), unary (Params.pQ lam mu n),
      unary (Params.pDm lam mu n)) =
    arParams (Params.pTw κ lam mu sigma n) (Params.pJ κ lam mu sigma n) Params.pD
      (Params.pL κ lam mu sigma n) (Params.pExtra κ lam mu sigma n) := by
  simp only [G10, pair_apply, comp_apply, fst_apply, snd_apply, const_apply, encoded_apply,
    mF_pL, jF_apply, arParams, Params.pExtra, Params.pL_ℓ, Params.pL_dm, Params.pL_r,
    Params.pL_s, Prod.mk.injEq, and_true]
  apply unary_ext
  simp only [timesU_apply, ap₂_apply, append_apply, const_apply, List.length_append,
    length_unary, Params.pTw, Params.pJ, comp_apply, fst_apply, snd_apply, pair_apply, mF_pL,
    jF_apply]

/-! ## The data between the stages -/

/-- `Q` in binary, after the budgets' routine. -/
def gQ : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp treeHead)
/-- `μ`, after `Q` in unary. -/
def gMu : PolyTimeFun Data ℕ :=
  readNat.comp (treeHead.comp (treeTail.comp (treeHead.comp (treeTail.comp treeTail))))
/-- `σ`, after `μ` in unary. -/
def gSig : PolyTimeFun Data ℕ :=
  readNat.comp (treeTail.comp (treeTail.comp (treeHead.comp (treeTail.comp (treeTail.comp
    treeTail)))))

/-- The middle stage: `(σ, μ, Q, n)` read, then `G6`. -/
def f6 (κ : Params.ArConsts) : PolyTimeFun Data Data :=
  encoded.comp ((G6 κ).comp ((readUnary.comp (fieldAt 0)).pair ((readUnary.comp (fieldAt 1)).pair
    ((readUnary.comp (fieldAt 2)).pair (readNat.comp (tailAt 5))))))

/-- `r`, after the middle stage. -/
def gR : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp treeHead)
/-- `s`, after `r` in unary. -/
def gS : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp (treeHead.comp treeTail))
/-- `2^j`, after `s` in unary. -/
def g2J : PolyTimeFun Data ℕ :=
  (pow2F.comp (jF.comp mF)).comp ((readUnary.comp (fieldAt 5)).pair ((readUnary.comp
    (tailAt 6)).pair ((readUnary.comp (fieldAt 1)).pair (readUnary.comp (fieldAt 0)))))

/-- The last stage: `(2^j, s, r, K, σ', Q, ◇)` read, then `G10`. -/
def f10 (κ : Params.ArConsts) : PolyTimeFun Data Data :=
  encoded.comp ((G10 κ).comp ((readUnary.comp (fieldAt 0)).pair ((readUnary.comp
    (fieldAt 1)).pair ((readUnary.comp (fieldAt 2)).pair ((readUnary.comp (fieldAt 4)).pair
      ((readUnary.comp (fieldAt 5)).pair ((readUnary.comp (fieldAt 6)).pair
        (readUnary.comp (tailAt 7)))))))))

section Data

variable (κ : Params.ArConsts) (lam mu sigma n : ℕ)

/-- The input. -/
abbrev x0 : Data := encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ)
/-- After the budgets' routine. -/
abbrev x1 : Data :=
  .cons (encode (AnswerReduction.arQ lam mu n, AnswerReduction.tPcp lam mu n)) (x0 lam mu sigma n)
/-- After `Q` in unary. -/
abbrev x2 : Data := .cons (encode (unary (Params.pQ lam mu n))) (x1 lam mu sigma n)
/-- After `μ` in unary. -/
abbrev x3 : Data := .cons (encode (unary mu)) (x2 lam mu sigma n)
/-- After `σ` in unary. -/
abbrev x4 : Data := .cons (encode (unary sigma)) (x3 lam mu sigma n)
/-- After the middle stage. -/
abbrev y6 : Data := encode (z6 κ lam mu sigma n)
/-- After `r` in unary. -/
abbrev y7 : Data := .cons (encode (unary (Params.pR κ lam mu sigma n))) (y6 κ lam mu sigma n)
/-- After `s` in unary. -/
abbrev y8 : Data := .cons (encode (unary (Params.pS κ lam mu sigma n))) (y7 κ lam mu sigma n)
/-- After `2^j` in unary. -/
abbrev y9 : Data :=
  .cons (encode (unary (2 ^ Params.pJ κ lam mu sigma n))) (y8 κ lam mu sigma n)

theorem gQ_apply : gQ (x1 lam mu sigma n) = Params.pQ lam mu n := by
  simp [gQ, encode_prod, readNat_encode]

theorem gMu_apply : gMu (x2 lam mu sigma n) = mu := by
  simp [gMu, encode_prod, readNat_encode]

theorem gSig_apply : gSig (x3 lam mu sigma n) = sigma := by
  simp [gSig, encode_prod, readNat_encode]

theorem f6_apply : f6 κ (x4 lam mu sigma n) = y6 κ lam mu sigma n := by
  simp only [f6, comp_apply, pair_apply, fieldAt, tailAt, treeHead_cons, treeTail_cons,
    PolyTimeFun.id_apply, encode_prod, readUnary_encode, readNat_encode, encoded_apply, G6_apply]

theorem gR_apply : gR (y6 κ lam mu sigma n) = Params.pR κ lam mu sigma n := by
  simp [gR, encode_prod, readNat_encode]

theorem gS_apply : gS (y7 κ lam mu sigma n) = Params.pS κ lam mu sigma n := by
  simp [gS, encode_prod, readNat_encode]

theorem g2J_apply : g2J (y8 κ lam mu sigma n) = 2 ^ Params.pJ κ lam mu sigma n := by
  simp only [g2J, comp_apply, pair_apply, fieldAt, tailAt, treeHead_cons, treeTail_cons,
    PolyTimeFun.id_apply, encode_prod, readUnary_encode, mF_pL, jF_apply, pow2F_apply]

theorem f10_apply : f10 κ (y9 κ lam mu sigma n) =
    encode (arParams (Params.pTw κ lam mu sigma n) (Params.pJ κ lam mu sigma n) Params.pD
      (Params.pL κ lam mu sigma n) (Params.pExtra κ lam mu sigma n)) := by
  simp only [f10, comp_apply, pair_apply, fieldAt, tailAt, treeHead_cons, treeTail_cons,
    PolyTimeFun.id_apply, encode_prod, readUnary_encode, encoded_apply]
  rw [G10_apply]

end Data

/-- The budgets' stage: the MIP* budgets' routine, its output kept in front of the input. -/
def budStage : Prog :=
  stageProg (ap₂ treePair (PolyTimeFun.id Data) (PolyTimeFun.id Data))
    AnswerReduction.ParRoutine.budCore AnswerReduction.ParRoutine.postKeep

theorem budStage_closed : budStage.WellScoped 1 :=
  stageProg_closed _ AnswerReduction.ParRoutine.budCore_closed _

/-- The stages after the budgets'. -/
def tailProg (κ : Params.ArConsts) : Prog :=
  seqProg (pushU gQ) <| seqProg (pushU gMu) <| seqProg (pushU gSig) <|
  seqProg (f6 κ).code <| seqProg (pushU gR) <| seqProg (pushU gS) <|
  seqProg (pushU g2J) (f10 κ).code

theorem tailProg_closed (κ : Params.ArConsts) : (tailProg κ).WellScoped 1 :=
  seqProg_closed (pushU_closed _) <| seqProg_closed (pushU_closed _) <|
  seqProg_closed (pushU_closed _) <| seqProg_closed (PolyTimeFun.closed _) <|
  seqProg_closed (pushU_closed _) <| seqProg_closed (pushU_closed _) <|
  seqProg_closed (pushU_closed _) (PolyTimeFun.closed _)

end ArPar

open ArPar

/-- **The parameter program of the answer-reduced verifier**, on `((λ, μ, σ), n)`. -/
def arParCore (κ : Params.ArConsts) : Prog := seqProg budStage (tailProg κ)

theorem arParCore_closed (κ : Params.ArConsts) : (arParCore κ).WellScoped 1 :=
  seqProg_closed budStage_closed (tailProg_closed κ)

open AnswerReduction.ParRoutine in
/-- **The parameter program computes the parameters.** -/
theorem arParCore_runs (κ : Params.ArConsts) (lam mu sigma n : ℕ) :
    ∃ τ, (arParCore κ).Runs (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ))
      (encode (arParams (Params.pTw κ lam mu sigma n) (Params.pJ κ lam mu sigma n) Params.pD
        (Params.pL κ lam mu sigma n) (Params.pExtra κ lam mu sigma n))) τ := by
  obtain ⟨tb, hb⟩ := AnswerReduction.budCore_runs lam mu sigma n
  obtain ⟨s1, S1⟩ := stageProg_runs (ap₂ treePair (PolyTimeFun.id Data) (PolyTimeFun.id Data))
    budCore_closed postKeep (x0 lam mu sigma n) (x0 lam mu sigma n) (x0 lam mu sigma n) _ tb
    (by simp) hb
  simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S1
  have S2 := pushU_runs gQ (x1 lam mu sigma n)
  rw [gQ_apply] at S2
  have S3 := pushU_runs gMu (x2 lam mu sigma n)
  rw [gMu_apply] at S3
  have S4 := pushU_runs gSig (x3 lam mu sigma n)
  rw [gSig_apply] at S4
  obtain ⟨t5, -, S5⟩ := (f6 κ).computes (x4 lam mu sigma n)
  rw [encode_data, f6_apply] at S5
  have S6 := pushU_runs gR (y6 κ lam mu sigma n)
  rw [gR_apply] at S6
  have S7 := pushU_runs gS (y7 κ lam mu sigma n)
  rw [gS_apply] at S7
  have S8 := pushU_runs g2J (y8 κ lam mu sigma n)
  rw [g2J_apply] at S8
  obtain ⟨t9, -, S9⟩ := (f10 κ).computes (y9 κ lam mu sigma n)
  rw [encode_data, f10_apply] at S9
  have c := fun g => pushU_closed g
  exact seq_runs (tailProg_closed κ) ⟨_, S1⟩ <|
    seq_runs (seqProg_closed (c _) <| seqProg_closed (c _) <|
      seqProg_closed (PolyTimeFun.closed _) <| seqProg_closed (c _) <| seqProg_closed (c _) <|
      seqProg_closed (c _) (PolyTimeFun.closed _)) S2 <|
    seq_runs (seqProg_closed (c _) <| seqProg_closed (PolyTimeFun.closed _) <|
      seqProg_closed (c _) <| seqProg_closed (c _) <| seqProg_closed (c _) (PolyTimeFun.closed _))
      S3 <|
    seq_runs (seqProg_closed (PolyTimeFun.closed _) <|
      seqProg_closed (c _) <| seqProg_closed (c _) <| seqProg_closed (c _) (PolyTimeFun.closed _))
      S4 <|
    seq_runs (seqProg_closed (c _) <| seqProg_closed (c _) <| seqProg_closed (c _)
      (PolyTimeFun.closed _)) ⟨_, S5⟩ <|
    seq_runs (seqProg_closed (c _) <| seqProg_closed (c _) (PolyTimeFun.closed _)) S6 <|
    seq_runs (seqProg_closed (c _) (PolyTimeFun.closed _)) S7 <|
    seq_runs (PolyTimeFun.closed _) S8 ⟨_, S9⟩

end MIPRE.Tailored.AnsRed.Typed

end

end
