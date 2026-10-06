/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.LpIntroData

@[expose] public section

/-!
# The auxiliary constraints of the introspection processor

Issue #281. At a pair of auxiliary labels `t, u` (fixed: the processor branches on the edge
over the finite label alphabet) and two readable answers `aR, bR`, the constraints
`AuxCons.auxPair` of `Typed.consRaw` as a `Cost.PolyTimeFun` on the environment and the two
answers (`DIn`): the readable conditions at both registers (`GP`), the consistency list
(`sameP`), and the directed lists of both orientations (`dirP`), assembled by `auxPairF`.

The data of each clause are read off the kernel's context (`CLData`) and the clocked runs of the
input's programs (`InputRuns`); the stage data are correct under the prefix guards, which the
readable conditions contain, so `dirP_spec` assumes them and `auxPairP_spec` does not.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.LpIntro

open Cost Cost.Data Cost.PolyTimeFun CL MIPRE.Introspection InputRuns

/-! ## Two answers in the environment -/

/-- The environment and two readable answers. -/
abbrev DIn := Env × BitStr × BitStr

def dE : PolyTimeFun DIn Env := fst
def dA : PolyTimeFun DIn BitStr := fst.comp snd
def dB : PolyTimeFun DIn BitStr := snd.comp snd

@[simp] theorem dE_apply (d : DIn) : dE d = d.1 := rfl
@[simp] theorem dA_apply (d : DIn) : dA d = d.2.1 := rfl
@[simp] theorem dB_apply (d : DIn) : dB d = d.2.2 := rfl

/-- The answers swapped. -/
def swapD : PolyTimeFun DIn DIn := dE.pair (dB.pair dA)

@[simp] theorem swapD_apply (e : Env) (a b : BitStr) : swapD (e, a, b) = (e, b, a) := rfl

/-- The window `win a o m`, `o` and `m` in unary. -/
def winF (a : PolyTimeFun DIn BitStr) (o m : PolyTimeFun DIn Unary) : PolyTimeFun DIn BitStr :=
  takeOf (dropOf a o) m

@[simp] theorem winF_apply (a : PolyTimeFun DIn BitStr) (o m : PolyTimeFun DIn Unary) (d : DIn) :
    winF a o m d = win (a d) (o d).length (m d).length := rfl

/-- The register `win a 0 Q` of an answer. -/
def regOf (a : PolyTimeFun DIn BitStr) : PolyTimeFun DIn BitStr := takeOf a (eQ.comp dE)

@[simp] theorem regOf_apply (a : PolyTimeFun DIn BitStr) (d : DIn) :
    regOf a d = win (a d) 0 d.1.2.2.2.2.1.length := by
  simp [regOf, win]

/-- The two registers. -/
abbrev ya : PolyTimeFun DIn BitStr := regOf dA
abbrev yb : PolyTimeFun DIn BitStr := regOf dB

/-- A register-level program at a computed register. -/
def atReg {X : Type} [SizedEncoding X] (F : PolyTimeFun RIn X) (y : PolyTimeFun DIn BitStr) :
    PolyTimeFun DIn X :=
  F.comp (dE.pair y)

@[simp] theorem atReg_apply {X : Type} [SizedEncoding X] (F : PolyTimeFun RIn X)
    (y : PolyTimeFun DIn BitStr) (d : DIn) : atReg F y d = F (d.1, y d) := rfl

/-- A kernel datum of role `w` at a computed register. -/
def kAt {X : Type} [SizedEncoding X] (F : PolyTimeFun CLData.Input X) (w : Bool)
    (y : PolyTimeFun DIn BitStr) : PolyTimeFun DIn X :=
  F.comp (((ctxP w).comp dE).pair y)

@[simp] theorem kAt_apply {X : Type} [SizedEncoding X] (F : PolyTimeFun CLData.Input X) (w : Bool)
    (y : PolyTimeFun DIn BitStr) (d : DIn) : kAt F w y d = F (ctxP w d.1, y d) := rfl

/-- `(Q, R)`. -/
def qr : PolyTimeFun DIn (Unary × Unary) := (eQ.comp dE).pair (eR.comp dE)

@[simp] theorem qr_apply (d : DIn) : qr d = (d.1.2.2.2.2.1, d.1.2.2.2.2.2) := rfl

/-- Equality of two computed bit strings. -/
def eqB (a b : PolyTimeFun DIn BitStr) : PolyTimeFun DIn Bool := ap₂ SAT.ArrayProg.eqBits a b

@[simp] theorem eqB_apply (a b : PolyTimeFun DIn BitStr) (d : DIn) :
    eqB a b d = decide (a d = b d) := rfl

/-! ## The clauses -/

variable (U : ClockedUniversalMachine)

/-- The input-answer equality between label `t` at `aR` and label `u` at `bR`: equal splits and
equal readable input answers. -/
def srcEqB (t u : AuxType 7 × Bool) : PolyTimeFun DIn Bool :=
  andOf (eqUOf (atReg (splitU U false t) ya) (atReg (splitU U false u) yb))
    (andOf (eqUOf (atReg (splitU U true t) ya) (atReg (splitU U true u) yb))
      (eqB (winF dA (eQ.comp dE) (atReg (splitU U false t) ya))
        (winF dB (eQ.comp dE) (atReg (splitU U false u) yb))))

/-- Consistency at the label `t`: `sameCons`. -/
def sameP (t : AuxType 7 × Bool) : PolyTimeFun DIn (List BitStr) :=
  sameConsF.comp (qr.pair ((const (isHideT t.1, isReadT t.1)).pair
    (((eqB ya yb).pair (srcEqB U t t)).pair (atReg (splitU U true t) ya))))

/-- The sampling comparison: `sampleCons`. -/
def sampleP (w : Bool) : PolyTimeFun DIn (List BitStr) :=
  sampleConsF.comp (qr.pair (((eqB ya (kAt (CLData.eval U) w yb)).pair
    (srcEqB U (.introspect, w) (.sample, w))).pair (atReg (splitU U true (.introspect, w)) ya)))

/-- The reading comparison: `readCons`. -/
def readP (w : Bool) : PolyTimeFun DIn (List BitStr) :=
  readConsF.comp (qr.pair (((eqB ya yb).pair
    (srcEqB U (.introspect, w) (.read, w))).pair (atReg (splitU U true (.introspect, w)) ya)))

/-- The last Hide against Read: `hideReadCons`. -/
def hideReadP (w : Bool) : PolyTimeFun DIn (List BitStr) :=
  hideReadConsF.comp (qr.pair (eqB (kAt (CLData.outputPrefix U 6) w ya)
    (kAt (CLData.outputPrefix U 6) w yb)))

/-- Consecutive Hide levels `k`, `k + 1`: `hideNextCons`. -/
def hideNextP (w : Bool) (k : ℕ) : PolyTimeFun DIn (List BitStr) :=
  hideNextConsF.comp ((eQ.comp dE).pair ((eqB (kAt (CLData.outputPrefix U k) w ya)
    (kAt (CLData.outputPrefix U k) w yb)).pair (((kAt (CLData.register U (k + 1)) w yb).pair
      ((kAt (CLData.register U (k + 2)) w yb).pair (kAt (CLData.factor U (k + 1)) w yb))).pair
        (kAt (CLData.kernelGenerators U (k + 1)) w yb))))

/-- The source game's constraints: the input's processor at the two Introspect registers. -/
def sourceP : PolyTimeFun DIn (List BitStr) :=
  let sRa := atReg (splitU U false (.introspect, false)) ya
  let sLa := atReg (splitU U true (.introspect, false)) ya
  let sRb := atReg (splitU U false (.introspect, true)) yb
  let sLb := atReg (splitU U true (.introspect, true)) yb
  let run := (lpRun U).comp ((eClock.comp dE).pair ((eM.comp dE).pair ((eIdx.comp dE).pair
    ((atReg (srcQP U (.introspect, false)) ya).pair ((atReg (srcQP U (.introspect, true)) yb).pair
      ((winF dA (eQ.comp dE) sRa).pair (winF dB (eQ.comp dE) sRb)))))))
  sourceConsF.comp (qr.pair (((sRa.pair sLa).pair (sRb.pair sLb)).pair run))

/-- One orientation of the directed auxiliary checks: `dirAux`. -/
def dirP : AuxType 7 × Bool → AuxType 7 × Bool → PolyTimeFun DIn (List BitStr)
  | (.introspect, w), (.sample, v) => if w = v then sampleP U w else const []
  | (.introspect, w), (.read, v) => if w = v then readP U w else const []
  | (.hide k, w), (.read, v) => if w = v ∧ k.val + 1 = 7 then hideReadP U w else const []
  | (.hide k, w), (.hide j, v) =>
      if w = v ∧ k.val + 1 = j.val then hideNextP U w k.val else const []
  | (.introspect, false), (.introspect, true) => sourceP U
  | _, _ => const []

/-- The length of a label's answers: `auxLen`. -/
def auxLenU (t : AuxType 7 × Bool) : PolyTimeFun DIn Unary :=
  auxLenF.comp (qr.pair (const (isHideT t.1, isReadT t.1)))

/-- **The constraints at a pair of auxiliary labels**: `auxPair`. -/
def auxPairP (t u : AuxType 7 × Bool) : PolyTimeFun DIn (List BitStr) :=
  auxPairF.comp (((andOf (atReg (GP U t) ya) (atReg (GP U u) yb)).pair
      (const (decide (t = u)))).pair
    (((auxLenU t).pair (auxLenU u)).pair ((sameP U t).pair ((dirP U t u).pair
      ((dirP U u t).comp swapD)))))

/-! ## Correctness -/

section Correct

variable {c lam n : ℕ} (T : TailoredVerifier 7) (V : Verifier 7) (hT : T.IsBounded lam)
  (hV : V.IsBounded lam) (hn : 1 ≤ n) (hsamp : V.sampler.prog = T.sampler.prog)
  (hs : V.sampler.dim (2 ^ n) ≤ QQ c lam n)

theorem envT_Q (c lam n : ℕ) (T : TailoredVerifier 7) :
    (envT c lam n T).2.2.2.2.1 = unary (QQ c lam n) := rfl

theorem envT_R (c lam n : ℕ) (T : TailoredVerifier 7) :
    (envT c lam n T).2.2.2.2.2 = unary ((2 ^ n) ^ lam) := by
  simp [envT, envOf, SourceCompiler.originalBound_eq]

theorem length_win_Q {a : BitStr} {Q : ℕ} (h : Q ≤ a.length) : (win a 0 Q).length = Q :=
  length_win (by omega)

include hT hV hn hsamp in
theorem srcEqB_envT (t u : AuxType 7 × Bool) (aR bR : BitStr) (ha : QQ c lam n ≤ aR.length)
    (hb : QQ c lam n ≤ bR.length) :
    srcEqB U t u (envT c lam n T, aR, bR) =
      decide (srcSplitR T V hs t (win aR 0 (QQ c lam n)) =
          srcSplitR T V hs u (win bR 0 (QQ c lam n)) ∧
        srcSplitL T V hs t (win aR 0 (QQ c lam n)) = srcSplitL T V hs u (win bR 0 (QQ c lam n)) ∧
        win aR (QQ c lam n) (srcSplitR T V hs t (win aR 0 (QQ c lam n))) =
          win bR (QQ c lam n) (srcSplitR T V hs u (win bR 0 (QQ c lam n)))) := by
  simp only [srcEqB, andOf_apply, eqUOf_apply, eqB_apply, winF_apply, atReg_apply, regOf_apply,
    dA_apply, dB_apply, comp_apply, dE_apply, eQ_apply, envT_Q, length_unary,
    splitU_envT U T V hT hV hn hsamp hs _ _ _ (length_win_Q ha),
    splitU_envT U T V hT hV hn hsamp hs _ _ _ (length_win_Q hb), Bool.decide_and]
  rfl

include hT hV hn hsamp in
/-- **Consistency at a label.** -/
theorem sameP_spec (t : AuxType 7 × Bool) (aR bR : BitStr) (ha : QQ c lam n ≤ aR.length)
    (hb : QQ c lam n ≤ bR.length) :
    sameP U t (envT c lam n T, aR, bR) =
      sameCons (QQ c lam n) ((2 ^ n) ^ lam) (srcSplitR T V hs) (srcSplitL T V hs) t aR bR := by
  rw [← sameConsF_spec]
  simp only [sameP, comp_apply, pair_apply, qr_apply, const_apply, eqB_apply, regOf_apply,
    dA_apply, dB_apply, atReg_apply, envT_Q, envT_R, length_unary,
    srcEqB_envT U T V hT hV hn hsamp hs t t aR bR ha hb,
    splitU_envT U T V hT hV hn hsamp hs _ _ _ (length_win_Q ha)]
  rfl

theorem toBits_inj {s : ℕ} {a b : Fin s → 𝔽₂} : CL.toBits a = CL.toBits b ↔ a = b :=
  ⟨fun h => by simpa using congrArg (CL.ofBits s) h, fun h => h ▸ rfl⟩

theorem decide_eq_toBits {Q : ℕ} {y : BitStr} (hy : y.length = Q) (X : Fin Q → 𝔽₂) :
    decide (y = CL.toBits X) = decide (CL.ofBits Q y = X) := by
  conv_lhs => rw [← toBits_ofBits hy]
  exact decide_eq_decide.2 toBits_inj

/-- The kernel generators of `regKerGens`, as bit strings, are the solver's output. -/
theorem regKerGens_toBits (Q : ℕ) (S : Finset (Fin Q)) (M : CL.RegLinear 𝔽₂ S) :
    (regKerGens Q S M).map CL.toBits = LowDegree.BinaryLinear.kernelGeneratorsProg
      (unary Q, LowDegree.BinaryLinear.matrixBits (LinearMap.toMatrix' M.toLinearMap)) := by
  rw [regKerGens, List.map_map]
  conv_rhs => rw [← List.map_id (LowDegree.BinaryLinear.kernelGeneratorsProg _)]
  apply List.map_congr_left
  intro v hv
  exact toBits_ofBits ((kernelGens_correct (LinearMap.toMatrix' M.toLinearMap)).1 v hv).1

/-- A `λ`-bounded tailored verifier's lengths are at most `m^λ`. -/
theorem lenOf_le {T : TailoredVerifier 7} {lam m : ℕ} (hT : T.IsBounded lam)
    (hm : 2 ≤ m) (x : BitStr) (κ : Bool) : T.lenOf m x κ ≤ m ^ lam := by
  unfold TailoredVerifier.lenOf
  split_ifs with h
  · exact (hT.1 m hm).2.2.2.2 x κ _ h.choose_spec
  · exact Nat.zero_le _

/-- The padded CL functions of the input. -/
abbrev LL (V : Verifier 7) {n Q : ℕ} (hs : V.sampler.dim (2 ^ n) ≤ Q) :
    Bool → CL.CLFun 𝔽₂ (Fin Q) 7 :=
  AuxiliaryDecision.padded V hs

include hT hsamp in
theorem kAt_envT {X : Type} [SizedEncoding X] (F : PolyTimeFun CLData.Input X) (w : Bool)
    (y : PolyTimeFun DIn BitStr) (aR bR : BitStr) :
    kAt F w y (envT c lam n T, aR, bR) =
      F (CLData.context V lam n (QQ c lam n) w, y (envT c lam n T, aR, bR)) := by
  rw [kAt_apply, ctxP_envT T V hT hsamp]

include hT hV hn hsamp in
/-- **The sampling comparison.** -/
theorem sampleP_spec (w : Bool) (aR bR : BitStr) (ha : QQ c lam n ≤ aR.length)
    (hb : QQ c lam n ≤ bR.length) :
    sampleP U w (envT c lam n T, aR, bR) =
      sampleCons (QQ c lam n) ((2 ^ n) ^ lam) (srcSplitR T V hs) (srcSplitL T V hs) (LL V hs) w
        aR bR := by
  rw [← sampleConsF_spec]
  have hyb := length_win_Q hb
  have he : CLData.eval U (CLData.context V lam n (QQ c lam n) w, win bR 0 (QQ c lam n)) =
      CL.toBits ((LL V hs w).eval (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n)))) := by
    conv_lhs => rw [← toBits_ofBits hyb]
    exact CLData.eval_correct U V hV hn hs w _
  simp only [sampleP, comp_apply, pair_apply, qr_apply, eqB_apply, regOf_apply,
    dA_apply, dB_apply, atReg_apply, envT_Q, envT_R, length_unary,
    kAt_apply, ctxP_envT T V hT hsamp, he, decide_eq_toBits (length_win_Q ha), srcSplitL,
    srcEqB_envT U T V hT hV hn hsamp hs _ _ aR bR ha hb,
    splitU_envT U T V hT hV hn hsamp hs _ _ _ (length_win_Q ha)]

include hT hV hn hsamp in
/-- **The reading comparison.** -/
theorem readP_spec (w : Bool) (aR bR : BitStr) (ha : QQ c lam n ≤ aR.length)
    (hb : QQ c lam n ≤ bR.length) :
    readP U w (envT c lam n T, aR, bR) =
      readCons (QQ c lam n) ((2 ^ n) ^ lam) (srcSplitR T V hs) (srcSplitL T V hs) w aR bR := by
  rw [← readConsF_spec]
  simp only [readP, comp_apply, pair_apply, qr_apply, eqB_apply, regOf_apply, srcSplitL,
    dA_apply, dB_apply, atReg_apply, envT_Q, envT_R, length_unary,
    srcEqB_envT U T V hT hV hn hsamp hs _ _ aR bR ha hb,
    splitU_envT U T V hT hV hn hsamp hs _ _ _ (length_win_Q ha)]

include hV hn in
theorem outputPrefix_at (w : Bool) {k : ℕ} (hk : k ≤ 7) (y : BitStr)
    (hy : y.length = QQ c lam n)
    (hg : CLData.Guard V hs w (k - 1) (CL.ofBits (QQ c lam n) y)) :
    CLData.outputPrefix U k (CLData.context V lam n (QQ c lam n) w, y) =
      CL.toBits ((LL V hs w).outputPrefix k (CL.ofBits (QQ c lam n) y)) := by
  conv_lhs => rw [← toBits_ofBits hy]
  exact CLData.outputPrefix_correct U V hV hn hs w hk _ hg

include hT hV hn hsamp in
/-- **The last Hide against Read**, under the prefix guards at level `6`. -/
theorem hideReadP_spec (w : Bool) (aR bR : BitStr) (ha : QQ c lam n ≤ aR.length)
    (hb : QQ c lam n ≤ bR.length)
    (hga : CLData.Guard V hs w 6 (CL.ofBits (QQ c lam n) (win aR 0 (QQ c lam n))))
    (hgb : CLData.Guard V hs w 6 (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n)))) :
    hideReadP U w (envT c lam n T, aR, bR) =
      hideReadCons (QQ c lam n) ((2 ^ n) ^ lam) (LL V hs) w aR bR := by
  rw [← hideReadConsF_spec]
  simp only [hideReadP, comp_apply, pair_apply, qr_apply, eqB_apply, regOf_apply,
    dA_apply, dB_apply, envT_Q, envT_R, length_unary, kAt_apply, ctxP_envT T V hT hsamp,
    outputPrefix_at U V hV hn hs w (k := 6) (by omega) _ (length_win_Q ha)
      (CLData.guard_mono V hs w (by omega) _ hga),
    outputPrefix_at U V hV hn hs w (k := 6) (by omega) _ (length_win_Q hb)
      (CLData.guard_mono V hs w (by omega) _ hgb), toBits_inj]

include hT hV hn hsamp in
/-- **Consecutive Hide levels**, under the prefix guards at `k` and `k + 1`. -/
theorem hideNextP_spec (w : Bool) (k : ℕ) (hk : k + 1 < 7) (aR bR : BitStr)
    (ha : QQ c lam n ≤ aR.length) (hb : QQ c lam n ≤ bR.length)
    (hga : CLData.Guard V hs w k (CL.ofBits (QQ c lam n) (win aR 0 (QQ c lam n))))
    (hgb : CLData.Guard V hs w (k + 1) (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n)))) :
    hideNextP U w k (envT c lam n T, aR, bR) =
      hideNextCons (QQ c lam n) (LL V hs) (regKerGens (QQ c lam n)) w k aR bR := by
  rw [← hideNextConsF_spec]
  have hyb := length_win_Q hb
  have hreg : ∀ i, i ≤ 7 → CLData.Guard V hs w (i - 1)
      (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n))) →
      CLData.register U i (CLData.context V lam n (QQ c lam n) w, win bR 0 (QQ c lam n)) =
        maskOf (CLChecks.prefixRegister (LL V hs w) i
          (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n)))) := by
    intro i hi hg
    conv_lhs => rw [← toBits_ofBits hyb]
    exact CLData.register_correct U V hV hn hs w hi _ hg
  have hfac : CLData.factor U (k + 1)
      (CLData.context V lam n (QQ c lam n) w, win bR 0 (QQ c lam n)) =
      maskOf ((LL V hs w).factorOfPrefix (k + 1)
        (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n)))) := by
    conv_lhs => rw [← toBits_ofBits hyb]
    exact CLData.factor_correct U V hV hn hs w hk _ hgb
  have hgen : CLData.kernelGenerators U (k + 1)
      (CLData.context V lam n (QQ c lam n) w, win bR 0 (QQ c lam n)) =
      (regKerGens (QQ c lam n) _ (CLChecks.stageLinear (LL V hs w) (k + 1)
        (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n))))).map CL.toBits := by
    rw [regKerGens_toBits]
    conv_lhs => rw [← toBits_ofBits hyb]
    exact CLData.kernelGenerators_correct U V hV hn hs w hk _ hgb
  simp only [hideNextP, comp_apply, pair_apply, eqB_apply, regOf_apply,
    dA_apply, dB_apply, dE_apply, eQ_apply, envT_Q, length_unary, kAt_apply, ctxP_envT T V hT hsamp,
    outputPrefix_at U V hV hn hs w (k := k) (by omega) _ (length_win_Q ha)
      (CLData.guard_mono V hs w (by omega) _ hga),
    outputPrefix_at U V hV hn hs w (k := k) (by omega) _ (length_win_Q hb)
      (CLData.guard_mono V hs w (by omega) _ hgb),
    hreg (k + 1) (by omega) (CLData.guard_mono V hs w (by omega) _ hgb),
    hreg (k + 2) (by omega) (CLData.guard_mono V hs w (by omega) _ hgb), hfac, hgen, toBits_inj]

theorem envT_clock (c lam n : ℕ) (T : TailoredVerifier 7) :
    (envT c lam n T).1 = unary (ansBound 5 lam n) := rfl
theorem envT_M (c lam n : ℕ) (T : TailoredVerifier 7) :
    (envT c lam n T).2.1 = clamp (T.progs, lam) := rfl
theorem envT_idx (c lam n : ℕ) (T : TailoredVerifier 7) : (envT c lam n T).2.2.1 = 2 ^ n := rfl

include hT hn in
theorem length_win_split_le (aR : BitStr) (o : ℕ) (q : BitStr) (κ : Bool) :
    (win aR o (T.lenOf (2 ^ n) q κ)).length ≤ (2 ^ n) ^ lam :=
  (List.length_take_le _ _).trans (lenOf_le hT ((two_le_exp_index_iff n).mpr hn) q κ)

include hT hV hn hsamp in
/-- **The source game's constraints.** -/
theorem sourceP_spec (aR bR : BitStr) (ha : QQ c lam n ≤ aR.length)
    (hb : QQ c lam n ≤ bR.length) :
    sourceP U (envT c lam n T, aR, bR) =
      sourceCons (QQ c lam n) ((2 ^ n) ^ lam) (srcSplitR T V hs) (srcSplitL T V hs)
        (Typed.srcCons (kk c lam n) (jj c lam n) T V hs) aR bR := by
  rw [← sourceConsF_spec]
  have hrun := lpRun_seven U T hT hn
    (srcQuestion V hs (.introspect, false) (win aR 0 (QQ c lam n)))
    (srcQuestion V hs (.introspect, true) (win bR 0 (QQ c lam n)))
    (win aR (QQ c lam n) (srcSplitR T V hs (.introspect, false) (win aR 0 (QQ c lam n))))
    (win bR (QQ c lam n) (srcSplitR T V hs (.introspect, true) (win bR 0 (QQ c lam n))))
    (length_srcQuestion_le V hV hn hs _ _) (length_srcQuestion_le V hV hn hs _ _)
    (length_win_split_le T hT hn _ _ _ _) (length_win_split_le T hT hn _ _ _ _)
    (c := unary (ansBound 5 lam n)) (by simp)
  simp only [sourceP, comp_apply, pair_apply, qr_apply, regOf_apply, dA_apply, dB_apply,
    dE_apply, eClock_apply, eM_apply, eIdx_apply, eQ_apply, atReg_apply, winF_apply, envT_Q,
    envT_R, envT_clock, envT_M, envT_idx, length_unary,
    splitU_envT U T V hT hV hn hsamp hs _ _ _ (length_win_Q ha),
    splitU_envT U T V hT hV hn hsamp hs _ _ _ (length_win_Q hb),
    srcQP_envT U T V hT hV hn hsamp hs _ _ (length_win_Q ha),
    srcQP_envT U T V hT hV hn hsamp hs _ _ (length_win_Q hb)]
  simp only [srcSplitR, srcSplitL, Typed.srcCons] at hrun ⊢
  rw [hrun]

include hT hV hn hsamp in
/-- **One orientation of the directed checks**, under the readable conditions at both
registers. -/
theorem dirP_spec (t u : AuxType 7 × Bool) (aR bR : BitStr) (ha : QQ c lam n ≤ aR.length)
    (hb : QQ c lam n ≤ bR.length)
    (hGa : Typed.G (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs t (win aR 0 (QQ c lam n)))
    (hGb : Typed.G (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs u (win bR 0 (QQ c lam n))) :
    dirP U t u (envT c lam n T, aR, bR) =
      dirAux (QQ c lam n) ((2 ^ n) ^ lam) (srcSplitR T V hs) (srcSplitL T V hs) (LL V hs)
        (regKerGens (QQ c lam n)) (Typed.srcCons (kk c lam n) (jj c lam n) T V hs) t u aR bR := by
  obtain ⟨t, w⟩ := t
  obtain ⟨u, v⟩ := u
  cases t with
  | introspect =>
    cases u with
    | sample =>
      simp only [dirP, dirAux]
      split_ifs with h
      · subst h; exact sampleP_spec U T V hT hV hn hsamp hs w aR bR ha hb
      · rfl
    | read =>
      simp only [dirP, dirAux]
      split_ifs with h
      · subst h; exact readP_spec U T V hT hV hn hsamp hs w aR bR ha hb
      · rfl
    | introspect =>
      cases w <;> cases v <;> first | rfl | exact sourceP_spec U T V hT hV hn hsamp hs aR bR ha hb
    | hide j => cases w <;> cases v <;> rfl
  | sample => cases u <;> cases w <;> cases v <;> rfl
  | read => cases u <;> cases w <;> cases v <;> rfl
  | hide k =>
    cases u with
    | read =>
      simp only [dirP, dirAux]
      split_ifs with h
      · obtain ⟨rfl, hk⟩ := h
        have hk6 : k.val = 6 := by omega
        have hga : CLData.Guard V hs w 6 (CL.ofBits (QQ c lam n) (win aR 0 (QQ c lam n))) := by
          have := hGa.2.1; rw [← hk6]; exact this
        exact hideReadP_spec U T V hT hV hn hsamp hs w aR bR ha hb hga hGb.2.1
      · rfl
    | hide j =>
      simp only [dirP, dirAux]
      split_ifs with h
      · obtain ⟨rfl, hk⟩ := h
        have hgb : CLData.Guard V hs w (k.val + 1)
            (CL.ofBits (QQ c lam n) (win bR 0 (QQ c lam n))) := by
          have := hGb.2.1; rw [hk]; exact this
        exact hideNextP_spec U T V hT hV hn hsamp hs w k.val (by omega) aR bR ha hb hGa.2.1 hgb
      · rfl
    | _ => cases w <;> cases v <;> rfl

theorem auxLenU_envT (t : AuxType 7 × Bool) (aR bR : BitStr) :
    auxLenU t (envT c lam n T, aR, bR) = unary (auxLen (QQ c lam n) ((2 ^ n) ^ lam) t.1) := by
  rw [← auxLenF_spec]
  simp only [auxLenU, comp_apply, pair_apply, qr_apply, const_apply, envT_Q, envT_R]

include hT hV hn hsamp in
/-- **The constraints at a pair of auxiliary labels**, for readable answers of the labels'
readable lengths. -/
theorem auxPairP_spec (t u : AuxType 7 × Bool) (aR bR : BitStr)
    (ha : aR.length = auxLenR (QQ c lam n) ((2 ^ n) ^ lam) t.1)
    (hb : bR.length = auxLenR (QQ c lam n) ((2 ^ n) ^ lam) u.1) :
    auxPairP U t u (envT c lam n T, aR, bR) =
      auxPair (QQ c lam n) ((2 ^ n) ^ lam) (srcSplitR T V hs) (srcSplitL T V hs) (LL V hs)
        (Typed.G (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs) (regKerGens (QQ c lam n))
        (Typed.srcCons (kk c lam n) (jj c lam n) T V hs) t u aR bR := by
  have ha' : QQ c lam n ≤ aR.length := ha ▸ auxLenR_add_le t.1
  have hb' : QQ c lam n ≤ bR.length := hb ▸ auxLenR_add_le u.1
  have hGa := GP_envT U T V hT hV hn hsamp hs t _ (length_win_Q ha')
  have hGb := GP_envT U T V hT hV hn hsamp hs u _ (length_win_Q hb')
  simp only [auxPairP, comp_apply, pair_apply, andOf_apply, atReg_apply, regOf_apply, dA_apply,
    dB_apply, envT_Q, length_unary, const_apply, auxPairF_apply, auxLenU_envT, swapD_apply]
  rw [auxPair]
  by_cases hg :
      Typed.G (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs t (win aR 0 (QQ c lam n)) ∧
      Typed.G (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs u (win bR 0 (QQ c lam n))
  · have hb1 : (GP U t (envT c lam n T, win aR 0 (QQ c lam n)) &&
        GP U u (envT c lam n T, win bR 0 (QQ c lam n))) = true := by
      rw [Bool.and_eq_true, hGa, hGb]; exact hg
    rw [hb1, ite_eq_left rfl, ite_eq_left hg, sameP_spec U T V hT hV hn hsamp hs t aR bR ha' hb',
      dirP_spec U T V hT hV hn hsamp hs t u aR bR ha' hb' hg.1 hg.2,
      dirP_spec U T V hT hV hn hsamp hs u t bR aR hb' ha' hg.2 hg.1]
    simp only [decide_eq_true_eq]
  · have hb1 : (GP U t (envT c lam n T, win aR 0 (QQ c lam n)) &&
        GP U u (envT c lam n T, win bR 0 (QQ c lam n))) = false := by
      rw [← Bool.not_eq_true, Bool.and_eq_true, hGa, hGb]; exact hg
    rw [hb1, ite_eq_right (by simp), ite_eq_right hg]

end Correct

end MIPRE.Tailored.Intro.LpIntro

end
