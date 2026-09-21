/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockArithmetic
import MIPRE.Foundations.Introspection.DynamicParser

/-! # Executable canonical register and answer bounds

For `R = 2^(lambda*n)`, the paper uses `t = max 2 (lambda*n)`,
`m = 2^(size(c*t+1)-1)`, and `log q = c*size(t-1)+1`.
Here `size(t-1)` is the integer ceiling of `log₂ t`. The universal even
constant `c` is fixed; `lambda` and `n` are binary program inputs.
The output is the binary pair `(Q,R)` with `Q = 2^m * log q`.
-/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial

def canonicalLog (lam n : ℕ) : ℕ := max 2 (lam * n)
def registerPower (c lam n : ℕ) : ℕ := 2 ^ ((c * canonicalLog lam n + 1).size - 1)
def fieldBits (c lam n : ℕ) : ℕ := c * (canonicalLog lam n - 1).size + 1
def registerBits (c lam n : ℕ) : ℕ := 2 ^ registerPower c lam n * fieldBits c lam n
def originalBound (lam n : ℕ) : ℕ := 2 ^ (lam * n)

theorem originalBound_eq (lam n : ℕ) : originalBound lam n = (2 ^ n) ^ lam := by
  simp [originalBound, ← pow_mul, Nat.mul_comm]

def affineUnary (c : ℕ) : PolyTimeFun Unary Unary where
  toFun u := unary (c * u.length + 1)
  code := polyProg [1, c]
  closed := polyProg_wellScoped _
  timeBound := (polyProg_runs [1, c]).choose
  computes u := by
    obtain ⟨t, ht, hr⟩ := (polyProg_runs [1, c]).choose_spec u.length []
    refine ⟨t, ht.trans (polynomial_eval_mono _ (length_le_esize_list u)), ?_⟩
    have he : encode u = Data.ofNat u.length := by rw [← unary_length u, encode_unary, length_unary]
    rw [he, encode_unary]
    simpa only [Prog.Runs, Data.polyEval, Nat.mul_zero, Nat.add_zero, Nat.mul_comm, Nat.add_comm] using hr

@[simp] theorem affineUnary_apply (c : ℕ) (u : Unary) :
    affineUnary c u = unary (c * u.length + 1) := rfl

def clampLog : PolyTimeFun Unary Unary :=
  ite (ap₂ leNat (const 2) unaryToBin) (PolyTimeFun.id Unary) (const (unary 2))

theorem clampLog_apply (u : Unary) : clampLog u = unary (max 2 u.length) := by
  by_cases h : 2 ≤ u.length
  · simp [clampLog, PolyTimeFun.ite_apply, h, unary_length]
  · simp [clampLog, PolyTimeFun.ite_apply, h, Nat.max_eq_left (by omega : u.length ≤ 2)]

def unarySize : PolyTimeFun Unary Unary := length.comp (natBits.comp unaryToBin)

theorem unarySize_apply (u : Unary) : unarySize u = unary u.length.size := by
  simp [unarySize, Nat.size_eq_bits_len]

/-- Prepare the binary-power exponent, the original logarithm, and the field bit length. -/
def parameterSeed (c : ℕ) : PolyTimeFun Unary (Unary × Unary × Unary) :=
  (tail.comp (unarySize.comp ((affineUnary c).comp clampLog))).pair
    ((PolyTimeFun.id Unary).pair ((affineUnary c).comp (unarySize.comp (tail.comp clampLog))))

theorem parameterSeed_apply (c : ℕ) (u : Unary) :
    parameterSeed c u = (unary ((c * max 2 u.length + 1).size - 1), u,
      unary (c * (max 2 u.length - 1).size + 1)) := by
  simp [parameterSeed, unarySize_apply, clampLog_apply, unary, List.tail_replicate]

def powerUnaryProg : Prog := .let_ expBitsProg toUnaryProg

theorem powerUnaryProg_closed : powerUnaryProg.WellScoped 1 :=
  ⟨expBitsProg_wellScoped, toUnaryProg_wellScoped.mono (by omega) _⟩

theorem powerUnaryProg_runs (j : ℕ) :
    ∃ t, powerUnaryProg.Runs (.ofNat j) (.ofNat (2 ^ j)) t := by
  obtain ⟨t, _, ht⟩ := expBitsProg_runs j
  obtain ⟨s, _, hs⟩ := toUnaryProg_runs (2 ^ j)
  exact ⟨_, Eval.let_ ht (Eval.append_of_wellScoped hs toUnaryProg_wellScoped _)⟩

/-- Read a raw unary chain by its length; total on arbitrary data. -/
def readUnary : PolyTimeFun Data Unary := length.comp (ofEncodeEq rawList encode_rawList)

theorem readUnary_ofNat (n : ℕ) : readUnary (.ofNat n) = unary n := by
  change unary (rawList (.ofNat n)).length = unary n
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Data.ofNat, rawList, List.length_cons] using congrArg (· + 1) ih

def parameterPost : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (treeHead.comp fst) (ap₂ treePair snd (treeTail.comp fst))

/-- Shift the binary field bit length by the computed unary register power. -/
def registerSizeProg : PolyTimeFun Data ℕ :=
  bitsValue.comp (ap₂ append ((map (const false : PolyTimeFun Unit Bool)).comp
      (readUnary.comp treeHead))
    (natBits.comp (unaryToBin.comp (readUnary.comp treeTail))))

private theorem bitsVal_zeros (j : ℕ) (bs : BitStr) :
    bitsVal (List.replicate j false ++ bs) = 2 ^ j * bitsVal bs := by
  induction j with
  | zero => simp
  | succ j ih => simp [List.replicate_succ, bitsVal_cons, ih, Nat.bit_val, pow_succ]; ring

theorem registerSizeProg_apply (m k : ℕ) :
    registerSizeProg (.cons (.ofNat m) (.ofNat k)) = 2 ^ m * k := by
  simp [registerSizeProg, readUnary_ofNat, unary, bitsVal_zeros, bitsVal_bits]

def boundsPost : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (encoded.comp (registerSizeProg.comp fst)) snd

/-- A fixed program computes the paper's binary `(Q,R)` from binary `(lambda,n)`. -/
def boundsProg (c : ℕ) : Prog :=
  .let_ ClockArithmetic.bothUnary (.let_ mulProg (.let_ (parameterSeed c).code
    (.let_ (callWithContext powerUnaryProg parameterPost)
      (callWithContext expBitsProg boundsPost))))

theorem boundsProg_closed (c : ℕ) : (boundsProg c).WellScoped 1 :=
  ⟨ClockArithmetic.bothUnary_closed, mulProg_wellScoped.mono (by omega) _,
    (parameterSeed c).closed.mono (by omega) _,
    (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
    (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩

theorem boundsProg_runs (c lam n : ℕ) : ∃ time,
    (boundsProg c).Runs (encode (lam, n)) (encode (registerBits c lam n, originalBound lam n)) time := by
  let j := (c * canonicalLog lam n + 1).size - 1
  let k := fieldBits c lam n
  let m := registerPower c lam n
  obtain ⟨t₁, _, h₁⟩ := ClockArithmetic.bothUnary_runs lam n
  obtain ⟨t₂, _, h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃, _, h₃⟩ := (parameterSeed c).computes (unary (lam * n))
  have hs : parameterSeed c (unary (lam * n)) = (unary j, unary (lam * n), unary k) := by
    simp only [parameterSeed_apply, length_unary, canonicalLog, fieldBits, j, k]
  rw [hs] at h₃
  simp only [encode_prod, encode_unary] at h₃
  obtain ⟨t₄, h₄⟩ := powerUnaryProg_runs j
  obtain ⟨t₅, h₅⟩ := callWithContext_runs powerUnaryProg_closed parameterPost _
    (.cons (.ofNat (lam * n)) (.ofNat k)) _ t₄ h₄
  have h₅' : (callWithContext powerUnaryProg parameterPost).Runs
      (.cons (.ofNat j) (.cons (.ofNat (lam * n)) (.ofNat k)))
      (.cons (.ofNat (lam * n)) (.cons (.ofNat m) (.ofNat k))) t₅ := by
    simpa only [parameterPost, ap₂_apply, comp_apply, fst_apply, snd_apply, treeHead_cons,
      treeTail_cons, treePair_apply, m, registerPower, j] using h₅
  obtain ⟨t₆, _, h₆⟩ := expBitsProg_runs (lam * n)
  obtain ⟨t₇, h₇⟩ := callWithContext_runs expBitsProg_wellScoped boundsPost _
    (.cons (.ofNat m) (.ofNat k)) _ t₆ h₆
  have h₇' : (callWithContext expBitsProg boundsPost).Runs
      (.cons (.ofNat (lam * n)) (.cons (.ofNat m) (.ofNat k)))
      (encode (registerBits c lam n, originalBound lam n)) t₇ := by
    simpa only [boundsPost, ap₂_apply, comp_apply, fst_apply, snd_apply, encoded_apply,
      treePair_apply, registerSizeProg_apply, registerBits, originalBound, encode_prod, m, k] using h₇
  exact ⟨_, Eval.let_ h₁ (Eval.append_of_wellScoped (Eval.let_ h₂
    (Eval.append_of_wellScoped (Eval.let_ h₃ (Eval.append_of_wellScoped
      (Eval.let_ h₅' (Eval.append_of_wellScoped h₇'
        (callWithContext_closed expBitsProg_wellScoped boundsPost) _))
      ⟨callWithContext_closed powerUnaryProg_closed parameterPost,
        (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _))
      ⟨(parameterSeed c).closed,
        (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
        (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _))
    ⟨mulProg_wellScoped, (parameterSeed c).closed.mono (by omega) _,
      (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
      (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _)⟩

end MIPRE.Introspection.SourceCompiler

end
