/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourceCompilerParams
import MIPRE.Foundations.Introspection.ClockSimulationCost

/-! # Explicit runtime of canonical parameter generation -/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program ClockArithmetic

def exponentBitsCost (j : ℕ) : ℕ := (j+2)*(4*j+20)
def powerUnaryCost (j : ℕ) : ℕ := exponentBitsCost j + unaryCost (2^j) + 1

theorem powerUnaryProg_runs_cost (j : ℕ) : ∃ t ≤ powerUnaryCost j,
    powerUnaryProg.Runs (.ofNat j) (.ofNat (2^j)) t := by
  obtain ⟨t,ht,hr⟩ := expBitsProg_runs j
  obtain ⟨s,hs,hsr⟩ := toUnaryProg_runs (2^j)
  refine ⟨_,?_,Eval.let_ hr (Eval.append_of_wellScoped hsr toUnaryProg_wellScoped _)⟩
  change t ≤ exponentBitsCost j at ht
  change s ≤ unaryCost (2^j) at hs
  exact Nat.add_le_add_right (Nat.add_le_add ht hs) 1

def contextCost (post : PolyTimeFun (Data × Data) Data) (a ctx r : Data) (t : ℕ) : ℕ :=
  2*a.size + 2*ctx.size + r.size + t + post.timeBound.eval (ctx.size+r.size+1) + 12

def boundsCost (c lam n : ℕ) : ℕ :=
  let u := lam*n
  let j := (c*canonicalLog lam n+1).size-1
  let m := registerPower c lam n
  let k := fieldBits c lam n
  unaryCost lam + unaryCost n + esize lam + esize n + 2*lam + 2*n + 20 +
    mulCost lam n + (parameterSeed c).timeBound.eval (2*u+1) +
    contextCost parameterPost (.ofNat j) (.cons (.ofNat u) (.ofNat k)) (.ofNat m)
      (powerUnaryCost j) +
    contextCost boundsPost (.ofNat u) (.cons (.ofNat m) (.ofNat k)) (encode (2^u))
      (exponentBitsCost u) + 4

theorem boundsProg_runs_cost (c lam n : ℕ) : ∃ time ≤ boundsCost c lam n,
    (boundsProg c).Runs (encode (lam,n)) (encode (registerBits c lam n,originalBound lam n)) time := by
  let j := (c*canonicalLog lam n+1).size-1
  let k := fieldBits c lam n
  let m := registerPower c lam n
  obtain ⟨t₁,ht₁,h₁⟩ := bothUnary_runs lam n
  obtain ⟨t₂,ht₂,h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃,ht₃,h₃⟩ := (parameterSeed c).computes (unary (lam*n))
  have hs : parameterSeed c (unary (lam*n)) = (unary j,unary (lam*n),unary k) := by
    simp only [parameterSeed_apply,length_unary,canonicalLog,fieldBits,j,k]
  rw [hs] at h₃
  simp only [encode_prod,encode_unary] at h₃
  obtain ⟨t₄,ht₄,h₄⟩ := powerUnaryProg_runs_cost j
  obtain ⟨t₅,ht₅,h₅⟩ := callWithContext_cost powerUnaryProg_closed parameterPost _
    (.cons (.ofNat (lam*n)) (.ofNat k)) _ t₄ h₄
  have h₅' : (callWithContext powerUnaryProg parameterPost).Runs
      (.cons (.ofNat j) (.cons (.ofNat (lam*n)) (.ofNat k)))
      (.cons (.ofNat (lam*n)) (.cons (.ofNat m) (.ofNat k))) t₅ := by
    simpa only [parameterPost,ap₂_apply,comp_apply,fst_apply,snd_apply,treeHead_cons,
      treeTail_cons,treePair_apply,m,registerPower,j] using h₅
  obtain ⟨t₆,ht₆,h₆⟩ := expBitsProg_runs (lam*n)
  obtain ⟨t₇,ht₇,h₇⟩ := callWithContext_cost expBitsProg_wellScoped boundsPost _
    (.cons (.ofNat m) (.ofNat k)) _ t₆ h₆
  have h₇' : (callWithContext expBitsProg boundsPost).Runs
      (.cons (.ofNat (lam*n)) (.cons (.ofNat m) (.ofNat k)))
      (encode (registerBits c lam n,originalBound lam n)) t₇ := by
    simpa only [boundsPost,ap₂_apply,comp_apply,fst_apply,snd_apply,encoded_apply,
      treePair_apply,registerSizeProg_apply,registerBits,originalBound,encode_prod,m,k] using h₇
  refine ⟨_,?_,Eval.let_ h₁ (Eval.append_of_wellScoped (Eval.let_ h₂
    (Eval.append_of_wellScoped (Eval.let_ h₃ (Eval.append_of_wellScoped
      (Eval.let_ h₅' (Eval.append_of_wellScoped h₇'
        (callWithContext_closed expBitsProg_wellScoped boundsPost) _))
      ⟨callWithContext_closed powerUnaryProg_closed parameterPost,
        (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _))
      ⟨(parameterSeed c).closed,
        (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
        (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _))
    ⟨mulProg_wellScoped,(parameterSeed c).closed.mono (by omega) _,
      (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
      (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _)⟩
  change t₂ ≤ mulCost lam n at ht₂
  change t₆ ≤ exponentBitsCost (lam*n) at ht₆
  simp only [esize_unary] at ht₃
  dsimp only [boundsCost,contextCost]
  change _ ≤ _ + _ + _ +
    (2*(Data.ofNat j).size + 2*(Data.cons (.ofNat (lam*n)) (.ofNat k)).size +
      (Data.ofNat m).size + powerUnaryCost j +
      parameterPost.timeBound.eval ((Data.cons (.ofNat (lam*n)) (.ofNat k)).size+(Data.ofNat m).size+1)+12) +
    (2*(Data.ofNat (lam*n)).size + 2*(Data.cons (.ofNat m) (.ofNat k)).size +
      (encode (2^(lam*n))).size + exponentBitsCost (lam*n) +
      boundsPost.timeBound.eval ((Data.cons (.ofNat m) (.ofNat k)).size+(encode (2^(lam*n))).size+1)+12) + 4
  have hm : 2^j = m := rfl
  rw [hm] at ht₅
  omega

end MIPRE.Introspection.SourceCompiler

end
