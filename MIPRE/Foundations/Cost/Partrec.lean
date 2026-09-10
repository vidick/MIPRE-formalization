/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.MachineData
import Mathlib.Computability.Partrec

/-!
# Ambient evaluation is partial recursive

The step of the evaluation machine on data is primitive recursive (`primrec_stepData`),
so evaluation — its `PFun.fix` from the initial configuration — is partial recursive
(`partrec_evalData`), and agrees with `Eval` (`mem_evalData_iff`). Consequently a
polynomial-time function of the ambient model is Mathlib-computable, as soon as its input
is produced by a computable encoding (`PolyTimeFun.computable_comp`). This is the bridge
from the ambient model to Mathlib's computability used by the halting-problem form of the
compression lemma; the other bridge (from `Nat.Partrec.Code` into the model) is
`Cost/FromPartrec.lean`.
-/

namespace MIPRE.Cost

namespace Machine

open Primrec

/-! ## The step is primitive recursive -/

theorem primrec_evD : Primrec evD := Data.primrec_cons.comp (const Data.nil) Primrec.id

theorem primrec_retD : Primrec retD := Data.primrec_cons.comp (const (Data.cons .nil .nil)) Primrec.id

/-- `p ↦ unaryToNat p.left`, the tag of an encoded program or frame. -/
theorem primrec_tag : Primrec fun d : Data => Data.unaryToNat d.left :=
  Data.primrec_unaryToNat.comp Data.primrec_left

theorem primrec_stepEv : Primrec fun q : Data × Data × Data => stepEv q.1 q.2.1 q.2.2 := by
  have hp : Primrec fun q : Data × Data × Data => q.1 := fst
  have henv : Primrec fun q : Data × Data × Data => q.2.1 := fst.comp snd
  have hk : Primrec fun q : Data × Data × Data => q.2.2 := snd.comp snd
  have htag : Primrec fun q : Data × Data × Data => Data.unaryToNat q.1.left := primrec_tag.comp hp
  have hbody : Primrec fun q : Data × Data × Data => q.1.right := Data.primrec_right.comp hp
  have hget0 : Primrec fun q : Data × Data × Data =>
      Data.getList q.2.1 (Data.unaryToNat q.1.right) :=
    Data.primrec_getList.comp henv (Data.primrec_unaryToNat.comp hbody)
  have hgetE : Primrec fun q : Data × Data × Data =>
      Data.getList q.2.1 (Data.unaryToNat q.1.right.left) :=
    Data.primrec_getList.comp henv (Data.primrec_unaryToNat.comp (Data.primrec_left.comp hbody))
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data × Data => Data.unaryToNat q.1.left = n :=
    fun n => PrimrecRel.comp Primrec.eq htag (const n)
  refine Primrec.ite (heq 0) ?_ (Primrec.ite (heq 1) ?_ (Primrec.ite (heq 2) ?_
    (Primrec.ite (heq 3) ?_ (Primrec.ite (heq 4) ?_ (Primrec.ite (heq 5) ?_ ?_)))))
  · exact Data.primrec_cons.comp (primrec_retD.comp hget0) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_retD.comp (const Data.nil)) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp (Data.primrec_left.comp hbody))
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 0))
          (Data.primrec_cons.comp (Data.primrec_right.comp hbody) henv)) hk))
  · refine Primrec.ite (PrimrecRel.comp Primrec.eq hgetE (const Data.nil)) ?_ ?_
    · exact Data.primrec_cons.comp
        (primrec_evD.comp (Data.primrec_left.comp (Data.primrec_right.comp hbody)))
        (Data.primrec_cons.comp henv hk)
    · exact Data.primrec_cons.comp
        (primrec_evD.comp (Data.primrec_right.comp (Data.primrec_right.comp hbody)))
        (Data.primrec_cons.comp (Data.primrec_cons.comp (Data.primrec_left.comp hgetE)
          (Data.primrec_cons.comp (Data.primrec_right.comp hgetE) henv)) hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp (Data.primrec_left.comp hbody))
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 2))
          (Data.primrec_cons.comp (Data.primrec_right.comp hbody) henv)) hk))
  · exact Data.primrec_cons.comp (primrec_evD.comp hbody)
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 3)) (Data.primrec_cons.comp hbody henv)) hk))
  · exact Data.primrec_cons.comp (primrec_retD.comp hbody) (Data.primrec_cons.comp henv hk)

theorem primrec_stepRet : Primrec fun q : Data × Data × Data => stepRet q.1 q.2.1 q.2.2 := by
  have hv : Primrec fun q : Data × Data × Data => q.1 := fst
  have henv : Primrec fun q : Data × Data × Data => q.2.1 := fst.comp snd
  have hk : Primrec fun q : Data × Data × Data => q.2.2 := snd.comp snd
  have hfr : Primrec fun q : Data × Data × Data => q.2.2.left := Data.primrec_left.comp hk
  have hk' : Primrec fun q : Data × Data × Data => q.2.2.right := Data.primrec_right.comp hk
  have hftag : Primrec fun q : Data × Data × Data => Data.unaryToNat q.2.2.left.left :=
    primrec_tag.comp hfr
  have hfb : Primrec fun q : Data × Data × Data => q.2.2.left.right := Data.primrec_right.comp hfr
  have hfb1 : Primrec fun q : Data × Data × Data => q.2.2.left.right.left :=
    Data.primrec_left.comp hfb
  have hfb2 : Primrec fun q : Data × Data × Data => q.2.2.left.right.right :=
    Data.primrec_right.comp hfb
  have hfb22 : Primrec fun q : Data × Data × Data => q.2.2.left.right.right.right :=
    Data.primrec_right.comp hfb2
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data × Data =>
      Data.unaryToNat q.2.2.left.left = n :=
    fun n => PrimrecRel.comp Primrec.eq hftag (const n)
  refine Primrec.ite (PrimrecRel.comp Primrec.eq hk (const Data.nil)) ?_
    (Primrec.ite (heq 0) ?_ (Primrec.ite (heq 1) ?_ (Primrec.ite (heq 2) ?_
      (Primrec.ite (PrimrecRel.comp Primrec.eq hv (const Data.nil)) ?_
        (Primrec.ite (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp hv) (const Data.nil)) ?_
          ?_)))))
  · exact Data.primrec_cons.comp (primrec_retD.comp hv) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp hfb2 (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 1)) hv) hk'))
  · exact Data.primrec_cons.comp (primrec_retD.comp (Data.primrec_cons.comp hfb hv))
      (Data.primrec_cons.comp henv hk')
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp (Data.primrec_cons.comp hv hfb2) hk')
  · exact Data.primrec_cons.comp (primrec_retD.comp (const Data.nil)) (Data.primrec_cons.comp hfb2 hk')
  · exact Data.primrec_cons.comp (primrec_retD.comp (Data.primrec_right.comp hv))
      (Data.primrec_cons.comp hfb2 hk')
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp (Data.primrec_cons.comp (Data.primrec_right.comp hv) hfb22)
        (Data.primrec_cons.comp (Data.primrec_cons.comp (const (Data.ofNat 3))
          (Data.primrec_cons.comp hfb1
            (Data.primrec_cons.comp (Data.primrec_right.comp hv) hfb22))) hk'))

theorem primrec_stepData : Primrec stepData := by
  have hq : Primrec fun d : Data => (d.left.right, d.right.left, d.right.right) :=
    Primrec.pair (Data.primrec_right.comp Data.primrec_left)
      (Primrec.pair (Data.primrec_left.comp Data.primrec_right)
        (Data.primrec_right.comp Data.primrec_right))
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil))
    (primrec_stepEv.comp hq) (primrec_stepRet.comp hq)

theorem primrec_isFinalD : PrimrecPred IsFinalD := by
  have h1 : PrimrecPred fun d : Data => d.left.left ≠ .nil :=
    (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil)).not
  have h2 : PrimrecPred fun d : Data => d.right.right = .nil :=
    PrimrecRel.comp Primrec.eq (Data.primrec_right.comp Data.primrec_right) (const Data.nil)
  exact h1.and h2

theorem primrec_resultD : Primrec resultD := Data.primrec_right.comp Data.primrec_left

theorem primrec_initData : Primrec₂ initData :=
  Data.primrec_cons.comp (primrec_evD.comp fst)
    (Data.primrec_cons.comp (Data.primrec_cons.comp snd (const Data.nil)) (const Data.nil))

/-! ## Evaluation as a fixed point -/

/-- One iteration of the evaluation loop: stop with the value on a final configuration,
otherwise step. -/
def evalStep (d : Data) : Data ⊕ Data :=
  if IsFinalD d then Sum.inl (resultD d) else Sum.inr (stepData d)

theorem computable_evalStep : Computable evalStep :=
  (Primrec.ite primrec_isFinalD (Primrec.sumInl.comp primrec_resultD)
    (Primrec.sumInr.comp primrec_stepData)).to_comp

/-- Evaluation of the program `p` (as data) on `x`, as a partial function: the fixed
point of the evaluation loop from the initial configuration. -/
def evalData (p x : Data) : Part Data :=
  PFun.fix (fun d => Part.some (evalStep d)) (initData p x)

theorem partrec_evalData : Partrec₂ evalData :=
  (Partrec.fix computable_evalStep).comp
    (primrec_initData.to_comp.comp Computable.fst Computable.snd)

theorem mem_fix_of_iterate (d : Data) (N : ℕ) (hfin : IsFinalD (stepData^[N] d))
    (hstep : ∀ n < N, ¬ IsFinalD (stepData^[n] d)) :
    resultD (stepData^[N] d) ∈ PFun.fix (fun d => Part.some (evalStep d)) d := by
  induction N generalizing d with
  | zero =>
    refine PFun.mem_fix_iff.2 (Or.inl ?_)
    simp only [Function.iterate_zero, id] at hfin ⊢
    simp [evalStep, hfin]
  | succ N ih =>
    refine PFun.mem_fix_iff.2 (Or.inr ⟨stepData d, ?_, ?_⟩)
    · have h0 := hstep 0 (Nat.succ_pos N)
      simp only [Function.iterate_zero, id] at h0
      simp [evalStep, h0]
    · rw [Function.iterate_succ_apply] at hfin ⊢
      exact ih _ hfin fun n hn => by
        have := hstep (n + 1) (Nat.succ_lt_succ hn)
        rwa [Function.iterate_succ_apply] at this

theorem exists_iterate_of_mem_fix {d r : Data}
    (h : r ∈ PFun.fix (fun d => Part.some (evalStep d)) d) :
    ∃ N, IsFinalD (stepData^[N] d) ∧ resultD (stepData^[N] d) = r := by
  refine PFun.fixInduction (C := fun d => ∃ N, IsFinalD (stepData^[N] d) ∧
    resultD (stepData^[N] d) = r) h fun d hd ih => ?_
  by_cases hf : IsFinalD d
  · refine ⟨0, hf, ?_⟩
    rcases PFun.mem_fix_iff.1 hd with h1 | ⟨d', hd', -⟩
    · simp [evalStep, hf] at h1
      exact h1.symm
    · simp [evalStep, hf] at hd'
  · rcases PFun.mem_fix_iff.1 hd with h1 | ⟨d', hd', -⟩
    · simp [evalStep, hf] at h1
    · have hd'' : d' = stepData d := by simpa [evalStep, hf] using hd'
      subst hd''
      obtain ⟨N, hN, hr⟩ := ih _ hd'
      exact ⟨N + 1, by rwa [Function.iterate_succ_apply], by rwa [Function.iterate_succ_apply]⟩

theorem mem_fix_of_steps : ∀ (N : ℕ) (c : Cfg) (r : Data) (e : Env),
    step^[N] c = ⟨.ret r, e, []⟩ → r ∈ PFun.fix (fun d => Part.some (evalStep d)) c.toData := by
  intro N
  induction N with
  | zero =>
    intro c r e h
    simp only [Function.iterate_zero, id] at h
    subst h
    refine PFun.mem_fix_iff.2 (Or.inl ?_)
    have hf : IsFinalD (Cfg.toData ⟨.ret r, e, []⟩) := (isFinalD_toData _).2 ⟨r, e, rfl⟩
    simp [evalStep, hf, resultD_toData]
  | succ N ih =>
    intro c r e h
    by_cases hf : ∃ r' e', c = ⟨.ret r', e', []⟩
    · obtain ⟨r', e', rfl⟩ := hf
      have hfix := Function.iterate_fixed (f := step) (x := ⟨.ret r', e', []⟩) rfl (N + 1)
      rw [hfix] at h
      obtain rfl := Ctrl.ret.inj (Cfg.mk.inj h).1
      refine PFun.mem_fix_iff.2 (Or.inl ?_)
      have hf : IsFinalD (Cfg.toData ⟨.ret r', e', []⟩) := (isFinalD_toData _).2 ⟨r', e', rfl⟩
      simp [evalStep, hf, resultD_toData]
    · have hnf : ¬ IsFinalD c.toData := fun h' => hf ((isFinalD_toData c).1 h')
      refine PFun.mem_fix_iff.2 (Or.inr ⟨(step c).toData, ?_, ?_⟩)
      · simp [evalStep, hnf, stepData_toData]
      · rw [Function.iterate_succ_apply] at h
        exact ih (step c) r e h

/-- Evaluation on data agrees with `Eval`. -/
theorem mem_evalData_iff (c : Prog) (x r : Data) :
    r ∈ evalData c.toData x ↔ ∃ t, c.Runs x r t := by
  rw [halts_iff, evalData, initData_eq]
  constructor
  · intro h
    obtain ⟨N, hN, hr⟩ := exists_iterate_of_mem_fix h
    rw [iterate_stepData_toData, isFinalD_toData] at hN
    obtain ⟨r', e, hc⟩ := hN
    rw [iterate_stepData_toData, hc, resultD_toData] at hr
    subst hr
    exact ⟨N, e, hc⟩
  · rintro ⟨N, e, hN⟩
    exact mem_fix_of_steps N _ r e hN

end Machine

/-! ## Polynomial-time functions are computable -/

theorem evalData_encode {α β : Type*} [SizedEncoding α] [SizedEncoding β] (F : PolyTimeFun α β)
    (a : α) : Machine.evalData (encode F.code) (encode a) = Part.some (encode (F a)) := by
  refine Part.eq_some_iff.2 ?_
  rw [show (encode F.code : Data) = F.code.toData from rfl, Machine.mem_evalData_iff]
  obtain ⟨t, -, h⟩ := F.computes a
  exact ⟨t, h⟩

/-- A polynomial-time function of the ambient model, precomposed with a computable
encoding of its input and followed by a computable decoding of its output, is
Mathlib-computable. -/
theorem PolyTimeFun.computable_comp {α β γ : Type*} [SizedEncoding α] [SizedEncoding β]
    [Primcodable γ] [Primcodable β] [Inhabited β] (F : PolyTimeFun α β) (h : γ → α)
    (hh : Computable fun c => (encode (h c) : Data))
    (hβ : Computable fun d : Data => (SizedEncoding.decode d : Option β)) :
    Computable fun c => F (h c) := by
  have h1 : Computable fun c => (encode (F (h c)) : Data) :=
    Partrec.of_eq_tot (Machine.partrec_evalData.comp (Computable.const (encode F.code)) hh)
      fun c => by rw [evalData_encode]; exact Part.mem_some _
  have h2 : Computable fun c => (SizedEncoding.decode (encode (F (h c)) : Data) : Option β) :=
    hβ.comp h1
  refine (Primrec.option_getD_default.to_comp.comp h2).of_eq fun c => ?_
  simp [SizedEncoding.decode_encode]


end MIPRE.Cost
