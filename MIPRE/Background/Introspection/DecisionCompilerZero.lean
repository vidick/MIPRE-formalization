/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockCompiler
import MIPRE.Foundations.CL.DetypingDeciderRoute
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram

/-! # Constant-resource branches of the introspection decider

At zero parameter or index, the sampler has dimension zero. These branches
inspect the answer payload without copying the index or source metadata.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open ClockSimulation
open AuxiliaryProgram

def zeroFields : PolyTimeFun Data (BitStr × BitStr × BitStr × BitStr) :=
  (readBits.comp treeHead).pair ((readBits.comp (treeHead.comp treeTail)).pair
    ((readBits.comp (treeHead.comp (treeTail.comp treeTail))).pair
      (readBits.comp (treeTail.comp (treeTail.comp treeTail)))))

def zeroTest : PolyTimeFun Data Bool :=
  let x := fst.comp zeroFields
  let y := fst.comp (snd.comp zeroFields)
  let a := fst.comp (snd.comp (snd.comp zeroFields))
  let b := snd.comp (snd.comp (snd.comp zeroFields))
  andCheck (equal (PolyTimeFun.id Data) (encoded.comp zeroFields))
    (andCheck (equal x (const [])) (andCheck (equal y (const []))
      (andCheck (leNat.comp ((CL.Detyping.DeciderProgram.lengthNat.comp a).pair (const 2)))
        (leNat.comp ((CL.Detyping.DeciderProgram.lengthNat.comp b).pair (const 2))))))

theorem zeroTest_encode (x y a b : BitStr) :
    zeroTest (encode (x,y,a,b)) = true ↔
      x = [] ∧ y = [] ∧ a.length ≤ 2 ∧ b.length ≤ 2 := by
  simp [zeroTest, zeroFields, andCheck_iff, equal_iff, encode_prod, readBits_encode]

/-- Ignore the index in place and inspect only the payload. -/
def zeroProg : Prog := .elim 0 .nil (callVar 1 zeroTest.code)

theorem zeroProg_closed : zeroProg.WellScoped 1 := by
  exact ⟨by omega, trivial, callVar_wellScoped (by omega) zeroTest.closed⟩

theorem zeroProg_runs (n d : Data) :
    ∃ t ≤ zeroTest.timeBound.eval d.size + d.size + 3,
      zeroProg.Runs (.cons n d) (encode (zeroTest d)) t := by
  obtain ⟨t, ht, hr⟩ := zeroTest.computes d
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (by rfl)
    (callVar_eval (i := 1) zeroTest.closed (by rfl) hr)⟩
  change t ≤ zeroTest.timeBound.eval d.size at ht
  simp only [encode_data]
  omega

/-- Test the encoded index before entering a program containing source metadata. -/
def zeroWrap (p : Prog) : Prog :=
  .elim 0 .nil (.elim 0 (callVar 1 zeroTest.code) (callVar 4 p))

theorem zeroWrap_closed {p : Prog} (hp : p.WellScoped 1) : (zeroWrap p).WellScoped 1 := by
  exact ⟨by omega, trivial, by omega, callVar_wellScoped (by omega) zeroTest.closed,
    callVar_wellScoped (by omega) hp⟩

theorem zeroWrap_runs_zero (p : Prog) (d : Data) :
    ∃ t ≤ zeroTest.timeBound.eval d.size + d.size + 4,
      (zeroWrap p).Runs (.cons (encode (0 : ℕ)) d) (encode (zeroTest d)) t := by
  obtain ⟨t, ht, hr⟩ := zeroTest.computes d
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (by rfl) (Eval.elim_nil (i := 0) (by rfl)
    (callVar_eval (i := 1) zeroTest.closed (by rfl) hr))⟩
  change t ≤ zeroTest.timeBound.eval d.size at ht
  simp only [encode_data]
  omega

theorem zeroWrap_runs_pos {p : Prog} (hp : p.WellScoped 1) {n : ℕ} (hn : 1 ≤ n)
    (d r : Data) (t : ℕ) (hr : p.Runs (.cons (encode n) d) r t) :
    (zeroWrap p).Runs (.cons (encode n) d) r (t + (Data.cons (encode n) d).size + 4) := by
  have hne : encode n ≠ Data.nil := by
    intro h
    have hz : n = 0 := encode_injective (show encode n = encode (0 : ℕ) from h)
    omega
  cases he : encode n with
  | nil => exact False.elim (hne he)
  | cons a b =>
    rw [he] at hr
    have hcall := callVar_eval
      (env := [a,b,Data.cons a b,d,Data.cons (.cons a b) d]) (i := 4) hp (by rfl) hr
    have hinner := Eval.elim_cons (env := [Data.cons a b,d,Data.cons (.cons a b) d])
      (i := 0) (n := callVar 1 zeroTest.code) (by rfl) hcall
    have houter := Eval.elim_cons (env := [Data.cons (.cons a b) d])
      (i := 0) (n := Prog.nil) (by rfl) hinner
    exact houter.cast_cost (by omega)

def zeroWrapCompiler : PolyTimeFun Prog Prog :=
  ap₂ codeElim (const .nil)
    (ap₂ codeElim (const (callVar 1 zeroTest.code)) (codeCall 4))

@[simp] theorem zeroWrapCompiler_apply (p : Prog) : zeroWrapCompiler p = zeroWrap p := rfl

theorem zero_time_bound :
    ∃ C, ∀ n d, ∃ t ≤ 2*(d.size+1)^C,
      zeroProg.Runs (.cons n d) (encode (zeroTest d)) t := by
  obtain ⟨C, hC⟩ := (PolyBounded.eval
    (zeroTest.timeBound + Polynomial.X + 4) PolyBounded.id).exists_le_pow
  refine ⟨C, fun n d => ?_⟩
  obtain ⟨t, ht, hr⟩ := zeroProg_runs n d
  have hd := Data.size_pos d
  have hm := polynomial_eval_mono zeroTest.timeBound (show d.size ≤ d.size+1 by omega)
  have hp := hC (d.size+1) (by omega)
  simp only [Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hp
  exact ⟨t, by omega, hr⟩

theorem zeroWrap_zero_time_bound :
    ∃ C, ∀ p d, ∃ t ≤ 2*(d.size+1)^C,
      (zeroWrap p).Runs (.cons (encode (0 : ℕ)) d) (encode (zeroTest d)) t := by
  obtain ⟨C, hC⟩ := (PolyBounded.eval
    (zeroTest.timeBound + Polynomial.X + 4) PolyBounded.id).exists_le_pow
  refine ⟨C, fun p d => ?_⟩
  obtain ⟨t, ht, hr⟩ := zeroWrap_runs_zero p d
  have hd := Data.size_pos d
  have hm := polynomial_eval_mono zeroTest.timeBound (show d.size ≤ d.size+1 by omega)
  have hp := hC (d.size+1) (by omega)
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat] at hp
  exact ⟨t, by omega, hr⟩

end MIPRE.Introspection.DecisionCompiler
