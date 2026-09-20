/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Flatten

/-!
# Polynomial-time case analysis on circuit gates

Unlike formula nodes, AND and OR gates carry two binary wire indices and NOT
carries one. Dispatch retains those payloads and charges for copying them.
-/

namespace MIPRE.SAT

open Cost Polynomial

namespace GateDispatch

private def callPayload (d : ℕ) (F : Prog) : Prog :=
  .let_ (.cons (.var (d + 2)) (.var (d + 1))) F
private def rest4 (Fn : Prog) : Prog := .elim 1 (callPayload 8 Fn) .nil
private def rest3 (Fo Fn : Prog) : Prog := .elim 1 (callPayload 6 Fo) (rest4 Fn)
private def rest2 (Fa Fo Fn : Prog) : Prog := .elim 1 (callPayload 4 Fa) (rest3 Fo Fn)
private def rest1 (Fc Fa Fo Fn : Prog) : Prog := .elim 1 (callPayload 2 Fc) (rest2 Fa Fo Fn)
private def tag (Fi Fc Fa Fo Fn : Prog) : Prog := .elim 0 (callPayload 0 Fi) (rest1 Fc Fa Fo Fn)

def program (Fi Fc Fa Fo Fn : Prog) : Prog :=
  .elim 0 .nil (.elim 1 .nil (tag Fi Fc Fa Fo Fn))

theorem program_closed {Fi Fc Fa Fo Fn : Prog} (hi : Fi.WellScoped 1)
    (hc : Fc.WellScoped 1) (ha : Fa.WellScoped 1) (ho : Fo.WellScoped 1) (hn : Fn.WellScoped 1) :
    (program Fi Fc Fa Fo Fn).WellScoped 1 := by
  simp [program, tag, rest1, rest2, rest3, rest4, callPayload, Prog.WellScoped,
    hi.mono (show 1 ≤ 6 by omega) _, hc.mono (show 1 ≤ 8 by omega) _,
    ha.mono (show 1 ≤ 10 by omega) _, ho.mono (show 1 ≤ 12 by omega) _,
    hn.mono (show 1 ≤ 14 by omega) _]

variable {Fi Fc Fa Fo Fn : Prog}

theorem program_input (hf : Fi.WellScoped 1) (ea : Data) (i : ℕ) {r : Data} {t : ℕ}
    (h : Eval [.cons ea (encode i)] Fi r t) :
    Eval [.cons ea (encode (Gate.input i))] (program Fi Fc Fa Fo Fn) r
      (ea.size + esize i + t + 7) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode (Gate.input i))]) (i := 0) (n := .nil)
    (a := ea) (b := encode (Gate.input i)) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 0) (b := encode i)
      (by rfl)
      (Eval.elim_nil (i := 0) (c := rest1 Fc Fa Fo Fn) (by simp [Data.ofNat])
          (show Eval _ (callPayload 0 Fi) _ _ from
            Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := ea) (by simp))
              (Eval.var_of_get (i := 1) (v := encode i) (by simp)))
              (Eval.append_of_wellScoped h hf _))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem program_const (hf : Fc.WellScoped 1) (ea : Data) (b : Bool) {r : Data} {t : ℕ}
    (h : Eval [.cons ea (encode b)] Fc r t) :
    Eval [.cons ea (encode (Gate.const b))] (program Fi Fc Fa Fo Fn) r
      (ea.size + esize b + t + 8) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode (Gate.const b))]) (i := 0) (n := .nil)
    (a := ea) (b := encode (Gate.const b)) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 1) (b := encode b)
      (by rfl)
      (Eval.elim_cons (i := 0) (n := callPayload 0 Fi)
          (a := .nil) (b := .ofNat 0) (by simp [Data.ofNat])
          (Eval.elim_nil (i := 1) (c := rest2 Fa Fo Fn) (by simp [Data.ofNat])
          (show Eval _ (callPayload 2 Fc) _ _ from
            Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := ea) (by simp))
              (Eval.var_of_get (i := 3) (v := encode b) (by simp)))
              (Eval.append_of_wellScoped h hf _)))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem program_and (hf : Fa.WellScoped 1) (ea : Data) (u v : ℕ) {r : Data} {t : ℕ}
    (h : Eval [.cons ea (encode (u, v))] Fa r t) :
    Eval [.cons ea (encode (Gate.and u v))] (program Fi Fc Fa Fo Fn) r
      (ea.size + esize (u, v) + t + 9) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode (Gate.and u v))]) (i := 0) (n := .nil)
    (a := ea) (b := encode (Gate.and u v)) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 2) (b := encode (u, v))
      (by rfl)
      (Eval.elim_cons (i := 0) (n := callPayload 0 Fi)
          (a := .nil) (b := .ofNat 1) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := callPayload 2 Fc)
          (a := .nil) (b := .ofNat 0) (by simp [Data.ofNat])
          (Eval.elim_nil (i := 1) (c := rest3 Fo Fn) (by simp [Data.ofNat])
          (show Eval _ (callPayload 4 Fa) _ _ from
            Eval.let_ (Eval.cons (Eval.var_of_get (i := 6) (v := ea) (by simp))
              (Eval.var_of_get (i := 5) (v := encode (u, v)) (by simp)))
              (Eval.append_of_wellScoped h hf _))))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem program_or (hf : Fo.WellScoped 1) (ea : Data) (u v : ℕ) {r : Data} {t : ℕ}
    (h : Eval [.cons ea (encode (u, v))] Fo r t) :
    Eval [.cons ea (encode (Gate.or u v))] (program Fi Fc Fa Fo Fn) r
      (ea.size + esize (u, v) + t + 10) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode (Gate.or u v))]) (i := 0) (n := .nil)
    (a := ea) (b := encode (Gate.or u v)) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 3) (b := encode (u, v))
      (by rfl)
      (Eval.elim_cons (i := 0) (n := callPayload 0 Fi)
          (a := .nil) (b := .ofNat 2) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := callPayload 2 Fc)
          (a := .nil) (b := .ofNat 1) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := callPayload 4 Fa)
          (a := .nil) (b := .ofNat 0) (by simp [Data.ofNat])
          (Eval.elim_nil (i := 1) (c := rest4 Fn) (by simp [Data.ofNat])
          (show Eval _ (callPayload 6 Fo) _ _ from
            Eval.let_ (Eval.cons (Eval.var_of_get (i := 8) (v := ea) (by simp))
              (Eval.var_of_get (i := 7) (v := encode (u, v)) (by simp)))
              (Eval.append_of_wellScoped h hf _)))))))
  exact e.cast_cost (by simp only [esize]; omega)

theorem program_not (hf : Fn.WellScoped 1) (ea : Data) (u : ℕ) {r : Data} {t : ℕ}
    (h : Eval [.cons ea (encode u)] Fn r t) :
    Eval [.cons ea (encode (Gate.not u))] (program Fi Fc Fa Fo Fn) r
      (ea.size + esize u + t + 11) := by
  have e := Eval.elim_cons (env := [Data.cons ea (encode (Gate.not u))]) (i := 0) (n := .nil)
    (a := ea) (b := encode (Gate.not u)) (by simp)
    (Eval.elim_cons (i := 1) (n := .nil) (a := .ofNat 4) (b := encode u)
      (by rfl)
      (Eval.elim_cons (i := 0) (n := callPayload 0 Fi)
          (a := .nil) (b := .ofNat 3) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := callPayload 2 Fc)
          (a := .nil) (b := .ofNat 2) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := callPayload 4 Fa)
          (a := .nil) (b := .ofNat 1) (by simp [Data.ofNat])
          (Eval.elim_cons (i := 1) (n := callPayload 6 Fo)
          (a := .nil) (b := .ofNat 0) (by simp [Data.ofNat])
          (Eval.elim_nil (i := 1) (c := .nil) (by simp [Data.ofNat])
          (show Eval _ (callPayload 8 Fn) _ _ from
            Eval.let_ (Eval.cons (Eval.var_of_get (i := 10) (v := ea) (by simp))
              (Eval.var_of_get (i := 9) (v := encode u) (by simp)))
              (Eval.append_of_wellScoped h hf _))))))))
  exact e.cast_cost (by simp only [esize]; omega)

end GateDispatch

namespace PolyTimeFun

variable {α β : Type*} [SizedEncoding α] [SizedEncoding β]

/-- The mathematical branch dispatcher, retaining every gate's payload. -/
def casesGateFun (Fi Fn : α × ℕ → β) (Fc : α × Bool → β)
    (Fa Fo : α × (ℕ × ℕ) → β) : α × Gate → β
  | (a, .input i) => Fi (a, i)
  | (a, .const b) => Fc (a, b)
  | (a, .and u v) => Fa (a, (u, v))
  | (a, .or u v) => Fo (a, (u, v))
  | (a, .not u) => Fn (a, u)

/-- Uniform ambient case analysis on a circuit gate. -/
noncomputable def casesGate (Fi : Cost.PolyTimeFun (α × ℕ) β)
    (Fc : Cost.PolyTimeFun (α × Bool) β) (Fa Fo : Cost.PolyTimeFun (α × (ℕ × ℕ)) β)
    (Fn : Cost.PolyTimeFun (α × ℕ) β) : Cost.PolyTimeFun (α × Gate) β where
  toFun := casesGateFun Fi Fn Fc Fa Fo
  code := GateDispatch.program Fi.code Fc.code Fa.code Fo.code Fn.code
  closed := GateDispatch.program_closed Fi.closed Fc.closed Fa.closed Fo.closed Fn.closed
  timeBound := X + Fi.timeBound + Fc.timeBound + Fa.timeBound + Fo.timeBound + Fn.timeBound + C 11
  computes p := by
    obtain ⟨a, g⟩ := p
    cases g with
    | input i =>
      obtain ⟨t, ht, e⟩ := Fi.computes (a, i)
      refine ⟨esize a + esize i + t + 7, ?_, GateDispatch.program_input Fi.closed _ i e⟩
      have hg : esize (Gate.input i) = esize i + 2 := by
        change (Data.cons (.ofNat 0) (encode i)).size = _
        simp [Data.ofNat, esize]
        omega
      have hm := polynomial_eval_mono Fi.timeBound
        (show esize (a, i) ≤ esize (a, Gate.input i) by simp only [esize_prod, hg]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod, hg] at hm ht ⊢
      omega
    | const b =>
      obtain ⟨t, ht, e⟩ := Fc.computes (a, b)
      refine ⟨esize a + esize b + t + 8, ?_, GateDispatch.program_const Fc.closed _ b e⟩
      have hg : esize (Gate.const b) = esize b + 4 := by
        change (Data.cons (.ofNat 1) (encode b)).size = _
        simp [Data.ofNat, esize]
        omega
      have hm := polynomial_eval_mono Fc.timeBound
        (show esize (a, b) ≤ esize (a, Gate.const b) by simp only [esize_prod, hg]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod, hg] at hm ht ⊢
      omega
    | and u v =>
      obtain ⟨t, ht, e⟩ := Fa.computes (a, (u, v))
      refine ⟨esize a + esize (u, v) + t + 9, ?_, GateDispatch.program_and Fa.closed _ u v e⟩
      have hg : esize (Gate.and u v) = esize (u, v) + 6 := by
        change (Data.cons (.ofNat 2) (encode (u, v))).size = _
        simp [Data.ofNat, esize]
        omega
      have hm := polynomial_eval_mono Fa.timeBound
        (show esize (a, (u, v)) ≤ esize (a, Gate.and u v) by simp only [esize_prod, hg]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod, hg] at hm ht ⊢
      omega
    | or u v =>
      obtain ⟨t, ht, e⟩ := Fo.computes (a, (u, v))
      refine ⟨esize a + esize (u, v) + t + 10, ?_, GateDispatch.program_or Fo.closed _ u v e⟩
      have hg : esize (Gate.or u v) = esize (u, v) + 8 := by
        change (Data.cons (.ofNat 3) (encode (u, v))).size = _
        simp [Data.ofNat, esize]
        omega
      have hm := polynomial_eval_mono Fo.timeBound
        (show esize (a, (u, v)) ≤ esize (a, Gate.or u v) by simp only [esize_prod, hg]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod, hg] at hm ht ⊢
      omega
    | not u =>
      obtain ⟨t, ht, e⟩ := Fn.computes (a, u)
      refine ⟨esize a + esize u + t + 11, ?_, GateDispatch.program_not Fn.closed _ u e⟩
      have hg : esize (Gate.not u) = esize u + 10 := by
        change (Data.cons (.ofNat 4) (encode u)).size = _
        simp [Data.ofNat, esize]
        omega
      have hm := polynomial_eval_mono Fn.timeBound
        (show esize (a, u) ≤ esize (a, Gate.not u) by simp only [esize_prod, hg]; omega)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod, hg] at hm ht ⊢
      omega

end PolyTimeFun

end MIPRE.SAT

