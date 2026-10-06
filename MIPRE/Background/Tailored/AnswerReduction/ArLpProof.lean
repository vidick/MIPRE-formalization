/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpArith
public import MIPRE.Foundations.SAT.CircuitFieldCorrect
public import MIPRE.Foundations.SAT.GatePadding

@[expose] public section

/-!
# The proof check, as a program

Slice P4h of `planning/aldous-lyons-track.md`: the constraints of the proof check of the
answer-reduced game (`Typed.proofCons`) at the oracle's point question, computed by a program
from the parameters, the point, the oracle's readable answer and the seed's circuit.

* `circValF`: the circuit polynomial at the point, by the circuit evaluator of
  `MIPRE.SAT.Circuit.circuitBits` (`circValF_eq`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
  MvPolynomial

variable {t : ℕ} {ht : 1 ≤ t}

/-! ## The circuit polynomial at a point -/

/-- **The circuit polynomial at a point**, on `(t, nIn, s, the point's coordinates, the gates)`:
the evaluator of the circuit on the coordinates of its `nIn` inputs and `s` gates. -/
def circValF : PolyTimeFun (Unary × Unary × Unary × List BitStr × List Gate) BitStr :=
  let pts := fst.comp (snd.comp (snd.comp snd))
  let nIn := fst.comp snd
  Circuit.circuitBitsProg.comp ((shoupLowerCoeffs.comp fst).pair
    ((take.comp (pts.pair nIn)).pair ((take.comp ((drop.comp (pts.pair nIn)).pair
      (fst.comp (snd.comp snd)))).pair (snd.comp (snd.comp (snd.comp snd))))))

theorem getD_eq_getElem {α : Type*} (l : List α) (d : α) {i : ℕ} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- **The evaluator computes the circuit polynomial** at a point whose coordinates are given. -/
theorem circValF_eq {m : ℕ} (C : Circuit) (hC : C.WellFormed) (hm : C.inputs + C.size = m)
    (q : Fin m → Fq t ht) (pts : List BitStr)
    (hpts : ∀ i : Fin m, pts.getD i [] = (shoupBinField t ht).toBits (q i)) :
    circValF (unary t, unary C.inputs, unary C.size, pts, C.gates) =
      (shoupBinField t ht).toBits
        (eval q (rename (Fin.cast hm) (C.finiteArith (F := Fq t ht)))) := by
  have hlen : m ≤ pts.length := by
    by_contra h
    replace h : pts.length < m := Nat.lt_of_not_le h
    cases m with
    | zero => omega
    | succ m =>
      have := hpts ⟨m, by omega⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
        Option.getD_none] at this
      have h2 := congrArg List.length this
      simp only [List.length_nil, BinField.length_toBits] at h2
      omega
  have hw : ∀ i (hi : i < m), (pts[i]'(by omega)).length = t := by
    intro i hi
    rw [← getD_eq_getElem pts [] (by omega), hpts ⟨i, hi⟩, BinField.length_toBits]
  set x := pts.take C.inputs
  set w := (pts.drop C.inputs).take C.size
  have hxl : x.length = C.inputs := by simp [x]; omega
  have hwl : w.length = C.size := by simp [w]; omega
  have hp : shoupLowerCoeffs (unary t) ≠ [] := by
    intro h
    have := shoupLowerCoeffs_length t ht
    rw [h] at this
    simp at this
    omega
  have hpl := shoupLowerCoeffs_length t ht
  have hx : ∀ b ∈ x, b.length = (shoupLowerCoeffs (unary t)).length := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    simp only [x, List.getElem_take, hpl]
    exact hw i (by simp [x] at hi; omega)
  have hw' : ∀ b ∈ w, b.length = (shoupLowerCoeffs (unary t)).length := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    simp only [w, List.getElem_take, List.getElem_drop, hpl]
    exact hw _ (by simp [w] at hi; omega)
  have hev := Circuit.evalBits_circuitBits_finite C hC (shoupRoot t ht) _ hp
    (shoupRoot_equation t ht) x w hxl hwl hx hw'
  have hfun : (Fin.addCases (fun i => evalBits (shoupRoot t ht) (x.getD i []))
      (fun j => evalBits (shoupRoot t ht) (w.getD j [])) : Fin (C.inputs + C.size) → Fq t ht) =
      q ∘ Fin.cast hm := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.addCases_left, Function.comp_apply]
      have hi : (i : ℕ) < m := by omega
      rw [show x.getD i [] = pts.getD i [] by
        simp only [x, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left i.2]]
      rw [hpts ⟨i, hi⟩, shoupRoot_eval_toBits]
      rfl
    · rw [Fin.addCases_right, Function.comp_apply]
      have hj : C.inputs + (j : ℕ) < m := by omega
      rw [show w.getD j [] = pts.getD (C.inputs + j) [] by
        simp only [w, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left j.2,
          List.getElem?_drop]]
      rw [hpts ⟨_, hj⟩, shoupRoot_eval_toBits]
      rfl
  rw [hfun, ← eval_rename] at hev
  have hl : (Circuit.circuitBits (shoupLowerCoeffs (unary t)) x w C.gates).length = t :=
    (Circuit.length_circuitBits C _ x w).trans hpl
  have hc : circValF (unary t, unary C.inputs, unary C.size, pts, C.gates) =
      Circuit.circuitBits (shoupLowerCoeffs (unary t)) x w C.gates := by
    simp only [circValF, comp_apply, pair_apply, fst_apply, snd_apply, take_apply, drop_apply,
      length_unary, Circuit.circuitBitsProg_apply, x, w]
  rw [hc]
  apply (shoupRoot_eval_eq_iff t ht _ _ hl (BinField.length_toBits _ _)).mp
  rw [hev, shoupRoot_eval_toBits]

/-! ## The input of the proof check -/

/-- The input of the proof check: the parameters, the offset `o` of the oracle's answer, `N`, the
coordinates of the point, the oracle's readable answer and the gates of the seed's circuit. -/
abbrev PrfIn : Type := ArParams × Unary × Unary × List BitStr × BitStr × List Gate

def rP : PolyTimeFun PrfIn ArParams := fst
def rO : PolyTimeFun PrfIn Unary := fst.comp snd
def rN : PolyTimeFun PrfIn Unary := fst.comp (snd.comp snd)
def rPts : PolyTimeFun PrfIn (List BitStr) := fst.comp (snd.comp (snd.comp snd))
def rA : PolyTimeFun PrfIn BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def rG : PolyTimeFun PrfIn (List Gate) := snd.comp (snd.comp (snd.comp (snd.comp snd)))

/-- `nIn`, the number of the circuits' inputs. -/
def nInF : PolyTimeFun ArParams Unary :=
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append pL (uC 1)) (ap₂ append pL (uC 1)))
    (ap₂ append oWF (uC 1))) ((AnswerReduction.ParRoutine.timesU 3).comp pR)) (uC 6)

/-- `R`, the oracle's readable count `6 + m + 2ℓ + ◇' + 3r`. -/
def rcF : PolyTimeFun ArParams Unary :=
  ap₂ append (uC 6) (ap₂ append mF (ap₂ append pL (ap₂ append pL (ap₂ append oWF
    ((AnswerReduction.ParRoutine.timesU 3).comp pR)))))

section ParamValues

variable (t j d : ℕ) (L : PcpDims) (e : Data)

theorem oWF_arParams : oWF (arParams t j d L e) = unary L.oW := by
  simp only [oWF, ap₂_apply, comp_apply, const_apply, pL_arParams, pDm_arParams,
    AnswerReduction.ParRoutine.timesU_apply, length_unary, append_unary, PcpDims.oW]

theorem nInF_arParams : nInF (arParams t j d L e) = unary L.nIn := by
  simp only [nInF, ap₂_apply, comp_apply, const_apply, pL_arParams, pR_arParams,
    oWF_arParams, AnswerReduction.ParRoutine.timesU_apply, length_unary, append_unary,
    PcpDims.nIn]

theorem mF_arParams : mF (arParams t j d L e) = unary L.m := by
  simp only [mF, ap₂_apply, comp_apply, const_apply, pL_arParams, pR_arParams, pS_arParams,
    oWF_arParams, AnswerReduction.ParRoutine.timesU_apply, length_unary, append_unary,
    PcpDims.m, PcpDims.nIn]

theorem rcF_arParams : rcF (arParams t j d L e) = unary (rSlots L).length := by
  simp only [rcF, ap₂_apply, comp_apply, const_apply, pL_arParams, pR_arParams, mF_arParams,
    oWF_arParams, AnswerReduction.ParRoutine.timesU_apply, length_unary, append_unary,
    length_rSlots]
  congr 1
  ring

end ParamValues

/-! ## Atoms -/

section Atoms

variable {J : Type} [SizedEncoding J] (ρ : PolyTimeFun J PrfIn)

/-- The field width, through `ρ`. -/
abbrev jT : PolyTimeFun J Unary := pT.comp (rP.comp ρ)
/-- The window width `ℓ`, through `ρ`. -/
abbrev jL : PolyTimeFun J Unary := pL.comp (rP.comp ρ)
/-- The index width `◇`, through `ρ`. -/
abbrev jDm : PolyTimeFun J Unary := pDm.comp (rP.comp ρ)
/-- The witness index width `r`, through `ρ`. -/
abbrev jR : PolyTimeFun J Unary := pR.comp (rP.comp ρ)
/-- `◇'`, through `ρ`. -/
abbrev jOW : PolyTimeFun J Unary := oWF.comp (rP.comp ρ)
/-- `m`, through `ρ`. -/
abbrev jM : PolyTimeFun J Unary := mF.comp (rP.comp ρ)
/-- `R`, through `ρ`. -/
abbrev jRc : PolyTimeFun J Unary := rcF.comp (rP.comp ρ)

/-- **The point's coordinate at a wire.** -/
def qAt (w : PolyTimeFun J Unary) : PolyTimeFun J BitStr :=
  (headD []).comp (drop.comp ((rPts.comp ρ).pair w))

/-- **The oracle's readable value at a position.** -/
def wAt (w : PolyTimeFun J Unary) : PolyTimeFun J BitStr :=
  windowF.comp ((jT ρ).pair ((mulU.comp (w.pair (jT ρ))).pair (rA.comp ρ)))

variable {ρ} {x : J} {j d : ℕ} {L : PcpDims} {e : Data}

theorem qAt_eq {q : Fin L.m → Fq t ht}
    (hpts : ∀ X : Fin L.m, (rPts (ρ x)).getD X [] = (shoupBinField t ht).toBits (q X))
    {w : PolyTimeFun J Unary} (X : Fin L.m) (hw : w x = unary X) :
    qAt ρ w x = (shoupBinField t ht).toBits (q X) := by
  simp only [qAt, comp_apply, pair_apply, drop_apply, hw, length_unary, headD_apply,
    headD_drop, hpts]

theorem wAt_eq (hP : rP (ρ x) = arParams t j d L e) {w : PolyTimeFun J Unary} {k : ℕ}
    (hw : w x = unary k) :
    wAt ρ w x = (shoupBinField t ht).toBits (elt t ht (rA (ρ x)) (k * t)) := by
  simp only [wAt, comp_apply, pair_apply, hP, pT_arParams, hw, mulU_apply, windowF_apply,
    toBits_elt]

/-- A readable value of the oracle's point answer is its window at the slot's position. -/
theorem vals_eq (aR : BitStr) (s : Slot L) :
    vals t ht j d L aR s = elt t ht aR (idxO s * t) := by
  simp only [vals, cw, ncoef, Nat.mul_one, Nat.add_zero]

end Atoms

/-! ## Wires and positions -/

section Index

variable {J : Type} [SizedEncoding J] (ρ : PolyTimeFun J PrfIn)

/-- A constant in unary. -/
abbrev uc (c : ℕ) : PolyTimeFun J Unary := const (unary c)

/-- `ℓ + 1`, the parity wire of the window `B`. -/
def wB0 : PolyTimeFun J Unary := ap₂ append (jL ρ) (uc 1)
/-- `ℓ + 1 + (ℓ + 1)`, the parity wire of the window `C`. -/
def wC0 : PolyTimeFun J Unary := ap₂ append (wB0 ρ) (wB0 ρ)
/-- The wire of index `i` of `O`. -/
def wVO (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (wC0 ρ) (uc 1)) i
/-- The wire of index `i` of the window `A`. -/
def wVA (i : PolyTimeFun J Unary) : PolyTimeFun J Unary := ap₂ append (uc 1) i
/-- The wire of index `i` of the window `B`. -/
def wVB (i : PolyTimeFun J Unary) : PolyTimeFun J Unary := ap₂ append (ap₂ append (wB0 ρ) (uc 1)) i
/-- The wire of index `i` of the `k`-th witness index. -/
def wVW (k : ℕ) (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (ap₂ append (wC0 ρ) (ap₂ append (jOW ρ) (uc 1)))
    ((AnswerReduction.ParRoutine.timesU k).comp (jR ρ))) i
/-- The `k`-th sign wire. -/
def wSgn (k : ℕ) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (ap₂ append (wC0 ρ) (ap₂ append (jOW ρ) (uc 1)))
    ((AnswerReduction.ParRoutine.timesU 3).comp (jR ρ))) (uc k)

/-- The position of `α_R X`. -/
def pαR (i : PolyTimeFun J Unary) : PolyTimeFun J Unary := ap₂ append (uc 6) i
/-- The position of `β_A i`. -/
def pβA (i : PolyTimeFun J Unary) : PolyTimeFun J Unary := ap₂ append (ap₂ append (uc 6) (jM ρ)) i
/-- The position of `β_B i`. -/
def pβB (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (ap₂ append (uc 6) (jM ρ)) (jL ρ)) i
/-- The position of `β_O i`. -/
def pβO (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (uc 6) (jM ρ)) (jL ρ)) (jL ρ)) i
/-- The position of `β_W k i`. -/
def pβW (k : ℕ) (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append (uc 6) (jM ρ)) (jL ρ))
    (jL ρ)) (jOW ρ)) ((AnswerReduction.ParRoutine.timesU k).comp (jR ρ))) i

variable {ρ} {x : J} {j d : ℕ} {L : PcpDims} {e : Data} (hP : rP (ρ x) = arParams t j d L e)
include hP

theorem wB0_eq : wB0 ρ x = unary (L.πB : ℕ) := by
  apply unary_ext; simp [wB0, hP]
theorem wC0_eq : wC0 ρ x = unary (L.πC : ℕ) := by
  apply unary_ext; simp [wC0, wB0_eq hP]
theorem wVO_eq {i : PolyTimeFun J Unary} (a : Fin L.oW) (hi : i x = unary a) :
    wVO ρ i x = unary (L.vO a : ℕ) := by
  apply unary_ext; simp [wVO, wC0_eq hP, hi]; omega
omit hP in
theorem wVA_eq {i : PolyTimeFun J Unary} (a : Fin L.ℓ) (hi : i x = unary a) :
    wVA i x = unary (L.vA a : ℕ) := by
  apply unary_ext; simp [wVA, hi]
theorem wVB_eq {i : PolyTimeFun J Unary} (a : Fin L.ℓ) (hi : i x = unary a) :
    wVB ρ i x = unary (L.vB a : ℕ) := by
  apply unary_ext; simp [wVB, wB0_eq hP, hi]; omega
theorem wVW_eq (k : Fin 3) {i : PolyTimeFun J Unary} (a : Fin L.r) (hi : i x = unary a) :
    wVW ρ k i x = unary (L.vW k a : ℕ) := by
  apply unary_ext
  simp [wVW, wC0_eq hP, hi, hP, oWF_arParams, AnswerReduction.ParRoutine.timesU_apply]; omega
theorem wSgn_eq (k : Fin 6) : wSgn ρ k x = unary (L.sgn k : ℕ) := by
  apply unary_ext
  simp [wSgn, wC0_eq hP, hP, oWF_arParams, AnswerReduction.ParRoutine.timesU_apply]; omega

omit hP in
theorem pαR_eq {i : PolyTimeFun J Unary} (a : Fin L.m) (hi : i x = unary a) :
    pαR i x = unary (idxO (Slot.αR a)) := by
  apply unary_ext; simp [pαR, hi, idxO_αR]
theorem pβA_eq {i : PolyTimeFun J Unary} (a : Fin L.ℓ) (hi : i x = unary a) :
    pβA ρ i x = unary (idxO (Slot.βA a)) := by
  apply unary_ext; simp [pβA, hi, hP, mF_arParams, idxO_βA]; omega
theorem pβB_eq {i : PolyTimeFun J Unary} (a : Fin L.ℓ) (hi : i x = unary a) :
    pβB ρ i x = unary (idxO (Slot.βB a)) := by
  apply unary_ext; simp [pβB, hi, hP, mF_arParams, idxO_βB]; omega
theorem pβO_eq {i : PolyTimeFun J Unary} (a : Fin L.oW) (hi : i x = unary a) :
    pβO ρ i x = unary (idxO (Slot.βO a)) := by
  apply unary_ext; simp [pβO, hi, hP, mF_arParams, idxO_βO]; omega
theorem pβW_eq (k : Fin 3) {i : PolyTimeFun J Unary} (a : Fin L.r) (hi : i x = unary a) :
    pβW ρ k i x = unary (idxO (Slot.βW k a)) := by
  apply unary_ext
  simp [pβW, hi, hP, mF_arParams, oWF_arParams, idxO_βW,
    AnswerReduction.ParRoutine.timesU_apply]; omega

end Index

/-! ## The readable checks -/

section Guard

/-- The identity of the proof check's input. -/
abbrev ι₀ : PolyTimeFun PrfIn PrfIn := PolyTimeFun.id PrfIn
/-- The input, under an index. -/
abbrev ι₁ : PolyTimeFun (Unary × PrfIn) PrfIn := snd

/-- **An assignment check** `g (1 - g) = ∑_{i < k} term i`. -/
def asgF (g : PolyTimeFun PrfIn BitStr) (term : PolyTimeFun (Unary × PrfIn) BitStr)
    (k : PolyTimeFun PrfIn Unary) : PolyTimeFun PrfIn Bool :=
  fEq (fCert (jT ι₀) g) (fSum (jT ι₀) term k)

/-- A term `x_i (1 - x_i) β_i` of an assignment check: the point's coordinate at a wire and the
readable value at a position, both of the index. -/
def termF (wire pos : PolyTimeFun (Unary × PrfIn) Unary) : PolyTimeFun (Unary × PrfIn) BitStr :=
  fMul (jT ι₁) (fCert (jT ι₁) (qAt ι₁ wire)) (wAt ι₁ pos)

/-- The assignment check of `g_A`. -/
def asgAF : PolyTimeFun PrfIn Bool :=
  asgF (wAt ι₀ (uc 0)) (termF (wVA fst) (pβA ι₁ fst)) (jL ι₀)
/-- The assignment check of `g_B`. -/
def asgBF : PolyTimeFun PrfIn Bool :=
  asgF (wAt ι₀ (uc 1)) (termF (wVB ι₁ fst) (pβB ι₁ fst)) (jL ι₀)
/-- The assignment check of `g_O`. -/
def asgOF : PolyTimeFun PrfIn Bool :=
  asgF (wAt ι₀ (uc 2)) (termF (wVO ι₁ fst) (pβO ι₁ fst)) (jOW ι₀)
/-- The assignment check of `g_{W,k}`. -/
def asgWF (k : ℕ) : PolyTimeFun PrfIn Bool :=
  asgF (wAt ι₀ (uc (3 + k))) (termF (wVW ι₁ k fst) (pβW ι₁ k fst)) (jR ι₀)

/-- The circuit polynomial at the point. -/
def circVF : PolyTimeFun PrfIn BitStr :=
  circValF.comp ((jT ι₀).pair ((nInF.comp rP).pair ((pS.comp rP).pair (rPts.pair rG))))

/-- A window literal `p_π w - p_ε`. -/
def litF (π : PolyTimeFun PrfIn Unary) (g k : ℕ) : PolyTimeFun PrfIn BitStr :=
  fAdd (fMul (jT ι₀) (qAt ι₀ π) (wAt ι₀ (uc g))) (qAt ι₀ (wSgn ι₀ k))

/-- A witness literal `w - p_ε`. -/
def witF (k : ℕ) : PolyTimeFun PrfIn BitStr := fAdd (wAt ι₀ (uc (3 + k))) (qAt ι₀ (wSgn ι₀ (3 + k)))

/-- **The formula check.** -/
def formF : PolyTimeFun PrfIn Bool :=
  fEq (fMul (jT ι₀) (fMul (jT ι₀) (fMul (jT ι₀) (fMul (jT ι₀) circVF (litF (uc 0) 0 0))
      (litF (wB0 ι₀) 1 1)) (litF (wC0 ι₀) 2 2))
      (fMul (jT ι₀) (fMul (jT ι₀) (witF 0) (witF 1)) (witF 2)))
    (fSum (jT ι₀) (termF fst (pαR fst)) (jM ι₀))

/-- **The readable checks of the proof check**, as a program. -/
def guardF : PolyTimeFun PrfIn Bool :=
  let w := andF.comp ((asgWF 0).pair (andF.comp ((asgWF 1).pair (asgWF 2))))
  andF.comp (formF.pair (andF.comp (asgAF.pair (andF.comp (asgBF.pair (andF.comp
    (asgOF.pair w)))))))

variable {j d : ℕ} {L : PcpDims} {e : Data} {inp : PrfIn}
  (hP : rP inp = arParams t j d L e) {q : Fin L.m → Fq t ht}
  (hpts : ∀ X : Fin L.m, (rPts inp).getD X [] = (shoupBinField t ht).toBits (q X))
include hP

theorem jT_ι₀ : jT ι₀ inp = unary t := by simp [hP]

omit hP in
theorem asgF_eq (hT : jT ι₀ inp = unary t) {g : PolyTimeFun PrfIn BitStr} {gv : Fq t ht}
    (hg : g inp = (shoupBinField t ht).toBits gv) {term : PolyTimeFun (Unary × PrfIn) BitStr}
    {k : PolyTimeFun PrfIn Unary} {K : ℕ} (hk : k inp = unary K) (x β : Fin K → Fq t ht)
    (hterm : ∀ i : Fin K,
      term (unary i, inp) = (shoupBinField t ht).toBits (x i * (1 - x i) * β i)) :
    asgF g term k inp = decide (gv * (1 - gv) = ∑ i, x i * (1 - x i) * β i) := by
  rw [asgF, fEq_eq (fCert_eq hT hg) (fSum_eq hT hk _ hterm)]

include hpts in
theorem termF_eq {wire pos : PolyTimeFun (Unary × PrfIn) Unary} (i : ℕ) (X : Fin L.m) (k : ℕ)
    (hw : wire (unary i, inp) = unary X) (hp : pos (unary i, inp) = unary k) :
    termF wire pos (unary i, inp) =
      (shoupBinField t ht).toBits (q X * (1 - q X) * elt t ht (rA inp) (k * t)) := by
  have hT : jT ι₁ (unary i, inp) = unary t := by simp [hP]
  exact fMul_eq hT (fCert_eq hT (qAt_eq (ρ := ι₁) (x := (unary i, inp)) hpts X hw))
    (wAt_eq (ρ := ι₁) (x := (unary i, inp)) hP hp)

theorem wAt_slot {s : Slot L} {g : ℕ} (hg : idxO s = g) :
    wAt ι₀ (uc g) inp = (shoupBinField t ht).toBits (vals t ht j d L (rA inp) s) := by
  rw [vals_eq, hg]
  exact wAt_eq (ρ := ι₀) (x := inp) hP rfl

include hpts in
theorem asgAF_eq : asgAF inp = decide (vals t ht j d L (rA inp) .gA *
    (1 - vals t ht j d L (rA inp) .gA) = ∑ i, (q ∘ L.vA) i * (1 - (q ∘ L.vA) i) *
      vals t ht j d L (rA inp) (.βA i)) :=
  asgF_eq (jT_ι₀ hP) (wAt_slot hP idxO_gA) (by simp [hP]) _ _ fun i => by
    rw [termF_eq hP hpts i (L.vA i) (idxO (Slot.βA i)) (wVA_eq i rfl) (pβA_eq (x := (unary i, inp))
      hP i rfl), vals_eq]
    rfl

include hpts in
theorem asgBF_eq : asgBF inp = decide (vals t ht j d L (rA inp) .gB *
    (1 - vals t ht j d L (rA inp) .gB) = ∑ i, (q ∘ L.vB) i * (1 - (q ∘ L.vB) i) *
      vals t ht j d L (rA inp) (.βB i)) :=
  asgF_eq (jT_ι₀ hP) (wAt_slot hP idxO_gB) (by simp [hP]) _ _ fun i => by
    rw [termF_eq hP hpts i (L.vB i) (idxO (Slot.βB i)) (wVB_eq (x := (unary i, inp)) hP i rfl)
      (pβB_eq (x := (unary i, inp)) hP i rfl), vals_eq]
    rfl

include hpts in
theorem asgOF_eq : asgOF inp = decide (vals t ht j d L (rA inp) .gO *
    (1 - vals t ht j d L (rA inp) .gO) = ∑ i, (q ∘ L.vO) i * (1 - (q ∘ L.vO) i) *
      vals t ht j d L (rA inp) (.βO i)) :=
  asgF_eq (jT_ι₀ hP) (wAt_slot hP idxO_gO) (by simp [hP, oWF_arParams]) _ _ fun i => by
    rw [termF_eq hP hpts i (L.vO i) (idxO (Slot.βO i)) (wVO_eq (x := (unary i, inp)) hP i rfl)
      (pβO_eq (x := (unary i, inp)) hP i rfl), vals_eq]
    rfl

include hpts in
theorem asgWF_eq (k : Fin 3) : asgWF k inp = decide (vals t ht j d L (rA inp) (.gW k) *
    (1 - vals t ht j d L (rA inp) (.gW k)) = ∑ i, (q ∘ L.vW k) i * (1 - (q ∘ L.vW k) i) *
      vals t ht j d L (rA inp) (.βW k i)) :=
  asgF_eq (jT_ι₀ hP) (wAt_slot hP (idxO_gW k)) (by simp [hP]) _ _ fun i => by
    rw [termF_eq hP hpts i (L.vW k i) (idxO (Slot.βW k i))
      (wVW_eq (x := (unary i, inp)) hP k i rfl) (pβW_eq (x := (unary i, inp)) hP k i rfl),
      vals_eq]
    rfl

include hpts in
theorem formF_eq (C : Circuit) (hC : C.WellFormed) (hm : C.inputs + C.size = L.m)
    (hin : C.inputs = L.nIn) (hs : C.size = L.s) (hG : rG inp = C.gates) :
    formF inp = decide (eval q (rename (Fin.cast hm) (C.finiteArith (F := Fq t ht))) *
        (q L.πA * vals t ht j d L (rA inp) .gA - q (L.sgn 0)) *
        (q L.πB * vals t ht j d L (rA inp) .gB - q (L.sgn 1)) *
        (q L.πC * vals t ht j d L (rA inp) .gO - q (L.sgn 2)) *
        ∏ k : Fin 3, (vals t ht j d L (rA inp) (.gW k) - q (L.sgn (3 + k.castLE (by omega)))) =
      ∑ X, q X * (1 - q X) * vals t ht j d L (rA inp) (.αR X)) := by
  have hT := jT_ι₀ hP
  have hc : circVF inp = (shoupBinField t ht).toBits
      (eval q (rename (Fin.cast hm) (C.finiteArith (F := Fq t ht)))) := by
    rw [← circValF_eq C hC hm q (rPts inp) hpts]
    simp only [circVF, comp_apply, pair_apply, hP, pT_arParams, nInF_arParams, pS_arParams,
      hin, hs, hG, PolyTimeFun.id_apply]
  have hq : ∀ (π : PolyTimeFun PrfIn Unary) (X : Fin L.m), π inp = unary X →
      qAt ι₀ π inp = (shoupBinField t ht).toBits (q X) := fun π X h =>
    qAt_eq (ρ := ι₀) (x := inp) hpts X h
  have hsg : ∀ k : Fin 6, qAt ι₀ (wSgn ι₀ k) inp = (shoupBinField t ht).toBits (q (L.sgn k)) :=
    fun k => hq _ _ (wSgn_eq (x := inp) hP k)
  have hl : ∀ (π : PolyTimeFun PrfIn Unary) (X : Fin L.m) (s : Slot L) (g : ℕ) (k : Fin 6),
      π inp = unary X → idxO s = g →
      litF π g k inp = (shoupBinField t ht).toBits
        (q X * vals t ht j d L (rA inp) s + q (L.sgn k)) := fun π X s g k h hg =>
    fAdd_eq (fMul_eq hT (hq π X h) (wAt_slot hP hg)) (hsg k)
  have hw : ∀ k : Fin 3, witF k inp = (shoupBinField t ht).toBits
      (vals t ht j d L (rA inp) (.gW k) + q (L.sgn ⟨3 + k, by omega⟩)) := fun k =>
    fAdd_eq (wAt_slot hP (idxO_gW k)) (hsg ⟨3 + k, by omega⟩)
  have hlhs := fMul_eq hT (fMul_eq hT (fMul_eq hT (fMul_eq hT hc
      (hl (uc 0) L.πA .gA 0 0 rfl idxO_gA)) (hl (wB0 ι₀) L.πB .gB 1 1 (wB0_eq hP) idxO_gB))
      (hl (wC0 ι₀) L.πC .gO 2 2 (wC0_eq hP) idxO_gO))
    (fMul_eq hT (fMul_eq hT (hw 0) (hw 1)) (hw 2))
  have hrhs := fSum_eq (uT := jT ι₀) (inp := inp) (f := termF fst (pαR fst)) (n := jM ι₀)
    (k := L.m) hT (by simp [hP, mF_arParams]) (fun X : Fin L.m => q X * (1 - q X) *
      vals t ht j d L (rA inp) (.αR X)) fun X => by
    rw [termF_eq hP hpts X X (idxO (Slot.αR X)) rfl (pαR_eq X rfl), vals_eq]
  rw [formF]
  refine (fEq_eq hlhs hrhs).trans ?_
  rw [Fin.prod_univ_three]
  simp only [CharTwo.sub_eq_add]
  rfl

include hpts in
/-- **The guard program decides the readable checks** of the proof check. -/
theorem guardF_eq (C : Circuit) (hC : C.WellFormed) (hm : C.inputs + C.size = L.m)
    (hin : C.inputs = L.nIn) (hs : C.size = L.s) (hG : rG inp = C.gates) :
    guardF inp = decide (PassesR (rename (Fin.cast hm) (C.finiteArith (F := Fq t ht)))
      (vals t ht j d L (rA inp)) q) := by
  have h0 : asgWF 0 inp = _ := asgWF_eq hP hpts 0
  have h1 : asgWF 1 inp = _ := asgWF_eq hP hpts 1
  have h2 : asgWF 2 inp = _ := asgWF_eq hP hpts 2
  simp only [guardF, comp_apply, pair_apply, andF_apply, formF_eq hP hpts C hC hm hin hs hG,
    asgAF_eq hP hpts, asgBF_eq hP hpts, asgOF_eq hP hpts, h0, h1, h2]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, PassesR, FormulaCheckV, AssignCheckV,
    Fin.forall_fin_succ, Function.comp_def, IsEmpty.forall_iff, and_true]
  rfl

end Guard

end MIPRE.Tailored.AnsRed.Typed

end
