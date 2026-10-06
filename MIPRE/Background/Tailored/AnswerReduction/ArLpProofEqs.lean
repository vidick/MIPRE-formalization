/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpProof

@[expose] public section

/-!
# The proof check's equations, as programs

Slice P4h of `planning/aldous-lyons-track.md`: the equations the linear values of an oracle's
point answer enter in the proof check (`Typed.proofEqs`): the system check and the three linear
assignment checks, each a field equation in the answer bits whose coefficients are read from the
point and the readable value of `g_O`. Each is computed by `fieldConsF` from a program of its
value at the answer bits (`proofEqsF_eq`); with the guard of `ArLpProof` they are the proof
check's constraints (`proofConsF_eq`).

* `zAt`: the answer bits' field element at a position of the oracle's answer.
* `pLin`, `pαL`, `pβLa`, `pβLb`, `pβL`: the positions of the linear slots, after the readable
  ones (`idxO_gLa` and the rest).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
  MIPRE.Tailored.Intro

variable {t : ℕ} {ht : 1 ≤ t}

/-! ## Positions of the linear slots and cells of an index of `O` -/

section LinIndex

variable {J : Type} [SizedEncoding J] (ρ : PolyTimeFun J PrfIn)

/-- The position `R + c` of the oracle's answer: `c` after the readable slots. -/
def pLin (c : PolyTimeFun J Unary) : PolyTimeFun J Unary := ap₂ append (jRc ρ) c

/-- `5 + ◇'`, the position of `β_{La}` after the readable slots. -/
def lB0 : PolyTimeFun J Unary := ap₂ append (uc 5) (jOW ρ)

/-- The position of `α^L_i`. -/
def pαL (i : PolyTimeFun J Unary) : PolyTimeFun J Unary := pLin ρ (ap₂ append (uc 5) i)

/-- The position of `β_{La, i}`. -/
def pβLa (i : PolyTimeFun J Unary) : PolyTimeFun J Unary := pLin ρ (ap₂ append (lB0 ρ) i)

/-- The position of `β_{Lb, i}`. -/
def pβLb (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  pLin ρ (ap₂ append (ap₂ append (lB0 ρ) (jL ρ)) i)

/-- The position of `β_{L, k, i}`. -/
def pβL (k : ℕ) (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  pLin ρ (ap₂ append (ap₂ append (ap₂ append (ap₂ append (lB0 ρ) (jL ρ)) (jL ρ))
    ((AnswerReduction.ParRoutine.timesU k).comp (jDm ρ))) i)

/-- The cell `ℓ + i` of an index of `O`: of the second linear answer. -/
def cB (i : PolyTimeFun J Unary) : PolyTimeFun J Unary := ap₂ append (jL ρ) i

/-- The cell `2ℓ + k ◇ + i` of an index of `O`: of the `k`-th copy. -/
def cL (k : ℕ) (i : PolyTimeFun J Unary) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (ap₂ append (jL ρ) (jL ρ))
    ((AnswerReduction.ParRoutine.timesU k).comp (jDm ρ))) i

/-- The cell `2ℓ + 3◇ + k` of an index of `O`: of the `k`-th sign. -/
def cSgn (k : ℕ) : PolyTimeFun J Unary :=
  ap₂ append (ap₂ append (ap₂ append (jL ρ) (jL ρ))
    ((AnswerReduction.ParRoutine.timesU 3).comp (jDm ρ))) (uc k)

variable {ρ} {x : J} {j d : ℕ} {L : PcpDims} {e : Data} (hP : rP (ρ x) = arParams t j d L e)
include hP

theorem pLin_eq {c : PolyTimeFun J Unary} {k : ℕ} (hc : c x = unary k) :
    pLin ρ c x = unary ((rSlots L).length + k) := by
  apply unary_ext; simp [pLin, hP, rcF_arParams, hc]

theorem pgLa_eq : pLin ρ (uc 0) x = unary (idxO (L := L) .gLa) := by
  rw [pLin_eq hP (k := 0) rfl, idxO_gLa, Nat.add_zero]
theorem pgLb_eq : pLin ρ (uc 1) x = unary (idxO (L := L) .gLb) := by
  rw [pLin_eq hP (k := 1) rfl, idxO_gLb]
theorem pgL_eq (k : Fin 3) : pLin ρ (uc (2 + k)) x = unary (idxO (L := L) (.gL k)) := by
  rw [pLin_eq hP (k := 2 + k) rfl, idxO_gL, Nat.add_assoc]
theorem pαL_eq {i : PolyTimeFun J Unary} (a : Fin L.oW) (hi : i x = unary a) :
    pαL ρ i x = unary (idxO (Slot.αL a)) := by
  apply unary_ext; simp [pαL, pLin, hi, hP, rcF_arParams, idxO_αL]; omega
theorem pβLa_eq {i : PolyTimeFun J Unary} (a : Fin L.ℓ) (hi : i x = unary a) :
    pβLa ρ i x = unary (idxO (Slot.βLa a)) := by
  apply unary_ext; simp [pβLa, pLin, lB0, hi, hP, rcF_arParams, oWF_arParams, idxO_βLa]; omega
theorem pβLb_eq {i : PolyTimeFun J Unary} (a : Fin L.ℓ) (hi : i x = unary a) :
    pβLb ρ i x = unary (idxO (Slot.βLb a)) := by
  apply unary_ext; simp [pβLb, pLin, lB0, hi, hP, rcF_arParams, oWF_arParams, idxO_βLb]; omega
theorem pβL_eq (k : Fin 3) {i : PolyTimeFun J Unary} (a : Fin L.dm) (hi : i x = unary a) :
    pβL ρ k i x = unary (idxO (Slot.βL k a)) := by
  apply unary_ext
  simp [pβL, pLin, lB0, hi, hP, rcF_arParams, oWF_arParams, idxO_βL,
    AnswerReduction.ParRoutine.timesU_apply]; omega

theorem cB_eq {i : PolyTimeFun J Unary} (a : Fin L.ℓ) (hi : i x = unary a) :
    cB ρ i x = unary (L.oB a : ℕ) := by
  apply unary_ext; simp [cB, hi, hP, PcpDims.oB]
theorem cL_eq (k : Fin 3) {i : PolyTimeFun J Unary} (a : Fin L.dm) (hi : i x = unary a) :
    cL ρ k i x = unary (L.oL k a : ℕ) := by
  apply unary_ext
  simp [cL, hi, hP, PcpDims.oL, AnswerReduction.ParRoutine.timesU_apply]; omega
theorem cSgn_eq (k : Fin 6) : cSgn ρ k x = unary (L.oSgn k : ℕ) := by
  apply unary_ext
  simp [cSgn, hP, PcpDims.oSgn, AnswerReduction.ParRoutine.timesU_apply]; omega

end LinIndex

/-! ## The answer bits at a position -/

section ZAt

variable {J : Type} [SizedEncoding J] (ρ : PolyTimeFun J PrfIn) (ζ : PolyTimeFun J BitStr)

/-- **The answer bits' field element at position `w` of the oracle's answer**, at its offset
`o`: the window at `o + w t`. -/
def zAt (w : PolyTimeFun J Unary) : PolyTimeFun J BitStr :=
  windowF.comp ((jT ρ).pair ((ap₂ append (rO.comp ρ) (mulU.comp (w.pair (jT ρ)))).pair ζ))

variable {ρ ζ} {x : J} {j d : ℕ} {L : PcpDims} {e : Data}

theorem zAt_eq (hP : rP (ρ x) = arParams t j d L e) {o : ℕ} (hO : rO (ρ x) = unary o)
    {w : PolyTimeFun J Unary} {k : ℕ} (hw : w x = unary k) {N : ℕ} (hz : (ζ x).length ≤ N) :
    zAt ρ ζ w x =
      (shoupBinField t ht).toBits (fldAt t ht N (o + k * t) (Intro.bitVec N (ζ x))) := by
  simp only [zAt, comp_apply, pair_apply, hP, pT_arParams, ap₂_apply, hO, hw, mulU_apply,
    append_unary, windowF_apply]
  exact window_eq_fldAt (ht := ht) _ hz _

end ZAt

/-! ## The values of the equations -/

/-- The input of an equation's value: the proof check's input and the answer bits. -/
abbrev vρ : PolyTimeFun (PrfIn × BitStr) PrfIn := fst
/-- The answer bits. -/
abbrev vζ : PolyTimeFun (PrfIn × BitStr) BitStr := snd
/-- The proof check's input, under an index. -/
abbrev tρ : PolyTimeFun (Unary × (PrfIn × BitStr)) PrfIn := fst.comp snd
/-- The answer bits, under an index. -/
abbrev tζ : PolyTimeFun (Unary × (PrfIn × BitStr)) BitStr := snd.comp snd

/-- A term `x_w (1 - x_w) v_p` of an equation: the point's coordinate at the wire of the index
and the linear value at the position of the index. -/
def eqTermF (wire pos : PolyTimeFun (Unary × (PrfIn × BitStr)) Unary) :
    PolyTimeFun (Unary × (PrfIn × BitStr)) BitStr :=
  fMul (jT tρ) (fCert (jT tρ) (qAt tρ wire)) (zAt tρ tζ pos)

/-- **The value of an assignment equation** `g (1 - g) - ∑_{i < k} x_{e_i} (1 - x_{e_i}) β_i`,
in characteristic `2` a sum. -/
def asgEqF (g : PolyTimeFun (PrfIn × BitStr) Unary)
    (term : PolyTimeFun (Unary × (PrfIn × BitStr)) BitStr)
    (k : PolyTimeFun (PrfIn × BitStr) Unary) : PolyTimeFun (PrfIn × BitStr) BitStr :=
  fAdd (fCert (jT vρ) (zAt vρ vζ g)) (fSum (jT vρ) term k)

/-- The assignment equation of `g_{La}`. -/
def asgAEqF : PolyTimeFun (PrfIn × BitStr) BitStr :=
  asgEqF (pLin vρ (uc 0)) (eqTermF (wVO tρ fst) (pβLa tρ fst)) (jL vρ)
/-- The assignment equation of `g_{Lb}`. -/
def asgBEqF : PolyTimeFun (PrfIn × BitStr) BitStr :=
  asgEqF (pLin vρ (uc 1)) (eqTermF (wVO tρ (cB tρ fst)) (pβLb tρ fst)) (jL vρ)
/-- The assignment equation of `g_{L,k}`. -/
def asgLEqF (k : ℕ) : PolyTimeFun (PrfIn × BitStr) BitStr :=
  asgEqF (pLin vρ (uc (2 + k))) (eqTermF (wVO tρ (cL tρ k fst)) (pβL tρ k fst)) (jDm vρ)

/-- `w_O x_{σ_k}`, the coefficient of a sign: the readable value of `g_O` times the point's
coordinate at the `k`-th sign of the index of `O`. -/
def sgnCoefF {J : Type} [SizedEncoding J] (ρ : PolyTimeFun J PrfIn) (k : ℕ) :
    PolyTimeFun J BitStr :=
  fMul (jT ρ) (wAt ρ (uc 2)) (qAt ρ (wVO ρ (cSgn ρ k)))

/-- **The value of the system equation**
`∑_{k < 5} w_O x_{σ_k} v_{c_k} - ∑_X x_X (1 - x_X) α^L_X`, the `c_k` being `g_{La}`, `g_{Lb}` and
the three `g_{L,k}`. -/
def sysEqF : PolyTimeFun (PrfIn × BitStr) BitStr :=
  let lin (k : ℕ) := fMul (jT vρ) (sgnCoefF vρ k) (zAt vρ vζ (pLin vρ (uc k)))
  fAdd (fAdd (fAdd (fAdd (fAdd (lin 0) (lin 1)) (lin 2)) (lin 3)) (lin 4))
    (fSum (jT vρ) (eqTermF (wVO tρ fst) (pαL tρ fst)) (jOW vρ))

/-- **The proof check's equations, as constraints**: those of the system equation, then those
of the five assignment equations. -/
def proofEqsF : PolyTimeFun PrfIn (List BitStr) :=
  let cons (val : PolyTimeFun (PrfIn × BitStr) BitStr) (κ : PolyTimeFun PrfIn BitStr) :=
    fieldConsF (jT ι₀) rN val κ
  let z := fZero (jT ι₀)
  ap₂ append (cons sysEqF (sgnCoefF ι₀ 5)) (ap₂ append (cons asgAEqF z) (ap₂ append
    (cons asgBEqF z) (ap₂ append (cons (asgLEqF 0) z) (ap₂ append (cons (asgLEqF 1) z)
      (cons (asgLEqF 2) z)))))

/-! ## Correctness -/

theorem eqsCons_cons {N : ℕ} (a : ((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht)
    (l : List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht)) :
    eqsCons t ht (a :: l) = (Intro.fieldChecks t ht a.1 a.2).map LinCheck.toCon ++
      eqsCons t ht l := by
  simp [eqsCons]

/-- The value of an assignment equation's linear map. -/
theorem asg_apply {N : ℕ} {S : Type} (v : S → (Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) (g : S)
    {n : ℕ} (c : Fin n → Fq t ht) (β : Fin n → S) (w : Fin N → ZMod 2) :
    (certLin ∘ₗ v g - ∑ i, mulL (c i) ∘ₗ v (β i)) w =
      v g w * (1 - v g w) + ∑ i, c i * v (β i) w := by
  simp [LinearMap.sub_apply, LinearMap.sum_apply, CharTwo.sub_eq_add]

section Correct

variable {j d : ℕ} {L : PcpDims} {e : Data} {inp : PrfIn} (hP : rP inp = arParams t j d L e)
  {o N : ℕ} (hO : rO inp = unary o) (hN : rN inp = unary N) {q : Fin L.m → Fq t ht}
  (hpts : ∀ X : Fin L.m, (rPts inp).getD X [] = (shoupBinField t ht).toBits (q X))
include hP hO hpts

theorem eqTermF_eq {z : BitStr} (hz : z.length ≤ N)
    {wire pos : PolyTimeFun (Unary × (PrfIn × BitStr)) Unary} (i : ℕ) (X : Fin L.m)
    (hw : wire (unary i, (inp, z)) = unary X) (s : Slot L)
    (hp : pos (unary i, (inp, z)) = unary (idxO s)) :
    eqTermF wire pos (unary i, (inp, z)) =
      (shoupBinField t ht).toBits
        (q X * (1 - q X) * fldAt t ht N (o + idxO s * t) (Intro.bitVec N z)) := by
  have hT : jT tρ (unary i, (inp, z)) = unary t := by simp [hP]
  exact fMul_eq hT (fCert_eq hT (qAt_eq (ρ := tρ) (x := (unary i, (inp, z))) hpts X hw))
    (zAt_eq (ρ := tρ) (ζ := tζ) (x := (unary i, (inp, z))) hP hO hp hz)

theorem asgEqF_eq {z : BitStr} (hz : z.length ≤ N) {g : PolyTimeFun (PrfIn × BitStr) Unary}
    (gs : Slot L) (hg : g (inp, z) = unary (idxO gs))
    {wire pos : PolyTimeFun (Unary × (PrfIn × BitStr)) Unary}
    {k : PolyTimeFun (PrfIn × BitStr) Unary} {n : ℕ} (hk : k (inp, z) = unary n)
    (we : Fin n → Fin L.m) (β : Fin n → Slot L)
    (hw : ∀ i : Fin n, wire (unary i, (inp, z)) = unary (we i))
    (hp : ∀ i : Fin n, pos (unary i, (inp, z)) = unary (idxO (β i))) :
    asgEqF g (eqTermF wire pos) k (inp, z) = (shoupBinField t ht).toBits
      ((certLin ∘ₗ fldAt t ht N (o + idxO gs * t) - ∑ i, mulL (q (we i) * (1 - q (we i))) ∘ₗ
        fldAt t ht N (o + idxO (β i) * t)) (Intro.bitVec N z)) := by
  have hT : jT vρ (inp, z) = unary t := by simp [hP]
  rw [asg_apply (fun s => fldAt t ht N (o + idxO s * t)) gs]
  exact fAdd_eq (fCert_eq hT (zAt_eq (ρ := vρ) (ζ := vζ) (x := (inp, z)) hP hO hg hz))
    (fSum_eq hT hk _ fun i => eqTermF_eq hP hO hpts hz i (we i) (hw i) (β i) (hp i))

theorem sgnCoefF_eq {J : Type} [SizedEncoding J] {ρ : PolyTimeFun J PrfIn} {x : J}
    (hx : ρ x = inp) (k : Fin 6) :
    sgnCoefF ρ k x = (shoupBinField t ht).toBits
      (vals t ht j d L (rA inp) .gO * q (L.vO (L.oSgn k))) := by
  subst hx
  have hT : jT ρ x = unary t := by simp [hP]
  refine fMul_eq hT ?_ (qAt_eq hpts _ (wVO_eq hP _ (cSgn_eq hP k)))
  rw [wAt_eq hP (k := 2) rfl, vals_eq, idxO_gO]

end Correct

section Lins

variable {L : PcpDims}

variable (L) in
/-- **The linear map of an assignment equation** at offset `o` of `N` answer bits: `g (1 - g)`
minus the sum of `x_{e_i} (1 - x_{e_i}) β_i`. -/
def asgLin (N o : ℕ) (q : Fin L.m → Fq t ht) {n : ℕ} (we : Fin n → Fin L.m) (g : Slot L)
    (β : Fin n → Slot L) : (Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht :=
  certLin ∘ₗ fldAt t ht N (o + idxO g * t) -
    ∑ i, mulL (q (we i) * (1 - q (we i))) ∘ₗ fldAt t ht N (o + idxO (β i) * t)

variable (L) in
/-- **The linear map of the system equation** at offset `o` of `N` answer bits. -/
def sysLin (N o : ℕ) (q : Fin L.m → Fq t ht) (wO : Fq t ht) :
    (Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht :=
  let v : Slot L → (Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht := fun s => fldAt t ht N (o + idxO s * t)
  let x := q ∘ L.vO
  mulL (wO * x (L.oSgn 0)) ∘ₗ v .gLa + mulL (wO * x (L.oSgn 1)) ∘ₗ v .gLb +
      ∑ k : Fin 3, mulL (wO * x (L.oSgn (2 + k.castLE (by decide)))) ∘ₗ v (.gL k) -
      ∑ X, mulL (x X * (1 - x X)) ∘ₗ v (.αL X)

/-- **The proof check's equations**, listed. -/
theorem proofEqs_eq (N o : ℕ) (wO : Fq t ht) (q : Fin L.m → Fq t ht) :
    proofEqs L N o wO q = [(sysLin L N o q wO, wO * q (L.vO (L.oSgn 5))),
      (asgLin L N o q (L.vO ∘ L.oA) .gLa Slot.βLa, 0),
      (asgLin L N o q (L.vO ∘ L.oB) .gLb Slot.βLb, 0),
      (asgLin L N o q (L.vO ∘ L.oL 0) (.gL 0) (Slot.βL 0), 0),
      (asgLin L N o q (L.vO ∘ L.oL 1) (.gL 1) (Slot.βL 1), 0),
      (asgLin L N o q (L.vO ∘ L.oL 2) (.gL 2) (Slot.βL 2), 0)] := rfl

end Lins

section Main

variable {j d : ℕ} {L : PcpDims} {e : Data} {inp : PrfIn} (hP : rP inp = arParams t j d L e)
  {o N : ℕ} (hO : rO inp = unary o) (hN : rN inp = unary N) {q : Fin L.m → Fq t ht}
  (hpts : ∀ X : Fin L.m, (rPts inp).getD X [] = (shoupBinField t ht).toBits (q X))
include hP hO hpts

/-- **The system equation's program computes its value.** -/
theorem sysEqF_eq {z : BitStr} (hz : z.length ≤ N) :
    sysEqF (inp, z) = (shoupBinField t ht).toBits
      (sysLin L N o q (vals t ht j d L (rA inp) .gO) (Intro.bitVec N z)) := by
  set wO := vals t ht j d L (rA inp) .gO
  have hT : jT vρ (inp, z) = unary t := by simp [hP]
  have hlin : ∀ (k : Fin 6) (s : Slot L), pLin vρ (uc k) (inp, z) = unary (idxO s) →
      fMul (jT vρ) (sgnCoefF vρ k) (zAt vρ vζ (pLin vρ (uc k))) (inp, z) =
        (shoupBinField t ht).toBits
          (wO * q (L.vO (L.oSgn k)) * fldAt t ht N (o + idxO s * t) (Intro.bitVec N z)) :=
    fun k s hs => fMul_eq hT (sgnCoefF_eq hP hO hpts (x := (inp, z)) rfl k)
      (zAt_eq (ρ := vρ) (ζ := vζ) (x := (inp, z)) hP hO hs hz)
  have hsum := fSum_eq hT (f := eqTermF (wVO tρ fst) (pαL tρ fst)) (n := jOW vρ)
    (k := L.oW) (by simp [hP, oWF_arParams])
    (fun X => q (L.vO X) * (1 - q (L.vO X)) * fldAt t ht N (o + idxO (Slot.αL X) * t)
      (Intro.bitVec N z))
    (fun X => eqTermF_eq hP hO hpts hz X (L.vO X)
      (wVO_eq (ρ := tρ) (x := (unary X, (inp, z))) hP X rfl) (Slot.αL X)
      (pαL_eq (ρ := tρ) (x := (unary X, (inp, z))) hP X rfl))
  have e0 : ((2 : Fin 6) + Fin.castLE (by decide) (0 : Fin 3)) = 2 := by decide
  have e1 : ((2 : Fin 6) + Fin.castLE (by decide) (1 : Fin 3)) = 3 := by decide
  have e2 : ((2 : Fin 6) + Fin.castLE (by decide) (2 : Fin 3)) = 4 := by decide
  refine (fAdd_eq (fAdd_eq (fAdd_eq (fAdd_eq (fAdd_eq (hlin 0 .gLa (pgLa_eq hP))
    (hlin 1 .gLb (pgLb_eq hP))) (hlin 2 (.gL 0) (pgL_eq hP 0))) (hlin 3 (.gL 1) (pgL_eq hP 1)))
    (hlin 4 (.gL 2) (pgL_eq hP 2))) hsum).trans ?_
  congr 1
  simp only [sysLin, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, Fin.sum_univ_three, Function.comp_apply,
    e0, e1, e2, CharTwo.sub_eq_add]
  ring

include hN in
/-- **The proof check's equations, as a program.** -/
theorem proofEqsF_eq :
    proofEqsF inp = eqsCons t ht (proofEqs L N o (vals t ht j d L (rA inp) .gO) q) := by
  have hT : jT ι₀ inp = unary t := by simp [hP]
  have hZ : fZero (jT ι₀) inp = (shoupBinField t ht).toBits 0 := fZero_eq (ht := ht) hT
  have hL : ∀ z : BitStr, jL vρ (inp, z) = unary L.ℓ := fun z => by simp [hP]
  have hD : ∀ z : BitStr, jDm vρ (inp, z) = unary L.dm := fun z => by simp [hP]
  have hAk : ∀ k : Fin 3, ∀ z : BitStr, z.length = N → asgLEqF k (inp, z) =
      (shoupBinField t ht).toBits (asgLin L N o q (L.vO ∘ L.oL k) (.gL k) (Slot.βL k)
        (Intro.bitVec N z)) := fun k z hz =>
    asgEqF_eq hP hO hpts hz.le (.gL k) (pgL_eq hP k) (hD z) (L.vO ∘ L.oL k) (Slot.βL k)
      (fun i => wVO_eq (ρ := tρ) (x := (unary i, (inp, z))) hP _
        (cL_eq (ρ := tρ) (x := (unary i, (inp, z))) hP k i rfl))
      (fun i => pβL_eq (ρ := tρ) (x := (unary i, (inp, z))) hP k i rfl)
  rw [proofEqs_eq]
  simp only [eqsCons_cons, proofEqsF, ap₂_apply, append_apply]
  have h0 : eqsCons t ht ([] : List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht)) = [] :=
    rfl
  rw [h0, List.append_nil]
  congr 1
  · exact fieldConsF_eq _ _ _ _ hT hN _ _ (fun z hz => sysEqF_eq hP hO hpts hz.le)
      (sgnCoefF_eq hP hO hpts (x := inp) rfl 5)
  congr 1
  · exact fieldConsF_eq _ _ _ _ hT hN _ _ (fun z hz => asgEqF_eq hP hO hpts hz.le .gLa
      (pgLa_eq hP) (hL z) (L.vO ∘ L.oA) Slot.βLa
      (fun i => wVO_eq (ρ := tρ) (x := (unary i, (inp, z))) hP (L.oA i) rfl)
      (fun i => pβLa_eq (ρ := tρ) (x := (unary i, (inp, z))) hP i rfl)) hZ
  congr 1
  · exact fieldConsF_eq _ _ _ _ hT hN _ _ (fun z hz => asgEqF_eq hP hO hpts hz.le .gLb
      (pgLb_eq hP) (hL z) (L.vO ∘ L.oB) Slot.βLb
      (fun i => wVO_eq (ρ := tρ) (x := (unary i, (inp, z))) hP _
        (cB_eq (ρ := tρ) (x := (unary i, (inp, z))) hP i rfl))
      (fun i => pβLb_eq (ρ := tρ) (x := (unary i, (inp, z))) hP i rfl)) hZ
  congr 1
  · exact fieldConsF_eq _ _ _ _ hT hN _ _ (hAk 0) hZ
  congr 1
  · exact fieldConsF_eq _ _ _ _ hT hN _ _ (hAk 1) hZ
  · exact fieldConsF_eq _ _ _ _ hT hN _ _ (hAk 2) hZ

/-- **The proof check, as a program**: the readable checks as a guard, then the equations. -/
def proofConsF : PolyTimeFun PrfIn (List BitStr) :=
  ap₂ append (guardConsF.comp (guardF.pair rN)) proofEqsF

include hN in
/-- **The proof check's program computes `proofCons`**, at the oracle's point answer at offset `o`
of `N` answer bits, for a well-formed circuit with the PCP's numbers of inputs and gates. -/
theorem proofConsF_eq (C : Circuit) (hC : C.WellFormed) (hm : C.inputs + C.size = L.m)
    (hin : C.inputs = L.nIn) (hs : C.size = L.s) (hG : rG inp = C.gates) {hLM : L.m ≤ 2 ^ j}
    {p : Fin (2 ^ j) → Fq t ht} (hq : ptm L hLM p = q) :
    proofConsF inp = proofCons j d L hLM N o
      (MvPolynomial.rename (Fin.cast hm) (C.finiteArith (F := Fq t ht))) p (rA inp) := by
  subst hq
  simp only [proofConsF, ap₂_apply, append_apply, comp_apply, pair_apply, guardConsF_apply, hN,
    length_unary, proofCons]
  rw [guardF_eq hP hpts C hC hm hin hs hG, proofEqsF_eq hP hO hN hpts]

end Main

end MIPRE.Tailored.AnsRed.Typed

end
