/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpField
public import MIPRE.Tailored.Intro.FormProg

@[expose] public section

/-!
# The low-degree checks, as programs

Slice P4h of `planning/aldous-lyons-track.md`: the constraints of the low-degree checks of the
answer-reduced game (`Typed.ldCons`) computed by a program from the parameters, the two
questions' low-degree bits and the layout of the answers.

* `ldEqF`: the equations that two answers agree codeword by codeword (`ldEq`), each the
  difference of two windows (`ldEqF_eq`).
* `ldLineF`: the equations that the line polynomials, evaluated at a parameter, are the point
  values (`ldLine`), by Horner's rule (`ldLineF_eq`).
* `ldConsF`: the low-degree checks at two questions of one role, by the pair of types
  (`ldConsF_eq`). A question's low-degree vector is read from the last bits of its vector part
  in runs of blocks (`blocks1_ldPart`): the point, the direction, the seed. The selected
  direction of an axis-parallel line is the seed's block (`selectorProg`), the point-on-line
  guard is `memberProg`, the line parameter `parameterProg`, the introspection stage's programs.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
  MIPRE.Tailored.Intro MIPRE.Introspection.FieldLineCheck
  MIPRE.Introspection.FieldPolynomialProgram MIPRE.AnswerReduction.StageProg

variable {t : ℕ} {ht : 1 ≤ t}

/-! ## Field elements of the answer bits -/

theorem window_eq_fldAt {N : ℕ} (z : BitStr) (hz : z.length ≤ N) (o : ℕ) :
    window z o t = (shoupBinField t ht).toBits (fldAt t ht N o (Intro.bitVec N z)) := by
  rw [fldAt_bitVec z hz, toBits_elt]

theorem zeros_eq (t : ℕ) (ht : 1 ≤ t) :
    List.replicate t false = (shoupBinField t ht).toBits 0 :=
  (PauliConsUnit.toBits_zero t ht).symm

/-- `(u, v) ↦ u v` in unary. -/
abbrev mulU : PolyTimeFun (Unary × Unary) Unary := LowDegree.DegreeArithmetic.mulUnaryProg

@[simp] theorem mulU_apply (a b : ℕ) : mulU (unary a, unary b) = unary (a * b) := by
  simp [mulU, LowDegree.DegreeArithmetic.mulUnaryProg_apply, length_unary]

@[simp] theorem append_unary (a b : ℕ) : append (unary a, unary b) = unary (a + b) := by
  rw [append_apply]
  exact (List.replicate_add a b ()).symm

theorem unary_append_unary (a b : ℕ) : unary a ++ unary b = unary (a + b) :=
  (List.replicate_add a b ()).symm

/-! ## Equal codewords -/

/-- The pairs `(c, e)` with `c < k` and `e < n`, in unary, `c` major. -/
def pairsF : PolyTimeFun (Unary × Unary) (List (Unary × Unary)) :=
  flatMapR (mapR ((fst.comp snd).pair fst) (rangeU.comp (snd.comp snd))) (rangeU.comp fst)

theorem pairsF_apply (k n : ℕ) : pairsF (unary k, unary n) =
    (List.range k).flatMap fun c => (List.range n).map fun e => (unary c, unary e) := by
  simp only [pairsF, flatMapR_apply, mapR_apply, comp_apply, fst_apply, snd_apply, pair_apply,
    rangeU_apply, length_unary, List.flatMap_map, List.map_map]
  rfl

/-- The input of the equality equations: `t`, `k`, the number `n` of coefficients, `Na`, `N`. -/
abbrev EqIn : Type := Unary × Unary × Unary × Unary × Unary

/-- **The equality equations** `ldEq`, as a program: at `(c, e)`, the window of the first answer
at `(c n + e) t` plus that of the second at `Na + (c n + e) t`. -/
def ldEqF : PolyTimeFun EqIn (List BitStr) :=
  let inp : PolyTimeFun (((Unary × Unary) × EqIn) × BitStr) EqIn := snd.comp fst
  let o := mulU.comp ((ap₂ append (mulU.comp ((fst.comp (fst.comp fst)).pair
    (fst.comp (snd.comp (snd.comp inp))))) (snd.comp (fst.comp fst))).pair (fst.comp inp))
  let w (off : PolyTimeFun (((Unary × Unary) × EqIn) × BitStr) Unary) :=
    windowF.comp ((fst.comp inp).pair (off.pair snd))
  eqsConsF fst (snd.comp (snd.comp (snd.comp snd)))
    (pairsF.comp ((fst.comp snd).pair (fst.comp (snd.comp snd))))
    (xorBitsProg.comp ((w o).pair (w (ap₂ append (fst.comp (snd.comp (snd.comp (snd.comp inp))))
      o))))
    (replicate.comp ((fst.comp snd).pair (const false)))

theorem mem_pairs {k n : ℕ} {p : Unary × Unary}
    (h : p ∈ (List.range k).flatMap fun c => (List.range n).map fun e => (unary c, unary e)) :
    ∃ c e, p = (unary c, unary e) := by
  obtain ⟨c, -, he⟩ := List.mem_flatMap.1 h
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 he
  exact ⟨c, e, rfl⟩

/-- **The equality program computes `ldEq`.** -/
theorem ldEqF_eq (k n Na N : ℕ) :
    ldEqF (unary t, unary k, unary n, unary Na, unary N) = eqsCons t ht (ldEq N Na k n) := by
  have hl : ldEq N Na k n = ((List.range k).flatMap fun c => (List.range n).map fun e =>
      (unary c, unary e)).map fun p : Unary × Unary =>
        ((fldAt t ht N ((p.1.length * n + p.2.length) * t) -
          fldAt t ht N (Na + (p.1.length * n + p.2.length) * t) :
          (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht)) := by
    simp only [ldEq, List.map_flatMap, List.map_map, Function.comp_def, length_unary]
  rw [hl]
  refine eqsConsF_eq _ _ _ _ _ (t := t) (ht := ht) (N := N) rfl rfl
    (by simp only [comp_apply, pair_apply, fst_apply, snd_apply, pairsF_apply]) _ _ ?_ ?_
  · intro p hp z hz
    obtain ⟨c, e, rfl⟩ := mem_pairs hp
    simp only [comp_apply, pair_apply, fst_apply, snd_apply, ap₂_apply, mulU_apply,
      append_unary, xorBitsProg_apply, windowF_apply, length_unary]
    rw [window_eq_fldAt z hz.le, window_eq_fldAt z hz.le, shoupXorBits_correct,
      LinearMap.sub_apply, CharTwo.sub_eq_add]
  · intro p _
    simp only [comp_apply, pair_apply, fst_apply, snd_apply, replicate_apply, const_apply,
      length_unary, zeros_eq t ht]

/-! ## Line polynomials against point values -/

/-- The input of the line equations: `t`, `k`, the number `n` of coefficients, the offsets `oL`
of the line answer and `oP` of the point answer, `N`, and the parameter's bits. -/
abbrev LineIn : Type := Unary × Unary × Unary × Unary × Unary × Unary × BitStr

/-- **The line equations** `ldLine`, as a program: at `c`, Horner's evaluation at the parameter of
the `n` windows of the `c`-th line polynomial, plus the window of the `c`-th point value. -/
def ldLineF : PolyTimeFun LineIn (List BitStr) :=
  let inp : PolyTimeFun ((Unary × LineIn) × BitStr) LineIn := snd.comp fst
  let tU := fst.comp inp
  let nU := fst.comp (snd.comp (snd.comp inp))
  let oL := fst.comp (snd.comp (snd.comp (snd.comp inp)))
  let oP := fst.comp (snd.comp (snd.comp (snd.comp (snd.comp inp))))
  let α := snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp inp)))))
  let c := fst.comp fst
  -- the window of coefficient `e` of the `c`-th polynomial, with `e` first in the input
  let coefW : PolyTimeFun (Unary × ((Unary × LineIn) × BitStr)) BitStr :=
    windowF.comp ((tU.comp snd).pair ((ap₂ append (oL.comp snd)
      (mulU.comp ((ap₂ append (mulU.comp ((c.comp snd).pair (nU.comp snd))) fst).pair
        (tU.comp snd)))).pair (snd.comp snd)))
  let horner := shoupHornerProg.comp (tU.pair (α.pair (mapR coefW (rangeU.comp nU))))
  let ptW := windowF.comp (tU.pair ((ap₂ append oP (mulU.comp (c.pair tU))).pair snd))
  eqsConsF fst (fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
    (rangeU.comp (fst.comp snd)) (xorBitsProg.comp (horner.pair ptW))
    (replicate.comp ((fst.comp snd).pair (const false)))

/-- **The line program computes `ldLine`.** -/
theorem ldLineF_eq (k n oL oP N : ℕ) (α : Fq t ht) :
    ldLineF (unary t, unary k, unary n, unary oL, unary oP, unary N,
      (shoupBinField t ht).toBits α) = eqsCons t ht (ldLine N k n oL oP α) := by
  have hl : ldLine N k n oL oP α = ((List.range k).map unary).map fun c : Unary =>
      ((∑ e ∈ Finset.range n, mulL (α ^ e) ∘ₗ fldAt t ht N (oL + (c.length * n + e) * t) -
        fldAt t ht N (oP + c.length * t) :
          (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht)) := by
    simp only [ldLine, List.map_map, Function.comp_def, length_unary]
  rw [hl]
  refine eqsConsF_eq _ _ _ _ _ (t := t) (ht := ht) (N := N) rfl rfl
    (by simp only [comp_apply, fst_apply, snd_apply, rangeU_apply, length_unary]) _ _ ?_ ?_
  · intro c hc z hz
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hc
    have hcoef : (List.range n).map (fun e => window z (oL + (c * n + e) * t) t) =
        (shoupBinField t ht).vecBits
          (fun e : Fin n => fldAt t ht N (oL + (c * n + e) * t) (Intro.bitVec N z)) := by
      simp only [BinField.vecBits]
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      rw [window_eq_fldAt z hz.le]
    simp only [comp_apply, pair_apply, fst_apply, snd_apply, ap₂_apply, mulU_apply,
      append_unary, mapR_apply, rangeU_apply, length_unary, xorBitsProg_apply, windowF_apply,
      List.map_map, Function.comp_def]
    rw [hcoef, shoupHornerProg_ofFn t ht, window_eq_fldAt (ht := ht) z hz.le, shoupXorBits_correct,
      LinearMap.sub_apply, CharTwo.sub_eq_add, LinearMap.sum_apply]
    congr 2
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    exact mul_comm _ _
  · intro c _
    simp only [comp_apply, pair_apply, fst_apply, snd_apply, replicate_apply, const_apply,
      length_unary, zeros_eq t ht]

/-! ## The low-degree vector of a question -/

/-- **The low-degree bits of a typed question's vector** are its last `D j * t` bits. -/
theorem ldBitsV_ldPart {j rV : ℕ} (y : Fin (rV + D j * t) → 𝔽₂) :
    ldBitsV j t ht (ldPart t ht j rV y) = (CL.toBits y).drop rV := by
  rw [← toBits_ld j t ht, ldPart, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    CL.drop_toBits]

/-- **The runs of the low-degree bits** of a typed question: the point, the direction, the
seed. -/
theorem blocks1_ldPart {j rV : ℕ} (y : Fin (rV + D j * t) → 𝔽₂) :
    blocks1 (unary t) (unary (2 ^ j)) ((CL.toBits y).drop rV) =
      ((shoupBinField t ht).vecBits ((regs j).ptOf (ldPart t ht j rV y)),
        (shoupBinField t ht).vecBits ((regs j).dirOf (ldPart t ht j rV y)),
        [(shoupBinField t ht).toBits (ldPart t ht j rV y (regs j).coord)]) := by
  rw [← ldBitsV_ldPart, blocks1_ldBitsV]

/-- The runs of `M + M + 1` blocks of `t` bits, on `(t, M, z)`. -/
def blkF : PolyTimeFun (Unary × Unary × BitStr) Blocks :=
  let m := fst.comp snd
  let l := Introspection.BinaryBlock.splitBlocksProg.comp
    ((ap₂ append m (ap₂ append m (const (unary 1)))).pair (fst.pair (snd.comp snd)))
  (take.comp (l.pair m)).pair ((take.comp ((drop.comp (l.pair m)).pair m)).pair
    (drop.comp ((drop.comp (l.pair m)).pair m)))

theorem blkF_apply (k m : Unary) (z : BitStr) : blkF (k, m, z) = blocks1 k m z := by
  simp only [blkF, blocks1, pair_apply, comp_apply, take_apply, drop_apply, ap₂_apply,
    append_apply, const_apply, fst_apply, snd_apply,
    Introspection.BinaryBlock.splitBlocksProg_apply, List.length_append, length_unary]

/-- The direction `e_i` of an axis-parallel line, on `(t, M, i)`: `M` field elements, one at `i`,
zero elsewhere. -/
def dirAF : PolyTimeFun (Unary × Unary × ℕ) (List BitStr) :=
  let zero : PolyTimeFun (ℕ × (Unary × Unary × ℕ)) BitStr :=
    replicate.comp ((fst.comp snd).pair (const false))
  mapR (ite (ap₂ SAT.ArrayProg.eqNat fst (snd.comp (snd.comp snd))) (oneBitsProg.comp zero) zero)
    (SAT.range'P.comp ((const 0).pair (fst.comp snd)))

theorem dirAF_apply {M : ℕ} (i : Fin M) :
    dirAF (unary t, unary M, (i : ℕ)) =
      (shoupBinField t ht).vecBits (Pi.single i (1 : Fq t ht)) := by
  simp only [dirAF, mapR_apply, comp_apply, pair_apply, const_apply, SAT.range'P_apply,
    length_unary, fst_apply, snd_apply, BinField.vecBits]
  rw [← List.range_eq_range']
  apply List.ext_getElem (by simp)
  intro l h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, PolyTimeFun.ite_apply,
    ap₂_apply, SAT.ArrayProg.eqNat_apply, comp_apply, pair_apply, fst_apply, snd_apply,
    replicate_apply, const_apply, length_unary, oneBitsProg_apply]
  by_cases h : l = (i : ℕ)
  · have hl : (⟨l, by simpa using h1⟩ : Fin M) = i := Fin.ext h
    rw [ite_eq_left (decide_eq_true h), hl, Pi.single_eq_same,
      shoupBinField_oneBits t ht _ (by simp)]
  · have hl : (⟨l, by simpa using h1⟩ : Fin M) ≠ i := fun e => h (congrArg Fin.val e)
    rw [ite_eq_right (by simpa using h), Pi.single_eq_of_ne hl, zeros_eq t ht]

/-! ## The checks at two questions of one role -/

/-- The input of the low-degree checks: `t`, `j`, `M`, `d`; the number `k` of codewords, the
length `Na` of the first answer, `N`; the two questions' types and low-degree bits. -/
abbrev LdCIn : Type :=
  (Unary × Unary × Unary × Unary) × (Unary × Unary × Unary) × (LIDT.CL.Ty × BitStr) ×
    (LIDT.CL.Ty × BitStr)

section Branches

def cT : PolyTimeFun LdCIn Unary := fst.comp fst
def cJ : PolyTimeFun LdCIn Unary := fst.comp (snd.comp fst)
def cM : PolyTimeFun LdCIn Unary := fst.comp (snd.comp (snd.comp fst))
def cD : PolyTimeFun LdCIn Unary := snd.comp (snd.comp (snd.comp fst))
def cK : PolyTimeFun LdCIn Unary := fst.comp (fst.comp snd)
def cNa : PolyTimeFun LdCIn Unary := fst.comp (snd.comp (fst.comp snd))
def cN : PolyTimeFun LdCIn Unary := snd.comp (snd.comp (fst.comp snd))
def cS₁ : PolyTimeFun LdCIn LIDT.CL.Ty := fst.comp (fst.comp (snd.comp snd))
def cS₂ : PolyTimeFun LdCIn LIDT.CL.Ty := fst.comp (snd.comp (snd.comp snd))

/-- The runs of a question's low-degree bits. -/
def cBlk (i : Bool) : PolyTimeFun LdCIn Blocks :=
  blkF.comp (cT.pair (cM.pair ((if i then snd.comp (snd.comp (snd.comp snd))
    else snd.comp (fst.comp (snd.comp snd))))))

/-- A question's point. -/
def cPt (i : Bool) : PolyTimeFun LdCIn (List BitStr) := fst.comp (cBlk i)
/-- A question's raw direction. -/
def cDir (i : Bool) : PolyTimeFun LdCIn (List BitStr) := fst.comp (snd.comp (cBlk i))
/-- The selected direction of a question's axis-parallel line. -/
def cDirA (i : Bool) : PolyTimeFun LdCIn (List BitStr) :=
  dirAF.comp (cT.pair (cM.pair (Introspection.SeedProgram.selectorProg.comp (cT.pair
    (cJ.pair ((headD []).comp (snd.comp (snd.comp (cBlk i)))))))))

/-- The equality equations of `n` coefficients. -/
def eqB (n : PolyTimeFun LdCIn Unary) : PolyTimeFun LdCIn (List BitStr) :=
  ldEqF.comp (cT.pair (cK.pair (n.pair (cNa.pair cN))))

/-- The guard and the line equations of `n` coefficients, the line question `i` with direction
`dir i` against the point question `!i`. -/
def lineB (i : Bool) (dir : Bool → PolyTimeFun LdCIn (List BitStr))
    (n : PolyTimeFun LdCIn Unary) : PolyTimeFun LdCIn (List BitStr) :=
  let line := cT.pair ((cPt i).pair ((dir i).pair (cPt !i)))
  let oL := if i then cNa else const (unary 0)
  let oP := if i then const (unary 0) else cNa
  ap₂ append (guardConsF.comp ((memberProg.comp line).pair cN))
    (ldLineF.comp (cT.pair (cK.pair (n.pair (oL.pair (oP.pair (cN.pair
      (parameterProg.comp line))))))))

/-- The number of coefficients of an axis-parallel line polynomial, `d + 1`. -/
def ncA : PolyTimeFun LdCIn Unary := ap₂ append cD (const (unary 1))
/-- The number of coefficients of a diagonal line polynomial, `M d + 1`. -/
def ncD : PolyTimeFun LdCIn Unary := ap₂ append (mulU.comp (cM.pair cD)) (const (unary 1))

/-- The branch at a pair of types. -/
def ldBranch : LIDT.CL.Ty × LIDT.CL.Ty → PolyTimeFun LdCIn (List BitStr)
  | (.point, .point) => eqB (const (unary 1))
  | (.aline, .aline) => eqB ncA
  | (.dline, .dline) => eqB ncD
  | (.aline, .point) => lineB false cDirA ncA
  | (.point, .aline) => lineB true cDirA ncA
  | (.dline, .point) => lineB false cDir ncD
  | (.point, .dline) => lineB true cDir ncD
  | _ => const []

end Branches

/-- **The low-degree checks**, as a program, by the pair of types. -/
def ldConsF : PolyTimeFun LdCIn (List BitStr) := choose (cS₁.pair cS₂) ldBranch (const [])

section Correct

variable {j d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM)
  (hsel : ∀ a, ((sel.χ a : Fin (2 ^ j)) : ℕ) =
    Introspection.SeedProgram.selectorProg (unary t, unary j, (shoupBinField t ht).toBits a))
  {rV : ℕ} (k Na N : ℕ) (S₁ S₂ : LIDT.CL.Ty) (y₁ y₂ : Fin (rV + D j * t) → 𝔽₂)

/-- The input at two typed questions. -/
abbrev ldIn : LdCIn :=
  ((unary t, unary j, unary (2 ^ j), unary d), (unary k, unary Na, unary N),
    (S₁, (CL.toBits y₁).drop rV), (S₂, (CL.toBits y₂).drop rV))

include hsel in
theorem cDirA_eq (i : Bool) :
    cDirA i (ldIn (t := t) (j := j) (d := d) k Na N S₁ S₂ y₁ y₂) =
      (shoupBinField t ht).vecBits (Pi.single (LIDT.CL.chi hM
        (sel.π (ldPart t ht j rV (if i then y₂ else y₁) (regs j).coord))) (1 : Fq t ht)) := by
  rw [sel.chi_π]
  have e : cDirA i (ldIn (t := t) (j := j) (d := d) k Na N S₁ S₂ y₁ y₂) =
      dirAF (unary t, unary (2 ^ j),
        ((sel.χ (ldPart t ht j rV (if i then y₂ else y₁) (regs j).coord) : Fin (2 ^ j)) : ℕ)) := by
    rw [hsel]
    cases i <;> simp only [cDirA, cBlk, comp_apply, pair_apply, cT, cM, cJ, fst_apply, snd_apply,
      Bool.false_eq_true, ite_false, ite_true, blkF_apply, blocks1_ldPart (ht := ht),
      headD_apply, List.headD_cons]
  rw [e]
  exact dirAF_apply _

theorem cPt_eq (i : Bool) :
    cPt i (ldIn (t := t) (j := j) (d := d) k Na N S₁ S₂ y₁ y₂) =
      (shoupBinField t ht).vecBits ((regs j).ptOf (ldPart t ht j rV (if i then y₂ else y₁))) := by
  cases i <;> simp only [cPt, cBlk, comp_apply, pair_apply, cT, cM, fst_apply, snd_apply,
    Bool.false_eq_true, ite_false, ite_true, blkF_apply, blocks1_ldPart (ht := ht)]

theorem cDir_eq (i : Bool) :
    cDir i (ldIn (t := t) (j := j) (d := d) k Na N S₁ S₂ y₁ y₂) =
      (shoupBinField t ht).vecBits ((regs j).dirOf (ldPart t ht j rV (if i then y₂ else y₁))) := by
  cases i <;> simp only [cDir, cBlk, comp_apply, pair_apply, cT, cM, fst_apply, snd_apply,
    Bool.false_eq_true, ite_false, ite_true, blkF_apply, blocks1_ldPart (ht := ht)]

theorem memberProg_eq (origin direction point : Fin (2 ^ j) → Fq t ht) :
    memberProg (unary t, (shoupBinField t ht).vecBits origin,
      (shoupBinField t ht).vecBits direction, (shoupBinField t ht).vecBits point) =
      decide (∃ τ : Fq t ht, point = origin + τ • direction) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact memberProg_correct t ht origin direction point

theorem parameter_eq_lineParam (origin direction point : Fin (2 ^ j) → Fq t ht) :
    parameter origin direction point = LIDT.CL.lineParam origin direction point := by
  rw [parameter_eq]
  rfl

include hsel in
/-- **The low-degree program computes the low-degree checks** at two typed questions. -/
theorem ldConsF_eq :
    ldConsF (ldIn (t := t) (j := j) (d := d) k Na N S₁ S₂ y₁ y₂) =
      ldCons j d hM k Na N (ldQ t ht j rV sel S₁ y₁) (ldQ t ht j rV sel S₂ y₂) := by
  have hS : (cS₁.pair cS₂) (ldIn (t := t) (j := j) (d := d) k Na N S₁ S₂ y₁ y₂) = (S₁, S₂) :=
    rfl
  have hA := cDirA_eq (d := d) sel hsel k Na N S₁ S₂ y₁ y₂
  have hP := cPt_eq (ht := ht) (d := d) k Na N S₁ S₂ y₁ y₂
  have hD := cDir_eq (ht := ht) (d := d) k Na N S₁ S₂ y₁ y₂
  rw [ldConsF, choose_apply, hS]
  cases S₁ <;> cases S₂ <;>
    simp only [ldBranch, ldQ, LIDT.CL.Regs.questionOf, ldCons, eqB, lineB, ncA, ncD, comp_apply,
      pair_apply, ap₂_apply, const_apply, cT, cK, cNa, cN, cM, cD, fst_apply, snd_apply,
      mulU_apply, append_unary, ldEqF_eq (ht := ht), Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, hA, hP, hD, memberProg_eq, parameterProg_correct,
      parameter_eq_lineParam, ldLineF_eq, guardConsF_apply, length_unary] <;>
    simp only [append_apply]

end Correct

end MIPRE.Tailored.AnsRed.Typed

end
