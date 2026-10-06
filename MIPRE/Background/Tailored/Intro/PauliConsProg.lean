/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Typed
public import MIPRE.Background.Tailored.Intro.PauliConsUnit

@[expose] public section

/-!
# Programs for the Pauli clauses of the tailored introspection verifier

The `Z`-basis guard of `Typed.pauliDir` compares the kernel's projection of the readable `Z`
answer with a register of the Sample answer. `zGuardProg` decides it in polynomial time from
the kernel's parameter triple, the readable answer and the register: it runs the kernel's full
answer program (`QLD.PauliBinaryProgram.fullAnswer`), whose second output is the projection's
bits, and compares them with the register cut or padded to the same length.
`zGuardProg_eq` is its correctness at answers of the label's length.

`pauliConsProg` computes the Pauli basis test's constraints `PauliCons.pauliCons` from the
parameter triple, `Q = 2^(2^j) k` in unary (the constraints have up to `2Q + 1` bits, more than
a polynomial in the questions alone), and the two labelled question payloads. It follows the
kernel's own route (`PauliBranchProgram.route`): equal labels give the bitwise comparison
(`sameP`, `same_eq`), and rule `r` of `pairTest` gives `r1`, …, `r7`. Every check of
`pairChecks` is affine in the answer bits, so its constraint vector is its value at the unit
vectors (`PauliConsUnit`): the program runs over the unit vectors of the answer bits, decodes
each into the two answers with the kernel's parser, and evaluates the rule's expression with the
kernel's field programs (the line parameter and Horner evaluation, the low-degree table, the
trace probe, bit reads); a field equation contributes the `k` coordinates of its values
(`fieldCons`, by transposition), a bit equation its values (`boolCon`). The question-only
conditions (the point on the line, `γ(ω)`, the Magic Square incidences) are the kernel's own
programs (`memberProg`, `gammaProg`, `magicInfo`, `probeEligible`).

* `rule1`, …, `rule7`: each rule program against its `pairChecks` branch, for either orientation;
* `pauliConsProg_eq`: **the program computes `pauliCons`**, for `j ≤ k` and payloads of length
  `(3·2^j + 3) k` (the kernel's question parser is characterized there).
-/

noncomputable section

namespace MIPRE.Tailored.Intro.PauliConsProg

open Cost Cost.PolyTimeFun MIPRE.SAT MIPRE.Introspection MIPRE.QLD

/-- A bit string cut or padded with zeros to the length of a reference string. -/
def fitTo : PolyTimeFun (BitStr × BitStr) BitStr :=
  Cost.PolyTimeFun.take.comp ((append.comp (snd.pair (replicate.comp
    ((length.comp fst).pair (const false))))).pair (length.comp fst))

theorem fitTo_apply (r z : BitStr) :
    fitTo (r, z) = (z ++ List.replicate r.length false).take r.length := by
  simp [fitTo]

theorem toBits_ofBits_eq_fit (s : ℕ) (z : BitStr) :
    CL.toBits (CL.ofBits s z) = (z ++ List.replicate s false).take s := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [CL.toBits, CL.ofBits, List.getElem_ofFn, List.getElem_take,
    List.getD_eq_getElem?_getD]
  by_cases hi : i < z.length
  · simp only [List.getElem?_eq_getElem hi, List.getElem_append_left hi, Option.getD_some]
    cases z[i] <;> decide
  · simp [List.getElem?_eq_none (show z.length ≤ i by omega),
      List.getElem_append_right (show z.length ≤ i by omega)]

/-- **The `Z`-basis guard**: the projection of the readable `Z` answer is the register. -/
def zGuardProg : PolyTimeFun (PauliSamplerParameters.Parameters × BitStr × BitStr) Bool :=
  ap₂ ArrayProg.eqBits (snd.comp (PauliBinaryProgram.fullAnswer.comp (fst.pair (fst.comp snd))))
    (fitTo.comp ((snd.comp (PauliBinaryProgram.fullAnswer.comp (fst.pair (fst.comp snd)))).pair
      (snd.comp snd)))

/-- **The `Z`-basis guard is decided by `zGuardProg`**, at readable answers of the label's
length. -/
theorem zGuardProg_eq (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (aR z : BitStr)
    (ha : aR.length = pauliLen (2 ^ j) k (.pauli .Z)) :
    zGuardProg ((unary k, unary j, unary (2 ^ j)), aR, z) =
      decide (Typed.proj k hk hodd j (Typed.pDec k hk j (.pauli .Z) aR) =
        CL.ofBits (Typed.Q k j) z) := by
  have hv := (PauliCons.parser_iff_length k hk (.pauli .Z) (2 ^ j) aR).2 ha
  have hraw := DecisionKernel.Answer.rawProject_pauliDecode k hk hodd j (2 ^ j) .Z aR hv
  have hfa := PauliBinaryProgram.fullAnswer_apply (unary k) (unary j) (unary (2 ^ j)) aR
  rw [PauliFullAnswerProgram.program_raw k hk hodd (2 ^ j) .Z aR hv] at hfa
  rw [DecisionKernel.Answer.rawProject, hfa, CL.ofBits_toBits] at hraw
  simp only [zGuardProg, ap₂_apply, comp_apply, pair_apply, fst_apply, snd_apply, hfa,
    fitTo_apply, ArrayProg.eqBits_apply, CL.length_toBits]
  rw [← toBits_ofBits_eq_fit, Typed.proj, Typed.pDec, ← hraw]
  apply decide_eq_decide.2
  constructor
  · intro h
    have := congrArg (CL.ofBits (2 ^ 2 ^ j * k)) h
    simpa only [CL.ofBits_toBits] using this
  · intro h
    rw [h]

/-! ## The Pauli basis test's constraints: the programs -/

section Programs

open PauliStageProgram PauliBooleanProgram PauliBranchProgram FieldQuestionProgram
  FieldLineCheck FieldTableProgram FieldGammaProgram FieldPolynomialProgram MIPRE.LowDegree

/-- The input: parameters, `Q` in unary, and the two labelled question payloads. -/
abbrev PIn : Type := PauliSamplerParameters.Parameters × Unary × (Ty × BitStr) × (Ty × BitStr)

/-- An input and a unit vector of the answer bits. -/
abbrev PPos : Type := PIn × BitStr

def pP : PolyTimeFun PIn PauliSamplerParameters.Parameters := fst
def uK : PolyTimeFun PIn Unary := fst.comp pP
def uM : PolyTimeFun PIn Unary := snd.comp (snd.comp pP)
def uQ : PolyTimeFun PIn Unary := fst.comp snd
def tA : PolyTimeFun PIn Ty := fst.comp (fst.comp (snd.comp snd))
def xA : PolyTimeFun PIn BitStr := snd.comp (fst.comp (snd.comp snd))
def tB : PolyTimeFun PIn Ty := fst.comp (snd.comp (snd.comp snd))
def xB : PolyTimeFun PIn BitStr := snd.comp (snd.comp (snd.comp snd))

/-- The answer length of a label, `pauliLen m k T`, in unary, from `k`, `m` and `2^m k`. -/
def lenBranch : Ty → PolyTimeFun (Unary × Unary × Unary × Ty) Unary
  | .point _ => fst
  | .aline _ => append.comp (fst.pair fst)
  | .dline _ => append.comp ((PauliAnswerProgram.productUnary.comp
      ((fst.comp snd).pair fst)).pair fst)
  | .pauli _ => fst.comp (snd.comp snd)
  | .pairB _ => const (unary 1)
  | .var _ => const (unary 1)
  | .pair => const (unary 2)
  | .con _ => const (unary 3)

def lenProg : PolyTimeFun (Unary × Unary × Unary × Ty) Unary :=
  choose (snd.comp (snd.comp snd)) lenBranch (const [])

def lenA : PolyTimeFun PIn Unary := lenProg.comp (uK.pair (uM.pair (uQ.pair tA)))
def lenB : PolyTimeFun PIn Unary := lenProg.comp (uK.pair (uM.pair (uQ.pair tB)))
def lenN : PolyTimeFun PIn Unary := append.comp (lenA.pair lenB)

def fA : PolyTimeFun PIn Fields := PauliBinaryProgram.fieldsProg.comp (pP.pair xA)
def fB : PolyTimeFun PIn Fields := PauliBinaryProgram.fieldsProg.comp (pP.pair xB)
def rt : PolyTimeFun PIn Route := routeProg.comp (tA.pair tB)
def sw : PolyTimeFun PIn Bool := fst.comp (snd.comp rt)
def bas : PolyTimeFun PIn ℕ := fst.comp (snd.comp (snd.comp rt))
def lF : PolyTimeFun PIn Fields := fst.comp (orientProg.comp (sw.pair (fA.pair fB)))
def rF : PolyTimeFun PIn Fields := snd.comp (orientProg.comp (sw.pair (fA.pair fB)))
def lT : PolyTimeFun PIn Ty := fst.comp (orientProg.comp (sw.pair (tA.pair tB)))
def rT : PolyTimeFun PIn Ty := snd.comp (orientProg.comp (sw.pair (tA.pair tB)))

def ptL : PolyTimeFun PIn (List BitStr) := selectedPoint.comp (bas.pair lF)
def ptR : PolyTimeFun PIn (List BitStr) := selectedPoint.comp (bas.pair rF)
def axisR : PolyTimeFun PIn (List BitStr) := axisDirectionProg.comp (pP.pair (seed.comp rF))
def dirR : PolyTimeFun PIn (List BitStr) := direction.comp rF
def tauA : PolyTimeFun PIn BitStr := parameterProg.comp (uK.pair (ptR.pair (axisR.pair ptL)))
def tauD : PolyTimeFun PIn BitStr := parameterProg.comp (uK.pair (ptR.pair (dirR.pair ptL)))
def memA : PolyTimeFun PIn Bool := memberProg.comp (uK.pair (ptR.pair (axisR.pair ptL)))
def memD : PolyTimeFun PIn Bool := memberProg.comp (uK.pair (ptR.pair (dirR.pair ptL)))
def gamR : PolyTimeFun PIn Bool :=
  gammaProg.comp (uK.pair ((zip.comp ((pointX.comp rF).pair (pointZ.comp rF))).pair
    ((scalarX.comp rF).pair (scalarZ.comp rF))))
def scR : PolyTimeFun PIn BitStr := selectedScalar.comp (bas.pair rF)
def magic : PolyTimeFun PIn (Bool × Bool × ℕ) := (finiteFunction magicInfo).comp (lT.pair rT)
def elig : PolyTimeFun PIn Bool := (finiteFunction probeEligible).comp (lT.pair rT)

/-! ### Reading the unit vector -/

def rowsA : PolyTimeFun PPos (List BitStr) :=
  snd.comp (PauliAnswerProgram.parser.comp ((tA.comp fst).pair ((uM.comp fst).pair
    ((uK.comp fst).pair ((const (unary 1)).pair (take.comp (snd.pair (lenA.comp fst))))))))
def rowsB : PolyTimeFun PPos (List BitStr) :=
  snd.comp (PauliAnswerProgram.parser.comp ((tB.comp fst).pair ((uM.comp fst).pair
    ((uK.comp fst).pair ((const (unary 1)).pair (drop.comp (snd.pair (lenA.comp fst))))))))
def lR : PolyTimeFun PPos (List BitStr) :=
  fst.comp (orientProg.comp ((sw.comp fst).pair (rowsA.pair rowsB)))
def rR : PolyTimeFun PPos (List BitStr) :=
  snd.comp (orientProg.comp ((sw.comp fst).pair (rowsA.pair rowsB)))
def lV : PolyTimeFun PPos BitStr := (nthD [] 0).comp lR

def boolXor : PolyTimeFun (Bool × Bool) Bool := finiteFunction (fun p => xor p.1 p.2)
def bitOf (i : ℕ) (rows : PolyTimeFun PPos (List BitStr)) : PolyTimeFun PPos Bool :=
  PauliBooleanProgram.bitAt.comp ((const i).pair rows)

/-! ### The values at a unit vector -/

def v1 : PolyTimeFun PPos BitStr :=
  BinaryPolynomial.xorBitsProg.comp ((shoupHornerProg.comp ((uK.comp fst).pair
    ((tauA.comp fst).pair rR))).pair lV)
def v2 : PolyTimeFun PPos BitStr :=
  BinaryPolynomial.xorBitsProg.comp ((shoupHornerProg.comp ((uK.comp fst).pair
    ((tauD.comp fst).pair rR))).pair lV)
def v3 : PolyTimeFun PPos BitStr :=
  BinaryPolynomial.xorBitsProg.comp ((tableProg.comp ((uK.comp fst).pair
    ((ptL.comp fst).pair rR))).pair lV)
def v4 : PolyTimeFun PPos Bool :=
  boolXor.comp ((bitOf 0 lR).pair (PauliBooleanProgram.bitAt.comp ((bas.comp fst).pair rR)))
def v5 : PolyTimeFun PPos Bool :=
  boolXor.comp ((probeProg.comp ((uK.comp fst).pair (lV.pair (scR.comp fst)))).pair
    (bitOf 0 rR))
def v6a : PolyTimeFun PPos Bool :=
  parityProg.comp ((bitOf 0 lR).pair ((bitOf 1 lR).pair (bitOf 2 lR)))
def v6b : PolyTimeFun PPos Bool :=
  boolXor.comp ((PauliBooleanProgram.bitAt.comp
    ((snd.comp (snd.comp (magic.comp fst))).pair lR)).pair (bitOf 0 rR))

/-! ### Constraint vectors -/

def units : PolyTimeFun PIn (List BitStr) := BinaryLinear.identityBitsProg.comp lenN

/-- The `k` constraints of a field equation, from its values at the unit vectors. -/
def fieldCons (val : PolyTimeFun PPos BitStr) : PolyTimeFun PIn (List BitStr) :=
  (map (append.comp ((PolyTimeFun.id _).pair (const [false])))).comp
    (BinaryLinear.transposeBitsProg.comp (uK.pair
      ((mapWith (val.comp (snd.pair fst))).comp (units.pair (PolyTimeFun.id _)))))

/-- The constraint of a bit equation, from its values at the unit vectors and its target. -/
def boolCon (val : PolyTimeFun PPos Bool) (target : PolyTimeFun PIn Bool) :
    PolyTimeFun PIn BitStr :=
  append.comp (((mapWith (val.comp (snd.pair fst))).comp (units.pair (PolyTimeFun.id _))).pair
    (cons target (const [])))

def rejectP : PolyTimeFun PIn (List BitStr) :=
  cons (append.comp ((replicate.comp (lenN.pair (const false))).pair (const [true])))
    (const [])

def r1 : PolyTimeFun PIn (List BitStr) := ite memA (fieldCons v1) rejectP
def r2 : PolyTimeFun PIn (List BitStr) := ite memD (fieldCons v2) rejectP
def r3 : PolyTimeFun PIn (List BitStr) := fieldCons v3
def r4 : PolyTimeFun PIn (List BitStr) :=
  ite gamR (const []) (cons (boolCon v4 (const false)) (const []))
def r5 : PolyTimeFun PIn (List BitStr) :=
  ite gamR (const []) (cons (boolCon v5 (const false)) (const []))
def r6 : PolyTimeFun PIn (List BitStr) :=
  ite gamR (ite (fst.comp magic) (cons (boolCon v6a (fst.comp (snd.comp magic)))
    (cons (boolCon v6b (const false)) (const []))) rejectP) (const [])
def r7 : PolyTimeFun PIn (List BitStr) :=
  ite gamR (ite elig (cons (boolCon v5 (const false)) (const [])) rejectP) (const [])

def isRule (r : ℕ) : PolyTimeFun PIn Bool := ap₂ ArrayProg.eqNat (fst.comp rt) (const r)

def sameP : PolyTimeFun PIn (List BitStr) :=
  (mapWith (append.comp ((append.comp (fst.pair fst)).pair (const [false])))).comp
    ((BinaryLinear.identityBitsProg.comp lenA).pair (PolyTimeFun.id _))

/-- **The Pauli basis test's constraints, as a program.** -/
def pauliConsProg : PolyTimeFun PIn (List BitStr) :=
  ite ((finiteFunction fun p : Ty × Ty => decide (p.1 = p.2)).comp (tA.pair tB)) sameP
    (ite (isRule 1) r1 (ite (isRule 2) r2 (ite (isRule 3) r3 (ite (isRule 4) r4
      (ite (isRule 5) r5 (ite (isRule 6) r6 (ite (isRule 7) r7 (const []))))))))

end Programs

/-! ## The Pauli basis test's constraints: correctness -/

section Correct

open PauliStageProgram PauliBooleanProgram PauliBranchProgram FieldQuestionProgram
  FieldLineCheck FieldTableProgram FieldGammaProgram FieldPolynomialProgram MIPRE.LowDegree
  PauliConsUnit PauliCons PauliAnswerProgram
open PauliHideProg (unitV)

theorem range_map_eq_ofFn {α : Type*} (n : ℕ) (g : ℕ → α) :
    (List.range n).map g = List.ofFn fun p : Fin n => g p := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

variable {k : ℕ} {hk : 1 ≤ k}

/-- The unit vectors of the answer bits. -/
theorem units_eq {inp : PIn} {N : ℕ} (hN : lenN inp = unary N) :
    units inp = List.ofFn fun p : Fin N => BinaryLinear.unitBits N p := by
  simp only [units, comp_apply, hN, BinaryLinear.identityBitsProg, congr_apply, length_unary,
    BinaryLinear.identityBits, range_map_eq_ofFn]
  rfl

/-- **Field constraints from unit values.** -/
theorem fieldCons_eq {inp : PIn} {N : ℕ} (hK : uK inp = unary k) (hN : lenN inp = unary N)
    (val : PolyTimeFun PPos BitStr)
    (E : (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField k hk).carrier)
    (hval : ∀ p : Fin N, val (inp, BinaryLinear.unitBits N p) =
      (shoupBinField k hk).toBits (E (unitV p))) :
    fieldCons val inp = (fieldChecks k hk E 0).map LinCheck.toCon := by
  rw [fieldChecks_toCon, toBits_zero]
  simp only [fieldCons, comp_apply, pair_apply, id_apply, mapWith_apply, units_eq hN, hK,
    BinaryLinear.transposeBitsProg_apply, length_unary, BinaryLinear.transposeBits, map_apply,
    List.map_ofFn, Function.comp_def, snd_apply, fst_apply, hval, append_apply, const_apply,
    range_map_eq_ofFn]
  apply congrArg List.ofFn
  funext s
  simp

/-- **A bit constraint from unit values.** -/
theorem boolCon_eq {inp : PIn} {N : ℕ} (hN : lenN inp = unary N) (val : PolyTimeFun PPos Bool)
    (target : PolyTimeFun PIn Bool) (χ : LinCheck N)
    (hval : ∀ p : Fin N, val (inp, BinaryLinear.unitBits N p) =
      BinaryLinear.bit (χ.φ (unitV p)))
    (ht : target inp = BinaryLinear.bit χ.c) :
    boolCon val target inp = χ.toCon := by
  simp only [boolCon, comp_apply, pair_apply, id_apply, mapWith_apply, units_eq hN,
    List.map_ofFn, Function.comp_def, snd_apply, fst_apply, hval, append_apply, cons_apply,
    const_apply, ht]
  rfl

theorem rejectP_eq {inp : PIn} {N : ℕ} (hN : lenN inp = unary N) :
    rejectP inp = [(LinCheck.reject N).toCon] := by
  rw [LinCheck.toCon_reject]
  simp [rejectP, hN, Tailored.rejectConstraint]

/-! ### Reading the unit vectors -/

variable {M : ℕ}

theorem parser_snd_eq (T : Ty) (a : BitStr) (ha : a.length = pauliLen M k T) :
    (parser (T, unary M, unary k, unary 1, a)).2 =
      answerRows (shoupBinField k hk) (decodeBits (shoupBinField k hk) M 1 T a) := by
  obtain ⟨hn, hw, -⟩ := parser_rows_spec T M k 1 a ((parser_iff_length k hk T M a).2 ha)
  rw [decodeBits, answerRows_decodeRows (shoupBinField k hk) (shoupBinField_toBits_ofBits k hk)
    T _ hn hw]

/-- The decoded answers at a unit vector, and what the programs and the checks read of them. -/
theorem pos_facts {inp : PIn} {TA TB : Ty} {LA LB : ℕ} (hK : uK inp = unary k)
    (hM : uM inp = unary M) (hA : tA inp = TA) (hB : tB inp = TB) (hLA : lenA inp = unary LA)
    (hA' : LA = pauliLen M k TA) (hB' : LB = pauliLen M k TB) (p : Fin (LA + LB)) :
    Reads (unitV p) 0 (answerBits (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TA ((BinaryLinear.unitBits (LA + LB) p).take LA))) ∧
      Reads (unitV p) LA (answerBits (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TB ((BinaryLinear.unitBits (LA + LB) p).drop LA))) ∧
      rowsA (inp, BinaryLinear.unitBits (LA + LB) p) = answerRows (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TA ((BinaryLinear.unitBits (LA + LB) p).take LA)) ∧
      rowsB (inp, BinaryLinear.unitBits (LA + LB) p) = answerRows (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TB ((BinaryLinear.unitBits (LA + LB) p).drop LA)) := by
  set u := BinaryLinear.unitBits (LA + LB) p
  have hu : u.length = LA + LB := by simp [u, BinaryLinear.unitBits]
  have ht : (u.take LA).length = pauliLen M k TA := by simp [hu]; omega
  have hd : (u.drop LA).length = pauliLen M k TB := by simp [hu]; omega
  have hv : unitV p = bitVec (LA + LB) (u.take LA ++ u.drop LA) := by
    rw [List.take_append_drop, bitVec_unitBits]
  have hN : (u.take LA ++ u.drop LA).length ≤ LA + LB := by simp [hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [PauliHide.answerBits_decodeBits_of_length k hk M TA _ ht, hv]
    exact reads_left _ _ hN
  · rw [PauliHide.answerBits_decodeBits_of_length k hk M TB _ hd, hv]
    have := reads_right (u.take LA) (u.drop LA) hN
    rwa [List.length_take, Nat.min_eq_left (by omega)] at this
  · simp only [rowsA, comp_apply, pair_apply, fst_apply, snd_apply, const_apply, take_apply,
      hK, hM, hA, hLA, length_unary]
    exact parser_snd_eq TA _ ht
  · simp only [rowsB, comp_apply, pair_apply, fst_apply, snd_apply, const_apply, drop_apply,
      hK, hM, hB, hLA, length_unary]
    exact parser_snd_eq TB _ hd

/-- The left and right decoded answers at a unit vector (after the route's orientation). -/
abbrev dL (TA TB : Ty) (LA N : ℕ) (s : Bool) (p : Fin N) :
    QLD.Answer (shoupBinField k hk).carrier M 1 :=
  decodeBits (shoupBinField k hk) M 1 (if s then TB else TA)
    (if s then (BinaryLinear.unitBits N p).drop LA else (BinaryLinear.unitBits N p).take LA)

abbrev dR (TA TB : Ty) (LA N : ℕ) (s : Bool) (p : Fin N) :
    QLD.Answer (shoupBinField k hk).carrier M 1 :=
  decodeBits (shoupBinField k hk) M 1 (if s then TA else TB)
    (if s then (BinaryLinear.unitBits N p).take LA else (BinaryLinear.unitBits N p).drop LA)

theorem lr_facts {inp : PIn} {TA TB : Ty} {LA LB : ℕ} {s : Bool} (hK : uK inp = unary k)
    (hM : uM inp = unary M) (hA : tA inp = TA) (hB : tB inp = TB) (hLA : lenA inp = unary LA)
    (hA' : LA = pauliLen M k TA) (hB' : LB = pauliLen M k TB) (hs : sw inp = s)
    (p : Fin (LA + LB)) :
    Reads (unitV p) (if s then LA else 0) (answerBits (shoupBinField k hk)
        (dL (hk := hk) (M := M) TA TB LA _ s p)) ∧
      Reads (unitV p) (if s then 0 else LA) (answerBits (shoupBinField k hk)
        (dR (hk := hk) (M := M) TA TB LA _ s p)) ∧
      lR (inp, BinaryLinear.unitBits (LA + LB) p) =
        answerRows (shoupBinField k hk) (dL (hk := hk) (M := M) TA TB LA _ s p) ∧
      rR (inp, BinaryLinear.unitBits (LA + LB) p) =
        answerRows (shoupBinField k hk) (dR (hk := hk) (M := M) TA TB LA _ s p) := by
  obtain ⟨h1, h2, h3, h4⟩ := pos_facts (hk := hk) hK hM hA hB hLA hA' hB' p
  simp only [lR, rR, comp_apply, pair_apply, fst_apply, snd_apply, orientProg_apply, hs, dL, dR]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨h1, h2, h3, h4⟩
  · simp only [↓reduceIte]
    exact ⟨h2, h1, h4, h3⟩

/-- The facts of `lr_facts`, with the labels of the two sides named. -/
theorem lr_facts₂ {inp : PIn} {TA TB TL TR : Ty} {LA LB : ℕ} {s : Bool} (hK : uK inp = unary k)
    (hM : uM inp = unary M) (hA : tA inp = TA) (hB : tB inp = TB) (hLA : lenA inp = unary LA)
    (hA' : LA = pauliLen M k TA) (hB' : LB = pauliLen M k TB) (hs : sw inp = s)
    (hTL : (if s then TB else TA) = TL) (hTR : (if s then TA else TB) = TR) (p : Fin (LA + LB)) :
    Reads (unitV p) (if s then LA else 0) (answerBits (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TL (if s then
          (BinaryLinear.unitBits (LA + LB) p).drop LA else
            (BinaryLinear.unitBits (LA + LB) p).take LA))) ∧
      Reads (unitV p) (if s then 0 else LA) (answerBits (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TR (if s then
          (BinaryLinear.unitBits (LA + LB) p).take LA else
            (BinaryLinear.unitBits (LA + LB) p).drop LA))) ∧
      lR (inp, BinaryLinear.unitBits (LA + LB) p) = answerRows (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TL (if s then
          (BinaryLinear.unitBits (LA + LB) p).drop LA else
            (BinaryLinear.unitBits (LA + LB) p).take LA)) ∧
      rR (inp, BinaryLinear.unitBits (LA + LB) p) = answerRows (shoupBinField k hk)
        (decodeBits (shoupBinField k hk) M 1 TR (if s then
          (BinaryLinear.unitBits (LA + LB) p).take LA else
            (BinaryLinear.unitBits (LA + LB) p).drop LA)) := by
  have h := lr_facts (hk := hk) hK hM hA hB hLA hA' hB' hs p
  simp only [dL, dR, hTL, hTR] at h
  exact h

section Shapes

variable (W : Bas) (a : BitStr)

theorem dec_point : ∃ x, decodeBits (shoupBinField k hk) M 1 (.point W) a = .val x :=
  eq_val_of_fmtOk (decodeBits_format (shoupBinField k hk) (Question.point W 0) a)
theorem dec_aline : ∃ f, decodeBits (shoupBinField k hk) M 1 (.aline W) a = .apoly f :=
  eq_apoly_of_fmtOk (decodeBits_format (shoupBinField k hk) (Question.aline W 0 0) a)
theorem dec_dline : ∃ f, decodeBits (shoupBinField k hk) M 1 (.dline W) a = .dpoly f :=
  eq_dpoly_of_fmtOk (decodeBits_format (shoupBinField k hk) (Question.dline W 0 0 0) a)
theorem dec_pauli : ∃ h, decodeBits (shoupBinField k hk) M 1 (.pauli W) a = .pauliAns h :=
  eq_pauliAns_of_fmtOk (decodeBits_format (shoupBinField k hk)
    (Question.pauli W : Question (shoupBinField k hk).carrier M) a)
theorem dec_pairB : ∃ b, decodeBits (shoupBinField k hk) M 1 (.pairB W) a = .bit b :=
  eq_bit_of_fmtOk_pairB (decodeBits_format (shoupBinField k hk) (Question.pairB W ⟨0, 0, 0, 0⟩) a)
theorem dec_pair : ∃ β, decodeBits (shoupBinField k hk) M 1 .pair a = .bitPair β :=
  eq_bitPair_of_fmtOk (decodeBits_format (shoupBinField k hk) (Question.pair ⟨0, 0, 0, 0⟩) a)
theorem dec_con (i : Fin LCS.MagicSquare.layout.r) :
    ∃ α, decodeBits (shoupBinField k hk) M 1 (.con i) a = .bitTriple α :=
  eq_bitTriple_of_fmtOk (decodeBits_format (shoupBinField k hk) (Question.con i ⟨0, 0, 0, 0⟩) a)
theorem dec_var (j : Fin LCS.MagicSquare.layout.s) :
    ∃ b, decodeBits (shoupBinField k hk) M 1 (.var j) a = .bit b :=
  eq_bit_of_fmtOk_var (decodeBits_format (shoupBinField k hk) (Question.var j ⟨0, 0, 0, 0⟩) a)

end Shapes

theorem bit_add (x y : ZMod 2) :
    BinaryLinear.bit (x + y) = xor (BinaryLinear.bit x) (BinaryLinear.bit y) := by
  revert x y; decide

theorem bit_ne (x : ZMod 2) : BinaryLinear.bit x = true ↔ x ≠ 0 := by
  revert x; decide

theorem bitAt_apply (i : ℕ) (rows : List BitStr) :
    PauliBooleanProgram.bitAt (i, rows) = (rows.getD i []).getD 0 false := by
  simp [PauliBooleanProgram.bitAt]

/-! ### Rules 1 and 2: a line against a point -/

theorem xorBits_toBits (a b : (shoupBinField k hk).carrier) :
    BinaryPolynomial.xorBits ((shoupBinField k hk).toBits a) ((shoupBinField k hk).toBits b) =
      (shoupBinField k hk).toBits (a + b) := shoupXorBits_correct k hk a b

/-- The line values at the unit vectors are the line equation's. -/
theorem line_core {inp : PIn} {N n oL oR : ℕ} (hK : uK inp = unary k) (hN : lenN inp = unary N)
    (τ : (shoupBinField k hk).carrier) (val : PolyTimeFun PPos BitStr)
    (hv : ∀ u, val (inp, u) = BinaryPolynomial.xorBits
      (shoupHornerProg (unary k, (shoupBinField k hk).toBits τ, rR (inp, u))) (lV (inp, u)))
    (hp : ∀ p : Fin N, ∃ (f : Fin (n + 1) → (shoupBinField k hk).carrier)
      (a : (shoupBinField k hk).carrier),
      rR (inp, BinaryLinear.unitBits N p) = (shoupBinField k hk).vecBits f ∧
      lR (inp, BinaryLinear.unitBits N p) = [(shoupBinField k hk).toBits a] ∧
      fldAt k hk N oL (unitV p) = a ∧
        ∀ i : Fin (n + 1), fldAt k hk N (oR + i * k) (unitV p) = f i) :
    fieldCons val inp = (fieldChecks k hk ((∑ i : Fin (n + 1), LinearMap.mulRight (ZMod 2)
      (τ ^ (i : ℕ)) ∘ₗ fldAt k hk N (oR + i * k)) - fldAt k hk N oL) 0).map LinCheck.toCon := by
  refine fieldCons_eq hK hN val _ fun p => ?_
  obtain ⟨f, a, hr, hl, ha, hf⟩ := hp p
  rw [hv, hr, lV, comp_apply, hl, nthD_apply, List.getD_cons_zero, shoupHornerProg_ofFn,
    xorBits_toBits, line_value _ τ ha hf]

section Rules

variable {inp : PIn} {TA TB : Ty} {LA LB : ℕ} {s : Bool} (hK : uK inp = unary k)
  (hM : uM inp = unary M) (hA : tA inp = TA) (hB : tB inp = TB) (hLA : lenA inp = unary LA)
  (hN : lenN inp = unary (LA + LB))
  (hA' : LA = pauliLen M k TA) (hB' : LB = pauliLen M k TB) (hs : sw inp = s)
include hK hM hA hB hLA hN hA' hB' hs

/-- **Rule 1**, the axis-parallel line against a point. -/
theorem rule1 {W : Bas}
    (hTL : (if s then TB else TA) = .point W) (hTR : (if s then TA else TB) = .aline W)
    (u₀ w y : Fin M → (shoupBinField k hk).carrier)
    (htau : tauA inp = (shoupBinField k hk).toBits (LIDT.CL.lineParam u₀ w y))
    (hmem : memA inp = decide (∃ t : (shoupBinField k hk).carrier, y = u₀ + t • w)) :
    r1 inp = (lineChecks k hk (LA + LB) 1 (if s then LA else 0) (if s then 0 else LA)
      u₀ w y).map LinCheck.toCon := by
  unfold r1 lineChecks
  rw [PolyTimeFun.ite_apply, hmem]
  by_cases hl : ∃ t : (shoupBinField k hk).carrier, y = u₀ + t • w
  · rw [ite_eq_left (by simpa using hl), ite_eq_left hl]
    refine line_core hK hN _ v1 (fun u => ?_) fun p => ?_
    · simp only [v1, comp_apply, pair_apply, fst_apply, hK, htau,
        BinaryPolynomial.xorBitsProg_apply]
    · obtain ⟨h1, h2, h3, h4⟩ := lr_facts₂ (hk := hk) hK hM hA hB hLA hA' hB' hs hTL hTR p
      obtain ⟨a, ha⟩ := dec_point (hk := hk) (M := M) W _
      obtain ⟨f, hf⟩ := dec_aline (hk := hk) (M := M) W _
      rw [ha] at h1 h3
      rw [hf] at h2 h4
      exact ⟨f, a, h4, h3, read_val h1, read_apoly h2⟩
  · rw [ite_eq_right (by simpa using hl), ite_eq_right hl, rejectP_eq hN]
    simp [LinCheck.toCon_reject]

/-- **Rule 2**, the diagonal line against a point. -/
theorem rule2 {W : Bas}
    (hTL : (if s then TB else TA) = .point W) (hTR : (if s then TA else TB) = .dline W)
    (u₀ w y : Fin M → (shoupBinField k hk).carrier)
    (htau : tauD inp = (shoupBinField k hk).toBits (LIDT.CL.lineParam u₀ w y))
    (hmem : memD inp = decide (∃ t : (shoupBinField k hk).carrier, y = u₀ + t • w)) :
    r2 inp = (lineChecks k hk (LA + LB) (M * 1) (if s then LA else 0) (if s then 0 else LA)
      u₀ w y).map LinCheck.toCon := by
  unfold r2 lineChecks
  rw [PolyTimeFun.ite_apply, hmem]
  by_cases hl : ∃ t : (shoupBinField k hk).carrier, y = u₀ + t • w
  · rw [ite_eq_left (by simpa using hl), ite_eq_left hl]
    refine line_core hK hN _ v2 (fun u => ?_) fun p => ?_
    · simp only [v2, comp_apply, pair_apply, fst_apply, hK, htau,
        BinaryPolynomial.xorBitsProg_apply]
    · obtain ⟨h1, h2, h3, h4⟩ := lr_facts₂ (hk := hk) hK hM hA hB hLA hA' hB' hs hTL hTR p
      obtain ⟨a, ha⟩ := dec_point (hk := hk) (M := M) W _
      obtain ⟨f, hf⟩ := dec_dline (hk := hk) (M := M) W _
      rw [ha] at h1 h3
      rw [hf] at h2 h4
      exact ⟨f, a, h4, h3, read_val h1, read_dpoly h2⟩
  · rw [ite_eq_right (by simpa using hl), ite_eq_right hl, rejectP_eq hN]
    simp [LinCheck.toCon_reject]

/-- **Rule 3**, the point probe against the full Pauli outcome. -/
theorem rule3 {W : Bas}
    (hTL : (if s then TB else TA) = .point W) (hTR : (if s then TA else TB) = .pauli W)
    (y : Fin M → (shoupBinField k hk).carrier) (hpt : ptL inp = (shoupBinField k hk).vecBits y) :
    r3 inp = (pauliChecks k hk (LA + LB) (if s then LA else 0) (if s then 0 else LA)
      y).map LinCheck.toCon := by
  refine fieldCons_eq hK hN v3 _ fun p => ?_
  obtain ⟨h1, h2, h3, h4⟩ := lr_facts₂ (hk := hk) hK hM hA hB hLA hA' hB' hs hTL hTR p
  obtain ⟨a, ha⟩ := dec_point (hk := hk) (M := M) W _
  obtain ⟨h, hh⟩ := dec_pauli (hk := hk) (M := M) W _
  rw [ha] at h1 h3
  rw [hh] at h2 h4
  rw [pauli_value _ y (read_val h1) (read_pauliAns h2)]
  simp only [v3, comp_apply, pair_apply, fst_apply, hK, hpt, h4, lV, h3,
    BinaryPolynomial.xorBitsProg_apply, nthD_apply, answerRows, List.getD_cons_zero]
  rw [← xorBits_toBits, ← tableProg_correct k hk y h]
  simp only [BinField.vecBits, List.map_ofFn]
  rfl

/-- **Rule 4**, the commutation check. -/
theorem rule4 {W : Bas}
    (hTL : (if s then TB else TA) = .pairB W) (hTR : (if s then TA else TB) = .pair)
    (ω : Omega (shoupBinField k hk).carrier M) (hgam : gamR inp = BinaryLinear.bit (gam ω))
    (hbas : bas inp = basIdx W) :
    r4 inp = (if gam ω ≠ 0 then [] else [bitEq (LA + LB) (if s then LA else 0)
      ((if s then 0 else LA) + basIdx W)]).map LinCheck.toCon := by
  unfold r4
  rw [PolyTimeFun.ite_apply, hgam]
  by_cases hg : gam ω ≠ 0
  · rw [ite_eq_left ((bit_ne _).2 hg), ite_eq_left hg]
    rfl
  · rw [ite_eq_right (by rwa [bit_ne]), ite_eq_right hg]
    simp only [cons_apply, const_apply, List.map_cons, List.map_nil]
    congr 1
    refine boolCon_eq hN v4 _ _ (fun p => ?_) rfl
    obtain ⟨h1, h2, h3, h4⟩ := lr_facts₂ (hk := hk) hK hM hA hB hLA hA' hB' hs hTL hTR p
    obtain ⟨b, hb⟩ := dec_pairB (hk := hk) (M := M) W _
    obtain ⟨β, hβ⟩ := dec_pair (hk := hk) (M := M) _
    rw [hb] at h1 h3
    rw [hβ] at h2 h4
    rw [PauliConsUnit.bitEq_value _ (read_bit h1) (read_bitPair h2 W), bit_add]
    simp only [v4, bitOf, comp_apply, pair_apply, fst_apply, const_apply, h3, h4,
      hbas, boolXor, finiteFunction_apply, bitAt_apply, answerRows]
    cases W <;> simp [basIdx]

/-- The probe values at the unit vectors. -/
theorem prb_core {TL TR : Ty}
    (hTL : (if s then TB else TA) = TL) (hTR : (if s then TA else TB) = TR)
    (hTL' : ∀ a, ∃ x, decodeBits (shoupBinField k hk) M 1 TL a = .val x)
    (hTR' : ∀ a, ∃ b, decodeBits (shoupBinField k hk) M 1 TR a = .bit b)
    (r : (shoupBinField k hk).carrier) (hsc : scR inp = (shoupBinField k hk).toBits r) :
    boolCon v5 (const false) inp =
      (prbCheck k hk (LA + LB) r (if s then LA else 0) (if s then 0 else LA)).toCon := by
  refine boolCon_eq hN v5 _ _ (fun p => ?_) rfl
  obtain ⟨h1, h2, h3, h4⟩ := lr_facts₂ (hk := hk) hK hM hA hB hLA hA' hB' hs hTL hTR p
  obtain ⟨a, ha⟩ := hTL' (if s then
    (BinaryLinear.unitBits (LA + LB) p).drop LA else (BinaryLinear.unitBits (LA + LB) p).take LA)
  obtain ⟨b, hb⟩ := hTR' (if s then
    (BinaryLinear.unitBits (LA + LB) p).take LA else (BinaryLinear.unitBits (LA + LB) p).drop LA)
  rw [ha] at h1 h3
  rw [hb] at h2 h4
  rw [PauliConsUnit.prb_value _ r (read_val h1) (read_bit h2), bit_add]
  simp only [v5, bitOf, comp_apply, pair_apply, fst_apply, const_apply, h3, h4,
    hK, hsc, lV, boolXor, finiteFunction_apply, bitAt_apply, answerRows, nthD_apply,
    List.getD_cons_zero, PauliArithmeticProgram.probeProg_eq_prb k hk]

/-- **Rule 5**, the commutation consistency check. -/
theorem rule5 {W : Bas}
    (hTL : (if s then TB else TA) = .point W) (hTR : (if s then TA else TB) = .pairB W)
    (ω : Omega (shoupBinField k hk).carrier M) (hgam : gamR inp = BinaryLinear.bit (gam ω))
    (hsc : scR inp = (shoupBinField k hk).toBits (ω.r W)) :
    r5 inp = (if gam ω ≠ 0 then [] else [prbCheck k hk (LA + LB) (ω.r W) (if s then LA else 0)
      (if s then 0 else LA)]).map LinCheck.toCon := by
  unfold r5
  rw [PolyTimeFun.ite_apply, hgam]
  by_cases hg : gam ω ≠ 0
  · rw [ite_eq_left ((bit_ne _).2 hg), ite_eq_left hg]
    rfl
  · rw [ite_eq_right (by rwa [bit_ne]), ite_eq_right hg]
    simp only [cons_apply, const_apply, List.map_cons, List.map_nil]
    rw [prb_core hK hM hA hB hLA hN hA' hB' hs hTL hTR (dec_point W) (dec_pairB W) _ hsc]

/-- **Rule 6**, the Magic Square check. -/
theorem rule6 {i : Fin LCS.MagicSquare.layout.r} {j' : Fin LCS.MagicSquare.layout.s}
    (hTL : (if s then TB else TA) = .con i) (hTR : (if s then TA else TB) = .var j')
    (ω : Omega (shoupBinField k hk).carrier M) (hgam : gamR inp = BinaryLinear.bit (gam ω))
    (hmagic : magic inp = magicInfo (.con i, .var j')) :
    r6 inp = (conVarChecks k hk (LA + LB) i j' ω (if s then LA else 0)
      (if s then 0 else LA)).map LinCheck.toCon := by
  unfold r6 conVarChecks
  rw [PolyTimeFun.ite_apply, hgam]
  by_cases hg : gam ω = 0
  · rw [ite_eq_right (by rw [bit_ne]; simpa using hg), ite_eq_left hg]
    rfl
  · rw [ite_eq_left ((bit_ne _).2 hg), ite_eq_right hg, PolyTimeFun.ite_apply]
    simp only [comp_apply, fst_apply, hmagic, magicInfo]
    by_cases hj : j' ∈ LCS.MagicSquare.layout.V i
    · rw [ite_eq_left (by simpa using hj), ite_eq_left hj]
      simp only [cons_apply, const_apply, List.map_cons, List.map_nil]
      congr 1
      · refine boolCon_eq hN v6a _ _ (fun p => ?_) (by
          simp only [comp_apply, fst_apply, snd_apply, hmagic, magicInfo])
        obtain ⟨h1, h2, h3, h4⟩ := lr_facts₂ (hk := hk) hK hM hA hB hLA hA' hB' hs hTL hTR p
        obtain ⟨α, hα⟩ := dec_con (hk := hk) (M := M) _ i
        rw [hα] at h1 h3
        have e0 := read_bitTriple h1 0
        have e1 := read_bitTriple h1 1
        have e2 := read_bitTriple h1 2
        simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at e0 e1 e2
        simp only [LinearMap.add_apply, e0, e1, e2]
        simp only [v6a, bitOf, comp_apply, pair_apply, const_apply, h3, parityProg,
          finiteFunction_apply, bitAt_apply, answerRows]
        simp [List.ofFn_succ, BinaryLinear.ofBool_bit]
      · congr 1
        refine boolCon_eq hN v6b _ _ (fun p => ?_) rfl
        obtain ⟨h1, h2, h3, h4⟩ := lr_facts₂ (hk := hk) hK hM hA hB hLA hA' hB' hs hTL hTR p
        obtain ⟨α, hα⟩ := dec_con (hk := hk) (M := M) _ i
        obtain ⟨b, hb⟩ := dec_var (hk := hk) (M := M) _ j'
        rw [hα] at h1 h3
        rw [hb] at h2 h4
        rw [PauliConsUnit.bitEq_value _ (read_bitTriple h1 _) (read_bit h2), bit_add]
        simp only [v6b, bitOf, comp_apply, pair_apply, fst_apply, snd_apply, const_apply, h3,
          h4, hmagic, magicInfo, boolXor, finiteFunction_apply, bitAt_apply, answerRows]
        simp only [List.getD_eq_getElem?_getD, List.ofFn_succ, List.ofFn_zero]
        generalize LCS.MagicSquare.cellIdx i j' = c
        fin_cases c <;> rfl
    · rw [ite_eq_right (by simpa using hj), ite_eq_right hj, rejectP_eq hN]
      simp [LinCheck.toCon_reject]

/-- **Rule 7**, the Magic Square consistency check. -/
theorem rule7 {W : Bas} {j' : Fin LCS.MagicSquare.layout.s}
    (hTL : (if s then TB else TA) = .point W) (hTR : (if s then TA else TB) = .var j')
    (ω : Omega (shoupBinField k hk).carrier M) (hgam : gamR inp = BinaryLinear.bit (gam ω))
    (hsc : scR inp = (shoupBinField k hk).toBits (ω.r W))
    (helig : elig inp = probeEligible (.point W, .var j')) :
    r7 inp = (pointVarChecks k hk (LA + LB) W j' ω (if s then LA else 0)
      (if s then 0 else LA)).map LinCheck.toCon := by
  unfold r7 pointVarChecks
  rw [PolyTimeFun.ite_apply, hgam]
  by_cases hg : gam ω = 0
  · rw [ite_eq_right (by rw [bit_ne]; simpa using hg), ite_eq_left hg]
    rfl
  · rw [ite_eq_left ((bit_ne _).2 hg), ite_eq_right hg, PolyTimeFun.ite_apply, helig]
    have hcore := prb_core hK hM hA hB hLA hN hA' hB' hs hTL hTR (dec_point W)
      (fun a => dec_var a j') _ hsc
    cases W
    · by_cases hj : j' = LCS.MagicSquare.v 0
      · simp only [probeEligible, hj, decide_true, ↓reduceIte, true_and, cons_apply,
          const_apply, List.map_cons, List.map_nil]
        rw [hcore]
        rfl
      · simp only [probeEligible, hj, decide_false, Bool.false_eq_true, ↓reduceIte, and_false,
          reduceCtorEq, false_and, rejectP_eq hN, List.map_cons, List.map_nil,
          LinCheck.toCon_reject]
    · by_cases hj : j' = LCS.MagicSquare.v 4
      · simp only [probeEligible, hj, decide_true, ↓reduceIte, true_and, cons_apply,
          const_apply, List.map_cons, List.map_nil, reduceCtorEq, false_and]
        rw [hcore]
        rfl
      · simp only [probeEligible, hj, decide_false, Bool.false_eq_true, ↓reduceIte, and_false,
          reduceCtorEq, false_and, rejectP_eq hN, List.map_cons, List.map_nil,
          LinCheck.toCon_reject]

end Rules

/-! ### Lengths and equal labels -/

theorem lenProg_apply (k m : ℕ) (T : Ty) :
    lenProg (unary k, unary m, unary (2 ^ m * k), T) = unary (pauliLen m k T) := by
  rw [← unary_length (lenProg _)]
  congr 1
  simp only [lenProg, choose_apply, comp_apply, snd_apply]
  cases T <;> simp [lenBranch, pauliLen, PauliAnswerProgram.count, PauliAnswerProgram.width,
    PauliAnswerProgram.productUnary_length] <;> ring

theorem same_eq (L : ℕ) :
    (List.ofFn fun l : Fin L =>
      BinaryLinear.unitBits L l ++ BinaryLinear.unitBits L l ++ [false]) =
      (sameChecks (L + L) L).map LinCheck.toCon := by
  simp only [sameChecks, List.map_ofFn]
  apply congrArg List.ofFn
  funext l
  simp only [Function.comp_apply, PauliConsUnit.toCon_eq_ofFn, LinearMap.add_apply,
    PauliHideProg.getv_unitV]
  congr 1
  apply List.ext_getElem (by simp [BinaryLinear.unitBits])
  intro q h1 h2
  simp only [List.getElem_ofFn, BinaryLinear.unitBits]
  have hq : q < L + L := by simpa [BinaryLinear.unitBits] using h1
  by_cases hqL : q < L
  · rw [List.getElem_append_left (by simpa using hqL)]
    simp only [List.getElem_map, List.getElem_range]
    by_cases hl : q = l
    · have hL0 : L ≠ 0 := by omega
      simp [hl, hL0, BinaryLinear.bit]
    · have : ¬ (L + l : ℕ) = q := by omega
      simp [hl, this, BinaryLinear.bit, Ne.symm hl]
  · rw [List.getElem_append_right (by simpa using hqL)]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    have : ¬ (l : ℕ) = q := by omega
    by_cases hl : q - L = l
    · have : (L + l : ℕ) = q := by omega
      simp [BinaryLinear.bit, *]
    · have : ¬ (L + l : ℕ) = q := by omega
      simp [BinaryLinear.bit, *]

/-! ### The concrete input -/

section Main

variable (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ)

/-- The program's input at labels `t, u` and question payloads `x, y`. -/
def inputOf (t u : Ty) (x y : BitStr) : PIn :=
  ((unary k, unary j, unary (2 ^ j)), unary (2 ^ 2 ^ j * k), (t, x), (u, y))

/-- The question vector a payload decodes to. -/
abbrev qv (x : BitStr) : PauliCL.Coord (2 ^ j) → (shoupBinField k hk).carrier :=
  (PauliCL.binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
    (CL.ofBits ((3 * 2 ^ j + 3) * k) x)

theorem dispatch (inp : PIn) (h : tA inp ≠ tB inp) :
    pauliConsProg inp = if (rt inp).1 = 1 then r1 inp else if (rt inp).1 = 2 then r2 inp
      else if (rt inp).1 = 3 then r3 inp else if (rt inp).1 = 4 then r4 inp
      else if (rt inp).1 = 5 then r5 inp else if (rt inp).1 = 6 then r6 inp
      else if (rt inp).1 = 7 then r7 inp else [] := by
  simp only [pauliConsProg, PolyTimeFun.ite_apply, comp_apply, pair_apply, finiteFunction_apply,
    h, decide_false, Bool.false_eq_true, ↓reduceIte, isRule, ap₂_apply, ArrayProg.eqNat_apply,
    decide_eq_true_eq, const_apply, fst_apply]

omit [NeZero k] in
theorem pt_content (π : (shoupBinField k hk).carrier ≃ (shoupBinField k hk).carrier)
    (X : PauliCL.Coord (2 ^ j) → (shoupBinField k hk).carrier) (W : Bas) :
    (PauliCL.ExplicitSeed.contentPermutation π (PauliCL.vectorContent X)).pt W =
      fun i => X (.point W i) := by
  cases W <;> rfl

omit [NeZero k] in
theorem omega_content (π : (shoupBinField k hk).carrier ≃ (shoupBinField k hk).carrier)
    (X : PauliCL.Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    (PauliCL.ExplicitSeed.contentPermutation π (PauliCL.vectorContent X)).omega =
      (PauliCL.vectorContent X).omega := rfl

omit [NeZero k] in
theorem r_omega (X : PauliCL.Coord (2 ^ j) → (shoupBinField k hk).carrier) (W : Bas) :
    (PauliCL.vectorContent X).omega.r W = X (.scalar W) := by
  cases W <;> rfl

variable {k hk hodd j}

theorem basisIndex_eq (W : Bas) : PauliBranchProgram.basisIndex W = basIdx W := by
  cases W <;> rfl

omit [NeZero k] in
theorem memberProg_eq {m : ℕ} (o d p : Fin m → (shoupBinField k hk).carrier) :
    memberProg (unary k, (shoupBinField k hk).vecBits o, (shoupBinField k hk).vecBits d,
      (shoupBinField k hk).vecBits p) = decide (∃ t : (shoupBinField k hk).carrier,
        p = o + t • d) := by
  apply Bool.eq_iff_iff.mpr
  rw [memberProg_correct, decide_eq_true_iff]

set_option hygiene false in
/-- Reduce the constraint side at concrete labels. -/
local macro "pauli_red" : tactic => `(tactic| simp only [PauliBranchProgram.route,
  PauliBranchProgram.pairRoute, htu, ↓reduceIte, PauliBinaryProgram.questionOfBits,
  PauliCL.ExplicitSeed.decode, pairChecks, pt_content])

set_option hygiene false in
/-- Evaluate the program's question data at the concrete input. -/
local macro "pauli_data" : tactic => `(tactic| (simp only [tauA, tauD, memA, memD, gamR, scR,
  ptL, ptR, axisR, dirR, lF, rF, lT, rT, sw, bas, magic, elig, comp_apply, pair_apply, fst_apply,
  snd_apply, hK, hP, hfA, hfB, hrt, PauliBranchProgram.route, PauliBranchProgram.pairRoute, htu,
  ↓reduceIte, PauliBranchProgram.orientProg_apply, Bool.false_eq_true,
  PauliQuestionProgram.selectedPoint_fieldEncoding,
  PauliQuestionProgram.selectedScalar_fieldEncoding, PauliBooleanProgram.seed_fieldEncoding,
  PauliBooleanProgram.direction_fieldEncoding,
  PauliQuestionProgram.axisDirectionProg_legacy k hk j hj hm, parameterProg_correct,
  PauliArithmeticProgram.parameter_eq_lineParam, memberProg_eq,
  PauliQuestionProgram.gammaProg_fieldEncoding k hk, finiteFunction_apply, r_omega,
  omega_content, PolyTimeFun.zip_apply] <;> first | rfl | exact basisIndex_eq _))

set_option hygiene false in
/-- Both sides are empty: the route falls through and `pairChecks` has no branch. -/
local macro "pauli_none" : tactic => `(tactic| simp [PauliBranchProgram.route,
  PauliBranchProgram.pairRoute, htu, pairChecks, PauliBinaryProgram.questionOfBits,
  PauliCL.ExplicitSeed.decode, *])

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- **The program computes the Pauli basis test's constraints**, exactly, at question payloads of
the right length. -/
theorem pauliConsProg_eq (hj : j ≤ k) (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier)
    (t u : Ty) (x y aR bR : BitStr) (hx : x.length = (3 * 2 ^ j + 3) * k)
    (hy : y.length = (3 * 2 ^ j + 3) * k) :
    pauliConsProg (inputOf k j t u x y) = pauliCons k hk hodd j hm t u x y aR bR := by
  have hK : uK (inputOf k j t u x y) = unary k := rfl
  have hM : uM (inputOf k j t u x y) = unary (2 ^ j) := rfl
  have hA : tA (inputOf k j t u x y) = t := rfl
  have hB : tB (inputOf k j t u x y) = u := rfl
  have hLA : lenA (inputOf k j t u x y) = unary (pauliLen (2 ^ j) k t) := lenProg_apply _ _ _
  have hLB : lenB (inputOf k j t u x y) = unary (pauliLen (2 ^ j) k u) := lenProg_apply _ _ _
  have hN : lenN (inputOf k j t u x y) =
      unary (pauliLen (2 ^ j) k t + pauliLen (2 ^ j) k u) := by
    simp only [lenN, comp_apply, pair_apply, append_apply, hLA, hLB, unary, List.replicate_add]
  have hfA : fA (inputOf k j t u x y) =
      PauliCL.fieldEncoding (shoupBinField k hk) (qv k hk hodd j x) :=
    PauliBinaryProgram.fieldsProg_ofBits k hk hodd j (2 ^ j) x hx
  have hfB : fB (inputOf k j t u x y) =
      PauliCL.fieldEncoding (shoupBinField k hk) (qv k hk hodd j y) :=
    PauliBinaryProgram.fieldsProg_ofBits k hk hodd j (2 ^ j) y hy
  have hrt : rt (inputOf k j t u x y) = route t u := rfl
  have hP : pP (inputOf k j t u x y) = (unary k, unary j, unary (2 ^ j)) := rfl
  unfold pauliCons
  by_cases htu : t = u
  · subst htu
    rw [ite_eq_left rfl, ← same_eq]
    simp only [pauliConsProg, PolyTimeFun.ite_apply, comp_apply, pair_apply,
      finiteFunction_apply, hA, hB, decide_true, ↓reduceIte, sameP, mapWith_apply,
      BinaryLinear.identityBitsProg, congr_apply, hLA, length_unary, BinaryLinear.identityBits,
      range_map_eq_ofFn, List.map_ofFn]
    rfl
  · rw [ite_eq_right htu, dispatch _ (by rwa [hA, hB]), hrt]
    cases t <;> cases u
    case point.aline Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule1 (s := false) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ _ _ ?_ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case aline.point Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule1 (s := true) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ _ _ ?_ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case point.dline Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule2 (s := false) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ _ _ ?_ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case dline.point Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule2 (s := true) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ _ _ ?_ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case point.pauli Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule3 (s := false) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case pauli.point Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule3 (s := true) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case pairB.pair Wa =>
      pauli_red
      refine rule4 (s := false) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_
      all_goals pauli_data
    case pair.pairB Wb =>
      pauli_red
      refine rule4 (s := true) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_
      all_goals pauli_data
    case point.pairB Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule5 (s := false) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case pairB.point Wa Wb =>
      by_cases hW : Wa = Wb
      · subst hW
        pauli_red
        refine rule5 (s := true) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_
        all_goals pauli_data
      · have hW' := Ne.symm hW
        pauli_none
    case con.var ia jb =>
      pauli_red
      refine rule6 (s := false) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_
      all_goals pauli_data
    case var.con ja ib =>
      pauli_red
      refine rule6 (s := true) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_
      all_goals pauli_data
    case point.var Wa jb =>
      pauli_red
      refine rule7 (s := false) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_ ?_
      all_goals pauli_data
    case var.point ja Wb =>
      pauli_red
      refine rule7 (s := true) hK hM hA hB hLA hN rfl rfl ?_ rfl rfl _ ?_ ?_ ?_
      all_goals pauli_data
    all_goals pauli_none

end Main

end Correct

end MIPRE.Tailored.Intro.PauliConsProg
