/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.DecideSpec
import MIPRE.Foundations.SAT.PcpFormat
import MIPRE.Foundations.Cost.FiniteChoice
import MIPRE.Foundations.OracularDecider

/-!
# The answer-reduced decision, as a program

Piece AR-3e of `planning/answer-reduction.md`: polynomial-time functions computing the decision on
blocks of `MIPRE/Background/AnswerReduction/DecideSpec`, each with the law that it computes its
specification (`verdictP_apply` for the whole). The type-dependent control is a finite table of
the type pair (`PolyTimeFun.finiteFunction`); the field arithmetic is the introspection stage
programs'.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun StageProg Pcp Introspection.FieldLineCheck
  Introspection.FieldQuestionProgram Introspection.SeededLineProgram Introspection.LineProgram
  CL.Detyping.Program

/-! ## Cutting a list into runs -/

private def chunkStep :
    PolyTimeFun ((List BitStr × List (List BitStr)) × Unary) (List BitStr × List (List BitStr)) :=
  (drop.comp ((fst.comp fst).pair snd)).pair
    (cons (take.comp ((fst.comp fst).pair snd)) (snd.comp fst))

private theorem chunkStep_apply (v : List BitStr) (vs : List (List BitStr)) (w : Unary) :
    chunkStep ((v, vs), w) = (v.drop w.length, v.take w.length :: vs) := rfl

private theorem chunkStep_fold (n : ℕ) (w : Unary) (v : List BitStr) (vs : List (List BitStr)) :
    ((List.replicate n w).foldl chunkStep.step (v, vs)).2 =
      (chunks w.length n v).reverse ++ vs := by
  induction n generalizing v vs with
  | zero => simp [chunks]
  | succ n ih =>
    change ((List.replicate n w).foldl chunkStep.step
      (v.drop w.length, v.take w.length :: vs)).2 = _
    rw [ih]
    simp [chunks, List.append_assoc]

/-- **Cutting into runs**, as a program: `(n, w, l) ↦ chunks w n l`. -/
def chunksProg : PolyTimeFun (Unary × Unary × List BitStr) (List (List BitStr)) :=
  let scan := foldlAdd chunkStep 2 (by
    rintro ⟨v, vs⟩ w
    have he := esize_list_append (v.take w.length) (v.drop w.length)
    rw [List.take_append_drop] at he
    simp only [chunkStep_apply, esize_prod, esize_list_cons, Polynomial.eval_ofNat]
    omega)
  congr ((PolyTimeFun.reverse.comp snd).comp (scan.comp
    ((replicate.comp (fst.pair (fst.comp snd))).pair ((snd.comp snd).pair (const [])))))
    (fun p => chunks p.2.1.length p.1.length p.2.2) (by
      rintro ⟨n, w, v⟩
      change (((List.replicate n.length w).foldl chunkStep.step (v, [])).2).reverse = _
      rw [chunkStep_fold, List.append_nil, List.reverse_reverse])

@[simp] theorem chunksProg_apply (n w : Unary) (l : List BitStr) :
    chunksProg (n, w, l) = chunks w.length n.length l := rfl

/-! ## Reading a finite type -/

section Finite

variable {α : Type*} [SizedEncoding α] [Inhabited α]

/-- Reading a value among a list of candidates, by comparing encodings; the default otherwise. -/
def decodeAmong : List α → PolyTimeFun Data α
  | [] => const default
  | a :: as => ite (ap₂ treeEq (PolyTimeFun.id Data) (const (encode a))) (const a) (decodeAmong as)

theorem decodeAmong_encode (l : List α) (a : α) (h : a ∈ l) : decodeAmong l (encode a) = a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [decodeAmong, PolyTimeFun.ite_apply, ap₂_apply, treeEq_apply, id_apply, const_apply]
    by_cases hb : a = b
    · subst hb; simp
    · have : (encode a : Data) ≠ encode b := fun he => hb (encode_injective he)
      simp only [this, decide_false, Bool.false_eq_true, if_false]
      exact ih ((List.mem_cons.mp h).resolve_left hb)

variable [Fintype α]

/-- **Reading a value of a finite type** off any datum. -/
def readFinite : PolyTimeFun Data α := decodeAmong Finset.univ.toList

@[simp] theorem readFinite_encode (a : α) : (readFinite : PolyTimeFun Data α) (encode a) = a :=
  decodeAmong_encode _ a (by simp)

end Finite

/-! ## The line-versus-point check -/

/-- The line, the point, the polynomials and the values. -/
abbrev LvpIn := (Unary × List BitStr × List BitStr × List BitStr) × List (List BitStr) × List BitStr

/-- `lvpB`, as a program. -/
def lvpBP : PolyTimeFun LvpIn Bool :=
  let item : PolyTimeFun ((List BitStr × BitStr) × (Unary × List BitStr × List BitStr ×
      List BitStr)) Bool := lineCheckProg.comp (snd.pair ((fst.comp fst).pair (snd.comp fst)))
  SAT.allBoolProg.comp ((mapWith item).comp ((zip.comp snd).pair fst))

@[simp] theorem lvpBP_apply (kU : Unary) (base dir pt : List BitStr) (polys : List (List BitStr))
    (vals : List BitStr) : lvpBP ((kU, base, dir, pt), polys, vals) = lvpB kU base dir pt polys vals := by
  simp only [lvpBP, comp_apply, pair_apply, fst_apply, snd_apply, mapWith_apply, zip_apply,
    SAT.allBoolProg_apply, lvpB, List.all_map]
  rfl

/-! ## The low-degree subtest of a copy -/

/-- Width, copy, test type, the two runs of blocks, polynomials and values. -/
abbrev LdIn := Unary × Desc × ℕ × Blocks × Blocks × List (List BitStr) × List BitStr

section Ld

def kL : PolyTimeFun LdIn Unary := fst
def dL : PolyTimeFun LdIn Desc := fst.comp snd
def τL : PolyTimeFun LdIn ℕ := fst.comp (snd.comp snd)
def xL : PolyTimeFun LdIn Blocks := fst.comp (snd.comp (snd.comp snd))
def yL : PolyTimeFun LdIn Blocks := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def polysL : PolyTimeFun LdIn (List (List BitStr)) :=
  fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
def valsL : PolyTimeFun LdIn (List BitStr) :=
  snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))

def oL : PolyTimeFun LdIn Unary := fst.comp dL
def szL : PolyTimeFun LdIn Unary := fst.comp (snd.comp dL)
def jwL : PolyTimeFun LdIn Unary := fst.comp (snd.comp (snd.comp dL))
def cL : PolyTimeFun LdIn Unary := snd.comp (snd.comp (snd.comp dL))

def sliceLd (l : PolyTimeFun LdIn (List BitStr)) : PolyTimeFun LdIn (List BitStr) :=
  sliceP.comp (oL.pair (szL.pair l))

def seedLd : PolyTimeFun LdIn BitStr :=
  (headD []).comp (drop.comp ((snd.comp (snd.comp yL)).pair cL))

def isτL (t : ℕ) : PolyTimeFun LdIn Bool := ap₂ SAT.ArrayProg.eqNat τL (const t)

def dirLd : PolyTimeFun LdIn (List BitStr) :=
  ite (isτL 1) (axisDirectionProg.comp ((kL.pair (jwL.pair szL)).pair seedLd))
    (selectedDirectionProg.comp ((kL.pair (jwL.pair seedLd)).pair
      (sliceLd (fst.comp (snd.comp yL)))))

def baseLd : PolyTimeFun LdIn (List BitStr) :=
  ite (isτL 1) (axisRepresentativeProg.comp ((kL.pair (jwL.pair seedLd)).pair
      (sliceLd (fst.comp yL))))
    (ite (isτL 2) (lineRepresentativeProg.comp (kL.pair ((sliceLd (fst.comp yL)).pair dirLd)))
      (sliceLd (fst.comp yL)))

/-- `ldB`, as a program. -/
def ldBP : PolyTimeFun LdIn Bool :=
  lvpBP.comp ((kL.pair (baseLd.pair (dirLd.pair (sliceLd (fst.comp xL))))).pair
    (polysL.pair valsL))

@[simp] theorem ldBP_apply (kU : Unary) (d : Desc) (τ : ℕ) (X Y : Blocks)
    (polys : List (List BitStr)) (vals : List BitStr) :
    ldBP (kU, d, τ, X, Y, polys, vals) = ldB kU d τ X Y polys vals := by
  simp only [ldBP, comp_apply, pair_apply, lvpBP_apply, ldB, kL, polysL, valsL, fst_apply,
    snd_apply, baseLd, dirLd, PolyTimeFun.ite_apply, isτL, ap₂_apply, SAT.ArrayProg.eqNat_apply,
    const_apply, decide_eq_true_eq, τL, jwL, szL, dL, seedLd, cL, yL, xL, sliceLd, sliceP_apply,
    oL, headD_apply, drop_apply, ptMapL, dirB, selDirL, seedOf]

end Ld

/-! ## The bounded parse -/

theorem decode_listBits_eq_some {d : Data} {bs : List BitStr} :
    (decode d : Option (List BitStr)) = some bs ↔ d = encode bs := by
  constructor
  · change Data.toList? decode d = some bs → d = Data.ofList encode bs
    induction d generalizing bs with
    | nil =>
      intro h
      simp only [Data.toList?, Option.some.injEq] at h
      subst h
      rfl
    | cons h tl _ ihtl =>
      intro hx
      simp only [Data.toList?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hx
      obtain ⟨b, hb, l, hl, rfl⟩ := hx
      rw [OracleDecider.decode_bitStr_eq_some.mp hb, ihtl hl]
      rfl
  · rintro rfl
    exact SizedEncoding.decode_encode bs

theorem readBits_rawList_encode (bs : List BitStr) :
    (rawList (encode bs)).map readBits = bs := by
  rw [rawList_encode, List.map_map]
  conv_rhs => rw [← List.map_id bs]
  apply List.map_congr_left
  intro b _
  exact readBits_encode b

/-- The blocks a serialized answer lists, whether or not it is well formed. -/
def rawBlocks (s : BitStr) : List BitStr := (rawList (Data.parse s)).map readBits

/-- **The bounded parse**, as a program: `(k, c, s)` to whether `s` parses to `c` blocks of `k`
bits, and the blocks. -/
def parseBP : PolyTimeFun (Unary × Unary × BitStr) (Bool × List BitStr) :=
  let d := OracleDecider.parseF.comp (snd.comp snd)
  let bs := (map readBits).comp (rawListP.comp d)
  (OracleDecider.andB (OracleDecider.eqD d (encoded.comp bs))
    (OracleDecider.andB (OracleDecider.eqD (encoded.comp (length.comp bs)) (encoded.comp (fst.comp snd)))
      (SAT.widthsProg.comp ((unaryToBin.comp fst).pair bs)))).pair bs

theorem parseBP_apply (kU cU : Unary) (s : BitStr) :
    parseBP (kU, cU, s) = ((parseB kU.length cU.length s).isSome, rawBlocks s) ∧
      ∀ bs, parseB kU.length cU.length s = some bs → rawBlocks s = bs := by
  have hraw : (rawListP (Data.parse s)).map readBits = rawBlocks s := rfl
  simp only [parseBP, pair_apply, OracleDecider.andB_apply, OracleDecider.eqD_apply, comp_apply,
    fst_apply, snd_apply, encoded_apply, map_apply, OracleDecider.parseF_apply, length_apply,
    SAT.widthsProg_apply, unaryToBin_apply, hraw]
  unfold parseB
  rcases hd : (decode (Data.parse s) : Option (List BitStr)) with _ | bs
  · have hne : Data.parse s ≠ encode (rawBlocks s) := fun he =>
      absurd (hd ▸ decode_listBits_eq_some.mpr he) (by simp)
    refine ⟨?_, fun _ h => by cases h⟩
    simp [hne]
  · have he := decode_listBits_eq_some.mp hd
    have hb : rawBlocks s = bs := by rw [rawBlocks, he, readBits_rawList_encode]
    rw [hb]
    refine ⟨?_, fun bs' h => ?_⟩
    · have hu : ((encode (unary bs.length) : Data) = encode cU) ↔ bs.length = cU.length := by
        rw [encode_injective.eq_iff]
        constructor
        · intro h; rw [← h, length_unary]
        · intro h; rw [h, unary_length]
      simp only [he, decide_true, Bool.true_and, hu]
      by_cases hc : bs.length = cU.length ∧ ∀ b ∈ bs, b.length = kU.length
      · rw [if_pos hc]
        simpa [hc.1] using hc.2
      · rw [if_neg hc]
        simp only [Option.isSome_none]
        by_cases hl : bs.length = cU.length
        · have : ¬ ∀ b ∈ bs, b.length = kU.length := fun h => hc ⟨hl, h⟩
          push Not at this
          simpa [hl] using this
        · simp [hl]
    · simp only at h
      split_ifs at h
      cases h
      rfl

/-! ## The number of elements -/

/-- `cntB`, in unary, as a program. -/
def cntP : PolyTimeFun ((Unary × Unary) × PcpTy) Unary :=
  let small := (finiteFunction fun t : PcpTy => decide ((t.1 : ℕ) < 5)).comp snd
  let ty (τ : LIDT.CL.Ty) := (finiteFunction fun t : PcpTy => decide (t.2 = τ)).comp snd
  let m := fst.comp fst
  let m' := snd.comp fst
  let mul (a b : PolyTimeFun ((Unary × Unary) × PcpTy) Unary) :=
    LowDegree.DegreeArithmetic.mulUnaryProg.comp (a.pair b)
  let succ (a : PolyTimeFun ((Unary × Unary) × PcpTy) Unary) := ap₂ append a (const (unary 1))
  let dm := succ (mul m (const (unary dPcp)))
  let dm' := succ (mul m' (const (unary dPcp)))
  let m6 := ap₂ append m' (const (unary 6))
  ite small (ite (ty .point) (const (unary 1)) (ite (ty .aline) (const (unary (dPcp + 1))) dm))
    (ite (ty .point) m6 (ite (ty .aline) (mul m6 (const (unary (dPcp + 1)))) (mul m6 dm')))

@[simp] theorem cntP_apply (mU m'U : Unary) (t : PcpTy) :
    cntP ((mU, m'U), t) = unary (cntB mU.length m'U.length t) := by
  obtain ⟨i, τ⟩ := t
  by_cases hi : (i : ℕ) < 5 <;> cases τ <;>
    simp [cntP, cntB, hi, ← unary_add]
  all_goals rw [unary_add, unary_length]

/-! ## One side -/

/-- The parameters, the game check's verdict, the types, the blocks of the questions and of the
answers. -/
abbrev SideIn := (Unary × Unary × List Desc) × Bool × (ArTy × ArTy) × (Blocks × Blocks) ×
  (List BitStr × List BitStr)

section Side

def kS : PolyTimeFun SideIn Unary := fst.comp fst
def m'S : PolyTimeFun SideIn Unary := fst.comp (snd.comp fst)
def descsS : PolyTimeFun SideIn (List Desc) := snd.comp (snd.comp fst)
def chkS : PolyTimeFun SideIn Bool := fst.comp snd
def tysS : PolyTimeFun SideIn (ArTy × ArTy) := fst.comp (snd.comp snd)
def xS : PolyTimeFun SideIn Blocks := fst.comp (fst.comp (snd.comp (snd.comp snd)))
def yS : PolyTimeFun SideIn Blocks := snd.comp (fst.comp (snd.comp (snd.comp snd)))
def aS : PolyTimeFun SideIn (List BitStr) := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def bS : PolyTimeFun SideIn (List BitStr) := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def onTys {β : Type*} [SizedEncoding β] (f : ArTy × ArTy → β) : PolyTimeFun SideIn β :=
  (finiteFunction f).comp tysS

def eqPart : PolyTimeFun SideIn Bool :=
  let idx := onTys fun pq => (eqPlan pq.1 pq.2).getD (0, 0)
  ite (onTys fun pq => (eqPlan pq.1 pq.2).isSome)
    (ap₂ SAT.ArrayProg.eqBits ((SAT.ArrayProg.getD []).comp ((fst.comp idx).pair aS))
      ((SAT.ArrayProg.getD []).comp ((snd.comp idx).pair bS)))
    (const true)

def widthP : PolyTimeFun SideIn Unary :=
  ite (onTys fun pq => decide (pq.2.2.2 = .aline)) (const (unary (dPcp + 1)))
    (ap₂ append (LowDegree.DegreeArithmetic.mulUnaryProg.comp (m'S.pair (const (unary dPcp))))
      (const (unary 1)))

def ldPart : PolyTimeFun SideIn Bool :=
  let idx := onTys fun pq => (ldPlan pq.1 pq.2).getD (0, false)
  let polys := ite (snd.comp idx)
    (chunksProg.comp ((ap₂ append m'S (const (unary 6))).pair (widthP.pair bS)))
    (cons bS (const []))
  ite (onTys fun pq => (ldPlan pq.1 pq.2).isSome)
    (ldBP.comp (kS.pair (((SAT.ArrayProg.getD default).comp ((fst.comp idx).pair descsS)).pair
      ((onTys fun pq => tyNat pq.2.2.2).pair (xS.pair (yS.pair (polys.pair aS)))))))
    (const true)

/-- `sideB`, as a program. -/
def sideBP : PolyTimeFun SideIn Bool :=
  OracleDecider.andB (OracleDecider.andB eqPart ldPart)
    (ite (onTys fun pq => chkPlan pq.1) chkS (const true))

@[simp] theorem sideBP_apply (kU m'U : Unary) (descs : List Desc) (chk : Bool) (p q : ArTy)
    (X Y : Blocks) (A B : List BitStr) :
    sideBP ((kU, m'U, descs), chk, (p, q), (X, Y), (A, B)) =
      sideB kU m'U descs chk p q X Y A B := by
  have hw : List.length (if q.2.2 = LIDT.CL.Ty.aline then unary (dPcp + 1)
      else unary (List.length m'U * dPcp) ++ unary 1) = width m'U.length q.2.2 := by
    by_cases hA : q.2.2 = .aline <;> simp [hA, width]
  have hl : (m'U ++ unary 6).length = m'U.length + 6 := by simp
  rcases hE : eqPlan p q with _ | ⟨α, β⟩ <;> rcases hL : ldPlan p q with _ | ⟨c, ch⟩ <;>
    simp only [sideBP, OracleDecider.andB_apply, eqPart, ldPart, widthP, onTys,
      PolyTimeFun.ite_apply, comp_apply, pair_apply, fst_apply, snd_apply, finiteFunction_apply,
      tysS, kS, m'S, descsS, chkS, xS, yS, aS, bS, ap₂_apply, SAT.ArrayProg.eqBits_apply,
      SAT.ArrayProg.getD_apply, const_apply, ldBP_apply, chunksProg_apply, cons_apply,
      append_apply, LowDegree.DegreeArithmetic.mulUnaryProg_apply, sideB, hE, hL,
      Option.isSome_none, Option.isSome_some, Option.getD_some, if_true, if_false,
      Bool.false_eq_true, hl] <;>
    by_cases h : chkPlan p = true <;> simp [h, hw]

end Side

/-! ## The predicate -/

/-- The parameters, the two game checks' verdicts, the types, the blocks of the questions and
the answers. -/
abbrev VerdictIn := (Unary × Unary × List Desc) × (Bool × Bool) × (ArTy × ArTy) ×
  (Blocks × Blocks) × (BitStr × BitStr)

section Verdict

def parV : PolyTimeFun VerdictIn (Unary × Unary × List Desc) := fst
def chksV : PolyTimeFun VerdictIn (Bool × Bool) := fst.comp snd
def tysV : PolyTimeFun VerdictIn (ArTy × ArTy) := fst.comp (snd.comp snd)
def blocksVP : PolyTimeFun VerdictIn (Blocks × Blocks) := fst.comp (snd.comp (snd.comp snd))
def ansV : PolyTimeFun VerdictIn (BitStr × BitStr) := snd.comp (snd.comp (snd.comp snd))

/-- The parse of one answer, at the type the selector names. -/
def parseV (ty : PolyTimeFun VerdictIn ArTy) (s : PolyTimeFun VerdictIn BitStr) :
    PolyTimeFun VerdictIn (Bool × List BitStr) :=
  let m := fst.comp (snd.comp ((SAT.ArrayProg.getD default).comp ((const 0).pair
    (snd.comp (snd.comp parV)))))
  parseBP.comp ((fst.comp parV).pair
    ((cntP.comp ((m.pair (fst.comp (snd.comp parV))).pair (snd.comp ty))).pair s))

/-- **`verdictB`, as a program.** -/
def verdictP : PolyTimeFun VerdictIn Bool :=
  let pa := parseV (fst.comp tysV) (fst.comp ansV)
  let pb := parseV (snd.comp tysV) (snd.comp ansV)
  let sideIn (sw : Bool) : PolyTimeFun VerdictIn SideIn :=
    let chk := if sw then snd.comp chksV else fst.comp chksV
    let tys := if sw then (snd.comp tysV).pair (fst.comp tysV) else tysV
    let bl := if sw then (snd.comp blocksVP).pair (fst.comp blocksVP) else blocksVP
    let an := if sw then (snd.comp pb).pair (snd.comp pa) else (snd.comp pa).pair (snd.comp pb)
    parV.pair (chk.pair (tys.pair (bl.pair an)))
  let sameTy := (finiteFunction fun pq : ArTy × ArTy => decide (pq.1 = pq.2)).comp tysV
  let eqAns := ite sameTy
    (OracleDecider.eqD (encoded.comp (snd.comp pa)) (encoded.comp (snd.comp pb))) (const true)
  OracleDecider.andB (fst.comp pa) (OracleDecider.andB (fst.comp pb)
    (OracleDecider.andB (OracleDecider.andB eqAns (sideBP.comp (sideIn false)))
      (sideBP.comp (sideIn true))))

theorem verdictP_apply (kU m'U : Unary) (descs : List Desc) (chkP chkQ : Bool) (p q : ArTy)
    (X Y : Blocks) (a b : BitStr) :
    verdictP ((kU, m'U, descs), (chkP, chkQ), (p, q), (X, Y), (a, b)) =
      verdictB kU m'U descs chkP chkQ p q X Y a b := by
  have hpa := parseBP_apply kU (unary (cntB (descs.getD 0 default).2.1.length m'U.length p.2)) a
  have hpb := parseBP_apply kU (unary (cntB (descs.getD 0 default).2.1.length m'U.length q.2)) b
  simp only [length_unary] at hpa hpb
  simp only [verdictP, parseV, OracleDecider.andB_apply, comp_apply, pair_apply, fst_apply,
    snd_apply, parV, chksV, tysV, blocksVP, ansV, SAT.ArrayProg.getD_apply, const_apply,
    cntP_apply, if_true, if_false, Bool.false_eq_true, PolyTimeFun.ite_apply,
    finiteFunction_apply, OracleDecider.eqD_apply, encoded_apply, sideBP_apply, hpa.1, hpb.1,
    verdictB]
  rcases hA : parseB kU.length (cntB (descs.getD 0 default).2.1.length m'U.length p.2) a
    with _ | A <;>
    rcases hB : parseB kU.length (cntB (descs.getD 0 default).2.1.length m'U.length q.2) b
    with _ | B <;> simp only [Option.isSome_none, Option.isSome_some, Bool.false_and,
      Bool.true_and]
  rw [hpa.2 A hA, hpb.2 B hB, acceptsB]
  congr 2
  by_cases hpq : p = q <;> simp [hpq, encode_injective.eq_iff]

end Verdict

end MIPRE.AnswerReduction

end
