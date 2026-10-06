/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArRoutine
public import MIPRE.Foundations.CL.DetypingProgFinite
public import MIPRE.Foundations.CL.DetypingDeciderGame

@[expose] public section

/-!
# The answer-length calculator of the answer-reduced verifier

Slice P4h of `planning/aldous-lyons-track.md`: the answer-length calculator of the output
tailored verifier of the answer reduction. At a detyped question, the presented game's lengths
are those of the type its graph view decodes to (`TypedData.detype`), and the typed lengths are
products: an answer of type `(r, S)` has a codeword count of the role — the oracle's readable or
linear count, or one for an isolated role — times the coefficients of a codeword at `S` — one,
`d + 1` or `M d + 1` — times the field width `t` (`Typed.lenR`, `Typed.lenL`).

On `(n, x, κ)`, with `(λ, μ, σ)` hardcoded, the calculator first runs the parameter program of
the routine (`ArRoutine.parCore`) on `((λ, μ, σ), n)`, as a stage: the parameters are written in
unary and grow like a power of `(λn + 1)^μ`, which no polynomial-time function of the binary
index can write. Then the polynomial-time function `lenF` reads the graph view of `x`, decodes it
with `κ` into the indices of the two factors by a finite table (`finiteFunction`, `idxAt`), and
multiplies the selected factors with `t` in unary; an undecodable view gives `0`.

* `lenD_lenIs`: what the calculator outputs on every input;
* `lenD_lenIs_question`: at a detyped question, the length of the type it decodes to;
* `lenD_presented`: the length half of `TailoredVerifier.MeetsAt`.
-/
noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun Cost.Data MIPRE.CL MIPRE.CL.CLFun MIPRE.CL.Detyping MIPRE.SAT

/-! ## The factors of a length -/

/-- The index of a role's codeword count at a kind: the oracle's readable (`0`) or linear (`1`)
count, or the one codeword of an isolated role (`2`). -/
def cntIdx : Role → Bool → ℕ
  | .oracle, false => 0
  | .oracle, true => 1
  | _, _ => 2

/-- The index of a type's number of coefficients: one, `d + 1`, `M d + 1`. -/
def ncIdx : LIDT.CL.Ty → ℕ
  | .point => 0
  | .aline => 1
  | .dline => 2

/-- The parameters of the lengths, in unary: the field width `t`, the oracle's readable and linear
codeword counts, `d + 1` and `M d + 1`. -/
abbrev LenPar := Unary × Unary × Unary × Unary × Unary

/-- The parameters of the typed data, in unary. -/
def lenPar (t j d : ℕ) (L : PcpDims) : LenPar :=
  (unary t, unary (rOf L .oracle).length, unary (lOf L .oracle).length, unary (d + 1),
    unary (2 ^ j * d + 1))

/-- The length at a pair of indices: the selected count, times the selected number of
coefficients, times `t`; `0` out of range. -/
def lenOfIdx (p : LenPar) (ik : ℕ × ℕ) : ℕ :=
  [p.2.1.length, p.2.2.1.length, 1].getD ik.1 0 *
    [1, p.2.2.2.1.length, p.2.2.2.2.length].getD ik.2 0 * p.1.length

/-- **The typed lengths are the selected products.** -/
theorem lenOfIdx_lenPar (t j d : ℕ) (L : PcpDims) (u : Role × LIDT.CL.Ty) (κ : Bool) :
    lenOfIdx (lenPar t j d L) (cntIdx u.1 κ, ncIdx u.2) =
      if κ then lenL t j d L u else lenR t j d L u := by
  obtain ⟨r, S⟩ := u
  cases κ <;> cases r <;> cases S <;>
    simp [lenOfIdx, lenPar, cntIdx, ncIdx, lenL, lenR, ncoef, rOf, lOf, length_unary]

/-! ## The decoding of a question -/

/-- The number of bits of a graph view of the answer-reduced types. -/
abbrev gdA : ℕ := graphDim (Role × LIDT.CL.Ty)

/-- The indices at a graph view and a kind: those of the type it decodes to, `(3, 3)` when it
does not decode. -/
def idxAt (g : Graph.Coord (Role × LIDT.CL.Ty) → 𝔽₂) (κ : Bool) : ℕ × ℕ :=
  ((decodeView arGraph g).map fun p => (cntIdx p.2.1 κ, ncIdx p.2.2)).getD (3, 3)

/-- The finite table: from the bits of a graph view and a kind, the indices. -/
def tabA (p : (Fin gdA → 𝔽₂) × Bool) : ℕ × ℕ :=
  idxAt (pull graphEquiv.toEmbedding p.1) p.2

/-- The parameters of the lengths, from the routine's parameters: `t`, the oracle's readable
count `6 + m + 2ℓ + ◇' + 3r` and linear count `5 + ◇' + 2ℓ + 3◇` (with `◇' = 2ℓ + 3◇ + 6` the
width of an index of `O` and `m` the number of wires), `d + 1` and `M d + 1`. -/
def lenParF : PolyTimeFun ArParams LenPar :=
  let oW := ap₂ append pL (ap₂ append pL (ap₂ append (AnswerReduction.ParRoutine.timesU 3 |>.comp
    pDm) (const (unary 6))))
  let nIn := ap₂ append (ap₂ append pL (const (unary 1))) (ap₂ append (ap₂ append pL
    (const (unary 1))) (ap₂ append (ap₂ append oW (const (unary 1))) (ap₂ append
      ((AnswerReduction.ParRoutine.timesU 3).comp pR) (const (unary 6)))))
  let m := ap₂ append nIn pS
  let rc := ap₂ append (const (unary 6)) (ap₂ append m (ap₂ append pL (ap₂ append pL
    (ap₂ append oW ((AnswerReduction.ParRoutine.timesU 3).comp pR)))))
  let lc := ap₂ append (const (unary 5)) (ap₂ append oW (ap₂ append pL (ap₂ append pL
    ((AnswerReduction.ParRoutine.timesU 3).comp pDm))))
  pT.pair (rc.pair (lc.pair ((ap₂ append pD (const (unary 1))).pair
    (ap₂ append (LowDegree.DegreeArithmetic.mulUnaryProg.comp (pM.pair pD)) (const (unary 1))))))

theorem unary_ext {u v : Unary} (h : u.length = v.length) : u = v := by
  rw [← unary_length u, ← unary_length v, h]

theorem lenParF_arParams (t j d : ℕ) (L : PcpDims) (e : Data) :
    lenParF (arParams t j d L e) = lenPar t j d L := by
  simp only [lenParF, lenPar, pair_apply, ap₂_apply, comp_apply, const_apply, append_apply,
    pT_arParams, pL_arParams, pDm_arParams, pR_arParams, pS_arParams, pD_arParams, pM_arParams,
    Prod.mk.injEq, true_and]
  refine ⟨unary_ext ?_, unary_ext ?_, unary_ext ?_, unary_ext ?_⟩ <;>
    simp only [List.length_append, length_unary, AnswerReduction.ParRoutine.timesU_apply,
      LowDegree.DegreeArithmetic.mulUnaryProg_apply, rOf, lOf, length_rSlots, length_lSlots,
      PcpDims.m, PcpDims.nIn, PcpDims.oW] <;> ring

/-- The input of the calculator's function: the parameters, the question and the kind. -/
abbrev LenIn := ArParams × BitStr × Bool

/-- **The calculator's function**, on the parameters, the question and the kind. -/
def lenF : PolyTimeFun LenIn Unary :=
  let p := lenParF.comp fst
  let ik := (finiteFunction tabA).comp
    (((Program.readVector gdA).comp (fst.comp snd)).pair (snd.comp snd))
  let cnt := (ArrayProg.getD ([] : Unary)).comp ((fst.comp ik).pair
    ((fst.comp (snd.comp p)).cons ((fst.comp (snd.comp (snd.comp p))).cons
      (const [unary 1]))))
  let nc := (ArrayProg.getD ([] : Unary)).comp ((snd.comp ik).pair
    ((const (unary 1)).cons ((fst.comp (snd.comp (snd.comp (snd.comp p)))).cons
      ((snd.comp (snd.comp (snd.comp (snd.comp p)))).cons (const [])))))
  LowDegree.DegreeArithmetic.mulUnaryProg.comp
    ((LowDegree.DegreeArithmetic.mulUnaryProg.comp (cnt.pair nc)).pair (fst.comp p))

theorem getD_unary_length (l : List ℕ) (i : ℕ) :
    ((l.map unary).getD i ([] : Unary)).length = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp [length_unary]
    | succ i => simpa using ih i

theorem length_lenF (p : ArParams) (x : BitStr) (κ : Bool) :
    (lenF (p, x, κ)).length = lenOfIdx (lenParF p) (idxAt (graphOfBits x) κ) := by
  have h1 : (finiteFunction tabA) (Program.readVector gdA x, κ) = idxAt (graphOfBits x) κ := rfl
  simp only [lenF, comp_apply, pair_apply, fst_apply, snd_apply, cons_apply, const_apply,
    ArrayProg.getD_apply, LowDegree.DegreeArithmetic.mulUnaryProg_apply, length_unary, h1,
    lenOfIdx]
  congr 2
  · have := getD_unary_length [(lenParF p).2.1.length, (lenParF p).2.2.1.length, 1]
      (idxAt (graphOfBits x) κ).1
    simpa [unary_length] using this
  · have := getD_unary_length [1, (lenParF p).2.2.2.1.length, (lenParF p).2.2.2.2.length]
      (idxAt (graphOfBits x) κ).2
    simpa [unary_length] using this

/-! ## The calculator -/

/-- The parameter stage's argument, on `((λ, μ, σ), (n, x, κ))`: `((λ, μ, σ), n)`. -/
def parArg : PolyTimeFun Data Data := ap₂ treePair treeHead (treeHead.comp treeTail)

/-- The calculator's input, read after the parameter stage. -/
def lenRead : PolyTimeFun Data LenIn :=
  (readParams.comp (fieldAt 0)).pair ((Program.readBits.comp (fieldAt 3)).pair
    (Program.rawTruthProg.comp (tailAt 4)))

namespace ArRoutine

variable (R : ArRoutine)

/-- **The calculator's core**, on `((λ, μ, σ), (n, x, κ))`: the parameter stage, then `lenF`. -/
def lenCore : Prog := seqProg (AnswerReduction.stg parArg R.parCore) (lenF.comp lenRead).code

theorem lenCore_closed : R.lenCore.WellScoped 1 :=
  seqProg_closed (AnswerReduction.stg_closed _ R.closed) (PolyTimeFun.closed _)

/-- **The answer-length calculator at `(λ, μ, σ)`**: the core with `(λ, μ, σ)` hardcoded. -/
def lenD (lam mu sigma : ℕ) : Decider :=
  ⟨hardcode R.lenCore (encode ((lam, mu, sigma) : ℕ × ℕ × ℕ)),
    hardcode_wellScoped R.lenCore_closed _⟩

/-- Its program, from `(λ, μ, σ)`, in polynomial time. -/
def lenPF : PolyTimeFun (ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (ℕ × ℕ × ℕ)).comp ((const R.lenCore).pair (PolyTimeFun.id _))

theorem lenPF_eq (lam mu sigma : ℕ) : R.lenPF (lam, mu, sigma) = (R.lenD lam mu sigma).prog :=
  rfl

/-- **What the calculator outputs**, on every input: the length of the type the question's graph
view decodes to, at the parameters of the index. -/
theorem lenD_lenIs (lam mu sigma n : ℕ) (x : BitStr) (κ : Bool) :
    LenIs (R.lenD lam mu sigma) n x κ
      (lenOfIdx (lenPar ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
        (R.L lam mu sigma n)) (idxAt (graphOfBits x) κ)) := by
  set X0 : Data := .cons (encode ((lam, mu, sigma) : ℕ × ℕ × ℕ)) (encode (n, x, κ))
  have r1 := AnswerReduction.stg_runs parArg R.closed X0 (encode (R.params lam mu sigma n))
    (by simpa [parArg, X0, encode_prod] using R.parCore_runs lam mu sigma n)
  obtain ⟨t2, -, r2⟩ := (lenF.comp lenRead).computes (.cons (encode (R.params lam mu sigma n)) X0)
  have hr : lenRead (.cons (encode (R.params lam mu sigma n)) X0) =
      (R.params lam mu sigma n, x, κ) := by
    simp only [lenRead, X0, fieldAt, tailAt, encode_prod, pair_apply, comp_apply,
      treeHead_cons, treeTail_cons, readParams_encode, Program.readBits_encode,
      Program.rawTruthProg_encode_bool, PolyTimeFun.id_apply]
  rw [encode_data, comp_apply, hr] at r2
  obtain ⟨t, ht⟩ := AnswerReduction.ParRoutine.seq_runs (PolyTimeFun.closed _) r1 ⟨t2, r2⟩
  refine ⟨_, _, hardcode_time R.lenCore_closed ht, ?_⟩
  rw [← unary_length (lenF _), encode_unary, length_spineList_ofNat, length_lenF, params,
    lenParF_arParams]

/-- **The calculator at a detyped question**: the length of the type the question decodes to,
`0` when it does not decode. -/
theorem lenD_lenIs_question (lam mu sigma n : ℕ) {s : ℕ}
    (q : Detyping.Coord (Role × LIDT.CL.Ty) (Fin s) → 𝔽₂) (κ : Bool) :
    LenIs (R.lenD lam mu sigma) n (toBits (DeciderProgram.vectorEquiv s q)) κ
      (((typeOf arGraph q).map fun u =>
        lenOfIdx (lenPar ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
          (R.d lam mu sigma n) (R.L lam mu sigma n)) (cntIdx u.1 κ, ncIdx u.2)).getD 0) := by
  have h := R.lenD_lenIs lam mu sigma n (toBits (DeciderProgram.vectorEquiv s q)) κ
  rw [show DeciderProgram.vectorEquiv s q = push (registerEquiv s).toEmbedding q from rfl,
    DeciderProgram.graphOfBits_register] at h
  have e : ((typeOf arGraph q).map fun u =>
      lenOfIdx (lenPar ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
        (R.d lam mu sigma n) (R.L lam mu sigma n)) (cntIdx u.1 κ, ncIdx u.2)).getD 0 =
      lenOfIdx (lenPar ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
        (R.L lam mu sigma n)) (idxAt (pull Function.Embedding.inl q) κ) := by
    unfold idxAt typeOf
    cases decodeView arGraph (pull Function.Embedding.inl q) with
    | none => simp [lenOfIdx]
    | some p => rfl
  rw [e]
  exact h

/-- **The length half of `TailoredVerifier.MeetsAt`**: the calculator outputs the presented
game's lengths at the detyped questions, at the routine's parameters. -/
theorem lenD_presented (lam mu sigma : ℕ) {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ}
    {Cc : V.Questions n → Circuit}
    {hm : ∀ z, (Cc z).inputs + (Cc z).size = (R.L lam mu sigma n).m} {ℓ : ℕ}
    {P : Bool → Role × LIDT.CL.Ty →
      CLFun (ZMod 2) (Fin (V.sampler.dim n + D ((R.fam lam mu sigma).j n) *
        (R.fam lam mu sigma).t n)) ℓ} {B : ℕ}
    (q : Detyping.Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D ((R.fam lam mu sigma).j n) *
      (R.fam lam mu sigma).t n)) → 𝔽₂) :
    LenIs (R.lenD lam mu sigma) n (toBits (DeciderProgram.vectorEquiv _ q)) false
        ((arPresented (R.d lam mu sigma n) ((R.fam lam mu sigma).dvd n)
          ((R.fam lam mu sigma).sel n) (R.L lam mu sigma n) (R.hLM lam mu sigma n) V n Cc hm P
          B).lenR q) ∧
      LenIs (R.lenD lam mu sigma) n (toBits (DeciderProgram.vectorEquiv _ q)) true
        ((arPresented (R.d lam mu sigma n) ((R.fam lam mu sigma).dvd n)
          ((R.fam lam mu sigma).sel n) (R.L lam mu sigma n) (R.hLM lam mu sigma n) V n Cc hm P
          B).lenL q) := by
  constructor
  · have h := R.lenD_lenIs_question lam mu sigma n q false
    simp only [lenOfIdx_lenPar, Bool.false_eq_true, ite_false] at h
    exact h
  · have h := R.lenD_lenIs_question lam mu sigma n q true
    simp only [lenOfIdx_lenPar, ite_true] at h
    exact h

end ArRoutine

end MIPRE.Tailored.AnsRed.Typed

end
