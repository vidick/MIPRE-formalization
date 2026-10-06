/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.OutSampler
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

On `((λ, μ, σ), n, x, κ)` the program `lenF` computes the parameters in unary at `n` (a parameter
program `par`, fixed in P4i), reads the graph view of `x`, decodes it with `κ` into the indices of
the two factors by a finite table (`finiteFunction`, `idxAt`), and multiplies the selected factors
with `t` in unary; an undecodable view gives `0`. The calculator at `(λ, μ, σ)` hardcodes
`(λ, μ, σ)` (`lenD`), its program a polynomial-time function of them (`lenPF_eq`).

* `lenD_lenIs`: what it outputs on every input;
* `lenD_lenIs_question`: at a detyped question, the presented lengths, when the parameter program
  computes the parameters of the typed data;
* `lenD_meets`: the length half of `TailoredVerifier.MeetsAt`.
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

/-- The input of the calculator's function: `((λ, μ, σ), n, x, κ)`. -/
abbrev LenIn := (ℕ × ℕ × ℕ) × ℕ × BitStr × Bool

/-- **The calculator's function**, on `((λ, μ, σ), n, x, κ)`, for a parameter program `par` of
`((λ, μ, σ), n)`. -/
def lenF (par : PolyTimeFun ((ℕ × ℕ × ℕ) × ℕ) LenPar) : PolyTimeFun LenIn Unary :=
  let p := par.comp (fst.pair (fst.comp snd))
  let ik := (finiteFunction tabA).comp (((Program.readVector gdA).comp (fst.comp (snd.comp snd))).pair
    (snd.comp (snd.comp snd)))
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

theorem length_lenF (par : PolyTimeFun ((ℕ × ℕ × ℕ) × ℕ) LenPar) (lms : ℕ × ℕ × ℕ) (n : ℕ)
    (x : BitStr) (κ : Bool) :
    (lenF par (lms, n, x, κ)).length = lenOfIdx (par (lms, n)) (idxAt (graphOfBits x) κ) := by
  have h1 : (finiteFunction tabA) (Program.readVector gdA x, κ) = idxAt (graphOfBits x) κ := rfl
  simp only [lenF, comp_apply, pair_apply, fst_apply, snd_apply, cons_apply, const_apply,
    ArrayProg.getD_apply, LowDegree.DegreeArithmetic.mulUnaryProg_apply, length_unary, h1,
    lenOfIdx]
  congr 2
  · have := getD_unary_length [(par (lms, n)).2.1.length, (par (lms, n)).2.2.1.length, 1]
      (idxAt (graphOfBits x) κ).1
    simpa [unary_length] using this
  · have := getD_unary_length [1, (par (lms, n)).2.2.2.1.length, (par (lms, n)).2.2.2.2.length]
      (idxAt (graphOfBits x) κ).2
    simpa [unary_length] using this

/-! ## The calculator -/

variable (par : PolyTimeFun ((ℕ × ℕ × ℕ) × ℕ) LenPar)

/-- **The answer-length calculator at `(λ, μ, σ)`**: the calculator's function with `(λ, μ, σ)`
hardcoded. -/
def lenD (lam mu sigma : ℕ) : Decider :=
  ⟨hardcode (lenF par).code (encode ((lam, mu, sigma) : ℕ × ℕ × ℕ)),
    hardcode_wellScoped (lenF par).closed _⟩

/-- Its program, from `(λ, μ, σ)`, in polynomial time. -/
def lenPF : PolyTimeFun (ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (ℕ × ℕ × ℕ)).comp ((const (lenF par).code).pair (PolyTimeFun.id _))

theorem lenPF_eq (lam mu sigma : ℕ) : lenPF par (lam, mu, sigma) = (lenD par lam mu sigma).prog :=
  rfl

/-- **What the calculator outputs**, on every input. -/
theorem lenD_lenIs (lam mu sigma n : ℕ) (x : BitStr) (κ : Bool) :
    LenIs (lenD par lam mu sigma) n x κ
      (lenOfIdx (par ((lam, mu, sigma), n)) (idxAt (graphOfBits x) κ)) := by
  obtain ⟨t, -, hr⟩ := (lenF par).computes (((lam, mu, sigma), n, x, κ) : LenIn)
  rw [encode_prod] at hr
  refine ⟨_, _, hardcode_time (lenF par).closed hr, ?_⟩
  rw [← unary_length (lenF par ((lam, mu, sigma), n, x, κ)), encode_unary,
    length_spineList_ofNat, length_lenF]

/-- **The calculator at a detyped question**: the length of the type the question decodes to, at
the parameters the program computes, `0` when it does not decode. -/
theorem lenD_lenIs_question (lam mu sigma n : ℕ) {s : ℕ}
    (q : Detyping.Coord (Role × LIDT.CL.Ty) (Fin s) → 𝔽₂) (κ : Bool) :
    LenIs (lenD par lam mu sigma) n (toBits (DeciderProgram.vectorEquiv s q)) κ
      (((typeOf arGraph q).map fun u =>
        lenOfIdx (par ((lam, mu, sigma), n)) (cntIdx u.1 κ, ncIdx u.2)).getD 0) := by
  have h := lenD_lenIs par lam mu sigma n (toBits (DeciderProgram.vectorEquiv s q)) κ
  rw [show DeciderProgram.vectorEquiv s q = push (registerEquiv s).toEmbedding q from rfl,
    DeciderProgram.graphOfBits_register] at h
  have e : ((typeOf arGraph q).map fun u =>
      lenOfIdx (par ((lam, mu, sigma), n)) (cntIdx u.1 κ, ncIdx u.2)).getD 0 =
      lenOfIdx (par ((lam, mu, sigma), n)) (idxAt (pull Function.Embedding.inl q) κ) := by
    unfold idxAt typeOf
    cases decodeView arGraph (pull Function.Embedding.inl q) with
    | none => simp [lenOfIdx]
    | some p => rfl
  rw [e]
  exact h

/-- **The length half of `TailoredVerifier.MeetsAt`**: when the parameter program computes the
parameters of the typed data at `n`, the calculator outputs the presented game's lengths at the
detyped questions. -/
theorem lenD_presented {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
    {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j} {ℓV : ℕ}
    {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
    {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
    {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}
    (lam mu sigma : ℕ) (hpar : par ((lam, mu, sigma), n) = lenPar t j d L)
    (q : Detyping.Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t)) → 𝔽₂) :
    LenIs (lenD par lam mu sigma) n (toBits (DeciderProgram.vectorEquiv _ q)) false
        ((arPresented d hM sel L hLM V n Cc hm P B).lenR q) ∧
      LenIs (lenD par lam mu sigma) n (toBits (DeciderProgram.vectorEquiv _ q)) true
        ((arPresented d hM sel L hLM V n Cc hm P B).lenL q) := by
  constructor
  · have h := lenD_lenIs_question par lam mu sigma n q false
    simp only [hpar, lenOfIdx_lenPar, Bool.false_eq_true, ite_false] at h
    exact h
  · have h := lenD_lenIs_question par lam mu sigma n q true
    simp only [hpar, lenOfIdx_lenPar, ite_true] at h
    exact h

end MIPRE.Tailored.AnsRed.Typed

end
