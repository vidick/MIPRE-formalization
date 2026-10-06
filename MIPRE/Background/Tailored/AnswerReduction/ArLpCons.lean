/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpProofEqs
public import MIPRE.Background.Tailored.AnswerReduction.ArLen

@[expose] public section

/-!
# The constraints at two detyped questions, as a program

Slice P4h of `planning/aldous-lyons-track.md`: the last stage of the answer-reduced verifier's
linear-constraints processor. From the parameters, the two questions' bits, the readable answers
and the input sampler's questions at the two seeds, it decodes the edge the two graph views sit
on by a finite table (`edgeF`), checks the readable lengths (`lenOkF`), and on the edge's pair of
types runs the four checks' programs (`consBranchF`), as the typed data does
(`Typed.cons`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.CL.Detyping MIPRE.SAT MIPRE.Tailored.Intro

variable {t : ℕ} {ht : 1 ≤ t}

/-! ## The input -/

/-- **The input of the processor's last stage**: the parameters; the two questions' bits and the
two readable answers; Alice's and Bob's questions of the input sampler at the first question's
seed, then at the second's; the input verifier's programs, `(λ, μ, σ)` and the index. -/
abbrev LpIn : Type := ArParams × (BitStr × BitStr × BitStr × BitStr) ×
  (BitStr × BitStr × BitStr × BitStr) × ((Prog × Prog × Prog) × (ℕ × ℕ × ℕ) × ℕ)

def lP : PolyTimeFun LpIn ArParams := fst
def lX : PolyTimeFun LpIn BitStr := fst.comp (fst.comp snd)
def lY : PolyTimeFun LpIn BitStr := fst.comp (snd.comp (fst.comp snd))
def lA : PolyTimeFun LpIn BitStr := fst.comp (snd.comp (snd.comp (fst.comp snd)))
def lB : PolyTimeFun LpIn BitStr := snd.comp (snd.comp (snd.comp (fst.comp snd)))
def lAx : PolyTimeFun LpIn BitStr := fst.comp (fst.comp (snd.comp snd))
def lBx : PolyTimeFun LpIn BitStr := fst.comp (snd.comp (fst.comp (snd.comp snd)))
def lAy : PolyTimeFun LpIn BitStr := fst.comp (snd.comp (snd.comp (fst.comp (snd.comp snd))))
def lBy : PolyTimeFun LpIn BitStr := snd.comp (snd.comp (snd.comp (fst.comp (snd.comp snd))))
def lV : PolyTimeFun LpIn (Prog × Prog × Prog) := fst.comp (snd.comp (snd.comp snd))
def lLms : PolyTimeFun LpIn (ℕ × ℕ × ℕ) := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def lN : PolyTimeFun LpIn ℕ := snd.comp (snd.comp (snd.comp (snd.comp snd)))

/-! ## The pieces of a question -/

/-- `D t = (2M + 1) t`, the number of a question's low-degree bits. -/
def dtF : PolyTimeFun ArParams Unary :=
  mulU.comp ((ap₂ append (ap₂ append pM pM) (const (unary 1))).pair pT)

/-- The vector part of a question's bits: after the graph view. -/
def vecF (q : PolyTimeFun LpIn BitStr) : PolyTimeFun LpIn BitStr :=
  ap₂ drop q (const (unary gdA))

/-- The low-degree bits of a question: the last `D t` bits of its vector part. -/
def ldbF (q : PolyTimeFun LpIn BitStr) : PolyTimeFun LpIn BitStr :=
  AnswerReduction.rightBP.comp ((vecF q).pair (dtF.comp lP))

/-- A question's readable length, by the calculator's function. -/
def lenRq (q : PolyTimeFun LpIn BitStr) : PolyTimeFun LpIn Unary :=
  lenF.comp (lP.pair (q.pair (const false)))

/-- A question's length. -/
def lenq (q : PolyTimeFun LpIn BitStr) : PolyTimeFun LpIn Unary :=
  ap₂ append (lenRq q) (lenF.comp (lP.pair (q.pair (const true))))

/-- The first question's length, `Na`. -/
def nAF : PolyTimeFun LpIn Unary := lenq lX
/-- The two questions' lengths, `N`. -/
def nF : PolyTimeFun LpIn Unary := ap₂ append (lenq lX) (lenq lY)

/-- The number of slots of a role. -/
def kF : Role → PolyTimeFun ArParams Unary
  | .oracle => ap₂ append (fst.comp (snd.comp lenParF)) (fst.comp (snd.comp (snd.comp lenParF)))
  | _ => const (unary 2)

/-- The number of coefficients of a codeword at a type. -/
def ncF : LIDT.CL.Ty → PolyTimeFun ArParams Unary
  | .point => const (unary 1)
  | .aline => fst.comp (snd.comp (snd.comp (snd.comp lenParF)))
  | .dline => snd.comp (snd.comp (snd.comp (snd.comp lenParF)))

/-- The gates of a circuit. -/
def gatesF : PolyTimeFun Circuit (List Gate) :=
  snd.comp (ofEncodeEq (fun C : Circuit => (C.inputs, C.gates)) fun _ => rfl)

@[simp] theorem gatesF_apply (C : Circuit) : gatesF C = C.gates := rfl

/-- The point coordinates of a question: the first run of its low-degree blocks. -/
def ptsF (q : PolyTimeFun LpIn BitStr) : PolyTimeFun LpIn (List BitStr) :=
  fst.comp (blkF.comp ((pT.comp lP).pair ((pM.comp lP).pair (ldbF q))))

/-! ## The checks at a pair of types -/

/-- The low-degree checks' input at a pair of types. -/
def ldInF (u v : Role × LIDT.CL.Ty) : PolyTimeFun LpIn LdCIn :=
  ((pT.comp lP).pair ((pJ.comp lP).pair ((pM.comp lP).pair (pD.comp lP)))).pair
    ((((kF u.1).comp lP).pair (nAF.pair nF)).pair
      (((const u.2).pair (ldbF lX)).pair ((const v.2).pair (ldbF lY))))

/-- The consistency checks' input at a pair of types. -/
def ccInF (u v : Role × LIDT.CL.Ty) : PolyTimeFun LpIn ConsIn :=
  (pT.comp lP).pair (((ncF u.2).comp lP).pair (nAF.pair (nF.pair ((rcF.comp lP).pair
    (const (u.1, v.1))))))

/-- The indifference checks' input of a question of type `r` at offset `o`. -/
def indInF (o : PolyTimeFun LpIn Unary) (r : Role × LIDT.CL.Ty) (q : PolyTimeFun LpIn BitStr) :
    PolyTimeFun LpIn IndCIn :=
  lP.pair (o.pair (nF.pair ((const r).pair (ldbF q))))

namespace ArRoutine

variable (R : ArRoutine)

/-- The circuit of a question's seed, from the input sampler's questions there. -/
def circQ (qa qb : PolyTimeFun LpIn BitStr) : PolyTimeFun LpIn Circuit :=
  R.circF.comp (lV.pair (lLms.pair (lN.pair (lP.pair (qa.pair qb)))))

/-- The proof check's input of a question at offset `o`, with readable answer `aR`. -/
def prfInF (o : PolyTimeFun LpIn Unary) (q aR qa qb : PolyTimeFun LpIn BitStr) :
    PolyTimeFun LpIn PrfIn :=
  lP.pair (o.pair (nF.pair ((ptsF q).pair (aR.pair (gatesF.comp (R.circQ qa qb))))))

/-- **The checks at a pair of types**: the low-degree checks at one role, the consistency checks
at one low-degree type, the indifference checks of each answer, and the proof check of each
oracle point answer. -/
def consBranchF (u v : Role × LIDT.CL.Ty) : PolyTimeFun LpIn (List BitStr) :=
  let ld := if u.1 = v.1 then ldConsF.comp (ldInF u v) else const []
  let cc := if u.2 = v.2 then consConsF.comp (ccInF u v) else const []
  let i₁ := indConsF.comp (indInF (const (unary 0)) u lX)
  let i₂ := indConsF.comp (indInF nAF v lY)
  let p₁ := if u = (.oracle, .point) then
    proofConsF.comp (R.prfInF (const (unary 0)) lX lA lAx lBx) else const []
  let p₂ := if v = (.oracle, .point) then proofConsF.comp (R.prfInF nAF lY lB lAy lBy)
    else const []
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append ld cc) i₁) i₂) p₁) p₂

end ArRoutine

/-! ## The edge and the lengths -/

/-- The edge two graph views sit on, Alice's first. -/
def selF (p : (Fin gdA → 𝔽₂) × (Fin gdA → 𝔽₂)) :
    Option ((Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty)) :=
  DeciderProgram.selectedEdge arGraph (pull graphEquiv.toEmbedding p.1)
    (pull graphEquiv.toEmbedding p.2)

/-- **The edge of two questions**, by a finite table on their graph views. -/
def edgeF : PolyTimeFun LpIn (Option ((Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty))) :=
  (finiteFunction selF).comp (((Program.readVector gdA).comp lX).pair
    ((Program.readVector gdA).comp lY))

/-- A unary number as a natural number. -/
def uNat : PolyTimeFun Unary ℕ := ap₂ addUnary (const 0) (PolyTimeFun.id _)

/-- **The length check**: both readable answers have their questions' readable lengths. -/
def lenOkF : PolyTimeFun LpIn Bool :=
  andF.comp ((ap₂ ArrayProg.eqNat (DeciderProgram.lengthNat.comp lA) (uNat.comp (lenRq lX))).pair
    (ap₂ ArrayProg.eqNat (DeciderProgram.lengthNat.comp lB) (uNat.comp (lenRq lY))))

/-- **The processor's last stage**: on the edge of the two questions, if the readable answers
have their lengths, the checks at the edge's pair of types; nothing otherwise. -/
def ArRoutine.lpPost (R : ArRoutine) : PolyTimeFun LpIn (List BitStr) :=
  ite lenOkF (choose edgeF (fun e => match e with
    | some (u, v) => R.consBranchF u v
    | none => const []) (const [])) (const [])

/-! ## Correctness of the pieces -/

theorem kF_arParams (t j d : ℕ) (L : PcpDims) (e : Data) (r : Role) :
    kF r (arParams t j d L e) = unary (slotsOf L r).length := by
  cases r <;> simp [kF, lenParF_arParams, lenPar, slotsOf, rOf, lOf, unary_append_unary]

theorem ncF_arParams (t j d : ℕ) (L : PcpDims) (e : Data) (S : LIDT.CL.Ty) :
    ncF S (arParams t j d L e) = unary (ncoef j d S) := by
  cases S <;> simp [ncF, lenParF_arParams, lenPar, ncoef]

theorem dtF_arParams (t j d : ℕ) (L : PcpDims) (e : Data) :
    dtF (arParams t j d L e) = unary (D j * t) := by
  apply unary_ext
  simp only [dtF, comp_apply, pair_apply, ap₂_apply, append_apply, const_apply, pM_arParams,
    pT_arParams, unary_append_unary, mulU_apply, length_unary, D]
  ring

/-- A typed view's indices are its type's. -/
theorem idxAt_of_typeOf {s : ℕ} {q : Coord (Role × LIDT.CL.Ty) (Fin s) → 𝔽₂}
    {u : Role × LIDT.CL.Ty} (h : typeOf arGraph q = some u) (κ : Bool) :
    idxAt (pull Function.Embedding.inl q) κ = (cntIdx u.1 κ, ncIdx u.2) := by
  unfold typeOf at h
  unfold idxAt
  cases hd : decodeView arGraph (pull Function.Embedding.inl q) with
  | none => simp [hd] at h
  | some p =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    simp [h]

/-- The edge of two detyped questions is read off their selected edge. -/
theorem edgeOf_eq_selectedEdge {s : ℕ} (x y : Coord (Role × LIDT.CL.Ty) (Fin s) → 𝔽₂) :
    edgeOf arGraph x y = (DeciderProgram.selectedEdge arGraph (pull Function.Embedding.inl x)
      (pull Function.Embedding.inl y)).map fun uv =>
        ((uv.1, pull Function.Embedding.inr x), (uv.2, pull Function.Embedding.inr y)) := by
  unfold edgeOf DeciderProgram.selectedEdge
  cases select arGraph false (pull Function.Embedding.inl x) <;>
    cases select arGraph true (pull Function.Embedding.inl y) <;> try rfl
  dsimp only
  split_ifs <;> rfl

section Reads

variable {s : ℕ} (p : ArParams) (qx qy : Coord (Role × LIDT.CL.Ty) (Fin s) → 𝔽₂)
  (aR bR : BitStr) (w : BitStr × BitStr × BitStr × BitStr)
  (c : (Prog × Prog × Prog) × (ℕ × ℕ × ℕ) × ℕ)

/-- The input at two detyped questions. -/
abbrev lpIn : LpIn :=
  (p, (toBits (DeciderProgram.vectorEquiv s qx), toBits (DeciderProgram.vectorEquiv s qy), aR, bR),
    w, c)

theorem edgeF_lpIn : edgeF (lpIn p qx qy aR bR w c) =
    DeciderProgram.selectedEdge arGraph (pull Function.Embedding.inl qx)
      (pull Function.Embedding.inl qy) := by
  have hx := DeciderProgram.graphOfBits_register s qx
  have hy := DeciderProgram.graphOfBits_register s qy
  simp only [graphOfBits] at hx hy
  simp only [edgeF, comp_apply, pair_apply, finiteFunction_apply, Program.readVector_apply, lX, lY,
    fst_apply, snd_apply, selF]
  rw [show DeciderProgram.vectorEquiv s qx = push (registerEquiv s).toEmbedding qx from rfl,
    show DeciderProgram.vectorEquiv s qy = push (registerEquiv s).toEmbedding qy from rfl, hx, hy]

theorem lenF_lpIn_x {t j d : ℕ} {L : PcpDims} {e : Data} (hp : p = arParams t j d L e)
    {u : Role × LIDT.CL.Ty} (hu : typeOf arGraph qx = some u) (κ : Bool) :
    lenF (p, toBits (DeciderProgram.vectorEquiv s qx), κ) =
      unary (if κ then lenL t j d L u else lenR t j d L u) := by
  apply unary_ext
  rw [length_lenF, length_unary, hp, lenParF_arParams,
    show DeciderProgram.vectorEquiv s qx = push (registerEquiv s).toEmbedding qx from rfl,
    DeciderProgram.graphOfBits_register, idxAt_of_typeOf hu, lenOfIdx_lenPar]

theorem lenOkF_lpIn {t j d : ℕ} {L : PcpDims} {e : Data} (hp : p = arParams t j d L e)
    {u v : Role × LIDT.CL.Ty} (hu : typeOf arGraph qx = some u)
    (hv : typeOf arGraph qy = some v) :
    lenOkF (lpIn p qx qy aR bR w c) =
      decide (aR.length = lenR t j d L u ∧ bR.length = lenR t j d L v) := by
  have h1 := lenF_lpIn_x p qx hp hu false
  have h2 := lenF_lpIn_x p qy hp hv false
  simp only [Bool.false_eq_true, ite_false] at h1 h2
  simp only [lenOkF, comp_apply, pair_apply, andF_apply, ap₂_apply, ArrayProg.eqNat_apply,
    DeciderProgram.lengthNat_apply, lA, lB, lX, lY, lP, fst_apply, snd_apply, lenRq,
    const_apply, h1, h2, uNat, addUnary_apply, id_apply, length_unary, zero_add,
    Bool.decide_and]

end Reads

/-- **The family's selector is the introspection stage's selector program.** -/
theorem LdFamily.sel_chi (F : LdFamily) (n : ℕ) (a : Fq (F.t n) (F.ht n)) :
    (((F.sel n).χ a : Fin (2 ^ F.j n)) : ℕ) = Introspection.SeedProgram.selectorProg
      (unary (F.t n), unary (F.j n), (shoupBinField (F.t n) (F.ht n)).toBits a) :=
  (Introspection.SeedProgram.selectorProg_correct (shoupBinField (F.t n) (F.ht n)) (F.j n)
    (F.hjt n) a).symm

/-! ## The checks on the processor's input -/

section Parts

variable {j d : ℕ} {L : PcpDims} {e : Data} {rV : ℕ} {p : ArParams}
  (hp : p = arParams t j d L e)
  (qx qy : Coord (Role × LIDT.CL.Ty) (Fin (rV + D j * t)) → 𝔽₂) (aR bR : BitStr)
  (w : BitStr × BitStr × BitStr × BitStr) (c : (Prog × Prog × Prog) × (ℕ × ℕ × ℕ) × ℕ)
  {u v : Role × LIDT.CL.Ty} (hu : typeOf arGraph qx = some u) (hv : typeOf arGraph qy = some v)

include hp

/-- The low-degree bits of a question's vector part. -/
theorem ldbF_toBits (q : PolyTimeFun LpIn BitStr) (z : Coord (Role × LIDT.CL.Ty)
      (Fin (rV + D j * t)) → 𝔽₂) (inp : LpIn) (hpi : lP inp = p)
    (hq : q inp = toBits (DeciderProgram.vectorEquiv _ z)) :
    ldbF q inp = (toBits (pull Function.Embedding.inr z)).drop rV := by
  simp only [ldbF, comp_apply, pair_apply, vecF, ap₂_apply, const_apply, drop_apply,
    length_unary, hpi, hp, dtF_arParams, AnswerReduction.rightBP_apply, hq]
  rw [show DeciderProgram.vectorEquiv _ z = push (registerEquiv _).toEmbedding z from rfl,
    DeciderProgram.drop_register, length_toBits]
  congr 1
  omega

include hu hv

omit hv in
theorem nAF_lpIn : nAF (lpIn p qx qy aR bR w c) = unary (len t j d L u) := by
  have h1 := lenF_lpIn_x p qx hp hu false
  have h2 := lenF_lpIn_x p qx hp hu true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h1 h2
  simp only [nAF, lenq, lenRq, ap₂_apply, comp_apply, pair_apply, lP, lX, fst_apply, snd_apply,
    const_apply, h1, h2, append_unary, len]

theorem nF_lpIn : nF (lpIn p qx qy aR bR w c) = unary (len t j d L u + len t j d L v) := by
  have h1 := lenF_lpIn_x p qx hp hu false
  have h2 := lenF_lpIn_x p qx hp hu true
  have h3 := lenF_lpIn_x p qy hp hv false
  have h4 := lenF_lpIn_x p qy hp hv true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h1 h2 h3 h4
  simp only [nF, lenq, lenRq, ap₂_apply, comp_apply, pair_apply, lP, lX, lY, fst_apply, snd_apply,
    const_apply, h1, h2, h3, h4, append_unary, len]

theorem ldInF_lpIn : ldInF u v (lpIn p qx qy aR bR w c) =
    ldIn (t := t) (j := j) (d := d) (slotsOf L u.1).length (len t j d L u)
      (len t j d L u + len t j d L v) u.2 v.2 (pull Function.Embedding.inr qx)
      (pull Function.Embedding.inr qy) := by
  subst hp
  simp only [ldInF, pair_apply, comp_apply, const_apply, lP, fst_apply, pT_arParams,
    pJ_arParams, pM_arParams, pD_arParams, kF_arParams, nAF_lpIn rfl qx qy aR bR w c hu,
    nF_lpIn rfl qx qy aR bR w c hu hv,
    ldbF_toBits rfl lX qx (lpIn (arParams t j d L e) qx qy aR bR w c) rfl rfl,
    ldbF_toBits rfl lY qy (lpIn (arParams t j d L e) qx qy aR bR w c) rfl rfl]

theorem ccInF_lpIn : ccInF u v (lpIn p qx qy aR bR w c) =
    (unary t, unary (ncoef j d u.2), unary (len t j d L u), unary (len t j d L u + len t j d L v),
      unary (rSlots L).length, (u.1, v.1)) := by
  subst hp
  simp only [ccInF, pair_apply, comp_apply, const_apply, lP, fst_apply, pT_arParams,
    ncF_arParams, rcF_arParams, nAF_lpIn rfl qx qy aR bR w c hu, nF_lpIn rfl qx qy aR bR w c hu hv]

theorem indInF_lX : indInF (const (unary 0)) u lX (lpIn p qx qy aR bR w c) =
    (arParams t j d L e, unary 0, unary (len t j d L u + len t j d L v), u,
      (toBits (pull Function.Embedding.inr qx)).drop rV) := by
  subst hp
  simp only [indInF, pair_apply, const_apply, lP, fst_apply,
    nF_lpIn rfl qx qy aR bR w c hu hv,
    ldbF_toBits rfl lX qx (lpIn (arParams t j d L e) qx qy aR bR w c) rfl rfl]

theorem indInF_lY : indInF nAF v lY (lpIn p qx qy aR bR w c) =
    (arParams t j d L e, unary (len t j d L u), unary (len t j d L u + len t j d L v), v,
      (toBits (pull Function.Embedding.inr qy)).drop rV) := by
  subst hp
  simp only [indInF, pair_apply, const_apply, lP, fst_apply,
    nAF_lpIn rfl qx qy aR bR w c hu, nF_lpIn rfl qx qy aR bR w c hu hv,
    ldbF_toBits rfl lY qy (lpIn (arParams t j d L e) qx qy aR bR w c) rfl rfl]

end Parts

theorem ptsF_getD {j d : ℕ} {L : PcpDims} {e : Data} {rV : ℕ} {p : ArParams}
    (hp : p = arParams t j d L e) (q : PolyTimeFun LpIn BitStr)
    (z : Coord (Role × LIDT.CL.Ty) (Fin (rV + D j * t)) → 𝔽₂) (inp : LpIn) (hpi : lP inp = p)
    (hq : q inp = toBits (DeciderProgram.vectorEquiv _ z)) (hLM : L.m ≤ 2 ^ j) (X : Fin L.m) :
    (ptsF q inp).getD X [] = (shoupBinField t ht).toBits
      (ptm L hLM ((regs j).ptOf (ldPart t ht j rV (pull Function.Embedding.inr z))) X) := by
  have hX : (X : ℕ) < 2 ^ j := lt_of_lt_of_le X.2 hLM
  simp only [ptsF, comp_apply, pair_apply, fst_apply, hpi, hp, pT_arParams, pM_arParams,
    ldbF_toBits hp q z inp hpi hq, blkF_apply, blocks1_ldPart (ht := ht), BinField.vecBits]
  rw [List.getD_eq_getElem _ _ (by simpa using hX)]
  simp [ptm, Fin.castLE]

namespace ArRoutine

section Correct

variable (R : ArRoutine) (lam mu sigma n : ℕ) {ℓ : ℕ} (V : TailoredVerifier (ℓ + 1))

/-- **The processor's last stage's input** at two detyped questions of the answer-reduced game:
with the input sampler's questions at their seeds, and the input's programs. -/
abbrev qIn (qx qy : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) (aR bR : BitStr) : LpIn :=
  lpIn (R.params lam mu sigma n) qx qy aR bR
    (toBits ((V.sampler.cl n .alice).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qx))),
      toBits ((V.sampler.cl n .bob).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qx))),
      toBits ((V.sampler.cl n .alice).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qy))),
      toBits ((V.sampler.cl n .bob).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qy))))
    (V.progs, (lam, mu, sigma), n)

/-- **The proof check of the first question**, an oracle point question, on the processor's
input. -/
theorem proof_lX (qx qy : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) (aR bR : BitStr)
    {u v : Role × LIDT.CL.Ty} (hu : typeOf arGraph qx = some u)
    (hv : typeOf arGraph qy = some v) :
    proofConsF (R.prfInF (const (unary 0)) lX lA lAx lBx (R.qIn lam mu sigma n V qx qy aR bR)) =
      proofCons ((R.fam lam mu sigma).j n) (R.d lam mu sigma n) (R.L lam mu sigma n)
        (R.hLM lam mu sigma n)
        (len ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
          (R.L lam mu sigma n) u + len ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
          (R.d lam mu sigma n) (R.L lam mu sigma n) v) 0
        (circOf (R.L lam mu sigma n) V n (R.circ lam mu sigma n V) (R.circ_wires lam mu sigma n V)
          (rolePart ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (V.sampler.dim n)
            (pull Function.Embedding.inr qx)))
        ((regs ((R.fam lam mu sigma).j n)).ptOf (ldPart ((R.fam lam mu sigma).t n)
          ((R.fam lam mu sigma).ht n) ((R.fam lam mu sigma).j n) (V.sampler.dim n)
          (pull Function.Embedding.inr qx))) aR :=
  proofConsF_eq (inp := R.prfInF (const (unary 0)) lX lA lAx lBx
      (R.qIn lam mu sigma n V qx qy aR bR)) rfl rfl (nF_lpIn rfl qx qy aR bR _ _ hu hv)
    (fun X => ptsF_getD rfl lX qx _ rfl rfl (R.hLM lam mu sigma n) X) _ (R.circ_wf _)
    (R.circ_wires lam mu sigma n V _) (R.circ_inputs' lam mu sigma n V _)
    (R.circ_size' lam mu sigma n V _) rfl rfl

/-- **The proof check of the second question**, an oracle point question, on the processor's
input. -/
theorem proof_lY (qx qy : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) (aR bR : BitStr)
    {u v : Role × LIDT.CL.Ty} (hu : typeOf arGraph qx = some u)
    (hv : typeOf arGraph qy = some v) :
    proofConsF (R.prfInF nAF lY lB lAy lBy (R.qIn lam mu sigma n V qx qy aR bR)) =
      proofCons ((R.fam lam mu sigma).j n) (R.d lam mu sigma n) (R.L lam mu sigma n)
        (R.hLM lam mu sigma n)
        (len ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
          (R.L lam mu sigma n) u + len ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
          (R.d lam mu sigma n) (R.L lam mu sigma n) v)
        (len ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
          (R.L lam mu sigma n) u)
        (circOf (R.L lam mu sigma n) V n (R.circ lam mu sigma n V) (R.circ_wires lam mu sigma n V)
          (rolePart ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (V.sampler.dim n)
            (pull Function.Embedding.inr qy)))
        ((regs ((R.fam lam mu sigma).j n)).ptOf (ldPart ((R.fam lam mu sigma).t n)
          ((R.fam lam mu sigma).ht n) ((R.fam lam mu sigma).j n) (V.sampler.dim n)
          (pull Function.Embedding.inr qy))) bR :=
  proofConsF_eq (inp := R.prfInF nAF lY lB lAy lBy (R.qIn lam mu sigma n V qx qy aR bR))
    rfl (nAF_lpIn rfl qx qy aR bR _ _ hu) (nF_lpIn rfl qx qy aR bR _ _ hu hv)
    (fun X => ptsF_getD rfl lY qy _ rfl rfl (R.hLM lam mu sigma n) X) _
    (R.circ_wf _) (R.circ_wires lam mu sigma n V _) (R.circ_inputs' lam mu sigma n V _)
    (R.circ_size' lam mu sigma n V _) rfl rfl

theorem lpPost_eq (qx qy : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) (aR bR : BitStr)
    {ℓ' : ℕ} (P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) ℓ') (B : ℕ) :
    R.lpPost (R.qIn lam mu sigma n V qx qy aR bR) =
      (arPresented (R.d lam mu sigma n) ((R.fam lam mu sigma).dvd n) ((R.fam lam mu sigma).sel n)
        (R.L lam mu sigma n) (R.hLM lam mu sigma n) V n (R.circ lam mu sigma n V)
        (R.circ_wires lam mu sigma n V) P B).cons qx qy aR bR := by
  unfold arPresented presented TypedData.detype
  dsimp only
  rw [edgeOf_eq_selectedEdge]
  have he := edgeF_lpIn (R.params lam mu sigma n) qx qy aR bR
    (toBits ((V.sampler.cl n .alice).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qx))),
      toBits ((V.sampler.cl n .bob).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qx))),
      toBits ((V.sampler.cl n .alice).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qy))),
      toBits ((V.sampler.cl n .bob).eval (rolePart ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (V.sampler.dim n) (pull Function.Embedding.inr qy))))
    (V.progs, (lam, mu, sigma), n)
  simp only [lpPost, PolyTimeFun.ite_apply, choose_apply]
  rw [he]
  cases hs : DeciderProgram.selectedEdge arGraph (pull Function.Embedding.inl qx)
      (pull Function.Embedding.inl qy) with
  | none => simp
  | some uv =>
    obtain ⟨u, v⟩ := uv
    have hed : edgeOf arGraph qx qy =
        some ((u, pull Function.Embedding.inr qx), (v, pull Function.Embedding.inr qy)) := by
      rw [edgeOf_eq_selectedEdge, hs]; rfl
    obtain ⟨hu, hv, -, -⟩ := TypedData.typeOf_of_edgeOf arGraph hed
    dsimp only [Option.map_some]
    have hok : lenOkF (R.qIn lam mu sigma n V qx qy aR bR) =
        decide (aR.length = lenR _ _ _ (R.L lam mu sigma n) u ∧
          bR.length = lenR _ _ _ (R.L lam mu sigma n) v) :=
      lenOkF_lpIn _ qx qy aR bR _ _ rfl hu hv
    rw [hok]
    simp only [tdata, cons]
    by_cases hl : aR.length = lenR ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n)
        (R.d lam mu sigma n) (R.L lam mu sigma n) u ∧ bR.length = lenR ((R.fam lam mu sigma).t n)
        ((R.fam lam mu sigma).j n) (R.d lam mu sigma n) (R.L lam mu sigma n) v
    · rw [ite_eq_left (by simpa using hl), ite_eq_left hl]
      simp only [consBranchF, ap₂_apply, append_apply]
      congr 1; congr 1; congr 1; congr 1; congr 1
      · split_ifs with h
        · exact (congrArg ldConsF.toFun (ldInF_lpIn rfl qx qy aR bR _ _ hu hv)).trans
            (ldConsF_eq _ (LdFamily.sel_chi _ n) _ _ _ _ _ _ _)
        · rfl
      · split_ifs with h
        · exact (congrArg consConsF.toFun (ccInF_lpIn rfl qx qy aR bR _ _ hu hv)).trans
            (consConsF_eq _ _ _ _ _ _ _ _)
        · rfl
      · exact (congrArg indConsF.toFun (indInF_lX rfl qx qy aR bR _ _ hu hv)).trans
          (indConsF_eq _ (LdFamily.sel_chi _ n) (R.hLM lam mu sigma n) _ _ _ _ _ _ _)
      · exact (congrArg indConsF.toFun (indInF_lY rfl qx qy aR bR _ _ hu hv)).trans
          (indConsF_eq _ (LdFamily.sel_chi _ n) (R.hLM lam mu sigma n) _ _ _ _ _ _ _)
      · split_ifs with h
        · subst h
          exact R.proof_lX lam mu sigma n V qx qy aR bR hu hv
        · rfl
      · split_ifs with h
        · subst h
          exact R.proof_lY lam mu sigma n V qx qy aR bR hu hv
        · rfl
    · rw [ite_eq_right (by simpa using hl), ite_eq_right hl]
      rfl

end Correct

end ArRoutine


end MIPRE.Tailored.AnsRed.Typed

end
