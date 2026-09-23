/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.DecideProg
import MIPRE.Background.AnswerReduction.ArSampler

/-!
# The typed answer-reduced decider

Piece AR-3e of `planning/answer-reduction.md`, concluded: the decider of the typed answer-reduced
verifier as a total `CL.TypedDecider` over the types `Role × PcpTy`, whose acceptance law is the
typed predicate `typedPred` of `MIPRE/Background/AnswerReduction/TypedGame` with the game check
`gameCheck` (`accepts_iff`).

The decider is `hardcode core (S̄, D̄, λ, μ, σ)`, one fixed program with the input programs and the
parameters as data. On a typed input `(n, u, x, v, y, a, b)` it runs eight stages, each keeping
its input as context:

1. the PCP parameters `pd n`, by the parameter routine of the sampler (`ParRoutine.core`);
2. `Q = (λn + 1)^μ` and `T = 2^{(Q + 5)(μ + 1)}` (`ParRoutine.budCore`);
3. to 6. the input sampler's full marginals `L^𝖠 x_O`, `L^𝖡 x_O`, `L^𝖠 y_O`, `L^𝖡 y_O` of the
   oracle halves of the two questions, through the universal machine;
7. and 8. the PCP verifier of `PD` on each question's game-check view;

and decides by the program `verdictP` of `MIPRE/Background/AnswerReduction/DecideProg` on what
it read. Unlike the oracularized decider it never runs the input decider, whose program only
enters the PCP verifier's input as data, and every stage halts on every input: the parsing
stages are total, the input sampler halts on every input (`Sampler.halts`), and the PCP
verifier runs on the encoding of a genuine input. So no clock is needed (`total`).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine

/-! ## Stages -/

/-- A stage: run `p` on an argument read off the context, and keep the context. -/
def stg (arg : PolyTimeFun Data Data) (p : Prog) : Prog :=
  stageProg (ap₂ treePair arg (PolyTimeFun.id Data)) p postKeep

theorem stg_closed (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1) :
    (stg arg p).WellScoped 1 :=
  stageProg_closed _ hp _

theorem stg_runs (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1) (X r : Data)
    (h : ∃ t, p.Runs (arg X) r t) : ∃ t, (stg arg p).Runs X (.cons r X) t := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', h'⟩ := stageProg_runs (ap₂ treePair arg (PolyTimeFun.id Data)) hp postKeep X
    (arg X) X r t (by simp) ht
  exact ⟨t', by simpa [postKeep, stg] using h'⟩

/-! ## Reading the context -/

/-- The context `k` stages back. -/
def tails : ℕ → PolyTimeFun Data Data
  | 0 => PolyTimeFun.id Data
  | k + 1 => (tails k).comp treeTail

@[simp] theorem tails_zero (d : Data) : tails 0 d = d := rfl

@[simp] theorem tails_cons (k : ℕ) (a d : Data) : tails (k + 1) (.cons a d) = tails k d := by
  simp [tails, treeTail_cons]

theorem tails_closed_comp {α : Type*} [SizedEncoding α] (f : PolyTimeFun Data α) (k : ℕ)
    (d : Data) : (f.comp (tails k)) d = f (tails k d) := rfl

/-- The result of the stage `k` stages back. -/
def res (k : ℕ) : PolyTimeFun Data Data := treeHead.comp (tails k)

/-- The input tuple and the hardcoded data, after `j` stages. -/
def hdat (j : ℕ) : PolyTimeFun Data Data := treeHead.comp (tails j)
def inp (j i : ℕ) : PolyTimeFun Data Data := treeHead.comp ((tails i).comp (treeTail.comp (tails j)))
def inpLast (j : ℕ) : PolyTimeFun Data Data := (tails 6).comp (treeTail.comp (tails j))

def spD (j : ℕ) : PolyTimeFun Data Data := treeHead.comp (hdat j)
def dpD (j : ℕ) : PolyTimeFun Data Data := treeHead.comp (treeTail.comp (hdat j))
def lmsD (j : ℕ) : PolyTimeFun Data Data := treeTail.comp (treeTail.comp (hdat j))

/-- The first `|x| - d` bits: the oracle half. -/
def leftBP : PolyTimeFun (BitStr × Unary) BitStr :=
  reverse.comp (drop.comp ((reverse.comp fst).pair snd))

/-- The last `d` bits: the PCP half. -/
def rightBP : PolyTimeFun (BitStr × Unary) BitStr :=
  reverse.comp (take.comp ((reverse.comp fst).pair snd))

theorem leftBP_apply (l : BitStr) (d : Unary) : leftBP (l, d) = l.take (l.length - d.length) := by
  simp only [leftBP, comp_apply, pair_apply, fst_apply, snd_apply, reverse_apply, drop_apply]
  rw [List.drop_reverse]; simp

theorem rightBP_apply (l : BitStr) (d : Unary) : rightBP (l, d) = l.drop (l.length - d.length) := by
  simp only [rightBP, comp_apply, pair_apply, fst_apply, snd_apply, reverse_apply, take_apply]
  rw [List.take_reverse]; simp

/-- The runs of blocks of a PCP half: `(k, m', z) ↦ blocksOf k m' z`. -/
def blocksOfP : PolyTimeFun (Unary × Unary × BitStr) Blocks :=
  let n := ap₂ append (fst.comp snd) (ap₂ append (fst.comp snd) (const (unary 6)))
  let l := Introspection.BinaryBlock.splitBlocksProg.comp (n.pair (fst.pair (snd.comp snd)))
  (take.comp (l.pair (fst.comp snd))).pair ((take.comp ((drop.comp (l.pair (fst.comp snd))).pair
    (fst.comp snd))).pair (drop.comp ((drop.comp (l.pair (fst.comp snd))).pair (fst.comp snd))))

@[simp] theorem blocksOfP_apply (k m' : Unary) (z : BitStr) :
    blocksOfP (k, m', z) = blocksOf k m' z := by
  simp only [blocksOfP, blocksOf, pair_apply, comp_apply, take_apply, drop_apply, ap₂_apply,
    append_apply, const_apply, fst_apply, snd_apply,
    Introspection.BinaryBlock.splitBlocksProg_apply, List.length_append, length_unary]

/-! ## The stages -/

instance : Inhabited LIDT.CL.Ty := ⟨.point⟩

section Stages

variable (PD : PcpDecider) (ℓ : ℕ)

/-- The PCP parameters `pd`, the width `k` and `m'`, after `j` stages (`j ≥ 1`). -/
def pdD (j : ℕ) : PolyTimeFun Data Data := res (j - 1)
def kD (j : ℕ) : PolyTimeFun Data Unary := readU.comp (treeHead.comp (pdD j))
def m'D (j : ℕ) : PolyTimeFun Data Unary := readU.comp (treeHead.comp (treeTail.comp (pdD j)))

/-- The bits of the question in the input's field `i` (`2` or `4`), after `j` stages. -/
def qBits (j i : ℕ) : PolyTimeFun Data BitStr := readBits.comp (inp j i)

/-- Its oracle half. -/
def oBits (j i : ℕ) : PolyTimeFun Data BitStr :=
  leftBP.comp ((qBits j i).pair (dimProg.comp (pdD j)))

/-- Its PCP half, in runs of blocks. -/
def pBlocks (j i : ℕ) : PolyTimeFun Data Blocks :=
  blocksOfP.comp ((kD j).pair ((m'D j).pair (rightBP.comp ((qBits j i).pair
    (dimProg.comp (pdD j))))))

/-- Stage 1's argument: `((λ, μ, σ), n)`. -/
def argPar (j : ℕ) : PolyTimeFun Data Data := ap₂ treePair (lmsD j) (inp j 0)

/-- A marginal call's argument, after `j` stages: the input sampler's program and the query
`(n, marginal w (ℓ + 1) z)` at the oracle half `z` of the question in field `i`. -/
def argMarg (j i : ℕ) (w : Player) : PolyTimeFun Data Data :=
  ap₂ treePair (spD j) (ap₂ treePair (inp j 0) (encoded.comp ((const (1 : ℕ)).pair
    ((const w).pair ((const (ℓ + 1)).pair ((oBits j i).pair (const ([] : BitStr))))))))

/-- The answer blocks of the answer in field `ia`, parsed at the type in field `it`. -/
def aBlocks (j it ia : ℕ) : PolyTimeFun Data (List BitStr) :=
  let m := fst.comp (snd.comp ((SAT.ArrayProg.getD default).comp ((const 0).pair
    ((map readDesc).comp (rawListP.comp (treeTail.comp (treeTail.comp (pdD j))))))))
  snd.comp (parseBP.comp ((kD j).pair ((cntP.comp ((m.pair (m'D j)).pair
    (snd.comp ((readFinite : PolyTimeFun Data ArTy).comp (inp j it))))).pair
    (readBits.comp (if ia = 5 then inp j ia else inpLast j)))))

/-- A game check's argument, after `j` stages (`j = 6, 7`): the PCP verifier's input on the
question in field `i`, the answer in field `ia` and the marginals `rA`, `rB` stages back. -/
def argVer (j i it ia rA rB : ℕ) : PolyTimeFun Data Data :=
  let qt := res (j - 2)
  let nat (f : PolyTimeFun Data Data) := encoded.comp (readNat.comp f)
  let bits (f : PolyTimeFun Data Data) := encoded.comp (readBits.comp f)
  ap₂ treePair (ap₂ treePair
      (ap₂ treePair (dpD j) (ap₂ treePair (nat (inp j 0)) (ap₂ treePair (nat (treeTail.comp qt))
        (ap₂ treePair (nat (treeHead.comp qt)) (nat (treeTail.comp (treeTail.comp (lmsD j))))))))
      (ap₂ treePair (bits (res rA)) (bits (res rB))))
    (ap₂ treePair (encoded.comp (fst.comp (pBlocks j i))) (encoded.comp (aBlocks j it ia)))

/-- The verdict's reader, after the eight stages. -/
def readV : PolyTimeFun Data VerdictIn :=
  let descs := (map readDesc).comp (rawListP.comp (treeTail.comp (treeTail.comp (pdD 8))))
  ((kD 8).pair ((m'D 8).pair descs)).pair
    (((rawTruthProg.comp (res 1)).pair (rawTruthProg.comp (res 0))).pair
      ((((readFinite : PolyTimeFun Data ArTy).comp (inp 8 1)).pair
        ((readFinite : PolyTimeFun Data ArTy).comp (inp 8 3))).pair
        (((pBlocks 8 2).pair (pBlocks 8 4)).pair
          ((readBits.comp (inp 8 5)).pair (readBits.comp (inpLast 8))))))

/-- **The core of the answer-reduced decider**, on `((S̄, D̄, λ, μ, σ), (n, u, x, v, y, a, b))`. -/
def core : Prog :=
  seqProg (stg (argPar 0) (ParRoutine.core PD)) <|
  seqProg (stg (argPar 1) budCore) <|
  seqProg (stg (argMarg ℓ 2 2 .alice) selfUniversal.univ) <|
  seqProg (stg (argMarg ℓ 3 2 .bob) selfUniversal.univ) <|
  seqProg (stg (argMarg ℓ 4 4 .alice) selfUniversal.univ) <|
  seqProg (stg (argMarg ℓ 5 4 .bob) selfUniversal.univ) <|
  seqProg (stg (argVer 6 2 1 5 3 2) PD.verify.code) <|
  seqProg (stg (argVer 7 4 3 6 2 1) PD.verify.code) (verdictP.comp readV).code

theorem core_closed : (core PD ℓ).WellScoped 1 := by
  have hu := selfUniversal.closed
  have hv := PD.verify.closed
  exact seqProg_closed (stg_closed _ (ParRoutine.core_closed PD)) <|
    seqProg_closed (stg_closed _ budCore_closed) <|
    seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
    seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
    seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) (PolyTimeFun.closed _)

end Stages

/-! ## The run -/

section Run

variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)

/-- The core's input. -/
def ctx0 : Data := .cons (encode (sp, dp, lam, mu, sigma)) (encode (n, u, x, v, y, a, b))

/-- The width of the PCP half at index `n`. -/
abbrev dB : Unary := unary (pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k)

theorem dimProg_pd' : dimProg ((family PD lam mu sigma).pd n) = dB PD lam mu sigma n := by
  have h := (family PD lam mu sigma).dimProg_pd n
  rw [← unary_length (dimProg _), h]
  rfl

/-- A marginal query at the oracle half of `z`. -/
def margQ (w : Player) (z : BitStr) : Data :=
  .cons (encode sp) (encode (n, Sampler.Query.marginal w (ℓ + 1)
    (leftBP (z, dB PD lam mu sigma n))))

variable (rxA rxB ryA ryB : Data)

/-- The PCP half of a question, in runs of blocks. -/
def pBl (z : BitStr) : Blocks :=
  blocksOf (unary (arPar PD lam mu sigma n).k) (unary (arPar PD lam mu sigma n).m')
    (rightBP (z, dB PD lam mu sigma n))

/-- The parse of an answer into blocks, at a type. -/
def aBl (t : ArTy) (s : BitStr) : List BitStr :=
  (parseBP (unary (arPar PD lam mu sigma n).k, unary (cntB (arPar PD lam mu sigma n).m
    (arPar PD lam mu sigma n).m' t.2), s)).2

/-- A game check's verdict. -/
def chkV (rA rB : Data) (z : BitStr) (t : ArTy) (s : BitStr) : Bool :=
  PD.verify (pcpInput dp n (tPcp lam mu n) (arQ lam mu n) sigma
    (readBits rA) (readBits rB) (pBl PD lam mu sigma n z).1 (aBl PD lam mu sigma n t s))

/-- The contexts after each stage. -/
def ctx1 : Data := .cons ((family PD lam mu sigma).pd n) (ctx0 sp dp lam mu sigma n u v x y a b)
def ctx2 : Data := .cons (encode (arQ lam mu n, tPcp lam mu n))
  (ctx1 PD sp dp lam mu sigma n u v x y a b)
def ctx6 : Data := .cons ryB (.cons ryA (.cons rxB (.cons rxA
  (ctx2 PD sp dp lam mu sigma n u v x y a b))))
def ctx7 : Data := .cons (encode (chkV PD dp lam mu sigma n rxA rxB x u a))
  (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)
def ctx8 : Data := .cons (encode (chkV PD dp lam mu sigma n ryA ryB y v b))
  (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)

theorem pd_heads : readU (treeHead ((family PD lam mu sigma).pd n)) =
      unary (arPar PD lam mu sigma n).k ∧
    readU (treeHead (treeTail ((family PD lam mu sigma).pd n))) =
      unary (arPar PD lam mu sigma n).m' ∧
    (rawListP (treeTail (treeTail ((family PD lam mu sigma).pd n)))).map readDesc =
      List.ofFn ((family PD lam mu sigma).desc n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [PcpFamily.pd, encode_prod, treeHead_cons, readU_encode]; rfl
  · simp only [PcpFamily.pd, encode_prod, treeHead_cons, treeTail_cons, readU_encode]; rfl
  · simp only [PcpFamily.pd, encode_prod, treeTail_cons, rawListP, ofEncodeEq_apply,
      rawList_encode, List.map_map]
    conv_rhs => rw [← List.map_id (List.ofFn _)]
    apply List.map_congr_left
    intro d _
    exact readDesc_encode d

theorem descs_m : ((List.ofFn ((family PD lam mu sigma).desc n)).getD 0 default).2.1 =
    unary (arPar PD lam mu sigma n).m := by
  rw [show (0 : ℕ) = ((0 : Fin 6) : ℕ) from rfl, getD_desc, PcpFamily.desc_lt _ _ 0 (by decide)]
  rfl

theorem argPar_zero : argPar 0 (ctx0 sp dp lam mu sigma n u v x y a b) =
    .cons (encode (lam, mu, sigma)) (encode n) := by
  simp [argPar, lmsD, hdat, inp, ctx0, encode_prod]

theorem argPar_one : argPar 1 (ctx1 PD sp dp lam mu sigma n u v x y a b) =
    .cons (encode (lam, mu, sigma)) (encode n) := by
  simp [argPar, lmsD, hdat, inp, ctx1, ctx0, encode_prod]

theorem pdD_eq {j : ℕ} (d : Data) (h : pdD j d = (family PD lam mu sigma).pd n) :
    kD j d = unary (arPar PD lam mu sigma n).k ∧ m'D j d = unary (arPar PD lam mu sigma n).m' ∧
      dimProg (pdD j d) = dB PD lam mu sigma n := by
  obtain ⟨h1, h2, -⟩ := pd_heads PD lam mu sigma n
  simp only [kD, m'D, comp_apply, h, h1, h2, dimProg_pd', and_self]

theorem margArg_eq (j i : ℕ) (w : Player) (d : Data) (z : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (hsp : spD j d = encode sp)
    (hn : inp j 0 d = encode n) (hz : inp j i d = encode z) :
    argMarg ℓ j i w d = margQ PD ℓ sp lam mu sigma n w z := by
  obtain ⟨-, -, hdim⟩ := pdD_eq PD lam mu sigma n d hpd
  simp only [argMarg, oBits, qBits, ap₂_apply, treePair_apply, comp_apply, pair_apply,
    const_apply, encoded_apply, hsp, hn, hz, readBits_encode, hdim, margQ, encode_prod]
  rfl

theorem aBlocks_eq (j it ia : ℕ) (d : Data) (t : ArTy) (s : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (ht : inp j it d = encode t)
    (hs : (if ia = 5 then inp j ia else inpLast j) d = encode s) :
    aBlocks j it ia d = aBl PD lam mu sigma n t s := by
  obtain ⟨hk, -, -⟩ := pdD_eq PD lam mu sigma n d hpd
  obtain ⟨-, hm', hds⟩ := pd_heads PD lam mu sigma n
  have hs' : readBits ((if ia = 5 then inp j ia else inpLast j) d) = s := by
    rw [hs, readBits_encode]
  simp only [aBlocks, comp_apply, pair_apply, snd_apply, fst_apply, const_apply, hk,
    SAT.ArrayProg.getD_apply, map_apply, hpd, hds, descs_m, ht, readFinite_encode, cntP_apply,
    length_unary, hs', aBl]
  simp only [m'D, comp_apply, hpd, hm', length_unary]

theorem pBlocks_eq (j i : ℕ) (d : Data) (z : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (hz : inp j i d = encode z) :
    pBlocks j i d = pBl PD lam mu sigma n z := by
  obtain ⟨hk, hm', hdim⟩ := pdD_eq PD lam mu sigma n d hpd
  simp only [pBlocks, comp_apply, pair_apply, hk, hm', qBits, hz, readBits_encode, hdim,
    blocksOfP_apply, pBl]

theorem argVer_eq (j i it ia rA rB : ℕ) (d RA RB : Data) (z : BitStr) (t : ArTy) (s : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (hdp : dpD j d = encode dp)
    (hn : inp j 0 d = encode n)
    (hqt : res (j - 2) d = encode (arQ lam mu n, tPcp lam mu n))
    (hσ : treeTail (treeTail (lmsD j d)) = encode sigma) (hA : res rA d = RA) (hB : res rB d = RB)
    (hz : inp j i d = encode z) (ht : inp j it d = encode t)
    (hs : (if ia = 5 then inp j ia else inpLast j) d = encode s) :
    argVer j i it ia rA rB d = encode (pcpInput dp n (tPcp lam mu n)
      (arQ lam mu n) sigma (readBits RA) (readBits RB) (pBl PD lam mu sigma n z).1
      (aBl PD lam mu sigma n t s)) := by
  rw [argVer]
  simp only [ap₂_apply, treePair_apply, comp_apply, encoded_apply, hdp, hn, hqt, hσ, hA, hB,
    readNat_encode, encode_prod, treeHead_cons, treeTail_cons,
    pBlocks_eq PD lam mu sigma n j i d z hpd hz, aBlocks_eq PD lam mu sigma n j it ia d t s hpd ht hs,
    fst_apply, pcpInput]

theorem ctx6_reads :
    pdD 6 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = (family PD lam mu sigma).pd n ∧
    dpD 6 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode dp ∧
    inp 6 0 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode n ∧
    res 4 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
      encode (arQ lam mu n, tPcp lam mu n) ∧
    treeTail (treeTail (lmsD 6 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB))) =
      encode sigma ∧
    res 3 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = rxA ∧
    res 2 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = rxB ∧
    inp 6 2 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode x ∧
    inp 6 1 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode u ∧
    (if (5 : ℕ) = 5 then inp 6 5 else inpLast 6)
      (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode a := by
  simp [pdD, res, dpD, hdat, inp, lmsD, ctx6, ctx2, ctx1, ctx0, encode_prod]

theorem ctx7_reads :
    pdD 7 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = (family PD lam mu sigma).pd n ∧
    dpD 7 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode dp ∧
    inp 7 0 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode n ∧
    res 5 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
      encode (arQ lam mu n, tPcp lam mu n) ∧
    treeTail (treeTail (lmsD 7 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB))) =
      encode sigma ∧
    res 2 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = ryA ∧
    res 1 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = ryB ∧
    inp 7 4 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode y ∧
    inp 7 3 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode v ∧
    (if (6 : ℕ) = 5 then inp 7 6 else inpLast 7)
      (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode b := by
  simp [pdD, res, dpD, hdat, inp, inpLast, lmsD, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod]

theorem readV_ctx8 : readV (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
    ((unary (arPar PD lam mu sigma n).k, unary (arPar PD lam mu sigma n).m',
      List.ofFn ((family PD lam mu sigma).desc n)),
      (chkV PD dp lam mu sigma n rxA rxB x u a, chkV PD dp lam mu sigma n ryA ryB y v b), (u, v),
      (pBl PD lam mu sigma n x, pBl PD lam mu sigma n y), (a, b)) := by
  have hpd : pdD 8 (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
      (family PD lam mu sigma).pd n := by
    simp [pdD, res, ctx8, ctx7, ctx6, ctx2, ctx1]
  obtain ⟨hk, hm', -⟩ := pdD_eq PD lam mu sigma n _ hpd
  obtain ⟨-, -, hds⟩ := pd_heads PD lam mu sigma n
  have hx : inp 8 2 (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode x := by
    simp [inp, ctx8, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod]
  have hy : inp 8 4 (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode y := by
    simp [inp, ctx8, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod]
  simp only [readV, pair_apply, comp_apply, hk, hm', map_apply, hpd, hds,
    pBlocks_eq PD lam mu sigma n 8 2 _ x hpd hx, pBlocks_eq PD lam mu sigma n 8 4 _ y hpd hy]
  simp only [res, inp, inpLast, ctx8, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod, comp_apply,
    tails_cons, tails_zero, treeHead_cons, treeTail_cons, readFinite_encode, rawTruthProg_encode_bool,
    readBits_encode]

/-- **The core's run**, given the input sampler's four runs. -/
theorem core_runs
    (hxA : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .alice x) rxA t)
    (hxB : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .bob x) rxB t)
    (hyA : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .alice y) ryA t)
    (hyB : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .bob y) ryB t) :
    ∃ t, (core PD ℓ).Runs (ctx0 sp dp lam mu sigma n u v x y a b)
      (encode (verdictP (readV (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)))) t := by
  have hu := selfUniversal.closed
  have hv := PD.verify.closed
  set X0 := ctx0 sp dp lam mu sigma n u v x y a b
  set X2 := ctx2 PD sp dp lam mu sigma n u v x y a b
  have r1 := stg_runs (argPar 0) (ParRoutine.core_closed PD) X0 _
    (by rw [argPar_zero]; exact parCore_runs PD lam mu sigma n)
  have r2 := stg_runs (argPar 1) budCore_closed (ctx1 PD sp dp lam mu sigma n u v x y a b) _
    (by rw [argPar_one]; exact budCore_runs lam mu sigma n)
  have r3 := stg_runs (argMarg ℓ 2 2 .alice) hu X2 rxA (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 2 2 .alice X2 x (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hxA)
  have r4 := stg_runs (argMarg ℓ 3 2 .bob) hu (.cons rxA X2) rxB (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 3 2 .bob _ x (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hxB)
  have r5 := stg_runs (argMarg ℓ 4 4 .alice) hu (.cons rxB (.cons rxA X2)) ryA (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 4 4 .alice _ y (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hyA)
  have r6 := stg_runs (argMarg ℓ 5 4 .bob) hu (.cons ryA (.cons rxB (.cons rxA X2))) ryB (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 5 4 .bob _ y (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hyB)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ :=
    ctx6_reads PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB
  have r7 := stg_runs (argVer 6 2 1 5 3 2) hv (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB
    ryA ryB) (encode (chkV PD dp lam mu sigma n rxA rxB x u a)) (by
      rw [argVer_eq PD dp lam mu sigma n 6 2 1 5 3 2 _ rxA rxB x u a e1 e2 e3 e4 e5 e6 e7 e8 e9 e10]
      obtain ⟨t, -, ht⟩ := PD.verify.computes (pcpInput dp n (tPcp lam mu n)
        (arQ lam mu n) sigma (readBits rxA) (readBits rxB) (pBl PD lam mu sigma n x).1
        (aBl PD lam mu sigma n u a))
      exact ⟨t, ht⟩)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ :=
    ctx7_reads PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB
  have r8 := stg_runs (argVer 7 4 3 6 2 1) hv (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB
    ryA ryB) (encode (chkV PD dp lam mu sigma n ryA ryB y v b)) (by
      rw [argVer_eq PD dp lam mu sigma n 7 4 3 6 2 1 _ ryA ryB y v b f1 f2 f3 f4 f5 f6 f7 f8 f9 f10]
      obtain ⟨t, -, ht⟩ := PD.verify.computes (pcpInput dp n (tPcp lam mu n)
        (arQ lam mu n) sigma (readBits ryA) (readBits ryB) (pBl PD lam mu sigma n y).1
        (aBl PD lam mu sigma n v b))
      exact ⟨t, ht⟩)
  obtain ⟨t9, -, r9⟩ := (verdictP.comp readV).computes
    (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)
  have hc := PolyTimeFun.closed (verdictP.comp readV)
  exact seq_runs (seqProg_closed (stg_closed _ budCore_closed) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r1 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r2 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hv) <|
      seqProg_closed (stg_closed _ hv) hc) r3 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r4 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hv) <|
      seqProg_closed (stg_closed _ hv) hc) r5 <|
    seq_runs (seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r6 <|
    seq_runs (seqProg_closed (stg_closed _ hv) hc) r7 <|
    seq_runs hc r8 ⟨t9, r9⟩

end Run

/-! ## The typed decider and its acceptance law -/

section Law

variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)

/-- **The typed answer-reduced decider** of `V` at the parameters `(λ, μ, σ)`. -/
def typedDecider : CL.Detyping.TypedDecider ArTy where
  prog := hardcode (core PD ℓ) (encode (V.sampler.prog, V.decider.prog, lam, mu, sigma))
  closed := hardcode_wellScoped (core_closed PD ℓ) _

variable (n : ℕ)

local notation "F" => family PD lam mu sigma

theorem leftBP_toBits (z : Fin (dim V n ((F).par n)) → 𝔽₂) :
    leftBP (toBits z, dB PD lam mu sigma n) = toBits (oraclePart V n ((F).par n) z) := by
  rw [leftBP_apply, length_toBits, length_unary, oraclePart, ← take_toBits]
  congr 1
  simp [dim, family]

theorem rightBP_toBits (z : Fin (dim V n ((F).par n)) → 𝔽₂) :
    rightBP (toBits z, dB PD lam mu sigma n) =
      flatBits ((F).par n) ((F).hk n) (pcpPart V n ((F).par n) ((F).hk n) z) := by
  rw [rightBP_apply, length_toBits, length_unary, pcpPart, ← toBits_pcp]
  simp only [LinearEquiv.apply_symm_apply]
  rw [show dim V n ((F).par n) - pcpDim (arPar PD lam mu sigma n) *
      (arPar PD lam mu sigma n).k = V.sampler.dim n by simp [dim, family], drop_toBits]

theorem pBl_toBits (z : Fin (dim V n ((F).par n)) → 𝔽₂) :
    pBl PD lam mu sigma n (toBits z) =
      blocksV ((F).hk n) ((F).par n) (pcpPart V n ((F).par n) ((F).hk n) z) := by
  rw [pBl, show arPar PD lam mu sigma n = (F).par n from rfl, rightBP_toBits,
    blocksOf_flatBits]
  rfl

/-- The input sampler's full marginal at the oracle half, in bits. -/
theorem margBits_oracle (w : Player) (z : Fin (dim V n ((F).par n)) → 𝔽₂) :
    OracleDecider.margBits V.sampler n (ℓ + 1) w (toBits (oraclePart V n ((F).par n) z)) =
      toBits ((V.sampler.cl n w).eval (oraclePart V n ((F).par n) z)) := by
  simp [OracleDecider.margBits]

/-- The input sampler's runs on the marginal queries at a question's oracle half. -/
theorem margQ_runs (w : Player) (z : Fin (dim V n ((F).par n)) → 𝔽₂) :
    ∃ t, selfUniversal.univ.Runs (margQ PD ℓ V.sampler.prog lam mu sigma n w (toBits z))
      (encode (toBits ((V.sampler.cl n w).eval (oraclePart V n ((F).par n) z)))) t := by
  rw [margQ, leftBP_toBits, ← margBits_oracle]
  exact OracleDecider.univ_marginal V.sampler n (ℓ + 1) (by omega) le_rfl w _ (length_toBits _)

/-- The game check of the typed game at index `n`. -/
abbrev chk : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin ((F).par n).m' → Fq ((F).par n) ((F).hk n)) →
    (Fin (((F).par n).m' + 6) → Fq ((F).par n) ((F).hk n)) → Bool :=
  gameCheck V n ((F).par n) ((F).hk n) PD V.decider.prog (tPcp lam mu n)
    (arQ lam mu n) sigma

/-- **The game check's verdict is the game check**, on a parsed `Point_6` answer. -/
theorem chkV_eq (t : ArTy) (z : Fin (dim V n ((F).par n)) → 𝔽₂) (s : BitStr)
    (u' : Ans ((F).par n) (Fq ((F).par n) ((F).hk n)))
    (hs : parse (fld ((F).par n) ((F).hk n)) t.2 s = some u') (ht : chkPlan t = true) :
    chkV PD V.decider.prog lam mu sigma n
        (encode (toBits ((V.sampler.cl n .alice).eval (oraclePart V n ((F).par n) z))))
        (encode (toBits ((V.sampler.cl n .bob).eval (oraclePart V n ((F).par n) z)))) (toBits z) t s =
      chk PD V lam mu sigma n (oraclePart V n ((F).par n) z)
        ((regs6 ((F).par n)).ptOf (pcpPart V n ((F).par n) ((F).hk n) z)) (vals6 u') := by
  simp only [chkPlan, decide_eq_true_eq] at ht
  obtain ⟨-, h5, hpt⟩ := ht
  have hfmt := ansFmt_of_parse _ hs
  rw [parse_eq] at hs
  rcases hA : parseB ((F).par n).k (cnt ((F).par n) t.2) s with _ | A <;> rw [hA] at hs
  · cases hs
  obtain ⟨hAl, hAw⟩ := parseB_spec hA
  simp only [Option.map_some, Option.some.injEq] at hs
  have hAu : ansB ((F).hk n) u' = A := by rw [← hs]; exact ansB_ofElems _ _ A hAl hAw
  have ht2 : t.2 = (t.2.1, .point) := by rw [← hpt]
  rw [ht2] at hfmt
  obtain ⟨av, -, hav, hv6, -⟩ := ansB_val6 ((F).hk n) h5 hfmt
  have hbl : aBl PD lam mu sigma n t s = (fld ((F).par n) ((F).hk n)).vecBits (vals6 u') := by
    have := (parseBP_apply (unary (arPar PD lam mu sigma n).k)
      (unary (cntB (arPar PD lam mu sigma n).m (arPar PD lam mu sigma n).m' t.2)) s).2 A
    simp only [length_unary, ← cnt_eq] at this
    rw [aBl, (parseBP_apply _ _ _).1, this hA, ← hAu, hav, hv6]
  simp only [chkV, readBits_encode, hbl, pBl_toBits, blocksV, chk, gameCheck]
  rfl

/-- **The acceptance law**: on questions of the typed game and any answers, the typed
answer-reduced decider accepts exactly when the typed predicate does. -/
theorem accepts_iff (u v : ArTy) (x y : Fin (dim V n ((F).par n)) → 𝔽₂) {B : ℕ}
    (a b : Verifier.Answers B) :
    (typedDecider PD V lam mu sigma).Accepts n u (toBits x) v (toBits y) a.1 b.1 ↔
      typedPred V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n)
        (chk PD V lam mu sigma n) B (u, x) (v, y) a b = true := by
  set rxA := encode (toBits ((V.sampler.cl n .alice).eval (oraclePart V n ((F).par n) x)))
  set rxB := encode (toBits ((V.sampler.cl n .bob).eval (oraclePart V n ((F).par n) x)))
  set ryA := encode (toBits ((V.sampler.cl n .alice).eval (oraclePart V n ((F).par n) y)))
  set ryB := encode (toBits ((V.sampler.cl n .bob).eval (oraclePart V n ((F).par n) y)))
  obtain ⟨t, hrun⟩ := core_runs PD ℓ V.sampler.prog V.decider.prog lam mu sigma n u v (toBits x)
    (toBits y) a.1 b.1 rxA rxB ryA ryB (margQ_runs PD V lam mu sigma n .alice x)
    (margQ_runs PD V lam mu sigma n .bob x) (margQ_runs PD V lam mu sigma n .alice y)
    (margQ_runs PD V lam mu sigma n .bob y)
  have hverdict : verdictP (readV (ctx8 PD V.sampler.prog V.decider.prog lam mu sigma n u v
      (toBits x) (toBits y) a.1 b.1 rxA rxB ryA ryB)) =
      typedPred V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n)
        (chk PD V lam mu sigma n) B (u, x) (v, y) a b := by
    rw [readV_ctx8, verdictP_apply, pBl_toBits, pBl_toBits]
    refine (verdictB_eq (F) n (chk PD V lam mu sigma n)
      (u, oraclePart V n ((F).par n) x, pcpPart V n ((F).par n) ((F).hk n) x)
      (v, oraclePart V n ((F).par n) y, pcpPart V n ((F).par n) ((F).hk n) y) a.1 b.1 _ _
      (fun u' hu' hp => chkV_eq PD V lam mu sigma n u x a.1 u' hu' hp)
      (fun v' hv' hq => chkV_eq PD V lam mu sigma n v y b.1 v' hv' hq)).trans ?_
    unfold typedPred
    rcases parse (fld ((F).par n) ((F).hk n)) u.2 a.1 with _ | u' <;>
      rcases parse (fld ((F).par n) ((F).hk n)) v.2 b.1 with _ | v' <;> rfl
  rw [← hverdict]
  constructor
  · rintro ⟨time, hr⟩
    obtain ⟨t', -, hr'⟩ := hardcode_time_rev (core_closed PD ℓ) hr
    have := (Eval.deterministic hr' hrun).1
    exact (encode_injective this).symm
  · intro h
    rw [h] at hrun
    exact ⟨_, hardcode_time (core_closed PD ℓ) hrun⟩

/-! ## Totality -/

theorem argMarg_general (j i : ℕ) (w : Player) (d : Data) (hsp : spD j d = encode V.sampler.prog)
    (hn : inp j 0 d = encode n) :
    argMarg ℓ j i w d = .cons (encode V.sampler.prog) (.cons (encode n)
      (encode ((1 : ℕ), w, ℓ + 1, oBits j i d, ([] : BitStr)))) := by
  simp only [argMarg, ap₂_apply, treePair_apply, comp_apply, pair_apply, const_apply,
    encoded_apply, hsp, hn]

theorem argVer_general (j i it ia rA rB : ℕ) (d : Data) (hdp : dpD j d = encode V.decider.prog) :
    argVer j i it ia rA rB d = encode (pcpInput V.decider.prog (readNat (inp j 0 d))
      (readNat (treeTail (res (j - 2) d))) (readNat (treeHead (res (j - 2) d)))
      (readNat (treeTail (treeTail (lmsD j d)))) (readBits (res rA d)) (readBits (res rB d))
      (pBlocks j i d).1 (aBlocks j it ia d)) := by
  rw [argVer]
  simp only [ap₂_apply, treePair_apply, comp_apply, encoded_apply, hdp, fst_apply, pcpInput,
    encode_prod]

/-- A marginal call halts, whatever its query. -/
theorem univ_marg_halts (q : Data) :
    ∃ r t, selfUniversal.univ.Runs (.cons (encode V.sampler.prog) (.cons (encode n) q)) r t := by
  obtain ⟨r, t, h⟩ := V.sampler.halts n q
  obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
  exact ⟨r, t', h'⟩

/-- **The typed answer-reduced decider halts on every input** `(n, …)`. -/
theorem total : (typedDecider PD V lam mu sigma).Total := by
  intro n d
  have hu := selfUniversal.closed
  have hv := PD.verify.closed
  set H : Data := encode (V.sampler.prog, V.decider.prog, lam, mu, sigma)
  set X0 : Data := .cons H (.cons (encode n) d)
  have r1 := stg_runs (argPar 0) (ParRoutine.core_closed PD) X0 _ (by
    rw [show argPar 0 X0 = .cons (encode (lam, mu, sigma)) (encode n) by
      simp [argPar, lmsD, hdat, inp, X0, H, encode_prod]]
    exact parCore_runs PD lam mu sigma n)
  set X1 : Data := .cons ((family PD lam mu sigma).pd n) X0
  have r2 := stg_runs (argPar 1) budCore_closed X1 _ (by
    rw [show argPar 1 X1 = .cons (encode (lam, mu, sigma)) (encode n) by
      simp [argPar, lmsD, hdat, inp, X1, X0, H, encode_prod]]
    exact budCore_runs lam mu sigma n)
  set X2 : Data := .cons (encode (arQ lam mu n, tPcp lam mu n)) X1
  obtain ⟨q3, e3⟩ : ∃ q, argMarg ℓ 2 2 .alice X2 = .cons (encode V.sampler.prog) (.cons (encode n) q) :=
    ⟨_, argMarg_general V n 2 2 .alice X2 (by simp [spD, hdat, X2, X1, X0, H, encode_prod])
      (by simp [inp, X2, X1, X0])⟩
  obtain ⟨rxA, t3, h3⟩ := univ_marg_halts V n q3
  have r3 := stg_runs (argMarg ℓ 2 2 .alice) hu X2 rxA (by rw [e3]; exact ⟨t3, h3⟩)
  set X3 : Data := .cons rxA X2
  obtain ⟨q4, e4⟩ : ∃ q, argMarg ℓ 3 2 .bob X3 = .cons (encode V.sampler.prog) (.cons (encode n) q) :=
    ⟨_, argMarg_general V n 3 2 .bob X3 (by simp [spD, hdat, X3, X2, X1, X0, H, encode_prod])
      (by simp [inp, X3, X2, X1, X0])⟩
  obtain ⟨rxB, t4, h4⟩ := univ_marg_halts V n q4
  have r4 := stg_runs (argMarg ℓ 3 2 .bob) hu X3 rxB (by rw [e4]; exact ⟨t4, h4⟩)
  set X4 : Data := .cons rxB X3
  obtain ⟨q5, e5⟩ : ∃ q, argMarg ℓ 4 4 .alice X4 = .cons (encode V.sampler.prog) (.cons (encode n) q) :=
    ⟨_, argMarg_general V n 4 4 .alice X4 (by simp [spD, hdat, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [inp, X4, X3, X2, X1, X0])⟩
  obtain ⟨ryA, t5, h5⟩ := univ_marg_halts V n q5
  have r5 := stg_runs (argMarg ℓ 4 4 .alice) hu X4 ryA (by rw [e5]; exact ⟨t5, h5⟩)
  set X5 : Data := .cons ryA X4
  obtain ⟨q6, e6⟩ : ∃ q, argMarg ℓ 5 4 .bob X5 = .cons (encode V.sampler.prog) (.cons (encode n) q) :=
    ⟨_, argMarg_general V n 5 4 .bob X5
      (by simp [spD, hdat, X5, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [inp, X5, X4, X3, X2, X1, X0])⟩
  obtain ⟨ryB, t6, h6⟩ := univ_marg_halts V n q6
  have r6 := stg_runs (argMarg ℓ 5 4 .bob) hu X5 ryB (by rw [e6]; exact ⟨t6, h6⟩)
  set X6 : Data := .cons ryB X5
  obtain ⟨c7, e7⟩ : ∃ c : PcpInput, argVer 6 2 1 5 3 2 X6 = encode c :=
    ⟨_, argVer_general V 6 2 1 5 3 2 X6
      (by simp [dpD, hdat, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])⟩
  have r7 := stg_runs (argVer 6 2 1 5 3 2) hv X6 _ (by
    rw [e7]; obtain ⟨t, -, h⟩ := PD.verify.computes c7; exact ⟨t, h⟩)
  set X7 : Data := .cons (encode (PD.verify c7)) X6
  obtain ⟨c8, e8⟩ : ∃ c : PcpInput, argVer 7 4 3 6 2 1 X7 = encode c :=
    ⟨_, argVer_general V 7 4 3 6 2 1 X7
      (by simp [dpD, hdat, X7, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])⟩
  have r8 := stg_runs (argVer 7 4 3 6 2 1) hv X7 _ (by
    rw [e8]; obtain ⟨t, -, h⟩ := PD.verify.computes c8; exact ⟨t, h⟩)
  obtain ⟨t9, -, r9⟩ := (verdictP.comp readV).computes (.cons (encode (PD.verify c8)) X7)
  have hc := PolyTimeFun.closed (verdictP.comp readV)
  obtain ⟨t, h⟩ := seq_runs (seqProg_closed (stg_closed _ budCore_closed) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r1 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r2 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hv) <|
      seqProg_closed (stg_closed _ hv) hc) r3 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r4 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hv) <|
      seqProg_closed (stg_closed _ hv) hc) r5 <|
    seq_runs (seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r6 <|
    seq_runs (seqProg_closed (stg_closed _ hv) hc) r7 <|
    seq_runs hc r8 ⟨t9, r9⟩
  exact ⟨_, _, hardcode_time (core_closed PD ℓ) h⟩

end Law

end MIPRE.AnswerReduction
