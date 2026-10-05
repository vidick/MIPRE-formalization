/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.LenProg
public import MIPRE.Tailored.Repeat.LpLists

@[expose] public section

/-!
# The repeated linear-constraints processor

The linear-constraints processor of the repeated tailored verifier (issue #280, P2b), on
`(n, x, y, a^R, b^R)`, with the input sampler `S̄`, calculator `L̄` and processor `P̄` and the
parameters `(λ, τ)` stored:

1. the dimension `s` and `k = k(n)` in unary, as the calculator does;
2. cut `x` and `y` into their `k` blocks, and run `L̄` on both kinds of every block of both;
3. from the lengths, cut `a^R` and `b^R` into the coordinates' readable answers, and run `P̄`
   on `(n, xᵢ, yᵢ, a^R_i, b^R_i)` for every coordinate;
4. output every coordinate's constraints, padded to all the variables (`padWithL`, which is
   `TailoredGame.padCons`).
-/

namespace MIPRE.Tailored.RepProg

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL Calls Polynomial

/-! ## The stages -/

/-- The stored data of the processor: `(S̄, L̄, P̄, λ, τ)`. -/
abbrev LpPar : Type := Prog × Prog × Prog × ℕ × ℕ

/-- The input of the core: the stored data and `(n, d)`. -/
abbrev LpIn : Type := LpPar × ℕ × Data

/-- Stage 1: the call to `S̄` on the dimension query. -/
noncomputable def lpA : PolyTimeFun LpIn (LpIn × (Prog × List Data)) :=
  (PolyTimeFun.id _).pair ((fst.comp fst).pair (listOf [dimQueryF (fst.comp snd)]))

@[simp] theorem lpA_apply (a : LpIn) :
    lpA a = (a, (a.1.1, [encode (a.2.1, CL.Sampler.Query.dimension)])) := rfl

/-- Stage 2: read the dimension. -/
noncomputable def lpB : PolyTimeFun (LpIn × List Data) (LpIn × ℕ) :=
  fst.pair (Detyping.Program.readNat.comp ((headD Data.nil).comp snd))

@[simp] theorem lpB_apply (p : LpIn × List Data) :
    lpB p = (p.1, Detyping.Program.readNat (p.2.headD .nil)) := rfl

/-- Stage 3: the input of `dimProg` computing `k`. -/
noncomputable def lpC : PolyTimeFun (LpIn × Unary) ((LpIn × Unary) × (ℕ × ℕ × ℕ × ℕ)) :=
  (PolyTimeFun.id _).pair ((const 1).pair
    ((fst.comp (snd.comp (snd.comp (snd.comp fst)))).comp fst |>.pair
    ((fst.comp (snd.comp fst)).pair ((snd.comp (snd.comp (snd.comp (snd.comp fst)))).comp fst))))

@[simp] theorem lpC_apply (a : LpIn) (us : Unary) :
    lpC (a, us) = ((a, us), (1, a.1.2.2.2.1, a.2.1, a.1.2.2.2.2)) := rfl

/-- The four components of the datum `d = (x, y, a^R, b^R)`. -/
noncomputable def readX (d : Data) : BitStr := Detyping.Program.readBits (treeHead d)

noncomputable def readY (d : Data) : BitStr := Detyping.Program.readBits (treeHead (treeTail d))

noncomputable def readAR (d : Data) : BitStr :=
  Detyping.Program.readBits (treeHead (treeTail (treeTail d)))

noncomputable def readBR (d : Data) : BitStr :=
  Detyping.Program.readBits (treeTail (treeTail (treeTail d)))

theorem read_encode (x y aR bR : BitStr) :
    readX (encode (x, y, aR, bR)) = x ∧ readY (encode (x, y, aR, bR)) = y ∧
      readAR (encode (x, y, aR, bR)) = aR ∧ readBR (encode (x, y, aR, bR)) = bR := by
  simp [readX, readY, readAR, readBR, encode_prod, Detyping.Program.readBits_encode]

noncomputable def readXF : PolyTimeFun Data BitStr :=
  Detyping.Program.readBits.comp treeHead

noncomputable def readYF : PolyTimeFun Data BitStr :=
  Detyping.Program.readBits.comp (treeHead.comp treeTail)

noncomputable def readARF : PolyTimeFun Data BitStr :=
  Detyping.Program.readBits.comp (treeHead.comp (treeTail.comp treeTail))

noncomputable def readBRF : PolyTimeFun Data BitStr :=
  Detyping.Program.readBits.comp (treeTail.comp (treeTail.comp treeTail))

/-- The state after `k` in unary: `((a, s), k)`. -/
abbrev LpSt : Type := (LpIn × Unary) × Unary

/-- The blocks of `x` and of `y` at a state. -/
noncomputable def blocksX (st : LpSt) : List BitStr :=
  blocks (readX st.1.1.2.2) st.1.2.length st.2.length

noncomputable def blocksY (st : LpSt) : List BitStr :=
  blocks (readY st.1.1.2.2) st.1.2.length st.2.length

noncomputable def blocksXF : PolyTimeFun LpSt (List BitStr) :=
  congr (blocksF.comp (((readXF.comp (snd.comp (snd.comp (fst.comp fst)))).pair (snd.comp fst)).pair
    snd)) blocksX (by intro st; simp [blocksX, readX, readXF])

@[simp] theorem blocksXF_apply (st : LpSt) : blocksXF st = blocksX st := congr_apply _ _ _ _

noncomputable def blocksYF : PolyTimeFun LpSt (List BitStr) :=
  congr (blocksF.comp (((readYF.comp (snd.comp (snd.comp (fst.comp fst)))).pair (snd.comp fst)).pair
    snd)) blocksY (by intro st; simp [blocksY, readY, readYF])

@[simp] theorem blocksYF_apply (st : LpSt) : blocksYF st = blocksY st := congr_apply _ _ _ _

/-- The length queries: every block of `x` at both kinds, then every block of `y`. -/
noncomputable def lpLenQs (st : LpSt) : List Data :=
  lenQueries st.1.1.2.1 (blocksX st) ++ lenQueries st.1.1.2.1 (blocksY st)

/-- The length queries at a list of blocks, in polynomial time. -/
noncomputable def lenQueriesF : PolyTimeFun (List BitStr × ℕ) (List Data) :=
  congr (append.comp ((mapWith (lenQueryF false)).pair (mapWith (lenQueryF true))))
    (fun p => lenQueries p.2 p.1) (by rintro ⟨bl, n⟩; simp [lenQueries])

@[simp] theorem lenQueriesF_apply (p : List BitStr × ℕ) : lenQueriesF p = lenQueries p.2 p.1 :=
  congr_apply _ _ _ _

/-- Stage 4: the queries to `L̄`. -/
noncomputable def lpD : PolyTimeFun LpSt (LpSt × (Prog × List Data)) :=
  congr ((PolyTimeFun.id _).pair ((fst.comp (snd.comp (fst.comp (fst.comp fst)))).pair
    (append.comp ((lenQueriesF.comp (blocksXF.pair (fst.comp (snd.comp (fst.comp fst))))).pair
      (lenQueriesF.comp (blocksYF.pair (fst.comp (snd.comp (fst.comp fst)))))))))
    (fun st => (st, (st.1.1.1.2.1, lpLenQs st))) (by intro st; simp [lpLenQs])

@[simp] theorem lpD_apply (st : LpSt) : lpD st = (st, (st.1.1.1.2.1, lpLenQs st)) :=
  congr_apply _ _ _ _

/-! ## From the lengths to the queries to the processor -/

/-- The lengths, in unary, of a list of outputs of the calculator. -/
def lensOf (rs : List Data) : List Unary :=
  rs.map fun r => unary (Detyping.Program.rawList r).length

noncomputable def lensOfF : PolyTimeFun (List Data) (List Unary) :=
  congr (map (length.comp (ofEncodeEq Detyping.Program.rawList Detyping.Program.encode_rawList)))
    lensOf (by intro rs; simp [lensOf])

/-- The `j`-th quarter of the results, `k` each. -/
def quarter (rs : List Data) (k j : ℕ) : List Data := (rs.drop (j * k)).take k

/-- The twelve lengths of every coordinate, from the results of the calls to `L̄`. -/
def lpPads (rs : List Data) (k : ℕ) : List (List Unary) :=
  padData (lensOf (quarter rs k 0)) (lensOf (quarter rs k 1)) (lensOf (quarter rs k 2))
    (lensOf (quarter rs k 3))

/-- The query to `P̄` at a coordinate: its blocks and its readable answers. -/
def lpQuery (n : ℕ) (aR bR : BitStr) (q : (BitStr × BitStr) × List Unary) : Data :=
  encode (n, q.1.1, q.1.2, (aR.drop (q.2.getD 0 []).length).take (q.2.getD 1 []).length,
    (bR.drop (q.2.getD 6 []).length).take (q.2.getD 7 []).length)

/-- The queries to `P̄`. -/
def lpQueries (n : ℕ) (bx by' : List BitStr) (aR bR : BitStr) (pads : List (List Unary)) :
    List Data :=
  ((bx.zip by').zip pads).map (lpQuery n aR bR)

/-- `j` blocks of `k` dropped. -/
noncomputable def dropTimesF : ℕ → PolyTimeFun (List Data × Unary) (List Data)
  | 0 => fst
  | j + 1 => drop.comp ((dropTimesF j).pair snd)

theorem dropTimesF_apply (rs : List Data) (uk : Unary) :
    ∀ j, dropTimesF j (rs, uk) = rs.drop (j * uk.length)
  | 0 => by simp [dropTimesF]
  | j + 1 => by
    simp only [dropTimesF, comp_apply, pair_apply, snd_apply, drop_apply, dropTimesF_apply rs uk j,
      List.drop_drop]
    congr 1
    ring

noncomputable def quarterF (j : ℕ) : PolyTimeFun (List Data × Unary) (List Data) :=
  congr (take.comp ((dropTimesF j).pair snd)) (fun p => quarter p.1 p.2.length j) (by
    rintro ⟨rs, uk⟩; simp [quarter, dropTimesF_apply])

@[simp] theorem quarterF_apply (j : ℕ) (p : List Data × Unary) :
    quarterF j p = quarter p.1 p.2.length j := congr_apply _ _ _ _

/-- The concatenation of the four triples of a coordinate. -/
noncomputable def concat4F :
    PolyTimeFun ((List Unary × List Unary) × (List Unary × List Unary)) (List Unary) :=
  append.comp ((append.comp ((fst.comp fst).pair (snd.comp fst))).pair
    (append.comp ((fst.comp snd).pair (snd.comp snd))))

noncomputable def lpPadsF : PolyTimeFun (List Data × Unary) (List (List Unary)) :=
  congr ((map concat4F).comp (zip.comp
    ((zip.comp ((triplesF.comp (lensOfF.comp (quarterF 0))).pair
      (triplesF.comp (lensOfF.comp (quarterF 1))))).pair
    (zip.comp ((triplesF.comp (lensOfF.comp (quarterF 2))).pair
      (triplesF.comp (lensOfF.comp (quarterF 3))))))))
    (fun p => lpPads p.1 p.2.length) (by
      rintro ⟨rs, uk⟩
      simp [lpPads, padData, lensOfF, concat4F, List.append_assoc])

@[simp] theorem lpPadsF_apply (p : List Data × Unary) : lpPadsF p = lpPads p.1 p.2.length :=
  congr_apply _ _ _ _

/-- The query to `P̄` at a coordinate, in polynomial time. -/
noncomputable def lpQueryF :
    PolyTimeFun (((BitStr × BitStr) × List Unary) × (ℕ × BitStr × BitStr)) Data :=
  congr (Detyping.Program.encoded.comp ((fst.comp snd).pair ((fst.comp (fst.comp fst)).pair
    ((snd.comp (fst.comp fst)).pair
      ((take.comp ((drop.comp ((fst.comp (snd.comp snd)).pair ((nthD [] 0).comp (snd.comp fst)))).pair
        ((nthD [] 1).comp (snd.comp fst)))).pair
      (take.comp ((drop.comp ((snd.comp (snd.comp snd)).pair ((nthD [] 6).comp (snd.comp fst)))).pair
        ((nthD [] 7).comp (snd.comp fst)))))))))
    (fun p => lpQuery p.2.1 p.2.2.1 p.2.2.2 p.1) (by
      rintro ⟨q, n, aR, bR⟩; simp [lpQuery])

/-- The queries to `P̄`, in polynomial time. -/
noncomputable def lpQueriesF :
    PolyTimeFun (((List BitStr × List BitStr) × List (List Unary)) × (ℕ × BitStr × BitStr))
      (List Data) :=
  congr ((mapWith lpQueryF).comp ((zip.comp ((zip.comp (fst.comp fst)).pair (snd.comp fst))).pair
    snd))
    (fun p => lpQueries p.2.1 p.1.1.1 p.1.1.2 p.2.2.1 p.2.2.2 p.1.2) (by
      rintro ⟨⟨⟨bx, by'⟩, pads⟩, n, aR, bR⟩
      simp [lpQueries, lpQueryF])

@[simp] theorem lpQueriesF_apply
    (p : ((List BitStr × List BitStr) × List (List Unary)) × (ℕ × BitStr × BitStr)) :
    lpQueriesF p = lpQueries p.2.1 p.1.1.1 p.1.1.2 p.2.2.1 p.2.2.2 p.1.2 := congr_apply _ _ _ _

/-- The queries to `P̄` at a state and the results of the calls to `L̄`. -/
noncomputable def lpPQs (st : LpSt) (rs : List Data) : List Data :=
  lpQueries st.1.1.2.1 (blocksX st) (blocksY st) (readAR st.1.1.2.2) (readBR st.1.1.2.2)
    (lpPads rs st.2.length)

/-- Projections of `(st, rs)`. -/
noncomputable def ppF : PolyTimeFun (LpSt × List Data) Prog :=
  fst.comp (snd.comp (snd.comp (fst.comp (fst.comp (fst.comp fst)))))

noncomputable def nF : PolyTimeFun (LpSt × List Data) ℕ :=
  fst.comp (snd.comp (fst.comp (fst.comp fst)))

noncomputable def dF : PolyTimeFun (LpSt × List Data) Data :=
  snd.comp (snd.comp (fst.comp (fst.comp fst)))

noncomputable def padsF : PolyTimeFun (LpSt × List Data) (List (List Unary)) :=
  lpPadsF.comp (snd.pair (snd.comp fst))

/-- Stage 5: the queries to `P̄`; the context is the twelve lengths of every coordinate. -/
noncomputable def lpE : PolyTimeFun (LpSt × List Data) (List (List Unary) × (Prog × List Data)) :=
  congr (padsF.pair (ppF.pair (lpQueriesF.comp
      ((((blocksXF.comp fst).pair (blocksYF.comp fst)).pair padsF).pair
        (nF.pair ((readARF.comp dF).pair (readBRF.comp dF)))))))
    (fun p => (lpPads p.2 p.1.2.length, (p.1.1.1.1.2.2.1, lpPQs p.1 p.2))) (by
      rintro ⟨st, rs⟩
      simp [lpPQs, readAR, readBR, readARF, readBRF, ppF, nF, dF, padsF])

@[simp] theorem lpE_apply (p : LpSt × List Data) :
    lpE p = (lpPads p.2 p.1.2.length, (p.1.1.1.1.2.2.1, lpPQs p.1 p.2)) := congr_apply _ _ _ _

theorem readBits_eq_bitsD (d : Data) : Detyping.Program.readBits d = bitsD d := by
  change (Detyping.Program.rawList d).map Detyping.Program.rawTruth = (spineList d).map bitD
  rw [rawList_eq_spineList]
  congr 1

/-- The output: every coordinate's constraints, padded. -/
def lpOut (pads : List (List Unary)) (rs : List Data) : List BitStr :=
  ((pads.zip rs).map fun q => (bitsListD q.2).map (padWithL q.1)).flatten

/-- `bitsListD`, in polynomial time. -/
noncomputable def bitsListDF : PolyTimeFun Data (List BitStr) :=
  congr ((map Detyping.Program.readBits).comp
      (ofEncodeEq Detyping.Program.rawList Detyping.Program.encode_rawList))
    bitsListD (by
      intro d
      simp only [comp_apply, map_apply, ofEncodeEq_apply, bitsListD, rawList_eq_spineList]
      exact List.map_congr_left fun d _ => readBits_eq_bitsD d)

@[simp] theorem bitsListDF_apply (d : Data) : bitsListDF d = bitsListD d := congr_apply _ _ _ _

/-- Stage 6: the output. -/
noncomputable def lpF : PolyTimeFun (List (List Unary) × List Data) (List BitStr) :=
  congr (flattenF.comp ((map ((mapWith padWithF).comp ((bitsListDF.comp snd).pair fst))).comp zip))
    (fun p => lpOut p.1 p.2) (by
      rintro ⟨pads, rs⟩
      simp only [comp_apply, flattenF_apply, map_apply, zip_apply, lpOut]
      congr 1)

@[simp] theorem lpF_apply (p : List (List Unary) × List Data) : lpF p = lpOut p.1 p.2 :=
  congr_apply _ _ _ _

/-! ## The program -/

/-- **The core of the repeated linear-constraints processor**, on `((S̄, L̄, P̄, λ, τ), (n, d))`. -/
noncomputable def lpCore (univ : Prog) : Prog :=
  seq lpA.code (seq (withCtx (mapCall univ)) (seq lpB.code (seq (withCtx toUnaryProg)
    (seq lpC.code (seq (withCtx dimProg) (seq (withCtx toUnaryProg)
      (seq lpD.code (seq (withCtx (mapCall univ)) (seq lpE.code
        (seq (withCtx (mapCall univ)) lpF.code))))))))))

theorem lpCore_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (lpCore univ).WellScoped 1 :=
  seq_wellScoped lpA.closed (seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU))
    (seq_wellScoped lpB.closed (seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped)
      (seq_wellScoped lpC.closed (seq_wellScoped (withCtx_wellScoped dimProg_wellScoped)
        (seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped)
          (seq_wellScoped lpD.closed (seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU))
            (seq_wellScoped lpE.closed (seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU))
              lpF.closed))))))))))

/-! ## The run -/

/-- The state after the first stages: `((a, s), k)`. -/
abbrev lpSt (sp lp pp : Prog) (lam tau n : ℕ) (d : Data) (s : ℕ) : LpSt :=
  (((((sp, lp, pp, lam, tau) : LpPar), n, d), unary s), unary (Repetition.reps lam tau n))

/-- The cost of the core, stage by stage, with the dimension query of cost at most `Td`, the
calls to `L̄` of cost at most `T₁` with bound `Z₁` on the second loop, and the calls to `P̄` of
cost at most `T₂` with bound `Z₂` on the third. -/
noncomputable def lpCoreCost (sp lp pp : Prog) (lam tau n : ℕ) (d : Data) (s Td T₁ Z₁ T₂ Z₂ : ℕ)
    (rs₁ rs₂ : List Data) : ℕ :=
  let a : LpIn := ((sp, lp, pp, lam, tau), n, d)
  let qd : Data := encode (n, CL.Sampler.Query.dimension)
  let k := Repetition.reps lam tau n
  let st := lpSt sp lp pp lam tau n d s
  lpA.timeBound.eval (esize a) +
    ((encode a : Data).size + (Data.cons (encode sp) (list [qd])).size +
      mapCallCost 1 Td (encode sp : Data).size
        ((list [qd]).size + (list [(encode s : Data)]).size + 1) + 5) +
    lpB.timeBound.eval (esize (a, [(encode s : Data)])) +
    ((encode a : Data).size + (encode s : Data).size + toUnaryCost s + 5) +
    lpC.timeBound.eval (esize (a, unary s)) +
    ((encode (a, unary s) : Data).size + (encode ((1 : ℕ), lam, n, tau) : Data).size +
      (dimCost tau (Nat.size lam + Nat.size n) (esize lam) (esize n) (esize (1 : ℕ)) + 3) + 5) +
    ((encode (a, unary s) : Data).size + (encode k : Data).size + toUnaryCost k + 5) +
    lpD.timeBound.eval (esize st) +
    ((encode st : Data).size + (Data.cons (encode lp) (list (lpLenQs st))).size +
      mapCallCost (lpLenQs st).length T₁ (encode lp : Data).size Z₁ + 5) +
    lpE.timeBound.eval (esize (st, rs₁)) +
    ((encode (lpPads rs₁ k) : Data).size + (Data.cons (encode pp) (list (lpPQs st rs₁))).size +
      mapCallCost (lpPQs st rs₁).length T₂ (encode pp : Data).size Z₂ + 5) +
    lpF.timeBound.eval (esize (lpPads rs₁ k, rs₂)) + 11

/-- **The run of the core**, from runs of the calls: the dimension query answered by `s`, the
calls to `L̄` by `f₁` and the calls to `P̄` by `f₂`. -/
theorem lpCore_runsLe {univ : Prog} (hU : univ.WellScoped 1) (sp lp pp : Prog) (lam tau n : ℕ)
    (d : Data) (s : ℕ) {Td : ℕ}
    (hdim : RunsLe univ (.cons (encode sp) (encode (n, CL.Sampler.Query.dimension))) (encode s) Td)
    (f₁ f₂ : Data → Data) (T₁ Z₁ T₂ Z₂ : ℕ)
    (hf₁ : ∀ q ∈ lpLenQs (lpSt sp lp pp lam tau n d s), RunsLe univ (.cons (encode lp) q) (f₁ q) T₁)
    (hZ₁ : (list (lpLenQs (lpSt sp lp pp lam tau n d s))).size +
      (list ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)).size + 1 ≤ Z₁)
    (hf₂ : ∀ q ∈ lpPQs (lpSt sp lp pp lam tau n d s) ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁),
      RunsLe univ (.cons (encode pp) q) (f₂ q) T₂)
    (hZ₂ : (list (lpPQs (lpSt sp lp pp lam tau n d s)
        ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁))).size +
      (list ((lpPQs (lpSt sp lp pp lam tau n d s)
        ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)).map f₂)).size + 1 ≤ Z₂) :
    RunsLe (lpCore univ) (encode (((sp, lp, pp, lam, tau) : LpPar), n, d))
      (encode (lpOut (lpPads ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)
          (Repetition.reps lam tau n))
        ((lpPQs (lpSt sp lp pp lam tau n d s)
          ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)).map f₂)))
      (lpCoreCost sp lp pp lam tau n d s Td T₁ Z₁ T₂ Z₂
        ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)
        ((lpPQs (lpSt sp lp pp lam tau n d s)
          ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)).map f₂)) := by
  have h1 := RunsLe.withCtx (mapCall_wellScoped hU) (encode (((sp, lp, pp, lam, tau) : LpPar), n, d))
    (RunsLe.mapCall hU (encode sp) [encode (n, CL.Sampler.Query.dimension)] (fun _ => encode s) Td
      _ (by simpa using hdim) le_rfl)
  obtain ⟨tu, htu, hu⟩ := toUnaryProg_runs s
  have h2 := RunsLe.withCtx toUnaryProg_wellScoped (encode (((sp, lp, pp, lam, tau) : LpPar), n, d))
    ⟨tu, htu, hu⟩
  rw [← encode_unary] at h2
  obtain ⟨tk, htk, hk⟩ := Repeat.dimProg_runs_encode lam tau n 1
  rw [mul_one] at hk
  have h3 := RunsLe.withCtx dimProg_wellScoped
    (encode (((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn), unary s))
    (p := dimProg) (b := encode ((1 : ℕ), lam, n, tau)) ⟨tk, htk, hk⟩
  obtain ⟨tu', htu', hu'⟩ := toUnaryProg_runs (Repetition.reps lam tau n)
  have h4 := RunsLe.withCtx toUnaryProg_wellScoped
    (encode (((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn), unary s)) ⟨tu', htu', hu'⟩
  rw [← encode_unary] at h4
  have h5 := RunsLe.withCtx (mapCall_wellScoped hU) (encode (lpSt sp lp pp lam tau n d s))
    (RunsLe.mapCall hU (encode lp) _ f₁ T₁ Z₁ hf₁ hZ₁)
  have h6 := RunsLe.withCtx (mapCall_wellScoped hU)
    (encode (lpPads ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁) (Repetition.reps lam tau n)))
    (RunsLe.mapCall hU (encode pp) _ f₂ T₂ Z₂ hf₂ hZ₂)
  have hA := RunsLe.pure lpA (((sp, lp, pp, lam, tau) : LpPar), n, d)
  have hB := RunsLe.pure lpB ((((sp, lp, pp, lam, tau) : LpPar), n, d), [(encode s : Data)])
  have hC := RunsLe.pure lpC ((((sp, lp, pp, lam, tau) : LpPar), n, d), unary s)
  have hD := RunsLe.pure lpD (lpSt sp lp pp lam tau n d s)
  have hE := RunsLe.pure lpE (lpSt sp lp pp lam tau n d s,
    (lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)
  have hF := RunsLe.pure lpF (lpPads ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)
      (Repetition.reps lam tau n),
    (lpPQs (lpSt sp lp pp lam tau n d s) ((lpLenQs (lpSt sp lp pp lam tau n d s)).map f₁)).map f₂)
  simp only [lpA_apply, lpB_apply, lpC_apply, lpD_apply, lpE_apply, lpF_apply, encode_prod,
    encode_list_data, Detyping.Program.readNat_encode, List.headD_cons, length_unary]
    at hA hB hC hD hE hF
  simp only [encode_prod, encode_list_data, List.map_cons, List.map_nil] at h1 h2 h3 h4 h5 h6
  have wF := lpF.closed
  have w11 := withCtx_wellScoped (mapCall_wellScoped hU)
  have w10 := seq_wellScoped w11 wF
  have w9 := seq_wellScoped lpE.closed w10
  have w8 := seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU)) w9
  have w7 := seq_wellScoped lpD.closed w8
  have w6 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w7
  have w5 := seq_wellScoped (withCtx_wellScoped dimProg_wellScoped) w6
  have w4 := seq_wellScoped lpC.closed w5
  have w3 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w4
  have w2 := seq_wellScoped lpB.closed w3
  have w1 := seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU)) w2
  have c11 := RunsLe.seq wF h6 hF
  have c10 := RunsLe.seq w10 hE c11
  have c9 := RunsLe.seq w9 h5 c10
  have c8 := RunsLe.seq w8 hD c9
  have c7 := RunsLe.seq w7 h4 c8
  have c6 := RunsLe.seq w6 h3 c7
  have c5 := RunsLe.seq w5 hC c6
  have c4 := RunsLe.seq w4 h2 c5
  have c3 := RunsLe.seq w3 hB c4
  have c2 := RunsLe.seq w2 h1 c3
  have c1 := RunsLe.seq w1 hA c2
  simp only [encode_prod, encode_list_data]
  refine c1.mono ?_
  unfold lpCoreCost
  simp only [List.length_singleton, encode_prod, encode_list_data, List.map_cons, List.map_nil,
    toUnaryCost]
  omega

/-- **Inversion of the core**: when the dimension query is answered by `s`, a halting run ran
`L̄` on every length query and `P̄` on every query its results determine, and output the
padded constraints. -/
theorem lpCore_inv {univ : Prog} (hU : univ.WellScoped 1) (sp lp pp : Prog) (lam tau n : ℕ)
    (d : Data) (s : ℕ) {td : ℕ}
    (hdim : univ.Runs (.cons (encode sp) (encode (n, CL.Sampler.Query.dimension))) (encode s) td)
    {r : Data} {t : ℕ}
    (h : (lpCore univ).Runs (encode (((sp, lp, pp, lam, tau) : LpPar), n, d)) r t) :
    ∃ rs₁ rs₂ : List Data,
      List.Forall₂ (fun q r => ∃ t', univ.Runs (.cons (encode lp) q) r t')
        (lpLenQs (lpSt sp lp pp lam tau n d s)) rs₁ ∧
      List.Forall₂ (fun q r => ∃ t', univ.Runs (.cons (encode pp) q) r t')
        (lpPQs (lpSt sp lp pp lam tau n d s) rs₁) rs₂ ∧
      r = encode (lpOut (lpPads rs₁ (Repetition.reps lam tau n)) rs₂) := by
  have wF := lpF.closed
  have w11 := withCtx_wellScoped (mapCall_wellScoped hU)
  have w10 := seq_wellScoped w11 wF
  have w9 := seq_wellScoped lpE.closed w10
  have w8 := seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU)) w9
  have w7 := seq_wellScoped lpD.closed w8
  have w6 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w7
  have w5 := seq_wellScoped (withCtx_wellScoped dimProg_wellScoped) w6
  have w4 := seq_wellScoped lpC.closed w5
  have w3 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w4
  have w2 := seq_wellScoped lpB.closed w3
  have w1 := seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU)) w2
  -- the dimension query
  obtain ⟨t₁, h⟩ := seq_pure_inv lpA w1 _ h
  simp only [lpA_apply, encode_prod, encode_list_data] at h
  obtain ⟨v, s₀, t₂, e₀, hm, h⟩ := seq_inv w2 h
  obtain ⟨r₁, tm, -, hm₁, rfl⟩ := withCtx_inv (mapCall_wellScoped hU) hm
  obtain ⟨rs₀, hrs₀, rfl⟩ := mapCall_inv hU _ _ hm₁
  obtain ⟨r₀, ⟨td', hd⟩, hnil⟩ : ∃ r₀, (∃ t', univ.Runs (.cons (encode sp)
      (encode (n, CL.Sampler.Query.dimension))) r₀ t') ∧ rs₀ = [r₀] := by
    rcases hrs₀ with _ | ⟨h₀, hrest⟩
    cases hrest
    exact ⟨_, h₀, rfl⟩
  subst hnil
  obtain ⟨rfl, -⟩ := Eval.deterministic hd hdim
  -- the dimension and `k` in unary
  obtain ⟨t₃, h⟩ := seq_pure_inv lpB w3 ((((sp, lp, pp, lam, tau) : LpPar), n, d),
    [(encode s : Data)]) h
  simp only [lpB_apply, Detyping.Program.readNat_encode, List.headD_cons, encode_prod] at h
  obtain ⟨tu, -, hu⟩ := toUnaryProg_runs s
  obtain ⟨t₄, h⟩ := seq_det_inv w4 (withCtx_runs toUnaryProg_wellScoped
    (encode ((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn)) hu) h
  obtain ⟨t₅, h⟩ := seq_pure_inv lpC w5 ((((sp, lp, pp, lam, tau) : LpPar), n, d), unary s)
    (by rw [← encode_unary] at h; exact h)
  simp only [lpC_apply, encode_prod] at h
  obtain ⟨tk, -, hk⟩ := Repeat.dimProg_runs_encode lam tau n 1
  rw [mul_one] at hk
  obtain ⟨t₆, h⟩ := seq_det_inv w6 (withCtx_runs dimProg_wellScoped
    (encode (((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn), unary s))
    (b := encode ((1 : ℕ), lam, n, tau)) hk) (by simpa only [encode_prod] using h)
  obtain ⟨tu', -, hu'⟩ := toUnaryProg_runs (Repetition.reps lam tau n)
  obtain ⟨t₇, h⟩ := seq_det_inv w7 (withCtx_runs toUnaryProg_wellScoped
    (encode (((((sp, lp, pp, lam, tau) : LpPar), n, d) : LpIn), unary s)) hu') h
  -- the calls to `L̄`
  obtain ⟨t₈, h⟩ := seq_pure_inv lpD w8 (lpSt sp lp pp lam tau n d s)
    (by rw [← encode_unary] at h; exact h)
  simp only [lpD_apply, encode_prod, encode_list_data] at h
  obtain ⟨v, s₁, t₉, e₁, hm, h⟩ := seq_inv w9 h
  obtain ⟨r₂, tm₂, -, hm₂, rfl⟩ := withCtx_inv (mapCall_wellScoped hU) hm
  obtain ⟨rs₁, hrs₁, rfl⟩ := mapCall_inv hU _ _ hm₂
  -- the calls to `P̄`
  obtain ⟨t₁₀, h⟩ := seq_pure_inv lpE w10 (lpSt sp lp pp lam tau n d s, rs₁) h
  simp only [lpE_apply, encode_prod, encode_list_data, length_unary] at h
  obtain ⟨v, s₂, t₁₁, e₂, hm, h⟩ := seq_inv wF h
  obtain ⟨r₃, tm₃, -, hm₃, rfl⟩ := withCtx_inv (mapCall_wellScoped hU) hm
  obtain ⟨rs₂, hrs₂, rfl⟩ := mapCall_inv hU _ _ hm₃
  refine ⟨rs₁, rs₂, hrs₁, hrs₂, ?_⟩
  obtain ⟨tF, -, hF⟩ := lpF.computes (lpPads rs₁ (Repetition.reps lam tau n), rs₂)
  have := (Eval.deterministic h hF).1
  simpa using this

end MIPRE.Tailored.RepProg

end
