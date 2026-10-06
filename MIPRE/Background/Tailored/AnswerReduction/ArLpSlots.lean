/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpLd
public import MIPRE.Tailored.AnsRed.SlotIndex

@[expose] public section

/-!
# The consistency and indifference checks, as programs

Slice P4h of `planning/aldous-lyons-track.md`: the constraints of the consistency checks
(`Typed.consCons`) and of the indifference checks (`Typed.indCons`) of the answer-reduced game,
computed by programs from the parameters and the layout of the answers.

* `copyF`: the equations that listed codewords of one answer are listed codewords of the other
  (`copyF_eq`); `consConsF` lists the isolated player's two codewords against the oracle's
  in the same slots, at the positions `idxO` (`consConsF_eq`).
* `indF`: the equations that the coefficients `1, …, d` of the codewords whose blocks miss a
  direction vanish (`indF_eq`), the blocks read off a table of intervals of wires (`ivF`, the
  blocks of `MIPRE.Tailored.AnsRed.Slot.lo`); `indConsF` at an axis-parallel line, in the
  direction its seed selects (`indConsF_eq`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.LowDegree.BinaryPolynomial
  MIPRE.Tailored.Intro MIPRE.AnswerReduction.StageProg

variable {t : ℕ} {ht : 1 ≤ t}

/-! ## Copies of codewords -/

/-- The input of the copy equations: `t`, the number `n` of coefficients, the offsets `oI` and
`oO` of the two answers, `N`, and the copied codewords `(c, o_c)`: the `c`-th codeword of the
first answer is the `o_c`-th of the second. -/
abbrev CopyIn : Type := Unary × Unary × Unary × Unary × Unary × List (Unary × Unary)

/-- **The copy equations**, as a program: at `((c, o_c), e)`, the window of coefficient `e` of the
`c`-th codeword at `oI` plus that of the `o_c`-th at `oO`. -/
def copyF : PolyTimeFun CopyIn (List BitStr) :=
  let inp : PolyTimeFun ((((Unary × Unary) × Unary) × CopyIn) × BitStr) CopyIn := snd.comp fst
  let tU := fst.comp inp
  let nU := fst.comp (snd.comp inp)
  let c := fst.comp (fst.comp (fst.comp fst))
  let oc := snd.comp (fst.comp (fst.comp fst))
  let e := snd.comp (fst.comp fst)
  let off (o : PolyTimeFun ((((Unary × Unary) × Unary) × CopyIn) × BitStr) Unary)
      (i : PolyTimeFun ((((Unary × Unary) × Unary) × CopyIn) × BitStr) Unary) :=
    ap₂ append o (mulU.comp ((ap₂ append (mulU.comp (i.pair nU)) e).pair tU))
  let w (o : PolyTimeFun ((((Unary × Unary) × Unary) × CopyIn) × BitStr) Unary) :=
    windowF.comp (tU.pair (o.pair snd))
  eqsConsF fst (fst.comp (snd.comp (snd.comp (snd.comp snd))))
    (flatMapR (mapR ((fst.comp snd).pair fst) (rangeU.comp (fst.comp (snd.comp snd))))
      (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
    (xorBitsProg.comp ((w (off (fst.comp (snd.comp (snd.comp inp))) c)).pair
      (w (off (fst.comp (snd.comp (snd.comp (snd.comp inp)))) oc))))
    (replicate.comp ((fst.comp snd).pair (const false)))

/-- **The copy program computes the copy equations.** -/
theorem copyF_eq (n oI oO N : ℕ) (cws : List (ℕ × ℕ)) :
    copyF (unary t, unary n, unary oI, unary oO, unary N, cws.map fun p => (unary p.1, unary p.2)) =
      eqsCons t ht (cws.flatMap fun p => (List.range n).map fun e =>
        (fldAt t ht N (oI + (p.1 * n + e) * t) - fldAt t ht N (oO + (p.2 * n + e) * t),
          (0 : Fq t ht))) := by
  have hl : (cws.flatMap fun p => (List.range n).map fun e =>
      ((fldAt t ht N (oI + (p.1 * n + e) * t) - fldAt t ht N (oO + (p.2 * n + e) * t) :
        (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht))) =
      ((cws.map fun p => (unary p.1, unary p.2)).flatMap fun p => (List.range n).map fun e =>
        (p, unary e)).map fun q : (Unary × Unary) × Unary =>
          ((fldAt t ht N (oI + (q.1.1.length * n + q.2.length) * t) -
            fldAt t ht N (oO + (q.1.2.length * n + q.2.length) * t) :
              (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht)) := by
    simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, length_unary]
  rw [hl]
  refine eqsConsF_eq _ _ _ _ _ (t := t) (ht := ht) (N := N) rfl rfl ?_ _ _ ?_ ?_
  · simp only [flatMapR_apply, mapR_apply, comp_apply, fst_apply, snd_apply, pair_apply,
      rangeU_apply, length_unary, List.map_map, Function.comp_def]
  · intro q hq z hz
    obtain ⟨p, hp, hq'⟩ := List.mem_flatMap.1 hq
    obtain ⟨⟨a, b⟩, -, rfl⟩ := List.mem_map.1 hp
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hq'
    simp only [comp_apply, pair_apply, fst_apply, snd_apply, ap₂_apply, mulU_apply, append_unary,
      xorBitsProg_apply, windowF_apply, length_unary]
    rw [window_eq_fldAt (ht := ht) z hz.le, window_eq_fldAt (ht := ht) z hz.le,
      shoupXorBits_correct, LinearMap.sub_apply, CharTwo.sub_eq_add]
  · intro q _
    simp only [comp_apply, pair_apply, fst_apply, snd_apply, replicate_apply, const_apply,
      length_unary, zeros_eq t ht]

/-! ## The consistency checks -/

section ConsCons

variable {L : PcpDims}

/-- **An isolated player's copy equations**: its two codewords against the oracle's in the same
slots, `g_A, g_{La}` at the oracle's positions `0` and `R` for Alice, `g_B, g_{Lb}` at `1` and
`R + 1` for Bob, `R` the oracle's readable count. -/
theorem consEqs_alice (N oI oO n : ℕ) : consEqs (t := t) (ht := ht) L N oI oO n .alice =
    [(0, 0), (1, (rSlots L).length)].flatMap fun p => (List.range n).map fun e =>
      (fldAt t ht N (oI + (p.1 * n + e) * t) - fldAt t ht N (oO + (p.2 * n + e) * t),
        (0 : Fq t ht)) := by
  simp [consEqs, slotsOf_alice, List.finRange_succ, idxO_gLa]

theorem consEqs_bob (N oI oO n : ℕ) : consEqs (t := t) (ht := ht) L N oI oO n .bob =
    [(0, 1), (1, (rSlots L).length + 1)].flatMap fun p => (List.range n).map fun e =>
      (fldAt t ht N (oI + (p.1 * n + e) * t) - fldAt t ht N (oO + (p.2 * n + e) * t),
        (0 : Fq t ht)) := by
  simp [consEqs, slotsOf_bob, List.finRange_succ, idxO_gLb]

end ConsCons

/-- The input of the consistency checks: `t`, the number `n` of coefficients, `Na`, `N`, the
oracle's readable count `R`, and the two roles. -/
abbrev ConsIn : Type := Unary × Unary × Unary × Unary × Unary × (Role × Role)

section ConsBranch

def kT : PolyTimeFun ConsIn Unary := fst
def kN : PolyTimeFun ConsIn Unary := fst.comp snd
def kNa : PolyTimeFun ConsIn Unary := fst.comp (snd.comp snd)
def kNN : PolyTimeFun ConsIn Unary := fst.comp (snd.comp (snd.comp snd))
def kR : PolyTimeFun ConsIn Unary := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def kRoles : PolyTimeFun ConsIn (Role × Role) := snd.comp (snd.comp (snd.comp (snd.comp snd)))

/-- The copied codewords `(0, i₀), (1, R + i₀)`. -/
def cwsF (i₀ : ℕ) : PolyTimeFun ConsIn (List (Unary × Unary)) :=
  PolyTimeFun.cons ((const (unary 0)).pair (const (unary i₀)))
    (PolyTimeFun.cons ((const (unary 1)).pair (ap₂ append kR (const (unary i₀)))) (const []))

/-- The copy equations at offsets `oI`, `oO`. -/
def copyB (oI oO : PolyTimeFun ConsIn Unary) (i₀ : ℕ) : PolyTimeFun ConsIn (List BitStr) :=
  copyF.comp (kT.pair (kN.pair (oI.pair (oO.pair (kNN.pair (cwsF i₀))))))

/-- The branch at a pair of roles. -/
def consBranch : Role × Role → PolyTimeFun ConsIn (List BitStr)
  | (.alice, .oracle) => copyB (const (unary 0)) kNa 0
  | (.bob, .oracle) => copyB (const (unary 0)) kNa 1
  | (.oracle, .alice) => copyB kNa (const (unary 0)) 0
  | (.oracle, .bob) => copyB kNa (const (unary 0)) 1
  | _ => const []

end ConsBranch

/-- **The consistency checks**, as a program, by the pair of roles. -/
def consConsF : PolyTimeFun ConsIn (List BitStr) := choose kRoles consBranch (const [])

/-- **The consistency program computes the consistency checks.** -/
theorem consConsF_eq (j d : ℕ) (L : PcpDims) (Na N : ℕ) (S : LIDT.CL.Ty) (r₁ r₂ : Role) :
    consConsF (unary t, unary (ncoef j d S), unary Na, unary N, unary (rSlots L).length,
      (r₁, r₂)) = consCons t ht j d L Na N S r₁ r₂ := by
  have hcws : ∀ i₀ : ℕ, cwsF i₀ (unary t, unary (ncoef j d S), unary Na, unary N,
      unary (rSlots L).length, (r₁, r₂)) =
      [(0, i₀), (1, (rSlots L).length + i₀)].map fun p => (unary p.1, unary p.2) := by
    intro i₀
    simp [cwsF, kR, unary_append_unary]
  rw [consConsF, choose_apply]
  cases r₁ <;> cases r₂ <;>
    simp only [kRoles, comp_apply, snd_apply, consBranch, copyB, pair_apply, kT, kN, kNa, kNN,
      fst_apply, const_apply, hcws, copyF_eq (ht := ht), consCons, consEqs_alice, consEqs_bob,
      Nat.add_zero]

/-! ## The indifference checks -/

/-- The input of the indifference equations: `t`, `d`, the offset `o` of the answer, `N`, the
direction `i`, and the blocks of the answer's codewords, as intervals `(lo, len)` of wires. -/
abbrev IndIn : Type := Unary × Unary × Unary × Unary × ℕ × List (Unary × Unary)

/-- **The indifference equations**, as a program: for each codeword whose block misses the
direction, the windows of its coefficients `1, …, d`. -/
def indF : PolyTimeFun IndIn (List BitStr) :=
  let ivs : PolyTimeFun IndIn (List (Unary × Unary)) :=
    snd.comp (snd.comp (snd.comp (snd.comp snd)))
  let el : PolyTimeFun ((Unary × (Unary × Unary)) × IndIn) (Unary × (Unary × Unary)) := fst
  let loN := PolyTimeFun.addUnary.comp ((const 0).pair (fst.comp (snd.comp el)))
  let hiN := PolyTimeFun.addUnary.comp (loN.pair (snd.comp (snd.comp el)))
  let iN : PolyTimeFun ((Unary × (Unary × Unary)) × IndIn) ℕ :=
    fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
  let inB := ite (ap₂ PolyTimeFun.leNat loN iN)
    (ite (ap₂ PolyTimeFun.leNat hiN iN) (const false) (const true)) (const false)
  let br := ite inB (const [])
    (mapR ((fst.comp (fst.comp snd)).pair fst) (rangeU.comp (fst.comp (snd.comp snd))))
  let idx := flatMapR br (zip.comp ((rangeU.comp (length.comp ivs)).pair ivs))
  let inp : PolyTimeFun (((Unary × Unary) × IndIn) × BitStr) IndIn := snd.comp fst
  let tU := fst.comp inp
  let off := ap₂ append (fst.comp (snd.comp (snd.comp inp))) (mulU.comp ((ap₂ append
    (mulU.comp ((fst.comp (fst.comp fst)).pair (ap₂ append (fst.comp (snd.comp inp))
      (const (unary 1))))) (ap₂ append (snd.comp (fst.comp fst)) (const (unary 1)))).pair tU))
  eqsConsF fst (fst.comp (snd.comp (snd.comp snd))) idx
    (windowF.comp (tU.pair (off.pair snd))) (replicate.comp ((fst.comp snd).pair (const false)))

/-- **The indifference program computes the indifference equations** of codewords with the
given blocks. -/
theorem indF_eq (d o N i : ℕ) (ivs : List (ℕ × ℕ)) :
    indF (unary t, unary d, unary o, unary N, i, ivs.map fun p => (unary p.1, unary p.2)) =
      eqsCons t ht (((List.range ivs.length).zip ivs).flatMap fun p =>
        if p.2.1 ≤ i ∧ i < p.2.1 + p.2.2 then [] else (List.range d).map fun e =>
          ((fldAt t ht N (o + (p.1 * (d + 1) + (e + 1)) * t) :
            (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht))) := by
  set is := ((List.range ivs.length).zip ivs).flatMap fun p =>
    if p.2.1 ≤ i ∧ i < p.2.1 + p.2.2 then ([] : List (Unary × Unary))
    else (List.range d).map fun e => (unary p.1, unary e) with his
  have hl : (((List.range ivs.length).zip ivs).flatMap fun p =>
      if p.2.1 ≤ i ∧ i < p.2.1 + p.2.2 then [] else (List.range d).map fun e =>
        ((fldAt t ht N (o + (p.1 * (d + 1) + (e + 1)) * t) :
          (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht))) =
      is.map fun q => ((fldAt t ht N (o + (q.1.length * (d + 1) + (q.2.length + 1)) * t) :
        (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht)) := by
    simp only [his, List.map_flatMap]
    refine List.flatMap_congr fun p _ => ?_
    split_ifs <;> simp [length_unary]
  rw [hl]
  refine eqsConsF_eq _ _ _ _ _ (t := t) (ht := ht) (N := N) rfl rfl ?_ _ _ ?_ ?_
  · simp only [flatMapR_apply, comp_apply, pair_apply, snd_apply, zip_apply,
      rangeU_apply, length_apply, length_unary, List.length_map, his]
    rw [← List.map_id (List.range ivs.length), List.zip_map, List.map_id, List.flatMap_map]
    refine List.flatMap_congr fun p _ => ?_
    simp only [PolyTimeFun.ite_apply, ap₂_apply, comp_apply, pair_apply, fst_apply, snd_apply,
      const_apply, PolyTimeFun.addUnary_apply, PolyTimeFun.leNat_apply, length_unary,
      Nat.zero_add, mapR_apply, rangeU_apply, List.map_map, Function.comp_def]
    by_cases h₁ : p.2.1 ≤ i <;> by_cases h₂ : p.2.1 + p.2.2 ≤ i <;> simp [h₁, h₂]
  · intro q hq z hz
    obtain ⟨p, -, hq'⟩ := List.mem_flatMap.1 hq
    split_ifs at hq' with hp
    · simp at hq'
    · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hq'
      simp only [comp_apply, pair_apply, fst_apply, snd_apply, ap₂_apply, const_apply,
        mulU_apply, append_unary, windowF_apply, length_unary]
      rw [window_eq_fldAt (ht := ht) z hz.le]
  · intro q _
    simp only [comp_apply, pair_apply, fst_apply, snd_apply, replicate_apply, const_apply,
      length_unary, zeros_eq t ht]

/-! ## The blocks of the codewords -/

section Blocks

variable {j : ℕ} {L : PcpDims}

/-- **A direction lies in a slot's block exactly when it lies in its interval of wires.** -/
theorem mem_blockM_iff (hLM : L.m ≤ 2 ^ j) (s : Slot L) (i : Fin (2 ^ j)) :
    i ∈ blockM j hLM s ↔ s.lo ≤ (i : ℕ) ∧ (i : ℕ) < s.lo + s.size := by
  rw [← Slot.exists_emb_iff]
  simp only [blockM, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply,
    Fin.ext_iff, Fin.val_castLE]

theorem flatMap_finRange_get {α β : Type*} (l : List α) (f : ℕ → α → List β) :
    (List.finRange l.length).flatMap (fun c : Fin l.length => f c (l.get c)) =
      ((List.range l.length).zip l).flatMap (fun p => f p.1 p.2) := by
  have h : (List.finRange l.length).map (fun c : Fin l.length => ((c : ℕ), l.get c)) =
      (List.range l.length).zip l := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp
  rw [← h, List.flatMap_map]

/-- The blocks of a role's codewords, as intervals of wires. -/
def ivsOf (L : PcpDims) (r : Role) : List (ℕ × ℕ) := (slotsOf L r).map fun s => (s.lo, s.size)

theorem length_ivsOf (r : Role) : (ivsOf L r).length = (slotsOf L r).length := by
  simp [ivsOf]

/-- **The indifference equations are those of the codewords' blocks.** -/
theorem indEqs_eq (d : ℕ) (hLM : L.m ≤ 2 ^ j) (N o : ℕ) (r : Role) (i : Fin (2 ^ j)) :
    indEqs (t := t) (ht := ht) d L hLM N o r i =
      ((List.range (ivsOf L r).length).zip (ivsOf L r)).flatMap fun p =>
        if p.2.1 ≤ (i : ℕ) ∧ (i : ℕ) < p.2.1 + p.2.2 then [] else (List.range d).map fun e =>
          ((fldAt t ht N (o + (p.1 * (d + 1) + (e + 1)) * t) :
            (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht)) := by
  have h := flatMap_finRange_get (slotsOf L r) (fun c (s : Slot L) =>
    if s.lo ≤ (i : ℕ) ∧ (i : ℕ) < s.lo + s.size then [] else (List.range d).map fun e =>
      ((fldAt t ht N (o + (c * (d + 1) + (e + 1)) * t) :
        (Fin N → ZMod 2) →ₗ[ZMod 2] (shoupBinField t ht).carrier), (0 : Fq t ht)))
  simp only [indEqs, mem_blockM_iff] at h ⊢
  rw [h, length_ivsOf, ivsOf, ← List.map_id (List.range (slotsOf L r).length), List.zip_map,
    List.map_id, List.flatMap_map]
  rfl

theorem ivsOf_alice : ivsOf L .alice = [(1, L.ℓ), (L.ℓ + L.ℓ + 3, L.ℓ)] := rfl
theorem ivsOf_bob : ivsOf L .bob = [(L.ℓ + 2, L.ℓ), (L.ℓ + L.ℓ + 3 + L.ℓ, L.ℓ)] := rfl

variable (L) in
/-- **The oracle's blocks, in runs**: `(count, lo, len)`, in the order of its codewords. -/
def oracleRuns : List (ℕ × ℕ × ℕ) :=
  let vO := L.ℓ + L.ℓ + 3
  let vW (k : ℕ) := L.ℓ + L.ℓ + 3 + L.oW + k * L.r
  let oL (k : ℕ) := L.ℓ + L.ℓ + 3 + L.ℓ + L.ℓ + k * L.dm
  [(1, 1, L.ℓ), (1, L.ℓ + 2, L.ℓ), (1, vO, L.oW), (1, vW 0, L.r), (1, vW 1, L.r), (1, vW 2, L.r),
    (L.m, 0, L.m), (L.ℓ, 1, L.ℓ), (L.ℓ, L.ℓ + 2, L.ℓ), (L.oW, vO, L.oW), (L.r, vW 0, L.r),
    (L.r, vW 1, L.r), (L.r, vW 2, L.r), (1, vO, L.ℓ), (1, vO + L.ℓ, L.ℓ), (1, oL 0, L.dm),
    (1, oL 1, L.dm), (1, oL 2, L.dm), (L.oW, vO, L.oW), (L.ℓ, vO, L.ℓ), (L.ℓ, vO + L.ℓ, L.ℓ),
    (L.dm, oL 0, L.dm), (L.dm, oL 1, L.dm), (L.dm, oL 2, L.dm)]

/-- **The oracle's blocks are its runs, expanded.** -/
theorem ivsOf_oracle :
    ivsOf L .oracle = (oracleRuns L).flatMap fun r => List.replicate r.1 (r.2.1, r.2.2) := by
  simp [ivsOf, oracleRuns, slotsOf, rOf, lOf, rSlots, lSlots, List.map_ofFn, Function.comp_def,
    Slot.lo, Slot.size, finRange3_flatMap, List.ofFn_const, List.ofFn_succ, List.append_assoc]

end Blocks

/-! ## The tables, as programs -/

/-- A list of programs, as a program of lists. -/
def listF {α β : Type} [SizedEncoding α] [SizedEncoding β] :
    List (PolyTimeFun α β) → PolyTimeFun α (List β)
  | [] => const []
  | f :: fs => PolyTimeFun.cons f (listF fs)

@[simp] theorem listF_apply {α β : Type} [SizedEncoding α] [SizedEncoding β]
    (fs : List (PolyTimeFun α β)) (a : α) : listF fs a = fs.map fun f => f a := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [listF, ih]

section Tables

/-- A constant in unary. -/
abbrev uC (c : ℕ) : PolyTimeFun ArParams Unary := const (unary c)
/-- `◇' = 2ℓ + 3◇ + 6`, the width of an index of `O`. -/
def oWF : PolyTimeFun ArParams Unary :=
  ap₂ append (ap₂ append (ap₂ append pL pL) ((AnswerReduction.ParRoutine.timesU 3).comp pDm)) (uC 6)
/-- `m`, the number of wires. -/
def mF : PolyTimeFun ArParams Unary :=
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append pL (uC 1))
    (ap₂ append pL (uC 1))) (ap₂ append oWF (uC 1)))
    ((AnswerReduction.ParRoutine.timesU 3).comp pR)) (uC 6)) pS
/-- The first wire of an index of `O`, `2ℓ + 3`. -/
def vOF : PolyTimeFun ArParams Unary := ap₂ append (ap₂ append pL pL) (uC 3)
/-- The first wire of the `k`-th witness index. -/
def vWF (k : ℕ) : PolyTimeFun ArParams Unary :=
  ap₂ append (ap₂ append vOF oWF) ((AnswerReduction.ParRoutine.timesU k).comp pR)
/-- The first wire of the `k`-th copy's cell. -/
def oLF (k : ℕ) : PolyTimeFun ArParams Unary :=
  ap₂ append (ap₂ append (ap₂ append vOF pL) pL) ((AnswerReduction.ParRoutine.timesU k).comp pDm)

/-- A run `(count, lo, len)`. -/
abbrev trF (c lo len : PolyTimeFun ArParams Unary) : PolyTimeFun ArParams (Unary × Unary × Unary) :=
  c.pair (lo.pair len)

/-- **The oracle's runs of blocks**, as a program of the parameters. -/
def runsF : PolyTimeFun ArParams (List (Unary × Unary × Unary)) :=
  listF [trF (uC 1) (uC 1) pL, trF (uC 1) (ap₂ append pL (uC 2)) pL, trF (uC 1) vOF oWF,
    trF (uC 1) (vWF 0) pR, trF (uC 1) (vWF 1) pR, trF (uC 1) (vWF 2) pR, trF mF (uC 0) mF,
    trF pL (uC 1) pL, trF pL (ap₂ append pL (uC 2)) pL, trF oWF vOF oWF, trF pR (vWF 0) pR,
    trF pR (vWF 1) pR, trF pR (vWF 2) pR, trF (uC 1) vOF pL, trF (uC 1) (ap₂ append vOF pL) pL,
    trF (uC 1) (oLF 0) pDm, trF (uC 1) (oLF 1) pDm, trF (uC 1) (oLF 2) pDm, trF oWF vOF oWF,
    trF pL vOF pL, trF pL (ap₂ append vOF pL) pL, trF pDm (oLF 0) pDm, trF pDm (oLF 1) pDm,
    trF pDm (oLF 2) pDm]

theorem runsF_arParams (t j d : ℕ) (L : PcpDims) (e : Data) :
    runsF (arParams t j d L e) =
      (oracleRuns L).map fun r => (unary r.1, unary r.2.1, unary r.2.2) := by
  simp only [runsF, listF_apply, List.map_cons, List.map_nil, oracleRuns, trF, pair_apply,
    ap₂_apply, comp_apply, const_apply, oWF, mF, vOF, vWF, oLF, append_unary,
    AnswerReduction.ParRoutine.timesU_apply, pL_arParams, pDm_arParams, pR_arParams,
    pS_arParams, length_unary, PcpDims.oW, PcpDims.m, PcpDims.nIn]

/-- The blocks of a role's codewords, at a role. -/
def ivBranch : Role → PolyTimeFun (ArParams × Role) (List (Unary × Unary))
  | .alice => listF [((uC 1).pair pL).comp fst, (vOF.pair pL).comp fst]
  | .bob => listF [((ap₂ append pL (uC 2)).pair pL).comp fst,
      ((ap₂ append vOF pL).pair pL).comp fst]
  | .oracle => flatMapR (replicate.comp ((fst.comp fst).pair (snd.comp fst))) (runsF.comp fst)

/-- **The blocks of a role's codewords**, as a program. -/
def ivF : PolyTimeFun (ArParams × Role) (List (Unary × Unary)) := choose snd ivBranch (const [])

theorem ivF_eq (t j d : ℕ) (L : PcpDims) (e : Data) (r : Role) :
    ivF (arParams t j d L e, r) = (ivsOf L r).map fun p => (unary p.1, unary p.2) := by
  rw [ivF, choose_apply, snd_apply]
  cases r
  · simp only [ivBranch, flatMapR_apply, comp_apply, fst_apply, runsF_arParams, ivsOf_oracle,
      List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun q _ => ?_
    simp [replicate_apply, length_unary, List.map_replicate]
  · simp only [ivBranch, listF_apply, List.map_cons, List.map_nil, comp_apply, fst_apply,
      pair_apply, const_apply, ap₂_apply, vOF, append_unary, pL_arParams, ivsOf_alice]
  · simp only [ivBranch, listF_apply, List.map_cons, List.map_nil, comp_apply, fst_apply,
      pair_apply, const_apply, ap₂_apply, vOF, append_unary, pL_arParams, ivsOf_bob]

end Tables

/-! ## The indifference checks at a question -/

/-- The input of the indifference checks of one answer: the parameters, the answer's offset `o`,
`N`, its type, and its question's low-degree bits. -/
abbrev IndCIn : Type := ArParams × Unary × Unary × (Role × LIDT.CL.Ty) × BitStr

section IndBranch

def iP : PolyTimeFun IndCIn ArParams := fst
def iO : PolyTimeFun IndCIn Unary := fst.comp snd
def iN : PolyTimeFun IndCIn Unary := fst.comp (snd.comp snd)
def iTy : PolyTimeFun IndCIn (Role × LIDT.CL.Ty) := fst.comp (snd.comp (snd.comp snd))
def iB : PolyTimeFun IndCIn BitStr := snd.comp (snd.comp (snd.comp snd))

/-- The direction the question's seed selects. -/
def iChi : PolyTimeFun IndCIn ℕ :=
  Introspection.SeedProgram.selectorProg.comp ((pT.comp iP).pair ((pJ.comp iP).pair
    ((headD []).comp (snd.comp (snd.comp (blkF.comp ((pT.comp iP).pair ((pM.comp iP).pair
      iB))))))))

/-- The indifference equations of an axis-parallel line answer. -/
def indAline : PolyTimeFun IndCIn (List BitStr) :=
  indF.comp ((pT.comp iP).pair ((pD.comp iP).pair (iO.pair (iN.pair (iChi.pair
    (ivF.comp (iP.pair (fst.comp iTy))))))))

/-- The branch at a type of the low-degree test. -/
def indBranch : LIDT.CL.Ty → PolyTimeFun IndCIn (List BitStr)
  | .aline => indAline
  | _ => const []

end IndBranch

/-- **The indifference checks of an answer**, as a program, by its type. -/
def indConsF : PolyTimeFun IndCIn (List BitStr) := choose (snd.comp iTy) indBranch (const [])

/-- **The indifference program computes the indifference checks** of an answer. -/
theorem indConsF_eq {j : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
    (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM)
    (hsel : ∀ a, ((sel.χ a : Fin (2 ^ j)) : ℕ) =
      Introspection.SeedProgram.selectorProg (unary t, unary j, (shoupBinField t ht).toBits a))
    {rV : ℕ} {L : PcpDims} (hLM : L.m ≤ 2 ^ j) (d o N : ℕ) (e : Data) (r : Role)
    (S : LIDT.CL.Ty) (y : Fin (rV + D j * t) → 𝔽₂) :
    indConsF (arParams t j d L e, unary o, unary N, (r, S), (CL.toBits y).drop rV) =
      indCons j d L hM hLM N o r (ldQ t ht j rV sel S y) := by
  rw [indConsF, choose_apply]
  cases S
  · rfl
  · simp only [iTy, comp_apply, fst_apply, snd_apply, indBranch, ldQ, LIDT.CL.Regs.questionOf,
      indCons, sel.chi_π, indAline, pair_apply, iP, iO, iN, iChi, iB, pT_arParams,
      pD_arParams, pJ_arParams, pM_arParams, blkF_apply, blocks1_ldPart (ht := ht), headD_apply,
      List.headD_cons, ← hsel, ivF_eq, indF_eq (ht := ht), indEqs_eq]
  · rfl

end MIPRE.Tailored.AnsRed.Typed

end
