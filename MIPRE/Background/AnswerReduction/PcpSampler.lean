/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.StageCorrect
import MIPRE.Background.AnswerReduction.Family
import MIPRE.Foundations.CL.ProductSamplerProg
import MIPRE.Foundations.LowDegree.UnaryDegreeArithmetic
import MIPRE.Foundations.SAT.ArrayProg
import MIPRE.Foundations.Cost.FiniteEncoding

/-!
# The PCP sampler as a directly answered sampler

Piece AR-3d of `planning/answer-reduction.md`: the downsized PCP half of the answer-reduced
sampler as a `CL.DirectSampler` (`MIPRE/Foundations/CL/ProductSamplerProg`), for a family of PCP
parameters whose `m` and `m'` are powers of two (`PcpFamily`), with the effective seed selectors:
the high bits of the seed (`PcpFamily.sel`), the selectors the introspection sampler uses.

* The queries of the downsized presentation, in bits, are the queries of the presentation over
  `F_q` in Shoup bits (`toBits_eval_truncate_pcpCl`, `toBits_mapOfPrefix_pcpCl`,
  `indicatorBits_factorOfPrefix_pcpCl`).
* The parameters at an index (`PcpFamily.pd`) are `k`, `m'` and the six copies' descriptions, in
  unary; a routine computes them. The answer function (`answerProg`) reads the copy and the test
  type off the type and runs the copy's program (`MIPRE/Background/AnswerReduction/StageProg`).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.CL.CLFun SAT Pcp Cost Cost.PolyTimeFun StageProg
  CL.Detyping.Program

/-! ## The type encoding -/

/-- A test type from its number. -/
def tyOfNat : ℕ → Option LIDT.CL.Ty
  | 0 => some .point
  | 1 => some .aline
  | 2 => some .dline
  | _ => none

instance : SizedEncoding LIDT.CL.Ty where
  encode τ := encode (tyNat τ)
  decode d := (decode d : Option ℕ).bind tyOfNat
  decode_encode τ := by cases τ <;> simp [SizedEncoding.decode_encode, tyNat, tyOfNat]

theorem encode_ty (τ : LIDT.CL.Ty) : (encode τ : Data) = encode (tyNat τ) := rfl

/-! ## The downsized presentation in bits -/

section Bits

variable (P : PcpParams) (hk : 1 ≤ P.k) [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)}
  {hm' : P.m' ∣ Fintype.card (Fq P hk)} (S : LIDT.CL.Sel (Fq P hk) P.m hm)
  (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')

theorem ofBits_flatBits (v : Coord P → Fq P hk) :
    ofBits (pcpDim P * P.k) (flatBits P hk v) =
      reindexEquiv (bitIndex P P.k) (downsizeEquiv (basis P hk) v) := by
  rw [← toBits_pcp, ofBits_toBits]

theorem toBits_eval_truncate_pcpCl (t : PcpTy) (j : ℕ) (v : Coord P → Fq P hk) :
    toBits (((pcpCl P hk S S' t).truncate j).eval (ofBits _ (flatBits P hk v))) =
      flatBits P hk (((Pcp.pres P S S' t).truncate j).eval v) := by
  rw [ofBits_flatBits, pcpCl, truncate_reindex, eval_reindex, pcpBin, eval_truncate_downsize,
    toBits_pcp]

theorem toBits_mapOfPrefix_pcpCl (t : PcpTy) (j : ℕ) (u y : Coord P → Fq P hk) :
    toBits ((pcpCl P hk S S' t).mapOfPrefix j (ofBits _ (flatBits P hk u))
      (ofBits _ (flatBits P hk y))) =
      flatBits P hk ((Pcp.pres P S S' t).mapOfPrefix j u y) := by
  rw [ofBits_flatBits, ofBits_flatBits, pcpCl, mapOfPrefix_reindex, pcpBin,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, mapOfPrefix_downsize, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.restrictScalars_apply, toBits_pcp]

theorem indicatorBits_factorOfPrefix_pcpCl (t : PcpTy) (j : ℕ) (u : Coord P → Fq P hk) :
    indicatorBits ((pcpCl P hk S S' t).factorOfPrefix j (ofBits _ (flatBits P hk u))) =
      flatInd P P.k ((Pcp.pres P S S' t).factorOfPrefix j u) := by
  rw [ofBits_flatBits, pcpCl, factorOfPrefix_reindex, pcpBin, factorOfPrefix_downsize,
    indicatorBits, flatInd, List.ofFn_mul]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  rw [← List.ofFn_const]
  apply List.ofFn_inj.mpr
  funext j'
  congr 1
  rw [Finset.mem_map_equiv, bitIndex_symm, Finset.mem_product]
  simp

end Bits

/-! ## Selectors of power-of-two blocks -/

section Sel

open Introspection.SeedProgram

variable (k : ℕ) (hk : 1 ≤ k) (sz jw : ℕ) (hsz : sz = 2 ^ jw) (hjw : jw ≤ k)

include hsz hjw in
theorem pow_dvd_card : sz ∣ Fintype.card (shoupBinField k hk).carrier := by
  rw [(shoupBinField k hk).card_carrier, hsz]
  exact Nat.pow_dvd_pow 2 hjw

variable [NeZero sz]

/-- **The effective seed selector**: the high `jw` bits of the seed, for blocks of size
`sz = 2^jw`. -/
def powSel : LIDT.CL.Sel (shoupBinField k hk).carrier sz (pow_dvd_card k hk sz jw hsz hjw) :=
  LIDT.CL.Sel.ofSelector _ (fun a => Fin.cast hsz.symm (selector (shoupBinField k hk) jw hjw a))
    (by
      intro i
      rw [Finset.filter_congr (q := fun a => selector (shoupBinField k hk) jw hjw a =
          Fin.cast hsz i) (fun a _ => by simp only [Fin.ext_iff, Fin.val_cast]),
        ← Fintype.card_subtype, card_selector_fiber, (shoupBinField k hk).card_carrier, hsz,
        Nat.pow_div hjw (by norm_num)])

theorem powSel_χ (a : (shoupBinField k hk).carrier) :
    ((powSel k hk sz jw hsz hjw).χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ) := rfl

end Sel

/-! ## Families of PCP parameters -/

/-- **A family of PCP parameters** whose `m` and `m'` are powers of two, `2^{jm}` and `2^{jm'}`,
with `jm, jm' ≤ k`: what the effective seed selectors need. -/
structure PcpFamily where
  /-- The parameters at each index. -/
  par : ℕ → PcpParams
  hk : ∀ n, 1 ≤ (par n).k
  /-- `log₂ m`. -/
  jm : ℕ → ℕ
  /-- `log₂ m'`. -/
  jm' : ℕ → ℕ
  m_eq : ∀ n, (par n).m = 2 ^ jm n
  m'_eq : ∀ n, (par n).m' = 2 ^ jm' n
  jm_le : ∀ n, jm n ≤ (par n).k
  jm'_le : ∀ n, jm' n ≤ (par n).k

namespace PcpFamily

variable (F : PcpFamily) (n : ℕ)

instance neZero_m : NeZero (F.par n).m := ⟨by rw [F.m_eq]; positivity⟩

/-- The selector of the first five copies. -/
def sel : LIDT.CL.Sel (Fq (F.par n) (F.hk n)) (F.par n).m
    (pow_dvd_card _ _ _ _ (F.m_eq n) (F.jm_le n)) :=
  powSel (F.par n).k (F.hk n) (F.par n).m (F.jm n) (F.m_eq n) (F.jm_le n)

/-- The selector of the sixth copy. -/
def sel' : LIDT.CL.Sel (Fq (F.par n) (F.hk n)) (F.par n).m'
    (pow_dvd_card _ _ _ _ (F.m'_eq n) (F.jm'_le n)) :=
  powSel (F.par n).k (F.hk n) (F.par n).m' (F.jm' n) (F.m'_eq n) (F.jm'_le n)

/-- The downsized PCP presentation at index `n`. -/
def cl (t : PcpTy) : CLFun 𝔽₂ (Fin (pcpDim (F.par n) * (F.par n).k)) 3 :=
  pcpCl (F.par n) (F.hk n) (F.sel n) (F.sel' n) t

/-- The description of a copy: offset, length, selector width, seed. -/
def desc (c : Fin 6) : Desc :=
  if (c : ℕ) < 5 then (unary (c * (F.par n).m), unary (F.par n).m, unary (F.jm n), unary c)
  else (unary 0, unary (F.par n).m', unary (F.jm' n), unary c)

/-- **The parameters at index `n`**: `k`, `m'` and the six copies' descriptions, in unary. -/
def pd : Data :=
  encode ((unary (F.par n).k, unary (F.par n).m', List.ofFn (F.desc n)) :
    Unary × Unary × List Desc)

end PcpFamily

/-! ## Reading the parameters -/

/-- A list's elements' encodings. -/
def rawListP : PolyTimeFun Data (List Data) := ofEncodeEq rawList encode_rawList

theorem rawList_encode {α : Type*} [SizedEncoding α] (l : List α) :
    rawList (encode l) = l.map encode := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [encode_list_cons]; simp only [rawList, ih, List.map_cons]

/-- A unary numeral. -/
def readU : PolyTimeFun Data Unary := (map (const ())).comp rawListP

theorem readU_encode (u : Unary) : readU (encode u) = u := by
  change (rawList (encode u)).map (fun _ => ()) = u
  rw [rawList_encode, List.map_map]
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.map_cons, ih]

/-- A copy's description. -/
def readDesc : PolyTimeFun Data Desc :=
  (readU.comp treeHead).pair ((readU.comp (treeHead.comp treeTail)).pair
    ((readU.comp (treeHead.comp (treeTail.comp treeTail))).pair
      (readU.comp (treeTail.comp (treeTail.comp treeTail)))))

theorem readDesc_encode (d : Desc) : readDesc (encode d) = d := by
  obtain ⟨a, b, c, e⟩ := d
  simp only [readDesc, pair_apply, comp_apply, encode_prod, treeHead_cons, treeTail_cons,
    readU_encode]

/-! ## The answer program -/

section Answer

def pdI : PolyTimeFun DirectInput Data := fst
def tagI : PolyTimeFun DirectInput Data := fst.comp snd
def kP : PolyTimeFun DirectInput Unary := readU.comp (treeHead.comp pdI)
def mP : PolyTimeFun DirectInput Unary := readU.comp (treeHead.comp (treeTail.comp pdI))
def descsP : PolyTimeFun DirectInput (List Data) :=
  rawListP.comp (treeTail.comp (treeTail.comp pdI))
def descP : PolyTimeFun DirectInput Desc :=
  readDesc.comp ((ArrayProg.getD Data.nil).comp ((readNat.comp (treeHead.comp tagI)).pair descsP))
def τP : PolyTimeFun DirectInput ℕ := readNat.comp (treeTail.comp tagI)

def kindA : PolyTimeFun DirectInput ℕ := fst.comp (snd.comp snd)
def jA : PolyTimeFun DirectInput ℕ := fst.comp (snd.comp (snd.comp snd))
def uA : PolyTimeFun DirectInput BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def yA : PolyTimeFun DirectInput BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

/-- The copy program's input, read off a direct query. -/
def assemble : PolyTimeFun DirectInput Input :=
  kP.pair (descP.pair (τP.pair (mP.pair (kindA.pair (jA.pair (uA.pair yA))))))

/-- **The answer program** of the PCP sampler: the copy program on the copy the type names. -/
def answerProg : PolyTimeFun DirectInput BitStr := copyProg.comp assemble

/-- The dimension program: `(2m' + 6) k` in unary. -/
def dimProg : PolyTimeFun Data Unary :=
  LowDegree.DegreeArithmetic.mulUnaryProg.comp
    ((ap₂ append (readU.comp (treeHead.comp treeTail)) (ap₂ append
      (readU.comp (treeHead.comp treeTail)) (const (unary 6)))).pair (readU.comp treeHead))

end Answer

namespace PcpFamily

variable (F : PcpFamily) (n : ℕ)

theorem answerProg_apply (t : PcpTy) (kind j : ℕ) (u y : BitStr) :
    answerProg (F.pd n, encode t, kind, j, u, y) =
      copyAnswer (unary (F.par n).k) (F.desc n t.1) (tyNat t.2) (unary (F.par n).m') kind j u y := by
  obtain ⟨i, τ⟩ := t
  rw [answerProg, comp_apply, ← copyProg_apply]
  congr 1
  have hi : readNat (encode i) = (i : ℕ) := readNat_encode (i : ℕ)
  have hτ : readNat (encode τ) = tyNat τ := readNat_encode (tyNat τ)
  simp only [assemble, pair_apply, kP, mP, descP, descsP, τP, pdI, tagI, kindA, jA, uA, yA,
    comp_apply, fst_apply, snd_apply, pd, encode_prod, treeHead_cons, treeTail_cons,
    readU_encode, ArrayProg.getD_apply, hi, hτ]
  simp only [rawListP, ofEncodeEq_apply, rawList_encode, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_ofFn, i.isLt, dif_pos, Fin.eta, Option.map_some,
    Option.getD_some, readDesc_encode]

theorem dimProg_pd : (dimProg (F.pd n)).length = pcpDim (F.par n) * (F.par n).k := by
  simp only [dimProg, comp_apply, pair_apply, ap₂_apply, append_apply, const_apply, pd,
    encode_prod, treeHead_cons, treeTail_cons, readU_encode,
    LowDegree.DegreeArithmetic.mulUnaryProg_apply, length_unary, List.length_append, pcpDim]

theorem le_lt (t : PcpTy) (h : (t.1 : ℕ) < 5) :
    (t.1 : ℕ) * (F.par n).m + (F.par n).m ≤ (F.par n).m' := regs_le (F.par n) ⟨t.1, h⟩

theorem pres_lt (t : PcpTy) (h : (t.1 : ℕ) < 5) :
    Pcp.pres (F.par n) (F.sel n) (F.sel' n) t =
      (regsAt (F.par n) (t.1 * (F.par n).m) (F.par n).m t.1 (F.le_lt n t h)).pres (F.sel n) t.2 := by
  unfold Pcp.pres
  rw [dif_pos h, regs_eq]
  rfl

theorem pres_ge (t : PcpTy) (h : ¬ (t.1 : ℕ) < 5) :
    Pcp.pres (F.par n) (F.sel n) (F.sel' n) t =
      (regsAt (F.par n) 0 (F.par n).m' t.1 (by simp)).pres (F.sel' n) t.2 := by
  unfold Pcp.pres
  rw [dif_neg h, regs6_eq]
  have h5 : t.1 = 5 := Fin.ext (by have := t.1.isLt; simp; omega)
  rw [h5]

theorem desc_lt (c : Fin 6) (h : (c : ℕ) < 5) :
    F.desc n c = (unary (c * (F.par n).m), unary (F.par n).m, unary (F.jm n), unary c) := by
  simp [desc, h]

theorem desc_ge (c : Fin 6) (h : ¬ (c : ℕ) < 5) :
    F.desc n c = (unary 0, unary (F.par n).m', unary (F.jm' n), unary c) := by
  simp [desc, h]

/-- **The marginals**, by the copy the type names. -/
theorem answer_marginal (t : PcpTy) {j : ℕ} (hj : 1 ≤ j) (v : Coord (F.par n) → Fq (F.par n) (F.hk n)) :
    answerProg (F.pd n, encode t, 1, j, flatBits (F.par n) (F.hk n) v, []) =
      flatBits (F.par n) (F.hk n)
        (((Pcp.pres (F.par n) (F.sel n) (F.sel' n) t).truncate j).eval v) := by
  rw [answerProg_apply]
  by_cases h : (t.1 : ℕ) < 5
  · rw [F.pres_lt n t h, F.desc_lt n t.1 h]
    exact copyAnswer_marginal (F.hk n) _ _ _ t.1 (F.sel n) (F.jm_le n)
      (powSel_χ _ _ _ _ _ _) (F.par n) _ t.2 hj v []
  · rw [F.pres_ge n t h, F.desc_ge n t.1 h]
    exact copyAnswer_marginal (F.hk n) _ _ _ t.1 (F.sel' n) (F.jm'_le n)
      (powSel_χ _ _ _ _ _ _) (F.par n) _ t.2 hj v []

/-- **The stage maps**, by the copy the type names. -/
theorem answer_linear (t : PcpTy) {j : ℕ} (hj : 1 ≤ j)
    (u y : Coord (F.par n) → Fq (F.par n) (F.hk n)) :
    answerProg (F.pd n, encode t, 2, j, flatBits (F.par n) (F.hk n) u,
        flatBits (F.par n) (F.hk n) y) =
      flatBits (F.par n) (F.hk n)
        ((Pcp.pres (F.par n) (F.sel n) (F.sel' n) t).mapOfPrefix (j - 1) u y) := by
  rw [answerProg_apply]
  by_cases h : (t.1 : ℕ) < 5
  · rw [F.pres_lt n t h, F.desc_lt n t.1 h]
    exact copyAnswer_linear (F.hk n) _ _ _ t.1 (F.sel n) (F.jm_le n)
      (powSel_χ _ _ _ _ _ _) (F.par n) _ t.2 hj u y
  · rw [F.pres_ge n t h, F.desc_ge n t.1 h]
    exact copyAnswer_linear (F.hk n) _ _ _ t.1 (F.sel' n) (F.jm'_le n)
      (powSel_χ _ _ _ _ _ _) (F.par n) _ t.2 hj u y

/-- **The factor spaces**, by the copy the type names. -/
theorem answer_factor (t : PcpTy) {j : ℕ} (hj : 1 ≤ j) (u : Coord (F.par n) → Fq (F.par n) (F.hk n)) :
    answerProg (F.pd n, encode t, 3, j, flatBits (F.par n) (F.hk n) u, []) =
      flatInd (F.par n) (F.par n).k
        ((Pcp.pres (F.par n) (F.sel n) (F.sel' n) t).factorOfPrefix (j - 1) u) := by
  rw [answerProg_apply]
  by_cases h : (t.1 : ℕ) < 5
  · rw [F.pres_lt n t h, F.desc_lt n t.1 h]
    exact copyAnswer_factor (F.hk n) _ _ _ t.1 (F.sel n) (F.jm_le n)
      (powSel_χ _ _ _ _ _ _) (F.par n) _ t.2 hj u []
  · rw [F.pres_ge n t h, F.desc_ge n t.1 h]
    exact copyAnswer_factor (F.hk n) _ _ _ t.1 (F.sel' n) (F.jm'_le n)
      (powSel_χ _ _ _ _ _ _) (F.par n) _ t.2 hj u []

theorem exists_flatBits_of_toBits {j : ℕ} (t : PcpTy)
    (x : Fin (pcpDim (F.par n) * (F.par n).k) → 𝔽₂) :
    ∃ u, toBits (((F.cl n t).truncate j).eval x) = flatBits (F.par n) (F.hk n) u :=
  exists_flatBits (F.par n) (F.hk n) (length_toBits _)

/-- **The PCP sampler**, directly answered, given a routine computing its parameters. -/
def directSampler (pp : Prog) (hpp : pp.WellScoped 1)
    (hruns : ∀ n, ∃ t, pp.Runs (encode n) (F.pd n) t) : DirectSampler 3 PcpTy where
  parProg := pp
  parProg_closed := hpp
  pd := F.pd
  parProg_runs := hruns
  dim n := pcpDim (F.par n) * (F.par n).k
  cl := F.cl
  cl_exactlyOn n t := pcpCl_exactlyOn _ _ _ _ t
  dimProg := dimProg
  dimProg_eq := F.dimProg_pd
  answer := answerProg
  answer_marginal n t j z hj hz := by
    obtain ⟨v, rfl⟩ := exists_flatBits (F.par n) (F.hk n) hz
    rw [F.answer_marginal n t hj v]
    exact (toBits_eval_truncate_pcpCl _ _ _ _ t j v).symm
  answer_linear n t j u y hj hu hy := by
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨u', hu'⟩ := F.exists_flatBits_of_toBits n (j := j - 1) t x
    obtain ⟨y', rfl⟩ := exists_flatBits (F.par n) (F.hk n) hy
    rw [hu', F.answer_linear n t hj u' y']
    exact (toBits_mapOfPrefix_pcpCl _ _ _ _ t (j - 1) u' y').symm
  answer_factor n t j u hj hu := by
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨u', hu'⟩ := F.exists_flatBits_of_toBits n (j := j - 1) t x
    rw [hu', F.answer_factor n t hj u']
    exact (indicatorBits_factorOfPrefix_pcpCl _ _ _ _ t (j - 1) u').symm

end PcpFamily

end MIPRE.AnswerReduction

end
