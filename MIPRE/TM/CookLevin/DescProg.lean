/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.FamilyProg
import MIPRE.Foundations.Cost.TreeBits

/-!
# The describer as a program

`descCircP` is the describer circuit as a polynomial-time function of
`((e in unary, T), (𝒟, n), (x, y))`, and `descCircP_apply` says it is `descCirc`. This is
item 4 of `thm:succinct-sat`; item 3, the gate bound, follows from it, because
`PolyTimeFun.esize_apply_le` bounds the size of the output of a program by its time bound
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## The candidate of the describer -/

variable {ι : Type*} [SizedEncoding ι]

/-- The sign at the offset `3 m + k`. -/
noncomputable def signR (eu : PolyTimeFun ι Unary) (k : ℕ) : PolyTimeFun ι Fml :=
  ap₁ Fml.inpF (ap₁ (incN k) (ap₁ unaryToBin (ap₁ (nsmulU 3) (mU eu))))

theorem signR_apply (eu : PolyTimeFun ι Unary) (k : ℕ) (i : ι) :
    signR eu k i = Fml.inp (3 * mOf (eu i).length Gc + k) := by
  rw [signR, ap₁_apply, Fml.inpF_apply, ap₁_apply, incN_apply, ap₁_apply, unaryToBin_apply,
    ap₁_apply, length_nsmulU, length_mU]

/-- `candOf`: the three field records at the bases `0`, `m` and `2 m`, and the three signs. -/
noncomputable def candR (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) : CandR ι where
  A₁ := litFieldsR eu TR (const [])
  σ₁ := signR eu 0
  A₂ := litFieldsR eu TR (mU eu)
  σ₂ := signR eu 1
  A₃ := litFieldsR eu TR (ap₁ (nsmulU 2) (mU eu))
  σ₃ := signR eu 2

theorem candR_ev (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (i : ι) :
    (candR eu TR).ev i = candOf (eu i).length Gc (TR i) := by
  have h1 : ((const [] : PolyTimeFun ι Unary) i).length = 0 := rfl
  have h2 : (mU eu i).length = mOf (eu i).length Gc := length_mU eu i
  have h3 : (ap₁ (nsmulU 2) (mU eu) i).length = 2 * mOf (eu i).length Gc := by
    rw [ap₁_apply, length_nsmulU, length_mU]
  simp only [CandR.ev, candR, candOf, CandF.mk.injEq]
  refine ⟨?_, signR_apply eu 0 i, ?_, signR_apply eu 1 i, ?_, signR_apply eu 2 i⟩
  · rw [litFieldsR_ev, h1]
  · rw [litFieldsR_ev, h2]
  · rw [litFieldsR_ev, h3]

/-! ## The fixed tapes -/

/-- The symbol codes of the serialization of a value. -/
noncomputable def codesP : PolyTimeFun Data (List ℕ) :=
  (map (PolyTimeFun.ite (PolyTimeFun.id Bool) (const (symCode (.sym Sym.one)))
    (const (symCode (.sym Sym.zero))))).comp PolyTimeFun.toBits

theorem codesOf_S (d : Data) : codesOf (S d) =
    d.toBits.map fun b => if b then symCode (.sym Sym.one) else symCode (.sym Sym.zero) := by
  rw [codesOf, S, bits, List.map_map]
  congr 1
  funext b
  cases b <;> rfl

@[simp] theorem codesP_apply (d : Data) : codesP d = codesOf (S d) := by
  rw [codesOf_S, codesP, comp_apply, map_apply, PolyTimeFun.toBits_apply]
  congr 1

/-- A bit string as its encoding. -/
noncomputable def bitsData : PolyTimeFun BitStr Data :=
  PolyTimeFun.ofEncodeEq (fun l => encode l) fun _ => rfl

@[simp] theorem bitsData_apply (l : BitStr) : bitsData l = encode l := rfl

/-- `tabsOf`: the value formulas of the five fixed tapes. -/
noncomputable def tabsR (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ)
    (DR : PolyTimeFun ι Prog) (nR : PolyTimeFun ι ℕ) (xR yR : PolyTimeFun ι BitStr) :
    PolyTimeFun ι (List (ℕ × Fml)) :=
  let A := litFieldsR eu TR (const [])
  listOf [
    (const 0).pair (cellValR eu A (ap₁ codesP (ap₁ PolyTimeFun.progData DR))),
    (const 1).pair (cellValR eu A (ap₁ codesP (ap₁ PolyTimeFun.natData nR))),
    (const 2).pair (unaryValR eu A TR),
    (const 3).pair (cellValR eu A (ap₁ codesP (ap₁ bitsData xR))),
    (const 4).pair (cellValR eu A (ap₁ codesP (ap₁ bitsData yR)))]

theorem tabsR_apply (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ)
    (DR : PolyTimeFun ι Prog) (nR : PolyTimeFun ι ℕ) (xR yR : PolyTimeFun ι BitStr) (i : ι) :
    tabsR eu TR DR nR xR yR i =
      tabsOf (eu i).length (TR i) (DR i) (nR i) (xR i) (yR i)
        (litFields (eu i).length Gc (TR i) 0) := by
  have hA : (litFieldsR eu TR (const []) : FieldsR ι).ev i =
      litFields (eu i).length Gc (TR i) 0 := by
    rw [litFieldsR_ev]
    rfl
  simp only [tabsR, listOf_apply, List.map_cons, List.map_nil, pair_apply, const_apply,
    ap₁_apply, cellValR_apply, unaryValR_apply, codesP_apply, bitsData_apply, hA, tabsOf]
  rfl

/-! ## The describer -/

/-- The input of the describer: `e` in unary and the time bound, the decider and the index,
the two questions. -/
abbrev DInp := (Unary × ℕ) × (Prog × ℕ) × (BitStr × BitStr)

noncomputable def euI : PolyTimeFun DInp Unary := ap₁ fst fst
noncomputable def TI : PolyTimeFun DInp ℕ := ap₁ snd fst
noncomputable def DI : PolyTimeFun DInp Prog := ap₁ fst (ap₁ fst snd)
noncomputable def nI : PolyTimeFun DInp ℕ := ap₁ snd (ap₁ fst snd)
noncomputable def xI : PolyTimeFun DInp BitStr := ap₁ fst (ap₁ snd snd)
noncomputable def yI : PolyTimeFun DInp BitStr := ap₁ snd (ap₁ snd snd)

@[simp] theorem euI_apply (p : DInp) : euI p = p.1.1 := rfl
@[simp] theorem TI_apply (p : DInp) : TI p = p.1.2 := rfl
@[simp] theorem DI_apply (p : DInp) : DI p = p.2.1.1 := rfl
@[simp] theorem nI_apply (p : DInp) : nI p = p.2.1.2 := rfl
@[simp] theorem xI_apply (p : DInp) : xI p = p.2.2.1 := rfl
@[simp] theorem yI_apply (p : DInp) : yI p = p.2.2.2 := rfl

/-- `descFml`, as a program. -/
noncomputable def descFmlP : PolyTimeFun DInp Fml :=
  tableauPlusR euI TI (candR euI TI) (tabsR euI TI DI nI xI yI) (const [5, 6])

theorem descFmlP_apply (p : DInp) :
    descFmlP p = descFml p.1.1.length p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 := by
  rw [descFmlP, tableauPlusR_apply, candR_ev, tabsR_apply, descFml]
  rfl

/-- **The describer circuit, as a program** (item 4 of `thm:succinct-sat`): the flattening of
`descFml` on `3 m + 3` inputs. -/
noncomputable def descCircP : PolyTimeFun DInp Circuit :=
  ap₂ Fml.toCircuitF
    (ap₁ unaryToBin (ap₂ addU (ap₁ (nsmulU 3) (mU euI)) (const (unary 3)))) descFmlP

theorem descCircP_apply (p : DInp) :
    descCircP p = descCirc p.1.1.length p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 := by
  rw [descCircP, ap₂_apply, Fml.toCircuitF_apply, descFmlP_apply, ap₁_apply, unaryToBin_apply,
    ap₂_apply, length_addU, ap₁_apply, length_nsmulU, length_mU, const_apply, length_unary,
    descCirc, euI_apply]

end MIPRE.TM.CookLevin.Desc
