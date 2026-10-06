/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.TM.CookLevin.Decoupled6
public import MIPRE.TM.CookLevin.DecoupledProg

@[expose] public section

/-!
# The windowed describer as a program, and the structure inhabited

The program of `descCirc6` (slice P4g of the Aldous–Lyons track), assembled from the readers
of `DecoupledProg.lean` at the six-block layout: the window lengths are read in unary off the
input, every offset is a unary sum, and the offset `2^ℓa` of the third window is a power of two
(`pow2P`), so no arithmetic on binary numbers is needed. The gate bound is the rounded bound of
`Assemble.lean` at a linear majorant of the input size, which uses that the windows are no wider
than the witness indices, themselves logarithmic in `T` and `σ`.
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## The link formula and the whole formula, as programs -/

section Prog6

variable {ι : Type*} [SizedEncoding ι] (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ)
  (la lb lc : PolyTimeFun ι Unary)

/-- The offset of the witness indices, in unary. -/
noncomputable def wOffU : PolyTimeFun ι Unary := ap₂ addU (ap₂ addU la lb) lc

@[simp] theorem length_wOffU (i : ι) :
    (wOffU la lb lc i).length = wOff (la i).length (lb i).length (lc i).length := by
  rw [wOffU, ap₂_apply, length_addU, ap₂_apply, length_addU, wOff]

/-- The offset of the six signs, in unary. -/
noncomputable def sgOff6U : PolyTimeFun ι Unary :=
  ap₂ addU (wOffU la lb lc) (ap₁ (nsmulU 3) (mU eu))

@[simp] theorem length_sgOff6U (i : ι) :
    (sgOff6U eu la lb lc i).length =
      sgOff6 (la i).length (lb i).length (lc i).length (mOf (eu i).length Gc) := by
  rw [sgOff6U, ap₂_apply, length_addU, length_wOffU, ap₁_apply, length_nsmulU, length_mU, sgOff6]

/-- The `k`-th of the six signs. -/
noncomputable def sg6R (k : ℕ) : PolyTimeFun ι Fml :=
  ap₁ Fml.inpF (ap₁ unaryToBin (ap₂ addU (sgOff6U eu la lb lc) (const (unary k))))

@[simp] theorem sg6R_apply (k : ℕ) (i : ι) :
    sg6R eu la lb lc k i =
      t₀F (la i).length (lb i).length (lc i).length (mOf (eu i).length Gc) k := by
  rw [sg6R, ap₁_apply, Fml.inpF_apply, ap₁_apply, unaryToBin_apply, ap₂_apply, length_addU,
    length_sgOff6U, const_apply, length_unary, t₀F]

/-- The three window indices, zero-padded, and the three witness indices. -/
noncomputable def kR₁ : PolyTimeFun ι (List Fml) :=
  ap₂ padToP (mU eu) (ap₂ fieldP (const 0) la)
noncomputable def kR₂ : PolyTimeFun ι (List Fml) :=
  ap₂ padToP (mU eu) (ap₂ fieldP (ap₁ unaryToBin la) lb)
noncomputable def kR₃ : PolyTimeFun ι (List Fml) :=
  ap₂ padToP (mU eu) (ap₂ fieldP (ap₁ unaryToBin (ap₂ addU la lb)) lc)
noncomputable def kR₄ : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin (wOffU la lb lc)) (mU eu)
noncomputable def kR₅ : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin (ap₂ addU (wOffU la lb lc) (mU eu))) (mU eu)
noncomputable def kR₆ : PolyTimeFun ι (List Fml) :=
  ap₂ fieldP (ap₁ unaryToBin (ap₂ addU (wOffU la lb lc) (ap₁ (nsmulU 2) (mU eu)))) (mU eu)

@[simp] theorem kR₁_apply (i : ι) :
    kR₁ eu la i = k₁F (la i).length (mOf (eu i).length Gc) := by
  rw [kR₁, ap₂_apply, padToP_apply, ap₂_apply, fieldP_apply, length_mU, const_apply, k₁F]

@[simp] theorem kR₂_apply (i : ι) :
    kR₂ eu la lb i = k₂F (la i).length (lb i).length (mOf (eu i).length Gc) := by
  rw [kR₂, ap₂_apply, padToP_apply, ap₂_apply, fieldP_apply, length_mU, ap₁_apply,
    unaryToBin_apply, k₂F]

@[simp] theorem kR₃_apply (i : ι) :
    kR₃ eu la lb lc i =
      k₃F (la i).length (lb i).length (lc i).length (mOf (eu i).length Gc) := by
  rw [kR₃, ap₂_apply, padToP_apply, ap₂_apply, fieldP_apply, length_mU, ap₁_apply,
    unaryToBin_apply, ap₂_apply, length_addU, k₃F]

@[simp] theorem kR₄_apply (i : ι) :
    kR₄ eu la lb lc i =
      k₄F (la i).length (lb i).length (lc i).length (mOf (eu i).length Gc) := by
  rw [kR₄, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, length_wOffU, length_mU, k₄F]

@[simp] theorem kR₅_apply (i : ι) :
    kR₅ eu la lb lc i =
      k₅F (la i).length (lb i).length (lc i).length (mOf (eu i).length Gc) := by
  rw [kR₅, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, ap₂_apply, length_addU,
    length_wOffU, length_mU, k₅F]

@[simp] theorem kR₆_apply (i : ι) :
    kR₆ eu la lb lc i =
      k₆F (la i).length (lb i).length (lc i).length (mOf (eu i).length Gc) := by
  rw [kR₆, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, ap₂_apply, length_addU,
    length_wOffU, ap₁_apply, length_nsmulU, length_mU, k₆F]

/-- `2^ℓa` on `r` bits. -/
noncomputable def pow2aR : PolyTimeFun ι BitStr := nbitsR (mU eu) (ap₁ natBits (ap₁ pow2P la))

@[simp] theorem pow2aR_apply (i : ι) :
    pow2aR eu la i = nbits (mOf (eu i).length Gc) (2 ^ (la i).length) := by
  rw [pow2aR, nbitsR_num, length_mU, ap₁_apply, pow2P_apply]

/-- `link6Fml`. -/
noncomputable def link6FmlR : PolyTimeFun ι Fml :=
  orR [
    andR [eqF (kR₁ eu la) (kR₄ eu la lb lc), xorR (sg6R eu la lb lc 0) (sg6R eu la lb lc 3)],
    andR [addRelR (kR₂ eu la lb) (kR₄ eu la lb lc) (twoTR eu TR),
      xorR (sg6R eu la lb lc 1) (sg6R eu la lb lc 3)],
    andR [addRelR (kR₃ eu la lb lc) (kR₄ eu la lb lc) (pow2aR eu la),
      xorR (sg6R eu la lb lc 2) (sg6R eu la lb lc 3)],
    andR [eqF (kR₄ eu la lb lc) (kR₅ eu la lb lc), xorR (sg6R eu la lb lc 3) (sg6R eu la lb lc 4)],
    andR [eqF (kR₅ eu la lb lc) (kR₆ eu la lb lc), xorR (sg6R eu la lb lc 4) (sg6R eu la lb lc 5)]]

theorem link6FmlR_apply (i : ι) :
    link6FmlR eu TR la lb lc i =
      link6Fml (la i).length (lb i).length (lc i).length (mOf (eu i).length Gc) (TR i) := by
  simp only [link6FmlR, link6Fml, orR_apply, andR_apply, List.map_cons, List.map_nil,
    eqF_apply, xorR_apply, addRelR_apply, kR₁_apply, kR₂_apply, kR₃_apply, kR₄_apply, kR₅_apply,
    kR₆_apply, twoTR_apply, pow2aR_apply, sg6R_apply]

/-- `candOf6`. -/
noncomputable def candR6 : CandR ι where
  A₁ := litFieldsR eu TR (wOffU la lb lc)
  σ₁ := sg6R eu la lb lc 3
  A₂ := litFieldsR eu TR (ap₂ addU (wOffU la lb lc) (mU eu))
  σ₂ := sg6R eu la lb lc 4
  A₃ := litFieldsR eu TR (ap₂ addU (wOffU la lb lc) (ap₁ (nsmulU 2) (mU eu)))
  σ₃ := sg6R eu la lb lc 5

theorem candR6_ev (i : ι) :
    (candR6 eu TR la lb lc).ev i =
      candOf6 (wOff (la i).length (lb i).length (lc i).length) (eu i).length (TR i) := by
  have h : ∀ k, sg6R eu la lb lc k i = Fml.inp (wOff (la i).length (lb i).length (lc i).length +
      3 * mOf (eu i).length Gc + k) := by
    intro k
    rw [sg6R_apply]
    rfl
  simp only [CandR.ev, candR6, candOf6, CandF.mk.injEq]
  refine ⟨?_, h 3, ?_, h 4, ?_, h 5⟩
  · rw [litFieldsR_ev, length_wOffU]
  · rw [litFieldsR_ev, ap₂_apply, length_addU, length_wOffU, length_mU]
  · rw [litFieldsR_ev, ap₂_apply, length_addU, length_wOffU, ap₁_apply, length_nsmulU,
      length_mU]

/-- `descFml6`. -/
noncomputable def descFml6R (DR : PolyTimeFun ι Prog) (nR : PolyTimeFun ι ℕ)
    (xR yR : PolyTimeFun ι BitStr) : PolyTimeFun ι Fml :=
  orTwo (tableauPlusR eu TR (candR6 eu TR la lb lc)
    (tabsR eu TR (wOffU la lb lc) DR nR xR yR) (const [5, 6])) (link6FmlR eu TR la lb lc)

theorem descFml6R_apply (DR : PolyTimeFun ι Prog) (nR : PolyTimeFun ι ℕ)
    (xR yR : PolyTimeFun ι BitStr) (i : ι) :
    descFml6R eu TR la lb lc DR nR xR yR i =
      descFml6 (la i).length (lb i).length (lc i).length (TR i) (eu i).length (DR i) (nR i)
        (xR i) (yR i) := by
  rw [descFml6R, orTwo_apply, tableauPlusR_apply, candR6_ev, tabsR_apply, length_wOffU,
    link6FmlR_apply, descFml6, descBody6, const_apply]

end Prog6

/-! ## The describer in the structure's argument order -/

noncomputable def w6a : PolyTimeFun Desc6Input Unary := ap₁ fst fst
noncomputable def w6b : PolyTimeFun Desc6Input Unary := ap₁ fst (ap₁ snd fst)
noncomputable def w6c : PolyTimeFun Desc6Input Unary := ap₁ snd (ap₁ snd fst)

@[simp] theorem w6a_apply (p : Desc6Input) : w6a p = p.1.1 := rfl
@[simp] theorem w6b_apply (p : Desc6Input) : w6b p = p.1.2.1 := rfl
@[simp] theorem w6c_apply (p : Desc6Input) : w6c p = p.1.2.2 := rfl

/-- **The windowed describer, as a program** (slice P4g, item 4). -/
noncomputable def describe6P : PolyTimeFun Desc6Input Circuit :=
  ap₂ Fml.toCircuitF
    (ap₁ unaryToBin (ap₂ addU (ap₂ addU (wOffU w6a w6b w6c) (ap₁ (nsmulU 3) (mU (dEu.comp snd))))
      (const (unary 6))))
    (descFml6R (dEu.comp snd) (dTR.comp snd) w6a w6b w6c (dDR.comp snd) (dnR.comp snd)
      (dxR.comp snd) (dyR.comp snd))

theorem describe6P_apply (p : Desc6Input) :
    describe6P p = descCirc6 p.1.1.length p.1.2.1.length p.1.2.2.length p.2.1.2.2.1
      (eOf p.2.1.2.2.1 p.2.1.2.2.2.2) p.2.1.1 p.2.1.2.1 p.2.2.1 p.2.2.2 := by
  rw [describe6P, ap₂_apply, Fml.toCircuitF_apply, descFml6R_apply, ap₁_apply, unaryToBin_apply,
    ap₂_apply, length_addU, ap₂_apply, length_addU, length_wOffU, ap₁_apply, length_nsmulU,
    length_mU, const_apply, length_unary]
  simp only [comp_apply, length_dEu, dTR_apply, dDR_apply, dnR_apply, dxR_apply, dyR_apply,
    w6a_apply, w6b_apply, w6c_apply, descCirc6, wOff]
  rfl

/-! ## The gate bound -/

/-- The constant of `mParam_le`. -/
noncomputable abbrev mK : ℕ := 431 + Qb + Gb Gc + 75

theorem esize_desc6Input_le (ua ub uc : Unary) (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (ha : ua.length ≤ mParam T σ) (hb : ub.length ≤ mParam T σ)
    (hc : uc.length ≤ mParam T σ) :
    esize (((ua, ub, uc), (D, n, T, Q, σ), x, y) : Desc6Input) ≤
      (6 * mK + 25) * LOf n T Q σ + (6 * mK + 18) := by
  have h0 := esize_descInput_le D n T Q σ x y hV
  have hu : ∀ u : Unary, esize u = 2 * u.length + 1 := fun u => by
    rw [← unary_length u, esize_unary, length_unary]
  have hm := mParam_le T σ
  have hsz : Nat.size T + Nat.size σ + 1 ≤ LOf n T Q σ + 1 := by
    have := size_le_self σ
    unfold LOf; omega
  have hm' : mParam T σ ≤ mK * (LOf n T Q σ + 1) :=
    hm.trans (Nat.mul_le_mul_left _ hsz)
  have h : esize (((ua, ub, uc), (D, n, T, Q, σ), x, y) : Desc6Input) =
      esize ua + esize ub + esize uc + esize (((D, n, T, Q, σ), x, y) : DescInput) + 3 := by
    simp only [esize_prod]
    omega
  rw [h, hu, hu, hu]
  have : mK * (LOf n T Q σ + 1) = mK * LOf n T Q σ + mK := by ring
  nlinarith

/-- The time bound of the windowed describer at a linear majorant of its input size. -/
noncomputable def gatePoly6 : Polynomial ℕ :=
  describe6P.timeBound.comp
    (Polynomial.C (6 * mK + 25) * Polynomial.X + Polynomial.C (6 * mK + 18))

/-- **The windowed describer is small** (item 3). -/
theorem describe6P_size_le (ua ub uc : Unary) (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) (ha : ua.length ≤ mParam T σ) (hb : ub.length ≤ mParam T σ)
    (hc : uc.length ≤ mParam T σ) :
    (describe6P ((ua, ub, uc), (D, n, T, Q, σ), x, y)).size ≤ roundUp gatePoly6 n T Q σ := by
  have h1 : (describe6P ((ua, ub, uc), (D, n, T, Q, σ), x, y)).size ≤
      describe6P.timeBound.eval (esize (((ua, ub, uc), (D, n, T, Q, σ), x, y) : Desc6Input)) :=
    (size_le_esize _).trans (describe6P.esize_apply_le _)
  have h2 := polynomial_eval_mono describe6P.timeBound
    (esize_desc6Input_le ua ub uc D n T Q σ x y hV ha hb hc)
  have h3 : describe6P.timeBound.eval ((6 * mK + 25) * LOf n T Q σ + (6 * mK + 18)) =
      gatePoly6.eval (LOf n T Q σ) := by
    rw [gatePoly6, Polynomial.eval_comp]
    simp
  exact ((h1.trans h2).trans (le_of_eq h3)).trans (le_roundUp gatePoly6 n T Q σ)

/-! ## The parameters as programs -/

noncomputable def params6 : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) (ℕ × ℕ) :=
  (describeM.comp ((ap₁ fst snd).pair (ap₁ snd (ap₁ snd snd)))).pair (roundUpProg gatePoly6)

theorem params6_apply (n T Q σ : ℕ) :
    params6 (n, T, Q, σ) = (mParam T σ, roundUp gatePoly6 n T Q σ) := by
  rw [params6, pair_apply, comp_apply, describeM_apply, roundUpProg_apply]
  rfl

end MIPRE.TM.CookLevin.Desc

namespace MIPRE.SAT

open Cost TM.CookLevin.Desc

/-- **Succinct decoupled descriptions of deciders through three windows** (slice P4g; paper
II's `prop:explicit-padded-succinct-deciders`, whose proof the paper only sketches): the
structure is inhabited. -/
noncomputable def windowDescriber : WindowDescriber where
  r₀ := mParam
  s₀ := roundUp gatePoly6
  describe := describe6P
  params := params6
  params_eq n T Q σ := params6_apply n T Q σ
  r₀_le := ⟨mK, mParam_le⟩
  four_mul_le T σ := four_T_le_m T σ
  s₀_le := ⟨roundPoly gatePoly6, fun n T Q σ => roundUp_le gatePoly6 n T Q σ⟩
  inputs_eq ua ub uc D n T Q σ x y := by
    rw [describe6P_apply]
    exact descCirc6_inputs _ _ _ _ _ _ _ _ _
  wellFormed inp := by
    obtain ⟨⟨ua, ub, uc⟩, ⟨D, n, T, Q, σ⟩, x, y⟩ := inp
    rw [describe6P_apply]
    exact descCirc6_wellFormed _ _ _ _ _ _ _ _ _
  size_le ua ub uc D n T Q σ x y hV ha hb hc := describe6P_size_le ua ub uc D n T Q σ x y hV ha hb hc
  describes ua ub uc 𝒟 n T Q σ x y hV hwac hwb ha hb hc := by
    rw [describe6P_apply]
    exact describes6 𝒟 ua.length ub.length uc.length T (eOf T σ) n x y hwac hwb ha hb hc
      (four_T_le_m T σ) (T_le_Sof T σ) (fixedLen_of_valid 𝒟.prog n T Q σ x y hV)
      (T_add_three_lt T σ)
      (fun ap bp hap hbp => runBound_le_two_pow 𝒟.prog n T Q σ x y ap bp hV hap hbp)

end MIPRE.SAT

end
