/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.DescProg
import MIPRE.TM.CookLevin.Sat
import MIPRE.Foundations.Cost.Growth

/-!
# Assembling the succinct Cook–Levin theorem

`MIPRE.SAT.succinctCookLevin` inhabits `SuccinctCookLevin`, which is blueprint
`thm:succinct-sat`. Everything mathematical is already proved; what is left is to discharge,
from the validity hypotheses, the side conditions the describer's theorems carry at
`e = eOf T σ`, and to name the two parameter functions.

* `T ≤ Sof (eOf T σ)`, `T + 3 < 2 ^ W (eOf T σ)` and `FixedLen`: the five fixed tapes are
  shorter than the tableau, since `|𝒟| ≤ σ < 2 ^ ⌈log σ⌉` and `2 ⌈log n⌉ ≤ T`, `|x|, |y| ≤ Q
  ≤ T`, and `eOf` has `5 ⌈log T⌉ + 5 ⌈log σ⌉ + 24` in the exponent.
* `4 T ≤ 2 ^ m`: an answer index is below `2 ^ flagOff`, and `flagOff < m`.
* The gate bound: the time bound of the program, evaluated at a linear majorant of the size of
  its input. To make it *computable from the parameters in time polynomial in their bit
  lengths* (item 5) it is rounded up to a power of two, `s = 2 ^ (k · r + c)` with
  `r = ⌈log ⌈log n⌉⌉ + ⌈log ⌈log T⌉⌉ + ⌈log Q⌉ + ⌈log σ⌉`: that needs no arithmetic on
  numbers, only `pow2P` on a unary exponent, and it is squeezed between the true gate count
  and a polynomial in `⌈log n⌉ + ⌈log T⌉ + Q + σ` (`planning/succinct-cook-levin.md`, S4).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Cost.PolyTimeFun

/-! ## Sizes of encodings -/

theorem esize_nat_le (k : ℕ) : esize k ≤ 4 * Nat.size k + 1 := by
  have h : esize k = esize k.bits := rfl
  have h2 := esize_bitStr_le k.bits
  rw [Nat.size_eq_bits_len] at h2
  rw [h]
  exact h2

theorem size_le_self (k : ℕ) : Nat.size k ≤ k := Nat.size_le.2 Nat.lt_two_pow_self

/-! ## The tableau is long enough -/

theorem two_pow_le_Sof (T σ k : ℕ) (h : k ≤ eOf T σ) : 2 ^ k ≤ Sof (eOf T σ) :=
  Nat.pow_le_pow_right (by omega) h

theorem T_le_Sof (T σ : ℕ) : T ≤ Sof (eOf T σ) := by
  have h1 := Nat.lt_size_self T
  have h2 := two_pow_le_Sof T σ (Nat.size T) (by unfold eOf; omega)
  omega

theorem four_T_add_one_le_Sof (T σ : ℕ) : 4 * T + 1 ≤ Sof (eOf T σ) := by
  have h1 := Nat.lt_size_self T
  have h2 := two_pow_le_Sof T σ (Nat.size T + 2) (by unfold eOf; omega)
  have h3 : (2 : ℕ) ^ (Nat.size T + 2) = 4 * 2 ^ Nat.size T := by rw [pow_add]; ring
  omega

theorem sigma_le_Sof (T σ : ℕ) : σ ≤ Sof (eOf T σ) := by
  have h1 := Nat.lt_size_self σ
  have h2 := two_pow_le_Sof T σ (Nat.size σ) (by unfold eOf; omega)
  omega

theorem T_add_three_lt (T σ : ℕ) : T + 3 < 2 ^ W (eOf T σ) := by
  have hT := T_le_Sof T σ
  have h1 : (2 : ℕ) ^ W (eOf T σ) = 16 * Sof (eOf T σ) := by
    unfold W Sof; rw [pow_add]; ring
  have h2 : 0 < Sof (eOf T σ) := Nat.two_pow_pos _
  omega

/-- The five fixed input tapes are shorter than the tableau. -/
theorem fixedLen_of_valid (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) : FixedLen (eOf T σ) D n T x y := by
  have hT := T_le_Sof T σ
  have h4T := four_T_add_one_le_Sof T σ
  have hσ := sigma_le_Sof T σ
  have hD : esize D ≤ Sof (eOf T σ) := le_trans hV.size_le hσ
  have hn : esize n ≤ Sof (eOf T σ) := by
    have := esize_nat_le n
    have := hV.logn_le
    omega
  have hx : esize x ≤ Sof (eOf T σ) := by
    have := esize_bitStr_le x
    have := hV.x_le
    have := hV.q_le
    omega
  have hy : esize y ≤ Sof (eOf T σ) := by
    have := esize_bitStr_le y
    have := hV.y_le
    have := hV.q_le
    omega
  intro j s hj
  fin_cases j <;> simp [fixedOf] at hj
  all_goals subst hj
  all_goals simp only [length_S, List.length_replicate]
  · exact hD
  · exact hn
  · exact hT
  · exact hx
  · exact hy

/-- An answer index is below `2 ^ m`. -/
theorem four_T_le_m (T σ : ℕ) : 4 * T ≤ 2 ^ mOf (eOf T σ) Gc := by
  refine le_trans (four_T_le_flag (eOf T σ) Gc T (T_le_Sof T σ)) ?_
  exact Nat.pow_le_pow_right (by omega) (flag_lt_m (eOf T σ) Gc).le

/-! ## The describer in the order the structure asks for -/

/-- `((𝒟, n, T, Q, σ), x, y)` reordered to `((T, σ), (𝒟, n), (x, y))`. -/
noncomputable def toPInp : PolyTimeFun DescInput PInp :=
  let pR : PolyTimeFun DescInput (Prog × ℕ × ℕ × ℕ × ℕ) := fst
  let DR : PolyTimeFun DescInput Prog := ap₁ fst pR
  let nR : PolyTimeFun DescInput ℕ := ap₁ fst (ap₁ snd pR)
  let TR : PolyTimeFun DescInput ℕ := ap₁ fst (ap₁ snd (ap₁ snd pR))
  let σR : PolyTimeFun DescInput ℕ := ap₁ snd (ap₁ snd (ap₁ snd (ap₁ snd pR)))
  (TR.pair σR).pair ((DR.pair nR).pair ((ap₁ fst snd).pair (ap₁ snd snd)))

@[simp] theorem toPInp_apply (inp : DescInput) :
    toPInp inp = ((inp.1.2.2.1, inp.1.2.2.2.2), (inp.1.1, inp.1.2.1), inp.2.1, inp.2.2) := rfl

/-- **The describer, in the structure's argument order.** -/
noncomputable def describeCirc : PolyTimeFun DescInput Circuit := describeP.comp toPInp

theorem describeCirc_apply (D : Prog) (n T Q σ : ℕ) (x y : BitStr) :
    describeCirc ((D, n, T, Q, σ), x, y) = descCirc (eOf T σ) T D n x y := by
  rw [describeCirc, comp_apply, describeP_apply, toPInp_apply]

/-! ## The size of the describer's input -/

/-- The parameter the gate bound is a polynomial in. -/
def LOf (n T Q σ : ℕ) : ℕ := Nat.size n + Nat.size T + Q + σ

theorem esize_toPInp_le (D : Prog) (n T Q σ : ℕ) (x y : BitStr) (hV : Valid D n T Q σ x y) :
    esize (toPInp ((D, n, T, Q, σ), x, y)) ≤ 21 * LOf n T Q σ + 10 := by
  have h : esize (toPInp ((D, n, T, Q, σ), x, y)) =
      esize T + esize σ + esize D + esize n + esize x + esize y + 5 := by
    rw [toPInp_apply]
    simp only [esize_prod]
    omega
  have hT := esize_nat_le T
  have hσ := esize_nat_le σ
  have hσ' := size_le_self σ
  have hn := esize_nat_le n
  have hx := esize_bitStr_le x
  have hy := esize_bitStr_le y
  have h1 := hV.size_le
  have h2 := hV.x_le
  have h3 := hV.y_le
  unfold LOf
  omega

/-! ## The two parameter functions -/

/-- The variable-count exponent `m(T, σ)`. -/
noncomputable def mParam (T σ : ℕ) : ℕ := mOf (eOf T σ) Gc

theorem mParam_eq (T σ : ℕ) :
    mParam T σ = 431 + Qb + Gb Gc + 75 * Nat.size T + 75 * Nat.size σ := by
  unfold mParam mOf W eOf
  ring

theorem mParam_le (T σ : ℕ) :
    mParam T σ ≤ (431 + Qb + Gb Gc + 75) * (Nat.size T + Nat.size σ + 1) := by
  rw [mParam_eq]
  have h1 : 75 * Nat.size T ≤ (431 + Qb + Gb Gc + 75) * Nat.size T :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 75 * Nat.size σ ≤ (431 + Qb + Gb Gc + 75) * Nat.size σ :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : (431 + Qb + Gb Gc + 75) * (Nat.size T + Nat.size σ + 1) =
      (431 + Qb + Gb Gc + 75) * Nat.size T + (431 + Qb + Gb Gc + 75) * Nat.size σ +
        (431 + Qb + Gb Gc + 75) := by ring
  omega

/-- The bit lengths of the parameters: the exponent of the gate bound is a multiple of this,
which is why the bound is computable without any arithmetic on numbers. -/
def rParam (n T Q σ : ℕ) : ℕ :=
  Nat.size (Nat.size n) + Nat.size (Nat.size T) + Nat.size Q + Nat.size σ

/-! ### Rounding a polynomial bound up to a power of two

Item 5 asks for the gate bound to be computable in time polynomial in the *bit lengths* of
the parameters, while item 3 lets it grow polynomially in `Q` and `σ` themselves. So the
bound is a number of about `log Q + log σ` bits that depends polynomially on `Q`, and
computing it looks as though it needs binary multiplication, which the ambient model does not
have. `roundUp P` is the way out: a power of two whose exponent is a multiple of `rParam`, so
that the exponent is unary and the value is `pow2P` on it. It is squeezed between `P` and a
polynomial, which is `le_roundUp` and `roundUp_le`. -/

/-- The degree of a polynomial bound. -/
noncomputable def roundK (P : Polynomial ℕ) : ℕ := P.natDegree

/-- The coefficient sum of a polynomial bound. -/
noncomputable def roundA (P : Polynomial ℕ) : ℕ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i

/-- The additive constant of the rounded bound. -/
noncomputable def roundC (P : Polynomial ℕ) : ℕ := Nat.size (roundA P * 5 ^ roundK P)

/-- **A polynomial bound, rounded up to a power of two** whose exponent is a multiple of the
bit lengths of the parameters. -/
noncomputable def roundUp (P : Polynomial ℕ) (n T Q σ : ℕ) : ℕ :=
  2 ^ (roundK P * rParam n T Q σ + roundC P)

theorem L_lt (n T Q σ : ℕ) : LOf n T Q σ + 1 ≤ 5 * 2 ^ rParam n T Q σ := by
  have h0 : 0 < (2 : ℕ) ^ rParam n T Q σ := Nat.two_pow_pos _
  have h1 : Nat.size n < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  have h2 : Nat.size T < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  have h3 : Q < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  have h4 : σ < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  unfold LOf
  omega

/-- **The rounded bound dominates the polynomial.** -/
theorem le_roundUp (P : Polynomial ℕ) (n T Q σ : ℕ) :
    P.eval (LOf n T Q σ) ≤ roundUp P n T Q σ := by
  have h1 : P.eval (LOf n T Q σ) ≤ P.eval (LOf n T Q σ + 1) :=
    polynomial_eval_mono _ (by omega)
  have h2 : P.eval (LOf n T Q σ + 1) ≤ roundA P * (LOf n T Q σ + 1) ^ roundK P :=
    polynomial_eval_le_sum_coeff_mul_pow P (by omega)
  have h3 : (LOf n T Q σ + 1) ^ roundK P ≤ (5 * 2 ^ rParam n T Q σ) ^ roundK P :=
    Nat.pow_le_pow_left (L_lt n T Q σ) _
  have h4 : ((5 * 2 ^ rParam n T Q σ) ^ roundK P : ℕ) =
      5 ^ roundK P * 2 ^ (roundK P * rParam n T Q σ) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (roundK P)]
  have h5 : roundA P * 5 ^ roundK P < 2 ^ roundC P := Nat.lt_size_self _
  calc P.eval (LOf n T Q σ) ≤ roundA P * (LOf n T Q σ + 1) ^ roundK P := h1.trans h2
    _ ≤ roundA P * (5 ^ roundK P * 2 ^ (roundK P * rParam n T Q σ)) := by
        rw [← h4]; exact Nat.mul_le_mul_left _ h3
    _ = roundA P * 5 ^ roundK P * 2 ^ (roundK P * rParam n T Q σ) := by ring
    _ ≤ 2 ^ roundC P * 2 ^ (roundK P * rParam n T Q σ) := Nat.mul_le_mul_right _ h5.le
    _ = roundUp P n T Q σ := by rw [roundUp, pow_add, Nat.mul_comm]

theorem two_pow_rParam_le (n T Q σ : ℕ) :
    2 ^ rParam n T Q σ ≤ (2 * LOf n T Q σ + 1) ^ 4 := by
  have e1 : (2 : ℕ) ^ rParam n T Q σ = 2 ^ Nat.size (Nat.size n) * 2 ^ Nat.size (Nat.size T) *
      2 ^ Nat.size Q * 2 ^ Nat.size σ := by
    unfold rParam; rw [pow_add, pow_add, pow_add]
  have b1 : (2 : ℕ) ^ Nat.size (Nat.size n) ≤ 2 * LOf n T Q σ + 1 := by
    refine le_trans (two_pow_size_le _) ?_
    have : Nat.size n ≤ LOf n T Q σ := by unfold LOf; omega
    omega
  have b2 : (2 : ℕ) ^ Nat.size (Nat.size T) ≤ 2 * LOf n T Q σ + 1 := by
    refine le_trans (two_pow_size_le _) ?_
    have : Nat.size T ≤ LOf n T Q σ := by unfold LOf; omega
    omega
  have b3 : (2 : ℕ) ^ Nat.size Q ≤ 2 * LOf n T Q σ + 1 := by
    refine le_trans (two_pow_size_le _) ?_
    have : Q ≤ LOf n T Q σ := by unfold LOf; omega
    omega
  have b4 : (2 : ℕ) ^ Nat.size σ ≤ 2 * LOf n T Q σ + 1 := by
    refine le_trans (two_pow_size_le _) ?_
    have : σ ≤ LOf n T Q σ := by unfold LOf; omega
    omega
  rw [e1, show ((2 * LOf n T Q σ + 1) ^ 4 : ℕ) = (2 * LOf n T Q σ + 1) * (2 * LOf n T Q σ + 1) *
      (2 * LOf n T Q σ + 1) * (2 * LOf n T Q σ + 1) by ring]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul b1 b2) b3) b4

/-- The polynomial the rounded bound stays inside. -/
noncomputable def roundPoly (P : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (2 ^ roundC P) *
    (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) ^ (4 * roundK P)

/-- **The rounded bound is still polynomial.** -/
theorem roundUp_le (P : Polynomial ℕ) (n T Q σ : ℕ) :
    roundUp P n T Q σ ≤ (roundPoly P).eval (LOf n T Q σ) := by
  have h2 : (2 : ℕ) ^ (roundK P * rParam n T Q σ) = (2 ^ rParam n T Q σ) ^ roundK P := by
    rw [← pow_mul, Nat.mul_comm]
  have h3 : ((2 ^ rParam n T Q σ) ^ roundK P : ℕ) ≤ ((2 * LOf n T Q σ + 1) ^ 4) ^ roundK P :=
    Nat.pow_le_pow_left (two_pow_rParam_le n T Q σ) _
  have h4 : (((2 * LOf n T Q σ + 1) ^ 4) ^ roundK P : ℕ) =
      (2 * LOf n T Q σ + 1) ^ (4 * roundK P) := by rw [← pow_mul]
  have heval : (roundPoly P).eval (LOf n T Q σ) =
      2 ^ roundC P * (2 * LOf n T Q σ + 1) ^ (4 * roundK P) := by
    rw [roundPoly]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X]
  rw [heval, roundUp, pow_add, Nat.mul_comm (2 ^ (roundK P * rParam n T Q σ))]
  exact Nat.mul_le_mul_left _ (by rw [h2, ← h4]; exact h3)

/-! ### The gate bound of the describer -/

/-- The time bound of the describer at a linear majorant of the size of its input. -/
noncomputable def gatePoly : Polynomial ℕ :=
  describeSize.comp (Polynomial.C 21 * Polynomial.X + Polynomial.C 10)

/-- The gate bound `s(n, T, Q, σ)`, rounded up to a power of two. -/
noncomputable def sParam (n T Q σ : ℕ) : ℕ := roundUp gatePoly n T Q σ

theorem sParam_le (n T Q σ : ℕ) :
    sParam n T Q σ ≤ (roundPoly gatePoly).eval (LOf n T Q σ) := roundUp_le gatePoly n T Q σ

/-- **The describer has at most `s` gates** (item 3). -/
theorem describeCirc_size_le (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) :
    (describeCirc ((D, n, T, Q, σ), x, y)).size ≤ sParam n T Q σ := by
  have h1 : (describeCirc ((D, n, T, Q, σ), x, y)).size ≤
      describeSize.eval (esize (toPInp ((D, n, T, Q, σ), x, y))) := by
    rw [describeCirc, comp_apply]
    exact describe_size_le _
  have h2 := polynomial_eval_mono describeSize (esize_toPInp_le D n T Q σ x y hV)
  have h3 : describeSize.eval (21 * LOf n T Q σ + 10) = gatePoly.eval (LOf n T Q σ) := by
    rw [gatePoly, Polynomial.eval_comp]
    simp
  exact ((h1.trans h2).trans (le_of_eq h3)).trans (le_roundUp gatePoly n T Q σ)

/-! ## The parameters as programs (item 5) -/

/-- `Nat.size`. -/
noncomputable def sizeN : PolyTimeFun ℕ ℕ := ap₁ unaryToBin sizeU

@[simp] theorem sizeN_apply (k : ℕ) : sizeN k = Nat.size k := by
  rw [sizeN, ap₁_apply, unaryToBin_apply, length_sizeU]

/-- `rParam`, in unary. -/
noncomputable def rProg : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) Unary :=
  ap₂ addU (ap₂ addU (ap₂ addU (ap₁ sizeU (ap₁ sizeN fst)) (ap₁ sizeU (ap₁ sizeN (ap₁ fst snd))))
    (ap₁ sizeU (ap₁ fst (ap₁ snd snd)))) (ap₁ sizeU (ap₁ snd (ap₁ snd snd)))

@[simp] theorem length_rProg (p : ℕ × ℕ × ℕ × ℕ) :
    (rProg p).length = rParam p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [rProg, rParam]
  omega

/-- `sParam`, as a program: a power of two whose exponent is unary, so no arithmetic on
numbers is needed. -/
noncomputable def sProg : PolyTimeFun (ℕ × ℕ × ℕ × ℕ) ℕ :=
  ap₁ pow2P (ap₂ addU (ap₁ (nsmulU (roundK gatePoly)) rProg)
    (const (unary (roundC gatePoly))))

theorem sProg_apply (p : ℕ × ℕ × ℕ × ℕ) : sProg p = sParam p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  rw [sProg, ap₁_apply, pow2P_apply, ap₂_apply, length_addU, ap₁_apply, length_nsmulU,
    length_rProg, const_apply, length_unary, sParam, roundUp]

end MIPRE.TM.CookLevin.Desc

namespace MIPRE.SAT

open Cost TM.CookLevin.Desc

/-- **The succinct Cook–Levin theorem** (blueprint `thm:succinct-sat`; the paper's
`prop:standard-succinct-sat`): the structure is inhabited. -/
noncomputable def succinctCookLevin : SuccinctCookLevin where
  m := mParam
  s := sParam
  describe := describeCirc
  mProg := describeM
  mProg_eq T σ := by rw [describeM_apply]; rfl
  sProg := sProg
  sProg_eq n T Q σ := sProg_apply (n, T, Q, σ)
  m_le := ⟨431 + Qb + Gb Gc + 75, mParam_le⟩
  four_mul_le T σ := four_T_le_m T σ
  s_le := ⟨roundPoly gatePoly, fun n T Q σ => sParam_le n T Q σ⟩
  inputs_eq D n T Q σ x y := by
    rw [describeCirc_apply]
    exact descCirc_inputs _ _ _ _ _ _
  wellFormed inp := by
    obtain ⟨⟨D, n, T, Q, σ⟩, x, y⟩ := inp
    rw [describeCirc_apply]
    exact descCirc_wellFormed _ _ _ _ _ _
  size_le D n T Q σ x y hV := describeCirc_size_le D n T Q σ x y hV
  accepts_iff 𝒟 n T Q σ x y hV a b := by
    rw [describeCirc_apply]
    exact extendsAnswers_iff 𝒟 n T x y (eOf T σ) (T_le_Sof T σ)
      (fixedLen_of_valid 𝒟.prog n T Q σ x y hV) (T_add_three_lt T σ)
      (fun ap bp hap hbp => runBound_le_two_pow 𝒟.prog n T Q σ x y ap bp hV hap hbp)
      (four_T_le_m T σ) a b

end MIPRE.SAT
