/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Paper.Cost
import MIPRE.Foundations.Halting.Paper.Induction
import MIPRE.Foundations.Halting.Paper.Stages

/-!
# Building the decider `𝒟^halt` from `(M, λ)`, in polynomial time

The class verifier of the polynomial-time halting reduction runs, on input `z`, the verifier
`𝒱^halt M λ` of `Paper/Decider.lean` for the machine `M = R z` at the parameter
`λ = Λ₀ + 4|M|`; so it must compute the description of `dec M λ` from `M` and `λ`. That
description is a fixed tree with `M`'s and `λ`'s encodings at two positions (`Paper/Size.lean`
computed its size): `dec M λ = hardcode K (encode K)` for `K = kleeneProg univ F`, and `F`'s
code holds `body`, `M` and `λ` as constants. `decBuild` assembles the tree with `pair` and
`const` over `Data` (`kleeneData`, `fcodeData`, `fixData` are the three shapes) and is a
`PolyTimeFun (Prog × ℕ) Prog`. Beside it, `lamF` computes the parameter `Λ₀ + 4|M|` and
`cutF K D` the answer cutoff `2 ^ (K + D · |λ|)` that the class decider applies before running
`𝒱^halt`'s decider — a power of two so that it can be computed from `|λ|` in unary
(`expBits`), and polynomial in `λ` since `2 ^ |λ| ≤ 32 λ ^ 4`.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-! ## The three shapes -/

/-- The description of `F.code` from those of `body`, `M` and `λ`. -/
def fcodeData (bodyD MD lamD : Data) : Data :=
  .cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) bodyD) (.cons (.ofNat 2)
    (.cons (.cons (.ofNat 6) MD) (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) lamD)
      (.cons (.ofNat 0) (.ofNat 0)))))))) smnProg.toData)

theorem toData_F_code (S' M : Prog) (lam : ℕ) :
    (F G U UT S' M lam).code.toData =
      fcodeData (body G U UT S').toData M.toData (encode lam) := rfl

/-- The description of `kleeneProg univ F` from those of `univ` and `F.code`. -/
def kleeneData (univD fD : Data) : Data :=
  .cons (.ofNat 3) (.cons (.ofNat 0) (.cons (.cons (.ofNat 1) .nil) (.cons (.ofNat 4)
    (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 0) (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 0))))
      (.cons (.ofNat 4) (.cons (.cons (.ofNat 4) (.cons (.cons (.ofNat 0) (.ofNat 0))
        smnProg.toData)) (.cons (.ofNat 4) (.cons (.cons (.ofNat 4) (.cons (.cons (.ofNat 0)
          (.ofNat 0)) fD)) (.cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 0)
            (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 4)))) (.cons (.ofNat 4) (.cons (.cons (.ofNat 0)
              (.ofNat 0)) univD))))))))))))

theorem toData_kleeneProg (univ : Prog) (F : PolyTimeFun Prog Prog) :
    (kleeneProg univ F).toData = kleeneData univ.toData F.code.toData := rfl

/-- The description of `hardcode K (encode K)` from that of `K`. -/
def fixData (kD : Data) : Data :=
  .cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) kD) (.cons .nil .nil))) kD)

theorem toData_kleeneFix (F : PolyTimeFun Prog Prog) :
    (kleeneFix U F).toData = fixData (kleeneProg U.univ F).toData := rfl

/-! ## The shapes as polynomial-time functions -/

/-- `fcodeData bodyD` on `(M, λ)`, as nested pairs of `Data`. -/
noncomputable def fcodeF (bodyD : Data) : PolyTimeFun (Prog × ℕ) Data :=
  cast (pair (const (Data.ofNat 4)) (pair (pair (const (Data.ofNat 2))
    (pair (pair (const (Data.ofNat 6)) (const bodyD)) (pair (const (Data.ofNat 2))
      (pair (pair (const (Data.ofNat 6)) (progData.comp fst)) (pair (const (Data.ofNat 2))
        (pair (pair (const (Data.ofNat 6)) (natData.comp snd))
          (const (Data.cons (.ofNat 0) (.ofNat 0)))))))))
    (const smnProg.toData)))
    (fun p => fcodeData bodyD p.1.toData (encode p.2)) (fun _ => rfl)

@[simp] theorem fcodeF_apply (bodyD : Data) (p : Prog × ℕ) :
    fcodeF bodyD p = fcodeData bodyD p.1.toData (encode p.2) := rfl

/-- `kleeneData univD` on `fD`, as nested pairs of `Data`. -/
noncomputable def kleeneF (univD : Data) : PolyTimeFun Data Data :=
cast (pair (const (Data.ofNat 3)) (pair (const (Data.ofNat 0)) (pair (const (Data.cons (.ofNat
    1) .nil)) (pair (const (Data.ofNat 4)) (pair (const (Data.cons (.ofNat 2) (.cons (.cons
    (.ofNat 0) (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 0))))) (pair (const (Data.ofNat 4)) (pair
    (const (Data.cons (.ofNat 4) (.cons (.cons (.ofNat 0) (.ofNat 0)) smnProg.toData))) (pair
    (const (Data.ofNat 4)) (pair (pair (const (Data.ofNat 4)) (pair (const (Data.cons (.ofNat 0)
    (.ofNat 0))) (id Data))) (pair (const (Data.ofNat 4)) (pair (const (Data.cons (.ofNat 2)
    (.cons (.cons (.ofNat 0) (.ofNat 0)) (.cons (.ofNat 0) (.ofNat 4))))) (const (Data.cons
    (.ofNat 4) (.cons (.cons (.ofNat 0) (.ofNat 0)) univD))))))))))))))
    (kleeneData univD) (fun _ => rfl)

@[simp] theorem kleeneF_apply (univD fD : Data) : kleeneF univD fD = kleeneData univD fD := rfl

/-- `fixData` on `kD`, as nested pairs of `Data`. -/
noncomputable def fixF : PolyTimeFun Data Data :=
  cast (pair (const (Data.ofNat 4)) (pair (pair (const (Data.ofNat 2))
    (pair (pair (const (Data.ofNat 6)) (id Data)) (const (Data.cons .nil .nil)))) (id Data)))
    fixData (fun _ => rfl)

@[simp] theorem fixF_apply (kD : Data) : fixF kD = fixData kD := rfl

/-- **The decider's description from `(M, λ)`**, in polynomial time. -/
noncomputable def decBuild (S' : Prog) : PolyTimeFun (Prog × ℕ) Prog :=
  cast (fixF.comp ((kleeneF U.univ.toData).comp (fcodeF (body G U UT S').toData)))
    (fun p => dec G U UT S' p.1 p.2) (fun p => by
      show (dec G U UT S' p.1 p.2).toData = _
      rw [dec, toData_kleeneFix, toData_kleeneProg, toData_F_code]
      rfl)

@[simp] theorem decBuild_apply (S' : Prog) (p : Prog × ℕ) :
    decBuild G U UT S' p = dec G U UT S' p.1 p.2 := rfl

/-! ## The parameter and the cutoff -/

/-- `M ↦ Λ₀ + 4|M|`: the size of `M` in unary, four copies, plus the constant, read in
binary. -/
noncomputable def lamF (Λ₀ : ℕ) : PolyTimeFun Prog ℕ :=
  addUnary.comp (pair (const Λ₀) ((unaryMul 4).comp (encodedSizeU Prog)))

@[simp] theorem lamF_apply (Λ₀ : ℕ) (M : Prog) : lamF Λ₀ M = Λ₀ + 4 * esize M := by
  show Λ₀ + (unaryMul 4 (unary (esize M))).length = _
  rw [unaryMul_apply]
  simp [unary]

/-- `λ ↦ 2 ^ (K + D · |λ|)`: the answer cutoff of the class decider. -/
noncomputable def cutF (K D : ℕ) : PolyTimeFun ℕ ℕ :=
  expBits.comp ((addConstU K).comp ((unaryMul D).comp (encodedSizeU ℕ)))

@[simp] theorem cutF_apply (K D lam : ℕ) : cutF K D lam = 2 ^ (K + D * esize lam) := by
  show 2 ^ (addConstU K (unaryMul D (unary (esize lam)))).length = _
  rw [unaryMul_apply, addConstU_apply]
  simp [unary]

/-- A bit string of length `k` encodes to at least `2k + 1` nodes. -/
theorem esize_bitStr_ge (l : BitStr) : 2 * l.length + 1 ≤ esize l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [esize_bitStr_cons]
    have := Data.size_pos (Data.ofBool b)
    simp only [List.length_cons]
    omega

/-- A bit string of length `k` encodes to at most `4k + 1` nodes. -/
theorem esize_bitStr_le (l : BitStr) : esize l ≤ 4 * l.length + 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [esize_bitStr_cons]
    have := Data.size_ofBool b
    simp only [List.length_cons]
    omega

/-- The binary length of `n` is at most the size of its encoding. -/
theorem size_le_esize (n : ℕ) : Nat.size n ≤ esize n := by
  have h1 : esize n.bits = esize n := rfl
  have h2 := esize_bitStr_ge n.bits
  rw [← Nat.size_eq_bits_len]
  omega

/-- A polynomial with natural coefficients is at most `A · (x + 1) ^ D`, for `A` the sum of
its coefficients and `D` its degree. -/
theorem polynomial_eval_le (P : Polynomial ℕ) (x : ℕ) :
    P.eval x ≤ (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i) * (x + 1) ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
  calc x ^ i ≤ (x + 1) ^ i := Nat.pow_le_pow_left (by omega) i
    _ ≤ (x + 1) ^ P.natDegree :=
      Nat.pow_le_pow_right (by omega) (by simpa [Nat.lt_succ_iff] using hi)

/-- **The cutoff dominates the compressor's bound**: for `K` large enough in terms of `G` and
`C`, `poly(C, λ) ≤ 2 ^ (K + deg · |λ|)` for every `λ`, where `deg` is the degree of
`G.bound`. -/
theorem exists_cut_ge : ∃ K, ∀ lam : ℕ,
    G.bound.eval (C G + lam) ≤ 2 ^ (K + G.bound.natDegree * esize lam) := by
  set A := ∑ i ∈ Finset.range (G.bound.natDegree + 1), G.bound.coeff i
  set D := G.bound.natDegree
  obtain ⟨K, hK⟩ : ∃ K, A * (C G + 2) ^ D ≤ 2 ^ K :=
    ⟨A * (C G + 2) ^ D, (Nat.lt_two_pow_self).le⟩
  refine ⟨K, fun lam => (polynomial_eval_le _ _).trans ?_⟩
  have h1 : lam < 2 ^ esize lam :=
    (Nat.lt_size_self lam).trans_le
      (Nat.pow_le_pow_right (by norm_num) (size_le_esize lam))
  have h2 : C G + lam + 1 ≤ (C G + 2) * 2 ^ esize lam := by
    have : 1 ≤ 2 ^ esize lam := Nat.one_le_two_pow
    nlinarith
  calc A * (C G + lam + 1) ^ D ≤ A * ((C G + 2) * 2 ^ esize lam) ^ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 D)
    _ = A * (C G + 2) ^ D * 2 ^ (D * esize lam) := by rw [mul_pow, ← pow_mul', mul_assoc]
    _ ≤ 2 ^ K * 2 ^ (D * esize lam) := Nat.mul_le_mul_right _ hK
    _ = 2 ^ (K + D * esize lam) := by rw [← pow_add]

end MIPRE.Halting
