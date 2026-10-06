/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.IndicatorCost
public import MIPRE.Foundations.CL.ProgBuild
public import MIPRE.Foundations.Cost.Growth

@[expose] public section

/-!
# The output indicator at constant parameters

At a fixed index, the parameters `(ℓ, ◇)` of the output indicator are a constant `p`, and the
parameter program is `PolyTimeFun.const p`. Three facts about `lstarProg (const p) L P`:

* its check runs within a polynomial, independent of `p`, of the size of its input plus `esize p`
  (`lstarFinal_const_timeBound`), so the indicator accepts what it accepts within
  `2^(E (k + 1) (τ + ρ + 1))` for one universal constant `E`, when the two programs run within
  `T (|d| + 1)^k` with `T ≤ 2^τ` and the input and `p` have size below `2^ρ`
  (`lstar_const_acceptsWithin_pow`);
* the program is a polynomial-time function of `(L, P, p)` (`lstarProgF`, `lstarProgF_apply`);
* its size is a constant plus `4 |L| + |P| + |p|` (`esize_lstarProg_const`): `L` occurs four
  times, `P` once and `p` once, as the constant the parameter program `const p` outputs.
-/

namespace MIPRE.Tailored.AnsRed

open Cost Cost.PolyTimeFun Polynomial

/-! ## Polynomials below powers -/

/-- Every polynomial over `ℕ` is at most `(x + 2)^D` for some `D`. -/
theorem polynomial_eval_le_add_two_pow (Q : Polynomial ℕ) :
    ∃ D : ℕ, ∀ x : ℕ, Q.eval x ≤ (x + 2) ^ D := by
  set A := ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i
  refine ⟨A + Q.natDegree, fun x => ?_⟩
  have h1 : Q.eval x ≤ Q.eval (x + 1) := polynomial_eval_mono Q (by omega)
  have h2 := polynomial_eval_le_sum_coeff_mul_pow Q (y := x + 1) (by omega)
  have h3 : A ≤ (x + 2) ^ A :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) A)
  have h4 : (x + 1) ^ Q.natDegree ≤ (x + 2) ^ Q.natDegree := Nat.pow_le_pow_left (by omega) _
  calc Q.eval x ≤ A * (x + 1) ^ Q.natDegree := h1.trans h2
    _ ≤ (x + 2) ^ A * (x + 2) ^ Q.natDegree := Nat.mul_le_mul h3 h4
    _ = (x + 2) ^ (A + Q.natDegree) := (pow_add _ _ _).symm

/-! ## The time bound of the check -/

/-- The time bound of the check at the constant parameters `p`, unfolded. -/
theorem lstarFinal_const_timeBound_eq (p : Unary × Unary) :
    (lstarFinal (PolyTimeFun.const p)).timeBound =
      ((X + 1) + (lstarIdx.timeBound + (C (esize p)).comp lstarIdx.timeBound + 1) + 1) +
        lstarCore.timeBound.comp
          ((X + 1) + (lstarIdx.timeBound + (C (esize p)).comp lstarIdx.timeBound + 1) + 1) + 1 :=
  rfl

/-- **The check at constant parameters runs within a polynomial independent of the parameters**,
of the size of its input plus that of the parameters. -/
theorem lstarFinal_const_timeBound : ∃ G : Polynomial ℕ, ∀ (p : Unary × Unary) (A : ℕ),
    (lstarFinal (PolyTimeFun.const p)).timeBound.eval A ≤ G.eval (A + esize p) := by
  set R : Polynomial ℕ := 2 * X + lstarIdx.timeBound + 3
  refine ⟨R + lstarCore.timeBound.comp R + 1, fun p A => ?_⟩
  have hQ : ((X + 1) + (lstarIdx.timeBound + (C (esize p)).comp lstarIdx.timeBound + 1) + 1 :
      Polynomial ℕ).eval A ≤ R.eval (A + esize p) := by
    have := polynomial_eval_mono lstarIdx.timeBound (show A ≤ A + esize p by omega)
    simp only [R, eval_add, eval_X, eval_one, eval_comp, eval_C, eval_mul, eval_ofNat]
    omega
  rw [lstarFinal_const_timeBound_eq]
  have := polynomial_eval_mono lstarCore.timeBound hQ
  simp only [eval_add, eval_comp, eval_one, eval_X, eval_C] at this hQ ⊢
  omega

/-! ## Acceptance within a power of two -/

theorem _root_.MIPRE.Decider.AcceptsWithin.mono {D : Decider} {n : ℕ} {x y a b : BitStr}
    {T T' : ℕ} (h : D.AcceptsWithin n x y a b T) (hT : T ≤ T') : D.AcceptsWithin n x y a b T' :=
  let ⟨t, ht, hrun⟩ := h
  ⟨t, ht.trans hT, hrun⟩

/-- `lstarBound` at constant parameters is at most a fixed polynomial of `T Z^k + S + |p|`. -/
theorem lstarBound_const_le : ∃ H : Polynomial ℕ, ∀ (p : Unary × Unary) (T k S Z : ℕ),
    lstarBound (PolyTimeFun.const p) T k S Z ≤ H.eval (T * Z ^ k + S + esize p) := by
  obtain ⟨G, hG⟩ := lstarFinal_const_timeBound
  set W : Polynomial ℕ := 5 * X + 5
  refine ⟨2 * (canonIn₁.timeBound.comp W + canonIn₂.timeBound.comp W +
      canonIn₃.timeBound.comp W + canonIn₄.timeBound.comp W + canonIn₅.timeBound.comp W) +
      G.comp W + 35 * X + 70, fun p T k S Z => ?_⟩
  unfold lstarBound
  dsimp only
  generalize T * Z ^ k = Y
  set M := Y + S + esize p
  have hW : W.eval M = 5 * M + 5 := by simp [W]
  have m1 := polynomial_eval_mono canonIn₁.timeBound (show S ≤ 5 * M + 5 by omega)
  have m2 := polynomial_eval_mono canonIn₂.timeBound (show Y + S + 1 ≤ 5 * M + 5 by omega)
  have m3 := polynomial_eval_mono canonIn₃.timeBound
    (show Y + (Y + S + 1) + 1 ≤ 5 * M + 5 by omega)
  have m4 := polynomial_eval_mono canonIn₄.timeBound
    (show Y + (Y + (Y + S + 1) + 1) + 1 ≤ 5 * M + 5 by omega)
  have m5 := polynomial_eval_mono canonIn₅.timeBound
    (show Y + (Y + (Y + (Y + S + 1) + 1) + 1) + 1 ≤ 5 * M + 5 by omega)
  have mf := (hG p (Y + (Y + (Y + (Y + (Y + S + 1) + 1) + 1) + 1) + 1)).trans
    (polynomial_eval_mono G
      (show Y + (Y + (Y + (Y + (Y + S + 1) + 1) + 1) + 1) + 1 + esize p ≤ 5 * M + 5 by omega))
  simp only [eval_add, eval_mul, eval_comp, hW, eval_X, eval_ofNat]
  omega

/-- **The output indicator at constant parameters accepts within `2^(E (k+1) (τ+ρ+1))`**
whatever it accepts, when its two programs run within `T (|d| + 1)^k` with `T ≤ 2^τ`, and the
input and the parameters have size below `2^ρ`; `E` is one universal constant. -/
theorem lstar_const_acceptsWithin_pow : ∃ E : ℕ, 1 ≤ E ∧ ∀ (p : Unary × Unary) {ℓ : ℕ}
    (V : TailoredVerifier ℓ) {n T k τ ρ : ℕ} {x y a b : BitStr},
    V.len.TimeBoundAt n T k → V.lp.TimeBoundAt n T k → T ≤ 2 ^ τ →
    esize ((n, x, y, a, b) : DIn) + 1 ≤ 2 ^ ρ → esize p ≤ 2 ^ ρ →
    (lstar (PolyTimeFun.const p) V).Accepts n x y a b →
    (lstar (PolyTimeFun.const p) V).AcceptsWithin n x y a b (2 ^ (E * (k + 1) * (τ + ρ + 1))) := by
  obtain ⟨H, hH⟩ := lstarBound_const_le
  obtain ⟨D, hD⟩ := polynomial_eval_le_add_two_pow H
  refine ⟨2 * D + 1, by omega, fun p ℓ V n T k τ ρ x y a b hLt hPt hT hS hp h => ?_⟩
  refine (lstar_acceptsWithin _ V hLt hPt h).mono ?_
  set S := esize ((n, x, y, a, b) : DIn)
  set u := τ + (ρ + 1) * k + ρ + 2
  have hZ : 2 * S + 2 ≤ 2 ^ (ρ + 1) := by rw [pow_succ]; omega
  have hY : T * (2 * S + 2) ^ k ≤ 2 ^ (τ + (ρ + 1) * k) := by
    rw [pow_add, pow_mul]
    exact Nat.mul_le_mul hT (Nat.pow_le_pow_left hZ k)
  have hM : T * (2 * S + 2) ^ k + S + esize p + 2 ≤ 2 ^ u := by
    have e1 : 2 ^ (τ + (ρ + 1) * k) ≤ 2 ^ (τ + (ρ + 1) * k + ρ) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : 2 ^ ρ ≤ 2 ^ (τ + (ρ + 1) * k + ρ) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e3 : 1 ≤ 2 ^ (τ + (ρ + 1) * k + ρ) := Nat.one_le_two_pow
    have e4 : 2 ^ u = 4 * 2 ^ (τ + (ρ + 1) * k + ρ) := by
      rw [show u = τ + (ρ + 1) * k + ρ + 2 from rfl, pow_add]; ring
    omega
  have hu : u ≤ 2 * ((k + 1) * (τ + ρ + 1)) := by
    have : (k + 1) * (τ + ρ + 1) = k * τ + k * ρ + k + τ + ρ + 1 := by ring
    have : (ρ + 1) * k = k * ρ + k := by ring
    have : 0 ≤ k * τ := Nat.zero_le _
    omega
  calc lstarBound (PolyTimeFun.const p) T k S (2 * S + 2)
      ≤ H.eval (T * (2 * S + 2) ^ k + S + esize p) := hH p T k S (2 * S + 2)
    _ ≤ (T * (2 * S + 2) ^ k + S + esize p + 2) ^ D := hD _
    _ ≤ (2 ^ u) ^ D := Nat.pow_le_pow_left hM D
    _ = 2 ^ (u * D) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ ((2 * D + 1) * (k + 1) * (τ + ρ + 1)) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      calc u * D ≤ 2 * ((k + 1) * (τ + ρ + 1)) * D := Nat.mul_le_mul_right D hu
        _ = 2 * D * ((k + 1) * (τ + ρ + 1)) := by ring
        _ ≤ (2 * D + 1) * ((k + 1) * (τ + ρ + 1)) := Nat.mul_le_mul_right _ (by omega)
        _ = (2 * D + 1) * (k + 1) * (τ + ρ + 1) := by ring

/-! ## The program, as a polynomial-time function of its data -/

open MIPRE.CL.ProgBuild MIPRE.CL.Detyping.Program

/-- `(h, t) ↦ cons h t`, in polynomial time. -/
noncomputable def consProgF : PolyTimeFun (Prog × Prog) Prog :=
  PolyTimeFun.cast (ap₂ treePair (const (Data.ofNat 2)) (encoded : PolyTimeFun (Prog × Prog) Data))
    (fun q => Prog.cons q.1 q.2) (fun _ => rfl)

@[simp] theorem consProgF_apply (h t : Prog) : consProgF (h, t) = Prog.cons h t := rfl

/-- `p ↦ const (encode p)`, the program outputting `p`, in polynomial time. -/
noncomputable def constProgF {α : Type*} [SizedEncoding α] : PolyTimeFun α Prog :=
  PolyTimeFun.cast (ap₂ treePair (const (Data.ofNat 6)) (encoded : PolyTimeFun α Data))
    (fun a => Prog.const (encode a)) (fun _ => rfl)

@[simp] theorem constProgF_apply {α : Type*} [SizedEncoding α] (a : α) :
    (constProgF : PolyTimeFun α Prog) a = Prog.const (encode a) := rfl

/-- `P ↦ pushProg F P`, in polynomial time. -/
noncomputable def pushProgF (F : Prog) : PolyTimeFun Prog Prog :=
  letF.comp ((const F).pair (letF.comp ((letF.comp ((const (.var 0)).pair (PolyTimeFun.id Prog))).pair
    (const (.cons (.var 0) (.var 2))))))

@[simp] theorem pushProgF_apply (F P : Prog) : pushProgF F P = Prog.pushProg F P := rfl

/-- The program of the check at constant parameters: the parameter-free check on the input and
the constant `p`. -/
theorem lstarFinal_const_code (p : Unary × Unary) :
    (lstarFinal (PolyTimeFun.const p)).code =
      .let_ (.cons (.var 0) (.let_ lstarIdx.code (.const (encode p)))) lstarCore.code := rfl

/-- `p ↦ (lstarFinal (const p)).code`, in polynomial time. -/
noncomputable def lstarFinalCodeF : PolyTimeFun (Unary × Unary) Prog :=
  letF.comp ((consProgF.comp ((const (.var 0)).pair
    (letF.comp ((const lstarIdx.code).pair constProgF)))).pair (const lstarCore.code))

@[simp] theorem lstarFinalCodeF_apply (p : Unary × Unary) :
    lstarFinalCodeF p = (lstarFinal (PolyTimeFun.const p)).code := rfl

/-- **The output indicator at constant parameters, as a polynomial-time function** of the
answer-length calculator, the processor and the parameters. -/
noncomputable def lstarProgF : PolyTimeFun ((Prog × Prog) × (Unary × Unary)) Prog :=
  let L : PolyTimeFun ((Prog × Prog) × (Unary × Unary)) Prog := fst.comp fst
  let P : PolyTimeFun ((Prog × Prog) × (Unary × Unary)) Prog := snd.comp fst
  let step : Prog → PolyTimeFun ((Prog × Prog) × (Unary × Unary)) Prog →
      PolyTimeFun ((Prog × Prog) × (Unary × Unary)) Prog →
      PolyTimeFun ((Prog × Prog) × (Unary × Unary)) Prog := fun F Q rest =>
    letF.comp (((pushProgF F).comp Q).pair rest)
  step canonIn₁.code L (step canonIn₂.code L (step canonIn₃.code L (step canonIn₄.code L
    (step canonIn₅.code P (lstarFinalCodeF.comp snd)))))

theorem lstarProgF_apply (L P : Prog) (p : Unary × Unary) :
    lstarProgF ((L, P), p) = lstarProg (PolyTimeFun.const p) L P := rfl

/-! ## The size of the program -/

/-- The constant part of the size of the output indicator at constant parameters
(`esize_lstarProg_const`): the five input builders of the canonical decider, the index
projection and the parameter-free check, and `366` for the wiring. -/
noncomputable def lstarProgSize₀ : ℕ :=
  esize canonIn₁.code + esize canonIn₂.code + esize canonIn₃.code + esize canonIn₄.code +
    esize canonIn₅.code + esize lstarIdx.code + esize lstarCore.code + 366

/-- **The size of the output indicator at constant parameters**: `L` occurs four times, `P`
once and `p` once. -/
theorem esize_lstarProg_const (p : Unary × Unary) (L P : Prog) :
    esize (lstarProg (PolyTimeFun.const p) L P) =
      lstarProgSize₀ + 4 * esize L + esize P + esize p := by
  -- `rw` and `omega` would try to decide equalities by unfolding the fixed programs, so the
  -- fixed sizes are abstracted first.
  have key : esize (lstarProg (PolyTimeFun.const p) L P) =
      (canonIn₁.code.toData.size + canonIn₂.code.toData.size + canonIn₃.code.toData.size +
        canonIn₄.code.toData.size + canonIn₅.code.toData.size + lstarIdx.code.toData.size +
        lstarCore.code.toData.size + 366) + 4 * L.toData.size + P.toData.size + esize p := by
    simp only [lstarProg, lstarTail₁, lstarTail₂, lstarTail₃, lstarTail₄, lstarFinal_const_code,
      seqProg, Prog.pushProg, Prog.esize_eq_size_toData, Prog.toData, Data.size_cons,
      Data.size_ofNat, show (encode p).size = esize p from rfl]
    generalize canonIn₁.code.toData.size = c₁
    generalize canonIn₂.code.toData.size = c₂
    generalize canonIn₃.code.toData.size = c₃
    generalize canonIn₄.code.toData.size = c₄
    generalize canonIn₅.code.toData.size = c₅
    generalize lstarIdx.code.toData.size = c₆
    generalize lstarCore.code.toData.size = c₇
    generalize esize p = e
    generalize L.toData.size = l
    generalize P.toData.size = q
    omega
  refine key.trans ?_
  delta lstarProgSize₀
  simp only [Prog.esize_eq_size_toData]

theorem esize_lstarProg_const_le : ∃ c₀ : ℕ, ∀ (p : Unary × Unary) (L P : Prog),
    esize (lstarProg (PolyTimeFun.const p) L P) ≤ c₀ + 4 * esize L + esize P + esize p :=
  ⟨lstarProgSize₀, fun p L P => (esize_lstarProg_const p L P).le⟩

/-- The size of the output indicator at constant parameters, in the vocabulary of deciders. -/
theorem size_lstar_const (p : Unary × Unary) {ℓ : ℕ} (V : TailoredVerifier ℓ) :
    (lstar (PolyTimeFun.const p) V).size =
      lstarProgSize₀ + 4 * V.len.size + V.lp.size + esize p :=
  esize_lstarProg_const p _ _

theorem size_lstar_const_le (p : Unary × Unary) {ℓ : ℕ} (V : TailoredVerifier ℓ) :
    (lstar (PolyTimeFun.const p) V).size ≤ lstarProgSize₀ + 5 * V.size + esize p := by
  rw [size_lstar_const]
  have h1 : V.len.size ≤ V.size := le_max_of_le_right (le_max_left _ _)
  have h2 : V.lp.size ≤ V.size := le_max_of_le_right (le_max_right _ _)
  omega

end MIPRE.Tailored.AnsRed

end
