/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.SoundDecoded
public import MIPRE.Background.LIDT.FinModel

@[expose] public section

/-!
# Soundness of the answer-reduced game

Slice P4e of `planning/aldous-lyons-track.md`: the soundness clause of
prop:completeness_soundness_combi_ans_red (II:10487), at one index of the input. If the
answer-reduced game presented by the typed data `tdata`, on any answer-reduced sampler, has
`val* > 1 - ε`, then `val*(𝒱_n) ≥ 1 - 24 √(errAR (16⁹ ε))` (`valStar_ar_sound`).

The chain:

1. the presented game's `val*` is at most the detyped game's (`valStar_presented_le`), whose
   typed game has `val*` above `1 - 16⁹ ε` (`CL.Detyping.quantumValue_typedGame_ge`);
2. a projective strategy `T` of a tensor-product model near that value, in which the seeded
   low-degree test is sound (`LIDT.Simul.approxSoundIn_tensor`);
3. the decoded strategy of `SoundDecoded`, which fails the typed oracularized game of the input at
   most `errAR` of `T`'s failure (`one_sub_value_decoded_le`): the nine pairs of roles at a seed
   (`sum_roles_condFail_le`), summed over the seeds;
4. oracularization's soundness (`ValueModel.OracularSound`), the typed oracularized game being
   at most the oracularization (`SeededGame.val_typedGame_le`), and the oracularized input's game
   being the input's (`inCL_toGame`).

`errAR` is explicit in the errors of the seeded test's soundness (`dS`) and the field size; P4i
bounds it by the contract's `AnswerReduction.delta`.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset Cost MIPRE.CL MIPRE.SAT MIPRE.LIDT

/-! ## The error -/

section Error

variable (t : ℕ) (ht : 1 ≤ t) (j d : ℕ) (L : PcpDims)

/-- **The error of the answer-reduced game's soundness**, at typed failure `θ`: the outcomes of the
oracle that are not block-local or pass the proof check sparsely, the two polynomial
measurements' disagreements at each role, and the agreement of the isolated roles' polynomials
with the oracle's. -/
def errAR (θ : ℝ) : ℝ :=
  6 * (2 * 2 ^ j * (12 * dS t ht j d L .oracle (9 * θ) + 1782 * θ)
      + (2 * dS t ht j d L .oracle (9 * θ) + 162 * θ))
    + 4 * dS t ht j d L .oracle (9 * θ) + dS t ht j d L .alice (9 * θ)
    + dS t ht j d L .bob (9 * θ) + 2 * errP t ht j d L .alice θ + 2 * errP t ht j d L .bob θ

variable {t ht j d L}

theorem deltaSim_mono {q m d r : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Simul.deltaSim q m d r x ≤ Simul.deltaSim q m d r y := by
  unfold Simul.deltaSim
  have hA : 0 ≤ Simul.simA * ((d * m * r : ℕ) : ℝ) ^ Simul.simA := by
    have := Simul.forty_le_simA
    positivity
  have h := Real.rpow_le_rpow hx hxy clB_pos.le
  exact mul_le_mul_of_nonneg_left (by linarith) hA

theorem dS_mono (r : Role) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    dS t ht j d L r x ≤ dS t ht j d L r y :=
  deltaSim_mono hx hxy

theorem errP_mono (r : Role) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    errP t ht j d L r x ≤ errP t ht j d L r y := by
  unfold errP
  have h1 := dS_mono (t := t) (ht := ht) (j := j) (d := d) (L := L) r
    (by linarith : 0 ≤ 9 * x) (by linarith : 9 * x ≤ 9 * y)
  have h2 := dS_mono (t := t) (ht := ht) (j := j) (d := d) (L := L) .oracle
    (by linarith : 0 ≤ 9 * x) (by linarith : 9 * x ≤ 9 * y)
  nlinarith

/-- **The error grows strictly with the typed failure.** -/
theorem errAR_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    errAR t ht j d L x < errAR t ht j d L y := by
  unfold errAR
  have h9 : 9 * x ≤ 9 * y := by linarith
  have h90 : 0 ≤ 9 * x := by linarith
  have hO := dS_mono (t := t) (ht := ht) (j := j) (d := d) (L := L) .oracle h90 h9
  have hA := dS_mono (t := t) (ht := ht) (j := j) (d := d) (L := L) .alice h90 h9
  have hB := dS_mono (t := t) (ht := ht) (j := j) (d := d) (L := L) .bob h90 h9
  have hPA := errP_mono (t := t) (ht := ht) (j := j) (d := d) (L := L) .alice hx hxy.le
  have hPB := errP_mono (t := t) (ht := ht) (j := j) (d := d) (L := L) .bob hx hxy.le
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

theorem errAR_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ errAR t ht j d L x := by
  unfold errAR errP
  have h90 : 0 ≤ 9 * x := by linarith
  have hO := dS_nonneg ht j d L .oracle h90
  have hA := dS_nonneg ht j d L .alice h90
  have hB := dS_nonneg ht j d L .bob h90
  positivity

/-- **The error is at least the typed failure.** -/
theorem le_errAR {x : ℝ} (hx : 0 ≤ x) : x ≤ errAR t ht j d L x := by
  unfold errAR errP
  have h90 : 0 ≤ 9 * x := by linarith
  have hO := dS_nonneg ht j d L .oracle h90
  have hA := dS_nonneg ht j d L .alice h90
  have hB := dS_nonneg ht j d L .bob h90
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hq : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht) := by positivity
  nlinarith

theorem errAR_pos (hd : 1 ≤ d) {x : ℝ} (hx : 0 ≤ x) : 0 < errAR t ht j d L x := by
  unfold errAR errP
  have h90 : 0 ≤ 9 * x := by linarith
  have hO := dS_nonneg ht j d L .oracle h90
  have hA := dS_nonneg ht j d L .alice h90
  have hB := dS_nonneg ht j d L .bob h90
  have hq : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

end Error

/-! ## The oracularized input -/

section Input

variable {ℓV : ℕ} (V : TailoredVerifier ℓV) (n : ℕ)

theorem roleFamily_liftedCl_eval (r : Role) (z : V.Questions n) :
    (roleFamily (liftedCl V n) r).eval z = oq V n r z := by
  cases r
  · exact CLFun.eval_ident _ _
  · exact CLFun.eval_liftTo _ _ (Nat.le_succ ℓV) _ _
  · exact CLFun.eval_liftTo _ _ (Nat.le_succ ℓV) _ _

/-- **The oracularized input's game is the input's.** -/
theorem inCL_toGame : (inCL V n).toGame = (V.tgame n).toGame := by
  have hA : (liftedCl V n .alice).eval = (V.sampler.cl n .alice).eval :=
    funext fun z => CLFun.eval_liftTo _ _ (Nat.le_succ ℓV) _ _
  have hB : (liftedCl V n .bob).eval = (V.sampler.cl n .bob).eval :=
    funext fun z => CLFun.eval_liftTo _ _ (Nat.le_succ ℓV) _ _
  have e : inCL V n = inSeeded V n := by
    simp only [inCL, SeededGame.ofCL, hA, hB]
    rfl
  rw [e]
  rfl

end Input

/-! ## The decoded strategy's failure -/

section Failure

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}
  (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B)) (hL : LIDT.Simul.SoundIn M)
  (hd : 1 ≤ d)

/-- **The decoded strategy's failure at a seed**, over the nine ordered pairs of roles. -/
theorem sum_roles_condFail_le (z : V.Questions n) :
    ∑ u : Role, ∑ v : Role, M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd)
        (u, oq V n u z) (v, oq V n v z)
      ≤ 3 * gcA T hL hd z + 3 * gcB T hL hd z
        + M.dis (GA T hL hd .oracle z) (GB T hL hd .oracle z)
        + M.dis (GA T hL hd .alice (oq V n .alice z)) (GB T hL hd .alice (oq V n .alice z))
        + M.dis (GA T hL hd .bob (oq V n .bob z)) (GB T hL hd .bob (oq V n .bob z))
        + (M.dis ((GA T hL hd .oracle z).map (restr L .alice))
            (GB T hL hd .alice (oq V n .alice z))
          + M.dis ((GA T hL hd .oracle z).map (restr L .bob)) (GB T hL hd .bob (oq V n .bob z))
          + M.dis (GA T hL hd .alice (oq V n .alice z))
            ((GB T hL hd .oracle z).map (restr L .alice))
          + M.dis (GA T hL hd .bob (oq V n .bob z))
            ((GB T hL hd .oracle z).map (restr L .bob))) := by
  simp only [Role.sum_eq]
  rw [show oq V n .oracle z = z from rfl]
  have h1 := condFail_OO_le T hL hd z
  have h2 := condFail_Or_le T hL hd (r := .alice) (by decide) z
  have h3 := condFail_Or_le T hL hd (r := .bob) (by decide) z
  have h4 := condFail_rO_le T hL hd (r := .alice) (by decide) z
  have h5 := condFail_rO_le T hL hd (r := .bob) (by decide) z
  have h6 := condFail_rr_le T hL hd (r := .alice) (by decide) (oq V n .alice z)
  have h7 := condFail_rr_le T hL hd (r := .bob) (by decide) (oq V n .bob z)
  have h8 := condFail_rr'_le T hL hd (r := .alice) (r' := .bob) (by decide) (by decide)
    (by decide) (oq V n .alice z) (oq V n .bob z)
  have h9 := condFail_rr'_le T hL hd (r := .bob) (r' := .alice) (by decide) (by decide)
    (by decide) (oq V n .bob z) (oq V n .alice z)
  have hg0 : 0 ≤ gcA T hL hd z := Finset.sum_nonneg fun f _ => by
    split_ifs
    · exact le_refl 0
    · exact M.bornProb_nonneg ((GA T hL hd .oracle z).op_nonneg f) zero_le_one
  have hg1 : 0 ≤ gcB T hL hd z := Finset.sum_nonneg fun f _ => by
    split_ifs
    · exact le_refl 0
    · exact M.bornProb_nonneg zero_le_one ((GB T hL hd .oracle z).op_nonneg f)
  linarith

open Classical in
/-- **The decoded strategy fails the typed oracularized game at most `errAR` of the typed
failure**, once the field has `2 (M + 1) d` and `2 m (5 + 6(d + 1))` elements. -/
theorem one_sub_value_decoded_le {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp L V n prm Cc Tt) (hP : ArSampler hM sel V n P)
    (hq : 2 * ((2 ^ j + 1) * d) ≤ Fintype.card (Fq t ht))
    (hτ : 2 * (L.m * chkDeg 5 d) ≤ Fintype.card (Fq t ht)) :
    1 - (decoded T hL hd).value ≤ errAR t ht j d L (1 - T.value) := by
  set θ := 1 - T.value with hθ
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr (BipartiteModel.ProjStrat.value_le_one _)
  set Zc : ℝ := (Fintype.card (V.Questions n) : ℝ) with hZc
  have hZ0 : 0 < Zc := by positivity
  -- the failure, by seeds and roles
  have hT := MIPRE.AnswerReduction.one_sub_povmValue_typed M (liftedCl V n) (inCL V n).oaccepts
    (MAd T hL hd) (MBd T hL hd)
  have hroles : ∀ z u v, M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd)
      (u, (roleFamily (liftedCl V n) u).eval z) (v, (roleFamily (liftedCl V n) v).eval z) =
      M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd) (u, oq V n u z) (v, oq V n v z) :=
    fun z u v => by rw [roleFamily_liftedCl_eval, roleFamily_liftedCl_eval]
  -- the summed bounds, in the form `sum_roles_condFail_le` produces
  have hBG : ∑ z, ∑ f, (if Good j L hLM f then 0
      else M.bornProb ((GA T hL hd .oracle z).op f) 1)
      ≤ Zc * (2 * 2 ^ j * (12 * dS t ht j d L .oracle (9 * θ) + 1782 * θ)) :=
    sum_badGood_le T hL hd hP hq
  have hBD : ∑ z, ∑ f, (if Dense L hLM (circOf L V n Cc hm z) f then 0
      else M.bornProb ((GA T hL hd .oracle z).op f) 1)
      ≤ Zc * (2 * dS t ht j d L .oracle (9 * θ) + 162 * θ) :=
    sum_badDense_le T hL hd hP hτ
  have hOO : ∑ z, M.dis (GA T hL hd .oracle z) (GB T hL hd .oracle z)
      ≤ Zc * dS t ht j d L .oracle (9 * θ) :=
    sum_dis_GA_GB_le T hL hd hP .oracle
  have hAA := sum_dis_GA_GB_le T hL hd hP .alice
  have hBB := sum_dis_GA_GB_le T hL hd hP .bob
  have hPA' : ∑ z, M.dis ((GA T hL hd .oracle z).map (restr L .alice))
      (GB T hL hd .alice (oq V n .alice z)) ≤ Zc * errP t ht j d L .alice θ :=
    sum_dis_GAO_GBr_poly_le T hL hd hP (r := .alice) (by decide)
  have hPB' : ∑ z, M.dis ((GA T hL hd .oracle z).map (restr L .bob))
      (GB T hL hd .bob (oq V n .bob z)) ≤ Zc * errP t ht j d L .bob θ :=
    sum_dis_GAO_GBr_poly_le T hL hd hP (r := .bob) (by decide)
  have hPA : ∑ z, M.dis (GA T hL hd .alice (oq V n .alice z))
      ((GB T hL hd .oracle z).map (restr L .alice)) ≤ Zc * errP t ht j d L .alice θ :=
    sum_dis_GAr_GBO_poly_le T hL hd hP (r := .alice) (by decide)
  have hPB : ∑ z, M.dis (GA T hL hd .bob (oq V n .bob z))
      ((GB T hL hd .oracle z).map (restr L .bob)) ≤ Zc * errP t ht j d L .bob θ :=
    sum_dis_GAr_GBO_poly_le T hL hd hP (r := .bob) (by decide)
  have hgA : ∑ z, gcA T hL hd z ≤ ∑ z, ∑ f, (if Good j L hLM f then 0
        else M.bornProb ((GA T hL hd .oracle z).op f) 1)
      + ∑ z, ∑ f, (if Dense L hLM (circOf L V n Cc hm z) f then 0
        else M.bornProb ((GA T hL hd .oracle z).op f) 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => gcA_le T hL hd H z
  have hgB : ∑ z, gcB T hL hd z ≤ ∑ z, M.dis (GA T hL hd .oracle z) (GB T hL hd .oracle z)
      + (∑ z, ∑ f, (if Good j L hLM f then 0
        else M.bornProb ((GA T hL hd .oracle z).op f) 1)
      + ∑ z, ∑ f, (if Dense L hLM (circOf L V n Cc hm z) f then 0
        else M.bornProb ((GA T hL hd .oracle z).op f) 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun z _ => gcB_le T hL hd H z
  have hsum := Finset.sum_le_sum fun z (_ : z ∈ univ) => sum_roles_condFail_le T hL hd z
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- the failure
  change 1 - M.povmValue (oGameT V n) (MAd T hL hd) (MBd T hL hd) ≤ _
  rw [hT]
  simp only [hroles]
  have hcard : ((Fintype.card (Fin (V.sampler.dim n) → CL.𝔽₂) : ℕ) : ℝ) = Zc := rfl
  rw [hcard]
  have hO0 := dS_nonneg ht j d L .oracle (by linarith : 0 ≤ 9 * θ)
  have hE0 := errAR_nonneg (t := t) (ht := ht) (j := j) (d := d) (L := L) hθ0
  have htot : ∑ z, ∑ u : Role, ∑ v : Role, M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd)
      (u, oq V n u z) (v, oq V n v z) ≤ Zc * errAR t ht j d L θ := by
    refine hsum.trans ?_
    unfold errAR
    nlinarith
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

end Failure

/-! ## The soundness of the answer-reduced game -/

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}

/-- An answer as one of the bounded answers, when its length allows. -/
def decB (B : ℕ) (a : Cost.BitStr) : Verifier.Answers B :=
  if h : a.length ≤ B then ⟨a, h⟩ else ⟨[], Nat.zero_le B⟩

open Classical in
/-- **The presented game's value is at most the detyped game's.** -/
theorem valStar_presented_ar_le (hB : ∀ u, len t j d L u ≤ B) :
    (presented arGraph (CL.Detyping.game arGraph P (arDt d hM sel L hLM V n Cc hm B))
        (tdata t ht j d L (V.sampler.dim n) sel hLM (circOf L V n Cc hm))).valStar
      ≤ quantumValue (CL.Detyping.game arGraph P (arDt d hM sel L hLM V n Cc hm B)) :=
  valStar_presented_le arGraph _ (arDt d hM sel L hLM V n Cc hm B) (fun _ _ _ _ => rfl) _
    (fun _ => decB B) ⟨[], Nat.zero_le B⟩ fun u v a b _ hab => by
      have h := (accepts_iff t ht j d L _ sel hLM _ u v a b).1 hab
      have ha : a.length ≤ B := h.1 ▸ hB u.1
      have hb : b.length ≤ B := h.2.1 ▸ hB v.1
      have e1 : (decB B a).1 = a := by simp [decB, ha]
      have e2 : (decB B b).1 = b := by simp [decB, hb]
      unfold arDt
      rw [e1, e2]
      exact decide_eq_true hab

/-- **The soundness of the answer-reduced game** (prop:completeness_soundness_combi_ans_red,
item 2): if the game presented by the typed data on an answer-reduced sampler has
`val* > 1 - ε`, then `val*(𝒱_n) ≥ 1 - 24 √(errAR (16⁹ ε))`, once the field has `2 (M + 1) d` and
`2 m (5 + 6(d + 1))` elements. -/
theorem valStar_ar_sound {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp L V n prm Cc Tt) (hd : 1 ≤ d) (hP : ArSampler hM sel V n P) (hℓ : 0 < ℓ)
    (hB : ∀ u, len t j d L u ≤ B) (hq : 2 * ((2 ^ j + 1) * d) ≤ Fintype.card (Fq t ht))
    (hτ : 2 * (L.m * chkDeg 5 d) ≤ Fintype.card (Fq t ht)) {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < (presented arGraph (CL.Detyping.game arGraph P (arDt d hM sel L hLM V n Cc hm B))
      (tdata t ht j d L (V.sampler.dim n) sel hLM (circOf L V n Cc hm))).valStar) :
    1 - 24 * √(errAR t ht j d L (16 ^ 9 * ε)) ≤ V.valStar n := by
  have hv0 : 0 ≤ V.valStar n := quantumValue_nonneg _
  have hε9 : 0 ≤ 16 ^ 9 * ε := by positivity
  -- the trivial case
  by_cases hbig : 1 ≤ 16 ^ 9 * ε
  · have h1 : 1 ≤ errAR t ht j d L (16 ^ 9 * ε) := hbig.trans (le_errAR hε9)
    have h2 : 1 ≤ √(errAR t ht j d L (16 ^ 9 * ε)) := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt h1
    linarith
  push Not at hbig
  -- the detyped game, then the typed game
  have h1 : 1 - ε < quantumValue (CL.Detyping.game arGraph P (arDt d hM sel L hLM V n Cc hm B)) :=
    lt_of_lt_of_le h (valStar_presented_ar_le hB)
  have h2 := CL.Detyping.quantumValue_typedGame_ge arGraph arGraph_symm arGraph_nonempty P
    hP.exactlyOn hℓ (arDt d hM sel L hLM V n Cc hm B)
  rw [show Fintype.card (Role × LIDT.CL.Ty) = 9 from rfl] at h2
  have h3 : 1 - 16 ^ 9 * ε < quantumValue (arGame d hM sel L hLM V n Cc hm P B) := by
    have : (16 : ℝ) ^ 9 * (1 - quantumValue
        (CL.Detyping.game arGraph P (arDt d hM sel L hLM V n Cc hm B))) < 16 ^ 9 * ε :=
      mul_lt_mul_of_pos_left (by linarith) (by positivity)
    exact lt_of_lt_of_le (by linarith) h2
  -- a strategy of a tensor-product model in which the seeded test is sound
  obtain ⟨𝒞, 𝒜, ℬ, _, _, _, _, _, _, _, _, _, _, _, _, _, M, hSound, hdom, T, hT⟩ :=
    LIDT.Simul.approxSoundIn_tensor (arGame d hM sel L hLM V n Cc hm P B)
      (by linarith : (0 : ℝ) ≤ 1 - 16 ^ 9 * ε) (by rwa [ValueModel.tensor_val])
  have hθ0 : 0 ≤ 1 - T.value := sub_nonneg.mpr (BipartiteModel.ProjStrat.value_le_one _)
  have hθ : 1 - T.value < 16 ^ 9 * ε := by linarith
  -- the decoded strategy, then oracularization
  have hdec := one_sub_value_decoded_le T hSound hd H hP hq hτ
  have hdv := hdom (oGameT V n) (decoded T hSound hd)
  have hor := SeededGame.val_typedGame_le ValueModel.tensor_oracularSound (liftedCl V n)
    (V.tgame n).toGame.D (inCL V n).oaccepts (fun _ a => a) (fun _ _ _ _ hab => hab)
  have hlt := errAR_lt (t := t) (ht := ht) (j := j) (d := d) (L := L) hθ0 hθ
  have hor2 : 1 - errAR t ht j d L (16 ^ 9 * ε) <
      ValueModel.tensor.val (inCL V n).oracular.toGame := by
    have : (decoded T hSound hd).value ≤ ValueModel.tensor.val (inCL V n).oracular.toGame :=
      hdv.trans hor
    linarith
  have hfin := ValueModel.tensor_oracularSound.oracular (inCL V n)
    (errAR_pos hd hε9) hor2
  rw [ValueModel.tensor_val, inCL_toGame] at hfin
  exact hfin

end MIPRE.Tailored.AnsRed.Typed

end
