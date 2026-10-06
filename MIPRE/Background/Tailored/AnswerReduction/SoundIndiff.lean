/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.SoundPoly
public import MIPRE.Background.Tailored.AnswerReduction.ShiftPoly

@[expose] public section

/-!
# Soundness of the answer-reduced game: indifference

The paper's second perturbation (II:10644): the oracle's polynomials are, with high probability,
*block-local* — each codeword's polynomial involves only the variables of its slot's block
(`Good`), which is what reading them as a PCP (`Pcp.ofPolys`) needs.

The paper derives it from the indifference check (II:10465, check 3) through the low-degree test's
conclusions at *lines*. The seeded test's soundness in the model gives conclusions at points only
(`LIDT.Simul.SoundIn`), and the argument here uses points only, with two points of one
axis-parallel line:

* the question of type `ALine` the registers of a vector `w` carry is the same at every point of
  its line: moving the vector's point along its own direction (`shiftW`) keeps it
  (`ldq_aline_shiftW`);
* at the type pair `(O, ALine), (O, Point)`, the low-degree check and the indifference check make
  the point values, in the codewords whose blocks miss the line's direction, the constant
  coefficients of the line answer's polynomials (`kv_eq_pv_of_arDt`);
* so, through the line answer, Bob's point values at two points `u, u + s eᵢ` of one line agree
  with Alice's polynomials evaluated at `u` (a disagreement triangle), and Alice's polynomials
  evaluated at `u` and at `u + s eᵢ` agree in those codewords (`sum_ite_ne_le_dis_add`);
* a polynomial with a monomial in a variable outside its block changes value along most steps in
  that direction (`MIPRE.LIDT.card_shift_ne_ge`), on a `1/M` fraction of the lines: so the
  weight of the outcomes that are not block-local is at most `2M` times the errors
  (`sum_badGood_le`).

`sum_ite_read_le` and its mirror move an event between the two players' measurements, at the cost
of their disagreement.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset MIPRE.CL MIPRE.SAT MIPRE.LIDT

/-! ## Moving events between the players -/

section Generic

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
  {Λ Λ' R : Type*} [Fintype Λ] [Fintype Λ'] [Fintype R] [DecidableEq R]

/-- **Two readings of the first player's outcome against one of the second's**: the weight of the
outcomes the two readings tell apart is at most the sum of the two disagreements. -/
theorem sum_ite_ne_le_dis_add (hψ : ‖M.ψ‖ = 1) (P : POVMIn Λ 𝒜) (Q : POVMIn Λ' ℬ)
    (f₁ f₂ : Λ → R) (g : Λ' → R) :
    ∑ a, (if f₁ a = f₂ a then 0 else M.bornProb (P.op a) 1)
      ≤ M.dis (P.map f₁) (Q.map g) + M.dis (P.map f₂) (Q.map g) := by
  rw [M.dis_map_eq_sum hψ, M.dis_map_eq_sum hψ, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  have hβ : ∀ b, 0 ≤ M.bornProb (P.op a) (Q.op b) := fun b =>
    M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b)
  by_cases h : f₁ a = f₂ a
  · rw [ite_eq_left h]
    exact Finset.sum_nonneg fun b _ =>
      add_nonneg (mul_nonneg (by split_ifs <;> norm_num) (hβ b))
        (mul_nonneg (by split_ifs <;> norm_num) (hβ b))
  · rw [ite_eq_right h, M.bornProb_one_right _ Q]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases h₁ : f₁ a = g b
    · have h₂ : ¬f₂ a = g b := fun h₂ => h (h₁.trans h₂.symm)
      rw [ite_eq_left h₁, ite_eq_right h₂]
      linarith [hβ b]
    · rw [ite_eq_right h₁]
      have := mul_nonneg (show (0 : ℝ) ≤ if f₂ a = g b then 0 else 1 by split_ifs <;> norm_num)
        (hβ b)
      linarith

/-- **An event of the first player's reading**, bounded by the disagreement and the same event of
the second player's reading. -/
theorem sum_ite_read_le (hψ : ‖M.ψ‖ = 1) (P : POVMIn Λ 𝒜) (Q : POVMIn Λ' ℬ) (f : Λ → R)
    (g : Λ' → R) (E : R → Prop) [DecidablePred E] :
    ∑ a, (if E (f a) then M.bornProb (P.op a) 1 else 0)
      ≤ M.dis (P.map f) (Q.map g) + ∑ b, (if E (g b) then M.bornProb 1 (Q.op b) else 0) := by
  have hB : ∑ b, (if E (g b) then M.bornProb 1 (Q.op b) else 0)
      = ∑ a, ∑ b, (if E (g b) then 1 else 0) * M.bornProb (P.op a) (Q.op b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp only [one_mul]; exact M.bornProb_one_left P _
    · simp
  rw [hB, M.dis_map_eq_sum hψ, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  have hβ : ∀ b, 0 ≤ M.bornProb (P.op a) (Q.op b) := fun b =>
    M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b)
  by_cases hE : E (f a)
  · rw [ite_eq_left hE, M.bornProb_one_right _ Q]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hfg : f a = g b
    · rw [ite_eq_left hfg, ite_eq_left (hfg ▸ hE)]
      linarith
    · rw [ite_eq_right hfg]
      have := mul_nonneg (show (0 : ℝ) ≤ if E (g b) then 1 else 0 by split_ifs <;> norm_num)
        (hβ b)
      linarith
  · rw [ite_eq_right hE]
    exact Finset.sum_nonneg fun b _ =>
      add_nonneg (mul_nonneg (by split_ifs <;> norm_num) (hβ b))
        (mul_nonneg (by split_ifs <;> norm_num) (hβ b))

/-- **An event of the second player's reading**, bounded by the disagreement and the same event of
the first player's reading. -/
theorem sum_ite_read_le' (hψ : ‖M.ψ‖ = 1) (P : POVMIn Λ 𝒜) (Q : POVMIn Λ' ℬ) (f : Λ → R)
    (g : Λ' → R) (E : R → Prop) [DecidablePred E] :
    ∑ b, (if E (g b) then M.bornProb 1 (Q.op b) else 0)
      ≤ M.dis (P.map f) (Q.map g) + ∑ a, (if E (f a) then M.bornProb (P.op a) 1 else 0) := by
  have hB : ∑ b, (if E (g b) then M.bornProb 1 (Q.op b) else 0)
      = ∑ a, ∑ b, (if E (g b) then 1 else 0) * M.bornProb (P.op a) (Q.op b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp only [one_mul]; exact M.bornProb_one_left P _
    · simp
  rw [hB, M.dis_map_eq_sum hψ, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  have hβ : ∀ b, 0 ≤ M.bornProb (P.op a) (Q.op b) := fun b =>
    M.bornProb_nonneg (P.op_nonneg a) (Q.op_nonneg b)
  have hA : (if E (f a) then M.bornProb (P.op a) 1 else 0)
      = ∑ b, (if E (f a) then 1 else 0) * M.bornProb (P.op a) (Q.op b) := by
    split_ifs
    · simp only [one_mul]; exact M.bornProb_one_right _ Q
    · simp
  rw [hA, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hE : E (g b)
  · rw [ite_eq_left hE, one_mul]
    by_cases hfg : f a = g b
    · rw [ite_eq_left (hfg ▸ hE : E (f a)), ite_eq_left hfg]
      linarith [hβ b]
    · rw [ite_eq_right hfg]
      have := mul_nonneg (show (0 : ℝ) ≤ if E (f a) then 1 else 0 by split_ifs <;> norm_num)
        (hβ b)
      linarith
  · rw [ite_eq_right hE, zero_mul]
    exact add_nonneg (mul_nonneg (by split_ifs <;> norm_num) (hβ b))
      (mul_nonneg (by split_ifs <;> norm_num) (hβ b))

/-- Swapping a triple sum of an outcome's weight, kept on a condition. -/
theorem sum_swap_ite {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] (C : X → Y → Z → Prop)
    [∀ x y z, Decidable (C x y z)] (β : Z → ℝ) :
    ∑ x, ∑ y, ∑ z, (if C x y z then 0 else β z)
      = ∑ z, β z * ∑ x, ∑ y, (if C x y z then 0 else (1 : ℝ)) := by
  calc ∑ x, ∑ y, ∑ z, (if C x y z then 0 else β z)
      = ∑ x, ∑ z, ∑ y, (if C x y z then 0 else β z) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, (if C x y z then 0 else β z) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [mul_ite, mul_zero, mul_one]

end Generic

/-! ## Moving along the line a vector carries -/

section Shift

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM)

/-- The direction of the axis-parallel line the registers of a low-degree vector carry. -/
def dirIdx (w : Fin (D j) → Fq t ht) : Fin (2 ^ j) := LIDT.CL.chi hM (sel.π (w (regs j).coord))

/-- A low-degree vector with its point moved by `s` along its own direction. -/
def shiftW (s : Fq t ht) (w : Fin (D j) → Fq t ht) : Fin (D j) → Fq t ht :=
  w + s • Pi.single ((regs j).pt (dirIdx sel w)) 1

theorem shiftW_coord (s : Fq t ht) (w : Fin (D j) → Fq t ht) :
    shiftW sel s w (regs j).coord = w (regs j).coord := by
  simp [shiftW, ((regs j).pt_ne_coord _).symm]

theorem dirIdx_shiftW (s : Fq t ht) (w : Fin (D j) → Fq t ht) :
    dirIdx sel (shiftW sel s w) = dirIdx sel w := by
  rw [dirIdx, shiftW_coord]
  rfl

theorem ptOf_shiftW (s : Fq t ht) (w : Fin (D j) → Fq t ht) :
    (regs j).ptOf (shiftW sel s w) = (regs j).ptOf w + s • Pi.single (dirIdx sel w) 1 := by
  funext k
  simp only [LIDT.CL.Regs.ptOf, shiftW, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    (regs j).pt_injective.eq_iff]

theorem shiftW_shiftW (s s' : Fq t ht) (w : Fin (D j) → Fq t ht) :
    shiftW sel s' (shiftW sel s w) = shiftW sel (s + s') w := by
  rw [shiftW, dirIdx_shiftW, shiftW, add_assoc, ← add_smul]
  rfl

theorem shiftW_zero (w : Fin (D j) → Fq t ht) : shiftW sel 0 w = w := by
  simp [shiftW]

/-- Moving along the line, as an equivalence. -/
def shiftEquiv (s : Fq t ht) : (Fin (D j) → Fq t ht) ≃ (Fin (D j) → Fq t ht) where
  toFun := shiftW sel s
  invFun := shiftW sel (-s)
  left_inv w := by rw [shiftW_shiftW, add_neg_cancel, shiftW_zero]
  right_inv w := by rw [shiftW_shiftW, neg_add_cancel, shiftW_zero]

theorem sum_shiftW {X : Type*} [AddCommMonoid X] (s : Fq t ht)
    (F : (Fin (D j) → Fq t ht) → X) : ∑ w, F (shiftW sel s w) = ∑ w, F w :=
  (shiftEquiv sel s).sum_comp F

/-- **The line question is the same at every point of the line.** -/
theorem ldq_aline_shiftW (s : Fq t ht) (w : Fin (D j) → Fq t ht) :
    ldq sel .aline (shiftW sel s w) = ldq sel .aline w := by
  have h := MIPRE.LIDT.Simul.rep_add_smul' (Pi.single (dirIdx sel w) (1 : Fq t ht))
    ((regs j).ptOf w) s
  simp only [ldq, LIDT.CL.Regs.sampleOf, LIDT.CL.Sample.question, shiftW_coord, ptOf_shiftW]
  simp only [dirIdx] at h ⊢
  rw [h]

end Shift

/-! ## The indifference check, read -/

section Read

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} {L : PcpDims} (hLM : L.m ≤ 2 ^ j)

variable (j L) in
/-- The codewords of the oracle whose slots' blocks miss the direction `i`, the others zeroed. -/
def maskI {X : Type*} [Zero X] (i : Fin (2 ^ j)) (v : Fin (slotsOf L .oracle).length → X) :
    Fin (slotsOf L .oracle).length → X :=
  fun c => if i ∈ blockM j hLM ((slotsOf L .oracle).get c) then 0 else v c

variable (t ht j d L) in
/-- The constant coefficients of the codewords of an answer at an axis-parallel line. -/
def kv {B : ℕ} (a : Verifier.Answers B) : Fin (slotsOf L .oracle).length → Fq t ht :=
  fun c => cw t ht j d .aline a.1 c 0

/-- A polynomial whose coefficients of positive degree vanish is its constant coefficient. -/
theorem linePoly_eval_eq_zero_coef {F : Type*} [Field F] {e : ℕ} (f : LIDT.LinePoly F e)
    (hf : ∀ k : Fin e, f k.succ = 0) (x : F) : f.eval x = f 0 := by
  rw [LIDT.LinePoly.eval, Fin.sum_univ_succ, Finset.sum_eq_zero fun k _ => by rw [hf k, zero_mul]]
  simp

variable {hM : 2 ^ j ∣ Fintype.card (Fq t ht)} {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {B : ℕ}

/-- **The low-degree and indifference checks at a line and a point**, the line's answer Alice's:
the point values in the codewords whose blocks miss the line's direction are the constant
coefficients of the line's polynomials. -/
theorem kv_eq_pv_of_arDt {y : V.Questions n} {u₀ x : Fin (2 ^ j) → Fq t ht} {s : Fq t ht}
    {a b : Verifier.Answers B}
    (h : arDt d hM sel L hLM V n Cc hm B (arQr sel _ .oracle y (.aline u₀ s))
      (arQr sel _ .oracle y (.point x)) a b = true) :
    maskI j L hLM (LIDT.CL.chi hM s) (kv t ht j d L a) =
      maskI j L hLM (LIDT.CL.chi hM s) (pvR t ht j d L .oracle b) := by
  have hA := arPred_of_arDt h
  have h1 := hA.1 .oracle rfl rfl
  rw [ldQ_arQr, ldQ_arQr] at h1
  have h3 := hA.2.2.1
  rw [ldQ_arQr] at h3
  simp only [arQr, LIDT.CL.Question.ty, decAns, LIDT.CL.accepts, LIDT.CL.Question.fmtOk,
    LIDT.CL.subtests, Bool.true_and, LIDT.CL.lineVsPoint, decide_eq_true_eq] at h1
  funext c
  simp only [maskI]
  split_ifs with hc
  · rfl
  · show cw t ht j d .aline a.1 c 0 = cw t ht j d .point b.1 c 0
    have := h1.2 c
    rw [linePoly_eval_eq_zero_coef _ (fun k => h3 c hc k k.2)] at this
    exact this

/-- **The low-degree and indifference checks at a point and a line**, the line's answer Bob's. -/
theorem pv_eq_kv_of_arDt {y : V.Questions n} {u₀ x : Fin (2 ^ j) → Fq t ht} {s : Fq t ht}
    {a b : Verifier.Answers B}
    (h : arDt d hM sel L hLM V n Cc hm B (arQr sel _ .oracle y (.point x))
      (arQr sel _ .oracle y (.aline u₀ s)) a b = true) :
    maskI j L hLM (LIDT.CL.chi hM s) (pvR t ht j d L .oracle a) =
      maskI j L hLM (LIDT.CL.chi hM s) (kv t ht j d L b) := by
  have hA := arPred_of_arDt h
  have h1 := hA.1 .oracle rfl rfl
  rw [ldQ_arQr, ldQ_arQr] at h1
  have h4 := hA.2.2.2.1
  rw [ldQ_arQr] at h4
  simp only [arQr, LIDT.CL.Question.ty, decAns, LIDT.CL.accepts, LIDT.CL.Question.fmtOk,
    LIDT.CL.subtests, Bool.true_and, LIDT.CL.lineVsPoint, decide_eq_true_eq] at h1
  funext c
  simp only [maskI]
  split_ifs with hc
  · rfl
  · show cw t ht j d .point a.1 c 0 = cw t ht j d .aline b.1 c 0
    have := h1.2 c
    rw [linePoly_eval_eq_zero_coef _ (fun k => h4 c hc k k.2)] at this
    exact this.symm

end Read

/-! ## Block-local polynomials -/

section Good

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} {L : PcpDims}

variable (j L) in
/-- An outcome of the oracle's polynomial measurement is **block-local** when no codeword's
polynomial has a monomial in a variable outside its slot's block. -/
def Good (hLM : L.m ≤ 2 ^ j) (f : PolyR t ht j d L .oracle) : Prop :=
  ∀ c e, f c e ≠ 0 → ∀ i, i ∉ blockM j hLM ((slotsOf L .oracle).get c) → (e i : ℕ) = 0

open Classical in
/-- **A polynomial tuple that is not block-local changes, in some codeword whose block misses the
line's direction, along many steps on the lines the registers carry.** -/
theorem card_differ_ge {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
    (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM) (hLM : L.m ≤ 2 ^ j) {f : PolyR t ht j d L .oracle}
    (hf : ¬Good j L hLM f) :
    ((Fintype.card (Fq t ht) / 2 ^ j : ℕ) : ℝ) * (Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) *
        ((Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) *
          ((Fintype.card (Fq t ht) : ℝ) - ((2 ^ j : ℕ) + 1) * d))
      ≤ ∑ w : Fin (D j) → Fq t ht, ∑ s : Fq t ht,
        (if maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf w) f) =
          maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f) then 0
          else (1 : ℝ)) := by
  -- a monomial outside its block
  simp only [Good, not_forall] at hf
  obtain ⟨c, e, he, i, hi, hei⟩ := hf
  set g := f c
  set N : (Fin (2 ^ j) → Fq t ht) → ℝ := fun u =>
    ((univ.filter fun s : Fq t ht => g.eval (u + s • Pi.single i 1) ≠ g.eval u).card : ℝ)
  -- each step that changes `g` on a line in the direction `i` is counted
  have hstep : ∀ w, (if dirIdx sel w = i then N ((regs j).ptOf w) else 0)
      ≤ ∑ s : Fq t ht, (if maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf w) f) =
          maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f) then 0
          else (1 : ℝ)) := by
    intro w
    by_cases hw : dirIdx sel w = i
    · rw [ite_eq_left hw]
      simp only [N, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      by_cases hs : g.eval ((regs j).ptOf w + s • Pi.single i 1) ≠ g.eval ((regs j).ptOf w)
      · rw [ite_eq_left hs]
        rw [ite_eq_right]
        · norm_num
        · intro hm
          have hc := congrFun hm c
          simp only [maskI, hw, ite_eq_right hi, evalR, ptOf_shiftW] at hc
          exact hs hc.symm
      · rw [ite_eq_right hs]
        split_ifs <;> norm_num
    · rw [ite_eq_right hw]
      exact Finset.sum_nonneg fun s _ => by split_ifs <;> norm_num
  -- the lines in the direction `i`: `q / M` seeds, every direction register, every point
  have hcount : ∑ w : Fin (D j) → Fq t ht, (if dirIdx sel w = i then N ((regs j).ptOf w) else 0)
      = ((Fintype.card (Fq t ht) / 2 ^ j : ℕ) : ℝ) * (Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) *
          ∑ u, N u := by
    have h := LIDT.CL.Regs.sum_sampleOf (regs j) sel .aline
      (fun sm => if LIDT.CL.chi hM sm.s = i then N sm.u else 0)
    rw [card_regs_sub, pow_zero, one_smul] at h
    have hs : ∀ u : Fin (2 ^ j) → Fq t ht, ∑ s : Fq t ht, (if LIDT.CL.chi hM s = i then N u else 0)
        = ((Fintype.card (Fq t ht) / 2 ^ j : ℕ) : ℝ) * N u := by
      intro u
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        LIDT.CL.card_chi_fiber hM i]
    have hdir : (Fintype.card (Fin (2 ^ j) → Fq t ht) : ℝ) =
        (Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [show (∑ w : Fin (D j) → Fq t ht, if dirIdx sel w = i then N ((regs j).ptOf w) else 0)
      = _ from h]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [← Finset.mul_sum, hs]
    rw [hdir]
    ring
  -- the steps that change `g`
  have hpairs : ∑ u, N u = ((univ.filter fun p : (Fin (2 ^ j) → Fq t ht) × Fq t ht =>
      g.eval (p.1 + p.2 • Pi.single i 1) ≠ g.eval p.1).card : ℝ) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [N, Finset.card_filter, Nat.cast_sum]
  have hshift := MIPRE.LIDT.card_shift_ne_ge g he hei
  rw [← hpairs] at hshift
  calc ((Fintype.card (Fq t ht) / 2 ^ j : ℕ) : ℝ) * (Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) *
          ((Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) *
            ((Fintype.card (Fq t ht) : ℝ) - ((2 ^ j : ℕ) + 1) * d))
      ≤ ((Fintype.card (Fq t ht) / 2 ^ j : ℕ) : ℝ) * (Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) *
          ∑ u, N u := mul_le_mul_of_nonneg_left hshift (by positivity)
    _ = _ := hcount.symm
    _ ≤ _ := Finset.sum_le_sum fun w _ => hstep w

open Classical in
/-- **The steps an outcome that is not block-local changes on**, at least `q^{2M+2} / (2M)` of
them, once the field has `2 (M + 1) d` elements. -/
theorem card_steps_ge {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
    (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM) (hLM : L.m ≤ 2 ^ j)
    (hq : 2 * ((2 ^ j + 1) * d) ≤ Fintype.card (Fq t ht)) {f : PolyR t ht j d L .oracle}
    (hf : ¬Good j L hLM f) :
    (Fintype.card (Fin (D j) → Fq t ht) : ℝ) * Fintype.card (Fq t ht) /
        (2 * ((2 ^ j : ℕ) : ℝ))
      ≤ ∑ w : Fin (D j) → Fq t ht, ∑ s : Fq t ht,
        (if maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf w) f) =
          maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f) then 0
          else (1 : ℝ)) := by
  refine le_trans ?_ (card_differ_ge sel hLM hf)
  have hq0 : (0 : ℝ) < Fintype.card (Fq t ht) := by positivity
  have hM0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hdiv : ((Fintype.card (Fq t ht) / 2 ^ j : ℕ) : ℝ) =
      (Fintype.card (Fq t ht) : ℝ) / ((2 ^ j : ℕ) : ℝ) := Nat.cast_div hM (by positivity)
  have hW : (Fintype.card (Fin (D j) → Fq t ht) : ℝ) =
      (Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) * (Fintype.card (Fq t ht) : ℝ) ^ (2 ^ j) *
        Fintype.card (Fq t ht) := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, D, pow_succ, two_mul, pow_add]
  have hd' : (((2 ^ j : ℕ) : ℝ) + 1) * d ≤ (Fintype.card (Fq t ht) : ℝ) / 2 := by
    have h0 : ((2 * ((2 ^ j + 1) * d) : ℕ) : ℝ) ≤ (Fintype.card (Fq t ht) : ℝ) := by
      exact_mod_cast hq
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h0
    linarith
  rw [hdiv, hW]
  generalize (Fintype.card (Fq t ht) : ℝ) = q at hq0 hd' ⊢
  generalize ((2 ^ j : ℕ) : ℝ) = Mj at hM0 hd' ⊢
  have hqj : 0 < q ^ (2 ^ j) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have e : q / Mj * q ^ (2 ^ j) * (q ^ (2 ^ j) * (q - (Mj + 1) * d)) * (2 * Mj)
      = 2 * q * q ^ (2 ^ j) * q ^ (2 ^ j) * (q - (Mj + 1) * d) := by
    field_simp
  rw [e]
  have h2 : q ≤ 2 * (q - (Mj + 1) * d) := by linarith
  have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ q * q ^ (2 ^ j) * q ^ (2 ^ j))
  nlinarith

end Good

/-! ## The weight of the outcomes that are not block-local -/

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}
  (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B)) (hL : LIDT.Simul.SoundIn M)
  (hd : 1 ≤ d) (hP : ArSampler hM sel V n P)

open Classical in
/-- **The steps along the lines where Alice's polynomials change**, in the codewords whose blocks
miss the line's direction, weigh at most the extraction's error and twice the failure at the type
pair `(O, ALine), (O, Point)`, `12` and `22` times, at one seed. -/
theorem sum_differ_le (z : V.Questions n) :
    ∑ w : Fin (D j) → Fq t ht, ∑ s : Fq t ht, ∑ f,
        (if maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf w) f) =
          maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f) then 0
          else M.bornProb ((GA T hL hd .oracle (oq V n .oracle z)).op f) 1)
      ≤ Fintype.card (Fq t ht) *
        (12 * ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
            (evalR ((regs j).ptOf w)))
          ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
            (pvR t ht j d L .oracle))
        + 22 * ∑ w, edgeFail T ((.oracle, .aline), (.oracle, .point)) z w) := by
  set G := GA T hL hd .oracle (oq V n .oracle z) with hG
  set E2 : ℝ := ∑ w, M.dis (G.map (evalR ((regs j).ptOf w)))
    ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
      (pvR t ht j d L .oracle)) with hE2
  set F : ℝ := ∑ w, edgeFail T ((.oracle, .aline), (.oracle, .point)) z w with hF
  -- the readings
  let A : (Fin (D j) → Fq t ht) → POVMIn (Fin (slotsOf L .oracle).length → Fq t ht) 𝒜 :=
    fun w => G.map fun f => maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf w) f)
  let Bw : (Fin (D j) → Fq t ht) → POVMIn (Fin (slotsOf L .oracle).length → Fq t ht) ℬ :=
    fun w => (T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
      fun b => maskI j L hLM (dirIdx sel w) (pvR t ht j d L .oracle b)
  let Cw : (Fin (D j) → Fq t ht) → POVMIn (Fin (slotsOf L .oracle).length → Fq t ht) 𝒜 :=
    fun w => (T.PA (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .aline w))).map
      fun a => maskI j L hLM (dirIdx sel w) (kv t ht j d L a)
  have hC : ∀ s w, Cw (shiftW sel s w) = Cw w := fun s w => by
    simp only [Cw, ldq_aline_shiftW, dirIdx_shiftW]
  -- Alice's evaluations against Bob's point values
  have hAB : ∀ w, M.dis (A w) (Bw w) ≤ M.dis (G.map (evalR ((regs j).ptOf w)))
      ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
        (pvR t ht j d L .oracle)) := fun w => by
    have e1 : A w = (G.map (evalR ((regs j).ptOf w))).map (maskI j L hLM (dirIdx sel w)) := by
      simp only [A, POVMIn.map_map]
    have e2 : Bw w = ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
        (pvR t ht j d L .oracle)).map (maskI j L hLM (dirIdx sel w)) := by
      simp only [Bw, POVMIn.map_map]
    rw [e1, e2]
    exact M.dis_map_le _ _ _
  -- the line answer against the point answer
  have hCB : ∀ w, M.dis (Cw w) (Bw w) ≤ edgeFail T ((.oracle, .aline), (.oracle, .point)) z w :=
    fun w => M.dis_map_le_condFail _ _ fun a b h => kv_eq_pv_of_arDt hLM h
  -- the triangle, on the vectors and the steps
  have htri := M.sum_dis_triangle T.ψ_unit
    (fun x : (Fin (D j) → Fq t ht) × Fq t ht => A x.1) (fun x => Cw x.1)
    (fun x => Bw x.1) (fun x => Bw (shiftW sel x.2 x.1))
  simp only [Fintype.sum_prod_type] at htri
  have h1 : ∑ w, ∑ _s : Fq t ht, M.dis (A w) (Bw w) ≤ Fintype.card (Fq t ht) * E2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hE2, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hAB w) (by positivity)
  have h2 : ∑ w, ∑ _s : Fq t ht, M.dis (Cw w) (Bw w) ≤ Fintype.card (Fq t ht) * F := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hF, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hCB w) (by positivity)
  have h3 : ∑ w, ∑ s : Fq t ht, M.dis (Cw w) (Bw (shiftW sel s w))
      ≤ Fintype.card (Fq t ht) * F := by
    rw [Finset.sum_comm]
    calc ∑ s : Fq t ht, ∑ w, M.dis (Cw w) (Bw (shiftW sel s w))
        = ∑ s : Fq t ht, ∑ w, M.dis (Cw (shiftW sel s w)) (Bw (shiftW sel s w)) := by
          simp only [hC]
      _ = ∑ s : Fq t ht, ∑ w, M.dis (Cw w) (Bw w) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          exact sum_shiftW sel s fun w => M.dis (Cw w) (Bw w)
      _ ≤ ∑ _s : Fq t ht, F := Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun w _ => hCB w
      _ = Fintype.card (Fq t ht) * F := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the second point, against Bob's point there
  have h4 : ∑ w, ∑ s : Fq t ht, M.dis (G.map fun f =>
        maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f))
        (Bw (shiftW sel s w)) ≤ Fintype.card (Fq t ht) * E2 := by
    rw [Finset.sum_comm]
    calc ∑ s : Fq t ht, ∑ w, M.dis (G.map fun f =>
          maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f))
          (Bw (shiftW sel s w))
        = ∑ s : Fq t ht, ∑ w, M.dis (A (shiftW sel s w)) (Bw (shiftW sel s w)) := by
          simp only [A, dirIdx_shiftW]
      _ = ∑ s : Fq t ht, ∑ w, M.dis (A w) (Bw w) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          exact sum_shiftW sel s fun w => M.dis (A w) (Bw w)
      _ ≤ ∑ _s : Fq t ht, E2 := Finset.sum_le_sum fun s _ => by
          rw [hE2]
          exact Finset.sum_le_sum fun w _ => hAB w
      _ = Fintype.card (Fq t ht) * E2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the two points of the line, against Bob's point at the second
  have hpt : ∀ w s, ∑ f, (if maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf w) f) =
        maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f) then 0
        else M.bornProb (G.op f) 1)
      ≤ M.dis (A w) (Bw (shiftW sel s w)) + M.dis (G.map fun f =>
        maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f))
        (Bw (shiftW sel s w)) := fun w s =>
    sum_ite_ne_le_dis_add M T.ψ_unit G _ _ _ _
  calc _ ≤ ∑ w, ∑ s : Fq t ht, (M.dis (A w) (Bw (shiftW sel s w)) + M.dis (G.map fun f =>
          maskI j L hLM (dirIdx sel w) (evalR ((regs j).ptOf (shiftW sel s w)) f))
          (Bw (shiftW sel s w))) :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun s _ => hpt w s
    _ ≤ 11 * (Fintype.card (Fq t ht) * E2 + Fintype.card (Fq t ht) * F +
          Fintype.card (Fq t ht) * F) + Fintype.card (Fq t ht) * E2 := by
        simp only [Finset.sum_add_distrib]
        have := htri.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3)
          (by norm_num))
        linarith
    _ = _ := by ring

open Classical in
/-- **The oracle outcomes of Alice that are not block-local**, at one seed: at most `2M` times the
errors of `sum_differ_le`, per vector, once the field has `2 (M + 1) d` elements. -/
theorem badGood_le (hq : 2 * ((2 ^ j + 1) * d) ≤ Fintype.card (Fq t ht)) (z : V.Questions n) :
    ∑ f, (if Good j L hLM f then 0
        else M.bornProb ((GA T hL hd .oracle (oq V n .oracle z)).op f) 1)
      ≤ 2 * 2 ^ j / Fintype.card (Fin (D j) → Fq t ht) *
        (12 * ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
            (evalR ((regs j).ptOf w)))
          ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
            (pvR t ht j d L .oracle))
        + 22 * ∑ w, edgeFail T ((.oracle, .aline), (.oracle, .point)) z w) := by
  have hq0 : (0 : ℝ) < Fintype.card (Fq t ht) := by positivity
  have hW0 : (0 : ℝ) < Fintype.card (Fin (D j) → Fq t ht) := by positivity
  have hsum := sum_differ_le T hL hd z (hLM := hLM)
  rw [sum_swap_ite] at hsum
  have hle : (Fintype.card (Fin (D j) → Fq t ht) : ℝ) * Fintype.card (Fq t ht) /
      (2 * ((2 ^ j : ℕ) : ℝ)) * ∑ f, (if Good j L hLM f then 0
        else M.bornProb ((GA T hL hd .oracle (oq V n .oracle z)).op f) 1)
      ≤ Fintype.card (Fq t ht) * (12 * ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
            (evalR ((regs j).ptOf w)))
          ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
            (pvR t ht j d L .oracle))
        + 22 * ∑ w, edgeFail T ((.oracle, .aline), (.oracle, .point)) z w) := by
    refine le_trans ?_ hsum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    have hβ := M.bornProb_nonneg ((GA T hL hd .oracle (oq V n .oracle z)).op_nonneg f)
      zero_le_one
    by_cases hg : Good j L hLM f
    · rw [ite_eq_left hg, mul_zero]
      exact mul_nonneg hβ (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun s _ => by
        split_ifs <;> norm_num)
    · rw [ite_eq_right hg, mul_comm]
      exact mul_le_mul_of_nonneg_left (card_steps_ge sel hLM hq hg) hβ
  have hpos : (0 : ℝ) < (Fintype.card (Fin (D j) → Fq t ht) : ℝ) * Fintype.card (Fq t ht) /
      (2 * ((2 ^ j : ℕ) : ℝ)) := by positivity
  rw [← le_div_iff₀' hpos] at hle
  refine hle.trans (le_of_eq ?_)
  push_cast
  field_simp


include hP in
open Classical in
/-- **The oracle outcomes of Alice that are not block-local**, averaged over the seeds: at most
`2M` times `12` times the extraction's error plus `1782` times the typed failure. -/
theorem sum_badGood_le (hq : 2 * ((2 ^ j + 1) * d) ≤ Fintype.card (Fq t ht)) :
    ∑ z, ∑ f, (if Good j L hLM f then 0
        else M.bornProb ((GA T hL hd .oracle (oq V n .oracle z)).op f) 1)
      ≤ Fintype.card (V.Questions n) * (2 * 2 ^ j *
        (12 * dS t ht j d L .oracle (9 * (1 - T.value)) + 1782 * (1 - T.value))) := by
  have hW0 : (0 : ℝ) < Fintype.card (Fin (D j) → Fq t ht) := by positivity
  have hE2 := sum_dis_GA_MB_le T hL hd hP .oracle
  have hF := sum_edge_le T hP ((.oracle, .aline), (.oracle, .point))
  calc _ ≤ ∑ z, 2 * 2 ^ j / Fintype.card (Fin (D j) → Fq t ht) *
          (12 * ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
              (evalR ((regs j).ptOf w)))
            ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
              (pvR t ht j d L .oracle))
          + 22 * ∑ w, edgeFail T ((.oracle, .aline), (.oracle, .point)) z w) :=
        Finset.sum_le_sum fun z _ => badGood_le T hL hd hq z
    _ = 2 * 2 ^ j / Fintype.card (Fin (D j) → Fq t ht) *
          (12 * ∑ z, ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
              (evalR ((regs j).ptOf w)))
            ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
              (pvR t ht j d L .oracle))
          + 22 * ∑ z, ∑ w, edgeFail T ((.oracle, .aline), (.oracle, .point)) z w) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * 2 ^ j / Fintype.card (Fin (D j) → Fq t ht) *
          (12 * (Fintype.card (V.Questions n) * (Fintype.card (Fin (D j) → Fq t ht) *
            dS t ht j d L .oracle (9 * (1 - T.value))))
          + 22 * (81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht)) *
            (1 - T.value))) := by
        gcongr
    _ = _ := by
        field_simp
        ring

end MIPRE.Tailored.AnsRed.Typed

end
