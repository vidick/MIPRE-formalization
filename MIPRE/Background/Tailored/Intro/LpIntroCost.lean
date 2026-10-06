/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.LpIntro

@[expose] public section

/-!
# The costs of the introspection processor

Issue #281. The linear-constraints processor `lpIntroC c U V λ` of `LpIntro.lean`:

* `lpIntroC_size`, `lpIntroC_size_le`: its description has size at most `C (λ + 1)^C`, whatever
  the input programs `V` (the clamped description has size at most `19 (λ + 1)`);
* `core_runs_poly`: the core runs within a fixed polynomial of any bound `v` of the input, the
  clock `2^{(λn + 1)^5}` and `Q`, `R` (the decision kernel's `prog_runs_poly`, the unary
  conversion, and the core's `PolyTimeFun` on the prepared input);
* `lpIntroC_budget`: one constant `C` with the processor within `2^{(λn + 1)^C}` at degree `C`
  on every input, malformed included, and for every `V` — the shape of `Introspection.budget`.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.LpIntro

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL MIPRE.Introspection InputRuns Polynomial
open CL.Detyping CL.Detyping.Program

/-! ## The size of the description -/

theorem esize_lenWrap (p : Prog) : esize (LenIntro.lenWrap p) = esize p + 54 := by
  simp only [LenIntro.lenWrap, callVar, Prog.esize_eq_size_toData, Prog.toData, Data.size_cons,
    Data.size_nil, Data.size_ofNat]
  omega

/-- The size of the processor's description. -/
theorem lpIntroC_size (c : ℕ) (U : ClockedUniversalMachine) (V : Prog × Prog × Prog)
    (lam : ℕ) :
    (lpIntroC c U V lam).size ≤ esize (core c U) + 19 * (lam + 1) + 89 := by
  change esize (lpProg c U V lam) ≤ _
  unfold lpProg
  split_ifs
  · simp only [Prog.esize_eq_size_toData, Prog.toData, Data.size_cons, Data.size_nil,
      Data.size_ofNat]
    omega
  · rw [esize_lenWrap, hardcode_size]
    have := clamp_size V lam
    change esize (core c U) + esize (clamp (V, lam)) + 35 + 54 ≤ _
    omega

/-- **The processor's description has size at most `C (λ + 1)^C`**, for every input. -/
theorem lpIntroC_size_le (c : ℕ) (U : ClockedUniversalMachine) : ∃ C : ℕ,
    ∀ (V : Prog × Prog × Prog) (lam : ℕ),
      (lpIntroC c U V lam).size ≤ C * (lam + 1) ^ C := by
  refine ⟨esize (core c U) + 110, fun V lam => (lpIntroC_size c U V lam).trans ?_⟩
  have h1 : lam + 1 ≤ (lam + 1) ^ (esize (core c U) + 110) :=
    Nat.le_self_pow (by omega) _
  nlinarith

/-! ## The run of the core -/

/-- A polynomial for the conversion of `(Q, R)` to unary. -/
def bothPoly : Polynomial ℕ :=
  2 * ((X + 2) * ((X + 1) * (4 * X + 14) + 7 * (4 * X + 1) + 8 * X + 90)) + 12 * X + 22

theorem bothPoly_eval (v : ℕ) :
    bothPoly.eval v = 2 * PauliSamplerParameters.unaryMajorant v + 12 * v + 22 := by
  simp only [bothPoly, PauliSamplerParameters.unaryMajorant, eval_add, eval_mul, eval_X,
    eval_ofNat, eval_one]

theorem esize_le_of_le {x v : ℕ} (h : x ≤ v) : esize x ≤ 4 * v + 1 :=
  (esize_nat_le x).trans (by have := (Nat.size_le.mpr Nat.lt_two_pow_self : x.size ≤ x); omega)

theorem bothCost_le {Q R v : ℕ} (hQ : Q ≤ v) (hR : R ≤ v) :
    ClockArithmetic.unaryCost Q + ClockArithmetic.unaryCost R + esize Q + esize R + 2 * Q +
      2 * R + 20 ≤ bothPoly.eval v := by
  have h1 := PauliSamplerParameters.unaryCost_le hQ
  have h2 := PauliSamplerParameters.unaryCost_le hR
  have e1 := esize_le_of_le hQ
  have e2 := esize_le_of_le hR
  rw [bothPoly_eval]
  omega

/-- The polynomial of the core. -/
def corePoly (c : ℕ) (U : ClockedUniversalMachine) : Polynomial ℕ :=
  DecisionPreparation.preparationPoly c +
    DecisionPreparation.appendPoly argQR (DecisionPreparation.preparationPoly c) bothPoly +
    (kernel U).timeBound.comp
      (DecisionPreparation.appendPoly argQR (DecisionPreparation.preparationPoly c) bothPoly) + 2

/-- **The core runs within a fixed polynomial** of any bound `v` of the input, the clock, `Q` and
`R`, at positive `λ` and index. -/
theorem core_runs_poly {c v : ℕ} (hc : 1 ≤ c) (U : ClockedUniversalMachine) (M : Metadata)
    (x : Data) (hl : 1 ≤ M.2) (hn : 1 ≤ ClockSimulation.indexReader x)
    (hz : esize M + x.size + 1 ≤ v) (hB : ansBound 5 M.2 (ClockSimulation.indexReader x) ≤ v)
    (hQ : SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x) ≤ v)
    (hR : SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x) ≤ v) :
    ∃ t ≤ (corePoly c U).eval v, (core c U).Runs (.cons (encode M) x)
      (encode (kernel U (kernelInput c M x,
        (unary (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x)),
          unary (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x)))))) t := by
  have hmeta : DecisionPreparation.inputLambda (.cons (encode M) x) = M.2 := by
    rcases M with ⟨⟨S, L, P⟩, lam⟩
    simp [DecisionPreparation.inputLambda, DecisionPreparation.inputMetadata, encode_prod,
      readNat_encode]
  obtain ⟨s₁, hs₁, h₁⟩ := DecisionPreparation.prog_runs_poly hc (.cons (encode M) x)
    (by rw [hmeta]; exact hl) hn (by change (encode M).size + x.size + 1 ≤ v; exact hz)
    (by rw [hmeta]; exact hB)
  rw [← encode_kernelInput] at h₁
  obtain ⟨t₂, ht₂, h₂⟩ := ClockArithmetic.bothUnary_runs
    (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x))
    (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x))
  rw [← argQR_kernelInput] at h₂
  obtain ⟨s₂, hs₂, h₂'⟩ := DecisionPreparation.appendStage_runs_poly argQR
    ClockArithmetic.bothUnary_closed (DecisionPreparation.preparationPoly c) bothPoly v _ _
    (h₁.size_le.trans hs₁) t₂ (ht₂.trans (bothCost_le hQ hR)) h₂
  have h₂'' : (DecisionPreparation.appendStage argQR ClockArithmetic.bothUnary).Runs
      (encode (kernelInput c M x)) (encode (kernelInput c M x,
        (unary (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x)),
          unary (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x))))) s₂ := by
    simpa only [encode_prod, encode_unary] using h₂'
  obtain ⟨s₃, hs₃, h₃⟩ := (kernel U).computes (kernelInput c M x,
    (unary (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x)),
      unary (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x))))
  have hsz := h₂''.size_le.trans hs₂
  have he := polynomial_eval_mono (kernel U).timeBound hsz
  refine ⟨_, ?_, DecisionPreparation.sequence_runs (DecisionPreparation.sequence_closed
    (DecisionPreparation.appendStage_closed _ ClockArithmetic.bothUnary_closed)
      (kernel U).closed) h₁
    (DecisionPreparation.sequence_runs (kernel U).closed h₂'' h₃)⟩
  simp only [corePoly, eval_add, eval_comp, eval_ofNat]
  change s₃ ≤ (kernel U).timeBound.eval (encode _ : Data).size at hs₃
  omega

/-! ## The budget -/

/-- The run of the processor at positive `λ` and `n`, on every input, with its cost. -/
theorem lpIntroC_runs_poly {c v : ℕ} (hc : 1 ≤ c) (U : ClockedUniversalMachine)
    (V : Prog × Prog × Prog) {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (d : Data)
    (hz : 19 * (lam + 1) + 4 * n + d.size + 3 ≤ v) (hB : ansBound 5 lam n ≤ v)
    (hQ : SourceCompiler.registerBits c lam n ≤ v)
    (hR : SourceCompiler.originalBound lam n ≤ v) :
    ∃ r, ∃ t ≤ (corePoly c U).eval v + 2 * v + 7,
      (lpIntroC c U V lam).prog.Runs (.cons (encode n) d) r t := by
  have hidx : ClockSimulation.indexReader (.cons (encode n) d) = n := by
    simp [ClockSimulation.indexReader, readNat_encode]
  have hM : (clamp (V, lam)).2 = lam := rfl
  have hsM := clamp_size V lam
  have hsn := esize_le_of_le (le_refl n)
  have hxs : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
  obtain ⟨t, ht, hr⟩ := core_runs_poly (v := v) hc U (clamp (V, lam)) (.cons (encode n) d)
    (by rw [hM]; exact hl) (by rw [hidx]; exact hn) (by omega) (by rw [hM, hidx]; exact hB)
    (by rw [hM, hidx]; exact hQ) (by rw [hM, hidx]; exact hR)
  have hh := hardcode_time (core_wellScoped c U) hr
  have hw := LenIntro.lenWrap_runs_pos (hardcode_wellScoped (core_wellScoped c U) _) hn _ _ _ hh
  refine ⟨_, _, ?_, (show (lpProg c U V lam).Runs _ _ _ by
    rw [lpProg, ite_eq_right (by omega)]; exact hw)⟩
  change t + esize (clamp (V, lam)) + (Data.cons (encode n) d).size + 3 +
    (Data.cons (encode n) d).size + 4 ≤ _
  omega

theorem small_le_two_pow {u E : ℕ} (hu : 1 ≤ u) (hE : 3 ≤ E) :
    64 * (u + 1) ≤ 2 ^ ((u + 1) ^ E) := by
  have h1 : u + 1 ≤ 2 ^ u := Nat.lt_two_pow_self
  have h2 : (u + 1) ^ 3 ≤ (u + 1) ^ E := Nat.pow_le_pow_right (by omega) hE
  have h3 : u + 6 ≤ (u + 1) ^ 3 := by
    have h4 : 4 ≤ (u + 1) ^ 2 := by nlinarith
    calc u + 6 ≤ 4 * (u + 1) := by omega
      _ ≤ (u + 1) ^ 2 * (u + 1) := Nat.mul_le_mul_right _ h4
      _ = (u + 1) ^ 3 := by ring
  calc 64 * (u + 1) ≤ 2 ^ 6 * 2 ^ u := by omega
    _ = 2 ^ (u + 6) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ ((u + 1) ^ E) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The costs of the processor**, in the shape of `Introspection.budget`: one constant `C` with
the processor within `2^{(λn + 1)^C}` at degree `C` on every input, for every input description. -/
theorem lpIntroC_budget {c : ℕ} (hc : 1 ≤ c) (U : ClockedUniversalMachine) : ∃ C : ℕ,
    ∀ (V : Prog × Prog × Prog) (lam n : ℕ),
      (lpIntroC c U V lam).TimeBoundAt n (ansBound C lam n) C := by
  have hF : PolyBounded fun v => (corePoly c U).eval v + 2 * v + 7 :=
    ((PolyBounded.eval _ PolyBounded.id).add (PolyBounded.id.const_mul 2)).add_const 7
  obtain ⟨L, hL⟩ := hF.exists_le_pow
  set E := 4 * c + 9 with hE
  refine ⟨E + 3 * L + 1, fun V lam n d => ?_⟩
  have hs := Data.size_pos d
  have hpos : 1 ≤ (d.size + 1) ^ (E + 3 * L + 1) := Nat.one_le_pow _ _ (by omega)
  have hab : 1 ≤ ansBound (E + 3 * L + 1) lam n := Nat.one_le_two_pow
  by_cases hl : lam = 0
  · subst hl
    refine ⟨.nil, 1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    show (lpProg c U V 0).Runs _ _ _
    rw [lpProg, ite_eq_left rfl]
    exact Eval.nil _
  by_cases hn : n = 0
  · subst hn
    refine ⟨.nil, 3, ?_, ?_⟩
    · have h2 : 2 ≤ (d.size + 1) ^ (E + 3 * L + 1) :=
        (show 2 ≤ d.size + 1 by omega).trans (Nat.le_self_pow (by omega) _)
      simp only [ansBound, Nat.mul_zero, Nat.zero_add, one_pow, pow_one]
      omega
    · show (lpProg c U V lam).Runs _ _ _
      rw [lpProg, ite_eq_right hl]
      exact LenIntro.lenWrap_runs_zero _ _
  have hl1 : 1 ≤ lam := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hlz, hnz, -, hQz, hRz⟩ := LenIntro.params_le_scale c hl1 hn1
  set u := lam * n with hu
  have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  set B := 2 ^ ((u + 1) ^ E) with hB
  -- the three parts of the bound
  have hA1 : ansBound 5 lam n ≤ B := by
    unfold ansBound
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
  have hA2 : LenIntro.scale c u ≤ B := by
    unfold LenIntro.scale
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 : (2 * c + 2) * (u + 2) ≤ (4 * c + 4) * (u + 1) := by nlinarith
    exact h1.trans (LenIntro.mul_le_pow hu1 (by omega)
      ((show 4 * c + 4 ≤ E - 1 by omega).trans Nat.lt_two_pow_self.le))
  have hA3 : 19 * (lam + 1) + 4 * n + 3 ≤ B := by
    have hlu : lam ≤ u := Nat.le_mul_of_pos_right lam hn1
    have hnu : n ≤ u := Nat.le_mul_of_pos_left n hl1
    exact le_trans (by omega) (small_le_two_pow hu1 (by omega : 3 ≤ E))
  set v := ansBound 5 lam n + LenIntro.scale c u + (19 * (lam + 1) + 4 * n + 3) + d.size with hv
  obtain ⟨r, t, ht, hr⟩ := lpIntroC_runs_poly (v := v) hc U V hl1 hn1 d (by omega) (by omega)
    (by omega) (by omega)
  refine ⟨r, t, ?_, hr⟩
  have hB1 : 1 ≤ B := Nat.one_le_two_pow
  have hv2 : 2 ≤ v := by
    have := ClockArithmetic.clock_arguments_le (by decide : 1 ≤ 5) hl1 hn1
    omega
  have hvle : v ≤ (3 * B) * (d.size + 1) := by nlinarith
  have hvL : v ^ L ≤ (3 * B) ^ L * (d.size + 1) ^ L := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hvle L
  -- `(3B)^L ≤ 2^{(u + 1)^C}`
  have hexp : L * ((u + 1) ^ E + 2) ≤ (u + 1) ^ (E + 3 * L + 1) := by
    have hx : 1 ≤ (u + 1) ^ E := Nat.one_le_pow _ _ (by omega)
    have h1 : L * ((u + 1) ^ E + 2) ≤ 3 * L * (u + 1) ^ E := by nlinarith
    have h2 : 3 * L ≤ (u + 1) ^ (3 * L + 1) :=
      (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega) _)).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    calc L * ((u + 1) ^ E + 2) ≤ 3 * L * (u + 1) ^ E := h1
      _ ≤ (u + 1) ^ (3 * L + 1) * (u + 1) ^ E := Nat.mul_le_mul_right _ h2
      _ = (u + 1) ^ (E + 3 * L + 1) := by rw [← pow_add]; ring_nf
  have h3B : (3 * B) ^ L ≤ ansBound (E + 3 * L + 1) lam n := by
    have : 3 * B ≤ 2 ^ ((u + 1) ^ E + 2) := by rw [pow_add]; omega
    calc (3 * B) ^ L ≤ (2 ^ ((u + 1) ^ E + 2)) ^ L := Nat.pow_le_pow_left this L
      _ = 2 ^ (L * ((u + 1) ^ E + 2)) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ ansBound (E + 3 * L + 1) lam n := Nat.pow_le_pow_right (by norm_num) hexp
  have hdeg : (d.size + 1) ^ L ≤ (d.size + 1) ^ (E + 3 * L + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc t ≤ (corePoly c U).eval v + 2 * v + 7 := ht
    _ ≤ v ^ L := hL v hv2
    _ ≤ (3 * B) ^ L * (d.size + 1) ^ L := hvL
    _ ≤ ansBound (E + 3 * L + 1) lam n * (d.size + 1) ^ (E + 3 * L + 1) := Nat.mul_le_mul h3B hdeg

/-! ## At the constant of `Introspection.seven` -/

/-- **The costs of `lpIntro`**, in the shape of `Introspection.budget`. -/
theorem lpIntro_budget : ∃ C : ℕ, ∀ (V : Prog × Prog × Prog) (lam n : ℕ),
    (lpIntro V lam).TimeBoundAt n (Introspection.budget C lam n).D
      (Introspection.budget C lam n).k :=
  lpIntroC_budget one_le_sevenConstant selfClockedUniversal

/-- **`|LP^intro| ≤ C (λ + 1)^C`**, for every input. -/
theorem lpIntro_size_le : ∃ C : ℕ, ∀ (V : Prog × Prog × Prog) (lam : ℕ),
    (lpIntro V lam).size ≤ C * (lam + 1) ^ C :=
  lpIntroC_size_le sevenConstant selfClockedUniversal

end MIPRE.Tailored.Intro.LpIntro

end
