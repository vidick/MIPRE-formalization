/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.ClassPolyTab
public import MIPRE.Tailored.Extend
public import MIPRE.Tailored.Halting.Reduction
public import MIPRE.Foundations.Halting.Paper.ClassSampler
public import MIPRE.Foundations.Cost.ManyOne

@[expose] public section

/-!
# `RE ⊆ TMIP*`, and `TMIP* = RE`, for the polynomial-time class

The polynomial-time tailored verifier (`TPolyVerifier`, `Tailored/ClassPoly.lean`) that puts an
r.e. language `L` in the paper's class `TMIP*` (II:787), for a polynomial-time reduction `R` of
`L` to halting on the empty input (`Cost.exists_polyTime_reduction`): on the input `z` it plays
the game of the tailored halting verifier `V^{R z, λ(z)}` (`Halting.VT`) at the fixed level `C`,
with `λ(z) = Λ₀ + 4|R z|` and `Λ₀` the threshold of `lem:lambda` (`Halting.lamThreshold`).

* **The sampler** is the class sampler of `Paper/ClassSampler.lean` for the compressed samplers
  (`TailoredGapCompression.samplerFamily`) at the level `C`; at the level `0` of the compression
  it outputs the empty pair, the questions being empty there.
* **The answer-length calculator**, on `(z, x, κ)`, computes the compressed calculator's program
  `L^{λ(z)}` (`lenPrep`) and runs it on `(C, x, κ)` through the universal machine.
* **The linear-constraints processor**, on `(z, x, y, a^R, b^R)`, computes the program of the
  processor `LP^{R z, λ(z)}` of the halting verifier, in polynomial time (`lpBuild`, `lpPrep`),
  and runs it on `(C, x, y, a^R, b^R)` through the universal machine.

The universal machine's simulation halts exactly when the simulated program does, with its
output (`seqUniv_runs`, `seqUniv_runs_rev`), so the calculator and the processor output what
those of `V^{R z, λ(z)}` output at the level `C` (`lenIs_iff`, `lpIs_iff`). The game of the class
verifier on `z` therefore extends that of `V^{R z, λ(z)}` at `C` along the embedding of the
questions as bit strings (`tgame_extends`, `TailoredGame.Extends`): it has the same quantum value
and inherits its perfect ZPC strategies, on the doubled games.

**Efficiency** (`classTV_efficient`). The sampler is `Paper/ClassSampler.lean`'s. The compressed
calculator runs within `poly(C, λ(z))` times a power of its input's size (the field `len_time`
of the compression), and the processor of `V^{M,λ}` within `Q(C + |M| + λ)` times one
(`exists_lp_cost_poly`), so both class programs run within polynomials in the total input length
(`lenB`, `lpB`), below the verifier's polynomial `classTP`.

Hence `MIPRE.Tailored.re_subset_tmipStar_of` from `thm:tailored-halting` at the fixed level
(`Halting.halting_tailored_search`), and `MIPRE.Tailored.tmipStar_eq_re_of` with
`TMIPStar.isRE` (`Tailored/ClassPolyTab.lean`).
-/

namespace MIPRE.Tailored

open Cost Cost.Prog Cost.PolyTimeFun
open MIPRE.Halting (lamz lamB lamF lamF_apply lamz_le polyBounded_lamB SamplerFamily)

/-- The compressed samplers of a tailored gap compression, as a polynomial-time family of
samplers at its level. -/
def TailoredGapCompression.samplerFamily {ℓ : ℕ} (TG : TailoredGapCompression ℓ) :
    SamplerFamily ℓ :=
  ⟨TG.sampler, TG.samplerProg, TG.samplerProg_eq, TG.bound, TG.deg, TG.sampler_time,
    TG.sampler_dim⟩

/-! ## A preparation followed by the universal machine -/

section SeqUniv

variable (U : UniversalMachine) {α β : Type*} [SizedEncoding α] [SizedEncoding β]
  (P : PolyTimeFun α (Prog × β))

/-- **A preparation followed by the universal machine** runs the prepared program on the
prepared input, at the cost of the preparation and of the simulation. -/
theorem seqUniv_runs (a : α) {r : Data} {t : ℕ} (h : (P a).1.Runs (encode (P a).2) r t) :
    ∃ t' ≤ 2 * P.timeBound.eval (esize a) + U.bound.eval (P.timeBound.eval (esize a) + t) + 3,
      (seq P.code U.univ).Runs (encode a) r t' := by
  obtain ⟨t₀, ht₀, e₀⟩ := P.computes a
  obtain ⟨tu, htu, hu⟩ := U.time_le _ _ _ t h
  have hu' : U.univ.Runs (encode (P a)) r tu := hu
  refine ⟨_, ?_, seq_runs U.closed e₀ hu'⟩
  have hsz := e₀.size_le
  have hsz' : (encode (P a) : Data).size = esize (P a).1 + (encode (P a).2 : Data).size + 1 :=
    rfl
  have hU := polynomial_eval_mono U.bound
    (show esize (P a).1 + (encode (P a).2 : Data).size + t ≤ P.timeBound.eval (esize a) + t by
      omega)
  omega

/-- **It halts only if the prepared program does**, with the same output. -/
theorem seqUniv_runs_rev (a : α) {r : Data} {t : ℕ}
    (h : (seq P.code U.univ).Runs (encode a) r t) : ∃ t', (P a).1.Runs (encode (P a).2) r t' := by
  obtain ⟨t₀, -, e₀⟩ := P.computes a
  change Eval [encode a] (.let_ P.code (callVar 0 U.univ)) r t at h
  cases h with
  | let_ h₁ h₂ =>
    obtain ⟨rfl, -⟩ := Eval.deterministic h₁ e₀
    obtain ⟨t', -, hU⟩ := callVar_runs_rev U.closed h₂
    rw [Env.get_cons_zero] at hU
    have hU' : U.univ.Runs (.cons (encode (P a).1) (encode (P a).2)) r t' := hU
    exact U.halts_of _ _ _ _ hU'

end SeqUniv

namespace Halting

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ) (U : UniversalMachine)
  (UT : ClockedUniversalMachine) (Λ₀ : ℕ) (R : PolyTimeFun BitStr Prog)

/-- The tailored halting verifier the class verifier plays on `z`: `V^{R z, λ(z)}`. -/
noncomputable abbrev VTz (z : BitStr) : TailoredVerifier ℓ := VT TG U UT (R z) (lamz Λ₀ R z)

/-! ## The calculator and the processor -/

/-- The calculator's preparation: `(z, x, κ) ↦ (L^{λ(z)}, (C, x, κ))`. -/
noncomputable def lenPrep : PolyTimeFun (BitStr × BitStr × Bool) (Prog × ℕ × BitStr × Bool) :=
  pair (TG.lenProg.comp ((lamF Λ₀).comp (R.comp fst))) (pair (const (C TG)) snd)

theorem lenPrep_apply (z x : BitStr) (κ : Bool) :
    lenPrep TG Λ₀ R (z, x, κ) = ((TG.len (lamz Λ₀ R z)).prog, (C TG, x, κ)) := by
  show (TG.lenProg (lamF Λ₀ (R z)), (C TG, x, κ)) = _
  rw [lamF_apply, TG.lenProg_eq]
  rfl

/-- The processor's preparation: `(z, x, y, a^R, b^R) ↦ (LP^{R z, λ(z)}, (C, x, y, a^R, b^R))`. -/
noncomputable def lpPrep :
    PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr)
      (Prog × ℕ × BitStr × BitStr × BitStr × BitStr) :=
  pair ((lpBuild TG U UT (search TG)).comp (pair (R.comp fst) ((lamF Λ₀).comp (R.comp fst))))
    (pair (const (C TG)) snd)

theorem lpPrep_apply (z x y aR bR : BitStr) :
    lpPrep TG U UT Λ₀ R (z, x, y, aR, bR) =
      ((VTz TG U UT Λ₀ R z).lp.prog, (C TG, x, y, aR, bR)) := by
  show (lpBuild TG U UT (search TG) (R z, lamF Λ₀ (R z)), (C TG, x, y, aR, bR)) = _
  rw [lpBuild_apply, lamF_apply]
  rfl

/-! ## The costs -/

/-- The calculator's preparation time, in the total input length `m`. -/
noncomputable def lenTB (m : ℕ) : ℕ := (lenPrep TG Λ₀ R).timeBound.eval (4 * m + 7)
/-- The compressed calculator's time, in `m`. -/
noncomputable def lenSB (m : ℕ) : ℕ :=
  TG.bound.eval (C TG + lamB Λ₀ R m) * (4 * m + 6) ^ TG.deg
/-- **The class calculator's cost**, in the total input length. -/
noncomputable def lenB (m : ℕ) : ℕ :=
  2 * lenTB TG Λ₀ R m + U.bound.eval (lenTB TG Λ₀ R m + lenSB TG Λ₀ R m) + 3

/-- The polynomial of the processor's cost (`exists_lp_cost_poly`). -/
noncomputable def lpQ : Polynomial ℕ := (exists_lp_cost_poly TG U UT (search TG)).choose
/-- The degree of the processor's cost in the size of its input. -/
noncomputable def lpK : ℕ := (exists_lp_cost_poly TG U UT (search TG)).choose_spec.choose

theorem lpQ_spec (M : Prog) (lam n : ℕ) (d : Data) : ∃ r t,
    t ≤ (lpQ TG U UT).eval (n + esize M + lam) * (d.size + 1) ^ lpK TG U UT ∧
      (lpProg TG U UT (search TG) M lam).Runs (.cons (encode n) d) r t :=
  (exists_lp_cost_poly TG U UT (search TG)).choose_spec.choose_spec M lam n d

/-- The processor's preparation time, in the total input length `m`. -/
noncomputable def lpTB (m : ℕ) : ℕ := (lpPrep TG U UT Λ₀ R).timeBound.eval (4 * m + 9)
/-- The processor's time, in `m`. -/
noncomputable def lpSB (m : ℕ) : ℕ :=
  (lpQ TG U UT).eval (C TG + R.timeBound.eval (4 * m + 1) + lamB Λ₀ R m) *
    (4 * m + 8) ^ lpK TG U UT
/-- **The class processor's cost**, in the total input length. -/
noncomputable def lpB (m : ℕ) : ℕ :=
  2 * lpTB TG U UT Λ₀ R m + U.bound.eval (lpTB TG U UT Λ₀ R m + lpSB TG U UT Λ₀ R m) + 3

theorem polyBounded_lenB : PolyBounded (lenB TG U Λ₀ R) :=
  have hT : PolyBounded (lenTB TG Λ₀ R) :=
    PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 7)
  have hS : PolyBounded (lenSB TG Λ₀ R) :=
    (PolyBounded.eval _ ((PolyBounded.const (C TG)).add (polyBounded_lamB Λ₀ R))).mul
      (((PolyBounded.id.const_mul 4).add_const 6).pow TG.deg)
  ((hT.const_mul 2).add (PolyBounded.eval _ (hT.add hS))).add_const 3

theorem polyBounded_lpB : PolyBounded (lpB TG U UT Λ₀ R) :=
  have hT : PolyBounded (lpTB TG U UT Λ₀ R) :=
    PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 9)
  have hS : PolyBounded (lpSB TG U UT Λ₀ R) :=
    (PolyBounded.eval _ (((PolyBounded.const (C TG)).add
      (PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 1))).add
        (polyBounded_lamB Λ₀ R))).mul (((PolyBounded.id.const_mul 4).add_const 8).pow _)
  ((hT.const_mul 2).add (PolyBounded.eval _ (hT.add hS))).add_const 3

/-! ## The class verifier -/

/-- **The polynomial of the class verifier**: above the sampler's cost, the dimension, and the
calculator's and the processor's costs. -/
noncomputable def classTP : Polynomial ℕ :=
  (TG.samplerFamily.polyBounded_classB (C TG) U Λ₀ R).poly +
    (TG.samplerFamily.polyBounded_dimB (C TG) Λ₀ R).poly + (polyBounded_lenB TG U Λ₀ R).poly +
      (polyBounded_lpB TG U UT Λ₀ R).poly

theorem classB_le (m : ℕ) :
    TG.samplerFamily.classB (C TG) U Λ₀ R m ≤ (classTP TG U UT Λ₀ R).eval m := by
  unfold classTP; simp only [Polynomial.eval_add]
  have := (TG.samplerFamily.polyBounded_classB (C TG) U Λ₀ R).le_poly_eval m; omega

theorem dimB_le (m : ℕ) :
    TG.samplerFamily.dimB (C TG) Λ₀ R m ≤ (classTP TG U UT Λ₀ R).eval m := by
  unfold classTP; simp only [Polynomial.eval_add]
  have := (TG.samplerFamily.polyBounded_dimB (C TG) Λ₀ R).le_poly_eval m; omega

theorem lenB_le (m : ℕ) : lenB TG U Λ₀ R m ≤ (classTP TG U UT Λ₀ R).eval m := by
  unfold classTP; simp only [Polynomial.eval_add]
  have := (polyBounded_lenB TG U Λ₀ R).le_poly_eval m; omega

theorem lpB_le (m : ℕ) : lpB TG U UT Λ₀ R m ≤ (classTP TG U UT Λ₀ R).eval m := by
  unfold classTP; simp only [Polynomial.eval_add]
  have := (polyBounded_lpB TG U UT Λ₀ R).le_poly_eval m; omega

/-- **The polynomial-time tailored verifier of the language reduced to halting by `R`.** -/
noncomputable def classTV : TPolyVerifier where
  sampler := TG.samplerFamily.classSampler (C TG) U Λ₀ R
  sampler_closed := TG.samplerFamily.classSampler_wellScoped (C TG) U Λ₀ R
  len := seq (lenPrep TG Λ₀ R).code U.univ
  len_closed := seq_wellScoped (lenPrep TG Λ₀ R).closed U.closed
  lp := seq (lpPrep TG U UT Λ₀ R).code U.univ
  lp_closed := seq_wellScoped (lpPrep TG U UT Λ₀ R).closed U.closed
  bound := classTP TG U UT Λ₀ R

/-- Its sampler samples the compressed samplers at the level `C`. -/
theorem classTV_samples :
    TG.samplerFamily.Samples (C TG) Λ₀ R (classTV TG U UT Λ₀ R).toPoly :=
  TG.samplerFamily.samples_of_runs (C TG) Λ₀ R (dimB_le TG U UT Λ₀ R)
    (TG.samplerFamily.classSampler_runs (C TG) U Λ₀ R) rfl (classB_le TG U UT Λ₀ R)

/-! ## Efficiency -/

/-- The calculator halts within `lenB` of the total input length. -/
theorem len_haltsWithin (z x : BitStr) (κ : Bool) :
    HaltsWithin (classTV TG U UT Λ₀ R).len (encode (z, x, κ))
      (lenB TG U Λ₀ R (z.length + x.length)) := by
  set m := z.length + x.length with hm
  obtain ⟨r, t, ht, h⟩ := TG.len_time (lamz Λ₀ R z) (C TG) (encode (x, κ))
  have h' : (lenPrep TG Λ₀ R (z, x, κ)).1.Runs (encode (lenPrep TG Λ₀ R (z, x, κ)).2) r t := by
    rw [lenPrep_apply]; exact h
  obtain ⟨t', ht', h''⟩ := seqUniv_runs U (lenPrep TG Λ₀ R) (z, x, κ) h'
  refine ⟨r, t', ?_, h''⟩
  have hez : esize (z, x, κ) ≤ 4 * m + 7 := by
    have := esize_bitStr_le z; have := esize_bitStr_le x; have := esize_bool_le κ
    simp only [esize_prod]; omega
  have hd : (encode (x, κ) : Data).size + 1 ≤ 4 * m + 6 := by
    have := esize_bitStr_le x; have := esize_bool_le κ
    show esize (x, κ) + 1 ≤ _
    simp only [esize_prod]; omega
  have hlam : lamz Λ₀ R z ≤ lamB Λ₀ R m := lamz_le Λ₀ R z m (by omega)
  have hT : (lenPrep TG Λ₀ R).timeBound.eval (esize (z, x, κ)) ≤ lenTB TG Λ₀ R m :=
    polynomial_eval_mono _ hez
  have hS : t ≤ lenSB TG Λ₀ R m :=
    ht.trans (Nat.mul_le_mul (polynomial_eval_mono _ (by omega)) (Nat.pow_le_pow_left hd _))
  have hU := polynomial_eval_mono U.bound (Nat.add_le_add hT hS)
  unfold lenB
  omega

/-- The processor halts within `lpB` of the total input length. -/
theorem lp_haltsWithin (z x y aR bR : BitStr) :
    HaltsWithin (classTV TG U UT Λ₀ R).lp (encode (z, x, y, aR, bR))
      (lpB TG U UT Λ₀ R (z.length + x.length + y.length + aR.length + bR.length)) := by
  set m := z.length + x.length + y.length + aR.length + bR.length with hm
  obtain ⟨r, t, ht, h⟩ := lpQ_spec TG U UT (R z) (lamz Λ₀ R z) (C TG) (encode (x, y, aR, bR))
  have h' : (lpPrep TG U UT Λ₀ R (z, x, y, aR, bR)).1.Runs
      (encode (lpPrep TG U UT Λ₀ R (z, x, y, aR, bR)).2) r t := by
    rw [lpPrep_apply]; exact h
  obtain ⟨t', ht', h''⟩ := seqUniv_runs U (lpPrep TG U UT Λ₀ R) (z, x, y, aR, bR) h'
  refine ⟨r, t', ?_, h''⟩
  have hez : esize (z, x, y, aR, bR) ≤ 4 * m + 9 := by
    have := esize_bitStr_le z; have := esize_bitStr_le x; have := esize_bitStr_le y
    have := esize_bitStr_le aR; have := esize_bitStr_le bR
    simp only [esize_prod]; omega
  have hd : (encode (x, y, aR, bR) : Data).size + 1 ≤ 4 * m + 8 := by
    have := esize_bitStr_le x; have := esize_bitStr_le y
    have := esize_bitStr_le aR; have := esize_bitStr_le bR
    show esize (x, y, aR, bR) + 1 ≤ _
    simp only [esize_prod]; omega
  have hM : esize (R z) ≤ R.timeBound.eval (4 * m + 1) :=
    (R.esize_apply_le z).trans (polynomial_eval_mono _ (by have := esize_bitStr_le z; omega))
  have hlam : lamz Λ₀ R z ≤ lamB Λ₀ R m := lamz_le Λ₀ R z m (by omega)
  have hT : (lpPrep TG U UT Λ₀ R).timeBound.eval (esize (z, x, y, aR, bR)) ≤
      lpTB TG U UT Λ₀ R m :=
    polynomial_eval_mono _ hez
  have hS : t ≤ lpSB TG U UT Λ₀ R m :=
    ht.trans (Nat.mul_le_mul (polynomial_eval_mono _ (by omega)) (Nat.pow_le_pow_left hd _))
  have hU := polynomial_eval_mono U.bound (Nat.add_le_add hT hS)
  unfold lpB
  omega

/-- **The class verifier is efficient on every input.** -/
theorem classTV_efficient (z : BitStr) : (classTV TG U UT Λ₀ R).Efficient z where
  sampler_runs := (classTV_samples TG U UT Λ₀ R).samplerRuns (dimB_le TG U UT Λ₀ R) z
  len_time x κ :=
    let ⟨r, t, ht, h⟩ := len_haltsWithin TG U UT Λ₀ R z x κ
    ⟨r, t, ht.trans (lenB_le TG U UT Λ₀ R _), h⟩
  lp_time x y aR bR :=
    let ⟨r, t, ht, h⟩ := lp_haltsWithin TG U UT Λ₀ R z x y aR bR
    ⟨r, t, ht.trans (lpB_le TG U UT Λ₀ R _), h⟩

/-! ## The outputs are those of the halting verifier -/

/-- The class calculator outputs what the compressed calculator outputs at the level `C`. -/
theorem lenIs_iff (z x : BitStr) (κ : Bool) (k : ℕ) :
    (classTV TG U UT Λ₀ R).LenIs z x κ k ↔ LenIs (VTz TG U UT Λ₀ R z).len (C TG) x κ k := by
  constructor
  · rintro ⟨t, d, h, hk⟩
    obtain ⟨t', h'⟩ := seqUniv_runs_rev U (lenPrep TG Λ₀ R) (z, x, κ) h
    rw [lenPrep_apply] at h'
    exact ⟨t', d, h', hk⟩
  · rintro ⟨t, d, h, hk⟩
    have h' : (lenPrep TG Λ₀ R (z, x, κ)).1.Runs (encode (lenPrep TG Λ₀ R (z, x, κ)).2) d t := by
      rw [lenPrep_apply]; exact h
    obtain ⟨t', -, h''⟩ := seqUniv_runs U (lenPrep TG Λ₀ R) (z, x, κ) h'
    exact ⟨t', d, h'', hk⟩

/-- The class processor outputs what the processor of `V^{R z, λ(z)}` outputs at the level `C`. -/
theorem lpIs_iff (z x y aR bR : BitStr) (cs : List BitStr) :
    (classTV TG U UT Λ₀ R).LpIs z x y aR bR cs ↔
      LpIs (VTz TG U UT Λ₀ R z).lp (C TG) x y aR bR cs := by
  constructor
  · rintro ⟨t, d, h, hk⟩
    obtain ⟨t', h'⟩ := seqUniv_runs_rev U (lpPrep TG U UT Λ₀ R) (z, x, y, aR, bR) h
    rw [lpPrep_apply] at h'
    exact ⟨t', d, h', hk⟩
  · rintro ⟨t, d, h, hk⟩
    have h' : (lpPrep TG U UT Λ₀ R (z, x, y, aR, bR)).1.Runs
        (encode (lpPrep TG U UT Λ₀ R (z, x, y, aR, bR)).2) d t := by
      rw [lpPrep_apply]; exact h
    obtain ⟨t', -, h''⟩ := seqUniv_runs U (lpPrep TG U UT Λ₀ R) (z, x, y, aR, bR) h'
    exact ⟨t', d, h'', hk⟩

theorem lenOf_eq (z x : BitStr) (κ : Bool) :
    (classTV TG U UT Λ₀ R).lenOf z x κ = (VTz TG U UT Λ₀ R z).lenOf (C TG) x κ := by
  unfold TPolyVerifier.lenOf TailoredVerifier.lenOf
  by_cases h : ∃ k, (classTV TG U UT Λ₀ R).LenIs z x κ k
  · have h' : ∃ k, LenIs (VTz TG U UT Λ₀ R z).len (C TG) x κ k :=
      ⟨h.choose, (lenIs_iff TG U UT Λ₀ R z x κ _).1 h.choose_spec⟩
    rw [dite_eq_left h, dite_eq_left h']
    exact ((lenIs_iff TG U UT Λ₀ R z x κ _).1 h.choose_spec).unique h'.choose_spec
  · have h' : ¬ ∃ k, LenIs (VTz TG U UT Λ₀ R z).len (C TG) x κ k :=
      fun ⟨k, hk⟩ => h ⟨k, (lenIs_iff TG U UT Λ₀ R z x κ k).2 hk⟩
    rw [dite_eq_right h, dite_eq_right h']

theorem lenDefined_iff (z x : BitStr) :
    (classTV TG U UT Λ₀ R).LenDefined z x ↔ (VTz TG U UT Λ₀ R z).LenDefined (C TG) x :=
  forall_congr' fun κ => exists_congr fun k => lenIs_iff TG U UT Λ₀ R z x κ k

theorem consOf_eq (z x y aR bR : BitStr) :
    (classTV TG U UT Λ₀ R).consOf z x y aR bR = (VTz TG U UT Λ₀ R z).consOf (C TG) x y aR bR := by
  by_cases h : (classTV TG U UT Λ₀ R).LenDefined z x ∧ (classTV TG U UT Λ₀ R).LenDefined z y ∧
      ∃ cs, (classTV TG U UT Λ₀ R).LpIs z x y aR bR cs
  · obtain ⟨hx, hy, cs, hcs⟩ := h
    rw [TPolyVerifier.consOf_eq _ hx hy hcs, TailoredVerifier.consOf_eq_of _
      ((lenDefined_iff TG U UT Λ₀ R z x).1 hx) ((lenDefined_iff TG U UT Λ₀ R z y).1 hy)
      ((lpIs_iff TG U UT Λ₀ R z x y aR bR cs).1 hcs)]
  · have h' : ¬ ((VTz TG U UT Λ₀ R z).LenDefined (C TG) x ∧
        (VTz TG U UT Λ₀ R z).LenDefined (C TG) y ∧
          ∃ cs, LpIs (VTz TG U UT Λ₀ R z).lp (C TG) x y aR bR cs) :=
      fun ⟨hx, hy, cs, hcs⟩ => h ⟨(lenDefined_iff TG U UT Λ₀ R z x).2 hx,
        (lenDefined_iff TG U UT Λ₀ R z y).2 hy, cs, (lpIs_iff TG U UT Λ₀ R z x y aR bR cs).2 hcs⟩
    unfold TPolyVerifier.consOf TailoredVerifier.consOf
    rw [dite_eq_right h, dite_eq_right h', lenOf_eq, lenOf_eq, lenOf_eq, lenOf_eq]

/-! ## The game -/

/-- **The class verifier's game extends that of `V^{R z, λ(z)}` at the level `C`**, along the
embedding of the questions as bit strings. -/
theorem tgame_extends (z : BitStr) :
    ((classTV TG U UT Λ₀ R).tgame z).Extends ((VTz TG U UT Λ₀ R z).tgame (C TG))
      (TG.samplerFamily.qEmb (C TG) Λ₀ R (dimB_le TG U UT Λ₀ R) z) where
  μ_eq x y :=
    TG.samplerFamily.game_μ_qEmb (C TG) Λ₀ R (classTV_samples TG U UT Λ₀ R)
      (dimB_le TG U UT Λ₀ R) z x y
  support :=
    TG.samplerFamily.game_support (C TG) Λ₀ R (classTV_samples TG U UT Λ₀ R)
      (dimB_le TG U UT Λ₀ R) z
  lenR_eq x := lenOf_eq TG U UT Λ₀ R z (CL.toBits x) false
  lenL_eq x := lenOf_eq TG U UT Λ₀ R z (CL.toBits x) true
  cons_eq x y := funext fun aR => funext fun bR =>
    consOf_eq TG U UT Λ₀ R z (CL.toBits x) (CL.toBits y) aR bR

/-- **The value of the class verifier's game** is that of `V^{R z, λ(z)}` at the level `C`. -/
theorem classTV_valStar (z : BitStr) :
    ((classTV TG U UT Λ₀ R).tgame z).valStar = (VTz TG U UT Λ₀ R z).valStar (C TG) :=
  (tgame_extends TG U UT Λ₀ R z).valStar_eq

/-- **A perfect ZPC strategy of `V^{R z, λ(z)}` at the level `C` is one of the class verifier's
game**, on the doubled games. -/
theorem classTV_hasPerfectZPC (z : BitStr) (h : (VTz TG U UT Λ₀ R z).HasPerfectZPC (C TG)) :
    ((classTV TG U UT Λ₀ R).tgame z).doubled.HasPerfectZPC :=
  (tgame_extends TG U UT Λ₀ R z).doubled.hasPerfectZPC h

/-- **The values on and off the language**, at the threshold `Λ₀` of `lem:lambda`. -/
theorem classTV_values (z : BitStr) :
    (Halts (R z) .nil →
      ((classTV TG U UT (lamThreshold TG U UT) R).tgame z).doubled.HasPerfectZPC) ∧
    (¬ Halts (R z) .nil →
      ((classTV TG U UT (lamThreshold TG U UT) R).tgame z).valStar ≤ 1 / 2) := by
  obtain ⟨h1, h2⟩ :=
    halting_tailored_search TG U UT (R z) (lamz (lamThreshold TG U UT) R z) le_rfl
  exact ⟨fun hM => classTV_hasPerfectZPC TG U UT _ R z (h1 hM),
    fun hM => (classTV_valStar TG U UT _ R z).trans_le (h2 hM)⟩

end Halting

/-! ## `RE ⊆ TMIP*`, and `TMIP* = RE` -/

variable {ℓ : ℕ}

/-- **`RE ⊆ TMIP*`** for the polynomial-time class, from a tailored gap compression. -/
theorem re_subset_tmipStar_of (TG : TailoredGapCompression ℓ) {L : Set BitStr} (hL : IsRE L) :
    TMIPStar L := by
  obtain ⟨U⟩ := exists_efficient_universal
  obtain ⟨UT⟩ := exists_clocked_universal
  obtain ⟨R, -, hR⟩ := Cost.exists_polyTime_reduction (p := (· ∈ L)) hL
  refine ⟨Halting.classTV TG U UT (Halting.lamThreshold TG U UT) R,
    Halting.classTV_efficient TG U UT _ R, fun z => ?_⟩
  obtain ⟨h1, h2⟩ := Halting.classTV_values TG U UT R z
  exact ⟨fun hz => h1 ((hR z).2 hz), fun hz => h2 fun h => hz ((hR z).1 h)⟩

/-- **`TMIP* = RE`** (II:787, `thm:tailored_MIP*=RE`), for the paper's polynomial-time class,
from a tailored gap compression. -/
theorem tmipStar_eq_re_of (TG : TailoredGapCompression ℓ) : TMIPStar = IsRE :=
  funext fun _ => propext ⟨TMIPStar.isRE, re_subset_tmipStar_of TG⟩

end MIPRE.Tailored

end
