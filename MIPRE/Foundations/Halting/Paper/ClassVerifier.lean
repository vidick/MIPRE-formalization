/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Paper.Main
public import MIPRE.Foundations.Halting.Paper.ClassSampler

@[expose] public section

/-!
# The class verifier of the polynomial-time halting reduction

The two programs of the `PolyVerifier` (`def:mipstar`) that puts an r.e. language `L` in the
paper's class `MIP*_{1,1/2}(2,1)`, for a polynomial-time reduction `R` of `L` to halting on the
empty input (`Cost.exists_polyTime_reduction`): on input `z` they play the game of
`𝒱^halt (R z) λ(z)` at the fixed level `C` (`Paper/Main.lean`), with
`λ(z) = Λ₀ + 4|R z|` the parameter of `lem:lambda`.

* **The sampler** `sampProg`, on `(z, r)`, is the class sampler of `Paper/ClassSampler.lean`
  for the compressed samplers (`GapCompression.samplerFamily`) at the fixed level `C`: it
  computes `M = R z`, `λ(z)` and the compressed sampler's program `S = ComputeSampler(λ(z))`;
  asks `S` its dimension `s = s(C)` through the universal machine; takes the first `s` bits `r'`
  of the seed and asks `S` the two marginals at `r'`. Its output is the question pair of
  `𝒱^halt` at the point `r'` (`sampProg_runs`), so that the uniform seed of length `B ≥ s`
  pushes forward to the compressed sampler's distribution.
* **The decider** `decProg`, on `(z, x, y, a, b)`: computes `M`, `λ(z)` and the description of
  `𝒱^halt`'s decider (`wrapCore` around `dec M λ(z)`, `decBuild`), rejects if `a` or `b` is
  longer than the cutoff `2 ^ (K + deg · |λ(z)|)` (`cutF`, at least the compressor's answer
  bound `poly(C, λ(z))` by `exists_cut_ge`), and otherwise runs the description on
  `(C, x, y, a, b)` through the universal machine. It accepts exactly when both
  answers are within the cutoff and `𝒱^halt`'s decider accepts (`decProg_accepts`).

The costs are bounded by explicit expressions in the total input length (`sampB`, `decB`),
polynomially bounded (`polyBounded_sampB`, `polyBounded_decB`); `Paper/ClassMain.lean` chooses
the verifier's polynomial above them and proves the game's value.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun CL

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)

/-! ## The sampler -/

/-- The compressed sampler of the input `z`. -/
noncomputable abbrev Sz (z : BitStr) : Sampler 7 := G.sampler (lamz Λ₀ R z)

/-- The dimension of its questions at the fixed level. -/
noncomputable abbrev dimz (z : BitStr) : ℕ := G.samplerFamily.dimz (C G) Λ₀ R z

/-- Player `w`'s question on the seed `r`, on the input `z`: the marginal of the compressed
sampler at the first `dimz z` bits of `r`. -/
noncomputable abbrev qOf (w : Player) (z r : BitStr) : BitStr :=
  G.samplerFamily.qOf (C G) Λ₀ R w z r

/-- **The sampler of the class verifier**: the class sampler of `Paper/ClassSampler.lean` for
the compressed samplers at the fixed level `C`. -/
noncomputable abbrev sampProg : Prog := G.samplerFamily.sampProg (C G) U Λ₀ R

theorem sampProg_wellScoped : (sampProg G U Λ₀ R).WellScoped 1 :=
  G.samplerFamily.sampProg_wellScoped (C G) U Λ₀ R

/-- The compressor's bound `poly(C, λ)`, in the total input length `m`: bounds the dimension
and the times. -/
noncomputable abbrev dimB (m : ℕ) : ℕ := G.samplerFamily.dimB (C G) Λ₀ R m

/-- **The sampler's cost**, in the total input length. -/
noncomputable abbrev sampB (m : ℕ) : ℕ := G.samplerFamily.sampB (C G) U Λ₀ R m

theorem dimz_le (z : BitStr) (m : ℕ) (hm : z.length ≤ m) :
    dimz G Λ₀ R z ≤ dimB G Λ₀ R m :=
  G.samplerFamily.dimz_le (C G) Λ₀ R z m hm

/-- **The sampler's run**: on `(z, r)` with `r` at least `dimz z` long, it halts with the
question pair of the seed within `sampB (|z| + |r|)`. -/
theorem sampProg_runs (z r : BitStr) (hd : dimz G Λ₀ R z ≤ r.length) :
    ∃ t, t ≤ sampB G U Λ₀ R (z.length + r.length) ∧
      (sampProg G U Λ₀ R).Runs (encode (z, r))
        (encode (qOf G Λ₀ R .alice z r, qOf G Λ₀ R .bob z r)) t :=
  G.samplerFamily.sampProg_runs (C G) U Λ₀ R (by norm_num) z r hd

/-! ## The decider -/

/-- `q ↦ R z` on the decider's input `q = (z, x, y, a, b)`. -/
noncomputable def MzF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) Prog :=
  R.comp fst

/-- `q ↦ λ(z)`. -/
noncomputable def lamzF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) ℕ :=
  (lamF Λ₀).comp (MzF R)

/-- The cutoff on the input `z`: `2 ^ (K + deg · |λ(z)|)`. -/
def cutz (z : BitStr) : ℕ := 2 ^ (K + G.bound.natDegree * esize (lamz Λ₀ R z))

/-- `q ↦ cutz z`. -/
noncomputable def cutzF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) ℕ :=
  (cutF K G.bound.natDegree).comp (lamzF Λ₀ R)

/-- `q ↦ a`. -/
noncomputable def aF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) BitStr :=
  fst.comp (snd.comp (snd.comp snd))

/-- `q ↦ b`. -/
noncomputable def bF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) BitStr :=
  snd.comp (snd.comp (snd.comp snd))

/-- `q ↦ wrapCore univ (ComputeSampler λ(z)) (dec (R z) λ(z))`, the decider of `𝒱^halt`. -/
noncomputable def wF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) Prog :=
  (wrapPoly G U).comp (pair (lamzF Λ₀ R)
    ((decBuild G U UT (semL G U)).comp (pair (MzF R) (lamzF Λ₀ R))))

/-- The decider of `𝒱^halt (R z) λ(z)`, wrapped. -/
noncomputable def wdec (z : BitStr) : Prog := (Vpaper G U UT (R z) (lamz Λ₀ R z)).decider.prog

theorem wF_apply (z x y a b : BitStr) :
    wF G U UT Λ₀ R (z, x, y, a, b) = wdec G U UT Λ₀ R z := by
  show wrapPoly G U (lamF Λ₀ (R z), decBuild G U UT (semL G U) (R z, lamF Λ₀ (R z))) = _
  rw [wrapPoly_apply, decBuild_apply, lamF_apply]
  rfl

/-- `q ↦ encode (C, x, y, a, b)`, the decider's input at the fixed level. -/
noncomputable def inputF : PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) Data :=
  cast (pair (const (C G)) (pair (fst.comp snd) (pair (fst.comp (snd.comp snd)) (pair aF bF))))
    (fun q => encode (C G, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) (fun _ => rfl)

/-- The rejecting branch: the constant-`false` program on the empty input. -/
noncomputable def rejF :
    PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) (Prog × Data) :=
  const (falseProg, Data.nil)

/-- **The preparation of the class decider**: the program to run and its input — the
constant-`false` program if `a` or `b` exceeds the cutoff, else `𝒱^halt`'s decider on
`(C, x, y, a, b)`. -/
noncomputable def D1 :
    PolyTimeFun (BitStr × BitStr × BitStr × BitStr × BitStr) (Prog × Data) :=
  ite (leNat.comp (pair (lenBin.comp aF) (cutzF G Λ₀ K R)))
    (ite (leNat.comp (pair (lenBin.comp bF) (cutzF G Λ₀ K R)))
      (pair (wF G U UT Λ₀ R) (inputF G)) rejF)
    rejF

theorem D1_apply (z x y a b : BitStr) :
    D1 G U UT Λ₀ K R (z, x, y, a, b) =
      if a.length ≤ cutz G Λ₀ K R z then
        (if b.length ≤ cutz G Λ₀ K R z then (wdec G U UT Λ₀ R z, encode (C G, x, y, a, b))
          else (falseProg, Data.nil))
      else (falseProg, Data.nil) := by
  have hc : cutzF G Λ₀ K R (z, x, y, a, b) = cutz G Λ₀ K R z := by
    show cutF K G.bound.natDegree (lamF Λ₀ (R z)) = _
    rw [cutF_apply, lamF_apply]
    rfl
  have ha : lenBin (aF (z, x, y, a, b)) = a.length := lenBin_apply _
  have hb : lenBin (bF (z, x, y, a, b)) = b.length := lenBin_apply _
  show (if decide (lenBin (aF (z, x, y, a, b)) ≤ cutzF G Λ₀ K R (z, x, y, a, b)) = true then
      (if decide (lenBin (bF (z, x, y, a, b)) ≤ cutzF G Λ₀ K R (z, x, y, a, b)) = true then
        (wF G U UT Λ₀ R (z, x, y, a, b), inputF G (z, x, y, a, b)) else (falseProg, Data.nil))
      else (falseProg, Data.nil)) = _
  rw [hc, ha, hb, wF_apply]
  simp only [decide_eq_true_eq]
  rfl

/-- **The decider of the class verifier**: the preparation, then the universal machine. -/
noncomputable def decProg : Prog := seq (D1 G U UT Λ₀ K R).code U.univ

theorem decProg_wellScoped : (decProg G U UT Λ₀ K R).WellScoped 1 :=
  seq_wellScoped (D1 G U UT Λ₀ K R).closed U.closed

/-- **Acceptance of the class decider**: both answers within the cutoff, and `𝒱^halt`'s
decider accepts at the fixed level. -/
theorem decProg_accepts (z x y a b : BitStr) :
    (∃ t, (decProg G U UT Λ₀ K R).Runs (encode (z, x, y, a, b)) (encode true) t) ↔
      a.length ≤ cutz G Λ₀ K R z ∧ b.length ≤ cutz G Λ₀ K R z ∧
        (Vpaper G U UT (R z) (lamz Λ₀ R z)).decider.Accepts (C G) x y a b := by
  obtain ⟨t₀, -, e₀⟩ := (D1 G U UT Λ₀ K R).computes (z, x, y, a, b)
  rw [D1_apply] at e₀
  constructor
  · rintro ⟨t, h⟩
    change Eval [encode (z, x, y, a, b)] (.let_ _ _) (encode true) t at h
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨rfl, -⟩ := Eval.deterministic h₁ e₀
      obtain ⟨t', -, hU⟩ := callVar_runs_rev U.closed h₂
      rw [Env.get_cons_zero] at hU
      have hrej : ∀ t', ¬ U.univ.Runs (encode (falseProg, Data.nil)) (encode true) t' := by
        intro t' hU'
        have hU'' : U.univ.Runs (.cons (encode falseProg) Data.nil) (encode true) t' := hU'
        obtain ⟨t'', h''⟩ := U.halts_of _ _ _ _ hU''
        obtain ⟨he, -⟩ := Eval.deterministic h'' (Eval.const [Data.nil] (encode false))
        simp [encode_bool, Data.ofBool] at he
      split_ifs at hU with ha hb
      · have hU' : U.univ.Runs (.cons (encode (wdec G U UT Λ₀ R z)) (encode (C G, x, y, a, b)))
            (encode true) t' := hU
        obtain ⟨t'', h''⟩ := U.halts_of _ _ _ _ hU'
        exact ⟨ha, hb, t'', h''⟩
      · exact (hrej t' hU).elim
      · exact (hrej t' hU).elim
  · rintro ⟨ha, hb, t, h⟩
    rw [if_pos ha, if_pos hb] at e₀
    obtain ⟨t', -, hU⟩ := U.time_le _ _ _ t h
    have hU' : U.univ.Runs (encode (wdec G U UT Λ₀ R z, encode (C G, x, y, a, b)))
      (encode true) t' := hU
    exact ⟨_, seq_runs U.closed e₀ hU'⟩

/-- The preparation's cost, in the total input length. -/
noncomputable def TDB (m : ℕ) : ℕ := (D1 G U UT Λ₀ K R).timeBound.eval (4 * m + 9)
/-- A common bound on the atoms of the wrapped decider's cost, in `m`. -/
noncomputable def zB (m : ℕ) : ℕ :=
  R.timeBound.eval (4 * m + 1) + C G + lamB Λ₀ R m + (4 * m + 7)
/-- **The class decider's cost**, in the total input length. -/
noncomputable def decB (m : ℕ) : ℕ :=
  3 * TDB G U UT Λ₀ K R m +
    U.bound.eval (TDB G U UT Λ₀ K R m + (WZ G U UT (semL G U) (zB G Λ₀ R m) + constCost)) + 6

/-- **The class decider halts on every input** within `decB (|z| + |x| + |y| + |a| + |b|)`. -/
theorem decProg_runs (z x y a b : BitStr) :
    ∃ r t, t ≤ decB G U UT Λ₀ K R (z.length + x.length + y.length + a.length + b.length) ∧
      (decProg G U UT Λ₀ K R).Runs (encode (z, x, y, a, b)) r t := by
  set m := z.length + x.length + y.length + a.length + b.length with hm
  obtain ⟨t₀, ht₀, e₀⟩ := (D1 G U UT Λ₀ K R).computes (z, x, y, a, b)
  rw [D1_apply] at e₀
  have hT : t₀ ≤ TDB G U UT Λ₀ K R m := by
    refine ht₀.trans (polynomial_eval_mono _ ?_)
    have := esize_bitStr_le z; have := esize_bitStr_le x; have := esize_bitStr_le y
    have := esize_bitStr_le a; have := esize_bitStr_le b
    simp only [esize_prod]; omega
  -- the atoms of the wrapped decider's cost
  have hzB1 : esize (R z) ≤ zB G Λ₀ R m := by
    have h1 := R.esize_apply_le z
    have h2 := esize_bitStr_le z
    have h3 := polynomial_eval_mono R.timeBound (show esize z ≤ 4 * m + 1 by omega)
    unfold zB; omega
  have hzB2 : C G ≤ zB G Λ₀ R m := by unfold zB; omega
  have hzB3 : lamz Λ₀ R z ≤ zB G Λ₀ R m := by
    have := lamz_le Λ₀ R z m (by omega)
    unfold zB; omega
  have hzB4 : (encode (x, y, a, b) : Data).size ≤ zB G Λ₀ R m := by
    have := esize_bitStr_le x; have := esize_bitStr_le y
    have := esize_bitStr_le a; have := esize_bitStr_le b
    have e : (encode (x, y, a, b) : Data).size =
      esize x + (esize y + (esize a + esize b + 1) + 1) + 1 := rfl
    unfold zB; omega
  -- the rejecting branch
  have hrej : (D1 G U UT Λ₀ K R).code.Runs (encode (z, x, y, a, b))
      (encode (falseProg, Data.nil)) t₀ → ∃ r t, t ≤ decB G U UT Λ₀ K R m ∧
        (decProg G U UT Λ₀ K R).Runs (encode (z, x, y, a, b)) r t := by
    intro e₁
    have hsz := e₁.size_le
    obtain ⟨tu, htu, hu⟩ := U.time_le falseProg Data.nil (encode false) _
      (Eval.const [Data.nil] (encode false))
    have hu' : U.univ.Runs (encode (falseProg, Data.nil)) (encode false) tu := hu
    refine ⟨encode false, _, ?_, seq_runs U.closed e₁ hu'⟩
    have hsz' : (encode (falseProg, Data.nil) : Data).size = esize falseProg + 1 + 1 := rfl
    have hcc : (encode false : Data).size ≤ constCost := by unfold constCost; omega
    have hu2 := htu.trans (polynomial_eval_mono U.bound
      (show esize falseProg + Data.nil.size + (encode false : Data).size ≤
        TDB G U UT Λ₀ K R m + (WZ G U UT (semL G U) (zB G Λ₀ R m) + constCost) by
          simp only [Data.size_nil]; omega))
    unfold decB; omega
  split_ifs at e₀ with ha hb
  · -- the wrapped decider, through the universal machine
    have hy := e₀.size_le
    obtain ⟨r, tc, htc, hc⟩ := Vhalt_decider_cost G U UT (semL G U) (R z) (lamz Λ₀ R z) (C G)
      (encode (x, y, a, b))
    have hW := htc.trans (wrapCoreCost_le_WZ G U UT (semL G U) (R z) hzB1 hzB2 hzB3 hzB4)
    have hc' : (wdec G U UT Λ₀ R z).Runs (encode (C G, x, y, a, b)) r tc := hc
    obtain ⟨tu, htu, hu⟩ := U.time_le _ _ _ tc hc'
    have hu' : U.univ.Runs (encode (wdec G U UT Λ₀ R z, encode (C G, x, y, a, b))) r tu := hu
    refine ⟨r, _, ?_, seq_runs U.closed e₀ hu'⟩
    have hsz : (encode (wdec G U UT Λ₀ R z, encode (C G, x, y, a, b)) : Data).size =
      esize (wdec G U UT Λ₀ R z) + (encode (C G, x, y, a, b) : Data).size + 1 := rfl
    have hu2 := htu.trans (polynomial_eval_mono U.bound
      (show esize (wdec G U UT Λ₀ R z) + (encode (C G, x, y, a, b) : Data).size + tc ≤
        TDB G U UT Λ₀ K R m + (WZ G U UT (semL G U) (zB G Λ₀ R m) + constCost) by omega))
    unfold decB; omega
  · exact hrej e₀
  · exact hrej e₀

end MIPRE.Halting

end
