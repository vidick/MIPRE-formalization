/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Halting.Induction
public import MIPRE.Foundations.Halting.Paper.Cost

@[expose] public section

/-!
# The tailored halting verifier: the accounting

Paper II, `lem:lambda` (II:2002), for the three programs of a tailored verifier, along the route
of `MIPRE/Foundations/Halting/Paper/{Size,Cost}.lean`, which this file parallels: the verifier
`Vhalt M λ` is `λ`-bounded (`TailoredVerifier.IsBounded λ`) as soon as `λ ≥ Λ₀ + 4|M|`, for a
threshold `Λ₀` depending on the compression, the universal machines and the search program
alone (`exists_lamBound`, `Lam0`).

* **Sizes** (`esize_lpProg`): the processor `lp M λ` is a hardcoding of the fixed point's
  program to its own description, so its size is `2 (|M| + |λ|)` plus a constant — the reason
  the parameter is `Λ₀ + 4|M|`.
* **The processor's run** (`lp_cost`): on `(n, d)`, `lp M λ` runs within `lpRunZ z |d|` at
  `z = n + |M| + λ`, assembled along the fixed point's time transfer
  (`Cost.kleeneFix_runs_of`), the hardcoding of the description, the run of `prep`, the
  universal machine on what `prep` returns, and the compressed processor's own time
  (`TailoredGapCompression.lp_time`). The existing halting verifier then wraps its decider in
  the question-length check; a processor is run as it is, so there is no wrapper layer here.
* **The clauses** of `IsBounded λ`, each absorbed past a threshold (`PolyBounded.absorb`,
  `PolyBounded.absorb_log`): the sampler's dimension and time and the answer-length
  calculator's time and lengths, all from the compression's `poly(n, λ)`; the processor's time;
  and the size.
-/

namespace MIPRE.Tailored.Halting

open Cost Cost.Prog Polynomial
open MIPRE.Halting (muZ vZ polyBounded_muZ polyCost_vZ polyCost_pow_size esize_nat_le_self
  size_descData)

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ) (U : UniversalMachine)
  (UT : ClockedUniversalMachine)

/-! ## Sizes -/

/-- The size of the code of `F` beyond `|M| + |λ|`. -/
noncomputable def cF (S' : Prog) : ℕ := esize (body TG U UT S') + esize smnProg + 77

theorem esize_F_code (S' M : Prog) (lam : ℕ) :
    esize (F TG U UT S' M lam).code = esize M + esize lam + cF TG U UT S' := by
  simp only [F, PolyTimeFun.comp, PolyTimeFun.pair, PolyTimeFun.const, PolyTimeFun.id,
    PolyTimeFun.smn, esize_eq_size_toData, toData, Data.size_cons, Data.size_ofNat]
  have h1 : M.toData.size = esize M := rfl
  have h1' : (encode M : Data).size = esize M := rfl
  have h2 : (encode lam : Data).size = esize lam := rfl
  have h3 : (body TG U UT S').toData.size = esize (body TG U UT S') := rfl
  have h3' : (encode (body TG U UT S') : Data).size = esize (body TG U UT S') := rfl
  have h4 : smnProg.toData.size = esize smnProg := rfl
  unfold cF
  omega

/-- The size of `kleeneProg U.univ F` beyond `|M| + |λ|`. -/
noncomputable def cK (S' : Prog) : ℕ := cF TG U UT S' + esize U.univ + esize smnProg + 136

theorem esize_kleeneProg_F (S' M : Prog) (lam : ℕ) :
    esize (kleeneProg U.univ (F TG U UT S' M lam)) = esize M + esize lam + cK TG U UT S' := by
  have h0 := esize_F_code TG U UT S' M lam
  simp only [kleeneProg, callVar, esize_eq_size_toData, toData, Data.size_cons,
    Data.size_ofNat, Data.size_nil] at h0 ⊢
  have h1 : U.univ.toData.size = esize U.univ := rfl
  have h2 : smnProg.toData.size = esize smnProg := rfl
  have h3 : M.toData.size = esize M := rfl
  unfold cK
  omega

/-- The size of the processor `lp M λ` beyond `2 (|M| + |λ|)`. -/
noncomputable def cD (S' : Prog) : ℕ := 2 * cK TG U UT S' + 35

theorem esize_lpProg (S' M : Prog) (lam : ℕ) :
    esize (lpProg TG U UT S' M lam) = 2 * (esize M + esize lam) + cD TG U UT S' := by
  rw [lpProg, kleeneFix, hardcode_size]
  have h1 : (encode (kleeneProg U.univ (F TG U UT S' M lam)) : Data).size =
    esize (kleeneProg U.univ (F TG U UT S' M lam)) := rfl
  rw [h1, esize_kleeneProg_F, cD]
  omega

/-- `F e = hardcode body (M, (λ, e))` has size `|body| + |M| + |λ| + |e| + 37`. -/
theorem esize_F_apply (S' M : Prog) (lam : ℕ) (e : Prog) :
    esize (F TG U UT S' M lam e) =
      esize (body TG U UT S') + esize M + esize lam + esize e + 37 := by
  rw [F_apply, hardcode_size, size_descData]
  omega

/-- The time bound of `F`: affine in the argument and in `|body| + |M| + |λ|`. -/
theorem F_timeBound_eval (S' M : Prog) (lam x : ℕ) :
    (F TG U UT S' M lam).timeBound.eval x =
      2 * (esize (body TG U UT S') + esize M + esize lam + x) + 47 := by
  simp only [F, PolyTimeFun.comp, PolyTimeFun.pair, PolyTimeFun.const, PolyTimeFun.id,
    PolyTimeFun.smn, eval_add, eval_comp, eval_X, eval_C, eval_one]
  omega

/-- The overhead of the fixed point's time transfer beyond `21 (|M| + |λ|)`. -/
noncomputable def cO (S' : Prog) : ℕ :=
  7 * cK TG U UT S' + 5 * cD TG U UT S' + 4 * esize (body TG U UT S') + 181

theorem kleeneOverhead_eq (S' M : Prog) (lam : ℕ) :
    kleeneOverhead U (F TG U UT S' M lam) = 21 * (esize M + esize lam) + cO TG U UT S' := by
  have h1 := esize_kleeneProg_F TG U UT S' M lam
  have h2 := esize_lpProg TG U UT S' M lam
  have h3 := esize_F_apply TG U UT S' M lam (lpProg TG U UT S' M lam)
  have h4 := F_timeBound_eval TG U UT S' M lam (esize (lpProg TG U UT S' M lam))
  rw [kleeneOverhead]
  change 7 * esize (kleeneProg U.univ (F TG U UT S' M lam)) + esize (lpProg TG U UT S' M lam) +
    (F TG U UT S' M lam).timeBound.eval (esize (lpProg TG U UT S' M lam)) +
    2 * esize (F TG U UT S' M lam (lpProg TG U UT S' M lam)) + 60 = _
  rw [h1, h4, h3, h2, cO]
  omega

/-! ## What `prep` returns -/

/-- The cost of the two constant programs: the sizes of the two constant outputs. -/
def constCost : ℕ := (encode ([] : List BitStr) : Data).size + (encode [rejectConstraint 0]).size

/-- The size of the program `prep` returns, at the parameter `λ` and the processor `e`: the
compressed processor's, from `compress`'s time bound at the size of its input. -/
noncomputable def progSize (lam : ℕ) (e : Prog) : ℕ :=
  TG.compress.timeBound.eval (TG.samplerProg.timeBound.eval (esize lam) +
    TG.lenProg.timeBound.eval (esize lam) + esize e + esize lam + 3) +
    esize acceptProg + esize rejectProg

/-- **What `prep` returns, on the description `(M, (λ, e))` and the input `(n, d)`**: a program
of size at most `progSize λ e`, an input of size at most `|n| + |d| + 1`, and the program runs
on the input within the compressed processor's time plus a constant. -/
theorem prep_output (S' M : Prog) (lam : ℕ) (e : Prog) (n : ℕ) (d : Data) :
    esize (prep TG UT S' ((M, (lam, e)), (n, d))).1 ≤ progSize TG lam e ∧
    (prep TG UT S' ((M, (lam, e)), (n, d))).2.size ≤ esize n + d.size + 1 ∧
    ∃ r t, t ≤ TG.bound.eval (n + lam) * (d.size + 1) ^ TG.deg + constCost ∧
      (prep TG UT S' ((M, (lam, e)), (n, d))).1.Runs
        (prep TG UT S' ((M, (lam, e)), (n, d))).2 r t := by
  rw [prep_apply]
  split_ifs with h1 h2
  · refine ⟨?_, ?_, encode ([] : List BitStr), _, ?_, Eval.const _ _⟩
    · simp only [progSize]; omega
    · simp only [Data.size_nil]; omega
    · simp only [constCost]; omega
  · refine ⟨?_, ?_, encode [rejectConstraint 0], _, ?_, Eval.const _ _⟩
    · simp only [progSize]; omega
    · simp only [Data.size_nil]; omega
    · simp only [constCost]; omega
  · refine ⟨?_, ?_, ?_⟩
    · show esize (comprLp TG lam e) ≤ _
      unfold comprLp progSize
      refine le_trans ((TG.compress.esize_apply_le _).trans (polynomial_eval_mono _ ?_))
        (Nat.le_add_right _ _) |>.trans (Nat.le_add_right _ _)
      simp only [esize_prod]
      have h1 := TG.samplerProg.esize_apply_le lam
      have h2 := TG.lenProg.esize_apply_le lam
      omega
    · show (Data.cons (encode n) d).size ≤ _
      simp only [Data.size_cons]
      exact le_rfl
    · obtain ⟨r, t, ht, h⟩ := TG.lp_time (TG.samplerProg lam, TG.lenProg lam, e) lam n d
      rw [TG.output_lp] at h
      exact ⟨r, t, by omega, h⟩

/-! ## The processor's run

Every atom of the cost — `|n|`, `|M| + |λ|`, `|λ|`, `n`, `λ` — is at most `muZ z = 5z + 1` or
`z` at `z = n + |M| + λ`. -/

/-- The size of the processor, in `z`. -/
noncomputable def eZ (S' : Prog) (z : ℕ) : ℕ := 2 * muZ z + cD TG U UT S'

/-- The size of the description `(M, (λ, lp M λ))`, in `z`. -/
noncomputable def pZ (S' : Prog) (z : ℕ) : ℕ := 3 * muZ z + cD TG U UT S' + 2

/-- The size of `F (lp M λ)`, in `z`. -/
noncomputable def feZ (S' : Prog) (z : ℕ) : ℕ := esize (body TG U UT S') + pZ TG U UT S' z + 35

/-- The time of `prep`, in `z` and `|d|`. -/
noncomputable def tpZ (S' : Prog) (z s : ℕ) : ℕ :=
  (prep TG UT S').timeBound.eval (pZ TG U UT S' z + vZ z s + 1)

/-- The size of the program `prep` returns, in `z`. -/
noncomputable def sigmaZ (S' : Prog) (z : ℕ) : ℕ :=
  TG.compress.timeBound.eval (TG.samplerProg.timeBound.eval (muZ z) +
    TG.lenProg.timeBound.eval (muZ z) + eZ TG U UT S' z + muZ z + 3) +
    esize acceptProg + esize rejectProg

/-- The time of the program `prep` returns, in `z` and `|d|`. -/
noncomputable def tcZ (z s : ℕ) : ℕ := TG.bound.eval (2 * z) * (s + 1) ^ TG.deg + constCost

/-- The time of the universal machine on it, in `z` and `|d|`. -/
noncomputable def tuZ (S' : Prog) (z s : ℕ) : ℕ :=
  U.bound.eval (sigmaZ TG U UT S' z + vZ z s + tcZ TG z s)

/-- The time of `body`, in `z` and `|d|`. -/
noncomputable def tbZ (S' : Prog) (z s : ℕ) : ℕ :=
  tpZ TG U UT S' z s + (sigmaZ TG U UT S' z + vZ z s + 1 + 1 + tuZ TG U UT S' z s + 1) + 1

/-- The time of `F (lp M λ)`, in `z` and `|d|`. -/
noncomputable def tfZ (S' : Prog) (z s : ℕ) : ℕ :=
  tbZ TG U UT S' z s + pZ TG U UT S' z + vZ z s + 3

/-- The overhead of the fixed point's transfer, in `z`. -/
noncomputable def ovZ (S' : Prog) (z : ℕ) : ℕ := 21 * muZ z + cO TG U UT S'

/-- **The master bound on the processor's run**, in `z` and `|d|`. -/
noncomputable def lpRunZ (S' : Prog) (z s : ℕ) : ℕ :=
  U.bound.eval (vZ z s + tfZ TG U UT S' z s + feZ TG U UT S' z) + 3 * vZ z s +
    ovZ TG U UT S' z

/-- **The processor's run**: on `(n, d)`, `lp M λ` halts within `lpRunZ (n + |M| + λ) |d|`. -/
theorem lp_cost (S' M : Prog) (lam n : ℕ) (d : Data) :
    ∃ r t, t ≤ lpRunZ TG U UT S' (n + esize M + lam) d.size ∧
      (lpProg TG U UT S' M lam).Runs (.cons (encode n) d) r t := by
  set z := n + esize M + lam with hz
  set e := lpProg TG U UT S' M lam with he
  -- the atoms
  have hn : esize n ≤ muZ z := by
    have := esize_nat_le_self n; unfold muZ; omega
  have hl : esize lam ≤ muZ z := by
    have := esize_nat_le_self lam; unfold muZ; omega
  have he_sz' : esize e ≤ 2 * muZ z + cD TG U UT S' := by
    have := esize_nat_le_self lam
    rw [he, esize_lpProg]; unfold muZ; omega
  have he_sz : esize e ≤ eZ TG U UT S' z := he_sz'
  have hP_sz : (encode (M, (lam, e)) : Data).size ≤ pZ TG U UT S' z := by
    have := esize_nat_le_self lam
    rw [size_descData]; unfold pZ muZ at *; omega
  have hv_sz : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
  have hv_le : (Data.cons (encode n) d).size ≤ vZ z d.size := by
    rw [hv_sz]; unfold vZ; omega
  have hFe : esize (F TG U UT S' M lam e) ≤ feZ TG U UT S' z := by
    have := esize_nat_le_self lam
    rw [esize_F_apply]; unfold feZ pZ muZ at *; omega
  have hov : kleeneOverhead U (F TG U UT S' M lam) ≤ ovZ TG U UT S' z := by
    have := esize_nat_le_self lam
    rw [kleeneOverhead_eq]; unfold ovZ muZ; omega
  -- the run of `prep`
  set q := prep TG UT S' ((M, (lam, e)), (n, d)) with hq
  obtain ⟨tp, htp, hp⟩ := (prep TG UT S').computes ((M, (lam, e)), (n, d))
  have htp' : tp ≤ tpZ TG U UT S' z d.size := by
    refine htp.trans (polynomial_eval_mono _ ?_)
    have h1 : esize ((M, (lam, e)), (n, d)) =
        (encode (M, (lam, e)) : Data).size + (esize n + d.size + 1) + 1 := rfl
    rw [h1]; unfold vZ; omega
  obtain ⟨hc_sz, hw_sz, r, tc, htc, hc⟩ := prep_output TG UT S' M lam e n d
  have hσ : esize q.1 ≤ sigmaZ TG U UT S' z := by
    refine hc_sz.trans ?_
    unfold progSize sigmaZ
    have h1 := polynomial_eval_mono TG.samplerProg.timeBound hl
    have h2 := polynomial_eval_mono TG.lenProg.timeBound hl
    refine Nat.add_le_add_right (Nat.add_le_add_right (polynomial_eval_mono _ ?_) _) _
    omega
  have hw : q.2.size ≤ vZ z d.size := hw_sz.trans (by unfold vZ; omega)
  have htc' : tc ≤ tcZ TG z d.size := by
    refine htc.trans ?_
    unfold tcZ
    have := polynomial_eval_mono TG.bound (show n + lam ≤ 2 * z by omega)
    have := Nat.mul_le_mul_right ((d.size + 1) ^ TG.deg) this
    omega
  -- the universal machine on it
  obtain ⟨tu, htu, hu⟩ := U.time_le q.1 q.2 r tc hc
  have htu' : tu ≤ tuZ TG U UT S' z d.size := by
    refine htu.trans (polynomial_eval_mono _ ?_)
    omega
  -- the run of `body`
  have hq_sz : esize q = esize q.1 + q.2.size + 1 := rfl
  have hbody : (body TG U UT S').Runs (.cons (encode (M, (lam, e))) (.cons (encode n) d)) r
      (tp + (esize q + 1 + tu + 1) + 1) := by
    have hu' : Eval [encode q] U.univ r tu := hu
    have h₂ := callVar_eval (env := [encode q, encode ((M, (lam, e)), (n, d))]) (i := 0)
      U.closed (v := encode q) (by simp) hu'
    exact Eval.let_ hp h₂
  have hF : (F TG U UT S' M lam e).Runs (.cons (encode n) d) r
      (tp + (esize q + 1 + tu + 1) + 1 + (encode (M, (lam, e)) : Data).size +
        (Data.cons (encode n) d).size + 3) :=
    hardcode_time (body_wellScoped TG U UT S') hbody
  -- the fixed point
  have hF' : (F TG U UT S' M lam (kleeneFix U (F TG U UT S' M lam))).Runs
      (.cons (encode n) d) r _ := hF
  obtain ⟨t', ht', hrun⟩ := kleeneFix_runs_of U (F TG U UT S' M lam) hF'
  have ht'' : t' ≤ U.bound.eval ((Data.cons (encode n) d).size +
      (tp + (esize q + 1 + tu + 1) + 1 + (encode (M, (lam, e)) : Data).size +
        (Data.cons (encode n) d).size + 3) + esize (F TG U UT S' M lam e)) +
      3 * (Data.cons (encode n) d).size + kleeneOverhead U (F TG U UT S' M lam) := ht'
  refine ⟨r, t', ht''.trans ?_, hrun⟩
  have htf : tp + (esize q + 1 + tu + 1) + 1 + (encode (M, (lam, e)) : Data).size +
      (Data.cons (encode n) d).size + 3 ≤ tfZ TG U UT S' z d.size := by
    unfold tfZ tbZ; omega
  have hev := polynomial_eval_mono U.bound (Nat.add_le_add (Nat.add_le_add hv_le htf) hFe)
  unfold lpRunZ
  omega

/-! ## The polynomial form -/

theorem polyBounded_eZ (S' : Prog) : PolyBounded (eZ TG U UT S') :=
  (polyBounded_muZ.const_mul 2).add_const _

theorem polyBounded_pZ (S' : Prog) : PolyBounded (pZ TG U UT S') :=
  ((polyBounded_muZ.const_mul 3).add_const _).add_const 2

theorem polyBounded_feZ (S' : Prog) : PolyBounded (feZ TG U UT S') :=
  ((PolyBounded.const _).add (polyBounded_pZ TG U UT S')).add_const 35

theorem polyBounded_sigmaZ (S' : Prog) : PolyBounded (sigmaZ TG U UT S') :=
  ((PolyBounded.eval _ (((((PolyBounded.eval _ polyBounded_muZ).add
    (PolyBounded.eval _ polyBounded_muZ)).add (polyBounded_eZ TG U UT S')).add
    polyBounded_muZ).add_const 3)).add_const _).add_const _

theorem polyBounded_ovZ (S' : Prog) : PolyBounded (ovZ TG U UT S') :=
  (polyBounded_muZ.const_mul 21).add_const _

theorem polyCost_tpZ (S' : Prog) : PolyCost fun z d => tpZ TG U UT S' z d.size :=
  PolyCost.poly _ (((PolyCost.ofIndex (polyBounded_pZ TG U UT S')).add polyCost_vZ).add
    (PolyCost.const 1))

theorem polyCost_tcZ : PolyCost fun z d => tcZ TG z d.size :=
  ((PolyCost.ofIndex (PolyBounded.eval _ (PolyBounded.id.const_mul 2))).mul
    (polyCost_pow_size TG.deg)).add (PolyCost.const _)

theorem polyCost_tuZ (S' : Prog) : PolyCost fun z d => tuZ TG U UT S' z d.size :=
  PolyCost.poly _ (((PolyCost.ofIndex (polyBounded_sigmaZ TG U UT S')).add polyCost_vZ).add
    (polyCost_tcZ TG))

theorem polyCost_tbZ (S' : Prog) : PolyCost fun z d => tbZ TG U UT S' z d.size :=
  ((polyCost_tpZ TG U UT S').add (((((PolyCost.ofIndex (polyBounded_sigmaZ TG U UT S')).add
    polyCost_vZ).add (PolyCost.const 1)).add (PolyCost.const 1)).add
    (polyCost_tuZ TG U UT S') |>.add (PolyCost.const 1))).add (PolyCost.const 1)

theorem polyCost_tfZ (S' : Prog) : PolyCost fun z d => tfZ TG U UT S' z d.size :=
  (((polyCost_tbZ TG U UT S').add (PolyCost.ofIndex (polyBounded_pZ TG U UT S'))).add
    polyCost_vZ).add (PolyCost.const 3)

theorem polyCost_lpRunZ (S' : Prog) : PolyCost fun z d => lpRunZ TG U UT S' z d.size :=
  ((PolyCost.poly _ ((polyCost_vZ.add (polyCost_tfZ TG U UT S')).add
    (PolyCost.ofIndex (polyBounded_feZ TG U UT S')))).add
    ((PolyCost.const 3).mul polyCost_vZ)).add (PolyCost.ofIndex (polyBounded_ovZ TG U UT S'))

/-- **The processor's cost, in polynomial form**: a polynomial `Q` and a degree `k`, depending on
`TG`, `U`, `UT` and `S'` alone, with `lp M λ` halting on `(n, d)` within
`Q (n + |M| + λ) · (|d| + 1) ^ k`. -/
theorem exists_lp_cost_poly (S' : Prog) : ∃ (Q : Polynomial ℕ) (k : ℕ),
    ∀ (M : Prog) (lam n : ℕ) (d : Data), ∃ r t,
      t ≤ Q.eval (n + esize M + lam) * (d.size + 1) ^ k ∧
        (lpProg TG U UT S' M lam).Runs (.cons (encode n) d) r t := by
  obtain ⟨Cq, k, hCq, hb⟩ := polyCost_lpRunZ TG U UT S'
  refine ⟨hCq.poly, k, fun M lam n d => ?_⟩
  obtain ⟨r, t, ht, h⟩ := lp_cost TG U UT S' M lam n d
  exact ⟨r, t, ht.trans ((hb _ d).trans (Nat.mul_le_mul_right _ (hCq.le_poly_eval _))), h⟩

/-! ## The clauses of `IsBounded` -/

/-- **The sampler and answer-length clauses, and the parameter inequality**: past a threshold
on `λ`, at every index `m ≥ 2`, the compression's bound `poly(m, λ)` is below `m ^ λ`, so the
compressed sampler at `λ` has dimension at most `m ^ λ` and runs within
`m ^ λ · (|d| + 1) ^ λ`, and the compressed answer-length calculator runs within the same bound
and outputs lengths at most `m ^ λ`. -/
theorem sampler_len_clauses : ∃ n₀, ∀ lam, n₀ ≤ lam → ∀ m, 2 ≤ m →
    TG.bound.eval (m + lam) ≤ m ^ lam ∧ (TG.sampler lam).dim m ≤ m ^ lam ∧
      (TG.sampler lam).TimeBoundAt m (m ^ lam) lam ∧ (TG.len lam).TimeBoundAt m (m ^ lam) lam ∧
      LenBound (TG.len lam) m (m ^ lam) := by
  obtain ⟨n₀, hn₀⟩ := (PolyBounded.eval TG.bound PolyBounded.id).absorb
  refine ⟨max n₀ TG.deg, fun lam hl m hm => ?_⟩
  have h1 : TG.bound.eval (m + lam) ≤ m ^ lam := by
    have := hn₀ lam (le_trans (le_max_left _ _) hl) m hm 1 le_rfl
    rw [one_pow, mul_one, mul_one] at this
    exact (polynomial_eval_mono _ (by omega)).trans this
  have hdeg : TG.deg ≤ lam := le_trans (le_max_right _ _) hl
  exact ⟨h1, (TG.sampler_dim _ m).trans h1, (TG.sampler_time lam m).mono h1 hdeg,
    (TG.len_time lam m).mono h1 hdeg,
    fun x κ k hk => (TG.len_bound lam m x κ k hk).trans h1⟩

/-- **The processor clause**: past a threshold on `λ`, for `|M| ≤ λ`, the processor of
`V^{M,λ}` runs within `m ^ λ · (|d| + 1) ^ λ` at every index `m ≥ 2`. -/
theorem lp_clause (S' : Prog) : ∃ n₀, ∀ (M : Prog) (lam : ℕ), n₀ ≤ lam →
    esize M ≤ lam → ∀ m, 2 ≤ m →
    (Vhalt TG U UT S' M lam).lp.TimeBoundAt m (m ^ lam) lam := by
  obtain ⟨Q, k, hQ⟩ := exists_lp_cost_poly TG U UT S'
  have hΦ : PolyBounded fun z => Q.eval (2 * z) * (z + 1) ^ k :=
    (PolyBounded.eval Q (PolyBounded.id.const_mul 2)).mul ((PolyBounded.id.add_const 1).pow k)
  obtain ⟨n₀, hn₀⟩ := hΦ.absorb
  refine ⟨n₀, fun M lam hl hM m hm d => ?_⟩
  obtain ⟨r, t, ht, hrun⟩ := hQ M lam m d
  refine ⟨r, t, ht.trans ?_, hrun⟩
  have hz := hn₀ lam hl m hm (d.size + 1) (by omega)
  refine le_trans (Nat.mul_le_mul (polynomial_eval_mono _ ?_)
    (Nat.pow_le_pow_left ?_ k)) hz
  · nlinarith
  · nlinarith

/-- The size of `V^{M,λ}` beyond `2|M|`, as a function of `|λ|`. -/
noncomputable def vsizeZ (S' : Prog) (l : ℕ) : ℕ :=
  TG.samplerProg.timeBound.eval l + TG.lenProg.timeBound.eval l + 2 * l + cD TG U UT S'

theorem polyBounded_vsizeZ (S' : Prog) : PolyBounded (vsizeZ TG U UT S') :=
  (((PolyBounded.eval _ PolyBounded.id).add (PolyBounded.eval _ PolyBounded.id)).add
    (PolyBounded.id.const_mul 2)).add_const _

/-- The size of `V^{M,λ}` is at most `2|M| + vsizeZ |λ|`. -/
theorem Vhalt_size_le (S' M : Prog) (lam : ℕ) :
    (Vhalt TG U UT S' M lam).size ≤ 2 * esize M + vsizeZ TG U UT S' (esize lam) := by
  have h1 : esize (TG.sampler lam).prog ≤ TG.samplerProg.timeBound.eval (esize lam) := by
    rw [← TG.samplerProg_eq]; exact TG.samplerProg.esize_apply_le lam
  have h2 : esize (TG.len lam).prog ≤ TG.lenProg.timeBound.eval (esize lam) := by
    rw [← TG.lenProg_eq]; exact TG.lenProg.esize_apply_le lam
  have h3 := esize_lpProg TG U UT S' M lam
  refine max_le ?_ (max_le ?_ ?_)
  · show esize (TG.sampler lam).prog ≤ _
    unfold vsizeZ; omega
  · show esize (TG.len lam).prog ≤ _
    unfold vsizeZ; omega
  · show esize (lpProg TG U UT S' M lam) ≤ _
    rw [h3]; unfold vsizeZ; omega

/-- **The size clause**: past a threshold on `λ`, for `4|M| ≤ λ`, `|V^{M,λ}| ≤ λ`. -/
theorem size_clause (S' : Prog) : ∃ n₀, ∀ (M : Prog) (lam : ℕ), n₀ ≤ lam →
    4 * esize M ≤ lam → (Vhalt TG U UT S' M lam).size ≤ lam := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_vsizeZ TG U UT S').absorb_log 1 4
  refine ⟨n₀, fun M lam hl hM => ?_⟩
  have h := hn₀ lam hl
  have h1 : vsizeZ TG U UT S' (esize lam) ≤ vsizeZ TG U UT S' (1 + 4 * Nat.size lam) := by
    have := esize_nat_le lam
    unfold vsizeZ
    have := polynomial_eval_mono TG.samplerProg.timeBound
      (show esize lam ≤ 1 + 4 * Nat.size lam by omega)
    have := polynomial_eval_mono TG.lenProg.timeBound
      (show esize lam ≤ 1 + 4 * Nat.size lam by omega)
    omega
  have h2 := Vhalt_size_le TG U UT S' M lam
  omega

/-! ## `lem:lambda` -/

/-- **`lem:lambda` for tailored verifiers**: there is a threshold `Λ₀`, depending on `TG`, `U`,
`UT` and `S'` alone, such that for every machine `M` and every `λ ≥ Λ₀ + 4|M|`, the verifier
`V^{M,λ}` is `λ`-bounded. -/
theorem exists_lamBound (S' : Prog) : ∃ Λ₀ : ℕ, ∀ (M : Prog) (lam : ℕ),
    Λ₀ + 4 * esize M ≤ lam → (Vhalt TG U UT S' M lam).IsBounded lam := by
  obtain ⟨nS, hS⟩ := sampler_len_clauses TG
  obtain ⟨nP, hP⟩ := lp_clause TG U UT S'
  obtain ⟨nZ, hZ⟩ := size_clause TG U UT S'
  refine ⟨max nS (max nP nZ), fun M lam hl => ⟨fun m hm => ?_, ?_⟩⟩
  · obtain ⟨-, h1, h2, h3, h4⟩ := hS lam (by omega) m hm
    exact ⟨h1, h2, h3, hP M lam (by omega) (by omega) m hm, h4⟩
  · exact hZ M lam (by omega) (by omega)

/-- The threshold of `lem:lambda`. -/
noncomputable def Lam0 (S' : Prog) : ℕ := (exists_lamBound TG U UT S').choose

theorem Lam0_spec (S' M : Prog) (lam : ℕ) (h : Lam0 TG U UT S' + 4 * esize M ≤ lam) :
    (Vhalt TG U UT S' M lam).IsBounded lam :=
  (exists_lamBound TG U UT S').choose_spec M lam h

end MIPRE.Tailored.Halting

end
