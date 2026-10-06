/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.WrapperCost

@[expose] public section

/-!
# The running time of the wrapper, at one index

`Prog.wrapCore_cost'` (`Halting/WrapperCost.lean`) bounds the wrapper of
`Verifier.ofSamplerDecider` explicitly, but asks for the sampler's time bound at *every* index,
while `λ`-boundedness — of a normal form verifier, or of a tailored one — supplies it only for
`n ≥ 2`. The wrapper calls the sampler at one index only, the index `n` of its own input (the
dimension query `(n, dimension)` of `Prog.wrapHead`), so the bound at that index is all the
proof uses. This file restates the three stages with the hypothesis at `n` alone:

* `wrapHead_cost_at`, `wrapPre_cost_at`, `wrapCore_cost_at`: `wrapHead_cost'`,
  `wrapPre_cost'`, `wrapCore_cost'` for a sampler with `S.TimeBoundAt n Cs kf`, at the
  constant cost function `fun _ => Cs` — so the bound is the same `wrapCoreCost`, and the
  existing accounting applies unchanged;
* `esize_wrapCore`: the wrapper's description is that of the sampler program plus that of the
  decider datum plus a constant depending on the universal machine alone.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

open Data

section At

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)

/-- **The head, at one index**: `wrapHead_cost'` from the sampler's time bound at the index of
the input only. -/
theorem wrapHead_cost_at {n Cs kf : ℕ} (hf : S.TimeBoundAt n Cs kf) :
    ∀ (c : Prog) (d r : Data) (t : ℕ),
      Eval (wrapHeadEnv S n d) c r t →
        ∃ t', t' ≤ t + 60 * wrapHeadZ U S (fun _ => Cs) kf n ^ 2 ∧
          Eval [.cons (encode n) d] (wrapHead U.univ S.prog c) r t' := by
  have hdimrun :
      ∃ t ≤ Cs * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ kf,
      S.prog.Runs (.cons (encode n) (encode CL.Sampler.Query.dimension)) (encode (S.dim n)) t := by
    obtain ⟨r, t, ht, hrun⟩ := hf (encode CL.Sampler.Query.dimension)
    obtain ⟨t₀, h₀⟩ := S.runs_dimension n
    obtain ⟨rfl, rfl⟩ := Eval.deterministic hrun h₀
    exact ⟨t, ht, hrun⟩
  have htu : ∀ m : ℕ, ∃ t ≤ (Nat.size m + 2) * ((m + 1) * (4 * m + 14) + 7 * esize m + 8 * m + 90),
      toUnaryProg.Runs (encode m) (Data.ofNat m) t := fun m => toUnaryProg_runs m
  intro c d r t hc
  set Z : ℕ := wrapHeadZ U S (fun _ => Cs) kf n with hZ
  obtain ⟨t₁, ht₁, h₁⟩ := hdimrun
  obtain ⟨t₂, ht₂, h₂⟩ := htu (S.dim n)
  obtain ⟨t₃, ht₃, h₃⟩ := U.time_le S.prog (.cons (encode n) (encode CL.Sampler.Query.dimension))
    (encode (S.dim n)) t₁ h₁
  refine ⟨_, ?_, Eval.elim_cons (env := [.cons (encode n) d]) (i := 0) (a := encode n) (b := d)
    (by simp)
    (Eval.let_ (Eval.cons (Eval.const _ _)
        (Eval.cons (Eval.var_of_get (i := 0) (v := encode n) (by simp)) (Eval.const _ _)))
      (Eval.let_ (callVar_eval U.closed (i := 0)
          (v := .cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension)))
          (by simp) h₃)
        (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 0) (v := encode (S.dim n))
            (by simp) h₂) hc)))⟩
  have hZ1 : 1 ≤ Z := by simp only [hZ, wrapHeadZ]; omega
  have hZsq : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) _
  have e0 : t₁ ≤ Z := ht₁.trans (by simp only [hZ, wrapHeadZ]; omega)
  have e1 : esize S.prog ≤ Z := by simp only [hZ, wrapHeadZ]; omega
  have e2 : esize n ≤ Z := by simp only [hZ, wrapHeadZ]; omega
  have e3 : (encode CL.Sampler.Query.dimension : Data).size ≤ Z := by
    simp only [hZ, wrapHeadZ]; omega
  have e4 : esize (S.dim n) ≤ Z := by simp only [hZ, wrapHeadZ]; omega
  have e5 : t₂ ≤ Z := ht₂.trans (by simp only [hZ, wrapHeadZ]; omega)
  have e6 : t₃ ≤ Z := by
    refine ht₃.trans ?_
    have : esize S.prog + (Data.cons (encode n) (encode CL.Sampler.Query.dimension)).size + t₁ ≤
        esize S.prog + (esize n + (encode CL.Sampler.Query.dimension : Data).size + 1) +
          Cs * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ kf := by
      have : (Data.cons (encode n) (encode CL.Sampler.Query.dimension)).size =
          esize n + (encode CL.Sampler.Query.dimension : Data).size + 1 := rfl
      omega
    exact (polynomial_eval_mono U.bound this).trans (by simp only [hZ, wrapHeadZ]; omega)
  have hsz : (encode n : Data).size = esize n := rfl
  have hszS : (encode S.prog : Data).size = esize S.prog := rfl
  have hszD : (encode (S.dim n) : Data).size = esize (S.dim n) := rfl
  simp only [Data.size_cons, hsz, hszS, hszD]
  omega

/-- **The prefix, at one index**: `wrapPre_cost'` from the sampler's time bound at the index of
the input only. -/
theorem wrapPre_cost_at {n Cs kf : ℕ} (hf : S.TimeBoundAt n Cs kf) :
    (∀ (c : Prog) (A B C r : Data) (t : ℕ),
        Eval (wrapPreEnvD S n A B C) c r t →
          ∃ t' ≤ t + (60 * wrapHeadZ U S (fun _ => Cs) kf n ^ 2 + 4),
            Eval [.cons (encode n) (.cons A (.cons B C))] (wrapPre U.univ S.prog c) r t') ∧
      (∀ (c : Prog) (d : Data), d.spine ≤ 1 →
        ∃ t ≤ 60 * wrapHeadZ U S (fun _ => Cs) kf n ^ 2 + 4,
          Eval [.cons (encode n) d] (wrapPre U.univ S.prog c) .nil t) := by
  have hhead := wrapHead_cost_at U S hf
  refine ⟨fun c A B C r t hc => ?_, fun c d hd => ?_⟩
  · obtain ⟨t', ht', h'⟩ := hhead (.elim 4 .nil (.elim 1 .nil c))
      (.cons A (.cons B C)) r (t + 1 + 1)
      (Eval.elim_cons (i := 4) (a := A) (b := .cons B C) (by simp [wrapHeadEnv])
        (Eval.elim_cons (i := 1) (a := B) (b := C) (by simp) hc))
    exact ⟨t', by omega, h'⟩
  · have hrej : ∃ u ≤ 3, Eval (wrapHeadEnv S n d) (.elim 4 .nil (.elim 1 .nil c)) .nil u := by
      match d, hd with
      | .nil, _ =>
        exact ⟨2, by omega,
          Eval.elim_nil (i := 4) (by simp [wrapHeadEnv]) (Eval.nil _)⟩
      | .cons A .nil, _ =>
        exact ⟨3, by omega,
          Eval.elim_cons (i := 4) (a := A) (b := .nil) (by simp [wrapHeadEnv])
            (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))⟩
      | .cons A (.cons B C), h => exact absurd h (by simp)
    obtain ⟨u, hu, hrun⟩ := hrej
    obtain ⟨t', ht', h'⟩ := hhead (.elim 4 .nil (.elim 1 .nil c)) d .nil u hrun
    exact ⟨t', by omega, h'⟩

/-- **The wrapper halts within the explicit `wrapCoreCost` on every input of index `n`**, from
the sampler's time bound at `n` alone and a bound `Td |d|` on the string's decider at `n`. -/
theorem wrapCore_cost_at (dec : Prog) {n Cs kf : ℕ} (hf : S.TimeBoundAt n Cs kf) (Td : ℕ → ℕ)
    (hdec : ∀ d : Data, ∃ r t, t ≤ Td d.size ∧ dec.Runs (.cons (encode n) d) r t) (d : Data) :
    ∃ r t, t ≤ wrapCoreCost U S dec (fun _ => Cs) kf n (Td d.size) d.size ∧
      (wrapCore U.univ S.prog (encode dec)).Runs (.cons (encode n) d) r t := by
  obtain ⟨hpre, hrej⟩ := wrapPre_cost_at U S hf
  rcases Nat.lt_or_ge d.spine 2 with hd | hd
  · obtain ⟨t, ht, hrun⟩ := hrej _ d (by omega)
    exact ⟨.nil, t, by simp only [wrapCoreCost]; omega, hrun⟩
  · match d, hd with
    | .cons A (.cons B C), _ =>
      set d : Data := Data.cons A (Data.cons B C) with hdef
      have hA : A.size ≤ d.size := by rw [hdef]; simp; omega
      have hB : B.size ≤ d.size := by rw [hdef]; simp; omega
      by_cases hxa : A.spine = S.dim n
      · by_cases hyb : B.spine = S.dim n
        · obtain ⟨r, td, htd, hdr⟩ := hdec d
          obtain ⟨t₇, ht₇, h₇⟩ := U.time_le dec (.cons (encode n) d) r td hdr
          have htail : Eval (wrapCheckEnvN (S.dim n) (S.dim n)
              (wrapCheckEnvN (S.dim n) (S.dim n) (wrapPreEnvD S n A B C)))
              (wrapTail U.univ (encode dec)) r _ :=
            Eval.let_ (Eval.cons (Eval.const _ _)
              (Eval.var_of_get (i := 19) (v := .cons (encode n) d)
                (by simp [wrapCheckEnvN, wrapPreEnvD, wrapHeadEnv, hdef])))
              (callVar_eval U.closed (i := 0)
                (v := .cons (encode dec) (.cons (encode n) d)) (by simp) h₇)
          obtain ⟨t₂, ht₂, h₂⟩ := wrapCheckD_cost_of_eq (i := 5) (j := 9)
            (env := wrapCheckEnvN (S.dim n) (S.dim n) (wrapPreEnvD S n A B C))
            (v := B) (m := S.dim n) rfl rfl hyb htail
          obtain ⟨t₁, ht₁, h₁⟩ := wrapCheckD_cost_of_eq (i := 2) (j := 4)
            (env := wrapPreEnvD S n A B C) (v := A) (m := S.dim n) rfl rfl hxa h₂
          obtain ⟨t₀, ht₀, h₀⟩ := hpre _ A B C r t₁ h₁
          refine ⟨r, t₀, ?_, hdef ▸ h₀⟩
          have hc1 : checkCost A.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
            checkCost_mono hA
          have hc2 : checkCost B.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
            checkCost_mono hB
          have hUb : t₇ ≤ U.bound.eval (esize dec + (esize n + d.size + 1) + Td d.size) :=
            ht₇.trans (polynomial_eval_mono U.bound (by
              have : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
              omega))
          have hsz1 : (encode dec : Data).size = esize dec := rfl
          have hsz2 : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
          simp only [Data.size_cons, hsz1, hsz2] at ht₂
          simp only [wrapCoreCost]
          omega
        · obtain ⟨t₂, ht₂, h₂⟩ := wrapCheckD_cost_of_ne (i := 5) (j := 9)
            (env := wrapCheckEnvN (S.dim n) (S.dim n) (wrapPreEnvD S n A B C))
            (v := B) (m := S.dim n) (c := wrapTail U.univ (encode dec)) rfl rfl hyb
          obtain ⟨t₁, ht₁, h₁⟩ := wrapCheckD_cost_of_eq (i := 2) (j := 4)
            (env := wrapPreEnvD S n A B C) (v := A) (m := S.dim n) rfl rfl hxa h₂
          obtain ⟨t₀, ht₀, h₀⟩ := hpre _ A B C .nil t₁ h₁
          refine ⟨.nil, t₀, ?_, hdef ▸ h₀⟩
          have hc1 : checkCost A.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
            checkCost_mono hA
          have hc2 : checkCost B.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
            checkCost_mono hB
          simp only [wrapCoreCost]
          omega
      · obtain ⟨t₁, ht₁, h₁⟩ := wrapCheckD_cost_of_ne (i := 2) (j := 4)
          (env := wrapPreEnvD S n A B C) (v := A) (m := S.dim n)
          (c := wrapCheck 5 9 (wrapTail U.univ (encode dec))) rfl rfl hxa
        obtain ⟨t₀, ht₀, h₀⟩ := hpre _ A B C .nil t₁ h₁
        refine ⟨.nil, t₀, ?_, hdef ▸ h₀⟩
        have hc1 : checkCost A.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
          checkCost_mono hA
        simp only [wrapCoreCost]
        omega

end At

/-- **The wrapper's description**: that of the sampler program, plus that of the decider
datum, plus a constant depending on the universal machine alone. -/
theorem esize_wrapCore (univ sampProg : Prog) (decD : Data) :
    esize (wrapCore univ sampProg decD) + esize Prog.nil + Data.nil.size =
      esize (wrapCore univ Prog.nil Data.nil) + esize sampProg + decD.size := by
  simp only [wrapCore, wrapPre, wrapHead, wrapCheck, wrapTail, callVar,
    esize_eq_size_toData, toData, Data.size_cons]
  have h1 : (encode sampProg : Data).size = sampProg.toData.size := rfl
  have h2 : (encode Prog.nil : Data).size = Prog.nil.toData.size := rfl
  have h3 : Prog.nil.toData.size = (Data.ofNat 1).size + Data.nil.size + 1 := rfl
  omega

end Cost.Prog

end MIPRE

end
