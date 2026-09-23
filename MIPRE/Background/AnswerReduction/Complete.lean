/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Construction
import MIPRE.Background.AnswerReduction.TypedComplete
import MIPRE.Foundations.CL.DetypingDeciderTransport

/-!
# Completeness of answer reduction

Piece AR-4 of `planning/answer-reduction.md`, concluded (`lem:ar-completeness`, with
`lem:oracle-timeout-pcc` in the ambient form the contract uses): for `λ, μ ≥ 1`, an input within
its budget whose decider has size at most `σ` and which has a value-`1` PCC strategy at the answer
bound `2^{(λn + 1)^μ}` gives an answer-reduced verifier with a value-`1` PCC strategy at the answer
cut (`arVerifier_hasPerfectPCC`), hence at the output bound (`arVerifier_completeness`).

The typed game's completeness (`exists_typedGame_perfectPCC`) asks for good PCP proofs of the
pairs the input decider accepts. They are the PCP decider's (`SAT.PcpDecider.completeness`), under
three facts:

* **the decider accepts within the PCP's time bound** `T = 2^{(Q + 5)(μ + 1)}`
  (`acceptsWithin_of_accepts`): an input within its budget runs within `2^Q (|d| + 1)^μ` on every
  input, and on answers of length at most `2^Q` that is at most `T` — the timeout the paper's
  `lem:oracle-timeout-pcc` handles by truncation is here a consequence of determinism, since the
  answer alphabet is already cut at `2^Q`;
* **the PCP's input is valid** (`valid_of`): `Q ≤ T`, `2 log n ≤ T`, `|𝒟| ≤ σ` and questions of
  length at most `Q`. The second is where `λ, μ ≥ 1` is needed (`Q ≥ n + 1`);
* **the PCP's field is the Shoup field** the answer-reduced sampler downsizes along
  (`ShoupField`, a hypothesis on the PCP decider like `ParamsBound`): the game check hands the PCP
  verifier the view in the Shoup representation, and the PCP's completeness is stated in its own.

Then the detyping compiler's completeness (`CL.Detyping.DeciderProgram.verifier_hasPerfectPCC`)
carries the typed strategy to the output verifier, its typed predicate being the typed game's at
the answer cut (`typedDecider`'s `accepts_iff`).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost

/-- **The PCP's field is the Shoup field**, for every admissible extension degree. -/
def ShoupField (PD : PcpDecider) : Prop :=
  ∀ k (h : Odd k), PD.fld k h = shoupAdmissibleField k h

/-! ## The view of a good proof -/

theorem vecBits_ofProof {P : PcpParams} (hk : 1 ≤ P.k) (pf : PcpProof P (Fq P hk))
    (z : Fin P.m' → Fq P hk) :
    (fld P hk).vecBits (fun j => MvPolynomial.eval z ((ofProof hk pf).c j)) =
      (fld P hk).vecBits (pf.ev z).1 ++ (fld P hk).vecBits (pf.ev z).2 := by
  simp only [BinField.vecBits, ← List.map_append]
  congr 1
  rw [List.ofFn_congr (show P.m' + 6 = 5 + (P.m' + 1) by omega), List.ofFn_add]
  congr 1
  · congr 1
    funext i
    simp only [ofProof, PcpProof.ev]
    rw [dif_pos (by simp), MvPolynomial.eval_rename]
    rfl
  · congr 1
    funext j
    simp only [ofProof, PcpProof.ev]
    rw [dif_neg (by simp)]
    congr 2
    ext
    simp

/-! ## The PCP's hypotheses -/

section Hyps

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ)

theorem pow_le_tPcp : 2 ^ arQ lam mu n * (2 ^ (arQ lam mu n + 5)) ^ mu ≤ tPcp lam mu n := by
  rw [← pow_mul, ← pow_add, tPcp]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **The input decider accepts within the PCP's time bound**: an accepted input of questions at
most `Q` long and answers at most `2^Q` long is accepted within `T = 2^{(Q + 5)(μ + 1)}`, by
determinism, when the decider is within its budget. -/
theorem acceptsWithin_of_accepts (hV : V.Within n (inBudget lam mu n)) {x y a b : BitStr}
    (hx : x.length ≤ arQ lam mu n) (hy : y.length ≤ arQ lam mu n)
    (ha : a.length ≤ inAns lam mu n) (hb : b.length ≤ inAns lam mu n)
    (h : V.decider.Accepts n x y a b) : V.decider.AcceptsWithin n x y a b (tPcp lam mu n) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨r, t', hle, hrun⟩ := hV.decider_time (encode (x, y, a, b))
  obtain ⟨-, rfl⟩ := Eval.deterministic ht hrun
  refine ⟨t, hle.trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)).trans
    (pow_le_tPcp lam mu n)), ht⟩
  have ex := esize_bitStr_le x
  have ey := esize_bitStr_le y
  have ea := esize_bitStr_le a
  have eb := esize_bitStr_le b
  have hQ : arQ lam mu n < 2 ^ arQ lam mu n := Nat.lt_two_pow_self
  have hsz : (encode (x, y, a, b) : Data).size =
      esize x + (esize y + (esize a + esize b + 1) + 1) + 1 := rfl
  change a.length ≤ 2 ^ arQ lam mu n at ha
  change b.length ≤ 2 ^ arQ lam mu n at hb
  rw [hsz, pow_add, show (2 : ℕ) ^ 5 = 32 by norm_num]
  omega

/-- **The PCP's input is valid**, for `λ, μ ≥ 1`. -/
theorem valid_of (hlam : 1 ≤ lam) (hmu : 1 ≤ mu) (hV : V.Within n (inBudget lam mu n))
    (hsz : V.decider.size ≤ sigma) (x : Fin (V.sampler.dim n) → 𝔽₂) :
    Valid V.decider.prog n (tPcp lam mu n) (arQ lam mu n) sigma
      (toBits ((V.sampler.cl n .alice).eval x)) (toBits ((V.sampler.cl n .bob).eval x)) := by
  have hQT : 2 * arQ lam mu n ≤ tPcp lam mu n := by
    have h1 : 2 * arQ lam mu n ≤ 2 ^ (arQ lam mu n + 1) := by
      rw [pow_succ]
      have := (Nat.lt_two_pow_self (n := arQ lam mu n)).le
      omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num)
      (by have := Nat.le_mul_of_pos_right (arQ lam mu n + 5) (show 0 < mu + 1 by omega); omega))
  have hdim : V.sampler.dim n ≤ arQ lam mu n := hV.sampler_dim
  have hn : n ≤ arQ lam mu n := by
    have h1 : n ≤ lam * n + 1 := by nlinarith
    exact h1.trans (Nat.le_self_pow (by omega) _)
  refine ⟨by omega, ?_, hsz, by simp [length_toBits]; omega, by simp [length_toBits]; omega⟩
  have : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

end Hyps

/-! ## The answer-reduced verifier -/

section Final

variable (PD : PcpDecider) (lam mu sigma : ℕ) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ)

local notation "F" => family PD lam mu sigma

/-- **Good PCP proofs exist** for the pairs the input decider accepts, by the PCP's completeness. -/
theorem exists_proofGood (hF : ShoupField PD) (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hV : V.Within n (inBudget lam mu n)) (hsz : V.decider.size ≤ sigma)
    (x : Fin (V.sampler.dim n) → 𝔽₂) (a b : Verifier.Answers (inAns lam mu n))
    (h : (V.seeded n (inAns lam mu n)).D ((V.sampler.cl n .alice).eval x)
      ((V.sampler.cl n .bob).eval x) a b = true) :
    ∃ pf, ProofGood ((F).hk n) (chk PD V lam mu sigma n) x a.1 b.1 pf := by
  have hacc : V.decider.Accepts n (toBits ((V.sampler.cl n .alice).eval x))
      (toBits ((V.sampler.cl n .bob).eval x)) a.1 b.1 := by
    simpa [SeededGame.ofCL, Verifier.game] using h
  have hdim : V.sampler.dim n ≤ arQ lam mu n := hV.sampler_dim
  have hAT : inAns lam mu n ≤ tPcp lam mu n := show 2 ^ arQ lam mu n ≤ _ from
    Nat.pow_le_pow_right (by norm_num)
    (by have := Nat.le_mul_of_pos_right (arQ lam mu n + 5) (show 0 < mu + 1 by omega); omega)
  have hAW := acceptsWithin_of_accepts V lam mu n hV (by simp [length_toBits, hdim])
    (by simp [length_toBits, hdim]) a.2 b.2 hacc
  obtain ⟨pf, h0, h1, hv⟩ := PD.completeness V.decider n (tPcp lam mu n) (arQ lam mu n) sigma _ _
    (valid_of V lam mu sigma n hlam hmu hV hsz x) a.1 b.1 (a.2.trans hAT) (b.2.trans hAT) hAW
  have key : ∀ E : BinField ((F).par n).k, E = fld ((F).par n) ((F).hk n) →
      ∀ pf : PcpProof ((F).par n) E.carrier,
        pf.g 0 = ldEnc (answerVec E.carrier ((F).par n).m a.1) →
        pf.g 1 = ldEnc (answerVec E.carrier ((F).par n).m b.1) →
        (∀ z, PD.verify (pcpInput V.decider.prog n (tPcp lam mu n) (arQ lam mu n) sigma
          (toBits ((V.sampler.cl n .alice).eval x)) (toBits ((V.sampler.cl n .bob).eval x))
          (pf.rawView E z).1 (pf.rawView E z).2) = true) →
        ∃ pf, ProofGood ((F).hk n) (chk PD V lam mu sigma n) x a.1 b.1 pf := by
    rintro E rfl pf h0 h1 hv
    refine ⟨pf, h0, h1, fun z => ?_⟩
    simp only [chk, gameCheck]
    rw [vecBits_ofProof]
    exact hv z
  exact key _ (by rw [hF]; rfl) pf h0 h1 hv

/-- The zero PCP proof. -/
def zeroProof (P : PcpParams) (hk : 1 ≤ P.k) : PcpProof P (Fq P hk) :=
  ⟨0, 0, fun _ _ => by simp, fun _ _ => by simp⟩

open Classical in
/-- **The oracles' PCP proofs**: a good proof where there is one. -/
def arPf (x : Fin (V.sampler.dim n) → 𝔽₂) (a b : BitStr) :
    PcpProof ((F).par n) (Fq ((F).par n) ((F).hk n)) :=
  if h : ∃ pf, ProofGood ((F).hk n) (chk PD V lam mu sigma n) x a b pf then h.choose
  else zeroProof _ _

/-- The typed decider's predicate, at the answer cut, is the typed game's. -/
theorem typedPredicate_eq (p q : CL.Detyping.Question ArTy (Fin (dim V n ((F).par n))))
    (a b : Verifier.Answers (cutVal ((F).par n))) :
    CL.Detyping.DeciderProgram.typedPredicate (typedSampler V.sampler PD lam mu sigma)
        (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) n p q a b =
      typedPred V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n) (chk PD V lam mu sigma n)
        (cutVal ((F).par n)) p q a b := by
  unfold CL.Detyping.DeciderProgram.typedPredicate
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  refine ⟨fun h => (accepts_iff PD V lam mu sigma n p.1 q.1 p.2 q.2 a b).mp h.2.2,
    fun h => ⟨a.2, b.2, (accepts_iff PD V lam mu sigma n p.1 q.1 p.2 q.2 a b).mpr h⟩⟩

set_option maxRecDepth 10000 in
/-- **Completeness of answer reduction, at the answer cut.** -/
theorem arVerifier_hasPerfectPCC (hF : ShoupField PD) (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hV : V.Within n (inBudget lam mu n)) (hsz : V.decider.size ≤ sigma)
    (h : V.HasPerfectPCC n (inAns lam mu n)) :
    (arVerifier PD lam mu sigma V).HasPerfectPCC n (cutVal (arPar PD lam mu sigma n)) := by
  have hpf : ∀ x (a b : Verifier.Answers (inAns lam mu n)),
      (V.seeded n (inAns lam mu n)).D ((V.sampler.cl n .alice).eval x)
        ((V.sampler.cl n .bob).eval x) a b = true →
      ProofGood ((F).hk n) (chk PD V lam mu sigma n) x a.1 b.1
        (arPf PD lam mu sigma V n x a.1 b.1) := by
    intro x a b hD
    have hex := exists_proofGood PD lam mu sigma V n hF hlam hmu hV hsz x a b hD
    rw [arPf, dif_pos hex]
    exact hex.choose_spec
  obtain ⟨R, hR, hval⟩ := exists_typedGame_perfectPCC V n ((F).par n) ((F).hk n)
    (arPf PD lam mu sigma V n) ((F).sel n) ((F).sel' n) (cutVal ((F).par n)) le_rfl h hpf
  have hμ : ∀ p q, (CL.Detyping.typedGame graph graph_nonempty
      (CL.Detyping.DeciderProgram.sourceFamily (typedSampler V.sampler PD lam mu sigma) n)
      (CL.Detyping.DeciderProgram.typedPredicate (typedSampler V.sampler PD lam mu sigma)
        (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) n)).doubled.μ p q =
      (typedGame V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n) (chk PD V lam mu sigma n)
        (cutVal ((F).par n))).doubled.μ (id p) (id q) := fun _ _ => rfl
  refine CL.Detyping.DeciderProgram.verifier_hasPerfectPCC graph
    (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
    (arCut PD lam mu sigma) (fun _ _ _ => trivial) graph_nonempty _ (total PD V lam mu sigma) n
    (R.relabel _ (Equiv.refl _) (Equiv.refl _)) (SyncStrategy.isPCC_relabel hR _ _ _ hμ) ?_
  refine (SyncStrategy.value_relabel R _ (Equiv.refl _) (Equiv.refl _) hμ ?_).trans hval
  intro p q a b
  change (if p.1 = false ∧ q.1 = true then
      CL.Detyping.DeciderProgram.typedPredicate (typedSampler V.sampler PD lam mu sigma)
        (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) n p.2 q.2 a b else false) =
    (if p.1 = false ∧ q.1 = true then
      typedPred V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n) (chk PD V lam mu sigma n)
        (cutVal ((F).par n)) p.2 q.2 a b else false)
  split_ifs
  · exact typedPredicate_eq PD lam mu sigma V n p.2 q.2 a b
  · rfl

/-- **Completeness of answer reduction** (`lem:ar-completeness`, the `completeness` clause of the
`AnswerReduction` contract, at the output bound of `arVerifier_bounds`). -/
theorem arVerifier_completeness (R : Polynomial ℕ) (hF : ShoupField PD) (hR : ParamsBound PD R) :
    ∃ (bound : Polynomial ℕ) (deg : ℕ),
      (∀ (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ), V.Within n (inBudget lam mu n) →
        V.size ≤ sigma → (arVerifier PD lam mu sigma V).Within n
          (Budget.uniform (outBound bound lam mu sigma n) (outDegree deg mu))) ∧
      ∀ (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ), 1 ≤ lam → 1 ≤ mu →
        V.Within n (inBudget lam mu n) → V.decider.size ≤ sigma →
        V.HasPerfectPCC n (inAns lam mu n) →
        (arVerifier PD lam mu sigma V).HasPerfectPCC n (outBound bound lam mu sigma n) := by
  obtain ⟨bound, deg, hW, hcut⟩ := arVerifier_bounds PD R ℓ hR
  exact ⟨bound, deg, hW, fun V lam mu sigma n hlam hmu hV hsz h =>
    Verifier.hasPerfectPCC_of_le _ (hcut lam mu sigma n)
      (arVerifier_hasPerfectPCC PD lam mu sigma V n hF hlam hmu hV hsz h)⟩

end Final

end MIPRE.AnswerReduction

end
