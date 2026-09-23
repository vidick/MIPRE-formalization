/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.ArSampler
import MIPRE.Background.AnswerReduction.ParamsCost
import MIPRE.Foundations.CL.ProductSamplerCost

/-!
# The running time of the typed answer-reduced sampler

Piece AR-3f of `planning/answer-reduction.md`, for `lem:ar-typed-sampler`. The typed sampler is
the product of the oracularized sampler of the input sampler and the directly answered PCP
sampler, whose parameters the routine `parProg` computes
(`MIPRE/Background/AnswerReduction/ArSampler`).
Its time at index `n` is dominated by `(C (W + 1)^M)^{μ + 1}` at degree `E (μ + 1)`
(`typedSampler_time`) for any `W` above `Q = (λn + 1)^μ`, `λ`, `σ`, `n` and the input sampler's
size, when the input sampler runs within `Q (|d| + 1)^μ`: the product's accounting
(`CL.ProductSampler.prog_time`) with the oracularized sampler's (`oracleSampler_timeBound`) and the
routine's (`parProg_time`).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost CL Pipeline SAT Pcp

/-- The sizes of the two programs the product hardcodes are dominated. -/
theorem progs_size_pdom (PD : PcpDecider) : ∃ c m e, ∀ {W X : ℕ} (sp : Prog) (lam mu sigma : ℕ),
    1 ≤ X → esize sp ≤ W → lam ≤ W → sigma ≤ W →
    PDom W X mu c m e (esize (OracleSampler.prog sp) + esize (parProg PD lam mu sigma)) := by
  exact ⟨_, _, _, fun {W X} sp lam mu sigma hX hsp hl hs => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    have h1 : esize (OracleSampler.prog sp) = esize OracleSampler.core + esize sp + 35 :=
      esize_hardcode _ _
    have h2 : esize (parProg PD lam mu sigma) =
        esize (ParRoutine.core PD) + (encode (lam, mu, sigma) : Data).size + 35 :=
      esize_hardcode _ _
    have h3 : (encode (lam, mu, sigma) : Data).size =
        esize lam + (esize mu + esize sigma + 1) + 1 := by
      simp only [encode_prod, Data.size_cons]; rfl
    rw [h1, h2, h3]
    exact ((PDom.const (esize OracleSampler.core + esize (ParRoutine.core PD) + 80)).add hX
      (pdLin hX (by omega : esize sp + (4 * lam + 1) + (4 * mu + 1) + (4 * sigma + 1) ≤
        40 * W + 40 * (mu + 1) + 40))).of_le (by omega)⟩

/-- **The running time of the typed answer-reduced sampler.** -/
theorem typedSampler_time (ℓ : ℕ) (PD : PcpDecider) (R : Polynomial ℕ) : ∃ C M E, ∀ {W : ℕ}
    (S : Sampler (ℓ + 1)) (lam mu sigma n : ℕ), ParamsBound PD R →
    arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W → esize S.prog ≤ W →
    S.TimeBoundAt n (arQ lam mu n) mu →
    (typedSampler S PD lam mu sigma).TimeBoundAt n ((C * (W + 1) ^ M) ^ (mu + 1))
      (E * (mu + 1)) := by
  obtain ⟨cp, mp, ep, hpp⟩ := parProg_time PD R
  obtain ⟨cs, ms, es, hsz⟩ := progs_size_pdom PD
  obtain ⟨cO, mO, eO, hO⟩ := OracleSampler.oracleSampler_timeBound
  obtain ⟨C, M, E, hP⟩ := ProductSampler.prog_time answerProg dimProg (ℓ + 1) cp mp ep cs ms es
    cO mO eO
  exact ⟨C, M, E, fun {W} S lam mu sigma n hR hQ hl hs hn hSz hS d => by
    obtain ⟨r, t, hPD, hrun⟩ := hP (W := W) (K := mu) (OracleSampler.prog S.prog)
      (parProg PD lam mu sigma) n ((family PD lam mu sigma).pd n) (cO * (W + 1) ^ mO) hn
      (fun hX => hpp hR lam mu sigma n hX hQ hl hs hn)
      (fun hX => hsz S.prog lam mu sigma hX hSz hl hs) le_rfl
      (hO S n (arQ lam mu n) mu W hQ hSz hn hS) d
    exact ⟨r, t, hPD.le_final, hrun⟩⟩

end MIPRE.AnswerReduction

end
