/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.LdSampler
public import MIPRE.Background.Tailored.AnswerReduction.Meets
public import MIPRE.Foundations.CL.DetypingDeciderTransport
public import MIPRE.Foundations.CL.DetypingProgSampler
public import MIPRE.Foundations.OracularSampler
public import MIPRE.Foundations.CL.ProgBuild

@[expose] public section

/-!
# The answer-reduced sampler

Slice P4h of `planning/aldous-lyons-track.md`: the sampler of the output tailored verifier of the
answer reduction, as the contract `TailoredAnswerReduction` asks for it, a function of the input
sampler and the parameters `(λ, μ, σ)` whose program is computed from the input sampler's in
polynomial time (`arSamplerProg_eq`).

* `arTyped`: the typed sampler, the oracularized input sampler (`oracleSampler`) and the
  low-degree half (`LdFamily.directSampler`) side by side (`TypedSampler.prodDirect`); its CL
  functions are the answer-reduced family `arCl` (`arTyped_cl`), an answer-reduced sampler
  (`arSampler_arCl`).
* `arSampler`: the typed sampler detyped along the complete graph with loops
  (`CL.Detyping.sampler`), of level `max (ℓ + 1) 3 + 2`.
* `arSampler_dist`: its question distribution, read along the numbering of the detyped
  coordinates (`vectorEquiv`), is the detyped game's, which the presented answer-reduced game
  takes (`dist_arPresented`): the sampler half of `TailoredVerifier.MeetsAt`.

The parameters of the low-degree half come from a routine (`LdRoutine`), fixed with the rest of
the parameters in P4i.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.CL.CLFun MIPRE.SAT

/-- **A parameter routine for the low-degree half**: the families of parameters at each
`(λ, μ, σ)`, and a polynomial-time map from `(λ, μ, σ)` to a closed program computing them at each
index. -/
structure LdRoutine where
  /-- The parameters of the low-degree half at `(λ, μ, σ)`. -/
  fam : ℕ → ℕ → ℕ → LdFamily
  /-- The parameter program, from `(λ, μ, σ)`. -/
  parPF : PolyTimeFun (ℕ × ℕ × ℕ) Prog
  closed : ∀ lam mu sigma, (parPF (lam, mu, sigma)).WellScoped 1
  runs : ∀ lam mu sigma n, ∃ t, (parPF (lam, mu, sigma)).Runs (encode n)
    ((fam lam mu sigma).pd n) t

namespace LdRoutine

variable (R : LdRoutine) (lam mu sigma : ℕ)

/-- The low-degree half at `(λ, μ, σ)`, directly answered. -/
def ldDirect : DirectSampler 3 LIDT.CL.Ty :=
  (R.fam lam mu sigma).directSampler (R.parPF (lam, mu, sigma)) (R.closed lam mu sigma)
    (R.runs lam mu sigma)

/-- **The answer-reduced typed sampler**: the oracularized input sampler and the low-degree half,
side by side. -/
def arTyped {ℓ : ℕ} (S : CL.Sampler (ℓ + 1)) :
    TypedSampler (max (ℓ + 1) 3) (Role × LIDT.CL.Ty) :=
  TypedSampler.prodDirect (oracleSampler S) (R.ldDirect lam mu sigma) (max (ℓ + 1) 3) (by omega)
    (le_max_left _ _) (le_max_right _ _)

/-- **The typed sampler's CL functions are the answer-reduced family.** -/
theorem arTyped_cl {ℓ : ℕ} (V : TailoredVerifier (ℓ + 1)) (n : ℕ) (w : Player)
    (u : Role × LIDT.CL.Ty) :
    (R.arTyped lam mu sigma V.sampler).cl n w u = arCl ((R.fam lam mu sigma).sel n) n V u := rfl

theorem arTyped_dim {ℓ : ℕ} (S : CL.Sampler (ℓ + 1)) (n : ℕ) :
    (R.arTyped lam mu sigma S).dim n =
      S.dim n + D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n := rfl

/-- **The answer-reduced sampler**: the typed sampler detyped along the complete graph with
loops. -/
def arSampler {ℓ : ℕ} (S : CL.Sampler (ℓ + 1)) : CL.Sampler (max (ℓ + 1) 3 + 2) :=
  CL.Detyping.sampler arGraph (R.arTyped lam mu sigma S) (by omega)

/-- The detyped questions, numbered, as the answer-reduced sampler's questions. -/
abbrev qe {ℓ : ℕ} (S : CL.Sampler (ℓ + 1)) (n : ℕ) :
    (Detyping.Coord (Role × LIDT.CL.Ty) (Fin ((R.arTyped lam mu sigma S).dim n)) → 𝔽₂) ≃
      (Fin ((R.arSampler lam mu sigma S).dim n) → 𝔽₂) :=
  CL.Detyping.DeciderProgram.vectorEquiv ((R.arTyped lam mu sigma S).dim n)

/-- **The question distribution of the answer-reduced sampler** is the detyped game's, read
along the numbering. -/
theorem arSampler_dist {ℓ : ℕ} (V : TailoredVerifier (ℓ + 1)) (n : ℕ) {A B : Type*}
    [Fintype A] [Fintype B]
    (Dt : Detyping.Question (Role × LIDT.CL.Ty) (Fin ((R.arTyped lam mu sigma V.sampler).dim n)) →
      Detyping.Question (Role × LIDT.CL.Ty) (Fin ((R.arTyped lam mu sigma V.sampler).dim n)) →
        A → B → Bool)
    (x y : Detyping.Coord (Role × LIDT.CL.Ty) (Fin ((R.arTyped lam mu sigma V.sampler).dim n)) →
      𝔽₂) :
    (R.arSampler lam mu sigma V.sampler).dist n (R.qe lam mu sigma V.sampler n x)
        (R.qe lam mu sigma V.sampler n y) =
      (CL.Detyping.game arGraph (fun _ u => arCl ((R.fam lam mu sigma).sel n) n V u) Dt).μ x y :=
  (CL.Detyping.DeciderProgram.numbered_clDist arGraph (R.arTyped lam mu sigma V.sampler) n x
    y).trans (CL.Detyping.game_mu_eq_clDist arGraph _ Dt x y).symm

/-! ## The program -/

/-- The typed sampler's program, from the input sampler's and `(λ, μ, σ)`. -/
def typedPF (ℓ : ℕ) : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (Prog × ℕ × Prog)).comp
    ((const (ProductSampler.core ldAnswerProg ldDimProg)).pair
      ((OracleSampler.samplerProgFun.comp fst).pair ((const (ℓ + 1)).pair (R.parPF.comp snd))))

/-- **The answer-reduced sampler's program**, from the input sampler's and `(λ, μ, σ)`. -/
def arSamplerProg (ℓ : ℕ) : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog :=
  (ProgBuild.routeOneCallF (CL.Detyping.Program.route arGraph)
    (CL.Detyping.Program.post (CL.Detyping.graphDim (Role × LIDT.CL.Ty)))).comp (R.typedPF ℓ)

theorem arSamplerProg_eq {ℓ : ℕ} (S : CL.Sampler (ℓ + 1)) :
    R.arSamplerProg ℓ (S.prog, lam, mu, sigma) = (R.arSampler lam mu sigma S).prog := rfl

end LdRoutine

/-! ## The presented game's weights -/

variable {d : ℕ} (R : LdRoutine) (lam mu sigma : ℕ) {ℓ : ℕ} {V : TailoredVerifier (ℓ + 1)}
  {n : ℕ} {L : PcpDims} {hLM : L.m ≤ 2 ^ (R.fam lam mu sigma).j n}
  {Cc : V.Questions n → Circuit} {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {B : ℕ}

/-- **The answer-reduced sampler's distribution is the presented game's weights**, along the
numbering of the detyped questions. -/
theorem dist_arPresented
    (x y : Detyping.Coord (Role × LIDT.CL.Ty) (Fin ((R.arTyped lam mu sigma V.sampler).dim n)) →
      𝔽₂) :
    (R.arSampler lam mu sigma V.sampler).dist n (R.qe lam mu sigma V.sampler n x)
        (R.qe lam mu sigma V.sampler n y) =
      (arPresented d ((R.fam lam mu sigma).dvd n) ((R.fam lam mu sigma).sel n) L hLM V n Cc hm
        (fun _ u => arCl ((R.fam lam mu sigma).sel n) n V u) B).μ x y :=
  R.arSampler_dist lam mu sigma V n
    (arDt d ((R.fam lam mu sigma).dvd n) ((R.fam lam mu sigma).sel n) L hLM V n Cc hm B) x y

end MIPRE.Tailored.AnsRed.Typed

end
