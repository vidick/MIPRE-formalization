/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Paper.Build
public import MIPRE.Foundations.Halting.Paper.Count
public import MIPRE.Foundations.ClassMIPStar
public import MIPRE.Foundations.Cost.Growth

@[expose] public section

/-!
# The class verifiers' sampler, for a polynomial-time family of samplers

The sampler of the class verifiers: the `PolyVerifier` that puts an r.e. language in
`MIP*_{1,1/2}(2,1)` (`Paper/ClassVerifier.lean`), and the polynomial-time tailored verifier
that puts it in `TMIP*` (`MIPRE/Tailored/ClassVerifier.lean`). It is stated for any family of
samplers `λ ↦ S^λ` of a level `ℓ` whose programs are computed from `λ` in polynomial time and
which run within a polynomial in `n + λ` (`SamplerFamily`). A `GapCompression` supplies one at
level `7` (`GapCompression.samplerFamily`), a tailored gap compression one at its own level.

On `(z, r)`, for a polynomial-time reduction `R` to halting and the parameter
`λ(z) = Λ₀ + 4|R z|` of `lem:lambda` (`lamz`), the sampler `sampProg` computes `M = R z`,
`λ(z)` and the program of `S^{λ(z)}` (`A1`); asks it its dimension `s` at the fixed index `n₀`
through the universal machine (`runUK`); converts `s` to unary (`unaryStage`); takes the first
`s` bits `r'` of the seed and asks `S^{λ(z)}` the two marginals at `r'` (`A2`, `A3`, `runUK`).
`sampProg_runs`: at a level `ℓ ≥ 1` it halts with the question pair of `S^{λ(z)}` at the point
`r'` within `sampB (|z| + |r|)`, a polynomially bounded function (`polyBounded_sampB`). At level
`0` the marginal queries say nothing, but there the questions are empty
(`CL.Sampler.dim_eq_zero_of_level_zero`): `classSampler` outputs the empty pair at level `0`
and is `sampProg` above it.

**The question distribution.** A `PolyVerifier` whose sampler does this on the seeds of length
`B z` (`Samples`) pushes the uniform seed forward to the distribution of `S^{λ(z)}` at `n₀`, on
the questions embedded as bit strings (`game_μ_qEmb`), and its game has no weight elsewhere
(`game_support`): the seeds producing a question pair are the extensions of the points of
`𝔽₂^s` producing it, each in `2^{B - s}` ways (`seedCount_eq`).
-/

namespace MIPRE.CL.Sampler

/-- At level `0` the questions are empty: the CL function of level `0` is the zero map, which is
exactly on the empty set only. -/
theorem dim_eq_zero_of_level_zero (S : Sampler 0) (n : ℕ) : S.dim n = 0 := by
  have h := S.cl_exactlyOn n .alice
  rw [CLFun.eq_zero (S.cl n .alice), CLFun.exactlyOn_zero, Finset.univ_eq_empty_iff] at h
  simpa using h

end MIPRE.CL.Sampler

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun CL

/-! ## The parameter -/

section Parameter

variable (Λ₀ : ℕ) (R : PolyTimeFun BitStr Prog)

/-- The parameter of the input `z`: `Λ₀ + 4|R z|`. -/
def lamz (z : BitStr) : ℕ := Λ₀ + 4 * esize (R z)

/-- The parameter, in the total input length `m`. -/
noncomputable def lamB (m : ℕ) : ℕ := Λ₀ + 4 * R.timeBound.eval (4 * m + 1)

theorem lamz_le (z : BitStr) (m : ℕ) (hm : z.length ≤ m) :
    lamz Λ₀ R z ≤ lamB Λ₀ R m := by
  unfold lamz lamB
  have h1 := R.esize_apply_le z
  have h2 := esize_bitStr_le z
  have h3 := polynomial_eval_mono R.timeBound (show esize z ≤ 4 * m + 1 by omega)
  omega

/-- The parameter's bound `lamB` is polynomial. -/
theorem polyBounded_lamB : PolyBounded (lamB Λ₀ R) :=
  (PolyBounded.const Λ₀).add
    ((PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 1)).const_mul 4)

end Parameter

/-- The cost of the binary-to-unary conversion, monotone in the number. -/
def unB (D : ℕ) : ℕ := (D + 2) * ((D + 1) * (4 * D + 14) + 7 * (4 * D + 1) + 8 * D + 90)

theorem unCost_le {d D : ℕ} (hd : d ≤ D) :
    (Nat.size d + 2) * ((d + 1) * (4 * d + 14) + 7 * esize d + 8 * d + 90) ≤ unB D := by
  have h1 : Nat.size d ≤ D := (Nat.size_le.2 Nat.lt_two_pow_self).trans hd
  have h2 : esize d ≤ 4 * D + 1 := (esize_nat_le_self d).trans (by omega)
  unfold unB
  exact Nat.mul_le_mul (by omega) (by nlinarith)

/-! ## Families of samplers -/

/-- **A polynomial-time family of samplers**: samplers `S^λ` of level `ℓ`, their programs computed
from `λ` in polynomial time, running within `poly(n + λ)` at degree `deg`, of dimension at most
`poly(n + λ)`. -/
structure SamplerFamily (ℓ : ℕ) where
  sampler : ℕ → Sampler ℓ
  samplerProg : PolyTimeFun ℕ Prog
  samplerProg_eq : ∀ lam : ℕ, samplerProg lam = (sampler lam).prog
  bound : Polynomial ℕ
  deg : ℕ
  sampler_time : ∀ lam n : ℕ, (sampler lam).TimeBoundAt n (bound.eval (n + lam)) deg
  sampler_dim : ∀ lam n : ℕ, (sampler lam).dim n ≤ bound.eval (n + lam)

namespace SamplerFamily

/-- The marginal query of player `w` at the level `ℓ` and the index `n₀`, as data. -/
noncomputable def queryF (ℓ n₀ : ℕ) (w : Player) : PolyTimeFun BitStr Data :=
  cast (pair (const n₀) (pair (const (1 : ℕ)) (pair (const w) (pair (const ℓ)
    (pair (id BitStr) (const ([] : BitStr)))))))
    (fun z => encode (n₀, Sampler.Query.marginal w ℓ z)) (fun _ => rfl)

@[simp] theorem queryF_apply (ℓ n₀ : ℕ) (w : Player) (z : BitStr) :
    queryF ℓ n₀ w z = encode (n₀, Sampler.Query.marginal w ℓ z) := rfl

/-- The dimension query at the index `n₀`, as data. -/
def qdim (n₀ : ℕ) : Data := encode (n₀, Sampler.Query.dimension)

/-- A run of a sampler on a query is within its time bound. -/
theorem sampler_run_bounded {ℓ : ℕ} (S : Sampler ℓ) {n T k : ℕ} (hb : S.TimeBoundAt n T k)
    (q : Sampler.Query) {r : Data} {t : ℕ} (h : S.prog.Runs (encode (n, q)) r t) :
    ∃ t' ≤ T * ((encode q : Data).size + 1) ^ k, S.prog.Runs (encode (n, q)) r t' := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb (encode q)
  have h₀' : S.prog.Runs (encode (n, q)) r₀ t₀ := h₀
  obtain ⟨rfl, -⟩ := Eval.deterministic h₀' h
  exact ⟨t₀, ht₀, h₀'⟩

variable {ℓ : ℕ} (F : SamplerFamily ℓ) (n₀ : ℕ) (U : UniversalMachine) (Λ₀ : ℕ)
  (R : PolyTimeFun BitStr Prog)

/-! ## The sampler and its pieces -/

/-- The sampler of the input `z`: `S^{λ(z)}`. -/
noncomputable abbrev Sz (z : BitStr) : Sampler ℓ := F.sampler (lamz Λ₀ R z)

/-- The dimension of its questions at the index `n₀`. -/
noncomputable def dimz (z : BitStr) : ℕ := (F.Sz Λ₀ R z).dim n₀

/-- Player `w`'s question on the seed `r`, on the input `z`: the marginal of `S^{λ(z)}` at the
first `dimz z` bits of `r`. -/
noncomputable def qOf (w : Player) (z r : BitStr) : BitStr :=
  toBits (((F.Sz Λ₀ R z).cl n₀ w).eval
    (ofBits (F.dimz n₀ Λ₀ R z) (r.take (F.dimz n₀ Λ₀ R z))))

theorem qOf_length (w : Player) (z r : BitStr) :
    (F.qOf n₀ Λ₀ R w z r).length = F.dimz n₀ Λ₀ R z :=
  length_toBits _

/-- `(z, r) ↦ ComputeSampler(λ(z))`. -/
noncomputable def spF : PolyTimeFun (BitStr × BitStr) Prog :=
  F.samplerProg.comp ((lamF Λ₀).comp (R.comp fst))

theorem spF_apply (z r : BitStr) : F.spF Λ₀ R (z, r) = (F.Sz Λ₀ R z).prog := by
  show F.samplerProg (lamF Λ₀ (R z)) = _
  rw [lamF_apply, F.samplerProg_eq]
  rfl

/-- Stage 1: from `(z, r)`, the pair `(S, dimension)` to run and the state `(S, r)`. -/
noncomputable def A1 : PolyTimeFun (BitStr × BitStr) ((Prog × Data) × (Prog × BitStr)) :=
  pair (pair (F.spF Λ₀ R) (const (qdim n₀))) (pair (F.spF Λ₀ R) snd)

theorem A1_apply (z r : BitStr) :
    F.A1 n₀ Λ₀ R (z, r) = (((F.Sz Λ₀ R z).prog, qdim n₀), ((F.Sz Λ₀ R z).prog, r)) := by
  show ((F.spF Λ₀ R (z, r), qdim n₀), (F.spF Λ₀ R (z, r), r)) = _
  rw [spF_apply]

/-- Stage 2: from `((S, r), s)` with `s` in unary, the pair `(S, marginal A (r.take s))` to run
and the state `(S, r.take s)`. -/
noncomputable def A2 :
    PolyTimeFun ((Prog × BitStr) × Unary) ((Prog × Data) × (Prog × BitStr)) :=
  pair (pair (fst.comp fst) ((queryF ℓ n₀ .alice).comp (take.comp (pair (snd.comp fst) snd))))
    (pair (fst.comp fst) (take.comp (pair (snd.comp fst) snd)))

theorem A2_apply (sp : Prog) (r : BitStr) (u : Unary) :
    A2 (ℓ := ℓ) n₀ ((sp, r), u) =
      ((sp, encode (n₀, Sampler.Query.marginal .alice ℓ (r.take u.length))),
        (sp, r.take u.length)) := rfl

/-- Stage 3: from `((S, r'), x)`, the pair `(S, marginal B r')` to run and the state `x`. -/
noncomputable def A3 : PolyTimeFun ((Prog × BitStr) × BitStr) ((Prog × Data) × BitStr) :=
  pair (pair (fst.comp fst) ((queryF ℓ n₀ .bob).comp (snd.comp fst))) snd

theorem A3_apply (sp : Prog) (z' x : BitStr) :
    A3 (ℓ := ℓ) n₀ ((sp, z'), x) = ((sp, encode (n₀, Sampler.Query.marginal .bob ℓ z')), x) :=
  rfl

/-- **The sampler of the class verifier.** -/
noncomputable def sampProg : Prog :=
  seq (F.A1 n₀ Λ₀ R).code (seq (runUK U.univ) (seq unaryStage (seq (A2 (ℓ := ℓ) n₀).code
    (seq (runUK U.univ) (seq (A3 (ℓ := ℓ) n₀).code (runUK U.univ))))))

theorem sampProg_wellScoped : (F.sampProg n₀ U Λ₀ R).WellScoped 1 :=
  seq_wellScoped (F.A1 n₀ Λ₀ R).closed (seq_wellScoped (runUK_wellScoped U.closed)
    (seq_wellScoped unaryStage_wellScoped (seq_wellScoped (A2 (ℓ := ℓ) n₀).closed
      (seq_wellScoped (runUK_wellScoped U.closed) (seq_wellScoped (A3 (ℓ := ℓ) n₀).closed
        (runUK_wellScoped U.closed))))))

/-! ## The costs -/

/-- The family's bound `poly(n₀, λ)`, in the total input length `m`: bounds the dimension and the
times. -/
noncomputable def dimB (m : ℕ) : ℕ := F.bound.eval (n₀ + lamB Λ₀ R m)
/-- Stage 1's cost. -/
noncomputable def T1B (m : ℕ) : ℕ := (F.A1 n₀ Λ₀ R).timeBound.eval (4 * m + 3)
/-- The first universal call's cost. -/
noncomputable def R1B (m : ℕ) : ℕ :=
  2 * F.T1B n₀ Λ₀ R m + (4 * F.dimB n₀ Λ₀ R m + 1) +
    U.bound.eval (2 * F.T1B n₀ Λ₀ R m + F.dimB n₀ Λ₀ R m * (F.T1B n₀ Λ₀ R m + 1) ^ F.deg) + 8
/-- The conversion's cost. -/
noncomputable def UnB (m : ℕ) : ℕ :=
  F.R1B n₀ U Λ₀ R m + (4 * F.dimB n₀ Λ₀ R m + 1) + unB (F.dimB n₀ Λ₀ R m) + 5
/-- Stage 2's cost. -/
noncomputable def T2B (m : ℕ) : ℕ := (A2 (ℓ := ℓ) n₀).timeBound.eval (F.UnB n₀ U Λ₀ R m)
/-- The second universal call's cost. -/
noncomputable def R2B (m : ℕ) : ℕ :=
  2 * F.T2B n₀ U Λ₀ R m + (4 * F.dimB n₀ Λ₀ R m + 1) +
    U.bound.eval (2 * F.T2B n₀ U Λ₀ R m + F.dimB n₀ Λ₀ R m * (F.T2B n₀ U Λ₀ R m + 1) ^ F.deg) + 8
/-- Stage 3's cost. -/
noncomputable def T3B (m : ℕ) : ℕ := (A3 (ℓ := ℓ) n₀).timeBound.eval (F.R2B n₀ U Λ₀ R m)
/-- The third universal call's cost. -/
noncomputable def R3B (m : ℕ) : ℕ :=
  2 * F.T3B n₀ U Λ₀ R m + (4 * F.dimB n₀ Λ₀ R m + 1) +
    U.bound.eval (2 * F.T3B n₀ U Λ₀ R m + F.dimB n₀ Λ₀ R m * (F.T3B n₀ U Λ₀ R m + 1) ^ F.deg) + 8
/-- **The sampler's cost**, in the total input length. -/
noncomputable def sampB (m : ℕ) : ℕ :=
  2 * (F.T1B n₀ Λ₀ R m + F.R1B n₀ U Λ₀ R m + F.UnB n₀ U Λ₀ R m + F.T2B n₀ U Λ₀ R m +
    F.R2B n₀ U Λ₀ R m + F.T3B n₀ U Λ₀ R m) + F.R3B n₀ U Λ₀ R m + 18

theorem dimz_le (z : BitStr) (m : ℕ) (hm : z.length ≤ m) :
    F.dimz n₀ Λ₀ R z ≤ F.dimB n₀ Λ₀ R m :=
  (F.sampler_dim _ _).trans (polynomial_eval_mono _ (by have := lamz_le Λ₀ R z m hm; omega))

/-- **The sampler's run**: on `(z, r)` with `r` at least `dimz z` long, it halts with the
question pair of the seed within `sampB (|z| + |r|)`. -/
theorem sampProg_runs (hℓ : 1 ≤ ℓ) (z r : BitStr) (hd : F.dimz n₀ Λ₀ R z ≤ r.length) :
    ∃ t, t ≤ F.sampB n₀ U Λ₀ R (z.length + r.length) ∧
      (F.sampProg n₀ U Λ₀ R).Runs (encode (z, r))
        (encode (F.qOf n₀ Λ₀ R .alice z r, F.qOf n₀ Λ₀ R .bob z r)) t := by
  set S := F.Sz Λ₀ R z with hS
  set d := F.dimz n₀ Λ₀ R z with hd_def
  set m := z.length + r.length with hm
  set z' := r.take d with hz'
  have hz'l : z'.length = d := by rw [hz', List.length_take]; omega
  have hbS : S.TimeBoundAt n₀ (F.bound.eval (n₀ + lamz Λ₀ R z)) F.deg :=
    F.sampler_time _ n₀
  have hdimB : F.bound.eval (n₀ + lamz Λ₀ R z) ≤ F.dimB n₀ Λ₀ R m :=
    polynomial_eval_mono _ (by have := lamz_le Λ₀ R z m (by omega); omega)
  have hdB : d ≤ F.dimB n₀ Λ₀ R m := F.dimz_le n₀ Λ₀ R z m (by omega)
  have hed : esize d ≤ 4 * F.dimB n₀ Λ₀ R m + 1 := (esize_nat_le_self d).trans (by omega)
  have hed' : (encode d : Data).size = esize d := rfl
  -- stage 1
  obtain ⟨t₁, ht₁, h₁⟩ := (F.A1 n₀ Λ₀ R).computes (z, r)
  rw [A1_apply, ← hS] at h₁
  have hT1 : t₁ ≤ F.T1B n₀ Λ₀ R m := by
    refine ht₁.trans (polynomial_eval_mono _ ?_)
    have := esize_bitStr_le z; have := esize_bitStr_le r
    simp only [esize_prod]; omega
  have hy₁ := h₁.size_le
  -- the dimension query
  obtain ⟨t₀, hdim⟩ := S.runs_dimension n₀
  obtain ⟨td, htd, hdim'⟩ := sampler_run_bounded S hbS _ hdim
  obtain ⟨tu₁, htu₁, hu₁⟩ := U.time_le S.prog (qdim n₀) (encode d) td hdim'
  obtain ⟨tk₁, htk₁, hk₁⟩ := runUK_runs U.closed (B := encode (S.prog, r)) hu₁
  have hk₁' : (runUK U.univ).Runs (encode ((S.prog, qdim n₀), (S.prog, r)))
    (encode ((S.prog, r), d)) tk₁ := hk₁
  have hy₂' := hk₁'.size_le
  have hsz₁ : (encode ((S.prog, qdim n₀), (S.prog, r)) : Data).size =
      (encode (S.prog, qdim n₀) : Data).size + (encode (S.prog, r) : Data).size + 1 := rfl
  have hsz₁' : (encode (S.prog, qdim n₀) : Data).size =
      esize S.prog + (qdim n₀).size + 1 := rfl
  have hqd : (encode Sampler.Query.dimension : Data).size ≤ (qdim n₀).size := by
    show _ ≤ (Data.cons (encode n₀) (encode Sampler.Query.dimension)).size
    simp only [Data.size_cons]; omega
  have hsim₁ : td ≤ F.dimB n₀ Λ₀ R m * (F.T1B n₀ Λ₀ R m + 1) ^ F.deg :=
    htd.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hq₁ : (Data.cons (encode S.prog) (qdim n₀)).size = esize S.prog + (qdim n₀).size + 1 := rfl
  have hR1 : tk₁ ≤ F.R1B n₀ U Λ₀ R m := by
    have hu := htu₁.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (qdim n₀).size + td ≤
        2 * F.T1B n₀ Λ₀ R m + F.dimB n₀ Λ₀ R m * (F.T1B n₀ Λ₀ R m + 1) ^ F.deg by omega))
    unfold SamplerFamily.R1B; omega
  have hy₂ := hk₁.size_le
  -- the conversion
  obtain ⟨tn, htn, hn⟩ := unaryStage_runs (encode (S.prog, r)) d
  have e_un : (encode ((S.prog, r), unary d) : Data) =
      .cons (encode (S.prog, r)) (Data.ofNat d) := by
    show Data.cons _ (encode (unary d)) = _
    rw [encode_unary]
  have hn' : unaryStage.Runs (encode ((S.prog, r), d)) (encode ((S.prog, r), unary d)) tn := by
    rw [e_un]; exact hn
  have hy₃' := hn'.size_le
  have hUn : tn ≤ F.UnB n₀ U Λ₀ R m := by
    have hsz₂ : (encode ((S.prog, r), d) : Data).size =
      (encode (S.prog, r) : Data).size + esize d + 1 := rfl
    have := unCost_le hdB
    unfold SamplerFamily.UnB; omega
  have hy₃ := hn.size_le
  -- stage 2
  obtain ⟨t₂, ht₂, h₂⟩ := (A2 (ℓ := ℓ) n₀).computes ((S.prog, r), unary d)
  rw [A2_apply, length_unary, ← hz'] at h₂
  have hT2 : t₂ ≤ F.T2B n₀ U Λ₀ R m := by
    refine ht₂.trans (polynomial_eval_mono _ ?_)
    have : esize ((S.prog, r), unary d) = (encode ((S.prog, r), unary d) : Data).size := rfl
    rw [this, e_un]; omega
  have hy₄ := h₂.size_le
  -- Alice's marginal
  obtain ⟨tA, hA⟩ := S.runs_marginal n₀ .alice ℓ z' hℓ le_rfl hz'l
  rw [CLFun.truncate_self] at hA
  obtain ⟨tA', htA', hA'⟩ := sampler_run_bounded S hbS _ hA
  obtain ⟨tu₂, htu₂, hu₂⟩ := U.time_le S.prog _ _ tA' hA'
  have hu₂' : U.univ.Runs
    (.cons (encode S.prog) (encode (n₀, Sampler.Query.marginal .alice ℓ z')))
    (encode (F.qOf n₀ Λ₀ R .alice z r)) tu₂ := hu₂
  obtain ⟨tk₂, htk₂, hk₂⟩ := runUK_runs U.closed (B := encode (S.prog, z')) hu₂'
  have hk₂' : (runUK U.univ).Runs
      (encode ((S.prog, encode (n₀, Sampler.Query.marginal .alice ℓ z')), (S.prog, z')))
      (encode ((S.prog, z'), F.qOf n₀ Λ₀ R .alice z r)) tk₂ := hk₂
  have hy₅' := hk₂'.size_le
  have hsz₄ : (encode ((S.prog, encode (n₀, Sampler.Query.marginal .alice ℓ z')),
      (S.prog, z')) : Data).size = (esize S.prog +
        (encode (n₀, Sampler.Query.marginal .alice ℓ z') : Data).size + 1) +
        (encode (S.prog, z') : Data).size + 1 := rfl
  have hqA : (encode (Sampler.Query.marginal .alice ℓ z') : Data).size ≤
      (encode (n₀, Sampler.Query.marginal .alice ℓ z') : Data).size := by
    show _ ≤ (Data.cons (encode n₀) (encode (Sampler.Query.marginal .alice ℓ z'))).size
    simp only [Data.size_cons]; omega
  have hsim₂ : tA' ≤ F.dimB n₀ Λ₀ R m * (F.T2B n₀ U Λ₀ R m + 1) ^ F.deg :=
    htA'.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hex : esize (F.qOf n₀ Λ₀ R .alice z r) ≤ 4 * F.dimB n₀ Λ₀ R m + 1 := by
    have := esize_bitStr_le (F.qOf n₀ Λ₀ R .alice z r)
    have : (F.qOf n₀ Λ₀ R .alice z r).length = d := length_toBits _
    omega
  have hexe : (encode (F.qOf n₀ Λ₀ R .alice z r) : Data).size =
    esize (F.qOf n₀ Λ₀ R .alice z r) := rfl
  have hq₂ : (Data.cons (encode S.prog) (encode (n₀, Sampler.Query.marginal .alice ℓ z'))).size
    = esize S.prog + (encode (n₀, Sampler.Query.marginal .alice ℓ z') : Data).size + 1 := rfl
  have hR2 : tk₂ ≤ F.R2B n₀ U Λ₀ R m := by
    have hu := htu₂.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (encode (n₀, Sampler.Query.marginal .alice ℓ z') : Data).size + tA'
        ≤ 2 * F.T2B n₀ U Λ₀ R m + F.dimB n₀ Λ₀ R m * (F.T2B n₀ U Λ₀ R m + 1) ^ F.deg by omega))
    have : (encode (F.qOf n₀ Λ₀ R .alice z r) : Data).size = esize (F.qOf n₀ Λ₀ R .alice z r) := rfl
    unfold SamplerFamily.R2B; omega
  have hy₅ := hk₂.size_le
  -- stage 3
  obtain ⟨t₃, ht₃, h₃⟩ := (A3 (ℓ := ℓ) n₀).computes ((S.prog, z'), F.qOf n₀ Λ₀ R .alice z r)
  rw [A3_apply] at h₃
  have hT3 : t₃ ≤ F.T3B n₀ U Λ₀ R m := by
    refine ht₃.trans (polynomial_eval_mono _ ?_)
    have : esize ((S.prog, z'), F.qOf n₀ Λ₀ R .alice z r) =
      (encode ((S.prog, z'), F.qOf n₀ Λ₀ R .alice z r) : Data).size := rfl
    rw [this]; omega
  have hy₆ := h₃.size_le
  -- Bob's marginal
  obtain ⟨tB, hB⟩ := S.runs_marginal n₀ .bob ℓ z' hℓ le_rfl hz'l
  rw [CLFun.truncate_self] at hB
  obtain ⟨tB', htB', hB'⟩ := sampler_run_bounded S hbS _ hB
  obtain ⟨tu₃, htu₃, hu₃⟩ := U.time_le S.prog _ _ tB' hB'
  have hu₃' : U.univ.Runs (.cons (encode S.prog) (encode (n₀, Sampler.Query.marginal .bob ℓ z')))
    (encode (F.qOf n₀ Λ₀ R .bob z r)) tu₃ := hu₃
  obtain ⟨tk₃, htk₃, hk₃⟩ :=
    runUK_runs U.closed (B := encode (F.qOf n₀ Λ₀ R .alice z r)) hu₃'
  have hk₃' : (runUK U.univ).Runs
      (encode ((S.prog, encode (n₀, Sampler.Query.marginal .bob ℓ z')),
        F.qOf n₀ Λ₀ R .alice z r))
      (encode (F.qOf n₀ Λ₀ R .alice z r, F.qOf n₀ Λ₀ R .bob z r)) tk₃ := hk₃
  have hsz₆ : (encode ((S.prog, encode (n₀, Sampler.Query.marginal .bob ℓ z')),
      F.qOf n₀ Λ₀ R .alice z r) : Data).size = (esize S.prog +
        (encode (n₀, Sampler.Query.marginal .bob ℓ z') : Data).size + 1) +
        esize (F.qOf n₀ Λ₀ R .alice z r) + 1 := rfl
  have hqB : (encode (Sampler.Query.marginal .bob ℓ z') : Data).size ≤
      (encode (n₀, Sampler.Query.marginal .bob ℓ z') : Data).size := by
    show _ ≤ (Data.cons (encode n₀) (encode (Sampler.Query.marginal .bob ℓ z'))).size
    simp only [Data.size_cons]; omega
  have hsim₃ : tB' ≤ F.dimB n₀ Λ₀ R m * (F.T3B n₀ U Λ₀ R m + 1) ^ F.deg :=
    htB'.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hey : esize (F.qOf n₀ Λ₀ R .bob z r) ≤ 4 * F.dimB n₀ Λ₀ R m + 1 := by
    have := esize_bitStr_le (F.qOf n₀ Λ₀ R .bob z r)
    have : (F.qOf n₀ Λ₀ R .bob z r).length = d := length_toBits _
    omega
  have heye : (encode (F.qOf n₀ Λ₀ R .bob z r) : Data).size = esize (F.qOf n₀ Λ₀ R .bob z r) := rfl
  have hq₃ : (Data.cons (encode S.prog) (encode (n₀, Sampler.Query.marginal .bob ℓ z'))).size
    = esize S.prog + (encode (n₀, Sampler.Query.marginal .bob ℓ z') : Data).size + 1 := rfl
  have hR3 : tk₃ ≤ F.R3B n₀ U Λ₀ R m := by
    have hu := htu₃.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (encode (n₀, Sampler.Query.marginal .bob ℓ z') : Data).size + tB'
        ≤ 2 * F.T3B n₀ U Λ₀ R m + F.dimB n₀ Λ₀ R m * (F.T3B n₀ U Λ₀ R m + 1) ^ F.deg by omega))
    have : (encode (F.qOf n₀ Λ₀ R .bob z r) : Data).size = esize (F.qOf n₀ Λ₀ R .bob z r) := rfl
    unfold SamplerFamily.R3B; omega
  -- assemble
  have w3 := runUK_wellScoped U.closed
  have w23 := seq_wellScoped (A3 (ℓ := ℓ) n₀).closed w3
  have wk2 := seq_wellScoped (runUK_wellScoped U.closed) w23
  have wc2 := seq_wellScoped (A2 (ℓ := ℓ) n₀).closed wk2
  have wun := seq_wellScoped unaryStage_wellScoped wc2
  have wk1 := seq_wellScoped (runUK_wellScoped U.closed) wun
  have hrun := seq_runs wk1 h₁ (seq_runs wun hk₁' (seq_runs wc2 hn' (seq_runs wk2 h₂
    (seq_runs w23 hk₂' (seq_runs w3 h₃ hk₃')))))
  refine ⟨_, ?_, hrun⟩
  unfold SamplerFamily.sampB
  omega

/-! ## The bounds are polynomial -/

theorem polyBounded_dimB : PolyBounded (F.dimB n₀ Λ₀ R) :=
  PolyBounded.eval _ ((PolyBounded.const n₀).add (polyBounded_lamB Λ₀ R))

theorem polyBounded_T1B : PolyBounded (F.T1B n₀ Λ₀ R) :=
  PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 3)

/-- The shape of the three universal calls' bounds. -/
theorem polyBounded_call {T : ℕ → ℕ} (hT : PolyBounded T) :
    PolyBounded fun m => 2 * T m + (4 * F.dimB n₀ Λ₀ R m + 1) +
      U.bound.eval (2 * T m + F.dimB n₀ Λ₀ R m * (T m + 1) ^ F.deg) + 8 :=
  have hd := F.polyBounded_dimB n₀ Λ₀ R
  (((hT.const_mul 2).add ((hd.const_mul 4).add_const 1)).add
    (PolyBounded.eval _ ((hT.const_mul 2).add (hd.mul ((hT.add_const 1).pow F.deg))))).add_const 8

theorem polyBounded_R1B : PolyBounded (F.R1B n₀ U Λ₀ R) :=
  F.polyBounded_call n₀ U Λ₀ R (F.polyBounded_T1B n₀ Λ₀ R)

theorem polyBounded_unB_dimB : PolyBounded fun m => unB (F.dimB n₀ Λ₀ R m) :=
  have hd := F.polyBounded_dimB n₀ Λ₀ R
  (hd.add_const 2).mul ((((hd.add_const 1).mul ((hd.const_mul 4).add_const 14)).add
    (((hd.const_mul 4).add_const 1).const_mul 7)).add ((hd.const_mul 8).add_const 90))

theorem polyBounded_UnB : PolyBounded (F.UnB n₀ U Λ₀ R) :=
  (((F.polyBounded_R1B n₀ U Λ₀ R).add
    (((F.polyBounded_dimB n₀ Λ₀ R).const_mul 4).add_const 1)).add
    (F.polyBounded_unB_dimB n₀ Λ₀ R)).add_const 5

theorem polyBounded_T2B : PolyBounded (F.T2B n₀ U Λ₀ R) :=
  PolyBounded.eval _ (F.polyBounded_UnB n₀ U Λ₀ R)

theorem polyBounded_R2B : PolyBounded (F.R2B n₀ U Λ₀ R) :=
  F.polyBounded_call n₀ U Λ₀ R (F.polyBounded_T2B n₀ U Λ₀ R)

theorem polyBounded_T3B : PolyBounded (F.T3B n₀ U Λ₀ R) :=
  PolyBounded.eval _ (F.polyBounded_R2B n₀ U Λ₀ R)

theorem polyBounded_R3B : PolyBounded (F.R3B n₀ U Λ₀ R) :=
  F.polyBounded_call n₀ U Λ₀ R (F.polyBounded_T3B n₀ U Λ₀ R)

theorem polyBounded_sampB : PolyBounded (F.sampB n₀ U Λ₀ R) :=
  ((((((((F.polyBounded_T1B n₀ Λ₀ R).add (F.polyBounded_R1B n₀ U Λ₀ R)).add
    (F.polyBounded_UnB n₀ U Λ₀ R)).add (F.polyBounded_T2B n₀ U Λ₀ R)).add
      (F.polyBounded_R2B n₀ U Λ₀ R)).add (F.polyBounded_T3B n₀ U Λ₀ R)).const_mul 2).add
        (F.polyBounded_R3B n₀ U Λ₀ R)).add_const 18

/-! ## At every level -/

/-- **The class sampler**, at every level: `sampProg` at the levels `ℓ ≥ 1`, and at level `0`,
where the questions are empty, the program outputting the empty pair. -/
noncomputable def classSampler : Prog :=
  if 1 ≤ ℓ then F.sampProg n₀ U Λ₀ R else .const (encode (([] : BitStr), ([] : BitStr)))

theorem classSampler_wellScoped : (F.classSampler n₀ U Λ₀ R).WellScoped 1 := by
  unfold classSampler
  split_ifs
  · exact F.sampProg_wellScoped n₀ U Λ₀ R
  · trivial

/-- The class sampler's cost, in the total input length. -/
noncomputable def classB (m : ℕ) : ℕ :=
  F.sampB n₀ U Λ₀ R m + (encode (([] : BitStr), ([] : BitStr)) : Data).size

/-- **The class sampler's run**, at every level: on `(z, r)` with `r` at least `dimz z` long, it
halts with the question pair of the seed within `classB (|z| + |r|)`. -/
theorem classSampler_runs (z r : BitStr) (hd : F.dimz n₀ Λ₀ R z ≤ r.length) :
    ∃ t, t ≤ F.classB n₀ U Λ₀ R (z.length + r.length) ∧
      (F.classSampler n₀ U Λ₀ R).Runs (encode (z, r))
        (encode (F.qOf n₀ Λ₀ R .alice z r, F.qOf n₀ Λ₀ R .bob z r)) t := by
  unfold classSampler classB
  split_ifs with hℓ
  · obtain ⟨t, ht, h⟩ := F.sampProg_runs n₀ U Λ₀ R hℓ z r hd
    exact ⟨t, by omega, h⟩
  · obtain rfl : ℓ = 0 := by omega
    have h0 : F.dimz n₀ Λ₀ R z = 0 := Sampler.dim_eq_zero_of_level_zero _ _
    have hq : ∀ w, F.qOf n₀ Λ₀ R w z r = [] := fun w =>
      List.eq_nil_of_length_eq_zero ((F.qOf_length n₀ Λ₀ R w z r).trans h0)
    rw [hq, hq]
    exact ⟨_, by omega, Eval.const _ _⟩

theorem polyBounded_classB : PolyBounded (F.classB n₀ U Λ₀ R) :=
  (F.polyBounded_sampB n₀ U Λ₀ R).add_const _

/-! ## The question distribution -/

section Game

variable (V : PolyVerifier)

/-- The questions of `S^{λ(z)}` at the index `n₀`. -/
abbrev Qz (z : BitStr) : Type := Fin ((F.Sz Λ₀ R z).dim n₀) → 𝔽₂

/-- **`V` samples `S^{λ(z)}` at `n₀`**: on every input `z` and every seed `r` of length `B z`, its
sampler halts within `P(|z| + |r|)` with the question pair of the seed. -/
def Samples : Prop :=
  ∀ z r : BitStr, r.length = V.B z → ∃ t, t ≤ V.bound.eval (z.length + r.length) ∧
    V.sampler.Runs (encode (z, r)) (encode (F.qOf n₀ Λ₀ R .alice z r, F.qOf n₀ Λ₀ R .bob z r)) t

variable {V}

theorem dimz_le_B (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m) (z : BitStr) :
    F.dimz n₀ Λ₀ R z ≤ V.B z :=
  (F.dimz_le n₀ Λ₀ R z z.length le_rfl).trans (hdim _)

/-- A sampler running as the class sampler does, within a bound below `P`, samples. -/
theorem samples_of_runs (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m) {p : Prog}
    {T : ℕ → ℕ} (hp : ∀ z r : BitStr, F.dimz n₀ Λ₀ R z ≤ r.length → ∃ t,
      t ≤ T (z.length + r.length) ∧
        p.Runs (encode (z, r)) (encode (F.qOf n₀ Λ₀ R .alice z r, F.qOf n₀ Λ₀ R .bob z r)) t)
    (hS : V.sampler = p) (hT : ∀ m, T m ≤ V.bound.eval m) : F.Samples n₀ Λ₀ R V := by
  intro z r hr
  obtain ⟨t, ht, h⟩ := hp z r (by rw [hr]; exact F.dimz_le_B n₀ Λ₀ R hdim z)
  exact ⟨t, ht.trans (hT _), hS ▸ h⟩

variable {F n₀ Λ₀ R} in
/-- A sampler that samples meets the sampler's clause of efficiency. -/
theorem Samples.samplerRuns (hS : F.Samples n₀ Λ₀ R V)
    (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m) (z : BitStr) : V.SamplerRuns z := by
  intro r hr
  obtain ⟨t, ht, h⟩ := hS z r hr
  have hd := F.dimz_le_B n₀ Λ₀ R hdim z
  exact ⟨_, _, t, ht, by rw [qOf_length]; exact hd, by rw [qOf_length]; exact hd, h⟩

/-- The question pair of a seed of the right length. -/
theorem questions_eq (hS : F.Samples n₀ Λ₀ R V) (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m)
    (z r : BitStr) (hr : r.length = V.B z) :
    V.questions z r =
      (⟨F.qOf n₀ Λ₀ R .alice z r, by rw [qOf_length]; exact F.dimz_le_B n₀ Λ₀ R hdim z⟩,
        ⟨F.qOf n₀ Λ₀ R .bob z r, by rw [qOf_length]; exact F.dimz_le_B n₀ Λ₀ R hdim z⟩) := by
  obtain ⟨x, y, t, -, hrun, hx, hy⟩ := V.questions_eq_of_samplerRuns (hS.samplerRuns hdim z) hr
  obtain ⟨t', -, hrun'⟩ := hS z r hr
  obtain ⟨he, -⟩ := Eval.deterministic hrun hrun'
  have he' := encode_injective he
  simp only [Prod.mk.injEq] at he'
  exact Prod.ext (Subtype.ext (hx.trans he'.1)) (Subtype.ext (hy.trans he'.2))

/-- The embedding of the questions of `S^{λ(z)}` into the strings of length at most `B z`. -/
noncomputable def qEmb (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m) (z : BitStr) :
    F.Qz n₀ Λ₀ R z ↪ Verifier.Answers (V.B z) where
  toFun v := ⟨toBits v, by rw [length_toBits]; exact F.dimz_le_B n₀ Λ₀ R hdim z⟩
  inj' v w h := by
    have := congrArg Subtype.val h
    simp only at this
    rw [← ofBits_toBits v, ← ofBits_toBits w, this]

@[simp] theorem qEmb_apply (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m) (z : BitStr)
    (v : F.Qz n₀ Λ₀ R z) : (F.qEmb n₀ Λ₀ R hdim z v).1 = toBits v := rfl

/-- The number of seeds producing a given question pair: a count over `𝔽₂^{s}` times
`2 ^ (B - s)`. -/
theorem seedCount_eq (hS : F.Samples n₀ Λ₀ R V) (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m)
    (z : BitStr) (x y : F.Qz n₀ Λ₀ R z) :
    V.seedCount z (F.qEmb n₀ Λ₀ R hdim z x) (F.qEmb n₀ Λ₀ R hdim z y) =
      (Finset.univ.filter fun v : F.Qz n₀ Λ₀ R z =>
        ((F.Sz Λ₀ R z).cl n₀ .alice).eval v = x ∧
          ((F.Sz Λ₀ R z).cl n₀ .bob).eval v = y).card *
        2 ^ (V.B z - F.dimz n₀ Λ₀ R z) := by
  classical
  set d := F.dimz n₀ Λ₀ R z with hd
  set B := V.B z with hB
  have hdB : d ≤ B := F.dimz_le_B n₀ Λ₀ R hdim z
  set L := ((F.Sz Λ₀ R z).cl n₀ .alice).eval
  set Rb := ((F.Sz Λ₀ R z).cl n₀ .bob).eval
  -- the seeds whose questions are `(x, y)` are those whose prefix maps to `(x, y)`
  have key : ∀ v w : F.Qz n₀ Λ₀ R z, toBits v = toBits w ↔ v = w :=
    fun v w => ⟨fun h => by rw [← ofBits_toBits v, h, ofBits_toBits], fun h => by rw [h]⟩
  have h1 : V.seedCount z (F.qEmb n₀ Λ₀ R hdim z x) (F.qEmb n₀ Λ₀ R hdim z y)
      = ((Data.bitStrsOfLen B).filter fun r =>
          decide (L (ofBits d (r.take d)) = x ∧ Rb (ofBits d (r.take d)) = y)).length := by
    unfold PolyVerifier.seedCount
    apply congrArg List.length
    refine List.filter_congr fun r hr => ?_
    have hr' : r.length = B := (Data.mem_bitStrsOfLen _ _).1 hr
    rw [F.questions_eq n₀ Λ₀ R hS hdim z r hr', decide_eq_decide, Prod.ext_iff]
    refine (and_congr Subtype.ext_iff Subtype.ext_iff).trans ?_
    show (toBits (L (ofBits d (r.take d))) = toBits x ∧
        toBits (Rb (ofBits d (r.take d))) = toBits y) ↔ _
    rw [key, key]
  rw [h1]
  have h2 := Data.length_filter_take (fun s => decide (L (ofBits d s) = x ∧ Rb (ofBits d s) = y))
    d (B - d)
  rw [Nat.add_sub_cancel' hdB] at h2
  rw [h2, show ((Data.bitStrsOfLen d).filter fun s =>
      decide (L (ofBits d s) = x ∧ Rb (ofBits d s) = y)).length =
      (Finset.univ.filter fun v => decide (L v = x ∧ Rb v = y) = true).card from
      Verifier.length_filter_bitStrsOfLen (s := d) (fun v => decide (L v = x ∧ Rb v = y))]
  congr 1

/-- **The distribution of the game, on the embedded questions, is the sampler's.** -/
theorem game_μ_qEmb (hS : F.Samples n₀ Λ₀ R V) (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m)
    (z : BitStr) (x y : F.Qz n₀ Λ₀ R z) :
    (V.game z).μ (F.qEmb n₀ Λ₀ R hdim z x) (F.qEmb n₀ Λ₀ R hdim z y) =
      (F.Sz Λ₀ R z).dist n₀ x y := by
  classical
  rw [PolyVerifier.game_μ, F.seedCount_eq n₀ Λ₀ R hS hdim, Sampler.dist, clDist]
  have hdB := F.dimz_le_B n₀ Λ₀ R hdim z
  have hcard : (Fintype.card (F.Qz n₀ Λ₀ R z) : ℝ) = 2 ^ F.dimz n₀ Λ₀ R z := by
    show (Fintype.card (Fin (F.dimz n₀ Λ₀ R z) → ZMod 2) : ℝ) = _
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    rfl
  have h2B : (2 : ℝ) ^ V.B z = 2 ^ F.dimz n₀ Λ₀ R z * 2 ^ (V.B z - F.dimz n₀ Λ₀ R z) := by
    rw [← pow_add, Nat.add_sub_cancel' hdB]
  rw [hcard, h2B]
  push_cast
  field_simp

/-- **The distribution of the game is supported on the embedded questions.** -/
theorem game_support (hS : F.Samples n₀ Λ₀ R V) (hdim : ∀ m, F.dimB n₀ Λ₀ R m ≤ V.bound.eval m)
    (z : BitStr) (x' y' : Verifier.Answers (V.B z)) (h : (V.game z).μ x' y' ≠ 0) :
    (∃ x, F.qEmb n₀ Λ₀ R hdim z x = x') ∧ ∃ y, F.qEmb n₀ Λ₀ R hdim z y = y' := by
  classical
  rw [PolyVerifier.game_μ] at h
  have hc : V.seedCount z x' y' ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  unfold PolyVerifier.seedCount at hc
  have hne : ((Data.bitStrsOfLen (V.B z)).filter fun r =>
      decide (V.questions z r = (x', y'))) ≠ [] :=
    fun h0 => hc (by rw [h0]; rfl)
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hr, hq⟩ := List.mem_filter.1 hr
  have hq := of_decide_eq_true hq
  have hr' : r.length = V.B z := (Data.mem_bitStrsOfLen _ _).1 hr
  rw [F.questions_eq n₀ Λ₀ R hS hdim z r hr'] at hq
  obtain ⟨hq1, hq2⟩ := Prod.ext_iff.1 hq
  exact ⟨⟨((F.Sz Λ₀ R z).cl n₀ .alice).eval
      (ofBits (F.dimz n₀ Λ₀ R z) (r.take (F.dimz n₀ Λ₀ R z))), hq1⟩,
    ⟨((F.Sz Λ₀ R z).cl n₀ .bob).eval
      (ofBits (F.dimz n₀ Λ₀ R z) (r.take (F.dimz n₀ Λ₀ R z))), hq2⟩⟩

end Game

end SamplerFamily

end MIPRE.Halting

namespace MIPRE

/-- The compressed samplers of a gap compression. -/
def GapCompression.samplerFamily (G : GapCompression) : Halting.SamplerFamily 7 :=
  ⟨G.sampler, G.samplerProg, G.samplerProg_eq, G.bound, G.deg, G.sampler_time, G.sampler_dim⟩

end MIPRE

end
