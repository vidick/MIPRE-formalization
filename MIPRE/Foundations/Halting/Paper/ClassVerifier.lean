/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Paper.Main
public import MIPRE.Foundations.Halting.Paper.Build
public import MIPRE.Foundations.ClassMIPStar

@[expose] public section

/-!
# The class verifier of the polynomial-time halting reduction

The two programs of the `PolyVerifier` (`def:mipstar`) that puts an r.e. language `L` in the
paper's class `MIP*_{1,1/2}(2,1)`, for a polynomial-time reduction `R` of `L` to halting on the
empty input (`Cost.exists_polyTime_reduction`): on input `z` they play the game of
`𝒱^halt (R z) λ(z)` at the fixed level `C` (`Paper/Main.lean`), with
`λ(z) = Λ₀ + 4|R z|` the parameter of `lem:lambda`.

* **The sampler** `sampProg`, on `(z, r)`: computes `M = R z`, `λ(z)` and the compressed
  sampler's program `S = ComputeSampler(λ(z))` (`A1`); asks `S` its dimension `s = s(C)` through
  the universal machine (`runUK`); converts `s` to unary (`unaryStage`); takes the first `s`
  bits `r'` of the seed and asks `S` Alice's marginal `L^A(r')` (`A2`, `runUK`); then Bob's
  (`A3`, `runUK`). Its output is the question pair of `𝒱^halt` at the point `r'`
  (`sampProg_runs`), so that the uniform seed of length `B ≥ s` pushes forward to the
  compressed sampler's distribution.
* **The decider** `decProg`, on `(z, x, y, a, b)`: computes `M`, `λ(z)` and the description of
  `𝒱^halt`'s decider (`wrapCore` around `dec M λ(z)`, `decBuild`), rejects if `a` or `b` is
  longer than the cutoff `2 ^ (K + deg · |λ(z)|)` (`cutF`, at least the compressor's answer
  bound `poly(C, λ(z))` by `exists_cut_ge`), and otherwise runs the description on
  `(C, x, y, a, b)` through the universal machine (`runU`). It accepts exactly when both
  answers are within the cutoff and `𝒱^halt`'s decider accepts (`decProg_accepts`).

The costs are bounded by explicit expressions in the total input length (`sampB`, `decB`),
polynomially bounded (`polyBounded_sampB`, `polyBounded_decB`); `Paper/ClassMain.lean` chooses
the verifier's polynomial above them and proves the game's value.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun CL

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)

/-! ## The parameter, the sampler and the pieces -/

/-- The parameter of the input `z`: `Λ₀ + 4|R z|`. -/
def lamz (z : BitStr) : ℕ := Λ₀ + 4 * esize (R z)

/-- The compressed sampler of the input `z`. -/
noncomputable abbrev Sz (z : BitStr) : Sampler 7 := G.sampler (lamz Λ₀ R z)

/-- The dimension of its questions at the fixed level. -/
noncomputable def dimz (z : BitStr) : ℕ := (Sz G Λ₀ R z).dim (C G)

/-- Player `w`'s question on the seed `r`, on the input `z`: the marginal of the compressed
sampler at the first `dimz z` bits of `r`. -/
noncomputable def qOf (w : Player) (z r : BitStr) : BitStr :=
  toBits (((Sz G Λ₀ R z).cl (C G) w).eval
    (ofBits (dimz G Λ₀ R z) (r.take (dimz G Λ₀ R z))))

/-- `(z, r) ↦ ComputeSampler(λ(z))`. -/
noncomputable def spF : PolyTimeFun (BitStr × BitStr) Prog :=
  G.samplerProg.comp ((lamF Λ₀).comp (R.comp fst))

theorem spF_apply (z r : BitStr) : spF G Λ₀ R (z, r) = (Sz G Λ₀ R z).prog := by
  show G.samplerProg (lamF Λ₀ (R z)) = _
  rw [lamF_apply, G.samplerProg_eq]
  rfl

/-- The marginal query of player `w` at the fixed level, as data. -/
noncomputable def queryF (w : Player) : PolyTimeFun BitStr Data :=
  cast (pair (const (C G)) (pair (const (1 : ℕ)) (pair (const w) (pair (const (7 : ℕ))
    (pair (id BitStr) (const ([] : BitStr)))))))
    (fun z => encode (C G, Sampler.Query.marginal w 7 z)) (fun _ => rfl)

@[simp] theorem queryF_apply (w : Player) (z : BitStr) :
    queryF G w z = encode (C G, Sampler.Query.marginal w 7 z) := rfl

/-- The dimension query at the fixed level, as data. -/
def qdim : Data := encode (C G, Sampler.Query.dimension)

/-- Stage 1: from `(z, r)`, the pair `(S, dimension)` to run and the state `(S, r)`. -/
noncomputable def A1 : PolyTimeFun (BitStr × BitStr) ((Prog × Data) × (Prog × BitStr)) :=
  pair (pair (spF G Λ₀ R) (const (qdim G))) (pair (spF G Λ₀ R) snd)

theorem A1_apply (z r : BitStr) :
    A1 G Λ₀ R (z, r) = (((Sz G Λ₀ R z).prog, qdim G), ((Sz G Λ₀ R z).prog, r)) := by
  show ((spF G Λ₀ R (z, r), qdim G), (spF G Λ₀ R (z, r), r)) = _
  rw [spF_apply]

/-- Stage 2: from `((S, r), s)` with `s` in unary, the pair `(S, marginal A (r.take s))` to
run and the state `(S, r.take s)`. -/
noncomputable def A2 :
    PolyTimeFun ((Prog × BitStr) × Unary) ((Prog × Data) × (Prog × BitStr)) :=
  pair (pair (fst.comp fst) ((queryF G .alice).comp (take.comp (pair (snd.comp fst) snd))))
    (pair (fst.comp fst) (take.comp (pair (snd.comp fst) snd)))

theorem A2_apply (sp : Prog) (r : BitStr) (u : Unary) :
    A2 G ((sp, r), u) = ((sp, encode (C G, Sampler.Query.marginal .alice 7 (r.take u.length))),
      (sp, r.take u.length)) := rfl

/-- Stage 3: from `((S, r'), x)`, the pair `(S, marginal B r')` to run and the state `x`. -/
noncomputable def A3 : PolyTimeFun ((Prog × BitStr) × BitStr) ((Prog × Data) × BitStr) :=
  pair (pair (fst.comp fst) ((queryF G .bob).comp (snd.comp fst))) snd

theorem A3_apply (sp : Prog) (z' x : BitStr) :
    A3 G ((sp, z'), x) = ((sp, encode (C G, Sampler.Query.marginal .bob 7 z')), x) := rfl

/-- **The sampler of the class verifier.** -/
noncomputable def sampProg : Prog :=
  seq (A1 G Λ₀ R).code (seq (runUK U.univ) (seq unaryStage (seq (A2 G).code
    (seq (runUK U.univ) (seq (A3 G).code (runUK U.univ))))))

theorem sampProg_wellScoped : (sampProg G U Λ₀ R).WellScoped 1 :=
  seq_wellScoped (A1 G Λ₀ R).closed (seq_wellScoped (runUK_wellScoped U.closed)
    (seq_wellScoped unaryStage_wellScoped (seq_wellScoped (A2 G).closed
      (seq_wellScoped (runUK_wellScoped U.closed) (seq_wellScoped (A3 G).closed
        (runUK_wellScoped U.closed))))))

/-! ## Running the sampler -/

/-- A run of the sampler on a query is within its time bound. -/
theorem sampler_run_bounded (S : Sampler 7) {n T k : ℕ} (hb : S.TimeBoundAt n T k)
    (q : Sampler.Query) {r : Data} {t : ℕ} (h : S.prog.Runs (encode (n, q)) r t) :
    ∃ t' ≤ T * ((encode q : Data).size + 1) ^ k, S.prog.Runs (encode (n, q)) r t' := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb (encode q)
  have h₀' : S.prog.Runs (encode (n, q)) r₀ t₀ := h₀
  obtain ⟨rfl, -⟩ := Eval.deterministic h₀' h
  exact ⟨t₀, ht₀, h₀'⟩

/-- The cost of the binary-to-unary conversion, monotone in the number. -/
def unB (D : ℕ) : ℕ := (D + 2) * ((D + 1) * (4 * D + 14) + 7 * (4 * D + 1) + 8 * D + 90)

theorem unCost_le {d D : ℕ} (hd : d ≤ D) :
    (Nat.size d + 2) * ((d + 1) * (4 * d + 14) + 7 * esize d + 8 * d + 90) ≤ unB D := by
  have h1 : Nat.size d ≤ D := (Nat.size_le.2 Nat.lt_two_pow_self).trans hd
  have h2 : esize d ≤ 4 * D + 1 := (esize_nat_le_self d).trans (by omega)
  unfold unB
  exact Nat.mul_le_mul (by omega) (by nlinarith)

/-- The parameter, in the total input length `m`. -/
noncomputable def lamB (m : ℕ) : ℕ := Λ₀ + 4 * R.timeBound.eval (4 * m + 1)
/-- The compressor's bound `poly(C, λ)`, in `m`: bounds the dimension and the times. -/
noncomputable def dimB (m : ℕ) : ℕ := G.bound.eval (C G + lamB Λ₀ R m)
/-- Stage 1's cost. -/
noncomputable def T1B (m : ℕ) : ℕ := (A1 G Λ₀ R).timeBound.eval (4 * m + 3)
/-- The first universal call's cost. -/
noncomputable def R1B (m : ℕ) : ℕ :=
  2 * T1B G Λ₀ R m + (4 * dimB G Λ₀ R m + 1) +
    U.bound.eval (2 * T1B G Λ₀ R m + dimB G Λ₀ R m * (T1B G Λ₀ R m + 1) ^ G.deg) + 8
/-- The conversion's cost. -/
noncomputable def UnB (m : ℕ) : ℕ :=
  R1B G U Λ₀ R m + (4 * dimB G Λ₀ R m + 1) + unB (dimB G Λ₀ R m) + 5
/-- Stage 2's cost. -/
noncomputable def T2B (m : ℕ) : ℕ := (A2 G).timeBound.eval (UnB G U Λ₀ R m)
/-- The second universal call's cost. -/
noncomputable def R2B (m : ℕ) : ℕ :=
  2 * T2B G U Λ₀ R m + (4 * dimB G Λ₀ R m + 1) +
    U.bound.eval (2 * T2B G U Λ₀ R m + dimB G Λ₀ R m * (T2B G U Λ₀ R m + 1) ^ G.deg) + 8
/-- Stage 3's cost. -/
noncomputable def T3B (m : ℕ) : ℕ := (A3 G).timeBound.eval (R2B G U Λ₀ R m)
/-- The third universal call's cost. -/
noncomputable def R3B (m : ℕ) : ℕ :=
  2 * T3B G U Λ₀ R m + (4 * dimB G Λ₀ R m + 1) +
    U.bound.eval (2 * T3B G U Λ₀ R m + dimB G Λ₀ R m * (T3B G U Λ₀ R m + 1) ^ G.deg) + 8
/-- **The sampler's cost**, in the total input length. -/
noncomputable def sampB (m : ℕ) : ℕ :=
  2 * (T1B G Λ₀ R m + R1B G U Λ₀ R m + UnB G U Λ₀ R m + T2B G U Λ₀ R m +
    R2B G U Λ₀ R m + T3B G U Λ₀ R m) + R3B G U Λ₀ R m + 18

theorem lamz_le (z : BitStr) (m : ℕ) (hm : z.length ≤ m) :
    lamz Λ₀ R z ≤ lamB Λ₀ R m := by
  unfold lamz lamB
  have h1 := R.esize_apply_le z
  have h2 := esize_bitStr_le z
  have h3 := polynomial_eval_mono R.timeBound (show esize z ≤ 4 * m + 1 by omega)
  omega

theorem dimz_le (z : BitStr) (m : ℕ) (hm : z.length ≤ m) :
    dimz G Λ₀ R z ≤ dimB G Λ₀ R m :=
  (G.sampler_dim _ _).trans (polynomial_eval_mono _ (by have := lamz_le Λ₀ R z m hm; omega))

/-- **The sampler's run**: on `(z, r)` with `r` at least `dimz z` long, it halts with the
question pair of the seed within `sampB (|z| + |r|)`. -/
theorem sampProg_runs (z r : BitStr) (hd : dimz G Λ₀ R z ≤ r.length) :
    ∃ t, t ≤ sampB G U Λ₀ R (z.length + r.length) ∧
      (sampProg G U Λ₀ R).Runs (encode (z, r))
        (encode (qOf G Λ₀ R .alice z r, qOf G Λ₀ R .bob z r)) t := by
  set S := Sz G Λ₀ R z with hS
  set d := dimz G Λ₀ R z with hd_def
  set m := z.length + r.length with hm
  set z' := r.take d with hz'
  have hz'l : z'.length = d := by rw [hz', List.length_take]; omega
  have hbS : S.TimeBoundAt (C G) (G.bound.eval (C G + lamz Λ₀ R z)) G.deg :=
    G.sampler_time _ (C G)
  have hdimB : G.bound.eval (C G + lamz Λ₀ R z) ≤ dimB G Λ₀ R m :=
    polynomial_eval_mono _ (by have := lamz_le Λ₀ R z m (by omega); omega)
  have hdB : d ≤ dimB G Λ₀ R m := dimz_le G Λ₀ R z m (by omega)
  have hed : esize d ≤ 4 * dimB G Λ₀ R m + 1 := (esize_nat_le_self d).trans (by omega)
  have hed' : (encode d : Data).size = esize d := rfl
  -- stage 1
  obtain ⟨t₁, ht₁, h₁⟩ := (A1 G Λ₀ R).computes (z, r)
  rw [A1_apply, ← hS] at h₁
  have hT1 : t₁ ≤ T1B G Λ₀ R m := by
    refine ht₁.trans (polynomial_eval_mono _ ?_)
    have := esize_bitStr_le z; have := esize_bitStr_le r
    simp only [esize_prod]; omega
  have hy₁ := h₁.size_le
  -- the dimension query
  obtain ⟨t₀, hdim⟩ := S.runs_dimension (C G)
  obtain ⟨td, htd, hdim'⟩ := sampler_run_bounded S hbS _ hdim
  obtain ⟨tu₁, htu₁, hu₁⟩ := U.time_le S.prog (qdim G) (encode d) td hdim'
  obtain ⟨tk₁, htk₁, hk₁⟩ := runUK_runs U.closed (B := encode (S.prog, r)) hu₁
  have hk₁' : (runUK U.univ).Runs (encode ((S.prog, qdim G), (S.prog, r)))
    (encode ((S.prog, r), d)) tk₁ := hk₁
  have hy₂' := hk₁'.size_le
  have hsz₁ : (encode ((S.prog, qdim G), (S.prog, r)) : Data).size =
      (encode (S.prog, qdim G) : Data).size + (encode (S.prog, r) : Data).size + 1 := rfl
  have hsz₁' : (encode (S.prog, qdim G) : Data).size =
      esize S.prog + (qdim G).size + 1 := rfl
  have hqd : (encode Sampler.Query.dimension : Data).size ≤ (qdim G).size := by
    show _ ≤ (Data.cons (encode (C G)) (encode Sampler.Query.dimension)).size
    simp only [Data.size_cons]; omega
  have hsim₁ : td ≤ dimB G Λ₀ R m * (T1B G Λ₀ R m + 1) ^ G.deg :=
    htd.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hq₁ : (Data.cons (encode S.prog) (qdim G)).size = esize S.prog + (qdim G).size + 1 := rfl
  have hR1 : tk₁ ≤ R1B G U Λ₀ R m := by
    have hu := htu₁.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (qdim G).size + td ≤
        2 * T1B G Λ₀ R m + dimB G Λ₀ R m * (T1B G Λ₀ R m + 1) ^ G.deg by omega))
    unfold R1B; omega
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
  have hUn : tn ≤ UnB G U Λ₀ R m := by
    have hsz₂ : (encode ((S.prog, r), d) : Data).size =
      (encode (S.prog, r) : Data).size + esize d + 1 := rfl
    have := unCost_le hdB
    unfold UnB; omega
  have hy₃ := hn.size_le
  -- stage 2
  obtain ⟨t₂, ht₂, h₂⟩ := (A2 G).computes ((S.prog, r), unary d)
  rw [A2_apply, length_unary, ← hz'] at h₂
  have hT2 : t₂ ≤ T2B G U Λ₀ R m := by
    refine ht₂.trans (polynomial_eval_mono _ ?_)
    have : esize ((S.prog, r), unary d) = (encode ((S.prog, r), unary d) : Data).size := rfl
    rw [this, e_un]; omega
  have hy₄ := h₂.size_le
  -- Alice's marginal
  obtain ⟨tA, hA⟩ := S.runs_marginal (C G) .alice 7 z' (by norm_num) le_rfl hz'l
  rw [CLFun.truncate_self] at hA
  obtain ⟨tA', htA', hA'⟩ := sampler_run_bounded S hbS _ hA
  obtain ⟨tu₂, htu₂, hu₂⟩ := U.time_le S.prog _ _ tA' hA'
  have hu₂' : U.univ.Runs
    (.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .alice 7 z')))
    (encode (qOf G Λ₀ R .alice z r)) tu₂ := hu₂
  obtain ⟨tk₂, htk₂, hk₂⟩ := runUK_runs U.closed (B := encode (S.prog, z')) hu₂'
  have hk₂' : (runUK U.univ).Runs
      (encode ((S.prog, encode (C G, Sampler.Query.marginal .alice 7 z')), (S.prog, z')))
      (encode ((S.prog, z'), qOf G Λ₀ R .alice z r)) tk₂ := hk₂
  have hy₅' := hk₂'.size_le
  have hsz₄ : (encode ((S.prog, encode (C G, Sampler.Query.marginal .alice 7 z')),
      (S.prog, z')) : Data).size = (esize S.prog +
        (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size + 1) +
        (encode (S.prog, z') : Data).size + 1 := rfl
  have hqA : (encode (Sampler.Query.marginal .alice 7 z') : Data).size ≤
      (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size := by
    show _ ≤ (Data.cons (encode (C G)) (encode (Sampler.Query.marginal .alice 7 z'))).size
    simp only [Data.size_cons]; omega
  have hsim₂ : tA' ≤ dimB G Λ₀ R m * (T2B G U Λ₀ R m + 1) ^ G.deg :=
    htA'.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hex : esize (qOf G Λ₀ R .alice z r) ≤ 4 * dimB G Λ₀ R m + 1 := by
    have := esize_bitStr_le (qOf G Λ₀ R .alice z r)
    have : (qOf G Λ₀ R .alice z r).length = d := length_toBits _
    omega
  have hexe : (encode (qOf G Λ₀ R .alice z r) : Data).size =
    esize (qOf G Λ₀ R .alice z r) := rfl
  have hq₂ : (Data.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .alice 7 z'))).size
    = esize S.prog + (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size + 1 := rfl
  have hR2 : tk₂ ≤ R2B G U Λ₀ R m := by
    have hu := htu₂.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size + tA'
        ≤ 2 * T2B G U Λ₀ R m + dimB G Λ₀ R m * (T2B G U Λ₀ R m + 1) ^ G.deg by omega))
    have : (encode (qOf G Λ₀ R .alice z r) : Data).size = esize (qOf G Λ₀ R .alice z r) := rfl
    unfold R2B; omega
  have hy₅ := hk₂.size_le
  -- stage 3
  obtain ⟨t₃, ht₃, h₃⟩ := (A3 G).computes ((S.prog, z'), qOf G Λ₀ R .alice z r)
  rw [A3_apply] at h₃
  have hT3 : t₃ ≤ T3B G U Λ₀ R m := by
    refine ht₃.trans (polynomial_eval_mono _ ?_)
    have : esize ((S.prog, z'), qOf G Λ₀ R .alice z r) =
      (encode ((S.prog, z'), qOf G Λ₀ R .alice z r) : Data).size := rfl
    rw [this]; omega
  have hy₆ := h₃.size_le
  -- Bob's marginal
  obtain ⟨tB, hB⟩ := S.runs_marginal (C G) .bob 7 z' (by norm_num) le_rfl hz'l
  rw [CLFun.truncate_self] at hB
  obtain ⟨tB', htB', hB'⟩ := sampler_run_bounded S hbS _ hB
  obtain ⟨tu₃, htu₃, hu₃⟩ := U.time_le S.prog _ _ tB' hB'
  have hu₃' : U.univ.Runs (.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .bob 7 z')))
    (encode (qOf G Λ₀ R .bob z r)) tu₃ := hu₃
  obtain ⟨tk₃, htk₃, hk₃⟩ :=
    runUK_runs U.closed (B := encode (qOf G Λ₀ R .alice z r)) hu₃'
  have hk₃' : (runUK U.univ).Runs
      (encode ((S.prog, encode (C G, Sampler.Query.marginal .bob 7 z')),
        qOf G Λ₀ R .alice z r))
      (encode (qOf G Λ₀ R .alice z r, qOf G Λ₀ R .bob z r)) tk₃ := hk₃
  have hsz₆ : (encode ((S.prog, encode (C G, Sampler.Query.marginal .bob 7 z')),
      qOf G Λ₀ R .alice z r) : Data).size = (esize S.prog +
        (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size + 1) +
        esize (qOf G Λ₀ R .alice z r) + 1 := rfl
  have hqB : (encode (Sampler.Query.marginal .bob 7 z') : Data).size ≤
      (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size := by
    show _ ≤ (Data.cons (encode (C G)) (encode (Sampler.Query.marginal .bob 7 z'))).size
    simp only [Data.size_cons]; omega
  have hsim₃ : tB' ≤ dimB G Λ₀ R m * (T3B G U Λ₀ R m + 1) ^ G.deg :=
    htB'.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hey : esize (qOf G Λ₀ R .bob z r) ≤ 4 * dimB G Λ₀ R m + 1 := by
    have := esize_bitStr_le (qOf G Λ₀ R .bob z r)
    have : (qOf G Λ₀ R .bob z r).length = d := length_toBits _
    omega
  have heye : (encode (qOf G Λ₀ R .bob z r) : Data).size = esize (qOf G Λ₀ R .bob z r) := rfl
  have hq₃ : (Data.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .bob 7 z'))).size
    = esize S.prog + (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size + 1 := rfl
  have hR3 : tk₃ ≤ R3B G U Λ₀ R m := by
    have hu := htu₃.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size + tB'
        ≤ 2 * T3B G U Λ₀ R m + dimB G Λ₀ R m * (T3B G U Λ₀ R m + 1) ^ G.deg by omega))
    have : (encode (qOf G Λ₀ R .bob z r) : Data).size = esize (qOf G Λ₀ R .bob z r) := rfl
    unfold R3B; omega
  -- assemble
  have w3 := runUK_wellScoped U.closed
  have w23 := seq_wellScoped (A3 G).closed w3
  have wk2 := seq_wellScoped (runUK_wellScoped U.closed) w23
  have wc2 := seq_wellScoped (A2 G).closed wk2
  have wun := seq_wellScoped unaryStage_wellScoped wc2
  have wk1 := seq_wellScoped (runUK_wellScoped U.closed) wun
  have hrun := seq_runs wk1 h₁ (seq_runs wun hk₁' (seq_runs wc2 hn' (seq_runs wk2 h₂
    (seq_runs w23 hk₂' (seq_runs w3 h₃ hk₃')))))
  refine ⟨_, ?_, hrun⟩
  unfold sampB
  omega

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
