/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Wrapper
import MIPRE.Foundations.Halting.PolyBounded
import MIPRE.Foundations.Halting.Bounded

/-!
# The running time of the wrapper

`Decider.wrap` reads a string as a decider (`Halting/Wrapper.lean`); this file bounds its
running time. That bound is what makes the verifier a string denotes `λ`-bounded, and so what
makes the classes `MIPRE.Halting.classA`, `classB` inhabited at all: until it, every proof of
`Verifier.IsBounded` in the repository was conditional on another time bound.

The shape throughout is `Cost.Prog.HasPolyCost`: cost at most `C n · (|d| + 1) ^ k` at index
`n` on input `d`, with `C` polynomially bounded and `k` constant — what `Decider.TimeBoundAt`
asks for after `Halting/Bounded.lean`, and what composes (`Cost.PolyCost`). Nothing here is
tight: each stage is bounded by a generous square and the stages are summed, since
`λ`-boundedness quantifies the constants away.

**Everything is proved on arbitrary data.** `TimeBoundAt` quantifies over every input at the
index, well formed or not, so no stage may assume it is handed a question pair:

* `Data.toSpine` and `Prog.lenProgD_runs`: the length program on any datum, walking its right
  spine, not only on a list built by `Data.list`.
* `Prog.wrapCheckEnvN` and `wrapCheckD_cost_of_eq`, `wrapCheckD_cost_of_ne`: one length check,
  which compares `Data.spine` with the sampler's dimension — on `encode l` that is `l.length`,
  and on anything else it is what the program actually computes.
* `Prog.wrapHead_cost` and `wrapPre_cost`: the head, whose cost depends on the index alone (the
  dimension query runs on a fixed input), and the prefix, which on a tail too short to hold two
  questions rejects outright.
* `Prog.wrapCore_hasPolyCost`: the whole, by the three outcomes — the first check fails, the
  second fails, or both pass and the string's own decider runs through the universal machine.
* `Verifier.ofSamplerDecider_isBounded`: the verifier a pair denotes is `n`-bounded at every
  level from some `n₀` on, by `Verifier.exists_isBounded`.

The hypotheses are exactly three: the sampler's program and the string's decider have
polynomially bounded cost, and the sampler's dimension is polynomially bounded. For a sampler
coming from `MIPRE.GapCompression` all three are its fields, through
`CL.Sampler.hasPolyCost_of_timeBound`.
-/
namespace MIPRE

open Cost

namespace Cost

/-! ## The right spine of a datum -/

namespace Data

/-- The right spine of a datum, as a list: `list (toSpine d) = d`. -/
def toSpine : Data → List Data
  | nil => []
  | cons a b => a :: toSpine b

theorem list_toSpine (d : Data) : list (toSpine d) = d := by
  induction d with
  | nil => rfl
  | cons a b _ ihb => rw [toSpine, list_cons, ihb]

theorem length_toSpine (d : Data) : (toSpine d).length = spine d := by
  induction d with
  | nil => rfl
  | cons a b _ ihb => rw [toSpine, List.length_cons, ihb, spine_cons]

end Data

namespace Prog

open Data

/-- The length program on arbitrary data: it walks the right spine. -/
theorem lenProgD_runs (d : Data) :
    ∃ t ≤ (d.spine + 2) * (d.size + 2 * d.spine + 14),
      lenProg.Runs d (Data.ofNat d.spine) t := by
  obtain ⟨t, ht, hrun⟩ := lenProg_runs (toSpine d)
  rw [length_toSpine] at ht hrun
  rw [list_toSpine] at ht hrun
  exact ⟨t, ht.trans (le_of_eq (by ring)), hrun⟩

/-! ## The stages -/

section Stages

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)

/-- The environment the head hands to its continuation. -/
def wrapHeadEnv (n : ℕ) (d : Data) : Env :=
  [Data.ofNat (S.dim n), encode (S.dim n),
    .cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension)),
    encode n, d, .cons (encode n) d]

/-- **The head.** Its cost depends on the index only: the dimension query runs on a fixed
input, and the conversion to unary on the dimension. -/
theorem wrapHead_cost (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim) :
    ∃ H : ℕ → ℕ, PolyBounded H ∧ ∀ (c : Prog) (n : ℕ) (d r : Data) (t : ℕ),
      Eval (wrapHeadEnv S n d) c r t →
        ∃ t', t' ≤ t + H n ∧ Eval [.cons (encode n) d] (wrapHead U.univ S.prog c) r t' := by
  obtain ⟨Cf, kf, hCf, hf⟩ := hS
  set q : Data := encode CL.Sampler.Query.dimension with hq
  -- the sampler's own run on the dimension query, bounded uniformly in `n`
  have hdimrun : ∀ n : ℕ, ∃ t ≤ Cf n * (q.size + 1) ^ kf,
      S.prog.Runs (.cons (encode n) q) (encode (S.dim n)) t := by
    intro n
    obtain ⟨r, t, ht, hrun⟩ := hf n q
    obtain ⟨t₀, h₀⟩ := S.runs_dimension n
    obtain ⟨rfl, rfl⟩ := Eval.deterministic hrun h₀
    exact ⟨t, ht, hrun⟩
  -- the unary conversion
  have htu : ∀ m : ℕ, ∃ t ≤ (Nat.size m + 2) * ((m + 1) * (4 * m + 14) + 7 * esize m + 8 * m + 90),
      toUnaryProg.Runs (encode m) (Data.ofNat m) t := fun m => toUnaryProg_runs m
  set Z : ℕ → ℕ := fun n => esize S.prog + esize n + q.size + esize (S.dim n) +
      Cf n * (q.size + 1) ^ kf +
      U.bound.eval (esize S.prog + (esize n + q.size + 1) + Cf n * (q.size + 1) ^ kf) +
      (Nat.size (S.dim n) + 2) * ((S.dim n + 1) * (4 * S.dim n + 14) + 7 * esize (S.dim n) +
        8 * S.dim n + 90) + 10 with hZ
  have hZpoly : PolyBounded Z := by
    have h1 : PolyBounded fun _ : ℕ => esize S.prog := PolyBounded.const _
    have h2 : PolyBounded fun n : ℕ => esize n := polyBounded_esize_nat
    have h3 : PolyBounded fun _ : ℕ => q.size := PolyBounded.const _
    have h4 : PolyBounded fun n : ℕ => esize (S.dim n) := polyBounded_esize_nat.comp hdim
    have h5 : PolyBounded fun n : ℕ => Cf n * (q.size + 1) ^ kf :=
      hCf.mul (PolyBounded.const _)
    have h6 : PolyBounded fun n : ℕ =>
        U.bound.eval (esize S.prog + (esize n + q.size + 1) + Cf n * (q.size + 1) ^ kf) :=
      PolyBounded.eval _ (((h1.add (h2.add_const (q.size + 1))).add h5))
    have h7 : PolyBounded fun n : ℕ => (Nat.size (S.dim n) + 2) *
        ((S.dim n + 1) * (4 * S.dim n + 14) + 7 * esize (S.dim n) + 8 * S.dim n + 90) :=
      ((PolyBounded.size.comp hdim).add_const 2).mul
        ((((hdim.add_const 1).mul ((hdim.const_mul 4).add_const 14)).add
          (h4.const_mul 7)).add ((hdim.const_mul 8).add_const 90))
    exact ((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add_const 10
  refine ⟨fun n => 60 * Z n ^ 2, hZpoly.pow 2 |>.const_mul 60, fun c n d r t hc => ?_⟩
  obtain ⟨t₁, ht₁, h₁⟩ := hdimrun n
  obtain ⟨t₂, ht₂, h₂⟩ := htu (S.dim n)
  obtain ⟨t₃, ht₃, h₃⟩ := U.time_le S.prog (.cons (encode n) q) (encode (S.dim n)) t₁ h₁
  -- `q` is an abbreviation for the bounds; the program carries the literal, so the runs that
  -- the term below is assembled from have to carry it too
  rw [hq] at h₁ h₃
  refine ⟨_, ?_, Eval.elim_cons (env := [.cons (encode n) d]) (i := 0) (a := encode n) (b := d)
    (by simp)
    (Eval.let_ (Eval.cons (Eval.const _ _)
        (Eval.cons (Eval.var_of_get (i := 0) (v := encode n) (by simp)) (Eval.const _ _)))
      (Eval.let_ (callVar_eval U.closed (i := 0)
          (v := .cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension)))
          (by simp) h₃)
        (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 0) (v := encode (S.dim n))
            (by simp) h₂) hc)))⟩
  -- the arithmetic: every piece is at most `Z n`, and there are fewer than sixty of them
  have hZ1 : 1 ≤ Z n := by simp only [hZ]; omega
  have hZsq : Z n ≤ Z n ^ 2 := Nat.le_self_pow (by norm_num) _
  have e0 : t₁ ≤ Z n := ht₁.trans (by simp only [hZ]; omega)
  have e1 : esize S.prog ≤ Z n := by simp only [hZ]; omega
  have e2 : esize n ≤ Z n := by simp only [hZ]; omega
  have e3 : q.size ≤ Z n := by simp only [hZ]; omega
  have e4 : esize (S.dim n) ≤ Z n := by simp only [hZ]; omega
  have e5 : t₂ ≤ Z n := ht₂.trans (by simp only [hZ]; omega)
  have e6 : t₃ ≤ Z n := by
    refine ht₃.trans ?_
    have : esize S.prog + (Data.cons (encode n) q).size + t₁ ≤
        esize S.prog + (esize n + q.size + 1) + Cf n * (q.size + 1) ^ kf := by
      have : (Data.cons (encode n) q).size = esize n + q.size + 1 := rfl
      omega
    exact (polynomial_eval_mono U.bound this).trans (by simp only [hZ]; omega)
  have hqs : (encode CL.Sampler.Query.dimension : Data).size = q.size := by rw [hq]
  have hsz : (encode n : Data).size = esize n := rfl
  have hszS : (encode S.prog : Data).size = esize S.prog := rfl
  have hszD : (encode (S.dim n) : Data).size = esize (S.dim n) := rfl
  simp only [Data.size_cons, hsz, hszS, hszD]
  omega

end Stages

/-! ## The length check, on arbitrary data -/

/-- The environment one length check hands to its continuation, parameterized by the spine
length it measured rather than by a bit string: the wrapper is run on malformed inputs too. -/
def wrapCheckEnvN (k m : ℕ) (env : Env) : Env :=
  .nil :: .nil :: encode true :: .cons (Data.ofNat k) (Data.ofNat m) :: Data.ofNat k :: env

theorem wrapCheckEnv_eq (l : BitStr) (m : ℕ) (env : Env) :
    wrapCheckEnv l m env = wrapCheckEnvN l.length m env := rfl

/-- A generous bound on the cost of one length check, in the size of the datum tested and the
number it is compared with. -/
def checkCost (E m : ℕ) : ℕ := 60 * (E + m + 30) ^ 2

private theorem eq_runB (p q : ℕ) :
    ∃ t ≤ (p + 1) * (2 * p + 2 * q + 23),
      eqBitsProg.Runs (.cons (Data.ofNat p) (Data.ofNat q)) (encode (decide (p = q))) t := by
  obtain ⟨t, ht, h⟩ := eqBitsProg_runs (Data.ofNat p) (Data.ofNat q) []
    ((Data.ofNat p).size + (Data.ofNat q).size) le_rfl
  rw [eqBits_ofNat] at h
  refine ⟨t, ht.trans ?_, h⟩
  rw [Data.spine_ofNat, Data.size_ofNat, Data.size_ofNat]
  exact Nat.mul_le_mul_left _ (by omega)

/-- Every factor appearing in the check's cost is at most three times `E + m + 30`. -/
private theorem check_mul_le {E m a b : ℕ} (ha : a ≤ E + m + 30) (hb : b ≤ 3 * (E + m + 30)) :
    a * b ≤ 3 * (E + m + 30) ^ 2 :=
  (Nat.mul_le_mul ha hb).trans (le_of_eq (by ring))

/-- **The check passes.** -/
theorem wrapCheckD_cost_of_eq {i j : ℕ} {c : Prog} {env : Env} {v : Data} {m : ℕ}
    (hi : env.get i = v) (hj : env.get j = Data.ofNat m) (heq : v.spine = m)
    {r : Data} {t : ℕ} (hc : Eval (wrapCheckEnvN m m env) c r t) :
    ∃ t' ≤ t + checkCost v.size m, Eval env (wrapCheck i j c) r t' := by
  obtain ⟨t₁, ht₁, h₁⟩ := lenProgD_runs v
  obtain ⟨t₂, ht₂, h₂⟩ := eq_runB v.spine m
  have hc' : Eval (Data.nil :: Data.nil :: encode (decide (v.spine = m)) ::
      Data.cons (Data.ofNat v.spine) (Data.ofNat m) :: Data.ofNat v.spine :: env) c r t := by
    simpa [wrapCheckEnvN, heq] using hc
  refine ⟨_, ?_, Eval.let_ (callVar_eval lenProg_wellScoped hi h₁)
    (Eval.let_ (Eval.cons
        (Eval.var_of_get (env := Data.ofNat v.spine :: env) (i := 0)
          (v := Data.ofNat v.spine) (by simp))
        (Eval.var_of_get (env := Data.ofNat v.spine :: env) (i := j + 1)
          (v := Data.ofNat m) (by simpa using hj)))
      (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat v.spine) (Data.ofNat m)) (by simp) h₂)
        (Eval.elim_cons (i := 0) (a := .nil) (b := .nil)
          (by simp [heq, encode_bool, Data.ofBool]) hc')))⟩
  have hE : v.spine ≤ v.size := Data.spine_le_size v
  have hQ0 : v.size + m + 30 ≤ (v.size + m + 30) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hQ1 : t₁ ≤ 3 * (v.size + m + 30) ^ 2 := ht₁.trans (check_mul_le (by omega) (by omega))
  have hQ2 : t₂ ≤ 3 * (v.size + m + 30) ^ 2 := ht₂.trans (check_mul_le (by omega) (by omega))
  simp only [Data.size_cons, Data.size_ofNat, checkCost]
  omega

/-- **The check fails**, and the whole wrapper rejects. -/
theorem wrapCheckD_cost_of_ne {i j : ℕ} {c : Prog} {env : Env} {v : Data} {m : ℕ}
    (hi : env.get i = v) (hj : env.get j = Data.ofNat m) (hne : v.spine ≠ m) :
    ∃ t' ≤ checkCost v.size m, Eval env (wrapCheck i j c) .nil t' := by
  obtain ⟨t₁, ht₁, h₁⟩ := lenProgD_runs v
  obtain ⟨t₂, ht₂, h₂⟩ := eq_runB v.spine m
  refine ⟨_, ?_, Eval.let_ (callVar_eval lenProg_wellScoped hi h₁)
    (Eval.let_ (Eval.cons
        (Eval.var_of_get (env := Data.ofNat v.spine :: env) (i := 0)
          (v := Data.ofNat v.spine) (by simp))
        (Eval.var_of_get (env := Data.ofNat v.spine :: env) (i := j + 1)
          (v := Data.ofNat m) (by simpa using hj)))
      (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat v.spine) (Data.ofNat m)) (by simp) h₂)
        (Eval.elim_nil (i := 0)
          (show Env.get (encode (decide (v.spine = m)) ::
              Data.cons (Data.ofNat v.spine) (Data.ofNat m) ::
              Data.ofNat v.spine :: env) 0 = Data.nil by
            simp [hne, encode_bool, Data.ofBool])
          (Eval.nil _))))⟩
  have hE : v.spine ≤ v.size := Data.spine_le_size v
  have hQ0 : v.size + m + 30 ≤ (v.size + m + 30) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hQ1 : t₁ ≤ 3 * (v.size + m + 30) ^ 2 := ht₁.trans (check_mul_le (by omega) (by omega))
  have hQ2 : t₂ ≤ 3 * (v.size + m + 30) ^ 2 := ht₂.trans (check_mul_le (by omega) (by omega))
  simp only [Data.size_cons, Data.size_ofNat, checkCost]
  omega

/-! ## The prefix -/

section Pre

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)

/-- The environment the prefix hands to the first length check, for an input whose tail is
`cons A (cons B C)` — the only shape on which the checks run at all. -/
def wrapPreEnvD (n : ℕ) (A B C : Data) : Env :=
  B :: C :: A :: (Data.cons B C) :: wrapHeadEnv S n (Data.cons A (Data.cons B C))

theorem wrapPreEnvD_eq (n : ℕ) (x y a b : BitStr) :
    wrapPreEnv S n x y a b
      = wrapPreEnvD S n (encode x) (encode y) (.cons (encode a) (encode b)) := rfl

/-- **The prefix, on every input.** On a tail of the shape `cons A (cons B C)` it hands the
environment `wrapPreEnvD` to its continuation; on a shorter tail it rejects outright. Both
cost `H n` beyond the continuation, `H` polynomially bounded. -/
theorem wrapPre_cost (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim) :
    ∃ H : ℕ → ℕ, PolyBounded H ∧
      (∀ (c : Prog) (n : ℕ) (A B C r : Data) (t : ℕ),
        Eval (wrapPreEnvD S n A B C) c r t →
          ∃ t' ≤ t + H n, Eval [.cons (encode n) (.cons A (.cons B C))]
            (wrapPre U.univ S.prog c) r t') ∧
      (∀ (c : Prog) (n : ℕ) (d : Data), d.spine ≤ 1 →
        ∃ t ≤ H n, Eval [.cons (encode n) d] (wrapPre U.univ S.prog c) .nil t) := by
  obtain ⟨H, hH, hhead⟩ := wrapHead_cost U S hS hdim
  refine ⟨fun n => H n + 4, hH.add_const 4, fun c n A B C r t hc => ?_, fun c n d hd => ?_⟩
  · obtain ⟨t', ht', h'⟩ := hhead (.elim 4 .nil (.elim 1 .nil c)) n
      (.cons A (.cons B C)) r (t + 1 + 1)
      (Eval.elim_cons (i := 4) (a := A) (b := .cons B C) (by simp [wrapHeadEnv])
        (Eval.elim_cons (i := 1) (a := B) (b := C) (by simp) hc))
    exact ⟨t', by show t' ≤ t + (H n + 4); omega, h'⟩
  · -- a tail of spine at most one: the first `elim` finds `nil` at index 4, or the second at 1
    have hrej : ∃ u ≤ 3, Eval (wrapHeadEnv S n d) (.elim 4 .nil (.elim 1 .nil c)) .nil u := by
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
    obtain ⟨t', ht', h'⟩ := hhead (.elim 4 .nil (.elim 1 .nil c)) n d .nil u hrun
    exact ⟨t', by show t' ≤ H n + 4; omega, h'⟩

end Pre

/-! ## The whole wrapper -/

theorem checkCost_mono {E E' m : ℕ} (h : E ≤ E') : checkCost E m ≤ checkCost E' m :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

section Core

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog)

/-- **The wrapper halts within a polynomially bounded cost on every input**, well formed or
not, provided the sampler and the string's own decider do. This is what inhabits
`Verifier.IsBounded` for the verifier a string denotes. -/
theorem wrapCore_hasPolyCost (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim)
    (hdec : dec.HasPolyCost) : (wrapCore U.univ S.prog dec).HasPolyCost := by
  obtain ⟨H, hH, hpre, hrej⟩ := wrapPre_cost U S hS hdim
  obtain ⟨Cd, kd, hCd, hdrun⟩ := hdec
  -- the bound: the prefix, the two checks, and the universal machine on the string's decider
  refine Prog.hasPolyCost_of_polyCost (B := fun n d => H n + 2 * checkCost d.size (S.dim n) +
      (2 * (esize dec + esize n + d.size + 2) +
        U.bound.eval (esize dec + (esize n + d.size + 1) + Cd n * (d.size + 1) ^ kd)) + 20)
    ?_ ?_
  · -- the bound is polynomial in the index and the input size
    have hsz : PolyCost fun (_ : ℕ) (d : Data) => d.size := PolyCost.size
    have hn : PolyCost fun (n : ℕ) (_ : Data) => esize n :=
      PolyCost.ofIndex polyBounded_esize_nat
    have hdm : PolyCost fun (n : ℕ) (_ : Data) => S.dim n := PolyCost.ofIndex hdim
    have hchk : PolyCost fun (n : ℕ) (d : Data) => checkCost d.size (S.dim n) := by
      have hb : PolyCost fun (n : ℕ) (d : Data) => d.size + S.dim n + 30 :=
        ((hsz.add hdm).add (PolyCost.const 30))
      exact ((PolyCost.const 60).mul (hb.mul hb)).mono fun n d => by
        simp only [checkCost]; nlinarith [sq_nonneg (d.size + S.dim n + 30)]
    have hpow : PolyCost fun (_ : ℕ) (d : Data) => (d.size + 1) ^ kd :=
      (PolyCost.poly ((Polynomial.X + Polynomial.C 1) ^ kd) hsz).mono fun n d => by simp
    have hU : PolyCost fun (n : ℕ) (d : Data) =>
        U.bound.eval (esize dec + (esize n + d.size + 1) + Cd n * (d.size + 1) ^ kd) :=
      PolyCost.poly U.bound
        (((PolyCost.const (esize dec)).add ((hn.add hsz).add (PolyCost.const 1))).add
          ((PolyCost.ofIndex hCd).mul hpow))
    exact ((((PolyCost.ofIndex hH).add ((PolyCost.const 2).mul hchk)).add
      (((PolyCost.const 2).mul ((((PolyCost.const (esize dec)).add hn).add hsz).add
        (PolyCost.const 2))).add hU)).add (PolyCost.const 20))
  · intro n d
    rcases Nat.lt_or_ge d.spine 2 with hd | hd
    · -- a tail too short for two questions: the prefix rejects
      obtain ⟨t, ht, hrun⟩ := hrej _ n d (by omega)
      exact ⟨.nil, t, by omega, hrun⟩
    · -- `d = cons A (cons B C)`
      match d, hd with
      | .cons A (.cons B C), _ =>
        set d : Data := Data.cons A (Data.cons B C) with hdef
        have hA : A.size ≤ d.size := by rw [hdef]; simp; omega
        have hB : B.size ≤ d.size := by rw [hdef]; simp; omega
        by_cases hxa : A.spine = S.dim n
        · by_cases hyb : B.spine = S.dim n
          · -- both checks pass: the string's decider runs, through the universal machine
            obtain ⟨r, td, htd, hdr⟩ := hdrun n d
            obtain ⟨t₇, ht₇, h₇⟩ := U.time_le dec (.cons (encode n) d) r td hdr
            have htail : Eval (wrapCheckEnvN (S.dim n) (S.dim n)
                (wrapCheckEnvN (S.dim n) (S.dim n) (wrapPreEnvD S n A B C)))
                (wrapTail U.univ dec) r _ :=
              Eval.let_ (Eval.cons (Eval.const _ _)
                (Eval.var_of_get (i := 19) (v := .cons (encode n) d)
                  (by simp [wrapCheckEnvN, wrapPreEnvD, wrapHeadEnv, hdef])))
                (callVar_eval U.closed (i := 0)
                  (v := .cons (encode dec) (.cons (encode n) d)) (by simp) h₇)
            obtain ⟨t₂, ht₂, h₂⟩ := wrapCheckD_cost_of_eq (i := 5) (j := 9)
              (env := wrapCheckEnvN (S.dim n) (S.dim n) (wrapPreEnvD S n A B C))
              (v := B) (m := S.dim n)
              rfl rfl
              hyb htail
            obtain ⟨t₁, ht₁, h₁⟩ := wrapCheckD_cost_of_eq (i := 2) (j := 4)
              (env := wrapPreEnvD S n A B C) (v := A) (m := S.dim n)
              rfl rfl
              hxa h₂
            obtain ⟨t₀, ht₀, h₀⟩ := hpre _ n A B C r t₁ h₁
            refine ⟨r, t₀, ?_, hdef ▸ h₀⟩
            have hc1 : checkCost A.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
              checkCost_mono hA
            have hc2 : checkCost B.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
              checkCost_mono hB
            have hUb : t₇ ≤ U.bound.eval (esize dec + (esize n + d.size + 1) +
                Cd n * (d.size + 1) ^ kd) :=
              ht₇.trans (polynomial_eval_mono U.bound (by
                have : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
                omega))
            have hsz1 : (encode dec : Data).size = esize dec := rfl
            have hsz2 : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
            simp only [Data.size_cons, hsz1, hsz2] at ht₂
            omega
          · -- the second check fails
            obtain ⟨t₂, ht₂, h₂⟩ := wrapCheckD_cost_of_ne (i := 5) (j := 9)
              (env := wrapCheckEnvN (S.dim n) (S.dim n) (wrapPreEnvD S n A B C))
              (v := B) (m := S.dim n) (c := wrapTail U.univ dec)
              rfl rfl hyb
            obtain ⟨t₁, ht₁, h₁⟩ := wrapCheckD_cost_of_eq (i := 2) (j := 4)
              (env := wrapPreEnvD S n A B C) (v := A) (m := S.dim n)
              rfl rfl hxa h₂
            obtain ⟨t₀, ht₀, h₀⟩ := hpre _ n A B C .nil t₁ h₁
            refine ⟨.nil, t₀, ?_, hdef ▸ h₀⟩
            have hc1 : checkCost A.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
              checkCost_mono hA
            have hc2 : checkCost B.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
              checkCost_mono hB
            omega
        · -- the first check fails
          obtain ⟨t₁, ht₁, h₁⟩ := wrapCheckD_cost_of_ne (i := 2) (j := 4)
            (env := wrapPreEnvD S n A B C) (v := A) (m := S.dim n)
            (c := wrapCheck 5 9 (wrapTail U.univ dec))
            rfl rfl hxa
          obtain ⟨t₀, ht₀, h₀⟩ := hpre _ n A B C .nil t₁ h₁
          refine ⟨.nil, t₀, ?_, hdef ▸ h₀⟩
          have hc1 : checkCost A.size (S.dim n) ≤ checkCost d.size (S.dim n) :=
            checkCost_mono hA
          omega

end Core

end Prog

end Cost

open Cost.Prog

namespace Verifier

/-- **The verifier a string denotes is `λ`-bounded**, at every level from some `n₀` on,
provided the sampler and the string's own decider have polynomially bounded cost and the
sampler's dimension is polynomially bounded. This is what inhabits `Verifier.IsBounded`. -/
theorem ofSamplerDecider_isBounded {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)
    (dec : Prog) (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim)
    (hdec : dec.HasPolyCost) :
    ∃ n₀, ∀ n, n₀ ≤ n → (ofSamplerDecider U S dec).IsBounded n :=
  (ofSamplerDecider U S dec).exists_isBounded hdim hS
    (wrapCore_hasPolyCost U S dec hS hdim hdec)

end Verifier

end MIPRE
