/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.GapCompression
import MIPRE.Foundations.VerifierValue
import MIPRE.Foundations.Cost.Closure

/-!
# Freezing a verifier at an index

Blueprint `rem:compression-abstract`, item 2: the recursion of the compressibility criterion
goes `n → 2n + 1`, while gap-preserving compression relates the game at index `2 ^ n` to the
output at index `n`; the two are reconciled by *freezing* the described verifier at index
`2n + 1` before compressing it. The frozen verifier answers at every index as the original
does at the frozen index, so its game at index `2 ^ n` is the original's game at level
`2n + 1`.

* `Cost.Prog.freezeProg k p`: on input `cons N d`, run `p` on `cons (encode k) d`. Its cost
  is that of `p` plus the cost of copying the input, which is what the reading of the time
  bounds a polynomial in the size of the input (`Decider.TimeBoundAt`) allows.
* `CL.Sampler.freeze`, `Decider.freeze`, `Verifier.freeze`: the frozen sampler, decider and
  verifier, with the transfer of the query clauses, of acceptance (`Decider.freeze_accepts`),
  of the values and perfect PCC strategies (`Verifier.freeze_valStar`,
  `Verifier.freeze_hasPerfectPCC`), of the time bounds, and of `λ`-boundedness
  (`Verifier.freeze_isBounded`): the frozen verifier is `λ`-bounded as soon as the original's
  dimension, running times and size at the frozen index fit under `2 ^ λ` and `λ`.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

/-- Freeze the index: on input `cons N d`, run `p` on `cons (encode k) d`. -/
def freezeProg (k : ℕ) (p : Prog) : Prog :=
  .let_ (.elim 0 .nil (.cons (.const (encode k)) (.var 1))) p

theorem freezeProg_wellScoped {p : Prog} (hp : p.WellScoped 1) (k : ℕ) :
    (freezeProg k p).WellScoped 1 :=
  ⟨by simp [WellScoped], hp.mono (by omega) _⟩

/-- The run of the index-replacing prefix of `freezeProg`. -/
theorem freezeProg_prefix_eval (k : ℕ) (N d : Data) :
    Eval [.cons N d] (.elim 0 .nil (.cons (.const (encode k)) (.var 1))) (.cons (encode k) d)
      ((encode k : Data).size + (d.size + 1) + 1 + 1) :=
  Eval.elim_cons (i := 0) (a := N) (b := d) (by simp)
    (Eval.cons (Eval.const _ _) (Eval.var_of_get (i := 1) (v := d) (by simp)))

/-- Forward transfer: a run of `p` at the frozen index gives a run of `freezeProg k p` at any
index, at the additional cost of copying the input. -/
theorem freezeProg_runs {p : Prog} (hp : p.WellScoped 1) {k : ℕ} {N d r : Data} {t : ℕ}
    (h : p.Runs (.cons (encode k) d) r t) :
    (freezeProg k p).Runs (.cons N d) r (t + esize k + d.size + 4) :=
  (Eval.let_ (freezeProg_prefix_eval k N d) (Eval.append_of_wellScoped h hp [.cons N d])).cast_cost
    (by unfold esize; omega)

/-- Backward transfer: a run of `freezeProg k p` is a run of `p` at the frozen index. -/
theorem freezeProg_runs_rev {p : Prog} (hp : p.WellScoped 1) {k : ℕ} {N d r : Data} {t : ℕ}
    (h : (freezeProg k p).Runs (.cons N d) r t) :
    ∃ t' ≤ t, p.Runs (.cons (encode k) d) r t' := by
  change Eval [.cons N d] (.let_ _ p) r t at h
  cases h with
  | let_ h₁ h₂ =>
    obtain ⟨rfl, -⟩ := h₁.deterministic (freezeProg_prefix_eval k N d)
    exact ⟨_, by omega,
      Eval.of_append_of_wellScoped (env := [.cons (encode k) d]) (extra := [.cons N d]) h₂ hp⟩

/-- The frozen program halts on `cons N d` exactly when `p` halts on `cons (encode k) d`,
with the same result. -/
theorem freezeProg_runs_iff {p : Prog} (hp : p.WellScoped 1) (k : ℕ) (N d r : Data) :
    (∃ t, (freezeProg k p).Runs (.cons N d) r t) ↔ ∃ t, p.Runs (.cons (encode k) d) r t :=
  ⟨fun ⟨_, h⟩ => let ⟨t', _, h'⟩ := freezeProg_runs_rev hp h; ⟨t', h'⟩,
    fun ⟨_, h⟩ => ⟨_, freezeProg_runs hp h⟩⟩

/-- The description of the frozen program: that of `p`, plus the index, plus `53` nodes. -/
theorem esize_freezeProg (k : ℕ) (p : Prog) : esize (freezeProg k p) = esize p + esize k + 53 := by
  rw [esize_eq_size_toData, esize_eq_size_toData]
  unfold esize
  simp only [freezeProg, Prog.toData, Data.size_cons, Data.size_ofNat, Data.size_nil]
  omega

end Cost.Prog

/-- The arithmetic shared by the two freezing time bounds: the frozen program's cost fits
under the same polynomial with the coefficient shifted by the cost of copying, once the
degree is at least one. -/
theorem freeze_cost_le {T j e t s : ℕ} (ht : t ≤ T * (s + 1) ^ j) :
    t + e + s + 4 ≤ (T + e + 4) * (s + 1) ^ max j 1 := by
  have h1 : (s + 1) ^ j ≤ (s + 1) ^ max j 1 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : s + 1 ≤ (s + 1) ^ max j 1 := by
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ max j 1 := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have h3 : (T + e + 4) * (s + 1) ^ max j 1 =
      T * (s + 1) ^ max j 1 + (e + 4) * (s + 1) ^ max j 1 := by ring
  have h4 : (e + 4) * (s + 1) ≤ (e + 4) * (s + 1) ^ max j 1 := Nat.mul_le_mul_left _ h2
  have h5 : T * (s + 1) ^ j ≤ T * (s + 1) ^ max j 1 := Nat.mul_le_mul_left _ h1
  nlinarith

/-! ## The frozen sampler -/

namespace CL.Sampler

variable {ℓ : ℕ} (S : Sampler ℓ)

/-- The sampler frozen at index `k`: at every index it presents the CL functions of `S` at
index `k`, its program being `freezeProg k S.prog`. -/
def freeze (k : ℕ) : Sampler ℓ where
  prog := Prog.freezeProg k S.prog
  closed := Prog.freezeProg_wellScoped S.closed k
  dim _ := S.dim k
  cl _ w := S.cl k w
  cl_exactlyOn _ w := S.cl_exactlyOn k w
  runs_dimension _ :=
    let ⟨_, h⟩ := S.runs_dimension k
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  runs_marginal _ w j z h₁ h₂ hz :=
    let ⟨_, h⟩ := S.runs_marginal k w j z h₁ h₂ hz
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  runs_linear _ w j u y h₁ h₂ hu hy :=
    let ⟨_, h⟩ := S.runs_linear k w j u y h₁ h₂ hu hy
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  runs_factor _ w j u h₁ h₂ hu :=
    let ⟨_, h⟩ := S.runs_factor k w j u h₁ h₂ hu
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  halts _ d :=
    let ⟨r, _, h⟩ := S.halts k d
    ⟨r, _, Prog.freezeProg_runs S.closed h⟩

@[simp] theorem freeze_prog (k : ℕ) : (S.freeze k).prog = Prog.freezeProg k S.prog := rfl

@[simp] theorem freeze_dim (k n : ℕ) : (S.freeze k).dim n = S.dim k := rfl

@[simp] theorem freeze_cl (k n : ℕ) (w : Player) : (S.freeze k).cl n w = S.cl k w := rfl

theorem freeze_dist (k n : ℕ) : (S.freeze k).dist n = S.dist k := rfl

theorem freeze_size (k : ℕ) : (S.freeze k).size = S.size + esize k + 53 :=
  Prog.esize_freezeProg k S.prog

/-- The frozen sampler's running time at any index is that of `S` at the frozen index, up
to the cost of copying the input. -/
theorem freeze_timeBoundAt {k T j : ℕ} (h : S.TimeBoundAt k T j) (n : ℕ) :
    (S.freeze k).TimeBoundAt n (T + esize k + 4) (max j 1) := by
  intro d
  obtain ⟨r, t, ht, hrun⟩ := h d
  exact ⟨r, t + esize k + d.size + 4, freeze_cost_le ht, Prog.freezeProg_runs S.closed hrun⟩

end CL.Sampler

/-! ## The frozen decider -/

namespace Decider

variable (D : Decider)

/-- The decider frozen at index `k`: at every index it decides as `D` does at index `k`. -/
def freeze (k : ℕ) : Decider :=
  ⟨Prog.freezeProg k D.prog, Prog.freezeProg_wellScoped D.closed k⟩

@[simp] theorem freeze_prog (k : ℕ) : (D.freeze k).prog = Prog.freezeProg k D.prog := rfl

theorem freeze_accepts (k n : ℕ) (x y a b : BitStr) :
    (D.freeze k).Accepts n x y a b ↔ D.Accepts k x y a b :=
  Prog.freezeProg_runs_iff D.closed k (encode n) (encode (x, y, a, b)) (encode true)

theorem freeze_size (k : ℕ) : (D.freeze k).size = D.size + esize k + 53 :=
  Prog.esize_freezeProg k D.prog

theorem freeze_timeBoundAt {k T j : ℕ} (h : D.TimeBoundAt k T j) (n : ℕ) :
    (D.freeze k).TimeBoundAt n (T + esize k + 4) (max j 1) := by
  intro d
  obtain ⟨r, t, ht, hrun⟩ := h d
  exact ⟨r, t + esize k + d.size + 4, freeze_cost_le ht, Prog.freezeProg_runs D.closed hrun⟩

end Decider

/-! ## The frozen verifier -/

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The verifier frozen at index `k`: its game at every index is the game of `V` at index
`k`. -/
def freeze (k : ℕ) : Verifier ℓ where
  sampler := V.sampler.freeze k
  decider := V.decider.freeze k
  accepts_length _ x y a b h := V.accepts_length k x y a b ((V.decider.freeze_accepts k _ x y a b).1 h)

@[simp] theorem freeze_sampler (k : ℕ) : (V.freeze k).sampler = V.sampler.freeze k := rfl

@[simp] theorem freeze_decider (k : ℕ) : (V.freeze k).decider = V.decider.freeze k := rfl

theorem freeze_size (k : ℕ) : (V.freeze k).size = V.size + esize k + 53 := by
  simp only [size, freeze_sampler, freeze_decider, CL.Sampler.freeze_size, Decider.freeze_size]
  omega

theorem freeze_isSynchronousAt (k n : ℕ) :
    (V.freeze k).IsSynchronousAt n ↔ V.IsSynchronousAt k := by
  simp only [IsSynchronousAt, freeze_decider, Decider.freeze_accepts]

/-- The value of the frozen verifier at any index is the value of `V` at the frozen index. -/
theorem freeze_valStar (k n T : ℕ) : (V.freeze k).valStar n T = V.valStar k T := by
  unfold valStar
  refine quantumValue_eq_of_equiv (V.game k T) ((V.freeze k).game n T) (Equiv.refl _)
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (fun _ _ => rfl) fun x y a b => ?_
  exact decide_eq_decide.2 (V.decider.freeze_accepts k n _ _ _ _)

/-- The frozen verifier has a perfect PCC strategy at any index exactly when `V` has one at
the frozen index. -/
theorem freeze_hasPerfectPCC (k n T : ℕ) :
    (V.freeze k).HasPerfectPCC n T ↔ V.HasPerfectPCC k T := by
  constructor
  · rintro ⟨hs, S, hpcc, hval⟩
    have hs' : V.IsSynchronousAt k := (V.freeze_isSynchronousAt k n).1 hs
    refine ⟨hs', S.copy (V.syncGame k T hs'), S.isPCC_copy hpcc _ (fun _ _ => rfl), ?_⟩
    exact (S.value_copy (V.syncGame k T hs') (fun _ _ => rfl) fun x y a b =>
      decide_eq_decide.2 (V.decider.freeze_accepts k n _ _ _ _).symm).trans hval
  · rintro ⟨hs, S, hpcc, hval⟩
    have hs' : (V.freeze k).IsSynchronousAt n := (V.freeze_isSynchronousAt k n).2 hs
    refine ⟨hs', S.copy ((V.freeze k).syncGame n T hs'), S.isPCC_copy hpcc _ (fun _ _ => rfl),
      ?_⟩
    exact (S.value_copy ((V.freeze k).syncGame n T hs') (fun _ _ => rfl) fun x y a b =>
      decide_eq_decide.2 (V.decider.freeze_accepts k n _ _ _ _)).trans hval

/-- **`λ`-boundedness of the frozen verifier.** The frozen verifier is `λ`-bounded when the
dimension and the running times of `V` at the frozen index, shifted by the cost of freezing,
fit under `2 ^ λ`, and its size, shifted by the size of the index, fits under `λ`. -/
theorem freeze_isBounded (k lam TS TD jS jD : ℕ) (hS : V.sampler.TimeBoundAt k TS jS)
    (hD : V.decider.TimeBoundAt k TD jD) (hdim : V.sampler.dim k ≤ 2 ^ lam)
    (hTS : TS + esize k + 4 ≤ 2 ^ lam) (hTD : TD + esize k + 4 ≤ 2 ^ lam)
    (hjS : max jS 1 ≤ lam) (hjD : max jD 1 ≤ lam)
    (hsize : V.size + esize k + 53 ≤ lam) : (V.freeze k).IsBounded lam := by
  refine ⟨fun n hn => ?_, ?_⟩
  · have h2 : 2 ^ lam ≤ n ^ lam := Nat.pow_le_pow_left hn lam
    refine ⟨?_, ?_, ?_⟩
    · exact (V.sampler.freeze_dim k n).le.trans (hdim.trans h2)
    · exact (V.sampler.freeze_timeBoundAt hS n).mono (hTS.trans h2) hjS
    · exact (V.decider.freeze_timeBoundAt hD n).mono (hTD.trans h2) hjD
  · rw [V.freeze_size k]; exact hsize

end Verifier

end MIPRE
