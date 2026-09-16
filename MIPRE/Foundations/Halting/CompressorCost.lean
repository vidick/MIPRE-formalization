/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Compressor
import MIPRE.Foundations.Halting.WrapperCost
import MIPRE.Foundations.Halting.Absorb

/-!
# The compressor's output is bounded: the accounting

Obligation O4, the accounting half: the verifier the compressor's output denotes is
`n`-bounded at every level `n` past a threshold depending on `G` and `U` alone — the field
`CompressorSpec.isBounded_compr` — and the parameter `λ(n)` it carries satisfies the growth
conditions `lam_ge` and `ansBound_le`.

The parameter is `λ(n) = 2 ^ (2 · size n)`, a `1` followed by zeros, so that the compressor can
write it in binary in time polynomial in `log n`; it is at least `(n + 1) ^ 2`, which is what
freezing the described verifier at index `2n + 1` needs (`Verifier.freeze_isBounded` through
`CompressorSpec.lam_ge`).

`Verifier.IsBounded n` has three clauses at every index `m ≥ 2` and a size clause, and each is
absorbed by `PolyBounded.absorb` or `PolyBounded.absorb_log` (`Halting/Absorb.lean`) once the
cost is written as a polynomially bounded function of the largest of the index, the level and
the input size:

* the sampler is `G.sampler (λ(n))`, whose dimension and running time at index `m` are
  `G.bound (m + λ(n))` (`GapCompression.sampler_dim`, `sampler_time`);
* the decider is the wrapper around `haltProg` with `(c, n, λ(n))` hardcoded, whose cost on an
  input `d` is `Prog.wrapCoreCost` (`Halting/WrapperCost.lean`) with the inner cost
  `innerBound`: the preparation (`prepBound`), the universal machine on the compressed decider,
  and the compressed decider's own time `G.bound (m + λ(n)) · (|d| + 1) ^ G.deg`
  (`GapCompression.decider_time`);
* the size is that of the compressed sampler's program, polynomial in `log n`, and of the
  wrapper's description, which carries `c` — the slack `2|c| ≤ n` of the criterion is what
  leaves room for it.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.Prog.ProgD

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The parameter -/

/-- **The parameter the output carries at level `n`**: `2 ^ (2 · size n)`. -/
def lamOf (n : ℕ) : ℕ := 2 ^ (2 * Nat.size n)

theorem polyBounded_lamOf : PolyBounded lamOf :=
  (PolyBounded.two_pow_size 0 2).mono fun n => by simp [lamOf]

theorem size_lamOf (n : ℕ) : Nat.size (lamOf n) = 2 * Nat.size n + 1 := by
  rw [lamOf, Nat.size_pow]

theorem esize_lamOf_le (n : ℕ) : esize (lamOf n) ≤ 8 * Nat.size n + 5 := by
  have := esize_nat_le (lamOf n)
  rw [size_lamOf] at this
  omega

/-- `λ(n) ≥ (n + 1) ^ 2`. -/
theorem sq_le_lamOf (n : ℕ) : (n + 1) ^ 2 ≤ lamOf n := by
  rw [lamOf, Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_size_self n) 2

/-- `λ(n)` is monotone. -/
theorem lamOf_mono {n n' : ℕ} (h : n ≤ n') : lamOf n ≤ lamOf n' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.size_le_size h))

/-! ## The output's verifier -/

/-- The decider program the output carries: `haltProg` with `(c, n, λ)` hardcoded. -/
def outDec (c : Prog) (n lam : ℕ) : Prog := hardcode (haltProg G U) (encode (c, n, lam))

theorem esize_outDec (c : Prog) (n lam : ℕ) :
    esize (outDec G U c n lam) = esize (haltProg G U) + esize c + esize n + esize lam + 37 := by
  rw [outDec, hardcode_size]
  have : (encode (c, n, lam) : Data).size = esize c + (esize n + esize lam + 1) + 1 := rfl
  omega

theorem Vof_comprStr' (c : Prog) (n lam : ℕ) :
    Vof G U (comprStr G U c n lam) = Verifier.ofSamplerDecider U (G.sampler lam) (outDec G U c n lam) :=
  Vof_comprStr G U c n lam

/-! ## The sampler clauses -/

/-- The dimension and running-time bound of the compressed sampler at `λ(n)`, index `m`, as
a polynomially bounded function of the largest of `m` and `n`. -/
noncomputable def sampZ (z : ℕ) : ℕ := G.bound.eval (z + lamOf z)

theorem polyBounded_sampZ : PolyBounded (sampZ G) :=
  PolyBounded.eval _ (PolyBounded.id.add polyBounded_lamOf)

theorem bound_le_sampZ {m n z : ℕ} (hm : m ≤ z) (hn : n ≤ z) :
    G.bound.eval (m + lamOf n) ≤ sampZ G z :=
  polynomial_eval_mono _ (Nat.add_le_add hm (lamOf_mono hn))

/-- **The sampler clauses**: past a threshold, at every index `m ≥ 2` the compressed sampler at
`λ(n)` has dimension at most `m ^ n` and runs within `m ^ n · (|d| + 1) ^ n`. -/
theorem sampler_clauses : ∃ n₀, ∀ n, n₀ ≤ n → ∀ m, 2 ≤ m →
    (G.sampler (lamOf n)).dim m ≤ m ^ n ∧ (G.sampler (lamOf n)).TimeBoundAt m (m ^ n) n := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_sampZ G).absorb
  refine ⟨max n₀ G.deg, fun n hn m hm => ?_⟩
  have h1 : G.bound.eval (m + lamOf n) ≤ m ^ n := by
    have := hn₀ n (le_trans (le_max_left _ _) hn) m hm 1 le_rfl
    rw [one_pow, mul_one, mul_one] at this
    exact (bound_le_sampZ G (by omega) (by omega)).trans this
  exact ⟨(G.sampler_dim _ m).trans h1,
    (G.sampler_time (lamOf n) m).mono h1 (le_trans (le_max_right _ _) hn)⟩

/-! ## The size clause -/

/-- The size of the output's verifier, beyond the description `c` it carries, as a function of
`size n`. -/
noncomputable def sizeZ (s : ℕ) : ℕ :=
  G.samplerProg.timeBound.eval (8 * s + 5) + 12 * s +
    (esize (haltProg G U) + 2 * esize U.univ + wrapNodes + 43)

theorem polyBounded_sizeZ : PolyBounded (sizeZ G U) :=
  ((PolyBounded.eval _ ((PolyBounded.id.const_mul 8).add_const 5)).add
    (PolyBounded.id.const_mul 12)).add_const _

/-- The compressed sampler's program at `λ(n)` has size polynomial in `size n`. -/
theorem esize_sampler_le (n : ℕ) :
    esize (G.sampler (lamOf n)).prog ≤ G.samplerProg.timeBound.eval (8 * Nat.size n + 5) := by
  rw [← G.samplerProg_eq]
  exact (G.samplerProg.esize_apply_le (lamOf n)).trans
    (polynomial_eval_mono _ (esize_lamOf_le n))

/-- The output's decider — the wrapper around `outDec` — has size at most
`|c| + sizeZ (size n)`. -/
theorem esize_wrapCore_le (c : Prog) (n : ℕ) :
    esize (wrapCore U.univ (G.sampler (lamOf n)).prog (encode (outDec G U c n (lamOf n)))) ≤
      esize c + sizeZ G U (Nat.size n) := by
  show (encode (wrapCore U.univ (G.sampler (lamOf n)).prog (encode (outDec G U c n (lamOf n)))) :
    Data).size ≤ _
  rw [← dWrapCore_eq, size_dWrapCore]
  have h1 : (encode (G.sampler (lamOf n)).prog : Data).size = esize (G.sampler (lamOf n)).prog := rfl
  have h2 : (encode (outDec G U c n (lamOf n)) : Data).size = esize (outDec G U c n (lamOf n)) := rfl
  have h3 : (encode U.univ : Data).size = esize U.univ := rfl
  have h4 := esize_sampler_le G n
  have h5 := esize_outDec G U c n (lamOf n)
  have h6 := esize_lamOf_le n
  have h7 : esize n ≤ 4 * Nat.size n + 1 := esize_nat_le n
  rw [h1, h2, h3, h5]
  simp only [sizeZ]
  omega

/-- **The size clause**: past a threshold, a description of size at most `n / 2` yields an
output whose verifier has size at most `n`. -/
theorem size_clause : ∃ n₀, ∀ n, n₀ ≤ n → ∀ c : Prog, 2 * esize c ≤ n →
    (Vof G U (comprStr G U c n (lamOf n))).size ≤ n := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_sizeZ G U).absorb_log 0 1
  refine ⟨n₀, fun n hn c hc => ?_⟩
  have h := hn₀ n hn
  simp only [Nat.zero_add, Nat.one_mul] at h
  rw [Vof_comprStr', Verifier.size]
  refine max_le ?_ ?_
  · exact (esize_sampler_le G n).trans (by simp only [sizeZ] at h ⊢; omega)
  · exact (esize_wrapCore_le G U c n).trans (by omega)


/-! ## The decider clause

The output's decider is the wrapper around `outDec`; its cost on an input `d` at index `m` is
`Prog.wrapCoreCost` with the inner cost `innerBound` below. Both are then bounded by a
polynomially bounded function `decZ` of the largest of the index `m`, the level `n` and the
input size `|d|`, and absorbed. -/

/-- The inner decider's cost at index `m` on an input of size `t`: for a description of size
`s` of a string of length `L`, at level `n` and parameter `lam` of size `l`. The sizes of the
binary numerals `m` and `n` appear as `4 · size + 1`, so that the bound is monotone. -/
noncomputable def innerBound (s n L lam l m t : ℕ) : ℕ :=
  3 * prepBound G U s n L l + 2 * (s + (4 * Nat.size n + 1) + l + 2) +
    3 * ((4 * Nat.size m + 1) + t + 1) +
    U.bound.eval (G.compress.timeBound.eval (fBound G U L n + l + 2) +
      ((4 * Nat.size m + 1) + t + 1) + G.bound.eval (m + lam) * (t + 1) ^ G.deg) + 15

/-- **The inner decider's cost.** On a succinct description `(c, n)` of `x`, `outDec` with
`(c, n, λ)` runs within `innerBound` on every input at every index: the compressed decider's
own time (`GapCompression.decider_time`), simulated by the universal machine, after the
preparation. -/
theorem outDec_cost {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam m : ℕ)
    (d : Data) :
    ∃ r t, t ≤ innerBound G U (esize c) n x.length lam (esize lam) m d.size ∧
      (outDec G U c n lam).Runs (.cons (encode m) d) r t := by
  obtain ⟨r, t₁, ht₁, h₁⟩ := G.decider_time
    ((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog) lam m d
  rw [G.output_decider] at h₁
  obtain ⟨t₂, ht₂, h₂⟩ := U.time_le _ _ _ _ h₁
  obtain ⟨t₃, ht₃, h₃⟩ := haltProg_runs G U hsd lam (d := .cons (encode m) d) h₂
  refine ⟨r, _, ?_, hardcode_time (haltProg_wellScoped G U) h₃⟩
  -- the sizes
  have hcmp : esize (G.compress (((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog),
      lam)) ≤ G.compress.timeBound.eval (fBound G U x.length n + esize lam + 2) := by
    refine (G.compress.esize_apply_le _).trans (polynomial_eval_mono _ ?_)
    have := esize_frozen_le G U x n
    simp only [esize_prod]; omega
  have hP : (encode (c, n, lam) : Data).size = esize c + (esize n + esize lam + 1) + 1 := rfl
  have hP' : esize (c, n, lam) = esize c + (esize n + esize lam + 1) + 1 := rfl
  have hin : (Data.cons (encode m) d).size = esize m + d.size + 1 := rfl
  have hm : esize m ≤ 4 * Nat.size m + 1 := esize_nat_le m
  have hn : esize n ≤ 4 * Nat.size n + 1 := esize_nat_le n
  have ht₂' : t₂ ≤ U.bound.eval (G.compress.timeBound.eval (fBound G U x.length n + esize lam + 2) +
      ((4 * Nat.size m + 1) + d.size + 1) + G.bound.eval (m + lam) * (d.size + 1) ^ G.deg) :=
    ht₂.trans (polynomial_eval_mono _ (by rw [hin]; omega))
  simp only [innerBound]
  omega

/-- **The output's decider, on every input.** -/
theorem outDec_wrap_cost {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (m : ℕ)
    (d : Data) :
    ∃ r t, t ≤ wrapCoreCost U (G.sampler (lamOf n)) (outDec G U c n (lamOf n))
        (fun m => G.bound.eval (m + lamOf n)) G.deg m
        (innerBound G U (esize c) n x.length (lamOf n) (esize (lamOf n)) m d.size) d.size ∧
      (wrapCore U.univ (G.sampler (lamOf n)).prog (encode (outDec G U c n (lamOf n)))).Runs
        (.cons (encode m) d) r t :=
  wrapCore_cost' U (G.sampler (lamOf n)) (outDec G U c n (lamOf n)) _ G.deg
    (fun m d => G.sampler_time (lamOf n) m d) m _
    (fun d => outDec_cost G U hsd (lamOf n) m d) d

/-! ### Monotonicity and polynomial boundedness of the bounds -/

section Bounds

attribute [local gcongr] polynomial_eval_mono Nat.size_le_size

theorem readIter_mono {s s' n n' L L' : ℕ} (hs : s ≤ s') (hn : n ≤ n') (hL : L ≤ L') :
    readIter U s n L ≤ readIter U s' n' L' := by
  unfold readIter; gcongr

theorem sampBound_mono {L L' : ℕ} (hL : L ≤ L') : sampBound G L ≤ sampBound G L' :=
  polynomial_eval_mono _ (by omega)

theorem wBound_mono {L L' : ℕ} (hL : L ≤ L') : wBound G U L ≤ wBound G U L' := by
  unfold wBound; have := sampBound_mono G hL; omega

theorem kBound_mono {n n' : ℕ} (hn : n ≤ n') : kBound n ≤ kBound n' := by
  unfold kBound; have := Nat.size_le_size hn; omega

theorem fBound_mono {L L' n n' : ℕ} (hL : L ≤ L') (hn : n ≤ n') :
    fBound G U L n ≤ fBound G U L' n' := by
  unfold fBound
  have := sampBound_mono G hL; have := wBound_mono G U hL; have := kBound_mono hn; omega

attribute [local gcongr] readIter_mono sampBound_mono wBound_mono kBound_mono fBound_mono

theorem prepBound_mono {s s' n n' L L' l l' : ℕ} (hs : s ≤ s') (hn : n ≤ n') (hL : L ≤ L')
    (hl : l ≤ l') : prepBound G U s n L l ≤ prepBound G U s' n' L' l' := by
  unfold prepBound; gcongr

attribute [local gcongr] prepBound_mono

theorem innerBound_mono {s s' n n' L L' lam lam' l l' m m' t t' : ℕ} (hs : s ≤ s') (hn : n ≤ n')
    (hL : L ≤ L') (hlam : lam ≤ lam') (hl : l ≤ l') (hm : m ≤ m') (ht : t ≤ t') :
    innerBound G U s n L lam l m t ≤ innerBound G U s' n' L' lam' l' m' t' := by
  unfold innerBound; gcongr

end Bounds

/-! `PolyBounded` for each bound, with every argument the same `z`. -/

section Poly

theorem polyBounded_readIter : PolyBounded fun z => readIter U z z (z + 1) := by
  have hz := PolyBounded.id
  have hL : PolyBounded fun z : ℕ => z + 1 := hz.add_const 1
  have hsz : PolyBounded fun z : ℕ => Nat.size (z + 1) := PolyBounded.size.comp hL
  unfold readIter
  exact (((((PolyBounded.eval _ ((hz.add ((hsz.const_mul 4).add_const 1)).add
    ((hz.add_const 1).mul ((hsz.add_const 1).pow 2)))).add (hz.const_mul 3)).add
    (((hsz.const_mul 4).add_const 1).const_mul 4)).add ((hL.const_mul 4).add_const 1)).add
    ((((hsz.add_const 2).mul (((((hsz.const_mul 4).add_const 1).const_mul 8).add
      (hsz.const_mul 8)).add_const 60))).const_mul 2)).add_const 30

theorem polyBounded_sampBound : PolyBounded fun z => sampBound G (z + 1) :=
  PolyBounded.eval _ (PolyBounded.id.add_const 1 |>.add_const 1)

theorem polyBounded_wBound : PolyBounded fun z => wBound G U (z + 1) := by
  unfold wBound
  exact (((polyBounded_sampBound G).add (PolyBounded.id.add_const 1 |>.add_const 1)).add_const
    (2 * esize U.univ)).add_const wrapNodes

theorem polyBounded_kBound : PolyBounded kBound :=
  (PolyBounded.size.const_mul 4).add_const 5

theorem polyBounded_fBound : PolyBounded fun z => fBound G U (z + 1) z := by
  unfold fBound
  exact ((((polyBounded_sampBound G).add polyBounded_kBound).add_const 53).add
    ((((polyBounded_wBound G U).add polyBounded_kBound).add_const 53)))

/-- The size of `λ(z)`'s encoding, as the bound `8 · size z + 5`. -/
theorem polyBounded_lsize : PolyBounded fun z => 8 * Nat.size z + 5 :=
  (PolyBounded.size.const_mul 8).add_const 5

theorem polyBounded_prepBound :
    PolyBounded fun z => prepBound G U z z (z + 1) (8 * Nat.size z + 5) := by
  have hz := PolyBounded.id
  have hL : PolyBounded fun z : ℕ => z + 1 := hz.add_const 1
  unfold prepBound
  refine ((((((((((hL.mul ((polyBounded_readIter U).add_const 1)).add
    ((hz.add_const 2).mul ((hz.const_mul 4).add_const 14))).add hz).add_const 7).add
    ((hz.add_const 2).mul ((((hz.const_mul 4).add_const 1).add (hz.const_mul 2)).add_const 25))).add
    ((hz.const_mul 4).add_const 1)).add
    (((hz.add_const 3).mul (hz.add_const 26)).add ((hL.const_mul 3).add_const 10))).add
    ((((polyBounded_sampBound G).add (polyBounded_wBound G U)).add (polyBounded_fBound G U)).add
      (PolyBounded.eval _ (((polyBounded_fBound G U).add polyBounded_lsize).add_const 2)))).add
    ((((((hz.const_mul 2).add (((hz.const_mul 4).add_const 1).const_mul 4)).add
      (hL.const_mul 12)).add ((polyBounded_sampBound G).const_mul 2)).add
      ((polyBounded_wBound G U).const_mul 3)).add (polyBounded_kBound.const_mul 6))).add
    ((((polyBounded_fBound G U).const_mul 2).add (polyBounded_lsize.const_mul 2)).add_const 200)).add
    ((hz.const_mul 22).add ((polyBounded_readIter U).add_const 136)) |>.mono
    fun z => by ring_nf; omega

theorem polyBounded_innerBound :
    PolyBounded fun z => innerBound G U z z (z + 1) (lamOf z) (8 * Nat.size z + 5) z z := by
  have hz := PolyBounded.id
  have hsz := PolyBounded.size
  have hm : PolyBounded fun z : ℕ => 4 * Nat.size z + 1 + z + 1 :=
    (((hsz.const_mul 4).add_const 1).add hz).add_const 1
  unfold innerBound
  exact (((((polyBounded_prepBound G U).const_mul 3).add
    ((((hz.add ((hsz.const_mul 4).add_const 1)).add polyBounded_lsize).add_const 2).const_mul 2)).add
    (hm.const_mul 3)).add
    (PolyBounded.eval _ (((PolyBounded.eval _ (((polyBounded_fBound G U).add
      polyBounded_lsize).add_const 2)).add hm).add
      ((PolyBounded.eval _ (hz.add polyBounded_lamOf)).mul ((hz.add_const 1).pow G.deg))))).add_const 15

end Poly


/-! ### The master bound, and the clause -/

section Master

/-- The size of the compressed sampler's program, in `z`. -/
noncomputable def sigZ (z : ℕ) : ℕ := G.samplerProg.timeBound.eval (8 * Nat.size z + 5)
/-- The size of the output's inner decider `outDec`, in `z`. -/
def deltaZ (z : ℕ) : ℕ :=
  esize (haltProg G U) + z + (4 * Nat.size z + 1) + (8 * Nat.size z + 5) + 37
/-- The inner cost, in `z`. -/
noncomputable def iotaZ (z : ℕ) : ℕ :=
  innerBound G U z z (z + 1) (lamOf z) (8 * Nat.size z + 5) z z
/-- `wrapHeadZ`, in `z`. -/
noncomputable def headZ (z : ℕ) : ℕ :=
  sigZ G z + (4 * Nat.size z + 1) + (encode CL.Sampler.Query.dimension : Data).size +
    (4 * sampZ G z + 1) + sampZ G z * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg +
    U.bound.eval (sigZ G z + ((4 * Nat.size z + 1) + (encode CL.Sampler.Query.dimension : Data).size + 1) +
      sampZ G z * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg) +
    (sampZ G z + 2) * ((sampZ G z + 1) * (4 * sampZ G z + 14) + 7 * (4 * sampZ G z + 1) +
      8 * sampZ G z + 90) + 10
/-- **The master bound**: `wrapCoreCost` with every atom replaced by its bound in `z`. -/
noncomputable def decZ (z : ℕ) : ℕ :=
  (60 * headZ G U z ^ 2 + 4) + 2 * (60 * (z + sampZ G z + 30) ^ 2) +
    (2 * (deltaZ G U z + (4 * Nat.size z + 1) + z + 2) +
      U.bound.eval (deltaZ G U z + ((4 * Nat.size z + 1) + z + 1) + iotaZ G U z)) + 20

theorem polyBounded_sigZ : PolyBounded (sigZ G) :=
  PolyBounded.eval _ ((PolyBounded.size.const_mul 8).add_const 5)

theorem polyBounded_deltaZ : PolyBounded (deltaZ G U) :=
  ((((PolyBounded.const _).add PolyBounded.id).add ((PolyBounded.size.const_mul 4).add_const 1)).add
    ((PolyBounded.size.const_mul 8).add_const 5)).add_const 37

theorem polyBounded_iotaZ : PolyBounded (iotaZ G U) := polyBounded_innerBound G U

theorem polyBounded_headZ : PolyBounded (headZ G U) := by
  have hσ := polyBounded_sigZ G
  have hβ := polyBounded_sampZ G
  have hs : PolyBounded fun z : ℕ => 4 * Nat.size z + 1 := (PolyBounded.size.const_mul 4).add_const 1
  unfold headZ
  exact (((((((hσ.add hs).add (PolyBounded.const _)).add ((hβ.const_mul 4).add_const 1)).add
    (hβ.mul (PolyBounded.const _))).add
    (PolyBounded.eval _ ((hσ.add ((hs.add_const _).add_const 1)).add (hβ.mul (PolyBounded.const _))))).add
    ((hβ.add_const 2).mul ((((hβ.add_const 1).mul ((hβ.const_mul 4).add_const 14)).add
      (((hβ.const_mul 4).add_const 1).const_mul 7)).add ((hβ.const_mul 8).add_const 90)))).add_const 10)

theorem polyBounded_decZ : PolyBounded (decZ G U) := by
  have hz := PolyBounded.id
  have hs : PolyBounded fun z : ℕ => 4 * Nat.size z + 1 := (PolyBounded.size.const_mul 4).add_const 1
  have hδ := polyBounded_deltaZ G U
  unfold decZ
  exact (((((polyBounded_headZ G U).pow 2).const_mul 60 |>.add_const 4).add
    (((((hz.add (polyBounded_sampZ G)).add_const 30).pow 2).const_mul 60).const_mul 2)).add
    (((((hδ.add hs).add hz).add_const 2).const_mul 2).add
      (PolyBounded.eval _ ((hδ.add ((hs.add hz).add_const 1)).add (polyBounded_iotaZ G U))))).add_const 20

attribute [local gcongr] polynomial_eval_mono Nat.size_le_size innerBound_mono

/-- **The output's decider cost is below the master bound** at the largest `z` of the index,
the level and the input size. -/
theorem wrapCoreCost_le_decZ {c : Prog} {x : BitStr} {n m t z : ℕ} (hc : esize c ≤ n)
    (hx : x.length ≤ n + 1) (hm : m ≤ z) (hn : n ≤ z) (ht : t ≤ z) :
    wrapCoreCost U (G.sampler (lamOf n)) (outDec G U c n (lamOf n))
        (fun m => G.bound.eval (m + lamOf n)) G.deg m
        (innerBound G U (esize c) n x.length (lamOf n) (esize (lamOf n)) m t) t ≤ decZ G U z := by
  -- the atoms
  have hσ : esize (G.sampler (lamOf n)).prog ≤ sigZ G z :=
    (esize_sampler_le G n).trans (polynomial_eval_mono _ (by have := Nat.size_le_size hn; omega))
  have hem : esize m ≤ 4 * Nat.size z + 1 :=
    (esize_nat_le m).trans (by have := Nat.size_le_size hm; omega)
  have hen : esize n ≤ 4 * Nat.size z + 1 :=
    (esize_nat_le n).trans (by have := Nat.size_le_size hn; omega)
  have hel : esize (lamOf n) ≤ 8 * Nat.size z + 5 :=
    (esize_lamOf_le n).trans (by have := Nat.size_le_size hn; omega)
  have hβ : G.bound.eval (m + lamOf n) ≤ sampZ G z := bound_le_sampZ G hm hn
  have hdim : (G.sampler (lamOf n)).dim m ≤ sampZ G z := (G.sampler_dim _ m).trans hβ
  have hedim : esize ((G.sampler (lamOf n)).dim m) ≤ 4 * sampZ G z + 1 :=
    (esize_nat_le _).trans (by
      have := Nat.size_le.2 (Nat.lt_two_pow_self (n := (G.sampler (lamOf n)).dim m)); omega)
  have hsdim : Nat.size ((G.sampler (lamOf n)).dim m) ≤ sampZ G z :=
    (Nat.size_le.2 (Nat.lt_two_pow_self)).trans hdim
  have hδ : esize (outDec G U c n (lamOf n)) ≤ deltaZ G U z := by
    rw [esize_outDec, deltaZ]; omega
  have hι : innerBound G U (esize c) n x.length (lamOf n) (esize (lamOf n)) m t ≤ iotaZ G U z :=
    innerBound_mono G U (by omega) hn (by omega) (lamOf_mono hn) hel hm ht
  have hcheck : checkCost t ((G.sampler (lamOf n)).dim m) ≤ 60 * (z + sampZ G z + 30) ^ 2 := by
    unfold checkCost; gcongr
  have hhead : wrapHeadZ U (G.sampler (lamOf n)) (fun m => G.bound.eval (m + lamOf n)) G.deg m ≤
      headZ G U z := by
    unfold wrapHeadZ headZ; gcongr
  unfold wrapCoreCost decZ
  gcongr

/-- **The decider clause**: past a threshold, on a succinct description `(c, n)` of a string
of length at most `n + 1` with `2|c| ≤ n`, the output's decider runs within
`m ^ n · (|d| + 1) ^ n` at every index `m ≥ 2`. -/
theorem decider_clause : ∃ n₀, ∀ n, n₀ ≤ n → ∀ (c : Prog) (x : BitStr), 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 → ∀ m, 2 ≤ m →
    (Vof G U (comprStr G U c n (lamOf n))).decider.TimeBoundAt m (m ^ n) n := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_decZ G U).absorb
  refine ⟨n₀, fun n hn c x hc hsd hx m hm d => ?_⟩
  rw [Vof_comprStr']
  show HaltsWithin (wrapCore U.univ (G.sampler (lamOf n)).prog (encode (outDec G U c n (lamOf n))))
    (.cons (encode m) d) _
  obtain ⟨r, t, ht, hrun⟩ := outDec_wrap_cost G U hsd m d
  refine ⟨r, t, ht.trans ?_, hrun⟩
  have hz := hn₀ n hn m hm (d.size + 1) (by omega)
  refine le_trans (wrapCoreCost_le_decZ G U (by omega) hx ?_ ?_ ?_) hz
  · nlinarith
  · nlinarith
  · nlinarith

end Master

/-! ## The output is bounded -/

/-- **The field `isBounded_compr`.** -/
theorem isBounded_comprStr : ∃ n₀, ∀ n, n₀ ≤ n → ∀ (c : Prog) (x : BitStr), 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 →
    (Vof G U (comprStr G U c n (lamOf n))).IsBounded n := by
  obtain ⟨nS, hS⟩ := sampler_clauses G
  obtain ⟨nZ, hZ⟩ := size_clause G U
  obtain ⟨nD, hD⟩ := decider_clause G U
  refine ⟨max nS (max nZ nD), fun n hn c x hc hsd hx => ⟨fun m hm => ?_, ?_⟩⟩
  · have h1 := hS n (by omega) m hm
    have h2 := hD n (by omega) c x hc hsd hx m hm
    refine ⟨?_, ?_, h2⟩
    · rw [Vof_comprStr']; exact h1.1
    · rw [Vof_comprStr']; exact h1.2
  · exact hZ n (by omega) c hc

/-! ## The growth of the parameter -/

/-- `size (2n + 1) ≤ size n + 1`. -/
theorem size_two_mul_add_one_le (n : ℕ) : Nat.size (2 * n + 1) ≤ Nat.size n + 1 :=
  Nat.size_le.2 (by have := Nat.lt_size_self n; rw [pow_succ]; omega)

/-- **The field `lam_ge`**: the growth `Verifier.freeze_isBounded` needs of `λ(n)`. -/
theorem lamOf_ge : ∃ n₀, ∀ n, n₀ ≤ n →
    (2 * n + 1) ^ (2 * n + 1) + esize (2 * n + 1) + 4 ≤ 2 ^ lamOf n ∧
    2 * n + 1 + esize (2 * n + 1) + 53 ≤ lamOf n := by
  obtain ⟨n₀, hn₀⟩ := (PolyBounded.id.add_const 60).absorb_log 0 1
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  have h := hn₀ n (le_trans (le_max_left _ _) hn)
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  simp only [Nat.zero_add, Nat.one_mul] at h
  have hsq := sq_le_lamOf n
  have hes : esize (2 * n + 1) ≤ 4 * Nat.size n + 5 := by
    have := esize_nat_le (2 * n + 1); have := size_two_mul_add_one_le n; omega
  have hsz : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  refine ⟨?_, by nlinarith⟩
  -- `(2n+1)^(2n+1) ≤ 2^((size n + 1)(2n+1))`, and the exponent is below `(n+1)^2 ≤ λ(n)`
  have h1 : (2 * n + 1) ^ (2 * n + 1) ≤ 2 ^ ((Nat.size n + 1) * (2 * n + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.size_le.1 (size_two_mul_add_one_le n)).le _
  have h2 : (Nat.size n + 1) * (2 * n + 1) + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have h3 : esize (2 * n + 1) + 4 ≤ (2 * n + 1) ^ (2 * n + 1) := by
    have : (2 * n + 1) ^ 2 ≤ (2 * n + 1) ^ (2 * n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  calc (2 * n + 1) ^ (2 * n + 1) + esize (2 * n + 1) + 4
      ≤ 2 * 2 ^ ((Nat.size n + 1) * (2 * n + 1)) := by omega
    _ = 2 ^ ((Nat.size n + 1) * (2 * n + 1) + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ lamOf n := Nat.pow_le_pow_right (by norm_num) (h2.trans hsq)

/-- **The field `ansBound_le`**, from `exists_ansBound_le` at `λ(n) ≥ n + 1`. -/
theorem ansBound_le_lamOf : ∃ n₀, ∀ (x : BitStr) (n : ℕ), n₀ ≤ n → x.length ≤ n + 1 →
    ansBound G x (2 * n + 1) ≤ (2 ^ n) ^ lamOf n := by
  obtain ⟨lam₀, n₀, h⟩ := exists_ansBound_le G
  refine ⟨max lam₀ n₀, fun x n hn hx => h x (lamOf n) n ?_ (le_trans (le_max_right _ _) hn) hx⟩
  have := sq_le_lamOf n
  have := le_trans (le_max_left _ _) hn
  nlinarith

/-! ## The specification, given the compressor's program -/

/-- **The compressor meets its specification**, given a polynomial-time program computing
`comprStr c n (λ(n))` from `(c, n)`. Everything the specification asks is proved here or in
`Halting/Compressor.lean`; the program itself is the last piece of obligation O4. -/
theorem exists_compressorSpec (compr : PolyTimeFun (Prog × ℕ) BitStr)
    (hcompr : ∀ (c : Prog) (n : ℕ), compr (c, n) = comprStr G U c n (lamOf n)) :
    ∃ S : CompressorSpec G U, S.compr = compr ∧ S.lam = lamOf := by
  obtain ⟨nB, hB⟩ := isBounded_comprStr G U
  obtain ⟨nL, hL⟩ := lamOf_ge
  obtain ⟨nA, hA⟩ := ansBound_le_lamOf G
  refine ⟨{
    n₀ := max G.C₀ (max nB (max nL nA))
    C₀_le := le_max_left _ _
    compr := compr
    lam := lamOf
    descLam_compr := fun c n => by rw [hcompr]; exact descLam_comprStr G U c n _
    accepts_compr := fun c x n _ _ hsd _ m x' y' a b => by
      rw [hcompr]; exact comprStr_accepts G U hsd (lamOf n) m x' y' a b
    isBounded_compr := fun c x n hn hc hsd hx _ => by
      rw [hcompr]
      exact hB n (by omega) c x hc hsd hx
    lam_ge := fun n hn => hL n (by omega)
    ansBound_le := fun x n hn hx => hA x n (by omega) hx },
    rfl, rfl⟩

end MIPRE.Halting
