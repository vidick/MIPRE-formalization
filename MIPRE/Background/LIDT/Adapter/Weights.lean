/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Adapter.Strategy

/-!
# The seeded-CL adapter, part 5: both tests' distributions, as counts

The reduction's remaining obligation is a push-forward bound between the two tests' question
distributions, and both are defined as sums over a `Sample` type against an indicator. So the
first thing to do is to turn each into a *count*, after which the bound is arithmetic on
cardinalities rather than on sums.

* `clGame`'s distribution is uniform over its samples, so it is the number of samples producing
  the question pair, over the total (`clGame_μ_eq`).
* `lidtGame`'s is not uniform — its three subtests are weighted `1/3` each and its diagonal
  directions carry a factor `q^{-(j+1)}` — so the best that can be said in general is that it is
  the sum of the weights of the samples producing the pair (`lidtGame_μ_eq`). That sum is a
  singleton for the point and axis-parallel shapes and a geometric series over the admissible
  `j` for the diagonal one, which is where the `q^{χ s}` against `q^{j+1}` matching of
  `planning/lidt-cl-adapter.md` lives.
-/

namespace MIPRE.LIDT.Adapter

open Finset MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]

/-- **The canonical-line test's distribution, as a sum of sample weights.** -/
theorem lidtGame_μ_eq (x y : Question F m) :
    (lidtGame F m d).μ x y
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m => s.questions = (x, y)), s.weight := by
  classical
  show ∑ s : Sample F m, s.weight * (if s.questions = (x, y) then 1 else 0) = _
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun s _ => by
    by_cases h : s.questions = (x, y)
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]

/-- **The seeded test's distribution, as a count.** It is uniform over its samples, so the
weight of a question pair is the number of samples producing it over the total. -/
theorem clGame_μ_eq (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y
      = ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y))).card : ℝ)
          / (Fintype.card (CL.Sample F m) : ℝ) := by
  classical
  show ∑ sm : CL.Sample F m, (Fintype.card (CL.Sample F m) : ℝ)⁻¹ *
    (if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0) = _
  rw [← Finset.mul_sum, Finset.sum_boole, div_eq_inv_mul]

omit [DecidableEq F] [NeZero m] in
/-- The seeded test has at least one sample, so its total is nonzero. -/
theorem card_clSample_pos : 0 < Fintype.card (CL.Sample F m) :=
  Fintype.card_pos_iff.mpr ⟨⟨.point, .point, 0, 0, 0⟩⟩

/-! ## The canonical-line test, shape by shape

Each shape needs the set of samples producing a given question pair. For the point and
axis-parallel shapes it is a singleton and the weight is read off directly; the diagonal shape is
the one where several samples contribute. -/

omit [NeZero m] in
/-- **Only the self-consistency sample asks the same point twice.** -/
theorem filter_questions_point (u : Point F m) :
    Finset.univ.filter (fun s : Sample F m =>
        s.questions = ((Question.point u : Question F m), Question.point u))
      = {Sample.selfConsistency u} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro s hs
    have hq := (Finset.mem_filter.mp hs).2
    match s, hq with
    | Sample.selfConsistency u', hq =>
        have hq' : (Question.point u', Question.point (F := F) u')
            = (Question.point u, Question.point u) := hq
        injection hq' with h1 _
        injection h1 with h2
        rw [h2]
    | Sample.axis false u' i, hq =>
        exact absurd hq (by simp [Sample.questions])
    | Sample.axis true u' i, hq =>
        exact absurd hq (by simp [Sample.questions])
    | Sample.diag false u' j v, hq =>
        exact absurd hq (by simp [Sample.questions])
    | Sample.diag true u' j v, hq =>
        exact absurd hq (by simp [Sample.questions])

/-- **The canonical-line test's weight on a repeated point question**: the self-consistency
subtest has probability `1/3` and its point is uniform. -/
theorem lidtGame_μ_point (u : Point F m) :
    (lidtGame F m d).μ (.point u) (.point u)
      = 1 / (3 * Fintype.card (Point F m)) := by
  rw [lidtGame_μ_eq, filter_questions_point, Finset.sum_singleton]
  rfl

omit [NeZero m] in
/-- **Only one sample asks a given axis-parallel line against a given point.** The point pins the
sample's point, and the line pins its direction index, `Pi.single` being injective. -/
theorem filter_questions_axis (u : Point F m) (i : Fin m) :
    Finset.univ.filter (fun s : Sample F m =>
        s.questions
          = ((Question.axisLine (Line.through u (Pi.single i 1)) : Question F m),
              Question.point u))
      = {Sample.axis false u i} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro s hs
    have hq := (Finset.mem_filter.mp hs).2
    match s, hq with
    | Sample.axis false u' i', hq =>
        have hq' : ((Question.axisLine (Line.through u' (Pi.single i' 1)) : Question F m),
            Question.point u') = (Question.axisLine (Line.through u (Pi.single i 1)),
              Question.point u) := hq
        injection hq' with h1 h2
        injection h2 with hu
        subst hu
        injection h1 with hℓ
        have hdir : (Pi.single i' 1 : Point F m) = Pi.single i 1 := by
          simpa [through_single] using congrArg Prod.snd hℓ
        rw [single_inj hdir]
    | Sample.axis true u' i', hq => exact absurd hq (by simp [Sample.questions])
    | Sample.selfConsistency u', hq => exact absurd hq (by simp [Sample.questions])
    | Sample.diag false u' j v, hq => exact absurd hq (by simp [Sample.questions])
    | Sample.diag true u' j v, hq => exact absurd hq (by simp [Sample.questions])

/-- **The canonical-line test's weight on an axis-parallel line against a point.** The subtest has
probability `1/3`, the roles are swapped with probability `1/2`, and the point and direction index
are uniform. -/
theorem lidtGame_μ_axis (u : Point F m) (i : Fin m) :
    (lidtGame F m d).μ (.axisLine (Line.through u (Pi.single i 1))) (.point u)
      = 1 / (6 * m * Fintype.card (Point F m)) := by
  rw [lidtGame_μ_eq, filter_questions_axis, Finset.sum_singleton]
  rfl

/-! ## The diagonal shape

Here several samples contribute, so the weight is a sum. It does **not** have to be evaluated:
in the push-forward bound the canonical-line weight appears only on the larger side, so an upper
bound suffices, and bounding the sum by `count × largest term` costs only a factor `m` in the
constant --- which `δ_CL` absorbs, being allowed a prefactor polynomial in `m` and `d`. What it
may *not* absorb is a factor growing with `q`, so the `q`-exponent has to be right, and that is
what `le_rev_diagIdx_of_questions` pins down. -/

omit [Fintype F] [NeZero m] in
/-- A sample producing a given diagonal line against a given point is a `diag` sample at that
point whose direction is a **nonzero multiple** of the line's. -/
theorem of_questions_diag {ℓ : Line F m} {u : Point F m} {s : Sample F m}
    (hℓ : ∃ k, ℓ.2 k ≠ 0)
    (hs : s.questions = ((Question.diagLine ℓ : Question F m), Question.point u)) :
    ∃ (j : Fin m) (v : Fin ((j : ℕ) + 1) → F), s = Sample.diag false u j v ∧
      ∃ c : F, c ≠ 0 ∧ (Sample.extend v : Point F m) = c • ℓ.2 := by
  classical
  match s, hs with
  | Sample.diag false u' j v, hs =>
      have hs' : ((Question.diagLine (Line.through u' (Sample.extend v)) : Question F m),
          Question.point u') = (Question.diagLine ℓ, Question.point u) := hs
      injection hs' with h1 h2
      injection h2 with hu
      subst hu
      injection h1 with hthr
      -- the direction cannot vanish, or the line's would too
      have hz : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
        by_contra hcon
        have h0 : (Sample.extend v : Point F m) = 0 :=
          funext fun k => not_not.mp fun hk => hcon ⟨k, hk⟩
        obtain ⟨k, hk⟩ := hℓ
        rw [h0, Line.through, dif_neg (by simp)] at hthr
        exact hk (by rw [← hthr]; simp)
      set p := Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hz with hp
      have hzp : (Sample.extend v : Point F m) p ≠ 0 := Fin.find_spec hz
      refine ⟨j, v, rfl, (Sample.extend v : Point F m) p, hzp, ?_⟩
      have hd : ℓ.2 = ((Sample.extend v : Point F m) p)⁻¹ • Sample.extend v := by
        rw [← hthr, through_eq hz]
      rw [hd, smul_smul, mul_inv_cancel₀ hzp, one_smul]
  | Sample.diag true u' j v, hs => exact absurd hs (by simp [Sample.questions])
  | Sample.axis false u' i, hs => exact absurd hs (by simp [Sample.questions])
  | Sample.axis true u' i, hs => exact absurd hs (by simp [Sample.questions])
  | Sample.selfConsistency u', hs => exact absurd hs (by simp [Sample.questions])

omit [Fintype F] in
/-- **The direction pins the `q`-exponent.** A sample producing the line has `j` at least the
reversal of `diagIdx ℓ`: its direction vanishes above `j`, hence so does the line's, hence the
*reversed* direction vanishes below `rev j`, so its first nonzero coordinate is at least
`rev j`. -/
theorem le_rev_diagIdx_of_questions {ℓ : Line F m} {u : Point F m} {j : Fin m}
    {v : Fin ((j : ℕ) + 1) → F} (hℓ : ∃ k, ℓ.2 k ≠ 0)
    (hs : (Sample.diag false u j v).questions
      = ((Question.diagLine ℓ : Question F m), Question.point u)) :
    ((Fin.rev (diagIdx ℓ) : ℕ)) ≤ (j : ℕ) := by
  classical
  obtain ⟨j', v', hjv, c, hc, hcv⟩ := of_questions_diag hℓ hs
  injection hjv with _ _ hj hv
  subst hj
  -- the line's direction vanishes above `j`
  have hvan : ∀ k : Fin m, (j : ℕ) < (k : ℕ) → ℓ.2 k = 0 := by
    intro k hk
    have hext : (Sample.extend v' : Point F m) k = 0 := by
      rw [Sample.extend, dif_neg (by omega)]
    have hprod : c * ℓ.2 k = 0 := by
      have h := congrFun hcv k
      rw [hext] at h
      simpa using h.symm
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hc
    · exact h
  -- so the reversed direction vanishes below `rev j`, and `diagIdx` is its first nonzero index
  have hex : ∃ k, (revPoint ℓ.2) k ≠ 0 := by
    obtain ⟨k, hk⟩ := hℓ
    exact ⟨Fin.rev k, by rwa [revPoint_apply, Fin.rev_rev]⟩
  have hmin : ∀ k : Fin m, (k : ℕ) < (Fin.rev j : ℕ) → (revPoint ℓ.2) k = 0 := by
    intro k hk
    rw [revPoint_apply]
    refine hvan _ ?_
    have h1 : (Fin.rev j : ℕ) = m - ((j : ℕ) + 1) := Fin.val_rev j
    have h2 : (Fin.rev k : ℕ) = m - ((k : ℕ) + 1) := Fin.val_rev k
    have := k.isLt
    have := j.isLt
    omega
  have hdi : diagIdx ℓ = Fin.find (fun k => (revPoint ℓ.2) k ≠ 0) hex := by
    rw [diagIdx, dif_pos hex]
  rw [hdi]
  set P := Fin.find (fun k => (revPoint ℓ.2) k ≠ 0) hex with hPdef
  by_contra hcon
  have hcon' : (j : ℕ) < ((Fin.rev P : Fin m) : ℕ) := Nat.lt_of_not_le hcon
  have h1 : ((Fin.rev P : Fin m) : ℕ) = m - ((P : ℕ) + 1) := Fin.val_rev P
  have h2 : ((Fin.rev j : Fin m) : ℕ) = m - ((j : ℕ) + 1) := Fin.val_rev j
  have h3 : (P : ℕ) < m := P.isLt
  have h4 : (j : ℕ) < m := j.isLt
  exact (Fin.find_spec hex) (hmin P (by omega))

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- `Sample.extend` is the extension by zero, so it recovers `v` on `v`'s own indices. -/
theorem extend_apply_coe {j : Fin m} (v : Fin ((j : ℕ) + 1) → F) (i : Fin ((j : ℕ) + 1)) :
    (Sample.extend v : Point F m)
        ⟨(i : ℕ), lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.isLt⟩ = v i := by
  rw [Sample.extend, dif_pos (Nat.le_of_lt_succ i.isLt)]

/-- The key `(j, c)` of a diagonal sample, read at a coordinate `p`. Two samples producing the
same line with the same key are equal, which is what bounds the count. -/
noncomputable def diagKey (p : Fin m) : Sample F m → Fin m × F
  | .diag _ _ j v => (j, (Sample.extend v : Point F m) p)
  | _ => (idx0, 0)

/-- **At most `m q` samples produce a given diagonal line against a given point.** A sample is
pinned by its `j` together with the scalar relating its direction to the line's, and there are
`m` values of the first and `q` of the second. -/
theorem card_filter_diag_le {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) (u : Point F m) :
    (Finset.univ.filter (fun s : Sample F m =>
        s.questions = ((Question.diagLine ℓ : Question F m), Question.point u))).card
      ≤ m * Fintype.card F := by
  classical
  set p := Fin.find (fun k => ℓ.2 k ≠ 0) hℓ with hp
  have hlp : ℓ.2 p ≠ 0 := Fin.find_spec hℓ
  have hcard : (Finset.univ : Finset (Fin m × F)).card = m * Fintype.card F := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (diagKey p) (fun _ _ => Finset.mem_univ _) ?_
  intro s₁ h₁ s₂ h₂ hkey
  obtain ⟨j₁, v₁, hs₁, c₁, hc₁, hcv₁⟩ :=
    of_questions_diag hℓ (Finset.mem_filter.mp h₁).2
  obtain ⟨j₂, v₂, hs₂, c₂, hc₂, hcv₂⟩ :=
    of_questions_diag hℓ (Finset.mem_filter.mp h₂).2
  subst hs₁
  subst hs₂
  obtain ⟨hj, hval⟩ := (Prod.mk.injEq _ _ _ _).mp hkey
  -- the scalars agree
  have hc : c₁ = c₂ := by
    have e₁ : (Sample.extend v₁ : Point F m) p = c₁ * ℓ.2 p := by
      rw [hcv₁]; simp
    have e₂ : (Sample.extend v₂ : Point F m) p = c₂ * ℓ.2 p := by
      rw [hcv₂]; simp
    rw [e₁, e₂] at hval
    exact mul_right_cancel₀ hlp hval
  subst hj
  subst hc
  -- hence the directions, hence `v`
  have hext : (Sample.extend v₁ : Point F m) = Sample.extend v₂ := by rw [hcv₁, hcv₂]
  have hv : v₁ = v₂ := by
    funext i
    rw [← extend_apply_coe v₁ i, ← extend_apply_coe v₂ i, hext]
  rw [hv]

/-- **Every sample producing a given diagonal line against a point has weight at most
`1/(6 m q^m q^{rev (diagIdx ℓ) + 1})`.** This is where the `q`-exponent of the bound is fixed:
`le_rev_diagIdx_of_questions` says a contributing sample's `j` is at least `rev (diagIdx ℓ)`. -/
theorem weight_le_of_questions_diag {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) {u : Point F m}
    {s : Sample F m} (hsq : s.questions = ((Question.diagLine ℓ : Question F m),
      Question.point u)) :
    s.weight ≤ 1 / (6 * m * Fintype.card (Point F m) *
      (Fintype.card F : ℝ) ^ ((Fin.rev (diagIdx ℓ) : ℕ) + 1)) := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hP : (0 : ℝ) < Fintype.card (Point F m) := by exact_mod_cast Fintype.card_pos
  have hA : (0 : ℝ) < 6 * m * Fintype.card (Point F m) := by positivity
  have hden : (0 : ℝ) < 6 * m * Fintype.card (Point F m) *
      (Fintype.card F : ℝ) ^ ((Fin.rev (diagIdx ℓ) : ℕ) + 1) := mul_pos hA (pow_pos hq _)
  obtain ⟨j, v, hsj, _, _, _⟩ := of_questions_diag hℓ hsq
  subst hsj
  have hjge : ((Fin.rev (diagIdx ℓ) : ℕ)) ≤ (j : ℕ) := le_rev_diagIdx_of_questions hℓ hsq
  show 1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ) ^ ((j : ℕ) + 1)) ≤ _
  refine one_div_le_one_div_of_le hden ?_
  refine mul_le_mul_of_nonneg_left ?_ hA.le
  exact pow_le_pow_right₀ hq1 (by omega)

/-- **The diagonal weight, bounded.** The sum over the contributing samples is at most their
number times the largest of them, and `le_rev_diagIdx_of_questions` says every one of them has
`j` at least `rev (diagIdx ℓ)`, which fixes the `q`-exponent. -/
theorem lidtGame_μ_diag_le {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) (u : Point F m) :
    (lidtGame F m d).μ (.diagLine ℓ) (.point u)
      ≤ (m * Fintype.card F : ℝ) *
          (1 / (6 * m * Fintype.card (Point F m) *
            (Fintype.card F : ℝ) ^ ((Fin.rev (diagIdx ℓ) : ℕ) + 1))) := by
  classical
  rw [lidtGame_μ_eq]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    have h : 1 ≤ Fintype.card F := Fintype.card_pos
    exact_mod_cast h
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hP : (0 : ℝ) < Fintype.card (Point F m) := by exact_mod_cast Fintype.card_pos
  have hA : (0 : ℝ) < 6 * m * Fintype.card (Point F m) := by
    have h6 : (0 : ℝ) < 6 * m := by linarith
    exact mul_pos h6 hP
  set S : Finset (Sample F m) := Finset.univ.filter (fun s : Sample F m =>
    s.questions = ((Question.diagLine ℓ : Question F m), Question.point u)) with hS
  set B : ℝ := 1 / (6 * m * Fintype.card (Point F m) *
    (Fintype.card F : ℝ) ^ ((Fin.rev (diagIdx ℓ) : ℕ) + 1)) with hB
  have hden : (0 : ℝ) < 6 * m * Fintype.card (Point F m) *
      (Fintype.card F : ℝ) ^ ((Fin.rev (diagIdx ℓ) : ℕ) + 1) := mul_pos hA (pow_pos hq _)
  have hBpos : 0 < B := by rw [hB]; exact div_pos one_pos hden
  have hterm : ∀ s ∈ S, s.weight ≤ B := by
    intro s hs
    rw [hS, Finset.mem_filter] at hs
    exact weight_le_of_questions_diag hℓ hs.2
  calc ∑ s ∈ S, s.weight
      ≤ S.card • B := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (S.card : ℝ) * B := by rw [nsmul_eq_mul]
    _ ≤ (m * Fintype.card F : ℝ) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hBpos.le
        have h := card_filter_diag_le hℓ u
        rw [← hS] at h
        exact_mod_cast h

/-! ## The seeded test, shape by shape

Only **lower** bounds are needed here, since the seeded weight sits on the smaller side of the
push-forward bound, and a lower bound on a count is an injection *into* the set of contributing
samples. That is much cheaper than an exact count, and it is why this section is short. -/

/-- The samples of the seeded test that ask the same point twice include one for every seed and
every raw direction, so there are at least `q · q^m` of them. -/
theorem card_filter_clPoint_ge (hm : m ∣ Fintype.card F) (xp : Point F m) :
    Fintype.card F * Fintype.card (Point F m)
      ≤ (Finset.univ.filter (fun sm : CL.Sample F m =>
          (sm.question hm sm.tyA, sm.question hm sm.tyB)
            = ((CL.Question.point xp : CL.Question F m), CL.Question.point xp))).card := by
  classical
  have hcard : Fintype.card F * Fintype.card (Point F m)
      = (Finset.univ : Finset (F × Point F m)).card := by simp [Fintype.card_prod]
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun sv => ({tyA := .point, tyB := .point, u := xp, s := sv.1, v := sv.2} : CL.Sample F m))
    (fun sv _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) ?_
  intro a _ b _ hab
  have h1 := congrArg CL.Sample.s hab
  have h2 := congrArg CL.Sample.v hab
  exact Prod.ext h1 h2

/-- Likewise for an axis-parallel line against a point: one sample for every raw direction. -/
theorem card_filter_clAxis_ge (hm : m ∣ Fintype.card F) (xp : Point F m) (s₀ : F) :
    Fintype.card (Point F m)
      ≤ (Finset.univ.filter (fun sm : CL.Sample F m =>
          (sm.question hm sm.tyA, sm.question hm sm.tyB)
            = ((CL.Question.aline (rep (Pi.single (chi hm s₀) 1) xp) s₀ : CL.Question F m),
                CL.Question.point xp))).card := by
  classical
  have hcard : Fintype.card (Point F m) = (Finset.univ : Finset (Point F m)).card := by simp
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun v => ({tyA := .aline, tyB := .point, u := xp, s := s₀, v := v} : CL.Sample F m))
    (fun v _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) ?_
  intro a _ b _ hab
  exact congrArg CL.Sample.v hab

/-- And for a diagonal line against a point, provided the direction really does vanish below the
seed's block --- which it must, for the question to be in the seeded test's support. There is one
sample for every completion of the direction *below* that block, hence at least `q^{χ s}`. -/
theorem card_filter_clDiag_ge (hm : m ∣ Fintype.card F) (xp : Point F m) (s₀ : F)
    (w : Point F m) (hw : ∀ k : Fin m, (k : ℕ) < ((chi hm s₀ : ℕ)) → w k = 0) :
    Fintype.card F ^ ((chi hm s₀ : ℕ))
      ≤ (Finset.univ.filter (fun sm : CL.Sample F m =>
          (sm.question hm sm.tyA, sm.question hm sm.tyB)
            = ((CL.Question.dline (rep w xp) s₀ w : CL.Question F m),
                CL.Question.point xp))).card := by
  classical
  have hcard : Fintype.card F ^ ((chi hm s₀ : ℕ))
      = (Finset.univ : Finset (Fin ((chi hm s₀ : ℕ)) → F)).card := by simp
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun g : Fin ((chi hm s₀ : ℕ)) → F =>
      ({ tyA := .dline, tyB := .point, u := xp, s := s₀,
         v := (fun k : Fin m =>
           if h : (k : ℕ) < ((chi hm s₀ : ℕ)) then g ⟨(k : ℕ), h⟩ else w k) }
        : CL.Sample F m)) ?_ ?_
  · intro g _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hz : CL.zeroBelow (chi hm s₀)
        (fun k : Fin m =>
          if h : (k : ℕ) < ((chi hm s₀ : ℕ)) then g ⟨(k : ℕ), h⟩ else w k) = w := by
      funext k
      rw [CL.zeroBelow]
      by_cases h : (k : ℕ) < ((chi hm s₀ : ℕ))
      · rw [if_pos h]
        exact (hw k h).symm
      · rw [if_neg h, dif_neg h]
    show ((CL.Sample.question hm _ CL.Ty.dline), (CL.Sample.question hm _ CL.Ty.point)) = _
    simp only [CL.Sample.question, hz]
  · intro a _ b _ hab
    have hv := congrArg CL.Sample.v hab
    funext i
    have h := congrFun hv (⟨(i : ℕ), lt_trans i.isLt (chi hm s₀).isLt⟩ : Fin m)
    dsimp only at h
    have hi : (⟨(i : ℕ), i.isLt⟩ : Fin ((chi hm s₀ : ℕ))) = i := Fin.ext rfl
    rw [dif_pos i.isLt, dif_pos i.isLt, hi] at h
    exact h

/-! ## From fibres of the question map to samples

The push-forward bound is stated over *fibres* of the question map, but the canonical-line test's
weight lives on *samples*, and only five shapes of question pair carry any weight at all. This
lemma moves the whole thing onto samples, where the case analysis is a case analysis on a
constructor. -/

theorem sum_fibre_μ_eq_sum_samples (f g : Question F m → CL.Question F m)
    (x y : CL.Question F m) :
    (∑ x' ∈ Finset.univ.filter (fun x' => f x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => g y' = y), (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          f s.questions.1 = x ∧ g s.questions.2 = y), s.weight := by
  classical
  -- write every indicator out, so both sides are sums of products
  have hμ : ∀ x' y' : Question F m, (lidtGame F m d).μ x' y'
      = ∑ s : Sample F m, (if s.questions = (x', y') then s.weight else 0) := by
    intro x' y'
    rw [lidtGame_μ_eq, Finset.sum_filter]
  have hLHS : (∑ x' ∈ Finset.univ.filter (fun x' => f x' = x),
      ∑ y' ∈ Finset.univ.filter (fun y' => g y' = y), (lidtGame F m d).μ x' y')
      = ∑ x' : Question F m, ∑ y' : Question F m, ∑ s : Sample F m,
          (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
            (if s.questions = (x', y') then s.weight else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases hx : f x' = x
    · rw [if_pos hx, Finset.sum_filter]
      refine Finset.sum_congr rfl fun y' _ => ?_
      by_cases hy : g y' = y
      · rw [if_pos hy, hμ]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos hx, if_pos hy, one_mul, one_mul]
      · rw [if_neg hy, if_pos hx, if_neg hy]
        simp
    · rw [if_neg hx]
      refine (Finset.sum_eq_zero fun y' _ => ?_).symm
      rw [if_neg hx]
      simp
  have hswap : ∀ x' : Question F m,
      (∑ y' : Question F m, ∑ s : Sample F m,
        (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
          (if s.questions = (x', y') then s.weight else 0))
      = ∑ s : Sample F m, ∑ y' : Question F m,
        (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
          (if s.questions = (x', y') then s.weight else 0) := fun _ => Finset.sum_comm
  rw [hLHS, Finset.sum_congr rfl (fun x' (_ : x' ∈ Finset.univ) => hswap x'), Finset.sum_comm]
  -- for each sample only one `(x', y')` survives
  have hinner : ∀ s : Sample F m,
      (∑ x' : Question F m, ∑ y' : Question F m,
        (if f x' = x then (1 : ℝ) else 0) * (if g y' = y then (1 : ℝ) else 0) *
          (if s.questions = (x', y') then s.weight else 0))
      = (if f s.questions.1 = x ∧ g s.questions.2 = y then s.weight else 0) := by
    intro s
    rw [Finset.sum_eq_single s.questions.1 (fun x' _ hx' => ?_) (fun h => absurd
      (Finset.mem_univ _) h)]
    · rw [Finset.sum_eq_single s.questions.2 (fun y' _ hy' => ?_) (fun h => absurd
        (Finset.mem_univ _) h)]
      · by_cases hx : f s.questions.1 = x
        · by_cases hy : g s.questions.2 = y
          · simp [hx, hy]
          · simp [hx, hy]
        · simp [hx]
      · rw [if_neg (fun hc => hy' (congrArg Prod.snd hc).symm), mul_zero]
    · refine Finset.sum_eq_zero fun y' _ => ?_
      rw [if_neg (fun hc => hx' (congrArg Prod.fst hc).symm), mul_zero]
  rw [Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => hinner s, Finset.sum_filter]

/-! ## Counting the seed choices

With the push-forward on samples, the average over the family becomes a weight times a *count of
family members*, and that is what the shapes differ in: a point question's image does not depend
on the family member at all, while a line question's pins the seed at one index (and, for a
diagonal, the scale). -/

/-- Averaging over a family, as a weight times a count of family members. -/
theorem sum_sum_filter_eq_sum_card {Seed ι : Type*} [Fintype Seed] [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (cond : Seed → ι → Prop) [∀ σ i, Decidable (cond σ i)] :
    (∑ σ : Seed, ∑ i ∈ Finset.univ.filter (fun i => cond σ i), w i)
      = ∑ i : ι, w i * (Finset.univ.filter (fun σ : Seed => cond σ i)).card := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The averaging family: a fibre position for each direction index, and one global nonzero
direction scale. The scale is there because of the second correction in
`planning/lidt-cl-adapter.md`. -/
abbrev Seed (F : Type*) [Field F] [Fintype F] (m : ℕ) : Type _ :=
  (Fin m → Fin (Fintype.card F / m)) × {c : F // c ≠ 0}

/-- The seeded question a canonical-line question is played through, for a family member. -/
noncomputable def qmapS (hm : m ∣ Fintype.card F) (σc : Seed F m) :
    Question F m → CL.Question F m :=
  qmap hm σc.1 σc.2.1

@[simp] theorem qmapS_point (hm : m ∣ Fintype.card F) (σc : Seed F m) (u : Point F m) :
    qmapS hm σc (.point u) = .point (revPoint u) := rfl

/-! ### The point shape

Only the self-consistency sample can contribute, and its image does not depend on the family
member, so averaging neither helps nor hurts here: the requirement is the unaveraged
`1/(3 q^m) ≤ C · 1/(9 q^m)`, i.e. `C ≥ 3`. -/

/-- The samples whose images are a pair of point questions: at most the self-consistency sample at
the reversed point. -/
theorem filter_qmapS_point_subset (hm : m ∣ Fintype.card F) (σc : Seed F m)
    (xp yp : Point F m) :
    Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = CL.Question.point xp ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)
      ⊆ {Sample.selfConsistency (revPoint xp)} := by
  classical
  intro s hs
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
  refine Finset.mem_singleton.mpr ?_
  match s, h1, h2 with
  | Sample.selfConsistency u, h1, _ =>
      have h : CL.Question.point (revPoint u) = CL.Question.point xp := h1
      injection h with h'
      rw [← h', revPoint_revPoint]
  | Sample.axis false u i, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.axis true u i, _, h2 => exact absurd h2 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag false u j v, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag true u j v, _, h2 => exact absurd h2 (by simp [Sample.questions, qmapS, qmap])

/-- And if the two points differ, nothing contributes: the one candidate fails the second
condition. -/
theorem filter_qmapS_point_eq_empty (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {xp yp : Point F m} (hxy : xp ≠ yp) :
    Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = CL.Question.point xp ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)
      = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
  have hmem := filter_qmapS_point_subset hm σc xp yp hs
  rw [Finset.mem_singleton] at hmem
  subst hmem
  obtain ⟨_, h2⟩ := (Finset.mem_filter.mp hs).2
  have h : CL.Question.point (revPoint (revPoint xp)) = CL.Question.point yp := h2
  rw [revPoint_revPoint] at h
  injection h with h'
  exact hxy h'


/-! ### Cardinalities

Three counts enter the arithmetic: the point space, the seeded test's sample space and the
averaging family. Only the first has to be known as a power of `q`; the other two enter as
symbols that cancel. -/

omit [Field F] [DecidableEq F] [NeZero m] in
theorem card_point_eq : Fintype.card (Point F m) = Fintype.card F ^ m := by
  simp

omit [DecidableEq F] [NeZero m] in
theorem card_clTy : Fintype.card CL.Ty = 3 := rfl

omit [Field F] [DecidableEq F] [NeZero m] in
/-- **The seeded test's sample space**: nine ordered type pairs against `(u, s, v)`. -/
theorem card_clSample_eq :
    Fintype.card (CL.Sample F m)
      = 9 * (Fintype.card (Point F m) * (Fintype.card F * Fintype.card (Point F m))) := by
  have e : CL.Sample F m ≃ (CL.Ty × CL.Ty) × (Point F m × F × Point F m) :=
    { toFun := fun sm => ((sm.tyA, sm.tyB), (sm.u, sm.s, sm.v))
      invFun := fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, card_clTy]

omit [NeZero m] in
/-- **The averaging family**: a fibre position per direction index, and one nonzero scale. -/
theorem card_seed_eq :
    Fintype.card (Seed F m)
      = (Fintype.card F / m) ^ m * (Fintype.card F - 1) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  congr 1
  have h : Fintype.card {c : F // c ≠ 0} = Fintype.card F - Fintype.card {c : F // c = 0} :=
    Fintype.card_subtype_compl _
  rw [h, Fintype.card_subtype_eq]

omit [DecidableEq F] in
/-- The family is nonempty, which the derandomization needs. -/
theorem nonempty_seed (hm : m ∣ Fintype.card F) : Nonempty (Seed F m) :=
  ⟨⟨fun _ => ⟨0, card_div_pos hm⟩, ⟨1, one_ne_zero⟩⟩⟩

/-! ### The shape of every one of the bounds

All four nonzero shapes are bounded the same way: the contributing samples lie in one finite set
`T` that does not depend on the family member, each of them has weight at most `B`, and each is
picked out by at most `M` family members. -/

/-- **Count times weight times count.** -/
theorem sum_sum_le_card_mul {S ι : Type*} [Fintype S] [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (cond : S → ι → Prop) [∀ σ i, Decidable (cond σ i)]
    (T : Finset ι) (B : ℝ) (M : ℕ)
    (hsub : ∀ σ i, cond σ i → i ∈ T) (hB : ∀ i ∈ T, w i ≤ B)
    (hM : ∀ i ∈ T, (Finset.univ.filter (fun σ : S => cond σ i)).card ≤ M) :
    (∑ σ : S, ∑ i ∈ Finset.univ.filter (fun i => cond σ i), w i)
      ≤ (T.card : ℝ) * (B * M) := by
  classical
  rw [sum_sum_filter_eq_sum_card]
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => ?_)]
  · refine (Finset.sum_le_card_nsmul T _ (B * M) ?_).trans ?_
    · intro i hi
      refine mul_le_mul (hB i hi) ?_ (Nat.cast_nonneg _) (le_trans (hw i) (hB i hi))
      exact_mod_cast hM i hi
    · rw [nsmul_eq_mul]
  · have he : (Finset.univ.filter (fun σ : S => cond σ i)) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun σ hσ =>
        hi (hsub σ i (Finset.mem_filter.mp hσ).2)
    rw [he]
    simp

/-! ### The mirrored shapes come for free

Both tests are symmetric under exchanging the two players --- `lidtGame`'s swap bit and
`clGame`'s ordered type pair --- so a bound for `(x, y)` is a bound for `(y, x)`, and only the
shapes with the *line* on the left have to be done by hand. -/

/-- Flipping a sample's swap bit. -/
def swapSample : Sample F m → Sample F m
  | .axis b u i => .axis (!b) u i
  | .selfConsistency u => .selfConsistency u
  | .diag b u j v => .diag (!b) u j v

omit [Fintype F] [NeZero m] in
@[simp] theorem swapSample_questions (s : Sample F m) :
    (swapSample s).questions = s.questions.swap := by
  cases s with
  | axis b u i => cases b <;> rfl
  | selfConsistency u => rfl
  | diag b u j v => cases b <;> rfl

omit [Field F] [DecidableEq F] [NeZero m] in
@[simp] theorem swapSample_weight (s : Sample F m) : (swapSample s).weight = s.weight := by
  cases s <;> rfl

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem swapSample_swapSample (s : Sample F m) : swapSample (swapSample s) = s := by
  cases s with
  | axis b u i => cases b <;> rfl
  | selfConsistency u => rfl
  | diag b u j v => cases b <;> rfl

/-- The swap as an equivalence of samples. -/
def swapEquiv : Sample F m ≃ Sample F m :=
  ⟨swapSample, swapSample, swapSample_swapSample, swapSample_swapSample⟩

omit [NeZero m] in
/-- **The canonical-line side is symmetric.** -/
theorem sum_filter_swap (f : Question F m → CL.Question F m) (x y : CL.Question F m) :
    (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
        f s.questions.1 = x ∧ f s.questions.2 = y), s.weight)
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
        f s.questions.1 = y ∧ f s.questions.2 = x), s.weight := by
  classical
  refine Finset.sum_equiv swapEquiv (fun s => ?_) (fun s _ => (swapSample_weight s).symm)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, swapEquiv, Equiv.coe_fn_mk,
    swapSample_questions, Prod.fst_swap, Prod.snd_swap]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Exchanging the two players' types in a seeded sample. -/
def clSwap (sm : CL.Sample F m) : CL.Sample F m := {sm with tyA := sm.tyB, tyB := sm.tyA}

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem clSwap_clSwap (sm : CL.Sample F m) : clSwap (clSwap sm) = sm := rfl

/-- The type exchange as an equivalence of seeded samples. -/
def clSwapEquiv : CL.Sample F m ≃ CL.Sample F m := ⟨clSwap, clSwap, clSwap_clSwap, clSwap_clSwap⟩

/-- **The seeded side is symmetric too**, the nine ordered type pairs being equally likely. -/
theorem clGame_μ_symm (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y = (clGame (d := d) (ldc := ldc) hm).μ y x := by
  classical
  rw [clGame_μ_eq, clGame_μ_eq]
  congr 1
  refine congrArg _ (Finset.card_equiv clSwapEquiv fun sm => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, clSwapEquiv, Equiv.coe_fn_mk, clSwap,
    Prod.mk.injEq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ### The seed counts

A line question's image pins the family's fibre position at exactly one index --- and, for a
diagonal, the scale as well. That is the whole content of the averaging: the family has
`(q/m)^m (q-1)` members and only `(q/m)^{m-1} (q-1)` or `(q/m)^{m-1}` of them can contribute. -/

omit [Field F] [DecidableEq F] [NeZero m] in
theorem card_ne_singleton (i : Fin m) : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
  simp

omit [NeZero m] in
theorem card_ne_zero_eq : Fintype.card {c : F // c ≠ 0} = Fintype.card F - 1 := by
  simp

omit [NeZero m] in
/-- **A pinned seed index costs a factor `q/m`.** -/
theorem card_filter_seed_le (hm : m ∣ Fintype.card F) (i : Fin m) (s₀ : F)
    (P : Seed F m → Prop) [DecidablePred P]
    (hP : ∀ σc, P σc → seedOf hm i (σc.1 i) = s₀) :
    (Finset.univ.filter P).card
      ≤ (Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) := by
  classical
  have hcard : (Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1)
      = (Finset.univ : Finset (({j : Fin m // j ≠ i} → Fin (Fintype.card F / m))
          × {c : F // c ≠ 0})).card := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      card_ne_singleton, card_ne_zero_eq]
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun σc => (fun j => σc.1 j.1, σc.2)) (fun _ _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  refine Prod.ext (funext fun j => ?_) h2
  by_cases hj : j = i
  · subst hj
    exact seedOf_injective hm j ((hP a (Finset.mem_filter.mp ha).2).trans
      (hP b (Finset.mem_filter.mp hb).2).symm)
  · exact congrFun h1 ⟨j, hj⟩

omit [NeZero m] in
/-- **A pinned seed index and a pinned scale cost a factor `(q/m)(q-1)`.** -/
theorem card_filter_seed_scale_le (hm : m ∣ Fintype.card F) (i : Fin m) (s₀ c₀ : F)
    (P : Seed F m → Prop) [DecidablePred P]
    (hP : ∀ σc, P σc → seedOf hm i (σc.1 i) = s₀ ∧ (σc.2 : F) = c₀) :
    (Finset.univ.filter P).card ≤ (Fintype.card F / m) ^ (m - 1) := by
  classical
  have hcard : (Fintype.card F / m) ^ (m - 1)
      = (Finset.univ : Finset ({j : Fin m // j ≠ i} → Fin (Fintype.card F / m))).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_ne_singleton]
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun σc => fun j => σc.1 j.1) (fun _ _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  obtain ⟨hsa, hca⟩ := hP a (Finset.mem_filter.mp ha).2
  obtain ⟨hsb, hcb⟩ := hP b (Finset.mem_filter.mp hb).2
  refine Prod.ext (funext fun j => ?_) (Subtype.ext (hca.trans hcb.symm))
  by_cases hj : j = i
  · subst hj
    exact seedOf_injective hm j (hsa.trans hsb.symm)
  · exact congrFun hab ⟨j, hj⟩

@[simp] theorem qmapS_axis (hm : m ∣ Fintype.card F) (σc : Seed F m) (ℓ : Line F m) :
    qmapS hm σc (.axisLine ℓ)
      = .aline (revPoint ℓ.1)
          (seedOf hm (Fin.rev (axisIdx ℓ)) (σc.1 (Fin.rev (axisIdx ℓ)))) := rfl

@[simp] theorem qmapS_diag (hm : m ∣ Fintype.card F) (σc : Seed F m) (ℓ : Line F m) :
    qmapS hm σc (.diagLine ℓ)
      = .dline (revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2)
          (seedOf hm (diagIdx ℓ) (σc.1 (diagIdx ℓ))) ((σc.2 : F) • revPoint ℓ.2) := rfl

/-! ### The axis-parallel shape

The seed determines the direction index, so the contributing sample is unique and the constraint
on the family is at one index. -/

/-- **At most one sample maps to an axis-parallel question against a point.** -/
theorem filter_qmapS_axis_subset (hm : m ∣ Fintype.card F) (σc : Seed F m)
    (u₀ : Point F m) (s₀ : F) (yp : Point F m) :
    Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀ ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)
      ⊆ {Sample.axis false (revPoint yp) (Fin.rev (chi hm s₀))} := by
  classical
  intro s hs
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
  refine Finset.mem_singleton.mpr ?_
  match s, h1, h2 with
  | Sample.axis false u i, h1, h2 =>
      have hu : revPoint u = yp := by
        have h : CL.Question.point (revPoint u) = CL.Question.point yp := h2
        injection h
      have hidx : axisIdx (Line.through u (Pi.single i 1) : Line F m) = i := by
        rw [through_single]; exact axisIdx_eq _ i
      have h1' : (CL.Question.aline (revPoint (Line.through u (Pi.single i 1) : Line F m).1)
          (seedOf hm (Fin.rev (axisIdx (Line.through u (Pi.single i 1) : Line F m)))
            (σc.1 (Fin.rev (axisIdx (Line.through u (Pi.single i 1) : Line F m)))))
          : CL.Question F m) = CL.Question.aline u₀ s₀ := h1
      rw [hidx] at h1'
      injection h1' with _ hs'
      have hchi : Fin.rev i = chi hm s₀ := by rw [← hs', chi_seedOf]
      have hi : i = Fin.rev (chi hm s₀) := by rw [← hchi, Fin.rev_rev]
      rw [hi, ← hu, revPoint_revPoint]
  | Sample.axis true u i, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.selfConsistency u, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag false u j v, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag true u j v, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])

omit [Fintype F] [NeZero m] in
/-- The adapter's axis-parallel base point, unreversed: exactly the seeded test's own. -/
theorem revPoint_through_single_eq_rep (i : Fin m) (u : Point F m) :
    revPoint (Line.through (revPoint u) (Pi.single (Fin.rev i) 1) : Line F m).1
      = CL.rep (Pi.single i 1) u := by
  have hthr : (Line.through (revPoint u) (Pi.single (Fin.rev i) 1) : Line F m).1
      = revPoint u - (revPoint u) (Fin.rev i) • (Pi.single (Fin.rev i) 1 : Point F m) := by
    rw [through_single]
  show revPoint (Line.through (revPoint u) (Pi.single (Fin.rev i) 1) : Line F m).1
      = MIPRE.CL.canonLin (Submodule.span F {(Pi.single i 1 : Point F m)}) u
  rw [hthr, ← rep_single]
  exact revPoint_rep_single i u

/-- **The base point the contributing sample forces.** If anything contributes to an
axis-parallel question against a point, the question is the one the *seeded* test itself would
have asked at that point and seed: `revPoint_rep_single` unreverses the adapter's base point. -/
theorem base_of_qmapS_axis (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    u₀ = CL.rep (Pi.single (chi hm s₀) 1) yp := by
  classical
  have hmem := filter_qmapS_axis_subset hm σc u₀ s₀ yp
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
  rw [Finset.mem_singleton] at hmem
  subst hmem
  have h1' : (CL.Question.aline
      (revPoint (Line.through (revPoint yp)
        (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m).1)
      (seedOf hm (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m)))
        (σc.1 (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m))))) : CL.Question F m)
      = CL.Question.aline u₀ s₀ := h1
  rw [← (CL.Question.aline.inj h1').1]
  exact revPoint_through_single_eq_rep (chi hm s₀) yp

/-- **The family members that can contribute to an axis-parallel question**: the seed index is
pinned, so there are at most `(q/m)^{m-1} (q-1)` of them. -/
theorem card_filter_axis_le (hm : m ∣ Fintype.card F)
    (u₀ : Point F m) (s₀ : F) (yp : Point F m) (s : Sample F m)
    (hs : s ∈ ({Sample.axis false (revPoint yp) (Fin.rev (chi hm s₀))} : Finset (Sample F m))) :
    (Finset.univ.filter (fun σc : Seed F m =>
        qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀ ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)).card
      ≤ (Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) := by
  classical
  rw [Finset.mem_singleton] at hs
  subst hs
  refine card_filter_seed_le hm (chi hm s₀) s₀ _ ?_
  intro σc hσc
  have h1' : (CL.Question.aline
      (revPoint (Line.through (revPoint yp)
        (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m).1)
      (seedOf hm (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m)))
        (σc.1 (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m))))) : CL.Question F m)
      = CL.Question.aline u₀ s₀ := hσc.1
  have hidx : axisIdx (Line.through (revPoint yp)
      (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m) = Fin.rev (chi hm s₀) := by
    rw [through_single]; exact axisIdx_eq _ _
  rw [hidx, Fin.rev_rev] at h1'
  exact (CL.Question.aline.inj h1').2

/-! ### The arithmetic facts

Each shape ends in an inequality between two explicit rationals in `q`, `m` and `q/m`. These are
the casts and positivity facts they all need. -/

/-- The block size, as a real. -/
noncomputable abbrev blk (F : Type*) [Fintype F] (m : ℕ) : ℝ := ((Fintype.card F / m : ℕ) : ℝ)

omit [DecidableEq F] in
theorem blk_pos (hm : m ∣ Fintype.card F) : (0 : ℝ) < blk F m := by
  exact_mod_cast card_div_pos hm

omit [Field F] [DecidableEq F] [NeZero m] in
theorem m_mul_blk (hm : m ∣ Fintype.card F) :
    (m : ℝ) * blk F m = (Fintype.card F : ℝ) := by
  exact_mod_cast Nat.mul_div_cancel' hm

omit [DecidableEq F] [NeZero m] in
theorem cast_card_sub_one :
    ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
  rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]

omit [DecidableEq F] [NeZero m] in
theorem card_pos_real : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos

omit [DecidableEq F] [NeZero m] in
theorem card_point_pos_real : (0 : ℝ) < Fintype.card (Point F m) := by
  exact_mod_cast Fintype.card_pos

omit [Field F] [Fintype F] [DecidableEq F] in
theorem m_pos_real : (0 : ℝ) < m := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem one_le_m_real : (1 : ℝ) ≤ m := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)

omit [NeZero m] in
/-- The averaging family's size, as a real. -/
theorem card_seed_real :
    (Fintype.card (Seed F m) : ℝ) = blk F m ^ m * ((Fintype.card F : ℝ) - 1) := by
  rw [card_seed_eq]
  push_cast [cast_card_sub_one]
  ring

omit [Field F] [DecidableEq F] [NeZero m] in
/-- The seeded test's sample space, as a real. -/
theorem cast_card_clSample :
    (Fintype.card (CL.Sample F m) : ℝ)
      = 9 * ((Fintype.card (Point F m) : ℝ) *
          ((Fintype.card F : ℝ) * (Fintype.card (Point F m) : ℝ))) := by
  rw [card_clSample_eq]
  push_cast
  ring

/-! ### The axis-parallel bound -/

/-- **The axis-parallel shape of the push-forward bound.** The one contributing sample has weight
`1/(6 m q^m)`, the family pins one seed index, and the seeded test puts at least `1/(9 q^{m+1})`
on the pair; the three combine with room to spare at `C = 3m` (`3/2` would do). -/
theorem hμ_axis (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.aline u₀ s₀),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.aline u₀ s₀) (CL.Question.point yp)) := by
  classical
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.aline u₀ s₀),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀ ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
    sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  by_cases hbase : u₀ = CL.rep (Pi.single (chi hm s₀) 1) yp
  · subst hbase
    -- the three ingredients
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1
            = CL.Question.aline (CL.rep (Pi.single (chi hm s₀) 1) yp) s₀ ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)
      {Sample.axis false (revPoint yp) (Fin.rev (chi hm s₀))}
      (1 / (6 * m * Fintype.card (Point F m)))
      ((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1))
      (fun σc s hc => filter_qmapS_axis_subset hm σc _ s₀ yp
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
      (fun s hs => by rw [Finset.mem_singleton] at hs; subst hs; exact le_of_eq rfl)
      (fun s hs => card_filter_axis_le hm _ s₀ yp s hs)
    refine hle.trans ?_
    rw [Finset.card_singleton, Nat.cast_one, clGame_μ_eq, cast_card_clSample, card_seed_real]
    -- the seeded test's count, from below
    have hcnt : (Fintype.card (Point F m) : ℝ)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.aline (CL.rep (Pi.single (chi hm s₀) 1) yp) s₀
                    : CL.Question F m), CL.Question.point yp))).card : ℝ) := by
      exact_mod_cast card_filter_clAxis_ge hm yp s₀
    -- notation
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    have hq : (0 : ℝ) < q := card_pos_real
    have hq1 : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
    have hP : (0 : ℝ) < P := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hN : (0 : ℝ) < N := blk_pos hm
    have hmN : (m : ℝ) * N = q := m_mul_blk hm
    have hden : (0 : ℝ) < 9 * (P * (q * P)) := by positivity
    have hA : (0 : ℝ) ≤ N ^ (m - 1) * (q - 1) := by
      refine mul_nonneg (by positivity) (by linarith)
    have hM : ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ)
        = N ^ (m - 1) * (q - 1) := by
      rw [hNdef, hqdef]
      push_cast [cast_card_sub_one]
      ring
    have hpow : N ^ m = N ^ (m - 1) * N := by
      rw [← pow_succ]
      congr 1
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
      omega
    calc (1 : ℝ) * (1 / (6 * m * P) *
            ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ))
        = 1 / (6 * m * P) * (N ^ (m - 1) * (q - 1)) := by rw [hM, one_mul]
      _ ≤ (N * (3 * m * (P / (9 * (P * (q * P)))))) * (N ^ (m - 1) * (q - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hA
          have hval : N * (3 * m * (P / (9 * (P * (q * P))))) = 1 / (3 * P) := by
            rw [← hmN]
            field_simp
            ring
          rw [hval]
          refine one_div_le_one_div_of_le (by positivity) ?_
          nlinarith
      _ = N ^ m * (q - 1) * (3 * m * (P / (9 * (P * (q * P))))) := by rw [hpow]; ring
      _ ≤ N ^ m * (q - 1) * (3 * m *
            (((Finset.univ.filter (fun sm : CL.Sample F m =>
              (sm.question hm sm.tyA, sm.question hm sm.tyB)
                = ((CL.Question.aline (CL.rep (Pi.single (chi hm s₀) 1) yp) s₀
                      : CL.Question F m), CL.Question.point yp))).card : ℝ)
              / (9 * (P * (q * P))))) := by
          have hfac : (0 : ℝ) ≤ N ^ m * (q - 1) :=
            mul_nonneg (by positivity) (by linarith)
          refine mul_le_mul_of_nonneg_left ?_ hfac
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hcnt (le_of_lt (inv_pos.mpr hden))
  · -- nothing contributes, and the right-hand side is nonnegative
    have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀ ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      refine Finset.sum_eq_zero fun s hs => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
      exact absurd (base_of_qmapS_axis hm σc h1 h2) hbase
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _

/-! ### The point bound

Here the averaging is neutral: the image of a point question does not depend on the family
member, so both sides carry the same factor `|Seed|` and the requirement is the unaveraged
`1/(3 q^m) ≤ C/(9 q^m)`. -/

/-- **The point shape of the push-forward bound.** -/
theorem hμ_point (hm : m ∣ Fintype.card F) (xp yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.point xp),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.point xp) (CL.Question.point yp)) := by
  classical
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.point xp),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.point xp ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
    sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  by_cases hxy : xp = yp
  · subst hxy
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1 = CL.Question.point xp ∧
          qmapS hm σc s.questions.2 = CL.Question.point xp)
      {Sample.selfConsistency (revPoint xp)}
      (1 / (3 * Fintype.card (Point F m))) (Fintype.card (Seed F m))
      (fun σc s hc => filter_qmapS_point_subset hm σc xp xp
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
      (fun s hs => by rw [Finset.mem_singleton] at hs; subst hs; exact le_of_eq rfl)
      (fun s _ => Finset.card_le_univ _)
    refine hle.trans ?_
    rw [Finset.card_singleton, Nat.cast_one, clGame_μ_eq, cast_card_clSample, card_seed_real]
    have hcnt : (Fintype.card F : ℝ) * (Fintype.card (Point F m) : ℝ)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.point xp : CL.Question F m), CL.Question.point xp))).card : ℝ) := by
      exact_mod_cast card_filter_clPoint_ge hm xp
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    have hq : (0 : ℝ) < q := card_pos_real
    have hq1 : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
    have hP : (0 : ℝ) < P := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hN : (0 : ℝ) < N := blk_pos hm
    have hden : (0 : ℝ) < 9 * (P * (q * P)) := by positivity
    have h3P : (0 : ℝ) < 3 * P := by positivity
    have hA : (0 : ℝ) ≤ N ^ m * (q - 1) := mul_nonneg (by positivity) (by linarith)
    have hval : 3 * (m : ℝ) * ((q * P) / (9 * (P * (q * P)))) = (m : ℝ) / (3 * P) := by
      field_simp
      ring
    calc (1 : ℝ) * (1 / (3 * P) * (N ^ m * (q - 1)))
        = 1 / (3 * P) * (N ^ m * (q - 1)) := one_mul _
      _ ≤ (3 * m * ((q * P) / (9 * (P * (q * P))))) * (N ^ m * (q - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hA
          rw [hval, div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hm1 (le_of_lt (inv_pos.mpr h3P))
      _ = N ^ m * (q - 1) * (3 * m * ((q * P) / (9 * (P * (q * P))))) := by ring
      _ ≤ N ^ m * (q - 1) * (3 * m *
            (((Finset.univ.filter (fun sm : CL.Sample F m =>
              (sm.question hm sm.tyA, sm.question hm sm.tyB)
                = ((CL.Question.point xp : CL.Question F m),
                    CL.Question.point xp))).card : ℝ) / (9 * (P * (q * P))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hcnt (le_of_lt (inv_pos.mpr hden))
  · have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.point xp ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      rw [filter_qmapS_point_eq_empty hm σc hxy, Finset.sum_empty]
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _

/-! ### The diagonal shape

Two cases, and they are genuinely different. A *nondegenerate* diagonal question determines the
line, the scale and the seed index, so the family is pinned twice over and only `(q/m)^{m-1}` of
its members contribute. A *singleton* question (direction zero) pins the seed index but not the
scale --- scaling the zero direction does nothing --- and is paid for instead by `diagIdx`
sending singleton lines to `χ = m - 1`, where the seeded test has `q^{m-1}` samples rather
than one. -/

omit [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem revPoint_zero : (revPoint (0 : Point F m) : Point F m) = 0 := by
  funext k; rfl

omit [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem extend_zero (j : Fin m) :
    (Sample.extend (0 : Fin ((j : ℕ) + 1) → F) : Point F m) = 0 := by
  funext k
  rw [Sample.extend]
  by_cases h : (k : ℕ) ≤ (j : ℕ)
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; rfl

omit [Fintype F] [NeZero m] in
@[simp] theorem through_zero (u : Point F m) :
    Line.through u (0 : Point F m) = (u, 0) := by
  rw [Line.through, dif_neg]
  rintro ⟨j, hj⟩
  exact hj rfl

/-- **Only a diagonal sample with the line on the left maps to a `DLine` question against a
point**, and the point pins its point. -/
theorem exists_diag_of_qmapS_dline (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    ∃ (j : Fin m) (v : Fin ((j : ℕ) + 1) → F), s = Sample.diag false (revPoint yp) j v := by
  classical
  match s, h1, h2 with
  | Sample.diag false u j v, h1, h2 =>
      refine ⟨j, v, ?_⟩
      have hu : revPoint u = yp := by
        have h : CL.Question.point (revPoint u) = CL.Question.point yp := h2
        injection h
      rw [← hu, revPoint_revPoint]
  | Sample.axis false u i, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.axis true u i, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.selfConsistency u, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])
  | Sample.diag true u j v, h1, _ => exact absurd h1 (by simp [Sample.questions, qmapS, qmap])

/-- **A singleton `DLine` question comes only from a sample with zero direction.** -/
theorem eq_diag_zero_of_qmapS (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    ∃ j : Fin m, s = Sample.diag false (revPoint yp) j (0 : Fin ((j : ℕ) + 1) → F) := by
  classical
  obtain ⟨j, v, rfl⟩ := exists_diag_of_qmapS_dline hm σc h1 h2
  refine ⟨j, ?_⟩
  -- the scale is nonzero, so the reversed direction vanishes, so the direction does
  set ℓ : Line F m := Line.through (revPoint yp) (Sample.extend v) with hℓ
  have h1' : (CL.Question.dline (revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2)
      (seedOf hm (diagIdx ℓ) (σc.1 (diagIdx ℓ))) ((σc.2 : F) • revPoint ℓ.2)
      : CL.Question F m) = CL.Question.dline u₀ s₀ 0 := h1
  have hdir : (σc.2 : F) • (revPoint ℓ.2 : Point F m) = 0 := (CL.Question.dline.inj h1').2.2
  have hrev : (revPoint ℓ.2 : Point F m) = 0 :=
    (smul_eq_zero.mp hdir).resolve_left σc.2.2
  have hℓ2 : (ℓ.2 : Point F m) = 0 := by
    have := congrArg revPoint hrev
    rwa [revPoint_revPoint, revPoint_zero] at this
  -- a canonical presentation has zero direction only for a zero input direction
  have hext : (Sample.extend v : Point F m) = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
      by_contra hall
      exact hne (funext fun k => not_not.mp fun hc => hall ⟨k, hc⟩)
    have hex : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := ⟨k, hk⟩
    have hp : (Sample.extend v : Point F m)
        (Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hex) ≠ 0 := Fin.find_spec hex
    have h2' : (ℓ.2 : Point F m)
        = ((Sample.extend v : Point F m)
            (Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hex))⁻¹
          • (Sample.extend v : Point F m) := by
      rw [hℓ, through_eq hex]
    rw [hℓ2] at h2'
    have := congrFun h2' (Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hex)
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hp] at this
    exact zero_ne_one this
  have hv : v = 0 := by
    funext i
    have hi := congrFun hext ⟨(i : ℕ), lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.isLt⟩
    rw [extend_apply_coe] at hi
    exact hi
  rw [hv]

/-- The adapter's image of a singleton diagonal line. -/
theorem qmapS_diag_zero (hm : m ∣ Fintype.card F) (σc : Seed F m) (u : Point F m) (j : Fin m) :
    qmapS hm σc (Question.diagLine
        (Line.through u (Sample.extend (0 : Fin ((j : ℕ) + 1) → F))))
      = CL.Question.dline (revPoint u) (seedOf hm (Fin.rev idx0) (σc.1 (Fin.rev idx0))) 0 := by
  rw [extend_zero, through_zero, qmapS_diag,
    diagIdx_of_dir_eq_zero (ℓ := ((u, 0) : Line F m)) (by simp)]
  simp

/-- **What a contributing sample forces, for a singleton `DLine` question.** -/
theorem base_of_qmapS_dline_zero (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    u₀ = yp ∧ seedOf hm (Fin.rev idx0) (σc.1 (Fin.rev idx0)) = s₀ := by
  classical
  obtain ⟨j, rfl⟩ := eq_diag_zero_of_qmapS hm σc h1 h2
  have h1' : (CL.Question.dline (revPoint (revPoint yp))
      (seedOf hm (Fin.rev idx0) (σc.1 (Fin.rev idx0))) 0 : CL.Question F m)
      = CL.Question.dline u₀ s₀ 0 := by
    rw [← qmapS_diag_zero hm σc (revPoint yp) j]
    exact h1
  rw [revPoint_revPoint] at h1'
  exact ⟨(CL.Question.dline.inj h1').1.symm, (CL.Question.dline.inj h1').2.1⟩

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- `rep` of the zero direction is the identity: a singleton line is its own base point. -/
theorem rep_zero (u : Point F m) : (CL.rep (0 : Point F m) u : Point F m) = u := by
  show MIPRE.CL.canonLin (Submodule.span F {(0 : Point F m)}) u = u
  rw [Set.singleton_zero, Submodule.span_zero, canonLin_bot]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem val_rev_idx0 : ((Fin.rev (idx0 : Fin m) : Fin m) : ℕ) = m - 1 := by
  rw [Fin.val_rev]
  rfl

/-- **The singleton diagonal shape of the push-forward bound.** The `m` contributing samples have
weight at most `1/(6 m q^m q)`, the family pins the seed index but *not* the scale, and the seeded
test has `q^{m-1}` samples for this question --- which is why `diagIdx` sends singleton lines to
the last block. The three combine at `C = 3m` with a factor `2` to spare. -/
theorem hμ_diag_zero (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ 0),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.dline u₀ s₀ 0) (CL.Question.point yp)) := by
  classical
  by_cases hb : u₀ = yp ∧ chi hm s₀ = Fin.rev idx0
  · obtain ⟨rfl, hchi⟩ := hb
    have hsamples : ∀ σc : Seed F m,
        (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ 0),
          ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point u₀),
            (lidtGame F m d).μ x' y')
        = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
            qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
              qmapS hm σc s.questions.2 = CL.Question.point u₀), s.weight := fun σc =>
      sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
    have hq : (0 : ℝ) < Fintype.card F := card_pos_real
    have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    have hP : (0 : ℝ) < Fintype.card (Point F m) := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
        qmapS hm σc s.questions.2 = CL.Question.point u₀)
      (Finset.univ.image (fun j : Fin m =>
        Sample.diag false (revPoint u₀) j (0 : Fin ((j : ℕ) + 1) → F)))
      (1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ)))
      ((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1))
      (fun σc s hc => by
        obtain ⟨j, rfl⟩ := eq_diag_zero_of_qmapS hm σc hc.1 hc.2
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      (fun s hs => by
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
        show 1 / (6 * m * Fintype.card (Point F m) *
            (Fintype.card F : ℝ) ^ ((j : ℕ) + 1)) ≤ _
        refine one_div_le_one_div_of_le (by positivity) ?_
        have hpow : (Fintype.card F : ℝ) ^ 1 ≤ (Fintype.card F : ℝ) ^ ((j : ℕ) + 1) :=
          pow_le_pow_right₀ hq1 (by omega)
        rw [pow_one] at hpow
        exact mul_le_mul_of_nonneg_left hpow (by positivity))
      (fun s hs => by
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
        exact card_filter_seed_le hm (Fin.rev idx0) s₀ _
          (fun σc hc => (base_of_qmapS_dline_zero hm σc hc.1 hc.2).2))
    refine hle.trans ?_
    -- the seeded count, from below
    have hcnt : ((Fintype.card F : ℝ)) ^ (m - 1)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.dline u₀ s₀ 0 : CL.Question F m),
                  CL.Question.point u₀))).card : ℝ) := by
      have h := card_filter_clDiag_ge hm u₀ s₀ 0 (fun k _ => rfl)
      rw [rep_zero, hchi, val_rev_idx0] at h
      exact_mod_cast h
    have hTcard : (Finset.univ.image (fun j : Fin m =>
        Sample.diag false (revPoint u₀) j (0 : Fin ((j : ℕ) + 1) → F))).card ≤ m := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    rw [clGame_μ_eq, cast_card_clSample, card_seed_real]
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    set cnt : ℝ := ((Finset.univ.filter (fun sm : CL.Sample F m =>
      (sm.question hm sm.tyA, sm.question hm sm.tyB)
        = ((CL.Question.dline u₀ s₀ 0 : CL.Question F m),
            CL.Question.point u₀))).card : ℝ) with hcntdef
    have hN : (0 : ℝ) < N := blk_pos hm
    have hmN : (m : ℝ) * N = q := m_mul_blk hm
    have hPq : P = q ^ m := by rw [hPdef, hqdef, card_point_eq]; push_cast; ring
    have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    have hY : P = q ^ (m - 1) * q := by
      rw [hPq, ← pow_succ]
      congr 1
      omega
    set Y : ℝ := q ^ (m - 1) with hYdef
    set Z : ℝ := N ^ (m - 1) with hZdef
    have hYpos : (0 : ℝ) < Y := by rw [hYdef]; positivity
    have hZpos : (0 : ℝ) < Z := by rw [hZdef]; positivity
    have hNm : N ^ m = Z * N := by
      rw [hZdef, ← pow_succ]
      congr 1
      omega
    have hMcast : ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ)
        = Z * (q - 1) := by
      rw [hZdef, hNdef, hqdef]
      push_cast [cast_card_sub_one]
      ring
    have hAnn : (0 : ℝ) ≤ Z * (q - 1) := mul_nonneg hZpos.le (by linarith)
    calc ((Finset.univ.image (fun j : Fin m =>
              Sample.diag false (revPoint u₀) j (0 : Fin ((j : ℕ) + 1) → F))).card : ℝ)
            * (1 / (6 * m * P * q) *
              ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ))
        ≤ (m : ℝ) * (1 / (6 * m * P * q) * (Z * (q - 1))) := by
          rw [hMcast]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hTcard
      _ = ((m : ℝ) * (1 / (6 * m * P * q))) * (Z * (q - 1)) := by ring
      _ ≤ (N * (3 * m * (Y / (9 * (P * (q * P)))))) * (Z * (q - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hAnn
          have hL : (m : ℝ) * (1 / (6 * m * P * q)) = 1 / (6 * (Y * q ^ 2)) := by
            rw [hY]; field_simp
          have hR : N * (3 * m * (Y / (9 * (P * (q * P))))) = 1 / (3 * (Y * q ^ 2)) := by
            rw [hY, ← hmN]; field_simp; ring
          rw [hL, hR]
          have hW : (0 : ℝ) < Y * q ^ 2 := mul_pos hYpos (pow_pos hq 2)
          exact one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = N ^ m * (q - 1) * (3 * m * (Y / (9 * (P * (q * P))))) := by rw [hNm]; ring
      _ ≤ N ^ m * (q - 1) * (3 * m * (cnt / (9 * (P * (q * P))))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (by positivity) (by linarith : (0:ℝ) ≤ q - 1))
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hYdef]
          exact hcnt
  · -- nothing contributes
    have hsamples : ∀ σc : Seed F m,
        (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ 0),
          ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
            (lidtGame F m d).μ x' y')
        = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
            qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
              qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
      sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
    have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      refine Finset.sum_eq_zero fun s hs => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
      obtain ⟨hu, hseed⟩ := base_of_qmapS_dline_zero hm σc h1 h2
      exact absurd ⟨hu, by rw [← hseed, chi_seedOf]⟩ hb
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _

/-! ### The nondegenerate diagonal shape

Here the question determines the line, the scale *and* the seed index, so the family is pinned
twice and only `(q/m)^{m-1}` of its members contribute. That second pinning is what the scale
averaging bought. -/

omit [Fintype F] [NeZero m] in
theorem exists_ne_zero {x : Point F m} (h : x ≠ 0) : ∃ k, x k ≠ 0 := by
  by_contra hall
  exact h (funext fun k => not_not.mp fun hc => hall ⟨k, hc⟩)

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem revPoint_ne_zero {x : Point F m} (h : x ≠ 0) : (revPoint x : Point F m) ≠ 0 := by
  intro hc
  exact h (by rw [← revPoint_revPoint x, hc, revPoint_zero])

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem ne_zero_of_exists {x : Point F m} (h : ∃ k, x k ≠ 0) : x ≠ 0 := by
  obtain ⟨k, hk⟩ := h
  intro hc
  exact hk (congrFun hc k)

omit [NeZero m] in
/-- **A set of family members agreeing at one seed index and on the scale has at most
`(q/m)^{m-1}` elements.** -/
theorem card_filter_pinned_le (i : Fin m) (P : Seed F m → Prop) [DecidablePred P]
    (hP : ∀ a ∈ Finset.univ.filter P, ∀ b ∈ Finset.univ.filter P,
      a.1 i = b.1 i ∧ (a.2 : F) = (b.2 : F)) :
    (Finset.univ.filter P).card ≤ (Fintype.card F / m) ^ (m - 1) := by
  classical
  have hcard : (Fintype.card F / m) ^ (m - 1)
      = (Finset.univ : Finset ({j : Fin m // j ≠ i} → Fin (Fintype.card F / m))).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_ne_singleton]
  rw [hcard]
  refine Finset.card_le_card_of_injOn (fun σc => fun j => σc.1 j.1)
    (fun _ _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  obtain ⟨hi, hc⟩ := hP a ha b hb
  refine Prod.ext (funext fun j => ?_) (Subtype.ext hc)
  by_cases hj : j = i
  · subst hj; exact hi
  · exact congrFun hab ⟨j, hj⟩

omit [Fintype F] [NeZero m] in
/-- **Rescaling a reversed direction does not move the adapter's base point off the seeded
test's.** This is the diagonal analogue of `revPoint_through_single_eq_rep`: the seeded question
carries `c · ρℓ₂` as its direction and `rep` of that is the adapter's `ρℓ₁ - sh · ρℓ₂`. -/
theorem adapter_base_eq_rep {ℓ : Line F m}
    {x : Point F m} (hx : ∃ t : F, (revPoint x : Point F m) = ℓ.1 + t • ℓ.2)
    {c : F} (hc : c ≠ 0) :
    revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2 = CL.rep (c • revPoint ℓ.2) x := by
  classical
  obtain ⟨t, ht⟩ := hx
  have hx' : (x : Point F m) = revPoint ℓ.1 + t • revPoint ℓ.2 := by
    have h := congrArg (fun z : Point F m => (revPoint z : Point F m)) ht
    simpa using h
  rw [← rep_rev_eq]
  show MIPRE.CL.canonLin (Submodule.span F {(revPoint ℓ.2 : Point F m)}) (revPoint ℓ.1)
      = MIPRE.CL.canonLin (Submodule.span F {(c • revPoint ℓ.2 : Point F m)}) x
  rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc), hx', rep_add_smul]

omit [Fintype F] in
/-- **A seeded direction vanishes below its own `χ`-index**, which is what puts the question in
the seeded test's support. -/
theorem smul_revPoint_eq_zero_below {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) (c : F)
    {k : Fin m} (hk : (k : ℕ) < ((diagIdx ℓ : Fin m) : ℕ)) :
    (c • revPoint ℓ.2 : Point F m) k = 0 := by
  classical
  have hex : ∃ j, (revPoint ℓ.2 : Point F m) j ≠ 0 := by
    obtain ⟨j, hj⟩ := hℓ
    exact ⟨Fin.rev j, by rwa [revPoint_apply, Fin.rev_rev]⟩
  rw [diagIdx_eq_find hex] at hk
  have hz : (revPoint ℓ.2 : Point F m) k = 0 := not_not.mp (Fin.find_min hex hk)
  simp only [Pi.smul_apply, hz, smul_zero]

omit [Fintype F] [NeZero m] in
/-- A canonical presentation has a nonzero direction as soon as its input direction is
nonzero. -/
theorem exists_dir_through {u z : Point F m} (hz : ∃ k, z k ≠ 0) :
    ∃ k, (Line.through u z).2 k ≠ 0 := by
  classical
  refine ⟨Fin.find (fun k => z k ≠ 0) hz, ?_⟩
  rw [through_snd hz]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [inv_mul_cancel₀ (Fin.find_spec hz)]
  exact one_ne_zero

omit [Fintype F] [NeZero m] in
/-- **Rescaling the reversed direction identifies the two canonical presentations.** -/
theorem through_eq_through_revPoint {u z w : Point F m} {c : F} (hc : c ≠ 0)
    (hz : ∃ k, z k ≠ 0)
    (h : c • (revPoint (Line.through u z).2 : Point F m) = w) :
    Line.through u z = Line.through u (revPoint w) := by
  classical
  have hzp : z (Fin.find (fun k => z k ≠ 0) hz) ≠ 0 := Fin.find_spec hz
  rw [through_snd hz, revPoint_smul, smul_smul] at h
  have hcz : c * (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ ≠ 0 :=
    mul_ne_zero hc (inv_ne_zero hzp)
  have hrw : (revPoint w : Point F m)
      = (c * (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹) • z := by
    rw [← h, revPoint_smul, revPoint_revPoint]
  have hzeq : z = (c * (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹)⁻¹ • (revPoint w : Point F m) := by
    rw [hrw, smul_smul, inv_mul_cancel₀ hcz, one_smul]
  have hwnz : ∃ k, (revPoint w : Point F m) k ≠ 0 := by
    refine ⟨Fin.find (fun k => z k ≠ 0) hz, ?_⟩
    rw [hrw]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hcz hzp
  exact (through_eq_through_iff hwnz hz).mpr ⟨_, inv_ne_zero hcz, hzeq⟩

/-- **The data a contributing sample carries**, read off the question. -/
theorem data_of_questions_diagLine (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m} {ℓ : Line F m}
    (hq : s.questions = ((Question.diagLine ℓ : Question F m), Question.point (revPoint yp)))
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w) :
    revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2 = u₀ ∧
      seedOf hm (diagIdx ℓ) (σc.1 (diagIdx ℓ)) = s₀ ∧ (σc.2 : F) • revPoint ℓ.2 = w := by
  have hq1 : s.questions.1 = (Question.diagLine ℓ : Question F m) := congrArg Prod.fst hq
  rw [hq1, qmapS_diag] at h1
  exact CL.Question.dline.inj h1

/-- **A sample mapping to a nondegenerate `DLine` question asks the reversed line at the
reversed point.** -/
theorem forced_of_qmapS_dline (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m} (hw : w ≠ 0)
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    s.questions = ((Question.diagLine (Line.through (revPoint yp) (revPoint w))
      : Question F m), Question.point (revPoint yp)) := by
  classical
  obtain ⟨j, v, rfl⟩ := exists_diag_of_qmapS_dline hm σc h1 h2
  have hq0 : (Sample.diag false (revPoint yp) j v).questions
      = ((Question.diagLine (Line.through (revPoint yp) (Sample.extend v)) : Question F m),
          Question.point (revPoint yp)) := rfl
  obtain ⟨_, _, hscale⟩ := data_of_questions_diagLine hm σc hq0 h1
  have hznz : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
    by_contra hall
    have hz0 : (Sample.extend v : Point F m) = 0 :=
      funext fun k => not_not.mp fun hc => hall ⟨k, hc⟩
    rw [hz0, through_zero] at hscale
    exact hw (by simpa using hscale.symm)
  rw [hq0, through_eq_through_revPoint σc.2.2 hznz hscale]

/-- **What a contributing sample forces, for a nondegenerate `DLine` question.** -/
theorem base_of_qmapS_dline (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m} (hw : w ≠ 0)
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    u₀ = CL.rep w yp
      ∧ chi hm s₀ = diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)
      ∧ ∀ k : Fin m, (k : ℕ) < ((chi hm s₀ : Fin m) : ℕ) → w k = 0 := by
  classical
  have hwnz : ∃ k, (revPoint w : Point F m) k ≠ 0 := exists_ne_zero (revPoint_ne_zero hw)
  have hq := forced_of_qmapS_dline hm σc hw h1 h2
  obtain ⟨hb, hseed, hscale⟩ := data_of_questions_diagLine hm σc hq h1
  have hchi : chi hm s₀ = diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m) := by
    rw [← hseed, chi_seedOf]
  refine ⟨?_, hchi, ?_⟩
  case refine_2 =>
    intro k hk
    rw [hchi] at hk
    have hz := smul_revPoint_eq_zero_below (exists_dir_through hwnz) (σc.2 : F) hk
    rwa [hscale] at hz
  rw [← hb]
  have hgen := adapter_base_eq_rep (ℓ := (Line.through (revPoint yp) (revPoint w) : Line F m))
    (x := yp) ⟨_, through_mem hwnz⟩ σc.2.2
  rw [hscale] at hgen
  exact hgen

/-- **The nondegenerate diagonal shape of the push-forward bound.** At most `m q` samples
contribute, each of weight at most `1/(6 m q^m q^{J+1})`, and the family is pinned both at the
seed index and on the scale, so only `(q/m)^{m-1}` of its members can contribute. Against the
seeded test's `q^{χ}` samples, with `J + 1 + χ = m`, the constant comes out `3q/(2(q-1))`, which
`C = 3m` covers for every `q ≥ 2`. -/
theorem hμ_diag_ne (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) {w : Point F m}
    (hw : w ≠ 0) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ w),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.dline u₀ s₀ w) (CL.Question.point yp)) := by
  classical
  have hwnz : ∃ k, (revPoint w : Point F m) k ≠ 0 := exists_ne_zero (revPoint_ne_zero hw)
  have hdir : ∃ k, (Line.through (revPoint yp) (revPoint w) : Line F m).2 k ≠ 0 :=
    exists_dir_through hwnz
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ w),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
    sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  by_cases hb : u₀ = CL.rep w yp
      ∧ chi hm s₀ = diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)
      ∧ ∀ k : Fin m, (k : ℕ) < ((chi hm s₀ : Fin m) : ℕ) → w k = 0
  · obtain ⟨hbase, hchi, hvan⟩ := hb
    have hq : (0 : ℝ) < Fintype.card F := card_pos_real
    have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    have hq2N : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have hP : (0 : ℝ) < Fintype.card (Point F m) := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w ∧
        qmapS hm σc s.questions.2 = CL.Question.point yp)
      (Finset.univ.filter (fun s : Sample F m => s.questions
        = ((Question.diagLine (Line.through (revPoint yp) (revPoint w)) : Question F m),
            Question.point (revPoint yp))))
      (1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ) ^
        ((Fin.rev (diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)) : ℕ) + 1)))
      ((Fintype.card F / m) ^ (m - 1))
      (fun σc s hc => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, forced_of_qmapS_dline hm σc hw hc.1 hc.2⟩)
      (fun s hs => weight_le_of_questions_diag hdir (Finset.mem_filter.mp hs).2)
      (fun s hs => by
        refine card_filter_pinned_le
          (diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)) _ ?_
        intro a ha b hb'
        have hqs := (Finset.mem_filter.mp hs).2
        obtain ⟨_, hsa, hca⟩ :=
          data_of_questions_diagLine hm a hqs (Finset.mem_filter.mp ha).2.1
        obtain ⟨_, hsb, hcb⟩ :=
          data_of_questions_diagLine hm b hqs (Finset.mem_filter.mp hb').2.1
        refine ⟨seedOf_injective hm _ (hsa.trans hsb.symm), ?_⟩
        have hX : (revPoint (Line.through (revPoint yp) (revPoint w) : Line F m).2
            : Point F m) ≠ 0 := revPoint_ne_zero (ne_zero_of_exists hdir)
        have hsub : (((a.2 : F) - (b.2 : F)) •
            (revPoint (Line.through (revPoint yp) (revPoint w) : Line F m).2 : Point F m)) = 0 := by
          rw [sub_smul, hca, hcb, sub_self]
        rcases smul_eq_zero.mp hsub with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hX)
    refine hle.trans ?_
    -- the seeded count, from below
    have hcnt : ((Fintype.card F : ℝ))
        ^ ((diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m) : Fin m) : ℕ)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.dline u₀ s₀ w : CL.Question F m),
                  CL.Question.point yp))).card : ℝ) := by
      have h := card_filter_clDiag_ge hm yp s₀ w hvan
      rw [← hbase, hchi] at h
      exact_mod_cast h
    have hTcard : (Finset.univ.filter (fun s : Sample F m => s.questions
        = ((Question.diagLine (Line.through (revPoint yp) (revPoint w)) : Question F m),
            Question.point (revPoint yp)))).card ≤ m * Fintype.card F :=
      card_filter_diag_le hdir (revPoint yp)
    rw [clGame_μ_eq, cast_card_clSample, card_seed_real]
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    set cnt : ℝ := ((Finset.univ.filter (fun sm : CL.Sample F m =>
      (sm.question hm sm.tyA, sm.question hm sm.tyB)
        = ((CL.Question.dline u₀ s₀ w : CL.Question F m),
            CL.Question.point yp))).card : ℝ) with hcntdef
    have hq2 : (2 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq2N
    have hN : (0 : ℝ) < N := blk_pos hm
    have hmN : (m : ℝ) * N = q := m_mul_blk hm
    have hPq : P = q ^ m := by rw [hPdef, hqdef, card_point_eq]; push_cast; ring
    set U : ℝ := q ^ ((Fin.rev (diagIdx (Line.through (revPoint yp) (revPoint w)
      : Line F m)) : ℕ) + 1) with hUdef
    set V : ℝ := q ^ ((diagIdx (Line.through (revPoint yp) (revPoint w)
      : Line F m) : Fin m) : ℕ) with hVdef
    set Z : ℝ := N ^ (m - 1) with hZdef
    have hUpos : (0 : ℝ) < U := by rw [hUdef]; exact pow_pos hq _
    have hVpos : (0 : ℝ) < V := by rw [hVdef]; exact pow_pos hq _
    have hZpos : (0 : ℝ) < Z := by rw [hZdef]; exact pow_pos hN _
    have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    have hUV : U * V = P := by
      rw [hUdef, hVdef, ← pow_add, hPq]
      congr 1
      have h1 : ((Fin.rev (diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m))
          : Fin m) : ℕ) = m - (((diagIdx (Line.through (revPoint yp) (revPoint w)
            : Line F m) : Fin m) : ℕ) + 1) := Fin.val_rev _
      have h2 : (((diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m))
          : Fin m) : ℕ) < m := (diagIdx _).isLt
      omega
    have hNm : N ^ m = Z * N := by
      rw [hZdef, ← pow_succ]
      congr 1
      omega
    have hMcast : ((((Fintype.card F / m) ^ (m - 1) : ℕ)) : ℝ) = Z := by
      rw [hZdef, hNdef]
      push_cast
      ring
    calc ((Finset.univ.filter (fun s : Sample F m => s.questions
              = ((Question.diagLine (Line.through (revPoint yp) (revPoint w)) : Question F m),
                  Question.point (revPoint yp)))).card : ℝ)
            * (1 / (6 * m * P * U) * ((((Fintype.card F / m) ^ (m - 1) : ℕ)) : ℝ))
        ≤ ((m : ℝ) * q) * (1 / (6 * m * P * U) * Z) := by
          rw [hMcast]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h : ((m * Fintype.card F : ℕ) : ℝ) = (m : ℝ) * q := by
            rw [hqdef]; push_cast; ring
          rw [← h]
          exact_mod_cast hTcard
      _ = (((m : ℝ) * q) * (1 / (6 * m * P * U))) * Z := by ring
      _ ≤ (N * (q - 1) * (3 * m * (V / (9 * (P * (q * P)))))) * Z := by
          refine mul_le_mul_of_nonneg_right ?_ hZpos.le
          have hL : ((m : ℝ) * q) * (1 / (6 * m * P * U)) = q / (6 * P * U) := by
            field_simp
          have hR : N * (q - 1) * (3 * m * (V / (9 * (P * (q * P)))))
              = ((q - 1) * V) / (3 * P * P) := by
            rw [← hmN]; field_simp; ring
          rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
          have hkey : (q - 1) * V * (6 * P * U) = 6 * P * P * (q - 1) := by
            linear_combination (6 * P * (q - 1)) * hUV
          rw [hkey]
          nlinarith [mul_pos hP hP, hq2]
      _ = N ^ m * (q - 1) * (3 * m * (V / (9 * (P * (q * P))))) := by rw [hNm]; ring
      _ ≤ N ^ m * (q - 1) * (3 * m * (cnt / (9 * (P * (q * P))))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (by positivity) (by linarith : (0:ℝ) ≤ q - 1))
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hVdef]
          exact hcnt
  · have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      refine Finset.sum_eq_zero fun s hs => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
      exact absurd (base_of_qmapS_dline hm σc hw h1 h2) hb
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _

/-! ### The pairs of lines, and the assembly

`lidtGame`'s only same-type subtest is point self-consistency, so no sample asks two lines and
the four remaining shapes carry no weight at all. That is the piece of luck this route runs on:
it needs no line-synchronicity transfer, hence no Schwartz--Zippel and no `d/q` term. -/

/-- **No sample of the canonical-line test asks two lines.** -/
theorem filter_qmapS_line_line_eq_empty (hm : m ∣ Fintype.card F) (σc : Seed F m)
    (x y : CL.Question F m) (hx : ∀ u, x ≠ CL.Question.point u)
    (hy : ∀ u, y ≠ CL.Question.point u) :
    Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = x ∧ qmapS hm σc s.questions.2 = y) = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
  match s, h1, h2 with
  | Sample.selfConsistency u, h1, _ =>
      exact hx _ (h1.symm : x = CL.Question.point (revPoint u))
  | Sample.axis false u i, _, h2 =>
      exact hy _ (h2.symm : y = CL.Question.point (revPoint u))
  | Sample.axis true u i, h1, _ =>
      exact hx _ (h1.symm : x = CL.Question.point (revPoint u))
  | Sample.diag false u j v, _, h2 =>
      exact hy _ (h2.symm : y = CL.Question.point (revPoint u))
  | Sample.diag true u j v, h1, _ =>
      exact hx _ (h1.symm : x = CL.Question.point (revPoint u))

/-- **The shapes with a line on both sides carry no weight.** -/
theorem hμ_line_line (hm : m ∣ Fintype.card F) (x y : CL.Question F m)
    (hx : ∀ u, x ≠ CL.Question.point u) (hy : ∀ u, y ≠ CL.Question.point u) :
    (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y) := by
  classical
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = x ∧ qmapS hm σc s.questions.2 = y), s.weight := fun σc =>
    sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  have hzero : ∀ σc : Seed F m,
      (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = x ∧ qmapS hm σc s.questions.2 = y), s.weight) = 0 := by
    intro σc
    rw [filter_qmapS_line_line_eq_empty hm σc x y hx hy, Finset.sum_empty]
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
  have hmR : (0 : ℝ) < m := m_pos_real
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
  exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _

/-- **The bound for `(x, y)` is the bound for `(y, x)`**, both tests being symmetric under
exchanging the players. -/
theorem hμ_swap (hm : m ∣ Fintype.card F) (x y : CL.Question F m)
    (h : (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = y),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = x), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) * (3 * m * (clGame (d := d) (ldc := ldc) hm).μ y x)) :
    (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y) := by
  classical
  rw [clGame_μ_symm hm x y]
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun σc _ => ?_
  rw [sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) x y,
    sum_fibre_μ_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) y x]
  exact sum_filter_swap (qmapS hm σc) x y

/-- **The push-forward bound, assembled.** The average over the family of the canonical-line
test's mass on the fibre of a seeded question pair is at most `3m` times the seeded test's mass
on it. This is the hypothesis `exists_one_sub_value_adapt_le` asks for, and `3m` is the constant
`thm:lidt-cl-soundness` multiplies its `ε` by --- polynomial in `m`, as `δ_CL` allows, and free
of `q`, which it does not. -/
theorem hμ_qmapS (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y) := by
  classical
  match x, y with
  | .point xp, .point yp => exact hμ_point hm xp yp
  | .aline u₀ s₀, .point yp => exact hμ_axis hm u₀ s₀ yp
  | .dline u₀ s₀ w, .point yp =>
      by_cases hw : w = 0
      · subst hw; exact hμ_diag_zero hm u₀ s₀ yp
      · exact hμ_diag_ne hm u₀ s₀ hw yp
  | .point xp, .aline u₀ s₀ => exact hμ_swap hm _ _ (hμ_axis hm u₀ s₀ xp)
  | .point xp, .dline u₀ s₀ w =>
      refine hμ_swap hm _ _ ?_
      by_cases hw : w = 0
      · subst hw; exact hμ_diag_zero hm u₀ s₀ xp
      · exact hμ_diag_ne hm u₀ s₀ hw xp
  | .aline _ _, .aline _ _ =>
      exact hμ_line_line hm _ _ (fun u => by simp) (fun u => by simp)
  | .aline _ _, .dline _ _ _ =>
      exact hμ_line_line hm _ _ (fun u => by simp) (fun u => by simp)
  | .dline _ _ _, .aline _ _ =>
      exact hμ_line_line hm _ _ (fun u => by simp) (fun u => by simp)
  | .dline _ _ _, .dline _ _ _ =>
      exact hμ_line_line hm _ _ (fun u => by simp) (fun u => by simp)

end MIPRE.LIDT.Adapter
