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
    have hsq := (Finset.mem_filter.mp (hS ▸ hs)).2
    obtain ⟨j, v, hsj, _, _, _⟩ := of_questions_diag hℓ hsq
    subst hsj
    have hjge : ((Fin.rev (diagIdx ℓ) : ℕ)) ≤ (j : ℕ) :=
      le_rev_diagIdx_of_questions hℓ hsq
    show 1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ) ^ ((j : ℕ) + 1)) ≤ B
    rw [hB]
    refine one_div_le_one_div_of_le hden ?_
    refine mul_le_mul_of_nonneg_left ?_ hA.le
    exact pow_le_pow_right₀ hq1 (by omega)
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

end MIPRE.LIDT.Adapter
