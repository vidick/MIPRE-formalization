/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Omega
public import MIPRE.Tailored.Sofic.Measure.Conclusion
public import MIPRE.Tactics

@[expose] public section

/-!
# The pseudo-subgroup polytopes at a stage

Paper I, Definition I:897, Lemma I:1105 and the proof of Main Theorem I (2) (I:1170–1220), in a
finitary form. At stage `t` the finite set `B` is the list `stageW T t` of the words of length at
most `t + 2` in the letters below `s + t` (`s` the number of generators); a *pattern* is a bit
list `p` indexed by these words, read as the set of words `extW B p`. A *grid point* is a list `n`
of naturals indexed by the patterns, summing to `M = P 2^t` (`P` the number of patterns), read as
the distribution `n/M` on patterns. It is *feasible* (`Feasible`) when

* every pattern of positive weight is *locally good* (`goodP`): it contains the empty word and
  is closed, within `B`, under cancelling a pair `(i, c)(i, ¬c)`, deleting a letter `i ≥ s`, and
  `u, v ↦ u v⁻¹` — the decidable "locally closed in `B`" relaxation of being a pseudo subgroup,
  which is all the proof of Lemma I:941 (2) uses;
* it is invariant up to `4P` under conjugation by each letter below `s` (`invErr`), comparing
  the distributions of the patterns on the words of length at most `t` (the polytope `Q_B` of
  Definition I:897, with slack).

The upper bound `upperSeq T t` is the best value of a feasible grid point plus the rounding
error `2/2^t`, rounded up to the grid of step `2^{-t}`; it is `1` while some challenge word lies
outside `B`. Everything is a list computation (primitive recursive in `UpperPrimrec.lean`).
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue

/-! ## Words up to a length -/

/-- The letters with generator below `L`. -/
def letters (L : ℕ) : List Letter := (List.range L).flatMap fun i => [(i, false), (i, true)]

/-- One more letter in front. -/
def wordsStep (L : ℕ) (acc : List Word) : List Word := acc.flatMap fun r => (letters L).map (· :: r)

/-- The words of length `k` in the letters below `L`. -/
def wordsLen (L k : ℕ) : List Word := (wordsStep L)^[k] [[]]

/-- The words of length at most `n` in the letters below `L`. -/
def wordsUpTo (L n : ℕ) : List Word := (List.range (n + 1)).flatMap (wordsLen L)

theorem mem_letters {L : ℕ} {l : Letter} : l ∈ letters L ↔ l.1 < L := by
  obtain ⟨i, e⟩ := l
  simp only [letters, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨j, hj, h | h⟩ <;> simp_all
  · intro h; exact ⟨i, h, by cases e <;> simp⟩

theorem mem_wordsLen {L k : ℕ} {u : Word} :
    u ∈ wordsLen L k ↔ u.length = k ∧ ∀ l ∈ u, l.1 < L := by
  induction k generalizing u with
  | zero =>
    simp only [wordsLen, Function.iterate_zero, id, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; simp
    · exact fun h => h.1
  | succ k ih =>
    rw [wordsLen, Function.iterate_succ_apply', ← wordsLen]
    simp only [wordsStep, List.mem_flatMap, List.mem_map, mem_letters]
    constructor
    · rintro ⟨r, hr, l, hl, rfl⟩
      rw [ih] at hr
      refine ⟨by simp [hr.1], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hl
      · exact hr.2 x hx
    · rintro ⟨hlen, hl⟩
      cases u with
      | nil => simp at hlen
      | cons a r =>
        refine ⟨r, ih.2 ⟨by simpa using hlen, fun x hx => hl x (by simp [hx])⟩, a,
          hl a (by simp), rfl⟩

theorem mem_wordsUpTo {L n : ℕ} {u : Word} :
    u ∈ wordsUpTo L n ↔ u.length ≤ n ∧ ∀ l ∈ u, l.1 < L := by
  simp only [wordsUpTo, List.mem_flatMap, List.mem_range, mem_wordsLen]
  constructor
  · rintro ⟨k, hk, rfl, h⟩; exact ⟨Nat.lt_succ_iff.1 hk, h⟩
  · rintro ⟨h1, h2⟩; exact ⟨_, Nat.lt_succ_iff.2 h1, rfl, h2⟩

/-! ## Bit lists -/

theorem mem_allBits {n : ℕ} {p : List Bool} : p ∈ allBits n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [allBits, List.length_eq_zero_iff]
  | succ n ih =>
    simp only [allBits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨r, hr, rfl | rfl⟩ <;> simp [ih.1 hr]
    · intro h
      cases p with
      | nil => simp at h
      | cons b r =>
        refine ⟨r, ih.2 (by simpa using h), ?_⟩
        cases b <;> simp

theorem nodup_allBits (n : ℕ) : (allBits n).Nodup := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
    simp only [allBits]
    refine List.nodup_flatMap.2 ⟨fun r _ => by simp, ?_⟩
    refine ih.pairwise_of_forall_ne fun a _ b _ hab => ?_
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simp_all

theorem length_allBits (n : ℕ) : (allBits n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allBits, List.length_flatMap, List.length_cons, List.length_nil]
    rw [List.map_const', List.sum_replicate, ih, pow_succ]
    simp

/-! ## Patterns -/

/-- The set of words of a pattern on `W`: false outside `W`. -/
def extW (W : List Word) (p : List Bool) : WordSpace := fun u => p.getD (W.idxOf u) false

theorem extW_map {W : List Word} (A : WordSpace) {u : Word} (hu : u ∈ W) :
    extW W (W.map A) u = A u := by
  unfold extW
  have h := List.idxOf_lt_length_of_mem hu
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_idxOf h]

/-- Two adjacent letters at `j` cancel. -/
def cancel2 (u : Word) (j : ℕ) : Bool :=
  decide (j + 1 < u.length) && ((u.getD j (0, false)).1 == (u.getD (j + 1) (0, false)).1) &&
    ((u.getD (j + 1) (0, false)).2 == !(u.getD j (0, false)).2)

/-- The letter at `j` is beyond the generators. -/
def drop1 (s : ℕ) (u : Word) (j : ℕ) : Bool :=
  decide (j < u.length) && decide (s ≤ (u.getD j (0, false)).1)

/-- Membership in a list of words, as a bit. -/
def memW (W : List Word) (u : Word) : Bool := decide (W.idxOf u < W.length)

theorem memW_iff {W : List Word} {u : Word} : memW W u = true ↔ u ∈ W := by
  simp [memW, List.idxOf_lt_length_iff]

/-- **A locally good pattern** on `W`. -/
def goodP (s : ℕ) (W : List Word) (p : List Bool) : Bool :=
  extW W p [] &&
  W.all (fun u => (List.range u.length).all fun j =>
    (!cancel2 u j || (extW W p u == extW W p (u.take j ++ u.drop (j + 2)))) &&
    (!drop1 s u j || (extW W p u == extW W p (u.take j ++ u.drop (j + 1))))) &&
  W.all (fun u => W.all fun v =>
    !(memW W (u ++ invW v) && extW W p u && extW W p v) || extW W p (u ++ invW v))

/-! ## Grid points -/

/-- One more entry in front, at most `M`. -/
def vecsStep (M : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc.flatMap fun r => (List.range (M + 1)).map (· :: r)

/-- The lists of length `P` with entries at most `M`. -/
def allVecs (P M : ℕ) : List (List ℕ) := (vecsStep M)^[P] [[]]

theorem mem_allVecs {P M : ℕ} {n : List ℕ} : n ∈ allVecs P M ↔ n.length = P ∧ ∀ a ∈ n, a ≤ M := by
  induction P generalizing n with
  | zero =>
    simp only [allVecs, Function.iterate_zero, id, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; simp
    · exact fun h => h.1
  | succ P ih =>
    rw [allVecs, Function.iterate_succ_apply', ← allVecs]
    simp only [vecsStep, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨r, hr, a, ha, rfl⟩
      rw [ih] at hr
      refine ⟨by simp [hr.1], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact hr.2 x hx
    · rintro ⟨hlen, hl⟩
      cases n with
      | nil => simp at hlen
      | cons a r =>
        exact ⟨r, ih.2 ⟨by simpa using hlen, fun x hx => hl x (by simp [hx])⟩, a,
          Nat.lt_succ_of_le (hl a (by simp)), rfl⟩

/-- The total weight of the patterns satisfying `f`. -/
def cntR (n : List ℕ) (Pt : List (List Bool)) (f : List Bool → Bool) : ℕ :=
  ((n.zip Pt).map fun x => if f x.2 then x.1 else 0).sum

/-- `|a − b|` on naturals. -/
def ndist (a b : ℕ) : ℕ := (a - b) + (b - a)

theorem ndist_cast (a b : ℕ) : (ndist a b : ℝ) = |(a : ℝ) - b| := by
  unfold ndist
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_sub_comm,
      abs_of_nonneg (by simp [h])]
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by simp [h])]

/-! ## The stage -/

variable (T : SubgroupTestData) (t : ℕ)

/-- The words of the stage: length at most `t + 2`, letters below `s + t`. -/
def stageW : List Word := wordsUpTo (T.nGen + t) (t + 2)

/-- The words on which invariance is compared: length at most `t`. -/
def stageD : List Word := wordsUpTo (T.nGen + t) t

/-- The patterns of the stage. -/
def stagePt : List (List Bool) := allBits (stageW T t).length

/-- The number of patterns. -/
def stageP : ℕ := (stagePt T t).length

/-- The grid size `M = P 2^t`. -/
def stageM : ℕ := stageP T t * 2 ^ t

/-- The invariance error of a grid point under conjugation by the letter `g`. -/
def invErr (g : Letter) (n : List ℕ) : ℕ :=
  ((allBits (stageD T t).length).map fun q =>
    ndist (cntR n (stagePt T t) fun p => (stageD T t).map (extW (stageW T t) p) == q)
      (cntR n (stagePt T t) fun p => (stageD T t).map (conjW g (extW (stageW T t) p)) == q)).sum

/-- **A feasible grid point**: total weight `M`, positive weight only on locally good patterns,
invariant up to `4P` under conjugation by each letter below `s`. -/
def Feasible (n : List ℕ) : Prop :=
  n.sum = stageM T t ∧ (∀ x ∈ n.zip (stagePt T t), 0 < x.1 → goodP T.nGen (stageW T t) x.2 = true) ∧
    ∀ g ∈ letters T.nGen, invErr T t g n ≤ 4 * stageP T t

instance : DecidablePred (Feasible T t) := fun _ => by unfold Feasible; infer_instance

/-- The value of a grid point, times `M`. -/
def numG (n : List ℕ) : ℕ :=
  (T.challenges.map fun ch =>
    ch.1 * cntR n (stagePt T t) fun p => passW ch.2.1 ch.2.2 (extW (stageW T t) p)).sum

/-- The best value of a feasible grid point, times `M`. -/
def maxNum : ℕ :=
  (((allVecs (stageP T t) (stageM T t)).filter (Feasible T t ·)).map (numG T t)).foldr max 0

/-- The challenge words all lie in the stage. -/
def Covers : Prop := ∀ ch ∈ T.challenges, ∀ k ∈ ch.2.1, k ∈ stageW T t

instance : Decidable (Covers T t) := by unfold Covers; infer_instance

/-- **The upper approximation** at stage `t`, as a numerator over `2^t`: the best value of a
feasible grid point plus `2/2^t`, rounded up; `2^t` (the value `1`) before the stage covers the
challenge words. -/
def upperSeq : ℕ :=
  if Covers T t then
    ceilDiv (2 ^ t * (maxNum T t + 2 * stageP T t * T.totalWeight)) (stageM T t * T.totalWeight)
  else 2 ^ t

theorem stageP_pos : 0 < stageP T t := by
  rw [stageP, stagePt, length_allBits]; positivity

theorem stageM_pos : 0 < stageM T t := Nat.mul_pos (stageP_pos T t) (by positivity)

end MIPRE.Tailored.Sofic.Measure

end
