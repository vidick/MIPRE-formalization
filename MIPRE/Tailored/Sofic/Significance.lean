/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.AssocValue

@[expose] public section

/-!
# The significance of the generators of the associated test

Proposition I:2283, for `assocTest g`. The words of the challenge at `(x, y)` use only `J` and the
variables `X(x, i)`, `i < ℓ(x)`, and `X(y, i)`, `i < ℓ(y)` (`wordOK_words`); there are at most
`2 + 2(ℓ(x) + ℓ(y)) + ℓ(x)² + ℓ(y)² + 2(ℓ^R(x) + ℓ^R(y)) + 2^{ℓ(x) + ℓ(y) + 1} + 1` of them,
the constraint words being deduplicated, each of length at most `ℓ(x) + ℓ(y) + 4`. Hence, with
`L = Λ = g.ansLen`, every generator has significance at most
`sigBound g = (2L + 4)(3 + 8L + 2L² + 2·4^L)` (`sig_le`), and the variable `X(x, i)` at most
`sigBound g · m(x) / W`, where `m(x) = Σ_y (w(x, y) + w(y, x))` is the weight of the question
pairs at `x` and `W` the total weight (`sig_genX_le`).

The paper's count is finer (`4 · 2^{2Λ}`); the coarser one suffices for the perturbation bound.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue Finset

/-! ## Bit lists -/

theorem length_allBits : ∀ n, (allBits n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp [allBits, List.length_flatMap, List.map_const', List.sum_replicate,
      length_allBits n, pow_succ]

theorem mem_allBits : ∀ (n : ℕ) (l : List Bool), l.length = n → l ∈ allBits n
  | 0, l, h => by simp at h; simp [h, allBits]
  | n + 1, [], h => by simp at h
  | n + 1, b :: r, h => by
    simp only [allBits, List.mem_flatMap]
    refine ⟨r, mem_allBits n r (by simpa using h), ?_⟩
    cases b <;> simp

theorem length_consWord_le (g : TailoredGameData) (x y : ℕ) (c : List Bool) :
    (consWord g x y c).length ≤ g.lenAt x + g.lenAt y + 1 := by
  unfold consWord
  split_ifs with h1 h2
  · simp [wJ, wX, genW, List.length_flatMap, List.map_const', List.sum_replicate]
    have := List.length_filter_le (fun i => c.getD i false) (List.range (g.lenAt x))
    have := List.length_filter_le (fun i => c.getD (g.lenAt x + i) false) (List.range (g.lenAt y))
    simp at *
    omega
  · simp [wX, genW, List.length_flatMap, List.map_const', List.sum_replicate]
    have := List.length_filter_le (fun i => c.getD i false) (List.range (g.lenAt x))
    have := List.length_filter_le (fun i => c.getD (g.lenAt x + i) false) (List.range (g.lenAt y))
    simp at *
    omega
  · simp [wJ, genW]

theorem length_consWords_le (g : TailoredGameData) (x y : ℕ) :
    (consWords g x y).length ≤ 2 ^ (g.lenAt x + g.lenAt y + 1) + 1 := by
  unfold consWords
  have hsub : ((consAt g x y).map fun e => consWord g x y e.2.2.2).dedup ⊆
      wJ :: (allBits (g.lenAt x + g.lenAt y + 1)).map (consWord g x y) := by
    intro w hw
    rw [List.mem_dedup, List.mem_map] at hw
    obtain ⟨e, _, rfl⟩ := hw
    by_cases h : e.2.2.2.length = g.lenAt x + g.lenAt y + 1
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_allBits _ _ h))
    · have : consWord g x y e.2.2.2 = wJ := by simp [consWord, h]
      rw [this]; exact List.mem_cons_self
  have := ((List.nodup_dedup _).subperm hsub).length_le
  simpa [length_allBits, add_comm] using this

/-! ## The generators of a challenge -/

/-- The generators that may occur in the challenge at `(x, y)`. -/
def GenOK (g : TailoredGameData) (x y k : ℕ) : Prop :=
  k = genJ ∨ (∃ i < g.lenAt x, k = genX g x i) ∨ (∃ i < g.lenAt y, k = genX g y i)

/-- Every letter of `w` is a generator of the challenge at `(x, y)`. -/
def WordOK (g : TailoredGameData) (x y : ℕ) (w : Word) : Prop := ∀ l ∈ w, GenOK g x y l.1

variable {g : TailoredGameData} {x y : ℕ}

theorem wordOK_append {u v : Word} (hu : WordOK g x y u) (hv : WordOK g x y v) :
    WordOK g x y (u ++ v) := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · exact hu l h
  · exact hv l h

theorem wordOK_invW {u : Word} (hu : WordOK g x y u) : WordOK g x y (invW u) := by
  intro l hl
  simp only [invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  exact hu l' hl'

theorem wordOK_commW {u v : Word} (hu : WordOK g x y u) (hv : WordOK g x y v) :
    WordOK g x y (commW u v) :=
  wordOK_append (wordOK_append (wordOK_append hu hv) (wordOK_invW hu)) (wordOK_invW hv)

theorem wordOK_wJ : WordOK g x y wJ := by
  intro l hl; simp [wJ, genW] at hl; subst hl; left; rfl

theorem wordOK_nil : WordOK g x y [] := by intro l hl; simp at hl

theorem wordOK_wX_x {i : ℕ} (hi : i < g.lenAt x) : WordOK g x y (wX g x i) := by
  intro l hl; simp [wX, genW] at hl; subst hl; right; left; exact ⟨i, hi, rfl⟩

theorem wordOK_wX_y {i : ℕ} (hi : i < g.lenAt y) : WordOK g x y (wX g y i) := by
  intro l hl; simp [wX, genW] at hl; subst hl; right; right; exact ⟨i, hi, rfl⟩

theorem wordOK_varsAt_x {X : Word} (h : X ∈ varsAt g x) : WordOK g x y X := by
  simp only [varsAt, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact wordOK_wX_x hi

theorem wordOK_varsAt_y {X : Word} (h : X ∈ varsAt g y) : WordOK g x y X := by
  simp only [varsAt, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact wordOK_wX_y hi

theorem wordOK_flatMap_x (L : List ℕ) (hL : ∀ i ∈ L, i < g.lenAt x) :
    WordOK g x y (L.flatMap (wX g x)) := by
  intro l hl
  obtain ⟨i, hi, hl⟩ := List.mem_flatMap.mp hl
  exact wordOK_wX_x (hL i hi) l hl

theorem wordOK_flatMap_y (L : List ℕ) (hL : ∀ i ∈ L, i < g.lenAt y) :
    WordOK g x y (L.flatMap (wX g y)) := by
  intro l hl
  obtain ⟨i, hi, hl⟩ := List.mem_flatMap.mp hl
  exact wordOK_wX_y (hL i hi) l hl

theorem wordOK_words {w : Word} (hw : w ∈ words g x y) : WordOK g x y w := by
  unfold words at hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨⟨w', b⟩, hwb, rfl⟩ := List.mem_map.mp hw
      unfold fixedLits at hwb
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap, Prod.mk.injEq,
        List.not_mem_nil, or_false] at hwb
      rcases hwb with ((((h | h) | ⟨X, hX, rfl, -⟩) | ⟨X, hX, rfl, -⟩) | ⟨X, hX, X', hX', rfl, -⟩) |
        ⟨X, hX, X', hX', rfl, -⟩
      · rw [h.1]; exact wordOK_wJ
      · rw [h.1]; exact wordOK_append wordOK_wJ wordOK_wJ
      · rcases hX with hX | hX
        · exact wordOK_commW wordOK_wJ (wordOK_varsAt_x hX)
        · exact wordOK_commW wordOK_wJ (wordOK_varsAt_y hX)
      · rcases hX with hX | hX
        · exact wordOK_append (wordOK_varsAt_x hX) (wordOK_varsAt_x hX)
        · exact wordOK_append (wordOK_varsAt_y hX) (wordOK_varsAt_y hX)
      · exact wordOK_commW (wordOK_varsAt_x hX) (wordOK_varsAt_x hX')
      · exact wordOK_commW (wordOK_varsAt_y hX) (wordOK_varsAt_y hX')
    · obtain ⟨X, hX, hw⟩ := List.mem_flatMap.mp hw
      have hXok : WordOK g x y X := by
        unfold readVars at hX
        rcases List.mem_append.mp hX with hX | hX
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
          exact wordOK_wX_x (lt_of_lt_of_le (List.mem_range.mp hi) (Nat.le_add_right _ _))
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
          exact wordOK_wX_y (lt_of_lt_of_le (List.mem_range.mp hi) (Nat.le_add_right _ _))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hXok
      · exact wordOK_append wordOK_wJ hXok
  · unfold consWords at hw
    rw [List.mem_dedup, List.mem_map] at hw
    obtain ⟨e, _, rfl⟩ := hw
    unfold consWord
    split_ifs
    · refine wordOK_append (wordOK_append wordOK_wJ (wordOK_flatMap_x _ ?_)) (wordOK_flatMap_y _ ?_)
      · intro i hi; exact List.mem_range.mp (List.mem_of_mem_filter hi)
      · intro i hi; exact List.mem_range.mp (List.mem_of_mem_filter hi)
    · refine wordOK_append (wordOK_append wordOK_nil (wordOK_flatMap_x _ ?_)) (wordOK_flatMap_y _ ?_)
      · intro i hi; exact List.mem_range.mp (List.mem_of_mem_filter hi)
      · intro i hi; exact List.mem_range.mp (List.mem_of_mem_filter hi)
    · exact wordOK_wJ

/-! ## Lengths -/

private theorem length_varsAt {z : ℕ} {X : Word} (h : X ∈ varsAt g z) : X.length = 1 := by
  simp only [varsAt, List.mem_map, List.mem_range] at h
  obtain ⟨i, _, rfl⟩ := h
  rfl

private theorem length_invW (u : Word) : (invW u).length = u.length := by simp [invW]

private theorem length_commW (u v : Word) :
    (commW u v).length = 2 * u.length + 2 * v.length := by
  simp [commW, length_invW]; ring

theorem length_words_le {w : Word} (hw : w ∈ words g x y) :
    w.length ≤ g.lenAt x + g.lenAt y + 4 := by
  unfold words at hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨⟨w', b⟩, hwb, rfl⟩ := List.mem_map.mp hw
      unfold fixedLits at hwb
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap, Prod.mk.injEq,
        List.not_mem_nil, or_false] at hwb
      rcases hwb with ((((h | h) | ⟨X, hX, rfl, -⟩) | ⟨X, hX, rfl, -⟩) | ⟨X, hX, X', hX', rfl, -⟩) |
        ⟨X, hX, X', hX', rfl, -⟩
      · rw [h.1]; simp [wJ, genW]
      · rw [h.1]; simp [wJ, genW]
      · have : X.length = 1 := by
          rcases hX with hX | hX <;> exact length_varsAt hX
        simp [length_commW, this, wJ, genW]
      · have : X.length = 1 := by
          rcases hX with hX | hX <;> exact length_varsAt hX
        simp [this]
      · simp [length_commW, length_varsAt hX, length_varsAt hX']
      · simp [length_commW, length_varsAt hX, length_varsAt hX']
    · obtain ⟨X, hX, hw⟩ := List.mem_flatMap.mp hw
      have hXl : X.length = 1 := by
        unfold readVars at hX
        rcases List.mem_append.mp hX with hX | hX
        · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX; rfl
        · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX; rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · omega
      · simp [hXl, wJ, genW]
  · unfold consWords at hw
    rw [List.mem_dedup, List.mem_map] at hw
    obtain ⟨e, _, rfl⟩ := hw
    have := length_consWord_le g x y e.2.2.2
    omega

theorem length_fixedLits :
    (fixedLits g x y).length = 2 + 2 * (g.lenAt x + g.lenAt y) + g.lenAt x ^ 2 + g.lenAt y ^ 2 := by
  simp [fixedLits, varsAt, List.length_flatMap, Function.comp_def, List.map_const',
    List.sum_replicate]
  ring

theorem length_readWords : (readWords g x y).length = 2 * (g.lenRAt x + g.lenRAt y) := by
  simp [readWords, readVars, List.length_flatMap, Function.comp_def, List.map_const',
    List.sum_replicate]
  ring

theorem lenRAt_le_lenAt (z : ℕ) : g.lenRAt z ≤ g.lenAt z := Nat.le_add_right _ _

theorem lenAt_le_ansLen {z : ℕ} (hz : z < g.nV + 1) : g.lenAt z ≤ g.ansLen :=
  Finset.le_sup (f := fun x : Fin (g.nV + 1) => g.lenAt x.val) (mem_univ ⟨z, hz⟩)

/-! ## Significance -/

variable (g) in
/-- The bound on the significance of every generator. -/
def sigBound : ℕ :=
  (2 * g.ansLen + 4) * (3 + 8 * g.ansLen + 2 * g.ansLen ^ 2 + 2 * 4 ^ g.ansLen)

open Classical in
/-- The occurrences of any generator in the words of a challenge number at most `sigBound g`,
and none unless the generator belongs to the challenge. -/
theorem count_words_le (hx : x < g.nV + 1) (hy : y < g.nV + 1) (k : ℕ) :
    ((words g x y).map fun w => (wordCount k w : ℝ)).sum ≤
      if GenOK g x y k then (sigBound g : ℝ) else 0 := by
  split_ifs with hk
  · have hL1 := lenAt_le_ansLen hx
    have hL2 := lenAt_le_ansLen hy
    have h1 : ((words g x y).map fun w => (wordCount k w : ℝ)).sum ≤
        ((words g x y).map fun _ => ((g.lenAt x + g.lenAt y + 4 : ℕ) : ℝ)).sum := by
      apply List.sum_le_sum
      intro w hw
      exact_mod_cast (List.countP_le_length).trans (length_words_le hw)
    refine h1.trans ?_
    rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
    have hlen : (words g x y).length ≤
        3 + 8 * g.ansLen + 2 * g.ansLen ^ 2 + 2 * 4 ^ g.ansLen := by
      have h3 := length_consWords_le g x y
      have h4 : 2 ^ (g.lenAt x + g.lenAt y + 1) ≤ 2 * 4 ^ g.ansLen := by
        rw [pow_succ, show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, mul_comm 2 (2 ^ _)]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h5 := lenRAt_le_lenAt (g := g) x
      have h6 := lenRAt_le_lenAt (g := g) y
      have h7 : g.lenAt x ^ 2 ≤ g.ansLen ^ 2 := Nat.pow_le_pow_left hL1 2
      have h8 : g.lenAt y ^ 2 ≤ g.ansLen ^ 2 := Nat.pow_le_pow_left hL2 2
      simp only [words, List.length_append, List.length_map, length_fixedLits, length_readWords]
      omega
    unfold sigBound
    have : ((g.lenAt x + g.lenAt y + 4 : ℕ) : ℝ) ≤ ((2 * g.ansLen + 4 : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    calc ((words g x y).length : ℝ) * ((g.lenAt x + g.lenAt y + 4 : ℕ) : ℝ)
        ≤ ((3 + 8 * g.ansLen + 2 * g.ansLen ^ 2 + 2 * 4 ^ g.ansLen : ℕ) : ℝ) *
            ((2 * g.ansLen + 4 : ℕ) : ℝ) := by
          gcongr
      _ = _ := by push_cast; ring
  · apply le_of_eq
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    have : wordCount k w = 0 := by
      unfold wordCount
      rw [List.countP_eq_zero]
      intro l hl hlk
      apply hk
      have := wordOK_words hw l hl
      simp only [decide_eq_true_eq] at hlk
      rwa [hlk] at this
    simp [this]

theorem sig_le (k : ℕ) : sig (assocTest g) k ≤ sigBound g := by
  rw [sig_eq, div_le_iff₀ (by exact_mod_cast qwTot_pos g)]
  unfold qwTot
  push_cast
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro x hx
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro y hy
  have := count_words_le (mem_range.mp hx) (mem_range.mp hy) k
  have h2 : ((words g x y).map fun w => (wordCount k w : ℝ)).sum ≤ sigBound g := by
    refine this.trans ?_
    split_ifs <;> simp
  calc (qw g x y : ℝ) * _ ≤ (qw g x y : ℝ) * sigBound g :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = _ := by ring

variable (g) in
/-- The weight of the question pairs at the vertex `x`, `m(x) = Σ_y (w(x, y) + w(y, x))`. -/
def mdeg (x : ℕ) : ℕ := ∑ y ∈ range (g.nV + 1), (qw g x y + qw g y x)

variable (g) in
theorem sum_mdeg : ∑ x ∈ range (g.nV + 1), mdeg g x = 2 * qwTot g := by
  unfold mdeg qwTot
  simp only [sum_add_distrib]
  rw [sum_comm (f := fun x y => qw g y x)]
  ring

/-- The generators `X(x, i)` and `X(x', i')`, `i, i' < Λ`, coincide only when `x = x'`. -/
theorem genX_inj {x x' i i' : ℕ} (hi : i < g.ansLen) (hi' : i' < g.ansLen)
    (h : genX g x i = genX g x' i') : x = x' := by
  unfold genX at h
  have hL : 0 < g.ansLen := by omega
  have e1 : x = (x * g.ansLen + i) / g.ansLen := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hi, zero_add]
  have e2 : x' = (x' * g.ansLen + i') / g.ansLen := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hi', zero_add]
  rw [e1, e2, show x * g.ansLen + i = x' * g.ansLen + i' by omega]

theorem genX_ne_genJ (x i : ℕ) : genX g x i ≠ genJ := by unfold genX genJ; omega

/-- **Significance of a variable** (Proposition I:2283): `X(x, i)` has significance at most
`sigBound g · m(x) / W`. -/
theorem sig_genX_le {x i : ℕ} (hx : x < g.nV + 1) (hi : i < g.lenAt x) :
    sig (assocTest g) (genX g x i) ≤ sigBound g * mdeg g x / qwTot g := by
  rw [sig_eq]
  gcongr
  have hiL : i < g.ansLen := lt_of_lt_of_le hi (lenAt_le_ansLen hx)
  have key : ∀ x' ∈ range (g.nV + 1), ∀ y' ∈ range (g.nV + 1),
      (qw g x' y' : ℝ) * ((words g x' y').map fun w => (wordCount (genX g x i) w : ℝ)).sum ≤
        sigBound g * ((if x' = x then (qw g x' y' : ℝ) else 0) +
          (if y' = x then (qw g x' y' : ℝ) else 0)) := by
    intro x' hx' y' hy'
    have hc := count_words_le (mem_range.mp hx') (mem_range.mp hy') (genX g x i)
    have hq : (0 : ℝ) ≤ qw g x' y' := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ sigBound g := Nat.cast_nonneg _
    have hA : (0 : ℝ) ≤ if x' = x then (qw g x' y' : ℝ) else 0 := by split_ifs <;> simp
    have hB : (0 : ℝ) ≤ if y' = x then (qw g x' y' : ℝ) else 0 := by split_ifs <;> simp
    split_ifs at hc with hk
    · have hor : x' = x ∨ y' = x := by
        rcases hk with h | ⟨i', hi', h⟩ | ⟨i', hi', h⟩
        · exact absurd h (genX_ne_genJ x i)
        · left
          exact (genX_inj hiL (lt_of_lt_of_le hi' (lenAt_le_ansLen (mem_range.mp hx'))) h).symm
        · right
          exact (genX_inj hiL (lt_of_lt_of_le hi' (lenAt_le_ansLen (mem_range.mp hy'))) h).symm
      have hle : (qw g x' y' : ℝ) * _ ≤ (qw g x' y' : ℝ) * sigBound g :=
        mul_le_mul_of_nonneg_left hc hq
      rcases hor with h | h
      · rw [ite_eq_left h] at hA ⊢
        nlinarith
      · rw [ite_eq_left h] at hB ⊢
        nlinarith
    · have h0 : (0 : ℝ) ≤ ((words g x' y').map fun w => (wordCount (genX g x i) w : ℝ)).sum :=
        List.sum_nonneg (fun a ha => by
          obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha; exact Nat.cast_nonneg _)
      have : ((words g x' y').map fun w => (wordCount (genX g x i) w : ℝ)).sum = 0 := by
        linarith
      rw [this, mul_zero]
      positivity
  refine (sum_le_sum fun x' hx' => sum_le_sum fun y' hy' => key x' hx' y' hy').trans
    (le_of_eq ?_)
  simp only [← Finset.mul_sum, sum_add_distrib]
  congr 1
  unfold mdeg
  push_cast
  rw [sum_add_distrib, sum_comm (f := fun x' y' => if y' = x then (qw g x' y' : ℝ) else 0)]
  simp [Finset.sum_ite_eq', mem_range.mpr hx]

end MIPRE.Tailored.Sofic

end
