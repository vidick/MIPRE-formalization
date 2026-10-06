/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.TraceIdentity
public import MIPRE.Tailored.Sofic.Passes
public import MIPRE.Tactics

@[expose] public section

/-!
# The signed permutation of a constraint word

Given a signed permutation `γ k` for each generator `k`, a word `w` has the signed permutation
`wordSP γ w`, the product of its letters. When `γ J = -1` and `γ X(z, i)` has matrix `U z i`, the
matrix of the constraint word of `c` is `consMat c = (-1)^{c_J} U^α V^β`
(`toMatrix_wordSP_consWord`): the word is `J^{c_J} ∏ X(x, i)^{c_i} ∏ X(y, i)^{c_{ℓ(x)+i}}` and
`U^α` is the same product over `Fin Λ`, the coefficients beyond `ℓ(x)` being zero.

The diagonal entries of a signed permutation matrix are `1` at the points it fixes with sign
`+`, and otherwise `-1` or `0` (`toMatrix_apply_self_eq_one_iff`, `re_one_sub_toMatrix_apply_self`).
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue

/-! ## Signed permutations of words -/

section WordSP

variable {Ω : Type*} (γ : ℕ → SignedPerm Ω)

/-- The signed permutation of a word, the product of its letters, a letter `(k, b)` acting as
`γ k`, inverted when `b`. -/
def wordSP (w : Word) : SignedPerm Ω :=
  (w.map fun l => if l.2 then (γ l.1)⁻¹ else γ l.1).prod

@[simp] theorem wordSP_nil : wordSP γ [] = 1 := rfl

@[simp] theorem wordSP_append (u v : Word) : wordSP γ (u ++ v) = wordSP γ u * wordSP γ v := by
  simp [wordSP]

@[simp] theorem wordSP_genW (k : ℕ) : wordSP γ (genW k) = γ k := by
  simp [wordSP, genW]

@[simp] theorem wordSP_wJ : wordSP γ wJ = γ genJ := wordSP_genW γ genJ

theorem wordSP_flatMap_genW (l : List ℕ) (f : ℕ → ℕ) :
    wordSP γ (l.flatMap fun i => genW (f i)) = (l.map fun i => γ (f i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [List.flatMap_cons, ih]

end WordSP

section Diag

variable {Ω : Type*} [DecidableEq Ω]

theorem toMatrix_apply_self (s : SignedPerm Ω) (j : Ω) :
    s.toMatrix j j = if s.perm j = j then bitSign (s.sign j) else 0 :=
  SignedPerm.toMatrix_apply s j j

theorem toMatrix_apply_self_eq_one_iff (s : SignedPerm Ω) (j : Ω) :
    s.toMatrix j j = 1 ↔ s.perm j = j ∧ s.sign j = false := by
  rw [toMatrix_apply_self]
  split_ifs with h
  · simp [h, bitSign_eq_one_iff]
  · simp [h]

/-- `Re (1 - M_{jj}) / 2` is `0` where the signed permutation fixes `j` with sign `+`, and at
most `1` elsewhere. -/
theorem re_one_sub_toMatrix_apply_self_le (s : SignedPerm Ω) (j : Ω) :
    ((1 / 2 : ℂ) * (1 - s.toMatrix j j)).re ≤
      if s.perm j = j ∧ s.sign j = false then 0 else 1 := by
  rw [toMatrix_apply_self]
  by_cases h : s.perm j = j
  · cases s.sign j <;> norm_num [h, bitSign]
  · norm_num [h]

theorem re_one_sub_toMatrix_apply_self_nonneg (s : SignedPerm Ω) (j : Ω) :
    0 ≤ ((1 / 2 : ℂ) * (1 - s.toMatrix j j)).re := by
  rw [toMatrix_apply_self]
  by_cases h : s.perm j = j
  · cases s.sign j <;> norm_num [h, bitSign]
  · norm_num [h]

end Diag

/-! ## The matrix of a constraint word -/

/-- A product over the filtered indices, as a product of `ite`s. -/
theorem list_prod_map_filter {M : Type*} [Monoid M] (l : List ℕ) (p : ℕ → Bool) (f : ℕ → M) :
    ((l.filter p).map f).prod = (l.map fun i => if p i then f i else 1).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases h : p i
    · simp [h, ih]
    · simp [h, ih]

namespace ZStrat

variable {g : TailoredGameData} (S : ZStrat g)

/-- The observable `U z i`, for a natural `i`, the identity beyond `Λ`. -/
noncomputable def Unat (z : Fin (g.nV + 1)) (i : ℕ) : Matrix (Fin S.m) (Fin S.m) ℂ :=
  if h : i < g.ansLen then S.U z ⟨i, h⟩ else 1

/-- `U^α`, for `α` supported on the first `ℓ` coordinates, as a product over `range ℓ`. -/
theorem obsChar_eq_prod (z : Fin (g.nV + 1)) (ℓ : ℕ) (hℓ : ℓ ≤ g.ansLen) (q : ℕ → Bool) :
    obsChar (S.U z) (fun i => decide (i.val < ℓ) && q i.val) =
      (((List.range ℓ).filter q).map (S.Unat z)).prod := by
  rw [list_prod_map_filter, obsChar]
  have e1 : (List.finRange g.ansLen).map (fun i => if (decide (i.val < ℓ) && q i.val) then
      S.U z i else 1) = (List.range g.ansLen).map fun i =>
        if (decide (i < ℓ) && q i) then S.Unat z i else 1 := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    have hi : i < g.ansLen := by simpa using h2
    simp [Unat, hi]
  rw [e1]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hℓ
  rw [show List.range g.ansLen = List.range (ℓ + k) by rw [hk], List.range_add, List.map_append,
    List.prod_append, List.map_map]
  rw [List.prod_eq_one (l := List.map _ (List.range k)) (fun a ha => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
    simp), mul_one]
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  simp [List.mem_range.mp hi]

theorem obsChar_coefX (x : Fin (g.nV + 1)) (c : List Bool) :
    obsChar (S.U x) (coefX g x c) =
      (((List.range (g.lenAt x.val)).filter fun i => c.getD i false).map (S.Unat x)).prod := by
  unfold coefX
  exact S.obsChar_eq_prod x _ (lenAt_le_ansLen_fin g x) (fun i => c.getD i false)

theorem obsChar_coefY (x y : Fin (g.nV + 1)) (c : List Bool) :
    obsChar (S.U y) (coefY g x y c) =
      (((List.range (g.lenAt y.val)).filter fun i => c.getD (g.lenAt x.val + i) false).map
        (S.Unat y)).prod := by
  unfold coefY
  exact S.obsChar_eq_prod y _ (lenAt_le_ansLen_fin g y) (fun i => c.getD (g.lenAt x.val + i) false)

/-- **The matrix of a constraint word is the constraint's matrix**, for generators whose signed
permutations have matrices `-1` (for `J`) and the observables (for the variables). -/
theorem toMatrix_wordSP_consWord (x y : Fin (g.nV + 1)) (γ : ℕ → SignedPerm (Fin S.m))
    (hJ : (γ genJ).toMatrix = -1)
    (hX : ∀ (z : Fin (g.nV + 1)) (i : ℕ), i < g.lenAt z.val → (γ (genX g z i)).toMatrix = S.Unat z i)
    (c : List Bool) :
    (wordSP γ (consWord g x y c)).toMatrix = S.consMat x y c := by
  unfold consWord consMat
  by_cases hc : c.length = g.lenAt x.val + g.lenAt y.val + 1
  · rw [ite_eq_left hc, ite_eq_left hc]
    have hmap : ∀ (z : Fin (g.nV + 1)) (l : List ℕ), (∀ i ∈ l, i < g.lenAt z.val) →
        (wordSP γ (l.flatMap (wX g z.val))).toMatrix = (l.map (S.Unat z)).prod := by
      intro z l hl
      rw [show l.flatMap (wX g z.val) = l.flatMap fun i => genW (genX g z.val i) from rfl,
        wordSP_flatMap_genW, ← SignedPerm.toMatrixHom_apply, map_list_prod, List.map_map]
      refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
      exact hX z i (hl i hi)
    have hfx : ∀ i ∈ (List.range (g.lenAt x.val)).filter (fun i => c.getD i false),
        i < g.lenAt x.val := fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
    have hfy : ∀ i ∈ (List.range (g.lenAt y.val)).filter
        (fun i => c.getD (g.lenAt x.val + i) false), i < g.lenAt y.val :=
      fun i hi => List.mem_range.mp (List.mem_filter.mp hi).1
    rw [wordSP_append, wordSP_append, SignedPerm.toMatrix_mul, SignedPerm.toMatrix_mul,
      hmap x _ hfx, hmap y _ hfy, ← S.obsChar_coefX, ← S.obsChar_coefY, coefJ]
    by_cases hJc : c.getD (g.lenAt x.val + g.lenAt y.val) false = true
    · rw [ite_eq_left hJc, wordSP_wJ, hJ, hJc, bitSign_true, neg_one_smul, Matrix.neg_mul,
        Matrix.one_mul, Matrix.neg_mul]
    · rw [ite_eq_right hJc, wordSP_nil, SignedPerm.toMatrix_one, Bool.eq_false_iff.mpr hJc,
        bitSign_false, one_smul, Matrix.one_mul]
  · rw [ite_eq_right hc, ite_eq_right hc, wordSP_wJ, hJ]

end ZStrat

end MIPRE.Tailored.Sofic

end
