/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Lines

/-!
# The padded space, and the sublines of a padded line

Blueprint `lem:qld-sublines`. The combining stage compares a measurement of *pairs* of
`m`-variable polynomials with a low-degree test, and a low-degree test wants a single polynomial
in a number of variables dividing `q`. The paper's device is to pad: work over `F_q^{4m}`, whose
coordinates split as `u = (x, z, alpha, beta, w)` with `x, z` in `F_q^m`, `alpha, beta` in `F_q`
and `w` in `F_q^{2m-2}` the dummy coordinates, and to combine the pair `(f_X, f_Z)` into the
single polynomial `alpha f_X(x) + beta f_Z(z)`. Admissibility makes `m` a power of two, so
`2m + 2` never divides `q = 2^k`, while `4m` does as soon as `4m <= q`; that is the whole reason
the dummy block is there.

This file is the geometry of that padding, and it is deliberately free of operators.

## The two pieces

* **The seed's block and offset.** The seeded test reads an axis index off a seed through
  `chi`, which is "which of the `m` equal blocks of `F` does `s` fall into". `seedEquiv` names
  the corresponding bijection `F ~ Fin m x Fin (q/m)`, with `chi` as its first component. Two
  things follow that the subline construction needs: a seed can be *retargeted* to a prescribed
  block keeping its offset (`seedIn`), and a uniform seed retargeted to a fixed block is uniform
  on that block's fibre (`sum_seedIn`). The paper's "choose `s_X` uniformly at random subject to
  `chi(s_X) = i`" is exactly this.
* **The blocks of `F_q^{4m}`.** `xIdx`, `zIdx`, `aIdx`, `bIdx` are the coordinate positions and
  `xBlk`, `zBlk`, `alph`, `bet` the projections. `padCase` classifies a coordinate position into
  the four blocks, which is the case distinction the construction of `lem:qld-sublines` branches
  on: whether the padded line's direction moves an `X` coordinate, a `Z` coordinate, or only
  `alpha`, `beta` and the dummy coordinates.

## Why `4m` and not `2m + 2`

`aIdx` and `bIdx` sit at positions `2m` and `2m + 1`, so the dummy block is positions
`2m + 2, ..., 4m - 1`, of size `2m - 2`. Every index bound below needs only `1 <= m`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE.LIDT MIPRE.LIDT.CL

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-! ## The seed's block and offset -/

section Seed

variable [NeZero m]

omit [DecidableEq F] in
theorem mul_card_div (hm : m ∣ Fintype.card F) : m * (Fintype.card F / m) = Fintype.card F :=
  Nat.mul_div_cancel' hm

/-- A seed's block and offset: the bijection `F ~ Fin m x Fin (q/m)` whose first component is
`chi`, available because `m` divides `q`. -/
def seedEquiv (hm : m ∣ Fintype.card F) : F ≃ Fin m × Fin (Fintype.card F / m) :=
  (Fintype.equivFin F).trans ((finCongr (mul_card_div hm).symm).trans finProdFinEquiv.symm)

omit [DecidableEq F] in
/-- The first component of `seedEquiv` is `chi`: both are "divide the index by the block size". -/
@[simp] theorem seedEquiv_fst (hm : m ∣ Fintype.card F) (s : F) :
    (seedEquiv hm s).1 = chi hm s := by
  apply Fin.ext
  rw [chi_val]
  rfl

/-- The seed in block `i` with the same offset as `s`. For a fixed `i` this turns a uniform seed
into a uniform seed of axis index `i`, which is the paper's "`s_X` uniformly at random subject to
`chi(s_X) = i`". -/
def seedIn (hm : m ∣ Fintype.card F) (i : Fin m) (s : F) : F :=
  (seedEquiv hm).symm (i, (seedEquiv hm s).2)

omit [DecidableEq F] in
@[simp] theorem chi_seedIn (hm : m ∣ Fintype.card F) (i : Fin m) (s : F) :
    chi hm (seedIn hm i s) = i := by
  rw [← seedEquiv_fst hm, seedIn, Equiv.apply_symm_apply]

omit [DecidableEq F] in
/-- Retargeting a seed to its own block does nothing. -/
@[simp] theorem seedIn_self (hm : m ∣ Fintype.card F) (s : F) :
    seedIn hm (chi hm s) s = s := by
  rw [seedIn, ← seedEquiv_fst hm]
  exact congrArg _ (Prod.mk.eta) |>.trans ((seedEquiv hm).symm_apply_apply s)

omit [DecidableEq F] in
/-- **A uniform seed retargeted to a fixed block is uniform on that block.** Summing over all
seeds counts each seed of block `i` exactly `m` times, once per block the offset could have come
from. This is the only property of `seedIn` the mixture-of-products statement of
`lem:qld-sublines` uses. -/
theorem sum_seedIn {M : Type*} [AddCommMonoid M] (hm : m ∣ Fintype.card F) (i : Fin m)
    (g : F → M) :
    ∑ s : F, g (seedIn hm i s) = m • ∑ o : Fin (Fintype.card F / m), g ((seedEquiv hm).symm (i, o)) := by
  classical
  rw [← Equiv.sum_comp (seedEquiv hm).symm fun s => g (seedIn hm i s)]
  have hstep : ∀ p : Fin m × Fin (Fintype.card F / m),
      g (seedIn hm i ((seedEquiv hm).symm p)) = g ((seedEquiv hm).symm (i, p.2)) := fun p => by
    rw [seedIn, Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl fun p _ => hstep p]
  calc ∑ p : Fin m × Fin (Fintype.card F / m), g ((seedEquiv hm).symm (i, p.2))
      = ∑ _b : Fin m, ∑ o : Fin (Fintype.card F / m), g ((seedEquiv hm).symm (i, o)) :=
        Fintype.sum_prod_type _
    _ = m • ∑ o : Fin (Fintype.card F / m), g ((seedEquiv hm).symm (i, o)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Seed

/-! ## The blocks of the padded space -/

section Blocks

variable (m)

/-- The position of the `i`-th `X` coordinate of the padded space. -/
def xIdx [NeZero m] (i : Fin m) : Fin (4 * m) :=
  ⟨(i : ℕ), by have := i.isLt; have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- The position of the `i`-th `Z` coordinate of the padded space. -/
def zIdx [NeZero m] (i : Fin m) : Fin (4 * m) :=
  ⟨m + (i : ℕ), by have := i.isLt; have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- The position of the `alpha` coordinate. -/
def aIdx [NeZero m] : Fin (4 * m) :=
  ⟨2 * m, by have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- The position of the `beta` coordinate. -/
def bIdx [NeZero m] : Fin (4 * m) :=
  ⟨2 * m + 1, by have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

variable {m} [NeZero m]

@[simp] theorem xIdx_val (i : Fin m) : (xIdx m i : ℕ) = (i : ℕ) := rfl
@[simp] theorem zIdx_val (i : Fin m) : (zIdx m i : ℕ) = m + (i : ℕ) := rfl
@[simp] theorem aIdx_val : (aIdx m : ℕ) = 2 * m := rfl
@[simp] theorem bIdx_val : (bIdx m : ℕ) = 2 * m + 1 := rfl

theorem xIdx_injective : Function.Injective (xIdx m) := fun i j h => by
  apply Fin.ext; simpa using congrArg Fin.val h

theorem zIdx_injective : Function.Injective (zIdx m) := fun i j h => by
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [zIdx_val] at this
  omega

theorem xIdx_ne_zIdx (i j : Fin m) : xIdx m i ≠ zIdx m j := by
  intro h
  have := congrArg Fin.val h
  simp only [xIdx_val, zIdx_val] at this
  have := i.isLt
  omega

theorem xIdx_ne_aIdx (i : Fin m) : xIdx m i ≠ aIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [xIdx_val, aIdx_val] at this
  have := i.isLt
  omega

theorem xIdx_ne_bIdx (i : Fin m) : xIdx m i ≠ bIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [xIdx_val, bIdx_val] at this
  have := i.isLt
  omega

theorem zIdx_ne_aIdx (i : Fin m) : zIdx m i ≠ aIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [zIdx_val, aIdx_val] at this
  have := i.isLt
  omega

theorem zIdx_ne_bIdx (i : Fin m) : zIdx m i ≠ bIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [zIdx_val, bIdx_val] at this
  have := i.isLt
  omega

theorem aIdx_ne_bIdx : aIdx m ≠ bIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [aIdx_val, bIdx_val] at this
  omega

/-- The `X` block of a padded point. -/
def xBlk (u : Point F (4 * m)) : Point F m := fun i => u (xIdx m i)

/-- The `Z` block of a padded point. -/
def zBlk (u : Point F (4 * m)) : Point F m := fun i => u (zIdx m i)

/-- The `alpha` coordinate of a padded point. -/
def alph (u : Point F (4 * m)) : F := u (aIdx m)

/-- The `beta` coordinate of a padded point. -/
def bet (u : Point F (4 * m)) : F := u (bIdx m)

@[simp] theorem xBlk_apply (u : Point F (4 * m)) (i : Fin m) : xBlk u i = u (xIdx m i) := rfl
@[simp] theorem zBlk_apply (u : Point F (4 * m)) (i : Fin m) : zBlk u i = u (zIdx m i) := rfl

@[simp] theorem xBlk_zero : xBlk (0 : Point F (4 * m)) = (0 : Point F m) := rfl
@[simp] theorem zBlk_zero : zBlk (0 : Point F (4 * m)) = (0 : Point F m) := rfl

@[simp] theorem xBlk_add (u v : Point F (4 * m)) : xBlk (u + v) = xBlk u + xBlk v := rfl
@[simp] theorem zBlk_add (u v : Point F (4 * m)) : zBlk (u + v) = zBlk u + zBlk v := rfl
@[simp] theorem xBlk_smul (t : F) (u : Point F (4 * m)) : xBlk (t • u) = t • xBlk u := rfl
@[simp] theorem zBlk_smul (t : F) (u : Point F (4 * m)) : zBlk (t • u) = t • zBlk u := rfl
@[simp] theorem alph_add (u v : Point F (4 * m)) : alph (u + v) = alph u + alph v := rfl
@[simp] theorem bet_add (u v : Point F (4 * m)) : bet (u + v) = bet u + bet v := rfl
@[simp] theorem alph_smul (t : F) (u : Point F (4 * m)) : alph (t • u) = t * alph u := rfl
@[simp] theorem bet_smul (t : F) (u : Point F (4 * m)) : bet (t • u) = t * bet u := rfl

/-- Moving along the padded line moves the `X` block along the `X` block of the direction. This
is the identity that makes the combining map of `lem:qld-padded-lines` well defined. -/
theorem xBlk_add_smul (u v : Point F (4 * m)) (t : F) :
    xBlk (u + t • v) = xBlk u + t • xBlk v := rfl

theorem zBlk_add_smul (u v : Point F (4 * m)) (t : F) :
    zBlk (u + t • v) = zBlk u + t • zBlk v := rfl

/-! ### Which block a coordinate position lies in -/

/-- Where a coordinate position of the padded space lies: in the `X` block, in the `Z` block, at
`alpha` or `beta`, or among the dummy coordinates. The construction of `lem:qld-sublines`
branches on this. -/
inductive PadCase (m : ℕ) [NeZero m]
  | xc (i : Fin m)
  | zc (i : Fin m)
  | ab
  | dum

/-- The block a coordinate position lies in. -/
def padCase (j : Fin (4 * m)) : PadCase m :=
  if h : (j : ℕ) < m then .xc ⟨(j : ℕ), h⟩
  else if h' : (j : ℕ) < 2 * m then .zc ⟨(j : ℕ) - m, by omega⟩
  else if (j : ℕ) < 2 * m + 2 then .ab
  else .dum

theorem padCase_eq_xc {j : Fin (4 * m)} {i : Fin m} (h : padCase j = .xc i) : j = xIdx m i := by
  unfold padCase at h
  split_ifs at h with h1 h2 h3
  cases h
  rfl

theorem padCase_eq_zc {j : Fin (4 * m)} {i : Fin m} (h : padCase j = .zc i) : j = zIdx m i := by
  unfold padCase at h
  split_ifs at h with h1 h2 h3
  cases h
  apply Fin.ext
  simp only [zIdx_val]
  omega

theorem padCase_xIdx (i : Fin m) : padCase (xIdx m i) = .xc i := by
  unfold padCase
  rw [dif_pos (show (xIdx m i : ℕ) < m from i.isLt)]
  rfl

theorem padCase_zIdx (i : Fin m) : padCase (zIdx m i) = .zc i := by
  unfold padCase
  have hi := i.isLt
  rw [dif_neg (by simp only [zIdx_val]; omega), dif_pos (by simp only [zIdx_val]; omega)]
  congr 1
  apply Fin.ext
  simp only [zIdx_val]
  omega

theorem padCase_aIdx : padCase (aIdx m) = .ab := by
  unfold padCase
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [dif_neg (by simp only [aIdx_val]; omega), dif_neg (by simp only [aIdx_val]; omega),
    if_pos (by simp only [aIdx_val]; omega)]

theorem padCase_bIdx : padCase (bIdx m) = .ab := by
  unfold padCase
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [dif_neg (by simp only [bIdx_val]; omega), dif_neg (by simp only [bIdx_val]; omega),
    if_pos (by simp only [bIdx_val]; omega)]

theorem le_of_padCase_zc {j : Fin (4 * m)} {i : Fin m} (h : padCase j = .zc i) : m ≤ (j : ℕ) := by
  rw [padCase_eq_zc h]; simp only [zIdx_val]; omega

theorem le_of_padCase_ab {j : Fin (4 * m)} (h : padCase j = .ab) : 2 * m ≤ (j : ℕ) := by
  unfold padCase at h
  split_ifs at h with h1 h2 h3
  all_goals omega

theorem le_of_padCase_dum {j : Fin (4 * m)} (h : padCase j = .dum) : 2 * m ≤ (j : ℕ) := by
  unfold padCase at h
  split_ifs at h with h1 h2 h3
  all_goals omega

/-! ### The blocks of a single coordinate and of a truncated direction

These are the only geometric facts the subline construction needs: they say which block of the
padded direction is nonzero, and what it is. -/

theorem xBlk_single_xIdx (i : Fin m) (c : F) :
    xBlk (Pi.single (xIdx m i) c) = Pi.single i c := by
  funext i'
  by_cases h : i' = i
  · subst h; simp [xBlk, Pi.single_eq_same]
  · rw [xBlk_apply, Pi.single_eq_of_ne (fun hh => h (xIdx_injective hh)),
      Pi.single_eq_of_ne h]

theorem xBlk_single_of_le {j : Fin (4 * m)} (h : m ≤ (j : ℕ)) (c : F) :
    xBlk (Pi.single j c) = (0 : Point F m) := by
  funext i'
  have : xIdx m i' ≠ j := fun hh => by
    have := congrArg Fin.val hh
    simp only [xIdx_val] at this
    have := i'.isLt
    omega
  rw [xBlk_apply, Pi.single_eq_of_ne this]
  rfl

theorem zBlk_single_zIdx (i : Fin m) (c : F) :
    zBlk (Pi.single (zIdx m i) c) = Pi.single i c := by
  funext i'
  by_cases h : i' = i
  · subst h; simp [zBlk, Pi.single_eq_same]
  · rw [zBlk_apply, Pi.single_eq_of_ne (fun hh => h (zIdx_injective hh)),
      Pi.single_eq_of_ne h]

theorem zBlk_single_of_lt {j : Fin (4 * m)} (h : (j : ℕ) < m) (c : F) :
    zBlk (Pi.single j c) = (0 : Point F m) := by
  funext i'
  have : zIdx m i' ≠ j := fun hh => by
    have := congrArg Fin.val hh
    simp only [zIdx_val] at this
    omega
  rw [zBlk_apply, Pi.single_eq_of_ne this]
  rfl

theorem zBlk_single_of_ge {j : Fin (4 * m)} (h : 2 * m ≤ (j : ℕ)) (c : F) :
    zBlk (Pi.single j c) = (0 : Point F m) := by
  funext i'
  have : zIdx m i' ≠ j := fun hh => by
    have := congrArg Fin.val hh
    simp only [zIdx_val] at this
    have := i'.isLt
    omega
  rw [zBlk_apply, Pi.single_eq_of_ne this]
  rfl

theorem xBlk_zeroBelow_of_le {j : Fin (4 * m)} (h : m ≤ (j : ℕ)) (v : Point F (4 * m)) :
    xBlk (zeroBelow j v) = (0 : Point F m) := by
  funext i'
  have hi := i'.isLt
  show (if ((xIdx m i' : Fin (4 * m)) : ℕ) < (j : ℕ) then (0 : F) else v (xIdx m i')) = 0
  rw [if_pos (show ((xIdx m i' : Fin (4 * m)) : ℕ) < (j : ℕ) by simp only [xIdx_val]; omega)]

theorem xBlk_zeroBelow_xIdx (i : Fin m) (v : Point F (4 * m)) :
    xBlk (zeroBelow (xIdx m i) v) = zeroBelow i (xBlk v) := by
  funext i'
  rfl

theorem zBlk_zeroBelow_of_le {j : Fin (4 * m)} (h : (j : ℕ) ≤ m) (v : Point F (4 * m)) :
    zBlk (zeroBelow j v) = zBlk v := by
  funext i'
  show (if ((zIdx m i' : Fin (4 * m)) : ℕ) < (j : ℕ) then (0 : F) else v (zIdx m i'))
      = v (zIdx m i')
  rw [if_neg (show ¬ ((zIdx m i' : Fin (4 * m)) : ℕ) < (j : ℕ) by
    simp only [zIdx_val]; omega)]

theorem zBlk_zeroBelow_zIdx (i : Fin m) (v : Point F (4 * m)) :
    zBlk (zeroBelow (zIdx m i) v) = zeroBelow i (zBlk v) := by
  funext i'
  show (if ((zIdx m i' : Fin (4 * m)) : ℕ) < ((zIdx m i : Fin (4 * m)) : ℕ) then (0 : F)
      else v (zIdx m i')) = if (i' : ℕ) < (i : ℕ) then (0 : F) else v (zIdx m i')
  by_cases hii : (i' : ℕ) < (i : ℕ)
  · rw [if_pos (show ((zIdx m i' : Fin (4 * m)) : ℕ) < ((zIdx m i : Fin (4 * m)) : ℕ) by
      simp only [zIdx_val]; omega), if_pos hii]
  · rw [if_neg (show ¬ ((zIdx m i' : Fin (4 * m)) : ℕ) < ((zIdx m i : Fin (4 * m)) : ℕ) by
      simp only [zIdx_val]; omega), if_neg hii]

theorem zBlk_zeroBelow_of_ge {j : Fin (4 * m)} (h : 2 * m ≤ (j : ℕ)) (v : Point F (4 * m)) :
    zBlk (zeroBelow j v) = (0 : Point F m) := by
  funext i'
  have hi := i'.isLt
  show (if ((zIdx m i' : Fin (4 * m)) : ℕ) < (j : ℕ) then (0 : F) else v (zIdx m i')) = 0
  rw [if_pos (show ((zIdx m i' : Fin (4 * m)) : ℕ) < (j : ℕ) by simp only [zIdx_val]; omega)]

end Blocks

/-! ## The sublines of a padded line

Blueprint `lem:qld-sublines`. The paper's `D` is a sampling procedure, and this is that procedure:
`subX` and `subZ` read the two `m`-dimensional line-point pairs off a padded one together with a
pair of fresh seeds and raw directions.

The shape of the construction is forced by what Property 2 demands. Moving along the padded line
moves the `X` block along the `X` block of the padded direction, so if that block is nonzero the
`X` subline has no choice: its direction must be exactly that block, and the only freedom left is
*which seed* presents it, which is where `seedIn` comes in. If the block vanishes the `X` block is
constant along the padded line, the containment is free, and the subline is sampled fresh.

The four cases of `padCase` say which blocks vanish, and they do not say the same thing for the
two line types. For an axis-parallel padded line the direction is a single coordinate, so at most
one of the two blocks is nonzero. For a diagonal padded line the direction is `v` truncated below
the axis index, so an index in the `X` block leaves the whole `Z` block untouched: both blocks are
then nonzero, and the `Z` subline is forced too --- at axis index `0`, since nothing of its
direction is truncated. That asymmetry is the only place `subZ` looks at the line type.
-/

section Sub

/-- The data a line-point pair of the seeded test is generated from: the point, the seed, and the
raw diagonal direction. This is the part of `MIPRE.LIDT.CL.Sample` that the line questions read,
and it has the same shape in the padded dimension `4m` and the unpadded dimension `m`. -/
structure LPData (F : Type*) (m : ℕ) where
  /-- The sampled point. -/
  pt : Point F m
  /-- The seed, which selects the axis index through `chi`. -/
  s : F
  /-- The raw diagonal direction, truncated by `zeroBelow` before use. -/
  raw : Point F m
  deriving DecidableEq, Fintype

variable [NeZero m]

instance : NeZero (4 * m) :=
  ⟨by have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- Truncating below the first coordinate truncates nothing. -/
@[simp] theorem zeroBelow_zero (v : Point F m) : zeroBelow (0 : Fin m) v = v := by
  funext k
  show (if (k : ℕ) < ((0 : Fin m) : ℕ) then (0 : F) else v k) = v k
  rw [if_neg (by simp)]

/-- The sample whose questions this data generates. Both players are given the same type, which is
all that the line questions read. -/
def LPData.toSample (t : CL.Ty) (c : LPData F m) : CL.Sample F m := ⟨t, t, c.pt, c.s, c.raw⟩

/-- The question of type `t` this data presents, as the seeded test computes it. -/
def LPData.question (hm : m ∣ Fintype.card F) (t : CL.Ty) (c : LPData F m) : CL.Question F m :=
  (c.toSample t).question hm t

/-- The direction of the line this data presents. -/
def LPData.dir (hm : m ∣ Fintype.card F) (t : CL.Ty) (c : LPData F m) : Point F m :=
  CL.Question.dir hm (c.question hm t)

@[simp] theorem LPData.dir_point (hm : m ∣ Fintype.card F) (c : LPData F m) :
    c.dir hm .point = 0 := rfl

@[simp] theorem LPData.dir_aline (hm : m ∣ Fintype.card F) (c : LPData F m) :
    c.dir hm .aline = Pi.single (chi hm c.s) 1 := rfl

@[simp] theorem LPData.dir_dline (hm : m ∣ Fintype.card F) (c : LPData F m) :
    c.dir hm .dline = zeroBelow (chi hm c.s) c.raw := rfl

/-- On a line type the base point of the question is the canonical representative of the point in
the direction, which is what puts the point on its own line. -/
theorem LPData.base_aline (hm : m ∣ Fintype.card F) (c : LPData F m) :
    CL.Question.base (c.question hm .aline) = CL.rep (c.dir hm .aline) c.pt := rfl

theorem LPData.base_dline (hm : m ∣ Fintype.card F) (c : LPData F m) :
    CL.Question.base (c.question hm .dline) = CL.rep (c.dir hm .dline) c.pt := rfl

/-- The `X`-side subline data, as a function of the block the padded axis index lies in. Splitting
the case distinction out of `subX` is what lets a proof rewrite the block and then reduce. -/
def subXof (hm : m ∣ Fintype.card F) (k : PadCase m) (P : LPData F (4 * m))
    (e : F × Point F m) : LPData F m :=
  match k with
  | .xc i => ⟨xBlk P.pt, seedIn hm i e.1, xBlk P.raw⟩
  | _ => ⟨xBlk P.pt, e.1, e.2⟩

/-- The `X`-side subline data of a padded line-point pair. The point is the `X` block of the padded
point; the direction is forced to the `X` block of the padded direction when that block is nonzero,
with the fresh seed `e.1` supplying only the offset inside the forced block, and is sampled from `e`
when it vanishes. No case distinction on the line type is needed here: an axis index in the `X`
block forces the `X` block of the direction for both types at once. -/
def subX (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) : LPData F m :=
  subXof hm (padCase (chi hm4 P.s)) P e

/-- The `Z`-side subline data, as a function of the line type and of the block the padded axis index
lies in. -/
def subZof (hm : m ∣ Fintype.card F) (t : CL.Ty) (k : PadCase m) (P : LPData F (4 * m))
    (e : F × Point F m) : LPData F m :=
  match t, k with
  | .dline, .xc _ => ⟨zBlk P.pt, seedIn hm 0 e.1, zBlk P.raw⟩
  | _, .zc i => ⟨zBlk P.pt, seedIn hm i e.1, zBlk P.raw⟩
  | _, _ => ⟨zBlk P.pt, e.1, e.2⟩

/-- The `Z`-side subline data. A diagonal padded line whose axis index lies in the `X` block leaves
the whole `Z` block of its direction intact, so the `Z` subline is forced, at axis index `0` since
nothing of its direction is truncated; an axis-parallel one leaves that block zero, so the `Z`
subline is free. That is the one asymmetry between the two sides. -/
def subZ (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) : LPData F m :=
  subZof hm t (padCase (chi hm4 P.s)) P e

section Eqns

variable (hm : m ∣ Fintype.card F) (t : CL.Ty) (i : Fin m) (P : LPData F (4 * m))
  (e : F × Point F m)

@[simp] theorem subXof_xc :
    subXof hm (.xc i) P e = ⟨xBlk P.pt, seedIn hm i e.1, xBlk P.raw⟩ := rfl
@[simp] theorem subXof_zc : subXof hm (.zc i) P e = ⟨xBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subXof_ab : subXof hm (.ab) P e = ⟨xBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subXof_dum : subXof hm (.dum) P e = ⟨xBlk P.pt, e.1, e.2⟩ := rfl

@[simp] theorem subZof_dline_xc :
    subZof hm .dline (.xc i) P e = ⟨zBlk P.pt, seedIn hm 0 e.1, zBlk P.raw⟩ := rfl
@[simp] theorem subZof_point_xc : subZof hm .point (.xc i) P e = ⟨zBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subZof_aline_xc : subZof hm .aline (.xc i) P e = ⟨zBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subZof_zc :
    subZof hm t (.zc i) P e = ⟨zBlk P.pt, seedIn hm i e.1, zBlk P.raw⟩ := by cases t <;> rfl
@[simp] theorem subZof_ab : subZof hm t (.ab) P e = ⟨zBlk P.pt, e.1, e.2⟩ := by cases t <;> rfl
@[simp] theorem subZof_dum : subZof hm t (.dum) P e = ⟨zBlk P.pt, e.1, e.2⟩ := by cases t <;> rfl

end Eqns

@[simp] theorem subX_pt (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) : (subX hm4 hm P e).pt = xBlk P.pt := by
  rw [subX]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> rfl

@[simp] theorem subZ_pt (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) : (subZ hm4 hm t P e).pt = zBlk P.pt := by
  rw [subZ]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> cases t <;> rfl

/-! ### Property 2 of `lem:qld-sublines`: the blocks of the padded direction -/

/-- **The `X` block of the padded direction is the `X` subline's direction, or it vanishes.** This
is the whole geometric content of the construction: in the first case the `X` block of a point moves
along the subline as the point moves along the padded line, in the second it does not move at all,
and either way it stays on the subline. -/
theorem xBlk_dir_sub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) :
    xBlk (P.dir hm4 t) = (subX hm4 hm P e).dir hm t ∨ xBlk (P.dir hm4 t) = 0 := by
  rw [subX]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _
  · left
    have hj : chi hm4 P.s = xIdx m i := padCase_eq_xc h
    rw [subXof_xc]
    cases t
    · rw [LPData.dir_point, LPData.dir_point, xBlk_zero]
    · rw [LPData.dir_aline, LPData.dir_aline, hj, xBlk_single_xIdx, chi_seedIn]
    · rw [LPData.dir_dline, LPData.dir_dline, hj, xBlk_zeroBelow_xIdx, chi_seedIn]
  all_goals
    right
    have hm' : m ≤ ((chi hm4 P.s : Fin (4 * m)) : ℕ) := by
      first
        | exact le_of_padCase_zc h
        | exact le_trans (show m ≤ 2 * m by omega) (le_of_padCase_ab h)
        | exact le_trans (show m ≤ 2 * m by omega) (le_of_padCase_dum h)
    cases t
    · rw [LPData.dir_point, xBlk_zero]
    · rw [LPData.dir_aline, xBlk_single_of_le hm']
    · rw [LPData.dir_dline, xBlk_zeroBelow_of_le hm']

/-- **The `Z` block of the padded direction is the `Z` subline's direction, or it vanishes.** -/
theorem zBlk_dir_sub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) :
    zBlk (P.dir hm4 t) = (subZ hm4 hm t P e).dir hm t ∨ zBlk (P.dir hm4 t) = 0 := by
  rw [subZ]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _
  · have hj : chi hm4 P.s = xIdx m i := padCase_eq_xc h
    cases t
    · right; rw [LPData.dir_point, zBlk_zero]
    · -- axis-parallel: the `Z` block of a single `X` coordinate vanishes
      right
      rw [LPData.dir_aline, zBlk_single_of_lt (by rw [hj]; exact i.isLt)]
    · -- diagonal: nothing of the `Z` block is truncated, so the subline is forced at index `0`
      left
      rw [LPData.dir_dline, LPData.dir_dline, subZof_dline_xc,
        zBlk_zeroBelow_of_le (by rw [hj]; exact le_of_lt i.isLt), chi_seedIn, zeroBelow_zero]
  · left
    have hj : chi hm4 P.s = zIdx m i := padCase_eq_zc h
    rw [subZof_zc]
    cases t
    · rw [LPData.dir_point, LPData.dir_point, zBlk_zero]
    · rw [LPData.dir_aline, LPData.dir_aline, hj, zBlk_single_zIdx, chi_seedIn]
    · rw [LPData.dir_dline, LPData.dir_dline, hj, zBlk_zeroBelow_zIdx, chi_seedIn]
  all_goals
    right
    have hm' : 2 * m ≤ ((chi hm4 P.s : Fin (4 * m)) : ℕ) := by
      first
        | exact le_of_padCase_ab h
        | exact le_of_padCase_dum h
    cases t
    · rw [LPData.dir_point, zBlk_zero]
    · rw [LPData.dir_aline, zBlk_single_of_ge hm']
    · rw [LPData.dir_dline, zBlk_zeroBelow_of_ge hm']

/-! ### Property 2 of `lem:qld-sublines`, the containment -/

section Containment

-- The canonical representative and the parameter are those of the seeded test, whose field is the
-- binary field the Pauli basis test works over.
variable [Algebra (ZMod 2) F]

/-- Whether the shift direction is the candidate direction or zero, the shifted point lies on the
line the candidate direction presents through the unshifted point. This is the one-line calculation
behind the containment, and it is where the point's own parameter enters. -/
theorem on_line_of_eq_or_zero {W w : Point F m} (h : w = W ∨ w = 0) (x : Point F m) (tau : F) :
    ∃ tau' : F, x + tau • w = CL.rep W x + tau' • W := by
  have hx : CL.rep W x + (CL.lineParam (CL.rep W x) W x) • W = x := rep_add_lineParam_smul W x
  rcases h with h | h <;> rw [h]
  · exact ⟨CL.lineParam (CL.rep W x) W x + tau, by rw [add_smul, ← add_assoc, hx]⟩
  · exact ⟨CL.lineParam (CL.rep W x) W x, by rw [smul_zero, add_zero, hx]⟩

/-- **Property 2 of `lem:qld-sublines`, the `X` side**: the `X` block of every point of the padded
line lies on the `X` subline. -/
theorem xBlk_on_subX (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) (tau : F) :
    ∃ tau' : F, xBlk (P.pt + tau • P.dir hm4 t)
      = CL.rep ((subX hm4 hm P e).dir hm t) (xBlk P.pt)
        + tau' • (subX hm4 hm P e).dir hm t := by
  rw [xBlk_add_smul]
  exact on_line_of_eq_or_zero (xBlk_dir_sub hm4 hm t P e) (xBlk P.pt) tau

/-- **Property 2 of `lem:qld-sublines`, the `Z` side.** -/
theorem zBlk_on_subZ (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) (tau : F) :
    ∃ tau' : F, zBlk (P.pt + tau • P.dir hm4 t)
      = CL.rep ((subZ hm4 hm t P e).dir hm t) (zBlk P.pt)
        + tau' • (subZ hm4 hm t P e).dir hm t := by
  rw [zBlk_add_smul]
  exact on_line_of_eq_or_zero (zBlk_dir_sub hm4 hm t P e) (zBlk P.pt) tau

/-- The containment in the paper's own terms for an axis-parallel padded line: the `X` block of a
point of the padded line is a point of the `X` subline as the seeded test presents it, base point
and direction. -/
theorem xBlk_on_subX_aline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) (tau : F) :
    ∃ tau' : F, xBlk (P.pt + tau • P.dir hm4 .aline)
      = CL.Question.base ((subX hm4 hm P e).question hm .aline)
        + tau' • (subX hm4 hm P e).dir hm .aline := by
  rw [LPData.base_aline, subX_pt]
  exact xBlk_on_subX hm4 hm .aline P e tau

theorem xBlk_on_subX_dline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) (tau : F) :
    ∃ tau' : F, xBlk (P.pt + tau • P.dir hm4 .dline)
      = CL.Question.base ((subX hm4 hm P e).question hm .dline)
        + tau' • (subX hm4 hm P e).dir hm .dline := by
  rw [LPData.base_dline, subX_pt]
  exact xBlk_on_subX hm4 hm .dline P e tau

theorem zBlk_on_subZ_aline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) (tau : F) :
    ∃ tau' : F, zBlk (P.pt + tau • P.dir hm4 .aline)
      = CL.Question.base ((subZ hm4 hm .aline P e).question hm .aline)
        + tau' • (subZ hm4 hm .aline P e).dir hm .aline := by
  rw [LPData.base_aline, subZ_pt]
  exact zBlk_on_subZ hm4 hm .aline P e tau

theorem zBlk_on_subZ_dline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) (tau : F) :
    ∃ tau' : F, zBlk (P.pt + tau • P.dir hm4 .dline)
      = CL.Question.base ((subZ hm4 hm .dline P e).question hm .dline)
        + tau' • (subZ hm4 hm .dline P e).dir hm .dline := by
  rw [LPData.base_dline, subZ_pt]
  exact zBlk_on_subZ hm4 hm .dline P e tau

/-! ### Property 3 of `lem:qld-sublines`

The paper's Property 3 --- an axis-parallel padded line has axis-parallel sublines --- is
definitional here, because the line type is a parameter handed to both sides rather than something
the construction chooses. What is *not* definitional, and is the reason the paper needs the
property, is that the two directions then agree in the way `xBlk_dir_sub` and `zBlk_dir_sub` state;
those are the lemmas a consumer should cite. -/

theorem subX_question_aline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) :
    ∃ u₀ s', (subX hm4 hm P e).question hm .aline = .aline u₀ s' := ⟨_, _, rfl⟩

theorem subZ_question_aline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) :
    ∃ u₀ s', (subZ hm4 hm .aline P e).question hm .aline = .aline u₀ s' := ⟨_, _, rfl⟩

end Containment

end Sub

end MIPRE.QLD
