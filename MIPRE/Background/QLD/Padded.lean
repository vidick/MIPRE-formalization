/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Lines
import MIPRE.Foundations.Blocks

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

/-! ## The padded space as a product of its blocks

`lem:qld-sublines`' second property is distributional: under a uniform point of a padded line the
two sublines are drawn from a mixture of *products* of restricted laws, with each side's point
conditionally uniform on its line. What makes that true is that the `X` and `Z` blocks of a uniform
padded point are uniform and independent, and that is a statement about the index type: `Fin (4m)`
is the disjoint union of the `X` block, the `Z` block, and the `2m` positions above them. `padEquiv`
names that decomposition and `sum_point_pad` is the resulting product identity.
-/

section Product

variable [NeZero m]

/-- The padded index type as a disjoint union of blocks: the `X` block, the `Z` block, and the `2m`
positions holding `alpha`, `beta` and the dummy coordinates. -/
abbrev PadSum (m : ℕ) := (Fin m ⊕ Fin m) ⊕ Fin (2 * m)

/-- The block decomposition of the padded index type. The `X` block lands on positions
`0, ..., m-1` and the `Z` block on `m, ..., 2m-1`, which is exactly `xIdx` and `zIdx`. -/
def padEquiv (m : ℕ) : PadSum m ≃ Fin (4 * m) :=
  ((Equiv.sumCongr (finSumFinEquiv (m := m) (n := m)) (Equiv.refl (Fin (2 * m)))).trans
    finSumFinEquiv).trans (finCongr (by ring))

@[simp] theorem padEquiv_inl_inl (i : Fin m) : padEquiv m (.inl (.inl i)) = xIdx m i := by
  apply Fin.ext
  simp [padEquiv, finSumFinEquiv, Fin.castAdd, Fin.castLE, xIdx]

@[simp] theorem padEquiv_inl_inr (i : Fin m) : padEquiv m (.inl (.inr i)) = zIdx m i := by
  apply Fin.ext
  simp [padEquiv, finSumFinEquiv, Fin.castAdd, Fin.castLE, Fin.natAdd, zIdx]

theorem padEquiv_symm_xIdx (i : Fin m) : (padEquiv m).symm (xIdx m i) = .inl (.inl i) := by
  rw [Equiv.symm_apply_eq, padEquiv_inl_inl]

theorem padEquiv_symm_zIdx (i : Fin m) : (padEquiv m).symm (zIdx m i) = .inl (.inr i) := by
  rw [Equiv.symm_apply_eq, padEquiv_inl_inr]

/-- **The `X` and `Z` blocks of a uniform padded point are uniform and independent.** The remaining
`2m` coordinates -- `alpha`, `beta` and the dummy block -- contribute the multiplicity. -/
theorem sum_point_pad {M : Type*} [AddCommMonoid M] (g : Point F m → Point F m → M) :
    ∑ u : Point F (4 * m), g (xBlk u) (zBlk u)
      = Fintype.card (Fin (2 * m) → F)
        • ∑ pX : Point F m, ∑ pZ : Point F m, g pX pZ := by
  classical
  rw [← Equiv.sum_comp (Equiv.arrowCongr (padEquiv m) (Equiv.refl F))
    (fun u : Point F (4 * m) => g (xBlk u) (zBlk u))]
  have hstep : ∀ U : PadSum m → F,
      g (xBlk ((Equiv.arrowCongr (padEquiv m) (Equiv.refl F)) U))
          (zBlk ((Equiv.arrowCongr (padEquiv m) (Equiv.refl F)) U))
        = (fun w : (Fin m ⊕ Fin m) → F =>
            g (fun i => w (.inl i)) (fun i => w (.inr i))) (fun a => U (.inl a)) := by
    intro U
    congr 1 <;> funext i <;>
      simp [Equiv.arrowCongr, xBlk, zBlk, padEquiv_symm_xIdx, padEquiv_symm_zIdx]
  rw [Finset.sum_congr rfl fun U _ => hstep U,
    sum_arrow_inl (fun w : (Fin m ⊕ Fin m) → F =>
      g (fun i => w (.inl i)) (fun i => w (.inr i))),
    sum_arrow_pair g]

/-- Only the `X` block of the padded point is read. -/
theorem sum_point_pad_x {M : Type*} [AddCommMonoid M] (g : Point F m → M) :
    ∑ u : Point F (4 * m), g (xBlk u)
      = (Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m)) • ∑ pX : Point F m, g pX := by
  rw [show (∑ u : Point F (4 * m), g (xBlk u))
      = ∑ u : Point F (4 * m), (fun pX (_ : Point F m) => g pX) (xBlk u) (zBlk u) from rfl,
    sum_point_pad (fun pX (_ : Point F m) => g pX),
    Finset.sum_congr rfl fun pX _ => Finset.sum_const (g pX), Finset.card_univ,
    Finset.sum_nsmul, smul_smul]

/-- Only the `Z` block of the padded point is read. -/
theorem sum_point_pad_z {M : Type*} [AddCommMonoid M] (g : Point F m → M) :
    ∑ u : Point F (4 * m), g (zBlk u)
      = (Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m)) • ∑ pZ : Point F m, g pZ := by
  rw [show (∑ u : Point F (4 * m), g (zBlk u))
      = ∑ u : Point F (4 * m), (fun (_ : Point F m) pZ => g pZ) (xBlk u) (zBlk u) from rfl,
    sum_point_pad (fun (_ : Point F m) pZ => g pZ), Finset.sum_const, Finset.card_univ,
    smul_smul]

end Product

/-! ## The law of the sublines

`lem:qld-sublines`' second property is that under a uniform point of a padded line the pair of
sublines is drawn from a mixture of *products* of restricted line-point laws, each side's point
conditionally uniform on its own line. `sumRestr` and `sumAll` are the two laws, unnormalized, and
`sumSub` is the sum over the sampling space; the four branch identities below say which product each
branch of the construction gives, and with what multiplicity.
-/

section Law

variable [NeZero m]

/-- The sum of `h` over the data of a line-point pair whose axis index is `i`: the restricted law
`D_{ty,i}` of `def:ith-restricted-line`, unnormalized. The seed ranges over the fibre of `chi` above
`i`, written through `seedEquiv` as an offset. -/
def sumRestr (hm : m ∣ Fintype.card F) (i : Fin m) {M : Type*} [AddCommMonoid M]
    (h : LPData F m → M) : M :=
  ∑ pt : Point F m, ∑ o : Fin (Fintype.card F / m), ∑ raw : Point F m,
    h ⟨pt, (seedEquiv hm).symm (i, o), raw⟩

/-- The sum of `h` over all the data of a line-point pair: the unrestricted seeded law,
unnormalized. -/
def sumAll {M : Type*} [AddCommMonoid M] (h : LPData F m → M) : M :=
  ∑ pt : Point F m, ∑ s : F, ∑ raw : Point F m, h ⟨pt, s, raw⟩

/-- **The unrestricted law is the sum of the `m` restricted ones.** This is the "mixture" of
`lem:qld-sublines`' second property: a branch that leaves a side free gives that side the
unrestricted law, which is the uniform mixture of the `D_{ty,i}`. -/
theorem sumAll_eq_sum_sumRestr (hm : m ∣ Fintype.card F) {M : Type*} [AddCommMonoid M]
    (h : LPData F m → M) : sumAll h = ∑ i : Fin m, sumRestr hm i h := by
  rw [sumAll, show (∑ i : Fin m, sumRestr hm i h)
      = ∑ pt : Point F m, ∑ i : Fin m, ∑ o : Fin (Fintype.card F / m), ∑ raw : Point F m,
          h ⟨pt, (seedEquiv hm).symm (i, o), raw⟩ from Finset.sum_comm]
  refine Finset.sum_congr rfl fun pt _ => ?_
  rw [← Equiv.sum_comp (seedEquiv hm).symm (fun s : F => ∑ raw : Point F m, h ⟨pt, s, raw⟩)]
  exact (MIPRE.sum_prod_eq (fun (i : Fin m) (o : Fin (Fintype.card F / m)) =>
    ∑ raw : Point F m, h ⟨pt, (seedEquiv hm).symm (i, o), raw⟩)).symm

/-- The sum over the subline sampling space at a fixed padded seed: the padded point and the padded
raw direction, and a fresh seed and raw direction for each side. -/
def sumSub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    {M : Type*} [AddCommMonoid M] (g : LPData F m → LPData F m → M) : M :=
  ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
    g (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm t ⟨pt, s, raw⟩ eZ)

/-- **Neither side is forced**: the axis index of the padded line lies in the `alpha`/`beta` block
or among the dummy coordinates, so the padded direction moves neither the `X` nor the `Z` block and
both sublines are sampled fresh. Both sides get the unrestricted law. -/
theorem sumSub_free (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) {s : F}
    (h : padCase (chi hm4 s) = .ab ∨ padCase (chi hm4 s) = .dum) {M : Type*} [AddCommMonoid M]
    (g : LPData F m → LPData F m → M) :
    sumSub hm4 hm t s g
      = (Fintype.card (Point F (4 * m)) * Fintype.card (Fin (2 * m) → F))
        • sumAll (fun cX => sumAll (fun cZ => g cX cZ)) := by
  have hX : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subX hm4 hm ⟨pt, s, raw⟩ e = ⟨xBlk pt, e.1, e.2⟩ := by
    intro pt raw e
    show subXof hm (padCase (chi hm4 s)) _ e = _
    rcases h with h | h <;> rw [h] <;> rfl
  have hZ : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subZ hm4 hm t ⟨pt, s, raw⟩ e = ⟨zBlk pt, e.1, e.2⟩ := by
    intro pt raw e
    show subZof hm t (padCase (chi hm4 s)) _ e = _
    rcases h with h | h <;> rw [h] <;> cases t <;> rfl
  rw [sumSub, Finset.sum_congr rfl fun pt _ => Finset.sum_congr rfl fun raw _ =>
    Finset.sum_congr rfl fun eX _ => Finset.sum_congr rfl fun eZ _ => by
      rw [hX pt raw eX, hZ pt raw eZ]]
  -- the padded raw direction is not read
  rw [Finset.sum_congr rfl fun pt _ => Finset.sum_const _, Finset.card_univ, Finset.sum_nsmul,
    show (∑ pt : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
        g ⟨xBlk pt, eX.1, eX.2⟩ ⟨zBlk pt, eZ.1, eZ.2⟩)
      = ∑ pt : Point F (4 * m), (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
          g ⟨pX, eX.1, eX.2⟩ ⟨pZ, eZ.1, eZ.2⟩) (xBlk pt) (zBlk pt) from rfl,
    sum_point_pad (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
      g ⟨pX, eX.1, eX.2⟩ ⟨pZ, eZ.1, eZ.2⟩), smul_smul]
  congr 1
  have hstep : ∀ pX pZ : Point F m,
      (∑ eX : F × Point F m, ∑ eZ : F × Point F m, g ⟨pX, eX.1, eX.2⟩ ⟨pZ, eZ.1, eZ.2⟩)
        = ∑ sX : F, ∑ vX : Point F m, ∑ sZ : F, ∑ vZ : Point F m,
            g ⟨pX, sX, vX⟩ ⟨pZ, sZ, vZ⟩ := by
    intro pX pZ
    rw [← MIPRE.sum_prod_eq (fun (sX : F) (vX : Point F m) => ∑ eZ : F × Point F m,
      g ⟨pX, sX, vX⟩ ⟨pZ, eZ.1, eZ.2⟩)]
    exact Finset.sum_congr rfl fun sX _ => Finset.sum_congr rfl fun vX _ =>
      (MIPRE.sum_prod_eq (fun (sZ : F) (vZ : Point F m) => g ⟨pX, sX, vX⟩ ⟨pZ, sZ, vZ⟩)).symm
  rw [Finset.sum_congr rfl fun pX _ => Finset.sum_congr rfl fun pZ _ => hstep pX pZ,
    sum_comm_six (fun (pX pZ : Point F m) (sX : F) (vX : Point F m) (sZ : F) (vZ : Point F m) =>
      g ⟨pX, sX, vX⟩ ⟨pZ, sZ, vZ⟩)]
  rfl

/-- **The `Z` side is forced**: the padded axis index lies in the `Z` block, so the `Z` subline's
direction is the `Z` block of the padded direction and its axis index is `i`, while the `X` block of
the padded direction vanishes and the `X` subline is sampled fresh. The `Z` side gets the restricted
law `D_{ty,i}`, the `X` side the unrestricted one. -/
theorem sumSub_zc (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .zc i) {M : Type*} [AddCommMonoid M]
    (g : LPData F m → LPData F m → M) :
    sumSub hm4 hm t s g
      = (Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m)
            * Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m) * m)
        • sumAll (fun cX => sumRestr hm i (fun cZ => g cX cZ)) := by
  have hX : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subX hm4 hm ⟨pt, s, raw⟩ e = ⟨xBlk pt, e.1, e.2⟩ := fun pt raw e => by
    show subXof hm (padCase (chi hm4 s)) _ e = _
    rw [h]
    rfl
  have hZ : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subZ hm4 hm t ⟨pt, s, raw⟩ e = ⟨zBlk pt, seedIn hm i e.1, zBlk raw⟩ := fun pt raw e => by
    show subZof hm t (padCase (chi hm4 s)) _ e = _
    rw [h, subZof_zc]
  rw [sumSub, sum_congr4 (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) => by
      rw [hX pt raw eX, hZ pt raw eZ]),
    sum_comm_four_in (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) =>
      g ⟨xBlk pt, eX.1, eX.2⟩ ⟨zBlk pt, seedIn hm i eZ.1, zBlk raw⟩),
    sum_congr3 (fun (pt : Point F (4 * m)) (eX eZ : F × Point F m) =>
      sum_point_pad_z fun vZ => g ⟨xBlk pt, eX.1, eX.2⟩ ⟨zBlk pt, seedIn hm i eZ.1, vZ⟩),
    sum_nsmul3 (Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m))
      (fun (pt : Point F (4 * m)) (eX eZ : F × Point F m) =>
        ∑ vZ : Point F m, g ⟨xBlk pt, eX.1, eX.2⟩ ⟨zBlk pt, seedIn hm i eZ.1, vZ⟩),
    show (∑ pt : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m, ∑ vZ : Point F m,
          g ⟨xBlk pt, eX.1, eX.2⟩ ⟨zBlk pt, seedIn hm i eZ.1, vZ⟩)
        = ∑ pt : Point F (4 * m), (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
            ∑ vZ : Point F m, g ⟨pX, eX.1, eX.2⟩ ⟨pZ, seedIn hm i eZ.1, vZ⟩) (xBlk pt) (zBlk pt)
      from rfl,
    sum_point_pad (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m, ∑ vZ : Point F m,
      g ⟨pX, eX.1, eX.2⟩ ⟨pZ, seedIn hm i eZ.1, vZ⟩), smul_smul,
    sum_congr2 (fun pX pZ : Point F m => (MIPRE.sum_prod_eq
      (fun (sX : F) (vX : Point F m) => ∑ eZ : F × Point F m, ∑ vZ : Point F m,
        g ⟨pX, sX, vX⟩ ⟨pZ, seedIn hm i eZ.1, vZ⟩)).symm),
    sum_congr4 (fun (pX pZ : Point F m) (sX : F) (vX : Point F m) =>
      sum_prod_fst fun sZ : F => ∑ vZ : Point F m, g ⟨pX, sX, vX⟩ ⟨pZ, seedIn hm i sZ, vZ⟩),
    sum_nsmul4 (Fintype.card (Point F m))
      (fun (pX pZ : Point F m) (sX : F) (vX : Point F m) =>
        ∑ sZ : F, ∑ vZ : Point F m, g ⟨pX, sX, vX⟩ ⟨pZ, seedIn hm i sZ, vZ⟩),
    smul_smul,
    sum_congr4 (fun (pX pZ : Point F m) (sX : F) (vX : Point F m) =>
      sum_seedIn hm i fun sZ : F => ∑ vZ : Point F m, g ⟨pX, sX, vX⟩ ⟨pZ, sZ, vZ⟩),
    sum_nsmul4 m (fun (pX pZ : Point F m) (sX : F) (vX : Point F m) =>
      ∑ o : Fin (Fintype.card F / m), ∑ vZ : Point F m,
        g ⟨pX, sX, vX⟩ ⟨pZ, (seedEquiv hm).symm (i, o), vZ⟩),
    smul_smul,
    sum_comm_six (fun (pX pZ : Point F m) (sX : F) (vX : Point F m)
      (o : Fin (Fintype.card F / m)) (vZ : Point F m) =>
        g ⟨pX, sX, vX⟩ ⟨pZ, (seedEquiv hm).symm (i, o), vZ⟩)]
  rfl

/-- **The `X` side is forced and the `Z` side is not**: the padded axis index lies in the `X` block
and the padded line is axis-parallel (or the question is a point), so the `Z` block of its direction
vanishes. The `X` side gets the restricted law `D_{ty,i}`, the `Z` side the unrestricted one. -/
theorem sumSub_xc (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) {t : CL.Ty} {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .xc i) (ht : t ≠ .dline) {M : Type*} [AddCommMonoid M]
    (g : LPData F m → LPData F m → M) :
    sumSub hm4 hm t s g
      = (Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m)
            * Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m) * m)
        • sumRestr hm i (fun cX => sumAll (fun cZ => g cX cZ)) := by
  have hX : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subX hm4 hm ⟨pt, s, raw⟩ e = ⟨xBlk pt, seedIn hm i e.1, xBlk raw⟩ := fun pt raw e => by
    show subXof hm (padCase (chi hm4 s)) _ e = _
    rw [h]
    rfl
  have hZ : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subZ hm4 hm t ⟨pt, s, raw⟩ e = ⟨zBlk pt, e.1, e.2⟩ := fun pt raw e => by
    show subZof hm t (padCase (chi hm4 s)) _ e = _
    rw [h]
    cases t
    · rfl
    · rfl
    · exact absurd rfl ht
  rw [sumSub, sum_congr4 (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) => by
      rw [hX pt raw eX, hZ pt raw eZ]),
    sum_comm_four_mid (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) =>
      g ⟨xBlk pt, seedIn hm i eX.1, xBlk raw⟩ ⟨zBlk pt, eZ.1, eZ.2⟩),
    sum_congr2 (fun (pt : Point F (4 * m)) (eX : F × Point F m) =>
      sum_point_pad_x fun vX => ∑ eZ : F × Point F m,
        g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, eZ.1, eZ.2⟩),
    sum_nsmul2 (Fintype.card (Fin (2 * m) → F) * Fintype.card (Point F m))
      (fun (pt : Point F (4 * m)) (eX : F × Point F m) =>
        ∑ vX : Point F m, ∑ eZ : F × Point F m,
          g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, eZ.1, eZ.2⟩),
    show (∑ pt : Point F (4 * m), ∑ eX : F × Point F m, ∑ vX : Point F m, ∑ eZ : F × Point F m,
          g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, eZ.1, eZ.2⟩)
        = ∑ pt : Point F (4 * m), (fun pX pZ => ∑ eX : F × Point F m, ∑ vX : Point F m,
            ∑ eZ : F × Point F m, g ⟨pX, seedIn hm i eX.1, vX⟩ ⟨pZ, eZ.1, eZ.2⟩)
              (xBlk pt) (zBlk pt) from rfl,
    sum_point_pad (fun pX pZ => ∑ eX : F × Point F m, ∑ vX : Point F m, ∑ eZ : F × Point F m,
      g ⟨pX, seedIn hm i eX.1, vX⟩ ⟨pZ, eZ.1, eZ.2⟩), smul_smul,
    sum_congr2 (fun pX pZ : Point F m =>
      sum_prod_fst fun sX : F => ∑ vX : Point F m, ∑ eZ : F × Point F m,
        g ⟨pX, seedIn hm i sX, vX⟩ ⟨pZ, eZ.1, eZ.2⟩),
    sum_nsmul2 (Fintype.card (Point F m)) (fun pX pZ : Point F m =>
      ∑ sX : F, ∑ vX : Point F m, ∑ eZ : F × Point F m,
        g ⟨pX, seedIn hm i sX, vX⟩ ⟨pZ, eZ.1, eZ.2⟩),
    smul_smul,
    sum_congr2 (fun pX pZ : Point F m =>
      sum_seedIn hm i fun sX : F => ∑ vX : Point F m, ∑ eZ : F × Point F m,
        g ⟨pX, sX, vX⟩ ⟨pZ, eZ.1, eZ.2⟩),
    sum_nsmul2 m (fun pX pZ : Point F m =>
      ∑ o : Fin (Fintype.card F / m), ∑ vX : Point F m, ∑ eZ : F × Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, eZ.1, eZ.2⟩),
    smul_smul,
    sum_congr4 (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) (vX : Point F m) =>
      (MIPRE.sum_prod_eq (fun (sZ : F) (vZ : Point F m) =>
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, sZ, vZ⟩)).symm),
    sum_comm_six (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) (vX : Point F m)
      (sZ : F) (vZ : Point F m) =>
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, sZ, vZ⟩)]
  rfl

/-- **Both sides are forced**: the padded axis index lies in the `X` block and the padded line is
diagonal, so its direction truncates nothing of the `Z` block and the `Z` subline is forced as well,
at axis index `0`. Both sides get restricted laws. This is the branch whose repair the paper's
round-12 note on `lem:qld-sublines` records. -/
theorem sumSub_xc_dline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .xc i) {M : Type*} [AddCommMonoid M]
    (g : LPData F m → LPData F m → M) :
    sumSub hm4 hm .dline s g
      = (Fintype.card (Fin (2 * m) → F) * Fintype.card (Fin (2 * m) → F)
            * Fintype.card (Point F m) * m * Fintype.card (Point F m) * m)
        • sumRestr hm i (fun cX => sumRestr hm 0 (fun cZ => g cX cZ)) := by
  have hX : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subX hm4 hm ⟨pt, s, raw⟩ e = ⟨xBlk pt, seedIn hm i e.1, xBlk raw⟩ := fun pt raw e => by
    show subXof hm (padCase (chi hm4 s)) _ e = _
    rw [h]
    rfl
  have hZ : ∀ (pt raw : Point F (4 * m)) (e : F × Point F m),
      subZ hm4 hm .dline ⟨pt, s, raw⟩ e = ⟨zBlk pt, seedIn hm 0 e.1, zBlk raw⟩ :=
    fun pt raw e => by
      show subZof hm .dline (padCase (chi hm4 s)) _ e = _
      rw [h]
      rfl
  rw [sumSub, sum_congr4 (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) => by
      rw [hX pt raw eX, hZ pt raw eZ]),
    sum_comm_four_in (fun (pt raw : Point F (4 * m)) (eX eZ : F × Point F m) =>
      g ⟨xBlk pt, seedIn hm i eX.1, xBlk raw⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, zBlk raw⟩),
    sum_congr3 (fun (pt : Point F (4 * m)) (eX eZ : F × Point F m) =>
      sum_point_pad (fun vX vZ =>
        g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, vZ⟩)),
    sum_nsmul3 (Fintype.card (Fin (2 * m) → F))
      (fun (pt : Point F (4 * m)) (eX eZ : F × Point F m) =>
        ∑ vX : Point F m, ∑ vZ : Point F m,
          g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, vZ⟩),
    show (∑ pt : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m, ∑ vX : Point F m,
          ∑ vZ : Point F m,
            g ⟨xBlk pt, seedIn hm i eX.1, vX⟩ ⟨zBlk pt, seedIn hm 0 eZ.1, vZ⟩)
        = ∑ pt : Point F (4 * m), (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
            ∑ vX : Point F m, ∑ vZ : Point F m,
              g ⟨pX, seedIn hm i eX.1, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩) (xBlk pt) (zBlk pt)
      from rfl,
    sum_point_pad (fun pX pZ => ∑ eX : F × Point F m, ∑ eZ : F × Point F m, ∑ vX : Point F m,
      ∑ vZ : Point F m, g ⟨pX, seedIn hm i eX.1, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩), smul_smul,
    sum_congr2 (fun pX pZ : Point F m =>
      sum_prod_fst fun sX : F => ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, seedIn hm i sX, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    sum_nsmul2 (Fintype.card (Point F m)) (fun pX pZ : Point F m =>
      ∑ sX : F, ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, seedIn hm i sX, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    smul_smul,
    sum_congr2 (fun pX pZ : Point F m =>
      sum_seedIn hm i fun sX : F => ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, sX, vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    sum_nsmul2 m (fun pX pZ : Point F m =>
      ∑ o : Fin (Fintype.card F / m), ∑ eZ : F × Point F m, ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, seedIn hm 0 eZ.1, vZ⟩),
    smul_smul,
    sum_congr3 (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
      sum_prod_fst fun sZ : F => ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, seedIn hm 0 sZ, vZ⟩),
    sum_nsmul3 (Fintype.card (Point F m))
      (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
        ∑ sZ : F, ∑ vX : Point F m, ∑ vZ : Point F m,
          g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, seedIn hm 0 sZ, vZ⟩),
    smul_smul,
    sum_congr3 (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
      sum_seedIn hm 0 fun sZ : F => ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, sZ, vZ⟩),
    sum_nsmul3 m (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) =>
      ∑ o' : Fin (Fintype.card F / m), ∑ vX : Point F m, ∑ vZ : Point F m,
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, (seedEquiv hm).symm (0, o'), vZ⟩),
    smul_smul,
    sum_comm_six_swap (fun (pX pZ : Point F m) (o o' : Fin (Fintype.card F / m))
      (vX vZ : Point F m) =>
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, (seedEquiv hm).symm (0, o'), vZ⟩),
    sum_comm_six (fun (pX pZ : Point F m) (o : Fin (Fintype.card F / m)) (vX : Point F m)
      (o' : Fin (Fintype.card F / m)) (vZ : Point F m) =>
        g ⟨pX, (seedEquiv hm).symm (i, o), vX⟩ ⟨pZ, (seedEquiv hm).symm (0, o'), vZ⟩)]
  rfl

end Law

/-! ## From sums to averages

The four branch identities are sum identities with an explicit multiplicity: the assignments to the
coordinates and to the fresh randomness that the construction does not read. Dividing by the number
of terms turns them into the statement `lem:qld-sublines` makes --- an identity of *laws*, with no
constant left over. The average over the subline sampling space is exactly the average over a
product of two line-point laws, restricted on a side exactly when the padded direction forces that
side's subline.
-/

section Average

variable [NeZero m]

/-- The average of `h` over all the data of a line-point pair: `q^m` points, `q` seeds, `q^m` raw
directions. -/
def avgAll (h : LPData F m → ℝ) : ℝ := ((Fintype.card F : ℝ) ^ (2 * m + 1))⁻¹ * sumAll h

/-- The average of `h` over the data of a line-point pair with axis index `i`: the restricted law
`D_{ty,i}`, whose seed ranges over one block of `q/m` elements. -/
def avgRestr (hm : m ∣ Fintype.card F) (i : Fin m) (h : LPData F m → ℝ) : ℝ :=
  ((Fintype.card F : ℝ) ^ (2 * m) * ((Fintype.card F / m : ℕ) : ℝ))⁻¹ * sumRestr hm i h

/-- The average of `g` over the subline sampling space at a fixed padded seed: two padded points and
two fresh seed-and-direction pairs. -/
def avgSub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g : LPData F m → LPData F m → ℝ) : ℝ :=
  ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * sumSub hm4 hm t s g

theorem sumAll_const_mul (c : ℝ) (h : LPData F m → ℝ) :
    sumAll (fun cX => c * h cX) = c * sumAll h := by
  simp only [sumAll, Finset.mul_sum]

theorem sumRestr_const_mul (hm : m ∣ Fintype.card F) (i : Fin m) (c : ℝ)
    (h : LPData F m → ℝ) : sumRestr hm i (fun cZ => c * h cZ) = c * sumRestr hm i h := by
  simp only [sumRestr, Finset.mul_sum]

/-- The block size as a real division, which is what clearing the denominators needs. -/
theorem cast_card_div (hm : m ∣ Fintype.card F) :
    ((Fintype.card F / m : ℕ) : ℝ) = (Fintype.card F : ℝ) / (m : ℝ) :=
  eq_div_of_mul_eq (Nat.cast_ne_zero.mpr (NeZero.ne m))
    (by rw [← Nat.cast_mul, mul_comm, mul_card_div hm])

/-- **Neither side forced**: the padded average is the product of the two unrestricted averages. -/
theorem avgSub_free (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) {s : F}
    (h : padCase (chi hm4 s) = .ab ∨ padCase (chi hm4 s) = .dum)
    (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm t s g = avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [avgSub, avgAll]
  rw [sumSub_free hm4 hm t h g, sumAll_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const]
  push_cast
  field_simp
  ring

/-- **The `Z` side forced**: the padded average is the product of the unrestricted `X` average and
the restricted `Z` average at index `i`. -/
theorem avgSub_zc (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .zc i) (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm t s g = avgAll (fun cX => avgRestr hm i (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgSub, avgAll, avgRestr]
  rw [sumSub_zc hm4 hm t h g, sumAll_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const, cast_card_div hm]
  push_cast
  field_simp
  ring

/-- **The `X` side forced, the `Z` side free.** -/
theorem avgSub_xc (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) {t : CL.Ty} {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .xc i) (ht : t ≠ .dline)
    (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm t s g = avgRestr hm i (fun cX => avgAll (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgSub, avgAll, avgRestr]
  rw [sumSub_xc hm4 hm h ht g, sumRestr_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const, cast_card_div hm]
  push_cast
  field_simp
  ring

/-- **Both sides forced**, the `Z` side at index `0`. -/
theorem avgSub_xc_dline (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) {s : F}
    {i : Fin m} (h : padCase (chi hm4 s) = .xc i) (g : LPData F m → LPData F m → ℝ) :
    avgSub hm4 hm .dline s g
      = avgRestr hm i (fun cX => avgRestr hm 0 (fun cZ => g cX cZ)) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgSub, avgAll, avgRestr]
  rw [sumSub_xc_dline hm4 hm h g, sumRestr_const_mul, nsmul_eq_mul, Fintype.card_pi_const,
    Fintype.card_pi_const, cast_card_div hm]
  push_cast
  field_simp
  ring

/-! ### The restricted law is the unrestricted one up to a factor of `m`

The paper's `def:ith-restricted-line` splits the line-point distribution by axis index and observes
that an approximation holding at error `delta` on average holds on each restricted law at
`2m * delta` --- the `2` being the mixture over the two line types, which here is a parameter rather
than something mixed over, so the factor is `m`. This is where every factor of `m` in
`delta_combine = m * poly(eps, md/q)` comes from, and it is one line on top of
`sumAll_eq_sum_sumRestr`: the `m` restricted laws are nonnegative and average to the unrestricted
one, so each of them is at most `m` times it. -/

theorem sumAll_nonneg {h : LPData F m → ℝ} (hpos : ∀ c, 0 ≤ h c) : 0 ≤ sumAll h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hpos _

theorem sumAll_mono {h h' : LPData F m → ℝ} (hle : ∀ c, h c ≤ h' c) : sumAll h ≤ sumAll h' :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
    Finset.sum_le_sum fun _ _ => hle _

theorem sumRestr_nonneg (hm : m ∣ Fintype.card F) (i : Fin m) {h : LPData F m → ℝ}
    (hpos : ∀ c, 0 ≤ h c) : 0 ≤ sumRestr hm i h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hpos _

theorem avgAll_nonneg {h : LPData F m → ℝ} (hpos : ∀ c, 0 ≤ h c) : 0 ≤ avgAll h :=
  mul_nonneg (by positivity) (sumAll_nonneg hpos)

theorem avgAll_mono {h h' : LPData F m → ℝ} (hle : ∀ c, h c ≤ h' c) : avgAll h ≤ avgAll h' :=
  mul_le_mul_of_nonneg_left (sumAll_mono hle) (by positivity)

theorem avgRestr_nonneg (hm : m ∣ Fintype.card F) (i : Fin m) {h : LPData F m → ℝ}
    (hpos : ∀ c, 0 ≤ h c) : 0 ≤ avgRestr hm i h :=
  mul_nonneg (by positivity) (sumRestr_nonneg hm i hpos)

theorem avgAll_const_mul (k : ℝ) (h : LPData F m → ℝ) :
    avgAll (fun c => k * h c) = k * avgAll h := by
  rw [avgAll, avgAll, sumAll_const_mul]
  ring

/-- **The restricted laws average to the unrestricted one.** -/
theorem sum_avgRestr (hm : m ∣ Fintype.card F) (h : LPData F m → ℝ) :
    ∑ i : Fin m, avgRestr hm i h = (m : ℝ) * avgAll h := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [avgRestr, avgAll]
  rw [← Finset.mul_sum, ← sumAll_eq_sum_sumRestr hm h, cast_card_div hm]
  field_simp
  ring

/-- **A bound on the unrestricted law bounds each restricted one, at `m` times the error.** -/
theorem avgRestr_le_mul_avgAll (hm : m ∣ Fintype.card F) (i : Fin m) {h : LPData F m → ℝ}
    (hpos : ∀ c, 0 ≤ h c) : avgRestr hm i h ≤ (m : ℝ) * avgAll h := by
  rw [← sum_avgRestr hm h]
  exact Finset.single_le_sum (f := fun j : Fin m => avgRestr hm j h)
    (fun j _ => avgRestr_nonneg hm j hpos) (mem_univ i)

/-- **The product form**, at `m^2` times the error: the shape the pasting lemma's hypotheses are in,
each side's line drawn from its own restricted law. -/
theorem avgRestr_prod_le_mul_avgAll (hm : m ∣ Fintype.card F) {g : LPData F m → LPData F m → ℝ}
    (hpos : ∀ cX cZ, 0 ≤ g cX cZ) (i j : Fin m) :
    avgRestr hm i (fun cX => avgRestr hm j (fun cZ => g cX cZ))
      ≤ (m : ℝ) * (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  refine le_trans (avgRestr_le_mul_avgAll hm i
    (fun cX => avgRestr_nonneg hm j (hpos cX))) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (avgAll_mono
    (fun cX => avgRestr_le_mul_avgAll hm j (hpos cX))) (Nat.cast_nonneg m)) ?_
  rw [avgAll_const_mul]
  ring_nf
  exact le_refl _

/-! ### The unrestricted law is the uniform average over the data

`pairs_of_lines_prod` is stated as a uniform average over `LPData F m x LPData F m`; `avgAll` is the
same average written as nested sums. One equiv identifies them. -/

instance : Nonempty (LPData F m) := ⟨⟨0, 0, 0⟩⟩

/-- The data of a line-point pair, as a triple. -/
def lpEquiv (F : Type*) (m : ℕ) : LPData F m ≃ Point F m × F × Point F m where
  toFun c := (c.pt, c.s, c.raw)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sumAll_eq_sum (h : LPData F m → ℝ) : sumAll h = ∑ c : LPData F m, h c := by
  rw [← Equiv.sum_comp (lpEquiv F m).symm h, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun pt _ => by rw [Fintype.sum_prod_type]; rfl

theorem card_lpData : Fintype.card (LPData F m) = Fintype.card F ^ (2 * m + 1) := by
  rw [Fintype.card_congr (lpEquiv F m), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_pi_const]
  ring

/-- **`avgAll` is the uniform average over the data**, which is the form
`pairs_of_lines_prod` is stated in. -/
theorem avgAll_eq_uniform (h : LPData F m → ℝ) :
    avgAll h = ∑ c : LPData F m, (Fintype.card (LPData F m) : ℝ)⁻¹ * h c := by
  rw [avgAll, sumAll_eq_sum, card_lpData, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by push_cast; ring

/-- The product form. -/
theorem avgAll_prod_eq_uniform (g : LPData F m → LPData F m → ℝ) :
    avgAll (fun cX => avgAll (fun cZ => g cX cZ))
      = ∑ p : LPData F m × LPData F m, (Fintype.card (LPData F m × LPData F m) : ℝ)⁻¹
          * g p.1 p.2 := by
  rw [avgAll_eq_uniform, Fintype.sum_prod_type, Fintype.card_prod]
  refine Finset.sum_congr rfl fun cX _ => ?_
  rw [avgAll_eq_uniform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun cZ _ => ?_
  push_cast
  ring

/-- The constant `1` averages to `1`. -/
theorem avgAll_one : avgAll (fun _ : LPData F m => (1 : ℝ)) = 1 := by
  rw [avgAll_eq_uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

theorem avgAll_prod_one :
    avgAll (fun _ : LPData F m => avgAll (fun _ : LPData F m => (1 : ℝ))) = 1 := by
  rw [avgAll_one, avgAll_one]

/-! ### The padded law is dominated by the product law

This is the distributional content of the paper's Claims 17-1 to 17-3, and it is stronger than what
those claims extract. The paper's `\cnote` on the conclusion of `lem:qld-4-13` says the joint law of
the two sublines-with-points is **not** a product, because "for diagonal lines both coordinates share
the line parameter", and the three claims are written to use only the marginals. That is right about
conditioning on the *padded* line: given it, the two blocks of a uniform point on it move with one
parameter. But the quantity to be bounded conditions only on the two *sublines*, which know each
block's coset in its own space and not the relative offset --- and `avgSub_free` and its three
companions say that at a fixed padded seed the joint law is exactly a product of the two marginals,
each of them restricted or not according to `padCase`. Combining that with the restricted-law
transfer bounds the padded law by `m^2` times the product of the two unrestricted laws, uniformly in
the padded seed and the line type. -/

theorem avgAll_prod_nonneg {g : LPData F m → LPData F m → ℝ} (hpos : ∀ cX cZ, 0 ≤ g cX cZ) :
    0 ≤ avgAll (fun cX => avgAll (fun cZ => g cX cZ)) :=
  avgAll_nonneg fun cX => avgAll_nonneg (hpos cX)

/-- The `Z` side restricted, the `X` side free. -/
theorem avgAll_avgRestr_le (hm : m ∣ Fintype.card F) {g : LPData F m → LPData F m → ℝ}
    (hpos : ∀ cX cZ, 0 ≤ g cX cZ) (j : Fin m) :
    avgAll (fun cX => avgRestr hm j (fun cZ => g cX cZ))
      ≤ (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  refine le_trans (avgAll_mono fun cX => avgRestr_le_mul_avgAll hm j (hpos cX)) ?_
  rw [avgAll_const_mul]

/-- The `X` side restricted, the `Z` side free. -/
theorem avgRestr_avgAll_le (hm : m ∣ Fintype.card F) {g : LPData F m → LPData F m → ℝ}
    (hpos : ∀ cX cZ, 0 ≤ g cX cZ) (i : Fin m) :
    avgRestr hm i (fun cX => avgAll (fun cZ => g cX cZ))
      ≤ (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) :=
  avgRestr_le_mul_avgAll hm i fun cX => avgAll_nonneg (hpos cX)

/-- **The padded line-point law is at most `m^2` times the product of the two unrestricted subline
laws**, whatever the padded seed and the line type. -/
theorem avgSub_le_mul_avgAll (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (s : F) {g : LPData F m → LPData F m → ℝ} (hpos : ∀ cX cZ, 0 ≤ g cX cZ) :
    avgSub hm4 hm t s g
      ≤ (m : ℝ) * (m : ℝ) * avgAll (fun cX => avgAll (fun cZ => g cX cZ)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hprod := avgAll_prod_nonneg hpos
  have hmm : (m : ℝ) ≤ (m : ℝ) * (m : ℝ) := by nlinarith [hm1]
  have h1mm : (1 : ℝ) ≤ (m : ℝ) * (m : ℝ) := le_trans hm1 hmm
  rcases h : padCase (chi hm4 s) with i | i | _ | _
  · -- the `X` block: the `X` side is restricted, and on a diagonal line so is the `Z` side
    cases t with
    | dline =>
        rw [avgSub_xc_dline hm4 hm h g]
        exact avgRestr_prod_le_mul_avgAll hm hpos i 0
    | point =>
        rw [avgSub_xc hm4 hm h (by simp) g]
        exact le_trans (avgRestr_avgAll_le hm hpos i) (mul_le_mul_of_nonneg_right hmm hprod)
    | aline =>
        rw [avgSub_xc hm4 hm h (by simp) g]
        exact le_trans (avgRestr_avgAll_le hm hpos i) (mul_le_mul_of_nonneg_right hmm hprod)
  · -- the `Z` block: only the `Z` side is restricted
    rw [avgSub_zc hm4 hm t h g]
    exact le_trans (avgAll_avgRestr_le hm hpos i) (mul_le_mul_of_nonneg_right hmm hprod)
  all_goals
    -- `alpha`, `beta` or a dummy coordinate: neither side is restricted
    rw [avgSub_free hm4 hm t (by simp [h]) g]
    exact le_mul_of_one_le_left hprod h1mm

end Average

/-! ## The `alpha` and `beta` coordinates of the padded point

The measurement of `lem:qld-padded-lines` reads `alpha` and `beta` at the sampled padded point, which
`avgSub` does not carry. They are coordinates of the padded point outside the `X` and `Z` blocks, so
translating the point in those two coordinates alone leaves both sublines untouched --- which makes
the `(alpha, beta)` average *uniform and independent of everything else*, and a bound that holds for
every fixed `(alpha, beta)` therefore holds for the joint law. No refinement of the block
decomposition is needed. -/

section AlphaBeta

variable [NeZero m]

/-- Translating the padded point in its `alpha` and `beta` coordinates only. -/
def shiftAB (c d : F) (u : Point F (4 * m)) : Point F (4 * m) :=
  u + (Pi.single (aIdx m) c + Pi.single (bIdx m) d)

@[simp] theorem xBlk_shiftAB (c d : F) (u : Point F (4 * m)) :
    xBlk (shiftAB c d u) = xBlk u := by
  funext i
  simp [shiftAB, xBlk, Pi.single_eq_of_ne (xIdx_ne_aIdx i), Pi.single_eq_of_ne (xIdx_ne_bIdx i)]

@[simp] theorem zBlk_shiftAB (c d : F) (u : Point F (4 * m)) :
    zBlk (shiftAB c d u) = zBlk u := by
  funext i
  simp [shiftAB, zBlk, Pi.single_eq_of_ne (zIdx_ne_aIdx i), Pi.single_eq_of_ne (zIdx_ne_bIdx i)]

@[simp] theorem alph_shiftAB (c d : F) (u : Point F (4 * m)) :
    alph (shiftAB c d u) = alph u + c := by
  simp only [shiftAB, alph, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne aIdx_ne_bIdx, add_zero]

@[simp] theorem bet_shiftAB (c d : F) (u : Point F (4 * m)) :
    bet (shiftAB c d u) = bet u + d := by
  simp only [shiftAB, bet, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm aIdx_ne_bIdx), zero_add]

theorem shiftAB_shiftAB (c d c' d' : F) (u : Point F (4 * m)) :
    shiftAB c' d' (shiftAB c d u) = shiftAB (c + c') (d + d') u := by
  simp only [shiftAB, Pi.single_add]
  abel

@[simp] theorem shiftAB_zero (u : Point F (4 * m)) : shiftAB (0 : F) 0 u = u := by
  simp only [shiftAB, Pi.single_zero, add_zero]

theorem bijective_shiftAB (c d : F) : Function.Bijective (shiftAB (F := F) (m := m) c d) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shiftAB (-c) (-d),
      fun u => by rw [shiftAB_shiftAB]; simp,
      fun u => by rw [shiftAB_shiftAB]; simp⟩

theorem subX_shiftAB (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (c d s : F)
    (pt raw : Point F (4 * m)) (e : F × Point F m) :
    subX hm4 hm ⟨shiftAB c d pt, s, raw⟩ e = subX hm4 hm ⟨pt, s, raw⟩ e := by
  simp only [subX]
  rcases h : padCase (chi hm4 s) with i | i | _ | _ <;>
    simp only [subXof_xc, subXof_zc, subXof_ab, subXof_dum, xBlk_shiftAB]

theorem subZ_shiftAB (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (c d s : F) (pt raw : Point F (4 * m)) (e : F × Point F m) :
    subZ hm4 hm t ⟨shiftAB c d pt, s, raw⟩ e = subZ hm4 hm t ⟨pt, s, raw⟩ e := by
  simp only [subZ]
  rcases h : padCase (chi hm4 s) with i | i | _ | _ <;> cases t <;>
    simp only [subZof_dline_xc, subZof_point_xc, subZof_aline_xc, subZof_zc, subZof_ab,
      subZof_dum, zBlk_shiftAB]

/-- The inner average of the subline sampling space, at a fixed padded point. -/
def sumSubAt (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (pt : Point F (4 * m)) (h : LPData F m → LPData F m → ℝ) : ℝ :=
  ∑ raw : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
    h (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm t ⟨pt, s, raw⟩ eZ)

theorem sumSub_eq_sum_sumSubAt (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (t : CL.Ty) (s : F) (h : LPData F m → LPData F m → ℝ) :
    sumSub hm4 hm t s h = ∑ pt : Point F (4 * m), sumSubAt hm4 hm t s pt h := rfl

theorem sumSubAt_shiftAB (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (s : F) (c d : F) (pt : Point F (4 * m)) (h : LPData F m → LPData F m → ℝ) :
    sumSubAt hm4 hm t s (shiftAB c d pt) h = sumSubAt hm4 hm t s pt h := by
  refine Finset.sum_congr rfl fun raw _ => Finset.sum_congr rfl fun eX _ =>
    Finset.sum_congr rfl fun eZ _ => ?_
  rw [subX_shiftAB, subZ_shiftAB]

/-- The padded average with `alpha` and `beta` carried. -/
def sumSubAB (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g : F → F → LPData F m → LPData F m → ℝ) : ℝ :=
  ∑ pt : Point F (4 * m), sumSubAt hm4 hm t s pt (g (alph pt) (bet pt))

/-- The normalized version. -/
def avgSubAB (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g : F → F → LPData F m → LPData F m → ℝ) : ℝ :=
  ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * sumSubAB hm4 hm t s g

/-- **`(alpha, beta)` is uniform and independent of the two sublines**, because translating the
padded point in those two coordinates alone is a bijection that leaves both sublines fixed. -/
theorem sumSubAB_eq (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g : F → F → LPData F m → LPData F m → ℝ) :
    (Fintype.card (F × F) : ℝ) * sumSubAB hm4 hm t s g
      = ∑ p : F × F, sumSub hm4 hm t s (g p.1 p.2) := by
  classical
  have hshift : ∀ p : F × F,
      ∑ pt : Point F (4 * m), sumSubAt hm4 hm t s pt (g (alph pt + p.1) (bet pt + p.2))
        = sumSubAB hm4 hm t s g := by
    intro p
    refine Fintype.sum_bijective (shiftAB (F := F) (m := m) p.1 p.2)
      (bijective_shiftAB p.1 p.2) _ _ fun pt => ?_
    rw [sumSubAt_shiftAB, alph_shiftAB, bet_shiftAB]
  have e3 : ∀ pt : Point F (4 * m),
      ∑ p : F × F, sumSubAt hm4 hm t s pt (g (alph pt + p.1) (bet pt + p.2))
        = ∑ p : F × F, sumSubAt hm4 hm t s pt (g p.1 p.2) := fun pt =>
    Equiv.sum_comp ((Equiv.addLeft (alph pt)).prodCongr (Equiv.addLeft (bet pt)))
      (fun p : F × F => sumSubAt hm4 hm t s pt (g p.1 p.2))
  calc (Fintype.card (F × F) : ℝ) * sumSubAB hm4 hm t s g
      = ∑ _p : F × F, sumSubAB hm4 hm t s g := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ p : F × F, ∑ pt : Point F (4 * m),
          sumSubAt hm4 hm t s pt (g (alph pt + p.1) (bet pt + p.2)) :=
        Finset.sum_congr rfl fun p _ => (hshift p).symm
    _ = ∑ pt : Point F (4 * m), ∑ p : F × F,
          sumSubAt hm4 hm t s pt (g (alph pt + p.1) (bet pt + p.2)) := Finset.sum_comm
    _ = ∑ pt : Point F (4 * m), ∑ p : F × F, sumSubAt hm4 hm t s pt (g p.1 p.2) :=
        Finset.sum_congr rfl fun pt _ => e3 pt
    _ = ∑ p : F × F, ∑ pt : Point F (4 * m), sumSubAt hm4 hm t s pt (g p.1 p.2) :=
        Finset.sum_comm
    _ = ∑ p : F × F, sumSub hm4 hm t s (g p.1 p.2) :=
        Finset.sum_congr rfl fun p _ => (sumSub_eq_sum_sumSubAt hm4 hm t s (g p.1 p.2)).symm

/-- **A bound that holds for every fixed `(alpha, beta)` holds for the padded law.** -/
theorem avgSubAB_le_of_forall (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (t : CL.Ty) (s : F) {g : F → F → LPData F m → LPData F m → ℝ} {delta : ℝ}
    (h : ∀ a b : F, avgSub hm4 hm t s (g a b) ≤ delta) :
    avgSubAB hm4 hm t s g ≤ delta := by
  have hcard : (0 : ℝ) < (Fintype.card (F × F) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hkey : (Fintype.card (F × F) : ℝ) * avgSubAB hm4 hm t s g
      = ∑ p : F × F, avgSub hm4 hm t s (g p.1 p.2) := by
    rw [avgSubAB, ← mul_assoc, mul_comm (Fintype.card (F × F) : ℝ), mul_assoc,
      sumSubAB_eq hm4 hm t s g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => rfl
  refine le_of_mul_le_mul_left ?_ hcard
  rw [hkey]
  refine le_trans (Finset.sum_le_sum fun p _ => h p.1 p.2) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end AlphaBeta

end MIPRE.QLD
