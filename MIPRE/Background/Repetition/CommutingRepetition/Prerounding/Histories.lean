/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Histories.lean
-/
/-
# Reverse reveal experiments (node 1.2.8, classical half)

The size-biased reverse experiments of the resolver-martingale
subsection (05_prerounding.tex, "Resolver martingales and state
alignment": eqs size-biased-partition, alice-reverse-background,
bob-size-biased-partition, bob-reverse-background, and the
law-equality computation around eq forward-outcome-probability).

In the Alice-reveal reverse experiment the referee first samples the
two-block partition `M₀ = L_X ⊔ L_Y⁺` with the size-biased law
`2^{−m}·(2N_A/m)` (`N_A = |L_Y⁺|`), a uniform order `π_Y` of `L_Y⁺`, a
uniform cut `k_Y ∈ {0,…,N_A−1}`, and the independent forward variables
`π_{X,−i}, k_X`; the live coordinate is read off as `i = π_Y[k_Y+1]`.
The manuscript's verification "Both reverse experiments have exactly
the forward law" is, in this encoding, a *pointwise* statement: the
datum map to the forward experiment (delete the live coordinate from
`π_Y`) is a bijection matching the laws term by term —
`2^{1−m}·N_A/(m·N_A·N_A!·|L_X|!·(|L_X|+1))
  = 2^{1−m}/(m·|L_X|!·(|L_X|+1)·(N_A−1)!·N_A)`,
which is eq forward-outcome-probability.

Encoding notes (for the fidelity review):
- The cut `k_Y : Fin LYp.card` makes the empty Bob-block literally
  unrepresentable ("The empty block has probability zero"): at
  `N_A = 0` the type has no inhabitants, so no zero-weight bookkeeping
  is needed.
- The live coordinate is DERIVED (`liveIdx = π_Y[k_Y+1]`), not a field;
  the reverse datum determines the forward one uniquely and vice versa.
- Only the datum layer and the law equality are stated here (the
  classical half of node 1.2.8). The reveal martingales `F_{j,z}` and
  their operator identities (eqs alice-reveal-martingale through
  bob-live-increment) consume this layer together with the branch
  effects of node 1.2.4 and are stated with the alignment layer.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.Reveal

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

set_option synthInstance.maxSize 1024 in
/-- The Alice-reveal reverse datum (05_prerounding.tex, eq
size-biased-partition and following): a two-block partition
`M₀ = L_X ⊔ L_Y⁺` of the non-core coordinates, a full order of the Bob
block `L_Y⁺`, a cut strictly inside it (whose entry is the live
coordinate), and the independent forward Alice-side order and cut. -/
structure AliceRevealDatum (n : ℕ) (D : Finset (Fin n)) where
  LX : Finset (Fin n)
  LYp : Finset (Fin n)
  disjoint : Disjoint LX LYp
  partition : LX ∪ LYp = Dᶜ
  πX : Fin LX.card ≃ {j : Fin n // j ∈ LX}
  πY : Fin LYp.card ≃ {j : Fin n // j ∈ LYp}
  kX : Fin (LX.card + 1)
  kY : Fin LYp.card
  deriving Fintype

set_option synthInstance.maxSize 1024 in
/-- The Bob-reveal reverse datum (05_prerounding.tex, eq
bob-size-biased-partition): the mirror image, with the Alice block
carrying the full order and the interior cut. -/
structure BobRevealDatum (n : ℕ) (D : Finset (Fin n)) where
  LXp : Finset (Fin n)
  LY : Finset (Fin n)
  disjoint : Disjoint LXp LY
  partition : LXp ∪ LY = Dᶜ
  πX : Fin LXp.card ≃ {j : Fin n // j ∈ LXp}
  πY : Fin LY.card ≃ {j : Fin n // j ∈ LY}
  kX : Fin LXp.card
  kY : Fin (LY.card + 1)
  deriving Fintype

namespace AliceRevealDatum

variable {n : ℕ} {D : Finset (Fin n)} (d : AliceRevealDatum n D)

/-- The live coordinate `i = π_Y[k_Y + 1]` (1-indexed manuscript entry =
0-indexed position `k_Y`). -/
def liveIdx : Fin n := (d.πY d.kY).1

theorem liveIdx_mem : d.liveIdx ∈ d.LYp := (d.πY d.kY).2

theorem liveIdx_notMem_core : d.liveIdx ∉ D := by
  have h1 : d.liveIdx ∈ Dᶜ := by
    rw [← d.partition]
    exact Finset.mem_union_right _ d.liveIdx_mem
  exact Finset.mem_compl.mp h1

/-- The size-biased reverse law (eq size-biased-partition with the
uniform order, interior cut, and independent forward variables):
`2^{−m}·(2N_A/m) · (1/N_A!) · (1/N_A) · (1/|L_X|!) · (1/(|L_X|+1))`,
`m = n − |D|`, `N_A = |L_Y⁺|`. -/
noncomputable def law (d : AliceRevealDatum n D) : ℝ :=
  (1 / 2 ^ (n - D.card)) * (2 * d.LYp.card / (n - D.card : ℕ)) *
    (1 / (Nat.factorial d.LYp.card)) * (1 / d.LYp.card) *
    (1 / (Nat.factorial d.LX.card)) * (1 / (d.LX.card + 1))

theorem law_nonneg : 0 ≤ d.law := by
  unfold law
  positivity

end AliceRevealDatum

namespace BobRevealDatum

variable {n : ℕ} {D : Finset (Fin n)} (d : BobRevealDatum n D)

/-- The live coordinate `i = π_X[k_X + 1]`. -/
def liveIdx : Fin n := (d.πX d.kX).1

theorem liveIdx_mem : d.liveIdx ∈ d.LXp := (d.πX d.kX).2

/-- The size-biased reverse law for the Bob-reveal experiment (eq
bob-size-biased-partition). -/
noncomputable def law (d : BobRevealDatum n D) : ℝ :=
  (1 / 2 ^ (n - D.card)) * (2 * d.LXp.card / (n - D.card : ℕ)) *
    (1 / (Nat.factorial d.LXp.card)) * (1 / d.LXp.card) *
    (1 / (Nat.factorial d.LY.card)) * (1 / (d.LY.card + 1))

theorem law_nonneg : 0 ≤ d.law := by
  unfold law
  positivity

end BobRevealDatum

/-! ### Shared surgery helpers for the pushforward bijections -/

private theorem pushHEqFin : ∀ {m m' : ℕ}, m = m' →
    ∀ (a : Fin m) (b : Fin m'), (a : ℕ) = (b : ℕ) → HEq a b := by
  rintro m m' rfl a b h
  exact heq_of_eq (Fin.ext h)

private theorem pushHEqEquiv : ∀ {n : ℕ} {S S' : Finset (Fin n)}, S = S' →
    ∀ (E : Fin S.card ≃ {j : Fin n // j ∈ S})
      (E' : Fin S'.card ≃ {j : Fin n // j ∈ S'}),
    (∀ (t : Fin S.card) (t' : Fin S'.card), (t : ℕ) = (t' : ℕ) →
      ((E t : Fin n)) = ((E' t' : Fin n))) → HEq E E' := by
  rintro n S S' rfl E E' h
  exact heq_of_eq (Equiv.ext fun t => Subtype.ext (h t t rfl))

private theorem pushAliceExt : ∀ {n : ℕ} {D : Finset (Fin n)}
    (a b : AliceRevealDatum n D), a.LX = b.LX → a.LYp = b.LYp →
    HEq a.πX b.πX → HEq a.πY b.πY → HEq a.kX b.kX → HEq a.kY b.kY →
    a = b := by
  rintro n D ⟨aLX, aLYp, _, _, aπX, aπY, akX, akY⟩
    ⟨bLX, bLYp, _, _, bπX, bπY, bkX, bkY⟩ h1 h2 h3 h4 h5 h6
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1; subst h2
  rw [heq_iff_eq] at h3 h4 h5 h6
  subst h3; subst h4; subst h5; subst h6
  rfl

private theorem pushBobExt : ∀ {n : ℕ} {D : Finset (Fin n)}
    (a b : BobRevealDatum n D), a.LXp = b.LXp → a.LY = b.LY →
    HEq a.πX b.πX → HEq a.πY b.πY → HEq a.kX b.kX → HEq a.kY b.kY →
    a = b := by
  rintro n D ⟨aLXp, aLY, _, _, aπX, aπY, akX, akY⟩
    ⟨bLXp, bLY, _, _, bπX, bπY, bkX, bkY⟩ h1 h2 h3 h4 h5 h6
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1; subst h2
  rw [heq_iff_eq] at h3 h4 h5 h6
  subst h3; subst h4; subst h5; subst h6
  rfl

private theorem pushRevealExt : ∀ {n : ℕ} {D : Finset (Fin n)}
    (a b : RevealDatum n D), a.i = b.i → a.LX = b.LX →
    a.LY = b.LY → HEq a.πX b.πX → HEq a.πY b.πY → HEq a.kX b.kX →
    HEq a.kY b.kY → a = b := by
  rintro n D ⟨ai, _, aLX, aLY, _, _, aπX, aπY, akX, akY⟩
    ⟨bi, _, bLX, bLY, _, _, bπX, bπY, bkX, bkY⟩ h0 h1 h2 h3 h4 h5 h6
  dsimp only at h0 h1 h2 h3 h4 h5 h6
  subst h0; subst h1; subst h2
  rw [heq_iff_eq] at h3 h4 h5 h6
  subst h3; subst h4; subst h5; subst h6
  rfl

private theorem pushInsEval : ∀ {n : ℕ} (S' : Finset (Fin n)) (i' : Fin n)
    (h' : i' ∉ S') (π' : Fin S'.card ≃ {j : Fin n // j ∈ S'})
    (k' : Fin (S'.card + 1)) (hcc : (insert i' S').card = S'.card + 1)
    (z : Fin (insert i' S').card)
    (j : Fin S'.card), Fin.cast hcc z = k'.succAbove j →
    ((((finCongr hcc).trans ((finSuccEquiv' k').trans
      ((Equiv.optionCongr π').trans
        (Finset.subtypeInsertEquivOption h').symm))) z :
          {j : Fin n // j ∈ insert i' S'}) : Fin n)
      = ↑(π' j) := by
  intro n S' i' h' π' k' hcc z j hz
  simp only [Equiv.trans_apply, finCongr_apply, hz, finSuccEquiv'_succAbove,
    Equiv.optionCongr_apply, Option.map_some]
  rfl

private theorem pushInsEvalCut : ∀ {n : ℕ} (S' : Finset (Fin n)) (i' : Fin n)
    (h' : i' ∉ S') (π' : Fin S'.card ≃ {j : Fin n // j ∈ S'})
    (k' : Fin (S'.card + 1)) (hcc : (insert i' S').card = S'.card + 1)
    (z : Fin (insert i' S').card),
    Fin.cast hcc z = k' →
    ((((finCongr hcc).trans ((finSuccEquiv' k').trans
      ((Equiv.optionCongr π').trans
        (Finset.subtypeInsertEquivOption h').symm))) z :
          {j : Fin n // j ∈ insert i' S'}) : Fin n)
      = i' := by
  intro n S' i' h' π' k' hcc z hz
  simp only [Equiv.trans_apply, finCongr_apply, hz, finSuccEquiv'_at,
    Equiv.optionCongr_apply, Option.map_none]
  rfl

private theorem pushDelEval : ∀ {n : ℕ} (S : Finset (Fin n)) (u : Fin n)
    (π : Fin S.card ≃ {j : Fin n // j ∈ S})
    (hb : (S.erase u).card = S.card - 1) (hN : S.card - 1 + 1 = S.card)
    (P : Fin (S.card - 1 + 1))
    (hIff : ∀ a, a ≠ P ↔ ↑(((finCongr hN).trans π) a) ≠ u)
    (hg : ∀ j : Fin n, (j ∈ S ∧ j ≠ u) ↔ j ∈ S.erase u)
    (t : Fin ((S.erase u).card)),
    ((((finCongr hb).trans ((finSuccAboveEquiv P).trans
        ((Equiv.subtypeEquiv ((finCongr hN).trans π) hIff).trans
          ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S) (· ≠ u)).trans
            (Equiv.subtypeEquivRight hg))))) t :
              {j : Fin n // j ∈ S.erase u}) : Fin n)
      = ↑(π (Fin.cast hN (P.succAbove (Fin.cast hb t)))) := by
  intro n S u π hb hN P hIff hg t
  simp only [Equiv.trans_apply, finCongr_apply, finSuccAboveEquiv_apply,
    Equiv.subtypeEquiv_apply, Equiv.subtypeEquivRight_apply]
  rfl

private theorem pushSuccAboveVal : ∀ {m₁ m₂ : ℕ} (p₁ : Fin (m₁+1))
    (p₂ : Fin (m₂+1)) (j₁ : Fin m₁) (j₂ : Fin m₂),
    (p₁ : ℕ) = (p₂ : ℕ) → (j₁ : ℕ) = (j₂ : ℕ) →
    ((p₁.succAbove j₁ : Fin (m₁+1)) : ℕ)
      = ((p₂.succAbove j₂ : Fin (m₂+1)) : ℕ) := by
  intro m₁ m₂ p₁ p₂ j₁ j₂ hp hj
  unfold Fin.succAbove
  split_ifs with h1 h2 <;>
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega

/-! ### The pushforward maps, as named data -/

namespace AliceRevealDatum

variable {n : ℕ} {D : Finset (Fin n)} (d : AliceRevealDatum n D)

/-- The forward map of the Alice-reveal pushforward: read off the live
coordinate `i = π_Y[k_Y+1]` and delete it from the Bob-block order. -/
@[reducible] def toReveal : RevealDatum n D where
  i := (d.πY d.kY).1
  i_notMem := d.liveIdx_notMem_core
  LX := d.LX
  LY := d.LYp.erase (d.πY d.kY).1
  disjoint := Finset.disjoint_of_subset_right
    (Finset.erase_subset _ _) d.disjoint
  partition := by
    have hiLX : (d.πY d.kY).1 ∉ d.LX := fun h =>
      (Finset.disjoint_left.mp d.disjoint h) (d.πY d.kY).2
    rw [Finset.compl_insert, ← d.partition, Finset.erase_union_distrib,
      Finset.erase_eq_of_notMem hiLX]
  πX := d.πX
  πY := by
    refine (finCongr (Finset.card_erase_of_mem (d.πY d.kY).2)).trans
      ((finSuccAboveEquiv
          (Fin.cast (by have := d.kY.pos; omega) d.kY)).trans
        ((Equiv.subtypeEquiv
            ((finCongr (by have := d.kY.pos; omega)).trans d.πY)
            (fun a => ?_)).trans
          ((Equiv.subtypeSubtypeEquivSubtypeInter
              (· ∈ d.LYp) (· ≠ (d.πY d.kY).1)).trans
            (Equiv.subtypeEquivRight (fun j => ?_)))))
    · constructor
      · intro h1 h2
        refine h1 ?_
        have h3 := d.πY.injective (Subtype.ext h2)
        have h4 : (a : ℕ) = (d.kY : ℕ) := by
          simpa using congrArg Fin.val h3
        exact Fin.ext (by simpa using h4)
      · intro h1 h2
        refine h1 ?_
        rw [h2, Equiv.trans_apply]
        exact congrArg (fun u : {j : Fin n // j ∈ d.LYp} => (u : Fin n))
          (congrArg (fun t => d.πY t) (Fin.ext (by simp)))
    · rw [Finset.mem_erase]
      exact and_comm
  kX := d.kX
  kY := ⟨(d.kY : ℕ), by
    rw [Finset.card_erase_of_mem (d.πY d.kY).2]
    have h1 := d.kY.isLt
    have h2 := d.kY.pos
    omega⟩

theorem toReveal_i : d.toReveal.i = d.liveIdx := rfl

theorem toReveal_LX : d.toReveal.LX = d.LX := rfl

theorem toReveal_LY : d.toReveal.LY = d.LYp.erase d.liveIdx := rfl

theorem toReveal_kX : (d.toReveal.kX : ℕ) = (d.kX : ℕ) := rfl

theorem toReveal_kY : (d.toReveal.kY : ℕ) = (d.kY : ℕ) := rfl

/-- The forward map matches the laws pointwise (eq
forward-outcome-probability). -/
theorem law_toReveal : d.law = d.toReveal.revealLaw := by
  have hDlt : D.card < n := by
    have h1 : (0:ℕ) < Dᶜ.card := Finset.card_pos.mpr
      ⟨d.liveIdx, Finset.mem_compl.mpr d.liveIdx_notMem_core⟩
    rw [Finset.card_compl, Fintype.card_fin] at h1
    omega
  have hN0 : 0 < d.LYp.card := d.kY.pos
  unfold AliceRevealDatum.law RevealDatum.revealLaw
  rw [toReveal_LX, toReveal_LY, Finset.card_erase_of_mem d.liveIdx_mem]
  obtain ⟨m', hm'⟩ : ∃ m', n - D.card = m' + 1 :=
    ⟨n - D.card - 1, by omega⟩
  obtain ⟨N', hN'⟩ : ∃ N', d.LYp.card = N' + 1 :=
    ⟨d.LYp.card - 1, by omega⟩
  rw [hm', hN']
  simp only [Nat.add_sub_cancel]
  rw [Nat.factorial_succ, pow_succ]
  have hfN : ((Nat.factorial N' : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hfX : ((Nat.factorial d.LX.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hE : ((2 : ℝ) ^ m') ≠ 0 := by positivity
  have hN1 : ((N' : ℝ) + 1) ≠ 0 := by positivity
  have hX1 : ((d.LX.card : ℝ) + 1) ≠ 0 := by positivity
  have hM1 : ((m' : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  generalize (Nat.factorial N' : ℝ) = A at hfN ⊢
  generalize (Nat.factorial d.LX.card : ℝ) = B at hfX ⊢
  generalize ((2 : ℝ) ^ m') = E at hE ⊢
  generalize ((N' : ℝ)) = NN at hN1 ⊢
  generalize ((d.LX.card : ℝ)) = C at hX1 ⊢
  generalize ((m' : ℝ)) = M at hM1 ⊢
  field_simp
  try ring

/-- Below the cut, the surgered Bob-block order agrees with the original
order: deleting the live coordinate at the cut fixes the strict
prefix. -/
theorem toReveal_πY_of_lt (t : Fin d.toReveal.LY.card)
    (s : Fin d.LYp.card) (hval : (t : ℕ) = (s : ℕ))
    (hlt : (s : ℕ) < (d.kY : ℕ)) :
    ((d.toReveal.πY t : Fin n)) = ↑(d.πY s) := by
  refine (pushDelEval _ _ _ _ _ _ _ _ t).trans ?_
  refine congrArg
    (fun z => ((d.πY z : {j : Fin n // j ∈ d.LYp}) : Fin n)) (Fin.ext ?_)
  unfold Fin.succAbove
  split_ifs with h
  · exact hval
  · exact absurd (hval.trans_lt hlt) h

end AliceRevealDatum

namespace BobRevealDatum

variable {n : ℕ} {D : Finset (Fin n)} (d : BobRevealDatum n D)

/-- The forward map of the Bob-reveal pushforward (mirror): read off the
live coordinate `i = π_X[k_X+1]` and delete it from the Alice-block
order. -/
@[reducible] def toReveal : RevealDatum n D where
  i := (d.πX d.kX).1
  i_notMem := by
    have h1 : (d.πX d.kX).1 ∈ Dᶜ := by
      rw [← d.partition]
      exact Finset.mem_union_left _ (d.πX d.kX).2
    exact Finset.mem_compl.mp h1
  LX := d.LXp.erase (d.πX d.kX).1
  LY := d.LY
  disjoint := Finset.disjoint_of_subset_left
    (Finset.erase_subset _ _) d.disjoint
  partition := by
    have hiLY : (d.πX d.kX).1 ∉ d.LY :=
      Finset.disjoint_left.mp d.disjoint (d.πX d.kX).2
    rw [Finset.compl_insert, ← d.partition, Finset.erase_union_distrib,
      Finset.erase_eq_of_notMem hiLY]
  πX := by
    refine (finCongr (Finset.card_erase_of_mem (d.πX d.kX).2)).trans
      ((finSuccAboveEquiv
          (Fin.cast (by have := d.kX.pos; omega) d.kX)).trans
        ((Equiv.subtypeEquiv
            ((finCongr (by have := d.kX.pos; omega)).trans d.πX)
            (fun a => ?_)).trans
          ((Equiv.subtypeSubtypeEquivSubtypeInter
              (· ∈ d.LXp) (· ≠ (d.πX d.kX).1)).trans
            (Equiv.subtypeEquivRight (fun j => ?_)))))
    · constructor
      · intro h1 h2
        refine h1 ?_
        have h3 := d.πX.injective (Subtype.ext h2)
        have h4 : (a : ℕ) = (d.kX : ℕ) := by
          simpa using congrArg Fin.val h3
        exact Fin.ext (by simpa using h4)
      · intro h1 h2
        refine h1 ?_
        rw [h2, Equiv.trans_apply]
        exact congrArg (fun u : {j : Fin n // j ∈ d.LXp} => (u : Fin n))
          (congrArg (fun t => d.πX t) (Fin.ext (by simp)))
    · rw [Finset.mem_erase]
      exact and_comm
  πY := d.πY
  kX := ⟨(d.kX : ℕ), by
    rw [Finset.card_erase_of_mem (d.πX d.kX).2]
    have h1 := d.kX.isLt
    have h2 := d.kX.pos
    omega⟩
  kY := d.kY

theorem toReveal_i : d.toReveal.i = d.liveIdx := rfl

theorem toReveal_LXp : d.toReveal.LX = d.LXp.erase d.liveIdx := rfl

theorem toReveal_LY : d.toReveal.LY = d.LY := rfl

theorem toReveal_kX : (d.toReveal.kX : ℕ) = (d.kX : ℕ) := rfl

theorem toReveal_kY : (d.toReveal.kY : ℕ) = (d.kY : ℕ) := rfl

/-- The forward map matches the laws pointwise (mirror). -/
theorem law_toReveal : d.law = d.toReveal.revealLaw := by
  have hDlt : D.card < n := by
    have h0 : (d.πX d.kX).1 ∈ Dᶜ := by
      rw [← d.partition]
      exact Finset.mem_union_left _ (d.πX d.kX).2
    have h1 : (0:ℕ) < Dᶜ.card := Finset.card_pos.mpr ⟨_, h0⟩
    rw [Finset.card_compl, Fintype.card_fin] at h1
    omega
  have hN0 : 0 < d.LXp.card := d.kX.pos
  unfold BobRevealDatum.law RevealDatum.revealLaw
  rw [toReveal_LXp, toReveal_LY, Finset.card_erase_of_mem d.liveIdx_mem]
  obtain ⟨m', hm'⟩ : ∃ m', n - D.card = m' + 1 :=
    ⟨n - D.card - 1, by omega⟩
  obtain ⟨N', hN'⟩ : ∃ N', d.LXp.card = N' + 1 :=
    ⟨d.LXp.card - 1, by omega⟩
  rw [hm', hN']
  simp only [Nat.add_sub_cancel]
  rw [Nat.factorial_succ, pow_succ]
  have hfN : ((Nat.factorial N' : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hfY : ((Nat.factorial d.LY.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hE : ((2 : ℝ) ^ m') ≠ 0 := by positivity
  have hN1 : ((N' : ℝ) + 1) ≠ 0 := by positivity
  have hY1 : ((d.LY.card : ℝ) + 1) ≠ 0 := by positivity
  have hM1 : ((m' : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  generalize (Nat.factorial N' : ℝ) = A at hfN ⊢
  generalize (Nat.factorial d.LY.card : ℝ) = B at hfY ⊢
  generalize ((2 : ℝ) ^ m') = E at hE ⊢
  generalize ((N' : ℝ)) = NN at hN1 ⊢
  generalize ((d.LY.card : ℝ)) = C at hY1 ⊢
  generalize ((m' : ℝ)) = M at hM1 ⊢
  field_simp
  try ring

/-- Below the cut, the surgered Alice-block order agrees with the
original order (mirror). -/
theorem toReveal_πX_of_lt (t : Fin d.toReveal.LX.card)
    (s : Fin d.LXp.card) (hval : (t : ℕ) = (s : ℕ))
    (hlt : (s : ℕ) < (d.kX : ℕ)) :
    ((d.toReveal.πX t : Fin n)) = ↑(d.πX s) := by
  refine (pushDelEval _ _ _ _ _ _ _ _ t).trans ?_
  refine congrArg
    (fun z => ((d.πX z : {j : Fin n // j ∈ d.LXp}) : Fin n)) (Fin.ext ?_)
  unfold Fin.succAbove
  split_ifs with h
  · exact hval
  · exact absurd (hval.trans_lt hlt) h

end BobRevealDatum

namespace RevealDatum

variable {n : ℕ} {D : Finset (Fin n)} (d₀ : RevealDatum n D)

/-- The reverse map of the Alice-reveal pushforward: re-insert the live
coordinate into the Bob-block order at the cut. -/
@[reducible] def toAliceReveal : AliceRevealDatum n D :=
  have hnot : d₀.i ∉ d₀.LY := fun h =>
    (Finset.mem_compl.mp (d₀.LY_subset h)) (Finset.mem_insert_self _ _)
  { LX := d₀.LX
    LYp := insert d₀.i d₀.LY
    disjoint := by
      rw [Finset.disjoint_insert_right]
      exact ⟨fun h => (Finset.mem_compl.mp (d₀.LX_subset h))
        (Finset.mem_insert_self _ _), d₀.disjoint⟩
    partition := by
      rw [Finset.union_insert, d₀.partition, Finset.compl_insert,
        Finset.insert_erase (Finset.mem_compl.mpr d₀.i_notMem)]
    πX := d₀.πX
    πY := (finCongr (Finset.card_insert_of_notMem hnot)).trans
      ((finSuccEquiv' d₀.kY).trans
        ((Equiv.optionCongr d₀.πY).trans
          (Finset.subtypeInsertEquivOption hnot).symm))
    kX := d₀.kX
    kY := ⟨(d₀.kY : ℕ), by
      rw [Finset.card_insert_of_notMem hnot]
      exact d₀.kY.isLt⟩ }

/-- The reverse map of the Bob-reveal pushforward (mirror). -/
@[reducible] def toBobReveal : BobRevealDatum n D :=
  have hnot : d₀.i ∉ d₀.LX := fun h =>
    (Finset.mem_compl.mp (d₀.LX_subset h)) (Finset.mem_insert_self _ _)
  { LXp := insert d₀.i d₀.LX
    LY := d₀.LY
    disjoint := by
      rw [Finset.disjoint_insert_left]
      exact ⟨fun h => (Finset.mem_compl.mp (d₀.LY_subset h))
        (Finset.mem_insert_self _ _), d₀.disjoint⟩
    partition := by
      rw [Finset.insert_union, d₀.partition, Finset.compl_insert,
        Finset.insert_erase (Finset.mem_compl.mpr d₀.i_notMem)]
    πX := (finCongr (Finset.card_insert_of_notMem hnot)).trans
      ((finSuccEquiv' d₀.kX).trans
        ((Equiv.optionCongr d₀.πX).trans
          (Finset.subtypeInsertEquivOption hnot).symm))
    πY := d₀.πY
    kX := ⟨(d₀.kX : ℕ), by
      rw [Finset.card_insert_of_notMem hnot]
      exact d₀.kX.isLt⟩
    kY := d₀.kY }

end RevealDatum

/-- The Alice-reveal pushforward bijection: delete the live coordinate
from the order, with re-insertion at the cut as inverse. -/
def aliceRevealEquiv (n : ℕ) (D : Finset (Fin n)) :
    AliceRevealDatum n D ≃ RevealDatum n D where
  toFun := AliceRevealDatum.toReveal
  invFun := RevealDatum.toAliceReveal
  left_inv := by
    classical
    intro d
    have hmem : (d.πY d.kY).1 ∈ d.LYp := (d.πY d.kY).2
    have hnotE : (d.πY d.kY).1 ∉ d.LYp.erase (d.πY d.kY).1 :=
      Finset.notMem_erase _ _
    refine pushAliceExt _ _ rfl (Finset.insert_erase hmem) HEq.rfl ?_ HEq.rfl
      (pushHEqFin (congrArg Finset.card (Finset.insert_erase hmem)) _ _ rfl)
    refine pushHEqEquiv (Finset.insert_erase hmem) _ _ ?_
    intro t t' htt
    by_cases hcut : (t' : ℕ) = (d.kY : ℕ)
    · refine (pushInsEvalCut _ _ _ _ _ _ _ ?_).trans ?_
      · exact Fin.ext (htt.trans hcut)
      · exact congrArg
          (fun z => ((d.πY z : {j : Fin n // j ∈ d.LYp}) : Fin n))
          (Fin.ext hcut.symm)
    · let K : Fin ((d.LYp.erase (d.πY d.kY).1).card + 1) :=
        ⟨(d.kY : ℕ), by
          rw [Finset.card_erase_of_mem hmem]
          have h1 := d.kY.isLt; have h2 := d.kY.pos; omega⟩
      have hne : Fin.cast (Finset.card_insert_of_notMem hnotE) t ≠ K := by
        intro h
        refine hcut ?_
        rw [← htt]
        simpa [Fin.val_cast] using congrArg Fin.val h
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      refine (pushInsEval _ _ _ _ _ _ _ j hj.symm).trans ?_
      refine (pushDelEval _ _ _ _ _ _ _ _ j).trans ?_
      refine congrArg
        (fun z => ((d.πY z : {j : Fin n // j ∈ d.LYp}) : Fin n))
        (Fin.ext ?_)
      rw [Fin.val_cast]
      refine ((pushSuccAboveVal _ K _ j ?_ ?_).trans ?_)
      · exact rfl
      · rw [Fin.val_cast]
      · exact (congrArg Fin.val hj).trans
          (by rw [Fin.val_cast]; exact htt)
  right_inv := by
    classical
    intro d₀
    have hnot : d₀.i ∉ d₀.LY := fun h =>
      (Finset.mem_compl.mp (d₀.LY_subset h)) (Finset.mem_insert_self _ _)
    have hlive : (((finCongr (Finset.card_insert_of_notMem hnot)).trans
        ((finSuccEquiv' d₀.kY).trans ((Equiv.optionCongr d₀.πY).trans
          (Finset.subtypeInsertEquivOption hnot).symm)))
          (⟨(d₀.kY : ℕ), by
            rw [Finset.card_insert_of_notMem hnot]; exact d₀.kY.isLt⟩ :
            Fin ((insert d₀.i d₀.LY).card)) :
          {j : Fin n // j ∈ insert d₀.i d₀.LY}).1 = d₀.i := by
      refine pushInsEvalCut _ _ _ _ _ _ _ ?_
      exact Fin.ext rfl
    have hSets : ∀ z : Fin n, z = d₀.i →
        (insert d₀.i d₀.LY).erase z = d₀.LY := by
      rintro z rfl
      exact Finset.erase_insert hnot
    have hcard : ∀ z : Fin n, z = d₀.i →
        ((insert d₀.i d₀.LY).erase z).card + 1 = d₀.LY.card + 1 := by
      rintro z rfl
      rw [Finset.erase_insert hnot]
    refine pushRevealExt _ _ hlive rfl (hSets _ hlive) HEq.rfl ?_ HEq.rfl
      (pushHEqFin (hcard _ hlive) _ _ rfl)
    refine pushHEqEquiv (hSets _ hlive) _ _ ?_
    intro t t' htt
    refine (pushDelEval _ _ _ _ _ _ _ _ t).trans ?_
    refine pushInsEval _ _ _ _ _ _ _ t' ?_
    refine Fin.ext ?_
    rw [Fin.val_cast, Fin.val_cast]
    refine pushSuccAboveVal _ d₀.kY _ t' ?_ ?_
    · exact rfl
    · rw [Fin.val_cast]; exact htt

/-- The Bob-reveal pushforward bijection (mirror). -/
def bobRevealEquiv (n : ℕ) (D : Finset (Fin n)) :
    BobRevealDatum n D ≃ RevealDatum n D where
  toFun := BobRevealDatum.toReveal
  invFun := RevealDatum.toBobReveal
  left_inv := by
    classical
    intro d
    have hmem : (d.πX d.kX).1 ∈ d.LXp := (d.πX d.kX).2
    have hnotE : (d.πX d.kX).1 ∉ d.LXp.erase (d.πX d.kX).1 :=
      Finset.notMem_erase _ _
    refine pushBobExt _ _ (Finset.insert_erase hmem) rfl ?_ HEq.rfl
      (pushHEqFin (congrArg Finset.card (Finset.insert_erase hmem)) _ _ rfl)
      HEq.rfl
    refine pushHEqEquiv (Finset.insert_erase hmem) _ _ ?_
    intro t t' htt
    by_cases hcut : (t' : ℕ) = (d.kX : ℕ)
    · refine (pushInsEvalCut _ _ _ _ _ _ _ ?_).trans ?_
      · exact Fin.ext (htt.trans hcut)
      · exact congrArg
          (fun z => ((d.πX z : {j : Fin n // j ∈ d.LXp}) : Fin n))
          (Fin.ext hcut.symm)
    · let K : Fin ((d.LXp.erase (d.πX d.kX).1).card + 1) :=
        ⟨(d.kX : ℕ), by
          rw [Finset.card_erase_of_mem hmem]
          have h1 := d.kX.isLt; have h2 := d.kX.pos; omega⟩
      have hne : Fin.cast (Finset.card_insert_of_notMem hnotE) t ≠ K := by
        intro h
        refine hcut ?_
        rw [← htt]
        simpa [Fin.val_cast] using congrArg Fin.val h
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      refine (pushInsEval _ _ _ _ _ _ _ j hj.symm).trans ?_
      refine (pushDelEval _ _ _ _ _ _ _ _ j).trans ?_
      refine congrArg
        (fun z => ((d.πX z : {j : Fin n // j ∈ d.LXp}) : Fin n))
        (Fin.ext ?_)
      rw [Fin.val_cast]
      refine ((pushSuccAboveVal _ K _ j ?_ ?_).trans ?_)
      · exact rfl
      · rw [Fin.val_cast]
      · exact (congrArg Fin.val hj).trans
          (by rw [Fin.val_cast]; exact htt)
  right_inv := by
    classical
    intro d₀
    have hnot : d₀.i ∉ d₀.LX := fun h =>
      (Finset.mem_compl.mp (d₀.LX_subset h)) (Finset.mem_insert_self _ _)
    have hlive : (((finCongr (Finset.card_insert_of_notMem hnot)).trans
        ((finSuccEquiv' d₀.kX).trans ((Equiv.optionCongr d₀.πX).trans
          (Finset.subtypeInsertEquivOption hnot).symm)))
          (⟨(d₀.kX : ℕ), by
            rw [Finset.card_insert_of_notMem hnot]; exact d₀.kX.isLt⟩ :
            Fin ((insert d₀.i d₀.LX).card)) :
          {j : Fin n // j ∈ insert d₀.i d₀.LX}).1 = d₀.i := by
      refine pushInsEvalCut _ _ _ _ _ _ _ ?_
      exact Fin.ext rfl
    have hSets : ∀ z : Fin n, z = d₀.i →
        (insert d₀.i d₀.LX).erase z = d₀.LX := by
      rintro z rfl
      exact Finset.erase_insert hnot
    have hcard : ∀ z : Fin n, z = d₀.i →
        ((insert d₀.i d₀.LX).erase z).card + 1 = d₀.LX.card + 1 := by
      rintro z rfl
      rw [Finset.erase_insert hnot]
    refine pushRevealExt _ _ hlive (hSets _ hlive) rfl ?_ HEq.rfl
      (pushHEqFin (hcard _ hlive) _ _ rfl) HEq.rfl
    refine pushHEqEquiv (hSets _ hlive) _ _ ?_
    intro t t' htt
    refine (pushDelEval _ _ _ _ _ _ _ _ t).trans ?_
    refine pushInsEval _ _ _ _ _ _ _ t' ?_
    refine Fin.ext ?_
    rw [Fin.val_cast, Fin.val_cast]
    refine pushSuccAboveVal _ d₀.kX _ t' ?_ ?_
    · exact rfl
    · rw [Fin.val_cast]; exact htt

/-- **The Alice-reveal reverse experiment has exactly the forward law**
(node 1.2.8; 05_prerounding.tex, "Both reverse experiments have exactly
the forward law", verified against eq forward-outcome-probability):
there is a bijection from Alice-reveal reverse data to forward reveal
data — read off the live coordinate `i = π_Y[k_Y+1]`, delete it from
the order — matching the laws pointwise and the derived public data:
the live coordinate, the two blocks, and the two cut values are carried
over unchanged. (Order compatibility across the bijection — the prefix
structure the martingale filtration consumes — is stated with the
operator half of node 1.2.8.) -/
theorem aliceReveal_pushforward_eq (n : ℕ) (D : Finset (Fin n)) :
    ∃ e : AliceRevealDatum n D ≃ RevealDatum n D,
      (∀ d : AliceRevealDatum n D, d.law = (e d).revealLaw) ∧
      (∀ d : AliceRevealDatum n D,
        (e d).i = d.liveIdx ∧ (e d).LX = d.LX ∧
        (e d).LY = d.LYp.erase d.liveIdx ∧
        ((e d).kX : ℕ) = (d.kX : ℕ) ∧ ((e d).kY : ℕ) = (d.kY : ℕ)) := by
  exact ⟨aliceRevealEquiv n D, fun d => d.law_toReveal,
    fun d => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **The Bob-reveal reverse experiment has exactly the forward law**
(node 1.2.8, mirror statement). -/
theorem bobReveal_pushforward_eq (n : ℕ) (D : Finset (Fin n)) :
    ∃ e : BobRevealDatum n D ≃ RevealDatum n D,
      (∀ d : BobRevealDatum n D, d.law = (e d).revealLaw) ∧
      (∀ d : BobRevealDatum n D,
        (e d).i = d.liveIdx ∧ (e d).LY = d.LY ∧
        (e d).LX = d.LXp.erase d.liveIdx ∧
        ((e d).kY : ℕ) = (d.kY : ℕ) ∧ ((e d).kX : ℕ) = (d.kX : ℕ)) := by
  exact ⟨bobRevealEquiv n D, fun d => d.law_toReveal,
    fun d => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

end CommutingRepetition
