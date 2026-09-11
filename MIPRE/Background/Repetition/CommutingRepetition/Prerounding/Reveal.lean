/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/Reveal.lean
-/
/-
# Reveal histories (node 1.2.3)

The forward reveal experiment of the pre-rounding argument
(05_prerounding.tex, "Reveal histories and exact branch effects":
eqs lambda-full, forward-reveal-sets, reveal-cover, P0-full,
forward-outcome-probability, prior-factorization). Everything here is
finite combinatorics and finite probability over the question words; the
operator-valued branch effects built on top of this layer are node 1.2.4
(Prerounding/Branches).

Encoding: the core `D` is an abstract `Finset (Fin n)` (supplied by the
greedy conditioning of node 1.2.1); `M₀ = [n] \ D` is its complement; a
reveal datum carries the live coordinate `i ∈ M₀`, the block partition
`M₀ \ {i} = L_X ⊔ L_Y`, orders of the two blocks as position↦element
equivalences, and the two uniform cuts. Orders-as-equivalences keep the
datum a `Fintype` and make prefix extraction (`π^{≤k}`) an image of an
initial segment of positions.
-/
import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators

set_option synthInstance.maxSize 1024 in
/-- The finite public reveal datum
`λ = (i, L_X, L_Y, π_{X,−i}, π_{Y,−i}, k_X, k_Y)` of the forward reveal
experiment over the core `D` (05_prerounding.tex, eq lambda-full): a live
coordinate `i ∉ D`, a two-block partition `L_X ⊔ L_Y` of the non-core
coordinates other than `i`, uniform orders of the two blocks (encoded as
position↦element equivalences), and cuts `k_X ∈ {0,…,|L_X|}`,
`k_Y ∈ {0,…,|L_Y|}`. -/
structure RevealDatum (n : ℕ) (D : Finset (Fin n)) where
  i : Fin n
  i_notMem : i ∉ D
  LX : Finset (Fin n)
  LY : Finset (Fin n)
  disjoint : Disjoint LX LY
  partition : LX ∪ LY = (insert i D)ᶜ
  πX : Fin LX.card ≃ {j : Fin n // j ∈ LX}
  πY : Fin LY.card ≃ {j : Fin n // j ∈ LY}
  kX : Fin (LX.card + 1)
  kY : Fin (LY.card + 1)
  deriving Fintype

namespace RevealDatum

variable {n : ℕ} {D : Finset (Fin n)} (d : RevealDatum n D)

/-- The first `k_X` entries of the order `π_{X,−i}`, as a set:
`π_{X,−i}^{≤ k_X}` (05_prerounding.tex, eq forward-reveal-sets). -/
def prefixX : Finset (Fin n) :=
  (Finset.univ.filter fun t : Fin d.LX.card => (t : ℕ) < (d.kX : ℕ)).image
    fun t => (d.πX t : Fin n)

/-- The first `k_Y` entries of the order `π_{Y,−i}`, as a set:
`π_{Y,−i}^{≤ k_Y}`. -/
def prefixY : Finset (Fin n) :=
  (Finset.univ.filter fun t : Fin d.LY.card => (t : ℕ) < (d.kY : ℕ)).image
    fun t => (d.πY t : Fin n)

/-- Alice's revealed coordinate set `C_X = D ∪ L_X ∪ π_{Y,−i}^{≤ k_Y}`
(05_prerounding.tex, eq forward-reveal-sets). -/
def CX : Finset (Fin n) := D ∪ d.LX ∪ d.prefixY

/-- Bob's revealed coordinate set `C_Y = D ∪ L_Y ∪ π_{X,−i}^{≤ k_X}`. -/
def CY : Finset (Fin n) := D ∪ d.LY ∪ d.prefixX

theorem prefixX_subset : d.prefixX ⊆ d.LX := by
  intro j hj
  simp only [prefixX, Finset.mem_image, Finset.mem_filter] at hj
  obtain ⟨t, _, rfl⟩ := hj
  exact (d.πX t).2

theorem prefixY_subset : d.prefixY ⊆ d.LY := by
  intro j hj
  simp only [prefixY, Finset.mem_image, Finset.mem_filter] at hj
  obtain ⟨t, _, rfl⟩ := hj
  exact (d.πY t).2

theorem LX_subset : d.LX ⊆ (insert d.i D)ᶜ :=
  d.partition ▸ Finset.subset_union_left

theorem LY_subset : d.LY ⊆ (insert d.i D)ᶜ :=
  d.partition ▸ Finset.subset_union_right

/-- First half of eq reveal-cover: `D ⊆ C_X ∩ C_Y`. -/
theorem core_subset : D ⊆ d.CX ∩ d.CY := by
  intro j hj
  simp only [Finset.mem_inter, CX, CY, Finset.mem_union]
  exact ⟨Or.inl (Or.inl hj), Or.inl (Or.inl hj)⟩

/-- Second half of eq reveal-cover: `C_X ∪ C_Y = [n] \ {i}` — every
coordinate other than the live one is revealed to at least one player.
This is what makes the prior factorize (eq prior-factorization). -/
theorem union_eq_compl_singleton :
    d.CX ∪ d.CY = ({d.i} : Finset (Fin n))ᶜ := by
  have hmem : ∀ j : Fin n, j ∈ d.LX ∪ d.LY ↔ ¬(j = d.i ∨ j ∈ D) := by
    intro j
    rw [d.partition, Finset.mem_compl, Finset.mem_insert]
  ext j
  simp only [CX, CY, Finset.mem_union, Finset.mem_compl,
    Finset.mem_singleton]
  constructor
  · rintro ((((hj | hj) | hj) | ((_hj | hj) | hj)))
    · rintro rfl; exact d.i_notMem hj
    · have := (hmem j).mp (Finset.mem_union.mpr (Or.inl hj))
      rintro rfl; exact this (Or.inl rfl)
    · have := (hmem j).mp
        (Finset.mem_union.mpr (Or.inr (d.prefixY_subset hj)))
      rintro rfl; exact this (Or.inl rfl)
    · rintro rfl; exact d.i_notMem _hj
    · have := (hmem j).mp (Finset.mem_union.mpr (Or.inr hj))
      rintro rfl; exact this (Or.inl rfl)
    · have := (hmem j).mp
        (Finset.mem_union.mpr (Or.inl (d.prefixX_subset hj)))
      rintro rfl; exact this (Or.inl rfl)
  · intro hne
    by_cases hjD : j ∈ D
    · exact Or.inl (Or.inl (Or.inl hjD))
    · have : j ∈ d.LX ∪ d.LY := (hmem j).mpr (by
        rintro (rfl | h)
        · exact hne rfl
        · exact hjD h)
      rcases Finset.mem_union.mp this with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (Or.inl (Or.inr h))

/-- The live coordinate is unrevealed to Alice. -/
theorem i_notMem_CX : d.i ∉ d.CX := by
  simp only [CX, Finset.mem_union]
  rintro ((h | h) | h)
  · exact d.i_notMem h
  · exact absurd (d.LX_subset h) (by simp)
  · exact absurd (d.LY_subset (d.prefixY_subset h)) (by simp)

/-- The live coordinate is unrevealed to Bob. -/
theorem i_notMem_CY : d.i ∉ d.CY := by
  simp only [CY, Finset.mem_union]
  rintro ((h | h) | h)
  · exact d.i_notMem h
  · exact absurd (d.LY_subset h) (by simp)
  · exact absurd (d.LX_subset (d.prefixX_subset h)) (by simp)

/-- Block sizes: `|L_X| + |L_Y| = m − 1` with `m = n − |D|` non-core
coordinates. -/
theorem card_LX_add_card_LY :
    d.LX.card + d.LY.card = n - D.card - 1 := by
  rw [← Finset.card_union_of_disjoint d.disjoint, d.partition,
    Finset.card_compl, Finset.card_insert_of_notMem d.i_notMem,
    Fintype.card_fin]
  omega

/-- The forward reveal law (05_prerounding.tex, eqs lambda-full and
forward-outcome-probability): `i` uniform on the `m` non-core
coordinates, each remaining coordinate assigned to a block by a fair
coin, uniform orders of the two blocks, uniform cuts — the datum's
probability is
`2^{1−m} / (m · |L_X|! · (|L_X|+1) · |L_Y|! · (|L_Y|+1))`. -/
noncomputable def revealLaw (d : RevealDatum n D) : ℝ :=
  (1 / (n - D.card : ℕ)) * (1 / 2 ^ (n - D.card - 1)) *
    (1 / (Nat.factorial d.LX.card)) * (1 / (Nat.factorial d.LY.card)) *
    (1 / (d.LX.card + 1)) * (1 / (d.LY.card + 1))

theorem revealLaw_nonneg : 0 ≤ d.revealLaw := by
  unfold revealLaw
  positivity

/-- The forward reveal law is a probability law on reveal data
(05_prerounding.tex, eq lambda-full with eq forward-outcome-probability:
`m` choices of `i`, `2^{m−1}` block assignments, `|L_X|!·|L_Y|!` orders,
`(|L_X|+1)(|L_Y|+1)` cuts). Requires a proper core `|D| < n`, which the
greedy conditioning guarantees (`|D| < n/2`). -/
theorem revealLaw_sum (hD : D.card < n) :
    (∑ d : RevealDatum n D, d.revealLaw) = 1 := by
  classical
  -- Reindex over (live coordinate, Alice block, orders, cuts); the Bob
  -- block is the complement of the Alice block.
  have key : (∑ d : RevealDatum n D, d.revealLaw)
      = ∑ t : Σ i : {i : Fin n // i ∉ D},
          Σ L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
            ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
             (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
               {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
             Fin (L.1.card + 1) ×
             Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
          (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
            (1 / (Nat.factorial t.2.1.1.card)) *
            (1 / (Nat.factorial ((insert t.1.1 D)ᶜ \ t.2.1.1).card)) *
            (1 / (t.2.1.1.card + 1)) *
            (1 / (((insert t.1.1 D)ᶜ \ t.2.1.1).card + 1)) := by
    refine Finset.sum_nbij'
      (fun d => ⟨⟨d.i, d.i_notMem⟩, ⟨⟨d.LX, d.LX_subset⟩,
        (d.πX,
         (show d.LY = (insert d.i D)ᶜ \ d.LX by
            rw [← d.partition, Finset.union_sdiff_cancel_left d.disjoint])
           ▸ d.πY,
         d.kX,
         (show d.LY = (insert d.i D)ᶜ \ d.LX by
            rw [← d.partition, Finset.union_sdiff_cancel_left d.disjoint])
           ▸ d.kY)⟩⟩)
      (fun t => { i := t.1.1
                  i_notMem := t.1.2
                  LX := t.2.1.1
                  LY := (insert t.1.1 D)ᶜ \ t.2.1.1
                  disjoint := Finset.disjoint_sdiff
                  partition := Finset.union_sdiff_of_subset t.2.1.2
                  πX := t.2.2.1
                  πY := t.2.2.2.1
                  kX := t.2.2.2.2.1
                  kY := t.2.2.2.2.2 })
      (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
      ?_ ?_ ?_
    · rintro ⟨i, hi, LX, LY, hdisj, hpart, πX, πY, kX, kY⟩ _
      have e : LY = ((insert i D)ᶜ : Finset (Fin n)) \ LX := by
        rw [← hpart, Finset.union_sdiff_cancel_left hdisj]
      subst e
      rfl
    · rintro ⟨⟨i, hi⟩, ⟨L, hL⟩, e1, e2, k1, k2⟩ _
      rfl
    · rintro ⟨i, hi, LX, LY, hdisj, hpart, πX, πY, kX, kY⟩ _
      have e : LY = ((insert i D)ᶜ : Finset (Fin n)) \ LX := by
        rw [← hpart, Finset.union_sdiff_cancel_left hdisj]
      subst e
      rfl
  -- Collapse the fibers: orders and cuts contribute their cardinalities,
  -- the block choice contributes 2^(m-1), the live coordinate m.
  have hfiber : ∀ (i : {i : Fin n // i ∉ D})
      (L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ}),
      (∑ _q : ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
         (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
           {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
         Fin (L.1.card + 1) ×
         Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
        (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
          (1 / (Nat.factorial L.1.card)) *
          (1 / (Nat.factorial ((insert i.1 D)ᶜ \ L.1).card)) *
          (1 / (L.1.card + 1)) *
          (1 / (((insert i.1 D)ᶜ \ L.1).card + 1)))
      = (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) := by
    intro i L
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_prod, Fintype.card_prod,
      Fintype.card_equiv L.1.equivFin.symm,
      Fintype.card_equiv ((insert i.1 D)ᶜ \ L.1).equivFin.symm,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
    have hk : ((Nat.factorial L.1.card : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hl : ((Nat.factorial ((insert i.1 D)ᶜ \ L.1).card : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hk1 : ((L.1.card : ℝ) + 1) ≠ 0 := by positivity
    have hl1 : ((((insert i.1 D)ᶜ \ L.1).card : ℝ) + 1) ≠ 0 := by
      positivity
    push_cast
    generalize (Nat.factorial L.1.card : ℝ) = K at hk ⊢
    generalize (Nat.factorial ((insert i.1 D)ᶜ \ L.1).card : ℝ) = Lf
      at hl ⊢
    generalize ((L.1.card : ℝ) + 1) = K1 at hk1 ⊢
    generalize ((((insert i.1 D)ᶜ \ L.1).card : ℝ) + 1) = L1 at hl1 ⊢
    generalize ((n - D.card : ℕ) : ℝ) = M
    generalize ((2 : ℝ) ^ (n - D.card - 1)) = E
    field_simp
  have hstep : ∀ i : {i : Fin n // i ∉ D},
      (∑ p : Σ L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
          ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
           (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
             {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
           Fin (L.1.card + 1) ×
           Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
        (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
          (1 / (Nat.factorial p.1.1.card)) *
          (1 / (Nat.factorial ((insert i.1 D)ᶜ \ p.1.1).card)) *
          (1 / (p.1.1.card + 1)) *
          (1 / (((insert i.1 D)ᶜ \ p.1.1).card + 1)))
      = (1 / (n - D.card : ℕ) : ℝ) := by
    intro i
    rw [← Finset.univ_sigma_univ]
    rw [Finset.sum_sigma]
    calc (∑ L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
          ∑ _q : ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
             (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
               {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
             Fin (L.1.card + 1) ×
             Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
            (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
              (1 / (Nat.factorial L.1.card)) *
              (1 / (Nat.factorial ((insert i.1 D)ᶜ \ L.1).card)) *
              (1 / (L.1.card + 1)) *
              (1 / (((insert i.1 D)ᶜ \ L.1).card + 1)))
        = ∑ _L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
            (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) :=
          Finset.sum_congr rfl fun L _ => hfiber i L
      _ = (1 / (n - D.card : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ]
          have hcardL : Fintype.card
              {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ}
              = 2 ^ (n - D.card - 1) := by
            rw [Fintype.card_subtype]
            have hfilter : (Finset.univ.filter
                fun L : Finset (Fin n) => L ⊆ (insert i.1 D)ᶜ)
                = ((insert i.1 D)ᶜ : Finset (Fin n)).powerset := by
              ext L
              simp [Finset.mem_powerset]
            rw [hfilter, Finset.card_powerset, Finset.card_compl,
              Finset.card_insert_of_notMem i.2, Fintype.card_fin,
              Nat.sub_sub]
          rw [hcardL, nsmul_eq_mul]
          have h2 : ((2 : ℝ) ^ (n - D.card - 1)) ≠ 0 := by positivity
          push_cast
          generalize hE : ((2 : ℝ) ^ (n - D.card - 1)) = E at h2 ⊢
          generalize ((n - D.card : ℕ) : ℝ) = M
          field_simp
  rw [key, ← Finset.univ_sigma_univ]
  rw [Finset.sum_sigma]
  calc (∑ i : {i : Fin n // i ∉ D},
        ∑ p : Σ L : {L : Finset (Fin n) // L ⊆ (insert i.1 D)ᶜ},
          ((Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
           (Fin ((insert i.1 D)ᶜ \ L.1).card ≃
             {j : Fin n // j ∈ (insert i.1 D)ᶜ \ L.1}) ×
           Fin (L.1.card + 1) ×
           Fin (((insert i.1 D)ᶜ \ L.1).card + 1)),
        (1 / (n - D.card : ℕ) : ℝ) * (1 / 2 ^ (n - D.card - 1)) *
          (1 / (Nat.factorial p.1.1.card)) *
          (1 / (Nat.factorial ((insert i.1 D)ᶜ \ p.1.1).card)) *
          (1 / (p.1.1.card + 1)) *
          (1 / (((insert i.1 D)ᶜ \ p.1.1).card + 1)))
      = ∑ _i : {i : Fin n // i ∉ D}, (1 / (n - D.card : ℕ) : ℝ) :=
        Finset.sum_congr rfl fun i _ => hstep i
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ]
        have hcardI : Fintype.card {i : Fin n // i ∉ D} = n - D.card := by
          rw [Fintype.card_subtype]
          have hfilter : (Finset.univ.filter fun i : Fin n => i ∉ D)
              = Dᶜ := by
            ext i
            simp
          rw [hfilter, Finset.card_compl, Fintype.card_fin]
        rw [hcardI, nsmul_eq_mul]
        have hm : ((n - D.card : ℕ) : ℝ) ≠ 0 := by
          have h0 : 0 < n - D.card := Nat.sub_pos_of_lt hD
          exact_mod_cast h0.ne'
        rw [mul_one_div_cancel hm]

end RevealDatum

section PriorFactorization

variable {n : ℕ} {X Y : Type} [Fintype X] [Fintype Y]

/-- Two words agree on a finite index set. -/
def agreesOn {α : Type*} (S : Finset (Fin n)) (w w' : Fin n → α) : Prop :=
  ∀ j ∈ S, w j = w' j

instance {α : Type*} [DecidableEq α] (S : Finset (Fin n))
    (w w' : Fin n → α) : Decidable (agreesOn S w w') := by
  unfold agreesOn; infer_instance

/-- The unnormalized posterior weight of a full question-word pair given
the reveal: the product prior `∏_j μ(x_j, y_j)` restricted to the words
consistent with the revealed values — `x` on `C_X ∪ {i}` and `y` on
`C_Y ∪ {i}` (the conditioning `(T₀ = t, X_i = x, Y_i = y)` of
05_prerounding.tex, eq prior-factorization, with the revealed values
packaged as reference words `x₀, y₀`). -/
noncomputable def priorWeight [DecidableEq X] [DecidableEq Y]
    {D : Finset (Fin n)} (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y)
    (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  if agreesOn (insert d.i d.CX) x x₀ ∧ agreesOn (insert d.i d.CY) y y₀
    then ∏ j, μ (x j) (y j) else 0

/-- **Prior factorization** (node 1.2.3; 05_prerounding.tex, eq
prior-factorization): given the reveal and the live questions, the full
Alice word and the full Bob word are conditionally independent under the
referee's product prior, because the unrevealed Alice coordinates and the
unrevealed Bob coordinates occupy disjoint coordinate sets (eq
reveal-cover) and each carries a pinned half of its coordinate's joint
law. Stated division-free as the exact identity
`E[fg]·E[1] = E[f]·E[g]` for the unnormalized conditioned weight, for
every pair of test functions; the identity is under the prior `ℙ`, not
under the posterior `ℚ`. -/
theorem prior_factorization [DecidableEq X] [DecidableEq Y]
    {D : Finset (Fin n)} (d : RevealDatum n D) (μ : X → Y → ℝ)
    (x₀ : Fin n → X) (y₀ : Fin n → Y)
    (f : (Fin n → X) → ℝ) (g : (Fin n → Y) → ℝ) :
    (∑ x : Fin n → X, ∑ y : Fin n → Y,
        priorWeight d μ x₀ y₀ x y * (f x * g y)) *
      (∑ x : Fin n → X, ∑ y : Fin n → Y, priorWeight d μ x₀ y₀ x y)
    = (∑ x : Fin n → X, ∑ y : Fin n → Y,
        priorWeight d μ x₀ y₀ x y * f x) *
      (∑ x : Fin n → X, ∑ y : Fin n → Y,
        priorWeight d μ x₀ y₀ x y * g y) := by
  classical
  -- Every coordinate has a pinned side (eq reveal-cover).
  have hcov : ∀ j : Fin n, j ∉ insert d.i d.CX → j ∈ insert d.i d.CY := by
    intro j hj
    have hji : j ≠ d.i := by
      rintro rfl; exact hj (Finset.mem_insert_self _ _)
    have hmem : j ∈ d.CX ∪ d.CY := by
      rw [d.union_eq_compl_singleton]
      simpa using hji
    rcases Finset.mem_union.mp hmem with h | h
    · exact absurd (Finset.mem_insert_of_mem h) hj
    · exact Finset.mem_insert_of_mem h
  -- The conditioned weight splits as an x-factor times a y-factor.
  set φ : (Fin n → X) → ℝ := fun x =>
    if agreesOn (insert d.i d.CX) x x₀ then
      ∏ j ∈ (insert d.i d.CX)ᶜ, μ (x j) (y₀ j)
    else 0 with hφ
  set ψ : (Fin n → Y) → ℝ := fun y =>
    if agreesOn (insert d.i d.CY) y y₀ then
      (∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (x₀ j) (y₀ j)) *
        ∏ j ∈ insert d.i d.CX \ insert d.i d.CY, μ (x₀ j) (y j)
    else 0 with hψ
  have hw : ∀ x y, priorWeight d μ x₀ y₀ x y = φ x * ψ y := by
    intro x y
    simp only [priorWeight, hφ, hψ]
    by_cases hx : agreesOn (insert d.i d.CX) x x₀
    · by_cases hy : agreesOn (insert d.i d.CY) y y₀
      · rw [if_pos ⟨hx, hy⟩, if_pos hx, if_pos hy]
        have e1 : (∏ j ∈ (insert d.i d.CX)ᶜ, μ (x j) (y j))
            = ∏ j ∈ (insert d.i d.CX)ᶜ, μ (x j) (y₀ j) :=
          Finset.prod_congr rfl fun j hj => by
            rw [hy j (hcov j (Finset.mem_compl.mp hj))]
        have e2 : (∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY,
              μ (x j) (y j))
            = ∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY,
                μ (x₀ j) (y₀ j) :=
          Finset.prod_congr rfl fun j hj => by
            rw [hx j (Finset.mem_inter.mp hj).1,
              hy j (Finset.mem_inter.mp hj).2]
        have e3 : (∏ j ∈ insert d.i d.CX \ insert d.i d.CY,
              μ (x j) (y j))
            = ∏ j ∈ insert d.i d.CX \ insert d.i d.CY,
                μ (x₀ j) (y j) :=
          Finset.prod_congr rfl fun j hj => by
            rw [hx j (Finset.mem_sdiff.mp hj).1]
        have hIsplit : (∏ j ∈ insert d.i d.CX, μ (x j) (y j))
            = (∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (x j) (y j)) *
              ∏ j ∈ insert d.i d.CX \ insert d.i d.CY, μ (x j) (y j) := by
          rw [← Finset.prod_filter_mul_prod_filter_not (insert d.i d.CX)
            (fun j => j ∈ insert d.i d.CY) (fun j => μ (x j) (y j)),
            Finset.filter_mem_eq_inter, ← Finset.sdiff_eq_filter]
        calc (∏ j, μ (x j) (y j))
            = (∏ j ∈ insert d.i d.CX, μ (x j) (y j)) *
              ∏ j ∈ (insert d.i d.CX)ᶜ, μ (x j) (y j) :=
              (Finset.prod_mul_prod_compl _ _).symm
          _ = ((∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY, μ (x j) (y j)) *
              ∏ j ∈ insert d.i d.CX \ insert d.i d.CY, μ (x j) (y j)) *
              ∏ j ∈ (insert d.i d.CX)ᶜ, μ (x j) (y j) := by
              rw [hIsplit]
          _ = (∏ j ∈ (insert d.i d.CX)ᶜ, μ (x j) (y₀ j)) *
              ((∏ j ∈ insert d.i d.CX ∩ insert d.i d.CY,
                μ (x₀ j) (y₀ j)) *
              ∏ j ∈ insert d.i d.CX \ insert d.i d.CY, μ (x₀ j) (y j)) := by
              rw [e1, e2, e3]; ring
      · rw [if_neg (fun h => hy h.2), if_pos hx, if_neg hy, mul_zero]
    · rw [if_neg (fun h => hx h.1), if_neg hx, zero_mul]
  -- With the split weight, all four sums factorize and the identity is
  -- commutative algebra.
  have key : ∀ (F : (Fin n → X) → ℝ) (G : (Fin n → Y) → ℝ),
      (∑ x : Fin n → X, ∑ y : Fin n → Y,
        priorWeight d μ x₀ y₀ x y * (F x * G y))
      = (∑ x : Fin n → X, φ x * F x) * (∑ y : Fin n → Y, ψ y * G y) := by
    intro F G
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hw x y]; ring
  have k1 := key f g
  have k2 : (∑ x : Fin n → X, ∑ y : Fin n → Y,
      priorWeight d μ x₀ y₀ x y)
      = (∑ x : Fin n → X, φ x) * (∑ y : Fin n → Y, ψ y) := by
    have := key (fun _ => 1) (fun _ => 1)
    simpa using this
  have k3 : (∑ x : Fin n → X, ∑ y : Fin n → Y,
      priorWeight d μ x₀ y₀ x y * f x)
      = (∑ x : Fin n → X, φ x * f x) * (∑ y : Fin n → Y, ψ y) := by
    have := key f (fun _ => 1)
    simpa using this
  have k4 : (∑ x : Fin n → X, ∑ y : Fin n → Y,
      priorWeight d μ x₀ y₀ x y * g y)
      = (∑ x : Fin n → X, φ x) * (∑ y : Fin n → Y, ψ y * g y) := by
    have := key (fun _ => 1) g
    simpa using this
  rw [k1, k2, k3, k4]
  ring

end PriorFactorization

end CommutingRepetition
