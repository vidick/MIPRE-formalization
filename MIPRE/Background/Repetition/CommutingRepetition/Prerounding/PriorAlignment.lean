/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/PriorAlignment.lean
-/
/-
# Pre-rounding: the prior alignment bound, proof layer (node 1.2.9)

Proof-side infrastructure for `prior_alignment_bound` (Prerounding/Costs.lean;
05_prerounding.tex, eqs random-martingale-increment, accepted-word-entropy,
IA-size-bias-calculation, prior-alignment-bound). Following the manuscript:

* the Alice reverse datum is re-read as a **base** (Alice block `L_X ⊆ Dᶜ`,
  Bob block `L_Y⁺ = Dᶜ \ L_X`, the two orders, the forward cut `k_X`) together
  with the uniform interior cut `k_Y`; the size-biased law factors as
  `(2/m)·β(base)` with `∑_base β = 1` (the fair-partition weights `2^{-m}`
  times the order/cut cardinalities);
* at a fixed base, the alignment integrand at cut `k_Y` is the `k_Y`-th
  increment of the Alice scenario reveal martingale (`scenMartA`), so summing
  over the uniform cut telescopes into the column entropy budget
  (`scenMartA_colBudget_mkALabel`): `≤ H₁(p_z(U))` per background and word;
* the size-bias step: the base-weighted prior pairings sum to exactly `p`
  (`pairSum_eq_core`), the total weight is at most `(|A||B|)^{|D|}`, and the
  weighted entropy bound `finite_weighted_entropy_le_of_weight_bound` gives
  `p·(t₀ + s₀)`.

The Bob side (`I_B`) is the mirror. No manuscript statement lives here.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.CostsLemmas

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]

/-! ### The Alice reverse datum as (base, interior cut) -/

/-- An Alice reverse **base**: the Alice block `L_X ⊆ Dᶜ` (the Bob block is
`L_Y⁺ = Dᶜ \ L_X`), the forward order `π_X`, the reverse order `π_Y`, and the
forward cut `k_X`. The interior cut `k_Y ∈ Fin |L_Y⁺|` is split off
(`aliceSigmaEquiv`), because the alignment integrand is summed over it
uniformly (eq IA-size-bias-calculation). -/
abbrev AliceBase (n : ℕ) (D : Finset (Fin n)) : Type :=
  Σ L : {L : Finset (Fin n) // L ⊆ Dᶜ},
    (Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
    (Fin (Dᶜ \ L.1).card ≃ {j : Fin n // j ∈ Dᶜ \ L.1}) ×
    Fin (L.1.card + 1)

namespace AliceBase

variable {D : Finset (Fin n)} (b : AliceBase n D)

/-- The Alice block `L_X`. -/
abbrev LX : Finset (Fin n) := b.1.1
/-- The Bob block `L_Y⁺ = Dᶜ \ L_X`. -/
abbrev LYp : Finset (Fin n) := Dᶜ \ b.1.1
/-- The reverse order of the Bob block. -/
abbrev πY : Fin (Dᶜ \ b.1.1).card ≃ {j : Fin n // j ∈ Dᶜ \ b.1.1} := b.2.2.1
/-- The Alice background `S_A = D ∪ L_X` of the scenario martingale. -/
abbrev SA : Finset (Fin n) := D ∪ b.1.1
/-- Bob's fixed revealed set `D ∪ L_Y⁺ ∪ π_X^{≤ k_X}` (the set behind
`aliceFixedBobEffect_eq_effectiveK`, cut-independent). -/
abbrev SB : Finset (Fin n) := D ∪ (Dᶜ \ b.1.1) ∪ ordPrefix b.2.1 (b.2.2.2 : ℕ)

/-- The base weight `β = 2^{-m}·(1/|L_Y⁺|!)·(1/|L_X|!)·(1/(|L_X|+1))`, so that the
size-biased law is `(2/m)·β` (eq size-biased-partition). -/
noncomputable def β : ℝ :=
  (1 / 2 ^ (n - D.card)) * (1 / (Nat.factorial (Dᶜ \ b.1.1).card)) *
    (1 / (Nat.factorial b.1.1.card)) * (1 / (b.1.1.card + 1))

theorem β_nonneg : 0 ≤ b.β := by unfold β; positivity

theorem disjoint_SA_LYp : Disjoint b.SA b.LYp := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  rcases Finset.mem_union.mp hj with h | h
  · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hj').1) h
  · exact (Finset.mem_sdiff.mp hj').2 h

theorem LYp_subset_SB : b.LYp ⊆ b.SB := fun j hj =>
  Finset.mem_union_left _ (Finset.mem_union_right _ hj)

theorem core_subset_SA : D ⊆ b.SA := Finset.subset_union_left

theorem core_subset_SB : D ⊆ b.SB := fun j hj =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hj)

theorem SA_union_SB : b.SA ∪ b.SB = Finset.univ := by
  ext j
  simp only [Finset.mem_univ, iff_true, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_compl]
  by_cases hD : j ∈ D
  · exact Or.inl (Or.inl hD)
  · by_cases hL : j ∈ b.1.1
    · exact Or.inl (Or.inr hL)
    · exact Or.inr (Or.inl (Or.inr ⟨hD, hL⟩))

end AliceBase

/-- The reverse datum with base `b` and interior cut `k`. -/
def mkAliceDatum {D : Finset (Fin n)} (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    AliceRevealDatum n D where
  LX := b.1.1
  LYp := Dᶜ \ b.1.1
  disjoint := Finset.disjoint_sdiff
  partition := Finset.union_sdiff_of_subset b.1.2
  πX := b.2.1
  πY := b.2.2.1
  kX := b.2.2.2
  kY := k

theorem AliceRevealDatum.LX_subset_compl {D : Finset (Fin n)} (d : AliceRevealDatum n D) :
    d.LX ⊆ Dᶜ := by
  rw [← d.partition]; exact Finset.subset_union_left

theorem AliceRevealDatum.LYp_eq {D : Finset (Fin n)} (d : AliceRevealDatum n D) :
    d.LYp = Dᶜ \ d.LX := by
  rw [← d.partition, Finset.union_sdiff_cancel_left d.disjoint]

/-- The (base, cut) presentation of the Alice reverse datum. -/
def aliceSigmaEquiv (D : Finset (Fin n)) :
    (Σ b : AliceBase n D, Fin (Dᶜ \ b.1.1).card) ≃ AliceRevealDatum n D where
  toFun t := mkAliceDatum t.1 t.2
  invFun d := ⟨⟨⟨d.LX, d.LX_subset_compl⟩, (d.πX, d.LYp_eq ▸ d.πY, d.kX)⟩, d.LYp_eq ▸ d.kY⟩
  left_inv := by
    rintro ⟨⟨⟨L, hL⟩, πX, πY, kX⟩, k⟩
    rfl
  right_inv := by
    rintro ⟨LX, LYp, hdisj, hpart, πX, πY, kX, kY⟩
    have e : LYp = Dᶜ \ LX := by
      rw [← hpart, Finset.union_sdiff_cancel_left hdisj]
    subst e
    rfl

/-- The size-biased law of a datum in (base, cut) form: `(2/m)·β(base)` (the
factor `(2N_A/m)·(1/N_A) = 2/m` of eq size-biased-partition; the cut's
existence forces `N_A > 0`). -/
theorem mkAliceDatum_law {D : Finset (Fin n)} (hm : D.card < n) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) :
    (mkAliceDatum b k).law = 2 / ((n - D.card : ℕ) : ℝ) * b.β := by
  have hN : (((Dᶜ \ b.1.1).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fin.pos k).ne'
  have hm' : ((n - D.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hm).ne'
  unfold AliceRevealDatum.law AliceBase.β mkAliceDatum
  simp only
  field_simp

/-- The base weights sum to one: fair partitions `2^{-m}` over the `2^m`
Alice blocks, uniform orders and forward cut (eq size-biased-partition,
"the last sum of the fair-partition weights is at most one" — here exact). -/
theorem AliceBase.sum_β (D : Finset (Fin n)) (hm : D.card < n) :
    (∑ b : AliceBase n D, b.β) = 1 := by
  classical
  rw [Fintype.sum_sigma]
  have hfiber : ∀ L : {L : Finset (Fin n) // L ⊆ Dᶜ},
      (∑ q : (Fin L.1.card ≃ {j : Fin n // j ∈ L.1}) ×
          (Fin (Dᶜ \ L.1).card ≃ {j : Fin n // j ∈ Dᶜ \ L.1}) × Fin (L.1.card + 1),
        AliceBase.β (⟨L, q⟩ : AliceBase n D)) = 1 / 2 ^ (n - D.card) := by
    intro L
    simp only [AliceBase.β]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_equiv L.1.equivFin.symm, Fintype.card_equiv (Dᶜ \ L.1).equivFin.symm,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have hk : ((Nat.factorial L.1.card : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hl : ((Nat.factorial (Dᶜ \ L.1).card : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hk1 : ((L.1.card : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun L _ => hfiber L, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hcard : Fintype.card {L : Finset (Fin n) // L ⊆ Dᶜ} = 2 ^ (n - D.card) := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun L : Finset (Fin n) => L ⊆ Dᶜ) = Dᶜ.powerset := by
      ext L; simp [Finset.mem_powerset]
    rw [this, Finset.card_powerset, Finset.card_compl, Fintype.card_fin]
  rw [hcard]
  push_cast
  field_simp

/-! ### Label identities for a datum in (base, cut) form (STEP 1 of the roadmap) -/

section LabelIdentities

variable {D : Finset (Fin n)}

theorem mkAliceDatum_liveIdx (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    (mkAliceDatum b k).liveIdx = (b.πY k : Fin n) := rfl

theorem mkAliceDatum_revealPrefix (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    (mkAliceDatum b k).revealPrefix (mkAliceDatum b k).kY.castSucc
      = ordPrefix b.πY (k : ℕ) := rfl

theorem mkAliceDatum_alicePrefixX (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    (mkAliceDatum b k).alicePrefixX = ordPrefix b.2.1 (b.2.2.2 : ℕ) := rfl

/-- `C_X = S_A ∪ π_Y^{≤ k_Y}` for the forward datum wired to `(b, k)`. -/
theorem RevealDatum.CX_of_alice (r : RevealDatum n D) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) (hLX : r.LX = (mkAliceDatum b k).LX)
    (hpre : r.prefixY = (mkAliceDatum b k).revealPrefix (mkAliceDatum b k).kY.castSucc) :
    r.CX = b.SA ∪ ordPrefix b.πY (k : ℕ) := by
  show D ∪ r.LX ∪ r.prefixY = _
  rw [hLX, hpre, mkAliceDatum_revealPrefix]
  rfl

/-- `{i} ∪ C_X = {π_Y(k_Y)} ∪ (S_A ∪ π_Y^{≤ k_Y})`. -/
theorem RevealDatum.insert_CX_of_alice (r : RevealDatum n D) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) (hi : r.i = (mkAliceDatum b k).liveIdx)
    (hLX : r.LX = (mkAliceDatum b k).LX)
    (hpre : r.prefixY = (mkAliceDatum b k).revealPrefix (mkAliceDatum b k).kY.castSucc) :
    insert r.i r.CX = insert (b.πY k : Fin n) (b.SA ∪ ordPrefix b.πY (k : ℕ)) := by
  rw [r.CX_of_alice b k hLX hpre, hi, mkAliceDatum_liveIdx]

/-- The KEY collapse: `{i} ∪ C_Y = D ∪ L_Y⁺ ∪ π_X^{≤ k_X} = S_B`, independent of the
cut `k_Y` (the set behind `aliceFixedBobEffect_eq_effectiveK`). -/
theorem RevealDatum.insert_CY_of_alice (r : RevealDatum n D) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) (hi : r.i = (mkAliceDatum b k).liveIdx)
    (hLY : r.LY = (mkAliceDatum b k).LYp.erase (mkAliceDatum b k).liveIdx)
    (hpx : r.prefixX = (mkAliceDatum b k).alicePrefixX) :
    insert r.i r.CY = b.SB := by
  have hCY : r.CY = D ∪ r.LY ∪ r.prefixX := rfl
  rw [hCY, hLY, hpx, hi, mkAliceDatum_alicePrefixX, ← Finset.insert_union,
    ← Finset.union_insert, Finset.insert_erase (mkAliceDatum b k).liveIdx_mem]
  rfl

end LabelIdentities

/-! ### Unnormalizing the block law -/

/-- Convert a bound on a block-law-weighted sum (the martingale's normalized
law `∏μ / M₀`) into a bound on the raw-prior-weighted sum, with the block
mass `M₀` as the factor; at `M₀ = 0` every raw block weight vanishes. -/
theorem block_unnormalize (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (L : Finset (Fin n)) (yw : Fin n → Y) (F : ({j : Fin n // j ∈ L} → X) → ℝ) (Bnd : ℝ)
    (h : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) ≠ 0 →
      (∑ ω : {j : Fin n // j ∈ L} → X,
        ((∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) /
          ∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) * F ω) ≤ Bnd) :
    (∑ ω : {j : Fin n // j ∈ L} → X, (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) * F ω)
      ≤ (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) * Bnd := by
  classical
  by_cases hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) = 0
  · have hzero : ∀ ω : {j : Fin n // j ∈ L} → X,
        (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) = 0 := by
      intro ω
      obtain ⟨c, -, hc⟩ := Finset.prod_eq_zero_iff.mp hM
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hμ v (yw c)).mp hc
      exact Finset.prod_eq_zero (Finset.mem_univ c) (hall (ω c) (Finset.mem_univ _))
    rw [hM, zero_mul]
    apply le_of_eq
    exact Finset.sum_eq_zero fun ω _ => by rw [hzero ω, zero_mul]
  · have hM0 : 0 ≤ ∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c) :=
      Finset.prod_nonneg fun c _ => Finset.sum_nonneg fun v _ => hμ v (yw c)
    calc (∑ ω : {j : Fin n // j ∈ L} → X, (∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) * F ω)
        = (∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) *
            ∑ ω : {j : Fin n // j ∈ L} → X,
              ((∏ c : {j : Fin n // j ∈ L}, μ (ω c) (yw c)) /
                ∏ c : {j : Fin n // j ∈ L}, ∑ v : X, μ v (yw c)) * F ω := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [← mul_assoc, mul_div_cancel₀ _ hM]
      _ ≤ _ := mul_le_mul_of_nonneg_left (h hM) hM0

namespace TracialStrategy

variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-! ### The size-bias identities (STEP 4 of the roadmap) -/

/-- **Collapse of the prior pairing to the core mass**: for revealed sets
`S_A ⊇ D`, `S_B ⊇ D` covering every coordinate, the prior-weighted pairing of the
two revealed-set effects, summed over the core answers with the `D`-measurable
weight, is exactly the weighted core mass `p` (`pairSum_eq_core`, the tower
property). This is the identity `∑ wᵢ hᵢ = p` behind eq accepted-word-entropy. -/
theorem sum_pairing_eq_coreMass (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    (SA SB : Finset (Fin n)) (hDA : D ⊆ SA) (hDB : D ⊆ SB)
    (hcov : SA ∪ SB = Finset.univ) :
    (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 *
            (S.M.τ (star S.σ *
              (S.setEffectA D SA μ xw yw (mkExtA D zD.1) * S.σ *
                S.setEffectB D SB μ xw yw (mkExtB D zD.2)))).re)
      = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) *
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              w xw yw zD.1 zD.2 *
                (S.M.τ (star S.σ *
                  (S.coreEffectA D xw (mkExtA D zD.1) * S.σ *
                    S.coreEffectB D yw (mkExtB D zD.2)))).re := by
  classical
  have hswap : ∀ (T : (Fin n → X) → (Fin n → Y) →
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) → ℝ),
      (∑ xw : Fin n → X, ∑ yw : Fin n → Y, (∏ j : Fin n, μ (xw j) (yw j)) *
          ∑ zD, T xw yw zD)
        = ∑ zD, ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) * T xw yw zD := by
    intro T
    simp only [Finset.mul_sum]
    calc (∑ xw : Fin n → X, ∑ yw : Fin n → Y, ∑ zD,
            (∏ j : Fin n, μ (xw j) (yw j)) * T xw yw zD)
        = ∑ xw : Fin n → X, ∑ zD, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) * T xw yw zD :=
          Finset.sum_congr rfl fun xw _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap, hswap]
  refine Finset.sum_congr rfl fun zD _ => ?_
  have hcore := S.pairSum_eq_core μ hμ (fun x y => w x y zD.1 zD.2)
    (fun x x' y hx => hwD x x' y y zD.1 zD.2 hx fun _ _ => rfl)
    (fun x y y' hy => hwD x x y y' zD.1 zD.2 (fun _ _ => rfl) hy)
    (mkExtA D zD.1) (mkExtB D zD.2) SA SB hDA hDB hcov
  simp only [pairSum] at hcore
  exact hcore

/-- **Total prior weight**: the `[0,1]`-weighted prior mass over the core answers
is at most the number `(|A||B|)^{|D|}` of core answer words ("the accepted words
have number at most `e^{s₀}`"). -/
theorem sum_prior_weight_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1) :
    (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2)
      ≤ ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card := by
  classical
  have hcard : (Fintype.card (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) : ℝ)
      = ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_coe]
    push_cast
    ring
  have hinner : ∀ (xw : Fin n → X) (yw : Fin n → Y),
      (∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B), w xw yw zD.1 zD.2)
        ≤ ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card := by
    intro xw yw
    calc (∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B), w xw yw zD.1 zD.2)
        ≤ ∑ _zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B), (1 : ℝ) :=
          Finset.sum_le_sum fun zD _ => hw1 xw yw zD.1 zD.2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  calc (∑ xw : Fin n → X, ∑ yw : Fin n → Y,
        (∏ j : Fin n, μ (xw j) (yw j)) *
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B), w xw yw zD.1 zD.2)
      ≤ ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) *
            ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card :=
        Finset.sum_le_sum fun xw _ => Finset.sum_le_sum fun yw _ =>
          mul_le_mul_of_nonneg_left (hinner xw yw)
            (Finset.prod_nonneg fun j _ => hμ _ _)
    _ = ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card := by
        simp only [← Finset.sum_mul]
        rw [sum_prod_mu_eq_one μ hμsum, one_mul]

end TracialStrategy

/-! ### Sum rearrangements -/

theorem sum4_rearrange {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (Q : β → γ → ℝ) (w : β → γ → δ → ℝ) (X : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, Q b c * ∑ d, w b c d * X a b c d)
      = ∑ c, ∑ d, ∑ b, Q b c * (w b c d * ∑ a, X a b c d) := by
  simp only [Finset.mul_sum]
  calc (∑ a, ∑ b, ∑ c, ∑ d, Q b c * (w b c d * X a b c d))
      = ∑ a, ∑ c, ∑ b, ∑ d, Q b c * (w b c d * X a b c d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, Q b c * (w b c d * X a b c d) := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, Q b c * (w b c d * X a b c d) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, Q b c * (w b c d * X a b c d) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, Q b c * (w b c d * X a b c d) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm

theorem sum3_rearrange {β γ δ : Type} [Fintype β] [Fintype γ] [Fintype δ]
    (Q : β → γ → ℝ) (w : β → γ → δ → ℝ) (Y : β → γ → δ → ℝ) :
    (∑ b, ∑ c, Q b c * ∑ d, w b c d * Y b c d)
      = ∑ c, ∑ d, ∑ b, Q b c * (w b c d * Y b c d) := by
  simp only [Finset.mul_sum]
  calc (∑ b, ∑ c, ∑ d, Q b c * (w b c d * Y b c d))
      = ∑ c, ∑ b, ∑ d, Q b c * (w b c d * Y b c d) := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, Q b c * (w b c d * Y b c d) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- Split a word sum at a block and put the off-block values outside. -/
theorem sum_split_comm (L : Finset (Fin n)) (F : (Fin n → X) → ℝ) :
    (∑ xw : Fin n → X, F xw)
      = ∑ g : {j : Fin n // ¬ j ∈ L} → X, ∑ ω : {j : Fin n // j ∈ L} → X,
          F ((wordSplit L X).symm (ω, g)) := by
  rw [sum_wordSplit L F]
  exact Finset.sum_comm

namespace TracialStrategy

variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-! ### The per-base telescoping bound (STEPS 2–3 of the roadmap) -/

/-- The alignment increment at base `b` and interior cut `k`: the squared
branch-vector increment between the Alice labels at `S_A ∪ π_Y^{≤k}` and at
`{π_Y(k)} ∪ S_A ∪ π_Y^{≤k}`, against Bob's cut-independent label at `S_B`
(the `alignCostA` integrand read through `insert_CX_of_alice` /
`insert_CY_of_alice`). -/
noncomputable def alignIncA
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) : ℝ :=
  ‖R.branch S.σ
      (mkALabel D (insert (b.πY k : Fin n) (b.SA ∪ ordPrefix b.πY (k : ℕ))) xw yw zD.1)
      (mkBLabel D b.SB xw yw zD.2)
    - R.branch S.σ (mkALabel D (b.SA ∪ ordPrefix b.πY (k : ℕ)) xw yw zD.1)
        (mkBLabel D b.SB xw yw zD.2)‖ ^ 2

/-- The scalar entropy `H₁` of the initial branch pairing at base `b`:
`H₁(re τ(σ* F_{S_A} σ G_{S_B}))` — `H₁(p_z(U_A))` of eq
random-martingale-increment. -/
noncomputable def alignEntA (μ : X → Y → ℝ) (b : AliceBase n D)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) : ℝ :=
  Real.negMulLog (S.M.τ (star S.σ *
    (S.setEffectA D b.SA μ xw yw (mkExtA D zD.1) * S.σ *
      S.setEffectB D b.SB μ xw yw (mkExtB D zD.2)))).re

/-- **Block bound at a fixed Alice background** (eqs random-martingale-increment
summed over the uniform cut, via `scenMartA_colBudget_mkALabel`): for fixed Bob
word `yw`, core answers `zD` and off-block Alice values `g`, the raw-prior-weighted
sum over the Bob-block values `ω` of the cut-summed increments is at most the
same weighted sum of the initial-pairing entropy. -/
theorem cutSumA_block_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hcol : R.ColEntropyBudget)
    (htotF : ∀ s, (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    (b : AliceBase n D) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B))
    (g : {j : Fin n // ¬ j ∈ b.LYp} → X) :
    (∑ ω : {j : Fin n // j ∈ b.LYp} → X,
      (∏ j : Fin n, μ ((wordSplit b.LYp X).symm (ω, g) j) (yw j)) *
        (w ((wordSplit b.LYp X).symm (ω, g)) yw zD.1 zD.2 *
          ∑ k : Fin (Dᶜ \ b.1.1).card,
            S.alignIncA R b k ((wordSplit b.LYp X).symm (ω, g)) yw zD))
      ≤ ∑ ω : {j : Fin n // j ∈ b.LYp} → X,
          (∏ j : Fin n, μ ((wordSplit b.LYp X).symm (ω, g) j) (yw j)) *
            (w ((wordSplit b.LYp X).symm (ω, g)) yw zD.1 zD.2 *
              S.alignEntA μ b ((wordSplit b.LYp X).symm (ω, g)) yw zD) := by
  classical
  -- the reference word with the same off-block values
  set ω₀ : {j : Fin n // j ∈ b.LYp} → X := fun _ => Classical.arbitrary X with hω₀
  set xw₀ : Fin n → X := (wordSplit b.LYp X).symm (ω₀, g) with hxw₀
  have hLsub : b.LYp ⊆ Dᶜ := Finset.sdiff_subset
  -- off the block, every split word reads `g`
  have hoff : ∀ (ω : {j : Fin n // j ∈ b.LYp} → X) (j : Fin n), j ∉ b.LYp →
      (wordSplit b.LYp X).symm (ω, g) j = xw₀ j := by
    intro ω j hj
    rw [hxw₀, wordSplit_symm_notMem b.LYp X ω g hj, wordSplit_symm_notMem b.LYp X ω₀ g hj]
  -- (f2) the weight is ω-independent
  have hw : ∀ ω : {j : Fin n // j ∈ b.LYp} → X,
      w ((wordSplit b.LYp X).symm (ω, g)) yw zD.1 zD.2 = w xw₀ yw zD.1 zD.2 := by
    intro ω
    refine hwD _ _ yw yw zD.1 zD.2 (fun j hj => hoff ω j ?_) fun _ _ => rfl
    intro hjL
    exact (Finset.mem_compl.mp (hLsub hjL)) hj
  -- (f3) Bob's label is ω-independent
  have hJ : ∀ ω : {j : Fin n // j ∈ b.LYp} → X,
      mkBLabel D b.SB ((wordSplit b.LYp X).symm (ω, g)) yw zD.2
        = mkBLabel D b.SB xw₀ yw zD.2 := by
    intro ω
    refine mkBLabel_congr D b.SB zD.2 (fun j hj => hoff ω j ?_) fun _ _ => rfl
    intro hjL
    exact hj (b.LYp_subset_SB hjL)
  -- (f4) the initial pairing is ω-independent
  have hEnt : ∀ ω : {j : Fin n // j ∈ b.LYp} → X,
      S.alignEntA μ b ((wordSplit b.LYp X).symm (ω, g)) yw zD
        = S.alignEntA μ b xw₀ yw zD := by
    intro ω
    unfold alignEntA
    rw [S.setEffectA_congr D b.SA μ (mkExtA D zD.1) (fun j hj => hoff ω j ?_)
        (fun _ _ => rfl),
      S.setEffectB_congr D b.SB μ (mkExtB D zD.2) (fun j hj => hoff ω j ?_)
        (fun _ _ => rfl)]
    · intro hjL
      exact hj (b.LYp_subset_SB hjL)
    · intro hjL
      exact Finset.disjoint_left.mp b.disjoint_SA_LYp hj hjL
  -- (f1) the prior splits at the block
  have hQ : ∀ ω : {j : Fin n // j ∈ b.LYp} → X,
      (∏ j : Fin n, μ ((wordSplit b.LYp X).symm (ω, g) j) (yw j))
        = (∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) *
          ∏ c : {j : Fin n // ¬ j ∈ b.LYp}, μ (g c) (yw c) :=
    fun ω => prod_mu_wordSplit b.LYp μ yw ω g
  -- the budget in unnormalized form
  set M₀ : ℝ := ∏ c : {j : Fin n // j ∈ b.LYp}, ∑ v : X, μ v (yw c) with hM₀
  set Goff : ℝ := ∏ c : {j : Fin n // ¬ j ∈ b.LYp}, μ (g c) (yw c) with hGoff
  have hGoff0 : 0 ≤ Goff := Finset.prod_nonneg fun c _ => hμ _ _
  have hw0' : 0 ≤ Goff * w xw₀ yw zD.1 zD.2 := mul_nonneg hGoff0 (hw0 _ _ _ _)
  set J₀ := mkBLabel D b.SB xw₀ yw zD.2 with hJ₀
  -- the increment with the ω-independent Bob label
  set Δ : Fin (Dᶜ \ b.1.1).card → ({j : Fin n // j ∈ b.LYp} → X) → ℝ := fun k ω =>
    ‖R.branch S.σ
        (mkALabel D (insert (b.πY k : Fin n) (b.SA ∪ ordPrefix b.πY (k : ℕ)))
          ((wordSplit b.LYp X).symm (ω, g)) yw zD.1) J₀
      - R.branch S.σ (mkALabel D (b.SA ∪ ordPrefix b.πY (k : ℕ))
          ((wordSplit b.LYp X).symm (ω, g)) yw zD.1) J₀‖ ^ 2 with hΔ
  have hInc : ∀ (ω : {j : Fin n // j ∈ b.LYp} → X) (k : Fin (Dᶜ \ b.1.1).card),
      S.alignIncA R b k ((wordSplit b.LYp X).symm (ω, g)) yw zD = Δ k ω := by
    intro ω k
    simp only [alignIncA, hΔ, hJ ω]
  -- the budget's entropy is the initial-pairing entropy at `xw₀`
  have hBnd : Real.negMulLog (S.M.τ (star S.σ *
      ((∑ a : Af, Ffam (mkALabel D b.SA xw₀ yw zD.1) a) * S.σ *
        (∑ c : Bf, Gfam J₀ c)))).re = S.alignEntA μ b xw₀ yw zD := by
    unfold alignEntA
    rw [htotF, htotG, hJ₀]
    simp only [mkALabel, mkBLabel]
    rw [S.setEffectA_canon, S.setEffectB_canon]
  -- the block-law budget, unnormalized
  have hblock : (∑ ω : {j : Fin n // j ∈ b.LYp} → X,
      (∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) * ∑ k, Δ k ω)
        ≤ M₀ * S.alignEntA μ b xw₀ yw zD := by
    rw [← hBnd]
    refine block_unnormalize μ hμ b.LYp yw (fun ω => ∑ k, Δ k ω) _ fun hM => ?_
    have key := S.scenMartA_colBudget_mkALabel μ hμ R hcol htotF b.SA b.LYp
      b.disjoint_SA_LYp b.πY yw g zD.1 hM S.σ S.σ_normalized J₀ ω₀
    calc (∑ ω : {j : Fin n // j ∈ b.LYp} → X,
          ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) / M₀) * ∑ k, Δ k ω)
        = ∑ k, ∑ ω : {j : Fin n // j ∈ b.LYp} → X,
            ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) / M₀) * Δ k ω := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ _ := key
  have hsumM : (∑ ω : {j : Fin n // j ∈ b.LYp} → X,
      ∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) = M₀ :=
    sum_prod_pi_subtype b.LYp fun c v => μ v (yw c)
  calc (∑ ω : {j : Fin n // j ∈ b.LYp} → X,
        (∏ j : Fin n, μ ((wordSplit b.LYp X).symm (ω, g) j) (yw j)) *
          (w ((wordSplit b.LYp X).symm (ω, g)) yw zD.1 zD.2 *
            ∑ k : Fin (Dᶜ \ b.1.1).card,
              S.alignIncA R b k ((wordSplit b.LYp X).symm (ω, g)) yw zD))
      = ∑ ω : {j : Fin n // j ∈ b.LYp} → X,
          ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) * Goff) *
            (w xw₀ yw zD.1 zD.2 * ∑ k, Δ k ω) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hQ ω, hw ω]
        congr 2
        exact Finset.sum_congr rfl fun k _ => hInc ω k
    _ = (Goff * w xw₀ yw zD.1 zD.2) *
          ∑ ω : {j : Fin n // j ∈ b.LYp} → X,
            (∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) * ∑ k, Δ k ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ (Goff * w xw₀ yw zD.1 zD.2) * (M₀ * S.alignEntA μ b xw₀ yw zD) :=
        mul_le_mul_of_nonneg_left hblock hw0'
    _ = (Goff * w xw₀ yw zD.1 zD.2 * S.alignEntA μ b xw₀ yw zD) *
          ∑ ω : {j : Fin n // j ∈ b.LYp} → X,
            ∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c) := by
        rw [hsumM]; ring
    _ = ∑ ω : {j : Fin n // j ∈ b.LYp} → X,
          ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (ω c) (yw c)) * Goff) *
            (w xw₀ yw zD.1 zD.2 * S.alignEntA μ b xw₀ yw zD) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hQ ω, hw ω, hEnt ω]

/-- **Per-base telescoped bound** (STEPS 2–3 of the roadmap): at a fixed base, the
uniform interior cut sums the alignment increments into the column budget, so the
prior-weighted cut-sum is at most the prior-weighted initial-pairing entropy. -/
theorem cutSumA_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hcol : R.ColEntropyBudget)
    (htotF : ∀ s, (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    (b : AliceBase n D) :
    (∑ k : Fin (Dᶜ \ b.1.1).card, ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 * S.alignIncA R b k xw yw zD)
      ≤ ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) *
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              w xw yw zD.1 zD.2 * S.alignEntA μ b xw yw zD := by
  rw [sum4_rearrange (fun xw yw => ∏ j : Fin n, μ (xw j) (yw j))
      (fun xw yw zD => w xw yw zD.1 zD.2) (fun k xw yw zD => S.alignIncA R b k xw yw zD),
    sum3_rearrange (fun xw yw => ∏ j : Fin n, μ (xw j) (yw j))
      (fun xw yw zD => w xw yw zD.1 zD.2) (fun xw yw zD => S.alignEntA μ b xw yw zD)]
  refine Finset.sum_le_sum fun yw _ => Finset.sum_le_sum fun zD _ => ?_
  rw [sum_split_comm b.LYp, sum_split_comm b.LYp]
  exact Finset.sum_le_sum fun g _ =>
    S.cutSumA_block_le μ hμ R hcol htotF htotG w hw0 hwD b yw zD g

end TracialStrategy

namespace TracialStrategy

variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-! ### The size-bias entropy step (STEP 4 of the roadmap) -/

/-- Reshaping the base-indexed flat sums into nested sums. -/
theorem sum_base_reshape (μ : X → Y → ℝ)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (F : AliceBase n D → (Fin n → X) → (Fin n → Y) →
      (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) → ℝ) :
    (∑ t : AliceBase n D × (Fin n → X) × (Fin n → Y) ×
        (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)),
      AliceBase.β t.1 * ((∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) *
        w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) * F t.1 t.2.1 t.2.2.1 t.2.2.2)
      = ∑ b : AliceBase n D, AliceBase.β b * ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) *
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              w xw yw zD.1 zD.2 * F b xw yw zD := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun xw _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yw _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun zD _ => ?_
  ring

/-- **The size-bias entropy bound** (eqs accepted-word-logsum,
accepted-word-entropy, in the weighted form of
`finite_weighted_entropy_le_of_weight_bound`): the base-weighted prior average of
the initial-pairing entropies is at most `p·log(N/p)`, `N = (|A||B|)^{|D|}`,
because the same weights average the pairings themselves to exactly `p`
(`sum_pairing_eq_coreMass`) and have total mass at most `N`
(`sum_prior_weight_le`, `AliceBase.sum_β`). -/
theorem sizeBiasA (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ}
    (hp : p = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 *
            (S.M.τ (star S.σ *
              (S.coreEffectA D xw (mkExtA D zD.1) * S.σ *
                S.coreEffectB D yw (mkExtB D zD.2)))).re)
    (hppos : 0 < p) (hm : D.card < n) :
    (∑ b : AliceBase n D, AliceBase.β b * ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 * S.alignEntA μ b xw yw zD)
      ≤ p * Real.log (((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card / p) := by
  classical
  -- the flat index, weights and pairings
  set ι := AliceBase n D × (Fin n → X) × (Fin n → Y) ×
    (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) with hι
  set wt : ι → ℝ := fun t => AliceBase.β t.1 *
    ((∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) * w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) with hwt
  set hf : ι → ℝ := fun t => (S.M.τ (star S.σ *
    (S.setEffectA D t.1.SA μ t.2.1 t.2.2.1 (mkExtA D t.2.2.2.1) * S.σ *
      S.setEffectB D t.1.SB μ t.2.1 t.2.2.1 (mkExtB D t.2.2.2.2)))).re with hhf
  set N : ℝ := ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card with hN
  have hwt0 : ∀ t, 0 ≤ wt t := fun t =>
    mul_nonneg (AliceBase.β_nonneg _)
      (mul_nonneg (Finset.prod_nonneg fun j _ => hμ _ _) (hw0 _ _ _ _))
  have hhf0 : ∀ t, 0 ≤ hf t := fun t =>
    S.M.pairing_nonneg S.σ (S.setEffectA_isPosElem D _ μ hμ _ _ _)
      (S.setEffectB_isPosElem D _ μ hμ _ _ _)
  -- the weighted pairings sum to p
  have hpsum : (∑ t : ι, wt t * hf t) = p := by
    have := sum_base_reshape μ w (fun b xw yw zD => (S.M.τ (star S.σ *
      (S.setEffectA D b.SA μ xw yw (mkExtA D zD.1) * S.σ *
        S.setEffectB D b.SB μ xw yw (mkExtB D zD.2)))).re)
    simp only [hwt, hhf]
    rw [this]
    have hcoll : ∀ b : AliceBase n D,
        (∑ xw : Fin n → X, ∑ yw : Fin n → Y, (∏ j : Fin n, μ (xw j) (yw j)) *
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            w xw yw zD.1 zD.2 * (S.M.τ (star S.σ *
              (S.setEffectA D b.SA μ xw yw (mkExtA D zD.1) * S.σ *
                S.setEffectB D b.SB μ xw yw (mkExtB D zD.2)))).re) = p := by
      intro b
      rw [hp]
      exact S.sum_pairing_eq_coreMass μ hμ w hwD b.SA b.SB b.core_subset_SA b.core_subset_SB
        b.SA_union_SB
    rw [Finset.sum_congr rfl fun b _ => by rw [hcoll b], ← Finset.sum_mul,
      AliceBase.sum_β D hm, one_mul]
  -- the total weight is at most N
  have hWle : (∑ t : ι, wt t) ≤ N := by
    have := sum_base_reshape μ w (fun _ _ _ _ => (1 : ℝ))
    simp only [mul_one] at this
    simp only [hwt]
    rw [this]
    calc (∑ b : AliceBase n D, AliceBase.β b * ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) *
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              w xw yw zD.1 zD.2)
        ≤ ∑ b : AliceBase n D, AliceBase.β b * N :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (sum_prior_weight_le μ hμ hμsum w hw1) (AliceBase.β_nonneg b)
      _ = N := by rw [← Finset.sum_mul, AliceBase.sum_β D hm, one_mul]
  -- positivity of the total weight
  have hW : 0 < ∑ t : ι, wt t := by
    rcases (Finset.sum_nonneg fun t _ => hwt0 t).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => hwt0 t).mp h.symm
      have : (∑ t : ι, wt t * hf t) = 0 :=
        Finset.sum_eq_zero fun t _ => by rw [hz t (Finset.mem_univ t), zero_mul]
      rw [hpsum] at this
      exact hppos.ne' this
  have hent := finite_weighted_entropy_le_of_weight_bound Finset.univ wt hf
    (fun t _ => hwt0 t) (fun t _ => hhf0 t) hW hppos rfl hpsum hWle
  have hreshape := sum_base_reshape μ w (fun b xw yw zD => S.alignEntA μ b xw yw zD)
  rw [← hreshape]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun t _ => ?_) hent
  simp only [hwt, hhf, alignEntA]

/-! ### The Alice conjunct -/

/-- **The prior Alice alignment cost is at most `2p(t₀ + s₀)/m`** (node 1.2.9,
eqs IA-size-bias-calculation, prior-alignment-bound; the body of `alignCostA`
with the canonical labels `mkALabel`/`mkBLabel`). -/
theorem alignSumA_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s, (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (hcol : R.ColEntropyBudget)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hw1 : ∀ xw yw zA zB, w xw yw zA zB ≤ 1)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    {p : ℝ}
    (hp : p = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
      (∏ j : Fin n, μ (xw j) (yw j)) *
        ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
          w xw yw zD.1 zD.2 *
            (S.M.τ (star S.σ *
              (S.coreEffectA D xw (mkExtA D zD.1) * S.σ *
                S.coreEffectB D yw (mkExtB D zD.2)))).re)
    (hppos : 0 < p) (hm : D.card < n) :
    (∑ r : RevealDatum n D, r.revealLaw *
      ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
        (∏ j : Fin n, μ (xw j) (yw j)) *
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            w xw yw zD.1 zD.2 *
              ‖R.branch S.σ (mkALabel D (insert r.i r.CX) xw yw zD.1)
                  (mkBLabel D (insert r.i r.CY) xw yw zD.2)
                - R.branch S.σ (mkALabel D r.CX xw yw zD.1)
                    (mkBLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2)
      ≤ 2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) /
        ((n : ℝ) - D.card) := by
  classical
  obtain ⟨e, hlaw, hwire⟩ := aliceReveal_pushforward_strong n D
  set Φ : RevealDatum n D → ℝ := fun r => ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
    (∏ j : Fin n, μ (xw j) (yw j)) *
      ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        w xw yw zD.1 zD.2 *
          ‖R.branch S.σ (mkALabel D (insert r.i r.CX) xw yw zD.1)
              (mkBLabel D (insert r.i r.CY) xw yw zD.2)
            - R.branch S.σ (mkALabel D r.CX xw yw zD.1)
                (mkBLabel D (insert r.i r.CY) xw yw zD.2)‖ ^ 2 with hΦ
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  -- per (base, cut): the integrand in scenario form
  have hΦ' : ∀ (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card),
      Φ (e (mkAliceDatum b k)) = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
        (∏ j : Fin n, μ (xw j) (yw j)) *
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            w xw yw zD.1 zD.2 * S.alignIncA R b k xw yw zD := by
    intro b k
    obtain ⟨hi, hLX, hLY, -, -, hpre, hpx⟩ := hwire (mkAliceDatum b k)
    simp only [hΦ, alignIncA]
    rw [(e (mkAliceDatum b k)).insert_CX_of_alice b k hi hLX hpre,
      (e (mkAliceDatum b k)).CX_of_alice b k hLX hpre,
      (e (mkAliceDatum b k)).insert_CY_of_alice b k hi hLY hpx]
  have hN0 : ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card ≠ 0 := by
    have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
    positivity
  calc (∑ r : RevealDatum n D, r.revealLaw * Φ r)
      = ∑ d : AliceRevealDatum n D, (e d).revealLaw * Φ (e d) :=
        (Equiv.sum_comp e fun r => r.revealLaw * Φ r).symm
    _ = ∑ t : Σ b : AliceBase n D, Fin (Dᶜ \ b.1.1).card,
          (e (aliceSigmaEquiv D t)).revealLaw * Φ (e (aliceSigmaEquiv D t)) :=
        (Fintype.sum_equiv (aliceSigmaEquiv D) _ _ fun t => rfl).symm
    _ = ∑ b : AliceBase n D, ∑ k : Fin (Dᶜ \ b.1.1).card,
          (2 / m * AliceBase.β b) * ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignIncA R b k xw yw zD := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
        show (e (mkAliceDatum b k)).revealLaw * Φ (e (mkAliceDatum b k)) = _
        rw [← hlaw, mkAliceDatum_law hm, hΦ']
    _ = ∑ b : AliceBase n D, (2 / m * AliceBase.β b) *
          ∑ k : Fin (Dᶜ \ b.1.1).card, ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignIncA R b k xw yw zD :=
        Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ b : AliceBase n D, (2 / m * AliceBase.β b) *
          ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignEntA μ b xw yw zD :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
          (S.cutSumA_le μ hμ R hcol htotF htotG w hw0 hwD b)
          (mul_nonneg (by positivity) (AliceBase.β_nonneg b))
    _ = 2 / m * ∑ b : AliceBase n D, AliceBase.β b *
          ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignEntA μ b xw yw zD := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ 2 / m * (p * Real.log (((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card / p)) :=
        mul_le_mul_of_nonneg_left
          (S.sizeBiasA μ hμ hμsum w hw0 hw1 hwD hp hppos hm) (by positivity)
    _ = 2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card) := by
        rw [Real.log_div hN0 hppos.ne', Real.log_pow, Real.log_inv, hmdef,
          Nat.cast_sub hm.le]
        ring

end TracialStrategy

end CommutingRepetition
