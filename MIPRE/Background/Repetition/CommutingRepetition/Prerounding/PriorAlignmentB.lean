/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Prerounding/PriorAlignmentB.lean
-/
/-
# Pre-rounding: the prior alignment bound, Bob side (node 1.2.9)

The mirror of `Prerounding/PriorAlignment.lean` for the Bob alignment cost `I_B`
(05_prerounding.tex, eq prior-alignment-bound, "the same calculation with `N_B`,
`G_{j,z}`, and the Bob functional"). The Bob reverse datum
(`BobRevealDatum`: Alice block `L_X⁺` carrying the reveal order and the interior
cut, Bob block `L_Y` with the forward order and cut) has exactly the shape of the
Alice base with the roles of the two blocks exchanged, so the same base type
`AliceBase` is reused: `b.1.1` is now the Bob block `L_Y`, `Dᶜ \ b.1.1` the Alice
block `L_X⁺`, `b.2.1` the forward order `π_Y`, `b.2.2.1` the reverse order
`π_X`, `b.2.2.2` the forward cut `k_Y`; Bob's background is `b.SA = D ∪ L_Y` and
Alice's fixed revealed set is `b.SB = D ∪ L_X⁺ ∪ π_Y^{≤ k_Y}`.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Prerounding.PriorAlignment

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

variable {n : ℕ} {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]

/-! ### The Bob reverse datum as (base, interior cut) -/

/-- The Bob reverse datum with base `b` (Bob block `b.1.1`) and interior cut `k`
in the Alice block. -/
def mkBobDatum {D : Finset (Fin n)} (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    BobRevealDatum n D where
  LXp := Dᶜ \ b.1.1
  LY := b.1.1
  disjoint := Finset.sdiff_disjoint
  partition := Finset.sdiff_union_of_subset b.1.2
  πX := b.2.2.1
  πY := b.2.1
  kX := k
  kY := b.2.2.2

theorem BobRevealDatum.LY_subset_compl {D : Finset (Fin n)} (d : BobRevealDatum n D) :
    d.LY ⊆ Dᶜ := by
  rw [← d.partition]; exact Finset.subset_union_right

theorem BobRevealDatum.LXp_eq {D : Finset (Fin n)} (d : BobRevealDatum n D) :
    d.LXp = Dᶜ \ d.LY := by
  rw [← d.partition, Finset.union_sdiff_cancel_right d.disjoint]

/-- The (base, cut) presentation of the Bob reverse datum. -/
def bobSigmaEquiv (D : Finset (Fin n)) :
    (Σ b : AliceBase n D, Fin (Dᶜ \ b.1.1).card) ≃ BobRevealDatum n D where
  toFun t := mkBobDatum t.1 t.2
  invFun d := ⟨⟨⟨d.LY, d.LY_subset_compl⟩, (d.πY, d.LXp_eq ▸ d.πX, d.kY)⟩, d.LXp_eq ▸ d.kX⟩
  left_inv := by
    rintro ⟨⟨⟨L, hL⟩, πY, πX, kY⟩, k⟩
    rfl
  right_inv := by
    rintro ⟨LXp, LY, hdisj, hpart, πX, πY, kX, kY⟩
    have e : LXp = Dᶜ \ LY := by
      rw [← hpart, Finset.union_sdiff_cancel_right hdisj]
    subst e
    rfl

/-- The Bob size-biased law in (base, cut) form: `(2/m)·β(base)` (eq
bob-size-biased-partition). -/
theorem mkBobDatum_law {D : Finset (Fin n)} (hm : D.card < n) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) :
    (mkBobDatum b k).law = 2 / ((n - D.card : ℕ) : ℝ) * b.β := by
  have hN : (((Dᶜ \ b.1.1).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fin.pos k).ne'
  have hm' : ((n - D.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hm).ne'
  unfold BobRevealDatum.law AliceBase.β mkBobDatum
  simp only
  field_simp

/-! ### Label identities (mirror) -/

section LabelIdentitiesB

variable {D : Finset (Fin n)}

theorem mkBobDatum_liveIdx (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    (mkBobDatum b k).liveIdx = (b.πY k : Fin n) := rfl

theorem mkBobDatum_revealPrefix (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    (mkBobDatum b k).revealPrefix (mkBobDatum b k).kX.castSucc
      = ordPrefix b.πY (k : ℕ) := rfl

theorem mkBobDatum_bobPrefixY (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card) :
    (mkBobDatum b k).bobPrefixY = ordPrefix b.2.1 (b.2.2.2 : ℕ) := rfl

/-- `C_Y = S_A ∪ π_X^{≤ k_X}` (Bob's background plus the revealed Alice-block
prefix) for the forward datum wired to `(b, k)`. -/
theorem RevealDatum.CY_of_bob (r : RevealDatum n D) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) (hLY : r.LY = (mkBobDatum b k).LY)
    (hpre : r.prefixX = (mkBobDatum b k).revealPrefix (mkBobDatum b k).kX.castSucc) :
    r.CY = b.SA ∪ ordPrefix b.πY (k : ℕ) := by
  show D ∪ r.LY ∪ r.prefixX = _
  rw [hLY, hpre, mkBobDatum_revealPrefix]
  rfl

theorem RevealDatum.insert_CY_of_bob (r : RevealDatum n D) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) (hi : r.i = (mkBobDatum b k).liveIdx)
    (hLY : r.LY = (mkBobDatum b k).LY)
    (hpre : r.prefixX = (mkBobDatum b k).revealPrefix (mkBobDatum b k).kX.castSucc) :
    insert r.i r.CY = insert (b.πY k : Fin n) (b.SA ∪ ordPrefix b.πY (k : ℕ)) := by
  rw [r.CY_of_bob b k hLY hpre, hi, mkBobDatum_liveIdx]

/-- The KEY collapse on the Bob side: `{i} ∪ C_X = D ∪ L_X⁺ ∪ π_Y^{≤ k_Y}`,
independent of the interior cut. -/
theorem RevealDatum.insert_CX_of_bob (r : RevealDatum n D) (b : AliceBase n D)
    (k : Fin (Dᶜ \ b.1.1).card) (hi : r.i = (mkBobDatum b k).liveIdx)
    (hLX : r.LX = (mkBobDatum b k).LXp.erase (mkBobDatum b k).liveIdx)
    (hpy : r.prefixY = (mkBobDatum b k).bobPrefixY) :
    insert r.i r.CX = b.SB := by
  have hCX : r.CX = D ∪ r.LX ∪ r.prefixY := rfl
  rw [hCX, hLX, hpy, hi, mkBobDatum_bobPrefixY, ← Finset.insert_union,
    ← Finset.union_insert, Finset.insert_erase (mkBobDatum b k).liveIdx_mem]
  rfl

end LabelIdentitiesB

/-! ### Unnormalizing the block law (Bob) -/

theorem block_unnormalizeB (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (L : Finset (Fin n)) (xw : Fin n → X) (F : ({j : Fin n // j ∈ L} → Y) → ℝ) (Bnd : ℝ)
    (h : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) ≠ 0 →
      (∑ ω : {j : Fin n // j ∈ L} → Y,
        ((∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) /
          ∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) * F ω) ≤ Bnd) :
    (∑ ω : {j : Fin n // j ∈ L} → Y, (∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) * F ω)
      ≤ (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) * Bnd := by
  classical
  by_cases hM : (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) = 0
  · have hzero : ∀ ω : {j : Fin n // j ∈ L} → Y,
        (∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) = 0 := by
      intro ω
      obtain ⟨c, -, hc⟩ := Finset.prod_eq_zero_iff.mp hM
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hμ (xw c) v).mp hc
      exact Finset.prod_eq_zero (Finset.mem_univ c) (hall (ω c) (Finset.mem_univ _))
    rw [hM, zero_mul]
    apply le_of_eq
    exact Finset.sum_eq_zero fun ω _ => by rw [hzero ω, zero_mul]
  · have hM0 : 0 ≤ ∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v :=
      Finset.prod_nonneg fun c _ => Finset.sum_nonneg fun v _ => hμ (xw c) v
    calc (∑ ω : {j : Fin n // j ∈ L} → Y, (∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) * F ω)
        = (∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) *
            ∑ ω : {j : Fin n // j ∈ L} → Y,
              ((∏ c : {j : Fin n // j ∈ L}, μ (xw c) (ω c)) /
                ∏ c : {j : Fin n // j ∈ L}, ∑ v : Y, μ (xw c) v) * F ω := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [← mul_assoc, mul_div_cancel₀ _ hM]
      _ ≤ _ := mul_le_mul_of_nonneg_left (h hM) hM0

/-- Split a Bob word sum at a block and put the off-block values outside. -/
theorem sum_split_commY (L : Finset (Fin n)) (F : (Fin n → Y) → ℝ) :
    (∑ yw : Fin n → Y, F yw)
      = ∑ g : {j : Fin n // ¬ j ∈ L} → Y, ∑ ω : {j : Fin n // j ∈ L} → Y,
          F ((wordSplit L Y).symm (ω, g)) := by
  rw [sum_wordSplit L F]
  exact Finset.sum_comm

/-- The Bob-side rearrangements: the cut index outermost and the Alice word
innermost. -/
theorem sum4_rearrangeB {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (Q : β → γ → ℝ) (w : β → γ → δ → ℝ) (X : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, Q b c * ∑ d, w b c d * X a b c d)
      = ∑ b, ∑ d, ∑ c, Q b c * (w b c d * ∑ a, X a b c d) := by
  simp only [Finset.mul_sum]
  calc (∑ a, ∑ b, ∑ c, ∑ d, Q b c * (w b c d * X a b c d))
      = ∑ b, ∑ a, ∑ c, ∑ d, Q b c * (w b c d * X a b c d) := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ d, ∑ c, Q b c * (w b c d * X a b c d) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ a, ∑ c, Q b c * (w b c d * X a b c d) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, ∑ a, Q b c * (w b c d * X a b c d) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm

theorem sum3_rearrangeB {β γ δ : Type} [Fintype β] [Fintype γ] [Fintype δ]
    (Q : β → γ → ℝ) (w : β → γ → δ → ℝ) (Y : β → γ → δ → ℝ) :
    (∑ b, ∑ c, Q b c * ∑ d, w b c d * Y b c d)
      = ∑ b, ∑ d, ∑ c, Q b c * (w b c d * Y b c d) := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

namespace TracialStrategy

variable (S : TracialStrategy.{0}
  (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B))
variable {D : Finset (Fin n)}
variable {Af Bf : Type} [Fintype Af] [Fintype Bf]

/-! ### The per-base telescoping bound (Bob) -/

/-- The Bob alignment increment at base `b` and interior cut `k`: Alice's label is
fixed at `S_B = D ∪ L_X⁺ ∪ π_Y^{≤k_Y}`, Bob's grows from `S_A ∪ π_X^{≤k}` to
`{π_X(k)} ∪ S_A ∪ π_X^{≤k}`. -/
noncomputable def alignIncB
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) : ℝ :=
  ‖R.branch S.σ (mkALabel D b.SB xw yw zD.1)
      (mkBLabel D (insert (b.πY k : Fin n) (b.SA ∪ ordPrefix b.πY (k : ℕ))) xw yw zD.2)
    - R.branch S.σ (mkALabel D b.SB xw yw zD.1)
        (mkBLabel D (b.SA ∪ ordPrefix b.πY (k : ℕ)) xw yw zD.2)‖ ^ 2

/-- The initial-pairing entropy on the Bob side: Alice at `S_B`, Bob at `S_A`. -/
noncomputable def alignEntB (μ : X → Y → ℝ) (b : AliceBase n D)
    (xw : Fin n → X) (yw : Fin n → Y)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) : ℝ :=
  Real.negMulLog (S.M.τ (star S.σ *
    (S.setEffectA D b.SB μ xw yw (mkExtA D zD.1) * S.σ *
      S.setEffectB D b.SA μ xw yw (mkExtB D zD.2)))).re

/-- **Block bound at a fixed Bob background** (mirror of `cutSumA_block_le`, via
`scenMartB_rowBudget_mkBLabel`). -/
theorem cutSumB_block_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hrow : R.RowEntropyBudget)
    (htotF : ∀ s, (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (w : (Fin n → X) → (Fin n → Y) →
      ({j : Fin n // j ∈ D} → A) → ({j : Fin n // j ∈ D} → B) → ℝ)
    (hw0 : ∀ xw yw zA zB, 0 ≤ w xw yw zA zB)
    (hwD : ∀ (xw xw' : Fin n → X) (yw yw' : Fin n → Y) zA zB,
      agreesOn D xw xw' → agreesOn D yw yw' →
      w xw yw zA zB = w xw' yw' zA zB)
    (b : AliceBase n D) (xw : Fin n → X)
    (zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B))
    (g : {j : Fin n // ¬ j ∈ b.LYp} → Y) :
    (∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
      (∏ j : Fin n, μ (xw j) ((wordSplit b.LYp Y).symm (ω, g) j)) *
        (w xw ((wordSplit b.LYp Y).symm (ω, g)) zD.1 zD.2 *
          ∑ k : Fin (Dᶜ \ b.1.1).card,
            S.alignIncB R b k xw ((wordSplit b.LYp Y).symm (ω, g)) zD))
      ≤ ∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
          (∏ j : Fin n, μ (xw j) ((wordSplit b.LYp Y).symm (ω, g) j)) *
            (w xw ((wordSplit b.LYp Y).symm (ω, g)) zD.1 zD.2 *
              S.alignEntB μ b xw ((wordSplit b.LYp Y).symm (ω, g)) zD) := by
  classical
  set ω₀ : {j : Fin n // j ∈ b.LYp} → Y := fun _ => Classical.arbitrary Y with hω₀
  set yw₀ : Fin n → Y := (wordSplit b.LYp Y).symm (ω₀, g) with hyw₀
  have hLsub : b.LYp ⊆ Dᶜ := Finset.sdiff_subset
  have hoff : ∀ (ω : {j : Fin n // j ∈ b.LYp} → Y) (j : Fin n), j ∉ b.LYp →
      (wordSplit b.LYp Y).symm (ω, g) j = yw₀ j := by
    intro ω j hj
    rw [hyw₀, wordSplit_symm_notMem b.LYp Y ω g hj, wordSplit_symm_notMem b.LYp Y ω₀ g hj]
  have hw : ∀ ω : {j : Fin n // j ∈ b.LYp} → Y,
      w xw ((wordSplit b.LYp Y).symm (ω, g)) zD.1 zD.2 = w xw yw₀ zD.1 zD.2 := by
    intro ω
    refine hwD xw xw _ _ zD.1 zD.2 (fun _ _ => rfl) fun j hj => hoff ω j ?_
    intro hjL
    exact (Finset.mem_compl.mp (hLsub hjL)) hj
  have hI : ∀ ω : {j : Fin n // j ∈ b.LYp} → Y,
      mkALabel D b.SB xw ((wordSplit b.LYp Y).symm (ω, g)) zD.1
        = mkALabel D b.SB xw yw₀ zD.1 := by
    intro ω
    refine mkALabel_congr D b.SB zD.1 (fun _ _ => rfl) fun j hj => hoff ω j ?_
    intro hjL
    exact hj (b.LYp_subset_SB hjL)
  have hEnt : ∀ ω : {j : Fin n // j ∈ b.LYp} → Y,
      S.alignEntB μ b xw ((wordSplit b.LYp Y).symm (ω, g)) zD
        = S.alignEntB μ b xw yw₀ zD := by
    intro ω
    unfold alignEntB
    rw [S.setEffectA_congr D b.SB μ (mkExtA D zD.1) (fun _ _ => rfl)
        (fun j hj => hoff ω j ?_),
      S.setEffectB_congr D b.SA μ (mkExtB D zD.2) (fun _ _ => rfl)
        (fun j hj => hoff ω j ?_)]
    · intro hjL
      exact Finset.disjoint_left.mp b.disjoint_SA_LYp hj hjL
    · intro hjL
      exact hj (b.LYp_subset_SB hjL)
  have hQ : ∀ ω : {j : Fin n // j ∈ b.LYp} → Y,
      (∏ j : Fin n, μ (xw j) ((wordSplit b.LYp Y).symm (ω, g) j))
        = (∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) *
          ∏ c : {j : Fin n // ¬ j ∈ b.LYp}, μ (xw c) (g c) :=
    fun ω => prod_mu_wordSplit' b.LYp μ xw ω g
  set M₀ : ℝ := ∏ c : {j : Fin n // j ∈ b.LYp}, ∑ v : Y, μ (xw c) v with hM₀
  set Goff : ℝ := ∏ c : {j : Fin n // ¬ j ∈ b.LYp}, μ (xw c) (g c) with hGoff
  have hGoff0 : 0 ≤ Goff := Finset.prod_nonneg fun c _ => hμ _ _
  have hw0' : 0 ≤ Goff * w xw yw₀ zD.1 zD.2 := mul_nonneg hGoff0 (hw0 _ _ _ _)
  set I₀ := mkALabel D b.SB xw yw₀ zD.1 with hI₀
  set Δ : Fin (Dᶜ \ b.1.1).card → ({j : Fin n // j ∈ b.LYp} → Y) → ℝ := fun k ω =>
    ‖R.branch S.σ I₀
        (mkBLabel D (insert (b.πY k : Fin n) (b.SA ∪ ordPrefix b.πY (k : ℕ)))
          xw ((wordSplit b.LYp Y).symm (ω, g)) zD.2)
      - R.branch S.σ I₀ (mkBLabel D (b.SA ∪ ordPrefix b.πY (k : ℕ))
          xw ((wordSplit b.LYp Y).symm (ω, g)) zD.2)‖ ^ 2 with hΔ
  have hInc : ∀ (ω : {j : Fin n // j ∈ b.LYp} → Y) (k : Fin (Dᶜ \ b.1.1).card),
      S.alignIncB R b k xw ((wordSplit b.LYp Y).symm (ω, g)) zD = Δ k ω := by
    intro ω k
    simp only [alignIncB, hΔ, hI ω]
  have hBnd : Real.negMulLog (S.M.τ (star S.σ *
      ((∑ a : Af, Ffam I₀ a) * S.σ *
        (∑ c : Bf, Gfam (mkBLabel D b.SA xw yw₀ zD.2) c)))).re
        = S.alignEntB μ b xw yw₀ zD := by
    unfold alignEntB
    rw [htotF, htotG, hI₀]
    simp only [mkALabel, mkBLabel]
    rw [S.setEffectA_canon, S.setEffectB_canon]
  have hblock : (∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
      (∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) * ∑ k, Δ k ω)
        ≤ M₀ * S.alignEntB μ b xw yw₀ zD := by
    rw [← hBnd]
    refine block_unnormalizeB μ hμ b.LYp xw (fun ω => ∑ k, Δ k ω) _ fun hM => ?_
    have key := S.scenMartB_rowBudget_mkBLabel μ hμ R hrow htotG b.SA b.LYp
      b.disjoint_SA_LYp b.πY xw g zD.2 hM S.σ S.σ_normalized I₀ ω₀
    calc (∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
          ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) / M₀) * ∑ k, Δ k ω)
        = ∑ k, ∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
            ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) / M₀) * Δ k ω := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ _ := key
  have hsumM : (∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
      ∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) = M₀ :=
    sum_prod_pi_subtype b.LYp fun c v => μ (xw c) v
  calc (∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
        (∏ j : Fin n, μ (xw j) ((wordSplit b.LYp Y).symm (ω, g) j)) *
          (w xw ((wordSplit b.LYp Y).symm (ω, g)) zD.1 zD.2 *
            ∑ k : Fin (Dᶜ \ b.1.1).card,
              S.alignIncB R b k xw ((wordSplit b.LYp Y).symm (ω, g)) zD))
      = ∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
          ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) * Goff) *
            (w xw yw₀ zD.1 zD.2 * ∑ k, Δ k ω) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hQ ω, hw ω]
        congr 2
        exact Finset.sum_congr rfl fun k _ => hInc ω k
    _ = (Goff * w xw yw₀ zD.1 zD.2) *
          ∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
            (∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) * ∑ k, Δ k ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ (Goff * w xw yw₀ zD.1 zD.2) * (M₀ * S.alignEntB μ b xw yw₀ zD) :=
        mul_le_mul_of_nonneg_left hblock hw0'
    _ = (Goff * w xw yw₀ zD.1 zD.2 * S.alignEntB μ b xw yw₀ zD) *
          ∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
            ∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c) := by
        rw [hsumM]; ring
    _ = ∑ ω : {j : Fin n // j ∈ b.LYp} → Y,
          ((∏ c : {j : Fin n // j ∈ b.LYp}, μ (xw c) (ω c)) * Goff) *
            (w xw yw₀ zD.1 zD.2 * S.alignEntB μ b xw yw₀ zD) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hQ ω, hw ω, hEnt ω]

/-- **Per-base telescoped bound, Bob side** (mirror of `cutSumA_le`). -/
theorem cutSumB_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam) (hrow : R.RowEntropyBudget)
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
          w xw yw zD.1 zD.2 * S.alignIncB R b k xw yw zD)
      ≤ ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
          (∏ j : Fin n, μ (xw j) (yw j)) *
            ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
              w xw yw zD.1 zD.2 * S.alignEntB μ b xw yw zD := by
  rw [sum4_rearrangeB (fun xw yw => ∏ j : Fin n, μ (xw j) (yw j))
      (fun xw yw zD => w xw yw zD.1 zD.2) (fun k xw yw zD => S.alignIncB R b k xw yw zD),
    sum3_rearrangeB (fun xw yw => ∏ j : Fin n, μ (xw j) (yw j))
      (fun xw yw zD => w xw yw zD.1 zD.2) (fun xw yw zD => S.alignEntB μ b xw yw zD)]
  refine Finset.sum_le_sum fun xw _ => Finset.sum_le_sum fun zD _ => ?_
  rw [sum_split_commY b.LYp, sum_split_commY b.LYp]
  exact Finset.sum_le_sum fun g _ =>
    S.cutSumB_block_le μ hμ R hrow htotF htotG w hw0 hwD b xw zD g

/-! ### The size-bias entropy step (Bob) -/

/-- **The size-bias entropy bound, Bob side** (mirror of `sizeBiasA`; the pairing
is Alice at `S_B`, Bob at `S_A`, again a covering pair containing the core). -/
theorem sizeBiasB (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
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
          w xw yw zD.1 zD.2 * S.alignEntB μ b xw yw zD)
      ≤ p * Real.log (((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card / p) := by
  classical
  set ι := AliceBase n D × (Fin n → X) × (Fin n → Y) ×
    (({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B)) with hι
  set wt : ι → ℝ := fun t => AliceBase.β t.1 *
    ((∏ j : Fin n, μ (t.2.1 j) (t.2.2.1 j)) * w t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) with hwt
  set hf : ι → ℝ := fun t => (S.M.τ (star S.σ *
    (S.setEffectA D t.1.SB μ t.2.1 t.2.2.1 (mkExtA D t.2.2.2.1) * S.σ *
      S.setEffectB D t.1.SA μ t.2.1 t.2.2.1 (mkExtB D t.2.2.2.2)))).re with hhf
  set N : ℝ := ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card with hN
  have hwt0 : ∀ t, 0 ≤ wt t := fun t =>
    mul_nonneg (AliceBase.β_nonneg _)
      (mul_nonneg (Finset.prod_nonneg fun j _ => hμ _ _) (hw0 _ _ _ _))
  have hhf0 : ∀ t, 0 ≤ hf t := fun t =>
    S.M.pairing_nonneg S.σ (S.setEffectA_isPosElem D _ μ hμ _ _ _)
      (S.setEffectB_isPosElem D _ μ hμ _ _ _)
  have hpsum : (∑ t : ι, wt t * hf t) = p := by
    have := sum_base_reshape μ w (fun b xw yw zD => (S.M.τ (star S.σ *
      (S.setEffectA D b.SB μ xw yw (mkExtA D zD.1) * S.σ *
        S.setEffectB D b.SA μ xw yw (mkExtB D zD.2)))).re)
    simp only [hwt, hhf]
    rw [this]
    have hcoll : ∀ b : AliceBase n D,
        (∑ xw : Fin n → X, ∑ yw : Fin n → Y, (∏ j : Fin n, μ (xw j) (yw j)) *
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            w xw yw zD.1 zD.2 * (S.M.τ (star S.σ *
              (S.setEffectA D b.SB μ xw yw (mkExtA D zD.1) * S.σ *
                S.setEffectB D b.SA μ xw yw (mkExtB D zD.2)))).re) = p := by
      intro b
      rw [hp]
      exact S.sum_pairing_eq_coreMass μ hμ w hwD b.SB b.SA b.core_subset_SB b.core_subset_SA
        (by rw [Finset.union_comm]; exact b.SA_union_SB)
    rw [Finset.sum_congr rfl fun b _ => by rw [hcoll b], ← Finset.sum_mul,
      AliceBase.sum_β D hm, one_mul]
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
  have hreshape := sum_base_reshape μ w (fun b xw yw zD => S.alignEntB μ b xw yw zD)
  rw [← hreshape]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun t _ => ?_) hent
  simp only [hwt, hhf, alignEntB]

/-! ### The Bob conjunct -/

/-- **The prior Bob alignment cost is at most `2p(t₀ + s₀)/m`** (node 1.2.9, eq
prior-alignment-bound, second conjunct; the body of `alignCostB` with the
canonical labels). -/
theorem alignSumB_le (μ : X → Y → ℝ) (hμ : ∀ x y, 0 ≤ μ x y)
    (hμsum : (∑ x : X, ∑ y : Y, μ x y) = 1)
    {Ffam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → A)) → Af → S.M.A}
    {Gfam : (Finset (Fin n) × (Fin n → X) × (Fin n → Y) × (Fin n → B)) → Bf → S.M.A}
    (R : ResolverArena S.M Ffam Gfam)
    (htotF : ∀ s, (∑ a : Af, Ffam s a) = S.setEffectA D s.1 μ s.2.1 s.2.2.1 s.2.2.2)
    (htotG : ∀ t, (∑ b : Bf, Gfam t b) = S.setEffectB D t.1 μ t.2.1 t.2.2.1 t.2.2.2)
    (hrow : R.RowEntropyBudget)
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
                - R.branch S.σ (mkALabel D (insert r.i r.CX) xw yw zD.1)
                    (mkBLabel D r.CY xw yw zD.2)‖ ^ 2)
      ≤ 2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) /
        ((n : ℝ) - D.card) := by
  classical
  obtain ⟨e, hlaw, hwire⟩ := bobReveal_pushforward_strong n D
  set Φ : RevealDatum n D → ℝ := fun r => ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
    (∏ j : Fin n, μ (xw j) (yw j)) *
      ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
        w xw yw zD.1 zD.2 *
          ‖R.branch S.σ (mkALabel D (insert r.i r.CX) xw yw zD.1)
              (mkBLabel D (insert r.i r.CY) xw yw zD.2)
            - R.branch S.σ (mkALabel D (insert r.i r.CX) xw yw zD.1)
                (mkBLabel D r.CY xw yw zD.2)‖ ^ 2 with hΦ
  set m : ℝ := ((n - D.card : ℕ) : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast Nat.sub_pos_of_lt hm
  have hΦ' : ∀ (b : AliceBase n D) (k : Fin (Dᶜ \ b.1.1).card),
      Φ (e (mkBobDatum b k)) = ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
        (∏ j : Fin n, μ (xw j) (yw j)) *
          ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
            w xw yw zD.1 zD.2 * S.alignIncB R b k xw yw zD := by
    intro b k
    obtain ⟨hi, hLY, hLX, -, -, hpre, hpy⟩ := hwire (mkBobDatum b k)
    simp only [hΦ, alignIncB]
    rw [(e (mkBobDatum b k)).insert_CY_of_bob b k hi hLY hpre,
      (e (mkBobDatum b k)).CY_of_bob b k hLY hpre,
      (e (mkBobDatum b k)).insert_CX_of_bob b k hi hLX hpy]
  have hN0 : ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card ≠ 0 := by
    have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
    positivity
  calc (∑ r : RevealDatum n D, r.revealLaw * Φ r)
      = ∑ d : BobRevealDatum n D, (e d).revealLaw * Φ (e d) :=
        (Equiv.sum_comp e fun r => r.revealLaw * Φ r).symm
    _ = ∑ t : Σ b : AliceBase n D, Fin (Dᶜ \ b.1.1).card,
          (e (bobSigmaEquiv D t)).revealLaw * Φ (e (bobSigmaEquiv D t)) :=
        (Fintype.sum_equiv (bobSigmaEquiv D) _ _ fun t => rfl).symm
    _ = ∑ b : AliceBase n D, ∑ k : Fin (Dᶜ \ b.1.1).card,
          (2 / m * AliceBase.β b) * ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignIncB R b k xw yw zD := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
        show (e (mkBobDatum b k)).revealLaw * Φ (e (mkBobDatum b k)) = _
        rw [← hlaw, mkBobDatum_law hm, hΦ']
    _ = ∑ b : AliceBase n D, (2 / m * AliceBase.β b) *
          ∑ k : Fin (Dᶜ \ b.1.1).card, ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignIncB R b k xw yw zD :=
        Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ b : AliceBase n D, (2 / m * AliceBase.β b) *
          ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignEntB μ b xw yw zD :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
          (S.cutSumB_le μ hμ R hrow htotF htotG w hw0 hwD b)
          (mul_nonneg (by positivity) (AliceBase.β_nonneg b))
    _ = 2 / m * ∑ b : AliceBase n D, AliceBase.β b *
          ∑ xw : Fin n → X, ∑ yw : Fin n → Y,
            (∏ j : Fin n, μ (xw j) (yw j)) *
              ∑ zD : ({j : Fin n // j ∈ D} → A) × ({j : Fin n // j ∈ D} → B),
                w xw yw zD.1 zD.2 * S.alignEntB μ b xw yw zD := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ 2 / m * (p * Real.log (((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) ^ D.card / p)) :=
        mul_le_mul_of_nonneg_left
          (S.sizeBiasB μ hμ hμsum w hw0 hw1 hwD hp hppos hm) (by positivity)
    _ = 2 * p * (Real.log p⁻¹ + (D.card : ℝ) *
          Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) / ((n : ℝ) - D.card) := by
        rw [Real.log_div hN0 hppos.ne', Real.log_pow, Real.log_inv, hmdef,
          Nat.cast_sub hm.le]
        ring

end TracialStrategy

end CommutingRepetition
