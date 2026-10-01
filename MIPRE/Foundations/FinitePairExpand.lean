/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.FinitePair
public import MIPRE.Foundations.AmplCommutant

@[expose] public section

/-!
# Finite pairs are closed under ancilla extensions and under the exchange of the players

The Pauli basis analysis applies the low-individual-degree hypothesis in the ancilla extensions
`M.expand e` of the model it works in (`QLD.soundIn_of_lidt`), and the answer-reduction and Pauli
basis analyses are stated for both orders of the players. So the class of finite pairs
(`MIPRE/Foundations/FinitePair.lean`) has to be closed under both, which this file shows
(`lem:finite-pair-expand`).

* **Extensions.** The players' operators of `M.expand e` are `X ⊗ 1_β` and `1_α ⊗ Y` for matrices
  `X` over `𝒜` and `Y` over `ℬ`. An operator commuting with every `1_α ⊗ Y` commutes with the
  register's matrix units and with `f ⊗ 1` for every operator `f` of the second player, so it is
  `X ⊗ 1_β` with entries in the commutant of the second player's operators
  (`OperatorMatrix.exists_eq_toCLM_liftLeft`), which are the first player's; and symmetrically.
  The trace of the first player's algebra is the normalized trace of the matrices,
  `τ'(X ⊗ 1) = |α × β|⁻¹ ∑ₚ τ((X ⊗ 1)ₚₚ) = |α|⁻¹ ∑ᵢ τ(Xᵢᵢ)`, given by the vectors
  `|α × β|^{-1/2} gₖ ⊗ eₚ` (`VecTrace.ampl`); it is tracial because `τ` is, and faithful because
  the vectors of `τ` separate the entries.
* **The exchange of the players** swaps the two conditions.
-/

namespace MIPRE

open scoped InnerProductSpace
open Matrix OperatorMatrix

/-! ## Faithful tracial states on matrices of operators -/

namespace VecTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A faithful tracial state given by vectors indexed by any finite type, numbered. -/
noncomputable def ofFintype {s : Set (H →L[ℂ] H)} {κ : Type*} [Fintype κ] (g : κ → H)
    (norm_sq_sum : ∑ k, ‖g k‖ ^ 2 = 1)
    (trace_mul_comm : ∀ x ∈ s, ∀ y ∈ s,
      ∑ k, ⟪g k, (x * y) (g k)⟫_ℂ = ∑ k, ⟪g k, (y * x) (g k)⟫_ℂ)
    (separating : ∀ x ∈ s, (∀ k, x (g k) = 0) → x = 0) : VecTrace s where
  n := Fintype.card κ
  g := g ∘ (Fintype.equivFin κ).symm
  norm_sq_sum := ((Fintype.equivFin κ).symm.sum_comp fun k => ‖g k‖ ^ 2).trans norm_sq_sum
  trace_mul_comm x hx y hy :=
    ((Fintype.equivFin κ).symm.sum_comp fun k => ⟪g k, (x * y) (g k)⟫_ℂ).trans <|
      (trace_mul_comm x hx y hy).trans
        ((Fintype.equivFin κ).symm.sum_comp fun k => ⟪g k, (y * x) (g k)⟫_ℂ).symm
  separating x hx h := separating x hx fun k => by
    simpa using h (Fintype.equivFin κ k)

/-- A faithful tracial state on a set is one on each of its subsets. -/
def mono {s t : Set (H →L[ℂ] H)} (τ : VecTrace t) (h : s ⊆ t) : VecTrace s where
  n := τ.n
  g := τ.g
  norm_sq_sum := τ.norm_sq_sum
  trace_mul_comm x hx y hy := τ.trace_mul_comm x (h hx) y (h hy)
  separating x hx := τ.separating x (h hx)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vectors of the amplified state: `|ι|^{-1/2} gₖ ⊗ eₚ`. -/
noncomputable def amplVec {s : Set (H →L[ℂ] H)} (τ : VecTrace s) (m : Fin τ.n × ι) :
    Ampl ι H :=
  ((√((Fintype.card ι : ℝ)⁻¹) : ℝ) : ℂ) • emb m.2 (τ.g m.1)

/-- The amplified state of the operator of a matrix is the normalized trace of the matrix,
`|ι|⁻¹ ∑ₚ τ(Zₚₚ)`. -/
theorem sum_inner_amplVec {s : Set (H →L[ℂ] H)} (τ : VecTrace s)
    (Z : Matrix ι ι (H →L[ℂ] H)) :
    ∑ m, ⟪τ.amplVec m, toCLM Z (τ.amplVec m)⟫_ℂ =
      (Fintype.card ι : ℂ)⁻¹ * ∑ p, ∑ k, ⟪τ.g k, Z p p (τ.g k)⟫_ℂ := by
  have hc : ((√((Fintype.card ι : ℝ)⁻¹) : ℝ) : ℂ) * ((√((Fintype.card ι : ℝ)⁻¹) : ℝ) : ℂ) =
      (Fintype.card ι : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (inv_nonneg.2 (Nat.cast_nonneg _)),
      Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [amplVec, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, hc,
    inner_emb_toCLM_emb]

omit [DecidableEq ι] in
/-- The normalized trace of a product of matrices over `s` is tracial when `τ` is. -/
theorem sum_trace_mul_comm {s : Set (H →L[ℂ] H)} (τ : VecTrace s)
    {Z W : Matrix ι ι (H →L[ℂ] H)} (hZ : Z ∈ s.matrix) (hW : W ∈ s.matrix) :
    ∑ p, ∑ k, ⟪τ.g k, (Z * W) p p (τ.g k)⟫_ℂ = ∑ p, ∑ k, ⟪τ.g k, (W * Z) p p (τ.g k)⟫_ℂ := by
  have expand : ∀ A B : Matrix ι ι (H →L[ℂ] H), ∑ p, ∑ k, ⟪τ.g k, (A * B) p p (τ.g k)⟫_ℂ =
      ∑ p, ∑ q, ∑ k, ⟪τ.g k, (A p q * B q p) (τ.g k)⟫_ℂ := fun A B =>
    Finset.sum_congr rfl fun p _ => by
      simp only [mul_apply, _root_.sum_apply, inner_sum]
      exact Finset.sum_comm
  rw [expand, expand, Finset.sum_comm (f := fun p q => ∑ k, ⟪τ.g k, (W p q * Z q p) (τ.g k)⟫_ℂ)]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    τ.trace_mul_comm _ (hZ p q) _ (hW q p)

/-- **The normalized trace of matrices over a set carrying a faithful tracial state**: the
operators of the `ι × ι` matrices with entries in `s` carry the faithful tracial state
`τ'(Z) = |ι|⁻¹ ∑ₚ τ(Zₚₚ)`, given by the vectors `|ι|^{-1/2} gₖ ⊗ eₚ`. -/
noncomputable def ampl [Nonempty ι] {s : Set (H →L[ℂ] H)} (τ : VecTrace s) :
    VecTrace (toCLM '' (s.matrix : Set (Matrix ι ι (H →L[ℂ] H)))) :=
  ofFintype τ.amplVec
    (by
      have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
      simp only [amplVec, Fintype.sum_prod_type, norm_smul, norm_emb, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (inv_nonneg.2 (Nat.cast_nonneg _)), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum, τ.norm_sq_sum]
      field_simp)
    (by
      rintro _ ⟨Z, hZ, rfl⟩ _ ⟨W, hW, rfl⟩
      rw [← toCLM_mul, ← toCLM_mul, sum_inner_amplVec, sum_inner_amplVec,
        τ.sum_trace_mul_comm hZ hW])
    (by
      rintro _ ⟨Z, hZ, rfl⟩ h
      have hc : ((√((Fintype.card ι : ℝ)⁻¹) : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
        exact inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
      suffices Z = 0 by rw [this, toCLM_zero]
      refine Matrix.ext fun p q => ?_
      refine τ.separating _ (hZ p q) fun k => ?_
      have h0 : toCLM Z (emb q (τ.g k)) = 0 := by
        have := h (k, q)
        rwa [amplVec, map_smul, smul_eq_zero, or_iff_right hc] at this
      rw [← entries_toCLM Z, entries_apply, h0]
      rfl)

end VecTrace

/-! ## The players' operators of an extension -/

section Lift

variable {R S α β : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Ring S] [StarRing S]
  [Algebra ℂ S] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The first register's matrices commute with a map of the entries vanishing at zero. -/
theorem liftLeft_map {f : R → S} (hf : f 0 = 0) (X : Matrix α α R) :
    (liftLeft (β := β) X).map f = liftLeft (X.map f) := by
  ext p q
  rw [map_apply, liftLeft_apply, liftLeft_apply]
  split_ifs
  · rfl
  · exact hf

/-- The second register's matrices commute with a map of the entries vanishing at zero. -/
theorem liftRight_map {f : R → S} (hf : f 0 = 0) (Y : Matrix β β R) :
    (liftRight (α := α) Y).map f = liftRight (Y.map f) := by
  ext p q
  rw [map_apply, liftRight_apply, liftRight_apply]
  split_ifs
  · rfl
  · exact hf

end Lift

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-- **A finite pair with the players exchanged is a finite pair.** -/
theorem IsFinitePair.swap (h : M.IsFinitePair) : M.swap.IsFinitePair :=
  ⟨h.injB, h.injA, h.commutantB, h.commutantA, h.traceB, h.traceA⟩

section Expand

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The first player's operators of an extension are `X ⊗ 1_β` over the model's operators. -/
theorem expand_π_πA_eq_toCLM (M : BipartiteModel 𝒞 𝒜 ℬ) (e : α × β → ℂ) (X : Matrix α α 𝒜) :
    (M.expand e).π ((M.expand e).πA X) = toCLM (liftLeft (X.map (M.π.comp M.πA))) := by
  show toCLM ((liftLeft (X.map M.πA)).map M.π) = _
  rw [liftLeft_map (map_zero M.π), Matrix.map_map]
  rfl

/-- The second player's operators of an extension are `1_α ⊗ Y` over the model's operators. -/
theorem expand_π_πB_eq_toCLM (M : BipartiteModel 𝒞 𝒜 ℬ) (e : α × β → ℂ) (Y : Matrix β β ℬ) :
    (M.expand e).π ((M.expand e).πB Y) = toCLM (liftRight (Y.map (M.π.comp M.πB))) := by
  show toCLM ((liftRight (Y.map M.πB)).map M.π) = _
  rw [liftRight_map (map_zero M.π), Matrix.map_map]
  rfl

/-- The first player's operators of an extension are operators of matrices over the first
player's operators of the model. -/
theorem opsA_expand_subset (M : BipartiteModel 𝒞 𝒜 ℬ) (e : α × β → ℂ) :
    (M.expand e).opsA ⊆ toCLM '' M.opsA.matrix := by
  rintro _ ⟨X, rfl⟩
  refine ⟨_, fun p q => ?_, (M.expand_π_πA_eq_toCLM e X).symm⟩
  rw [liftLeft_apply]
  split_ifs
  · exact ⟨X p.1 q.1, rfl⟩
  · exact ⟨0, map_zero (M.π.comp M.πA)⟩

/-- The second player's operators of an extension are operators of matrices over the second
player's operators of the model. -/
theorem opsB_expand_subset (M : BipartiteModel 𝒞 𝒜 ℬ) (e : α × β → ℂ) :
    (M.expand e).opsB ⊆ toCLM '' M.opsB.matrix := by
  rintro _ ⟨Y, rfl⟩
  refine ⟨_, fun p q => ?_, (M.expand_π_πB_eq_toCLM e Y).symm⟩
  rw [liftRight_apply]
  split_ifs
  · exact ⟨Y p.2 q.2, rfl⟩
  · exact ⟨0, map_zero (M.π.comp M.πB)⟩

end Expand

/-- **An ancilla extension of a finite pair is a finite pair** (`lem:finite-pair-expand`), for
nonempty registers. -/
theorem IsFinitePair.expand (h : M.IsFinitePair) {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β] (e : α × β → ℂ) :
    (M.expand e).IsFinitePair where
  injA X X' hX := by
    simp only [expand_π_πA_eq_toCLM] at hX
    exact Matrix.map_injective h.injA (toCLM_liftLeft_injective hX)
  injB Y Y' hY := by
    simp only [expand_π_πB_eq_toCLM] at hY
    exact Matrix.map_injective h.injB (toCLM_liftRight_injective hY)
  commutantA T hT := by
    simp only [expand_π_πB_eq_toCLM] at hT
    have hs : ∀ f ∈ M.opsB, Commute T (toCLM (diagonal fun _ : α × β => f)) := by
      rintro _ ⟨b, rfl⟩
      have hb := hT (diagonal fun _ => b)
      rwa [diagonal_map (map_zero _), liftRight_diagonal_const] at hb
    have hreg : ∀ b b', Commute T (toCLM (liftRight (α := α) (single b b' (1 : M.H →L[ℂ] M.H))))
        := by
      intro b b'
      have hb := hT (single b b' 1)
      rwa [map_single, map_one] at hb
    obtain ⟨X, hX, rfl⟩ := exists_eq_toCLM_liftLeft hs hreg
    choose X' hX' using fun a a' => h.commutantA (X a a') fun b => hX a a' _ ⟨b, rfl⟩
    refine ⟨of X', ?_⟩
    show (M.expand e).π ((M.expand e).πA (of X')) = _
    rw [expand_π_πA_eq_toCLM]
    congr 2
    ext a a' : 1
    exact hX' a a'
  commutantB T hT := by
    simp only [expand_π_πA_eq_toCLM] at hT
    have hs : ∀ f ∈ M.opsA, Commute T (toCLM (diagonal fun _ : α × β => f)) := by
      rintro _ ⟨a, rfl⟩
      have ha := hT (diagonal fun _ => a)
      rwa [diagonal_map (map_zero _), liftLeft_diagonal_const] at ha
    have hreg : ∀ a a', Commute T (toCLM (liftLeft (β := β) (single a a' (1 : M.H →L[ℂ] M.H))))
        := by
      intro a a'
      have ha := hT (single a a' 1)
      rwa [map_single, map_one] at ha
    obtain ⟨Y, hY, rfl⟩ := exists_eq_toCLM_liftRight hs hreg
    choose Y' hY' using fun b b' => h.commutantB (Y b b') fun a => hY b b' _ ⟨a, rfl⟩
    refine ⟨of Y', ?_⟩
    show (M.expand e).π ((M.expand e).πB (of Y')) = _
    rw [expand_π_πB_eq_toCLM]
    congr 2
    ext b b' : 1
    exact hY' b b'
  traceA := by
    obtain ⟨τ⟩ := h.traceA
    exact ⟨τ.ampl.mono (M.opsA_expand_subset e)⟩
  traceB := by
    obtain ⟨τ⟩ := h.traceB
    exact ⟨τ.ampl.mono (M.opsB_expand_subset e)⟩

end MIPRE.BipartiteModel

end
