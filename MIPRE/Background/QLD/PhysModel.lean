/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ModelEmbedding
public import MIPRE.Foundations.Introspection.RegisterModel
public import MIPRE.Foundations.KrausDilation
public import MIPRE.Background.LIDT.ModelTransport

@[expose] public section

/-!
# The models of the Pauli basis test's stages 4 and 5

The soundness analysis of the Pauli basis test runs, from stage 2 on, in the register model
`N.reg I` of a bipartite model `N`: an EPR register `I`, whose first half `A'` the first player
holds and whose second half `A''` the second player holds. Stages 4 and 5 adjoin more registers,
and read one state along several assignments of the registers to the players. This file builds
those models once, generically in the register type `I` (the analysis takes `I := Anc F m`), and
the maps between them. The names of the registers are the paper's: `A` is the first player's own
space (the algebra `𝒜`), `A'` and `A''` the two halves of the pair, `Ea` the padding register;
`B`, `B'`, `B''`, `Eb` for the second player.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The matrix analysis builds each
of these states as an explicit vector on a product of index sets and moves between them by
`Matrix.reindex` along regroupings of those sets (`PadReg`, `padState`, `extVec2`, `mirrorVec`,
`physLiftEquiv`, `outerPairEquiv`, `endEquiv`). Here every state is an extension `N.expand e` of
the bipartite model by finite registers in a joint vector `e`, only the finite registers are ever
regrouped, and a regrouping is a local isometry or an isomorphism of models
(`MIPRE/Foundations/ModelEmbedding.lean`, `MIPRE/Foundations/ModelIso.lean`); several readings of
one extended state are readings (`BipartiteModel.recut`, `MIPRE/Foundations/ModelReading.lean`)
of one state model.

## Stage 4: the Halmos-dilated padded strategy

* **The padding register** `PadAnc F m d K`: the ancilla `DilationAncilla` of the Halmos dilation
  of a POVM with the seeded test's answers as outcomes, with reference vector `t₀` at the zero
  answer `ansZero`. Both players' dilations are taken on it with one common `K`.
* **The padded model** `padModel I F m d N K`: the register model `N.reg I` extended by the padding
  register of each player, in the product basis vector `|t₀⟩ ⊗ |t₀⟩`. A projective strategy of it
  is the two one-sided Halmos dilations, and its Born probabilities are those of the reference
  entries (`BipartiteModel.bornProb_expand_basisVec`).
* **Where the seeded test's soundness is applied** (`soundIn_padModel`): the padded model is the
  extension of `N` by the registers `(Ea, A')` and `(Eb, A'')` in the flattened vector `padE`, by
  associativity (`BipartiteModel.assocIso`), so the test's soundness in every extension of `N` by
  a unit vector gives it in the padded model; and, the test being symmetric in the players, in the
  padded model of `N.swap` (`soundIn_padModel_swap`).

## Stage 5: the physical state and its readings

* **The physical registers** `PhysReg I F m d K = I × (PadAnc F m d K × I)` of each player,
  `(A'', (Ea, A'))` and `(B'', (Eb, B'))`, in the **physical state** `physE`: each player's own
  EPR pair `(A'', A')`, `(B'', B')`, and the two padding registers in `|t₀⟩ ⊗ |t₀⟩`. The physical
  model is `phys I F m d N K = N.expand (physE …)`. The state is symmetric in the two players'
  blocks (`physE_symm`), a unit vector (`norm_physE`), and each player's pair satisfies the mirror
  identity (`physE_mirror_A`, `physE_mirror_B`, and their product forms): an operator on the near
  half acts on the state as its transpose on the far half.
* **The first cut** `cut1 I F m d N K`: the reading of the physical state model that hands the first
  player's far half `A''` to the second player, `A A' Ea | B A'' Eb (B' B'')`. It has the physical
  model's space, state and representation; only the players' operators differ, and the reading
  lemmas `cut1_πA`, `cut1_πB` write its operators as physical ones. The second cut is `cut1` of
  `N.swap`, a reading of the same state model with the second player's registers first.
* **The stage-4 models embed in the first cut**: `j₁` embeds the padded model, and `ι₁` the
  register model (with `ι₁_ΦA`, `ι₁_ΦB`), each carrying the state to the physical state.
* **Item 1's cut** `tgt I F m d N K`: the extension of `N` by the padded registers, with an EPR
  register `(A'', B'')` outside; `unassoc` regroups the physical registers into it, with no state
  condition.
* **The exchange of the blocks** `blockSwapIso`: the physical model of `N.swap` is the physical
  model of `N` with the players exchanged, the players' algebras unchanged.
-/

noncomputable section

namespace MIPRE.QLD

open Matrix OperatorMatrix Introspection
open scoped Kronecker

/-! ## The padding register -/

section Padding

variable {F : Type*} [Field F] {m d K : ℕ}

/-- The zero answer to the seeded test at `(q, 4m, d, 1)`: the reference answer of the Halmos
dilation of the padded strategy. -/
def ansZero : LIDT.CL.Answer F (4 * m) d 1 := LIDT.CL.Answer.values fun _ => 0

variable (F m d K) in
/-- **The padding register** `Ea` (and `Eb`): the ancilla of the Halmos dilation of a POVM with the
seeded test's answers as outcomes (`DilationAncilla`), with `K + 1` terms. Both players' dilations
are taken on it with one common `K`, so that the two runs of stage 4 read one physical state. -/
abbrev PadAnc := DilationAncilla (LIDT.CL.Answer F (4 * m) d 1) K

/-- The reference vector of the padding register: the zero answer, at the first term, where the
dilation compresses to the POVM it dilates (`exists_pvm_dilation_ge`). -/
def t₀ : PadAnc F m d K := Sum.inl (ansZero, 0)

variable [Fintype F] [DecidableEq F]

instance instFintypePadAnc : Fintype (PadAnc F m d K) :=
  inferInstanceAs (Fintype (DilationAncilla (LIDT.CL.Answer F (4 * m) d 1) K))

/-- Decidable equality on the padding register, assembled once. -/
instance instDecidableEqPadAnc : DecidableEq (PadAnc F m d K) :=
  inferInstanceAs (DecidableEq (DilationAncilla (LIDT.CL.Answer F (4 * m) d 1) K))

end Padding

/-! ## The padded model, where the seeded test's soundness is applied -/

section PaddedModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {I : Type*} [Fintype I] [DecidableEq I] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {m d : ℕ}

variable (I F m d) in
/-- **The joint state of the padded model's registers**, flattened: the first player's `(Ea, A')`
and the second player's `(Eb, A'')`, the padding registers in `|t₀⟩ ⊗ |t₀⟩` and the EPR pair
across. -/
def padE (K : ℕ) : (PadAnc F m d K × I) × (PadAnc F m d K × I) → ℂ :=
  fun q => basisVec t₀ t₀ (q.1.1, q.2.1) * registerEPR I (q.1.2, q.2.2)

omit [Fintype F] in
/-- The product condition of the associativity from the padded model (`padModel`). -/
theorem padE_apply {K : ℕ} (q : (PadAnc F m d K × I) × (PadAnc F m d K × I)) :
    padE I F m d K q = basisVec t₀ t₀ (q.1.1, q.2.1) * registerEPR I (q.1.2, q.2.2) := rfl

omit [Fintype F] in
/-- The flattened padded state is the expanded vector of the two padding vectors and the pair. -/
theorem padE_eq_expVec {K : ℕ} :
    padE I F m d K = expVec (basisVec (t₀ : PadAnc F m d K) t₀) (registerEPR I) := rfl

/-- The flattened padded state is a unit vector. -/
theorem norm_padE [Nonempty I] {K : ℕ} : ‖evec (padE I F m d K)‖ = 1 := by
  rw [padE_eq_expVec, norm_evec_expVec, norm_basisVec, registerEPR_norm, one_mul]

variable (I F m d) in
/-- **The model of the Halmos-dilated padded strategy**: the register model `N.reg I` extended by
the padding register of each player, in the product basis vector `|t₀⟩ ⊗ |t₀⟩`. Each player's
dilation acts on that player's padding register only, so the two dilations are one-sided; a Born
probability of the padded model is that of the two reference entries
(`BipartiteModel.bornProb_expand_basisVec`). -/
abbrev padModel (N : BipartiteModel 𝒞 𝒜 ℬ) (K : ℕ) :=
  (N.reg I).expand (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K))

end PaddedModel

section Sound

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [StarProper 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarProper ℬ]
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m d : ℕ} {N : BipartiteModel 𝒞 𝒜 ℬ}

/-- **The seeded test is sound in the padded model** as soon as it is sound in every extension of
`N` by a unit vector: the padded model is the extension of `N` by the registers `(Ea, A')` and
`(Eb, A'')` in the flattened vector `padE`, by associativity (`BipartiteModel.assocIso`). -/
theorem soundIn_padModel
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (N.expand e)) (K : ℕ) :
    LIDT.Simul.SoundIn (padModel I F m d N K) :=
  LIDT.Simul.SoundIn.of_iso
    (N.assocIso (registerEPR I) (basisVec t₀ t₀) (padE I F m d K) padE_apply)
    (@hL _ _ _ _ _ _ (padE I F m d K) norm_padE)

/-- **The seeded test is sound in the padded model of the model with the players exchanged**, from
its soundness in the extensions of `N`: the test is symmetric in the players
(`LIDT.Simul.soundIn_swap_expand_of_norm`). -/
theorem soundIn_padModel_swap
    (hL : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → LIDT.Simul.SoundIn (N.expand e)) (K : ℕ) :
    LIDT.Simul.SoundIn (padModel I F m d N.swap K) :=
  soundIn_padModel (N := N.swap) (fun e he => LIDT.Simul.soundIn_swap_expand_of_norm hL e he) K

end Sound

/-! ## The physical registers and the physical state -/

section Physical

variable {I : Type*} [Fintype I] [DecidableEq I] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {m d : ℕ}

variable (I F m d) in
/-- **One player's physical registers** `(A'', (Ea, A'))`: the far half of the player's own EPR
pair, then the padding register and the near half. -/
abbrev PhysReg (K : ℕ) := I × (PadAnc F m d K × I)

instance instFintypePhysReg (K : ℕ) : Fintype (PhysReg I F m d K) := instFintypeProd _ _

/-- Decidable equality on the physical registers, assembled by hand once. -/
instance instDecidableEqPhysReg (K : ℕ) : DecidableEq (PhysReg I F m d K) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

variable (I F m d) in
/-- **The physical state of the registers**: each player's own EPR pair, `(A'', A')` and
`(B'', B')`, and the two padding registers in `|t₀⟩ ⊗ |t₀⟩`. -/
def physE (K : ℕ) : PhysReg I F m d K × PhysReg I F m d K → ℂ := fun p =>
  registerEPR I (p.1.1, p.1.2.2) * registerEPR I (p.2.1, p.2.2.2) *
    basisVec t₀ t₀ (p.1.2.1, p.2.2.1)

omit [Fintype F] in
/-- The physical state, entry by entry. -/
theorem physE_apply {K : ℕ} (p : PhysReg I F m d K × PhysReg I F m d K) :
    physE I F m d K p = registerEPR I (p.1.1, p.1.2.2) * registerEPR I (p.2.1, p.2.2.2) *
      basisVec t₀ t₀ (p.1.2.1, p.2.2.1) := rfl

omit [Fintype F] in
/-- **The physical state is symmetric in the two players' blocks**: exchanging the blocks exchanges
the two pairs and the two padding registers, which are in the same state. -/
theorem physE_symm {K : ℕ} (p : PhysReg I F m d K × PhysReg I F m d K) :
    physE I F m d K p.swap = physE I F m d K p := by
  show registerEPR I (p.2.1, p.2.2.2) * registerEPR I (p.1.1, p.1.2.2) *
      basisVec t₀ t₀ (p.1.2.1, p.2.2.1).swap = _
  rw [basisVec_swap, mul_comm (registerEPR I (p.2.1, p.2.2.2))]
  rfl

/-- The regrouping of the physical registers as the three pairs `((A'', B''), Ea)` and
`((A', B'), Eb)`, along which the physical state is a product. -/
def physSplit (K : ℕ) : PhysReg I F m d K × PhysReg I F m d K ≃
    ((I × I) × PadAnc F m d K) × ((I × I) × PadAnc F m d K) where
  toFun p := (((p.1.1, p.2.1), p.1.2.1), ((p.1.2.2, p.2.2.2), p.2.2.1))
  invFun q := ((q.1.1.1, (q.1.2, q.2.1.1)), (q.1.1.2, (q.2.2, q.2.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype F] in
/-- The physical state, read along `physSplit`, is the product of the two pairs and the padding
vector. -/
theorem physE_eq_comp {K : ℕ} : physE I F m d K =
    expVec (expVec (registerEPR I) (registerEPR I)) (basisVec (t₀ : PadAnc F m d K) t₀) ∘
      physSplit K := rfl

/-- **The physical state is a unit vector.** -/
theorem norm_physE [Nonempty I] {K : ℕ} : ‖evec (physE I F m d K)‖ = 1 := by
  have h : ‖evec (physE I F m d K)‖ = ‖evec (expVec (expVec (registerEPR I) (registerEPR I))
      (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K)))‖ := by
    rw [physE_eq_comp, evec, evec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp (physSplit K) fun q => ‖expVec (expVec (registerEPR I) (registerEPR I))
      (basisVec (t₀ : PadAnc F m d K) (t₀ : PadAnc F m d K)) q‖ ^ 2
  rw [h, norm_evec_expVec, norm_evec_expVec, registerEPR_norm, norm_basisVec, one_mul, one_mul]

/-! ### The mirror identities of the two pairs -/

/-- A register operator of the first factor, on a vector of the pair of registers. -/
private theorem kronecker_one_mulVec_apply {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (L : Matrix α α ℂ) (v : α × β → ℂ) (p : α × β) :
    ((L ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ v) p = (L *ᵥ fun a => v (a, p.2)) p.1 := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single p.2]
  · rw [kroneckerMap_apply, one_apply_eq, mul_one]
  · intro b _ hb
    rw [kroneckerMap_apply, one_apply_ne (Ne.symm hb), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A register operator of the second factor, on a vector of the pair of registers. -/
private theorem one_kronecker_mulVec_apply {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (L : Matrix β β ℂ) (v : α × β → ℂ) (p : α × β) :
    (((1 : Matrix α α ℂ) ⊗ₖ L) *ᵥ v) p = (L *ᵥ fun b => v (p.1, b)) p.2 := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_eq_single p.1, mulVec, dotProduct]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [kroneckerMap_apply, one_apply_eq, one_mul]
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [kroneckerMap_apply, one_apply_ne (Ne.symm ha), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The EPR pair's contraction with a matrix, read on either half. -/
private theorem sum_mul_registerEPR (P : Matrix I I ℂ) (a b : I) (z : ℂ) :
    ∑ c, P b c * (registerEPR I (a, c) * z) = ∑ c, Pᵀ a c * (registerEPR I (c, b) * z) := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [registerEPR, transpose_apply]
  · intro c _ hc
    simp only [registerEPR, ite_eq_right hc, zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    simp only [registerEPR, ite_eq_right (Ne.symm hc), zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The mirror identity of the first player's pair**, on the registers: an operator `P` on the
near half `A'` acts on the physical state as its transpose on the far half `A''`, whatever acts on
the second player's registers. -/
theorem physE_mulVec_mirror_A {K : ℕ} (P : Matrix I I ℂ)
    (Q : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ) :
    (((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P)) ⊗ₖ Q)
        *ᵥ physE I F m d K
      = ((Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ)) ⊗ₖ Q)
        *ᵥ physE I F m d K := by
  have hsplit : ∀ L : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ,
      L ⊗ₖ Q = ((1 : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ) ⊗ₖ Q) *
        (L ⊗ₖ (1 : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ)) := fun L => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hsplit ((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P)),
    hsplit (Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ)),
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  funext ⟨⟨a, e, b⟩, p₂⟩
  rw [kronecker_one_mulVec_apply, kronecker_one_mulVec_apply, one_kronecker_mulVec_apply,
    one_kronecker_mulVec_apply, kronecker_one_mulVec_apply]
  simp only [mulVec, dotProduct, physE_apply, mul_assoc]
  exact sum_mul_registerEPR P a b _

/-- **The mirror identity of the second player's pair**, on the registers: an operator `P` on the
near half `B'` acts on the physical state as its transpose on the far half `B''`, whatever acts on
the first player's registers. -/
theorem physE_mulVec_mirror_B {K : ℕ} (Q : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ)
    (P : Matrix I I ℂ) :
    (Q ⊗ₖ ((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P)))
        *ᵥ physE I F m d K
      = (Q ⊗ₖ (Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ)))
        *ᵥ physE I F m d K := by
  have hsplit : ∀ L : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ,
      Q ⊗ₖ L = (Q ⊗ₖ (1 : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ)) *
        ((1 : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ) ⊗ₖ L) := fun L => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hsplit ((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P)),
    hsplit (Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ)),
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  funext ⟨p₁, a, e, b⟩
  rw [one_kronecker_mulVec_apply, one_kronecker_mulVec_apply, one_kronecker_mulVec_apply,
    one_kronecker_mulVec_apply, kronecker_one_mulVec_apply]
  simp only [mulVec, dotProduct, physE_apply]
  have h : ∀ c, registerEPR I (p₁.1, p₁.2.2) * registerEPR I (a, c) * basisVec t₀ t₀ (p₁.2.1, e)
      = registerEPR I (a, c) * (registerEPR I (p₁.1, p₁.2.2) * basisVec t₀ t₀ (p₁.2.1, e)) :=
    fun c => by ring
  have h' : ∀ c, registerEPR I (p₁.1, p₁.2.2) * registerEPR I (c, b) * basisVec t₀ t₀ (p₁.2.1, e)
      = registerEPR I (c, b) * (registerEPR I (p₁.1, p₁.2.2) * basisVec t₀ t₀ (p₁.2.1, e)) :=
    fun c => by ring
  simp only [h, h']
  exact sum_mul_registerEPR P a b _

end Physical

/-! ## The physical model and its first cut -/

section PhysicalModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {I : Type*} [Fintype I] [DecidableEq I] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {m d : ℕ}

variable (I F m d) in
/-- **The physical model**: `N` with each player's physical registers `(A'', (Ea, A'))` and
`(B'', (Eb, B'))`, in the physical state. The first player's operators are the matrices over `𝒜`
on the first player's physical registers, the second's over `ℬ` on the second's. -/
abbrev phys (N : BipartiteModel 𝒞 𝒜 ℬ) (K : ℕ) := N.expand (physE I F m d K)

variable {N : BipartiteModel 𝒞 𝒜 ℬ} {K : ℕ}

/-- **The mirror identity of the first player's pair**, in the physical model: an operator of the
first player that acts as `P` on the near half `A'` acts on the state as the one that acts as `Pᵀ`
on the far half `A''`, whatever the second player applies. -/
theorem physE_mirror_smulKron_A (X : 𝒜) (Y : ℬ) (P : Matrix I I ℂ)
    (Q : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ) :
    (phys I F m d N K).π ((phys I F m d N K).πA
        (smulKron X ((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P)))
        * (phys I F m d N K).πB (smulKron Y Q)) (phys I F m d N K).ψ
      = (phys I F m d N K).π ((phys I F m d N K).πA
        (smulKron X (Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ)))
        * (phys I F m d N K).πB (smulKron Y Q)) (phys I F m d N K).ψ := by
  rw [BipartiteModel.expand_π_smulKron_ψ, BipartiteModel.expand_π_smulKron_ψ,
    physE_mulVec_mirror_A]

/-- **The mirror identity of the second player's pair**, in the physical model: an operator of the
second player that acts as `P` on the near half `B'` acts on the state as the one that acts as
`Pᵀ` on the far half `B''`, whatever the first player applies. -/
theorem physE_mirror_smulKron_B (X : 𝒜) (Y : ℬ)
    (Q : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℂ) (P : Matrix I I ℂ) :
    (phys I F m d N K).π ((phys I F m d N K).πA (smulKron X Q) * (phys I F m d N K).πB
        (smulKron Y
          ((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P))))
        (phys I F m d N K).ψ
      = (phys I F m d N K).π ((phys I F m d N K).πA (smulKron X Q) * (phys I F m d N K).πB
        (smulKron Y (Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ))))
        (phys I F m d N K).ψ := by
  rw [BipartiteModel.expand_π_smulKron_ψ, BipartiteModel.expand_π_smulKron_ψ,
    physE_mulVec_mirror_B]

/-- **The mirror identity of the first player's pair** (`reg_mirror` for the physical model): a
matrix `P` on the near half `A'` acts on the state as its transpose on the far half `A''`. -/
theorem physE_mirror_A (P : Matrix I I ℂ) :
    (phys I F m d N K).π ((phys I F m d N K).πA
        (smulKron 1
          ((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P))))
        (phys I F m d N K).ψ
      = (phys I F m d N K).π ((phys I F m d N K).πA
        (smulKron 1 (Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ))))
        (phys I F m d N K).ψ := by
  have h := physE_mirror_smulKron_A (N := N) (F := F) (m := m) (d := d) (K := K) (1 : 𝒜) (1 : ℬ)
    P 1
  rwa [smulKron_one_one, map_one, mul_one, mul_one] at h

/-- **The mirror identity of the second player's pair** (`reg_mirror` for the physical model): a
matrix `P` on the near half `B'` acts on the state as its transpose on the far half `B''`. -/
theorem physE_mirror_B (P : Matrix I I ℂ) :
    (phys I F m d N K).π ((phys I F m d N K).πB
        (smulKron 1
          ((1 : Matrix I I ℂ) ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ P))))
        (phys I F m d N K).ψ
      = (phys I F m d N K).π ((phys I F m d N K).πB
        (smulKron 1 (Pᵀ ⊗ₖ (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℂ))))
        (phys I F m d N K).ψ := by
  have h := physE_mirror_smulKron_B (N := N) (F := F) (m := m) (d := d) (K := K) (1 : 𝒜) (1 : ℬ)
    1 P
  rwa [smulKron_one_one, map_one, one_mul, one_mul] at h

variable (I F m d N K) in
/-- **The first cut**, `A A' Ea | B A'' Eb (B' B'')`: the reading of the physical state model that
hands the first player's far half `A''` to the second player. It has the physical model's space,
state and representation; the first player's operators act on `(Ea, A')`, the second player's on
`(A'', (B'', (Eb, B')))`. -/
abbrev cut1 := N.recut (physE I F m d K) (moveEquiv I (PadAnc F m d K × I) (PhysReg I F m d K))

/-- **Reading lemma for the first player of the first cut**: an operator `X` of `(Ea, A')` is the
physical operator `1_{A''} ⊗ X`. -/
theorem cut1_πA (X : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) 𝒜) :
    (cut1 I F m d N K).πA X = (phys I F m d N K).πA (compHom (diagonal fun _ : I => X)) :=
  N.recut_move_πA (physE I F m d K) X

/-- **Reading lemma for the second player of the first cut**: an operator that is a product
`Q ⊗ Y` of a matrix `Q` on the moved half `A''` and an operator `Y` of the second player's
physical registers is the product of the physical first-player operator `Q ⊗ 1` and the physical
second-player operator `Y`. -/
theorem cut1_πB (Y : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ) (Q : Matrix I I ℂ) :
    (cut1 I F m d N K).πB (compHom (smulKron Y Q))
      = (phys I F m d N K).πA
          (compHom (smulKron (1 : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) 𝒜) Q))
        * (phys I F m d N K).πB Y :=
  N.recut_move_πB (physE I F m d K) Y Q

end PhysicalModel

/-! ## The stage-4 models in the first cut -/

section Embeddings

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {I : Type*} [Fintype I] [DecidableEq I] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {m d : ℕ}

variable (I) in
/-- The second player's pair `(B'', B')`, adjoined to the padded model's registers with nothing for
the first player. -/
def pair2 : Unit × (I × I) → ℂ := fun p => registerEPR I p.2

/-- The adjoined pair is a unit vector. -/
theorem norm_pair2 [Nonempty I] : ‖evec (pair2 I)‖ = 1 := by
  rw [← registerEPR_norm (I := I), evec, evec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (Equiv.punitProd (I × I)) _ _ fun _ => rfl

variable (I F m d) in
/-- The registers of the first cut before their regrouping: the first player's `((), (Ea, A'))`,
the second player's `((B'', B'), (Eb, A''))`, in the product of the adjoined pair and the flattened
padded state. -/
def pairPadE (K : ℕ) :
    (Unit × (PadAnc F m d K × I)) × ((I × I) × (PadAnc F m d K × I)) → ℂ :=
  fun q => pair2 I (q.1.1, q.2.1) * padE I F m d K (q.1.2, q.2.2)

omit [Fintype F] in
/-- The product condition of the associativity adjoining the second player's pair. -/
theorem pairPadE_apply {K : ℕ}
    (q : (Unit × (PadAnc F m d K × I)) × ((I × I) × (PadAnc F m d K × I))) :
    pairPadE I F m d K q = pair2 I (q.1.1, q.2.1) * padE I F m d K (q.1.2, q.2.2) := rfl

variable (I F m d) in
/-- The regrouping of the second player's registers of the first cut: `(A'', (B'', (Eb, B')))` as
`((B'', B'), (Eb, A''))`. -/
def cutRelabel (K : ℕ) : I × PhysReg I F m d K ≃ (I × I) × (PadAnc F m d K × I) where
  toFun p := ((p.2.1, p.2.2.2), (p.2.2.1, p.1))
  invFun q := (q.2.2, (q.1.1, (q.2.1, q.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype F] in
/-- **The relabelling condition of the first cut**: the physical state, read along the first cut,
is the adjoined pair times the flattened padded state, regrouped. -/
theorem physE_comp_moveEquiv_symm {K : ℕ}
    (p : (PadAnc F m d K × I) × (I × PhysReg I F m d K)) :
    (physE I F m d K ∘ (moveEquiv I (PadAnc F m d K × I) (PhysReg I F m d K)).symm) p =
      pairPadE I F m d K ((Equiv.punitProd _).symm p.1, cutRelabel I F m d K p.2) := by
  obtain ⟨⟨e, a'⟩, a'', b'', eb, b'⟩ := p
  have h : registerEPR I (a'', a') = registerEPR I (a', a'') := registerEPR_swap (a', a'')
  show registerEPR I (a'', a') * registerEPR I (b'', b') * basisVec t₀ t₀ (e, eb) =
    registerEPR I (b'', b') * (basisVec t₀ t₀ (e, eb) * registerEPR I (a', a''))
  rw [h]
  ring

variable (I F m d) in
/-- **The padded model embeds in the first cut**: flatten the padded registers
(`BipartiteModel.assocEmb`), adjoin the second player's pair (`BipartiteModel.inertEmb`), flatten
again, regroup the second player's registers (`BipartiteModel.relabelEmb`), and read the result
as the first cut (`BipartiteModel.recutEmb`). -/
def j₁ [Nonempty I] (N : BipartiteModel 𝒞 𝒜 ℬ) (K : ℕ) :
    (padModel I F m d N K).Embedding (cut1 I F m d N K) :=
  (N.recutEmb (physE I F m d K) (moveEquiv I (PadAnc F m d K × I) (PhysReg I F m d K))).comp
    ((N.relabelEmb (pairPadE I F m d K)
        (physE I F m d K ∘ (moveEquiv I (PadAnc F m d K × I) (PhysReg I F m d K)).symm)
        (Equiv.punitProd _).symm (cutRelabel I F m d K) physE_comp_moveEquiv_symm).comp
      ((N.assocEmb (padE I F m d K) (pair2 I) (pairPadE I F m d K) pairPadE_apply).comp
        (((N.expand (padE I F m d K)).inertEmb (pair2 I) norm_pair2).comp
          (N.assocEmb (registerEPR I) (basisVec (t₀ : PadAnc F m d K) t₀) (padE I F m d K)
            padE_apply))))

variable (I F m d) in
/-- **The register model embeds in the first cut**: the padding registers in `|t₀⟩ ⊗ |t₀⟩`
(`BipartiteModel.inertEmb`), then `j₁`. Both runs of stage 4 carry the register state to the one
physical state. -/
def ι₁ [Nonempty I] (N : BipartiteModel 𝒞 𝒜 ℬ) (K : ℕ) : (N.reg I).Embedding (cut1 I F m d N K) :=
  (j₁ I F m d N K).comp ((N.reg I).inertEmb (basisVec (t₀ : PadAnc F m d K) t₀) norm_basisVec)

variable [Nonempty I] {N : BipartiteModel 𝒞 𝒜 ℬ} {K : ℕ}

/-- The first player's operators of the padded model, in the first cut: the flattening. -/
@[simp]
theorem j₁_ΦA (X : Matrix (PadAnc F m d K) (PadAnc F m d K) (Matrix I I 𝒜)) :
    (j₁ I F m d N K).ΦA X = compHom X := by
  ext p q
  simp only [j₁, BipartiteModel.Embedding.comp_ΦA, BipartiteModel.inertEmb_ΦA,
    BipartiteModel.assocEmb_ΦA, BipartiteModel.relabelEmb_ΦA, BipartiteModel.recutEmb_ΦA,
    submatrix_apply, Equiv.punitProd_symm_apply, compHom_apply, diagonal_apply_eq]

/-- **The first player's register operators, in the first cut**: an operator `Z` of `A'` acts as
`1_{Ea} ⊗ Z`. -/
@[simp]
theorem ι₁_ΦA (Z : Matrix I I 𝒜) :
    (ι₁ I F m d N K).ΦA Z = compHom (diagonal fun _ : PadAnc F m d K => Z) := by
  ext p q
  simp only [ι₁, j₁, BipartiteModel.Embedding.comp_ΦA, BipartiteModel.inertEmb_ΦA,
    BipartiteModel.assocEmb_ΦA, BipartiteModel.relabelEmb_ΦA, BipartiteModel.recutEmb_ΦA,
    submatrix_apply, Equiv.punitProd_symm_apply, compHom_apply, diagonal_apply_eq]

/-- **The second player's register operators, in the first cut**: an operator `Z` of `A''` acts
as `Z ⊗ 1` on `(A'', (B'', (Eb, B')))`. -/
@[simp]
theorem ι₁_ΦB (Z : Matrix I I ℬ) :
    (ι₁ I F m d N K).ΦB Z = compHom (Z.map fun y => diagonal fun _ : PhysReg I F m d K => y) := by
  ext ⟨a, b, e, c⟩ ⟨a', b', e', c'⟩
  simp only [ι₁, j₁, BipartiteModel.Embedding.comp_ΦB, BipartiteModel.inertEmb_ΦB,
    BipartiteModel.assocEmb_ΦB, BipartiteModel.relabelEmb_ΦB, BipartiteModel.recutEmb_ΦB,
    submatrix_apply, compHom_apply, cutRelabel, Equiv.coe_fn_mk, Matrix.map_apply]
  by_cases hb : b = b' <;> by_cases hc : c = c' <;> by_cases he : e = e' <;> simp [hb, hc, he]

-- `CutSimul N S K δ := SimulPair N S (cut1 I F m d N K) (ι₁ I F m d N K) δ`, the simultaneous
-- pair measurement on the first cut, goes here once the model `SimulPair` of
-- `MIPRE/Background/QLD/Simul.lean` is stated.

end Embeddings

/-! ## Item 1's cut, and the exchange of the blocks -/

section Regroupings

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {I : Type*} [Fintype I] [DecidableEq I] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {m d : ℕ}

variable (I F m d) in
/-- **Item 1's cut** `(A A' Ea, B B' Eb) × (A'', B'')`: the extension of `N` by the padded
registers `(Ea, A')` and `(Eb, B')`, with an EPR register `(A'', B'')` outside. -/
abbrev tgt (N : BipartiteModel 𝒞 𝒜 ℬ) (K : ℕ) := (N.expand (padE I F m d K)).reg I

variable (I F m d) in
/-- The isometry of `unassoc`: a vector of the physical registers, read with the outer registers
`(A'', B'')` of the two players outside and the inner ones `((Ea, A'), (Eb, B'))` inside. -/
def unassocIsometry (N : BipartiteModel 𝒞 𝒜 ℬ) (K : ℕ) :
    (phys I F m d N K).H →ₗᵢ[ℂ] (tgt I F m d N K).H :=
  ((N.expand (padE I F m d K)).ampl (registerEPR I)).symm.toLinearIsometry.comp
    ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : I × I =>
        (N.ampl (padE I F m d K)).symm).toLinearIsometry.comp
      ((amplCurry (ι := I × I) (κ := (PadAnc F m d K × I) × (PadAnc F m d K × I))
          (H := N.H)).comp
        ((amplReindex (H := N.H)
            (Equiv.prodProdProdComm I (PadAnc F m d K × I) I (PadAnc F m d K × I)).symm).comp
          (N.ampl (physE I F m d K)).toLinearIsometry)))

variable {N : BipartiteModel 𝒞 𝒜 ℬ} {K : ℕ}

/-- The components of `unassocIsometry`. -/
theorem ampl_unassocIsometry (w : (phys I F m d N K).H) (i : I × I)
    (q : (PadAnc F m d K × I) × (PadAnc F m d K × I)) :
    N.ampl (padE I F m d K)
        ((N.expand (padE I F m d K)).ampl (registerEPR I) (unassocIsometry I F m d N K w) i) q
      = N.ampl (physE I F m d K) w ((i.1, q.1), (i.2, q.2)) := rfl

/-- The associativity of item 1's cut undoes `unassocIsometry`. -/
theorem assoc_W_unassocIsometry (w : (phys I F m d N K).H) :
    (N.assoc (padE I F m d K) (registerEPR I) (physE I F m d K)).W
      (unassocIsometry I F m d N K w) = w :=
  N.expand_ext _ fun _ => rfl

variable (I F m d N K) in
/-- **The physical registers regrouped as item 1's cut**: the inverse of the associativity
`BipartiteModel.assoc` of item 1's cut, with no state condition --- the two cuts hold different
pairs, so it does not carry the physical state to the state of item 1's cut, and it is read on a
transported state (`LocalIsometry.bornProb_withState`). -/
def unassoc : BipartiteModel.LocalIsometry (phys I F m d N K) (tgt I F m d N K) :=
  (N.assoc (padE I F m d K) (registerEPR I) (physE I F m d K)).symm (unassocIsometry I F m d N K)
    assoc_W_unassocIsometry uncompHom compHom_uncompHom uncompHom compHom_uncompHom

@[simp]
theorem unassoc_W (w : (phys I F m d N K).H) :
    (unassoc I F m d N K).W w = unassocIsometry I F m d N K w := rfl

/-- The first player's physical operators, in item 1's cut: the block matrices over `A''`. -/
@[simp]
theorem unassoc_ΦA (X : Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜) :
    (unassoc I F m d N K).ΦA X = uncompHom X := rfl

/-- The second player's physical operators, in item 1's cut: the block matrices over `B''`. -/
@[simp]
theorem unassoc_ΦB (Y : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ) :
    (unassoc I F m d N K).ΦB Y = uncompHom Y := rfl

variable (I F m d N K) in
/-- **The exchange of the blocks**: the physical model of `N.swap` is the physical model of `N`
with the players exchanged, by the unitary exchanging the two blocks of registers
(`BipartiteModel.swapExpand`), which fixes the physical state (`physE_symm`). The players'
algebras are the same on both sides and the isomorphism is the identity on them, so the second
player's objects of one are the first player's of the other. -/
def blockSwapIso : BipartiteModel.Iso (phys I F m d N.swap K) (phys I F m d N K).swap :=
  (BipartiteModel.Iso.ofLocalIsometry (N.swapExpand (physE I F m d K) (physE I F m d K))
    (N.swapExpand_W_ψ _ _ fun p => (physE_symm p).symm)
    (fun w => (N.ampl (physE I F m d K)).symm
      (WithLp.toLp 2 fun p => N.swap.ampl (physE I F m d K) w p.swap))
    (fun _ => N.swap.expand_ext _ fun _ => rfl)
    id (fun _ => rfl) (fun _ => rfl) id (fun _ => rfl) (fun _ => rfl)).symm

@[simp]
theorem blockSwapIso_ΦA (X : Matrix (PhysReg I F m d K) (PhysReg I F m d K) ℬ) :
    (blockSwapIso I F m d N K).ΦA X = X := rfl

@[simp]
theorem blockSwapIso_ΦB (Y : Matrix (PhysReg I F m d K) (PhysReg I F m d K) 𝒜) :
    (blockSwapIso I F m d N K).ΦB Y = Y := rfl

/-- The unitary of `blockSwapIso` exchanges the two blocks of registers. -/
theorem ampl_blockSwapIso_W (w : (phys I F m d N.swap K).H)
    (p : PhysReg I F m d K × PhysReg I F m d K) :
    N.ampl (physE I F m d K) ((blockSwapIso I F m d N K).W w) p
      = N.swap.ampl (physE I F m d K) w p.swap := rfl

end Regroupings

end MIPRE.QLD

end

end
