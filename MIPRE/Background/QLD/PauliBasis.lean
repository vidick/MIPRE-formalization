/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Win
public import MIPRE.Foundations.Pasting
public import MIPRE.Background.QLD.Simul

@[expose] public section

/-!
# The point measurement and the Pauli basis reading, on one party

The repaired proof of `lem:qld-exact-paulis` needs the strategy's `(Point, W)` measurement to be
close to the low-degree reading of its `(Pauli, W)` answer **on the same party**: the Pauli basis
answer does not depend on the sampled point, which is what lets Schwartz--Zippel be applied to a
uniform point independent of the operators.

Both inputs are items of `lem:qld-win-implications`, and both are *cross-party*: the point
measurements of the two players agree (`item_consistency` at the type `(Point, W)`), and Alice's
point answer agrees with the evaluation at the sampled point of the low-degree encoding of Bob's
Pauli basis answer (`item_pauli_consistency`). They share Alice's family, so the triangle
inequality of `BipartiteModel.swap_stateSqNorm_sub_le` leaves a statement about Bob alone, at four
times the error: `688 ε`.

Nothing here is padded: this is the bare strategy, and its reading on the expanded state, which
is the statement the mass argument of `MIPRE/Background/QLD/Multilinear.lean` consumes.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The strategy is a pair of
families of POVMs in the two players' algebras of a bipartite model `M`, Bob's squared state norm
`‖stateVecB ψ Y‖²` is `M.swap.stateSqNorm Y`, and the expanded state is the register model
`M.reg (Anc F m)`. A hatted measurement is a convolution of a family of the player's algebra with a
projective family of the register, `∑_{a + b = c} smulKron (Z a) (T b)` (register outer,
`conv`), and the shared register factor drops out of a same-party deviation exactly
(`sum_normSq_stateVecB_conv_eq`), by the two-sided factorization of Born probabilities of the
extended model (`BipartiteModel.swap_stateSqNorm_expand_smulKron_one`). The hatted Pauli basis
measurement `hatPauli` is a POVM in the register's matrices over the player's algebra.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## A common register factor drops out of a same-party deviation -/

section Conv

variable {R : Type*} [Ring R] [Algebra ℂ R] {α C : Type*} [Fintype α] [DecidableEq α]
  [Fintype C] [DecidableEq C] [AddCommGroup C]

/-- **The convolution of a family of the player's algebra with one on a register**: the shape
every hatted measurement has, `X̂_c = ∑_{a + b = c} X_a ⊗ T_b`, as a matrix over the player's
algebra on the register (register outer). -/
def conv (Z : C → R) (T : C → Matrix α α ℂ) (c : C) : Matrix α α R :=
  ∑ p ∈ univ.filter fun p : C × C => p.1 + p.2 = c, smulKron (Z p.1) (T p.2)

/-- Against a projective register family the cross terms of `X̂⋆ X̂` vanish: the register outcome
determines the other one. -/
theorem conjTranspose_conv_mul_conv [StarRing R] [StarModule ℂ R] (Z : C → R)
    {T : C → Matrix α α ℂ} (hT : IsPVM T) (c : C) :
    star (conv Z T c) * conv Z T c = conv (fun a => star (Z a) * Z a) T c := by
  classical
  simp only [conv, star_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · rw [star_smulKron, smulKron_mul, hT.isSelfAdjoint, hT.idem]
  · intro p' hp' hne
    have hb : p'.2 ≠ p.2 := by
      intro hb
      apply hne
      have h1 := (mem_filter.mp hp).2
      have h2 := (mem_filter.mp hp').2
      refine Prod.ext ?_ hb
      have : p'.1 + p'.2 = p.1 + p.2 := by rw [h1, h2]
      rw [hb] at this
      exact add_right_cancel this
    rw [star_smulKron, smulKron_mul, hT.isSelfAdjoint, hT.orthogonal hb, smulKron_zero_right]
  · intro hp'
    exact absurd hp hp'

/-- Summing a convolution over the outcome frees the register factor. -/
theorem sum_conv (Z : C → R) {T : C → Matrix α α ℂ} (hT : IsPVM T) :
    ∑ c, conv Z T c = smulKron (∑ a, Z a) (1 : Matrix α α ℂ) := by
  classical
  simp only [conv]
  have h : ∑ c, ∑ p ∈ univ.filter fun p : C × C => p.1 + p.2 = c, smulKron (Z p.1) (T p.2)
      = ∑ p : C × C, smulKron (Z p.1) (T p.2) :=
    Finset.sum_fiberwise univ (fun p : C × C => p.1 + p.2) fun p => smulKron (Z p.1) (T p.2)
  have hrow : ∀ a : C, (∑ b : C, smulKron (Z a) (T b)) = smulKron (Z a) (1 : Matrix α α ℂ) :=
    fun a => by rw [← smulKron_sum_right, hT.sum_eq_one]
  calc ∑ c, ∑ p ∈ univ.filter fun p : C × C => p.1 + p.2 = c, smulKron (Z p.1) (T p.2)
      = ∑ p : C × C, smulKron (Z p.1) (T p.2) := h
    _ = ∑ a : C, ∑ b : C, smulKron (Z a) (T b) := Fintype.sum_prod_type _
    _ = ∑ a : C, smulKron (Z a) (1 : Matrix α α ℂ) := Finset.sum_congr rfl fun a _ => hrow a
    _ = smulKron (∑ a, Z a) (1 : Matrix α α ℂ) := (smulKron_sum_left univ Z 1).symm

end Conv

/-- **The Kronecker product of two coarse-grainings is the coarse-graining of the product**,
along the product map on the outcomes. -/
theorem POVM.map_kron_map {dB anc' : Type*} [Fintype dB] [DecidableEq dB] [Fintype anc']
    [DecidableEq anc'] {ι κ ι' κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    (Y : POVM ι dB) (P : POVM κ anc') (f : ι → ι') (g : κ → κ') :
    (Y.kron P).map (fun p => (f p.1, g p.2)) = (Y.map f).kron (P.map g) := by
  classical
  refine POVM.ext' fun q => ?_
  rw [POVM.map_mats, POVM.kron_mats, POVM.map_mats, POVM.map_mats]
  have hset : (univ.filter fun p : ι × κ => (f p.1, g p.2) = q)
      = (univ.filter fun h => f h = q.1) ×ˢ (univ.filter fun b => g b = q.2) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, Finset.mem_product, Prod.ext_iff]
  rw [hset, Finset.sum_product]
  simp only [POVM.kron_mats]
  rw [sum_kronecker_left]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [kronecker_sum_right]

section Transfer

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ]
  {α β C : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype C]
  [DecidableEq C] [AddCommGroup C]

/-- **The transfer**: on an extension of a model by registers in a unit vector, the second
player's same-party deviation of two convolutions with a common projective register family is the
deviation of the two families themselves. -/
theorem sum_normSq_stateVecB_conv_eq (M : BipartiteModel 𝒞 𝒜 ℬ) {e : α × β → ℂ}
    (he : ‖evec e‖ = 1) (Z : C → ℬ) {T : C → Matrix β β ℂ} (hT : IsPVM T) :
    ∑ c, (M.expand e).swap.stateSqNorm (conv Z T c) = ∑ a, M.swap.stateSqNorm (Z a) := by
  have hterm : ∀ c, (M.expand e).swap.stateSqNorm (conv Z T c)
      = (M.expand e).swap.bornProb (conv (fun a => star (Z a) * Z a) T c) 1 := fun c => by
    rw [BipartiteModel.stateSqNorm_eq_bornProb_one, conjTranspose_conv_mul_conv Z hT]
  have hone : ∀ a, (M.expand e).swap.bornProb (smulKron (star (Z a) * Z a) 1) 1
      = M.swap.stateSqNorm (Z a) := fun a => by
    have h := M.swap_stateSqNorm_expand_smulKron_one e (Z a)
    rw [he, one_pow, one_mul, BipartiteModel.stateSqNorm_eq_bornProb_one (M.expand e).swap,
      star_smulKron_one, smulKron_mul, Matrix.one_mul] at h
    exact h
  rw [Finset.sum_congr rfl fun c _ => hterm c, ← BipartiteModel.bornProb_sum_left, sum_conv _ hT,
    smulKron_sum_left, BipartiteModel.bornProb_sum_left]
  exact Finset.sum_congr rfl fun a _ => hone a

end Transfer

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

section Bare

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-- **The point measurement and the Pauli basis reading agree on Bob's side**, on average over the
verifier's content and at `688 ε`: the two cross-party items of `lem:qld-win-implications` share
Alice's point measurement, so the triangle inequality removes it. -/
theorem sum_normSq_point_sub_pauli_le (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : F, M.swap.stateSqNorm (((PB (c.question hm (.point W))).map rdVal).op o
          - ((PB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).op o)
      ≤ 688 * ε := by
  have h1 := item_consistency (PB := PB) hM hfail (.point W) rdVal
  have h2 := item_pauli_consistency (PB := PB) hM hfail W
  rw [BipartiteModel.xPovmDist] at h1
  have hterm : ∀ c : Content F m,
      ∑ o : F, M.swap.stateSqNorm (((PB (c.question hm (.point W))).map rdVal).op o
        - ((PB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).op o)
      ≤ 2 * ∑ o : F, M.xSqNorm (((PA (c.question hm (.point W))).map rdVal).op o)
            (((PB (c.question hm (.point W))).map rdVal).op o)
        + 2 * ∑ o : F, M.xSqNorm (((PA (c.question hm (.point W))).map rdVal).op o)
            (((PB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).op o) := by
    intro c
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun o _ => M.swap_stateSqNorm_sub_le _ _ _
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ univ) =>
    mul_le_mul_of_nonneg_left (hterm c)
      (by positivity : (0 : ℝ) ≤ (Fintype.card (Content F m) : ℝ)⁻¹)
  have hsplit : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      (2 * ∑ o : F, M.xSqNorm (((PA (c.question hm (.point W))).map rdVal).op o)
          (((PB (c.question hm (.point W))).map rdVal).op o)
        + 2 * ∑ o : F, M.xSqNorm (((PA (c.question hm (.point W))).map rdVal).op o)
          (((PB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).op o))
      = 2 * (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : F, M.xSqNorm (((PA (c.question hm (.point W))).map rdVal).op o)
            (((PB (c.question hm (.point W))).map rdVal).op o))
        + 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : F, M.xSqNorm (((PA (c.question hm (.point W))).map rdVal).op o)
            (((PB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).op o) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit] at hsum
  linarith

end Bare

/-! ## The Pauli basis measurement, indexed by cube data -/

/-- The cube data a `(Pauli, W)` answer reports; zero on an ill-formatted answer. -/
def rdPauliVec : Answer F m d → Anc F m
  | .pauliAns h => h
  | _ => 0

/-- The low-degree reading at a point is the pairing of the cube data with the point's indicator
vector. -/
theorem rdPauli_eq_dotF (u : Point F m) (a : Answer F m d) :
    rdPauli u a = dotF (rdPauliVec a) (indVec u) := by
  cases a with
  | pauliAns h => rw [rdPauli, rdPauliVec, dotF_indVec]
  | val _ => simp [rdPauli, rdPauliVec, dotF]
  | apoly _ => simp [rdPauli, rdPauliVec, dotF]
  | dpoly _ => simp [rdPauli, rdPauliVec, dotF]
  | bit _ => simp [rdPauli, rdPauliVec, dotF]
  | bitPair _ => simp [rdPauli, rdPauliVec, dotF]
  | bitTriple _ => simp [rdPauli, rdPauliVec, dotF]

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem dotF_add_left (a b v : Anc F m) : dotF (a + b) v = dotF a v + dotF b v := by
  simp only [dotF, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- **The ancilla's Weyl measurement**, whose outcomes are the cube data themselves: the
syndrome measurements are its coarse-grainings. -/
def weylPOVM (W : Bas) : POVM (Anc F m) (Anc F m) := synOfPOVM W id

theorem weylPOVM_mats (W : Bas) (e : Anc F m) :
    (((weylPOVM (F := F) (m := m) W).mats e).val) = proj (weylOf W) e := by
  rw [weylPOVM, synOfPOVM_mats, synOf]
  rw [show (univ.filter fun c : Anc F m => id c = e) = {e} from by ext c; simp [eq_comm],
    Finset.sum_singleton]

/-- The ancilla's Weyl measurement is projective. -/
theorem isPVM_weylPOVM (W : Bas) :
    IsPVM fun e => (((weylPOVM (F := F) (m := m) W).mats e).val) :=
  isPVM_synOfPOVM W id

/-- Every syndrome measurement is a coarse-graining of it. -/
theorem synOfPOVM_eq_map {C : Type*} [Fintype C] [DecidableEq C] (W : Bas) (φ : Anc F m → C) :
    synOfPOVM (F := F) (m := m) W φ = (weylPOVM W).map φ := by
  refine POVM.ext' fun o => ?_
  rw [POVM.map_mats, synOfPOVM_mats, synOf]
  exact Finset.sum_congr rfl fun e _ => (weylPOVM_mats W e).symm

section Hat

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

/-- **The Pauli basis measurement convolved with the ancilla's Weyl measurement**: a POVM in the
register's matrices over the player's algebra, whose outcomes are cube data and which, crucially,
does not depend on any sampled point. -/
def hatPauli (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) :
    POVMIn (Anc F m) (Matrix (Anc F m) (Anc F m) R) :=
  (kronIn ((P (.pauli W)).map rdPauliVec) (weylPOVM W) (isPVM_weylPOVM W)).map
    fun p => p.1 + p.2

/-- **Reading it at a point is the hatted Pauli basis measurement at that point.** The pairing is
additive, so coarse-graining commutes with the convolution. -/
theorem hatPauli_map (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) :
    (hatPauli P W).map (fun k => dotF k (indVec u))
      = (kronIn ((P (.pauli W)).map (rdPauli u)) (synPOVM W u) (isPVM_synPOVM W u)).map
          fun p => p.1 + p.2 := by
  have hsplit : (hatPauli P W).map (fun k => dotF k (indVec u))
      = ((kronIn ((P (.pauli W)).map rdPauliVec) (weylPOVM W) (isPVM_weylPOVM W)).map
          (fun r : Anc F m × Anc F m => (dotF r.1 (indVec u), dotF r.2 (indVec u)))).map
          (fun q : F × F => q.1 + q.2) := by
    rw [hatPauli, POVMIn.map_map, POVMIn.map_map]
    congr 1
    funext p
    exact dotF_add_left p.1 p.2 (indVec u)
  have hY : ((P (.pauli W)).map rdPauliVec).map (fun k => dotF k (indVec u))
      = (P (.pauli W)).map (rdPauli u) := by
    rw [POVMIn.map_map, show (fun a => dotF (rdPauliVec a) (indVec u)) = rdPauli u from
      funext fun a => (rdPauli_eq_dotF u a).symm]
  have hP : (weylPOVM (F := F) (m := m) W).map (fun k => dotF k (indVec u)) = synPOVM W u := by
    rw [synPOVM, synOfPOVM_eq_map]
  have hQ : IsPVM fun k =>
      ((((weylPOVM (F := F) (m := m) W).map (fun k => dotF k (indVec u))).mats k).val) := by
    rw [hP]
    exact isPVM_synPOVM W u
  rw [hsplit, ← kronIn_map ((P (.pauli W)).map rdPauliVec) (weylPOVM W) (isPVM_weylPOVM W)
    (fun k => dotF k (indVec u)) (fun k => dotF k (indVec u)) hQ, hY,
    kronIn_congr _ hP hQ (isPVM_synPOVM W u)]

end Hat

/-! ## Substituting one family for another inside an agreement -/

section Substitute

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **Cauchy--Schwarz for a Born probability** with a self-adjoint first factor. -/
theorem abs_bornProb_le (M : BipartiteModel 𝒞 𝒜 ℬ) {T : 𝒜} (hT : star T = T) (D : ℬ) :
    |M.bornProb T D| ≤ M.snorm (M.πA T) * M.snorm (M.πB D) := by
  have h := M.abs_qform_πA_mul_πB_le' T D
  rw [hT] at h
  exact h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- **The substitution estimate.** Against a projective family of one player, an agreement with a
family of the other is bounded by the root of that family's total weight: the projective family's
own weights sum to one, so one Cauchy--Schwarz over the outcomes leaves only the other root. This
is what pays for replacing one measurement by another inside the helper's agreement. -/
theorem abs_sum_bornProb_le {C : Type*} [Fintype C] {M : BipartiteModel 𝒞 𝒜 ℬ}
    (hM : ‖M.ψ‖ = 1) {T : C → 𝒜} (hT : IsPVMIn T) (D : C → ℬ) :
    |∑ c, M.bornProb (T c) (D c)| ≤ Real.sqrt (∑ c, M.swap.stateSqNorm (D c)) := by
  have h1 : |∑ c, M.bornProb (T c) (D c)|
      ≤ ∑ c, M.snorm (M.πA (T c)) * M.snorm (M.πB (D c)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun c _ => abs_bornProb_le M (hT.star_eq c) (D c))
  have h3 : ∑ c, M.snorm (M.πA (T c)) ^ 2 = 1 := by
    have hc : ∀ c, M.snorm (M.πA (T c)) ^ 2 = M.bornProb (T c) 1 := fun c => by
      show M.stateSqNorm (T c) = _
      rw [M.stateSqNorm_eq_bornProb_one, hT.star_eq, hT.idem]
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hc c, ← M.bornProb_sum_left,
      hT.sum_eq_one, M.bornProb_one_one hM]
  have h2 := sum_mul_le_sqrt (fun c => M.snorm (M.πA (T c))) (fun c => M.snorm (M.πB (D c)))
  rw [h3, Real.sqrt_one, one_mul] at h2
  exact h1.trans h2

end Substitute

/-! ## The same statement on the expanded state -/

section Expanded

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The convolution shape of a hatted point measurement: the party's own reading tensored with the
ancilla's syndrome measurement, summed along the sum of outcomes. -/
theorem hatPtPOVM_mats_eq_conv (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (u : Point F m) (a : F) :
    (hatPtPOVM P W u).op a
      = conv (fun o => ((P (.point W u)).map rdVal).op o)
        (fun b => (((synPOVM W u).mats b).val)) a :=
  POVMIn.map_op _ _ _

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The same shape for the Pauli basis answer read at the point. -/
theorem hatPauliPOVM_mats_eq_conv (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (u : Point F m) (a : F) :
    ((kronIn ((P (.pauli W)).map (rdPauli u)) (synPOVM W u) (isPVM_synPOVM W u)).map
        fun p => p.1 + p.2).op a
      = conv (fun o => ((P (.pauli W)).map (rdPauli u)).op o)
        (fun b => (((synPOVM W u).mats b).val)) a :=
  POVMIn.map_op _ _ _

end Expanded

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
  {ε : ℝ}

/-- **The same-party closeness, on the expanded state.** The hatted point measurement and the
hatted Pauli basis reading differ, on Bob's side of the register model, by what the bare
measurements differ by: the shared register factor drops out exactly, so the constant is
unchanged. -/
theorem sum_normSq_hat_point_sub_pauli_le [StarModule ℂ ℬ] [StarProper ℬ] (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ a : F, (M.reg (Anc F m)).swap.stateSqNorm ((hatPtPOVM PB W (c.pt W)).op a
          - ((kronIn ((PB (.pauli W)).map (rdPauli (c.pt W))) (synPOVM W (c.pt W))
              (isPVM_synPOVM W (c.pt W))).map fun p => p.1 + p.2).op a)
      ≤ 688 * ε := by
  have hbare := sum_normSq_point_sub_pauli_le (PB := PB) hM hfail W
  have hterm : ∀ c : Content F m,
      ∑ a : F, (M.reg (Anc F m)).swap.stateSqNorm ((hatPtPOVM PB W (c.pt W)).op a
        - ((kronIn ((PB (.pauli W)).map (rdPauli (c.pt W))) (synPOVM W (c.pt W))
            (isPVM_synPOVM W (c.pt W))).map fun p => p.1 + p.2).op a)
      = ∑ a : F, M.swap.stateSqNorm (((PB (.point W (c.pt W))).map rdVal).op a
          - ((PB (.pauli W)).map (rdPauli (c.pt W))).op a) := by
    intro c
    have hconv : ∀ a : F,
        (hatPtPOVM PB W (c.pt W)).op a
          - ((kronIn ((PB (.pauli W)).map (rdPauli (c.pt W))) (synPOVM W (c.pt W))
            (isPVM_synPOVM W (c.pt W))).map fun p => p.1 + p.2).op a
        = conv (fun o => ((PB (.point W (c.pt W))).map rdVal).op o
            - ((PB (.pauli W)).map (rdPauli (c.pt W))).op o)
          (fun b => (((synPOVM W (c.pt W)).mats b).val)) a := by
      intro a
      rw [hatPtPOVM_mats_eq_conv, hatPauliPOVM_mats_eq_conv, conv, conv, conv,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => smulKron_sub_left _ _ _
    simp only [hconv]
    exact sum_normSq_stateVecB_conv_eq M Introspection.registerEPR_norm _ (isPVM_synOfPOVM W _)
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by rw [hterm c]]
  exact hbare

end MIPRE.QLD

end

end
