/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Sign
public import MIPRE.Foundations.StateDistance
public import MIPRE.Foundations.CrossConsistency
public import MIPRE.Foundations.Swap
public import MIPRE.Foundations.POVMValue
public import MIPRE.LCS.MagicSquare.Game

@[expose] public section

/-!
# Direct Magic Square anticommutation

Blueprint `lem:ms-direct-anticomm`: a strategy failing the Magic Square game with probability
`ε` has `‖{B₁, B₅}|ψ⟩‖² ≤ 186624 ε` for the *original* `±1`-observables of the player who receives
the variables --- no isometry and no extracted EPR pairs. This is the only thing the Pauli basis
test consumes from the Magic Square, and it is much weaker than the full rigidity theorem
`thm:ms-rigidity`, which this repository does not prove.

## The shape of the argument

Alice's constraint answers are **repaired** to parity-valid ones and pushed forward to a
measurement with four outcomes (`repPOVM`). Her measurements are projective, and a
coarse-graining of a projective measurement is projective (`isPVMIn_repPOVM`), so the repaired
measurement is one too. Signed sums of it are reflections that commute within a constraint and
multiply to its sign *exactly* (`MIPRE.IsPVMIn.pvmObs_mul_mul`) --- that is what projectivity
buys, and it is why the repair has to happen first.

The rest is norm bookkeeping on the state, in the operator-bound calculus of the model
(`MIPRE/Foundations/StateModel.lean`): each of Alice's reflections is within `γ` of the
corresponding Bob observable, `γ² ≤ 144 ε`; a Bob word of length `t` can be replaced by the
reversed word of Alice reflections at cost `t γ`; a within-constraint relation costs `3 γ`; and
the six-step path through the six constraints turns `d a e b` into `- d e a b` at cost `24 γ`.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The strategy is a model
`M : BipartiteModel 𝒞 𝒜 ℬ` with `‖M.ψ‖ = 1` and two families of POVMs `PA`, `PB` in the players'
ordered algebras (`POVMIn _ 𝒜`, `POVMIn _ ℬ`). The operators are elements of `𝒜` and `ℬ` acting
through `M.πA` and `M.πB`, the norms are the model's (`M.snorm`, and `M.swap.stateSqNorm` for the
second player's `‖(Id ⊗ Y)|ψ⟩‖²`), and the value is `M.povmValue`. The constraint player's
measurements are **projective** (`IsPVMIn`), as every strategy of the Pauli basis test is from the
start. So the Naimark dilation of the matrix statement --- whose only purpose was to make the
repaired measurement projective, on one ancilla shared by the six constraints --- is gone: the
repaired measurement is used as it is, on the model's own state, and its reflections are
elements of the first player's algebra. The variable player's measurements stay arbitrary POVMs;
the other player's half of the lemma (`ms_direct_anticomm'`) asks for his to be projective
instead. On a unit vector `ψ : dA × dB → ℂ` the statement is read at the tensor-product model
`BipartiteModel.tensor ψ` with the families `POVM.toIn` (projectivity through `IsPVM.toIn`),
where `M.swap.stateSqNorm Y` is `‖stateVecB ψ Y‖²` (`normSq_stateVecB_eq_tensor`) and the value is
`povmValue` (`povmValue_eq_tensor`).
-/

noncomputable section

namespace MIPRE.QLD.MS

open Finset MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare

/-! ## Alice's repaired outcomes

A parity-valid answer to a constraint is determined by its bits at the first two cells, so the
repaired outcome set is `ZMod 2 × ZMod 2` and the bit at the third cell is read off the
constraint's right-hand side. -/

/-- The repaired outcome set of a constraint. -/
abbrev PV : Type := ZMod 2 × ZMod 2

/-- The bit that outcome `k` assigns to cell `j` of constraint `c`. -/
def pvBit (c : Fin layout.r) (k : PV) (j : Fin 3) : ZMod 2 :=
  if j = 0 then k.1 else if j = 1 then k.2 else game.b c + k.1 + k.2

theorem pvBit_sum (c : Fin layout.r) (k : PV) :
    pvBit c k 0 + pvBit c k 1 + pvBit c k 2 = game.b c := by
  revert c k
  decide

/-- The sign weighting of constraint `c` at its `j`-th cell. -/
def csgn (c : Fin layout.r) (j : Fin 3) : PV → ℂ := fun k => sgn (pvBit c k j)

theorem csgn_mul_self (c : Fin layout.r) (j : Fin 3) (k : PV) :
    csgn c j k * csgn c j k = 1 := sgn_mul_self _

theorem star_csgn (c : Fin layout.r) (j : Fin 3) (k : PV) :
    star (csgn c j k) = csgn c j k := star_sgn _

/-- **The three signs of a constraint multiply to its sign.** -/
theorem csgn_prod (c : Fin layout.r) (k : PV) :
    csgn c 0 k * csgn c 1 k * csgn c 2 k = sgn (game.b c) := by
  rw [csgn, csgn, csgn, ← sgn_add, ← sgn_add, pvBit_sum]

/-- Alice's answer to a constraint, **repaired** to a parity-valid outcome: an assignment
satisfying the constraint keeps its bits at the first two cells, and everything else --- an
assignment violating the parity, or an answer of the wrong shape --- is sent to `(0, 0)`. This
preserves every originally winning pair, which is all the argument needs. -/
def rep (c : Fin layout.r) : layout.Answer → PV
  | .inl a => if (∑ k ∈ layout.V c, a k) = game.b c then (a (cell c 0), a (cell c 1)) else (0, 0)
  | .inr _ => (0, 0)

/-- **On a parity-valid answer the repair loses nothing**: the outcome's bit at each cell is the
answer's. For the third cell this is the parity condition. -/
theorem pvBit_rep (c : Fin layout.r) {a : Fin layout.s → ZMod 2}
    (ha : (∑ k ∈ layout.V c, a k) = game.b c) (j : Fin 3) :
    pvBit c (rep c (Sum.inl a)) j = a (cell c j) := by
  have hrep : rep c (Sum.inl a) = (a (cell c 0), a (cell c 1)) := by
    rw [rep, ite_eq_left ha]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [hrep]
  fin_cases j
  · rfl
  · rfl
  · show game.b c + a (cell c 0) + a (cell c 1) = a (cell c 2)
    rw [← ha, sum_cells, show a (cell c 0) + a (cell c 1) + a (cell c 2) + a (cell c 0)
        + a (cell c 1) = (a (cell c 0) + a (cell c 0))
          + ((a (cell c 1) + a (cell c 1)) + a (cell c 2)) from by ring,
      h2, h2, zero_add, zero_add]

/-! ## Numerals for the magic square -/

/-- Variable `k`, in row-major order. -/
def var (k : ℕ) (h : k < layout.s := by decide) : Fin layout.s := ⟨k, h⟩

/-- Constraint `c`: the three rows then the three columns. -/
def con (c : ℕ) (h : c < layout.r := by decide) : Fin layout.r := ⟨c, h⟩

/-! ## The repaired Alice measurement, and Alice's reflections

The repaired measurement is the coarse-graining of Alice's constraint measurement along `rep`,
and it is projective because hers is: this is what replaces the matrix statement's dilation. -/

section Alice

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜]

/-- Alice's repaired constraint measurement, with the four parity-valid outcomes. -/
def repPOVM (PA : layout.Question → POVMIn layout.Answer 𝒜) (c : Fin layout.r) (k : PV) : 𝒜 :=
  ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k}, (PA (Sum.inl c)).op d

theorem repPOVM_eq (PA : layout.Question → POVMIn layout.Answer 𝒜) (c : Fin layout.r) (k : PV) :
    repPOVM PA c k
      = ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k}, (PA (Sum.inl c)).op d := rfl

/-- **The repaired measurement of a projective measurement is projective**: it is a
coarse-graining. -/
theorem isPVMIn_repPOVM {PA : layout.Question → POVMIn layout.Answer 𝒜}
    (hPA : ∀ q, IsPVMIn (PA q).op) (c : Fin layout.r) : IsPVMIn (repPOVM PA c) :=
  (hPA (Sum.inl c)).coarse (rep c)

variable [Algebra ℂ 𝒜]

/-- Alice's reflection for constraint `c` at its `j`-th cell. -/
def refl (PA : layout.Question → POVMIn layout.Answer 𝒜) (c : Fin layout.r) (j : Fin 3) : 𝒜 :=
  pvmObs (repPOVM PA c) (csgn c j)

variable {PA : layout.Question → POVMIn layout.Answer 𝒜}

theorem refl_conjTranspose [StarModule ℂ 𝒜] (hPA : ∀ q, IsPVMIn (PA q).op) (c : Fin layout.r)
    (j : Fin 3) : star (refl PA c j) = refl PA c j :=
  (isPVMIn_repPOVM hPA c).pvmObs_star_eq fun k => star_csgn c j k

theorem refl_mul_self (hPA : ∀ q, IsPVMIn (PA q).op) (c : Fin layout.r) (j : Fin 3) :
    refl PA c j * refl PA c j = 1 :=
  (isPVMIn_repPOVM hPA c).pvmObs_mul_self fun k => csgn_mul_self c j k

theorem refl_comm (hPA : ∀ q, IsPVMIn (PA q).op) (c : Fin layout.r) (i j : Fin 3) :
    refl PA c i * refl PA c j = refl PA c j * refl PA c i :=
  (isPVMIn_repPOVM hPA c).pvmObs_comm _ _

/-- **The three reflections of a constraint multiply to its sign, exactly.** -/
theorem refl_prod (hPA : ∀ q, IsPVMIn (PA q).op) (c : Fin layout.r) :
    refl PA c 0 * refl PA c 1 * refl PA c 2 = sgn (game.b c) • 1 :=
  (isPVMIn_repPOVM hPA c).pvmObs_mul_mul fun k => csgn_prod c k

/-- **The three reflections of a constraint, in the form the relations use**: the product of the
first two is the constraint's sign times the third. -/
theorem refl_two_eq (hPA : ∀ q, IsPVMIn (PA q).op) (c : Fin layout.r) :
    refl PA c 0 * refl PA c 1 = sgn (game.b c) • refl PA c 2 := by
  have h := refl_prod hPA c
  calc refl PA c 0 * refl PA c 1 = refl PA c 0 * refl PA c 1 * refl PA c 2 * refl PA c 2 := by
        rw [mul_assoc (refl PA c 0 * refl PA c 1), refl_mul_self hPA, mul_one]
    _ = (sgn (game.b c) • (1 : 𝒜)) * refl PA c 2 := by rw [h]
    _ = sgn (game.b c) • refl PA c 2 := by rw [smul_mul_assoc, one_mul]

theorem refl_isometry [StarModule ℂ 𝒜] (hPA : ∀ q, IsPVMIn (PA q).op) (c : Fin layout.r)
    (j : Fin 3) : star (refl PA c j) * refl PA c j = 1 := by
  rw [refl_conjTranspose hPA]
  exact refl_mul_self hPA c j

omit [PartialOrder 𝒜] [Algebra ℂ 𝒜] in
theorem isometry_mul {X Y : 𝒜} (hX : star X * X = 1) (hY : star Y * Y = 1) :
    star (X * Y) * (X * Y) = 1 := by
  rw [star_mul]
  calc star Y * star X * (X * Y) = star Y * (star X * X) * Y := by simp only [mul_assoc]
    _ = star Y * Y := by rw [hX, mul_one]
    _ = 1 := hY

/-- **Alice's reflection is her constraint measurement, signed by the repaired outcome**: each
original answer contributes with the sign its repaired outcome gives the cell. -/
theorem refl_eq_sum (PA : layout.Question → POVMIn layout.Answer 𝒜) (c : Fin layout.r)
    (j : Fin 3) :
    refl PA c j = ∑ d : layout.Answer, csgn c j (rep c d) • (PA (Sum.inl c)).op d := by
  classical
  have hstep : refl PA c j = ∑ k : PV, csgn c j k • repPOVM PA c k := rfl
  rw [hstep]
  have hfib : ∀ k : PV, csgn c j k • repPOVM PA c k
      = ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k},
          csgn c j (rep c d) • (PA (Sum.inl c)).op d := by
    intro k
    rw [repPOVM_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [(Finset.mem_filter.mp hd).2]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  exact Finset.sum_fiberwise (univ : Finset layout.Answer) (rep c)
    fun d => csgn c j (rep c d) • (PA (Sum.inl c)).op d

end Alice

/-! ## Bob's observables -/

section Bob

variable {ℬ : Type*} [Ring ℬ] [StarRing ℬ] [PartialOrder ℬ]

/-- Bob's `±1`-observable at variable `j`: the difference of the two bit outcomes. Answers of
the wrong shape contribute zero, which is exactly the paper's convention. -/
def bobs (PB : layout.Question → POVMIn layout.Answer ℬ) (j : Fin layout.s) : ℬ :=
  (PB (Sum.inr j)).op (Sum.inr 0) - (PB (Sum.inr j)).op (Sum.inr 1)

theorem bobs_conjTranspose {PB : layout.Question → POVMIn layout.Answer ℬ} (j : Fin layout.s) :
    star (bobs PB j) = bobs PB j := by
  rw [bobs, star_sub, POVMIn.star_op, POVMIn.star_op]

/-- `{B₀, B₄}`, the anticommutator the Pauli basis test consumes. -/
def anti (PB : layout.Question → POVMIn layout.Answer ℬ) : ℬ :=
  bobs PB (var 0) * bobs PB (var 4) + bobs PB (var 4) * bobs PB (var 0)

end Bob

/-! ## An operator fact

`Id - b²` is a contraction for a difference `b` of two operators between `0` and `1`. It is a
statement about operators on a Hilbert space, where the functional calculus is: a player's algebra
need not have one. -/

/-- **`1 - (P - Q)²` is a contraction for `0 ≤ P, Q ≤ 1`**: it lies between `0` and `1`, the
upper bound because `(P - Q)²` is positive and the lower because `1 - (P - Q)²` is the product of
the commuting positive operators `1 - (P - Q)` and `1 + (P - Q)`. -/
theorem bnd_one_sub_sq_of_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {P Q : H →L[ℂ] H} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hQ0 : 0 ≤ Q)
    (hQ1 : Q ≤ 1) : Op.Bnd (1 - (P - Q) * (P - Q)) 1 := by
  have hsa : star (P - Q) = P - Q := by
    rw [star_sub, (IsSelfAdjoint.of_nonneg hP0).star_eq, (IsSelfAdjoint.of_nonneg hQ0).star_eq]
  have h1 : 0 ≤ 1 - (P - Q) := by
    rw [show (1 : H →L[ℂ] H) - (P - Q) = (1 - P) + Q by abel]
    exact add_nonneg (sub_nonneg.2 hP1) hQ0
  have h2 : 0 ≤ 1 + (P - Q) := by
    rw [show (1 : H →L[ℂ] H) + (P - Q) = (1 - Q) + P by abel]
    exact add_nonneg (sub_nonneg.2 hQ1) hP0
  have hc : Commute (1 - (P - Q)) (1 + (P - Q)) :=
    (Commute.one_left _).sub_left ((Commute.one_right _).add_right (Commute.refl _))
  have hprod := hc.mul_nonneg h1 h2
  rw [show (1 - (P - Q)) * (1 + (P - Q)) = 1 - (P - Q) * (P - Q) by noncomm_ring] at hprod
  have hsq : 0 ≤ (P - Q) * (P - Q) := by
    have h := star_mul_self_nonneg (P - Q)
    rwa [hsa] at h
  exact Op.bnd_one_of_nonneg_of_le_one hprod (sub_le_self _ hsq)

/-! ## The calculus on the state

Every estimate of the argument is a state norm `M.snorm` of an element of the model's algebra,
built from Alice's reflections (through `M.πA`) and Bob's observables (through `M.πB`). -/

section Calculus

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- An isometry of the first player's algebra is an isometry of the model's. -/
theorem isometry_πA (M : BipartiteModel 𝒞 𝒜 ℬ) {X : 𝒜} (h : star X * X = 1) :
    star (M.πA X) * M.πA X = 1 := by
  rw [← map_star, ← map_mul, h, map_one]

/-- `‖(πB X - πB Y) ψ‖`, the quantity every step of the word argument estimates. -/
def dd (M : BipartiteModel 𝒞 𝒜 ℬ) (X Y : ℬ) : ℝ := M.snorm (M.πB X - M.πB Y)

theorem dd_comm (M : BipartiteModel 𝒞 𝒜 ℬ) (X Y : ℬ) : dd M X Y = dd M Y X :=
  M.snorm_sub_comm _ _

theorem dd_triangle (M : BipartiteModel 𝒞 𝒜 ℬ) (X Y Z : ℬ) :
    dd M X Z ≤ dd M X Y + dd M Y Z := by
  have h : M.πB X - M.πB Z = (M.πB X - M.πB Y) + (M.πB Y - M.πB Z) := by abel
  rw [dd, h]
  exact M.snorm_add_le _ _

/-- Negating both sides changes nothing. -/
theorem dd_neg (M : BipartiteModel 𝒞 𝒜 ℬ) (X Y : ℬ) : dd M (-X) (-Y) = dd M X Y := by
  have h : M.πB (-X) - M.πB (-Y) = -(M.πB X - M.πB Y) := by
    rw [map_neg, map_neg]
    abel
  rw [dd, dd, h, M.snorm_neg]

/-- A product of Bob observables is a contraction. -/
theorem bnd_bobs_mul (M : BipartiteModel 𝒞 𝒜 ℬ) (X Y : ℬ) (hX : M.Bnd (M.πB X) 1)
    (hY : M.Bnd (M.πB Y) 1) : M.Bnd (M.πB (X * Y)) 1 := by
  rw [map_mul]
  have h := StateModel.Bnd.mul _ (by norm_num : (0 : ℝ) ≤ 1) hX hY
  rwa [one_mul] at h

/-- A Bob prefix does not increase the distance. -/
theorem dd_prefix {M : BipartiteModel 𝒞 𝒜 ℬ} {P : ℬ} (hP : M.Bnd (M.πB P) 1) (X Y : ℬ) :
    dd M (P * X) (P * Y) ≤ dd M X Y := by
  have h : M.πB (P * X) - M.πB (P * Y) = M.πB P * (M.πB X - M.πB Y) := by
    rw [map_mul, map_mul, mul_sub]
  rw [dd, h]
  have := M.snorm_mul_le hP (M.πB X - M.πB Y)
  rw [one_mul] at this
  exact this

/-- **Appending a Bob suffix costs twice its replacement cost.** -/
theorem dd_suffix {M : BipartiteModel 𝒞 𝒜 ℬ} {X Y W : ℬ} {XD : 𝒜} {δ : ℝ}
    (hX : M.Bnd (M.πB X) 1) (hY : M.Bnd (M.πB Y) 1) (hXD : star XD * XD = 1)
    (hδ : M.snorm (M.πB W - M.πA XD) ≤ δ) :
    dd M (X * W) (Y * W) ≤ dd M X Y + 2 * δ := by
  have hZ : M.Bnd (M.πB X - M.πB Y) 2 := by
    have h := StateModel.Bnd.sub _ hX hY
    rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
    exact h
  have hcomm : M.πA XD * (M.πB X - M.πB Y) = (M.πB X - M.πB Y) * M.πA XD := by
    rw [mul_sub, sub_mul, (M.commute XD X).eq, (M.commute XD Y).eq]
  have h : M.πB (X * W) - M.πB (Y * W) = (M.πB X - M.πB Y) * M.πB W := by
    rw [map_mul, map_mul, sub_mul]
  rw [dd, h]
  exact M.snorm_mul_swap (isometry_πA M hXD) hcomm hZ (by norm_num) hδ

/-- Bob's observable is a contraction: the difference of two POVM elements. -/
theorem bnd_bobs (M : BipartiteModel 𝒞 𝒜 ℬ) [PartialOrder ℬ] [StarOrderedRing ℬ]
    {PB : layout.Question → POVMIn layout.Answer ℬ} (j : Fin layout.s) :
    M.Bnd (M.πB (bobs PB j)) 1 :=
  M.swap.bnd_πA_sub (PB (Sum.inr j)) (Sum.inr 0) (Sum.inr 1)

/-- Alice's reflection is an isometry of the model's algebra. -/
theorem alice_isometry (M : BipartiteModel 𝒞 𝒜 ℬ) [PartialOrder 𝒜] [StarModule ℂ 𝒜]
    {PA : layout.Question → POVMIn layout.Answer 𝒜} (hPA : ∀ q, IsPVMIn (PA q).op)
    (c : Fin layout.r) (j : Fin 3) :
    star (M.πA (refl PA c j)) * M.πA (refl PA c j) = 1 :=
  isometry_πA M (refl_isometry hPA c j)

theorem bnd_alice (M : BipartiteModel 𝒞 𝒜 ℬ) [PartialOrder 𝒜] [StarModule ℂ 𝒜]
    {PA : layout.Question → POVMIn layout.Answer 𝒜} (hPA : ∀ q, IsPVMIn (PA q).op)
    (c : Fin layout.r) (j : Fin 3) : M.Bnd (M.πA (refl PA c j)) 1 :=
  M.bnd_one_of_isometry (alice_isometry M hPA c j)

/-- The anticommutator is bounded by two. -/
theorem bnd_anti (M : BipartiteModel 𝒞 𝒜 ℬ) [PartialOrder ℬ] [StarOrderedRing ℬ]
    {PB : layout.Question → POVMIn layout.Answer ℬ} : M.Bnd (M.πB (anti PB)) 2 := by
  rw [anti, map_add]
  have h1 := bnd_bobs_mul M (bobs PB (var 0)) (bobs PB (var 4)) (bnd_bobs M _) (bnd_bobs M _)
  have h2 := bnd_bobs_mul M (bobs PB (var 4)) (bobs PB (var 0)) (bnd_bobs M _) (bnd_bobs M _)
  have h := StateModel.Bnd.add _ h1 h2
  rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
  exact h

/-- **`Id - b²` is a contraction**, because `0 ≤ b² ≤ 1`. -/
theorem bnd_one_sub_sq (M : BipartiteModel 𝒞 𝒜 ℬ) [PartialOrder ℬ] [StarOrderedRing ℬ]
    {PB : layout.Question → POVMIn layout.Answer ℬ} (j : Fin layout.s) :
    M.Bnd (M.πB (1 - bobs PB j * bobs PB j)) 1 := by
  have hP0 := M.π_πB_nonneg ((PB (Sum.inr j)).op_nonneg (Sum.inr 0))
  have hP1 := M.swap.π_πA_le_one ((PB (Sum.inr j)).op_le_one (Sum.inr 0))
  have hQ0 := M.π_πB_nonneg ((PB (Sum.inr j)).op_nonneg (Sum.inr 1))
  have hQ1 := M.swap.π_πA_le_one ((PB (Sum.inr j)).op_le_one (Sum.inr 1))
  have hT : M.π (M.πB (1 - bobs PB j * bobs PB j))
      = 1 - (M.π (M.πB ((PB (Sum.inr j)).op (Sum.inr 0)))
            - M.π (M.πB ((PB (Sum.inr j)).op (Sum.inr 1))))
          * (M.π (M.πB ((PB (Sum.inr j)).op (Sum.inr 0)))
            - M.π (M.πB ((PB (Sum.inr j)).op (Sum.inr 1)))) := by
    simp only [bobs, map_sub, map_one, map_mul]
  show Op.Bnd (M.π (M.πB (1 - bobs PB j * bobs PB j))) 1
  rw [hT]
  exact bnd_one_sub_sq_of_sub hP0 hP1 hQ0 hQ1

end Calculus

/-! ## Replacing Bob's letters by Alice's reflections

A Bob word of length `t` agrees on the state with the *reversed* word of Alice reflections to
within `t γ`: replace the letters one at a time from the right, each replacement costing `γ`,
and cross the two players' algebras so the Alice letters accumulate in the opposite order. Only
lengths one, two and three occur in the argument, so the three cases are spelled out rather than
induced. -/

section Words

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : layout.Question → POVMIn layout.Answer 𝒜} {PB : layout.Question → POVMIn layout.Answer ℬ}
  {γ : ℝ}

omit [StarOrderedRing ℬ] [StarModule ℂ 𝒜] in
theorem word1 (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ)
    (c : Fin layout.r) (j : Fin 3) :
    M.snorm (M.πB (bobs PB (cell c j)) - M.πA (refl PA c j)) ≤ γ := by
  rw [M.snorm_sub_comm]
  exact hγ c j

theorem word2 (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ)
    (c c' : Fin layout.r) (i j : Fin 3) :
    M.snorm (M.πB (bobs PB (cell c i) * bobs PB (cell c' j))
      - M.πA (refl PA c' j * refl PA c i)) ≤ 2 * γ := by
  have h1 : M.πA (refl PA c' j) * M.πB (bobs PB (cell c i))
      = M.πB (bobs PB (cell c i)) * M.πA (refl PA c' j) := (M.commute _ _).eq
  have hsplit : M.πB (bobs PB (cell c i) * bobs PB (cell c' j))
        - M.πA (refl PA c' j * refl PA c i)
      = M.πB (bobs PB (cell c i)) * (M.πB (bobs PB (cell c' j)) - M.πA (refl PA c' j))
        + M.πA (refl PA c' j) * (M.πB (bobs PB (cell c i)) - M.πA (refl PA c i)) := by
    rw [map_mul, map_mul, mul_sub, mul_sub, h1]
    abel
  rw [hsplit]
  refine le_trans (M.snorm_add_le _ _) ?_
  have hb := M.snorm_mul_le (bnd_bobs M (PB := PB) (cell c i))
    (M.πB (bobs PB (cell c' j)) - M.πA (refl PA c' j))
  have ha := M.snorm_mul_le (bnd_alice M hPA c' j)
    (M.πB (bobs PB (cell c i)) - M.πA (refl PA c i))
  have hw1 := word1 hγ c' j
  have hw2 := word1 hγ c i
  linarith

theorem word3 (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ)
    (c c' c'' : Fin layout.r) (i j k : Fin 3) :
    M.snorm (M.πB (bobs PB (cell c i) * bobs PB (cell c' j) * bobs PB (cell c'' k))
      - M.πA (refl PA c'' k * (refl PA c' j * refl PA c i))) ≤ 3 * γ := by
  have hcomm : M.πA (refl PA c'' k) * M.πB (bobs PB (cell c i) * bobs PB (cell c' j))
      = M.πB (bobs PB (cell c i) * bobs PB (cell c' j)) * M.πA (refl PA c'' k) :=
    (M.commute _ _).eq
  have hsplit : M.πB (bobs PB (cell c i) * bobs PB (cell c' j) * bobs PB (cell c'' k))
        - M.πA (refl PA c'' k * (refl PA c' j * refl PA c i))
      = M.πB (bobs PB (cell c i) * bobs PB (cell c' j))
          * (M.πB (bobs PB (cell c'' k)) - M.πA (refl PA c'' k))
        + M.πA (refl PA c'' k)
          * (M.πB (bobs PB (cell c i) * bobs PB (cell c' j))
              - M.πA (refl PA c' j * refl PA c i)) := by
    rw [map_mul M.πB (bobs PB (cell c i) * bobs PB (cell c' j)), map_mul M.πA (refl PA c'' k),
      mul_sub, mul_sub, hcomm]
    abel
  rw [hsplit]
  refine le_trans (M.snorm_add_le _ _) ?_
  have hbb := bnd_bobs_mul M (bobs PB (cell c i)) (bobs PB (cell c' j))
    (bnd_bobs M _) (bnd_bobs M _)
  have hb := M.snorm_mul_le hbb (M.πB (bobs PB (cell c'' k)) - M.πA (refl PA c'' k))
  have ha := M.snorm_mul_le (bnd_alice M hPA c'' k)
    (M.πB (bobs PB (cell c i) * bobs PB (cell c' j)) - M.πA (refl PA c' j * refl PA c i))
  have hw1 := word1 hγ c'' k
  have hw2 := word2 hPA hγ c c' i j
  linarith

end Words

/-! ## Rewriting inside a word -/

section Rewrites

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : layout.Question → POVMIn layout.Answer 𝒜} {PB : layout.Question → POVMIn layout.Answer ℬ}
  {γ : ℝ}

/-- **A within-constraint relation costs `3 γ`.** The two Bob letters are transported to the
constraint's two Alice reflections, which costs `2 γ`; their product *is* the third reflection
times the constraint's sign, with no error; and that reflection is returned to Bob for a
further `γ`. -/
theorem relation_core (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ)
    (c : Fin layout.r) (i j : Fin 3)
    (hij : refl PA c j * refl PA c i = sgn (game.b c) • refl PA c 2) :
    dd M (bobs PB (cell c i) * bobs PB (cell c j)) (sgn (game.b c) • bobs PB (cell c 2))
      ≤ 3 * γ := by
  have h1 := word2 hPA hγ c c i j
  rw [hij] at h1
  have h2 : M.snorm (M.πA (sgn (game.b c) • refl PA c 2)
      - M.πB (sgn (game.b c) • bobs PB (cell c 2))) ≤ γ := by
    rw [map_smul, map_smul, ← smul_sub, M.snorm_smul, norm_sgn, one_mul]
    exact hγ c 2
  have hsplit : M.πB (bobs PB (cell c i) * bobs PB (cell c j))
        - M.πB (sgn (game.b c) • bobs PB (cell c 2))
      = (M.πB (bobs PB (cell c i) * bobs PB (cell c j)) - M.πA (sgn (game.b c) • refl PA c 2))
        + (M.πA (sgn (game.b c) • refl PA c 2)
            - M.πB (sgn (game.b c) • bobs PB (cell c 2))) := by
    abel
  rw [dd, hsplit]
  refine le_trans (M.snorm_add_le _ _) ?_
  linarith

theorem relation10 (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ)
    (c : Fin layout.r) :
    dd M (bobs PB (cell c 1) * bobs PB (cell c 0)) (sgn (game.b c) • bobs PB (cell c 2))
      ≤ 3 * γ :=
  relation_core hPA hγ c 1 0 (refl_two_eq hPA c)

theorem relation01 (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ)
    (c : Fin layout.r) :
    dd M (bobs PB (cell c 0) * bobs PB (cell c 1)) (sgn (game.b c) • bobs PB (cell c 2))
      ≤ 3 * γ :=
  relation_core hPA hγ c 0 1 (by rw [refl_comm hPA]; exact refl_two_eq hPA c)

end Rewrites

/-! ## The six-step path

`d a e b` becomes `- d e a b` by applying the six constraints in turn --- column one, column
two, row three, column three, row two, row one --- at a total cost of `24 γ`. The sign appears
exactly once, at column three, which is the constraint of product `-1`. -/

section Path

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : layout.Question → POVMIn layout.Answer 𝒜} {PB : layout.Question → POVMIn layout.Answer ℬ}
  {γ : ℝ}

/-- **The six-step path.** -/
theorem path (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ) :
    dd M (bobs PB (var 3) * bobs PB (var 0) * (bobs PB (var 4) * bobs PB (var 1)))
      (-(bobs PB (var 3) * bobs PB (var 4) * (bobs PB (var 0) * bobs PB (var 1)))) ≤ 24 * γ := by
  have c00 : cell (con 0) 0 = var 0 := rfl
  have c01 : cell (con 0) 1 = var 1 := rfl
  have c02 : cell (con 0) 2 = var 2 := rfl
  have c10 : cell (con 1) 0 = var 3 := rfl
  have c11 : cell (con 1) 1 = var 4 := rfl
  have c12 : cell (con 1) 2 = var 5 := rfl
  have c20 : cell (con 2) 0 = var 6 := rfl
  have c21 : cell (con 2) 1 = var 7 := rfl
  have c22 : cell (con 2) 2 = var 8 := rfl
  have c30 : cell (con 3) 0 = var 0 := rfl
  have c31 : cell (con 3) 1 = var 3 := rfl
  have c32 : cell (con 3) 2 = var 6 := rfl
  have c40 : cell (con 4) 0 = var 1 := rfl
  have c41 : cell (con 4) 1 = var 4 := rfl
  have c42 : cell (con 4) 2 = var 7 := rfl
  have c50 : cell (con 5) 0 = var 2 := rfl
  have c51 : cell (con 5) 1 = var 5 := rfl
  have c52 : cell (con 5) 2 = var 8 := rfl
  have hb0 : game.b (con 0) = 0 := by decide
  have hb1 : game.b (con 1) = 0 := by decide
  have hb2 : game.b (con 2) = 0 := by decide
  have hb3 : game.b (con 3) = 0 := by decide
  have hb4 : game.b (con 4) = 0 := by decide
  have hb5 : game.b (con 5) = 1 := by decide
  have hb34 : M.Bnd (M.πB (bobs PB (var 3) * bobs PB (var 4))) 1 :=
    bnd_bobs_mul M _ _ (bnd_bobs M _) (bnd_bobs M _)
  have hb30 : M.Bnd (M.πB (bobs PB (var 3) * bobs PB (var 0))) 1 :=
    bnd_bobs_mul M _ _ (bnd_bobs M _) (bnd_bobs M _)
  -- the six within-constraint relations
  have r3 : dd M (bobs PB (var 3) * bobs PB (var 0)) (bobs PB (var 6)) ≤ 3 * γ := by
    have h := relation10 hPA hγ (con 3)
    rw [c31, c30, c32, hb3, sgn_zero, one_smul] at h
    exact h
  have r4 : dd M (bobs PB (var 4) * bobs PB (var 1)) (bobs PB (var 7)) ≤ 3 * γ := by
    have h := relation10 hPA hγ (con 4)
    rw [c41, c40, c42, hb4, sgn_zero, one_smul] at h
    exact h
  have r2 : dd M (bobs PB (var 6) * bobs PB (var 7)) (bobs PB (var 8)) ≤ 3 * γ := by
    have h := relation01 hPA hγ (con 2)
    rw [c20, c21, c22, hb2, sgn_zero, one_smul] at h
    exact h
  have r5 : dd M (bobs PB (var 5) * bobs PB (var 2)) (-bobs PB (var 8)) ≤ 3 * γ := by
    have h := relation10 hPA hγ (con 5)
    rw [c51, c50, c52, hb5, sgn_one, neg_one_smul] at h
    exact h
  have r1 : dd M (bobs PB (var 5)) (bobs PB (var 3) * bobs PB (var 4)) ≤ 3 * γ := by
    have h := relation01 hPA hγ (con 1)
    rw [c10, c11, c12, hb1, sgn_zero, one_smul] at h
    rw [dd_comm]
    exact h
  have r0 : dd M (bobs PB (var 2)) (bobs PB (var 0) * bobs PB (var 1)) ≤ 3 * γ := by
    have h := relation01 hPA hγ (con 0)
    rw [c00, c01, c02, hb0, sgn_zero, one_smul] at h
    rw [dd_comm]
    exact h
  -- step 1: `d a e b` to `g e b`, with the suffix `e b`
  have s1 : dd M (bobs PB (var 3) * bobs PB (var 0) * (bobs PB (var 4) * bobs PB (var 1)))
      (bobs PB (var 6) * (bobs PB (var 4) * bobs PB (var 1))) ≤ 7 * γ := by
    have hsuf := word2 hPA hγ (con 4) (con 4) 1 0
    rw [c41, c40] at hsuf
    have h := dd_suffix (M := M) (X := bobs PB (var 3) * bobs PB (var 0)) (Y := bobs PB (var 6))
      (W := bobs PB (var 4) * bobs PB (var 1)) hb30 (bnd_bobs M _)
      (isometry_mul (refl_isometry hPA (con 4) 0) (refl_isometry hPA (con 4) 1)) hsuf
    linarith
  -- step 2: `g e b` to `g h`, behind the prefix `g`
  have s2 : dd M (bobs PB (var 6) * (bobs PB (var 4) * bobs PB (var 1)))
      (bobs PB (var 6) * bobs PB (var 7)) ≤ 3 * γ := by
    have h := dd_prefix (M := M) (P := bobs PB (var 6)) (bnd_bobs M _)
      (bobs PB (var 4) * bobs PB (var 1)) (bobs PB (var 7))
    linarith
  -- step 3: `g h` to `i`
  have s3 : dd M (bobs PB (var 6) * bobs PB (var 7)) (bobs PB (var 8)) ≤ 3 * γ := r2
  -- step 4: `i` to `- f c`, the one constraint of product `-1`
  have s4 : dd M (bobs PB (var 8)) (-(bobs PB (var 5) * bobs PB (var 2))) ≤ 3 * γ := by
    rw [dd_comm]
    have h := dd_neg M (bobs PB (var 5) * bobs PB (var 2)) (-bobs PB (var 8))
    rw [neg_neg] at h
    rw [h]
    exact r5
  -- step 5: `- f c` to `- d e c`, with the suffix `c`
  have s5 : dd M (-(bobs PB (var 5) * bobs PB (var 2)))
      (-(bobs PB (var 3) * bobs PB (var 4) * bobs PB (var 2))) ≤ 5 * γ := by
    have hw := word1 hγ (con 0) 2
    rw [c02] at hw
    have h := dd_suffix (M := M) (X := bobs PB (var 5)) (Y := bobs PB (var 3) * bobs PB (var 4))
      (W := bobs PB (var 2)) (bnd_bobs M _) hb34 (refl_isometry hPA (con 0) 2) hw
    rw [dd_neg]
    linarith
  -- step 6: `- d e c` to `- d e a b`, behind the prefix `d e`
  have s6 : dd M (-(bobs PB (var 3) * bobs PB (var 4) * bobs PB (var 2)))
      (-(bobs PB (var 3) * bobs PB (var 4) * (bobs PB (var 0) * bobs PB (var 1)))) ≤ 3 * γ := by
    have h := dd_prefix (M := M) (P := bobs PB (var 3) * bobs PB (var 4)) hb34
      (bobs PB (var 2)) (bobs PB (var 0) * bobs PB (var 1))
    rw [dd_neg]
    linarith
  -- chain the six steps
  have t1 := dd_triangle M (bobs PB (var 3) * bobs PB (var 0) * (bobs PB (var 4) * bobs PB (var 1)))
    (bobs PB (var 6) * (bobs PB (var 4) * bobs PB (var 1)))
    (-(bobs PB (var 3) * bobs PB (var 4) * (bobs PB (var 0) * bobs PB (var 1))))
  have t2 := dd_triangle M (bobs PB (var 6) * (bobs PB (var 4) * bobs PB (var 1)))
    (bobs PB (var 6) * bobs PB (var 7))
    (-(bobs PB (var 3) * bobs PB (var 4) * (bobs PB (var 0) * bobs PB (var 1))))
  have t3 := dd_triangle M (bobs PB (var 6) * bobs PB (var 7)) (bobs PB (var 8))
    (-(bobs PB (var 3) * bobs PB (var 4) * (bobs PB (var 0) * bobs PB (var 1))))
  have t4 := dd_triangle M (bobs PB (var 8)) (-(bobs PB (var 5) * bobs PB (var 2)))
    (-(bobs PB (var 3) * bobs PB (var 4) * (bobs PB (var 0) * bobs PB (var 1))))
  have t5 := dd_triangle M (-(bobs PB (var 5) * bobs PB (var 2)))
    (-(bobs PB (var 3) * bobs PB (var 4) * bobs PB (var 2)))
    (-(bobs PB (var 3) * bobs PB (var 4) * (bobs PB (var 0) * bobs PB (var 1))))
  linarith

end Path

/-! ## Removing the two outer letters

The path bounds `‖d (a e + e a) b |ψ⟩‖`. Removing `d` costs the non-projectivity of `b_3`,
which is `‖(Id - b_3²) W |ψ⟩‖ ≤ (2 + t) γ` for a word of length `t`; removing `b` costs `2 γ`,
because Alice's reflection for variable `1` is unitary and commutes with the anticommutator. -/

section Final

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : layout.Question → POVMIn layout.Answer 𝒜} {PB : layout.Question → POVMIn layout.Answer ℬ}
  {γ : ℝ}

/-- **`‖(Id - b²)|ψ⟩‖ ≤ 2 γ`**, from `Id - b² = (D + b)(D - b)` across the two players. -/
theorem snorm_one_sub_sq (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ)
    (c : Fin layout.r) (j : Fin 3) :
    M.snorm (M.πB (1 - bobs PB (cell c j) * bobs PB (cell c j))) ≤ 2 * γ := by
  have hcomm : M.πA (refl PA c j) * M.πB (bobs PB (cell c j))
      = M.πB (bobs PB (cell c j)) * M.πA (refl PA c j) := (M.commute _ _).eq
  have hfac : M.πB (1 - bobs PB (cell c j) * bobs PB (cell c j))
      = (M.πA (refl PA c j) + M.πB (bobs PB (cell c j)))
        * (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) := by
    rw [map_sub, map_one, map_mul, add_mul, mul_sub, mul_sub, hcomm, ← map_mul M.πA,
      refl_mul_self hPA, map_one]
    abel
  rw [hfac]
  have hb : M.Bnd (M.πA (refl PA c j) + M.πB (bobs PB (cell c j))) 2 := by
    have h := StateModel.Bnd.add _ (bnd_alice M hPA c j) (bnd_bobs M (PB := PB) (cell c j))
    rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
    exact h
  refine le_trans (M.snorm_mul_le hb _) ?_
  exact mul_le_mul_of_nonneg_left (hγ c j) (by norm_num)

/-- **The anticommutator is within `36 γ` of zero on the state.** -/
theorem snorm_anti (hPA : ∀ q, IsPVMIn (PA q).op)
    (hγ : ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ≤ γ) :
    M.snorm (M.πB (anti PB)) ≤ 36 * γ := by
  have c10 : cell (con 1) 0 = var 3 := rfl
  have c11 : cell (con 1) 1 = var 4 := rfl
  have c40 : cell (con 4) 0 = var 1 := rfl
  have c30 : cell (con 3) 0 = var 0 := rfl
  -- the word `T = (a e + e a) b`
  set T : ℬ := anti PB * bobs PB (var 1) with hT
  -- step A: the path, rearranged
  have hA : M.snorm (M.πB (bobs PB (var 3) * T)) ≤ 24 * γ := by
    have h := path hPA hγ
    rw [dd] at h
    rw [show M.πB (bobs PB (var 3) * T)
        = M.πB (bobs PB (var 3) * bobs PB (var 0) * (bobs PB (var 4) * bobs PB (var 1)))
          - M.πB (-(bobs PB (var 3) * bobs PB (var 4)
              * (bobs PB (var 0) * bobs PB (var 1)))) from by
      rw [← map_sub]
      congr 1
      rw [hT, anti]
      noncomm_ring]
    exact h
  -- step B: the two length-three words, with `Id - b₃²` in front
  have hB : M.snorm (M.πB ((1 - bobs PB (var 3) * bobs PB (var 3)) * T)) ≤ 10 * γ := by
    have hz := snorm_one_sub_sq hPA hγ (con 1) 0
    rw [c10] at hz
    have hzb := bnd_one_sub_sq M (PB := PB) (var 3)
    have hstep : ∀ (X Y Z : ℬ) (cX cY cZ : Fin layout.r) (iX iY iZ : Fin 3),
        X = bobs PB (cell cX iX) → Y = bobs PB (cell cY iY) → Z = bobs PB (cell cZ iZ) →
        M.snorm (M.πB ((1 - bobs PB (var 3) * bobs PB (var 3)) * (X * Y * Z))) ≤ 5 * γ := by
      intro X Y Z cX cY cZ iX iY iZ hX hY hZ
      subst hX; subst hY; subst hZ
      have hw := word3 hPA hγ cX cY cZ iX iY iZ
      have hcomm : M.πA (refl PA cZ iZ * (refl PA cY iY * refl PA cX iX))
          * M.πB (1 - bobs PB (var 3) * bobs PB (var 3))
          = M.πB (1 - bobs PB (var 3) * bobs PB (var 3))
            * M.πA (refl PA cZ iZ * (refl PA cY iY * refl PA cX iX)) := (M.commute _ _).eq
      have hiso := isometry_mul (refl_isometry hPA cZ iZ)
        (isometry_mul (refl_isometry hPA cY iY) (refl_isometry hPA cX iX))
      have h := M.snorm_mul_swap (isometry_πA M hiso) hcomm hzb (by norm_num) hw
      rw [← map_mul] at h
      linarith
    have h1 := hstep (bobs PB (var 0)) (bobs PB (var 4)) (bobs PB (var 1))
      (con 3) (con 1) (con 4) 0 1 0 (congrArg (bobs PB) c30.symm)
      (congrArg (bobs PB) c11.symm) (congrArg (bobs PB) c40.symm)
    have h2 := hstep (bobs PB (var 4)) (bobs PB (var 0)) (bobs PB (var 1))
      (con 1) (con 3) (con 4) 1 0 0 (congrArg (bobs PB) c11.symm)
      (congrArg (bobs PB) c30.symm) (congrArg (bobs PB) c40.symm)
    have hsplit : (1 - bobs PB (var 3) * bobs PB (var 3)) * T
        = (1 - bobs PB (var 3) * bobs PB (var 3))
            * (bobs PB (var 0) * bobs PB (var 4) * bobs PB (var 1))
          + (1 - bobs PB (var 3) * bobs PB (var 3))
            * (bobs PB (var 4) * bobs PB (var 0) * bobs PB (var 1)) := by
      rw [hT, anti]
      noncomm_ring
    rw [hsplit, map_add]
    refine le_trans (M.snorm_add_le _ _) ?_
    linarith
  -- step C: `T` itself
  have hC : M.snorm (M.πB T) ≤ 34 * γ := by
    have hsplit : T = (1 - bobs PB (var 3) * bobs PB (var 3)) * T
        + bobs PB (var 3) * (bobs PB (var 3) * T) := by noncomm_ring
    have hlast : M.snorm (M.πB (bobs PB (var 3) * (bobs PB (var 3) * T))) ≤ 24 * γ := by
      rw [map_mul]
      refine le_trans (M.snorm_mul_le (bnd_bobs M (PB := PB) (var 3)) _) ?_
      rw [one_mul]
      exact hA
    rw [hsplit, map_add]
    refine le_trans (M.snorm_add_le _ _) ?_
    linarith
  -- step D: remove the trailing `b`
  have hD2 := hγ (con 4) 0
  rw [c40] at hD2
  have hiso := alice_isometry M hPA (con 4) 0
  have hcomm : M.πA (refl PA (con 4) 0) * M.πB (anti PB)
      = M.πB (anti PB) * M.πA (refl PA (con 4) 0) := (M.commute _ _).eq
  have hrewrite : M.snorm (M.πB (anti PB))
      = M.snorm (M.πB (anti PB) * M.πA (refl PA (con 4) 0)) := by
    rw [← hcomm, M.snorm_mul_of_isometry hiso]
  have hsplit : M.πB (anti PB) * M.πA (refl PA (con 4) 0)
      = M.πB T + M.πB (anti PB) * (M.πA (refl PA (con 4) 0) - M.πB (bobs PB (var 1))) := by
    rw [mul_sub, hT, map_mul]
    abel
  rw [hrewrite, hsplit]
  refine le_trans (M.snorm_add_le _ _) ?_
  have hlast := M.snorm_mul_le (bnd_anti M (PB := PB))
    (M.πA (refl PA (con 4) 0) - M.πB (bobs PB (var 1)))
  linarith

end Final

/-! ## From the game's value to the closeness hypothesis

The correlation `⟨ψ| C_{c,j} ⊗ B_j |ψ⟩` is agreement minus disagreement between Alice's
repaired outcome bit and Bob's answer bit, and every *winning* answer pair agrees --- that is
what the repair preserves. So the correlation is at least `1 - 2 ℓ_{c,j}`, and since
`δ²_{c,j} = 2 - 2⟨ψ| C B |ψ⟩ - (1 - ⟨ψ| B² |ψ⟩) ≤ 2 - 2⟨ψ| C B |ψ⟩`, the reflection is
within `2√ℓ` of the observable. -/

section Correlation

/-- `(-1)^x` for a bit, as a real. -/
def rsgn (x : ZMod 2) : ℝ := if x.val = 1 then -1 else 1

theorem sgn_eq_rsgn (x : ZMod 2) : sgn x = ((rsgn x : ℝ) : ℂ) := by
  rw [sgn, rsgn]; split_ifs <;> norm_num

theorem val_inj (x y : ZMod 2) (h : x.val = y.val) : x = y := by
  revert x y
  decide

theorem rsgn_mul_eq (x y : ZMod 2) :
    rsgn x * rsgn y = 2 * (if x = y then (1 : ℝ) else 0) - 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hy : y.val < 2 := ZMod.val_lt y
  have hiff : (x = y) ↔ (x.val = y.val) :=
    ⟨fun h => by rw [h], fun h => val_inj x y h⟩
  rw [rsgn, rsgn, show (if x = y then (1 : ℝ) else 0)
      = (if x.val = y.val then (1 : ℝ) else 0) from by
    by_cases h : x = y
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.mpr hc))]]
  interval_cases h1 : x.val <;> interval_cases h2 : y.val <;> norm_num

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]

/-- The signed Born mass at an incidence: Alice's repaired outcome bit against Bob's answer
bit, agreement counting `+1` and disagreement `-1`. -/
def corr (M : BipartiteModel 𝒞 𝒜 ℬ) (PA : layout.Question → POVMIn layout.Answer 𝒜)
    (PB : layout.Question → POVMIn layout.Answer ℬ) (c : Fin layout.r) (j : Fin 3) : ℝ :=
  ∑ d : layout.Answer, ∑ w : ZMod 2,
    rsgn (pvBit c (rep c d) j) * rsgn w
      * M.bornProb ((PA (Sum.inl c)).op d) ((PB (Sum.inr (cell c j))).op (Sum.inr w))

variable [StarOrderedRing 𝒜] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  {PA : layout.Question → POVMIn layout.Answer 𝒜} {PB : layout.Question → POVMIn layout.Answer ℬ}

/-- The total Born mass on Bob's *bit* answers is at most one. -/
theorem sum_bornProb_inr_le (hM : ‖M.ψ‖ = 1) (c : Fin layout.r) (k : Fin layout.s) :
    ∑ d : layout.Answer, ∑ w : ZMod 2,
      M.bornProb ((PA (Sum.inl c)).op d) ((PB (Sum.inr k)).op (Sum.inr w)) ≤ 1 := by
  rw [← M.sum_bornProb hM (PA (Sum.inl c)) (PB (Sum.inr k))]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have h : (0 : ℝ) ≤ ∑ a' : Fin layout.s → ZMod 2,
      M.bornProb ((PA (Sum.inl c)).op d) ((PB (Sum.inr k)).op (Sum.inl a')) :=
    Finset.sum_nonneg fun a' _ =>
      M.bornProb_nonneg ((PA (Sum.inl c)).op_nonneg d) ((PB (Sum.inr k)).op_nonneg _)
  linarith

/-- **Every winning answer pair agrees**, so the accepted mass is at most the agreeing mass. -/
theorem condWin_le_agree (c : Fin layout.r) (j : Fin 3) :
    M.condWin nonlocalGame PA PB (Sum.inl c) (Sum.inr (cell c j))
      ≤ ∑ d : layout.Answer, ∑ w : ZMod 2,
          (if pvBit c (rep c d) j = w then (1 : ℝ) else 0)
            * M.bornProb ((PA (Sum.inl c)).op d) ((PB (Sum.inr (cell c j))).op (Sum.inr w)) := by
  rw [BipartiteModel.condWin]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have hzero : ∀ a' : Fin layout.s → ZMod 2,
      (if nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inl a') then (1 : ℝ) else 0)
        * M.bornProb ((PA (Sum.inl c)).op d) ((PB (Sum.inr (cell c j))).op (Sum.inl a')) = 0 := by
    intro a'
    have : nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inl a') = false := by
      cases d <;> rfl
    rw [this, ite_eq_right (by simp), zero_mul]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => hzero a', Finset.sum_const_zero, zero_add]
  refine Finset.sum_le_sum fun w _ => ?_
  refine mul_le_mul_of_nonneg_right ?_
    (M.bornProb_nonneg ((PA (Sum.inl c)).op_nonneg d) ((PB _).op_nonneg _))
  by_cases hacc : nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inr w)
  · rw [ite_eq_left hacc]
    -- an accepted pair has Alice's answer parity-valid and agreeing with Bob's bit
    have hd : ∃ a : Fin layout.s → ZMod 2, d = Sum.inl a := by
      cases d with
      | inl a => exact ⟨a, rfl⟩
      | inr x => exact absurd hacc (by simp [nonlocalGame, Game.toNonlocalGame, Game.accepts])
    obtain ⟨a, rfl⟩ := hd
    have hacc' : (decide ((cell c j) ∈ layout.V c)
        && decide ((∑ k ∈ layout.V c, a k) = game.b c) && decide (a (cell c j) = w)) = true := by
      simpa [nonlocalGame, Game.toNonlocalGame, Game.accepts] using hacc
    have hpar : (∑ k ∈ layout.V c, a k) = game.b c := by
      simpa using (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hacc').1).2
    have hval : a (cell c j) = w := by
      simpa using (Bool.and_eq_true _ _ |>.mp hacc').2
    rw [ite_eq_left (by rw [pvBit_rep c hpar j, hval])]
  · rw [ite_eq_right hacc]
    split_ifs <;> norm_num

/-- **The correlation is at least `1 - 2 ℓ`.** -/
theorem one_sub_two_mul_condFail_le_corr (hM : ‖M.ψ‖ = 1) (c : Fin layout.r) (j : Fin 3) :
    1 - 2 * M.condFail nonlocalGame PA PB (Sum.inl c) (Sum.inr (cell c j))
      ≤ corr M PA PB c j := by
  set q : layout.Answer → ZMod 2 → ℝ := fun d w =>
    M.bornProb ((PA (Sum.inl c)).op d) ((PB (Sum.inr (cell c j))).op (Sum.inr w)) with hq
  have hexp : corr M PA PB c j
      = 2 * (∑ d : layout.Answer, ∑ w : ZMod 2,
            (if pvBit c (rep c d) j = w then (1 : ℝ) else 0) * q d w)
        - ∑ d : layout.Answer, ∑ w : ZMod 2, q d w := by
    rw [corr, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rsgn_mul_eq]
    ring
  have hS := sum_bornProb_inr_le (PA := PA) (PB := PB) hM c (cell c j)
  have hQ := condWin_le_agree (M := M) (PA := PA) (PB := PB) c j
  rw [hexp, BipartiteModel.condFail]
  linarith

end Correlation

/-! ## The correlation is the quadratic form -/

section Assemble

theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ w : ZMod 2, f w = f 0 + f 1 := by
  show ∑ w : Fin 2, f w = f 0 + f 1
  exact Fin.sum_univ_two f

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]
  {M : BipartiteModel 𝒞 𝒜 ℬ} {PA : layout.Question → POVMIn layout.Answer 𝒜}
  {PB : layout.Question → POVMIn layout.Answer ℬ}

/-- **The correlation is the quadratic form of `C_{c,j} ⊗ B_j`.** No projectivity: this is the
expansion of the reflection into Alice's original constraint measurement (`refl_eq_sum`). -/
theorem qform_eq_corr (c : Fin layout.r) (j : Fin 3) :
    M.qform (M.πA (refl PA c j) * M.πB (bobs PB (cell c j))) = corr M PA PB c j := by
  classical
  rw [refl_eq_sum, map_sum, Finset.sum_mul, M.qform_sum, corr]
  refine Finset.sum_congr rfl fun d _ => ?_
  -- pull out the sign
  rw [show csgn c j (rep c d) • (PA (Sum.inl c)).op d
      = ((rsgn (pvBit c (rep c d) j) : ℝ) : ℂ) • (PA (Sum.inl c)).op d from by
    rw [csgn, sgn_eq_rsgn], map_smul, smul_mul_assoc, M.qform_smul_real]
  -- expand Bob's observable
  rw [sum_zmod2 (fun w => rsgn (pvBit c (rep c d) j) * rsgn w
    * M.bornProb ((PA (Sum.inl c)).op d) ((PB (Sum.inr (cell c j))).op (Sum.inr w)))]
  have h0 : rsgn (0 : ZMod 2) = 1 := by rw [rsgn]; norm_num
  have h1 : rsgn (1 : ZMod 2) = -1 := by rw [rsgn]; norm_num
  rw [bobs, map_sub, mul_sub, M.qform_sub, h0, h1, BipartiteModel.bornProb,
    BipartiteModel.bornProb]
  ring

/-! ## The closeness hypothesis, from the game's value -/

variable [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarModule ℂ 𝒜]

theorem snorm_sq_le_condFail (hM : ‖M.ψ‖ = 1) (hPA : ∀ q, IsPVMIn (PA q).op)
    (c : Fin layout.r) (j : Fin 3) :
    M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ^ 2
      ≤ 4 * M.condFail nonlocalGame PA PB (Sum.inl c) (Sum.inr (cell c j)) := by
  set A : 𝒞 := M.πA (refl PA c j) with hA
  set B : 𝒞 := M.πB (bobs PB (cell c j)) with hB
  have hAsa : star A = A := by rw [hA, ← map_star, refl_conjTranspose hPA]
  have hBsa : star B = B := by rw [hB, ← map_star, bobs_conjTranspose]
  have hAA : A * A = 1 := by rw [hA, ← map_mul, refl_mul_self hPA, map_one]
  have hcomm : A * B = B * A := by rw [hA, hB]; exact (M.commute _ _).eq
  have hexp : star (A - B) * (A - B) = 1 - (((2 : ℝ) : ℂ)) • (A * B) + B * B := by
    rw [star_sub, hAsa, hBsa]
    have h : (A - B) * (A - B) = A * A - A * B - B * A + B * B := by noncomm_ring
    rw [h, hAA, ← hcomm]
    module
  rw [M.snorm_sq_eq_qform, hexp, M.qform_add, M.qform_sub, M.qform_one hM, M.qform_smul_real]
  have hBB : M.qform (B * B) ≤ 1 := by
    have h : M.qform (B * B) = M.snorm B ^ 2 := by
      rw [M.snorm_sq_eq_qform, hBsa]
    rw [h]
    have hb : M.snorm B ≤ 1 := by
      have := M.snorm_mul_le (bnd_bobs M (PB := PB) (cell c j)) 1
      rwa [mul_one, M.snorm_one hM, mul_one] at this
    nlinarith [M.snorm_nonneg B, hb]
  have hcorr := one_sub_two_mul_condFail_le_corr (PA := PA) (PB := PB) hM c j
  rw [qform_eq_corr]
  linarith

/-- **The closeness hypothesis, with `γ = 12 √ε`.** -/
theorem close_of_fail (hM : ‖M.ψ‖ = 1) (hPA : ∀ q, IsPVMIn (PA q).op) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - M.povmValue nonlocalGame PA PB ≤ ε) :
    ∀ c j, M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j)))
      ≤ 12 * Real.sqrt ε := by
  intro c j
  have hμ : nonlocalGame.μ (Sum.inl c) (Sum.inr (cell c j)) = 1 / 36 := by
    have hmem : cell c j ∈ layout.V c := cell_mem c j
    have hcard : (layout.V c).card = 3 := by fin_cases c <;> decide
    rw [nonlocalGame, Game.toNonlocalGame_μ]
    show (if cell c j ∈ layout.V c then 1 / (2 * (layout.r : ℝ) * ((layout.V c).card : ℝ))
      else 0) = 1 / 36
    rw [ite_eq_left hmem, hcard, show ((layout.r : ℕ) : ℝ) = 6 from by norm_num [layout]]
    norm_num
  have hℓ := M.condFail_le_div (G := nonlocalGame) (MA := PA) (MB := PB) hM hfail
    (x := Sum.inl c) (y := Sum.inr (cell c j)) (by rw [hμ]; norm_num)
  rw [hμ] at hℓ
  have hsq := snorm_sq_le_condFail (PA := PA) (PB := PB) hM hPA c j
  have hsq' : M.snorm (M.πA (refl PA c j) - M.πB (bobs PB (cell c j))) ^ 2 ≤ 144 * ε := by
    have : (4 : ℝ) * (ε / (1/36)) = 144 * ε := by ring
    linarith [hsq, hℓ, this]
  have hnn := M.snorm_nonneg (M.πA (refl PA c j) - M.πB (bobs PB (cell c j)))
  have hs : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  nlinarith [hsq', hnn, Real.sqrt_nonneg ε, hs]

end Assemble

/-! ## The lemma, for the player who receives the variables -/

section Lemma

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]

/-- **Direct Magic Square anticommutation** (blueprint `lem:ms-direct-anticomm`), for the player
who receives the variable questions, in a bipartite model. No isometry and no extracted EPR
pairs: the bound is on the original observables and the original state. The constraint player's
measurements are projective; the variable player's are arbitrary POVMs. -/
theorem ms_direct_anticomm [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarModule ℂ 𝒜]
    {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1)
    (PA : layout.Question → POVMIn layout.Answer 𝒜) (hPA : ∀ q, IsPVMIn (PA q).op)
    (PB : layout.Question → POVMIn layout.Answer ℬ)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - M.povmValue nonlocalGame PA PB ≤ ε) :
    M.swap.stateSqNorm (anti PB) ≤ 186624 * ε := by
  have h36 := snorm_anti hPA (close_of_fail (PB := PB) hM hPA hε hfail)
  have hs : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  have hb : M.swap.stateNorm (anti PB) ≤ 432 * Real.sqrt ε := by
    calc M.swap.stateNorm (anti PB) = M.snorm (M.πB (anti PB)) := rfl
      _ ≤ 36 * (12 * Real.sqrt ε) := h36
      _ = 432 * Real.sqrt ε := by ring
  rw [BipartiteModel.stateSqNorm]
  nlinarith [M.swap.stateNorm_nonneg (anti PB), Real.sqrt_nonneg ε, hb, hs]

end Lemma

/-! ## The other player, by the symmetry of the game

Exchanging the players is an automorphism of the Magic Square game
(`MIPRE.LCS.Layout.questionDist_symm`, `MIPRE.LCS.Game.accepts_symm`), so Alice's half of the
lemma is Bob's half in the swapped model, `BipartiteModel.swap`. -/

section Swap

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [PartialOrder ℬ]

/-- **The value of a Magic Square strategy is unchanged by exchanging the players**, in the
swapped model. -/
theorem povmValue_swap (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : layout.Question → POVMIn layout.Answer 𝒜)
    (PB : layout.Question → POVMIn layout.Answer ℬ) :
    M.swap.povmValue nonlocalGame PB PA = M.povmValue nonlocalGame PA PB :=
  M.povmValue_swap_of_symm PA PB
    (fun x y => by
      rw [nonlocalGame, Game.toNonlocalGame_μ, Game.toNonlocalGame_μ]
      exact Layout.questionDist_symm _ x y)
    (fun x y a b => by
      rw [nonlocalGame, Game.toNonlocalGame_D, Game.toNonlocalGame_D]
      exact Game.accepts_symm game x y a b)

/-- **Direct Magic Square anticommutation for the other player.** The game is symmetric in the
players, so this is `ms_direct_anticomm` in the swapped model; now the variable player's
measurements are the projective ones. -/
theorem ms_direct_anticomm' [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarModule ℂ ℬ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1)
    (PA : layout.Question → POVMIn layout.Answer 𝒜)
    (PB : layout.Question → POVMIn layout.Answer ℬ) (hPB : ∀ q, IsPVMIn (PB q).op)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - M.povmValue nonlocalGame PA PB ≤ ε) :
    M.stateSqNorm (anti PA) ≤ 186624 * ε := by
  have hfail' : 1 - M.swap.povmValue nonlocalGame PB PA ≤ ε := by
    rw [povmValue_swap]
    exact hfail
  exact ms_direct_anticomm (M := M.swap) hM PB hPB PA hε hfail'

/-- **The averaged form.** The bound is pointwise, so averaging it over a family of strategies
in models over the same algebras costs nothing --- no Jensen step, and the same constant. -/
theorem ms_direct_anticomm_avg [StarOrderedRing 𝒜] [StarOrderedRing ℬ] [StarModule ℂ 𝒜]
    {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (M : Ω → BipartiteModel 𝒞 𝒜 ℬ) (hM : ∀ ω, ‖(M ω).ψ‖ = 1)
    (PA : Ω → layout.Question → POVMIn layout.Answer 𝒜) (hPA : ∀ ω q, IsPVMIn (PA ω q).op)
    (PB : Ω → layout.Question → POVMIn layout.Answer ℬ)
    (ε : Ω → ℝ) (hε : ∀ ω, 0 ≤ ε ω)
    (hfail : ∀ ω, 1 - (M ω).povmValue nonlocalGame (PA ω) (PB ω) ≤ ε ω) :
    ∑ ω, ν ω * (M ω).swap.stateSqNorm (anti (PB ω)) ≤ 186624 * ∑ ω, ν ω * ε ω := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h := ms_direct_anticomm (hM ω) (PA ω) (hPA ω) (PB ω) (hε ω) (hfail ω)
  calc ν ω * (M ω).swap.stateSqNorm (anti (PB ω)) ≤ ν ω * (186624 * ε ω) :=
        mul_le_mul_of_nonneg_left h (hν ω)
    _ = 186624 * (ν ω * ε ω) := by ring

end Swap

end MIPRE.QLD.MS

end

end
