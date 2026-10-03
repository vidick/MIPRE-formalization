/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.OracularSound
public import MIPRE.Foundations.Sandwich
public import MIPRE.Foundations.GameAdapt
public import MIPRE.Foundations.CommutingModel

@[expose] public section

/-!
# Soundness of oracularization, in a bipartite model

Item 2 of blueprint `thm:oracularization` at the level of games, proved once for **projective
strategies in a bipartite model** (`lem:oracular-soundness-model`; Phase 2 of
`planning/mipco-track.md`): a strategy of value at least `1 - ε` for
`MIPRE.SeededGame.oracular`, whose measurements are projective in the players' algebras, yields a
strategy in the same model, of value at least `1 - 24√ε`, for the input game
(`SeededGame.povmValue_sound_ge`). Its two readings:

* in the tensor-product model it is `SeededGame.tensorSound_value_ge` (`OracularTensor.lean`), a
  tensor-product strategy being projective;
* in the commuting-operator model it is `SeededGame.commutingOperatorValue_ge_of_oracular`:
  `ω_co` of the oracularization above `1 - ε` puts `ω_co` of the input at least `1 - 24√ε`,
  through the strategies projective in their own model that approach `ω_co`
  (`exists_isPVMIn_lt_povmValue`) and the commuting-operator strategy of a strategy in a model
  (`BipartiteModel.povmValue_le_commutingOperatorValue`).

The proof is the one of `OracularTensor.lean`, with nothing finite-dimensional in it: its uses of
projectivity — the front factors of the chain, the oracle's joint marginal, the Born
probabilities as squared masses — are hypotheses here, and legitimate by construction in both
models.

## The argument

Fix a seed `z` and write `O` for the first player's oracle measurement at `(oracle, z)`, `O^𝖠`,
`O^𝖡` for its two component marginals (`OAns.aliceView`, `OAns.bobView`, `oracleView`), `C` for
the first player's isolated-Alice measurement at `L^𝖠 z`, and `P`, `Q` for the second player's
isolated-Alice and isolated-Bob measurements at `L^𝖠 z` and `L^𝖡 z`. Then, in the model's algebra,

`πA(C_u) πB(Q_v) - πA(O^𝖠_u O^𝖡_v) = πB(Q_v)(πA(C_u) - πB(P_u))`
  `+ πB(Q_v)(πB(P_u) - πA(O^𝖠_u)) + πA(O^𝖠_u)(πB(Q_v) - πA(O^𝖡_v))`

(`BipartiteModel.sum_snorm_sq_chain`). Each front factor is a projective measurement, so it costs
nothing summed over its outcome (`StateModel.sum_snorm_sq_mul_le`), and each of the three
deviations is the cross-party consistency of one role pair — `(alice, alice)`,
`(oracle, alice)`, `(oracle, bob)` — hence at most twice that pair's conditional failure
(`BipartiteModel.xSqNorm_sum_le_condFail`). The single square root is spent once, in
`StateModel.sum_snorm_sq_ge_of_close`, the paper's `fact:approx-implies-close-value`; the oracle's
joint marginal puts at least the oracle's own acceptance probability on the accepted pairs
(`condWin_oracle_le`). Averaging over the seed, the four role pairs used carry a ninth of the
question weight each (`sum_condFail_four_le`), and `val ≥ 1 - 9ε - 2√(54ε) ≥ 1 - 24√ε`.
-/

namespace MIPRE

open Finset

/-! ## Close measurements have close values -/

namespace StateModel

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] (M : StateModel 𝒞)

/-- **Close measurements have close values**, in a state model (the paper's
`fact:approx-implies-close-value`, NW19's Fact 4.31): two families whose total squared mass on the
state is at most one put masses within `2√δ` of each other on any set of outcomes, `δ` their
summed squared deviation. -/
theorem sum_snorm_sq_ge_of_close {ι : Type*} [Fintype ι] (R O : ι → 𝒞)
    (hR : ∑ i, M.snorm (R i) ^ 2 ≤ 1) (hO : ∑ i, M.snorm (O i) ^ 2 ≤ 1) (acc : Finset ι) :
    ∑ i ∈ acc, M.snorm (O i) ^ 2 - 2 * √(∑ i, M.snorm (R i - O i) ^ 2)
      ≤ ∑ i ∈ acc, M.snorm (R i) ^ 2 := by
  set D : ι → ℝ := fun i => M.snorm (R i - O i) with hD
  set s : ι → ℝ := fun i => M.snorm (O i) + M.snorm (R i) with hs
  have hterm : ∀ i, M.snorm (O i) ^ 2 - M.snorm (R i) ^ 2 ≤ D i * s i := by
    intro i
    have h1 : M.snorm (O i) ≤ M.snorm (R i) + D i := by
      have h := M.snorm_sub_le (R i) (R i - O i)
      rwa [sub_sub_cancel] at h
    have h0 := M.snorm_nonneg (O i)
    have h0' := M.snorm_nonneg (R i)
    have hk : 0 ≤ (D i - (M.snorm (O i) - M.snorm (R i))) * s i :=
      mul_nonneg (by linarith) (by simp only [hs]; linarith)
    simp only [hs] at hk ⊢
    nlinarith [hk]
  have hD0 : ∀ i, 0 ≤ D i * s i := fun i =>
    mul_nonneg (M.snorm_nonneg _) (add_nonneg (M.snorm_nonneg _) (M.snorm_nonneg _))
  have hsum : ∑ i ∈ acc, M.snorm (O i) ^ 2 - ∑ i ∈ acc, M.snorm (R i) ^ 2
      ≤ ∑ i, D i * s i := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ i ∈ acc, (M.snorm (O i) ^ 2 - M.snorm (R i) ^ 2) ≤ ∑ i ∈ acc, D i * s i :=
          Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ∑ i, D i * s i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hD0 i
  have hs2 : ∑ i, s i ^ 2 ≤ 4 := by
    have hle : ∀ i, s i ^ 2 ≤ 2 * M.snorm (O i) ^ 2 + 2 * M.snorm (R i) ^ 2 := fun i => by
      simp only [hs]
      nlinarith [sq_nonneg (M.snorm (O i) - M.snorm (R i))]
    calc ∑ i, s i ^ 2 ≤ ∑ i, (2 * M.snorm (O i) ^ 2 + 2 * M.snorm (R i) ^ 2) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = 2 * ∑ i, M.snorm (O i) ^ 2 + 2 * ∑ i, M.snorm (R i) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 4 := by linarith
  have hsq : √(∑ i, s i ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
    exact Real.sqrt_le_sqrt hs2
  have hcs : ∑ i, D i * s i ≤ 2 * √(∑ i, D i ^ 2) :=
    calc ∑ i, D i * s i ≤ √(∑ i, D i ^ 2) * √(∑ i, s i ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ D s
      _ ≤ √(∑ i, D i ^ 2) * 2 := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ = 2 * √(∑ i, D i ^ 2) := by ring
  have hDsq : ∑ i, D i ^ 2 = ∑ i, M.snorm (R i - O i) ^ 2 := rfl
  rw [hDsq] at hcs
  linarith

/-- A projective measurement has total squared mass one on a unit state. -/
theorem sum_snorm_sq_eq_one_of_isPVMIn (hψ : ‖M.ψ‖ = 1) {ι : Type*} [Fintype ι] {P : ι → 𝒞}
    (hP : IsPVMIn P) : ∑ i, M.snorm (P i) ^ 2 = 1 := by
  rw [Finset.sum_congr rfl fun i _ => by rw [M.snorm_sq_eq_qform, hP.star_eq, hP.idem],
    ← M.qform_sum, hP.sum_eq_one, M.qform_one hψ]

/-- The squared mass of a star projection is its quadratic form. -/
theorem snorm_sq_of_isStarProjection {P : 𝒞} (hP : IsStarProjection P) :
    M.snorm P ^ 2 = M.qform P := by
  rw [M.snorm_sq_eq_qform, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]

end StateModel

/-! ## Fibres of a projective measurement -/

/-- **The product of two fibre sums of a projective measurement is the fibre sum over the
intersection**: distinct outcomes are orthogonal. -/
theorem IsPVMIn.sum_mul_sum {R Λ : Type*} [Ring R] [StarRing R] [Fintype Λ] [DecidableEq Λ]
    {P : Λ → R} (hP : IsPVMIn P) (s t : Finset Λ) :
    (∑ a ∈ s, P a) * (∑ b ∈ t, P b) = ∑ a ∈ s ∩ t, P a := by
  rw [Finset.sum_mul_sum, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ t
  · rw [ite_eq_left ha, Finset.sum_eq_single_of_mem a ha fun b _ hba => hP.orthogonal (Ne.symm hba),
      hP.idem a]
  · rw [ite_eq_right ha]
    exact Finset.sum_eq_zero fun b hb => hP.orthogonal fun hab => ha (hab ▸ hb)

/-- The coarse-graining of a POVM along the identity is the POVM. -/
theorem POVMIn.map_op_self {X R : Type*} [Fintype X] [DecidableEq X] [Ring R] [StarRing R]
    [PartialOrder R] [StarOrderedRing R] (P : POVMIn X R) (x : X) :
    (P.map fun x => x).op x = P.op x := by
  rw [POVMIn.map_op, Finset.filter_eq', ite_eq_left (Finset.mem_univ x), Finset.sum_singleton]

/-! ## The chain of three deviations, in a model -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)

/-- **The per-seed algebra.** `πA(C_u) πB(Q_v) - πA(O^𝖠_u O^𝖡_v)` splits into three
cross-party deviations, each behind a front factor that is a projective measurement and so costs
nothing summed over its outcome. -/
theorem sum_snorm_sq_chain {K : Type*} [Fintype K] (C OA OB : K → 𝒜) (P Q : K → ℬ)
    (hQ : IsPVMIn Q) (hOA : IsPVMIn OA) :
    ∑ o : K × K, M.snorm (M.πA (C o.1) * M.πB (Q o.2) - M.πA (OA o.1 * OB o.2)) ^ 2
      ≤ 3 * ∑ u, M.xSqNorm (C u) (P u) + 3 * ∑ u, M.xSqNorm (OA u) (P u)
        + 3 * ∑ v, M.xSqNorm (OB v) (Q v) := by
  have hQF : M.IsColContraction fun v => M.πB (Q v) :=
    M.isColContraction_of_isPVMIn (hQ.map M.πB)
  have hOF : M.IsColContraction fun u => M.πA (OA u) :=
    M.isColContraction_of_isPVMIn (hOA.map M.πA)
  refine le_trans (M.sum_snorm_sq_triangle3 univ
    (fun o : K × K => M.πA (C o.1) * M.πB (Q o.2))
    (fun o => M.πB (Q o.2) * M.πB (P o.1))
    (fun o => M.πA (OA o.1) * M.πB (Q o.2))
    (fun o => M.πA (OA o.1 * OB o.2))) ?_
  -- the first deviation: `πB(Q_v)(πA(C_u) - πB(P_u))`
  have h1 : ∑ o : K × K, M.snorm (M.πA (C o.1) * M.πB (Q o.2) - M.πB (Q o.2) * M.πB (P o.1)) ^ 2
      ≤ ∑ u, M.xSqNorm (C u) (P u) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    have heq : ∀ v, M.πA (C u) * M.πB (Q v) - M.πB (Q v) * M.πB (P u)
        = M.πB (Q v) * (M.πA (C u) - M.πB (P u)) := fun v => by
      rw [(M.commute (C u) (Q v)).eq, mul_sub]
    simp only [heq]
    exact M.sum_snorm_sq_mul_le (fun v => M.πB (Q v)) hQF (M.πA (C u) - M.πB (P u))
  -- the second: `πB(Q_v)(πB(P_u) - πA(O^𝖠_u))`
  have h2 : ∑ o : K × K, M.snorm (M.πB (Q o.2) * M.πB (P o.1) - M.πA (OA o.1) * M.πB (Q o.2)) ^ 2
      ≤ ∑ u, M.xSqNorm (OA u) (P u) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    have heq : ∀ v, M.πB (Q v) * M.πB (P u) - M.πA (OA u) * M.πB (Q v)
        = M.πB (Q v) * (M.πB (P u) - M.πA (OA u)) := fun v => by
      rw [(M.commute (OA u) (Q v)).eq, mul_sub]
    simp only [heq]
    have h := M.sum_snorm_sq_mul_le (fun v => M.πB (Q v)) hQF (M.πB (P u) - M.πA (OA u))
    rw [M.snorm_sub_comm (M.πB (P u))] at h
    exact h
  -- the third: `πA(O^𝖠_u)(πB(Q_v) - πA(O^𝖡_v))`
  have h3 : ∑ o : K × K, M.snorm (M.πA (OA o.1) * M.πB (Q o.2) - M.πA (OA o.1 * OB o.2)) ^ 2
      ≤ ∑ v, M.xSqNorm (OB v) (Q v) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_le_sum fun v _ => ?_
    have heq : ∀ u, M.πA (OA u) * M.πB (Q v) - M.πA (OA u * OB v)
        = M.πA (OA u) * (M.πB (Q v) - M.πA (OB v)) := fun u => by
      rw [map_mul, mul_sub]
    simp only [heq]
    have h := M.sum_snorm_sq_mul_le (fun u => M.πA (OA u)) hOF (M.πB (Q v) - M.πA (OB v))
    rw [M.snorm_sub_comm (M.πB (Q v))] at h
    exact h
  linarith

/-- The squared mass of a product of two star projections of the two players is their Born
probability. -/
theorem snorm_sq_πA_mul_πB_of_proj {U : 𝒜} {V : ℬ} (hU : IsStarProjection U)
    (hV : IsStarProjection V) : M.snorm (M.πA U * M.πB V) ^ 2 = M.bornProb U V :=
  M.snorm_sq_of_isStarProjection (M.isStarProjection_πA_mul_πB hU hV)

/-- The squared mass of a star projection of the first player is its quadratic form. -/
theorem snorm_sq_πA_of_isStarProjection {U : 𝒜} (hU : IsStarProjection U) :
    M.snorm (M.πA U) ^ 2 = M.qform (M.πA U) :=
  M.snorm_sq_of_isStarProjection (hU.map M.πA)

/-- **Post-processing the answers, question by question, loses no value**, in a model: on the
same questions and distribution, if every tuple `G` accepts is accepted by `G'` after the answers
are read through `rA`, `rB`, the coarse-grained families win `G'` at least as often. This is the
typed oracularized game's transfer to the oracularization (`SeededGame.val_typedGame_le`). -/
theorem povmValue_le_postprocess [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
    [StarOrderedRing ℬ] {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] [DecidableEq A'] [DecidableEq B'] (G : Game X Y A B)
    (G' : Game X Y A' B') (MA : X → POVMIn A 𝒜) (MB : Y → POVMIn B ℬ) (rA : X → A → A')
    (rB : Y → B → B') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y (rA x a) (rB y b) = true) :
    M.povmValue G MA MB
      ≤ M.povmValue G' (fun x => (MA x).map (rA x)) (fun y => (MB y).map (rB y)) := by
  unfold povmValue
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  rw [hμ]
  exact mul_le_mul_of_nonneg_left (M.condWin_le_condWin_adapt MA MB G' (fun x => x) (fun y => y)
    rA rB x y (hD x y)) (G.μ_nonneg x y)

end BipartiteModel

section Postprocess

open scoped MatrixOrder

variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype A']
  [Fintype B'] [DecidableEq A'] [DecidableEq B']

/-- Post-processing the answers question by question raises the quantum value, when every
accepted tuple stays accepted: `BipartiteModel.povmValue_le_postprocess` in the tensor-product
model of each strategy. -/
theorem quantumValue_le_postprocess (G : Game X Y A B) (G' : Game X Y A' B') (rA : X → A → A')
    (rB : Y → B → B') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y (rA x a) (rB y b) = true) :
    quantumValue G ≤ quantumValue G' := by
  refine Real.iSup_le (fun R => ?_) (quantumValue_nonneg _)
  refine le_trans ?_ (le_ciSup (TensorProductStrategy.bddAbove_range_value _)
    (R.adapt G' (fun x => x) (fun y => y) rA rB))
  rw [TensorProductStrategy.value_adapt, TensorProductStrategy.value_eq_tensor_povmValue]
  exact (BipartiteModel.tensor R.ψ).povmValue_le_postprocess G G' _ _ rA rB hμ hD

/-- Post-processing the answers question by question raises the commuting-operator value, when
every accepted tuple stays accepted: the model form in the model of each strategy, whose
post-processed families are a commuting-operator strategy. -/
theorem commutingOperatorValue_le_postprocess (G : Game X Y A B) (G' : Game X Y A' B')
    (rA : X → A → A') (rB : Y → B → B') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y (rA x a) (rB y b) = true) :
    commutingOperatorValue G ≤ commutingOperatorValue G' := by
  refine Real.iSup_le (fun S => ?_) (commutingOperatorValue_nonneg _)
  rw [S.value_eq_povmValue]
  exact (S.toModel.povmValue_le_postprocess G G' S.aliceMeas S.bobMeas rA rB hμ hD).trans
    (S.toModel.povmValue_le_commutingOperatorValue S.toModel_ψ_norm _ _ _)

end Postprocess

/-! ## Reading an oracle's answer one component at a time -/

section Views

variable {A : Type*}

/-- An oracularized answer read as the answer meant for the original Alice: an oracle's pair is
read as its first component; an isolated player's answer is left as it is (for an oracle it is
rejected by the shape check anyway). -/
def OAns.aliceView : OAns A → OAns A
  | .pair a _ => .single a
  | .single a => .single a

/-- An oracularized answer read as the answer meant for the original Bob. -/
def OAns.bobView : OAns A → OAns A
  | .pair _ b => .single b
  | .single b => .single b

end Views

/-! ## The three roles -/

/-- A sum over the three roles. -/
theorem Role.sum_eq {M : Type*} [AddCommMonoid M] (f : Role → M) :
    ∑ r, f r = f .oracle + f .alice + f .bob := by
  change ∑ r ∈ ({Role.oracle, Role.alice, Role.bob} : Finset Role), f r = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

namespace SeededGame

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)

/-! ## What acceptance forces -/

/-- The oracle's own answer passes the game check: it is a pair, which the input decider accepts
at the question pair the seed determines. -/
def oracleGood (z : V) : OAns A → Bool
  | .pair a b => S.D (S.LA z) (S.LB z) a b
  | .single _ => false

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem oracleGood_of_oaccepts {z : V} {q : Role × V} {w u : OAns A}
    (h : S.oaccepts (Role.oracle, z) q w u = true) : S.oracleGood z w = true := by
  cases w <;> simp_all [oaccepts, shapeOk, gameCheck, oracleGood]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem aliceView_of_oaccepts {z x : V} {w u : OAns A}
    (h : S.oaccepts (Role.oracle, z) (Role.alice, x) w u = true) : w.aliceView = u := by
  cases w <;> cases u <;> simp_all [oaccepts, shapeOk, gameCheck, oracleVsPlayer, OAns.aliceView]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem bobView_of_oaccepts {z y : V} {w v : OAns A}
    (h : S.oaccepts (Role.oracle, z) (Role.bob, y) w v = true) : w.bobView = v := by
  cases w <;> cases v <;> simp_all [oaccepts, shapeOk, gameCheck, oracleVsPlayer, OAns.bobView]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [Inhabited A] in
theorem eq_of_oaccepts_self {p : Role × V} {u v : OAns A} (h : S.oaccepts p p u v = true) :
    u = v := by
  by_contra hne
  rw [S.oaccepts_eq_false_of_ne hne] at h
  exact Bool.false_ne_true h

/-- The answer pairs the input decider accepts at the question pair the seed determines. -/
def accPairs (z : V) : Finset (A × A) :=
  univ.filter fun p => S.D (S.LA z) (S.LB z) p.1 p.2 = true

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
/-- Pairs of isolated answers. -/
def singlePairEmb : A × A ↪ OAns A × OAns A :=
  ⟨fun p => (OAns.single p.1, OAns.single p.2), fun p q h => by
    simp only [Prod.mk.injEq, OAns.single.injEq] at h
    exact Prod.ext h.1 h.2⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
@[simp] theorem singlePairEmb_apply (p : A × A) :
    singlePairEmb p = (OAns.single p.1, OAns.single p.2) := rfl

/-! ## The oracle's views, in a model -/

section Model

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
variable (MA : Role × V → POVMIn (OAns A) 𝒜) (MB : Role × V → POVMIn (OAns A) ℬ)

omit [Nonempty V] [Inhabited A] in
/-- The oracle's measurement at `(oracle, z)`, coarse-grained along a view of its answer. -/
def oracleView (z : V) (f : OAns A → OAns A) (u : OAns A) : 𝒜 :=
  ((MA (Role.oracle, z)).map f).op u

omit [Fintype V] [DecidableEq V] [Nonempty V] [Inhabited A] [Algebra ℂ 𝒜] in
theorem isPVMIn_oracleView (hA : ∀ q, IsPVMIn (MA q).op) (z : V) (f : OAns A → OAns A) :
    IsPVMIn (oracleView MA z f) := by
  rw [show oracleView MA z f = fun u => ∑ w ∈ univ.filter fun w => f w = u,
      (MA (Role.oracle, z)).op w from funext fun u => POVMIn.map_op f _ u]
  exact (hA (Role.oracle, z)).coarse f

omit [Fintype V] [DecidableEq V] [Nonempty V] [Inhabited A] [Algebra ℂ 𝒜] in
/-- The two component marginals multiply to the joint marginal. -/
theorem oracleView_mul (hA : ∀ q, IsPVMIn (MA q).op) (z : V) (u v : OAns A) :
    oracleView MA z OAns.aliceView u * oracleView MA z OAns.bobView v
      = ∑ w ∈ univ.filter fun w => (w.aliceView, w.bobView) = (u, v),
          (MA (Role.oracle, z)).op w := by
  rw [oracleView, oracleView, POVMIn.map_op, POVMIn.map_op, (hA _).sum_mul_sum,
    ← Finset.filter_and]
  refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun _ _ => rfl
  simp [Prod.ext_iff]

omit [Fintype V] [DecidableEq V] [Nonempty V] [Inhabited A] [Algebra ℂ 𝒜] in
/-- **The oracle's joint marginal is a projective measurement.** -/
theorem isPVMIn_oracleJoint (hA : ∀ q, IsPVMIn (MA q).op) (z : V) :
    IsPVMIn fun o : OAns A × OAns A =>
      oracleView MA z OAns.aliceView o.1 * oracleView MA z OAns.bobView o.2 := by
  have h := (hA (Role.oracle, z)).coarse fun w : OAns A => (w.aliceView, w.bobView)
  convert h using 1
  funext o
  exact oracleView_mul MA hA z o.1 o.2

/-! ## The estimate at one seed -/

omit [Inhabited A] in
/-- **The three cross-party deviations**, each bounded by its role pair's conditional failure, and
chained: the product of the two isolated measurements is within `6` times three conditional
failures of the oracle's joint marginal. Linear in the failures; no square root yet. -/
theorem sum_snorm_sq_joint_le (hψ : ‖M.ψ‖ = 1) (hA : ∀ q, IsPVMIn (MA q).op)
    (hB : ∀ q, IsPVMIn (MB q).op) (z : V) :
    ∑ o : OAns A × OAns A,
        M.snorm (M.πA ((MA (Role.alice, S.LA z)).op o.1) * M.πB ((MB (Role.bob, S.LB z)).op o.2)
          - M.πA (oracleView MA z OAns.aliceView o.1 * oracleView MA z OAns.bobView o.2)) ^ 2
      ≤ 6 * (M.condFail S.oracular.toGame MA MB (Role.alice, S.LA z) (Role.alice, S.LA z)
        + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.alice, S.LA z)
        + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.bob, S.LB z)) := by
  have hchain := M.sum_snorm_sq_chain (MA (Role.alice, S.LA z)).op
    (oracleView MA z OAns.aliceView) (oracleView MA z OAns.bobView)
    (MB (Role.alice, S.LA z)).op (MB (Role.bob, S.LB z)).op (hB _) (isPVMIn_oracleView MA hA z _)
  -- `(alice, alice)`: equal questions force equal answers
  have h1 := M.xSqNorm_sum_le_condFail (G := S.oracular.toGame) (MA := MA) (MB := MB) hψ
    (x := (Role.alice, S.LA z)) (y := (Role.alice, S.LA z)) (fun u : OAns A => u) (fun u => u)
    fun a b h => S.eq_of_oaccepts_self h
  -- `(oracle, alice)`: the oracle's Alice component matches the isolated Alice
  have h2 := M.xSqNorm_sum_le_condFail (G := S.oracular.toGame) (MA := MA) (MB := MB) hψ
    (x := (Role.oracle, z)) (y := (Role.alice, S.LA z)) OAns.aliceView (fun u => u)
    fun a b h => S.aliceView_of_oaccepts h
  -- `(oracle, bob)`: the oracle's Bob component matches the isolated Bob
  have h3 := M.xSqNorm_sum_le_condFail (G := S.oracular.toGame) (MA := MA) (MB := MB) hψ
    (x := (Role.oracle, z)) (y := (Role.bob, S.LB z)) OAns.bobView (fun u => u)
    fun a b h => S.bobView_of_oaccepts h
  simp only [POVMIn.map_op_self] at h1 h2 h3
  have e2 : ∀ c, ((MA (Role.oracle, z)).map OAns.aliceView).op c
      = oracleView MA z OAns.aliceView c := fun c => rfl
  have e3 : ∀ c, ((MA (Role.oracle, z)).map OAns.bobView).op c
      = oracleView MA z OAns.bobView c := fun c => rfl
  simp only [e2, e3] at h2 h3
  linarith

omit [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq A] [Inhabited A] [StarOrderedRing 𝒜]
  [StarOrderedRing ℬ] in
/-- The product of the two isolated measurements has total mass one. -/
theorem sum_snorm_sq_isolated (hψ : ‖M.ψ‖ = 1) (hA : ∀ q, IsPVMIn (MA q).op)
    (hB : ∀ q, IsPVMIn (MB q).op) (x y : V) :
    ∑ o : OAns A × OAns A,
        M.snorm (M.πA ((MA (Role.alice, x)).op o.1) * M.πB ((MB (Role.bob, y)).op o.2)) ^ 2
      = 1 := by
  rw [Fintype.sum_prod_type, ← M.sum_bornProb hψ (MA (Role.alice, x)) (MB (Role.bob, y))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact M.snorm_sq_πA_mul_πB_of_proj ((hA _).isStarProjection a) ((hB _).isStarProjection b)

omit [Fintype V] [DecidableEq V] [Nonempty V] [Inhabited A] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The oracle's joint marginal has total mass one. -/
theorem sum_snorm_sq_oracleJoint (hψ : ‖M.ψ‖ = 1) (hA : ∀ q, IsPVMIn (MA q).op) (z : V) :
    ∑ o : OAns A × OAns A,
        M.snorm (M.πA (oracleView MA z OAns.aliceView o.1 * oracleView MA z OAns.bobView o.2))
          ^ 2 = 1 :=
  M.sum_snorm_sq_eq_one_of_isPVMIn hψ ((isPVMIn_oracleJoint MA hA z).map M.πA)

omit [Inhabited A] in
/-- **The oracle's joint marginal carries the oracle's acceptance.** On the accepted pairs of
isolated answers it has at least the mass with which the oracle passes its own game check at
`(oracle, oracle)`. -/
theorem condWin_oracle_le (hA : ∀ q, IsPVMIn (MA q).op) (z : V) :
    M.condWin S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ o ∈ (S.accPairs z).map singlePairEmb,
          M.snorm (M.πA (oracleView MA z OAns.aliceView o.1 * oracleView MA z OAns.bobView o.2))
            ^ 2 := by
  -- the oracle's acceptance is at most the mass of its good answers
  have hgood : M.condWin S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ u, (if S.oracleGood z u then 1 else 0) * M.qform (M.πA ((MA (Role.oracle, z)).op u)) := by
    unfold BipartiteModel.condWin
    refine Finset.sum_le_sum fun u _ => ?_
    have hmarg : ∑ w, M.bornProb ((MA (Role.oracle, z)).op u) ((MB (Role.oracle, z)).op w)
        = M.qform (M.πA ((MA (Role.oracle, z)).op u)) := by
      rw [← M.bornProb_sum_right, (MB _).sum_op]
      show M.qform (M.πA _ * M.πB 1) = _
      rw [map_one, mul_one]
    rw [← hmarg, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine mul_le_mul_of_nonneg_right ?_
      (M.bornProb_nonneg ((MA _).op_nonneg u) ((MB _).op_nonneg w))
    by_cases h : S.oracular.toGame.D (Role.oracle, z) (Role.oracle, z) u w = true
    · rw [ite_eq_left h, ite_eq_left (S.oracleGood_of_oaccepts h)]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  -- the good answers are the accepted pairs
  have hpairs : ∑ u, (if S.oracleGood z u then 1 else 0)
        * M.qform (M.πA ((MA (Role.oracle, z)).op u))
      = ∑ p ∈ S.accPairs z, M.qform (M.πA ((MA (Role.oracle, z)).op (OAns.pair p.1 p.2))) := by
    rw [OAns.sum_eq, accPairs, Finset.sum_filter]
    have hsingle : ∑ a : A, (if S.oracleGood z (OAns.single a) = true then (1 : ℝ) else 0) *
        M.qform (M.πA ((MA (Role.oracle, z)).op (OAns.single a))) = 0 :=
      Finset.sum_eq_zero fun a _ => by
        show (if false = true then (1 : ℝ) else 0) * _ = 0
        simp
    rw [hsingle, add_zero]
    refine Finset.sum_congr rfl fun p _ => ?_
    show (if S.D (S.LA z) (S.LB z) p.1 p.2 = true then (1 : ℝ) else 0) * _ = _
    split_ifs <;> simp
  -- and each accepted pair lies in its fibre of the joint marginal
  have hfibre : ∀ p ∈ S.accPairs z,
      M.qform (M.πA ((MA (Role.oracle, z)).op (OAns.pair p.1 p.2)))
        ≤ M.snorm (M.πA (oracleView MA z OAns.aliceView (OAns.single p.1)
            * oracleView MA z OAns.bobView (OAns.single p.2))) ^ 2 := by
    intro p _
    rw [M.snorm_sq_πA_of_isStarProjection (U := oracleView MA z OAns.aliceView (OAns.single p.1)
      * oracleView MA z OAns.bobView (OAns.single p.2))
      ((isPVMIn_oracleJoint MA hA z).isStarProjection (OAns.single p.1, OAns.single p.2)),
      oracleView_mul MA hA z, map_sum, M.qform_sum]
    refine Finset.single_le_sum (f := fun w => M.qform (M.πA ((MA (Role.oracle, z)).op w)))
      (fun w _ => M.qform_nonneg (M.π_πA_nonneg ((MA _).op_nonneg w))) ?_
    simp [OAns.aliceView, OAns.bobView]
  calc M.condWin S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
      ≤ ∑ p ∈ S.accPairs z, M.qform (M.πA ((MA (Role.oracle, z)).op (OAns.pair p.1 p.2))) :=
        hgood.trans (le_of_eq hpairs)
    _ ≤ _ := by
        rw [Finset.sum_map]
        exact Finset.sum_le_sum hfibre

/-- **The extracted strategy wins at least the accepted isolated answer pairs.** -/
theorem sum_snorm_sq_le_condWin_sound (hA : ∀ q, IsPVMIn (MA q).op)
    (hB : ∀ q, IsPVMIn (MB q).op) (z : V) :
    ∑ o ∈ (S.accPairs z).map singlePairEmb,
        M.snorm (M.πA ((MA (Role.alice, S.LA z)).op o.1) * M.πB ((MB (Role.bob, S.LB z)).op o.2))
          ^ 2
      ≤ M.condWin S.toGame (fun x => (MA (Role.alice, x)).map OAns.singlePart)
          (fun y => (MB (Role.bob, y)).map OAns.singlePart) (S.LA z) (S.LB z) := by
  rw [M.condWin_adapt MA MB S.toGame (fun x => (Role.alice, x)) (fun y => (Role.bob, y))
    (fun _ => OAns.singlePart) (fun _ => OAns.singlePart), ← Fintype.sum_prod_type']
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ
    ((S.accPairs z).map singlePairEmb)) fun o _ _ =>
      mul_nonneg (by split_ifs <;> norm_num)
        (M.bornProb_nonneg ((MA _).op_nonneg _) ((MB _).op_nonneg _)))
  refine Finset.sum_congr rfl fun o ho => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp ho
  have hD : S.D (S.LA z) (S.LB z) p.1 p.2 = true := (Finset.mem_filter.mp hp).2
  rw [M.snorm_sq_πA_mul_πB_of_proj ((hA _).isStarProjection _) ((hB _).isStarProjection _)]
  simp only [singlePairEmb_apply, OAns.singlePart, toGame_D, hD, ite_true, one_mul]

/-- **Soundness at one seed**, where the square root is spent. -/
theorem condWin_sound_ge (hψ : ‖M.ψ‖ = 1) (hA : ∀ q, IsPVMIn (MA q).op)
    (hB : ∀ q, IsPVMIn (MB q).op) (z : V) :
    1 - M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
        - 2 * √(6 * (M.condFail S.oracular.toGame MA MB (Role.alice, S.LA z) (Role.alice, S.LA z)
          + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.alice, S.LA z)
          + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.bob, S.LB z)))
      ≤ M.condWin S.toGame (fun x => (MA (Role.alice, x)).map OAns.singlePart)
          (fun y => (MB (Role.bob, y)).map OAns.singlePart) (S.LA z) (S.LB z) := by
  have hclose := M.sum_snorm_sq_ge_of_close
    (fun o : OAns A × OAns A =>
      M.πA ((MA (Role.alice, S.LA z)).op o.1) * M.πB ((MB (Role.bob, S.LB z)).op o.2))
    (fun o => M.πA (oracleView MA z OAns.aliceView o.1 * oracleView MA z OAns.bobView o.2))
    (le_of_eq (sum_snorm_sq_isolated M MA MB hψ hA hB _ _))
    (le_of_eq (sum_snorm_sq_oracleJoint M MA hψ hA z)) ((S.accPairs z).map singlePairEmb)
  have hroot := Real.sqrt_le_sqrt (S.sum_snorm_sq_joint_le M MA MB hψ hA hB z)
  have hsucc := S.condWin_oracle_le M MA MB hA z
  have hwin := S.sum_snorm_sq_le_condWin_sound M MA MB hA hB z
  have hfail : M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
      = 1 - M.condWin S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z) := rfl
  linarith

/-! ## Averaging over the seed -/

omit [Inhabited A] in
/-- **The budget.** The four role pairs the argument uses are distinct, and each carries a ninth
of the question weight, so their conditional failures, averaged over the seed, add up to at most
nine times the failure probability. -/
theorem sum_condFail_four_le (hψ : ‖M.ψ‖ = 1) :
    (Fintype.card V : ℝ)⁻¹ * ∑ z,
        (M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
          + (M.condFail S.oracular.toGame MA MB (Role.alice, S.LA z) (Role.alice, S.LA z)
            + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.alice, S.LA z)
            + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.bob, S.LB z)))
      ≤ 9 * (1 - M.povmValue S.oracular.toGame MA MB) := by
  set g : Role × Role × V → ℝ := fun s => M.condFail S.oracular.toGame MA MB
    (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => M.condFail_nonneg hψ _ _
  have htot : 1 - M.povmValue S.oracular.toGame MA MB
      = (Fintype.card (Role × Role × V) : ℝ)⁻¹ * ∑ s, g s := by
    rw [M.one_sub_povmValue_eq]
    exact S.sum_oDist_mul (M.condFail S.oracular.toGame MA MB)
  have hsplit : ∑ s, g s = ∑ r₁ : Role, ∑ r₂ : Role, ∑ z : V, g (r₁, r₂, z) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r₁ _ => Fintype.sum_prod_type _
  have hpos : ∀ r₁ r₂ : Role, 0 ≤ ∑ z : V, g (r₁, r₂, z) := fun r₁ r₂ =>
    Finset.sum_nonneg fun z _ => hg0 _
  have hfour : ∑ z, (M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
        + (M.condFail S.oracular.toGame MA MB (Role.alice, S.LA z) (Role.alice, S.LA z)
          + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.alice, S.LA z)
          + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.bob, S.LB z)))
      = ∑ z, g (.oracle, .oracle, z) + (∑ z, g (.alice, .alice, z)
          + ∑ z, g (.oracle, .alice, z) + ∑ z, g (.oracle, .bob, z)) := by
    simp only [← Finset.sum_add_distrib]
    rfl
  have hle : ∑ z, (M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z)
        + (M.condFail S.oracular.toGame MA MB (Role.alice, S.LA z) (Role.alice, S.LA z)
          + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.alice, S.LA z)
          + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.bob, S.LB z)))
      ≤ ∑ s, g s := by
    rw [hfour, hsplit]
    simp only [Role.sum_eq]
    linarith [hpos .alice .oracle, hpos .alice .bob, hpos .bob .oracle, hpos .bob .alice,
      hpos .bob .bob]
  have hcard : (Fintype.card V : ℝ)⁻¹ = 9 * (Fintype.card (Role × Role × V) : ℝ)⁻¹ := by
    have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    rw [card_role_prod_prod (V := V)]
    field_simp
  rw [htot, hcard, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hle (by positivity)) (by norm_num)

/-- The value of the extracted strategy is the average over the seed of its conditional success
at the question pair the seed determines. -/
theorem povmValue_sound_eq :
    M.povmValue S.toGame (fun x => (MA (Role.alice, x)).map OAns.singlePart)
        (fun y => (MB (Role.bob, y)).map OAns.singlePart)
      = (Fintype.card V : ℝ)⁻¹ * ∑ z, M.condWin S.toGame
          (fun x => (MA (Role.alice, x)).map OAns.singlePart)
          (fun y => (MB (Role.bob, y)).map OAns.singlePart) (S.LA z) (S.LB z) :=
  S.sum_dist_mul _

/-! ## Soundness -/

/-- **Soundness of oracularization, in a bipartite model** (item 2 of blueprint
`thm:oracularization`, `lem:oracular-soundness-model`): projective families of value at least
`1 - ε` for the oracularized game yield, in the same model, the families of value at least
`1 - 24√ε` for the input game in which Alice plays the first player's isolated-Alice measurement
and Bob the second player's isolated-Bob measurement, each relabelled along `OAns.singlePart`.
The loss carries the single square root of repair 1 of `rem:oracularization-repairs`, spent in
`StateModel.sum_snorm_sq_ge_of_close`. -/
theorem povmValue_sound_ge (hψ : ‖M.ψ‖ = 1) (hA : ∀ q, IsPVMIn (MA q).op)
    (hB : ∀ q, IsPVMIn (MB q).op) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hval : 1 - ε ≤ M.povmValue S.oracular.toGame MA MB) :
    1 - 24 * √ε ≤ M.povmValue S.toGame (fun x => (MA (Role.alice, x)).map OAns.singlePart)
      (fun y => (MB (Role.bob, y)).map OAns.singlePart) := by
  have hcardV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hW : (0 : ℝ) < (Fintype.card V : ℝ)⁻¹ := by positivity
  set F : V → ℝ := fun z =>
    M.condFail S.oracular.toGame MA MB (Role.alice, S.LA z) (Role.alice, S.LA z)
      + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.alice, S.LA z)
      + M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.bob, S.LB z) with hF
  set Gm : V → ℝ := fun z =>
    M.condFail S.oracular.toGame MA MB (Role.oracle, z) (Role.oracle, z) with hGm
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    add_nonneg (add_nonneg (M.condFail_nonneg hψ _ _) (M.condFail_nonneg hψ _ _))
      (M.condFail_nonneg hψ _ _)
  have hG0 : ∀ z, 0 ≤ Gm z := fun z => M.condFail_nonneg hψ _ _
  -- the budget, split between the game check and the three consistencies
  have hbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z + (Fintype.card V : ℝ)⁻¹ * ∑ z, F z
      ≤ 9 * ε := by
    have h := S.sum_condFail_four_le M MA MB hψ
    rw [← mul_add, ← Finset.sum_add_distrib]
    linarith
  have hGbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z ≤ 9 * ε := by
    have : 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, F z :=
      mul_nonneg hW.le (Finset.sum_nonneg fun z _ => hF0 z)
    linarith
  have hFbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, F z ≤ 9 * ε := by
    have : 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z :=
      mul_nonneg hW.le (Finset.sum_nonneg fun z _ => hG0 z)
    linarith
  -- the averaging step: `𝔼 √(6 F) ≤ √(54 ε)`
  have hjensen : (Fintype.card V : ℝ)⁻¹ * ∑ z, √(6 * F z) ≤ √(54 * ε) := by
    have hj0 := sum_mul_sqrt_le (univ : Finset V) (fun _ => (Fintype.card V : ℝ)⁻¹)
      (fun z => 6 * F z) (fun _ => hW.le) fun z => mul_nonneg (by norm_num) (hF0 z)
    have hj1 : (∑ _z : V, (Fintype.card V : ℝ)⁻¹) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [hj1, Real.sqrt_one, one_mul, ← Finset.mul_sum, ← Finset.mul_sum] at hj0
    refine hj0.trans (Real.sqrt_le_sqrt ?_)
    have h6 : (Fintype.card V : ℝ)⁻¹ * ∑ z, 6 * F z
        = 6 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, F z) := by
      rw [← Finset.mul_sum]
      ring
    rw [h6]
    linarith
  -- put the seeds together
  rw [S.povmValue_sound_eq M MA MB]
  have hmono : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - Gm z - 2 * √(6 * F z))
      ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, M.condWin S.toGame
          (fun x => (MA (Role.alice, x)).map OAns.singlePart)
          (fun y => (MB (Role.bob, y)).map OAns.singlePart) (S.LA z) (S.LB z) :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun z _ => S.condWin_sound_ge M MA MB hψ hA hB z) hW.le
  refine le_trans ?_ hmono
  have hexp : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - Gm z - 2 * √(6 * F z))
      = 1 - (Fintype.card V : ℝ)⁻¹ * (∑ z, Gm z)
        - 2 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, √(6 * F z)) := by
    rw [show (∑ z : V, (1 - Gm z - 2 * √(6 * F z)))
        = ((∑ _z : V, (1 : ℝ)) - ∑ z, Gm z) - 2 * ∑ z, √(6 * F z) from by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub, mul_sub,
      inv_mul_cancel₀ hcardV.ne']
    ring
  rw [hexp]
  -- and the final arithmetic
  have heps : ε ≤ √ε := by
    have h1 : √(ε ^ 2) ≤ √ε := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq hε0] at h1
  have hs54 : √(54 * ε) ≤ (7.35 : ℝ) * √ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 54)]
    have h54 : √(54 : ℝ) ≤ 7.35 := by
      rw [show (7.35 : ℝ) = √(7.35 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact mul_le_mul_of_nonneg_right h54 (Real.sqrt_nonneg ε)
  nlinarith [hjensen, hGbud, heps, hs54, Real.sqrt_nonneg ε]

end Model

/-! ## In the commuting-operator model -/

omit [DecidableEq V] in
/-- **Soundness of oracularization, in commuting-operator values** (`lem:oracular-soundness-co`):
`ω_co` of the oracularized game above `1 - ε` puts `ω_co` of the input game at least
`1 - 24√ε`. A projective strategy of model value above `1 - ε` approaches `ω_co`
(`exists_isPVMIn_lt_povmValue`), the model-level soundness extracts a strategy in its model, and
that strategy is a commuting-operator strategy
(`BipartiteModel.povmValue_le_commutingOperatorValue`). -/
theorem commutingOperatorValue_ge_of_oracular {V A : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] (S : SeededGame V A) {ε : ℝ}
    (hε : 0 < ε) (h : 1 - ε < commutingOperatorValue S.oracular.toGame) :
    1 - 24 * √ε ≤ commutingOperatorValue S.toGame := by
  by_cases hε1 : ε ≤ 1
  · obtain ⟨T, hA, hB, hT⟩ := exists_isPVMIn_lt_povmValue (by linarith) h
    exact (S.povmValue_sound_ge T.toModel T.aliceMeas T.bobMeas T.toModel_ψ_norm hA hB hε.le hε1
      hT.le).trans (T.toModel.povmValue_le_commutingOperatorValue T.toModel_ψ_norm _ _ _)
  · rw [not_le] at hε1
    have h1 : 1 < √ε := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt zero_le_one hε1
    have h2 := commutingOperatorValue_nonneg S.toGame
    linarith

end SeededGame

end MIPRE

end
