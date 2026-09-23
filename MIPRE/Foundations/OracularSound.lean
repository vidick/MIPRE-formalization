/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularGame
import MIPRE.Foundations.PerfectStrategy
import MIPRE.Foundations.GameDouble
import MIPRE.Foundations.Closeness

/-!
# Soundness of oracularization

Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness`), at the level of games: a
synchronous strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of
value at least `1 - 24√ε` for the doubled input game.

The loss carries the **single square root** that repair 1 of `rem:oracularization-repairs`
insists on -- an earlier revision of the blueprint wrote `poly(ε)`, which the campaign found
"not merely imprecise but false as stated". It is spent in exactly one place,
`MIPRE.sum_ntr_mul_ge`; everything before it is linear in `ε`.

## The shape of the argument

* **The extracted strategy** (`soundStrategy`) is the two isolated players' own measurements,
  relabelled along `OAns.singlePart` so that an oracle-shaped answer is grouped into one
  distinguished outcome. Relabelling is what makes them *measurements* rather than
  sub-measurements, which is the game-level residue of repair 3; `SyncStrategy.push` does it,
  and a sum over a fibre is a projection because distinct outcomes are orthogonal.
* **The budget** (`budget`) is all that is taken from the hypothesis. Each of the nine ordered
  role pairs carries a ninth of the question weight, so at any one of them a set of outcome
  pairs the decider rejects carries mass at most `9ε` on average over the seed. Three
  instances (`gammaTerm_budget`, `betaTerm_budget`, `alphaTerm_budget`) are used: the oracle's
  own pair is accepted, and each isolated player agrees with the oracle's component.
* **The closeness estimate** (`sqDist_le`, from `MIPRE.sum_hsNormSq_sub_le`) bounds the
  squared Hilbert--Schmidt distance between the oracle's relabelled measurement and the
  product of the two isolated players' by three times the sum of the two disagreements --
  linearly, with no square root.
* **The value comparison** (`valSeed_ge`, from `MIPRE.sum_ntr_mul_ge`) is where the square
  root enters, and one more Cauchy--Schwarz takes the average inside it.

For a synchronous strategy the state is the normalized trace, so the paper's state-dependent
`≈_δ` is the normalized Hilbert--Schmidt distance of `MIPRE/Foundations/Distances.lean`; see
blueprint `rem:distance-state`. `MIPRE/Foundations/Closeness.lean` is that calculus.

## Scope

Nothing here inhabits `MIPRE.Oracularization`: that is done at the level of verifiers, in
`Foundations/Pipeline/Oracularization.lean`, whose bipartite soundness rests on
`Foundations/OracularTensor.lean` rather than on the synchronous argument here. The complexity
clause, the bounded parse and its grouping, the truncation to `B_𝒟(n)` and the level accounting
are all statements about a verifier and none of them appears at this level;
`rem:oracular-game-level` records that.
-/

namespace MIPRE

open Finset Matrix

/-! ## Relabelling an oracularized answer -/

variable {A : Type*} [Inhabited A]

/-- An oracularized answer read as a pair: an oracle's answer is the pair it is, and an
isolated player's answer is grouped into the distinguished outcome `(default, default)`. -/
def OAns.pairPart : OAns A → A × A
  | .pair a b => (a, b)
  | .single _ => (default, default)

/-- An oracularized answer read as a single answer: an isolated player's answer is itself, and
an oracle's pair is grouped into the distinguished outcome `default`. -/
def OAns.singlePart : OAns A → A
  | .single a => a
  | .pair _ _ => default

namespace SeededGame

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)

/-! ## Averages over the seed

Both question distributions are pushforwards of the uniform distribution on the seed space, so
every sum against them is an average over seeds. -/

omit [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
/-- The input game's distribution, against a test function: an average over the seed. -/
theorem sum_dist_mul (F : V → V → ℝ) :
    ∑ x, ∑ y, S.dist x y * F x y
      = (Fintype.card V : ℝ)⁻¹ * ∑ z, F (S.LA z) (S.LB z) := by
  have hfib : ∀ p : V × V, (univ.filter fun z => S.LA z = p.1 ∧ S.LB z = p.2)
      = univ.filter fun z => (S.LA z, S.LB z) = p := by
    intro p; ext z; simp [Prod.ext_iff]
  rw [← Fintype.sum_prod_type' fun x y => S.dist x y * F x y]
  calc ∑ p : V × V, S.dist p.1 p.2 * F p.1 p.2
      = ∑ p : V × V, (Fintype.card V : ℝ)⁻¹ *
          ∑ _z ∈ univ.filter fun z => (S.LA z, S.LB z) = p, F p.1 p.2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [dist, hfib p, Finset.sum_const, nsmul_eq_mul]
        ring
    _ = (Fintype.card V : ℝ)⁻¹ * ∑ p : V × V,
          ∑ _z ∈ univ.filter fun z => (S.LA z, S.LB z) = p, F p.1 p.2 := by
        rw [Finset.mul_sum]
    _ = (Fintype.card V : ℝ)⁻¹ * ∑ z, F (S.LA z) (S.LB z) := by
        rw [Finset.sum_fiberwise' univ (fun z => (S.LA z, S.LB z)) fun p => F p.1 p.2]

omit [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
/-- The oracularized game's distribution, against a test function: an average over the ordered
pair of roles and the seed. -/
theorem sum_oDist_mul (F : Role × V → Role × V → ℝ) :
    ∑ p, ∑ q, S.oDist p q * F p q
      = (Fintype.card (Role × Role × V) : ℝ)⁻¹ *
        ∑ s : Role × Role × V, F (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) := by
  simp only [oDist]
  rw [← Fintype.sum_prod_type' fun p q =>
    (∑ s : Role × Role × V, (Fintype.card (Role × Role × V) : ℝ)⁻¹ *
      if (S.oquestion s.1 s.2.2, S.oquestion s.2.1 s.2.2) = (p, q) then 1 else 0) * F p q]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single_of_mem
    (S.oquestion s.1 s.2.2, S.oquestion s.2.1 s.2.2) (mem_univ _)]
  · simp
  · intro pq _ hne
    simp [Ne.symm hne]

/-! ## The three relabelled families, and the extracted strategy -/

variable {S}

/-- The oracle's measurement, read as a measurement on answer *pairs*: the shape failures are
grouped into the distinguished outcome `(default, default)`, which is what makes it a
measurement rather than a sub-measurement (repair 3 of `rem:oracularization-repairs`, at the
game level). -/
noncomputable def oFam (N : SyncStrategy S.oracular) (z : V) (p : A × A) :
    Matrix (Fin N.d) (Fin N.d) ℂ := (N.push OAns.pairPart).M (.oracle, z) p

/-- Alice's own measurement, with the oracle-shaped answers grouped into `default`. -/
noncomputable def cFam (N : SyncStrategy S.oracular) (x : V) (a : A) :
    Matrix (Fin N.d) (Fin N.d) ℂ := (N.push OAns.singlePart).M (.alice, x) a

/-- Bob's own measurement, with the oracle-shaped answers grouped into `default`. -/
noncomputable def dFam (N : SyncStrategy S.oracular) (y : V) (b : A) :
    Matrix (Fin N.d) (Fin N.d) ℂ := (N.push OAns.singlePart).M (.bob, y) b

/-- The isolated players' measurements as one projective measurement on the doubled input
game's questions. -/
noncomputable def sideMeas (N : SyncStrategy S.oracular) :
    ProjectiveMeasurement (Bool × V) A (Matrix (Fin N.d) (Fin N.d) ℂ) where
  M p a := (N.push OAns.singlePart).M
    (if p.1 then (Role.bob, p.2) else (Role.alice, p.2)) a
  selfAdjoint _p a := (N.push OAns.singlePart).selfAdjoint _ a
  projective _p a := (N.push OAns.singlePart).projective _ a
  normalized _p := (N.push OAns.singlePart).normalized _

/-- **The extracted strategy** for the input game: the two isolated players keep their own
measurements. -/
noncomputable def soundStrategy (N : SyncStrategy S.oracular) :
    SyncStrategy S.toGame.doubled where
  d := N.d
  d_pos := N.d_pos
  P := sideMeas N

@[simp] theorem soundStrategy_d (N : SyncStrategy S.oracular) : (soundStrategy N).d = N.d := rfl

@[simp] theorem soundStrategy_false (N : SyncStrategy S.oracular) (x : V) (a : A) :
    (soundStrategy N).P.M (false, x) a = cFam N x a := rfl

@[simp] theorem soundStrategy_true (N : SyncStrategy S.oracular) (y : V) (b : A) :
    (soundStrategy N).P.M (true, y) b = dFam N y b := rfl

/-! ## The two values, as averages over the seed -/

/-- The extracted strategy's value. -/
theorem soundStrategy_value (N : SyncStrategy S.oracular) :
    (soundStrategy N).value = (Fintype.card V : ℝ)⁻¹ * ∑ z,
      ∑ a, ∑ b, (if S.D (S.LA z) (S.LB z) a b then 1 else 0) *
        ntr (cFam N (S.LA z) a * dFam N (S.LB z) b) := by
  have h1 : (soundStrategy N).value
      = ∑ x, ∑ y, S.dist x y * ∑ a, ∑ b,
          (if S.D x y a b then 1 else 0) * ntr (cFam N x a * dFam N y b) := by
    rw [SyncStrategy.value_eq_ntr, Game.sum_doubled S.toGame
      fun p q a b => ntr ((soundStrategy N).P.M p a * (soundStrategy N).P.M q b)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [S.toGame_μ, S.toGame_D, soundStrategy_false, soundStrategy_true, mul_assoc]
    rfl
  rw [h1, S.sum_dist_mul]

omit [Inhabited A] in
/-- The oracularized value. -/
theorem value_oracular (N : SyncStrategy S.oracular) :
    N.value = (Fintype.card (Role × Role × V) : ℝ)⁻¹ * ∑ s : Role × Role × V,
      ∑ uv : OAns A × OAns A,
        (if S.oaccepts (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) uv.1 uv.2
          then 1 else 0) *
        ntr (N.P.M (S.oquestion s.1 s.2.2) uv.1 * N.P.M (S.oquestion s.2.1 s.2.2) uv.2) := by
  have h1 : N.value = ∑ p, ∑ q, S.oDist p q *
      ∑ u, ∑ v, (if S.oaccepts p q u v then 1 else 0) * ntr (N.P.M p u * N.P.M q v) := by
    rw [SyncStrategy.value_eq_ntr]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [S.oracular_μ, S.oracular_D]
    ring
  rw [h1, S.sum_oDist_mul]
  refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
  rw [← Fintype.sum_prod_type' fun u v =>
    (if S.oaccepts (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) u v then 1 else 0) *
      ntr (N.P.M (S.oquestion s.1 s.2.2) u * N.P.M (S.oquestion s.2.1 s.2.2) v)]

omit [Inhabited A] in
/-- The total mass of the oracularized game: one. -/
theorem sum_ntr_oracular (N : SyncStrategy S.oracular) :
    (Fintype.card (Role × Role × V) : ℝ)⁻¹ * ∑ s : Role × Role × V,
      ∑ uv : OAns A × OAns A,
        ntr (N.P.M (S.oquestion s.1 s.2.2) uv.1 * N.P.M (S.oquestion s.2.1 s.2.2) uv.2)
      = 1 := by
  rw [show (∑ s : Role × Role × V, ∑ uv : OAns A × OAns A,
        ntr (N.P.M (S.oquestion s.1 s.2.2) uv.1 * N.P.M (S.oquestion s.2.1 s.2.2) uv.2))
      = ∑ s : Role × Role × V, ∑ u, ∑ v,
        ntr (N.P.M (S.oquestion s.1 s.2.2) u * N.P.M (S.oquestion s.2.1 s.2.2) v) from
    Finset.sum_congr rfl fun s _ => Fintype.sum_prod_type'
      fun u v => ntr (N.P.M (S.oquestion s.1 s.2.2) u * N.P.M (S.oquestion s.2.1 s.2.2) v)]
  rw [← S.sum_oDist_mul fun p q => ∑ u, ∑ v, ntr (N.P.M p u * N.P.M q v)]
  refine (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_).trans
    S.oracular.μ_sum_one
  rw [N.sum_ntr_eq_one p q, mul_one, S.oracular_μ]

/-! ## The rejection budget

Everything the argument takes from `1 - ε ≤ val(oracular)` is this: at any one ordered pair of
roles, a set of outcome pairs the decider rejects carries mass at most `9ε` on average over the
seed. The `9` is the number of ordered role pairs. -/

omit [DecidableEq V] [Nonempty V] [Inhabited A] in
theorem card_role_prod_prod : (Fintype.card (Role × Role × V) : ℝ) = 9 * Fintype.card V := by
  rw [Fintype.card_prod, Fintype.card_prod, show Fintype.card Role = 3 from rfl]
  push_cast
  ring

omit [Inhabited A] in
theorem budget (N : SyncStrategy S.oracular) {ε : ℝ} (hval : 1 - ε ≤ N.value)
    (r₁ r₂ : Role) (T : V → Finset (OAns A × OAns A))
    (hT : ∀ z, ∀ uv ∈ T z,
      S.oaccepts (S.oquestion r₁ z) (S.oquestion r₂ z) uv.1 uv.2 = false) :
    (Fintype.card V : ℝ)⁻¹ * ∑ z, ∑ uv ∈ T z,
        ntr (N.P.M (S.oquestion r₁ z) uv.1 * N.P.M (S.oquestion r₂ z) uv.2) ≤ 9 * ε := by
  have hcardV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  set W : ℝ := (Fintype.card (Role × Role × V) : ℝ)⁻¹ with hWdef
  set g : Role × Role × V → ℝ := fun s => ∑ uv : OAns A × OAns A,
    (1 - (if S.oaccepts (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) uv.1 uv.2
      then 1 else 0)) *
      ntr (N.P.M (S.oquestion s.1 s.2.2) uv.1 * N.P.M (S.oquestion s.2.1 s.2.2) uv.2) with hgdef
  have hterm : ∀ (s : Role × Role × V) (uv : OAns A × OAns A),
      0 ≤ (1 - (if S.oaccepts (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) uv.1 uv.2
        then 1 else 0)) *
        ntr (N.P.M (S.oquestion s.1 s.2.2) uv.1 * N.P.M (S.oquestion s.2.1 s.2.2) uv.2) :=
    fun s uv => mul_nonneg (by split_ifs <;> norm_num) (N.ntr_mul_nonneg _ _ _ _)
  have hg_nonneg : ∀ s, 0 ≤ g s := fun s => Finset.sum_nonneg fun uv _ => hterm s uv
  -- the total rejected mass is `1 - val`
  have htot : W * ∑ s, g s = 1 - N.value := by
    have hsplit : ∑ s, g s
        = (∑ s : Role × Role × V, ∑ uv : OAns A × OAns A,
            ntr (N.P.M (S.oquestion s.1 s.2.2) uv.1 * N.P.M (S.oquestion s.2.1 s.2.2) uv.2))
          - ∑ s : Role × Role × V, ∑ uv : OAns A × OAns A,
            (if S.oaccepts (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) uv.1 uv.2
              then 1 else 0) *
            ntr (N.P.M (S.oquestion s.1 s.2.2) uv.1 * N.P.M (S.oquestion s.2.1 s.2.2) uv.2) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hgdef, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun uv _ => by ring
    rw [hsplit, mul_sub, sum_ntr_oracular N, ← value_oracular N]
  have hle : W * ∑ s, g s ≤ ε := by rw [htot]; linarith
  -- the sub-sum at the chosen role pair
  have hsub : ∑ z, ∑ uv ∈ T z,
      ntr (N.P.M (S.oquestion r₁ z) uv.1 * N.P.M (S.oquestion r₂ z) uv.2) ≤ ∑ s, g s := by
    have hstep : ∀ z : V, ∑ uv ∈ T z,
        ntr (N.P.M (S.oquestion r₁ z) uv.1 * N.P.M (S.oquestion r₂ z) uv.2)
          ≤ g (r₁, r₂, z) := by
      intro z
      calc ∑ uv ∈ T z, ntr (N.P.M (S.oquestion r₁ z) uv.1 * N.P.M (S.oquestion r₂ z) uv.2)
          = ∑ uv ∈ T z, (1 - (if S.oaccepts (S.oquestion r₁ z) (S.oquestion r₂ z) uv.1 uv.2
              then 1 else 0)) *
              ntr (N.P.M (S.oquestion r₁ z) uv.1 * N.P.M (S.oquestion r₂ z) uv.2) := by
            refine Finset.sum_congr rfl fun uv huv => ?_
            rw [hT z uv huv]
            simp
        _ ≤ g (r₁, r₂, z) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun uv _ _ => hterm (r₁, r₂, z) uv
    calc ∑ z, ∑ uv ∈ T z,
          ntr (N.P.M (S.oquestion r₁ z) uv.1 * N.P.M (S.oquestion r₂ z) uv.2)
        ≤ ∑ z : V, g (r₁, r₂, z) := Finset.sum_le_sum fun z _ => hstep z
      _ = ∑ s ∈ univ.image fun z : V => (r₁, r₂, z), g s := by
          rw [Finset.sum_image]
          intro x _ y _ h
          simpa using h
      _ ≤ ∑ s, g s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun s _ _ => hg_nonneg s
  have hWval : (Fintype.card V : ℝ)⁻¹ = 9 * W := by
    rw [hWdef, card_role_prod_prod (V := V)]
    field_simp
  calc (Fintype.card V : ℝ)⁻¹ * ∑ z, ∑ uv ∈ T z,
        ntr (N.P.M (S.oquestion r₁ z) uv.1 * N.P.M (S.oquestion r₂ z) uv.2)
      ≤ (Fintype.card V : ℝ)⁻¹ * ∑ s, g s := by
        exact mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = 9 * (W * ∑ s, g s) := by rw [hWval]; ring
    _ ≤ 9 * ε := by linarith

/-! ## Relabelled sums, unrelabelled

Each budget below is stated about the *relabelled* families, and the budget lemma is about the
strategy's own operators. This is the translation: a sum over a set of relabelled outcome pairs
is the sum over the outcome pairs whose labels land in that set. -/

omit [Inhabited A] in
theorem sum_push_pair (N : SyncStrategy S.oracular) (p q : Role × V)
    {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (f : OAns A → B) (g : OAns A → C) (E : Finset (B × C)) :
    ∑ bc ∈ E, ntr ((N.push f).M p bc.1 * (N.push g).M q bc.2)
      = ∑ uv ∈ univ.filter fun uv : OAns A × OAns A => (f uv.1, g uv.2) ∈ E,
          ntr (N.P.M p uv.1 * N.P.M q uv.2) := by
  have hfib : ∀ bc : B × C,
      (univ.filter fun u => f u = bc.1) ×ˢ (univ.filter fun v => g v = bc.2)
        = univ.filter fun uv : OAns A × OAns A => (f uv.1, g uv.2) = bc := by
    intro bc
    ext uv
    simp [Finset.mem_product, Prod.ext_iff]
  calc ∑ bc ∈ E, ntr ((N.push f).M p bc.1 * (N.push g).M q bc.2)
      = ∑ bc ∈ E, ∑ uv ∈ univ.filter fun uv : OAns A × OAns A => (f uv.1, g uv.2) = bc,
          ntr (N.P.M p uv.1 * N.P.M q uv.2) := by
        refine Finset.sum_congr rfl fun bc _ => ?_
        rw [← hfib bc, Finset.sum_product, SyncStrategy.push_apply, SyncStrategy.push_apply,
          Finset.sum_mul_sum, ntr_sum]
        exact Finset.sum_congr rfl fun u _ => ntr_sum _ _
    _ = ∑ uv ∈ univ.filter fun uv : OAns A × OAns A => (f uv.1, g uv.2) ∈ E,
          ntr (N.P.M p uv.1 * N.P.M q uv.2) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := univ.filter fun uv : OAns A × OAns A => (f uv.1, g uv.2) ∈ E) (t := E)
          (g := fun uv : OAns A × OAns A => (f uv.1, g uv.2))
          (fun uv huv => (Finset.mem_filter.mp huv).2)
          (fun uv => ntr (N.P.M p uv.1 * N.P.M q uv.2))]
        refine Finset.sum_congr rfl fun bc hbc => Finset.sum_congr ?_ fun _ _ => rfl
        ext uv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun h => ⟨by rw [h]; exact hbc, h⟩, fun h => h.2⟩

omit [Inhabited A] in
theorem sum_push_single (N : SyncStrategy S.oracular) (p : Role × V)
    {B : Type*} [Fintype B] [DecidableEq B] (f : OAns A → B) (E : Finset B) :
    ∑ b ∈ E, ntr ((N.push f).M p b)
      = ∑ u ∈ univ.filter fun u => f u ∈ E, ntr (N.P.M p u) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun u => f u ∈ E) (t := E) (g := f)
    (fun u hu => (Finset.mem_filter.mp hu).2) (fun u => ntr (N.P.M p u))]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [SyncStrategy.push_apply, ntr_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨by rw [h]; exact hb, h⟩, fun h => h.2⟩

/-! ## The three rejection sets, and their budgets

The decider's checks that the argument uses are three: the oracle's own pair must satisfy the
input predicate, and each isolated player's answer must agree with the oracle's corresponding
component. Each is a set of outcome pairs on which `oaccepts` is false, so each carries mass at
most `9ε`. -/

/-- The outcome pairs on which the oracle's Alice-component and Alice's own answer disagree.
It also contains every shape mismatch, which the decider rejects anyway. -/
def TAlice : Finset (OAns A × OAns A) :=
  univ.filter fun uv => ¬ ((OAns.pairPart uv.1).1 = OAns.singlePart uv.2)

/-- The outcome pairs on which the oracle's Bob-component and Bob's own answer disagree. -/
def TBob : Finset (OAns A × OAns A) :=
  univ.filter fun uv => ¬ ((OAns.pairPart uv.1).2 = OAns.singlePart uv.2)

/-- The outcome pairs, at a seed, on which the oracle repeats an answer the input predicate
rejects. -/
def TGame (z : V) : Finset (OAns A × OAns A) :=
  (univ.filter fun u : OAns A =>
      S.D (S.LA z) (S.LB z) (OAns.pairPart u).1 (OAns.pairPart u).2 = false).image
    fun u => (u, u)

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem rejected_TAlice (z : V) : ∀ uv ∈ (TAlice : Finset (OAns A × OAns A)),
    S.oaccepts (S.oquestion .oracle z) (S.oquestion .alice z) uv.1 uv.2 = false := by
  rintro ⟨u, v⟩ huv
  have h := (Finset.mem_filter.mp huv).2
  cases u <;> cases v <;>
    simp_all [OAns.pairPart, OAns.singlePart, oaccepts, shapeOk, gameCheck, oracleVsPlayer,
      oquestion]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem rejected_TBob (z : V) : ∀ uv ∈ (TBob : Finset (OAns A × OAns A)),
    S.oaccepts (S.oquestion .oracle z) (S.oquestion .bob z) uv.1 uv.2 = false := by
  rintro ⟨u, v⟩ huv
  have h := (Finset.mem_filter.mp huv).2
  cases u <;> cases v <;>
    simp_all [OAns.pairPart, OAns.singlePart, oaccepts, shapeOk, gameCheck, oracleVsPlayer,
      oquestion]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem rejected_TGame (z : V) : ∀ uv ∈ S.TGame z,
    S.oaccepts (S.oquestion .oracle z) (S.oquestion .oracle z) uv.1 uv.2 = false := by
  intro uv huv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp huv
  have h := (Finset.mem_filter.mp hu).2
  cases u <;>
    simp_all [OAns.pairPart, oaccepts, shapeOk, gameCheck, oracleVsPlayer, oquestion]

/-! ## The three budgets, on the relabelled families

Each budget is now a statement about the relabelled families `oFam`, `cFam`, `dFam`: the
oracle's own answer is accepted, and each isolated player agrees with the oracle's component,
all but `9ε` of the time. -/

private def EAliceAgree : Finset ((A × A) × A) := univ.image fun p : A × A => (p, p.1)

private def EBobAgree : Finset ((A × A) × A) := univ.image fun p : A × A => (p, p.2)

omit [Inhabited A] in
private theorem mem_EAliceAgree (bc : (A × A) × A) :
    bc ∈ (EAliceAgree : Finset ((A × A) × A)) ↔ bc.1.1 = bc.2 := by
  simp [EAliceAgree, Prod.ext_iff]

omit [Inhabited A] in
private theorem mem_EBobAgree (bc : (A × A) × A) :
    bc ∈ (EBobAgree : Finset ((A × A) × A)) ↔ bc.1.2 = bc.2 := by
  simp [EBobAgree, Prod.ext_iff, eq_comm]

omit [Inhabited A] in
private theorem sum_ntr_pair_eq_one (N : SyncStrategy S.oracular) (p q : Role × V) :
    ∑ uv : OAns A × OAns A, ntr (N.P.M p uv.1 * N.P.M q uv.2) = 1 := by
  rw [Fintype.sum_prod_type' fun u v => ntr (N.P.M p u * N.P.M q v)]
  exact N.sum_ntr_eq_one p q

/-- The oracle's disagreement with Alice, as a mass on the strategy's own outcomes. -/
theorem sum_disagree_alice (N : SyncStrategy S.oracular) (z : V) :
    (1 : ℝ) - ∑ p : A × A, ntr (oFam N z p * cFam N (S.LA z) p.1)
      = ∑ uv ∈ (TAlice : Finset (OAns A × OAns A)),
          ntr (N.P.M ((.oracle, z) : Role × V) uv.1 *
            N.P.M ((.alice, S.LA z) : Role × V) uv.2) := by
  have hagree : ∑ p : A × A, ntr (oFam N z p * cFam N (S.LA z) p.1)
      = ∑ uv ∈ univ.filter fun uv : OAns A × OAns A =>
            (OAns.pairPart uv.1).1 = OAns.singlePart uv.2,
          ntr (N.P.M ((.oracle, z) : Role × V) uv.1 *
            N.P.M ((.alice, S.LA z) : Role × V) uv.2) := by
    have h1 : ∑ bc ∈ (EAliceAgree : Finset ((A × A) × A)),
        ntr ((N.push OAns.pairPart).M ((.oracle, z) : Role × V) bc.1 *
          (N.push OAns.singlePart).M ((.alice, S.LA z) : Role × V) bc.2)
        = ∑ p : A × A, ntr (oFam N z p * cFam N (S.LA z) p.1) := by
      rw [EAliceAgree, Finset.sum_image fun x _ y _ h => (Prod.ext_iff.mp h).1]
      rfl
    rw [← h1, sum_push_pair]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext uv
    simp [mem_EAliceAgree]
  rw [hagree, ← sum_ntr_pair_eq_one N ((.oracle, z) : Role × V) ((.alice, S.LA z) : Role × V),
    ← Finset.sum_filter_add_sum_filter_not univ
      fun uv : OAns A × OAns A => (OAns.pairPart uv.1).1 = OAns.singlePart uv.2, TAlice]
  ring

/-- The oracle's disagreement with Bob. -/
theorem sum_disagree_bob (N : SyncStrategy S.oracular) (z : V) :
    (1 : ℝ) - ∑ p : A × A, ntr (oFam N z p * dFam N (S.LB z) p.2)
      = ∑ uv ∈ (TBob : Finset (OAns A × OAns A)),
          ntr (N.P.M ((.oracle, z) : Role × V) uv.1 *
            N.P.M ((.bob, S.LB z) : Role × V) uv.2) := by
  have hagree : ∑ p : A × A, ntr (oFam N z p * dFam N (S.LB z) p.2)
      = ∑ uv ∈ univ.filter fun uv : OAns A × OAns A =>
            (OAns.pairPart uv.1).2 = OAns.singlePart uv.2,
          ntr (N.P.M ((.oracle, z) : Role × V) uv.1 *
            N.P.M ((.bob, S.LB z) : Role × V) uv.2) := by
    have h1 : ∑ bc ∈ (EBobAgree : Finset ((A × A) × A)),
        ntr ((N.push OAns.pairPart).M ((.oracle, z) : Role × V) bc.1 *
          (N.push OAns.singlePart).M ((.bob, S.LB z) : Role × V) bc.2)
        = ∑ p : A × A, ntr (oFam N z p * dFam N (S.LB z) p.2) := by
      rw [EBobAgree, Finset.sum_image fun x _ y _ h => (Prod.ext_iff.mp h).1]
      rfl
    rw [← h1, sum_push_pair]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext uv
    simp [mem_EBobAgree]
  rw [hagree, ← sum_ntr_pair_eq_one N ((.oracle, z) : Role × V) ((.bob, S.LB z) : Role × V),
    ← Finset.sum_filter_add_sum_filter_not univ
      fun uv : OAns A × OAns A => (OAns.pairPart uv.1).2 = OAns.singlePart uv.2, TBob]
  ring

/-- The mass the oracle puts on pairs the input predicate rejects. -/
theorem sum_game_reject (N : SyncStrategy S.oracular) (z : V) :
    ∑ p ∈ univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = false,
        ntr (oFam N z p)
      = ∑ uv ∈ S.TGame z,
          ntr (N.P.M ((.oracle, z) : Role × V) uv.1 *
            N.P.M ((.oracle, z) : Role × V) uv.2) := by
  rw [TGame, Finset.sum_image fun x _ y _ h => (Prod.ext_iff.mp h).1,
    show (∑ p ∈ univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = false,
          ntr (oFam N z p))
        = ∑ u ∈ univ.filter fun u : OAns A => OAns.pairPart u ∈
            univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = false,
            ntr (N.P.M ((.oracle, z) : Role × V) u) from
      sum_push_single N _ OAns.pairPart _]
  refine Finset.sum_congr ?_ fun u _ => ?_
  · ext u; simp
  · rw [N.P.projective]

/-! ## The three families are projective measurements -/

theorem oFam_selfAdjoint (N : SyncStrategy S.oracular) (z : V) (p : A × A) :
    star (oFam N z p) = oFam N z p := (N.push OAns.pairPart).selfAdjoint _ _

theorem oFam_projective (N : SyncStrategy S.oracular) (z : V) (p : A × A) :
    oFam N z p * oFam N z p = oFam N z p := (N.push OAns.pairPart).projective _ _

theorem cFam_selfAdjoint (N : SyncStrategy S.oracular) (x : V) (a : A) :
    star (cFam N x a) = cFam N x a := (N.push OAns.singlePart).selfAdjoint _ _

theorem cFam_projective (N : SyncStrategy S.oracular) (x : V) (a : A) :
    cFam N x a * cFam N x a = cFam N x a := (N.push OAns.singlePart).projective _ _

theorem dFam_selfAdjoint (N : SyncStrategy S.oracular) (y : V) (b : A) :
    star (dFam N y b) = dFam N y b := (N.push OAns.singlePart).selfAdjoint _ _

theorem dFam_projective (N : SyncStrategy S.oracular) (y : V) (b : A) :
    dFam N y b * dFam N y b = dFam N y b := (N.push OAns.singlePart).projective _ _

theorem sum_ntr_oFam (N : SyncStrategy S.oracular) (z : V) :
    ∑ p : A × A, ntr (oFam N z p) = 1 := by
  have := Fin.pos_iff_nonempty.mp N.d_pos
  rw [← ntr_sum, show (∑ p : A × A, oFam N z p) = 1 from
    (N.push OAns.pairPart).normalized ((.oracle, z) : Role × V)]
  exact ntr_one

theorem sum_ntr_cFam_dFam (N : SyncStrategy S.oracular) (x y : V) :
    ∑ p : A × A, ntr (cFam N x p.1 * dFam N y p.2) = 1 := by
  have := Fin.pos_iff_nonempty.mp N.d_pos
  rw [← ntr_sum, Fintype.sum_prod_type' fun a b => cFam N x a * dFam N y b,
    ← Fintype.sum_mul_sum,
    show (∑ a, cFam N x a) = 1 from (N.push OAns.singlePart).normalized ((.alice, x) : Role × V),
    show (∑ b, dFam N y b) = 1 from (N.push OAns.singlePart).normalized ((.bob, y) : Role × V),
    one_mul]
  exact ntr_one

/-! ## The per-seed quantities -/

/-- The squared Hilbert--Schmidt distance, at one seed, between the oracle's relabelled
measurement and the product of the two isolated players'. -/
noncomputable def sqDist (N : SyncStrategy S.oracular) (z : V) : ℝ :=
  ∑ p : A × A, hsNormSq (cFam N (S.LA z) p.1 * dFam N (S.LB z) p.2 - oFam N z p)

/-- The oracle's disagreement with Bob at one seed. -/
noncomputable def alphaTerm (N : SyncStrategy S.oracular) (z : V) : ℝ :=
  ∑ p : A × A, ntr (oFam N z p * (1 - dFam N (S.LB z) p.2))

/-- The oracle's disagreement with Alice at one seed. -/
noncomputable def betaTerm (N : SyncStrategy S.oracular) (z : V) : ℝ :=
  ∑ p : A × A, ntr (oFam N z p * (1 - cFam N (S.LA z) p.1))

/-- The mass the oracle puts on pairs the input predicate rejects, at one seed. -/
noncomputable def gammaTerm (N : SyncStrategy S.oracular) (z : V) : ℝ :=
  ∑ p ∈ univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = false, ntr (oFam N z p)

theorem alphaTerm_eq (N : SyncStrategy S.oracular) (z : V) :
    alphaTerm N z = 1 - ∑ p : A × A, ntr (oFam N z p * dFam N (S.LB z) p.2) := by
  rw [alphaTerm, ← sum_ntr_oFam N z, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [Matrix.mul_sub, Matrix.mul_one, ntr_sub]

theorem betaTerm_eq (N : SyncStrategy S.oracular) (z : V) :
    betaTerm N z = 1 - ∑ p : A × A, ntr (oFam N z p * cFam N (S.LA z) p.1) := by
  rw [betaTerm, ← sum_ntr_oFam N z, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [Matrix.mul_sub, Matrix.mul_one, ntr_sub]

/-- **The closeness estimate at one seed**, linear in the two disagreements. -/
theorem sqDist_le (N : SyncStrategy S.oracular) (z : V) :
    sqDist N z ≤ 3 * (alphaTerm N z + betaTerm N z) :=
  sum_hsNormSq_sub_le (fun p : A × A => oFam N z p) (fun p => cFam N (S.LA z) p.1)
    (fun p => dFam N (S.LB z) p.2)
    (fun p => oFam_selfAdjoint N z p) (fun p => oFam_projective N z p)
    (fun p => cFam_selfAdjoint N _ p.1) (fun p => cFam_projective N _ p.1)
    (fun p => dFam_selfAdjoint N _ p.2) (fun p => dFam_projective N _ p.2)
    (sum_ntr_oFam N z) (sum_ntr_cFam_dFam N _ _)

/-- **The value comparison at one seed**, where the square root is spent. -/
theorem valSeed_ge (N : SyncStrategy S.oracular) (z : V) :
    1 - gammaTerm N z - 2 * √(sqDist N z)
      ≤ ∑ a, ∑ b, (if S.D (S.LA z) (S.LB z) a b then 1 else 0) *
          ntr (cFam N (S.LA z) a * dFam N (S.LB z) b) := by
  have hacc : ∑ p ∈ univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = true,
      ntr (oFam N z p) = 1 - gammaTerm N z := by
    rw [gammaTerm, eq_sub_iff_add_eq, ← sum_ntr_oFam N z,
      show (univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = false)
        = univ.filter fun p : A × A => ¬ (S.D (S.LA z) (S.LB z) p.1 p.2 = true) from by
      ext p; simp]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hval : ∑ a, ∑ b, (if S.D (S.LA z) (S.LB z) a b then 1 else 0) *
        ntr (cFam N (S.LA z) a * dFam N (S.LB z) b)
      = ∑ p ∈ univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = true,
        ntr (cFam N (S.LA z) p.1 * dFam N (S.LB z) p.2) := by
    rw [Finset.sum_filter, ← Fintype.sum_prod_type' fun a b =>
      (if S.D (S.LA z) (S.LB z) a b = true then 1 else 0) *
        ntr (cFam N (S.LA z) a * dFam N (S.LB z) b)]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  rw [hval, ← hacc]
  have h := sum_ntr_mul_ge (fun p : A × A => oFam N z p) (fun p => cFam N (S.LA z) p.1)
    (fun p => dFam N (S.LB z) p.2)
    (univ.filter fun p : A × A => S.D (S.LA z) (S.LB z) p.1 p.2 = true)
    (fun p => oFam_selfAdjoint N z p) (fun p => oFam_projective N z p)
    (fun p => cFam_selfAdjoint N _ p.1) (fun p => cFam_projective N _ p.1)
    (fun p => dFam_selfAdjoint N _ p.2) (fun p => dFam_projective N _ p.2)
    (sum_ntr_oFam N z)
  have hd : sqDist N z = ∑ p : A × A,
      hsNormSq (cFam N (S.LA z) p.1 * dFam N (S.LB z) p.2 - oFam N z p) := rfl
  rw [hd]
  exact h

/-! ## The three budgets, averaged over the seed -/

theorem betaTerm_budget (N : SyncStrategy S.oracular) {ε : ℝ} (hval : 1 - ε ≤ N.value) :
    (Fintype.card V : ℝ)⁻¹ * ∑ z, betaTerm N z ≤ 9 * ε := by
  have h := budget N hval .oracle .alice (fun _ => TAlice) fun z => rejected_TAlice z
  simp only [S.oquestion_oracle, S.oquestion_alice] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [betaTerm_eq, sum_disagree_alice]

theorem alphaTerm_budget (N : SyncStrategy S.oracular) {ε : ℝ} (hval : 1 - ε ≤ N.value) :
    (Fintype.card V : ℝ)⁻¹ * ∑ z, alphaTerm N z ≤ 9 * ε := by
  have h := budget N hval .oracle .bob (fun _ => TBob) fun z => rejected_TBob z
  simp only [S.oquestion_oracle, S.oquestion_bob] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [alphaTerm_eq, sum_disagree_bob]

theorem gammaTerm_budget (N : SyncStrategy S.oracular) {ε : ℝ} (hval : 1 - ε ≤ N.value) :
    (Fintype.card V : ℝ)⁻¹ * ∑ z, gammaTerm N z ≤ 9 * ε := by
  have h := budget N hval .oracle .oracle S.TGame fun z => rejected_TGame z
  simp only [S.oquestion_oracle] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [gammaTerm, sum_game_reject]

/-! ## Soundness -/

/-- **Soundness of oracularization** (item 2 of blueprint `thm:oracularization`), at the level
of games: a synchronous strategy of value at least `1 - ε` for the oracularized game yields
one of value at least `1 - 24 √ε` for the doubled input game. The loss carries the *single*
square root of repair 1 of `rem:oracularization-repairs`, and it is spent in exactly one place,
`MIPRE.sum_ntr_mul_ge`. -/
theorem soundStrategy_value_ge (N : SyncStrategy S.oracular) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hval : 1 - ε ≤ N.value) :
    1 - 24 * √ε ≤ (soundStrategy N).value := by
  have hcardV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hW : (0 : ℝ) < (Fintype.card V : ℝ)⁻¹ := by positivity
  have hsq : ∀ z, 0 ≤ sqDist N z := fun z => Finset.sum_nonneg fun p _ => hsNormSq_nonneg _
  have hA := alphaTerm_budget N hval
  have hB := betaTerm_budget N hval
  have hG := gammaTerm_budget N hval
  -- the averaged closeness is at most `54 ε`
  have hDelta : (Fintype.card V : ℝ)⁻¹ * ∑ z, sqDist N z ≤ 54 * ε := by
    have h3 : (Fintype.card V : ℝ)⁻¹ * ∑ z, sqDist N z
        ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, 3 * (alphaTerm N z + betaTerm N z) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => sqDist_le N z) hW.le
    have h4 : (Fintype.card V : ℝ)⁻¹ * ∑ z, 3 * (alphaTerm N z + betaTerm N z)
        = 3 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, alphaTerm N z)
          + 3 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, betaTerm N z) := by
      rw [show (∑ z : V, 3 * (alphaTerm N z + betaTerm N z))
          = 3 * (∑ z, alphaTerm N z) + 3 * ∑ z, betaTerm N z from by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        ring]
      ring
    linarith
  -- the averaging step: `𝔼 √(sqDist) ≤ √(54 ε)`
  have hjensen : (Fintype.card V : ℝ)⁻¹ * ∑ z, √(sqDist N z) ≤ √(54 * ε) := by
    have hj0 := sum_mul_sqrt_le (univ : Finset V) (fun _ => (Fintype.card V : ℝ)⁻¹)
      (fun z => sqDist N z) (fun _ => hW.le) hsq
    have hj1 : (∑ _z : V, (Fintype.card V : ℝ)⁻¹) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [hj1, Real.sqrt_one, one_mul, ← Finset.mul_sum, ← Finset.mul_sum] at hj0
    exact hj0.trans (Real.sqrt_le_sqrt hDelta)
  -- put the seeds together
  rw [soundStrategy_value]
  have hmono : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - gammaTerm N z - 2 * √(sqDist N z))
      ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, ∑ a, ∑ b,
          (if S.D (S.LA z) (S.LB z) a b then 1 else 0) *
            ntr (cFam N (S.LA z) a * dFam N (S.LB z) b) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => valSeed_ge N z) hW.le
  refine le_trans ?_ hmono
  have hexp : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - gammaTerm N z - 2 * √(sqDist N z))
      = 1 - (Fintype.card V : ℝ)⁻¹ * (∑ z, gammaTerm N z)
        - 2 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, √(sqDist N z)) := by
    rw [show (∑ z : V, (1 - gammaTerm N z - 2 * √(sqDist N z)))
        = ((∑ _z : V, (1 : ℝ)) - ∑ z, gammaTerm N z) - 2 * ∑ z, √(sqDist N z) from by
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
  nlinarith [hjensen, hG, heps, hs54, Real.sqrt_nonneg ε]

end SeededGame

end MIPRE
