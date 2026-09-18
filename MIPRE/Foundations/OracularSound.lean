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

Item 2 of blueprint `thm:oracularization`, at the level of games.
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

end SeededGame

end MIPRE
