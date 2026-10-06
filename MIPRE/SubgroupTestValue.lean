/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Computability.Partrec
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Subgroup tests, their sofic value, and the Aldous–Lyons conjecture (paper I)

A self-contained statement file, depending on Mathlib only, for *The Aldous–Lyons Conjecture
I: Subgroup Tests* (L. Bowen, M. Chapman, A. Lubotzky, T. Vidick, arXiv:2408.00110, "paper I";
line numbers `I:n` of its LaTeX source). Its definitions, with the paper's:

* `SubgroupTestData` (I:439–457): a first-order description of a *subgroup test* over the free
  group on `nGen` generators — finitely many *challenges*, each a weight, a finite list `K` of
  words, and a decision on the subsets of `K`, given in disjunctive normal form over the
  literals "the `i`-th word of `K` lies (or does not lie) in the subgroup". Every decision
  function on the subsets of a finite `K` has such a form; the paper's decisions are arbitrary.
* `FiniteAction`, `SubgroupTestData.value`, `SubgroupTestData.valSof` (I:501–520): a finite
  action `σ` of the free group, the value of the finitely described IRS `Φ(σ)` (the stabilizer of
  a uniform point) against the test, and the *sofic value*, its supremum over finite actions.
* `SofValueApproximable`: the sofic value is computable, in the sense that a computable function
  approximates it to within `1/(k+1)` on every test. Paper I deduces the negation of the
  Aldous–Lyons conjecture from its failure (Corollary I:605 with Main Theorem I, I:594).
* `SubgroupSpace`, `IRS`, `finDescIRS`, `AldousLyons` (I:467–530): the space of subgroups of
  the free group as a closed subspace of `{0,1}^F` with the product topology, the invariant
  random subgroups, the finitely described ones `Φ(σ)`, and the conjecture that the latter are
  weak-* dense in the former.

Words are lists of letters `(i, e)`, the generator `i` (to the power `-1` when `e`), read as a
product from left to right; a letter whose generator is not among the `nGen` acts as the
identity. A literal `(i, b)` with `i` beyond the length of `K` is false.
-/

namespace SubgroupTestValue

/-! ## Descriptions of subgroup tests -/

/-- A letter: a generator and whether it is inverted. -/
abbrev Letter := ℕ × Bool

/-- A word in the generators and their inverses. -/
abbrev Word := List Letter

/-- A first-order description of a subgroup test (I:439–457) over the free group on `nGen`
generators: a list of challenges `(weight, K, clauses)`. The challenge is passed by a subgroup
`H` when some clause holds, a clause being a list of literals `(i, b)`, each saying that the
`i`-th word of `K` lies in `H` when `b` and does not when `¬b`. The challenge distribution is
proportional to the weights. -/
structure SubgroupTestData where
  nGen : ℕ
  challenges : List (ℕ × List Word × List (List (ℕ × Bool)))

namespace SubgroupTestData

/-- `SubgroupTestData` is a tuple of naturals and lists. -/
def equivTuple : SubgroupTestData ≃ ℕ × List (ℕ × List Word × List (List (ℕ × Bool))) where
  toFun T := (T.nGen, T.challenges)
  invFun t := ⟨t.1, t.2⟩

instance : Primcodable SubgroupTestData := Primcodable.ofEquiv _ equivTuple

end SubgroupTestData

/-! ## Finite actions and the value -/

/-- A finite action of the free group on `nGen` generators: a permutation of `Fin N`, `N ≥ 1`,
for each generator. -/
structure FiniteAction (nGen : ℕ) where
  N : ℕ
  N_pos : 0 < N
  σ : Fin nGen → Equiv.Perm (Fin N)

namespace FiniteAction

variable {nGen : ℕ} (σ : FiniteAction nGen)

/-- The permutation of a letter. -/
def letterPerm (l : Letter) : Equiv.Perm (Fin σ.N) :=
  if h : l.1 < nGen then (if l.2 then (σ.σ ⟨l.1, h⟩)⁻¹ else σ.σ ⟨l.1, h⟩) else 1

/-- The permutation of a word, the product of its letters from left to right. -/
def wordPerm (w : Word) : Equiv.Perm (Fin σ.N) := (w.map σ.letterPerm).prod

/-- The word `w` lies in the stabilizer `Stab(σ, x)` of the point `x`. -/
def InStab (x : Fin σ.N) (w : Word) : Prop := σ.wordPerm w x = x

instance (x : Fin σ.N) (w : Word) : Decidable (σ.InStab x w) := by
  unfold InStab; infer_instance

/-- The literal `(i, b)` holds at `x` for the list of words `K`. -/
def LitHolds (K : List Word) (x : Fin σ.N) (lit : ℕ × Bool) : Prop :=
  ∃ h : lit.1 < K.length, decide (σ.InStab x (K[lit.1]'h)) = lit.2

instance (K : List Word) (x : Fin σ.N) (lit : ℕ × Bool) : Decidable (σ.LitHolds K x lit) := by
  unfold LitHolds; infer_instance

/-- The stabilizer of `x` passes the challenge `(K, clauses)`: some clause holds. -/
def Passes (K : List Word) (clauses : List (List (ℕ × Bool))) (x : Fin σ.N) : Prop :=
  ∃ c ∈ clauses, ∀ lit ∈ c, σ.LitHolds K x lit

instance (K : List Word) (clauses : List (List (ℕ × Bool))) (x : Fin σ.N) :
    Decidable (σ.Passes K clauses x) := by
  unfold Passes; infer_instance

/-- The probability that the stabilizer of a uniform point passes the challenge. -/
noncomputable def passProb (K : List Word) (clauses : List (List (ℕ × Bool))) : ℝ :=
  ((Finset.univ.filter fun x => σ.Passes K clauses x).card : ℝ) / σ.N

end FiniteAction

namespace SubgroupTestData

variable (T : SubgroupTestData)

/-- The total weight of the challenges. -/
def totalWeight : ℕ := (T.challenges.map (·.1)).sum

/-- The value `val(T, Φ(σ))` (I:455) of the finitely described IRS of `σ`: the probability that
the stabilizer of a uniform point passes a challenge drawn with probability proportional to its
weight. -/
noncomputable def value (σ : FiniteAction T.nGen) : ℝ :=
  (T.challenges.map fun c => (c.1 : ℝ) * σ.passProb c.2.1 c.2.2).sum / T.totalWeight

/-- **The sofic value** (I:518): the supremum of the value over finite actions. -/
noncomputable def valSof : ℝ := ⨆ σ : FiniteAction T.nGen, T.value σ

end SubgroupTestData

/-- **The sofic value is approximable**: a computable function approximates it to within
`1/(k+1)` on every test. Paper I shows this follows from the Aldous–Lyons conjecture (Corollary
I:605), and, with paper II, that it is false (Corollary I:2144). -/
def SofValueApproximable : Prop :=
  ∃ f : SubgroupTestData → ℕ → ℚ, Computable₂ f ∧
    ∀ T k, |T.valSof - (f T k : ℝ)| ≤ 1 / ((k : ℝ) + 1)

/-! ## Invariant random subgroups and the conjecture -/

/-- The indicator functions of the subgroups of the free group on `Fin s`. -/
def IsSubgroupIndicator {s : ℕ} (A : FreeGroup (Fin s) → Bool) : Prop :=
  A 1 = true ∧ ∀ v w, A v = true → A w = true → A (v * w⁻¹) = true

/-- The space `Sub(F)` of subgroups of the free group on `Fin s`, as indicator functions, with
the subspace topology of the product topology on `{0,1}^F` (I:469). -/
def SubgroupSpace (s : ℕ) : Type := {A : FreeGroup (Fin s) → Bool // IsSubgroupIndicator A}

instance (s : ℕ) : TopologicalSpace (SubgroupSpace s) := instTopologicalSpaceSubtype

instance (s : ℕ) : MeasurableSpace (SubgroupSpace s) := borel _

instance (s : ℕ) : BorelSpace (SubgroupSpace s) := ⟨rfl⟩

/-- Conjugation by `w` on `Sub(F)`: `H ↦ w H w⁻¹`. -/
def conj {s : ℕ} (w : FreeGroup (Fin s)) (H : SubgroupSpace s) : SubgroupSpace s :=
  ⟨fun v => H.1 (w⁻¹ * v * w), by
    obtain ⟨h1, h2⟩ := H.2
    refine ⟨by simpa using h1, fun v u hv hu => ?_⟩
    have := h2 _ _ hv hu
    simpa [mul_assoc] using this⟩

/-- The **invariant random subgroups** (Definition I:486): the probability measures on `Sub(F)`
invariant under conjugation. -/
def IRS (s : ℕ) : Set (MeasureTheory.ProbabilityMeasure (SubgroupSpace s)) :=
  {μ | ∀ w : FreeGroup (Fin s), (μ : MeasureTheory.Measure (SubgroupSpace s)).map (conj w) = μ}

/-- The stabilizer `Stab(σ, x)` (I:503) of a point under a finite action, as an indicator. -/
def stab {s : ℕ} (σ : FiniteAction s) (x : Fin σ.N) : SubgroupSpace s :=
  ⟨fun v => decide (FreeGroup.lift σ.σ v x = x), by
    refine ⟨by simp, fun v w hv hw => ?_⟩
    simp only [decide_eq_true_eq] at hv hw ⊢
    rw [map_mul, map_inv, Equiv.Perm.mul_apply]
    have : (FreeGroup.lift σ.σ w)⁻¹ x = x := by
      rw [Equiv.Perm.inv_eq_iff_eq]; exact hw.symm
    rw [this, hv]⟩

/-- The **finitely described IRSs** `Φ(σ) = E_x 1_{Stab(σ, x)}` (I:510–514). -/
def finDescIRS (s : ℕ) : Set (MeasureTheory.ProbabilityMeasure (SubgroupSpace s)) :=
  {μ | ∃ σ : FiniteAction s, (μ : MeasureTheory.Measure (SubgroupSpace s)) =
    ((σ.N : ENNReal)⁻¹) • ∑ x : Fin σ.N, MeasureTheory.Measure.dirac (stab σ x)}

/-- **The Aldous–Lyons conjecture** (Conjecture I:528): for every finite rank, the finitely
described IRSs of the free group are weak-* dense in its IRSs. Paper I with paper II refutes it
(Corollary I:2144). -/
def AldousLyons : Prop := ∀ s : ℕ, IRS s ⊆ closure (finDescIRS s)

end SubgroupTestValue

end
