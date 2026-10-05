/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Verifier
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import MIPRE.Tactics

@[expose] public section

/-!
# Tailored games and Z-aligned permutation strategies

Paper II of the Aldous–Lyons track (Bowen–Chapman–Vidick, arXiv:2501.00173), §2.2–2.4
(II:1008–1290); the plan is `planning/aldous-lyons-track.md`. This file is the library-side
vocabulary of the track: the statement file `MIPRE.TailoredGameValue` has its own first-order
copy, written against Mathlib only, which the library is to be bridged to.

* `MIPRE.Tailored.TailoredGame X`: a game on the question set `X` whose question `x` has
  `lenR x` *readable* and `lenL x` *linear* formal variables, and whose decision is given by
  *controlled linear constraints*: for questions `x, y` and readable answers `a^R, b^R`, a list
  `cons x y a^R b^R` of vectors over `S_x ⊔ S_y ⊔ {J}`. The answers are bit strings, the answer
  at `x` of length exactly `len x = lenR x + lenL x`, readable bits first.
* `TailoredGame.Accepts`: the paper's *canonical decider* (II:1757–1787): both answers have the
  right length, and every constraint `c` satisfies `⟨c, a b 1⟩ = 0` over `F₂` (`Satisfies`),
  the last coordinate `J` being set to `1`. The empty list accepts, `[rejectConstraint _]`
  rejects.
* `TailoredGame.toGame`, `valStar`: the bipartite game, with answers the bit strings of length
  at most `maxLen`, and its quantum value. Answers of the wrong length are rejected, so the
  alphabet is the paper's `F₂^{S_x}` up to answers that lose.
* `TailoredGame.doubled`: the game on the doubled question set, Alice asked `(false, x)` and
  Bob `(true, y)` — again a tailored game, bipartite, with no weight on loops; it is the game
  in which the pipeline's completeness clauses are read, as `Verifier.HasPerfectPCC` reads the
  completeness of the existing pipeline on `Verifier.doubledGame`.
* `PermStrategy`, `HasPerfectZPC` (II:1043–1057, II:1279–1283): a strategy whose observables
  are signed permutation matrices — one per formal variable, involutions, commuting at each
  question — with diagonal observables for the readable variables (*Z-aligned*) and commuting
  across the edges of positive weight (*commuting along edges*); its measurements are the
  Fourier transforms `P^x_a = ∏_i (1 + (-1)^{a_i} U(x, i)) / 2`, and it is *perfect* when its
  value is `1`. The answer alphabet at `x` is literally `F₂^{len x}` here, as in the paper.

Nothing is proved about these objects yet: Phase 1 of the plan proves that a permutation
strategy is a synchronous strategy commuting on the support with the same value
(`ZPC → PCC`), and the transports between this file and `MIPRE.TailoredGameValue`.
-/

namespace MIPRE.Tailored

open Cost

/-! ## Linear constraints over `F₂` -/

/-- A bit vector `v` satisfies the linear constraint `c` when they have the same length and
`⟨c, v⟩ = 0` over `F₂`. A constraint of the wrong length is never satisfied, as the paper's
canonical decider rejects malformed constraints. -/
def Satisfies (c v : BitStr) : Prop :=
  c.length = v.length ∧ Even ((List.zipWith (· && ·) c v).count true)

instance (c v : BitStr) : Decidable (Satisfies c v) := by
  unfold Satisfies; infer_instance

/-- The constraint `J = 0` on `d` variables and the affine coordinate: never satisfied by a
vector whose last coordinate is `1`, so a constraint list containing it rejects. -/
def rejectConstraint (d : ℕ) : BitStr := List.replicate d false ++ [true]

/-! ## Tailored games -/

/-- A tailored game (II:1243) on the finite question set `X`. -/
structure TailoredGame (X : Type*) [Fintype X] where
  /-- The probability of the question pair `(x, y)`. -/
  μ : X → X → ℝ
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  /-- The number of readable variables at a question. -/
  lenR : X → ℕ
  /-- The number of linear variables at a question. -/
  lenL : X → ℕ
  /-- The controlled linear constraints `L_xy(a^R, b^R)`: vectors over the variables at `x`
  (readable, then linear), those at `y`, and the affine coordinate `J`. -/
  cons : X → X → BitStr → BitStr → List BitStr

namespace TailoredGame

variable {X : Type*} [Fintype X] (G : TailoredGame X)

/-- The number of variables at a question, the length of its answers. -/
def len (x : X) : ℕ := G.lenR x + G.lenL x

/-- The largest answer length. -/
def maxLen : ℕ := Finset.univ.sup G.len

/-- The canonical decider (II:1757–1787): both answers have their lengths, and every
constraint of `L_xy(a^R, b^R)` is satisfied by the two answers followed by `J = 1`. -/
def Accepts (x y : X) (a b : BitStr) : Prop :=
  a.length = G.len x ∧ b.length = G.len y ∧
    ∀ c ∈ G.cons x y (a.take (G.lenR x)) (b.take (G.lenR y)), Satisfies c (a ++ b ++ [true])

instance (x y : X) (a b : BitStr) : Decidable (G.Accepts x y a b) := by
  unfold Accepts; infer_instance

/-- The bipartite game: answers the bit strings of length at most `maxLen`, accepted by the
canonical decider. -/
noncomputable def toGame :
    Game X X (Verifier.Answers G.maxLen) (Verifier.Answers G.maxLen) where
  μ := G.μ
  μ_nonneg := G.μ_nonneg
  μ_sum_one := G.μ_sum_one
  D x y a b := decide (G.Accepts x y a.1 b.1)

/-- The quantum value of a tailored game. -/
noncomputable def valStar : ℝ := quantumValue G.toGame

/-- The game on the doubled question set: Alice is asked `(false, x)`, Bob `(true, y)`, with
the weight of `(x, y)`; every other pair has no weight. The variables and constraints are those
of the underlying questions. -/
def doubled : TailoredGame (Bool × X) where
  μ p q := if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0
  μ_nonneg p q := by split_ifs; exacts [G.μ_nonneg _ _, le_rfl]
  μ_sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [G.μ_sum_one]
  lenR p := G.lenR p.2
  lenL p := G.lenL p.2
  cons p q := G.cons p.2 q.2

end TailoredGame

/-! ## Z-aligned permutation strategies commuting along edges -/

/-- The signed permutation matrix `e_j ↦ (-1)^{s j} e_{σ j}` (II:1043–1053): the action of the
signed permutation `(σ, s)` of `Ω_± = {±} × Fin m` on the anti-symmetric functions, in their
standard basis. -/
def signedPermMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin m → Bool) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if σ j = i then (if s j then -1 else 1) else 0

/-- A signed permutation matrix. -/
def IsSignedPerm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ σ s, M = signedPermMatrix σ s

variable {X : Type*} [Fintype X]

/-- A Z-aligned permutation strategy commuting along edges (II:1056, II:1279–1283) for a
tailored game: on `ℂ^m`, an observable `U x i` for each variable `i` at each question `x`, a
signed permutation matrix and an involution, the observables at a question commuting; the
observables of the readable variables are diagonal, and the observables at the two ends of an
edge of positive weight commute. -/
structure PermStrategy (G : TailoredGame X) where
  /-- The dimension. -/
  m : ℕ
  m_pos : 0 < m
  /-- The observables. -/
  U : (x : X) → Fin (G.len x) → Matrix (Fin m) (Fin m) ℂ
  signedPerm : ∀ x i, IsSignedPerm (U x i)
  invol : ∀ x i, U x i * U x i = 1
  comm : ∀ x i j, U x i * U x j = U x j * U x i
  zAligned : ∀ x (i : Fin (G.len x)), i.val < G.lenR x → (U x i).IsDiag
  commEdges : ∀ x y, 0 < G.μ x y → ∀ i j, U x i * U y j = U y j * U x i

namespace PermStrategy

variable {G : TailoredGame X} (S : PermStrategy G)

/-- The measurement at `x`, the Fourier transform of the observables (II:974):
`P^x_a = ∏_i (1 + (-1)^{a_i} U(x, i)) / 2`, for `a ∈ F₂^{len x}`. -/
noncomputable def proj (x : X) (a : Fin (G.len x) → Bool) : Matrix (Fin S.m) (Fin S.m) ℂ :=
  ((List.finRange (G.len x)).map fun i =>
    (1 / 2 : ℂ) • (1 + (if a i then (-1 : ℂ) else 1) • S.U x i)).prod

/-- The value of a permutation strategy (II:1130): the players answer `(x, y)` with
`(a, b)` with probability `Tr(P^x_a P^y_b) / m`. -/
noncomputable def value : ℝ :=
  ∑ x, ∑ y, ∑ a : Fin (G.len x) → Bool, ∑ b : Fin (G.len y) → Bool,
    G.μ x y * (if G.Accepts x y (List.ofFn a) (List.ofFn b) then 1 else 0) *
      ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ))

end PermStrategy

/-- The game has a perfect Z-aligned permutation strategy commuting along edges (II:1279). -/
def TailoredGame.HasPerfectZPC (G : TailoredGame X) : Prop := ∃ S : PermStrategy G, S.value = 1

end MIPRE.Tailored

end
