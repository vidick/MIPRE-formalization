/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularGame
import MIPRE.Foundations.PerfectStrategy
import MIPRE.Foundations.GameDouble

/-!
# Completeness of oracularization

Item 1 of blueprint `thm:oracularization`: a value-`1` PCC strategy for the input game gives
one for the oracularized game of `MIPRE.SeededGame.oracular`.

The honest oracle measures the input strategy's *two* measurements jointly: at seed `z` its
operator for the answer pair `(a, b)` is `M^{(false, L^𝖠 z)}_a · M^{(true, L^𝖡 z)}_b`. That
product is a projection exactly because the two commute, which is what `IsPCC` supplies at the
question pair the seed determines — and the seed always determines a pair of positive weight,
since `z` itself lies in its fibre (`dist_pos`).

Repair 2 of `rem:oracularization-repairs` --- that the completeness witness has *identical
measurement operators* for the two players rather than a symmetric state, the campaign having
found the symmetry claim unjustified --- is structural here: a `SyncStrategy` is one family of
projective measurements played by both players, so there is nothing to arrange.
-/

namespace MIPRE

open Finset Matrix

namespace SeededGame

variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)

/-! ## The seed always lands on a question pair of positive weight -/

omit [Fintype A] [DecidableEq A] in

theorem dist_pos (z : V) : 0 < S.dist (S.LA z) (S.LB z) := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  refine div_pos ?_ hcard
  have hz : z ∈ univ.filter fun w => S.LA w = S.LA z ∧ S.LB w = S.LB z :=
    mem_filter.mpr ⟨mem_univ z, rfl, rfl⟩
  exact_mod_cast Finset.card_pos.mpr ⟨z, hz⟩

theorem doubled_mu_pos (z : V) :
    0 < S.toGame.doubled.μ (false, S.LA z) (true, S.LB z) := by
  rw [Game.doubled_μ]
  simpa using S.dist_pos z

/-! ## The oracle's joint measurement -/

variable {S}

/-- The commutation the oracle's joint measurement needs, from `IsPCC` at the question pair the
seed determines. -/
theorem commute_of_isPCC {T : SyncStrategy S.toGame.doubled} (hT : T.IsPCC)
    (z : V) (a b : A) :
    T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b
      = T.P.M (true, S.LB z) b * T.P.M (false, S.LA z) a :=
  hT _ _ (S.doubled_mu_pos z) a b

variable (S)

/-- The operators of the honest oracularized strategy: an oracle measures the input strategy's
two measurements jointly, an isolated player the one the input strategy would have used, and a
shape that does not match the role gets `0`. -/
noncomputable def oracleOp (T : SyncStrategy S.toGame.doubled) :
    Role × V → OAns A → Matrix (Fin T.d) (Fin T.d) ℂ
  | (.oracle, z), .pair a b => T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b
  | (.alice, x), .single a => T.P.M (false, x) a
  | (.bob, y), .single b => T.P.M (true, y) b
  | _, _ => 0

variable {S}

@[simp] theorem oracleOp_oracle_pair (T : SyncStrategy S.toGame.doubled) (z : V) (a b : A) :
    S.oracleOp T (.oracle, z) (.pair a b)
      = T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b := rfl

@[simp] theorem oracleOp_oracle_single (T : SyncStrategy S.toGame.doubled) (z : V) (a : A) :
    S.oracleOp T (.oracle, z) (.single a) = 0 := rfl

@[simp] theorem oracleOp_alice_single (T : SyncStrategy S.toGame.doubled) (x : V) (a : A) :
    S.oracleOp T (.alice, x) (.single a) = T.P.M (false, x) a := rfl

@[simp] theorem oracleOp_alice_pair (T : SyncStrategy S.toGame.doubled) (x : V) (a b : A) :
    S.oracleOp T (.alice, x) (.pair a b) = 0 := rfl

@[simp] theorem oracleOp_bob_single (T : SyncStrategy S.toGame.doubled) (y : V) (b : A) :
    S.oracleOp T (.bob, y) (.single b) = T.P.M (true, y) b := rfl

@[simp] theorem oracleOp_bob_pair (T : SyncStrategy S.toGame.doubled) (y : V) (a b : A) :
    S.oracleOp T (.bob, y) (.pair a b) = 0 := rfl

/-- The honest oracularized measurement family. Projectivity of the oracle's operators is
where the commutation of `IsPCC` is used. -/
noncomputable def oracleMeas (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    ProjectiveMeasurement (Role × V) (OAns A) (Matrix (Fin T.d) (Fin T.d) ℂ) where
  M := S.oracleOp T
  selfAdjoint := by
    rintro ⟨r, z⟩ u
    cases r <;> cases u
    · simp only [oracleOp_oracle_pair, star_mul, T.P.selfAdjoint]
      exact (commute_of_isPCC hT z _ _).symm
    · simp
    · simp
    · simp [T.P.selfAdjoint]
    · simp
    · simp [T.P.selfAdjoint]
  projective := by
    rintro ⟨r, z⟩ u
    cases r <;> cases u
    · rename_i a b
      have hP := T.P.projective (false, S.LA z) a
      have hQ := T.P.projective (true, S.LB z) b
      calc T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b *
              (T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b)
          = T.P.M (false, S.LA z) a * (T.P.M (true, S.LB z) b *
              T.P.M (false, S.LA z) a) * T.P.M (true, S.LB z) b := by noncomm_ring
        _ = T.P.M (false, S.LA z) a * (T.P.M (false, S.LA z) a *
              T.P.M (true, S.LB z) b) * T.P.M (true, S.LB z) b := by
            rw [← commute_of_isPCC hT z a b]
        _ = T.P.M (false, S.LA z) a * T.P.M (false, S.LA z) a *
              (T.P.M (true, S.LB z) b * T.P.M (true, S.LB z) b) := by noncomm_ring
        _ = T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b := by rw [hP, hQ]
    · simp
    · simp
    · simp [T.P.projective]
    · simp
    · simp [T.P.projective]
  normalized := by
    rintro ⟨r, z⟩
    cases r
    · rw [OAns.sum_eq]
      simp only [oracleOp_oracle_pair, oracleOp_oracle_single, Finset.sum_const_zero, add_zero]
      rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, T.P.normalized, T.P.normalized, one_mul]
    · rw [OAns.sum_eq]
      simp only [oracleOp_alice_pair, oracleOp_alice_single, Finset.sum_const_zero, zero_add]
      exact T.P.normalized _
    · rw [OAns.sum_eq]
      simp only [oracleOp_bob_pair, oracleOp_bob_single, Finset.sum_const_zero, zero_add]
      exact T.P.normalized _

end SeededGame

end MIPRE
