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

@[simp] theorem oracleMeas_M (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    (S.oracleMeas T hT).M = S.oracleOp T := rfl

/-! ## The support of the oracularized question distribution

Two questions of positive weight come from one seed. Everything the case analysis below needs
about `oDist` is in these two lemmas: equal roles force equal questions, so orthogonality is
available at a repeated question, and an oracle paired with an isolated player is paired with
*that player's own* question. -/

omit [Nonempty V] [Fintype A] [DecidableEq A] in
/-- On the support of `oDist` the two questions are read off one seed. -/
theorem exists_of_oDist_pos {p q : Role × V} (h : 0 < S.oDist p q) :
    ∃ r₁ r₂ z, S.oquestion r₁ z = p ∧ S.oquestion r₂ z = q := by
  by_contra hc
  push Not at hc
  rw [oDist] at h
  refine absurd (Finset.sum_eq_zero fun s _ => ?_) h.ne'
  obtain ⟨r₁, r₂, z⟩ := s
  have hne : (S.oquestion r₁ z, S.oquestion r₂ z) ≠ (p, q) := by
    intro he
    rw [Prod.ext_iff] at he
    exact hc r₁ r₂ z he.1 he.2
  simp [hne]

omit [Nonempty V] [Fintype A] [DecidableEq A] in
/-- On the support, equal roles mean equal questions. -/
theorem eq_of_oDist_pos_of_fst_eq {p q : Role × V} (h : 0 < S.oDist p q) (hr : p.1 = q.1) :
    p = q := by
  obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos h
  have h1 : r₁ = p.1 := by rw [← hp, oquestion_fst]
  have h2 : r₂ = q.1 := by rw [← hq, oquestion_fst]
  have hrr : r₁ = r₂ := by rw [h1, h2]; exact hr
  rw [← hp, ← hq, hrr]

/-! ## Rejected answers are zero operators

The honest oracle's operator at a pair the original predicate rejects is not merely
improbable: it is `0`. This is where faithfulness of the normalized trace
(`SyncStrategy.eq_zero_of_trace_re_eq_zero`) earns its keep, and it is what makes the case
analysis of the decider's seven checks short. -/

/-- An answer whose shape does not match the role gets the zero operator. -/
theorem oracleOp_eq_zero_of_shapeOk (T : SyncStrategy S.toGame.doubled) {p : Role × V}
    {u : OAns A} (h : shapeOk p.1 u = false) : S.oracleOp T p u = 0 := by
  obtain ⟨r, z⟩ := p
  cases r <;> cases u <;> simp_all [shapeOk]

/-- An oracle's answer pair that the original predicate rejects gets the zero operator. -/
theorem oracleOp_eq_zero_of_gameCheck (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    (hval : T.value = 1) {p : Role × V} {u : OAns A} (h : S.gameCheck p u = false) :
    S.oracleOp T p u = 0 := by
  obtain ⟨r, z⟩ := p
  cases r <;> cases u <;> simp only [gameCheck, Bool.true_eq_false] at h
  rename_i a b
  have hD : S.toGame.doubled.D (false, S.LA z) (true, S.LB z) a b = false := by
    simpa using h
  exact T.eq_zero_of_trace_re_eq_zero
    ((S.oracleMeas T hT).selfAdjoint (.oracle, z) (.pair a b))
    ((S.oracleMeas T hT).projective (.oracle, z) (.pair a b))
    (T.re_eq_zero_of_value_eq_one hval (S.doubled_mu_pos z) hD)

/-! ## The two consistency checks

An oracle's component for a player's role and that player's own answer are measured by
operators at the *same* question of the doubled game, so orthogonality applies once the
oracle's other factor has been commuted out of the way. -/

/-- Transposing a vanishing product: the operators are self-adjoint, so one order vanishes
exactly when the other does. -/
theorem oracleOp_mul_eq_zero_of_swap (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    {p q : Role × V} {u v : OAns A} (h : S.oracleOp T q v * S.oracleOp T p u = 0) :
    S.oracleOp T p u * S.oracleOp T q v = 0 := by
  have h1 : star (S.oracleOp T p u) = S.oracleOp T p u := by
    simpa using (S.oracleMeas T hT).selfAdjoint p u
  have h2 : star (S.oracleOp T q v) = S.oracleOp T q v := by
    simpa using (S.oracleMeas T hT).selfAdjoint q v
  have := congrArg star h
  rwa [star_mul, h1, h2, star_zero] at this

/-- Check 2(b) for Alice: the oracle's first component against Alice's answer. -/
theorem oracleOp_oracle_mul_alice (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) (z : V)
    {a a' : A} (b : A) (h : a ≠ a') :
    S.oracleOp T (.oracle, z) (.pair a b) * S.oracleOp T (.alice, S.LA z) (.single a') = 0 := by
  simp only [oracleOp_oracle_pair, oracleOp_alice_single]
  calc T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b * T.P.M (false, S.LA z) a'
      = T.P.M (false, S.LA z) a * (T.P.M (true, S.LB z) b * T.P.M (false, S.LA z) a') := by
        noncomm_ring
    _ = T.P.M (false, S.LA z) a * (T.P.M (false, S.LA z) a' * T.P.M (true, S.LB z) b) := by
        rw [← commute_of_isPCC hT z a' b]
    _ = T.P.M (false, S.LA z) a * T.P.M (false, S.LA z) a' * T.P.M (true, S.LB z) b := by
        noncomm_ring
    _ = 0 := by rw [T.orthogonal (false, S.LA z) h, Matrix.zero_mul]

/-- Check 2(b) for Bob: the oracle's second component against Bob's answer. -/
theorem oracleOp_oracle_mul_bob (T : SyncStrategy S.toGame.doubled) (z : V) (a : A)
    {b b' : A} (h : b ≠ b') :
    S.oracleOp T (.oracle, z) (.pair a b) * S.oracleOp T (.bob, S.LB z) (.single b') = 0 := by
  simp only [oracleOp_oracle_pair, oracleOp_bob_single]
  rw [Matrix.mul_assoc, T.orthogonal (true, S.LB z) h, Matrix.mul_zero]

/-! ## The honest oracularized strategy, and its value

`fig:oracle-decider` runs seven checks, and each one that can fail makes one of the two
operators, or their product, zero: a shape mismatch and a rejected oracle pair by
`oracleOp_eq_zero_of_shapeOk` and `oracleOp_eq_zero_of_gameCheck`, check 2(a) by orthogonality
at a repeated question (which the support lemma makes available), and check 2(b) by the two
lemmas above. So the strategy never produces a rejected outcome, and
`MIPRE.tracialValue_eq_one_of_re_eq_zero` turns that into value `1`. -/

variable (S)

/-- The honest strategy for the oracularized game: the same Hilbert space as the input
strategy, the joint measurement for an oracle, and the input strategy's own measurement for an
isolated player. -/
noncomputable def oracleStrategy (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    SyncStrategy S.oracular where
  d := T.d
  d_pos := T.d_pos
  P := S.oracleMeas T hT

variable {S}

@[simp] theorem oracleStrategy_d (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    (S.oracleStrategy T hT).d = T.d := rfl

/-- **No rejected outcome.** At any question pair of positive weight, the honest operators for
a rejected answer pair multiply to zero. -/
theorem oracleOp_mul_eq_zero (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    (hval : T.value = 1) {p q : Role × V} (hμ : 0 < S.oDist p q) {u v : OAns A}
    (hrej : S.oaccepts p q u v = false) :
    S.oracleOp T p u * S.oracleOp T q v = 0 := by
  simp only [oaccepts, Bool.and_eq_false_iff] at hrej
  rcases hrej with ((((((h | h) | h) | h) | h) | h) | h)
  · rw [oracleOp_eq_zero_of_shapeOk T h, Matrix.zero_mul]
  · rw [oracleOp_eq_zero_of_shapeOk T h, Matrix.mul_zero]
  · rw [oracleOp_eq_zero_of_gameCheck T hT hval h, Matrix.zero_mul]
  · rw [oracleOp_eq_zero_of_gameCheck T hT hval h, Matrix.mul_zero]
  · -- check 2(a): equal roles, unequal answers. On the support equal roles mean equal
    -- questions, so this is orthogonality of distinct outcomes.
    by_cases hpq : p.1 = q.1
    · have huv : u ≠ v := by simpa [hpq] using h
      have hp : p = q := eq_of_oDist_pos_of_fst_eq hμ hpq
      subst hp
      exact (S.oracleStrategy T hT).orthogonal p huv
    · simp [hpq] at h
  · -- check 2(b), the oracle first
    obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos hμ
    subst hp; subst hq
    cases r₁ <;> cases r₂ <;> cases u <;> cases v <;>
      simp only [oquestion, oracleVsPlayer, Bool.true_eq_false, decide_eq_false_iff_not] at h ⊢
    · exact oracleOp_oracle_mul_alice T hT z _ h
    · exact oracleOp_oracle_mul_bob T z _ h
  · -- check 2(b), the isolated player first
    refine oracleOp_mul_eq_zero_of_swap T hT ?_
    obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos hμ
    subst hp; subst hq
    cases r₁ <;> cases r₂ <;> cases u <;> cases v <;>
      simp only [oquestion, oracleVsPlayer, Bool.true_eq_false, decide_eq_false_iff_not] at h ⊢
    · exact oracleOp_oracle_mul_alice T hT z _ h
    · exact oracleOp_oracle_mul_bob T z _ h

/-- **Completeness of oracularization** (item 1 of blueprint `thm:oracularization`): a
value-`1` PCC synchronous strategy for the input game gives a value-`1` synchronous strategy
for the oracularized game, on the same Hilbert space and with the same operators. -/
theorem oracleStrategy_value_eq_one (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    (hval : T.value = 1) : (S.oracleStrategy T hT).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  refine tracialValue_eq_one_of_re_eq_zero S.oracular _ _ ?_
  intro p q hμ u v hrej
  rw [show (S.oracleStrategy T hT).P.M p u * (S.oracleStrategy T hT).P.M q v = 0 from
    oracleOp_mul_eq_zero T hT hval hμ hrej]
  rw [normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

/-! ## The honest strategy is PCC

Every honest operator at seed `z` is a product of factors drawn from the four atoms
`M^{(\mathsf{false}, L^𝖠 z)}_a` and `M^{(\mathsf{true}, L^𝖡 z)}_b`, and those atoms commute
pairwise: two at one question because distinct outcomes are orthogonal
(`SyncStrategy.orthogonal`) and equal ones are equal, and one of each because the input
strategy is PCC. So the case analysis is `Commute.mul_left` and `Commute.mul_right` over the
nine role pairs. -/

theorem oracleOp_commute (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    {p q : Role × V} (hμ : 0 < S.oDist p q) (u v : OAns A) :
    S.oracleOp T p u * S.oracleOp T q v = S.oracleOp T q v * S.oracleOp T p u := by
  obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos hμ
  subst hp; subst hq
  -- the four atoms at seed `z` commute pairwise
  have c1 : ∀ a a' : A, Commute (T.P.M (false, S.LA z) a) (T.P.M (false, S.LA z) a') := by
    intro a a'
    by_cases h : a = a'
    · rw [h]
    · show _ * _ = _ * _
      rw [T.orthogonal (false, S.LA z) h, T.orthogonal (false, S.LA z) (Ne.symm h)]
  have c2 : ∀ b b' : A, Commute (T.P.M (true, S.LB z) b) (T.P.M (true, S.LB z) b') := by
    intro b b'
    by_cases h : b = b'
    · rw [h]
    · show _ * _ = _ * _
      rw [T.orthogonal (true, S.LB z) h, T.orthogonal (true, S.LB z) (Ne.symm h)]
  have c3 : ∀ a b : A, Commute (T.P.M (false, S.LA z) a) (T.P.M (true, S.LB z) b) :=
    fun a b => commute_of_isPCC hT z a b
  -- hence every honest operator at seed `z` commutes with each atom
  have kA : ∀ (r : Role) (w : OAns A) (a : A),
      Commute (S.oracleOp T (S.oquestion r z) w) (T.P.M (false, S.LA z) a) := by
    intro r w a
    cases r <;> cases w <;>
      simp only [oquestion, oracleOp_oracle_pair, oracleOp_oracle_single, oracleOp_alice_pair,
        oracleOp_alice_single, oracleOp_bob_pair, oracleOp_bob_single] <;>
      first
        | exact Commute.zero_left _
        | exact c1 _ _
        | exact (c3 _ _).symm
        | exact Commute.mul_left (c1 _ _) ((c3 _ _).symm)
  have kB : ∀ (r : Role) (w : OAns A) (b : A),
      Commute (S.oracleOp T (S.oquestion r z) w) (T.P.M (true, S.LB z) b) := by
    intro r w b
    cases r <;> cases w <;>
      simp only [oquestion, oracleOp_oracle_pair, oracleOp_oracle_single, oracleOp_alice_pair,
        oracleOp_alice_single, oracleOp_bob_pair, oracleOp_bob_single] <;>
      first
        | exact Commute.zero_left _
        | exact c2 _ _
        | exact c3 _ _
        | exact Commute.mul_left (c3 _ _) (c2 _ _)
  -- so it commutes with every honest operator, by induction on the second one's shape
  cases r₂ <;> cases v <;>
    simp only [oquestion, oracleOp_oracle_pair, oracleOp_oracle_single, oracleOp_alice_pair,
      oracleOp_alice_single, oracleOp_bob_pair, oracleOp_bob_single] <;>
    first
      | exact Commute.zero_right _
      | exact kA _ _ _
      | exact kB _ _ _
      | exact Commute.mul_right (kA _ _ _) (kB _ _ _)

/-- **The honest oracularized strategy is PCC.** -/
theorem isPCC_oracleStrategy (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    (S.oracleStrategy T hT).IsPCC :=
  fun _ _ hμ u v => oracleOp_commute T hT hμ u v

end SeededGame

end MIPRE
