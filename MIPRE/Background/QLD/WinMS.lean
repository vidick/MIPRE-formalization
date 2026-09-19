/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Win
import MIPRE.Background.QLD.Anticomm

/-!
# The Magic Square item of the win implications

Blueprint `lem:qld-win`, item 6 (the paper's `enu:qld-ms` in `lem:qld-win-implications`). It is
the one item that is not a consistency relation: it says that on an *anticommuting* tuple `ω`
the Pauli basis test's own `Constraint`/`Variable` measurements form a strategy for the Magic
Square game of value `1 - O(ε)`. Composed with `lem:ms-direct-anticomm` --- which is what the
Magic Square is in the test for --- it gives the anticommutator bound this file ends with, and
that bound is what the expansion stage's sign cancellation runs on.

## The conditional strategy

`msPOVM M ω` is the strategy: at a Magic Square question `x` it is the Pauli test's measurement
at the corresponding question `msQ ω x`, relabelled into the Magic Square's answer alphabet by
`msAns`. The relabelling is where the paper's `F_2^3` constraint answers meet the layout's full
`F_2^9` assignments: `msAssign` places the three bits at the constraint's cells
(`MIPRE.LCS.MagicSquare.cell`) and `0` elsewhere, which is invisible to the Magic Square decider
because it reads only the support.

`sum_weight_bornProb_map` is what makes the relabelling harmless: relabelling outcomes is data
processing, so the relabelled strategy wins whenever the original answers would have been
accepted. That is `condFail_ms_le` --- the Magic Square failure at an incidence is at most the
Pauli test's failure at the corresponding question pair.

## The error, and why it is a sum over the incidences

`msEps` is the Magic Square game's own question-weighted sum of those Pauli-test failures, so
`one_sub_povmValue_ms_le` is immediate off the support --- where the Magic Square distribution
puts no mass, and the two deciders need not agree at all. On the support the pair *is* an
oriented incidence, hence an edge of the Pauli test's type graph, and `subtest_le` applies. The
average of `msEps` over the anticommuting tuples is then `86 ε`, one factor of `86` and not
thirty-six, because the Magic Square's own distribution is normalized.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LCS.MagicSquare

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The conditional Magic Square strategy -/

/-- The question type a Magic Square question corresponds to. -/
def msTy : layout.Question → Ty
  | .inl i => .con i
  | .inr j => .var j

/-- The Pauli-test question a Magic Square question corresponds to, at the tuple `ω`. -/
def msQ (ω : Omega F m) : layout.Question → Question F m
  | .inl i => .con i ω
  | .inr j => .var j ω

omit [DecidableEq F] [Algebra (ZMod 2) F] in
theorem question_msTy (hm : m ∣ Fintype.card F) (c : Content F m) (x : layout.Question) :
    c.question hm (msTy x) = msQ c.omega x := by
  cases x <;> rfl

/-- A constraint answer read as a full assignment: its three bits at the constraint's cells and
`0` elsewhere. The Magic Square decider reads only the support, so the padding is invisible. -/
def msAssign (i : Fin layout.r) : Answer F m d → (Fin layout.s → ZMod 2)
  | .bitTriple α => fun k => ∑ t : Fin 3, if cell i t = k then α t else 0
  | _ => fun _ => 0

/-- The reading of a Pauli-test answer as an answer of the Magic Square game. -/
def msAns : layout.Question → Answer F m d → layout.Answer
  | .inl i, a => .inl (msAssign i a)
  | .inr _, a => .inr (rdBit a)

/-- **The conditional Magic Square strategy of the tuple `ω`.** -/
def msPOVM (M : Question F m → POVM (Answer F m d) dA) (ω : Omega F m) :
    layout.Question → POVM layout.Answer dA :=
  fun x => (M (msQ ω x)).map (msAns x)

/-! ## The assignment reads the three bits -/

theorem cell_injective (i : Fin layout.r) : Function.Injective (cell i) :=
  Function.LeftInverse.injective (cellIdx_cell i)

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem msAssign_cell (i : Fin layout.r) (α : Fin 3 → ZMod 2) (t : Fin 3) :
    msAssign (d := d) (F := F) (m := m) i (.bitTriple α) (cell i t) = α t := by
  show (∑ t' : Fin 3, if cell i t' = cell i t then α t' else 0) = α t
  rw [Finset.sum_eq_single t (fun t' _ h => if_neg fun hh => h ((cell_injective i) hh))
    fun h => absurd (Finset.mem_univ t) h]
  exact if_pos rfl

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem sum_msAssign (i : Fin layout.r) (α : Fin 3 → ZMod 2) :
    ∑ k ∈ layout.V i, msAssign (d := d) (F := F) (m := m) i (.bitTriple α) k = ∑ t, α t := by
  rw [sum_cells, msAssign_cell, msAssign_cell, msAssign_cell, Fin.sum_univ_three]

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem msAssign_mem (i : Fin layout.r) (α : Fin 3 → ZMod 2) {j : Fin layout.s}
    (hj : j ∈ layout.V i) :
    msAssign (d := d) (F := F) (m := m) i (.bitTriple α) j = α (cellIdx i j) := by
  obtain ⟨t, rfl⟩ : ∃ t, cell i t = j := ⟨cellIdx i j, cell_cellIdx hj⟩
  rw [msAssign_cell, cellIdx_cell]

/-! ## The Pauli test's Magic Square rule implies the Magic Square game's decider -/

theorem adj_con_var {i : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V i) :
    adj (.con i) (.var j) = true := by
  simp [adj, adjRaw, h]

theorem adj_var_con {i : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V i) :
    adj (.var j) (.con i) = true := by
  rw [adj_symm]; exact adj_con_var h

theorem accepts_ms_of_accepts {hm : m ∣ Fintype.card F} {i : Fin layout.r} {j : Fin layout.s}
    {ω : Omega F m} {a b : Answer F m d} (hγ : gam ω ≠ 0)
    (h : accepts hm (.con i ω) (.var j ω) a b = true) :
    game.accepts (.inl i) (.inr j) (msAns (.inl i) a) (msAns (.inr j) b) = true := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨α, rfl⟩ := eq_bitTriple_of_fmtOk hfa
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_var hfb
  have hs' : (j ∈ layout.V i ∧ (∑ t, α t) = game.b i) ∧ α (cellIdx i j) = b' := by
    simpa [subtests, Question.ty, pairTest, hγ] using hs
  have h1 : j ∈ layout.V i := hs'.1.1
  have h2 : ∑ k ∈ layout.V i, msAssign (d := d) (F := F) (m := m) i (.bitTriple α) k = game.b i := by
    rw [sum_msAssign]; exact hs'.1.2
  have h3 : msAssign (d := d) (F := F) (m := m) i (.bitTriple α) j = b' := by
    rw [msAssign_mem i α h1]; exact hs'.2
  simp [msAns, MIPRE.LCS.Game.accepts, rdBit, h1, h2, h3]

theorem accepts_ms_of_accepts' {hm : m ∣ Fintype.card F} {i : Fin layout.r} {j : Fin layout.s}
    {ω : Omega F m} {a b : Answer F m d} (hγ : gam ω ≠ 0)
    (h : accepts hm (.var j ω) (.con i ω) a b = true) :
    game.accepts (.inr j) (.inl i) (msAns (.inr j) a) (msAns (.inl i) b) = true := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_var hfa
  obtain ⟨α, rfl⟩ := eq_bitTriple_of_fmtOk hfb
  have hs' : (j ∈ layout.V i ∧ (∑ t, α t) = game.b i) ∧ α (cellIdx i j) = b' := by
    simpa [subtests, Question.ty, pairTest, hγ] using hs
  have h1 : j ∈ layout.V i := hs'.1.1
  have h2 : ∑ k ∈ layout.V i, msAssign (d := d) (F := F) (m := m) i (.bitTriple α) k = game.b i := by
    rw [sum_msAssign]; exact hs'.1.2
  have h3 : msAssign (d := d) (F := F) (m := m) i (.bitTriple α) j = b' := by
    rw [msAssign_mem i α h1]; exact hs'.2
  simp [msAns, MIPRE.LCS.Game.accepts, rdBit, h1, h2, h3]

/-! ## The failure transfers -/

section Transfer

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}

/-- **Relabelling is data processing, so the Magic Square failure at a question pair is at most
the Pauli test's failure at the corresponding pair** --- given that the Pauli test's rule is the
stricter of the two there. -/
theorem condFail_ms_le (ω : Omega F m) (x y : layout.Question)
    (hD : ∀ a b : Answer F m d, accepts hm (msQ ω x) (msQ ω y) a b = true →
      game.accepts x y (msAns x a) (msAns y b) = true) :
    condFail nonlocalGame ψ (msPOVM MA ω) (msPOVM MB ω) x y
      ≤ condFail (qldGame hm) ψ MA MB (msQ ω x) (msQ ω y) := by
  classical
  have hwin : condWin (qldGame hm) ψ MA MB (msQ ω x) (msQ ω y)
      ≤ condWin nonlocalGame ψ (msPOVM MA ω) (msPOVM MB ω) x y := by
    rw [condWin, condWin, msPOVM, msPOVM,
      sum_weight_bornProb_map (ψ := ψ) (MA (msQ ω x)) (MB (msQ ω y)) (msAns x) (msAns y)
        fun A B => if nonlocalGame.D x y A B then (1 : ℝ) else 0]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have h0 : 0 ≤ bornProb ψ (((MA (msQ ω x)).mats a).val) (((MB (msQ ω y)).mats b).val) :=
      bornProb_nonneg ψ ((MA (msQ ω x)).posSemidef a) ((MB (msQ ω y)).posSemidef b)
    refine mul_le_mul_of_nonneg_right ?_ h0
    by_cases h : (qldGame hm).D (msQ ω x) (msQ ω y) a b = true
    · rw [if_pos h, if_pos (show nonlocalGame.D x y (msAns x a) (msAns y b) = true from hD a b h)]
    · rw [if_neg h]
      split_ifs <;> norm_num
  rw [condFail, condFail]
  linarith

/-- The error the conditional Magic Square strategy inherits: the Magic Square game's own
question-weighted sum of the Pauli test's conditional failures. -/
def msEps (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (ω : Omega F m) : ℝ :=
  ∑ x : layout.Question, ∑ y : layout.Question,
    layout.questionDist x y * condFail (qldGame hm) ψ MA MB (msQ ω x) (msQ ω y)

theorem msEps_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (ω : Omega F m) : 0 ≤ msEps hm ψ MA MB ω :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (layout.questionDist_nonneg _ _) (condFail_nonneg hψ _ _)

/-- Off the support of the Magic Square distribution the two deciders need not agree at all; on
it, the pair is an oriented incidence. -/
theorem incidence_of_questionDist_ne_zero {x y : layout.Question}
    (h : layout.questionDist x y ≠ 0) :
    (∃ i j, j ∈ layout.V i ∧ x = .inl i ∧ y = .inr j) ∨
      (∃ i j, j ∈ layout.V i ∧ x = .inr j ∧ y = .inl i) := by
  cases x with
  | inl i =>
      cases y with
      | inl i' => exact absurd rfl h
      | inr j =>
          refine Or.inl ⟨i, j, ?_, rfl, rfl⟩
          by_contra hj
          exact h (by simp [MIPRE.LCS.Layout.questionDist, hj])
  | inr j =>
      cases y with
      | inl i =>
          refine Or.inr ⟨i, j, ?_, rfl, rfl⟩
          by_contra hj
          exact h (by simp [MIPRE.LCS.Layout.questionDist, hj])
      | inr j' => exact absurd rfl h

/-- **The conditional Magic Square strategy of an anticommuting tuple fails by at most
`msEps`.** -/
theorem one_sub_povmValue_ms_le {ω : Omega F m} (hγ : gam ω ≠ 0) :
    1 - povmValue nonlocalGame ψ (msPOVM MA ω) (msPOVM MB ω) ≤ msEps hm ψ MA MB ω := by
  rw [one_sub_povmValue_eq, msEps]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  by_cases h : layout.questionDist x y = 0
  · rw [show nonlocalGame.μ x y = layout.questionDist x y from rfl, h, zero_mul, zero_mul]
  · rw [show nonlocalGame.μ x y = layout.questionDist x y from rfl]
    refine mul_le_mul_of_nonneg_left ?_ (layout.questionDist_nonneg x y)
    rcases incidence_of_questionDist_ne_zero h with ⟨i, j, _, rfl, rfl⟩ | ⟨i, j, _, rfl, rfl⟩
    · exact condFail_ms_le ω _ _ fun a b hab => accepts_ms_of_accepts hγ hab
    · exact condFail_ms_le ω _ _ fun a b hab => accepts_ms_of_accepts' hγ hab

/-- **The averaged error is `86 ε`**, one factor of `86` and not thirty-six: the Magic Square's
own question distribution is normalized, so the thirty-six incidences share the mass rather than
each contributing. -/
theorem sum_msEps_le (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ * msEps hm ψ MA MB c.omega
      ≤ 86 * ε := by
  classical
  -- the average of the Pauli test's failures at the questions a Magic Square question pair names
  set S : layout.Question → layout.Question → ℝ := fun x y =>
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
      condFail (qldGame hm) ψ MA MB (c.question hm (msTy x)) (c.question hm (msTy y)) with hSdef
  have step1 : ∀ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * msEps hm ψ MA MB c.omega
      = ∑ x : layout.Question, ∑ y : layout.Question,
          layout.questionDist x y * ((Fintype.card (Content F m) : ℝ)⁻¹ *
            condFail (qldGame hm) ψ MA MB (c.question hm (msTy x)) (c.question hm (msTy y))) := by
    intro c
    rw [msEps, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [question_msTy, question_msTy]
    ring
  -- exchange the content average with the Magic Square question average
  have hex : ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ * msEps hm ψ MA MB c.omega
      = ∑ x : layout.Question, ∑ y : layout.Question, layout.questionDist x y * S x y := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ acommSet) => step1 c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  -- termwise, the Pauli test's subtest bound at that edge of the type graph
  have hterm : ∀ x y : layout.Question,
      layout.questionDist x y * S x y ≤ layout.questionDist x y * (86 * ε) := by
    intro x y
    by_cases h : layout.questionDist x y = 0
    · rw [h, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (layout.questionDist_nonneg x y)
      rw [hSdef]
      rcases incidence_of_questionDist_ne_zero h with ⟨i, j, hj, rfl, rfl⟩ | ⟨i, j, hj, rfl, rfl⟩
      · exact subtest_le hψ hfail (adj_con_var hj) acommSet
      · exact subtest_le hψ hfail (adj_var_con hj) acommSet
  have hsum : (∑ x : layout.Question, ∑ y : layout.Question, layout.questionDist x y)
        * (86 * ε)
      = ∑ x : layout.Question, ∑ y : layout.Question, layout.questionDist x y * (86 * ε) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_mul _ _ _
  rw [hex]
  refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y) ?_
  rw [← hsum, MIPRE.LCS.Layout.sum_questionDist r_pos V_nonempty, one_mul]

/-! ## The point observables

The first half of the paper's `lem:qld-win-implications-obs`: item 1 at the two-outcome probe,
then `xStateDist_obsOf_le`. -/

/-- **The point observables are cross-party consistent**, the paper's `eq:pts-obs-consistency`.
For each basis `W` and each `r ∈ F_q`, the `±1`-observable of the two-outcome probe
`a ↦ tr(a r)` of the `(Point, W)` measurement is cross-party consistent at `344 ε = 2 · 172 ε`,
the `2` being the two outcomes of the probe. Item 1 at the reading `φ = tr(· r)`, then
`xStateDist_obsOf_le`. -/
theorem pts_obs_consistency (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) (r : F) :
    xStateDist (fun _ : Content F m => (Fintype.card (Content F m) : ℝ)⁻¹) ψ
        (obsOf sgn fun c => (MA (c.question hm (.point W))).map (fun a => prb (rdVal a) r))
        (obsOf sgn fun c => (MB (c.question hm (.point W))).map (fun a => prb (rdVal a) r))
      ≤ 344 * ε := by
  refine le_trans (xStateDist_obsOf_le (fun _ => by positivity) ψ _ _ sgn
    fun a => le_of_eq (norm_sgn a)) ?_
  rw [show (344 : ℝ) * ε = (Fintype.card (ZMod 2) : ℝ) * (172 * ε) from by
    rw [ZMod.card]; push_cast; ring]
  exact mul_le_mul_of_nonneg_left
    (item_consistency hψ hfail (.point W) fun a => prb (rdVal a) r) (by positivity)


/-! ## The anticommutator bound

`lem:ms-direct-anticomm` applied to the conditional strategy of each anticommuting tuple, then
averaged. This is what the expansion stage consumes. -/

/-- **Item 6 of `lem:qld-win`, composed with `lem:ms-direct-anticomm`.** On average over the
anticommuting tuples, the anticommutator of the Pauli test's own two distinguished `Variable`
observables annihilates the state up to `186624 * 86 = 16049664` times the failure probability.

The two variables are `0` and `4` --- the paper's `Variable_1` and `Variable_5` --- which are the
ones its `(Point, X)` and `(Point, Z)` rules tie to the point measurements. -/
theorem item_magicSquare (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2
      ≤ 16049664 * ε := by
  classical
  have havg := MS.ms_direct_anticomm_avg (Ω := ↥(acommSet : Finset (Content F m)))
    (fun _ => (Fintype.card (Content F m) : ℝ)⁻¹) (fun _ => by positivity)
    (fun _ => ψ) (fun _ => hψ)
    (fun c => msPOVM MA c.val.omega) (fun c => msPOVM MB c.val.omega)
    (fun c => msEps hm ψ MA MB c.val.omega) (fun c => msEps_nonneg hψ _)
    fun c => one_sub_povmValue_ms_le (gam_ne_zero_of_mem_acommSet c.2)
  rw [Finset.sum_coe_sort acommSet fun c => (Fintype.card (Content F m) : ℝ)⁻¹ *
      ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2,
    Finset.sum_coe_sort acommSet fun c => (Fintype.card (Content F m) : ℝ)⁻¹ *
      msEps hm ψ MA MB c.omega] at havg
  refine le_trans havg ?_
  rw [show (16049664 : ℝ) * ε = 186624 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (sum_msEps_le hψ hfail) (by norm_num)

end Transfer

end MIPRE.QLD

end
