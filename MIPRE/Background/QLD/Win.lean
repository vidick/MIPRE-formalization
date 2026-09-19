/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Game
import MIPRE.Foundations.CrossConsistency

/-!
# What winning the Pauli basis test implies

Blueprint `lem:qld-win`, the paper's `lem:qld-win-implications` (`qld-commutation.tex`). A
strategy succeeding with probability `1 - ε` satisfies one cross-party consistency relation per
subtest, each at error `O(ε)` --- and the blueprint's proof is exactly one sentence: "each item
is the definition of the value of the corresponding subtest, divided by the probability that the
subtest is selected".

This file makes that sentence mechanical, in two steps.

## Step one: every subtest is selected with probability at least `1/86`

`qldGame`'s question distribution is uniform over `TyEdge × Content`, so a question pair arising
from a *fixed* ordered type edge has probability at least `1/86` times the conditional
probability of its content (`le_qldGame_mu`). `subtest_le` is the consequence: for any edge
`(t, u)` of the type graph, the content-averaged conditional failure at that edge is at most
`86 ε`. The `86` is `card_adj`, the ordered pairs of the type graph, and it is where the
paper's "the probability of any of the subtests being executed is at least some universal
constant" becomes a number.

Nothing here is about which subtest it is: one lemma serves all seven, because the
distribution factors.

## Step two: each item is an agreement subtest

`MIPRE.xSqNorm_sum_le_condFail` turns "the decider accepts iff `f a = g b`" into a bound on the
cross-party deviation of the POVMs coarse-grained along `f` and `g`. So each item of the lemma
is: name `f` and `g`, check the decider against them, and compose with `subtest_le`. That
composition is `agree_subtest_le`, and the seven items below are its instances --- the
identity for the plain consistency check, a polynomial evaluation for the low-degree check, the
low-degree encoding for Pauli-basis consistency, a projection for the commutation check, and the
trace probe `prb` for the two commutation- and Magic-Square-consistency checks.

The Magic Square item itself is not of this shape --- it is a statement about the *value* of a
conditional Magic Square strategy, which is what `lem:ms-direct-anticomm` consumes --- and it is
in `MIPRE/Background/QLD/WinMS.lean`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The size of the sample space -/

theorem card_TyEdge : Fintype.card TyEdge = 86 := by
  rw [Fintype.card_subtype]
  exact card_adj

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem card_Sample : Fintype.card (Sample F m) = 86 * Fintype.card (Content F m) := by
  rw [Fintype.card_prod, card_TyEdge]

omit [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem card_Content_pos : 0 < Fintype.card (Content F m) :=
  Fintype.card_pos_iff.mpr ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-! ## Every subtest is selected with probability at least `1/86` -/

/-- The question distribution in closed form: the fraction of samples that produce the pair. -/
theorem qldGame_mu_eq (hm : m ∣ Fintype.card F) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y
      = (Fintype.card (Sample F m) : ℝ)⁻¹ *
        (#{sm : Sample F m | (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2)
            = (x, y)} : ℝ) := by
  classical
  show ∑ sm : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ * _ = _
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_boole]

/-- **A subtest at a fixed edge of the type graph carries at least `1/86` of the mass.** The
sample space is an ordered type edge times the content, drawn independently and uniformly, so
conditioning on the edge costs exactly the `86` ordered pairs of `card_adj`. -/
theorem le_qldGame_mu (hm : m ∣ Fintype.card F) {t u : Ty} (htu : adj t u = true)
    (p : Question F m × Question F m) :
    (86 : ℝ)⁻¹ * ∑ _c ∈ univ.filter fun c : Content F m =>
        (c.question hm t, c.question hm u) = p, (Fintype.card (Content F m) : ℝ)⁻¹
      ≤ (qldGame (d := d) hm).μ p.1 p.2 := by
  classical
  set S : Finset (Content F m) :=
    univ.filter fun c => (c.question hm t, c.question hm u) = p with hS
  set T : Finset (Sample F m) :=
    univ.filter fun sm => (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = p with hT
  -- embedding the contents of the fixed edge into the samples that produce `p`
  have hcard : (#S : ℝ) ≤ (#T : ℝ) := by
    refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn
      (fun c => ((⟨(t, u), htu⟩ : TyEdge), c)) (fun c hc => ?_) fun a _ b _ h => ?_)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2⟩)
    · exact congrArg Prod.snd h
  have hL : (86 : ℝ)⁻¹ * ∑ _c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹
      = (86 : ℝ)⁻¹ * (Fintype.card (Content F m) : ℝ)⁻¹ * (#S : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hR : (Fintype.card (Sample F m) : ℝ)⁻¹ * (#T : ℝ)
      = (86 : ℝ)⁻¹ * (Fintype.card (Content F m) : ℝ)⁻¹ * (#T : ℝ) := by
    rw [card_Sample, Nat.cast_mul, mul_inv]; norm_num
  rw [qldGame_mu_eq hm, hL, hR]
  exact mul_le_mul_of_nonneg_left hcard (by positivity)

/-- **The content-averaged conditional failure of a subtest is at most `86 ε`.** This is the
blueprint's "divided by the probability that the subtest is selected", with the probability
computed. The sum is over any set `S` of contents, since a rule gated on `γ` fires only on part
of the sample space; dropping the rest only decreases a sum of nonnegative terms. -/
theorem subtest_le {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) {t u : Ty} (htu : adj t u = true)
    (S : Finset (Content F m)) :
    ∑ c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹ *
        condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u) ≤ 86 * ε := by
  classical
  have h := sum_condFail_le_of_pushforward (ι := Content F m) hψ hfail
    (fun _ => (Fintype.card (Content F m) : ℝ)⁻¹)
    (fun c => (c.question hm t, c.question hm u))
    (c := (86 : ℝ)⁻¹) (by norm_num) fun p => le_qldGame_mu hm htu p
  rw [show (ε / (86 : ℝ)⁻¹) = 86 * ε from by field_simp] at h
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun c _ _ => ?_) h
  exact mul_nonneg (by positivity) (condFail_nonneg hψ _ _)

/-! ## Each item is an agreement subtest -/

/-- **The master estimate for the Pauli basis test.** A subtest that accepts only when two
post-processings of the answers agree gives, at error `172 ε`, cross-party closeness of the
coarse-grained measurements --- averaged over the verifier's content, which is the "on average
over ..." of every item of `lem:qld-win`.

`S` is the set of contents on which the rule fires: everything for the ungated rules, the
commuting or the anticommuting tuples for the four rules gated on `γ`. The weight is `1/#Content`
throughout, so for a gated rule this is the *unconditional* average with the gate's indicator
inside; the paper's conditional form is this divided by the gate's probability, which is where
`fact:omega-anticomm-prob` and the hypothesis `6md ≤ q` enter.

The `172` is `2 · 86`: the factor `2` of `xSqNorm_sum_le_condFail` and the selection probability
`1/86` of `subtest_le`. -/
theorem agree_subtest_le {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) {t u : Ty} (htu : adj t u = true)
    {C : Type*} [Fintype C] [DecidableEq C] (S : Finset (Content F m))
    (f g : Content F m → Answer F m d → C)
    (hD : ∀ c ∈ S, ∀ a b, (qldGame hm).D (c.question hm t) (c.question hm u) a b = true →
      f c a = g c b) :
    ∑ c ∈ S, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
          ((((MB (c.question hm u)).map (g c)).mats o).val)
      ≤ 172 * ε := by
  classical
  have hstep : ∀ c ∈ S,
      (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
          ((((MB (c.question hm u)).map (g c)).mats o).val)
      ≤ 2 * ((Fintype.card (Content F m) : ℝ)⁻¹ *
        condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u)) := by
    intro c hc
    have h2 := xSqNorm_sum_le_condFail (G := qldGame hm) (ψ := ψ) (MA := MA) (MB := MB)
      hψ (f c) (g c) (hD c hc)
    have hk : (0 : ℝ) ≤ (Fintype.card (Content F m) : ℝ)⁻¹ := by positivity
    calc (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ o : C, xSqNorm ψ ((((MA (c.question hm t)).map (f c)).mats o).val)
            ((((MB (c.question hm u)).map (g c)).mats o).val)
        ≤ (Fintype.card (Content F m) : ℝ)⁻¹ *
            (2 * condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u)) :=
          mul_le_mul_of_nonneg_left h2 hk
      _ = 2 * ((Fintype.card (Content F m) : ℝ)⁻¹ *
            condFail (qldGame hm) ψ MA MB (c.question hm t) (c.question hm u)) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, show (172 : ℝ) * ε = 2 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (subtest_le hψ hfail htu S) (by norm_num)

/-! ## The readings each rule compares

A rule of `fig:decider_pauli` compares a post-processing of Alice's answer with one of Bob's.
Each is named here, with `0` on answers of the wrong format --- which costs nothing, because the
format check rejects those before any rule runs, and `xSqNorm_sum_le_condFail` only needs
*accept implies agree*. -/

/-- The field element a point answer reports. -/
def rdVal : Answer F m d → F
  | .val a => a
  | _ => 0

/-- The value at `y` of an axis-parallel line answer, at the parameter of `y` on the line. -/
def rdAPoly (u₀ w y : Point F m) : Answer F m d → F
  | .apoly p => p.eval (MIPRE.LIDT.CL.lineParam u₀ w y)
  | _ => 0

/-- The value at `y` of a diagonal line answer. -/
def rdDPoly (u₀ w y : Point F m) : Answer F m d → F
  | .dpoly p => p.eval (MIPRE.LIDT.CL.lineParam u₀ w y)
  | _ => 0

/-- The low-degree encoding of a `(Pauli, W)` answer, evaluated at `y`: the paper's
`g_h(y)`. -/
def rdPauli (y : Point F m) : Answer F m d → F
  | .pauliAns h => MvPolynomial.eval y (MIPRE.LowDegree.ldEnc h)
  | _ => 0

/-- The bit a `(Pair, W)` or `Variable_j` answer reports. -/
def rdBit : Answer F m d → ZMod 2
  | .bit b => b
  | _ => 0

/-- The `W`-component of a `Pair` answer. -/
def rdBitPair (W : Bas) : Answer F m d → ZMod 2
  | .bitPair β => β W
  | _ => 0

/-- The trace probe `tr(a · r)` of a point answer: the two-outcome measurement the commutation
and Magic Square checks compare against. -/
def rdProbe (r : F) : Answer F m d → ZMod 2
  | .val a => prb a r
  | _ => 0

/-- The axis-parallel direction the seed selects. -/
def dirOf (hm : m ∣ Fintype.card F) (c : Content F m) : Point F m :=
  Pi.single (MIPRE.LIDT.CL.chi hm c.s) 1

/-- Bob's reading of an axis-parallel line answer, at the point the same content gives Alice. -/
def rdALineAt (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) : Answer F m d → F :=
  rdAPoly (MIPRE.LIDT.CL.rep (dirOf hm c) (c.pt W)) (dirOf hm c) (c.pt W)

/-- Bob's reading of a diagonal line answer, at the point the same content gives Alice. -/
def rdDLineAt (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) : Answer F m d → F :=
  rdDPoly (MIPRE.LIDT.CL.rep (MIPRE.LIDT.CL.zeroBelow (MIPRE.LIDT.CL.chi hm c.s) c.v) (c.pt W))
    (MIPRE.LIDT.CL.zeroBelow (MIPRE.LIDT.CL.chi hm c.s) c.v) (c.pt W)

/-! ## The commuting and anticommuting contents

Four rules are gated on `γ(ω)` and check nothing on the other value, so their statements carry
the gate as a restriction of the content average. -/

/-- The contents whose tuple is *commuting*, `γ(ω) = 0`. -/
def commSet : Finset (Content F m) := univ.filter fun c => gam c.omega = 0

/-- The contents whose tuple is *anticommuting*, `γ(ω) ≠ 0`. -/
def acommSet : Finset (Content F m) := univ.filter fun c => gam c.omega ≠ 0

omit [DecidableEq F] [NeZero m] in
theorem gam_eq_zero_of_mem_commSet {c : Content F m} (hc : c ∈ commSet) :
    gam c.omega = 0 := (Finset.mem_filter.mp hc).2

omit [DecidableEq F] [NeZero m] in
theorem gam_ne_zero_of_mem_acommSet {c : Content F m} (hc : c ∈ acommSet) :
    gam c.omega ≠ 0 := (Finset.mem_filter.mp hc).2

/-! ## The edges the rules live on -/

theorem adj_self' (t : Ty) : adj t t = true := adj_self t

theorem adj_point_aline (W : Bas) : adj (.point W) (.aline W) = true := by cases W <;> rfl

theorem adj_point_dline (W : Bas) : adj (.point W) (.dline W) = true := by cases W <;> rfl

theorem adj_point_pauli (W : Bas) : adj (.point W) (.pauli W) = true := by cases W <;> rfl

theorem adj_point_pairB (W : Bas) : adj (.point W) (.pairB W) = true := by cases W <;> rfl

theorem adj_pairB_pair (W : Bas) : adj (.pairB W) .pair = true := by cases W <;> rfl

theorem adj_pointX_var0 : adj (.point .X) (.var (v 0)) = true := by decide

theorem adj_pointZ_var4 : adj (.point .Z) (.var (v 4)) = true := by decide

/-! ## The items

Each is `agree_subtest_le` at a named edge with the two readings the rule compares. -/

section Items

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- The three components of an acceptance. -/
theorem of_accepts {x y : Question F m} {a b : Answer F m d}
    (h : accepts hm x y a b = true) :
    x.fmtOk a = true ∧ y.fmtOk b = true ∧ subtests hm x y a b = true := by
  rw [accepts, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Item 1, the consistency check.** At equal types the two players' measurements are
cross-party consistent at error `172 ε`. -/
theorem item_consistency (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (t : Ty) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : Answer F m d,
          xSqNorm ψ ((((MA (c.question hm t)).map (fun a => a)).mats o).val)
            ((((MB (c.question hm t)).map (fun a => a)).mats o).val)
      ≤ 172 * ε :=
  agree_subtest_le hψ hfail (adj_self t) univ (fun _ a => a) (fun _ b => b)
    fun c _ a b h => by
      have hs := (of_accepts h).2.2
      rw [subtests, if_pos rfl] at hs
      exact of_decide_eq_true hs


/-! ### Inverting the format check

`accepts` rejects before any rule runs unless both answers have the shape their question's type
prescribes, so each rule may be read on one pair of constructors only. These are the inversions,
one per answer format; they are what keeps the proofs of the items below to a single branch
instead of the forty-nine a blind case split would produce. -/

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_val_of_fmtOk {W : Bas} {y : Point F m} {a : Answer F m d}
    (h : (Question.point W y).fmtOk a = true) : ∃ a', a = .val a' := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_apoly_of_fmtOk {W : Bas} {u₀ : Point F m} {s : F} {a : Answer F m d}
    (h : (Question.aline W u₀ s).fmtOk a = true) : ∃ p, a = .apoly p := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_dpoly_of_fmtOk {W : Bas} {u₀ : Point F m} {s : F} {w : Point F m} {a : Answer F m d}
    (h : (Question.dline W u₀ s w).fmtOk a = true) : ∃ p, a = .dpoly p := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_pauliAns_of_fmtOk {W : Bas} {a : Answer F m d}
    (h : (Question.pauli W : Question F m).fmtOk a = true) : ∃ h', a = .pauliAns h' := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_bit_of_fmtOk_pairB {W : Bas} {ω : Omega F m} {a : Answer F m d}
    (h : (Question.pairB W ω).fmtOk a = true) : ∃ b, a = .bit b := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_bitPair_of_fmtOk {ω : Omega F m} {a : Answer F m d}
    (h : (Question.pair ω).fmtOk a = true) : ∃ β, a = .bitPair β := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_bit_of_fmtOk_var {j : Fin layout.s} {ω : Omega F m} {a : Answer F m d}
    (h : (Question.var j ω).fmtOk a = true) : ∃ b, a = .bit b := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_bitTriple_of_fmtOk {i : Fin layout.r} {ω : Omega F m} {a : Answer F m d}
    (h : (Question.con i ω).fmtOk a = true) : ∃ α, a = .bitTriple α := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The parameter agreement a line-against-point acceptance yields. -/
theorem eval_eq_of_lowDeg {n : ℕ} {u₀ w y : Point F m} {p : LinePoly F n} {a : F}
    (h : lowDeg u₀ w y p a = true) : p.eval (MIPRE.LIDT.CL.lineParam u₀ w y) = a :=
  (of_decide_eq_true h).2 0

/-- **Item 2a, the low-degree check against an axis-parallel line.** The line polynomial,
evaluated at the parameter of the sampled point, agrees with the point answer, at error
`172 ε`. This is the seeded CL decider's own check (`lowDeg_eq_cl`). -/
theorem item_lowDeg_aline (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : F,
          xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
            ((((MB (c.question hm (.aline W))).map (rdALineAt hm W c)).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail (adj_point_aline W) univ (fun _ => rdVal) (rdALineAt hm W)
    fun c _ a b h => ?_
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨p, rfl⟩ := eq_apoly_of_fmtOk hfb
  have hs' : lowDeg (MIPRE.LIDT.CL.rep (dirOf hm c) (c.pt W)) (dirOf hm c) (c.pt W) p a'
      = true := by
    simpa [subtests, Question.ty, Content.question, pairTest, dirOf] using hs
  exact (eval_eq_of_lowDeg hs').symm

/-- **Item 2b, the low-degree check against a diagonal line.** -/
theorem item_lowDeg_dline (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : F,
          xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
            ((((MB (c.question hm (.dline W))).map (rdDLineAt hm W c)).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail (adj_point_dline W) univ (fun _ => rdVal) (rdDLineAt hm W)
    fun c _ a b h => ?_
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨p, rfl⟩ := eq_dpoly_of_fmtOk hfb
  have hs' : lowDeg
      (MIPRE.LIDT.CL.rep (MIPRE.LIDT.CL.zeroBelow (MIPRE.LIDT.CL.chi hm c.s) c.v) (c.pt W))
      (MIPRE.LIDT.CL.zeroBelow (MIPRE.LIDT.CL.chi hm c.s) c.v) (c.pt W) p a' = true := by
    simpa [subtests, Question.ty, Content.question, pairTest] using hs
  exact (eval_eq_of_lowDeg hs').symm

/-- **Item 3, Pauli basis consistency.** The low-degree encoding of the full `(Pauli, W)`
outcome, evaluated at the sampled point, agrees with the point answer. -/
theorem item_pauli_consistency (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : F,
          xSqNorm ψ ((((MA (c.question hm (.point W))).map rdVal).mats o).val)
            ((((MB (c.question hm (.pauli W))).map (rdPauli (c.pt W))).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail (adj_point_pauli W) univ (fun _ => rdVal)
    (fun c => rdPauli (c.pt W)) fun c _ a b h => ?_
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨h', rfl⟩ := eq_pauliAns_of_fmtOk hfb
  have hs' : MvPolynomial.eval (c.pt W) (MIPRE.LowDegree.ldEnc h') = a' := by
    simpa [subtests, Question.ty, Content.question, pairTest] using hs
  exact hs'.symm

/-- **Item 4, the commutation check**, on the commuting tuples: the `(Pair, W)` bit agrees with
the `W`-component of the `Pair` answer. On an anticommuting tuple the rule checks nothing, by
design, which is why the average is restricted. -/
theorem item_commutation (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          xSqNorm ψ ((((MA (c.question hm (.pairB W))).map rdBit).mats o).val)
            ((((MB (c.question hm .pair)).map (rdBitPair W)).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail (adj_pairB_pair W) commSet (fun _ => rdBit)
    (fun _ => rdBitPair W) fun c hc a b h => ?_
  have hγ := gam_eq_zero_of_mem_commSet hc
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_pairB hfa
  obtain ⟨β, rfl⟩ := eq_bitPair_of_fmtOk hfb
  have hs' : b' = β W := by
    simpa [subtests, Question.ty, Content.question, pairTest, hγ] using hs
  exact hs'

/-- The trace probe of a point answer against the `W`-side qubit basis element of the
content. -/
def rdProbeAt (W : Bas) (c : Content F m) : Answer F m d → ZMod 2 :=
  rdProbe (c.omega.r W)

/-- **Item 5, commutation consistency**, on the commuting tuples: the trace probe of the point
answer agrees with the `(Pair, W)` bit. -/
theorem item_commutation_consistency (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c ∈ commSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          xSqNorm ψ ((((MA (c.question hm (.point W))).map (rdProbeAt W c)).mats o).val)
            ((((MB (c.question hm (.pairB W))).map rdBit).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail (adj_point_pairB W) commSet (rdProbeAt W)
    (fun _ => rdBit) fun c hc a b h => ?_
  have hγ := gam_eq_zero_of_mem_commSet hc
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_pairB hfb
  have hs' : prb a' (c.omega.r W) = b' := by
    simpa [subtests, Question.ty, Content.question, pairTest, hγ] using hs
  exact hs'

/-- **Item 7 for `X`, Magic Square consistency**, on the anticommuting tuples: the trace probe
of the `(Point, X)` answer agrees with the `Variable_1` bit --- `var 0` at this file's
`0`-indexing. -/
theorem item_ms_consistency_X (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          xSqNorm ψ ((((MA (c.question hm (.point .X))).map (rdProbeAt .X c)).mats o).val)
            ((((MB (c.question hm (.var (v 0)))).map rdBit).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail adj_pointX_var0 acommSet (rdProbeAt .X)
    (fun _ => rdBit) fun c hc a b h => ?_
  have hγ := gam_ne_zero_of_mem_acommSet hc
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_var hfb
  have hs' : prb a' c.omega.rX = b' := by
    simpa [subtests, Question.ty, Content.question, pairTest, hγ] using hs
  exact hs'

/-- **Item 7 for `Z`.** -/
theorem item_ms_consistency_Z (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ o : ZMod 2,
          xSqNorm ψ ((((MA (c.question hm (.point .Z))).map (rdProbeAt .Z c)).mats o).val)
            ((((MB (c.question hm (.var (v 4)))).map rdBit).mats o).val)
      ≤ 172 * ε := by
  refine agree_subtest_le hψ hfail adj_pointZ_var4 acommSet (rdProbeAt .Z)
    (fun _ => rdBit) fun c hc a b h => ?_
  have hγ := gam_ne_zero_of_mem_acommSet hc
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_var hfb
  have hs' : prb a' c.omega.rZ = b' := by
    simpa [subtests, Question.ty, Content.question, pairTest, hγ] using hs
  exact hs'

end Items

end MIPRE.QLD

end
