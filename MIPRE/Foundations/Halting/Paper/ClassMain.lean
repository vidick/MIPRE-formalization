/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Paper.ClassVerifier
public import MIPRE.Foundations.Halting.Paper.Count
public import MIPRE.Foundations.GameRestrict
public import MIPRE.Foundations.ClassMIPStarTab
public import MIPRE.Foundations.Cost.Growth

@[expose] public section

/-!
# `RE ⊆ MIP*_{1,1/2}(2,1)`, and `MIP*_{1,1/2}(2,1) = RE`

The class verifier of `Paper/ClassVerifier.lean` is a `PolyVerifier` for the polynomial
`classP` chosen above its four cost bounds (`sampB`, `dimB`, `decB`, `cutB`, each polynomially
bounded here), and:

* it is **efficient** on every input (`classV_efficient`): the sampler's cost and the decider's
  are within the polynomial, the questions have the compressed sampler's dimension at the fixed
  level, and the decider rejects overlong messages — the answers by its cutoff, the questions
  by the wrapper's length check;
* its **game** on `z` has the value of `𝒱^halt (R z) λ(z)` at the fixed level `C` with the
  answers cut at `cutz z` (`classV_value`): the uniform seed of length `B ≥ s(C)` pushes
  forward, through its first `s(C)` bits, to the compressed sampler's distribution
  (`length_filter_take`, `length_filter_bitStrsOfLen`), so the game is the restriction of the
  verifier's to the questions of length `s(C)` (`quantumValue_restrictQuestions`) with the
  answers extended by always-rejected ones (`quantumValue_extendAnswers`);
* that value is `1` on `L` and at most `1/2` off it (`thm:halting` at the fixed level,
  `halting_paper`): the cutoff is at least the compressor's answer bound, and below it the
  decider of `𝒱^halt` rejects overlong answers whenever `M` does not halt.

Hence `re_subset_mipstar_of` and `mipstar_eq_re_of` (blueprint `thm:mipstar-eq-re`,
for the paper's class), given a compressor and the two universal machines; the unconditional
forms are in `MIPRE/Background/Pipeline.lean` and `MIPRE/MainTheorem.lean`.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Cost.PolyTimeFun CL Verifier

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)

/-! ## The bounds are polynomial -/

theorem polyBounded_lamB : PolyBounded (lamB Λ₀ R) :=
  (PolyBounded.const Λ₀).add
    ((PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 1)).const_mul 4)

theorem polyBounded_dimB : PolyBounded (dimB G Λ₀ R) :=
  PolyBounded.eval _ ((PolyBounded.const (C G)).add (polyBounded_lamB Λ₀ R))

theorem polyBounded_T1B : PolyBounded (T1B G Λ₀ R) :=
  PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 3)

/-- The shape of the three universal calls' bounds. -/
theorem polyBounded_call {T : ℕ → ℕ} (hT : PolyBounded T) :
    PolyBounded fun m => 2 * T m + (4 * dimB G Λ₀ R m + 1) +
      U.bound.eval (2 * T m + dimB G Λ₀ R m * (T m + 1) ^ G.deg) + 8 :=
  have hd := polyBounded_dimB G Λ₀ R
  (((hT.const_mul 2).add ((hd.const_mul 4).add_const 1)).add
    (PolyBounded.eval _ ((hT.const_mul 2).add (hd.mul ((hT.add_const 1).pow G.deg))))).add_const 8

theorem polyBounded_R1B : PolyBounded (R1B G U Λ₀ R) :=
  polyBounded_call G U Λ₀ R (polyBounded_T1B G Λ₀ R)

theorem polyBounded_unB_dimB : PolyBounded fun m => unB (dimB G Λ₀ R m) :=
  have hd := polyBounded_dimB G Λ₀ R
  (hd.add_const 2).mul ((((hd.add_const 1).mul ((hd.const_mul 4).add_const 14)).add
    (((hd.const_mul 4).add_const 1).const_mul 7)).add ((hd.const_mul 8).add_const 90))

theorem polyBounded_UnB : PolyBounded (UnB G U Λ₀ R) :=
  (((polyBounded_R1B G U Λ₀ R).add (((polyBounded_dimB G Λ₀ R).const_mul 4).add_const 1)).add
    (polyBounded_unB_dimB G Λ₀ R)).add_const 5

theorem polyBounded_T2B : PolyBounded (T2B G U Λ₀ R) :=
  PolyBounded.eval _ (polyBounded_UnB G U Λ₀ R)

theorem polyBounded_R2B : PolyBounded (R2B G U Λ₀ R) :=
  polyBounded_call G U Λ₀ R (polyBounded_T2B G U Λ₀ R)

theorem polyBounded_T3B : PolyBounded (T3B G U Λ₀ R) :=
  PolyBounded.eval _ (polyBounded_R2B G U Λ₀ R)

theorem polyBounded_R3B : PolyBounded (R3B G U Λ₀ R) :=
  polyBounded_call G U Λ₀ R (polyBounded_T3B G U Λ₀ R)

theorem polyBounded_sampB : PolyBounded (sampB G U Λ₀ R) :=
  ((((((((polyBounded_T1B G Λ₀ R).add (polyBounded_R1B G U Λ₀ R)).add
    (polyBounded_UnB G U Λ₀ R)).add (polyBounded_T2B G U Λ₀ R)).add
    (polyBounded_R2B G U Λ₀ R)).add (polyBounded_T3B G U Λ₀ R)).const_mul 2).add
    (polyBounded_R3B G U Λ₀ R)).add_const 18

theorem polyBounded_TDB : PolyBounded (TDB G U UT Λ₀ K R) :=
  PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 9)

theorem polyBounded_zB : PolyBounded (zB G Λ₀ R) :=
  (((PolyBounded.eval _ ((PolyBounded.id.const_mul 4).add_const 1)).add
    (PolyBounded.const (C G))).add (polyBounded_lamB Λ₀ R)).add
    ((PolyBounded.id.const_mul 4).add_const 7)

theorem polyBounded_decB : PolyBounded (decB G U UT Λ₀ K R) :=
  have hTD := polyBounded_TDB G U UT Λ₀ K R
  ((hTD.const_mul 3).add (PolyBounded.eval _ (hTD.add
    (((polyBounded_WZ G U UT (semL G U)).comp (polyBounded_zB G Λ₀ R)).add_const
      constCost)))).add_const 6

/-- The cutoff, in the input length. -/
noncomputable def cutB (m : ℕ) : ℕ :=
  2 ^ (K + G.bound.natDegree) * (2 * lamB Λ₀ R m + 1) ^ (4 * G.bound.natDegree)

theorem polyBounded_cutB : PolyBounded (cutB G Λ₀ K R) :=
  (PolyBounded.const _).mul ((((polyBounded_lamB Λ₀ R).const_mul 2).add_const 1).pow _)

theorem cutz_le (z : BitStr) : cutz G Λ₀ K R z ≤ cutB G Λ₀ K R z.length := by
  unfold cutz cutB
  set D := G.bound.natDegree
  set lam := lamz Λ₀ R z
  have h1 : esize lam ≤ 4 * Nat.size lam + 1 := esize_nat_le _
  have h2 : 2 ^ Nat.size lam ≤ 2 * lam + 1 := two_pow_size_le _
  have h3 : lam ≤ lamB Λ₀ R z.length := lamz_le Λ₀ R z z.length le_rfl
  calc 2 ^ (K + D * esize lam) ≤ 2 ^ (K + D * (4 * Nat.size lam + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left (Nat.mul_le_mul_left D h1) K)
    _ = 2 ^ (K + D) * (2 ^ Nat.size lam) ^ (4 * D) := by
        rw [show K + D * (4 * Nat.size lam + 1) = (K + D) + Nat.size lam * (4 * D) by ring,
          pow_add, pow_mul]
    _ ≤ 2 ^ (K + D) * (2 * lam + 1) ^ (4 * D) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ ≤ 2 ^ (K + D) * (2 * lamB Λ₀ R z.length + 1) ^ (4 * D) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-! ## The class verifier -/

/-- **The polynomial of the class verifier**: above the sampler's cost, the dimension, the
decider's cost and the cutoff. -/
noncomputable def classP : Polynomial ℕ :=
  (polyBounded_sampB G U Λ₀ R).poly + (polyBounded_dimB G Λ₀ R).poly +
    (polyBounded_decB G U UT Λ₀ K R).poly + (polyBounded_cutB G Λ₀ K R).poly

theorem sampB_le (m : ℕ) : sampB G U Λ₀ R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_sampB G U Λ₀ R).le_poly_eval m; omega

theorem dimB_le (m : ℕ) : dimB G Λ₀ R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_dimB G Λ₀ R).le_poly_eval m; omega

theorem decB_le (m : ℕ) : decB G U UT Λ₀ K R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_decB G U UT Λ₀ K R).le_poly_eval m; omega

theorem cutB_le (m : ℕ) : cutB G Λ₀ K R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_cutB G Λ₀ K R).le_poly_eval m; omega

/-- **The class verifier** of the language reduced to halting by `R`. -/
noncomputable def classV : PolyVerifier where
  sampler := sampProg G U Λ₀ R
  sampler_closed := sampProg_wellScoped G U Λ₀ R
  decider := decProg G U UT Λ₀ K R
  decider_closed := decProg_wellScoped G U UT Λ₀ K R
  bound := classP G U UT Λ₀ K R

theorem classV_B (z : BitStr) :
    (classV G U UT Λ₀ K R).B z = (classP G U UT Λ₀ K R).eval z.length :=
  rfl

theorem dimz_le_B (z : BitStr) : dimz G Λ₀ R z ≤ (classV G U UT Λ₀ K R).B z :=
  (dimz_le G Λ₀ R z z.length le_rfl).trans (dimB_le G U UT Λ₀ K R _)

theorem cutz_le_B (z : BitStr) : cutz G Λ₀ K R z ≤ (classV G U UT Λ₀ K R).B z :=
  (cutz_le G Λ₀ K R z).trans (cutB_le G U UT Λ₀ K R _)

/-- The verifier `𝒱^halt (R z) λ(z)` the class verifier plays on `z`. -/
noncomputable abbrev Vz (z : BitStr) : Verifier 7 := Vpaper G U UT (R z) (lamz Λ₀ R z)

theorem qOf_length (w : Player) (z r : BitStr) : (qOf G Λ₀ R w z r).length = dimz G Λ₀ R z :=
  length_toBits _

/-- **The class verifier is efficient on every input.** -/
theorem classV_efficient (z : BitStr) : (classV G U UT Λ₀ K R).Efficient z := by
  have hdim := dimz_le_B G U UT Λ₀ K R z
  refine ⟨fun r hr => ?_, fun x y a b => ?_, fun x y a b h => ?_⟩
  · obtain ⟨t, ht, hrun⟩ := sampProg_runs G U Λ₀ R z r (by rw [hr]; exact hdim)
    refine ⟨_, _, t, ht.trans (sampB_le G U UT Λ₀ K R _), ?_, ?_, hrun⟩
    · rw [qOf_length]; exact hdim
    · rw [qOf_length]; exact hdim
  · obtain ⟨r, t, ht, hrun⟩ := decProg_runs G U UT Λ₀ K R z x y a b
    exact ⟨r, t, ht.trans (decB_le G U UT Λ₀ K R _), hrun⟩
  · intro hacc
    obtain ⟨ha, hb, hV⟩ := (decProg_accepts G U UT Λ₀ K R z x y a b).1 hacc
    have hcut := cutz_le_B G U UT Λ₀ K R z
    rw [Vpaper, Vhalt, Verifier.ofSamplerDecider_accepts] at hV
    obtain ⟨hx, hy, -⟩ := hV
    have e : dimz G Λ₀ R z = (G.sampler (lamz Λ₀ R z)).dim (C G) := rfl
    rcases h with h | h | h | h <;> omega

/-! ## The value of the game -/

/-- The question pair of a seed of the right length. -/
theorem classV_questions (z r : BitStr) (hr : r.length = (classV G U UT Λ₀ K R).B z) :
    (classV G U UT Λ₀ K R).questions z r =
      (⟨qOf G Λ₀ R .alice z r, by rw [qOf_length]; exact dimz_le_B G U UT Λ₀ K R z⟩,
        ⟨qOf G Λ₀ R .bob z r, by rw [qOf_length]; exact dimz_le_B G U UT Λ₀ K R z⟩) := by
  obtain ⟨x, y, t, -, hrun, hx, hy⟩ :=
    (classV G U UT Λ₀ K R).questions_eq_of_efficient (classV_efficient G U UT Λ₀ K R z) hr
  obtain ⟨t', -, hrun'⟩ := sampProg_runs G U Λ₀ R z r
    (by rw [hr]; exact dimz_le_B G U UT Λ₀ K R z)
  obtain ⟨he, -⟩ := Eval.deterministic hrun hrun'
  have he' := encode_injective he
  simp only [Prod.mk.injEq] at he'
  exact Prod.ext (Subtype.ext (hx.trans he'.1)) (Subtype.ext (hy.trans he'.2))

/-- The embedding of the compressed sampler's questions into the strings of length at most
`B z`. -/
noncomputable def qEmb (z : BitStr) :
    (Vz G U UT Λ₀ R z).Questions (C G) ↪ Answers ((classV G U UT Λ₀ K R).B z) where
  toFun v := ⟨toBits v, by rw [length_toBits]; exact dimz_le_B G U UT Λ₀ K R z⟩
  inj' v w h := by
    have := congrArg Subtype.val h
    simp only at this
    rw [← ofBits_toBits v, ← ofBits_toBits w, this]

theorem qEmb_val (z : BitStr) (v : (Vz G U UT Λ₀ R z).Questions (C G)) :
    (qEmb G U UT Λ₀ K R z v).1 = toBits v := rfl

/-- The number of seeds producing a given question pair: a count over `𝔽₂^{s(C)}` times
`2 ^ (B - s(C))`. -/
theorem seedCount_eq (z : BitStr) (x y : (Vz G U UT Λ₀ R z).Questions (C G)) :
    (classV G U UT Λ₀ K R).seedCount z (qEmb G U UT Λ₀ K R z x) (qEmb G U UT Λ₀ K R z y) =
      (Finset.univ.filter fun v : (Vz G U UT Λ₀ R z).Questions (C G) =>
        ((Vz G U UT Λ₀ R z).sampler.cl (C G) .alice).eval v = x ∧
          ((Vz G U UT Λ₀ R z).sampler.cl (C G) .bob).eval v = y).card *
        2 ^ ((classV G U UT Λ₀ K R).B z - dimz G Λ₀ R z) := by
  classical
  set d := dimz G Λ₀ R z with hd
  set B := (classV G U UT Λ₀ K R).B z with hB
  have hdB : d ≤ B := dimz_le_B G U UT Λ₀ K R z
  set L := ((Vz G U UT Λ₀ R z).sampler.cl (C G) .alice).eval
  set Rb := ((Vz G U UT Λ₀ R z).sampler.cl (C G) .bob).eval
  -- the seeds whose questions are `(x, y)` are those whose prefix maps to `(x, y)`
  have key : ∀ v w : (Vz G U UT Λ₀ R z).Questions (C G), toBits v = toBits w ↔ v = w :=
    fun v w => ⟨fun h => by rw [← ofBits_toBits v, h, ofBits_toBits], fun h => by rw [h]⟩
  have h1 : (classV G U UT Λ₀ K R).seedCount z (qEmb G U UT Λ₀ K R z x)
      (qEmb G U UT Λ₀ K R z y)
      = ((Data.bitStrsOfLen B).filter fun r =>
          decide (L (ofBits d (r.take d)) = x ∧ Rb (ofBits d (r.take d)) = y)).length := by
    unfold PolyVerifier.seedCount
    apply congrArg List.length
    refine List.filter_congr fun r hr => ?_
    have hr' : r.length = B := (Data.mem_bitStrsOfLen _ _).1 hr
    rw [classV_questions G U UT Λ₀ K R z r hr', decide_eq_decide, Prod.ext_iff]
    refine (and_congr Subtype.ext_iff Subtype.ext_iff).trans ?_
    show (toBits (L (ofBits d (r.take d))) = toBits x ∧
        toBits (Rb (ofBits d (r.take d))) = toBits y) ↔ _
    rw [key, key]
  rw [h1]
  have h2 := Data.length_filter_take (fun s => decide (L (ofBits d s) = x ∧ Rb (ofBits d s) = y))
    d (B - d)
  rw [Nat.add_sub_cancel' hdB] at h2
  rw [h2, show ((Data.bitStrsOfLen d).filter fun s =>
      decide (L (ofBits d s) = x ∧ Rb (ofBits d s) = y)).length =
      (Finset.univ.filter fun v => decide (L v = x ∧ Rb v = y) = true).card from
      length_filter_bitStrsOfLen (s := d) (fun v => decide (L v = x ∧ Rb v = y))]
  congr 1

/-- The distribution of the class verifier's game, on the embedded questions, is the
compressed sampler's. -/
theorem classV_game_μ (z : BitStr) (x y : (Vz G U UT Λ₀ R z).Questions (C G)) :
    ((classV G U UT Λ₀ K R).game z).μ (qEmb G U UT Λ₀ K R z x) (qEmb G U UT Λ₀ K R z y) =
      ((Vz G U UT Λ₀ R z).game (C G) (cutz G Λ₀ K R z)).μ x y := by
  classical
  rw [PolyVerifier.game_μ, seedCount_eq]
  show _ = (Vz G U UT Λ₀ R z).sampler.dist (C G) x y
  rw [Sampler.dist, clDist]
  have hdB := dimz_le_B G U UT Λ₀ K R z
  have hcard : (Fintype.card ((Vz G U UT Λ₀ R z).Questions (C G)) : ℝ) =
      2 ^ dimz G Λ₀ R z := by
    show (Fintype.card (Fin (dimz G Λ₀ R z) → ZMod 2) : ℝ) = _
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    rfl
  have h2B : (2 : ℝ) ^ (classV G U UT Λ₀ K R).B z =
      2 ^ dimz G Λ₀ R z * 2 ^ ((classV G U UT Λ₀ K R).B z - dimz G Λ₀ R z) := by
    rw [← pow_add, Nat.add_sub_cancel' hdB]
  rw [hcard, h2B]
  push_cast
  field_simp

/-- The distribution of the class verifier's game is supported on the embedded questions. -/
theorem classV_game_support (z : BitStr) (x' y' : Answers ((classV G U UT Λ₀ K R).B z))
    (h : ((classV G U UT Λ₀ K R).game z).μ x' y' ≠ 0) :
    (∃ x, qEmb G U UT Λ₀ K R z x = x') ∧ ∃ y, qEmb G U UT Λ₀ K R z y = y' := by
  classical
  rw [PolyVerifier.game_μ] at h
  have hc : (classV G U UT Λ₀ K R).seedCount z x' y' ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  unfold PolyVerifier.seedCount at hc
  have hne : ((Data.bitStrsOfLen ((classV G U UT Λ₀ K R).B z)).filter fun r =>
      decide ((classV G U UT Λ₀ K R).questions z r = (x', y'))) ≠ [] :=
    fun h0 => hc (by rw [h0]; rfl)
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hr, hq⟩ := List.mem_filter.1 hr
  have hq := of_decide_eq_true hq
  have hr' : r.length = (classV G U UT Λ₀ K R).B z := (Data.mem_bitStrsOfLen _ _).1 hr
  rw [classV_questions G U UT Λ₀ K R z r hr'] at hq
  obtain ⟨hq1, hq2⟩ := Prod.ext_iff.1 hq
  exact ⟨⟨((Vz G U UT Λ₀ R z).sampler.cl (C G) .alice).eval
      (ofBits (dimz G Λ₀ R z) (r.take (dimz G Λ₀ R z))), hq1⟩,
    ⟨((Vz G U UT Λ₀ R z).sampler.cl (C G) .bob).eval
      (ofBits (dimz G Λ₀ R z) (r.take (dimz G Λ₀ R z))), hq2⟩⟩

/-- **The value of the class verifier's game** is that of `𝒱^halt (R z) λ(z)` at the fixed
level `C`, with the answers cut at `cutz z`. -/
theorem classV_value (z : BitStr) :
    quantumValue ((classV G U UT Λ₀ K R).game z) =
      (Vz G U UT Λ₀ R z).valStar (C G) (cutz G Λ₀ K R z) := by
  classical
  set V := classV G U UT Λ₀ K R with hV
  set W := Vz G U UT Λ₀ R z with hW
  set cut := cutz G Λ₀ K R z with hcut_def
  have hcut : cut ≤ V.B z := cutz_le_B G U UT Λ₀ K R z
  set ex := qEmb G U UT Λ₀ K R z with hex
  have hμ : ∀ x y : W.Questions (C G), (V.game z).μ (ex x) (ex y) = (W.game (C G) cut).μ x y :=
    classV_game_μ G U UT Λ₀ K R z
  have hsum : ∑ x, ∑ y, (V.game z).μ (ex x) (ex y) = 1 := by
    simp_rw [hμ]; exact (W.game (C G) cut).μ_sum_one
  set Gmid := (V.game z).restrict ex ex hsum with hGmid
  have h1 : quantumValue Gmid = quantumValue (V.game z) :=
    quantumValue_restrictQuestions (V.game z) Gmid ex ex (fun _ _ => rfl)
      (classV_game_support G U UT Λ₀ K R z) (fun _ _ _ _ => rfl)
  -- acceptance on the embedded questions
  have hacc : ∀ (x y : W.Questions (C G)) (a b : BitStr),
      V.Accepts z (toBits x) (toBits y) a b ↔
        a.length ≤ cut ∧ b.length ≤ cut ∧
          W.decider.Accepts (C G) (toBits x) (toBits y) a b :=
    fun x y a b => decProg_accepts G U UT Λ₀ K R z (toBits x) (toBits y) a b
  have h2 : quantumValue Gmid = quantumValue (W.game (C G) cut) := by
    refine quantumValue_extendAnswers (W.game (C G) cut) Gmid (Answers.castLE hcut)
      (Answers.castLE hcut) hμ ?_ ?_
    · intro x y a b
      show decide (V.Accepts z (toBits x) (toBits y) a.1 b.1) =
        decide (W.decider.Accepts (C G) (toBits x) (toBits y) a.1 b.1)
      simp only [decide_eq_decide]
      rw [hacc]
      exact ⟨fun h => h.2.2, fun h => ⟨a.2, b.2, h⟩⟩
    · intro x y a' b' h
      have h' : V.Accepts z (toBits x) (toBits y) a'.1 b'.1 := of_decide_eq_true h
      obtain ⟨ha, hb, -⟩ := (hacc x y a'.1 b'.1).1 h'
      exact ⟨⟨⟨a'.1, ha⟩, Subtype.ext rfl⟩, ⟨⟨b'.1, hb⟩, Subtype.ext rfl⟩⟩
  rw [Verifier.valStar, ← h2, h1]

/-! ## `RE ⊆ MIP*`, and `MIP* = RE` -/

/-- **The values on and off the language**, for the parameter `Λ₀` of `lem:lambda` and a
cutoff above the compressor's bound. -/
theorem classV_values
    (hK : ∀ lam, G.bound.eval (C G + lam) ≤ 2 ^ (K + G.bound.natDegree * esize lam))
    (z : BitStr) :
    (Halts (R z) .nil →
      quantumValue ((classV G U UT (lamThreshold G U UT) K R).game z) = 1) ∧
    (¬ Halts (R z) .nil →
      quantumValue ((classV G U UT (lamThreshold G U UT) K R).game z) ≤ 1 / 2) := by
  rw [classV_value]
  set W := Vz G U UT (lamThreshold G U UT) R z
  have hT : G.bound.eval (C G + lamz (lamThreshold G U UT) R z) ≤
      cutz G (lamThreshold G U UT) K R z := hK _
  obtain ⟨h1, h2⟩ := halting_paper G U UT (R z) (lamz (lamThreshold G U UT) R z) le_rfl
  constructor
  · intro hM
    exact W.valStar_eq_one_of_hasPerfectPCC (W.hasPerfectPCC_of_le hT (h1 hM))
  · intro hM
    have hrej : W.RejectsLong (C G) (G.bound.eval (C G + lamz (lamThreshold G U UT) R z)) :=
      rejectsLong_of_not_branch1 G U UT (R z) _ (not_branch1_of_not_halts hM (C G))
    rw [W.valStar_eq_of_rejects hT hrej]
    exact h2 hM

include G U UT in
/-- **`RE ⊆ MIP*_{1,1/2}(2,1)`**, given a compressor and the two universal machines. -/
theorem re_subset_mipstar_of {L : Set BitStr} (hL : IsRE L) : MIPStar L := by
  obtain ⟨R, -, hR⟩ := Cost.exists_polyTime_reduction (p := (· ∈ L)) hL
  obtain ⟨K, hK⟩ := exists_cut_ge G
  refine ⟨classV G U UT (lamThreshold G U UT) K R,
    classV_efficient G U UT (lamThreshold G U UT) K R, fun z => ?_⟩
  obtain ⟨h1, h2⟩ := classV_values G U UT K R hK z
  exact ⟨fun hz => h1 ((hR z).2 hz), fun hz => h2 fun h => hz ((hR z).1 h)⟩

include G U UT in
/-- **`MIP*_{1,1/2}(2,1) = RE`** (blueprint `thm:mipstar-eq-re`, the paper's class), given a
compressor and the two universal machines. -/
theorem mipstar_eq_re_of : MIPStar = IsRE :=
  funext fun _ => propext ⟨MIPStar.isRE, re_subset_mipstar_of G U UT⟩

end MIPRE.Halting

end
