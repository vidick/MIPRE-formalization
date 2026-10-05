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
  (`SamplerFamily.game_μ_qEmb`, `SamplerFamily.game_support`, in `Paper/ClassSampler.lean`), so
  the game is the restriction of the verifier's to the questions of length `s(C)`
  (`quantumValue_restrictQuestions`) with the answers extended by always-rejected ones
  (`quantumValue_extendAnswers`);
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

theorem polyBounded_dimB : PolyBounded (dimB G Λ₀ R) :=
  G.samplerFamily.polyBounded_dimB (C G) Λ₀ R

theorem polyBounded_sampB : PolyBounded (sampB G U Λ₀ R) :=
  G.samplerFamily.polyBounded_sampB (C G) U Λ₀ R

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

theorem dimz_le_B (z : BitStr) : dimz G Λ₀ R z ≤ (classV G U UT Λ₀ K R).B z :=
  (dimz_le G Λ₀ R z z.length le_rfl).trans (dimB_le G U UT Λ₀ K R _)

theorem cutz_le_B (z : BitStr) : cutz G Λ₀ K R z ≤ (classV G U UT Λ₀ K R).B z :=
  (cutz_le G Λ₀ K R z).trans (cutB_le G U UT Λ₀ K R _)

/-- The verifier `𝒱^halt (R z) λ(z)` the class verifier plays on `z`. -/
noncomputable abbrev Vz (z : BitStr) : Verifier 7 := Vpaper G U UT (R z) (lamz Λ₀ R z)

/-- The class verifier samples the compressed samplers at the fixed level. -/
theorem classV_samples : G.samplerFamily.Samples (C G) Λ₀ R (classV G U UT Λ₀ K R) :=
  G.samplerFamily.samples_of_runs (C G) Λ₀ R (dimB_le G U UT Λ₀ K R) (sampProg_runs G U Λ₀ R)
    rfl (sampB_le G U UT Λ₀ K R)

/-- **The class verifier is efficient on every input.** -/
theorem classV_efficient (z : BitStr) : (classV G U UT Λ₀ K R).Efficient z := by
  refine ⟨(classV_samples G U UT Λ₀ K R).samplerRuns (dimB_le G U UT Λ₀ K R) z,
    fun x y a b => ?_, fun x y a b h => ?_⟩
  · obtain ⟨r, t, ht, hrun⟩ := decProg_runs G U UT Λ₀ K R z x y a b
    exact ⟨r, t, ht.trans (decB_le G U UT Λ₀ K R _), hrun⟩
  · intro hacc
    obtain ⟨ha, hb, hV⟩ := (decProg_accepts G U UT Λ₀ K R z x y a b).1 hacc
    have hcut := cutz_le_B G U UT Λ₀ K R z
    have hdim := dimz_le_B G U UT Λ₀ K R z
    rw [Vpaper, Vhalt, Verifier.ofSamplerDecider_accepts] at hV
    obtain ⟨hx, hy, -⟩ := hV
    have e : dimz G Λ₀ R z = (G.sampler (lamz Λ₀ R z)).dim (C G) := rfl
    rcases h with h | h | h | h <;> omega

/-! ## The value of the game -/

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
  have hS := classV_samples G U UT Λ₀ K R
  have hdim : ∀ m, dimB G Λ₀ R m ≤ V.bound.eval m := dimB_le G U UT Λ₀ K R
  set ex : W.Questions (C G) ↪ Answers (V.B z) := G.samplerFamily.qEmb (C G) Λ₀ R hdim z
    with hex
  have hμ : ∀ x y : W.Questions (C G), (V.game z).μ (ex x) (ex y) = (W.game (C G) cut).μ x y :=
    G.samplerFamily.game_μ_qEmb (C G) Λ₀ R hS hdim z
  have hsum : ∑ x, ∑ y, (V.game z).μ (ex x) (ex y) = 1 := by
    simp_rw [hμ]; exact (W.game (C G) cut).μ_sum_one
  set Gmid := (V.game z).restrict ex ex hsum with hGmid
  have h1 : quantumValue Gmid = quantumValue (V.game z) :=
    quantumValue_restrictQuestions (V.game z) Gmid ex ex (fun _ _ => rfl)
      (G.samplerFamily.game_support (C G) Λ₀ R hS hdim z) (fun _ _ _ _ => rfl)
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
