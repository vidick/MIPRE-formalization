/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.SamplerCost
import MIPRE.Foundations.Repeat.DeciderCost
import MIPRE.Background.Repetition.TensorPower
import MIPRE.Background.Repetition.Soundness

/-!
# Parallel repetition of normal form verifiers: the assembly

`MIPRE.repetition ℓ : Repetition ℓ` — blueprint `thm:parallel-repetition`, inhabited
(`planning/repetition-verifier.md`, R4). The output verifier `repVerifier V λ τ β` packages the
repeated sampler (`MIPRE.Repeat.repSampler`) and the repeated decider
(`MIPRE.Repeat.repDecider`). Its game at index `n`, with answers of length at most `T` for any
`T` past the length of an encoded `k`-tuple, is the `k`-fold direct repetition of `𝒱_n` at the
parse length `B`, up to two relabelings (`valStar_repVerifier`):

* the questions `𝔽₂^{k s}` are the `k`-tuples of questions `𝔽₂^s` (`CL.blockEquiv`), with the
  distribution matching because the repeated sampler's CL functions are direct sums
  (`CL.clDist_famSum`), and the decider reads the `i`-th block of a question where the repeated
  game reads the `i`-th coordinate (`toBits_block`);
* the answers of length at most `T` contain the encoded `k`-tuples of answers of length at most
  `B` (`tupleEmbed`), on which the repeated decider accepts exactly when every coordinate is
  accepted (`repDecider_accepts_iff`), and it accepts nothing else, so the extra answers do not
  change the value (`quantumValue_extendAnswers`) nor the PCC strategies (`SyncStrategy.extend`).

Completeness is then the tensor power (`exists_perfectPCC_repeat_doubled`), soundness is
`quantumValue_repeat_le_soundBound`, and the complexity clause is the two running-time theorems
`repSampler_timeBound` and `repDecider_timeBound` at `W = Repetition.arg`, the constants they
provide chosen once (`sampC`, `decC`, …) for the polynomial `bound`.
-/

namespace MIPRE

open Cost Cost.Data Cost.Prog CL Repeat Verifier

/-! ## The output verifier -/

/-- The output of the procedure on `𝒱` at `(λ, τ, β)`: the repeated sampler and decider. -/
noncomputable def repVerifier {ℓ : ℕ} (V : Verifier ℓ) (lam tau beta : ℕ) : Verifier ℓ where
  sampler := repSampler V.sampler lam tau
  decider := repDecider V.sampler.prog V.decider.prog lam tau beta
  accepts_length n x y a b h :=
    repDecider_accepts_length V.sampler V.decider lam tau beta n x y a b h

/-! ## Games reindexed along an equivalence of the questions -/

section Reindex

variable {X Y A B X' Y' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype X']
  [Fintype Y']

/-- The game `G` played through equivalences of the question alphabets. -/
def Game.reindex (G : Game X Y A B) (eX : X' ≃ X) (eY : Y' ≃ Y) : Game X' Y' A B where
  μ x y := G.μ (eX x) (eY y)
  μ_nonneg x y := G.μ_nonneg _ _
  μ_sum_one := by
    rw [← G.μ_sum_one]
    exact Fintype.sum_equiv eX _ _ fun x => Fintype.sum_equiv eY _ _ fun y => rfl
  D x y a b := G.D (eX x) (eY y) a b

theorem quantumValue_reindex (G : Game X Y A B) (eX : X' ≃ X) (eY : Y' ≃ Y) :
    quantumValue (G.reindex eX eY) = quantumValue G :=
  quantumValue_eq_of_equiv G (G.reindex eX eY) eX eY (Equiv.refl A) (Equiv.refl B)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

end Reindex

/-! ## Blocks of a question -/

/-- The `i`-th block of a question of `𝔽₂^{k s}` is the `i`-th chunk of its bit string. -/
theorem toBits_block {k s : ℕ} (x : Fin (k * s) → 𝔽₂) (i : Fin k) :
    toBits (block finProdFinEquiv i x) = chunk s i (toBits x) := by
  have h := block_ofBits (k := k) (s := s) (toBits x) i
  rw [ofBits_toBits] at h
  rw [h, toBits_ofBits (length_chunk (by simp) i)]

/-! ## Encoded tuples of answers -/

/-- Encoded `k`-tuples of bit strings are determined by their coordinates. -/
theorem tuple_encode_injective {k : ℕ} {f g : Fin k → BitStr}
    (h : (list (List.ofFn fun i => encode (f i))).toBitsPost =
      (list (List.ofFn fun i => encode (g i))).toBitsPost) : f = g := by
  have h2 := congrArg parse h
  simp only [parse_toBitsPost] at h2
  have h3 := congrArg toList h2
  simp only [toList_list] at h3
  have h4 := List.ofFn_injective h3
  funext i
  exact encode_injective (congrFun h4 i)

/-- The `k`-tuples of answers of length at most `B`, as answers of length at most `T`, for
`T` past the length of an encoded tuple. -/
noncomputable def tupleEmbed (k B T : ℕ) (hT : k * (4 * B + 2) + 1 ≤ T) :
    (Fin k → Answers B) ↪ Answers T where
  toFun aa := ⟨(list (List.ofFn fun i => encode (aa i).1)).toBitsPost,
    (length_toBitsPost_list_le k B _ fun i => (aa i).2).trans hT⟩
  inj' aa bb h := by
    have := tuple_encode_injective (congrArg Subtype.val h)
    funext i
    exact Subtype.ext (congrFun this i)

theorem tupleEmbed_val (k B T : ℕ) (hT : k * (4 * B + 2) + 1 ≤ T) (aa : Fin k → Answers B) :
    (tupleEmbed k B T hT aa).1 = (list (List.ofFn fun i => encode (aa i).1)).toBitsPost := rfl

/-! ## The game of the output is the repeated game -/

section Game

variable {ℓ : ℕ} (V : Verifier ℓ) (lam tau beta n : ℕ)

/-- The questions of the output at index `n` are `k`-tuples of questions of `𝒱_n`. -/
noncomputable def questionsEquiv : (repVerifier V lam tau beta).Questions n ≃
    (Fin (Repetition.reps lam tau n) → V.Questions n) :=
  blockEquiv (finProdFinEquiv (m := Repetition.reps lam tau n) (n := V.sampler.dim n))

/-- The repeated game, on the output's questions. -/
noncomputable def midGame : Game ((repVerifier V lam tau beta).Questions n)
    ((repVerifier V lam tau beta).Questions n)
    (Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n))
    (Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n)) :=
  ((V.game n (Repetition.parseBound lam beta n)).repeat (Repetition.reps lam tau n)).reindex
    (questionsEquiv V lam tau beta n) (questionsEquiv V lam tau beta n)

theorem quantumValue_midGame : quantumValue (midGame V lam tau beta n) =
    quantumValue ((V.game n (Repetition.parseBound lam beta n)).repeat
      (Repetition.reps lam tau n)) :=
  quantumValue_reindex _ _ _

/-- The distribution of the output's game is that of the repeated game. -/
theorem game_μ_eq (T : ℕ) (x y : (repVerifier V lam tau beta).Questions n) :
    ((repVerifier V lam tau beta).game n T).μ x y = (midGame V lam tau beta n).μ x y := by
  show clDist (CLFun.famSum finProdFinEquiv ℓ fun _ => V.sampler.cl n .alice).eval
    (CLFun.famSum finProdFinEquiv ℓ fun _ => V.sampler.cl n .bob).eval x y =
    ∏ i, V.sampler.dist n (block finProdFinEquiv i x) (block finProdFinEquiv i y)
  exact clDist_famSum finProdFinEquiv _ _ x y

/-- The output's decider on encoded tuples: every coordinate accepted. -/
theorem game_D_tuple (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T)
    (x y : (repVerifier V lam tau beta).Questions n)
    (aa bb : Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n)) :
    ((repVerifier V lam tau beta).game n T).D x y (tupleEmbed _ _ T hT aa)
      (tupleEmbed _ _ T hT bb) = (midGame V lam tau beta n).D x y aa bb := by
  classical
  have key := repDecider_accepts_iff V.sampler V.decider lam tau beta n (toBits x) (toBits y)
    (tupleEmbed _ _ T hT aa).1 (tupleEmbed _ _ T hT bb).1
  simp only [Verifier.game, midGame, Game.reindex, Game.repeat, tupleEmbed_val, questionsEquiv,
    blockEquiv, Equiv.coe_fn_mk]
  apply decide_eq_decide.mpr
  refine key.trans ?_
  constructor
  · rintro ⟨-, -, aa', bb', ha, hb, hall⟩
    have ha' := tuple_encode_injective ha
    have hb' := tuple_encode_injective hb
    subst ha' hb'
    intro i
    have hx : toBits (block finProdFinEquiv i x) = chunk (V.sampler.dim n) i (toBits x) :=
      toBits_block x i
    have hy : toBits (block finProdFinEquiv i y) = chunk (V.sampler.dim n) i (toBits y) :=
      toBits_block y i
    exact decide_eq_true (by erw [hx, hy]; exact (hall i).2.2)
  · intro h
    refine ⟨(length_toBits x).trans rfl, (length_toBits y).trans rfl, fun i => (aa i).1,
      fun i => (bb i).1, rfl, rfl, fun i => ⟨(aa i).2, (bb i).2, ?_⟩⟩
    have hx : toBits (block finProdFinEquiv i x) = chunk (V.sampler.dim n) i (toBits x) :=
      toBits_block x i
    have hy : toBits (block finProdFinEquiv i y) = chunk (V.sampler.dim n) i (toBits y) :=
      toBits_block y i
    have := of_decide_eq_true (h i)
    erw [hx, hy] at this
    exact this

/-- The output's decider accepts only encoded tuples. -/
theorem game_D_range (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T)
    (x y : (repVerifier V lam tau beta).Questions n) (a b : Answers T)
    (h : ((repVerifier V lam tau beta).game n T).D x y a b = true) :
    (∃ aa, tupleEmbed _ _ T hT aa = a) ∧ ∃ bb, tupleEmbed _ _ T hT bb = b := by
  classical
  simp only [Verifier.game] at h
  obtain ⟨-, -, aa, bb, ha, hb, hall⟩ :=
    (repDecider_accepts_iff V.sampler V.decider lam tau beta n _ _ _ _).mp (of_decide_eq_true h)
  exact ⟨⟨fun i => ⟨aa i, (hall i).1⟩, Subtype.ext ha.symm⟩,
    ⟨fun i => ⟨bb i, (hall i).2.1⟩, Subtype.ext hb.symm⟩⟩

/-- **The value of the output's game is that of the repeated game**, at any answer bound past
the length of an encoded tuple. -/
theorem valStar_repVerifier (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T) :
    (repVerifier V lam tau beta).valStar n T =
      quantumValue ((V.game n (Repetition.parseBound lam beta n)).repeat
        (Repetition.reps lam tau n)) := by
  classical
  have : Nonempty (Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n)) :=
    ⟨fun _ => ⟨[], by simp⟩⟩
  rw [← quantumValue_midGame]
  exact quantumValue_extendAnswers (midGame V lam tau beta n) _ (tupleEmbed _ _ T hT)
    (tupleEmbed _ _ T hT) (game_μ_eq V lam tau beta n T) (game_D_tuple V lam tau beta n T hT)
    (game_D_range V lam tau beta n T hT)

/-- **Completeness**: a value-`1` PCC strategy for `𝒱_n` at the parse length gives one for the
output's game, the tensor power relabeled and extended to the output's answers. -/
theorem hasPerfectPCC_repVerifier (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T)
    (h : V.HasPerfectPCC n (Repetition.parseBound lam beta n)) :
    (repVerifier V lam tau beta).HasPerfectPCC n T := by
  classical
  obtain ⟨S, hS, hv⟩ := exists_perfectPCC_repeat_doubled (Repetition.reps lam tau n) h
  let eX : Bool × (repVerifier V lam tau beta).Questions n ≃
      Bool × (Fin (Repetition.reps lam tau n) → V.Questions n) :=
    Equiv.prodCongr (Equiv.refl Bool) (questionsEquiv V lam tau beta n)
  have hμ₂ : ∀ p q, (midGame V lam tau beta n).doubled.μ p q =
      ((V.game n (Repetition.parseBound lam beta n)).repeat
        (Repetition.reps lam tau n)).doubled.μ (eX p) (eX q) := by
    rintro ⟨t, x⟩ ⟨u, y⟩; rfl
  have hD₂ : ∀ p q a b, (midGame V lam tau beta n).doubled.D p q a b =
      ((V.game n (Repetition.parseBound lam beta n)).repeat
        (Repetition.reps lam tau n)).doubled.D (eX p) (eX q) ((Equiv.refl _) a)
        ((Equiv.refl _) b) := by
    rintro ⟨t, x⟩ ⟨u, y⟩ a b; rfl
  have hμ₃ : ∀ p q, ((repVerifier V lam tau beta).game n T).doubled.μ p q =
      (midGame V lam tau beta n).doubled.μ p q := by
    rintro ⟨t, x⟩ ⟨u, y⟩
    simp only [Game.doubled, game_μ_eq]
  have hD₃ : ∀ p q a b, ((repVerifier V lam tau beta).game n T).doubled.D p q
      (tupleEmbed _ _ T hT a) (tupleEmbed _ _ T hT b) = (midGame V lam tau beta n).doubled.D p q a b := by
    rintro ⟨t, x⟩ ⟨u, y⟩ a b
    simp only [Game.doubled, game_D_tuple]
  let S₂ := S.relabel (midGame V lam tau beta n).doubled eX (Equiv.refl _)
  let S₃ := S₂.extend ((repVerifier V lam tau beta).game n T).doubled (tupleEmbed _ _ T hT)
  refine ⟨S₃, SyncStrategy.isPCC_extend (SyncStrategy.isPCC_relabel hS _ _ _ hμ₂) _ _ hμ₃, ?_⟩
  show S₃.value = 1
  rw [SyncStrategy.value_extend _ _ _ hμ₃ hD₃, SyncStrategy.value_relabel _ _ _ _ hμ₂ hD₂, hv]

/-- **Soundness**: `val*(𝒱_n) ≤ 1 - ε` at the parse length gives the direct repetition bound
for the output's game. -/
theorem valStar_repVerifier_le (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T) {ε : ℝ} (hε : 0 < ε)
    (h : V.valStar n (Repetition.parseBound lam beta n) ≤ 1 - ε) :
    (repVerifier V lam tau beta).valStar n T ≤ Repetition.soundBound Repetition.repConst ε
      (Repetition.reps lam tau n) (Repetition.parseBound lam beta n) := by
  rw [valStar_repVerifier V lam tau beta n T hT]
  exact Repetition.quantumValue_repeat_le_soundBound _ hε h (Nat.two_pow_pos _)

end Game

/-! ## The constants of the running-time bounds -/

/-- The constants of `repSampler_timeBound`, chosen once. -/
noncomputable def sampC : ℕ := repSampler_timeBound.choose
noncomputable def sampM : ℕ := repSampler_timeBound.choose_spec.choose
noncomputable def sampE : ℕ := repSampler_timeBound.choose_spec.choose_spec.choose

theorem sampC_spec {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
    (hW : SampDom S lam tau n R W) (hS : S.TimeBoundAt n R.S R.k) :
    (repSampler S lam tau).TimeBoundAt n (sampC * (W + 1) ^ sampM) (sampE * (R.k + 1)) :=
  repSampler_timeBound.choose_spec.choose_spec.choose_spec S lam tau n R W hW hS

/-- The constants of `repDecider_timeBound`, chosen once. -/
noncomputable def decC : ℕ := repDecider_timeBound.choose
noncomputable def decM : ℕ := repDecider_timeBound.choose_spec.choose
noncomputable def decE : ℕ := repDecider_timeBound.choose_spec.choose_spec.choose

theorem decC_spec {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider) (lam tau beta n : ℕ) (R : Budget)
    (W : ℕ) (hW : DecDom S D lam tau beta n R W) (hS : S.TimeBoundAt n R.S R.k)
    (hD : D.TimeBoundAt n R.D R.k) :
    (repDecider S.prog D.prog lam tau beta).TimeBoundAt n (decC * (W + 1) ^ decM)
      (decE * (R.k + 1)) :=
  repDecider_timeBound.choose_spec.choose_spec.choose_spec S D lam tau beta n R W hW hS hD

/-- The polynomial bounding the running times and the dimension of the output. -/
noncomputable def repBound : Polynomial ℕ :=
  Polynomial.C (sampC + decC + 1) * (Polynomial.X + 1) ^ (max sampM decM + 2)

theorem repBound_eval (W : ℕ) :
    repBound.eval W = (sampC + decC + 1) * (W + 1) ^ (max sampM decM + 2) := by
  simp [repBound]

/-- The polynomial bounding the answers the output accepts, in `k(n) + B(n)`. -/
noncomputable def repAnsBound : Polynomial ℕ := Polynomial.C 5 * (Polynomial.X + 1) ^ 2

theorem repAnsBound_eval (A : ℕ) : repAnsBound.eval A = 5 * (A + 1) ^ 2 := by
  simp [repAnsBound]

theorem ans_ineq (k B : ℕ) : k * (4 * B + 2) + 1 ≤ 5 * (k + B + 1) ^ 2 := by nlinarith

/-- The encoded tuples fit in the answer bound. -/
theorem ansArg_bound (lam tau beta n : ℕ) :
    Repetition.reps lam tau n * (4 * Repetition.parseBound lam beta n + 2) + 1 ≤
      repAnsBound.eval (Repetition.ansArg lam tau beta n) := by
  rw [repAnsBound_eval]
  exact ans_ineq _ _

/-! ## The complexity clause -/

/-- **The complexity clause**: within `repBound` at `Repetition.arg`, at degree
`max sampE decE (R.k + 1)`, with answers within `repAnsBound` at `k(n) + B(n)`. -/
theorem within_repVerifier {ℓ : ℕ} (V : Verifier ℓ) (lam tau beta n : ℕ) (R : Budget)
    (hV : V.Within n R) :
    (repVerifier V lam tau beta).Within n
      ⟨repBound.eval (Repetition.arg lam tau beta n R V.size),
        repBound.eval (Repetition.arg lam tau beta n R V.size),
        repBound.eval (Repetition.arg lam tau beta n R V.size), max sampE decE * (R.k + 1),
        repAnsBound.eval (Repetition.ansArg lam tau beta n)⟩ := by
  have hW : Repetition.arg lam tau beta n R V.size = Repetition.reps lam tau n +
      Repetition.parseBound lam beta n + R.S + R.d + R.D + R.B + V.size + lam + tau + beta + n +
      10 ^ R.k := rfl
  have hsize : esize V.sampler.prog ≤ V.size := le_max_left _ _
  have hsizeD : esize V.decider.prog ≤ V.size := le_max_right _ _
  have hdim := hV.sampler_dim
  have h10 : 1 ≤ 10 ^ R.k := Nat.one_le_pow _ _ (by norm_num)
  rw [repBound_eval]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hSD : SampDom V.sampler lam tau n R (Repetition.arg lam tau beta n R V.size) :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact (sampC_spec V.sampler lam tau n R _ hSD hV.sampler_time).mono
      (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · show Repetition.reps lam tau n * V.sampler.dim n ≤ _
    calc Repetition.reps lam tau n * V.sampler.dim n ≤
          Repetition.arg lam tau beta n R V.size * Repetition.arg lam tau beta n R V.size :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (Repetition.arg lam tau beta n R V.size + 1) ^ 2 := by
          rw [← sq]; exact Nat.pow_le_pow_left (Nat.le_succ _) 2
      _ ≤ (Repetition.arg lam tau beta n R V.size + 1) ^ (max sampM decM + 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (sampC + decC + 1) * (Repetition.arg lam tau beta n R V.size + 1) ^
            (max sampM decM + 2) := Nat.le_mul_of_pos_left _ (by omega)
  · have hDD : DecDom V.sampler V.decider lam tau beta n R
        (Repetition.arg lam tau beta n R V.size) :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    exact (decC_spec V.sampler V.decider lam tau beta n R _ hDD hV.sampler_time
      hV.decider_time).mono
      (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
      (Nat.mul_le_mul_right _ (le_max_right _ _))
  · intro x y a b hab h
    have hab' : repAnsBound.eval (Repetition.ansArg lam tau beta n) < a.length ∨
      repAnsBound.eval (Repetition.ansArg lam tau beta n) < b.length := hab
    have := repDecider_rejectsLong V.sampler V.decider lam tau beta n x y a b _
      (ansArg_bound lam tau beta n) h
    omega

/-! ## The theorem -/

/-- **Parallel repetition of normal form verifiers** (blueprint `thm:parallel-repetition`),
inhabited: the repeated sampler and decider, their programs as polynomial-time functions of
the inputs through the s-m-n map, the complexity clause `within_repVerifier`, completeness
`hasPerfectPCC_repVerifier` and soundness `valStar_repVerifier_le`. -/
noncomputable def repetition (ℓ : ℕ) : Repetition ℓ where
  c := Repetition.repConst
  c_pos := Repetition.repConst_pos
  bound := repBound
  ansBound := repAnsBound
  deg := max sampE decE
  sampler S lam tau := repSampler S lam tau
  samplerProg := (PolyTimeFun.smn (Prog × ℕ × ℕ)).comp
    ((PolyTimeFun.const (repSampCore selfUniversal.univ)).pair (PolyTimeFun.id _))
  samplerProg_eq _ _ _ := rfl
  compute := (PolyTimeFun.smn ((Prog × Prog) × ℕ × ℕ × ℕ)).comp
    ((PolyTimeFun.const (repDecCore selfUniversal.univ)).pair (PolyTimeFun.id _))
  output V lam tau beta := repVerifier V lam tau beta
  output_sampler _ _ _ _ := rfl
  output_decider _ _ _ _ := rfl
  within V lam tau beta n R hV := within_repVerifier V lam tau beta n R hV
  completeness V lam tau beta n h :=
    hasPerfectPCC_repVerifier V lam tau beta n _ (ansArg_bound lam tau beta n) h
  soundness V lam tau beta n _ hε _ h :=
    valStar_repVerifier_le V lam tau beta n _ (ansArg_bound lam tau beta n) hε h

end MIPRE
