/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliarySamplingProgram
import MIPRE.Foundations.Introspection.AuxiliaryRegisterBits

/-! # Bounded-source correctness of the full-register sampling program -/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryProgram
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight
  leftParts rightParts)

theorem marginal_query_size_le (R : ℕ) (hR : 1 ≤ R) (w : Player) (j : ℕ) (z : BitStr)
    (hj : Nat.size j ≤ R) (hz : z.length ≤ R) :
    esize (CL.Sampler.Query.marginal w j z) + 1 ≤ 32 * R := by
  have hw : esize w ≤ 3 := by cases w <;> decide
  have hjb := esize_nat_le j
  have hzb := esize_bitStr_le z
  change esize ((1 : ℕ),w,j,z,([] : BitStr)) + 1 ≤ _
  simp only [esize_prod]
  have hone : esize (1 : ℕ) = 5 := by decide
  have hnil : esize ([] : BitStr) = 1 := rfl
  rw [hone,hnil]
  omega

private theorem size_cost_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (b : ℕ)
    (hb : b ≤ 32 * (2^n)^lam) : (2^n)^lam * b^lam ≤ ansBound 5 lam n := by
  let u := lam*n
  have hlu : lam ≤ u := by dsimp [u]; nlinarith
  have hu : 1 ≤ u := hl.trans hlu
  have hR : (2^n)^lam = 2^u := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have hs : b ≤ 2^(5+u) := by simpa [hR,pow_add] using hb
  have he : u+(5+u)*lam ≤ (u+1)^5 := by
    have hc : 8 ≤ (u+1)^3 := by
      calc 8 = 2^3 := by norm_num
        _ ≤ (u+1)^3 := Nat.pow_le_pow_left (by omega) 3
    calc u+(5+u)*lam ≤ u+(5+u)*u := by gcongr
      _ ≤ 8*(u+1)^2 := by nlinarith
      _ ≤ (u+1)^3*(u+1)^2 := Nat.mul_le_mul_right _ hc
      _ = (u+1)^5 := by ring
  calc (2^n)^lam * b^lam ≤ 2^u * (2^(5+u))^lam := by rw [hR]; gcongr
    _ = 2^(u+(5+u)*lam) := by rw [← pow_mul,← pow_add]
    _ ≤ 2^((u+1)^5) := Nat.pow_le_pow_right (by decide) he

/-- A legal marginal query fits the same exponent-five clock as the source
decider. Its level enters through the length of its binary encoding. -/
theorem bounded_marginal_result {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (w : Player) (j : ℕ) (z : BitStr) (hj : 1 ≤ j) (hjℓ : j ≤ ℓ)
    (hjR : Nat.size j ≤ (2^n)^lam) (hz : z.length = V.sampler.dim (2^n)) :
    clockedResult V.sampler.prog (encode (2^n,CL.Sampler.Query.marginal w j z)) (ansBound 5 lam n) =
      .cons (encode true) (encode (CL.toBits
        (((V.sampler.cl (2^n) w).truncate j).eval (CL.ofBits (V.sampler.dim (2^n)) z)))) := by
  have hn' := (two_le_exp_index_iff n).mpr hn
  have hs : z.length ≤ (2^n)^lam := hz ▸ (hV.1 (2^n) hn').1
  have hb := marginal_query_size_le ((2^n)^lam) (Nat.one_le_pow _ _ (by positivity)) w j z hjR hs
  obtain ⟨r,t,ht,hr⟩ := (hV.1 (2^n) hn').2.1 (encode (CL.Sampler.Query.marginal w j z))
  obtain ⟨tu,hu⟩ := V.sampler.runs_marginal (2^n) w j z hj hjℓ hz
  rw [ClockProgram.clockedResult_eq_iff]
  refine ⟨t,ht.trans (size_cost_le (by have := hV.two_le; omega) hn _ hb),?_⟩
  exact (hr.deterministic hu).1 ▸ hr

theorem samplingResult_marginal {ℓ lam n Q R : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hℓR : Nat.size ℓ ≤ (2^n)^lam)
    (hQ : V.sampler.dim (2^n) ≤ Q) (w : Bool) (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    samplingResult 5 lam V.sampler.prog
      (ℓ,w,n,Q,R,V.sampler.dim (2^n),AnswerParser.pairBits (CL.toBits y) a,
        AnswerParser.pairBits (CL.toBits z) b) =
      .cons (encode true) (encode (CL.toBits ((V.sampler.cl (2^n) (Player.ofBool w)).eval
        (CL.pull (firstEmbedding hQ) z)))) := by
  rw [samplingResult,samplingCall_apply]
  simp only [inputIndex,inputDim,inputQ,inputRight,rightParts,comp_apply,pair_apply,fst_apply,snd_apply,
    DynamicParser.pairParts_apply,AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
  have he : ClockSimulation.reindexed (encode
      (n,CL.Sampler.Query.marginal (Player.ofBool w) ℓ
        ((CL.toBits z).take (V.sampler.dim (2^n))))) = encode
      (2^n,CL.Sampler.Query.marginal (Player.ofBool w) ℓ
        ((CL.toBits z).take (V.sampler.dim (2^n)))) := ClockSimulation.reindexed_cons n _
  have hi : ClockSimulation.indexReader (encode
      (n,CL.Sampler.Query.marginal (Player.ofBool w) ℓ
        ((CL.toBits z).take (V.sampler.dim (2^n))))) = n := readNat_encode n
  rw [he,hi,bounded_marginal_result V hV hn (Player.ofBool w) ℓ _ hℓ le_rfl hℓR
    (by simp [List.length_take,Nat.min_eq_left hQ]),ofBits_take_first hQ]
  simp only [CL.CLFun.truncate_self]

theorem samplingReady_vectors {s Q R ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hs : s ≤ Q)
    (hQ : 4 ≤ Q) (hR : 3*R ≤ Q) (n : ℕ) (w : Bool)
    (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    SamplingReady (ℓ,w,n,Q,R,s,AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.pairBits (CL.toBits z) b) ↔
      a.length ≤ R ∧ b.length ≤ R ∧ SourceCompiler.InSource s (CL.toBits y) ∧ a = b := by
  simp only [SamplingReady,hℓ,hs,true_and,outerCheck_iff,pairLeft,pairRight,
    inputDim,inputQ,inputR,inputLeft,inputRight,leftParts,rightParts,
    comp_apply,pair_apply,fst_apply,snd_apply,DynamicParser.pairCheck_apply,
    DynamicParser.pairParts_apply,
    AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
  have hp (v : Fin Q → CL.𝔽₂) (c : BitStr) :
      decide (AnswerParser.pairValid Q R (AnswerParser.pairBits (CL.toBits v) c)) = true ↔
        c.length ≤ R := by
    rw [← AnswerParser.pairCheck_apply,AnswerParser.pairCheck_pairBits]
    simp
  rw [hp,hp]
  constructor
  · rintro ⟨_,ha,hb,rest⟩
    exact ⟨ha,hb,rest⟩
  · rintro ⟨ha,hb,rest⟩
    exact ⟨⟨AnswerParser.pairBits_lt_outer Q R hQ hR _ _ (CL.length_toBits _) ha,
      AnswerParser.pairBits_lt_outer Q R hQ hR _ _ (CL.length_toBits _) hb⟩,ha,hb,rest⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual program accepts precisely the full-Q sampling relation for the
same-depth padded source CL, on the original answer cutoff. No restriction is
placed on the Sample seed's spectator coordinates. -/
theorem samplingProg_depthFamily {ℓ lam n Q R : ℕ} (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓR : Nat.size ℓ ≤ (2^n)^lam) (hs : V.sampler.dim (2^n) ≤ Q)
    (hQ : 4 ≤ Q) (hR : 3*R ≤ Q) (w : Bool) (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    (∃ t, (samplingProg 5 lam U V.sampler.prog).Runs
      (encode (ℓ,w,n,Q,R,V.sampler.dim (2^n),AnswerParser.pairBits (CL.toBits y) a,
        AnswerParser.pairBits (CL.toBits z) b)) (encode true) t) ↔
      a.length ≤ R ∧ b.length ≤ R ∧
      CLChecks.sampling (SourcePadding.depthFamily (firstEmbedding hs)
        (fun w => V.sampler.cl (2^n) (Player.ofBool w)) w) (y,a) (z,b) := by
  rw [samplingProg_accepts_iff]
  simp only [SamplingRawReady,readSamplingInput_encode,true_and]
  rw [samplingReady_vectors hℓ hs hQ hR,
    samplingResult_marginal V hV hn hℓ hℓR hs,samplingExpected_apply]
  simp only [inputDim,leftParts,inputQ,inputLeft,comp_apply,pair_apply,fst_apply,snd_apply,
    DynamicParser.pairParts_apply,
    AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _),Data.cons.injEq,
    true_and,encode_injective.eq_iff]
  rw [CLChecks.sampling,SourcePadding.depthFamily_eval (firstEmbedding hs)
    (fun w => V.sampler.cl (2^n) (Player.ofBool w)) hℓ
    (fun w => (V.sampler.cl_exactlyOn (2^n) (Player.ofBool w)).supportedOn),
    SourcePadding.family,CL.CLFun.eval_embed]
  constructor
  · rintro ⟨⟨ha,hb,hy,hab⟩,he⟩
    exact ⟨ha,hb,(source_bits_iff hs y _).mp ⟨hy,he.symm⟩,hab⟩
  · rintro ⟨ha,hb,hy,hab⟩
    obtain ⟨hys,he⟩ := (source_bits_iff hs y _).mpr hy
    exact ⟨⟨ha,hb,hys,hab⟩,he.symm⟩

end MIPRE.Introspection.AuxiliaryProgram
end
