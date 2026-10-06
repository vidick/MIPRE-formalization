/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.LpIntroCons
public import MIPRE.Background.Tailored.Intro.Output

@[expose] public section

/-!
# The linear-constraints processor of the introspection verifier

Issue #281 (Phase 3 of `planning/aldous-lyons-track.md`): the linear-constraints processor
`P^intro` of the tailored presentation of `Introspection.seven`, at the input's three programs
`(S, L, P)` and the parameter `λ`. On `(n, x, y, a^R, b^R)`, for `λ ≥ 1` and `n ≥ 1`, its
program

1. prepares the shared resources as the decision kernel of `seven` does
   (`DecisionPreparation.prog`): the clock `2^{(λn + 1)^5}` in unary, the index `2^n`, the
   Pauli parameters `(k, j, 2^j)` in unary, `Q` and `R`;
2. puts `Q` and `R` in unary (`ClockArithmetic.bothUnary`);
3. runs the core `mainP` (`LpIntroCons.lean`) on the environment, with the input's description
   clamped to `λ` (`InputRuns.clamp`) stored in the program (`hardcode`).

At `λ = 0` it is the empty program, and at `n = 0` it inspects the index in place
(`LenIntro.lenWrap`) and outputs `nil`: both output the empty list of constraints.

* `lpIntroC c U V λ`, `lpIntroProgC c U`: the processor and its program from `(V, λ)`, in
  polynomial time (`lpIntroProgC_eq`);
* `lpIntroC_lpIs`: what it outputs, on every input, at positive `λ` and `n`;
  `lpIntroC_lpIs_zero`: the empty list at `λ = 0` or `n = 0`;
* `lpIntro`, `lpIntroProg`: the same at `sevenConstant` and `selfClockedUniversal`;
* `lpIntro_cons_eq`: **the `cons_eq` clause of `Output.IntroSpec`** for a `λ`-bounded input whose
  normal form verifier `T.ofTNFVT U0` is `λ`-bounded, at `n ≥ 1`;
  `introSpec_lenIntro_lpIntro`: the whole specification, with `LenIntro.lenIntro`.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.LpIntro

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL MIPRE.Introspection InputRuns
open CL.Detyping CL.Detyping.Program

/-! ## The kernel input -/

/-- The prepared resources, the description typed. -/
abbrev KIn := Data × Metadata × Unary × ℕ × PauliSamplerParameters.Parameters × ℕ × ℕ

/-- The resources `DecisionPreparation.prog` prepares from `cons (encode M) x`. -/
def kernelInput (c : ℕ) (M : Metadata) (x : Data) : KIn :=
  let n := ClockSimulation.indexReader x
  (x, M, unary (ansBound 5 M.2 n), 2 ^ n, PauliSamplerParameters.parameters c M.2 n,
    SourceCompiler.registerBits c M.2 n, SourceCompiler.originalBound M.2 n)

theorem encode_kernelInput (c : ℕ) (M : Metadata) (x : Data) :
    encode (kernelInput c M x) =
      encode (DecisionPreparation.resources c (.cons (encode M) x)) := by
  rcases M with ⟨⟨S, L, P⟩, lam⟩
  simp [kernelInput, DecisionPreparation.resources, DecisionPreparation.inputRaw,
    DecisionPreparation.inputMetadata, DecisionPreparation.inputLambda, encode_prod,
    readNat_encode]

/-- The pair `(Q, R)` in the encoded resources. -/
def argQR : PolyTimeFun Data Data :=
  treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))

theorem argQR_kernelInput (c : ℕ) (M : Metadata) (x : Data) :
    argQR (encode (kernelInput c M x)) =
      encode (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x),
        SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x)) := by
  simp [argQR, kernelInput, encode_prod]

/-- The readers of the raw input `(n, x, y, a, b)`. -/
def rX : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp treeTail)
def rY : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (treeTail.comp treeTail))
def rA : PolyTimeFun Data BitStr :=
  readBits.comp (treeHead.comp (treeTail.comp (treeTail.comp treeTail)))
def rB : PolyTimeFun Data BitStr :=
  readBits.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))

/-- The core's input, from the resources and `(Q, R)` in unary. -/
def toIIn : PolyTimeFun (KIn × (Unary × Unary)) IIn :=
  let k : PolyTimeFun (KIn × (Unary × Unary)) KIn := fst
  let raw : PolyTimeFun (KIn × (Unary × Unary)) Data := fst.comp k
  let env : PolyTimeFun (KIn × (Unary × Unary)) Env :=
    (fst.comp (snd.comp (snd.comp k))).pair ((fst.comp (snd.comp k)).pair
      ((fst.comp (snd.comp (snd.comp (snd.comp k)))).pair
        ((fst.comp (snd.comp (snd.comp (snd.comp (snd.comp k))))).pair snd)))
  (env.pair ((rA.comp raw).pair (rB.comp raw))).pair ((rX.comp raw).pair (rY.comp raw))

theorem toIIn_kernelInput (c lam n : ℕ) (M : Metadata) (hM : M.2 = lam) (xs ys aR bR : BitStr) :
    toIIn (kernelInput c M (encode (n, xs, ys, aR, bR)),
        (unary (SourceCompiler.registerBits c lam n), unary (SourceCompiler.originalBound lam n))) =
      ((envOf c lam n M, aR, bR), xs, ys) := by
  subst hM
  simp [toIIn, kernelInput, envOf, rX, rY, rA, rB, encode_prod, readBits_encode,
    ClockSimulation.indexReader, readNat_encode]

/-- The kernel: the core on the prepared input. -/
def kernel (U : ClockedUniversalMachine) : PolyTimeFun (KIn × (Unary × Unary)) (List BitStr) :=
  (mainP U).comp toIIn

/-- The core program on `cons (encode M) (n, x, y, a, b)`. -/
def core (c : ℕ) (U : ClockedUniversalMachine) : Prog :=
  DecisionPreparation.sequence (DecisionPreparation.prog c)
    (DecisionPreparation.sequence (DecisionPreparation.appendStage argQR ClockArithmetic.bothUnary)
      (kernel U).code)

theorem core_wellScoped (c : ℕ) (U : ClockedUniversalMachine) : (core c U).WellScoped 1 :=
  DecisionPreparation.sequence_closed (DecisionPreparation.prog_closed c)
    (DecisionPreparation.sequence_closed
      (DecisionPreparation.appendStage_closed _ ClockArithmetic.bothUnary_closed) (kernel U).closed)

theorem core_runs (c : ℕ) (U : ClockedUniversalMachine) (M : Metadata) (x : Data) :
    ∃ t, (core c U).Runs (.cons (encode M) x)
      (encode (kernel U (kernelInput c M x,
        (unary (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x)),
          unary (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x)))))) t := by
  obtain ⟨s₁, h₁⟩ := DecisionPreparation.prog_runs c (.cons (encode M) x)
  rw [← encode_kernelInput] at h₁
  obtain ⟨t₂, -, h₂⟩ := ClockArithmetic.bothUnary_runs
    (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x))
    (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x))
  rw [← argQR_kernelInput] at h₂
  obtain ⟨s₂, h₂'⟩ :=
    DecisionPreparation.appendStage_runs argQR ClockArithmetic.bothUnary_closed
    _ _ t₂ h₂
  obtain ⟨s₃, -, h₃⟩ := (kernel U).computes (kernelInput c M x,
    (unary (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x)),
      unary (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x))))
  have h₂'' : (DecisionPreparation.appendStage argQR ClockArithmetic.bothUnary).Runs
      (encode (kernelInput c M x)) (encode (kernelInput c M x,
        (unary (SourceCompiler.registerBits c M.2 (ClockSimulation.indexReader x)),
          unary (SourceCompiler.originalBound M.2 (ClockSimulation.indexReader x))))) s₂ := by
    simpa only [encode_prod, encode_unary] using h₂'
  exact ⟨_, DecisionPreparation.sequence_runs (DecisionPreparation.sequence_closed
    (DecisionPreparation.appendStage_closed _ ClockArithmetic.bothUnary_closed)
      (kernel U).closed) h₁
    (DecisionPreparation.sequence_runs (kernel U).closed h₂'' h₃)⟩

/-! ## The processor -/

/-- The program of the processor at the input's programs `V` and `λ`: empty at `λ = 0`,
otherwise the core with the clamped description stored, behind the index test. -/
def lpProg (c : ℕ) (U : ClockedUniversalMachine) (V : Prog × Prog × Prog) (lam : ℕ) : Prog :=
  if lam = 0 then .nil else LenIntro.lenWrap (hardcode (core c U) (encode (clamp (V, lam))))

theorem lpProg_wellScoped (c : ℕ) (U : ClockedUniversalMachine) (V : Prog × Prog × Prog)
    (lam : ℕ) : (lpProg c U V lam).WellScoped 1 := by
  unfold lpProg
  split_ifs
  · trivial
  · exact LenIntro.lenWrap_wellScoped (hardcode_wellScoped (core_wellScoped c U) _)

/-- **The linear-constraints processor of the introspection verifier** at the constant `c`, the
clocked universal machine `U`, the input's programs `V` and the level `λ`. -/
def lpIntroC (c : ℕ) (U : ClockedUniversalMachine) (V : Prog × Prog × Prog) (lam : ℕ) :
    Decider :=
  ⟨lpProg c U V lam, lpProg_wellScoped c U V lam⟩

/-- **The processor's program from `(V, λ)`, in polynomial time.** -/
def lpIntroProgC (c : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun Metadata Prog :=
  ite (AuxiliaryProgram.equal snd (const 0)) (const .nil)
    (LenIntro.lenWrapF.comp ((PolyTimeFun.smn Metadata).comp ((const (core c U)).pair clamp)))

theorem lpIntroProgC_eq (c : ℕ) (U : ClockedUniversalMachine) (V : Prog × Prog × Prog)
    (lam : ℕ) : lpIntroProgC c U (V, lam) = (lpIntroC c U V lam).prog := by
  simp only [lpIntroProgC, PolyTimeFun.ite_apply, AuxiliaryProgram.equal_iff, snd_apply,
    const_apply, comp_apply, pair_apply, PolyTimeFun.smn_apply, LenIntro.lenWrapF_apply]
  rfl

/-- **What the processor outputs** at positive `λ` and `n`: the core on the environment of the
clamped description. -/
theorem lpIntroC_lpIs (c : ℕ) (U : ClockedUniversalMachine) (V : Prog × Prog × Prog)
    {lam n : ℕ}
    (hl : 1 ≤ lam) (hn : 1 ≤ n) (xs ys aR bR : BitStr) :
    LpIs (lpIntroC c U V lam) n xs ys aR bR
      (mainP U ((envOf c lam n (clamp (V, lam)), aR, bR), xs, ys)) := by
  obtain ⟨t, ht⟩ := core_runs c U (clamp (V, lam)) (encode (n, xs, ys, aR, bR))
  have hidx : ClockSimulation.indexReader (encode (n, xs, ys, aR, bR)) = n := by
    simp [ClockSimulation.indexReader, encode_prod, readNat_encode]
  have hM : (clamp (V, lam)).2 = lam := rfl
  rw [hidx, hM, kernel, comp_apply, toIIn_kernelInput c lam n _ hM] at ht
  have ht' : (core c U).Runs (.cons (encode (clamp (V, lam))) (.cons (encode n)
      (encode (xs, ys, aR, bR)))) (encode (mainP U ((envOf c lam n (clamp (V, lam)), aR, bR),
        xs, ys))) t := by
    rw [show (Data.cons (encode n) (encode (xs, ys, aR, bR))) = encode (n, xs, ys, aR, bR) from
      (encode_prod _ _).symm]
    exact ht
  have hh := hardcode_time (core_wellScoped c U) ht'
  have hw := LenIntro.lenWrap_runs_pos (hardcode_wellScoped (core_wellScoped c U) _) hn _ _ _ hh
  have hrun : (lpIntroC c U V lam).prog.Runs (encode (n, xs, ys, aR, bR))
      (encode (mainP U ((envOf c lam n (clamp (V, lam)), aR, bR), xs, ys)))
      (t + (encode (clamp (V, lam))).size + (Data.cons (encode n) (encode (xs, ys, aR, bR))).size +
        3 + (Data.cons (encode n) (encode (xs, ys, aR, bR))).size + 4) := by
    show (lpProg c U V lam).Runs _ _ _
    rw [lpProg, ite_eq_right (by omega),
      show (encode (n, xs, ys, aR, bR) : Data) = Data.cons (encode n) (encode (xs, ys, aR, bR))
        from encode_prod _ _]
    exact hw
  exact ⟨_, _, hrun, bitsListD_encode _⟩

/-- **At `λ = 0` or `n = 0` the processor outputs no constraint.** -/
theorem lpIntroC_lpIs_zero (c : ℕ) (U : ClockedUniversalMachine) (V : Prog × Prog × Prog)
    {lam n : ℕ} (h : lam = 0 ∨ n = 0) (xs ys aR bR : BitStr) :
    LpIs (lpIntroC c U V lam) n xs ys aR bR [] := by
  rcases h with rfl | rfl
  · refine ⟨1, .nil, ?_, rfl⟩
    show (lpProg c U V 0).Runs _ _ _
    rw [lpProg, ite_eq_left rfl]
    exact Eval.nil _
  · by_cases hl : lam = 0
    · subst hl
      refine ⟨1, .nil, ?_, rfl⟩
      show (lpProg c U V 0).Runs _ _ _
      rw [lpProg, ite_eq_left rfl]
      exact Eval.nil _
    · refine ⟨3, .nil, ?_, rfl⟩
      show (lpProg c U V lam).Runs _ _ _
      rw [lpProg, ite_eq_right hl, encode_prod]
      exact LenIntro.lenWrap_runs_zero _ _

/-! ## At the constant of `Introspection.seven` -/

/-- **The linear-constraints processor `P^intro_λ`** of the tailored presentation of
`Introspection.seven`, at the input's programs `V`. -/
def lpIntro (V : Prog × Prog × Prog) (lam : ℕ) : Decider :=
  lpIntroC sevenConstant selfClockedUniversal V lam

/-- Its program from `(V, λ)`, in polynomial time. -/
def lpIntroProg : PolyTimeFun ((Prog × Prog × Prog) × ℕ) Prog :=
  lpIntroProgC sevenConstant selfClockedUniversal

theorem lpIntroProg_eq (V : Prog × Prog × Prog) (lam : ℕ) :
    lpIntroProg (V, lam) = (lpIntro V lam).prog :=
  lpIntroProgC_eq sevenConstant selfClockedUniversal V lam

/-- At `λ = 0` or `n = 0`, the processor outputs no constraint. -/
theorem lpIntro_lpIs_zero {V : Prog × Prog × Prog} {lam n : ℕ} (h : lam = 0 ∨ n = 0)
    (xs ys aR bR : BitStr) : LpIs (lpIntro V lam) n xs ys aR bR [] :=
  lpIntroC_lpIs_zero _ _ V h xs ys aR bR

/-! ## The specification -/

theorem toBits_qe {c : ℕ} {hc : 1 ≤ c} {he : Even c} {lam n : ℕ} {U : ClockedUniversalMachine}
    {V : Verifier 7} (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (x : Coord Label (Fin (PauliSampler.dimension c lam n)) → ZMod 2) :
    CL.toBits (Output.qe c hc he U V hl hn x) =
      CL.toBits (DeciderProgram.vectorEquiv (PauliSampler.dimension c lam n) x) := by
  simp only [Output.qe, Equiv.trans_apply]
  exact Verifier.toBits_dimensionEquiv _ _

/-- **The `cons_eq` clause of the specification**, at a constant `c`: for a `λ`-bounded input
`T` and a `λ`-bounded normal form verifier `V` with `T`'s sampler program, at `n ≥ 1`, the
processor outputs at every pair of detyped questions the presented game's constraints. -/
theorem lpIntroC_cons_eq {c : ℕ} (hc : 1 ≤ c) (he : Even c) {lam n : ℕ}
    (U : ClockedUniversalMachine) (T : TailoredVerifier 7) (V : Verifier 7)
    (hT : T.IsBounded lam) (hV : V.IsBounded lam) (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (hsamp : V.sampler.prog = T.sampler.prog)
    (hs : V.sampler.dim (2 ^ n) ≤ SourceCompiler.registerBits c lam n)
    (x y : Coord Label (Fin (PauliSampler.dimension c lam n)) → ZMod 2) (aR bR : BitStr) :
    LpIs (lpIntroC c U T.progs lam) n (CL.toBits (Output.qe c hc he U V hl hn x))
      (CL.toBits (Output.qe c hc he U V hl hn y)) aR bR
      ((presented DecisionCompiler.graph (Sound.H c hc he lam n U V)
        (Sound.tdata c hc he lam n T V hs
          (regKerGens (SourceCompiler.registerBits c lam n)))).cons x y aR bR) := by
  have h := lpIntroC_lpIs c U T.progs hl hn (CL.toBits (Output.qe c hc he U V hl hn x))
    (CL.toBits (Output.qe c hc he U V hl hn y)) aR bR
  rw [toBits_qe, toBits_qe] at h ⊢
  have hm := mainP_spec U hc he T V hT hV hn hsamp hs x y aR bR
  change LpIs _ n _ _ aR bR (mainP U ((envT c lam n T, aR, bR), _, _)) at h
  rw [hm] at h
  convert h using 1
  unfold presented TypedData.detype
  dsimp only
  cases hE : edgeOf DecisionCompiler.graph x y <;> (erw [hE]; try rfl)

/-- **The `cons_eq` clause of `Output.IntroSpec` for `lpIntro`**: for a `λ`-bounded tailored
input `T` whose normal form verifier `T.ofTNFVT U0` is `λ`-bounded, at `n ≥ 1`, with the kernel
generators `regKerGens`. -/
theorem lpIntro_cons_eq {lam n : ℕ} (T : TailoredVerifier 7) (U0 : UniversalMachine)
    (hT : T.IsBounded lam) (hV : (T.ofTNFVT U0).IsBounded lam) (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (hs : (T.ofTNFVT U0).sampler.dim (2 ^ n) ≤ SourceCompiler.registerBits sevenConstant lam n)
    (x y : Coord Label (Fin (PauliSampler.dimension sevenConstant lam n)) → ZMod 2)
    (aR bR : BitStr) :
    LpIs (lpIntro T.progs lam) n
      (CL.toBits (Output.qe sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
        selfClockedUniversal (T.ofTNFVT U0) hl hn x))
      (CL.toBits (Output.qe sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
        selfClockedUniversal (T.ofTNFVT U0) hl hn y)) aR bR
      ((presented DecisionCompiler.graph (Sound.H sevenConstant one_le_sevenConstant
          sevenConstant_spec.2.1 lam n selfClockedUniversal (T.ofTNFVT U0))
        (Sound.tdata sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 lam n T
          (T.ofTNFVT U0) hs (regKerGens (SourceCompiler.registerBits sevenConstant lam n)))).cons
        x y aR bR) :=
  lpIntroC_cons_eq one_le_sevenConstant sevenConstant_spec.2.1 selfClockedUniversal T _ hT hV hl hn
    rfl hs x y aR bR

/-- **The specification `Output.IntroSpec` of the output's two programs**, with
`LenIntro.lenIntro` and `lpIntro`: for a `λ`-bounded tailored input `T` whose normal form verifier
`T.ofTNFVT U0` is `λ`-bounded, at `n ≥ 1`, with the kernel generators `regKerGens`. -/
theorem introSpec_lenIntro_lpIntro {lam n : ℕ} (T : TailoredVerifier 7) (U0 : UniversalMachine)
    (hT : T.IsBounded lam) (hV : (T.ofTNFVT U0).IsBounded lam) (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (hs : (T.ofTNFVT U0).sampler.dim (2 ^ n) ≤ SourceCompiler.registerBits sevenConstant lam n) :
    Output.IntroSpec sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
      selfClockedUniversal (T.ofTNFVT U0) hl hn
      (presented DecisionCompiler.graph (Sound.H sevenConstant one_le_sevenConstant
          sevenConstant_spec.2.1 lam n selfClockedUniversal (T.ofTNFVT U0))
        (Sound.tdata sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 lam n T
          (T.ofTNFVT U0) hs (regKerGens (SourceCompiler.registerBits sevenConstant lam n))))
      (LenIntro.lenIntro lam) (lpIntro T.progs lam) where
  lenR_eq x := by
    rw [toBits_qe]
    exact (LenIntro.lenIntroC_lenIs_detype sevenConstant hl hn _ rfl rfl _ _ _ x).1
  lenL_eq x := by
    rw [toBits_qe]
    exact (LenIntro.lenIntroC_lenIs_detype sevenConstant hl hn _ rfl rfl _ _ _ x).2
  cons_eq x y aR bR := lpIntro_cons_eq T U0 hT hV hl hn hs x y aR bR

end MIPRE.Tailored.Intro.LpIntro

end
