/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArLpCons
public import MIPRE.Foundations.OracularDecider

@[expose] public section

/-!
# The linear-constraints processor of the answer-reduced verifier

Slice P4h of `planning/aldous-lyons-track.md`: the linear-constraints processor of the output
tailored verifier of the answer reduction, as a staged program. On `(n, x, y, a^R, b^R)`, with the
input verifier's programs and `(λ, μ, σ)` hardcoded, it runs

1. the routine's parameter program on `((λ, μ, σ), n)` (`ArRoutine.parCore`);
2. to 5. the input sampler on the marginal queries of Alice and Bob at the seeds of `x` and of
   `y`, through the universal machine;
6. and 7. the routine's circuit function on the input's programs, the parameters and the two
   questions at each seed, on its encoding;
8. and 9. the proof check of each question, on its encoding, the circuit's gates spliced in;

and then the last stage `lpFinal` on what it read. No stage decodes a program: the circuit
function and the proof check run on encodings assembled from the context.

* `lpRuns`: the run, and `lpD_lpIs`: the processor outputs the presented answer-reduced game's
  constraints at every pair of detyped questions.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.CL.Detyping MIPRE.SAT

/-! ## Reading the context -/

/-- The hardcoded data, `(V.progs, λ, μ, σ)`, after `k` stages. -/
def hdL (k : ℕ) : PolyTimeFun Data Data := treeHead.comp (AnswerReduction.tails k)
/-- The input tuple `(n, x, y, a^R, b^R)`, after `k` stages. -/
def inL (k : ℕ) : PolyTimeFun Data Data := treeTail.comp (AnswerReduction.tails k)
/-- The index. -/
def nL (k : ℕ) : PolyTimeFun Data Data := treeHead.comp (inL k)
/-- The first question. -/
def xL (k : ℕ) : PolyTimeFun Data Data := treeHead.comp (treeTail.comp (inL k))
/-- The second question. -/
def yL (k : ℕ) : PolyTimeFun Data Data := treeHead.comp (treeTail.comp (treeTail.comp (inL k)))
/-- The first readable answer. -/
def aL (k : ℕ) : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp (inL k))))
/-- The second readable answer. -/
def bL (k : ℕ) : PolyTimeFun Data Data :=
  treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp (inL k))))
/-- The input verifier's programs. -/
def progsL (k : ℕ) : PolyTimeFun Data Data := treeHead.comp (hdL k)
/-- `(λ, μ, σ)`. -/
def lmsL (k : ℕ) : PolyTimeFun Data Data := treeTail.comp (hdL k)

/-- The parameters, the first stage's result, after `k ≥ 1` stages. -/
def parL (k : ℕ) : PolyTimeFun Data ArParams := readParams.comp (AnswerReduction.res (k - 1))

/-- **The typed view of the context** after `k ≥ 1` stages: the parameters, the questions and the
readable answers, without input sampler questions or programs. -/
def preL (k : ℕ) : PolyTimeFun Data LpIn :=
  (parL k).pair (((Program.readBits.comp (xL k)).pair ((Program.readBits.comp (yL k)).pair
    ((Program.readBits.comp (aL k)).pair (Program.readBits.comp (bL k))))).pair
    ((const (([], [], [], []) : BitStr × BitStr × BitStr × BitStr)).pair
      (const ((default : Prog × Prog × Prog), ((0, 0, 0) : ℕ × ℕ × ℕ), (0 : ℕ)))))

/-! ## The stages' arguments -/

/-- Stage 1's argument: `((λ, μ, σ), n)`. -/
def argParL : PolyTimeFun Data Data := ap₂ treePair (lmsL 0) (nL 0)

/-- The seed bits of a question, after `k ≥ 1` stages: its vector part before the low-degree
bits. -/
def seedL (k : ℕ) (q : ℕ → PolyTimeFun Data Data) : PolyTimeFun Data BitStr :=
  AnswerReduction.leftBP.comp ((ap₂ drop (Program.readBits.comp (q k)) (const (unary gdA))).pair
    (dtF.comp (parL k)))

/-- A marginal call's argument, after `k` stages: the input sampler's program and the query
`(n, marginal w (ℓ + 1) z)` at the seed `z` of a question. -/
def argMgL (ℓ k : ℕ) (q : ℕ → PolyTimeFun Data Data) (w : Player) : PolyTimeFun Data Data :=
  ap₂ treePair (treeHead.comp (progsL k)) (ap₂ treePair (nL k) (Program.encoded.comp
    ((const (1 : ℕ)).pair ((const w).pair ((const (ℓ + 1)).pair ((seedL k q).pair
      (const ([] : BitStr))))))))

/-- A circuit stage's argument, after `k` stages: the encoding of the circuit function's input,
from the input's programs, `(λ, μ, σ)`, the index, the parameters and the input sampler's
questions `rA` and `rB` stages back, read as bit strings — so that the argument is an encoding on
every input, whatever the input sampler output. -/
def argCircL (k rA rB : ℕ) : PolyTimeFun Data Data :=
  ap₂ treePair (progsL k) (ap₂ treePair (lmsL k) (ap₂ treePair (nL k) (ap₂ treePair
    (AnswerReduction.res (k - 1)) (ap₂ treePair
      (Program.encoded.comp (Program.readBits.comp (AnswerReduction.res rA)))
      (Program.encoded.comp (Program.readBits.comp (AnswerReduction.res rB)))))))

/-- A proof stage's argument, after `k` stages: the encoding of the proof check's input of a
question at offset `o`, with readable answer `a` read as a bit string, the gates of the circuit
`rC` stages back. -/
def argPrfL (k rC : ℕ) (o : PolyTimeFun LpIn Unary) (q : PolyTimeFun LpIn BitStr)
    (a : ℕ → PolyTimeFun Data Data) : PolyTimeFun Data Data :=
  ap₂ treePair (AnswerReduction.res (k - 1)) (ap₂ treePair (Program.encoded.comp (o.comp (preL k)))
    (ap₂ treePair (Program.encoded.comp (nF.comp (preL k))) (ap₂ treePair
      (Program.encoded.comp ((ptsF q).comp (preL k))) (ap₂ treePair
        (Program.encoded.comp (Program.readBits.comp (a k)))
        (treeTail.comp (AnswerReduction.res rC))))))

/-- A list of bit strings from its encoding. -/
def readBL : PolyTimeFun Data (List BitStr) := (map Program.readBits).comp AnswerReduction.rawListP

/-- The last stage's reader, after the nine stages. -/
def finRead : PolyTimeFun Data LpFin :=
  (parL 9).pair (((Program.readBits.comp (xL 9)).pair ((Program.readBits.comp (yL 9)).pair
    ((Program.readBits.comp (aL 9)).pair (Program.readBits.comp (bL 9))))).pair
    ((readBL.comp (AnswerReduction.res 1)).pair (readBL.comp (AnswerReduction.res 0))))

namespace ArRoutine

variable (R : ArRoutine)

/-- **The processor's core**, on `((V.progs, λ, μ, σ), (n, x, y, a^R, b^R))`, for an input sampler
of level `ℓ + 1`. -/
def lpCore (ℓ : ℕ) : Prog :=
  seqProg (AnswerReduction.stg argParL R.parCore) <|
  seqProg (AnswerReduction.stg (argMgL ℓ 1 xL .alice) selfUniversal.univ) <|
  seqProg (AnswerReduction.stg (argMgL ℓ 2 xL .bob) selfUniversal.univ) <|
  seqProg (AnswerReduction.stg (argMgL ℓ 3 yL .alice) selfUniversal.univ) <|
  seqProg (AnswerReduction.stg (argMgL ℓ 4 yL .bob) selfUniversal.univ) <|
  seqProg (AnswerReduction.stg (argCircL 5 3 2) R.circF.code) <|
  seqProg (AnswerReduction.stg (argCircL 6 2 1) R.circF.code) <|
  seqProg (AnswerReduction.stg (argPrfL 7 1 (const (unary 0)) lX aL) proofConsF.code) <|
  seqProg (AnswerReduction.stg (argPrfL 8 1 nAF lY bL) proofConsF.code)
    (lpFinal.comp finRead).code

theorem lpCore_closed (ℓ : ℕ) : (R.lpCore ℓ).WellScoped 1 := by
  have hu := selfUniversal.closed
  have hc := R.circF.closed
  have hp := proofConsF.closed
  exact seqProg_closed (AnswerReduction.stg_closed _ R.closed) <|
    seqProg_closed (AnswerReduction.stg_closed _ hu) <|
    seqProg_closed (AnswerReduction.stg_closed _ hu) <|
    seqProg_closed (AnswerReduction.stg_closed _ hu) <|
    seqProg_closed (AnswerReduction.stg_closed _ hu) <|
    seqProg_closed (AnswerReduction.stg_closed _ hc) <|
    seqProg_closed (AnswerReduction.stg_closed _ hc) <|
    seqProg_closed (AnswerReduction.stg_closed _ hp) <|
    seqProg_closed (AnswerReduction.stg_closed _ hp) (PolyTimeFun.closed _)

/-- **The linear-constraints processor**, for the input programs `V` and `(λ, μ, σ)`. -/
def lpD (ℓ : ℕ) (V : Prog × Prog × Prog) (lam mu sigma : ℕ) : Decider :=
  ⟨hardcode (R.lpCore ℓ) (encode (V, lam, mu, sigma)), hardcode_wellScoped (R.lpCore_closed ℓ) _⟩

/-- Its program, from the input programs and `(λ, μ, σ)`, in polynomial time. -/
def lpPF (ℓ : ℕ) : PolyTimeFun ((Prog × Prog × Prog) × ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn ((Prog × Prog × Prog) × ℕ × ℕ × ℕ)).comp
    ((const (R.lpCore ℓ)).pair (PolyTimeFun.id _))

theorem lpPF_eq (ℓ : ℕ) (V : Prog × Prog × Prog) (lam mu sigma : ℕ) :
    R.lpPF ℓ (V, lam, mu, sigma) = (R.lpD ℓ V lam mu sigma).prog :=
  rfl

end ArRoutine

/-! ## The run -/

theorem readBL_encode (l : List BitStr) : readBL (encode l) = l := by
  simp only [readBL, comp_apply, AnswerReduction.rawListP, ofEncodeEq_apply,
    AnswerReduction.rawList_encode, map_apply, List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun s _ => Program.readBits_encode s

/-- The seed bits of a question's bits are its role part's. -/
theorem leftBP_rolePart {t j rV : ℕ} (y : Fin (rV + D j * t) → 𝔽₂) :
    AnswerReduction.leftBP (toBits y, unary (D j * t)) = toBits (rolePart t j rV y) := by
  rw [AnswerReduction.leftBP_apply, length_toBits, length_unary, Nat.add_sub_cancel, rolePart,
    take_toBits]

namespace ArRoutine

section Run

variable (R : ArRoutine) (lam mu sigma n : ℕ) {ℓ : ℕ} (V : TailoredVerifier (ℓ + 1))
  (qx qy : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
    D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) (aR bR : BitStr)

/-- The core's input. -/
abbrev lpX0 : Data := .cons (encode (V.progs, lam, mu, sigma))
  (encode (n, toBits (DeciderProgram.vectorEquiv _ qx), toBits (DeciderProgram.vectorEquiv _ qy),
    aR, bR))

/-- A question's seed, as a question of the input verifier. -/
abbrev seedOf (q : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
    D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) : V.Questions n :=
  rolePart ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (V.sampler.dim n)
    (pull Function.Embedding.inr q)

/-- The input sampler's question of player `w` at a question's seed, as data. -/
abbrev margD (w : Player) (q : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
    D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) : Data :=
  encode (toBits ((V.sampler.cl n w).eval (R.seedOf lam mu sigma n V q)))

theorem seedL_eq (k : ℕ) (X : Data) (q : ℕ → PolyTimeFun Data Data)
    (z : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂)
    (hp : AnswerReduction.res (k - 1) X = encode (R.params lam mu sigma n))
    (hq : q k X = encode (toBits (DeciderProgram.vectorEquiv _ z))) :
    seedL k q X = toBits (R.seedOf lam mu sigma n V z) := by
  simp only [seedL, comp_apply, pair_apply, ap₂_apply, const_apply, drop_apply, length_unary,
    hq, Program.readBits_encode, parL, hp, readParams_encode, ArRoutine.params, dtF_arParams]
  rw [show DeciderProgram.vectorEquiv _ z = push (registerEquiv _).toEmbedding z from rfl,
    DeciderProgram.drop_register, leftBP_rolePart]

/-- A marginal call's argument is the query at the question's seed. -/
theorem argMgL_eq (k : ℕ) (X : Data) (q : ℕ → PolyTimeFun Data Data) (w : Player)
    (z : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂)
    (hp : AnswerReduction.res (k - 1) X = encode (R.params lam mu sigma n))
    (hq : q k X = encode (toBits (DeciderProgram.vectorEquiv _ z)))
    (hs : treeHead (progsL k X) = encode V.sampler.prog) (hn : nL k X = encode n) :
    argMgL ℓ k q w X = .cons (encode V.sampler.prog)
      (encode (n, Sampler.Query.marginal w (ℓ + 1) (toBits (R.seedOf lam mu sigma n V z)))) := by
  simp only [argMgL, ap₂_apply, treePair_apply, comp_apply, pair_apply, const_apply,
    Program.encoded_apply, hs, hn, R.seedL_eq lam mu sigma n V k X q z hp hq, encode_prod]
  rfl

/-- The input sampler's run on a marginal query at a question's seed. -/
theorem marg_runs (w : Player) (z : Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) → 𝔽₂) :
    ∃ t, selfUniversal.univ.Runs (.cons (encode V.sampler.prog)
      (encode (n, Sampler.Query.marginal w (ℓ + 1) (toBits (R.seedOf lam mu sigma n V z)))))
      (R.margD lam mu sigma n V w z) t := by
  have h := OracleDecider.univ_marginal V.sampler n (ℓ + 1) (by omega) le_rfl w
    (toBits (R.seedOf lam mu sigma n V z)) (length_toBits _)
  simpa [OracleDecider.margBits] using h

/-- **The core's run**: it outputs the presented answer-reduced game's constraints. -/
theorem lpCore_runs {ℓ' : ℕ} (P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) ℓ') (B : ℕ) :
    ∃ t, (R.lpCore ℓ).Runs (R.lpX0 lam mu sigma n V qx qy aR bR)
      (encode ((arPresented (R.d lam mu sigma n) ((R.fam lam mu sigma).dvd n)
        ((R.fam lam mu sigma).sel n) (R.L lam mu sigma n) (R.hLM lam mu sigma n) V n
        (R.circ lam mu sigma n V) (R.circ_wires lam mu sigma n V) P B).cons qx qy aR bR)) t := by
  have hu := selfUniversal.closed
  have hc := R.circF.closed
  have hpf := proofConsF.closed
  set X0 := R.lpX0 lam mu sigma n V qx qy aR bR with hX0
  set prm := R.params lam mu sigma n with hprm
  set qI := R.qIn lam mu sigma n V qx qy aR bR with hqI
  set rAx := R.margD lam mu sigma n V .alice qx
  set rBx := R.margD lam mu sigma n V .bob qx
  set rAy := R.margD lam mu sigma n V .alice qy
  set rBy := R.margD lam mu sigma n V .bob qy
  -- stage 1: the parameters
  have r1 := AnswerReduction.stg_runs argParL R.closed X0 (encode prm) (by
    simpa [argParL, lmsL, nL, hdL, inL, X0, encode_prod] using R.parCore_runs lam mu sigma n)
  set X1 := Data.cons (encode prm) X0
  -- stages 2 to 5: the marginal calls
  have r2 := AnswerReduction.stg_runs (argMgL ℓ 1 xL .alice) hu X1 rAx (by
    rw [R.argMgL_eq lam mu sigma n V 1 X1 xL .alice qx (by simp [AnswerReduction.res, X1, hprm])
      (by simp [xL, inL, X1, X0, encode_prod]) (by simp [progsL, hdL, X1, X0, encode_prod]; rfl)
      (by simp [nL, inL, X1, X0, encode_prod])]
    exact R.marg_runs lam mu sigma n V .alice qx)
  set X2 := Data.cons rAx X1
  have r3 := AnswerReduction.stg_runs (argMgL ℓ 2 xL .bob) hu X2 rBx (by
    rw [R.argMgL_eq lam mu sigma n V 2 X2 xL .bob qx (by simp [AnswerReduction.res, X2, X1, hprm])
      (by simp [xL, inL, X2, X1, X0, encode_prod])
      (by simp [progsL, hdL, X2, X1, X0, encode_prod]; rfl)
      (by simp [nL, inL, X2, X1, X0, encode_prod])]
    exact R.marg_runs lam mu sigma n V .bob qx)
  set X3 := Data.cons rBx X2
  have r4 := AnswerReduction.stg_runs (argMgL ℓ 3 yL .alice) hu X3 rAy (by
    rw [R.argMgL_eq lam mu sigma n V 3 X3 yL .alice qy
      (by simp [AnswerReduction.res, X3, X2, X1, hprm])
      (by simp [yL, inL, X3, X2, X1, X0, encode_prod])
      (by simp [progsL, hdL, X3, X2, X1, X0, encode_prod]; rfl)
      (by simp [nL, inL, X3, X2, X1, X0, encode_prod])]
    exact R.marg_runs lam mu sigma n V .alice qy)
  set X4 := Data.cons rAy X3
  have r5 := AnswerReduction.stg_runs (argMgL ℓ 4 yL .bob) hu X4 rBy (by
    rw [R.argMgL_eq lam mu sigma n V 4 X4 yL .bob qy
      (by simp [AnswerReduction.res, X4, X3, X2, X1, hprm])
      (by simp [yL, inL, X4, X3, X2, X1, X0, encode_prod])
      (by simp [progsL, hdL, X4, X3, X2, X1, X0, encode_prod]; rfl)
      (by simp [nL, inL, X4, X3, X2, X1, X0, encode_prod])]
    exact R.marg_runs lam mu sigma n V .bob qy)
  set X5 := Data.cons rBy X4
  -- stages 6 and 7: the circuits
  set Cx := R.circ lam mu sigma n V (R.seedOf lam mu sigma n V qx)
  set Cy := R.circ lam mu sigma n V (R.seedOf lam mu sigma n V qy)
  have r6 := AnswerReduction.stg_runs (argCircL 5 3 2) hc X5 (encode Cx) (by
    obtain ⟨t, -, ht⟩ := R.circF.computes (V.progs, (lam, mu, sigma), n, prm,
      toBits ((V.sampler.cl n .alice).eval (R.seedOf lam mu sigma n V qx)),
      toBits ((V.sampler.cl n .bob).eval (R.seedOf lam mu sigma n V qx)))
    refine ⟨t, ?_⟩
    convert ht using 1
    · simp [argCircL, progsL, lmsL, nL, hdL, inL, AnswerReduction.res, X5, X4, X3, X2, X1, X0,
        encode_prod, rAx, rBx, ArRoutine.margD, hprm, Program.readBits_encode]
    · rfl)
  set X6 := Data.cons (encode Cx) X5
  have r7 := AnswerReduction.stg_runs (argCircL 6 2 1) hc X6 (encode Cy) (by
    obtain ⟨t, -, ht⟩ := R.circF.computes (V.progs, (lam, mu, sigma), n, prm,
      toBits ((V.sampler.cl n .alice).eval (R.seedOf lam mu sigma n V qy)),
      toBits ((V.sampler.cl n .bob).eval (R.seedOf lam mu sigma n V qy)))
    refine ⟨t, ?_⟩
    convert ht using 1
    · simp [argCircL, progsL, lmsL, nL, hdL, inL, AnswerReduction.res, X6, X5, X4, X3, X2, X1, X0,
        encode_prod, rAy, rBy, ArRoutine.margD, hprm, Program.readBits_encode]
    · rfl)
  set X7 := Data.cons (encode Cy) X6
  -- stages 8 and 9: the proof checks
  have hpre7 : preL 7 X7 = lpIn prm qx qy aR bR ([], [], [], []) (default, (0, 0, 0), 0) := by
    simp [preL, parL, xL, yL, aL, bL, inL, AnswerReduction.res, X7, X6, X5, X4, X3, X2, X1, X0,
      encode_prod, readParams_encode, Program.readBits_encode]
  have r8 := AnswerReduction.stg_runs (argPrfL 7 1 (const (unary 0)) lX aL) hpf X7
    (encode (proofConsF (R.prfInF (const (unary 0)) lX lA lAx lBx qI))) (by
    obtain ⟨t, -, ht⟩ := proofConsF.computes (R.prfInF (const (unary 0)) lX lA lAx lBx qI)
    refine ⟨t, ?_⟩
    convert ht using 1
    simp only [argPrfL, ap₂_apply, treePair_apply, comp_apply, Program.encoded_apply, hpre7]
    simp [AnswerReduction.res, aL, inL, X7, X6, X5, X4, X3, X2, X1, X0, encode_prod, Cx,
      Program.readBits_encode]
    rfl)
  set X8 := Data.cons (encode (proofConsF (R.prfInF (const (unary 0)) lX lA lAx lBx qI))) X7
  have hpre8 : preL 8 X8 = lpIn prm qx qy aR bR ([], [], [], []) (default, (0, 0, 0), 0) := by
    simp [preL, parL, xL, yL, aL, bL, inL, AnswerReduction.res, X8, X7, X6, X5, X4, X3, X2, X1,
      X0, encode_prod, readParams_encode, Program.readBits_encode]
  have r9 := AnswerReduction.stg_runs (argPrfL 8 1 nAF lY bL) hpf X8
    (encode (proofConsF (R.prfInF nAF lY lB lAy lBy qI))) (by
    obtain ⟨t, -, ht⟩ := proofConsF.computes (R.prfInF nAF lY lB lAy lBy qI)
    refine ⟨t, ?_⟩
    convert ht using 1
    simp only [argPrfL, ap₂_apply, treePair_apply, comp_apply, Program.encoded_apply, hpre8]
    simp [AnswerReduction.res, bL, inL, X8, X7, X6, X5, X4, X3, X2, X1, X0, encode_prod, Cy,
      Program.readBits_encode]
    rfl)
  set X9 := Data.cons (encode (proofConsF (R.prfInF nAF lY lB lAy lBy qI))) X8
  -- the last stage
  obtain ⟨t10, -, r10⟩ := (lpFinal.comp finRead).computes X9
  have hfin : finRead X9 = (prm, (toBits (DeciderProgram.vectorEquiv _ qx),
      toBits (DeciderProgram.vectorEquiv _ qy), aR, bR),
      (proofConsF (R.prfInF (const (unary 0)) lX lA lAx lBx qI),
        proofConsF (R.prfInF nAF lY lB lAy lBy qI))) := by
    simp [finRead, parL, xL, yL, aL, bL, inL, AnswerReduction.res, X9, X8, X7, X6, X5, X4, X3, X2,
      X1, X0, encode_prod, readParams_encode, Program.readBits_encode, readBL_encode]
  rw [encode_data, comp_apply, hfin, R.lpFinal_eq lam mu sigma n V qx qy aR bR P B] at r10
  exact AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r1 <|
    AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r2 <|
    AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r3 <|
    AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hu) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r4 <|
    AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r5 <|
    AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hc) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r6 <|
    AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hpf) <|
        seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r7 <|
    AnswerReduction.ParRoutine.seq_runs (by
      exact seqProg_closed (AnswerReduction.stg_closed _ hpf) (PolyTimeFun.closed _)) r8 <|
    AnswerReduction.ParRoutine.seq_runs (PolyTimeFun.closed _) r9 ⟨t10, r10⟩

/-- **The processor outputs the presented answer-reduced game's constraints** at every pair of
detyped questions. -/
theorem lpD_lpIs {ℓ' : ℕ} (P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n +
      D ((R.fam lam mu sigma).j n) * (R.fam lam mu sigma).t n)) ℓ') (B : ℕ) :
    LpIs (R.lpD ℓ V.progs lam mu sigma) n (toBits (DeciderProgram.vectorEquiv _ qx))
      (toBits (DeciderProgram.vectorEquiv _ qy)) aR bR
      ((arPresented (R.d lam mu sigma n) ((R.fam lam mu sigma).dvd n)
        ((R.fam lam mu sigma).sel n) (R.L lam mu sigma n) (R.hLM lam mu sigma n) V n
        (R.circ lam mu sigma n V) (R.circ_wires lam mu sigma n V) P B).cons qx qy aR bR) := by
  obtain ⟨t, ht⟩ := R.lpCore_runs lam mu sigma n V qx qy aR bR P B
  exact ⟨_, _, hardcode_time (R.lpCore_closed ℓ) ht, Data.bitsListD_encode _⟩

end Run

/-! ## The output verifier -/

section Output

variable (R : ArRoutine) {ℓ : ℕ} (V : TailoredVerifier (ℓ + 1)) (lam mu sigma : ℕ)

/-- **The output tailored verifier of the answer reduction**: the answer-reduced sampler, the
answer-length calculator and the linear-constraints processor. -/
def output : TailoredVerifier (max (ℓ + 1) 3 + 2) where
  sampler := R.toLd.arSampler lam mu sigma V.sampler
  len := R.lenD lam mu sigma
  lp := R.lpD ℓ V.progs lam mu sigma

/-- **The output verifier meets the presented answer-reduced game** at every index, along the
numbering of the detyped questions. -/
theorem arMeets_output (n B : ℕ) :
    ArMeets (R.d lam mu sigma n) ((R.fam lam mu sigma).dvd n) ((R.fam lam mu sigma).sel n)
      (R.L lam mu sigma n) (R.hLM lam mu sigma n) V n (R.circ lam mu sigma n V)
      (R.circ_wires lam mu sigma n V) (fun _ u => arCl ((R.fam lam mu sigma).sel n) n V u) B
      (R.output V lam mu sigma) (R.toLd.qe lam mu sigma V.sampler n) where
  dist_eq x y := dist_arPresented R.toLd lam mu sigma x y
  lenR_eq x := (R.lenD_presented lam mu sigma x).1
  lenL_eq x := (R.lenD_presented lam mu sigma x).2
  cons_eq x y aR bR := R.lpD_lpIs lam mu sigma n V x y aR bR _ B

/-- **Completeness of the output verifier**, under the honest PCPs' hypotheses, for a degree
`d ≥ 17` and an answer bound at least the types' lengths. -/
theorem hasPerfectZPC_output (n B : ℕ) {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp (R.L lam mu sigma n) V n prm (R.circ lam mu sigma n V) Tt)
    (hd : 17 ≤ R.d lam mu sigma n)
    (hB : ∀ u, len ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
      (R.L lam mu sigma n) u ≤ B) (hV : V.HasPerfectZPC n) :
    (R.output V lam mu sigma).HasPerfectZPC n :=
  hasPerfectZPC_of_arMeets (R.arMeets_output V lam mu sigma n B) H hd
    (arSampler_arCl ((R.fam lam mu sigma).sel n) n V) (by omega) hB hV

/-- **Soundness of the output verifier**: if its `n`-th game has `val* > 1 - ε`, then
`val*(𝒱_n) ≥ 1 - 24 √(errAR (16⁹ ε))`, once the field is large enough. -/
theorem valStar_sound_output (n B : ℕ) {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp (R.L lam mu sigma n) V n prm (R.circ lam mu sigma n V) Tt)
    (hd : 1 ≤ R.d lam mu sigma n)
    (hB : ∀ u, len ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
      (R.L lam mu sigma n) u ≤ B)
    (hq : 2 * ((2 ^ (R.fam lam mu sigma).j n + 1) * R.d lam mu sigma n) ≤
      Fintype.card (Fq ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).ht n)))
    (hτ : 2 * ((R.L lam mu sigma n).m * chkDeg 5 (R.d lam mu sigma n)) ≤
      Fintype.card (Fq ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).ht n)))
    {ε : ℝ} (hε : 0 < ε) (hv : 1 - ε < (R.output V lam mu sigma).valStar n) :
    1 - 24 * √(errAR ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).ht n)
      ((R.fam lam mu sigma).j n) (R.d lam mu sigma n) (R.L lam mu sigma n) (16 ^ 9 * ε)) ≤
      V.valStar n :=
  valStar_sound_of_arMeets (R.arMeets_output V lam mu sigma n B) H hd
    (arSampler_arCl ((R.fam lam mu sigma).sel n) n V) (by omega) hB hq hτ hε hv

end Output

end ArRoutine

end MIPRE.Tailored.AnsRed.Typed

end
