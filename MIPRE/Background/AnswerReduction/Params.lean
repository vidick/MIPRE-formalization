/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.PcpSampler
import MIPRE.Foundations.Pipeline.UnaryArith
import MIPRE.Foundations.Pipeline.AnswerReduction

/-!
# The PCP parameters of answer reduction, and the routine computing them

Piece AR-3d of `planning/answer-reduction.md`. At index `n`, with the parameters `(λ, μ, σ)`,
answer reduction runs the PCP of a `PcpDecider` at `pcpparams(n, T, Q, σ)` with
`Q = (λn + 1)^μ` the input sampler's budget and `T = 2^Q` the input decider's (`arPar`); `m` and
`m'` are powers of two, so this is a `PcpFamily` (`family`).

The routine `parProg` computes the family's parameters `pd n` from `n`, with `(λ, μ, σ)`
hardcoded: `λ` and `n` in unary, `Q` by a power loop, `T` from `Q`, the PCP's parameters by its
parameter program, and `k, m, s` in unary. `parProg_runs` is its correctness.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg

variable (PD : PcpDecider) (lam mu sigma : ℕ)

/-- The input sampler's budget `Q = (λn + 1)^μ`. -/
abbrev arQ (n : ℕ) : ℕ := (lam * n + 1) ^ mu

/-- **The PCP parameters at index `n`**: `pcpparams(n, 2^Q, Q, σ)`. -/
def arPar (n : ℕ) : PcpParams := PD.params n (AnswerReduction.inAns lam mu n) (arQ lam mu n) sigma

theorem arPar_hk (n : ℕ) : 1 ≤ (arPar PD lam mu sigma n).k :=
  (PD.odd_k _ _ _ _).pos

theorem pow_size_sub_one {m : ℕ} (h : ∃ j, m = 2 ^ j) : m = 2 ^ (m.size - 1) := by
  obtain ⟨j, rfl⟩ := h
  rw [Nat.size_pow, Nat.add_sub_cancel]

theorem size_sub_one_le {m k : ℕ} (h : ∃ j, m = 2 ^ j) (hd : m ∣ 2 ^ k) : m.size - 1 ≤ k := by
  rw [pow_size_sub_one h] at hd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd

/-- **The family of PCP parameters** of answer reduction. -/
def family : PcpFamily where
  par := arPar PD lam mu sigma
  hk := arPar_hk PD lam mu sigma
  jm n := (arPar PD lam mu sigma n).m.size - 1
  jm' n := (arPar PD lam mu sigma n).m'.size - 1
  m_eq n := pow_size_sub_one (PD.m_isPow _ _ _ _)
  m'_eq n := pow_size_sub_one (PD.m'_isPow _ _ _ _)
  jm_le n := size_sub_one_le (PD.m_isPow _ _ _ _) (PD.m_dvd_q _ _ _ _)
  jm'_le n := size_sub_one_le (PD.m'_isPow _ _ _ _) (PD.m'_dvd_q _ _ _ _)

/-! ## The routine -/

namespace ParRoutine

/-- The hardcoded `(λ, μ, σ)`. -/
def hD : PolyTimeFun Data Data := treeHead

/-- Stage 1: `λ` in unary. The input is `X₀ = (λ, μ, σ), n`. -/
def pre1 : PolyTimeFun Data Data := ap₂ treePair (treeHead.comp hD) (PolyTimeFun.id Data)
def post1 : PolyTimeFun (Data × Data) Data := ap₂ treePair snd fst

/-- Stage 2: `n` in unary; then the base `λn + 1` and the exponent `μ`. -/
def pre2 : PolyTimeFun Data Data := ap₂ treePair (treeTail.comp treeTail) (PolyTimeFun.id Data)
def post2 : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (ap₂ treePair (encoded.comp ((const ()).cons
      (LowDegree.DegreeArithmetic.mulUnaryProg.comp ((readUnary.comp (treeHead.comp fst)).pair
        (readUnary.comp snd)))))
      (treeHead.comp (treeTail.comp (treeHead.comp (treeTail.comp fst)))))
    (treeTail.comp fst)

/-- Stage 3: `Q = (λn + 1)^μ`, then `T = 2^Q` and the PCP's parameters `(k, m, s)`. -/
def pre3 : PolyTimeFun Data Data := PolyTimeFun.id Data
def post3 : PolyTimeFun (Data × Data) Data :=
  let Q := readUnary.comp snd
  let T := bitsValue.comp (ap₂ append ((map (const false)).comp Q) (const [true]))
  let n := readNat.comp (treeTail.comp fst)
  let σ := readNat.comp (treeTail.comp (treeTail.comp (treeHead.comp fst)))
  encoded.comp (PD.paramsProg.comp (n.pair (T.pair ((addUnary.comp ((const 0).pair Q)).pair σ))))

/-- Stages 4, 5, 6: `k`, `m`, `s` in unary. -/
def pre4 : PolyTimeFun Data Data := ap₂ treePair treeHead (PolyTimeFun.id Data)
def pre5 : PolyTimeFun Data Data :=
  ap₂ treePair (treeHead.comp (treeTail.comp treeTail)) (PolyTimeFun.id Data)
def pre6 : PolyTimeFun Data Data :=
  ap₂ treePair (treeTail.comp (treeTail.comp (treeTail.comp treeTail))) (PolyTimeFun.id Data)
def postKeep : PolyTimeFun (Data × Data) Data := ap₂ treePair snd fst

/-- `log₂` of a power of two, from its binary encoding, in unary. -/
def logU : PolyTimeFun ℕ Unary := tail.comp ((map (const ())).comp (readBits.comp encoded))

theorem logU_apply (m : ℕ) : logU m = unary (m.size - 1) := by
  change (List.map (fun _ => ()) (readBits (encode m.bits))).tail = _
  rw [readBits_encode, List.map_const', List.tail_replicate, Nat.size_eq_bits_len]
  rfl

/-- `c` copies of a unary numeral. -/
def timesU : ℕ → PolyTimeFun Unary Unary
  | 0 => const []
  | c + 1 => ap₂ append (timesU c) (PolyTimeFun.id Unary)

theorem timesU_apply (c : ℕ) (u : Unary) : timesU c u = unary (c * u.length) := by
  induction c with
  | zero => simp [timesU, unary]
  | succ c ih =>
    simp only [timesU, ap₂_apply, append_apply, ih, id_apply]
    conv_lhs => rw [← unary_length u, ← unary_add]
    rw [length_unary]
    congr 1
    ring

/-- Stage 6's post-processing: the parameters `pd n`. The context is `(m, k, (k, m, s))` in unary
and binary, the answer `s` in unary. -/
def post6 : PolyTimeFun (Data × Data) Data :=
  let us := readUnary.comp snd
  let um := readUnary.comp (treeHead.comp fst)
  let uk := readUnary.comp (treeHead.comp (treeTail.comp fst))
  let m := readNat.comp (treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp fst))))
  let um' := ap₂ append (ap₂ append ((timesU 5).comp um) (const (unary 5))) us
  let jm := logU.comp m
  let jm' := logU.comp (addUnary.comp ((const 0).pair um'))
  let d (c : ℕ) : PolyTimeFun (Data × Data) Desc :=
    if c < 5 then ((timesU c).comp um).pair (um.pair (jm.pair (const (unary c))))
    else (const []).pair (um'.pair (jm'.pair (const (unary c))))
  encoded.comp (uk.pair (um'.pair (listOf ((List.range 6).map d))))

/-- **The routine's core**, on `((λ, μ, σ), n)`. -/
def core : Prog :=
  seqProg (stageProg pre1 toUnaryProg post1) <|
  seqProg (stageProg pre2 toUnaryProg post2) <|
  seqProg (stageProg pre3 powProg (post3 PD)) <|
  seqProg (stageProg pre4 toUnaryProg postKeep) <|
  seqProg (stageProg pre5 toUnaryProg postKeep) (stageProg pre6 toUnaryProg post6)

theorem core_closed : (core PD).WellScoped 1 :=
  seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
  seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
  seqProg_closed (stageProg_closed _ powProg_closed _) <|
  seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
  seqProg_closed (stageProg_closed _ toUnaryProg_closed _) (stageProg_closed _ toUnaryProg_closed _)

theorem seq_runs {p q : Prog} (hq : q.WellScoped 1) {x y r : Data}
    (hp : ∃ t, p.Runs x y t) (hq' : ∃ t, q.Runs y r t) : ∃ t, (seqProg p q).Runs x r t := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq'
  exact ⟨_, seqProg_runs hq hs ht⟩

theorem bitsVal_pow (Q : ℕ) : bitsVal (List.replicate Q false ++ [true]) = 2 ^ Q := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    rw [List.replicate_succ, List.cons_append, bitsVal_cons, ih, Nat.bit_val, pow_succ]
    simp [Bool.toNat]
    ring

theorem map_const_toFun {α β : Type*} [SizedEncoding α] [SizedEncoding β] (b : β)
    (l : List α) : l.map (const b : PolyTimeFun α β).toFun = List.replicate l.length b := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih, List.length_cons, List.replicate_succ]; rfl

theorem unary_mul_succ (a b : ℕ) :
    () :: unary (a * b) = unary (a * b + 1) := by
  simp [unary, List.replicate_succ]

end ParRoutine

open ParRoutine in
/-- **The parameter routine** of answer reduction, with `(λ, μ, σ)` hardcoded. -/
def parProg : Prog := hardcode (core PD) (encode (lam, mu, sigma))

theorem parProg_closed : (parProg PD lam mu sigma).WellScoped 1 :=
  hardcode_wellScoped (ParRoutine.core_closed PD) _

open ParRoutine in
theorem post6_apply (n : ℕ) :
    post6 (Data.cons (encode (unary (arPar PD lam mu sigma n).m))
        (Data.cons (encode (unary (arPar PD lam mu sigma n).k))
          (encode ((arPar PD lam mu sigma n).k, (arPar PD lam mu sigma n).m,
            (arPar PD lam mu sigma n).s))),
      encode (unary (arPar PD lam mu sigma n).s)) = (family PD lam mu sigma).pd n := by
  set P := arPar PD lam mu sigma n with hP
  have hm' : unary (5 * P.m) ++ unary 5 ++ unary P.s = unary P.m' := by
    rw [← unary_add, ← unary_add]; rfl
  simp only [post6, comp_apply, pair_apply, fst_apply, snd_apply, treeHead_cons, treeTail_cons,
    encode_prod, readUnary_encode, readNat_encode, ap₂_apply, append_apply, const_apply,
    timesU_apply, length_unary, hm', logU_apply, addUnary_apply, listOf_apply, encoded_apply]
  simp only [PcpFamily.pd, family, PcpFamily.desc]
  congr 3
  simp [List.range_succ, List.ofFn_succ, hP, timesU_apply, logU_apply, readNat_encode, unary,
    PcpFamily.desc]
  have hs : (arPar PD lam mu sigma n).m' = 5 * (arPar PD lam mu sigma n).m +
      ((arPar PD lam mu sigma n).s + 1 + 1 + 1 + 1 + 1) := by simp only [PcpParams.m']; ring
  refine ⟨?_, by rw [hs]⟩
  rw [hs, List.replicate_add]
  simp [List.replicate_succ]

open ParRoutine in
/-- **The routine computes the parameters** of the family. -/
theorem parProg_runs (n : ℕ) :
    ∃ t, (parProg PD lam mu sigma).Runs (encode n) ((family PD lam mu sigma).pd n) t := by
  set P := arPar PD lam mu sigma n with hP
  let X0 : Data := .cons (encode (lam, mu, sigma)) (encode n)
  obtain ⟨t1, h1⟩ := toUnaryProg_runs lam
  obtain ⟨s1, S1⟩ := stageProg_runs pre1 toUnaryProg_closed post1 X0 (encode lam) X0 _ t1 rfl h1
  let X1 : Data := .cons (encode (unary lam)) X0
  obtain ⟨t2, h2⟩ := toUnaryProg_runs n
  obtain ⟨s2, S2⟩ := stageProg_runs pre2 toUnaryProg_closed post2 X1 (encode n) X1 _ t2 rfl h2
  have hpost2 : post2 (X1, encode (unary n)) =
      .cons (encode (unary (lam * n + 1), mu)) X0 := by
    simp only [post2, ap₂_apply, treePair_apply, comp_apply, fst_apply, snd_apply,
      treeHead_cons, treeTail_cons, readUnary_encode, cons_apply, const_apply, pair_apply,
      LowDegree.DegreeArithmetic.mulUnaryProg_apply, length_unary, encoded_apply,
      unary_mul_succ, X1, X0, encode_prod]
  rw [hpost2] at S2
  obtain ⟨t3, h3⟩ := powProg_runs (unary (lam * n + 1)) mu
  obtain ⟨s3, S3⟩ := stageProg_runs pre3 powProg_closed (post3 PD) _ _ X0 _ t3 rfl h3
  have hpost3 : post3 PD (X0, encode (unary ((unary (lam * n + 1)).length ^ mu))) =
      encode (P.k, P.m, P.s) := by
    simp only [post3, comp_apply, pair_apply, fst_apply, snd_apply, treeHead_cons, treeTail_cons,
      readUnary_encode, map_apply, ap₂_apply, append_apply, const_apply, readNat_encode,
      addUnary_apply, length_unary, encoded_apply, X0, encode_prod]
    rw [map_const_toFun, length_unary, PolyTimeFun.bitsValue_apply, bitsVal_pow, zero_add,
      PD.paramsProg_eq]
    rfl
  rw [hpost3] at S3
  let X3 : Data := encode (P.k, P.m, P.s)
  obtain ⟨t4, h4⟩ := toUnaryProg_runs P.k
  obtain ⟨s4, S4⟩ := stageProg_runs pre4 toUnaryProg_closed postKeep X3 (encode P.k) X3 _ t4
    rfl h4
  let X4 : Data := .cons (encode (unary P.k)) X3
  obtain ⟨t5, h5⟩ := toUnaryProg_runs P.m
  obtain ⟨s5, S5⟩ := stageProg_runs pre5 toUnaryProg_closed postKeep X4 (encode P.m) X4 _ t5
    rfl h5
  let X5 : Data := .cons (encode (unary P.m)) X4
  obtain ⟨t6, h6⟩ := toUnaryProg_runs P.s
  obtain ⟨s6, S6⟩ := stageProg_runs pre6 toUnaryProg_closed post6 X5 (encode P.s) X5 _ t6
    rfl h6
  rw [post6_apply] at S6
  obtain ⟨t, h⟩ := seq_runs (seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
      seqProg_closed (stageProg_closed _ powProg_closed _) <|
      seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
      seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
        (stageProg_closed _ toUnaryProg_closed _)) ⟨_, S1⟩ <|
    seq_runs (seqProg_closed (stageProg_closed _ powProg_closed _) <|
      seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
      seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
        (stageProg_closed _ toUnaryProg_closed _)) ⟨_, S2⟩ <|
    seq_runs (seqProg_closed (stageProg_closed _ toUnaryProg_closed _) <|
      seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
        (stageProg_closed _ toUnaryProg_closed _)) ⟨_, S3⟩ <|
    seq_runs (seqProg_closed (stageProg_closed _ toUnaryProg_closed _)
        (stageProg_closed _ toUnaryProg_closed _)) ⟨_, S4⟩ <|
    seq_runs (stageProg_closed _ toUnaryProg_closed _) ⟨_, S5⟩ ⟨_, S6⟩
  exact ⟨_, hardcode_time (core_closed PD) h⟩

end MIPRE.AnswerReduction

end
