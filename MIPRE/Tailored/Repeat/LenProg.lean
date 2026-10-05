/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.Calls
public import MIPRE.Tailored.Repeat.Lists
public import MIPRE.Tailored.Repeat.Verifier
public import MIPRE.Foundations.CL.DetypingProgParse
public import MIPRE.Foundations.Halting.Arith

@[expose] public section

/-!
# The repeated answer-length calculator

The answer-length calculator of the repeated tailored verifier (issue #280, P2b), on
`(n, x, κ)`, with the input sampler `S̄` and calculator `L̄` and the parameters `(λ, τ)` stored:

1. ask `S̄` for the dimension `s = s(n)`, and put it in unary;
2. compute `k = k(n) = Repetition.reps λ τ n` in unary (`dimProg` on `1`, then to unary);
3. cut `x` into its `k` blocks of `s` bits, and run `L̄` on `(n, xᵢ, κ')` for every block and
   both kinds `κ'`;
4. output the concatenation of the outputs at the kind `κ`, whose length is the sum of the
   coordinates' lengths.

It runs `L̄` on both kinds so that it halts only where every coordinate has both its lengths
(`RepSpec.good_of_len`). Every stage between the calls is a `PolyTimeFun`; the calls go through
`Calls.mapCall`.
-/

namespace MIPRE.Tailored.RepProg

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL Calls Polynomial

theorem rawList_eq_spineList : ∀ d : Data, Detyping.Program.rawList d = spineList d
  | .nil => rfl
  | .cons a b => by simp [Detyping.Program.rawList, rawList_eq_spineList b]

/-! ## The stages -/

/-- The stored data of the calculator: `(S̄, L̄, λ, τ)`. -/
abbrev LenPar : Type := Prog × Prog × ℕ × ℕ

/-- The input of the core: the stored data and `(n, d)`. -/
abbrev LenIn : Type := LenPar × ℕ × Data

/-- The dimension query `(n, dimension)`. -/
noncomputable def dimQueryF {ι : Type} [SizedEncoding ι] (nF : PolyTimeFun ι ℕ) :
    PolyTimeFun ι Data :=
  Detyping.Program.encoded.comp (nF.pair (const CL.Sampler.Query.dimension))

/-- Stage 1: the call to `S̄` on the dimension query. -/
noncomputable def lenA : PolyTimeFun LenIn (LenIn × (Prog × List Data)) :=
  (PolyTimeFun.id _).pair ((fst.comp fst).pair (listOf [dimQueryF (fst.comp snd)]))

@[simp] theorem lenA_apply (a : LenIn) :
    lenA a = (a, (a.1.1, [encode (a.2.1, CL.Sampler.Query.dimension)])) := rfl

/-- Stage 2: read the dimension. -/
noncomputable def lenB : PolyTimeFun (LenIn × List Data) (LenIn × ℕ) :=
  fst.pair (Detyping.Program.readNat.comp ((headD Data.nil).comp snd))

@[simp] theorem lenB_apply (p : LenIn × List Data) :
    lenB p = (p.1, Detyping.Program.readNat (p.2.headD .nil)) := rfl

/-- Stage 3: the input of `dimProg` computing `k = 2^{τ(|λ| + |n|)} · 1`. -/
noncomputable def lenC : PolyTimeFun (LenIn × Unary) ((LenIn × Unary) × (ℕ × ℕ × ℕ × ℕ)) :=
  (PolyTimeFun.id _).pair ((const 1).pair ((fst.comp (snd.comp (snd.comp fst))).comp fst |>.pair
    ((fst.comp (snd.comp fst)).pair ((snd.comp (snd.comp (snd.comp fst))).comp fst))))

@[simp] theorem lenC_apply (a : LenIn) (us : Unary) :
    lenC (a, us) = ((a, us), (1, a.1.2.2.1, a.2.1, a.1.2.2.2)) := rfl

/-- The query to `L̄` at a block and a kind: `(n, xᵢ, κ)`. -/
noncomputable def lenQueryF (κ : Bool) : PolyTimeFun (BitStr × ℕ) Data :=
  Detyping.Program.encoded.comp (snd.pair (fst.pair (const κ)))

@[simp] theorem lenQueryF_apply (κ : Bool) (p : BitStr × ℕ) :
    lenQueryF κ p = encode (p.2, p.1, κ) := rfl

/-- The queries to `L̄`: every block at `false`, then every block at `true`. -/
def lenQueries (n : ℕ) (bl : List BitStr) : List Data :=
  bl.map (fun xi => encode (n, xi, false)) ++ bl.map (fun xi => encode (n, xi, true))

/-- The question and the kind read off the datum `d = (x, κ)`. -/
noncomputable def readQ (d : Data) : BitStr := Detyping.Program.readBits (treeHead d)

noncomputable def readK (d : Data) : Bool :=
  Detyping.Program.rawTruthProg (treeTail d)

/-- Stage 4: the blocks of `x` and the queries to `L̄`; the context is `(κ, k)`. -/
noncomputable def lenD : PolyTimeFun ((LenIn × Unary) × Unary) ((Bool × Unary) × (Prog × List Data)) :=
  congr
    (((Detyping.Program.rawTruthProg.comp (treeTail.comp
        (snd.comp (snd.comp (fst.comp fst))))).pair snd).pair
      ((fst.comp (snd.comp (fst.comp (fst.comp fst)))).pair
        (append.comp
          (((mapWith (lenQueryF false)).comp ((blocksF.comp
              (((Detyping.Program.readBits.comp (treeHead.comp
                (snd.comp (snd.comp (fst.comp fst))))).pair (snd.comp fst)).pair snd)).pair
              (fst.comp (snd.comp (fst.comp fst))))).pair
            ((mapWith (lenQueryF true)).comp ((blocksF.comp
              (((Detyping.Program.readBits.comp (treeHead.comp
                (snd.comp (snd.comp (fst.comp fst))))).pair (snd.comp fst)).pair snd)).pair
              (fst.comp (snd.comp (fst.comp fst)))))))))
    (fun p => ((readK p.1.1.2.2, p.2), (p.1.1.1.2.1,
      lenQueries p.1.1.2.1 (blocks (readQ p.1.1.2.2) p.1.2.length p.2.length))))
    (by
      rintro ⟨⟨⟨⟨sp, lp, lam, tau⟩, n, d⟩, us⟩, uk⟩
      simp [lenQueries, readQ, readK])

@[simp] theorem lenD_apply (p : (LenIn × Unary) × Unary) :
    lenD p = ((readK p.1.1.2.2, p.2), (p.1.1.1.2.1,
      lenQueries p.1.1.2.1 (blocks (readQ p.1.1.2.2) p.1.2.length p.2.length))) :=
  congr_apply _ _ _ _

/-- The output: the concatenation of the outputs at the kind `κ`. -/
def lenOut (κ : Bool) (k : ℕ) (rs : List Data) : List Data :=
  ((if κ then rs.drop k else rs.take k).map Detyping.Program.rawList).flatten

/-- Stage 5: the output. -/
noncomputable def lenE : PolyTimeFun ((Bool × Unary) × List Data) (List Data) :=
  congr (flattenF.comp ((map (ofEncodeEq Detyping.Program.rawList
      Detyping.Program.encode_rawList)).comp
    (PolyTimeFun.ite (fst.comp fst) (drop.comp (snd.pair (snd.comp fst)))
      (take.comp (snd.pair (snd.comp fst))))))
    (fun p => lenOut p.1.1 p.1.2.length p.2) (by
      rintro ⟨⟨κ, uk⟩, rs⟩
      cases κ <;> rfl)

@[simp] theorem lenE_apply (p : (Bool × Unary) × List Data) :
    lenE p = lenOut p.1.1 p.1.2.length p.2 := congr_apply _ _ _ _

/-! ## The program -/

/-- **The core of the repeated answer-length calculator**, on `((S̄, L̄, λ, τ), (n, d))`. -/
noncomputable def lenCore (univ : Prog) : Prog :=
  seq lenA.code (seq (withCtx (mapCall univ)) (seq lenB.code (seq (withCtx toUnaryProg)
    (seq lenC.code (seq (withCtx dimProg) (seq (withCtx toUnaryProg)
      (seq lenD.code (seq (withCtx (mapCall univ)) lenE.code))))))))

theorem lenCore_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (lenCore univ).WellScoped 1 :=
  seq_wellScoped lenA.closed (seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU))
    (seq_wellScoped lenB.closed (seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped)
      (seq_wellScoped lenC.closed (seq_wellScoped (withCtx_wellScoped dimProg_wellScoped)
        (seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped)
          (seq_wellScoped lenD.closed (seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU))
            lenE.closed))))))))

/-! ## The run -/

@[simp] theorem encode_list_data (l : List Data) : (encode l : Data) = list l := by
  rw [encode_list_eq_list]
  exact congrArg list (List.map_id l)

/-- The queries of the calculator to `L̄` at `(n, d)`, with dimension `s` and `k` coordinates. -/
noncomputable def lenQs (n : ℕ) (d : Data) (s k : ℕ) : List Data :=
  lenQueries n (blocks (readQ d) s k)

/-- The cost of the core, stage by stage, with the dimension query of cost at most `Td`, the
calls to `L̄` of cost at most `T`, and `Z` bounding the queries and results of the last loop. -/
noncomputable def lenCoreCost (sp lp : Prog) (lam tau n : ℕ) (d : Data) (s k Td T Z : ℕ)
    (rs : List Data) : ℕ :=
  let a : LenIn := ((sp, lp, lam, tau), n, d)
  let qd : Data := encode (n, CL.Sampler.Query.dimension)
  let qs := lenQs n d s k
  lenA.timeBound.eval (esize a) +
    ((encode a : Data).size + (Data.cons (encode sp) (list [qd])).size +
      mapCallCost 1 Td (encode sp : Data).size
        ((list [qd]).size + (list [(encode s : Data)]).size + 1) + 5) +
    lenB.timeBound.eval (esize (a, [(encode s : Data)])) +
    ((encode a : Data).size + (encode s : Data).size + toUnaryCost s + 5) +
    lenC.timeBound.eval (esize (a, unary s)) +
    ((encode (a, unary s) : Data).size + (encode ((1 : ℕ), lam, n, tau) : Data).size +
      (dimCost tau (Nat.size lam + Nat.size n) (esize lam) (esize n) (esize (1 : ℕ)) + 3) + 5) +
    ((encode (a, unary s) : Data).size + (encode k : Data).size + toUnaryCost k + 5) +
    lenD.timeBound.eval (esize ((a, unary s), unary k)) +
    ((encode (readK d, unary k) : Data).size + (Data.cons (encode lp) (list qs)).size +
      mapCallCost qs.length T (encode lp : Data).size Z + 5) +
    lenE.timeBound.eval (esize ((readK d, unary k), rs)) + 9

/-- **The run of the core**, from runs of the calls: the dimension query answered by `s`, and the
calls to `L̄` answered by `f`. -/
theorem lenCore_runsLe {univ : Prog} (hU : univ.WellScoped 1) (sp lp : Prog) (lam tau n : ℕ)
    (d : Data) (s : ℕ) {Td : ℕ}
    (hdim : RunsLe univ (.cons (encode sp) (encode (n, CL.Sampler.Query.dimension))) (encode s) Td)
    (f : Data → Data) (T Z : ℕ)
    (hf : ∀ q ∈ lenQs n d s (Repetition.reps lam tau n), RunsLe univ (.cons (encode lp) q) (f q) T)
    (hZ : (list (lenQs n d s (Repetition.reps lam tau n))).size +
      (list ((lenQs n d s (Repetition.reps lam tau n)).map f)).size + 1 ≤ Z) :
    RunsLe (lenCore univ) (encode (((sp, lp, lam, tau) : LenPar), n, d))
      (encode (lenOut (readK d) (Repetition.reps lam tau n)
        ((lenQs n d s (Repetition.reps lam tau n)).map f)))
      (lenCoreCost sp lp lam tau n d s (Repetition.reps lam tau n) Td T Z
        ((lenQs n d s (Repetition.reps lam tau n)).map f)) := by
  -- stage 1, the dimension query
  have h1 := RunsLe.withCtx (mapCall_wellScoped hU) (encode (((sp, lp, lam, tau) : LenPar), n, d))
    (RunsLe.mapCall hU (encode sp) [encode (n, CL.Sampler.Query.dimension)] (fun _ => encode s) Td
      _ (by simpa using hdim) le_rfl)
  -- stage 2, the dimension in unary
  obtain ⟨tu, htu, hu⟩ := toUnaryProg_runs s
  have h2 := RunsLe.withCtx toUnaryProg_wellScoped (encode (((sp, lp, lam, tau) : LenPar), n, d))
    ⟨tu, htu, hu⟩
  rw [← encode_unary] at h2
  -- stage 3, `k` in unary
  obtain ⟨tk, htk, hk⟩ := Repeat.dimProg_runs_encode lam tau n 1
  rw [mul_one] at hk
  have h3 := RunsLe.withCtx dimProg_wellScoped
    (encode (((((sp, lp, lam, tau) : LenPar), n, d) : LenIn), unary s))
    (p := dimProg) (b := encode ((1 : ℕ), lam, n, tau)) ⟨tk, htk, hk⟩
  obtain ⟨tu', htu', hu'⟩ := toUnaryProg_runs (Repetition.reps lam tau n)
  have h4 := RunsLe.withCtx toUnaryProg_wellScoped
    (encode (((((sp, lp, lam, tau) : LenPar), n, d) : LenIn), unary s)) ⟨tu', htu', hu'⟩
  rw [← encode_unary] at h4
  -- stage 4, the calls to `L̄`
  have h5 := RunsLe.withCtx (mapCall_wellScoped hU) (encode (readK d, unary (Repetition.reps lam tau n)))
    (RunsLe.mapCall hU (encode lp) (lenQs n d s (Repetition.reps lam tau n)) f T Z hf hZ)
  have hA := RunsLe.pure lenA (((sp, lp, lam, tau) : LenPar), n, d)
  have hB := RunsLe.pure lenB ((((sp, lp, lam, tau) : LenPar), n, d), [(encode s : Data)])
  have hC := RunsLe.pure lenC ((((sp, lp, lam, tau) : LenPar), n, d), unary s)
  have hD := RunsLe.pure lenD (((((sp, lp, lam, tau) : LenPar), n, d), unary s),
    unary (Repetition.reps lam tau n))
  have hE := RunsLe.pure lenE ((readK d, unary (Repetition.reps lam tau n)),
    (lenQs n d s (Repetition.reps lam tau n)).map f)
  simp only [lenA_apply, lenB_apply, lenC_apply, lenD_apply, lenE_apply, encode_prod,
    encode_list_data, Detyping.Program.readNat_encode, List.headD_cons, length_unary] at hA hB hC hD hE
  simp only [encode_prod, encode_list_data, List.map_cons, List.map_nil] at h1 h2 h3 h4 h5
  have wE := lenE.closed
  have w9 := withCtx_wellScoped (mapCall_wellScoped hU)
  have w8 := seq_wellScoped w9 wE
  have w7 := seq_wellScoped lenD.closed w8
  have w6 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w7
  have w5 := seq_wellScoped (withCtx_wellScoped dimProg_wellScoped) w6
  have w4 := seq_wellScoped lenC.closed w5
  have w3 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w4
  have w2 := seq_wellScoped lenB.closed w3
  have w1 := seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU)) w2
  have c9 := RunsLe.seq wE h5 hE
  have c8 := RunsLe.seq w8 hD c9
  have c7 := RunsLe.seq w7 h4 c8
  have c6 := RunsLe.seq w6 h3 c7
  have c5 := RunsLe.seq w5 hC c6
  have c4 := RunsLe.seq w4 h2 c5
  have c3 := RunsLe.seq w3 hB c4
  have c2 := RunsLe.seq w2 h1 c3
  have c1 := RunsLe.seq w1 hA c2
  simp only [encode_prod, encode_list_data]
  refine c1.mono ?_
  unfold lenCoreCost
  simp only [List.length_singleton, encode_prod, encode_list_data, List.map_cons, List.map_nil,
    toUnaryCost]
  omega

/-- **Inversion of the core**: when the dimension query is answered by `s`, a halting run ran
`L̄` on every query, and output the concatenation of the results at the kind `κ`. -/
theorem lenCore_inv {univ : Prog} (hU : univ.WellScoped 1) (sp lp : Prog) (lam tau n : ℕ)
    (d : Data) (s : ℕ) {td : ℕ}
    (hdim : univ.Runs (.cons (encode sp) (encode (n, CL.Sampler.Query.dimension))) (encode s) td)
    {r : Data} {t : ℕ}
    (h : (lenCore univ).Runs (encode (((sp, lp, lam, tau) : LenPar), n, d)) r t) :
    ∃ rs : List Data, List.Forall₂ (fun q r => ∃ t', univ.Runs (.cons (encode lp) q) r t')
        (lenQs n d s (Repetition.reps lam tau n)) rs ∧
      r = encode (lenOut (readK d) (Repetition.reps lam tau n) rs) := by
  have wE := lenE.closed
  have w9 := withCtx_wellScoped (mapCall_wellScoped hU)
  have w8 := seq_wellScoped w9 wE
  have w7 := seq_wellScoped lenD.closed w8
  have w6 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w7
  have w5 := seq_wellScoped (withCtx_wellScoped dimProg_wellScoped) w6
  have w4 := seq_wellScoped lenC.closed w5
  have w3 := seq_wellScoped (withCtx_wellScoped toUnaryProg_wellScoped) w4
  have w2 := seq_wellScoped lenB.closed w3
  have w1 := seq_wellScoped (withCtx_wellScoped (mapCall_wellScoped hU)) w2
  -- the dimension query
  obtain ⟨t₁, h⟩ := seq_pure_inv lenA w1 _ h
  simp only [lenA_apply, encode_prod, encode_list_data] at h
  obtain ⟨v, s₀, t₂, e₀, hm, h⟩ := seq_inv w2 h
  obtain ⟨r₁, tm, -, hm₁, rfl⟩ := withCtx_inv (mapCall_wellScoped hU) hm
  obtain ⟨rs₁, hrs₁, rfl⟩ := mapCall_inv hU _ _ hm₁
  obtain ⟨r₀, ⟨td', hd⟩, hnil⟩ : ∃ r₀, (∃ t', univ.Runs (.cons (encode sp)
      (encode (n, CL.Sampler.Query.dimension))) r₀ t') ∧ rs₁ = [r₀] := by
    rcases hrs₁ with _ | ⟨h₀, hrest⟩
    cases hrest
    exact ⟨_, h₀, rfl⟩
  subst hnil
  obtain ⟨rfl, -⟩ := Eval.deterministic hd hdim
  -- the dimension in unary
  obtain ⟨t₃, h⟩ := seq_pure_inv lenB w3 ((((sp, lp, lam, tau) : LenPar), n, d),
    [(encode s : Data)]) h
  simp only [lenB_apply, Detyping.Program.readNat_encode, List.headD_cons, encode_prod] at h
  obtain ⟨tu, -, hu⟩ := toUnaryProg_runs s
  obtain ⟨t₄, h⟩ := seq_det_inv w4 (withCtx_runs toUnaryProg_wellScoped
    (encode ((((sp, lp, lam, tau) : LenPar), n, d) : LenIn)) hu) h
  -- `k` in unary
  obtain ⟨t₅, h⟩ := seq_pure_inv lenC w5 ((((sp, lp, lam, tau) : LenPar), n, d), unary s)
    (by rw [← encode_unary] at h; exact h)
  simp only [lenC_apply, encode_prod] at h
  obtain ⟨tk, -, hk⟩ := Repeat.dimProg_runs_encode lam tau n 1
  rw [mul_one] at hk
  obtain ⟨t₆, h⟩ := seq_det_inv w6 (withCtx_runs dimProg_wellScoped
    (encode (((((sp, lp, lam, tau) : LenPar), n, d) : LenIn), unary s))
    (b := encode ((1 : ℕ), lam, n, tau)) hk) (by simpa only [encode_prod] using h)
  obtain ⟨tu', -, hu'⟩ := toUnaryProg_runs (Repetition.reps lam tau n)
  obtain ⟨t₇, h⟩ := seq_det_inv w7 (withCtx_runs toUnaryProg_wellScoped
    (encode (((((sp, lp, lam, tau) : LenPar), n, d) : LenIn), unary s)) hu') h
  -- the calls to `L̄`
  obtain ⟨t₈, h⟩ := seq_pure_inv lenD w8 (((((sp, lp, lam, tau) : LenPar), n, d), unary s),
    unary (Repetition.reps lam tau n))
    (by rw [← encode_unary] at h; exact h)
  simp only [lenD_apply, encode_prod, encode_list_data, length_unary] at h
  obtain ⟨v, s₉, t₉, e₉, hm, h⟩ := seq_inv wE h
  obtain ⟨r₂, tm₂, -, hm₂, rfl⟩ := withCtx_inv (mapCall_wellScoped hU) hm
  obtain ⟨rs, hrs, rfl⟩ := mapCall_inv hU _ _ hm₂
  refine ⟨rs, hrs, ?_⟩
  obtain ⟨tE, -, hE⟩ := lenE.computes ((readK d, unary (Repetition.reps lam tau n)), rs)
  have := (Eval.deterministic h hE).1
  simpa using this

/-! ## The calculator -/

/-- The program of the repeated answer-length calculator: the core with `(S̄, L̄, λ, τ)` stored. -/
noncomputable def repLenProg (sp lp : Prog) (lam tau : ℕ) : Prog :=
  hardcode (lenCore selfUniversal.univ) (encode ((sp, lp, lam, tau) : LenPar))

/-- **The repeated answer-length calculator.** -/
noncomputable def repLen {ℓ : ℕ} (S : CL.Sampler ℓ) (L : Decider) (lam tau : ℕ) : Decider :=
  ⟨repLenProg S.prog L.prog lam tau,
    hardcode_wellScoped (lenCore_wellScoped selfUniversal.closed) _⟩

theorem readQ_encode (x : BitStr) (κ : Bool) : readQ (encode (x, κ)) = x := by
  simp [readQ, encode_prod, Detyping.Program.readBits_encode]

theorem readK_encode (x : BitStr) (κ : Bool) : readK (encode (x, κ)) = κ := by
  simp only [readK, encode_prod, treeTail_cons]
  cases κ <;> rfl

/-- The `i`-th block of a question of `𝔽₂^{k s}` is the `i`-th chunk of its bit string. -/
theorem toBits_blockEquiv {k s : ℕ} (x : Fin (k * s) → 𝔽₂) (i : Fin k) :
    toBits (blockEquiv finProdFinEquiv x i) = Cost.Data.chunk s i (toBits x) := by
  have h := block_ofBits (k := k) (s := s) (toBits x) i
  rw [ofBits_toBits] at h
  change toBits (block finProdFinEquiv i x) = _
  rw [h, toBits_ofBits (length_chunk (by simp) i)]

theorem blocks_toBits {k s : ℕ} (x : Fin (k * s) → 𝔽₂) :
    blocks (toBits x) s k = List.ofFn fun i => toBits (blockEquiv finProdFinEquiv x i) := by
  simp only [blocks, toBits_blockEquiv]

theorem exists_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, _, h => by simp at h
  | a' :: _, b' :: _, .cons hab hrest, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨b', hab⟩
    · exact exists_of_forall₂ hrest a h

/-- The output at the queries of a list of blocks: the concatenation of the results at the
kind `κ`. -/
theorem lenOut_lenQueries (n : ℕ) (bl : List BitStr) (κ : Bool) (f : Data → Data) {k : ℕ}
    (hk : bl.length = k) :
    lenOut κ k ((lenQueries n bl).map f) =
      (bl.map fun xi => Detyping.Program.rawList (f (encode (n, xi, κ)))).flatten := by
  subst hk
  unfold lenOut lenQueries
  rw [List.map_append]
  cases κ
  · rw [ite_eq_right (by decide), List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
    simp [List.map_map, Function.comp_def]
  · rw [ite_eq_left rfl, List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp)]
    simp [List.map_map, Function.comp_def]

/-- The length of a list concatenated over the coordinates. -/
theorem length_flatten_map_ofFn {α : Type*} {k : ℕ} (g : Fin k → BitStr) (F : BitStr → List α) :
    ((List.ofFn g).map F).flatten.length = ∑ i, (F (g i)).length := by
  rw [List.length_flatten, List.map_map, List.map_ofFn, List.sum_ofFn]
  rfl

section Spec

variable {ℓ : ℕ} (V : TailoredVerifier ℓ) (lam tau : ℕ)

open TailoredVerifier

/-- The queries at a question of the repeated verifier are those of its coordinates. -/
theorem lenQs_toBits (n : ℕ) (x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) (κ : Bool) :
    lenQs n (encode (toBits x, κ)) (V.sampler.dim n) (K lam tau n) =
      lenQueries n (List.ofFn fun i => toBits (qc V lam tau n x i)) := by
  rw [lenQs, readQ_encode, blocks_toBits]

/-- The dimension query, through the universal machine. -/
theorem dim_univ (n : ℕ) : ∃ td, selfUniversal.univ.Runs
    (.cons (encode V.sampler.prog) (encode (n, CL.Sampler.Query.dimension)))
      (encode (V.sampler.dim n)) td := by
  obtain ⟨t, h⟩ := V.sampler.runs_dimension n
  obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
  exact ⟨t', h'⟩

/-- The run of the calculator from a run of its core. -/
theorem repLen_runs_of {n : ℕ} {d r : Data} {t : ℕ}
    (h : (lenCore selfUniversal.univ).Runs
      (encode (((V.sampler.prog, V.len.prog, lam, tau) : LenPar), n, d)) r t) :
    ∃ t', (repLen V.sampler V.len lam tau).prog.Runs (.cons (encode n) d) r t' :=
  ⟨_, hardcode_time (lenCore_wellScoped selfUniversal.closed) h⟩

/-- **`RepSpec.len_eq`**: at a question all of whose coordinates have their lengths, the
calculator outputs the sum of the coordinates' lengths. -/
theorem repLen_lenIs (n : ℕ) (x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂)
    (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i))) (κ : Bool) :
    LenIs (repLen V.sampler V.len lam tau) n (toBits x) κ
      (∑ i, V.lenOf n (toBits (qc V lam tau n x i)) κ) := by
  classical
  set qs := lenQs n (encode (toBits x, κ)) (V.sampler.dim n) (K lam tau n) with hqs
  let f : Data → Data := fun q =>
    if h : ∃ r t, selfUniversal.univ.Runs (.cons (encode V.len.prog) q) r t then h.choose else .nil
  have hf : ∀ i (b : Bool), ∃ t, V.len.prog.Runs (encode (n, toBits (qc V lam tau n x i), b))
      (f (encode (n, toBits (qc V lam tau n x i), b))) t := by
    intro i b
    obtain ⟨k, t, dd, hrun, -⟩ := hx i b
    obtain ⟨t', -, hu⟩ := selfUniversal.time_le _ _ _ _ hrun
    have hex : ∃ r t, selfUniversal.univ.Runs
        (.cons (encode V.len.prog) (encode (n, toBits (qc V lam tau n x i), b))) r t := ⟨_, _, hu⟩
    obtain ⟨t'', h''⟩ := selfUniversal.halts_of _ _ _ _ hex.choose_spec.choose_spec
    refine ⟨t'', ?_⟩
    simpa only [f, dite_eq_left hex] using h''
  have hmem : ∀ q ∈ qs, ∃ t, selfUniversal.univ.Runs (.cons (encode V.len.prog) q) (f q) t := by
    intro q hq
    rw [hqs, lenQs_toBits, lenQueries, List.mem_append, List.mem_map, List.mem_map] at hq
    rcases hq with ⟨xi, hxi, rfl⟩ | ⟨xi, hxi, rfl⟩ <;>
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hxi
      obtain ⟨t, h⟩ := hf i _
      obtain ⟨t', -, hu⟩ := selfUniversal.time_le _ _ _ _ h
      exact ⟨t', hu⟩
  obtain ⟨T, hT⟩ := Repeat.exists_uniform_bound qs
    (fun q t => selfUniversal.univ.Runs (.cons (encode V.len.prog) q) (f q) t) hmem
  obtain ⟨td, hd⟩ := dim_univ V n
  obtain ⟨t₀, -, h₀⟩ := lenCore_runsLe selfUniversal.closed V.sampler.prog V.len.prog lam tau n
    (encode (toBits x, κ)) (V.sampler.dim n) ⟨td, le_rfl, hd⟩ f T _ hT le_rfl
  obtain ⟨t₁, h₁⟩ := repLen_runs_of V lam tau h₀
  refine ⟨t₁, _, h₁, ?_⟩
  rw [encode_list_data, list, spineList_ofList, List.length_map, readK_encode, ← hqs, hqs,
    lenQs_toBits]
  rw [lenOut_lenQueries n _ κ f (by simp), length_flatten_map_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rawList_eq_spineList]
  obtain ⟨t, h⟩ := hf i κ
  exact LenIs.unique ⟨t, _, h, rfl⟩ (Classical.choose_spec (hx i κ) |> fun h' => by
    unfold lenOf; rw [dite_eq_left (hx i κ)]; exact h')

/-- **`RepSpec.good_of_len`**: the calculator halts only at questions all of whose coordinates
have their lengths. -/
theorem good_of_repLen (n : ℕ) (x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) (κ : Bool) (m : ℕ)
    (h : LenIs (repLen V.sampler V.len lam tau) n (toBits x) κ m) (i : Fin (K lam tau n)) :
    V.LenDefined n (toBits (qc V lam tau n x i)) := by
  obtain ⟨t, r, hr, -⟩ := h
  obtain ⟨t', -, hc⟩ := hardcode_time_rev (lenCore_wellScoped selfUniversal.closed) hr
  obtain ⟨td, hd⟩ := dim_univ V n
  obtain ⟨rs, hrs, -⟩ := lenCore_inv selfUniversal.closed V.sampler.prog V.len.prog lam tau n
    (encode (toBits x, κ)) (V.sampler.dim n) hd (r := r) (t := t') hc
  intro b
  have hq : encode (n, toBits (qc V lam tau n x i), b) ∈
      lenQs n (encode (toBits x, κ)) (V.sampler.dim n) (K lam tau n) := by
    rw [lenQs_toBits, lenQueries, List.mem_append]
    cases b
    · exact Or.inl (List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
    · exact Or.inr (List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
  obtain ⟨r', t'', hu⟩ := exists_of_forall₂ hrs _ hq
  obtain ⟨t₃, h₃⟩ := selfUniversal.halts_of _ _ _ _ hu
  exact ⟨_, t₃, r', h₃, rfl⟩

end Spec

/-- **The lengths of the repeated calculator** are at most `k(n)` times the input's. -/
theorem repLen_lenBound {ℓ : ℕ} (S : CL.Sampler ℓ) (L : Decider) (lam tau n B : ℕ)
    (hB : LenBound L n B) :
    LenBound (repLen S L lam tau) n (Repetition.reps lam tau n * B) := by
  rintro x κ m ⟨t, r, hr, rfl⟩
  obtain ⟨t', -, hc⟩ := hardcode_time_rev (lenCore_wellScoped selfUniversal.closed) hr
  obtain ⟨td, hd⟩ : ∃ td, selfUniversal.univ.Runs
      (.cons (encode S.prog) (encode (n, CL.Sampler.Query.dimension))) (encode (S.dim n)) td := by
    obtain ⟨t, h⟩ := S.runs_dimension n
    obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
    exact ⟨t', h'⟩
  obtain ⟨rs, hrs, rfl⟩ := lenCore_inv selfUniversal.closed S.prog L.prog lam tau n
    (encode (x, κ)) (S.dim n) hd (r := r) (t := t') hc
  have hlen : rs.length = 2 * Repetition.reps lam tau n := by
    rw [← hrs.length_eq]; simp [lenQs, lenQueries]; omega
  -- every result is a length of `L`
  have hres : ∀ r ∈ rs, (spineList r).length ≤ B := by
    intro r hr
    obtain ⟨-, hall⟩ := List.forall₂_iff_get.1 hrs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    obtain ⟨t₁, hu⟩ := hall i (by rw [hrs.length_eq]; exact hi) hi
    obtain ⟨t₂, h₂⟩ := selfUniversal.halts_of _ _ _ _ hu
    have hq := List.getElem_mem (l := lenQs n (encode (x, κ)) (S.dim n) (Repetition.reps lam tau n))
      (by rw [hrs.length_eq]; exact hi)
    unfold lenQs lenQueries at hq
    rw [List.mem_append, List.mem_map, List.mem_map] at hq
    rcases hq with ⟨xi, -, hq⟩ | ⟨xi, -, hq⟩ <;>
    · simp only [List.get_eq_getElem] at h₂
      exact hB _ _ _ ⟨t₂, _, (by rw [hq]; exact h₂), rfl⟩
  rw [encode_list_data, list, spineList_ofList, List.map_id, lenOut, List.length_flatten,
    List.map_map]
  have hsel : ∀ l ⊆ rs, ((l.map ((List.length) ∘ Detyping.Program.rawList)).sum ≤ l.length * B) := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply]
      have ha := hres a (hl (by simp))
      rw [rawList_eq_spineList]
      have := ih (fun b hb => hl (by simp [hb]))
      nlinarith
  split_ifs
  · refine (hsel _ (List.drop_subset _ _)).trans ?_
    rw [List.length_drop, hlen]
    exact Nat.mul_le_mul_right _ (by omega)
  · refine (hsel _ (List.take_subset _ _)).trans ?_
    rw [List.length_take]
    exact Nat.mul_le_mul_right _ (min_le_left _ _)

end MIPRE.Tailored.RepProg

end
