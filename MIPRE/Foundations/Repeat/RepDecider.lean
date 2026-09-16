/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.DecMain
import MIPRE.Foundations.Repeat.RepSampler

/-!
# The repeated decider

The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `Decider`: the core
`Prog.repDecCore` of `MIPRE.Foundations.Repeat.DecMain`, run through the self-interpreter and
the s-m-n construction on `((S̄, D̄), λ, τ, β)`. Its acceptance is characterized exactly
(`repDecider_accepts_iff`): on `(n, x, y, a, b)` it accepts iff `|x| = |y| = k s`, `a` and `b`
are the serializations of lists of `k` bit strings of length at most `B` each, and the input
decider accepts every coordinate `(n, x_i, y_i, a_i, b_i)`, with `k = 2^{τ(|λ| + |n|)}`,
`s = s(n)` the dimension of the input sampler and `B = 2^{β(|λ| + |n|)}` the parse length.
Both directions go through the inversion lemmas of the programs, since the input decider
need not halt on inputs it rejects.
-/

namespace MIPRE.Repeat

open Cost Cost.Data Cost.Prog CL

/-- The program of the repeated decider on `((S̄, D̄), λ, τ, β)`: the core, hardcoded. -/
noncomputable def repDeciderProg (sp dp : Prog) (lam tau beta : ℕ) : Prog :=
  hardcode (repDecCore selfUniversal.univ) (encode ((sp, dp), lam, tau, beta))

theorem repDeciderProg_wellScoped (sp dp : Prog) (lam tau beta : ℕ) :
    (repDeciderProg sp dp lam tau beta).WellScoped 1 :=
  hardcode_wellScoped (repDecCore_wellScoped selfUniversal.closed) _

/-- **The repeated decider** (`ComputeParrepVerifier`, decider half). -/
noncomputable def repDecider (sp dp : Prog) (lam tau beta : ℕ) : Decider :=
  ⟨repDeciderProg sp dp lam tau beta, repDeciderProg_wellScoped sp dp lam tau beta⟩

theorem encode_decParams (sp dp : Prog) (lam tau beta : ℕ) :
    (encode ((sp, dp), lam, tau, beta) : Data) =
      decParams (encode sp) (encode dp) (encode lam) (encode tau) (encode beta) := rfl

theorem encode_decInput (n : ℕ) (x y a b : BitStr) :
    (encode (n, x, y, a, b) : Data) =
      .cons (encode n) (.cons (encode x) (.cons (encode y) (.cons (encode a) (encode b)))) := rfl

/-- The run of the repeated decider on a well-formed input, from a run of `decMain`. -/
theorem repDeciderProg_runs (sp dp : Prog) (lam tau beta n : ℕ) (x y a b : BitStr) {r : Data} {t : ℕ}
    (h : Eval [decInput (encode sp) (encode dp) (encode lam) (encode tau) (encode beta) (encode n)
      (encode x) (encode y) (encode a) (encode b)] (decMain selfUniversal.univ) r t) :
    ∃ t', (repDeciderProg sp dp lam tau beta).Runs (encode (n, x, y, a, b)) r t' :=
  ⟨_, hardcode_time (repDecCore_wellScoped selfUniversal.closed)
    (repDecCore_runs selfUniversal.closed _ _ _ _ _ _ _ _ _ _ h)⟩

/-- Conversely, a run of the repeated decider on a well-formed input is a run of `decMain`. -/
theorem repDeciderProg_inv (sp dp : Prog) (lam tau beta n : ℕ) (x y a b : BitStr) {r : Data} {t : ℕ}
    (h : (repDeciderProg sp dp lam tau beta).Runs (encode (n, x, y, a, b)) r t) :
    ∃ t', Eval [decInput (encode sp) (encode dp) (encode lam) (encode tau) (encode beta) (encode n)
      (encode x) (encode y) (encode a) (encode b)] (decMain selfUniversal.univ) r t' := by
  obtain ⟨t₁, -, h₁⟩ := hardcode_time_rev (repDecCore_wellScoped selfUniversal.closed) h
  exact repDecCore_inv selfUniversal.closed _ _ _ _ _ _ _ _ _ _ h₁

variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)

/-- The universal machine accepts a coordinate query iff the input decider does. -/
theorem univ_accepts_iff (n : ℕ) (xi yi ai bi : BitStr) :
    (∃ t, Eval [decQuery (encode D.prog) (encode n) (encode xi) (encode yi) (encode ai) (encode bi)]
      selfUniversal.univ (.cons .nil .nil) t) ↔ D.Accepts n xi yi ai bi := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨t', h'⟩ := selfUniversal.halts_of _ _ _ _ h
    exact ⟨t', h'⟩
  · rintro ⟨t, h⟩
    obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
    exact ⟨t', h'⟩

/-- The acceptance predicate of the coordinate loop, read as `k`-tuples of bit strings. -/
theorem DecAcc_iff (univ : Prog) (dD nD : Data) (s B : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data),
      DecAcc univ dD nD s B k remX remY remA remB ↔
        ∃ aa bb : Fin k → BitStr,
          remA = List.ofFn (fun i => encode (aa i)) ∧ remB = List.ofFn (fun i => encode (bb i)) ∧
          ∀ i, (aa i).length ≤ B ∧ (bb i).length ≤ B ∧
            ∃ t, Eval [decQuery dD nD (list (chunk s i remX)) (list (chunk s i remY))
              (encode (aa i)) (encode (bb i))] univ (.cons .nil .nil) t
  | 0, remX, remY, remA, remB => by
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp, by simp, fun i => i.elim0⟩
    · rintro ⟨aa, bb, rfl, rfl, -⟩
      exact ⟨by simp, by simp⟩
  | k + 1, remX, remY, [], remB => by
    constructor
    · intro h; exact h.elim
    · rintro ⟨aa, bb, h, -, -⟩
      simp [List.ofFn_succ] at h
  | k + 1, remX, remY, _ :: _, [] => by
    constructor
    · intro h; exact h.elim
    · rintro ⟨aa, bb, -, h, -⟩
      simp [List.ofFn_succ] at h
  | k + 1, remX, remY, ai :: remA', bi :: remB' => by
    constructor
    · rintro ⟨hoka, hokb, hcall, hrec⟩
      obtain ⟨a₀, rfl, ha₀⟩ := (okBits_iff B ai).mp hoka
      obtain ⟨b₀, rfl, hb₀⟩ := (okBits_iff B bi).mp hokb
      obtain ⟨aa, bb, rfl, rfl, hall⟩ := (DecAcc_iff univ dD nD s B k _ _ remA' remB').mp hrec
      refine ⟨Fin.cons a₀ aa, Fin.cons b₀ bb, ?_, ?_, ?_⟩
      · simp [List.ofFn_succ]
      · simp [List.ofFn_succ]
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · simpa [chunk_zero] using ⟨ha₀, hb₀, hcall⟩
        · simpa [chunk_succ] using hall i'
    · rintro ⟨aa, bb, hA, hB, hall⟩
      simp only [List.ofFn_succ, List.cons.injEq] at hA hB
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨rfl, rfl⟩ := hB
      obtain ⟨ha₀, hb₀, hcall⟩ := hall 0
      refine ⟨(okBits_iff B _).mpr ⟨_, rfl, ha₀⟩, (okBits_iff B _).mpr ⟨_, rfl, hb₀⟩,
        by simpa [chunk_zero] using hcall, ?_⟩
      refine (DecAcc_iff univ dD nD s B k _ _ _ _).mpr ⟨fun i => aa i.succ, fun i => bb i.succ, rfl, rfl,
        fun i => ?_⟩
      simpa [chunk_succ] using hall i.succ

/-- **Acceptance of the repeated decider**, on the parameters `(λ, τ, β)` at index `n`, read as
`k`-tuples: `|x| = |y| = k s`, `a` and `b` the serializations of lists of `k` bit strings of
length at most `B`, and the input decider accepting every coordinate. -/
def RepAcc (lam tau beta n : ℕ) (x y a b : BitStr) : Prop :=
  x.length = Repetition.reps lam tau n * S.dim n ∧ y.length = Repetition.reps lam tau n * S.dim n ∧
    ∃ aa bb : Fin (Repetition.reps lam tau n) → BitStr,
      a = (list (List.ofFn fun i => encode (aa i))).toBitsPost ∧
      b = (list (List.ofFn fun i => encode (bb i))).toBitsPost ∧
      ∀ i, (aa i).length ≤ Repetition.parseBound lam beta n ∧
        (bb i).length ≤ Repetition.parseBound lam beta n ∧
        D.Accepts n (chunk (S.dim n) i x) (chunk (S.dim n) i y) (aa i) (bb i)

theorem bitsOf_toList_encode (x : BitStr) : bitsOf (toList (encode x)) = x := by
  rw [toList_encode_bitStr, bitsOf_map_ofBool]

/-- **The repeated decider accepts exactly on `RepAcc`.** -/
theorem repDecider_accepts_iff (lam tau beta n : ℕ) (x y a b : BitStr) :
    (repDecider S.prog D.prog lam tau beta).Accepts n x y a b ↔ RepAcc S D lam tau beta n x y a b := by
  obtain ⟨td, hdim⟩ := dim_call S n
  obtain ⟨tp, -, hp⟩ := prepProg_runs selfUniversal.closed (encode S.prog) (encode D.prog) lam tau beta
    n (S.dim n) (encode x) (encode y) (encode a) (encode b) hdim
  simp only [bitsOf_toList_encode] at hp
  -- the loop's predicate, in tuple form
  have hloop : DecAcc selfUniversal.univ (encode D.prog) (encode n) (S.dim n)
      (Repetition.parseBound lam beta n) (Repetition.reps lam tau n) (x.map ofBool) (y.map ofBool)
      (toList (parse a)) (toList (parse b)) ↔
      ∃ aa bb : Fin (Repetition.reps lam tau n) → BitStr,
        parse a = list (List.ofFn fun i => encode (aa i)) ∧ parse b = list (List.ofFn fun i => encode (bb i)) ∧
        ∀ i, (aa i).length ≤ Repetition.parseBound lam beta n ∧
          (bb i).length ≤ Repetition.parseBound lam beta n ∧
          D.Accepts n (chunk (S.dim n) i x) (chunk (S.dim n) i y) (aa i) (bb i) := by
    rw [DecAcc_iff]
    constructor
    · rintro ⟨aa, bb, hA, hB, hall⟩
      refine ⟨aa, bb, ?_, ?_, fun i => ?_⟩
      · rw [← list_toList (parse a), hA]
      · rw [← list_toList (parse b), hB]
      · obtain ⟨h1, h2, h3⟩ := hall i
        refine ⟨h1, h2, ?_⟩
        rw [← univ_accepts_iff]
        simpa [chunk_map, encode_bitStr_eq_list] using h3
    · rintro ⟨aa, bb, hA, hB, hall⟩
      refine ⟨aa, bb, ?_, ?_, fun i => ?_⟩
      · rw [hA, toList_list]
      · rw [hB, toList_list]
      · obtain ⟨h1, h2, h3⟩ := hall i
        refine ⟨h1, h2, ?_⟩
        rw [← univ_accepts_iff] at h3
        simpa [chunk_map, encode_bitStr_eq_list] using h3
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨t₁, h₁⟩ := repDeciderProg_inv S.prog D.prog lam tau beta n x y a b h
    obtain ⟨p, t₀, hp', hcase⟩ := decMain_inv selfUniversal.closed _ h₁
    obtain ⟨rfl, -⟩ := hp'.deterministic hp
    by_cases hok : prepOk lam tau n (S.dim n) x y a b = true
    · rw [show prepResult (encode D.prog) lam tau beta n (S.dim n) x y a b =
          prepState (encode D.prog) lam tau beta n (S.dim n) x y a b by simp [prepResult, hok]] at hcase
      rcases hcase with ⟨h, -⟩ | ⟨st₀, st₁, hst, t₂, h₂⟩
      · simp [prepState] at h
      · rw [← hst, prepState_eq] at h₂
        have hacc := coordLoop_inv selfUniversal.closed (encode D.prog) (encode n) (S.dim n) _ _
          (x.map ofBool) (y.map ofBool) (toList (parse a)) (toList (parse b)) [] h₂
        simp only [prepOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
        obtain ⟨⟨⟨hx, hy⟩, ha⟩, hb⟩ := hok
        obtain ⟨aa, bb, hA, hB, hall⟩ := hloop.mp hacc
        exact ⟨hx, hy, aa, bb, by rw [← hA, ha], by rw [← hB, hb], hall⟩
    · rw [show prepResult (encode D.prog) lam tau beta n (S.dim n) x y a b = .nil by
          simp [prepResult, hok]] at hcase
      rcases hcase with ⟨-, h⟩ | ⟨st₀, st₁, hst, -⟩
      · cases h
      · cases hst
  · rintro ⟨hx, hy, aa, bb, hA, hB, hall⟩
    have hpa : parse a = list (List.ofFn fun i => encode (aa i)) := by rw [hA, parse_toBitsPost]
    have hpb : parse b = list (List.ofFn fun i => encode (bb i)) := by rw [hB, parse_toBitsPost]
    have hok : prepOk lam tau n (S.dim n) x y a b = true := by
      simp only [prepOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨⟨hx, hy⟩, by rw [hpa, ← hA]⟩, by rw [hpb, ← hB]⟩
    rw [show prepResult (encode D.prog) lam tau beta n (S.dim n) x y a b =
        prepState (encode D.prog) lam tau beta n (S.dim n) x y a b by simp [prepResult, hok]] at hp
    have hacc := hloop.mpr ⟨aa, bb, hpa, hpb, hall⟩
    obtain ⟨t₂, h₂⟩ := coordLoop_of_acc selfUniversal.closed (encode D.prog) (encode n) (S.dim n) _ _
      (x.map ofBool) (y.map ofBool) (toList (parse a)) (toList (parse b)) [] hacc
    rw [← prepState_eq] at h₂
    obtain ⟨t', h'⟩ := repDeciderProg_runs S.prog D.prog lam tau beta n x y a b
      (decMain_runs_state selfUniversal.closed _ _ _ hp h₂)
    exact ⟨t', h'⟩

/-- The repeated decider accepts only questions of the repeated dimension. -/
theorem repDecider_accepts_length (lam tau beta n : ℕ) (x y a b : BitStr)
    (h : (repDecider S.prog D.prog lam tau beta).Accepts n x y a b) :
    x.length = Repetition.reps lam tau n * S.dim n ∧ y.length = Repetition.reps lam tau n * S.dim n :=
  let ⟨hx, hy, _⟩ := (repDecider_accepts_iff S D lam tau beta n x y a b).mp h
  ⟨hx, hy⟩

/-- The length of the serialization of a list of `k` bit strings of length at most `B`. -/
theorem length_toBitsPost_list_le (k B : ℕ) (aa : Fin k → BitStr) (h : ∀ i, (aa i).length ≤ B) :
    (list (List.ofFn fun i => encode (aa i))).toBitsPost.length ≤ k * (4 * B + 2) + 1 := by
  rw [length_toBitsPost]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, size_list_cons, Nat.succ_mul]
    have h1 : (encode (aa 0) : Data).size ≤ 4 * (aa 0).length + 1 := esize_bitStr_le (aa 0)
    have h2 := ih (fun i => aa i.succ) (fun i => h i.succ)
    have h3 := h 0
    change (encode (aa 0) : Data).size + _ + 1 ≤ _
    omega

/-- **The repeated decider rejects long answers**: every accepted answer has length at most
`k (4B + 2) + 1`. -/
theorem repDecider_rejectsLong (lam tau beta n : ℕ) (x y a b : BitStr) (T : ℕ)
    (hT : Repetition.reps lam tau n * (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T)
    (h : (repDecider S.prog D.prog lam tau beta).Accepts n x y a b) :
    a.length ≤ T ∧ b.length ≤ T := by
  obtain ⟨-, -, aa, bb, hA, hB, hall⟩ := (repDecider_accepts_iff S D lam tau beta n x y a b).mp h
  constructor
  · rw [hA]
    exact (length_toBitsPost_list_le _ _ aa fun i => (hall i).1).trans hT
  · rw [hB]
    exact (length_toBitsPost_list_le _ _ bb fun i => (hall i).2.1).trans hT

end MIPRE.Repeat
