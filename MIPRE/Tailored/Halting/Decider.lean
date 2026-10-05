/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Compression
public import MIPRE.Foundations.Halting.Paper.Decider
public import MIPRE.Tactics

@[expose] public section

/-!
# The tailored halting verifier: the linear-constraints processor

Paper II, II:1887–2001 (the map `F`, the verifier `V^{M,λ}`, `lem:dhalt-values`), along the
route of `MIPRE/Foundations/Halting/Paper/Decider.lean`, which this file parallels with the
linear-constraints processor in the role of the decider. For a tailored gap compression `TG`, a
machine `M`, a search program `S'` and a parameter `λ`, the verifier is

  `Vhalt TG U UT S' M λ = (S^λ, L^λ, lp M λ)`,

the compressed sampler and answer-length calculator at `λ` with the linear-constraints processor
`lp M λ`, the efficient Kleene fixed point (`Cost.kleeneFix`) of
`P ↦ hardcode body (encode (M, (λ, P)))`. On `(n, x, y, a^R, b^R)` it runs `body` on its own
description and the input, and `body`:

1. runs `M` on the empty input for the budget `Nat.size n`; if it halts, outputs the empty list
   of constraints, which accepts every answer pair of the right lengths;
2. otherwise runs the search program `S'` on the description `descOf λ (lp M λ)` for the budget
   `Nat.size n`; if it halts, outputs the list `[J]` (`rejectConstraint 0`), which rejects
   every answer pair;
3. otherwise computes the compressed linear-constraints processor
   `Compress ((S^λ, L^λ, lp M λ), λ)` of its own verifier and runs it on the input through the
   universal machine.

Branches 1 and 3 are the paper's `F` (II:1900), with "accept" the empty list and "reject" the
list `{J}`. Branch 2 is Lin's search branch, which the existing halting layer has too: the value
form of compression has no base case for soundness, and the search supplies it.

* `lp_runs_iff` (`lem:dhalt-values`): the processor's output, branch by branch.
* `hasPerfectZPC_of_branch1`, `valStar_eq_zero_of_branch2`: the first two branches decide the
  level outright — a perfect ZPC strategy, the trivial one (`hasPerfectZPC_of_accepts_zero`),
  and value `0`.
* `hasPerfectZPC_iff_W`, `valStar_eq_W`: otherwise the level is that of the compressed verifier
  `W`, the output of `TG` on the verifier's own programs, with which it shares the sampler and
  the answer-length calculator, and whose processor outputs the same constraints there.
-/

namespace MIPRE.Tailored.Halting

open Cost Cost.Prog Polynomial

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ) (U : UniversalMachine)
  (UT : ClockedUniversalMachine)

/-! ## The construction -/

/-- The program outputting the empty list of constraints, which accepts every answer pair of the
right lengths. -/
def acceptProg : Prog := .const (encode ([] : List BitStr))

/-- The program outputting the list `[J]`, which rejects every answer pair. -/
def rejectProg : Prog := .const (encode [rejectConstraint 0])

/-- The compressed linear-constraints processor of the verifier `(S^λ, L^λ, P)`. -/
noncomputable def comprLp (lam : ℕ) (P : Prog) : Prog :=
  TG.compress ((TG.samplerProg lam, TG.lenProg lam, P), lam)

/-- **The three branches**, as a polynomial-time function of the description `(M, (λ, P))` and
the input `(n, rest)`: the program to run and its input. -/
noncomputable def prep (S' : Prog) :
    PolyTimeFun ((Prog × (ℕ × Prog)) × (ℕ × Data)) (Prog × Data) :=
  PolyTimeFun.ite
    ((PolyTimeFun.haltsWithin UT).comp
      (PolyTimeFun.pair (PolyTimeFun.fst.comp PolyTimeFun.fst)
        (PolyTimeFun.fst.comp PolyTimeFun.snd)))
    (PolyTimeFun.const (acceptProg, Data.nil))
    (PolyTimeFun.ite
      ((PolyTimeFun.haltsWithin UT).comp
        (PolyTimeFun.pair
          ((haltingReduction S').comp (MIPRE.Halting.descPoly.comp
            (PolyTimeFun.pair ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)
              ((PolyTimeFun.snd.comp PolyTimeFun.snd).comp PolyTimeFun.fst))))
          (PolyTimeFun.fst.comp PolyTimeFun.snd)))
      (PolyTimeFun.const (rejectProg, Data.nil))
      (PolyTimeFun.pair
        (TG.compress.comp (PolyTimeFun.pair
          (PolyTimeFun.pair
            (TG.samplerProg.comp ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst))
            (PolyTimeFun.pair
              (TG.lenProg.comp ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst))
              ((PolyTimeFun.snd.comp PolyTimeFun.snd).comp PolyTimeFun.fst)))
          ((PolyTimeFun.fst.comp PolyTimeFun.snd).comp PolyTimeFun.fst)))
        (MIPRE.Halting.reencode.comp PolyTimeFun.snd)))

theorem prep_apply (S' M : Prog) (lam : ℕ) (P : Prog) (n : ℕ) (rest : Data) :
    prep TG UT S' ((M, (lam, P)), (n, rest)) =
      if (evalWithin M .nil (Nat.size n)).isSome then (acceptProg, Data.nil)
      else if (evalWithin (MIPRE.Halting.searchP S' lam P) .nil (Nat.size n)).isSome then
        (rejectProg, Data.nil)
      else (comprLp TG lam P, encode (n, rest)) := rfl

/-- **The body of the processor**: run `prep`, then the universal machine on its output. -/
noncomputable def body (S' : Prog) : Prog := .let_ (prep TG UT S').code (callVar 0 U.univ)

theorem body_wellScoped (S' : Prog) : (body TG U UT S').WellScoped 1 :=
  ⟨(prep TG UT S').closed, callVar_wellScoped (by decide) U.closed⟩

/-- The map whose fixed point is the processor: `P ↦ hardcode body (encode (M, (λ, P)))`. -/
noncomputable def F (S' M : Prog) (lam : ℕ) : PolyTimeFun Prog Prog :=
  (PolyTimeFun.smn (Prog × (ℕ × Prog))).comp
    (PolyTimeFun.pair (PolyTimeFun.const (body TG U UT S'))
      (PolyTimeFun.pair (PolyTimeFun.const M)
        (PolyTimeFun.pair (PolyTimeFun.const lam) (PolyTimeFun.id Prog))))

theorem F_apply (S' M : Prog) (lam : ℕ) (P : Prog) :
    F TG U UT S' M lam P = hardcode (body TG U UT S') (encode (M, (lam, P))) := rfl

/-- **The linear-constraints processor `LP^{M,λ}`**: the efficient Kleene fixed point of `F`. -/
noncomputable def lpProg (S' M : Prog) (lam : ℕ) : Prog := kleeneFix U (F TG U UT S' M lam)

/-- `LP^{M,λ}`, as a closed program. -/
noncomputable def lp (S' M : Prog) (lam : ℕ) : Decider :=
  ⟨lpProg TG U UT S' M lam, kleeneFix_wellScoped _ _⟩

/-- **The tailored verifier `V^{M,λ}`** (II:1925): the compressed sampler and answer-length
calculator at `λ`, and the processor `LP^{M,λ}`. -/
noncomputable def Vhalt (S' M : Prog) (lam : ℕ) : TailoredVerifier ℓ where
  sampler := TG.sampler lam
  len := TG.len lam
  lp := lp TG U UT S' M lam

@[simp] theorem Vhalt_sampler (S' M : Prog) (lam : ℕ) :
    (Vhalt TG U UT S' M lam).sampler = TG.sampler lam := rfl

@[simp] theorem Vhalt_len (S' M : Prog) (lam : ℕ) :
    (Vhalt TG U UT S' M lam).len = TG.len lam := rfl

theorem Vhalt_lp_prog (S' M : Prog) (lam : ℕ) :
    (Vhalt TG U UT S' M lam).lp.prog = lpProg TG U UT S' M lam := rfl

/-- The compressed verifier of `V^{M,λ}`: the output of `TG` on its own programs, the same at
every level. -/
noncomputable abbrev W (S' M : Prog) (lam : ℕ) : TailoredVerifier ℓ :=
  TG.output (Vhalt TG U UT S' M lam).progs lam

theorem W_lp_prog (S' M : Prog) (lam : ℕ) :
    (W TG U UT S' M lam).lp.prog = comprLp TG lam (lpProg TG U UT S' M lam) := by
  rw [TG.output_lp, comprLp, TG.samplerProg_eq, TG.lenProg_eq]
  rfl

/-! ## Running the processor -/

/-- A run of `body` on `(P, (n, rest))` is a run of the program `prep` returns on the input it
returns. -/
theorem body_runs_iff (S' : Prog) (P : Prog × (ℕ × Prog)) (n : ℕ) (rest r : Data) :
    (∃ t, (body TG U UT S').Runs (encode (P, (n, rest))) r t) ↔
      ∃ t, (prep TG UT S' (P, (n, rest))).1.Runs (prep TG UT S' (P, (n, rest))).2 r t := by
  obtain ⟨t₀, -, e₀⟩ := (prep TG UT S').computes (P, (n, rest))
  constructor
  · rintro ⟨t, h⟩
    change Eval [encode (P, (n, rest))] (.let_ _ _) r t at h
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨rfl, -⟩ := Eval.deterministic h₁ e₀
      obtain ⟨t', -, hU⟩ := callVar_runs_rev U.closed h₂
      rw [Env.get_cons_zero] at hU
      have hU' : U.univ.Runs (.cons (encode (prep TG UT S' (P, (n, rest))).1)
          (prep TG UT S' (P, (n, rest))).2) r t' := hU
      exact U.halts_of _ _ _ _ hU'
  · rintro ⟨t, h⟩
    obtain ⟨t', -, hU⟩ := U.time_le _ _ _ t h
    have hU' : Eval [encode (prep TG UT S' (P, (n, rest)))] U.univ r t' := hU
    have h₂ := callVar_eval
      (env := [encode (prep TG UT S' (P, (n, rest))), encode (P, (n, rest))]) (i := 0)
      U.closed (v := encode (prep TG UT S' (P, (n, rest)))) (by simp) hU'
    exact ⟨_, Eval.let_ e₀ h₂⟩

/-- A run of the processor on `v` is a run of `body` on its own description and `v`. -/
theorem lpProg_runs_iff (S' M : Prog) (lam : ℕ) (v r : Data) :
    (∃ t, (lpProg TG U UT S' M lam).Runs v r t) ↔
      ∃ t, (body TG U UT S').Runs (.cons (encode (M, (lam, lpProg TG U UT S' M lam))) v) r t := by
  have hw := body_wellScoped TG U UT S'
  unfold lpProg
  rw [kleeneFix_halts_iff]
  constructor
  · rintro ⟨t, h⟩
    have h' : (hardcode (body TG U UT S')
        (encode (M, (lam, kleeneFix U (F TG U UT S' M lam))))).Runs v r t := h
    obtain ⟨t', -, h''⟩ := hardcode_time_rev hw h'
    exact ⟨t', h''⟩
  · rintro ⟨t, h⟩
    exact ⟨_, hardcode_time hw h⟩

/-- The first branch fires at the level `n`: `M` halts within `Nat.size n`. -/
abbrev branch1 (M : Prog) (n : ℕ) : Prop := (evalWithin M .nil (Nat.size n)).isSome = true

/-- The second branch fires at the level `n`: the search halts within `Nat.size n`. -/
abbrev branch2 (S' M : Prog) (lam n : ℕ) : Prop :=
  (evalWithin (MIPRE.Halting.searchP S' lam (lpProg TG U UT S' M lam)) .nil
    (Nat.size n)).isSome = true

/-- **The outputs of `LP^{M,λ}`** (`lem:dhalt-values`): on an input of index `n`, the empty list
if `M` halts within `Nat.size n`; otherwise `[J]` if the search halts within `Nat.size n`;
otherwise exactly what the compressed processor outputs. -/
theorem lp_runs_iff (S' M : Prog) (lam n : ℕ) (rest r : Data) :
    (∃ t, (lpProg TG U UT S' M lam).Runs (encode (n, rest)) r t) ↔
      if branch1 M n then r = encode ([] : List BitStr)
      else if branch2 TG U UT S' M lam n then r = encode [rejectConstraint 0]
      else ∃ t, (comprLp TG lam (lpProg TG U UT S' M lam)).Runs (encode (n, rest)) r t := by
  rw [lpProg_runs_iff,
    show Data.cons (encode (M, (lam, lpProg TG U UT S' M lam))) (encode (n, rest))
      = encode ((M, (lam, lpProg TG U UT S' M lam)), (n, rest)) from rfl,
    body_runs_iff, prep_apply]
  split_ifs with h1 h2
  · constructor
    · rintro ⟨t, h⟩
      exact (Eval.deterministic h (Eval.const [Data.nil] _)).1
    · rintro rfl
      exact ⟨_, Eval.const _ _⟩
  · constructor
    · rintro ⟨t, h⟩
      exact (Eval.deterministic h (Eval.const [Data.nil] _)).1
    · rintro rfl
      exact ⟨_, Eval.const _ _⟩
  · exact Iff.rfl

/-! ## The level, by branch -/

/-- The answer-length calculator halts at every question of the sampler. -/
theorem lenDefined (S' M : Prog) (lam n : ℕ) (x : (Vhalt TG U UT S' M lam).Questions n) :
    (Vhalt TG U UT S' M lam).LenDefined n (CL.toBits x) :=
  TG.len_total lam n _ (CL.length_toBits x)

/-- **The first branch**: at a level where `M` has halted, `V^{M,λ}` has a perfect ZPC
strategy, the trivial one: every constraint list is empty. -/
theorem hasPerfectZPC_of_branch1 (S' M : Prog) (lam : ℕ) {n : ℕ} (h1 : branch1 M n) :
    (Vhalt TG U UT S' M lam).HasPerfectZPC n := by
  refine hasPerfectZPC_of_accepts_zero _ fun p q _ => ⟨by simp, by simp, ?_⟩
  intro c hc
  have hnil : ∀ aR bR, (Vhalt TG U UT S' M lam).consOf n (CL.toBits p.2) (CL.toBits q.2) aR bR
      = [] := by
    intro aR bR
    refine (Vhalt TG U UT S' M lam).consOf_eq_of (lenDefined TG U UT S' M lam n p.2)
      (lenDefined TG U UT S' M lam n q.2) ?_
    obtain ⟨t, hrun⟩ := (lp_runs_iff TG U UT S' M lam n (encode (CL.toBits p.2, CL.toBits q.2,
      aR, bR)) (encode ([] : List BitStr))).2 (by rw [ite_eq_left h1])
    exact ⟨t, _, hrun, Data.bitsListD_encode []⟩
  change c ∈ (Vhalt TG U UT S' M lam).consOf n (CL.toBits p.2) (CL.toBits q.2) _ _ at hc
  rw [hnil] at hc
  exact absurd hc (List.not_mem_nil)

/-- **The second branch**: at a level where the search has halted and `M` has not, `V^{M,λ}`
has value `0`: every constraint list holds a rejecting constraint. -/
theorem valStar_eq_zero_of_branch2 (S' M : Prog) (lam : ℕ) {n : ℕ} (h1 : ¬ branch1 M n)
    (h2 : branch2 TG U UT S' M lam n) : (Vhalt TG U UT S' M lam).valStar n = 0 := by
  refine (Vhalt TG U UT S' M lam).valStar_eq_zero_of_rejects fun x y aR bR => ⟨0, ?_⟩
  obtain ⟨t, hrun⟩ := (lp_runs_iff TG U UT S' M lam n (encode (CL.toBits x, CL.toBits y,
    aR, bR)) (encode [rejectConstraint 0])).2 (by rw [ite_eq_right h1, ite_eq_left h2])
  rw [(Vhalt TG U UT S' M lam).consOf_eq_of (lenDefined TG U UT S' M lam n x)
    (lenDefined TG U UT S' M lam n y) ⟨t, _, hrun, Data.bitsListD_encode _⟩]
  exact List.mem_singleton_self _

/-- Off the first two branches, `V^{M,λ}` and its compressed verifier output the same
constraints at the level `n`. -/
theorem lpIs_iff_W (S' M : Prog) (lam : ℕ) {n : ℕ} (h1 : ¬ branch1 M n)
    (h2 : ¬ branch2 TG U UT S' M lam n) (x y aR bR : BitStr) (cs : List BitStr) :
    LpIs (Vhalt TG U UT S' M lam).lp n x y aR bR cs ↔
      LpIs (W TG U UT S' M lam).lp n x y aR bR cs := by
  unfold LpIs
  rw [Vhalt_lp_prog, W_lp_prog]
  constructor
  · rintro ⟨t, d, hrun, hd⟩
    have := (lp_runs_iff TG U UT S' M lam n (encode (x, y, aR, bR)) d).1 ⟨t, hrun⟩
    rw [ite_eq_right h1, ite_eq_right h2] at this
    obtain ⟨t', h'⟩ := this
    exact ⟨t', d, h', hd⟩
  · rintro ⟨t, d, hrun, hd⟩
    have := (lp_runs_iff TG U UT S' M lam n (encode (x, y, aR, bR)) d).2
      (by rw [ite_eq_right h1, ite_eq_right h2]; exact ⟨t, hrun⟩)
    obtain ⟨t', h'⟩ := this
    exact ⟨t', d, h', hd⟩

/-- **Off the first two branches, completeness is the compressed verifier's.** -/
theorem hasPerfectZPC_iff_W (S' M : Prog) (lam : ℕ) {n : ℕ} (h1 : ¬ branch1 M n)
    (h2 : ¬ branch2 TG U UT S' M lam n) :
    (Vhalt TG U UT S' M lam).HasPerfectZPC n ↔ (W TG U UT S' M lam).HasPerfectZPC n :=
  TailoredVerifier.hasPerfectZPC_congr (TG.output_sampler _ _).symm (TG.output_len _ _).symm
    (lpIs_iff_W TG U UT S' M lam h1 h2)

/-- **Off the first two branches, the value is the compressed verifier's.** -/
theorem valStar_eq_W (S' M : Prog) (lam : ℕ) {n : ℕ} (h1 : ¬ branch1 M n)
    (h2 : ¬ branch2 TG U UT S' M lam n) :
    (Vhalt TG U UT S' M lam).valStar n = (W TG U UT S' M lam).valStar n :=
  TailoredVerifier.valStar_congr (TG.output_sampler _ _).symm (TG.output_len _ _).symm
    (lpIs_iff_W TG U UT S' M lam h1 h2)

end MIPRE.Tailored.Halting

end
