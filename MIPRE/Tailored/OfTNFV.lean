/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Canonical
public import MIPRE.Tailored.ZPC
public import MIPRE.Foundations.Halting.Wrapper
public import MIPRE.Foundations.VerifierValue
public import MIPRE.Tactics

@[expose] public section

/-!
# A tailored verifier as a normal form verifier

Paper II, II:1757–1787. A tailored normal form verifier `(S, L, LP)` is a normal form verifier
whose decider is the canonical decider; `TailoredVerifier.ofTNFV U V` is that verifier, the
canonical decider written as a program (`canonProg`) and wrapped in the question-length check of
`def:normal-verifier` (`Verifier.ofSamplerDecider`, which runs it through the universal machine
`U`).

* `tgame_accepts_iff`: the `n`-th tailored game `V.tgame n` accepts `(a, b)` at `(x, y)` exactly
  when the canonical decider does — when the answer-length calculator and the linear-constraints
  processor halt, by the determinism of the model, and both reject when they do not.
* `ofTNFV_accepts_iff`: so the normal form verifier's decider accepts exactly what the tailored
  game accepts.
* `valStar_ofTNFV`: the values agree, for every answer bound `T` above the answer lengths of the
  tailored game (`Verifier.valStar_eq_of_rejects`' argument: answers longer than the lengths are
  rejected).
* `hasPerfectPCC_ofTNFV`: a perfect ZPC strategy for the doubled tailored game is a perfect PCC
  strategy of the doubled game of `ofTNFV U V` (`lem:zpc-pcc`).

So the existing pipeline's statements about `MIPRE.Verifier` — its soundness analyses in value
form, its completeness notion `HasPerfectPCC` — apply to tailored verifiers through `ofTNFV`. The
running time of the canonical decider, which `Verifier.IsBounded` of `ofTNFV U V` needs, is not
bounded here: the halting protocol of Phase 1 reasons about tailored verifiers directly.
-/

namespace MIPRE.Tailored

open Cost Cost.Data

/-- A vector whose last coordinate is `1` never satisfies the rejecting constraint `J = 0`. -/
theorem not_satisfies_rejectConstraint (d : ℕ) (v : BitStr) :
    ¬Satisfies (rejectConstraint d) (v ++ [true]) := by
  rintro ⟨hlen, heven⟩
  simp only [rejectConstraint, List.length_append, List.length_replicate, List.length_singleton]
    at hlen
  have hv : (List.replicate d false).length = v.length := by simp; omega
  rw [rejectConstraint, List.zipWith_append hv, List.count_append] at heven
  have h0 : (List.zipWith (· && ·) (List.replicate d false) v).count true = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hmem
    simp [List.getElem_zipWith] at he
  rw [h0] at heven
  simp at heven

namespace TailoredVerifier

variable {ℓ : ℕ} (V : TailoredVerifier ℓ)

theorem lenOf_eq {n : ℕ} {x : BitStr} {κ : Bool} {d : Data} {t : ℕ}
    (h : V.len.prog.Runs (encode (n, x, κ)) d t) : V.lenOf n x κ = (spineList d).length := by
  have hex : ∃ k, LenIs V.len n x κ k := ⟨_, t, d, h, rfl⟩
  unfold lenOf
  rw [dite_eq_left hex]
  obtain ⟨t', d', h', hk⟩ := hex.choose_spec
  rw [← hk]
  obtain ⟨rfl, -⟩ := Eval.deterministic h' h
  rfl

theorem lenDefined_of {n : ℕ} {x : BitStr} {d₀ d₁ : Data} {t₀ t₁ : ℕ}
    (h₀ : V.len.prog.Runs (encode (n, x, false)) d₀ t₀)
    (h₁ : V.len.prog.Runs (encode (n, x, true)) d₁ t₁) : V.LenDefined n x := by
  intro κ
  cases κ
  · exact ⟨_, t₀, d₀, h₀, rfl⟩
  · exact ⟨_, t₁, d₁, h₁, rfl⟩

theorem consOf_eq {n : ℕ} {x y aR bR : BitStr} (hx : V.LenDefined n x) (hy : V.LenDefined n y)
    {d : Data} {t : ℕ} (h : V.lp.prog.Runs (encode (n, x, y, aR, bR)) d t) :
    V.consOf n x y aR bR = bitsListD d := by
  have hex : V.LenDefined n x ∧ V.LenDefined n y ∧ ∃ cs, LpIs V.lp n x y aR bR cs :=
    ⟨hx, hy, _, t, d, h, rfl⟩
  unfold consOf
  rw [dite_eq_left hex]
  obtain ⟨t', d', h', hcs⟩ := hex.2.2.choose_spec
  rw [← hcs]
  obtain ⟨rfl, -⟩ := Eval.deterministic h' h
  rfl

theorem consOf_eq_reject {n : ℕ} {x y aR bR : BitStr}
    (h : ¬(V.LenDefined n x ∧ V.LenDefined n y ∧ ∃ cs, LpIs V.lp n x y aR bR cs)) :
    ∃ d, V.consOf n x y aR bR = [rejectConstraint d] :=
  ⟨_, by unfold consOf; rw [dite_eq_right h]⟩

/-- **The tailored game accepts exactly what the canonical decider accepts.** -/
theorem tgame_accepts_iff (n : ℕ) (x y : V.Questions n) (a b : BitStr) :
    (V.tgame n).Accepts x y a b ↔
      ∃ t, (canonProg V.len.prog V.lp.prog).Runs
        (encode ((n, CL.toBits x, CL.toBits y, a, b) : DIn)) (encode true) t := by
  rw [canonProg_accepts V.len.closed V.lp.closed]
  constructor
  · intro hacc
    by_cases hall : V.LenDefined n (CL.toBits x) ∧ V.LenDefined n (CL.toBits y) ∧
        ∃ cs, LpIs V.lp n (CL.toBits x) (CL.toBits y) (a.take ((V.tgame n).lenR x))
          (b.take ((V.tgame n).lenR y)) cs
    · obtain ⟨hx, hy, cs, t₅, r₀, h₅, hcs⟩ := hall
      obtain ⟨k₁, t₁, r₁, h₁, -⟩ := hx false
      obtain ⟨k₂, t₂, r₂, h₂, -⟩ := hx true
      obtain ⟨k₃, t₃, r₃, h₃, -⟩ := hy false
      obtain ⟨k₄, t₄, r₄, h₄, -⟩ := hy true
      have e₁ := V.lenOf_eq h₁
      have e₂ := V.lenOf_eq h₂
      have e₃ := V.lenOf_eq h₃
      have e₄ := V.lenOf_eq h₄
      have hlenR : (V.tgame n).lenR x = (spineList r₁).length := e₁
      have hlenRy : (V.tgame n).lenR y = (spineList r₃).length := e₃
      rw [hlenR, hlenRy] at h₅
      refine ⟨r₁, r₂, r₃, r₄, r₀, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨t₃, h₃⟩, ⟨t₄, h₄⟩, ⟨t₅, h₅⟩, ?_, ?_, ?_⟩
      · have := hacc.1
        simp only [TailoredGame.len, tgame, e₁, e₂] at this
        exact this
      · have := hacc.2.1
        simp only [TailoredGame.len, tgame, e₃, e₄] at this
        exact this
      · intro c hc
        refine hacc.2.2 c ?_
        change c ∈ V.consOf n (CL.toBits x) (CL.toBits y) (a.take ((V.tgame n).lenR x))
          (b.take ((V.tgame n).lenR y))
        rw [hlenR, hlenRy, V.consOf_eq hx hy h₅]
        exact hc
    · obtain ⟨d, hd⟩ := V.consOf_eq_reject hall
      refine absurd (hacc.2.2 (rejectConstraint d) ?_) (not_satisfies_rejectConstraint d (a ++ b))
      change rejectConstraint d ∈ V.consOf n (CL.toBits x) (CL.toBits y)
        (a.take ((V.tgame n).lenR x)) (b.take ((V.tgame n).lenR y))
      rw [hd]
      exact List.mem_singleton_self _
  · rintro ⟨r₁, r₂, r₃, r₄, r₀, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨t₃, h₃⟩, ⟨t₄, h₄⟩, ⟨t₅, h₅⟩, ha, hb, hsat⟩
    have hx := V.lenDefined_of h₁ h₂
    have hy := V.lenDefined_of h₃ h₄
    have e₁ := V.lenOf_eq h₁
    have e₂ := V.lenOf_eq h₂
    have e₃ := V.lenOf_eq h₃
    have e₄ := V.lenOf_eq h₄
    refine ⟨?_, ?_, ?_⟩
    · change a.length = V.lenOf n (CL.toBits x) false + V.lenOf n (CL.toBits x) true
      rw [e₁, e₂]
      exact ha
    · change b.length = V.lenOf n (CL.toBits y) false + V.lenOf n (CL.toBits y) true
      rw [e₃, e₄]
      exact hb
    · intro c hc
      change c ∈ V.consOf n (CL.toBits x) (CL.toBits y)
        (a.take (V.lenOf n (CL.toBits x) false)) (b.take (V.lenOf n (CL.toBits y) false)) at hc
      rw [e₁, e₃, V.consOf_eq hx hy h₅] at hc
      exact hsat c hc

/-- **A tailored verifier as a normal form verifier**: its sampler, and the canonical decider as
a program, wrapped in the question-length check. -/
noncomputable def ofTNFV (U : UniversalMachine) : Verifier ℓ :=
  Verifier.ofSamplerDecider U V.sampler (canonProg V.len.prog V.lp.prog)

@[simp] theorem ofTNFV_sampler (U : UniversalMachine) : (V.ofTNFV U).sampler = V.sampler := rfl

/-- **The normal form verifier's decider accepts exactly what the tailored game accepts.** -/
theorem ofTNFV_accepts_iff (U : UniversalMachine) (n : ℕ) (x y : V.Questions n)
    (a b : BitStr) :
    (V.ofTNFV U).decider.Accepts n (CL.toBits x) (CL.toBits y) a b ↔
      (V.tgame n).Accepts x y a b := by
  rw [ofTNFV, Verifier.ofSamplerDecider_accepts, V.tgame_accepts_iff]
  simp only [CL.length_toBits, true_and]

/-- **The decision predicates agree** on the answers the tailored game has, embedded in the
answers of length at most `T`. -/
theorem ofTNFV_game_D (U : UniversalMachine) {n T : ℕ} (hT : (V.tgame n).maxLen ≤ T)
    (x y : V.Questions n) (a b : Verifier.Answers (V.tgame n).maxLen) :
    ((V.ofTNFV U).game n T).D x y (Verifier.Answers.castLE hT a) (Verifier.Answers.castLE hT b) =
      (V.tgame n).toGame.D x y a b := by
  rw [Bool.eq_iff_iff]
  refine (Verifier.game_D (V.ofTNFV U) n T x y _ _).trans ?_
  refine (V.ofTNFV_accepts_iff U n x y a.1 b.1).trans ?_
  exact decide_eq_true_iff.symm

/-- **The values agree**, for an answer bound above the tailored game's answer lengths. -/
theorem valStar_ofTNFV (U : UniversalMachine) (n T : ℕ) (hT : (V.tgame n).maxLen ≤ T) :
    (V.ofTNFV U).valStar n T = V.valStar n := by
  refine ValueModel.tensor.extendAnswers (V.tgame n).toGame ((V.ofTNFV U).game n T)
    (Verifier.Answers.castLE hT) (Verifier.Answers.castLE hT) (fun _ _ => rfl)
    (V.ofTNFV_game_D U hT) ?_
  intro x y a' b' h
  have h' := (V.ofTNFV_accepts_iff U n x y a'.1 b'.1).1
    ((Verifier.game_D (V.ofTNFV U) n T x y a' b').1 h)
  refine ⟨⟨⟨a'.1, ?_⟩, Subtype.ext rfl⟩, ⟨⟨b'.1, ?_⟩, Subtype.ext rfl⟩⟩
  · rw [h'.1]; exact (V.tgame n).len_le_maxLen x
  · rw [h'.2.1]; exact (V.tgame n).len_le_maxLen y

/-- **A perfect ZPC strategy gives a perfect PCC strategy of `ofTNFV`** (`lem:zpc-pcc`), for an
answer bound above the tailored game's answer lengths. -/
theorem hasPerfectPCC_ofTNFV (U : UniversalMachine) {n T : ℕ} (hT : (V.tgame n).maxLen ≤ T)
    (h : V.HasPerfectZPC n) : (V.ofTNFV U).HasPerfectPCC n T := by
  obtain ⟨S, hpcc, hval⟩ := TailoredGame.HasPerfectZPC.exists_pcc h
  have hD : ∀ (p q : Bool × V.Questions n) (a b : Verifier.Answers (V.tgame n).maxLen),
      ((V.ofTNFV U).doubledGame n T).D p q (Verifier.Answers.castLE hT a)
        (Verifier.Answers.castLE hT b) = (V.tgame n).toGame.doubled.D p q a b := by
    intro p q a b
    change (if p.1 = false ∧ q.1 = true then ((V.ofTNFV U).game n T).D p.2 q.2 _ _ else false) =
      (if p.1 = false ∧ q.1 = true then (V.tgame n).toGame.D p.2 q.2 a b else false)
    split_ifs
    · exact V.ofTNFV_game_D U hT p.2 q.2 a b
    · rfl
  refine ⟨S.extend ((V.ofTNFV U).doubledGame n T) (Verifier.Answers.castLE hT),
    S.isPCC_extend hpcc _ _ (fun _ _ => rfl), ?_⟩
  exact (S.value_extend ((V.ofTNFV U).doubledGame n T) (Verifier.Answers.castLE hT)
    (fun _ _ => rfl) hD).trans hval

end TailoredVerifier

end MIPRE.Tailored

end
