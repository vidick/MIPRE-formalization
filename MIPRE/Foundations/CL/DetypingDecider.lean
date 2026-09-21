/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingDeciderProg
import MIPRE.Foundations.VerifierValue

/-! # Acceptance and global answer bounds for the detyping compiler -/

noncomputable section

namespace MIPRE.CL.Detyping.DeciderProgram

open Cost Cost.PolyTimeFun Program

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

theorem decisionStage_accepts_direct (c r : Data) (h : route E c = (false, r)) :
    (∃ time, (decisionStage E D).Runs c (encode true) time) ↔ r = encode true := by
  obtain ⟨t, ht⟩ := decisionStage_direct E D c r h
  constructor
  · rintro ⟨time, hr⟩
    exact (ht.deterministic hr).1
  · rintro rfl
    exact ⟨t, ht⟩

theorem decisionStage_accepts_indirect (c arg ctx : Data)
    (h : route E c = (true, .cons arg ctx)) (hD : Halts D.prog arg) :
    (∃ time, (decisionStage E D).Runs c (encode true) time) ↔
      ∃ time, D.prog.Runs arg (encode true) time := by
  obtain ⟨r, time, hr⟩ := hD
  obtain ⟨t, ht⟩ := decisionStage_indirect E D c arg ctx r time h hr
  constructor
  · rintro ⟨t', ht'⟩
    have he := (ht.deterministic ht').1
    have he' : r = encode true := by
      rw [post_apply] at he
      exact of_decide_eq_true (encode_injective he)
    exact ⟨time, he' ▸ hr⟩
  · rintro ⟨time', hr'⟩
    have he := (hr.deterministic hr').1
    refine ⟨t, ?_⟩
    simpa [post_apply, he] using ht

/-- A raw-input acceptance law: the executable preliminary stages merely supply
their verified dimension and cutoffs to the final router. -/
theorem prog_accepts_iff_stage (hD : D.Total) (input : Data) :
    (∃ time, (prog E S D C).Runs input (encode true) time) ↔
      ∃ time, (decisionStage E D).Runs
        (context input (S.dim (readNat (treeHead input)))
          (C.inner (readNat (treeHead input))) (C.outer (readNat (treeHead input))))
        (encode true) time := by
  obtain ⟨r, t, ht⟩ := decisionStage_halts E D hD
    (context input (S.dim (readNat (treeHead input)))
      (C.inner (readNat (treeHead input))) (C.outer (readNat (treeHead input))))
  obtain ⟨tp, hp⟩ := prog_runs E S D C input r t ht
  constructor
  · rintro ⟨time, hr⟩
    have he := (hp.deterministic hr).1
    exact ⟨t, he ▸ ht⟩
  · rintro ⟨time, hr⟩
    exact prog_runs E S D C input (encode true) time hr

/-- The decision-stage acceptance law on arbitrary trees. A routed call accepts
precisely when the supplied typed program returns canonical Boolean true. -/
theorem decisionStage_accepts_iff (hD : D.Total) (c : Data) :
    (∃ time, (decisionStage E D).Runs c (encode true) time) ↔
      match routeResult E c with
      | (false, r) => r = encode true
      | (true, payload) => ∃ time, D.prog.Runs (treeHead payload) (encode true) time := by
  rw [← route_apply]
  cases h : route E c with
  | mk call payload =>
    cases call with
    | false => exact decisionStage_accepts_direct E D c payload h
    | true =>
      obtain ⟨d, ctx, rfl⟩ := route_preserves E c payload h
      exact decisionStage_accepts_indirect E D c _ ctx h (hD (indexReader c) d)

/-- Fully explicit raw-input acceptance after the two executable index queries.
The routing function includes canonical format, dimension and cutoff checks. -/
theorem raw_accepts_iff (hD : D.Total) (input : Data) :
    (∃ time, (prog E S D C).Runs input (encode true) time) ↔
      match routeResult E
        (context input (S.dim (readNat (treeHead input)))
          (C.inner (readNat (treeHead input))) (C.outer (readNat (treeHead input)))) with
      | (false, r) => r = encode true
      | (true, payload) => ∃ time, D.prog.Runs (treeHead payload) (encode true) time := by
  rw [prog_accepts_iff_stage E S D C hD, decisionStage_accepts_iff E D hD]

/-- Exact typed-input acceptance. Nonedges accept within the global cutoff;
genuine edges retain the source's inner cutoff and the unchanged answers. -/
theorem accepts_iff (hD : D.Total) (n : ℕ) (x y a b : BitStr) :
    (decider E S D C).Accepts n x y a b ↔
      x.length = graphDim T + S.dim n ∧ y.length = graphDim T + S.dim n ∧
      a.length ≤ C.outer n ∧ b.length ≤ C.outer n ∧
      match selectedEdge E (graphOfBits x) (graphOfBits y) with
      | none => True
      | some uv => a.length ≤ C.inner n ∧ b.length ≤ C.inner n ∧
          D.Accepts n uv.1 (x.drop (graphDim T)) uv.2 (y.drop (graphDim T)) a b := by
  change (∃ time, (prog E S D C).Runs (encode (n, x, y, a, b)) (encode true) time) ↔ _
  rw [prog_accepts_iff_stage E S D C hD]
  have hn : readNat (treeHead (encode (n, x, y, a, b))) = n := by
    simp only [encode_prod, treeHead_cons, readNat_encode]
  rw [hn]
  have hroute := route_context E n (S.dim n) (C.inner n) (C.outer n) x y a b
  by_cases hlength : x.length = graphDim T + S.dim n ∧
      y.length = graphDim T + S.dim n ∧ a.length ≤ C.outer n ∧ b.length ≤ C.outer n
  · rw [if_pos hlength] at hroute
    cases he : selectedEdge E (graphOfBits x) (graphOfBits y) with
    | none =>
      simp only [he] at hroute
      rw [decisionStage_accepts_direct E D _ _ hroute]
      simp [hlength.1, hlength.2.1, hlength.2.2.1, hlength.2.2.2]
    | some uv =>
      simp only [he] at hroute
      by_cases hinner : a.length ≤ C.inner n ∧ b.length ≤ C.inner n
      · rw [if_pos hinner] at hroute
        rw [decisionStage_accepts_indirect E D _ _ _ hroute (hD n _)]
        simp [hlength.1, hlength.2.1, hlength.2.2.1, hlength.2.2.2,
          hinner.1, hinner.2, TypedDecider.Accepts]
      · rw [if_neg hinner] at hroute
        rw [decisionStage_accepts_direct E D _ _ hroute]
        simp [hlength.1, hlength.2.1, hlength.2.2.1, hlength.2.2.2]
        intro ha hb
        exact False.elim (hinner ⟨ha, hb⟩)
  · rw [if_neg hlength] at hroute
    rw [decisionStage_accepts_direct E D _ _ hroute]
    constructor
    · intro h
      have hf : false = true := encode_injective h
      cases hf
    · intro h
      exact False.elim (hlength ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)

/-- The executable sampler and decider form a normal-form ambient verifier. -/
def verifier (hℓ : 0 < ℓ) (hD : D.Total) : MIPRE.Verifier (ℓ + 2) where
  sampler := Detyping.sampler E S hℓ
  decider := decider E S D C
  accepts_length n x y a b h := by
    have h' := (accepts_iff E S D C hD n x y a b).mp h
    exact ⟨h'.1, h'.2.1⟩

/-- The outer answer cut is enforced globally, including malformed graph views. -/
theorem verifier_rejectsLong (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ) :
    (verifier E S D C hℓ hD).RejectsLong n (C.outer n) := by
  intro x y a b hlong haccept
  have h := (accepts_iff E S D C hD n x y a b).mp haccept
  rcases hlong with hlong | hlong
  · exact (Nat.not_lt_of_ge h.2.2.1) hlong
  · exact (Nat.not_lt_of_ge h.2.2.2.1) hlong

end MIPRE.CL.Detyping.DeciderProgram
