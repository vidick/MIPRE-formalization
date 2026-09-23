/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.DetypingDecider
import MIPRE.Foundations.Pipeline.PowDomRun

/-!
# The running time of the detyped decider

The detyped decider (`CL.Detyping.DeciderProgram.prog`) runs three stages on its input `(n, d)`:
the typed sampler on the dimension query, the cutoff routine on `n`, and the router, which either
answers directly or calls the typed decider once, on a typed input whose questions have the
typed sampler's dimension and whose answers are within the inner cut (`route_call_typed`). So its
time is dominated in the sense of `MIPRE.Pipeline.PDom` as soon as the three programs' are, the
typed decider's on those inputs only (`prog_time`).
-/

namespace MIPRE.CL.Detyping.DeciderProgram

open Cost Cost.PolyTimeFun Detyping.Program Pipeline

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]

/-- **The one call of the router** is to the typed decider on a typed input, with the index,
questions of the typed sampler's dimension and answers within the inner cut, whatever the input. -/
theorem route_call_typed (n s inner outer : ℕ) (d payload : Data)
    (h : route E (context (.cons (encode n) d) s inner outer) = (true, payload)) :
    ∃ (u v : T) (x y a b : BitStr), payload = .cons (encode (n, u, x, v, y, a, b)) .nil ∧
      x.length = s ∧ y.length = s ∧ a.length ≤ inner ∧ b.length ≤ inner := by
  rw [route_apply] at h
  dsimp only [routeResult] at h
  have hn : indexReader (context (.cons (encode n) d) s inner outer) = n := by
    simp [indexReader, inputReader, context, readNat_encode]
  have hs : dimensionReader (context (.cons (encode n) d) s inner outer) = s := by
    simp [dimensionReader, context, readNat_encode]
  have hi : innerReader (context (.cons (encode n) d) s inner outer) = inner := by
    simp [innerReader, context, encode_prod, readNat_encode]
  split_ifs at h with hc h2 h3
  · obtain ⟨-, hx, hy, -, -⟩ := hc
    obtain ⟨ha, hb⟩ := h3
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    set x := xReader (context (.cons (encode n) d) s inner outer)
    set y := yReader (context (.cons (encode n) d) s inner outer)
    rw [hn]
    rw [hs] at hx hy
    rw [hi] at ha hb
    cases hsel : selectedEdge E (graphOfBits x) (graphOfBits y) with
    | none => simp [edgeData, hsel, rawTruth] at h2
    | some uv =>
      refine ⟨uv.1, uv.2, x.drop (graphDim T), y.drop (graphDim T), _, _, ?_, by simp [hx],
        by simp [hy], ha, hb⟩
      simp only [edgeData, hsel, treeHead_cons, treeTail_cons]
      rfl
  all_goals simp at h

variable {ℓ : ℕ} (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

/-- **The running time of the detyped decider**: dominated as soon as the typed sampler runs
within `(cS (W + 1)^{mS})^{K + 1}` at degree `eS (K + 1)` at `n`, the cutoff routine within a
dominated time, and the typed decider within one on the typed inputs the router hands it. -/
theorem prog_time (cS mS eS cC mC eC cD mD eD : ℕ) : ∃ c m e, ∀ {W K : ℕ} (n : ℕ), n ≤ W →
    S.TimeBoundAt n ((cS * (W + 1) ^ mS) ^ (K + 1)) (eS * (K + 1)) →
    (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cC mC eC C.prog (encode n) (encode (C.inner n, C.outer n))) →
    (∀ {X : ℕ}, 1 ≤ X → ∀ (u v : T) (x y a b : BitStr), x.length = S.dim n →
      y.length = S.dim n → a.length ≤ C.inner n → b.length ≤ C.inner n →
      ∃ r, PRuns W X K cD mD eD D.prog (encode (n, u, x, v, y, a, b)) r) →
    (decider E S D C).TimeBoundAt n ((c * (W + 1) ^ m) ^ (K + 1)) (e * (K + 1)) := by
  obtain ⟨ci, mi, ei, hi⟩ := PDom.indexInput
  obtain ⟨c1, m1, e1, h1⟩ := PRuns.routeCall dimensionRoute pairPost ci mi ei (cS * 2 ^ eS) mS 0
  obtain ⟨cx, mx, ex, hx⟩ := PDom.consSize ci mi ei (cS * 2 ^ eS) mS 0
  obtain ⟨c2, m2, e2, h2⟩ := PRuns.routeCall cutoffRoute pairPost cx mx ex cC mC eC
  obtain ⟨cc, mc, ec, hc⟩ := PDom.consSize cx mx ex cC mC eC
  obtain ⟨c3, m3, e3, h3⟩ := PRuns.routeCall (route E) post cc mc ec cD mD eD
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.routeDirect (route E) post cc mc ec
  exact ⟨_, _, _, fun {W K} n hn hS hC hD d => by
    have hX : 1 ≤ d.size + 1 := by omega
    set input : Data := .cons (encode n) d with hinput
    have pin : PDom W (d.size + 1) K ci mi ei input.size := hi n d hX hn le_rfl
    -- the dimension
    obtain ⟨rd, td, htd, hrd⟩ := hS .nil
    obtain ⟨td', hrd'⟩ := S.runs_dimension n
    have hrd_eq : rd = encode (S.dim n) :=
      (Eval.deterministic (show S.prog.Runs (encode (n, (TypedSampler.Query.dimension :
        TypedSampler.Query T))) rd td from hrd) hrd').1
    subst hrd_eq
    have pS : PRuns W (d.size + 1) K (cS * 2 ^ eS) mS 0 S.prog (.cons (encode n) .nil)
        (encode (S.dim n)) := by
      refine ⟨td, htd.trans (le_of_eq ?_), hrd⟩
      simp only [Data.size_nil, pow_zero, Nat.mul_one]
      rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm eS]
      ring
    have R1 := h1 S.closed input _ input _ hX (by simp [dimensionRoute, input, readNat_encode])
      pin pS
    have hp1 : pairPost (input, encode (S.dim n)) = .cons input (encode (S.dim n)) := rfl
    rw [hp1] at R1
    set x1 : Data := .cons input (encode (S.dim n)) with hx1def
    have px1 : PDom W (d.size + 1) K cx mx ex x1.size := hx input _ hX pin pS.size_le
    -- the cutoff
    have PC := hC hX
    have R2 := h2 C.closed x1 _ x1 _ hX
      (by simp [cutoffRoute, x1, input, readNat_encode]) px1 PC
    have hp2 : pairPost (x1, encode (C.inner n, C.outer n)) =
        context input (S.dim n) (C.inner n) (C.outer n) := rfl
    rw [hp2] at R2
    set c : Data := context input (S.dim n) (C.inner n) (C.outer n) with hcdef
    have pc : PDom W (d.size + 1) K cc mc ec c.size := hc x1 _ hX px1 PC.size_le
    -- the decision
    have R3 : ∃ r, PRuns W (d.size + 1) K (c3 + c4) (max m3 m4) (max e3 e4) (decisionStage E D)
        c r := by
      cases hroute : route E c with
      | mk call payload =>
        cases call with
        | false =>
          exact ⟨payload, (h4 D.prog c payload hX hroute pc).mono hX (by omega)
            (le_max_right _ _) (le_max_right _ _)⟩
        | true =>
          obtain ⟨u, v, x, y, a, b, rfl, hxl, hyl, ha, hb⟩ :=
            route_call_typed E n (S.dim n) (C.inner n) (C.outer n) d _ hroute
          obtain ⟨r, PD⟩ := hD hX u v x y a b hxl hyl ha hb
          exact ⟨_, (h3 D.closed c _ _ r hX hroute pc PD).mono hX (by omega) (le_max_left _ _)
            (le_max_left _ _)⟩
    obtain ⟨r, R3⟩ := R3
    obtain ⟨t, ht, hr⟩ := PRuns.seq hX (seqProg_closed (cutoffStage_closed C)
      (decisionStage_closed E D)) R1 (PRuns.seq hX (decisionStage_closed E D) R2 R3)
    exact ⟨r, t, ht.le_final, hr⟩⟩

end MIPRE.CL.Detyping.DeciderProgram
