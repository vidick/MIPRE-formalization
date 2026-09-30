/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.AnswerReduction.SoundPoly

@[expose] public section

/-!
# Soundness of answer reduction: the game check under the extracted measurement

Piece AR-5e of `planning/answer-reduction.md` (the game check of `lem:ar-ar`): the probability
that the PCP check rejects the evaluations of Alice's simultaneous polynomial measurement `J`, at a
uniform point, is at most its probability of rejecting Bob's `Point_6` answer plus their
disagreement (`sum_ite_bornProb_one_le`): the first is bounded by the typed game's failure at the
type pair of two `Point_6` questions, whose step 5 checks Bob's answer, and the second by the
extraction (`sum_gcEvA_le`). The mirror image bounds Bob's `J` (`sum_gcEvB_le`).

The paper argues through its decoded strategy's closeness to the original (`lem:ar-ar`, the game
check, with `lem:close-strategies-have-close-values`); the event transfer used here is linear in
the disagreement and needs no projectivity.
-/

noncomputable section

namespace MIPRE.BipartiteModel

open Finset

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (M : BipartiteModel 𝒞 𝒜 ℬ)
variable {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]

/-- An event of a relabelled outcome, under the first player's measurement. -/
theorem sum_ite_bornProb_one_map [PartialOrder 𝒜] [StarOrderedRing 𝒜] (P : POVMIn A 𝒜)
    (φ : A → C) (E : C → Prop) [DecidablePred E] :
    ∑ c, (if E c then M.bornProb ((P.map φ).op c) 1 else 0)
      = ∑ a, (if E (φ a) then M.bornProb (P.op a) 1 else 0) := by
  have h := M.sum_bornProb_mapA P φ (1 : ℬ) (fun c => if E c then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  exact h

/-- An event of a relabelled outcome, under the second player's measurement. -/
theorem sum_ite_bornProb_one_map' [PartialOrder ℬ] [StarOrderedRing ℬ] (Q : POVMIn A ℬ)
    (φ : A → C) (E : C → Prop) [DecidablePred E] :
    ∑ c, (if E c then M.bornProb 1 ((Q.map φ).op c) else 0)
      = ∑ a, (if E (φ a) then M.bornProb 1 (Q.op a) else 0) := by
  have h := M.sum_bornProb_mapB (1 : 𝒜) Q φ (fun c => if E c then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  exact h

end MIPRE.BipartiteModel

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ) (T : M.ProjStrat (typedGame V n P hk S S' check B)) (hL : LIDT.Simul.SoundIn M)

/-- **What a typed question carries**: the type, the oracle half its role family computes, and the
PCP vector its presentation computes. -/
theorem decodeQ_tq (u : ArTy) (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    decodeQ V n P hk (tq V n P hk S S' u x w)
      = (u, (roleFamily (V.sampler.cl n) u.1).eval x, (Pcp.pres P S S' u.2).eval w) := by
  simp only [decodeQ, tq, oraclePart_eval, pcpPart_eval, oraclePart_append, pcpPart_append]

theorem ptOf_pres6 (w : Coord P → Fq P hk) :
    (regs6 P).ptOf ((Pcp.pres P S S' ((5 : Fin 6), .point)).eval w) = (regs6 P).ptOf w := by
  rw [pres_six S S' w .point (by rfl)]
  exact ptOf_point_eval _ _ w

/-- **Step 5 at two `Point_6` questions**: acceptance forces the PCP check to pass on both
answers. -/
theorem check_of_typedPred (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk)
    {a b : Verifier.Answers B}
    (h : typedPred V n P hk S S' check B (tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) x w)
      (tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) x w) a b = true) :
    check ((roleFamily (V.sampler.cl n) .oracle).eval x) ((regs6 P).ptOf w) (rd6all P hk B a)
        = true ∧
      check ((roleFamily (V.sampler.cl n) .oracle).eval x) ((regs6 P).ptOf w) (rd6all P hk B b)
        = true := by
  obtain ⟨u, v, hu, hv, hacc⟩ := accepts_of_typedPred V n P hk S S' check h
  have hu' : parse (fld P hk) ((5 : Fin 6), .point) a.1 = some u := hu
  have hv' : parse (fld P hk) ((5 : Fin 6), .point) b.1 = some v := hv
  simp only [rd6all, hu', hv', Option.getD_some]
  rw [decodeQ_tq] at hacc
  simp only [accepts, Bool.and_eq_true] at hacc
  obtain ⟨⟨-, hs⟩, hs'⟩ := hacc
  simp only [side, Bool.and_eq_true] at hs hs'
  have hp := ptOf_pres6 P hk S S' w
  refine ⟨?_, ?_⟩
  · have h5 := hs.2
    simp only [true_and] at h5
    rw [hp] at h5
    exact h5
  · have h5 := hs'.2
    simp only [true_and] at h5
    rw [hp] at h5
    exact h5

/-- The event that the PCP check rejects a view. -/
def Rej (y : Fin (V.sampler.dim n) → 𝔽₂) (z : Fin P.m' → Fq P hk)
    (α : Fin (P.m' + 6) → Fq P hk) : Prop :=
  check y z α = false

instance (y : Fin (V.sampler.dim n) → 𝔽₂) (z : Fin P.m' → Fq P hk) :
    DecidablePred (Rej V n P hk check y z) := fun _ => inferInstanceAs (Decidable (_ = _))

/-- **The rejection probability of Alice's `J`**, at a uniform point: the weight of the outcomes
whose evaluations the check rejects. -/
def gcEvA (x : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  ∑ z, uniform (Fin P.m' → Fq P hk) z *
    ∑ f, (if Rej V n P hk check ((roleFamily (V.sampler.cl n) .oracle).eval x) z
        (fun j => (f j).eval z) then M.bornProb
        ((JA V n P hk S S' check B T hL ((roleFamily (V.sampler.cl n) .oracle).eval x)).op f) 1
        else 0)

/-- **The rejection probability of Bob's `J`**, at a uniform point. -/
def gcEvB (x : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  ∑ z, uniform (Fin P.m' → Fq P hk) z *
    ∑ f, (if Rej V n P hk check ((roleFamily (V.sampler.cl n) .oracle).eval x) z
        (fun j => (f j).eval z) then M.bornProb 1
        ((JB V n P hk S S' check B T hL ((roleFamily (V.sampler.cl n) .oracle).eval x)).op f)
        else 0)

theorem tuplePOVMA_copy6_all (y : Fin (V.sampler.dim n) → 𝔽₂) (u : Fin P.m' → Fq P hk) :
    Simul.tuplePOVMAIn hm' (copyStrategy6 V n P hk S S' check B T y) u
      = (T.PA (arQ6 V n P hk S' .oracle y (.point u))).map (rd6all P hk B) := by
  unfold Simul.tuplePOVMAIn copyStrategy6 BipartiteModel.ProjStrat.adapt
  rw [POVMIn.map_map]
  exact congrArg (fun f => POVMIn.map f _) (funext fun a => valsOf_ans6' P hk _)

theorem tuplePOVMB_copy6_all (y : Fin (V.sampler.dim n) → 𝔽₂) (u : Fin P.m' → Fq P hk) :
    Simul.tuplePOVMBIn hm' (copyStrategy6 V n P hk S S' check B T y) u
      = (T.PB (arQ6 V n P hk S' .oracle y (.point u))).map (rd6all P hk B) := by
  unfold Simul.tuplePOVMBIn copyStrategy6 BipartiteModel.ProjStrat.adapt
  rw [POVMIn.map_map]
  exact congrArg (fun f => POVMIn.map f _) (funext fun a => valsOf_ans6' P hk _)

/-- **Alice's `J` against the check**: summed over the oracle halves, at most the sixth copy's
extraction error plus `54²` times the typed failure, per oracle half. -/
theorem sum_gcEvA_le :
    ∑ x, gcEvA V n P hk S S' check B T hL x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) *
        (err6 V n P hk S S' check B T + 2916 * (1 - T.value)) := by
  have hW : (0 : ℝ) < Fintype.card (Coord P → Fq P hk) := by positivity
  set L := roleFamily (V.sampler.cl n) .oracle
  -- the edge of two `Point_6` questions
  have hedge := sum_edges_le V n P hk S S' check B T
    (fun _ : Unit => (((.oracle, ((5 : Fin 6), .point)) : ArTy),
      ((.oracle, ((5 : Fin 6), .point)) : ArTy))) (fun _ _ _ => rfl)
  rw [card_arTy_sq, Fintype.sum_unique, card_idx V n P hk, card_idx_eq] at hedge
  -- the per-oracle-half bound
  have hx : ∀ x, gcEvA V n P hk S S' check B T hL x
      ≤ (∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
        + Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T (L.eval x)) := by
    intro x
    set y := L.eval x with hy
    set E := fun (z : Fin P.m' → Fq P hk) => Rej V n P hk check y z
    set MB := fun z : Fin P.m' → Fq P hk =>
      (T.PB (arQ6 V n P hk S' .oracle y (.point z))).map (rd6all P hk B)
    set JAall := Simul.evalTuplePOVMIn (JA V n P hk S S' check B T hL y)
    -- per point: transfer to Bob's `Point_6` answer
    have hz : ∀ z, ∑ f, (if E z (fun j => (f j).eval z) then M.bornProb ((JA V n P hk S S' check B T hL y).op f) 1 else 0)
        ≤ ∑ α, (if E z α then M.bornProb 1 ((MB z).op α) else 0) + M.dis (JAall z) (MB z) := by
      intro z
      have h1 := M.sum_ite_bornProb_one_map ((JA V n P hk S S' check B T hL y))
        (fun f j => (f j).eval z) (E z)
      rw [← h1]
      exact M.sum_ite_bornProb_one_le T.ψ_unit (JAall z) (MB z) (E z)
    -- the extraction's disagreement
    obtain ⟨-, h2, -⟩ := ext6_spec V n P hk S S' check B T hL y
    have h2' := M.sum_dis_le_of_inconsistency T.ψ_unit _ _ h2
    have hsum : ∑ z, M.dis (JAall z) (MB z)
        ≤ (Fintype.card (Fin P.m' → Fq P hk) : ℝ) * Simul.deltaSim (Fintype.card (Fq P hk))
          P.m' dPcp (P.m' + 6) (eps6 V n P hk S S' check B T y) := by
      refine le_trans (Finset.sum_le_sum fun z _ => ?_) h2'
      simp only [MB, JAall]
      rw [← tuplePOVMB_copy6_all]
    have hU : (0 : ℝ) < Fintype.card (Fin P.m' → Fq P hk) := by positivity
    have hdis : ∑ z, uniform (Fin P.m' → Fq P hk) z * M.dis (JAall z) (MB z)
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T y) := by
      simp only [uniform, ← Finset.mul_sum]
      rw [inv_mul_le_iff₀ hU]
      exact hsum
    -- Bob's rejections, at the edge
    have hB : ∑ z, uniform (Fin P.m' → Fq P hk) z * ∑ α, (if E z α then M.bornProb 1 ((MB z).op α) else 0)
        ≤ (∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk) := by
      rw [← sum_ptOf6_div P hk (fun z => ∑ α, (if E z α then M.bornProb 1 ((MB z).op α) else 0))]
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => ?_) hW.le
      have hq : tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) x w
          = arQ6 V n P hk S' .oracle y (.point ((regs6 P).ptOf w)) :=
        tq_point6 V n P hk S S' .oracle x w
      simp only [MB]
      rw [← hq, M.sum_ite_bornProb_one_map', edgeFail, BipartiteModel.ProjStrat.failAt]
      refine M.sum_ite_bornProb_le_condFail T.ψ_unit _ fun a b h => ?_
      simp only [E, Rej, Bool.not_eq_false]
      exact (check_of_typedPred V n P hk S S' check B x w h).2
    calc gcEvA V n P hk S S' check B T hL x
        ≤ ∑ z, uniform (Fin P.m' → Fq P hk) z * (∑ α, (if E z α then M.bornProb 1 ((MB z).op α) else 0)
            + M.dis (JAall z) (MB z)) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hz z) (by simp [uniform])
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add hB hdis
  calc ∑ x, gcEvA V n P hk S S' check B T hL x
      ≤ ∑ x, ((∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
        + Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T (L.eval x))) := Finset.sum_le_sum fun x _ => hx x
    _ = (∑ x, ∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
        + ∑ x, Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T (L.eval x)) := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := by
        have h6 := sum_deltaSim6_le V n P hk S S' check B T
        have h1 : (∑ x, ∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
            (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
            ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (2916 * (1 - T.value)) := by
          rw [div_le_iff₀ hW]
          push_cast at hedge
          linarith
        rw [err6]
        linarith

/-- **Bob's `J` against the check**, the mirror image. -/
theorem sum_gcEvB_le :
    ∑ x, gcEvB V n P hk S S' check B T hL x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) *
        (err6 V n P hk S S' check B T + 2916 * (1 - T.value)) := by
  have hW : (0 : ℝ) < Fintype.card (Coord P → Fq P hk) := by positivity
  set L := roleFamily (V.sampler.cl n) .oracle
  -- the edge of two `Point_6` questions
  have hedge := sum_edges_le V n P hk S S' check B T
    (fun _ : Unit => (((.oracle, ((5 : Fin 6), .point)) : ArTy),
      ((.oracle, ((5 : Fin 6), .point)) : ArTy))) (fun _ _ _ => rfl)
  rw [card_arTy_sq, Fintype.sum_unique, card_idx V n P hk, card_idx_eq] at hedge
  -- the per-oracle-half bound
  have hx : ∀ x, gcEvB V n P hk S S' check B T hL x
      ≤ (∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
        + Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T (L.eval x)) := by
    intro x
    set y := L.eval x with hy
    set E := fun (z : Fin P.m' → Fq P hk) => Rej V n P hk check y z
    set MB := fun z : Fin P.m' → Fq P hk =>
      (T.PA (arQ6 V n P hk S' .oracle y (.point z))).map (rd6all P hk B)
    set JAall := Simul.evalTuplePOVMIn (JB V n P hk S S' check B T hL y)
    -- per point: transfer to Bob's `Point_6` answer
    have hz : ∀ z, ∑ f, (if E z (fun j => (f j).eval z) then M.bornProb 1 ((JB V n P hk S S' check B T hL y).op f) else 0)
        ≤ ∑ α, (if E z α then M.bornProb ((MB z).op α) 1 else 0) + M.dis (MB z) (JAall z) := by
      intro z
      have h1 := M.sum_ite_bornProb_one_map' ((JB V n P hk S S' check B T hL y))
        (fun f j => (f j).eval z) (E z)
      rw [← h1]
      exact M.sum_ite_bornProb_one_le' T.ψ_unit (MB z) (JAall z) (E z)
    -- the extraction's disagreement
    obtain ⟨h2, -, -⟩ := ext6_spec V n P hk S S' check B T hL y
    have h2' := M.sum_dis_le_of_inconsistency T.ψ_unit _ _ h2
    have hsum : ∑ z, M.dis (MB z) (JAall z)
        ≤ (Fintype.card (Fin P.m' → Fq P hk) : ℝ) * Simul.deltaSim (Fintype.card (Fq P hk))
          P.m' dPcp (P.m' + 6) (eps6 V n P hk S S' check B T y) := by
      refine le_trans (Finset.sum_le_sum fun z _ => ?_) h2'
      simp only [MB, JAall]
      rw [← tuplePOVMA_copy6_all]
    have hU : (0 : ℝ) < Fintype.card (Fin P.m' → Fq P hk) := by positivity
    have hdis : ∑ z, uniform (Fin P.m' → Fq P hk) z * M.dis (MB z) (JAall z)
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T y) := by
      simp only [uniform, ← Finset.mul_sum]
      rw [inv_mul_le_iff₀ hU]
      exact hsum
    -- Bob's rejections, at the edge
    have hB : ∑ z, uniform (Fin P.m' → Fq P hk) z * ∑ α, (if E z α then M.bornProb ((MB z).op α) 1 else 0)
        ≤ (∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk) := by
      rw [← sum_ptOf6_div P hk (fun z => ∑ α, (if E z α then M.bornProb ((MB z).op α) 1 else 0))]
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => ?_) hW.le
      have hq : tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) x w
          = arQ6 V n P hk S' .oracle y (.point ((regs6 P).ptOf w)) :=
        tq_point6 V n P hk S S' .oracle x w
      simp only [MB]
      rw [← hq, M.sum_ite_bornProb_one_map, edgeFail, BipartiteModel.ProjStrat.failAt]
      refine M.sum_ite_bornProb_le_condFail' T.ψ_unit _ fun a b h => ?_
      simp only [E, Rej, Bool.not_eq_false]
      exact (check_of_typedPred V n P hk S S' check B x w h).1
    calc gcEvB V n P hk S S' check B T hL x
        ≤ ∑ z, uniform (Fin P.m' → Fq P hk) z * (∑ α, (if E z α then M.bornProb ((MB z).op α) 1 else 0)
            + M.dis (MB z) (JAall z)) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hz z) (by simp [uniform])
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add hB hdis
  calc ∑ x, gcEvB V n P hk S S' check B T hL x
      ≤ ∑ x, ((∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
        + Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T (L.eval x))) := Finset.sum_le_sum fun x _ => hx x
    _ = (∑ x, ∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
          (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
        + ∑ x, Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T (L.eval x)) := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := by
        have h6 := sum_deltaSim6_le V n P hk S S' check B T
        have h1 : (∑ x, ∑ w, edgeFail V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
            (.oracle, ((5 : Fin 6), .point))) x w) / Fintype.card (Coord P → Fq P hk)
            ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (2916 * (1 - T.value)) := by
          rw [div_le_iff₀ hW]
          push_cast at hedge
          linarith
        rw [err6]
        linarith

end MIPRE.AnswerReduction

end

end
