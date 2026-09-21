/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgBranches
import MIPRE.Foundations.CL.DetypingProgQueries

/-! # The actual detyping sampler

A fixed finite graph and an arbitrary typed sampler compile to an ordinary
sampler with two additional levels. The construction includes a closed ambient
program, all query correctness clauses and halting on every malformed query.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Cost Program

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)

def samplerProg : Prog := Prog.routeOneCall (route E) S.prog (post (graphDim T))

theorem samplerProg_closed : (samplerProg E S).WellScoped 1 :=
  Prog.routeOneCall_closed _ S.closed _

theorem samplerProg_halts (n : ℕ) (q : Data) :
    Halts (samplerProg E S) (.cons (encode n) q) :=
  Prog.routeOneCall_halts _ S.closed _ n q (S.halts n) (route_preserves E n q)

private theorem run_direct (n : ℕ) (q : Sampler.Query) (out : BitStr)
    (h : route E (encode (n, q)) = directResult out) :
    ∃ time, (samplerProg E S).Runs (encode (n, q)) (encode out) time :=
  Prog.routeOneCall_direct _ _ _ _ _ h

private theorem run_call (n : ℕ) (q : Sampler.Query) (sub : TypedSampler.Query T)
    (preBits out : BitStr) (time : ℕ)
    (h : route E (encode (n, q)) = callResult (encode (n, sub)) (withPrefix preBits))
    (hr : S.prog.Runs (encode (n, sub)) (encode out) time) :
    ∃ t, (samplerProg E S).Runs (encode (n, q)) (encode (preBits ++ out)) t := by
  obtain ⟨t, ht⟩ := Prog.routeOneCall_indirect (route E) S.closed (post (graphDim T))
    _ _ _ _ time h hr
  exact ⟨t, by simpa only [post_prefix, samplerProg] using ht⟩

theorem samplerProg_dimension (n : ℕ) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.dimension))
      (encode (graphDim T + S.dim n)) time := by
  obtain ⟨time, hr⟩ := S.runs_dimension n
  obtain ⟨t, ht⟩ := Prog.routeOneCall_indirect (route E) S.closed (post (graphDim T))
    _ _ _ _ time (route_dimension E n) hr
  exact ⟨t, by simpa only [post_dimension, Nat.add_comm, samplerProg] using ht⟩

theorem samplerProg_marginal (hℓ : 0 < ℓ) (n : ℕ) (w : Player) (j : ℕ) (z : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ ℓ + 2) (hz : z.length = graphDim T + S.dim n) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.marginal w j z))
      (encode (toBits (((numbered E w (S.cl n w)).truncate j).eval
        (ofBits (graphDim T + S.dim n) z)))) time := by
  by_cases he : j ≤ 2
  · rw [numbered_marginal_graph E w _ j he z hz, graphOfBits_take_eq]
    apply run_direct E S
    rw [route_marginal_early E n w j z hj he, pad_content false z hz]
  · obtain ⟨r, rfl⟩ : ∃ r, j = r + 2 := ⟨j - 2, by omega⟩
    rw [numbered_marginal_content E w _ (S.cl_exactlyOn n w) hℓ r z hz, graphOfBits_take_eq]
    have hroute := route_marginal_late E n w (r + 2) z (by omega)
    cases ht : select E w.toBool (graphOfBits z) with
    | none =>
      simp only [selected, CLFun.eval_truncate_zeroOn, toBits_zero]
      apply run_direct E S
      simpa only [ht, pad_content false z hz] using hroute
    | some t =>
      simp only [selected]
      obtain ⟨time, hr⟩ := S.runs_marginal n w t r (content (graphDim T) z)
        (by omega) (by omega) (content_length z hz)
      exact run_call E S n _ _ _ _ time (by simpa only [ht, Nat.add_sub_cancel] using hroute) hr

theorem samplerProg_linear (hℓ : 0 < ℓ) (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ ℓ + 2)
    (hu : ∃ x, u = toBits (((numbered E w (S.cl n w)).truncate (j - 1)).eval x))
    (hy : y.length = graphDim T + S.dim n) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.linear w j u y))
      (encode (toBits ((numbered E w (S.cl n w)).mapOfPrefix (j - 1)
        (ofBits (graphDim T + S.dim n) u) (ofBits (graphDim T + S.dim n) y)))) time := by
  have huLen : u.length = graphDim T + S.dim n := by
    obtain ⟨x, rfl⟩ := hu
    exact length_toBits _
  by_cases he : j ≤ 2
  · rw [numbered_linear_graph E w _ (j - 1) (by omega) u y huLen hy,
      graphOfBits_take_eq, graphOfBits_take_eq]
    apply run_direct E S
    rw [route_linear_early E n w j u y hj he, pad_content false y hy]
  · obtain ⟨r, rfl⟩ : ∃ r, j = r + 3 := ⟨j - 3, by omega⟩
    have hi : r + 3 - 1 = r + 2 := by omega
    have hi' : r + 3 - 2 = r + 1 := by omega
    rw [hi, numbered_linear_content E w _ r u y huLen hy, graphOfBits_take_eq]
    have hroute := route_linear_late E n w (r + 3) u y (by omega)
    cases ht : select E w.toBool (graphOfBits u) with
    | none =>
      simp only [selected, CLFun.mapOfPrefix_zeroOn, LinearMap.zero_apply, toBits_zero]
      apply run_direct E S
      simpa only [ht, pad_content false y hy] using hroute
    | some t =>
      simp only [selected]
      have hp := numbered_selected_prefix E w (S.cl n w) (S.cl_exactlyOn n w) hℓ
        (r + 1) (by omega) u ((show r + 3 - 1 = r + 1 + 1 by omega) ▸ hu)
        (by simpa only [graphOfBits_take_eq] using ht)
      obtain ⟨time, hr⟩ := S.runs_linear n w t (r + 1)
        (content (graphDim T) u) (content (graphDim T) y) (by omega) (by omega)
        hp (content_length y hy)
      simpa only [Nat.add_sub_cancel, content] using
        run_call E S n _ _ _ _ time (by simpa only [ht, hi'] using hroute) hr

theorem samplerProg_factor (hℓ : 0 < ℓ) (n : ℕ) (w : Player) (j : ℕ) (u : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ ℓ + 2)
    (hu : ∃ x, u = toBits (((numbered E w (S.cl n w)).truncate (j - 1)).eval x)) :
    ∃ time, (samplerProg E S).Runs (encode (n, Sampler.Query.factor w j u))
      (encode (indicatorBits ((numbered E w (S.cl n w)).factorOfPrefix (j - 1)
        (ofBits (graphDim T + S.dim n) u)))) time := by
  have huLen : u.length = graphDim T + S.dim n := by
    obtain ⟨x, rfl⟩ := hu
    exact length_toBits _
  by_cases he : j ≤ 2
  · rw [numbered_factor_graph E w _ (j - 1) (by omega) u huLen, graphOfBits_take_eq]
    apply run_direct E S
    rw [route_factor_early E n w j u hj he, pad_content false u huLen]
  · obtain ⟨r, rfl⟩ : ∃ r, j = r + 3 := ⟨j - 3, by omega⟩
    have hi : r + 3 - 1 = r + 2 := by omega
    have hi' : r + 3 - 2 = r + 1 := by omega
    rw [hi, numbered_factor_content E w _ r u huLen, graphOfBits_take_eq]
    have hroute := route_factor_late E n w (r + 3) u (by omega)
    cases ht : select E w.toBool (graphOfBits u) with
    | none =>
      simp only [ht] at hroute
      rw [pad_content _ u huLen] at hroute
      have hℓ' : ℓ ≠ 0 := by omega
      cases r with
      | zero =>
        simpa [ht, selected, CLFun.factorOfPrefix_zeroOn, hℓ', indicatorBits] using
          run_direct E S n _ _ hroute
      | succ r =>
        simpa [ht, selected, CLFun.factorOfPrefix_zeroOn, hℓ', indicatorBits] using
          run_direct E S n _ _ hroute
    | some t =>
      simp only [selected]
      have hp := numbered_selected_prefix E w (S.cl n w) (S.cl_exactlyOn n w) hℓ
        (r + 1) (by omega) u ((show r + 3 - 1 = r + 1 + 1 by omega) ▸ hu)
        (by simpa only [graphOfBits_take_eq] using ht)
      obtain ⟨time, hr⟩ := S.runs_factor n w t (r + 1) (content (graphDim T) u)
        (by omega) (by omega) hp
      simpa only [Nat.add_sub_cancel, content] using
        run_call E S n _ _ _ _ time (by simpa only [ht, hi'] using hroute) hr

/-- Detyping as a genuine ambient sampler, with two additional CL levels. -/
def sampler (hℓ : 0 < ℓ) : Sampler (ℓ + 2) where
  prog := samplerProg E S
  closed := samplerProg_closed E S
  dim n := graphDim T + S.dim n
  cl n w := numbered E w (S.cl n w)
  cl_exactlyOn n w := numbered_exactlyOn E w _ (S.cl_exactlyOn n w) hℓ
  runs_dimension := samplerProg_dimension E S
  runs_marginal := samplerProg_marginal E S hℓ
  runs_linear := samplerProg_linear E S hℓ
  runs_factor := samplerProg_factor E S hℓ
  halts := samplerProg_halts E S

theorem sampler_dim (hℓ : 0 < ℓ) (n : ℕ) :
    (sampler E S hℓ).dim n = 4 * Fintype.card T + S.dim n := by
  change Fintype.card (Graph.Coord T) + S.dim n = _
  simp [Graph.Coord]
  omega

end MIPRE.CL.Detyping
