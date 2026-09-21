/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgSampler
import MIPRE.Foundations.Cost.Growth
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Polynomial runtime transfer for the detyping sampler

The bound follows the actual one-call program: preprocessing bounds the size
of the forwarded query and continuation, the original sampler bounds the
forwarded run, and postprocessing reads their combined output. Constants in
the graph table are fixed; no uniform graph-compilation bound is asserted.
-/

namespace MIPRE.Cost

open PolyTimeFun Polynomial

namespace Prog

theorem callWithContext_cost {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (a ctx r : Data) (time : ℕ)
    (hr : p.Runs a r time) :
    ∃ t ≤ 2 * a.size + 2 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 12,
      (callWithContext p post).Runs (.cons a ctx) (post (ctx, r)) t := by
  obtain ⟨tp, htp, hpRun⟩ := post.computes (ctx, r)
  have ectx := callVar_eval (env := [r, a, Data.cons a ctx]) (i := 2)
    sndProg_wellScoped (by simp) (sndProg_runs a ctx)
  have run := Eval.let_ (fstProg_runs a ctx)
    (Eval.let_ (Eval.append_of_wellScoped hr hp _)
      (Eval.let_ (Eval.cons ectx (Eval.var_of_get (i := 0) (by simp)))
        (Eval.append_of_wellScoped hpRun post.closed _)))
  refine ⟨_, ?_, run⟩
  simp only [esize_prod, esize_data, Data.size_cons, encode_data] at *
  omega

theorem routeOneCall_direct_cost (route : PolyTimeFun Data (Bool × Data))
    (p : Prog) (post : PolyTimeFun (Data × Data) Data) (x r : Data)
    (h : route x = (false, r)) :
    ∃ t ≤ route.timeBound.eval x.size + r.size + 4,
      (routeOneCall route p post).Runs x r t := by
  obtain ⟨t, ht, hr⟩ := route.computes x
  rw [h] at hr
  refine ⟨_, ?_, Eval.let_ hr
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := r) (by simp [encode, Data.ofBool])
      (Eval.elim_nil (i := 0) (by simp) (Eval.var_of_get (i := 1) (by simp))))⟩
  simp only [esize_data] at ht
  omega

theorem routeOneCall_indirect_cost (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (x a ctx r : Data) (time : ℕ) (h : route x = (true, .cons a ctx))
    (hr : p.Runs a r time) :
    ∃ t ≤ route.timeBound.eval x.size + 3 * a.size + 3 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 18,
      (routeOneCall route p post).Runs x (post (ctx, r)) t := by
  obtain ⟨t, ht, hroute⟩ := route.computes x
  rw [h] at hroute
  obtain ⟨tc, htc, hc⟩ := callWithContext_cost hp post a ctx r time hr
  refine ⟨_, ?_, Eval.let_ hroute
    (Eval.elim_cons (i := 0) (a := Data.cons .nil .nil) (b := .cons a ctx)
      (by simp [encode, Data.ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := .nil) (by simp)
        (callVar_eval (i := 3) (callWithContext_closed hp post) (by simp) hc)))⟩
  simp only [esize_data, Data.size_cons] at *
  omega

/-- The closed polynomial expression bounding a router with one call to a
sampler whose indexed coefficient and input degree are `B` and `k`. -/
noncomputable def routeCost (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (B k : ℕ) : Polynomial ℕ :=
  let R := route.timeBound
  let F := C B * (R + 1) ^ k
  C 10 * (R + F + post.timeBound.comp (R + F + 1) + C 10)

/-- A common query degree, independent of the index and runtime coefficient. -/
noncomputable def routeDegree (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (k : ℕ) : ℕ :=
  route.timeBound.natDegree * (k + 1) * (post.timeBound.natDegree + 1)

theorem routeCost_natDegree_le (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (B k : ℕ) :
    (routeCost route post B k).natDegree ≤ routeDegree route post k := by
  let R := route.timeBound
  let F := C B * (R + 1) ^ k
  let A := R.natDegree * (k + 1)
  have hR : R.natDegree ≤ A := by dsimp [A]; nlinarith
  have hR1 : (R + 1).natDegree ≤ R.natDegree :=
    natDegree_add_le_of_degree_le le_rfl (by simp)
  have hF : F.natDegree ≤ A := by
    exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le k hR1).trans
      (by dsimp [A]; nlinarith))
  have hRF : (R + F).natDegree ≤ A := natDegree_add_le_of_degree_le hR hF
  have hRF1 : (R + F + 1).natDegree ≤ A :=
    natDegree_add_le_of_degree_le hRF (by simp)
  have hP : (post.timeBound.comp (R + F + 1)).natDegree ≤ post.timeBound.natDegree * A :=
    natDegree_comp_le.trans (Nat.mul_le_mul_left _ hRF1)
  have hA : A ≤ routeDegree route post k := by
    change A ≤ A * (post.timeBound.natDegree + 1)
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left A
      (Nat.succ_le_succ (Nat.zero_le post.timeBound.natDegree))
  have hPA : post.timeBound.natDegree * A ≤ routeDegree route post k := by
    dsimp [A, R, routeDegree]
    nlinarith
  exact (natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (hRF.trans hA) (hP.trans hPA)) (by simp))

theorem routeOneCall_haltsWithin (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (n B k : ℕ) (q : Data)
    (bound : ∀ d, HaltsWithin p (.cons (encode n) d) (B * (d.size + 1) ^ k))
    (preserves : ∀ a, route (.cons (encode n) q) = (true, a) →
      ∃ d ctx, a = .cons (.cons (encode n) d) ctx) :
    HaltsWithin (routeOneCall route p post) (.cons (encode n) q)
      ((routeCost route post B k).eval (Data.cons (encode n) q).size) := by
  let x := Data.cons (encode n) q
  let R := route.timeBound.eval x.size
  let F := B * (R + 1) ^ k
  let P := post.timeBound.eval (R + F + 1)
  have heval : (routeCost route post B k).eval x.size = 10 * (R + F + P + 10) := by
    simp only [routeCost, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_comp]
    rfl
  change HaltsWithin _ x _
  rw [heval]
  have hs := route.esize_apply_le x
  cases h : route x with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨time, ht, hr⟩ := routeOneCall_direct_cost route p post x payload h
      rw [h] at hs
      simp only [esize_prod, esize_false, esize_data] at hs
      refine ⟨payload, time, ?_, hr⟩
      change time ≤ R + payload.size + 4 at ht
      change 1 + payload.size + 1 ≤ R at hs
      omega
    | true =>
      obtain ⟨d, ctx, he⟩ := preserves payload h
      subst payload
      rw [h] at hs
      simp only [esize_prod, esize_true, esize_data, Data.size_cons] at hs
      obtain ⟨r, time, ht, hr⟩ := bound d
      have hd : d.size + 1 ≤ R + 1 := by
        change 3 + ((encode n).size + d.size + 1 + ctx.size + 1) + 1 ≤ R at hs
        omega
      have htF : time ≤ F := ht.trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_left hd k))
      have hrF : r.size ≤ F := hr.size_le.trans htF
      have hpost : post.timeBound.eval (ctx.size + r.size + 1) ≤ P :=
        polynomial_eval_mono _ (by
          change 3 + ((encode n).size + d.size + 1 + ctx.size + 1) + 1 ≤ R at hs
          omega)
      obtain ⟨time', ht', hr'⟩ := routeOneCall_indirect_cost route hp post x _ ctx r time h hr
      refine ⟨_, time', ht'.trans ?_, hr'⟩
      simp only [Data.size_cons]
      change R + 3 * ((encode n).size + d.size + 1) + 3 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 18 ≤ 10 * (R + F + P + 10)
      change 3 + ((encode n).size + d.size + 1 + ctx.size + 1) + 1 ≤ R at hs
      omega

end Prog
end MIPRE.Cost

namespace MIPRE.CL.Detyping

open Cost Polynomial

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)

/-- The explicit detyping runtime polynomial in the raw query's size. -/
noncomputable def samplerCost (n B k : ℕ) : Polynomial ℕ :=
  (Prog.routeCost (Program.route E) (Program.post (graphDim T)) B k).comp
    (X + C (esize n + 1))

/-- The common query degree for every index and every original coefficient. -/
noncomputable def samplerDegree (k : ℕ) : ℕ :=
  Prog.routeDegree (Program.route E) (Program.post (graphDim T)) k

theorem samplerCost_natDegree_le (n B k : ℕ) :
    (samplerCost E n B k).natDegree ≤ samplerDegree E k := by
  have hi : (X + C (esize n + 1) : Polynomial ℕ).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp only [natDegree_X]; omega)
      (by simp only [natDegree_C]; omega)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul
    (Prog.routeCost_natDegree_le _ _ B k) hi).trans (by simp [samplerDegree]))

/-- The coefficient obtained from the explicit runtime polynomial. -/
noncomputable def samplerCoefficient (n B k : ℕ) : ℕ :=
  let Q := samplerCost E n B k
  ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i

theorem sampler_haltsWithin (hℓ : 0 < ℓ) (n B k : ℕ) (h : S.TimeBoundAt n B k) (q : Data) :
    HaltsWithin (sampler E S hℓ).prog (.cons (encode n) q)
      ((samplerCost E n B k).eval q.size) := by
  have hr := Prog.routeOneCall_haltsWithin (Program.route E) S.closed
    (Program.post (graphDim T)) n B k q h (Program.route_preserves E n q)
  simpa only [sampler, samplerProg, samplerCost, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Data.size_cons, esize, encode_data,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr

/-- Polynomial boundedness transfers to the genuine detyped sampler. -/
theorem sampler_timeBoundAt (hℓ : 0 < ℓ) (n B k : ℕ) (h : S.TimeBoundAt n B k) :
    ∃ B' k', (sampler E S hℓ).TimeBoundAt n B' k' := by
  let Q := samplerCost E n B k
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i, Q.natDegree, ?_⟩
  intro q
  obtain ⟨r, time, ht, hr⟩ := sampler_haltsWithin E S hℓ n B k h q
  exact ⟨r, time, ht.trans ((polynomial_eval_mono Q (Nat.le_succ q.size)).trans
    (polynomial_eval_le_sum_coeff_mul_pow Q (by omega))), hr⟩

/-- Detyping preserves a polynomial query bound with a degree independent of `n`. -/
theorem sampler_timeBoundAt_uniform_degree (hℓ : 0 < ℓ) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) :
    (sampler E S hℓ).TimeBoundAt n (samplerCoefficient E n B k) (samplerDegree E k) := by
  let Q := samplerCost E n B k
  have hQ : (sampler E S hℓ).TimeBoundAt n (samplerCoefficient E n B k) Q.natDegree := by
    intro q
    obtain ⟨r, time, ht, hr⟩ := sampler_haltsWithin E S hℓ n B k h q
    exact ⟨r, time, ht.trans ((polynomial_eval_mono Q (Nat.le_succ q.size)).trans
      (polynomial_eval_le_sum_coeff_mul_pow Q (by omega))), hr⟩
  exact hQ.mono le_rfl (samplerCost_natDegree_le E n B k)

/-- The actual detyped sampler has a global bound whenever the typed sampler does. -/
theorem sampler_timeBound (hℓ : 0 < ℓ) (B : ℕ → ℕ) (k : ℕ)
    (h : ∀ n, S.TimeBoundAt n (B n) k) :
    (sampler E S hℓ).TimeBound (fun n => samplerCoefficient E n (B n) k)
      (samplerDegree E k) := fun n => sampler_timeBoundAt_uniform_degree E S hℓ n (B n) k (h n)

end MIPRE.CL.Detyping
