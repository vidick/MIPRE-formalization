/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgFinite

/-! # A total query router with at most one sampler call

The preprocessing program either supplies a direct result, or an argument and
continuation context. Only the latter branch calls the supplied sampler. The
postprocessor is total on raw data, so malformed inputs preserve termination
whenever routing preserves the sampler index.
-/

namespace MIPRE.Cost

open PolyTimeFun

namespace Prog

def callWithContext (p : Prog) (post : PolyTimeFun (Data × Data) Data) : Prog :=
  .let_ fstProg (.let_ p
    (.let_ (.cons (callVar 2 sndProg) (.var 0)) post.code))

theorem callWithContext_closed {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) : (callWithContext p post).WellScoped 1 := by
  refine ⟨fstProg_wellScoped, hp.mono (by omega) _, ?_⟩
  exact ⟨⟨callVar_wellScoped (by decide) sndProg_wellScoped, by simp [WellScoped]⟩,
    post.closed.mono (by omega) _⟩

theorem callWithContext_runs {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (a ctx r : Data) (time : ℕ)
    (hr : p.Runs a r time) :
    ∃ t, (callWithContext p post).Runs (.cons a ctx) (post (ctx, r)) t := by
  obtain ⟨tp, _, hpRun⟩ := post.computes (ctx, r)
  have ectx := callVar_eval (env := [r, a, Data.cons a ctx]) (i := 2)
    sndProg_wellScoped (by simp) (sndProg_runs a ctx)
  exact ⟨_, Eval.let_ (fstProg_runs a ctx)
    (Eval.let_ (Eval.append_of_wellScoped hr hp _)
      (Eval.let_ (Eval.cons ectx (Eval.var_of_get (i := 0) (by simp)))
        (Eval.append_of_wellScoped hpRun post.closed _)))⟩

def routeOneCall (route : PolyTimeFun Data (Bool × Data))
    (p : Prog) (post : PolyTimeFun (Data × Data) Data) : Prog :=
  .let_ route.code (.elim 0 .nil (.elim 0 (.var 1)
    (callVar 3 (callWithContext p post))))

theorem routeOneCall_closed (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data) :
    (routeOneCall route p post).WellScoped 1 := by
  exact ⟨route.closed, by decide, trivial, by decide, by simp [WellScoped],
    callVar_wellScoped (by decide) (callWithContext_closed hp post)⟩

theorem routeOneCall_direct (route : PolyTimeFun Data (Bool × Data))
    (p : Prog) (post : PolyTimeFun (Data × Data) Data) (x r : Data)
    (h : route x = (false, r)) : ∃ t, (routeOneCall route p post).Runs x r t := by
  obtain ⟨t, _, hr⟩ := route.computes x
  rw [h] at hr
  exact ⟨_, Eval.let_ hr
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := r) (by simp [encode, Data.ofBool])
      (Eval.elim_nil (i := 0) (by simp) (Eval.var_of_get (i := 1) (by simp))))⟩

theorem routeOneCall_indirect (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (x a ctx r : Data) (time : ℕ) (h : route x = (true, .cons a ctx))
    (hr : p.Runs a r time) :
    ∃ t, (routeOneCall route p post).Runs x (post (ctx, r)) t := by
  obtain ⟨t, _, hroute⟩ := route.computes x
  rw [h] at hroute
  obtain ⟨tc, hc⟩ := callWithContext_runs hp post a ctx r time hr
  exact ⟨_, Eval.let_ hroute
    (Eval.elim_cons (i := 0) (a := Data.cons .nil .nil) (b := .cons a ctx)
      (by simp [encode, Data.ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := .nil) (by simp)
        (callVar_eval (i := 3) (callWithContext_closed hp post) (by simp) hc)))⟩

/-- Halting is preserved if each routed call retains the original index. -/
theorem routeOneCall_halts (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (n : ℕ) (q : Data)
    (halts : ∀ d, Halts p (.cons (encode n) d))
    (preserves : ∀ a, route (.cons (encode n) q) = (true, a) →
      ∃ d ctx, a = .cons (.cons (encode n) d) ctx) :
    Halts (routeOneCall route p post) (.cons (encode n) q) := by
  cases h : route (.cons (encode n) q) with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨t, hr⟩ := routeOneCall_direct route p post _ payload h
      exact ⟨payload, t, hr⟩
    | true =>
      obtain ⟨d, ctx, rfl⟩ := preserves payload h
      obtain ⟨r, time, hr⟩ := halts d
      obtain ⟨t, hout⟩ := routeOneCall_indirect route hp post _ _ ctx r time h hr
      exact ⟨_, t, hout⟩

end Prog
end MIPRE.Cost
