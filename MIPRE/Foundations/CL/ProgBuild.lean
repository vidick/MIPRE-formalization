/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.CL.DetypingProgCall
import MIPRE.Foundations.CL.DetypingProgParse

/-!
# Building programs in polynomial time

A program is data (`Prog.toData`), so placing variable subprograms in a fixed context is a
polynomial-time function of the subprograms: `letF` for `let e in b`, `elimF` for
`elim i n c`, and from them `routeOneCallF` for a router with one call to a variable program.
These are how a verifier's programs are computed from its input programs when the input programs
enter as code rather than as data (the detyping compiler's).
-/

namespace MIPRE.CL.ProgBuild

open Cost Cost.PolyTimeFun Detyping.Program

/-- `(e, b) ↦ let e in b`, in polynomial time. -/
noncomputable def letF : PolyTimeFun (Prog × Prog) Prog :=
  PolyTimeFun.cast (ap₂ treePair (const (Data.ofNat 4)) (encoded : PolyTimeFun (Prog × Prog) Data))
    (fun p => Prog.let_ p.1 p.2) (fun _ => rfl)

@[simp] theorem letF_apply (e b : Prog) : letF (e, b) = Prog.let_ e b := rfl

/-- `c ↦ elim i n c`, in polynomial time. -/
noncomputable def elimF (i : ℕ) (n : Prog) : PolyTimeFun Prog Prog :=
  PolyTimeFun.cast (ap₂ treePair (const (Data.ofNat 3)) (ap₂ treePair (const (Data.ofNat i))
    (ap₂ treePair (const n.toData) (encoded : PolyTimeFun Prog Data))))
    (fun c => Prog.elim i n c) (fun _ => rfl)

@[simp] theorem elimF_apply (i : ℕ) (n c : Prog) : elimF i n c = Prog.elim i n c := rfl

/-- `p ↦ callWithContext p post`, in polynomial time. -/
noncomputable def callWithContextF (post : PolyTimeFun (Data × Data) Data) : PolyTimeFun Prog Prog :=
  letF.comp ((const Prog.fstProg).pair (letF.comp ((PolyTimeFun.id Prog).pair
    (const (Prog.let_ (.cons (Prog.callVar 2 Prog.sndProg) (.var 0)) post.code)))))

@[simp] theorem callWithContextF_apply (post : PolyTimeFun (Data × Data) Data) (p : Prog) :
    callWithContextF post p = Prog.callWithContext p post := rfl

/-- `p ↦ routeOneCall route p post`, in polynomial time. -/
noncomputable def routeOneCallF (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) : PolyTimeFun Prog Prog :=
  letF.comp ((const route.code).pair ((elimF 0 .nil).comp ((elimF 0 (.var 1)).comp
    (letF.comp ((const (.var 3)).pair (callWithContextF post))))))

@[simp] theorem routeOneCallF_apply (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (p : Prog) :
    routeOneCallF route post p = Prog.routeOneCall route p post := rfl

end MIPRE.CL.ProgBuild
