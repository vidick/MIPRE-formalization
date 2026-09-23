/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryScanStage

/-! # The fixed-depth polynomial-time Gaussian scan program

The source depth is a compiler constant (seven in introspection). Each stage
is a composition of actual polynomial-time programs. A failed stage stops
all subsequent source queries. The register width comes from the actual
claimed answer, so malformed data never causes a binary-sized allocation.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryScan
open Cost Cost.PolyTimeFun

abbrev Input := AuxiliarySource.Context × BitStr

def contextAt (ctx : AuxiliarySource.Context) (j : ℕ) (u : BitStr) : AuxiliarySource.Context :=
  (ctx.1, ctx.2.1, ctx.2.2.1, ctx.2.2.2.1, j, u)

def nextContext (k : ℕ) : PolyTimeFun (Input × State) AuxiliarySource.Context :=
  let ctx : PolyTimeFun (Input × State) AuxiliarySource.Context := fst.comp fst
  (AuxiliarySource.budget.comp ctx).pair ((AuxiliarySource.source.comp ctx).pair
    ((AuxiliarySource.index.comp ctx).pair ((AuxiliarySource.player.comp ctx).pair
      ((const (k + 1)).pair (fst.comp (snd.comp snd))))))

def advance (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ) :
    PolyTimeFun (Input × State) State :=
  ite (fst.comp snd)
    ((stage f m).comp ((nextContext k).pair
      ((snd.comp fst).pair (snd.comp (snd.comp snd)))))
    (const (false, [], []))

theorem advance_apply (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ)
    (ctx : AuxiliarySource.Context) (y : BitStr) (b : Bool) (u x : BitStr) :
    advance f m k ((ctx, y), b, u, x) =
      if b then stage f m (contextAt ctx (k + 1) u, y, x) else (false, [], []) := by
  cases b <;> rfl

def zeros : PolyTimeFun BitStr BitStr := map (const false)

theorem zeros_toBits {n : ℕ} (y : Fin n → CL.𝔽₂) :
    zeros (CL.toBits y) = CL.toBits (0 : Fin n → CL.𝔽₂) := by
  change (CL.toBits y).map (fun _ => false) = _
  simp [CL.toBits]

def program (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) : ℕ → PolyTimeFun Input State
  | 0 => (const true).pair ((zeros.comp snd).pair (zeros.comp snd))
  | k + 1 => (advance f m k).comp ((PolyTimeFun.id _).pair (program f m k))

theorem program_zero (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    (y : BitStr) : program f m 0 (ctx, y) = (true, zeros y, zeros y) := rfl

theorem program_succ (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ)
    (ctx : AuxiliarySource.Context) (y : BitStr) :
    program f m (k + 1) (ctx, y) = advance f m k ((ctx, y), program f m k (ctx, y)) := rfl

end MIPRE.Introspection.AuxiliaryScan
end
