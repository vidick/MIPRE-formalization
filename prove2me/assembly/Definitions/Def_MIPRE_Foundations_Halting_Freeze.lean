/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Freeze.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped

/-!
# Freezing a verifier at an index

Blueprint `rem:compression-abstract`, item 2: the recursion of the compressibility criterion
goes `n → 2n + 1`, while gap-preserving compression relates the game at index `2 ^ n` to the
output at index `n`; the two are reconciled by *freezing* the described verifier at index
`2n + 1` before compressing it. The frozen verifier answers at every index as the original
does at the frozen index, so its game at index `2 ^ n` is the original's game at level
`2n + 1`.

* `Cost.Prog.freezeProg k p`: on input `cons N d`, run `p` on `cons (encode k) d`. Its cost
  is that of `p` plus the cost of copying the input, which is what the reading of the time
  bounds a polynomial in the size of the input (`Decider.TimeBoundAt`) allows.
* `CL.Sampler.freeze`, `Decider.freeze`, `Verifier.freeze`: the frozen sampler, decider and
  verifier, with the transfer of the query clauses, of acceptance (`Decider.freeze_accepts`),
  of the values and perfect PCC strategies (`Verifier.freeze_valStar`,
  `Verifier.freeze_hasPerfectPCC`), of the time bounds, and of `λ`-boundedness
  (`Verifier.freeze_isBounded`): the frozen verifier is `λ`-bounded as soon as the original's
  dimension, running times and size at the frozen index fit under `2 ^ λ` and `λ`.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

/-- Freeze the index: on input `cons N d`, run `p` on `cons (encode k) d`. -/
def freezeProg (k : ℕ) (p : Prog) : Prog :=
  .let_ (.elim 0 .nil (.cons (.const (encode k)) (.var 1))) p

theorem freezeProg_wellScoped {p : Prog} (hp : p.WellScoped 1) (k : ℕ) :
    (freezeProg k p).WellScoped 1 :=
  ⟨by simp [WellScoped], hp.mono (by omega) _⟩

/-- The run of the index-replacing prefix of `freezeProg`. -/
theorem freezeProg_prefix_eval (k : ℕ) (N d : Data) :
    Eval [.cons N d] (.elim 0 .nil (.cons (.const (encode k)) (.var 1))) (.cons (encode k) d)
      ((encode k : Data).size + (d.size + 1) + 1 + 1) :=
  Eval.elim_cons (i := 0) (a := N) (b := d) (by simp)
    (Eval.cons (Eval.const _ _) (Eval.var_of_get (i := 1) (v := d) (by simp)))

/-- Forward transfer: a run of `p` at the frozen index gives a run of `freezeProg k p` at any
index, at the additional cost of copying the input. -/
theorem freezeProg_runs {p : Prog} (hp : p.WellScoped 1) {k : ℕ} {N d r : Data} {t : ℕ}
    (h : p.Runs (.cons (encode k) d) r t) :
    (freezeProg k p).Runs (.cons N d) r (t + esize k + d.size + 4) :=
  (Eval.let_ (freezeProg_prefix_eval k N d) (Eval.append_of_wellScoped h hp [.cons N d])).cast_cost
    (by unfold esize; omega)

/-- Backward transfer: a run of `freezeProg k p` is a run of `p` at the frozen index. -/
theorem freezeProg_runs_rev {p : Prog} (hp : p.WellScoped 1) {k : ℕ} {N d r : Data} {t : ℕ}
    (h : (freezeProg k p).Runs (.cons N d) r t) :
    ∃ t' ≤ t, p.Runs (.cons (encode k) d) r t' := by
  change Eval [.cons N d] (.let_ _ p) r t at h
  cases h with
  | let_ h₁ h₂ =>
    obtain ⟨rfl, -⟩ := h₁.deterministic (freezeProg_prefix_eval k N d)
    exact ⟨_, by omega,
      Eval.of_append_of_wellScoped (env := [.cons (encode k) d]) (extra := [.cons N d]) h₂ hp⟩

/-- The frozen program halts on `cons N d` exactly when `p` halts on `cons (encode k) d`,
with the same result. -/
theorem freezeProg_runs_iff {p : Prog} (hp : p.WellScoped 1) (k : ℕ) (N d r : Data) :
    (∃ t, (freezeProg k p).Runs (.cons N d) r t) ↔ ∃ t, p.Runs (.cons (encode k) d) r t :=
  ⟨fun ⟨_, h⟩ => let ⟨t', _, h'⟩ := freezeProg_runs_rev hp h; ⟨t', h'⟩,
    fun ⟨_, h⟩ => ⟨_, freezeProg_runs hp h⟩⟩

end Cost.Prog

/-! ## The frozen sampler -/

namespace CL.Sampler

variable {ℓ : ℕ} (S : Sampler ℓ)

/-- The sampler frozen at index `k`: at every index it presents the CL functions of `S` at
index `k`, its program being `freezeProg k S.prog`. -/
def freeze (k : ℕ) : Sampler ℓ where
  prog := Prog.freezeProg k S.prog
  closed := Prog.freezeProg_wellScoped S.closed k
  dim _ := S.dim k
  cl _ w := S.cl k w
  cl_exactlyOn _ w := S.cl_exactlyOn k w
  runs_dimension _ :=
    let ⟨_, h⟩ := S.runs_dimension k
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  runs_marginal _ w j z h₁ h₂ hz :=
    let ⟨_, h⟩ := S.runs_marginal k w j z h₁ h₂ hz
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  runs_linear _ w j u y h₁ h₂ hu hy :=
    let ⟨_, h⟩ := S.runs_linear k w j u y h₁ h₂ hu hy
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  runs_factor _ w j u h₁ h₂ hu :=
    let ⟨_, h⟩ := S.runs_factor k w j u h₁ h₂ hu
    ⟨_, Prog.freezeProg_runs S.closed h⟩
  halts _ d :=
    let ⟨r, _, h⟩ := S.halts k d
    ⟨r, _, Prog.freezeProg_runs S.closed h⟩

@[simp] theorem freeze_prog (k : ℕ) : (S.freeze k).prog = Prog.freezeProg k S.prog := rfl

@[simp] theorem freeze_dim (k n : ℕ) : (S.freeze k).dim n = S.dim k := rfl

@[simp] theorem freeze_cl (k n : ℕ) (w : Player) : (S.freeze k).cl n w = S.cl k w := rfl

end CL.Sampler

/-! ## The frozen decider -/

namespace Decider

variable (D : Decider)

/-- The decider frozen at index `k`: at every index it decides as `D` does at index `k`. -/
def freeze (k : ℕ) : Decider :=
  ⟨Prog.freezeProg k D.prog, Prog.freezeProg_wellScoped D.closed k⟩

@[simp] theorem freeze_prog (k : ℕ) : (D.freeze k).prog = Prog.freezeProg k D.prog := rfl

theorem freeze_accepts (k n : ℕ) (x y a b : BitStr) :
    (D.freeze k).Accepts n x y a b ↔ D.Accepts k x y a b :=
  Prog.freezeProg_runs_iff D.closed k (encode n) (encode (x, y, a, b)) (encode true)

end Decider

/-! ## The frozen verifier -/

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The verifier frozen at index `k`: its game at every index is the game of `V` at index
`k`. -/
def freeze (k : ℕ) : Verifier ℓ where
  sampler := V.sampler.freeze k
  decider := V.decider.freeze k
  accepts_length _ x y a b h := V.accepts_length k x y a b ((V.decider.freeze_accepts k _ x y a b).1 h)

@[simp] theorem freeze_sampler (k : ℕ) : (V.freeze k).sampler = V.sampler.freeze k := rfl

@[simp] theorem freeze_decider (k : ℕ) : (V.freeze k).decider = V.decider.freeze k := rfl

end Verifier

end MIPRE
