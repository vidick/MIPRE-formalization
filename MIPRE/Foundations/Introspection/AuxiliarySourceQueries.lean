/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.ClockedQueryProgram
import MIPRE.Foundations.LowDegree.BinaryMatrixSolve
import MIPRE.Foundations.CL.DetypingProgParse

/-! # Executable source queries and matrix reconstruction

The clock is supplied once as unary data. Matrix reconstruction queries the
linear map on the standard basis and transposes those columns. All operations
are polynomial in the explicit clock, source text, and register length.
Correctness is used only after the prefix scan establishes the source
interface's attained-prefix premise.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliarySource
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear

abbrev Context := Unary × Prog × ℕ × Bool × ℕ × BitStr

def budget : PolyTimeFun Context Unary := fst
def source : PolyTimeFun Context Prog := fst.comp snd
def index : PolyTimeFun Context ℕ := fst.comp (snd.comp snd)
def player : PolyTimeFun Context Bool := fst.comp (snd.comp (snd.comp snd))
def level : PolyTimeFun Context ℕ := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def inputPrefix : PolyTimeFun Context BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def queryInput (kind : ℕ) : PolyTimeFun (BitStr × Context) Data :=
  encoded.comp ((index.comp snd).pair ((const kind).pair ((player.comp snd).pair
    ((level.comp snd).pair ((inputPrefix.comp snd).pair fst)))))

def query (U : ClockedUniversalMachine) (kind : ℕ) : PolyTimeFun (BitStr × Context) Data :=
  (ClockedQuery.run U).comp ((budget.comp snd).pair ((source.comp snd).pair (queryInput kind)))

theorem query_apply (U : ClockedUniversalMachine) (kind : ℕ) (y : BitStr)
    (b : Unary) (S : Prog) (n : ℕ) (w : Bool) (j : ℕ) (u : BitStr) :
    query U kind (y, b, S, n, w, j, u) =
      clockedResult S (encode (n, kind, Player.ofBool w, j, u, y)) b.length := by
  cases w <;> rfl

/-- Read a returned bit string; malformed results also terminate. -/
def linear (U : ClockedUniversalMachine) : PolyTimeFun (BitStr × Context) BitStr :=
  readBits.comp (treeTail.comp (query U 2))

def factor (U : ClockedUniversalMachine) : PolyTimeFun Context BitStr :=
  (readBits.comp (treeTail.comp (query U 3))).comp ((const []).pair (PolyTimeFun.id _))

theorem linear_correct (U : ClockedUniversalMachine) (y v : BitStr)
    (b : Unary) (S : Prog) (n : ℕ) (w : Bool) (j : ℕ) (u : BitStr)
    (h : clockedResult S (encode (n, CL.Sampler.Query.linear (Player.ofBool w) j u y)) b.length =
      .cons (encode true) (encode v)) :
    linear U (y, b, S, n, w, j, u) = v := by
  simp only [linear, comp_apply, query_apply]
  change readBits (treeTail (clockedResult S
    (encode (n, CL.Sampler.Query.linear (Player.ofBool w) j u y)) b.length)) = v
  rw [h, treeTail_cons, readBits_encode]

theorem factor_correct (U : ClockedUniversalMachine) (v : BitStr)
    (b : Unary) (S : Prog) (n : ℕ) (w : Bool) (j : ℕ) (u : BitStr)
    (h : clockedResult S (encode (n, CL.Sampler.Query.factor (Player.ofBool w) j u)) b.length =
      .cons (encode true) (encode v)) :
    factor U (b, S, n, w, j, u) = v := by
  simp only [factor, comp_apply, pair_apply, const_apply, id_apply, query_apply]
  change readBits (treeTail (clockedResult S
    (encode (n, CL.Sampler.Query.factor (Player.ofBool w) j u)) b.length)) = v
  rw [h, treeTail_cons, readBits_encode]

/-- Collect the matrix using a polynomial number of source calls. -/
def matrix (U : ClockedUniversalMachine) : PolyTimeFun Context (List BitStr) :=
  let width := length.comp inputPrefix
  let columns := (mapWith (linear U)).comp
    ((identityBitsProg.comp width).pair (PolyTimeFun.id _))
  transposeBitsProg.comp (width.pair columns)

set_option backward.isDefEq.respectTransparency false in
theorem matrix_correct (U : ClockedUniversalMachine) (ctx : Context) {n : ℕ}
    (L : (Fin n → CL.𝔽₂) →ₗ[CL.𝔽₂] (Fin n → CL.𝔽₂))
    (hn : (inputPrefix ctx).length = n)
    (h : ∀ x : Fin n → CL.𝔽₂, linear U (vectorBits x, ctx) = vectorBits (L x)) :
    matrix U ctx = matrixBits (LinearMap.toMatrix' L) := by
  change transposeBits (unary (inputPrefix ctx).length).length
    ((identityBits (unary (inputPrefix ctx).length).length).map
      (fun v => linear U (v, ctx))) = _
  simp only [length_unary]
  rw [hn, identityBits_eq_matrixBits]
  have hc : (matrixBits (1 : Matrix (Fin n) (Fin n) CL.𝔽₂)).map
      (fun v => linear U (v, ctx)) = matrixBits (LinearMap.toMatrix' L).transpose := by
    simp only [matrixBits, List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply]
    have hi : (1 : Matrix (Fin n) (Fin n) CL.𝔽₂) j = Pi.single j 1 := by
      funext i
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [hi, h]
    congr 1
  rw [hc, transposeBits_matrixBits, Matrix.transpose_transpose]

end MIPRE.Introspection.AuxiliarySource
end
