/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SourcePaddingQueries
import MIPRE.Foundations.Introspection.AuxiliarySourceQueries
import MIPRE.Foundations.Introspection.AuxiliaryRegisterBits

/-! # Uniform programs for queries to a padded source

Source width is input data. The full register width is read from the prefix.
Source queries receive only the original prefix and vector coordinates;
their answers are extended to the full register. The first factor consumes
the unused suffix and all later factors leave it empty.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding.Program
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram

abbrev QContext := Unary × AuxiliarySource.Context

def sourceWidth : PolyTimeFun QContext Unary := fst
def fullWidth : PolyTimeFun QContext Unary := length.comp (AuxiliarySource.inputPrefix.comp snd)
def suffixWidth : PolyTimeFun QContext Unary := drop.comp (fullWidth.pair sourceWidth)

def sourceContext : PolyTimeFun QContext AuxiliarySource.Context :=
  (AuxiliarySource.budget.comp snd).pair ((AuxiliarySource.source.comp snd).pair
    ((AuxiliarySource.index.comp snd).pair ((AuxiliarySource.player.comp snd).pair
      ((AuxiliarySource.level.comp snd).pair
        (take.comp ((AuxiliarySource.inputPrefix.comp snd).pair sourceWidth))))))

theorem sourceContext_apply (s b : Unary) (S : Prog) (n : ℕ) (w : Bool) (j : ℕ) (u : BitStr) :
    sourceContext (s, b, S, n, w, j, u) = (b, S, n, w, j, u.take s.length) := rfl

def linear (U : ClockedUniversalMachine) : PolyTimeFun (BitStr × QContext) BitStr :=
  let input := take.comp (fst.pair (sourceWidth.comp snd))
  let output := (AuxiliarySource.linear U).comp (input.pair (sourceContext.comp snd))
  append.comp (output.pair (replicate.comp ((suffixWidth.comp snd).pair (const false))))

theorem linear_apply (U : ClockedUniversalMachine) (y : BitStr) (s : Unary)
    (ctx : AuxiliarySource.Context) :
    linear U (y, s, ctx) = AuxiliarySource.linear U
      (y.take s.length, sourceContext (s, ctx)) ++
      List.replicate ((AuxiliarySource.inputPrefix ctx).length - s.length) false := by
  simp [linear, suffixWidth, fullWidth, sourceWidth]

def factor (U : ClockedUniversalMachine) : PolyTimeFun QContext BitStr :=
  let first := SAT.ArrayProg.eqNat.comp ((AuxiliarySource.level.comp snd).pair (const 1))
  append.comp (((AuxiliarySource.factor U).comp sourceContext).pair
    (replicate.comp (suffixWidth.pair first)))

theorem factor_apply (U : ClockedUniversalMachine) (s : Unary) (ctx : AuxiliarySource.Context) :
    factor U (s, ctx) = AuxiliarySource.factor U (sourceContext (s, ctx)) ++
      List.replicate ((AuxiliarySource.inputPrefix ctx).length - s.length)
        (decide (AuxiliarySource.level ctx = 1)) := by
  simp [factor, suffixWidth, fullWidth, sourceWidth]

def matrix (U : ClockedUniversalMachine) : PolyTimeFun QContext (List BitStr) :=
  let columns := (mapWith (linear U)).comp
    ((identityBitsProg.comp fullWidth).pair (PolyTimeFun.id _))
  transposeBitsProg.comp (fullWidth.pair columns)

theorem toBits_pull_first {s Q : ℕ} (h : s ≤ Q) (x : Fin Q → CL.𝔽₂) :
    CL.toBits (CL.pull (firstEmbedding h) x) = (CL.toBits x).take s := by
  rw [← ofBits_take_first h x, CL.toBits_ofBits]
  simp [CL.length_toBits, Nat.min_eq_left h]

theorem linear_correct (U : ClockedUniversalMachine) {s Q : ℕ} (h : s ≤ Q)
    (ctx : AuxiliarySource.Context) (u y : Fin Q → CL.𝔽₂) (v : Fin s → CL.𝔽₂)
    (hu : AuxiliarySource.inputPrefix ctx = CL.toBits u)
    (hv : AuxiliarySource.linear U
      (CL.toBits (CL.pull (firstEmbedding h) y), sourceContext (unary s, ctx)) = CL.toBits v) :
    linear U (CL.toBits y, unary s, ctx) = CL.toBits (CL.push (firstEmbedding h) v) := by
  rw [linear_apply, length_unary, ← toBits_pull_first h, hv, hu, CL.length_toBits,
    toBits_push_first]

theorem indicatorBits_padding {s Q : ℕ} (h : s ≤ Q) (S : Finset (Fin s)) (first : Bool) :
    CL.indicatorBits (S.map (firstEmbedding h) ∪
      if first then (Finset.univ.map (firstEmbedding h))ᶜ else ∅) =
      CL.indicatorBits S ++ List.replicate (Q-s) first := by
  classical
  apply List.ext_getElem
  · simp only [CL.length_indicatorBits, List.length_append, List.length_replicate]
    omega
  · intro i hi hi'
    have hq : i < Q := by simpa using hi
    by_cases hs : i < s
    · have he : (⟨i, hq⟩ : Fin Q) = firstEmbedding h ⟨i, hs⟩ := rfl
      rw [List.getElem_append_left (by simpa using hs)]
      cases first <;> simp [CL.indicatorBits, he]
    · have hn : ¬ ∃ j, firstEmbedding h j = (⟨i, hq⟩ : Fin Q) := by
        rintro ⟨j, hj⟩
        have hjv := congrArg Fin.val hj
        change j.val = i at hjv
        exact hs (hjv ▸ j.isLt)
      rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hs)]
      cases first <;> simp [CL.indicatorBits]
      · exact fun j _ he => hn ⟨j, he⟩
      · exact Or.inr (fun j he => hn ⟨j, he⟩)

theorem factor_correct (U : ClockedUniversalMachine) {s Q ℓ : ℕ} (h : s ≤ Q)
    (L : Bool → CL.CLFun CL.𝔽₂ (Fin s) ℓ) (hℓ : 0 < ℓ) (w : Bool) (j : ℕ)
    (ctx : AuxiliarySource.Context) (u : Fin Q → CL.𝔽₂)
    (hu : AuxiliarySource.inputPrefix ctx = CL.toBits u)
    (hj : AuxiliarySource.level ctx = j + 1)
    (hf : AuxiliarySource.factor U (sourceContext (unary s, ctx)) =
      CL.indicatorBits ((L w).factorOfPrefix j (CL.pull (firstEmbedding h) u))) :
    factor U (unary s, ctx) = CL.indicatorBits
      ((depthFamily (firstEmbedding h) L w).factorOfPrefix j u) := by
  rw [factor_apply, length_unary, hf, hu, CL.length_toBits, hj,
    depthFamily_factorOfPrefix _ _ hℓ]
  simpa using (indicatorBits_padding h
    ((L w).factorOfPrefix j (CL.pull (firstEmbedding h) u)) (decide (j = 0))).symm

set_option backward.isDefEq.respectTransparency false in
theorem matrix_correct (U : ClockedUniversalMachine) (ctx : QContext) {Q : ℕ}
    (L : (Fin Q → CL.𝔽₂) →ₗ[CL.𝔽₂] (Fin Q → CL.𝔽₂))
    (hn : (AuxiliarySource.inputPrefix ctx.2).length = Q)
    (h : ∀ x : Fin Q → CL.𝔽₂, linear U (vectorBits x, ctx) = vectorBits (L x)) :
    matrix U ctx = matrixBits (LinearMap.toMatrix' L) := by
  change transposeBits (unary (AuxiliarySource.inputPrefix ctx.2).length).length
    ((identityBits (unary (AuxiliarySource.inputPrefix ctx.2).length).length).map
      (fun v => linear U (v, ctx))) = _
  simp only [length_unary]
  rw [hn, identityBits_eq_matrixBits]
  have hc : (matrixBits (1 : Matrix (Fin Q) (Fin Q) CL.𝔽₂)).map
      (fun v => linear U (v, ctx)) = matrixBits (LinearMap.toMatrix' L).transpose := by
    simp only [matrixBits, List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply]
    have hi : (1 : Matrix (Fin Q) (Fin Q) CL.𝔽₂) j = Pi.single j 1 := by
      funext i
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [hi, h]
    congr 1
  rw [hc, transposeBits_matrixBits, Matrix.transpose_transpose]

/-- Read the source dimension with the already supplied source clock. -/
def dimension (U : ClockedUniversalMachine) : PolyTimeFun AuxiliarySource.Context ℕ :=
  let query := encoded.comp
    (AuxiliarySource.index.pair (const CL.Sampler.Query.dimension))
  readNat.comp (treeTail.comp ((ClockedQuery.run U).comp
    (AuxiliarySource.budget.pair (AuxiliarySource.source.pair query))))

theorem dimension_correct (U : ClockedUniversalMachine) (ctx : AuxiliarySource.Context) (s : ℕ)
    (h : clockedResult (AuxiliarySource.source ctx)
      (encode (AuxiliarySource.index ctx, CL.Sampler.Query.dimension))
      (AuxiliarySource.budget ctx).length = .cons (encode true) (encode s)) :
    dimension U ctx = s := by
  simp only [dimension, comp_apply, pair_apply, const_apply, encoded_apply, ClockedQuery.run_apply]
  rw [h, treeTail_cons, readNat_encode]

/-- Cap the dimension by the actual full prefix length before creating unary
data. Consequently arbitrary dimension-query results cannot cause large allocation. -/
def adapt (U : ClockedUniversalMachine) : PolyTimeFun AuxiliarySource.Context QContext :=
  (DynamicParser.boundedOffset.comp (AuxiliarySource.inputPrefix.pair (dimension U))).pair
    (PolyTimeFun.id _)

theorem adapt_correct (U : ClockedUniversalMachine) (ctx : AuxiliarySource.Context) (s : ℕ)
    (hs : s ≤ (AuxiliarySource.inputPrefix ctx).length) (hd : dimension U ctx = s) :
    adapt U ctx = (unary s, ctx) := by
  simp only [adapt, pair_apply, comp_apply, id_apply, hd, DynamicParser.boundedOffset_apply,
    Nat.min_eq_left hs]

/-- The original scan context is sufficient: width is queried at runtime. -/
def factorFromContext (U : ClockedUniversalMachine) : PolyTimeFun AuxiliarySource.Context BitStr :=
  (factor U).comp (adapt U)

def matrixFromContext (U : ClockedUniversalMachine) :
    PolyTimeFun AuxiliarySource.Context (List BitStr) := (matrix U).comp (adapt U)

theorem factorFromContext_correct (U : ClockedUniversalMachine)
    (ctx : AuxiliarySource.Context) (s : ℕ)
    (hs : s ≤ (AuxiliarySource.inputPrefix ctx).length) (hd : dimension U ctx = s) :
    factorFromContext U ctx = factor U (unary s, ctx) := by
  rw [factorFromContext, comp_apply, adapt_correct U ctx s hs hd]

theorem matrixFromContext_correct (U : ClockedUniversalMachine)
    (ctx : AuxiliarySource.Context) (s : ℕ)
    (hs : s ≤ (AuxiliarySource.inputPrefix ctx).length) (hd : dimension U ctx = s) :
    matrixFromContext U ctx = matrix U (unary s, ctx) := by
  rw [matrixFromContext, comp_apply, adapt_correct U ctx s hs hd]

end MIPRE.Introspection.SourcePadding.Program
end
