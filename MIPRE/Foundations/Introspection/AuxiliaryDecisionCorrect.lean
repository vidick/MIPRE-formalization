/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryDecisionProgram
import MIPRE.Foundations.Introspection.AuxiliarySourceScan

/-! # Source semantics of the assembled auxiliary branches

The runtime context is instantiated with the existing bounded source
verifier. Every factor and matrix is obtained from its actual clocked
sampler, only at prefixes certified by the scan.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]

variable {parameters : Parameters}

def canonical (V : Verifier 7) (lam n Q R : ℕ) (parameters : Parameters) (t u : QuestionType P 7)
    (a b : BitStr) : Input P 7 :=
  ((queryContext V lam n false 0 (0 : Fin Q → CL.𝔽₂),
    ((Q,R,V.sampler.dim (2 ^ n),V.decider.prog),parameters)),(t,a),(u,b))

def padded {n Q : ℕ} (V : Verifier 7) (hQ : V.sampler.dim (2 ^ n) ≤ Q) :
    Bool → CL.CLFun CL.𝔽₂ (Fin Q) 7 :=
  depthFamily (firstEmbedding hQ) (sourceFamily V n)

theorem padded_supported {n Q : ℕ} (V : Verifier 7)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) :
    (padded V hQ w).SupportedOn Finset.univ :=
  (depthFamily_exactlyOn (firstEmbedding hQ) (sourceFamily V n) (by decide)
    (fun w => V.sampler.cl_exactlyOn _ _) w).supportedOn

omit [Fintype P] [DecidableEq P] in
theorem canonical_types (V : Verifier 7) (lam n Q R : ℕ) (t u : QuestionType P 7)
    (a b : BitStr) :
    leftType (canonical V lam n Q R parameters t u a b) = t ∧
      rightType (canonical V lam n Q R parameters t u a b) = u := ⟨rfl,rfl⟩

theorem directed_canonical (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (V : Verifier 7) (lam n Q R : ℕ)
    (t u : QuestionType P 7) (a b : BitStr) :
    directed U X Z project (canonical V lam n Q R parameters t u a b) =
      branch U X Z project (route X Z (t,u)).1 (canonical V lam n Q R parameters t u a b) :=
  directed_apply U X Z project _

/-- The Z/Sample edge compares the full register, including padding coordinates. -/
theorem directed_z_sample (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (V : Verifier 7) (lam n Q R : ℕ)
    (w : Bool) (a : BitStr) (z : Fin Q → CL.𝔽₂) (b : BitStr) :
    let x := canonical V lam n Q R parameters (.inl Z) (.inr (.sample,w)) a
      (AnswerParser.pairBits (CL.toBits z) b)
    directed U X Z project x = true ↔ project x = CL.toBits z := by
  dsimp only
  rw [directed_canonical]
  simp only [route, ↓reduceIte]
  change equal project (fst.comp rightPair) _ = true ↔ _
  rw [equal_iff]
  simp only [comp_apply, rightPair, pair_apply, fst_apply, rightBits, right, width, bounds,
    canonical, snd_apply, DynamicParser.pairParts_apply,
    AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]

/-- The actual source Sample call enforces the full padded CL relation. -/
theorem directed_sampling (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q R : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (w : Bool) (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    directed U X Z project (canonical V lam n Q R parameters
      (.inr (.introspect,w)) (.inr (.sample,w))
      (AnswerParser.pairBits (CL.toBits y) a) (AnswerParser.pairBits (CL.toBits z) b)) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧ CLChecks.sampling (padded V hs w) (y,a) (z,b) := by
  rw [directed_canonical]
  simp only [route, ↓reduceIte]
  simp only [branch, show (1 : Fin 8).val = 1 from rfl, comp_apply, pair_apply, metadata,
    finiteFunction_apply, leftType, rightType, left, right, canonical, fst_apply, snd_apply,
    route, ↓reduceIte]
  change ClockedSourceChecks.sampling U (unary (ansBound 5 lam n), V.sampler.prog,
    7,w,2 ^ n,Q,R,V.sampler.dim (2 ^ n),AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.pairBits (CL.toBits z) b) = true ↔ _
  exact ClockedSourceChecks.sampling_depthFamily U V hV hn (by decide)
    (AuxiliarySourceScan.level_size_le hV.two_le hn (by decide : 6 < 7)) hs hQ hR w y z a b

/-- Introspect/Read retains the ordinary answer cutoff and full-register question. -/
theorem directed_reading (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (V : Verifier 7) (lam n : ℕ)
    {Q R : ℕ} (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q) (w : Bool)
    (y z zp : Fin Q → CL.𝔽₂) (a b : BitStr) :
    directed U X Z project (canonical V lam n Q R parameters
      (.inr (.introspect,w)) (.inr (.read,w))
      (AnswerParser.pairBits (CL.toBits y) a)
      (AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) b)) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧ CLChecks.reading (y,a) (z,zp,b) := by
  rw [directed_canonical]
  simp only [route, ↓reduceIte]
  exact readingCheck_vectors hQ hR (2 ^ n) (V.sampler.dim (2 ^ n)) y z zp a b

/-- The first hiding edge uses the actual source's initial dual quotient. -/
theorem directed_first (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q R : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (x y yp z : Fin Q → CL.𝔽₂) (a : BitStr)
    (hp : project (canonical V lam n Q R parameters (.inl X) (.inr (.hide 0,w)) a
      (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits z))) = CL.toBits x) :
    directed U X Z project (canonical V lam n Q R parameters (.inl X) (.inr (.hide 0,w)) a
      (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits z))) = true ↔
      AuxiliaryQuotient.hidingPauli (padded V hs w) x (y,yp,z) := by
  rw [directed_canonical]
  simp only [route, Fin.val_zero, and_self, ↓reduceIte]
  simp only [branch, show (5 : Fin 8).val = 5 from rfl, comp_apply, pair_apply]
  simp only [sourceContext, contextWith, metadata, finiteFunction_apply, comp_apply,
    pair_apply, fst_apply, snd_apply, leftType, rightType, left, right, canonical,
    route, Fin.val_zero, and_self, ↓reduceIte]
  simp only [rightTriple, rightBits, right, width, bounds, context, comp_apply, pair_apply,
    fst_apply, snd_apply, DynamicParser.tripleParts_apply]
  change AuxiliaryBoundary.first (factorFromContext U) (matrixFromContext U) (queryContext V lam n w 0 (0 : Fin Q → CL.𝔽₂), project _,
    AnswerParser.tripleParts Q (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits z))) = true ↔ _
  dsimp only [canonical] at hp
  rw [hp, AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _)]
  exact AuxiliaryBoundary.first_correct_of_queries _ _ _ (padded V hs w) x y yp z
    (AuxiliarySourceScan.queriesCorrectAt U V hV hn hs w 0 0 0 (by decide))

/-- The interior hiding edge is exactly the quotient comparison together
with its two legally queried prefix conditions. -/
theorem directed_next (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q R : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (k j : Fin 7) (hk : k.val + 1 = j.val)
    (y yp x z zp t : Fin Q → CL.𝔽₂) :
    directed U X Z project (canonical V lam n Q R parameters (.inr (.hide k,w)) (.inr (.hide j,w))
      (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x))
      (AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) (CL.toBits t))) = true ↔
      (∃ a, ((padded V hs w).truncate k.val).eval a = (padded V hs w).outputPrefix k.val y) ∧
      (∃ a, ((padded V hs w).truncate (k.val+1)).eval a = (padded V hs w).outputPrefix (k.val+1) z) ∧
      AuxiliaryQuotient.hidingNext (padded V hs w) k.val (y,yp,x) (z,zp,t) := by
  rw [directed_canonical]
  simp only [route, hk, and_self, ↓reduceIte]
  simp only [branch, show (4 : Fin 8).val = 4 from rfl, choose_apply, comp_apply, snd_apply, metadata, finiteFunction_apply,
    pair_apply, leftType, rightType, left, right, canonical, fst_apply, route, hk,
    and_self, ↓reduceIte, nextBranch]
  simp only [sourceContext, contextWith, metadata, comp_apply, pair_apply, finiteFunction_apply,
    leftType, rightType, left, right, fst_apply, snd_apply, route, hk, and_self, ↓reduceIte]
  simp only [leftTriple, rightTriple, leftBits, rightBits, left, right, width, bounds, context,
    comp_apply, pair_apply, fst_apply, snd_apply, DynamicParser.tripleParts_apply]
  change AuxiliaryHiding.check (factorFromContext U) (matrixFromContext U) k.val (queryContext V lam n w 0 (0 : Fin Q → CL.𝔽₂), AnswerParser.tripleParts Q
    (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x)), AnswerParser.tripleParts Q
    (AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) (CL.toBits t))) = true ↔ _
  rw [AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _),
    AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _)]
  rw [← hk]
  exact AuxiliaryHiding.check_correct _ _ _ (padded_supported V hs w) k.val y yp x z zp t
    (fun i hi => AuxiliarySourceScan.queriesCorrectAt U V hV hn hs w 0 0 i (by omega))

/-- The terminal hiding edge compares the penultimate prefixes and full dual labels. -/
theorem directed_last (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q R : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (k : Fin 7) (hk : k.val + 1 = 7)
    (y yp x z zp : Fin Q → CL.𝔽₂) (a : BitStr) :
    directed U X Z project (canonical V lam n Q R parameters (.inr (.hide k,w)) (.inr (.read,w))
      (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x))
      (AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) a)) = true ↔
      (∃ b, ((padded V hs w).truncate 6).eval b = (padded V hs w).outputPrefix 6 y) ∧
      (∃ b, ((padded V hs w).truncate 6).eval b = (padded V hs w).outputPrefix 6 z) ∧
      CLChecks.hidingRead (padded V hs w) (y,yp,x) (z,zp,a) := by
  rw [directed_canonical]
  simp only [route, hk, and_self, ↓reduceIte]
  simp only [branch, show (3 : Fin 8).val = 3 from rfl, comp_apply, pair_apply, fst_apply]
  simp only [sourceContext, contextWith, metadata, comp_apply, pair_apply, finiteFunction_apply,
    leftType, rightType, left, right, canonical, fst_apply, snd_apply, route, hk,
    and_self, ↓reduceIte]
  simp only [leftTriple, rightTriple, leftBits, rightBits, left, right, width, bounds, context,
    comp_apply, pair_apply, fst_apply, snd_apply, DynamicParser.tripleParts_apply,
    AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _)]
  exact AuxiliaryBoundary.last_correct _ _ _ (padded_supported V hs w) y yp x z zp
    (fun i hi => AuxiliarySourceScan.queriesCorrectAt U V hV hn hs w 0 0 i (by omega))

/-- The cross-Introspect branch runs the original decision program after
the full source-membership and original-answer guards. -/
theorem directed_cross (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) (a b : BitStr) :
    let g : SourceCompiler.GuardInput :=
      (2 ^ n,Q,(2 ^ n)^lam,V.sampler.dim (2 ^ n),a,b)
    directed U X Z project (canonical V lam n Q ((2 ^ n)^lam) parameters
      (.inr (.introspect,false)) (.inr (.introspect,true)) a b) = true ↔
      SourceCompiler.GuardReady g ∧ V.decider.Accepts (2 ^ n)
        ((SourceCompiler.leftParts g).1.take (V.sampler.dim (2 ^ n)))
        ((SourceCompiler.rightParts g).1.take (V.sampler.dim (2 ^ n)))
        (SourceCompiler.leftParts g).2 (SourceCompiler.rightParts g).2 := by
  dsimp only
  rw [directed_canonical]
  simp only [route]
  exact ClockedSourceChecks.cross_original U V hV hn (V.sampler.dim (2 ^ n)) a b

/-- Unlisted directed type pairs impose no auxiliary comparison. -/
theorem directed_default (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (x : Input P 7)
    (h : (route X Z (leftType x,rightType x)).1 = 7) : directed U X Z project x = true := by
  rw [directed_apply, h]
  rfl

end MIPRE.Introspection.AuxiliaryDecision
end
