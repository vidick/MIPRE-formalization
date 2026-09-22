/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliRowPrograms
import MIPRE.Background.QLD.TypeEncoding
import MIPRE.Foundations.Introspection.PauliFactorProg
import MIPRE.Foundations.CL.TypedSampler
import MIPRE.Foundations.CL.DetypingProgRoute

/-! # The actual uniform Pauli query router

Every input tree is parsed by total programs. Dimension, marginal, linear and
factor queries use the uniform programs on the supplied parameters; the type
table is the fixed twenty-six-element table only.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL.SamplerProgram
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
open Introspection.PauliStageProgram

def dimensionProg : PolyTimeFun Parameters ℕ :=
  unaryToBin.comp (length.comp (factorBits.comp ((PolyTimeFun.id _).pair (const 1))))

theorem dimensionProg_apply (p : Parameters) :
    dimensionProg p = (3 * p.2.2.length + 3) * p.1.length := by
  simp [dimensionProg, factorBits_length]

abbrev RawInput := Parameters × Data

def parsed : PolyTimeFun RawInput Parsed :=
  parse.comp (ap₂ treePair (const (encode (0 : ℕ))) (treeTail.comp snd))
def tag : PolyTimeFun RawInput Tag := typeTag.comp (treeHead.comp snd)
def level : PolyTimeFun RawInput ℕ := pLevel.comp parsed
def inputU : PolyTimeFun RawInput BitStr := pU.comp parsed
def inputY : PolyTimeFun RawInput BitStr := pY.comp parsed

def marginalInput : PolyTimeFun RawInput BinaryInput :=
  fst.pair (tag.pair (level.pair (inputU.pair inputU)))
def linearInput : PolyTimeFun RawInput BinaryInput :=
  fst.pair (tag.pair (level.pair (inputU.pair inputY)))

def query : PolyTimeFun RawInput Data :=
  ite (rawTruthProg.comp snd)
    (ite (ap₂ SAT.ArrayProg.eqNat (pKind.comp parsed) (const 1))
      (encoded.comp (marginalBits.comp marginalInput))
      (ite (ap₂ SAT.ArrayProg.eqNat (pKind.comp parsed) (const 2))
        (encoded.comp (linearBits.comp linearInput))
        (ite (ap₂ SAT.ArrayProg.eqNat (pKind.comp parsed) (const 3))
          (encoded.comp (factorBits.comp (fst.pair level))) (const .nil))))
    (encoded.comp (dimensionProg.comp fst))

theorem parsed_atType (p : Parameters) (T : Ty) (q : Sampler.Query) :
    parsed (p, encode (TypedSampler.Query.atType T q)) =
      (encode (0 : ℕ), q.toTuple.1, q.toTuple.2.1.toBool, q.toTuple.2.2.1,
        q.toTuple.2.2.2.1, q.toTuple.2.2.2.2) := by
  change parse (encode (0, q)) = _
  exact parse_query 0 q

theorem tag_atType (p : Parameters) (T : Ty) (q : Sampler.Query) :
    tag (p, encode (TypedSampler.Query.atType T q)) = programTag T := by
  change typeTag (encode T) = _
  exact typeTag_encode T

theorem query_dimension (p : Parameters) :
    query (p, encode (TypedSampler.Query.dimension : TypedSampler.Query Ty)) =
      encode ((3 * p.2.2.length + 3) * p.1.length) := by
  change encode (dimensionProg p) = _
  rw [dimensionProg_apply]

theorem query_marginal (p : Parameters) (w : Player) (T : Ty) (r : ℕ) (z : BitStr) :
    query (p, encode (TypedSampler.Query.atType T (.marginal w r z))) =
      encode (marginalBits (p, programTag T, r, z, z)) := by
  simp only [query, PolyTimeFun.ite_apply, PolyTimeFun.comp_apply,
    PolyTimeFun.pair_apply, PolyTimeFun.ap₂_apply, PolyTimeFun.const_apply,
    PolyTimeFun.fst_apply, PolyTimeFun.snd_apply, parsed_atType, tag_atType,
    marginalInput, level, inputU, encoded_apply, pKind, pLevel, pU,
    Sampler.Query.toTuple, SAT.ArrayProg.eqNat_apply]
  rfl

theorem query_linear (p : Parameters) (w : Player) (T : Ty) (r : ℕ) (u y : BitStr) :
    query (p, encode (TypedSampler.Query.atType T (.linear w r u y))) =
      encode (linearBits (p, programTag T, r, u, y)) := by
  simp only [query, PolyTimeFun.ite_apply, PolyTimeFun.comp_apply,
    PolyTimeFun.pair_apply, PolyTimeFun.ap₂_apply, PolyTimeFun.const_apply,
    PolyTimeFun.fst_apply, PolyTimeFun.snd_apply, parsed_atType, tag_atType,
    linearInput, level, inputU, inputY, encoded_apply, pKind, pLevel, pU, pY,
    Sampler.Query.toTuple, SAT.ArrayProg.eqNat_apply]
  rfl

theorem query_factor (p : Parameters) (w : Player) (T : Ty) (r : ℕ) (u : BitStr) :
    query (p, encode (TypedSampler.Query.atType T (.factor w r u))) =
      encode (factorBits (p, r)) := by
  simp only [query, PolyTimeFun.ite_apply, PolyTimeFun.comp_apply,
    PolyTimeFun.pair_apply, PolyTimeFun.ap₂_apply, PolyTimeFun.const_apply,
    PolyTimeFun.fst_apply, PolyTimeFun.snd_apply, parsed_atType, level, encoded_apply, pKind, pLevel,
    Sampler.Query.toTuple, SAT.ArrayProg.eqNat_apply]
  rfl

theorem query_runs (p : Parameters) (d : Data) :
    ∃ t ≤ query.timeBound.eval (esize (p, d)),
      query.code.Runs (encode (p, d)) (query (p, d)) t := query.computes (p, d)

end MIPRE.QLD.PauliCL.SamplerProgram
end
