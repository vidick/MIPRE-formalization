/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.SamplerQueryProgram
import MIPRE.Background.QLD.PauliFactorPrograms
import MIPRE.Foundations.Introspection.PauliSamplerParams
import MIPRE.Foundations.Introspection.ClockCompiler

/-! # The canonical index-dependent executable Pauli sampler

The field, selector, basis and question dimension are the canonical
index-dependent choices. The sampler program computes these parameters from
the index and calls the uniform query router. Its semantic family uses the
effective Shoup self-dual basis, and all query contracts concern the actual
numbered binary vectors.

This is the canonical positive-index component. The final introspection
compiler must wrap the detyped sampler with a zero-dimensional fallback at
zero index (and zero boundedness parameter) to respect its all-index budget.
-/

noncomputable section
namespace MIPRE.Introspection.PauliSampler
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program SAT
open SourceCompiler PauliSamplerParameters QLD QLD.PauliCL

local instance registerPower_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨by have := registerPower_pos c lam n; omega⟩

def dimension (c lam n : ℕ) : ℕ :=
  (3 * registerPower c lam n + 3) * fieldBits c lam n

def presentation (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ) (T : Ty) :
    CLFun 𝔽₂ (Fin (dimension c lam n)) 3 :=
  ExplicitSeed.binaryPresentation
    (SeedProgram.selector (shoupBinField (fieldBits c lam n) (fieldBits_pos c lam n))
      (selectorBits c lam n) (selectorBits_le_fieldBits hc lam n))
    (shoupSelfDualNormalBasis (fieldBits c lam n) (fieldBits_pos c lam n)
      (fieldBits_odd he lam n)) T

theorem presentation_exactlyOn (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (T : Ty) : (presentation c hc he lam n T).ExactlyOn Finset.univ :=
  ExplicitSeed.binaryPresentation_exactlyOn _ _ _

/-- Route the index to parameter generation and retain the complete raw query. -/
def route : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (encoded.comp (readNat.comp treeHead)) treeTail)

def post : PolyTimeFun (Data × Data) Data := ap₂ treePair snd fst

def prog (c lam : ℕ) : Prog :=
  .let_ (routeOneCall route (hardcode (PauliSamplerParameters.prog c) (encode lam)) post)
    QLD.PauliCL.SamplerProgram.query.code

theorem prog_closed (c lam : ℕ) : (prog c lam).WellScoped 1 :=
  ⟨routeOneCall_closed route (hardcode_wellScoped (PauliSamplerParameters.prog_closed c) _) post,
    QLD.PauliCL.SamplerProgram.query.closed.mono (by omega) _⟩

theorem prog_runs (c lam n : ℕ) (d : Data) : ∃ time,
    (prog c lam).Runs (.cons (encode n) d)
      (QLD.PauliCL.SamplerProgram.query (parameters c lam n, d)) time := by
  obtain ⟨t₁, h₁⟩ := PauliSamplerParameters.prog_runs c lam n
  have h₂ := hardcode_time (PauliSamplerParameters.prog_closed c) h₁
  obtain ⟨t₃, h₃⟩ := routeOneCall_indirect route
    (hardcode_wellScoped (PauliSamplerParameters.prog_closed c) _) post
    (.cons (encode n) d) (encode n) d (encode (parameters c lam n)) _
    (by simp [route, readNat_encode]) h₂
  have hout : post (d, encode (parameters c lam n)) =
      encode (parameters c lam n, d) := rfl
  rw [hout] at h₃
  obtain ⟨t₄, _, h₄⟩ := QLD.PauliCL.SamplerProgram.query.computes (parameters c lam n, d)
  exact ⟨_, Eval.let_ h₃
    (Eval.append_of_wellScoped h₄ QLD.PauliCL.SamplerProgram.query.closed _)⟩

theorem prog_halts (c lam n : ℕ) (d : Data) :
    Halts (prog c lam) (.cons (encode n) d) := by
  obtain ⟨t, ht⟩ := prog_runs c lam n d
  exact ⟨_, t, ht⟩

set_option backward.isDefEq.respectTransparency false in
theorem query_marginal (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (w : Player) (T : Ty) (r : ℕ) (z : BitStr)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hz : z.length = dimension c lam n) :
    QLD.PauliCL.SamplerProgram.query
      (parameters c lam n, encode (TypedSampler.Query.atType T (.marginal w r z))) =
      encode (toBits (((presentation c hc he lam n T).truncate r).eval
        (ofBits (dimension c lam n) z))) := by
  rw [QLD.PauliCL.SamplerProgram.query_marginal]
  let b := shoupSelfDualNormalBasis (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n)
  let x := (binaryVectorEquiv (m := 2 ^ selectorBits c lam n) b).symm
    (ofBits (dimension c lam n) z)
  have hx : toBits (binaryVectorEquiv b x) = z := by
    exact (congrArg CL.toBits ((binaryVectorEquiv b).apply_symm_apply _)).trans (toBits_ofBits hz)
  have hxe : binaryVectorEquiv b x = ofBits (dimension c lam n) z :=
    (binaryVectorEquiv b).apply_symm_apply _
  have h := marginalBits_correct (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits hc lam n) T r hr1 hr3 x x
  dsimp only [b] at hx hxe
  rw [hx, hxe] at h
  apply congrArg encode
  simpa only [parameters, presentation, registerPower_eq] using h

set_option backward.isDefEq.respectTransparency false in
theorem query_linear (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (w : Player) (T : Ty) (r : ℕ) (u y : BitStr)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hu : u.length = dimension c lam n) (hy : y.length = dimension c lam n) :
    QLD.PauliCL.SamplerProgram.query
      (parameters c lam n, encode (TypedSampler.Query.atType T (.linear w r u y))) =
      encode (toBits ((presentation c hc he lam n T).mapOfPrefix (r - 1)
        (ofBits (dimension c lam n) u) (ofBits (dimension c lam n) y))) := by
  rw [QLD.PauliCL.SamplerProgram.query_linear]
  let b := shoupSelfDualNormalBasis (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n)
  let v := (binaryVectorEquiv (m := 2 ^ selectorBits c lam n) b).symm
    (ofBits (dimension c lam n) u)
  let x := (binaryVectorEquiv (m := 2 ^ selectorBits c lam n) b).symm
    (ofBits (dimension c lam n) y)
  have hv : toBits (binaryVectorEquiv b v) = u := by
    exact (congrArg CL.toBits ((binaryVectorEquiv b).apply_symm_apply _)).trans (toBits_ofBits hu)
  have hx : toBits (binaryVectorEquiv b x) = y := by
    exact (congrArg CL.toBits ((binaryVectorEquiv b).apply_symm_apply _)).trans (toBits_ofBits hy)
  have hve : binaryVectorEquiv b v = ofBits (dimension c lam n) u :=
    (binaryVectorEquiv b).apply_symm_apply _
  have hxe : binaryVectorEquiv b x = ofBits (dimension c lam n) y :=
    (binaryVectorEquiv b).apply_symm_apply _
  have h := linearBits_correct (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits hc lam n) T r hr1 hr3 v x
  dsimp only [b] at hv hx hve hxe
  rw [hv, hx, hve, hxe] at h
  apply congrArg encode
  convert h using 1 <;> rfl

theorem query_factor (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (w : Player) (T : Ty) (r : ℕ) (u : BitStr)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    QLD.PauliCL.SamplerProgram.query
      (parameters c lam n, encode (TypedSampler.Query.atType T (.factor w r u))) =
      encode (indicatorBits ((presentation c hc he lam n T).factorOfPrefix (r - 1)
        (ofBits (dimension c lam n) u))) := by
  rw [QLD.PauliCL.SamplerProgram.query_factor]
  apply congrArg encode
  exact factorBits_correct _ _ T (selectorBits c lam n) r hr1 hr3 _

/-- The actual uniform three-level Pauli sampler at canonical parameters. -/
def sampler (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam : ℕ) : TypedSampler 3 Ty where
  prog := prog c lam
  closed := prog_closed c lam
  dim := dimension c lam
  cl n _ := presentation c hc he lam n
  cl_exactlyOn n _ := presentation_exactlyOn c hc he lam n
  runs_dimension n := by
    obtain ⟨time, ht⟩ := prog_runs c lam n (encode (TypedSampler.Query.dimension : TypedSampler.Query Ty))
    rw [QLD.PauliCL.SamplerProgram.query_dimension] at ht
    exact ⟨time, by simpa only [parameters, length_unary, dimension, encode_prod] using ht⟩
  runs_marginal n w T r z hr1 hr3 hz := by
    obtain ⟨time, ht⟩ := prog_runs c lam n
      (encode (TypedSampler.Query.atType T (.marginal w r z)))
    exact ⟨time, by rw [query_marginal c hc he lam n w T r z hr1 hr3 hz] at ht; exact ht⟩
  runs_linear n w T r u y hr1 hr3 hu hy := by
    have huLen : u.length = dimension c lam n := by
      obtain ⟨x, rfl⟩ := hu
      exact length_toBits _
    obtain ⟨time, ht⟩ := prog_runs c lam n
      (encode (TypedSampler.Query.atType T (.linear w r u y)))
    exact ⟨time, by rw [query_linear c hc he lam n w T r u y hr1 hr3 huLen hy] at ht; exact ht⟩
  runs_factor n w T r u hr1 hr3 _ := by
    obtain ⟨time, ht⟩ := prog_runs c lam n
      (encode (TypedSampler.Query.atType T (.factor w r u)))
    exact ⟨time, by rw [query_factor c hc he lam n w T r u hr1 hr3] at ht; exact ht⟩
  halts := prog_halts c lam

/-- The compiler copies only the binary encoding of the boundedness parameter. -/
def compiler (c : ℕ) : PolyTimeFun ℕ Prog :=
  ClockSimulation.codeLet.comp
    (((ClockSimulation.codeRoute route post).comp
      ((PolyTimeFun.smn ℕ).comp ((const (PauliSamplerParameters.prog c)).pair (PolyTimeFun.id ℕ)))).pair
        (const QLD.PauliCL.SamplerProgram.query.code))

theorem compiler_apply (c lam : ℕ) : compiler c lam = prog c lam := rfl

end MIPRE.Introspection.PauliSampler
end
