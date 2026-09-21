/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryArtinSchreier
import MIPRE.Foundations.LowDegree.BinaryArtinSchreierProg
import MIPRE.Foundations.LowDegree.BinaryOrbitDescent
import MIPRE.Foundations.LowDegree.BinaryCanonical

/-! # A uniform effective step of the binary Artin–Schreier tower -/

noncomputable section

namespace MIPRE.LowDegree.BinaryArtinSchreier

open Cost Cost.PolyTimeFun BinaryPolynomial BinaryQuotient Polynomial

/-- The canonical quotient root, computed by multiplying the encoded unit by `X`. -/
def rootVectorBits (p : BitStr) : BitStr := shiftReduce p (oneBits p)

@[simp] theorem rootVectorBits_length (p : BitStr) : (rootVectorBits p).length = p.length := by
  exact length_shiftReduce p _ (length_oneBits p)

theorem evalBits_rootVectorBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (p : BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) :
    evalBits z (rootVectorBits p) = z := by
  rw [rootVectorBits, evalBits_shiftReduce z p _ (length_oneBits p) hz,
    evalBits_oneBits z p hp, mul_one]

/-- The uniform parameter `α³ + α²` in the supplied quotient. -/
def cubicParameterBits (p : BitStr) : BitStr :=
  let x := rootVectorBits p
  let y := mulReduce p x x
  xorBits (mulReduce p y x) y

@[simp] theorem cubicParameterBits_length (p : BitStr) :
    (cubicParameterBits p).length = p.length := by
  simp only [cubicParameterBits, length_xorBits,
    length_mulReduce p _ _ (rootVectorBits_length p)]
  rw [length_mulReduce p _ _ (length_mulReduce p _ _ (rootVectorBits_length p))]
  exact min_self _

theorem evalBits_cubicParameterBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (p : BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) :
    evalBits z (cubicParameterBits p) = z ^ 3 + z ^ 2 := by
  have hx := rootVectorBits_length p
  have hy := length_mulReduce p (rootVectorBits p) (rootVectorBits p) hx
  rw [cubicParameterBits, evalBits_xor z _ _ (by
    rw [length_mulReduce p _ _ hy, hy]), evalBits_mulReduce z p _ _ hy hz,
    evalBits_mulReduce z p _ _ hx hz, evalBits_rootVectorBits z p hp hz]
  ring

def rootVectorBitsProg : PolyTimeFun BitStr BitStr :=
  shiftReduceProg.comp ((PolyTimeFun.id _).pair oneBitsProg)

def cubicParameterBitsProg : PolyTimeFun BitStr BitStr :=
  let x := rootVectorBitsProg
  let y := mulReduceProg.comp ((PolyTimeFun.id _).pair (x.pair x))
  xorBitsProg.comp ((mulReduceProg.comp ((PolyTimeFun.id _).pair (y.pair x))).pair y)

@[simp] theorem rootVectorBitsProg_apply (p : BitStr) : rootVectorBitsProg p = rootVectorBits p := rfl
@[simp] theorem cubicParameterBitsProg_apply (p : BitStr) :
    cubicParameterBitsProg p = cubicParameterBits p := rfl

/-- Form the parameter's complete Frobenius product and substitute `X² + X`. -/
def towerStepBits (p : BitStr) : BitStr :=
  substituteArtinSchreierBits (orbitPolynomialBits (unary p.length) p (cubicParameterBits p))

/-- A single ambient program for one tower step, valid also on malformed moduli. -/
def towerStepBitsProg : PolyTimeFun BitStr BitStr :=
  substituteArtinSchreierBitsProg.comp (orbitPolynomialBitsProg.comp
    (length.pair ((PolyTimeFun.id _).pair cubicParameterBitsProg)))

@[simp] theorem towerStepBitsProg_apply (p : BitStr) : towerStepBitsProg p = towerStepBits p := rfl

/-- The coefficient list of the parameter's complete old-field Frobenius product. -/
def parameterOrbitBits (p : BitStr) : BitStr :=
  orbitPolynomialBits (unary p.length) p (cubicParameterBits p)

@[simp] theorem parameterOrbitBits_length (p : BitStr) :
    (parameterOrbitBits p).length = p.length + 1 := by
  simp [parameterOrbitBits, orbitPolynomialBits, descendBits, unary]

/-- A linear width bound on every input, independent of validity of the modulus. -/
theorem towerStepBits_width (p : BitStr) : (towerStepBits p).length ≤ 2 * (p.length + 1) := by
  exact (substituteArtinSchreierBits_width (parameterOrbitBits p)).trans_eq
    (congrArg (2 * ·) (parameterOrbitBits_length p))

local instance quotientFintype (p : BitStr) : Fintype (AdjoinRoot (polyOfBits (p ++ [true]))) :=
  Fintype.ofEquiv (Fin (polyOfBits (p ++ [true])).natDegree → ZMod 2)
    (coordinateEquiv _ (monic_polyOfBits_append_true p)).symm.toEquiv

local instance quotientFiniteDimensional (p : BitStr) :
    Module.Finite (ZMod 2) (AdjoinRoot (polyOfBits (p ++ [true]))) :=
  (monic_polyOfBits_append_true p).finite_adjoinRoot

local instance quotientCharP (p : BitStr) [Fact (Irreducible (polyOfBits (p ++ [true])))] :
    CharP (AdjoinRoot (polyOfBits (p ++ [true]))) 2 :=
  charP_of_injective_ringHom (AdjoinRoot.of _).injective 2

private theorem quotient_finrank (p : BitStr) :
    Module.finrank (ZMod 2) (AdjoinRoot (polyOfBits (p ++ [true]))) = p.length := by
  rw [(AdjoinRoot.powerBasis' (monic_polyOfBits_append_true p)).finrank]
  exact natDegree_polyOfBits_append_true p

private theorem quotient_pow_card (p : BitStr) [Fact (Irreducible (polyOfBits (p ++ [true])))]
    (x : AdjoinRoot (polyOfBits (p ++ [true]))) : x ^ (2 ^ p.length) = x := by
  have hcard : Fintype.card (AdjoinRoot (polyOfBits (p ++ [true]))) = 2 ^ p.length := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, quotient_finrank]
  rw [← hcard]
  exact FiniteField.pow_card x

/-- The descended complete orbit is monic of the old field degree and annihilates
its cubic parameter; repeated conjugates cause no difficulty. -/
theorem parameterOrbitBits_spec (p : BitStr) [Fact (Irreducible (polyOfBits (p ++ [true])))]
    (hp : p ≠ []) :
    (polyOfBits (parameterOrbitBits p)).Monic ∧
      (polyOfBits (parameterOrbitBits p)).natDegree = p.length ∧
      aeval (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2)
        (polyOfBits (parameterOrbitBits p)) = 0 := by
  let f := polyOfBits (p ++ [true])
  have hm : f.Monic := monic_polyOfBits_append_true p
  have hd : p.length = f.natDegree := (natDegree_polyOfBits_append_true p).symm
  have hc : evalBits (AdjoinRoot.root f) (cubicParameterBits p) ^
      (2 ^ (unary p.length).length) = evalBits (AdjoinRoot.root f) (cubicParameterBits p) := by
    simpa [unary] using quotient_pow_card p (evalBits (AdjoinRoot.root f) (cubicParameterBits p))
  have hs := orbitPolynomialBits_monic_natDegree f hm (unary p.length) p (cubicParameterBits p)
    hd rfl hp (cubicParameterBits_length p) hc
  refine ⟨hs.1, by simpa [parameterOrbitBits, unary] using hs.2, ?_⟩
  have he := evalBits_cubicParameterBits (AdjoinRoot.root f) p hp (root_eq f p rfl)
  rw [← he, aeval_def, eval₂_eq_eval_map, parameterOrbitBits,
    map_orbitPolynomialBits f hm (unary p.length) p (cubicParameterBits p) hd rfl hp
      (cubicParameterBits_length p) hc]
  exact eval_orbitPolynomial _ _ (by simpa [unary] using List.length_pos_iff.mpr hp)

/-- One valid power-of-two tower stage gives the next irreducible flat binary polynomial. -/
theorem towerStepBits_irreducible (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (t : ℕ) (hd : p.length = 2 ^ t)
    (hc : Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2))) :
    Irreducible (polyOfBits (towerStepBits p)) := by
  have hp : p ≠ [] := List.length_pos_iff.mp (by rw [hd]; positivity)
  obtain ⟨hg, hgd, hgz⟩ := parameterOrbitBits_spec p hp
  have h := comp_quadratic_irreducible t ((quotient_finrank p).trans hd) _ hc
    (polyOfBits (parameterOrbitBits p)) hg (hgd.trans hd) hgz
  simpa only [towerStepBits, polyOfBits_substituteArtinSchreierBits, quadratic, C_0,
    add_zero, parameterOrbitBits] using h

/-- The normalized step output has exactly the doubled degree plus its leading bit. -/
theorem towerStepBits_monic_natDegree (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (hp : p ≠ []) :
    (polyOfBits (towerStepBits p)).Monic ∧
      (polyOfBits (towerStepBits p)).natDegree = 2 * p.length := by
  obtain ⟨hg, hd, _⟩ := parameterOrbitBits_spec p hp
  have hq : (X ^ 2 + X : (ZMod 2)[X]).Monic := by
    simpa [quadratic] using quadratic_monic (0 : ZMod 2)
  have hqd : (X ^ 2 + X : (ZMod 2)[X]).natDegree = 2 := by
    simpa [quadratic] using quadratic_natDegree (0 : ZMod 2)
  change (polyOfBits (substituteArtinSchreierBits (parameterOrbitBits p))).Monic ∧ _
  rw [polyOfBits_substituteArtinSchreierBits]
  constructor
  · exact hg.comp hq (by rw [hqd]; decide)
  · rw [towerStepBits, polyOfBits_substituteArtinSchreierBits, natDegree_comp, hqd]
    change (polyOfBits (parameterOrbitBits p)).natDegree * 2 = _
    rw [hd, Nat.mul_comm]

set_option maxHeartbeats 2000000 in
/-- The effective flat step preserves the invariant for its canonical quotient root. -/
theorem towerStepBits_cubic (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (t : ℕ) (hd : p.length = 2 ^ t)
    (hc : Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2))) :
    let : Fact (Irreducible (polyOfBits (towerStepBits p))) :=
      ⟨towerStepBits_irreducible p t hd hc⟩
    Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (towerStepBits p)) ^ 3 +
        AdjoinRoot.root (polyOfBits (towerStepBits p)) ^ 2)) := by
  have hp : p ≠ [] := List.length_pos_iff.mp (by rw [hd]; positivity)
  obtain ⟨hg, hgd, hgz⟩ := parameterOrbitBits_spec p hp
  have h := comp_quadratic_cubic_irreducible t ((quotient_finrank p).trans hd) _ hc
    (polyOfBits (parameterOrbitBits p)) hg (hgd.trans hd) hgz
  have he : polyOfBits (towerStepBits p) =
      (polyOfBits (parameterOrbitBits p)).comp (quadratic (0 : ZMod 2)) := by
    rw [towerStepBits, polyOfBits_substituteArtinSchreierBits]
    simp only [quadratic, C_0, add_zero, parameterOrbitBits]
  exact cubic_irreducible_congr he (towerStepBits_irreducible p t hd hc)
    (comp_quadratic_irreducible t ((quotient_finrank p).trans hd) _ hc
      (polyOfBits (parameterOrbitBits p)) hg (hgd.trans hd) hgz) h

/-- Normalization leaves a true leading bit on every valid step output. -/
theorem towerStepBits_getLast (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (hp : p ≠ []) :
    (towerStepBits p).getLastD false = true := by
  have hm := (towerStepBits_monic_natDegree p hp).1
  rcases normalizeBits_getLast
    ((parameterOrbitBits p).foldr (fun b s => artinSchreierStep s b) []) with h | h
  · have he : towerStepBits p = [] := h
    exact (hm.ne_zero (by rw [he]; rfl)).elim
  · exact h

/-- A valid step has doubled lower-coefficient width. -/
theorem towerStepBits_length (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (hp : p ≠ []) :
    (towerStepBits p).length = 2 * p.length + 1 := by
  rw [← natDegree_add_one_of_getLast _ (towerStepBits_getLast p hp),
    (towerStepBits_monic_natDegree p hp).2]

/-- The seed is the specified degree-two polynomial. -/
theorem initial_polynomial : polyOfBits [true, true, true] = quadratic (1 : ZMod 2) := by
  simp only [polyOfBits_cons, show polyOfBits [] = 0 from rfl, ofBool, if_true, mul_zero, add_zero, C_1,
    quadratic]
  ring

/-- A valid stage records the exact power-of-two width and the cubic no-root invariant. -/
structure TowerInvariant (p : BitStr) (t : ℕ) : Prop where
  width : p.length = 2 ^ (t + 1)
  irreducible : Irreducible (polyOfBits (p ++ [true]))
  cubic : let : Fact (Irreducible (polyOfBits (p ++ [true]))) := ⟨irreducible⟩
    Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2))

/-- The initial stage satisfies the reusable tower invariant. -/
theorem initial_invariant : TowerInvariant [true, true] 0 := by
  have hi : Irreducible (polyOfBits ([true, true] ++ [true])) := by
    simpa only [List.cons_append, List.nil_append, initial_polynomial] using binary_initial_irreducible
  refine ⟨rfl, hi, ?_⟩
  exact cubic_irreducible_congr initial_polynomial hi binary_initial_irreducible
    (cubic_quadratic_irreducible (1 : ZMod 2) binary_initial_irreducible)

set_option maxHeartbeats 2000000 in
/-- Dropping the normalized leading bit prepares the next supplied modulus. -/
theorem towerStep_invariant (p : BitStr) (t : ℕ) (h : TowerInvariant p t) :
    TowerInvariant (towerStepBits p).dropLast (t + 1) := by
  let : Fact (Irreducible (polyOfBits (p ++ [true]))) := ⟨h.irreducible⟩
  have hp : p ≠ [] := List.length_pos_iff.mp (by rw [h.width]; positivity)
  have he : (towerStepBits p).dropLast ++ [true] = towerStepBits p :=
    dropLast_append_true _ (towerStepBits_getLast p hp)
  have hi := towerStepBits_irreducible p (t + 1) h.width h.cubic
  refine ⟨?_, he.symm ▸ hi, ?_⟩
  · rw [List.length_dropLast, towerStepBits_length p hp, Nat.add_sub_cancel, h.width,
      pow_succ]
    simp only [pow_succ]
    ring
  · exact cubic_irreducible_congr (congrArg polyOfBits he) (he.symm ▸ hi) hi
      (towerStepBits_cubic p (t + 1) h.width h.cubic)

end MIPRE.LowDegree.BinaryArtinSchreier

end