/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Mirror
public import MIPRE.Background.QLD.SwapState

@[expose] public section

/-!
# The pulling chain's index algebra, and its first displays

`lem:qld-pauli-selfcons` is proved by a chain of eleven displays that ends at

```
sum_{g,h,g',h' : g - g_h = g' - g_h', (cd(g) - h) . u-tilde = a}
  ((S-hat^W_g)_{A A'} (x) (tau^W_h)_{A''}) . ((S-hat^W_g')_{B B'} (x) (tau^W_h')_{B''})
```

and concludes by the observation that **this expression is symmetric between `(g, h)` and
`(g', h')`**, so that the analogous derivation starting from Bob's exact Pauli measurement reaches
the same place, and the two are therefore close to each other. That observation is the whole reason
the lemma holds, and the reason it is not obvious is that the two conditions cutting out the index
set look asymmetric: the second mentions both pairs, but the first mentions only `g` and `h`.

The paper's sentence is that the conditions `(cd(g) - h) . u-tilde = a` and `g - g_h = g' - g_h'`
are together equivalent to `(cd(g') - h') . u-tilde = a` and `g - g_h = g' - g_h'`. This file is
that sentence, together with the rewriting of the exact Pauli measurement over the same index set
(`eq:qld-pulling-2` and `eq:qld-pulling-2b`), the chain's Schwartz--Zippel step, and the chain's
first displays, `eq:qld-pulling-0` to `eq:qld-pulling-3b`, each of which concerns one simultaneous
pair measurement. The displays that compare the two players' pair measurements on the physical
state, from `eq:qld-pulling-4` on, are in `MIPRE/Background/QLD/ChainPhysical.lean`.

Subtraction is written as addition throughout, the field having characteristic two.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The index algebra is unchanged.
The chain's summand `chainOp` is, as `mTildeAnc` is, a matrix over the first algebra of the model
of a `SimulPair` on the register `Anc F m` (register outer, `smulKron`). The displays
`eq:qld-pulling-0` to `-3b` are stated for a pair measurement on the first cut of the physical state
(`CutSimul N S K δ`) and read in the physical model `phys (Anc F m) F m d N K` itself. The matrix
route ran them on a regrouping `mVec` of the first cut's state that gives `A''` to Alice --- whose
model is the physical model --- and then carried them to the physical cut by an explicit lift
(`physLift`, which regrouped the registers and appended Bob's pair); the first cut and the physical
model share one state model, so here the chain's terms are elements of its algebra from the start,
and nothing is lifted. The helper's near-identity `nearId` is the first cut's agreement operator,
written physically by the reading lemmas `cut1_πA`, `cut1_πB`; the strategy's point measurements
are read with the registers inert (`physInert`); the EPR switching of `eq:qld-pulling-3a` is the
mirror identity of Alice's own pair in the physical state (`physE_mirror_A`); and the estimates
about one state are stated in a state model (`sum_snorm_sq_sub_mul`,
`sum_snorm_sq_fiber_sandwich_subset_le`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-! ## The label a pair of outcomes carries -/

/-- **The chain's label.** `cd(g) - h` is the paper's difference of the pair outcome's cube data
and the Weyl outcome; the chain's index set asks its pairing with the probe to be the measurement
outcome. -/
def chainLabel (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h : Anc F m) : Anc F m :=
  cubeData g + h

/-- **The chain's coupling condition.** The paper's `g - g_h = g' - g_{h'}`, with `g_h` the
low-degree encoding of `h`. -/
def ChainCoupled (g g' : LowIndDegPoly (F := F) (m := m) (d := d)) (h h' : Anc F m) : Prop :=
  g.toMv + ldEnc h = g'.toMv + ldEnc h'

instance decidableChainCoupled (g g' : LowIndDegPoly (F := F) (m := m) (d := d))
    (h h' : Anc F m) : Decidable (ChainCoupled g g' h h') :=
  inferInstanceAs (Decidable (g.toMv + ldEnc h = g'.toMv + ldEnc h'))

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The coupling is symmetric on its face, which is half of the display's symmetry. -/
theorem chainCoupled_symm {g g' : LowIndDegPoly (F := F) (m := m) (d := d)} {h h' : Anc F m}
    (hc : ChainCoupled g g' h h') : ChainCoupled g' g h' h := Eq.symm hc

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Coupled pairs carry the same label**, which is the other half. Evaluating the coupling at a
cube point reads off the two labels there, the encoding of a cube datum being that datum on the
cube. -/
theorem chainLabel_eq_of_coupled {g g' : LowIndDegPoly (F := F) (m := m) (d := d)}
    {h h' : Anc F m} (hc : ChainCoupled g g' h h') : chainLabel g h = chainLabel g' h' := by
  funext y
  have hy := congrArg (fun p => MvPolynomial.eval (pt (F := F) y) p) hc
  simpa [chainLabel, cubeData, LowIndDegPoly.eval_toMv] using hy

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **So the chain's last display is symmetric between the two pairs.** Its index set is cut out by
the coupling, symmetric on its face, and by a pairing condition read off one pair --- and the two
readings agree, so it may be read off either. That is what lets the derivation starting from Bob's
exact Pauli measurement reach the same expression as Alice's, and hence what makes
`lem:qld-pauli-selfcons` conclude. -/
theorem dotF_chainLabel_eq_of_coupled {g g' : LowIndDegPoly (F := F) (m := m) (d := d)}
    {h h' : Anc F m} (hc : ChainCoupled g g' h h') (v : Anc F m) :
    dotF (chainLabel g h) v = dotF (chainLabel g' h') v := by
  rw [chainLabel_eq_of_coupled hc]

/-! ## The index set, and the exact Pauli measurement written over it -/

/-- **The chain's index set** at the probe `v` and the outcome `a`: the pairs whose label pairs
with the probe to give `a`. -/
def chainIdx (v : Anc F m) (a : F) :
    Finset (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :=
  univ.filter fun p => dotF (chainLabel p.1 p.2) v = a

omit [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mem_chainIdx {v : Anc F m} {a : F}
    {p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m} :
    p ∈ chainIdx v a ↔ dotF (chainLabel p.1 p.2) v = a := by
  rw [chainIdx, mem_filter]
  exact and_iff_right (mem_univ p)

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- In characteristic two the syndrome's condition and the label's are one condition. -/
theorem dotF_chainLabel_eq_iff (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h v : Anc F m)
    (a : F) : dotF (chainLabel g h) v = a ↔ dotF h v = dotF (cubeData g) v + a := by
  rw [chainLabel, dotF_add_left]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hx, ← add_assoc, add_self, zero_add]
  · rw [hx, ← add_assoc, add_self, zero_add]

/-! ## A reindexing, and the label filters

The chain's label filters are products, the label reading only the first pair. The reindexing
fact before them is not the chain's: it is about matrices, a regrouping of the matrix route
(`SwapItemTwo.lean`) still uses it, and it is kept here unchanged. -/

/-- **A reindexing carries `mulVec` the way it carries the quadratic form.** -/
theorem mulVec_comp_equiv {N N' : Type*} [Fintype N] [Fintype N'] [DecidableEq N] [DecidableEq N']
    (e : N ≃ N') (v : N → ℂ) (A : Matrix N N ℂ) :
    (Matrix.reindex e e A) *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The chain's three- and four-index label filters are products**, the label reading only the
first pair. -/
theorem sum_chainLabel_filter {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*}
    [AddCommMonoid A] (v : Anc F m) (a : F)
    (f : ((LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × ι) → A) :
    (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × ι
        => dotF (chainLabel t.1.1 t.1.2) v = a, f t)
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a, ∑ i : ι, f (p, i) := by
  classical
  rw [show (univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × ι
      => dotF (chainLabel t.1.1 t.1.2) v = a)
      = (chainIdx (F := F) (m := m) (d := d) v a) ×ˢ (univ : Finset ι) from by
    ext t
    simp [chainIdx]]
  exact Finset.sum_product _ _ f

/-! ## The chain's endpoint index set, and its symmetry

Display `eq:qld-pulling-12` is a sum over *pairs* of index pairs, one per party, coupled by
`g - g_h = g' - g_{h'}` and cut out by the pairing condition on the first. Both parties' derivations
end there, and that is only because the expression does not in fact depend on which party's pair
the condition is read off. -/

/-- **The index set of `eq:qld-pulling-12`**: coupled pairs, with the label read off the first. -/
def coupledIdx (v : Anc F m) (a : F) :
    Finset ((LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :=
  univ.filter fun q => ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2 ∧ dotF (chainLabel q.1.1 q.1.2) v = a

omit [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mem_coupledIdx {v : Anc F m} {a : F}
    {q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)} :
    q ∈ coupledIdx v a
      ↔ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2 ∧ dotF (chainLabel q.1.1 q.1.2) v = a := by
  rw [coupledIdx, mem_filter]
  exact and_iff_right (mem_univ q)

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The index set does not care which pair the label is read off.** This is the paper's sentence:
the conditions `(cd(g) - h) . u-tilde = a` and `g - g_h = g' - g_{h'}` are together equivalent to
`(cd(g') - h') . u-tilde = a` and the same coupling. -/
theorem swap_mem_coupledIdx {v : Anc F m} {a : F}
    {q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)} :
    q.swap ∈ coupledIdx v a ↔ q ∈ coupledIdx v a := by
  simp only [mem_coupledIdx, Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨hc, hl⟩
    exact ⟨chainCoupled_symm hc, (dotF_chainLabel_eq_of_coupled (chainCoupled_symm hc) v).trans hl⟩
  · rintro ⟨hc, hl⟩
    exact ⟨chainCoupled_symm hc, (dotF_chainLabel_eq_of_coupled (chainCoupled_symm hc) v).trans hl⟩

/-- **The outcome the chain's four-index pair carries**, the paper's `(g - g_h + g_h')(u)`. -/
def chainQShift (u : Point F m)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) : F :=
  q.1.1.eval u + dotF q.1.2 (indVec u) + dotF q.2.2 (indVec u)

/-! ## `eq:qld-pulling-12`, Schwartz--Zippel

The chain's last display, and its only step that is not about operators: the constraint the chain
carries is an equality of polynomial *values* at the sampled point, and passing to equality of the
polynomials themselves discards only the tuples where distinct polynomials happen to agree
there. -/

/-- **Schwartz--Zippel for the chain's coupling.** Two index pairs that are not coupled carry
distinct polynomials, and distinct polynomials of individual degree at most `d` agree at a uniform
point with probability at most `md/q`. The encoding of a Weyl outcome is multilinear, so adding it
keeps the degree bound as long as `d` is at least one. -/
theorem sum_uniform_chainCoupled_agree_le (hd : 1 ≤ d)
    {g g' : LowIndDegPoly (F := F) (m := m) (d := d)} {h h' : Anc F m}
    (hne : ¬ ChainCoupled g g' h h') :
    ∑ u, uniform (Point F m) u
        * (if g.eval u + dotF h (indVec u) = g'.eval u + dotF h' (indVec u) then (1 : ℝ) else 0)
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  have hdeg : ∀ (a : LowIndDegPoly (F := F) (m := m) (d := d)) (b : Anc F m) (i : Fin m),
      (a.toMv + ldEnc b).degreeOf i ≤ d := by
    intro a b i
    refine le_trans (MvPolynomial.degreeOf_add_le i _ _) ?_
    exact max_le (LowIndDegPoly.degreeOf_toMv_le a i)
      (le_trans (degreeOf_ldEnc_le b i) hd)
  have hsz := prob_agree_le_individualDegree hne (hdeg g h) (hdeg g' h')
  have hset : (univ.filter fun u : Point F m =>
        g.eval u + dotF h (indVec u) = g'.eval u + dotF h' (indVec u))
      = agree (g.toMv + ldEnc h) (g'.toMv + ldEnc h') := by
    ext u
    rw [mem_filter, mem_agree, map_add, map_add, LowIndDegPoly.eval_toMv,
      LowIndDegPoly.eval_toMv, ← dotF_indVec, ← dotF_indVec]
    simp only [mem_univ, true_and]
  simp only [uniform]
  rw [← Finset.mul_sum, Finset.sum_boole, hset, Fintype.card_fun, Fintype.card_fin]
  push_cast at hsz ⊢
  rw [inv_mul_eq_div]
  exact hsz

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- **The chain's agreement condition, in the form Schwartz--Zippel reads.** In characteristic two
the shift the chain carries may be moved to the other side. -/
theorem chainQShift_eq_iff (u : Point F m)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    MIPRE.QLD.chainQShift u q = q.2.1.eval u
      ↔ q.1.1.eval u + dotF q.1.2 (indVec u)
        = q.2.1.eval u + dotF q.2.2 (indVec u) := by
  rw [chainQShift]
  constructor <;> intro hx
  · rw [← hx, add_add_cancel]
  · rw [hx, add_add_cancel]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- A version of `Finset.filter` bookkeeping the display needs: restricting a weighted sum to a
subset of the index is the same as zeroing the weights outside it. -/
theorem sum_filter_and {ι : Type*} [Fintype ι] [DecidableEq ι] (p r : ι → Prop)
    [DecidablePred p] [DecidablePred r] (f : ι → ℝ) :
    (∑ i ∈ univ.filter fun i => r i ∧ p i, f i)
      = ∑ i ∈ univ.filter r, (if p i then f i else 0) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases hr : r i <;> by_cases hp : p i <;> simp [hr, hp]

/-- **Display `eq:qld-pulling-12`, as a bound on a weighted sum.** The chain's constraint is an
equality of polynomial *values* at the sampled point; passing to equality of the polynomials
themselves discards only the tuples where distinct polynomials happen to agree there, and those
carry at most `md/q` of the weight. -/
theorem sum_uniform_chainCoupled_mass_le (hd : 1 ≤ d)
    (w : ((LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
        × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) → ℝ)
    (hw0 : ∀ q, 0 ≤ w q) (hw : ∑ q, w q ≤ 1) :
    (∑ u, uniform (Point F m) u
        * ∑ q ∈ univ.filter fun q => MIPRE.QLD.chainQShift u q = q.2.1.eval u
            ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2, w q)
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  set w' : ((LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) → ℝ :=
    fun q => if ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2 then w q else 0 with hw'
  have hw'0 : ∀ q, 0 ≤ w' q := fun q => by
    simp only [hw']
    split_ifs with h
    · exact le_refl 0
    · exact hw0 q
  have hw'le : ∑ q, w' q ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun q (_ : q ∈ univ) => ?_) hw
    simp only [hw']
    split_ifs with h
    · exact hw0 q
    · exact le_refl _
  have hmd : (0 : ℝ) ≤ (m : ℝ) * d / Fintype.card F := by positivity
  have hrw : ∀ u : Point F m,
      (∑ q ∈ univ.filter fun q => MIPRE.QLD.chainQShift u q = q.2.1.eval u
          ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2, w q)
        = ∑ q ∈ univ.filter fun q => q.1.1.eval u + dotF q.1.2 (indVec u)
            = q.2.1.eval u + dotF q.2.2 (indVec u), w' q := by
    intro u
    simp only [hw']
    rw [sum_filter_and
      (p := fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
        ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2)
      (r := fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
        MIPRE.QLD.chainQShift u q = q.2.1.eval u) w]
    exact Finset.sum_congr (Finset.filter_congr fun q _ => by
      rw [chainQShift_eq_iff u q]) fun q _ => rfl
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hrw u]]
  have hswap : (∑ u, uniform (Point F m) u
        * ∑ q ∈ univ.filter fun q => q.1.1.eval u + dotF q.1.2 (indVec u)
            = q.2.1.eval u + dotF q.2.2 (indVec u), w' q)
      = ∑ q, w' q * ∑ u, uniform (Point F m) u
          * (if q.1.1.eval u + dotF q.1.2 (indVec u)
              = q.2.1.eval u + dotF q.2.2 (indVec u) then (1 : ℝ) else 0) := by
    simp only [Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
  rw [hswap]
  calc ∑ q, w' q * ∑ u, uniform (Point F m) u
          * (if q.1.1.eval u + dotF q.1.2 (indVec u)
              = q.2.1.eval u + dotF q.2.2 (indVec u) then (1 : ℝ) else 0)
      ≤ ∑ q, w' q * ((m : ℝ) * d / Fintype.card F) :=
        Finset.sum_le_sum fun q _ => by
          by_cases hc : ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2
          · have hz : w' q = 0 := by
              simp only [hw']
              exact if_neg (not_not_intro hc)
            rw [hz, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left
              (sum_uniform_chainCoupled_agree_le hd hc) (hw'0 q)
    _ = (∑ q, w' q) * ((m : ℝ) * d / Fintype.card F) := by rw [Finset.sum_mul]
    _ ≤ 1 * ((m : ℝ) * d / Fintype.card F) := mul_le_mul_of_nonneg_right hw'le hmd
    _ = (m : ℝ) * d / Fintype.card F := one_mul _

/-! ## Estimates about one state

Two facts about a single state that the chain's displays share, stated in a state model
(`MIPRE/Foundations/StateModel.lean`): right-multiplying a projective measurement costs exactly the
operator's deviation from the identity, and the chain's terms, grouped by the measurement outcome,
have as summed squared norm a sum of sandwiches. -/

section OneState

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]

/-- **Right-multiplying a projective measurement costs exactly the operator's deviation from the
identity.** Summed over the outcomes there is no cross term, so no factor of the outcome count
appears --- which is what makes display `eq:qld-pulling-1` free rather than lossy. -/
theorem sum_snorm_sq_sub_mul (M : StateModel 𝒞) {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Λ → 𝒞} (hP : IsPVMIn P) (Y : 𝒞) :
    ∑ a : Λ, M.snorm (P a - P a * Y) ^ 2 = M.snorm (1 - Y) ^ 2 := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
    rw [show P a - P a * Y = P a * (1 - Y) by rw [mul_sub, mul_one]]]
  rw [← M.snorm_sq_sum_orthogonal hP (1 - Y) univ, hP.sum_eq_one, one_mul]

/-- **The outer shape both remaining displays share.** Each is a bound on the summed squared norm
of the chain's terms, grouped by the measurement outcome. Projectivity turns each group into a sum
of sandwiches (`snorm_sq_sum_proj_sandwich`), the groups are the fibres of the outcome map, so the
double sum is the single one over the index --- and what is left to bound is a sum of sandwiches
with no outcome in it. The index may be a subset, which is what `eq:qld-pulling-10` needs: it sums
over the pairs whose outcomes *disagree*. -/
theorem sum_snorm_sq_fiber_sandwich_subset_le (M : StateModel 𝒞) {ι C : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype C] [DecidableEq C] {P : ι → 𝒞} (hP : IsPVMIn P) (W : ι → 𝒞)
    (c : ι → C) (D : Finset ι) {ε : ℝ}
    (hbound : ∑ i ∈ D, M.qform (star (W i) * P i * W i) ≤ ε) :
    ∑ a : C, M.snorm (∑ i ∈ D.filter fun i => c i = a, P i * W i) ^ 2 ≤ ε := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => snorm_sq_sum_proj_sandwich M hP W _,
    Finset.sum_fiberwise D c fun i => M.qform (star (W i) * P i * W i)]
  exact hbound

/-- The case the first of the two displays uses, where the whole index is summed over. -/
theorem sum_snorm_sq_fiber_sandwich_le (M : StateModel 𝒞) {ι C : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype C] [DecidableEq C] {P : ι → 𝒞} (hP : IsPVMIn P) (W : ι → 𝒞)
    (c : ι → C) {ε : ℝ} (hbound : ∑ i, M.qform (star (W i) * P i * W i) ≤ ε) :
    ∑ a : C, M.snorm (∑ i ∈ univ.filter fun i => c i = a, P i * W i) ^ 2 ≤ ε :=
  sum_snorm_sq_fiber_sandwich_subset_le M hP W c univ hbound

end OneState

/-! ## Two projective families of the two players, and `fact:add-a-proj` -/

section TwoPlayers

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- **A product of projective measurements of the two players is projective**, indexed by the pairs
of outcomes: the two families commute. -/
theorem isPVMIn_πA_mul_πB (M : BipartiteModel 𝒞 𝒜 ℬ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {P : ι → 𝒜} {Q : κ → ℬ} (hP : IsPVMIn P) (hQ : IsPVMIn Q) :
    IsPVMIn fun t : ι × κ => M.πA (P t.1) * M.πB (Q t.2) where
  star_eq t := by rw [M.star_πA_mul_πB, hP.star_eq, hQ.star_eq]
  idem t := by rw [M.πA_mul_πB_mul, hP.idem, hQ.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← map_sum, hQ.sum_eq_one, map_one, mul_one, ← map_sum,
      hP.sum_eq_one, map_one]
  orthogonal {t t'} htt' := by
    rw [M.πA_mul_πB_mul]
    by_cases h1 : t.1 = t'.1
    · have h2 : t.2 ≠ t'.2 := fun h2 => htt' (Prod.ext h1 h2)
      rw [hQ.orthogonal h2, map_zero, mul_zero]
    · rw [hP.orthogonal h1, map_zero, zero_mul]

/-- **A second-player sandwich of a product of the two players' operators**: the first player's
factor is untouched. -/
theorem πB_sandwich (M : BipartiteModel 𝒞 𝒜 ℬ) (A : 𝒜) (Y B : ℬ) :
    star (M.πB B) * (M.πA A * M.πB Y) * M.πB B = M.πA A * M.πB (star B * Y * B) := by
  rw [← map_star, ← mul_assoc, ← (M.commute A (star B)).eq, mul_assoc (M.πA A),
    mul_assoc (M.πA A), ← map_mul, ← map_mul]

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [StarModule ℂ R] [PartialOrder R] [StarOrderedRing R] [StarProper R]

/-- **Dropping the far party's sub-identity factor.** Each of the chain's sandwiches carries, on
the far party, a projector times a Weyl outcome; summed over the outcome those are at most the
identity, so the whole sum is bounded by the near party's sandwiches alone. This is
`fact:add-a-proj` in the form `eq:qld-pulling-7` and `eq:qld-pulling-11` consume it, for a second
player whose algebra is the matrices over `R` on the register. -/
theorem sum_bornProb_sandwich_drop_le {anc ι κ : Type*} [Fintype anc] [DecidableEq anc]
    [Fintype ι] [Fintype κ] (M : BipartiteModel 𝒞 𝒜 (Matrix anc anc R)) {S : ι → 𝒜}
    (hS : IsPVMIn S) (X : ι → 𝒜) {B : ι → R} (hBsa : ∀ i, star (B i) = B i)
    (hBidem : ∀ i, B i * B i = B i) {T : κ → Matrix anc anc ℂ} (hT : IsPVM T) :
    ∑ i, ∑ x : κ, M.bornProb (star (X i) * S i * X i) (smulKron (B i) (T x))
      ≤ ∑ i, M.bornProb (star (X i) * S i * X i) 1 := by
  refine Finset.sum_le_sum fun i _ => ?_
  exact sum_bornProb_kron_le M (star_left_conjugate_nonneg (hS.nonneg i) _)
    (B := fun _ : κ => B i) (fun _ => hBsa i) (fun _ => hBidem i) hT

/-- **The same, for a second player whose registers are a pair**: the second player's algebra is
the matrices over `R` on `anc × α`, the far party's factor a projection of `α` times a projective
measurement of `anc` flattened onto the pair (`compHom`). The flattening is monotone, being a
`⋆`-homomorphism of star-ordered rings. -/
theorem sum_bornProb_compHom_kron_le {anc α X : Type*} [Fintype anc] [DecidableEq anc]
    [Fintype α] [DecidableEq α] [Fintype X] (M : BipartiteModel 𝒞 𝒜 (Matrix (anc × α) (anc × α) R))
    {A : 𝒜} (hA : 0 ≤ A) {B : X → Matrix α α R} (hBsa : ∀ x, star (B x) = B x)
    (hB : ∀ x, B x * B x = B x) {T : X → Matrix anc anc ℂ} (hT : IsPVM T) :
    ∑ x, M.bornProb A (compHom (smulKron (B x) (T x))) ≤ M.bornProb A 1 := by
  rw [← M.bornProb_sum_right]
  refine bornProb_mono_right M hA ?_
  rw [← map_sum, ← compHom_one]
  exact OrderHomClass.mono compHom (sum_kron_le_one hBsa hB hT)

end TwoPlayers

/-! ## The physical registers' operators

A player's physical registers are `(A'', (Ea, A'))` (`PhysReg`). Three kinds of operators of them
occur in the chain: an operator `X` of `(Ea, A')` with the far half `A''` inert,
`compHom (diagonal fun _ => X)` --- the first player's operators of the first cut, read physically
(`cut1_πA`); a matrix `Q` of scalars on the far half, `compHom (smulKron 1 Q)`; and their products,
`compHom (smulKron X Q)`. These are the identities between them, over any `⋆`-algebra. -/

section PhysOps

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] {γ α η : Type*} [Fintype γ]
  [DecidableEq γ] [Fintype α] [DecidableEq α] [Fintype η] [DecidableEq η]

omit [StarRing R] in
/-- `(1 ⊗ Q)(X ⊗ 1) = X ⊗ Q`. -/
theorem smulKron_one_mul_diagonal (X : R) (Q : Matrix γ γ ℂ) :
    smulKron (1 : R) Q * diagonal (fun _ : γ => X) = smulKron X Q := by
  ext a b
  rw [mul_diagonal, smulKron_apply, smulKron_apply, smul_mul_assoc, one_mul]

omit [StarRing R] in
/-- `(A ⊗ 1)(X ⊗ Q) = AX ⊗ Q`. -/
theorem diagonal_mul_smulKron (A X : R) (Q : Matrix γ γ ℂ) :
    diagonal (fun _ : γ => A) * smulKron X Q = smulKron (A * X) Q := by
  ext a b
  rw [diagonal_mul, smulKron_apply, smulKron_apply, mul_smul_comm]

omit [StarRing R] in
/-- `(X ⊗ Q)(A ⊗ 1) = XA ⊗ Q`. -/
theorem smulKron_mul_diagonal (X A : R) (Q : Matrix γ γ ℂ) :
    smulKron X Q * diagonal (fun _ : γ => A) = smulKron (X * A) Q := by
  ext a b
  rw [mul_diagonal, smulKron_apply, smulKron_apply, smul_mul_assoc]

omit [StarRing R] [Fintype γ] in
/-- `X ⊗ 1` is the block-diagonal matrix of `X`. -/
theorem smulKron_one_right (X : R) : smulKron X (1 : Matrix γ γ ℂ) = diagonal fun _ => X := by
  ext a b
  by_cases h : a = b
  · subst h
    simp
  · simp [one_apply_ne h, diagonal_apply_ne _ h]

/-- **An operator of the inner register, with the outer one inert, is its right lift**, a unital
`⋆`-homomorphism. -/
theorem compHom_diagonal_eq_liftRight (X : Matrix α α R) :
    compHom (diagonal fun _ : γ => X) = liftRight (α := γ) X := by
  ext p q
  rw [compHom_apply, liftRight_apply, diagonal_apply]
  split_ifs <;> rfl

/-- The identity minus an operator of the inner register is one of the inner register. -/
theorem one_sub_compHom_diagonal (X : Matrix α α R) :
    1 - compHom (diagonal fun _ : γ => X) = compHom (diagonal fun _ : γ => 1 - X) := by
  rw [compHom_diagonal_eq_liftRight, compHom_diagonal_eq_liftRight, map_sub, map_one]

/-- The adjoint of an operator of the inner register is one of the inner register. -/
theorem star_compHom_diagonal (X : Matrix α α R) :
    star (compHom (diagonal fun _ : γ => X)) = compHom (diagonal fun _ : γ => star X) := by
  rw [compHom_diagonal_eq_liftRight, compHom_diagonal_eq_liftRight, map_star]

/-- Operators of the inner register multiply as they do there. -/
theorem compHom_diagonal_mul (X Y : Matrix α α R) :
    compHom (diagonal fun _ : γ => X) * compHom (diagonal fun _ : γ => Y)
      = compHom (diagonal fun _ : γ => X * Y) := by
  rw [compHom_diagonal_eq_liftRight, compHom_diagonal_eq_liftRight, compHom_diagonal_eq_liftRight,
    map_mul]

/-- An element on the diagonal of the pair of registers is one on the diagonal of each. -/
theorem compHom_diagonal_diagonal (X : R) :
    compHom (diagonal fun _ : γ => diagonal fun _ : α => X) = diagonal fun _ : γ × α => X := by
  ext ⟨c, a⟩ ⟨c', a'⟩
  rw [compHom_apply, diagonal_apply, diagonal_apply]
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl, diagonal_apply]
    by_cases ha : a = a'
    · subst ha
      simp
    · rw [if_neg ha, if_neg fun h => ha (Prod.mk.inj h).2]
  · rw [if_neg hc, if_neg fun h => hc (Prod.mk.inj h).1]
    rfl

omit [DecidableEq α] in
/-- **An operator of the near half, read on the three registers**: `X ⊗ Q` on the innermost
register `α`, with the two outer ones inert. -/
theorem compHom_diagonal_compHom_diagonal_smulKron (X : R) (Q : Matrix α α ℂ) :
    compHom (diagonal fun _ : γ => compHom (diagonal fun _ : η => smulKron X Q))
      = smulKron X ((1 : Matrix γ γ ℂ) ⊗ₖ ((1 : Matrix η η ℂ) ⊗ₖ Q)) := by
  ext ⟨c, e, a⟩ ⟨c', e', a'⟩
  rw [compHom_apply, smulKron_apply, kroneckerMap_apply, kroneckerMap_apply, diagonal_apply]
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl, one_apply_eq, one_mul, compHom_apply, diagonal_apply]
    by_cases he : e = e'
    · subst he
      rw [if_pos rfl, one_apply_eq, one_mul, smulKron_apply]
    · rw [if_neg he, one_apply_ne he, zero_mul, zero_smul]
      rfl
  · rw [if_neg hc, one_apply_ne hc, zero_mul, zero_smul]
    rfl

end PhysOps

/-! ## The Weyl spectral projectors, and the hatted point measurement against one -/

/-- **A Weyl family's spectral projectors are a projective measurement.** The three facts are in
Foundations one by one; this is them bundled. -/
theorem isPVM_proj {n : Type*} [Fintype n] [DecidableEq n]
    {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) : IsPVM (proj w) where
  isSelfAdjoint e := proj_conjTranspose hw e
  idem e := by simpa using proj_mul_proj hw e e
  sum_eq_one := sum_proj hw

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The point measurement read off a strategy is projective** when the strategy's own is: it is a
coarse-graining of it along the answer's value. -/
theorem isPVM_ptAtPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    {P : Question F m → POVMIn (Answer F m d) R} (hP : ∀ q, IsPVMIn (P q).op) (W : Bas)
    (u : Point F m) : IsPVMIn (ptAtPOVM P W u).op :=
  POVMIn.isPVMIn_map (hP _) _

/-- **A syndrome projector meets a single spectral projector in that projector or in nothing.**
The syndrome is the fibre of the spectral family over the pairing, so the product keeps the one
outcome exactly when it lies in the fibre. -/
theorem syn_mul_proj {n : Type*} [Fintype n] [DecidableEq n]
    {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) (v : n → F) (b : F)
    (h : n → F) :
    syn w v b * proj w h = if dotF h v = b then proj w h else 0 := by
  classical
  rw [syn, Finset.sum_mul,
    Finset.sum_congr rfl fun e (_ : e ∈ univ.filter fun e => dotF e v = b) => proj_mul_proj hw e h]
  by_cases hb : dotF h v = b
  · rw [if_pos hb, Finset.sum_ite_eq' (univ.filter fun e : n → F => dotF e v = b) h (proj w),
      if_pos (mem_filter.mpr ⟨mem_univ h, hb⟩)]
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun e he => if_neg fun hc => hb ?_
    rw [← hc]
    exact (mem_filter.mp he).2

/-- **Display `eq:qld-pulling-3b`.** The chain's factor `(M^{Point}_r)_A (x) (tau_h)_{A'}` is the
hatted point measurement itself, cut down by the Weyl outcome: `M-hat^{u}_{c}` times the projector
at `h` keeps exactly the point outcome `c - g_h(u)`, the syndrome factor selecting the one term of
the convolution whose shift matches `h`. Over any `⋆`-algebra, with the register outer. -/
theorem hatMats_mul_proj {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R]
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) (c : F)
    (h : Anc F m) :
    hatMats P W u c * smulKron (1 : R) (proj (weylOf W) h)
      = smulKron ((ptAtPOVM P W u).op (c + dotF h (indVec u))) (proj (weylOf W) h) := by
  classical
  rw [← sum_kron_syn_eq_hatMats P W u c, Finset.sum_mul,
    Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => by
      rw [smulKron_mul, mul_one, synPOVM_mats,
        syn_mul_proj (isWeylFamily_weylOf W) (indVec u) (c + a') h]]
  rw [Finset.sum_eq_single (c + dotF h (indVec u))]
  · rw [if_pos (by rw [← add_assoc, add_self, zero_add])]
  · intro b _ hb
    rw [if_neg (fun hc => hb (by rw [hc, ← add_assoc, add_self, zero_add])), smulKron_zero_right]
  · intro hmem
    exact absurd (mem_univ _) hmem

/-! ## A single Weyl projector across the expanded state -/

section Register

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- **A single Weyl spectral projector transports across the expanded state, exactly.** The
syndrome version is `stateVec_hatVec_syn`; the chain's display `eq:qld-pulling-3a` moves one
projector, not a fibre of them. -/
theorem stateVec_hatVec_proj (M : BipartiteModel 𝒞 𝒜 ℬ) (W : Bas) (h : Anc F m) :
    (M.reg (Anc F m)).π ((M.reg (Anc F m)).πA (smulKron 1 (proj (weylOf W) h)))
        (M.reg (Anc F m)).ψ
      = (M.reg (Anc F m)).π ((M.reg (Anc F m)).πB (smulKron 1 (proj (weylOf W) h)))
        (M.reg (Anc F m)).ψ := by
  rw [M.reg_mirror, proj_weylOf_transpose]

/-- The same, as the vanishing of a cross-party deviation. -/
theorem xSqNorm_hatVec_proj (M : BipartiteModel 𝒞 𝒜 ℬ) (W : Bas) (h : Anc F m) :
    (M.reg (Anc F m)).xSqNorm (smulKron 1 (proj (weylOf W) h))
        (smulKron 1 (proj (weylOf W) h)) = 0 := by
  rw [BipartiteModel.xSqNorm, BipartiteModel.xNorm, StateModel.snorm, Op.snorm, map_sub,
    _root_.sub_apply, stateVec_hatVec_proj, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0)]

end Register

/-! ## The chain's summand, on one pair measurement -/

section Summand

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

namespace SimulPair

variable (P : SimulPair M S K ι δ)

/-- **The chain's summand on one party**: the pair measurement's `W`-marginal at `g`, tensored with
the Weyl spectral projector at `h` on the register. -/
def chainOp (W : Bas) (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (Anc F m) (Anc F m) 𝒜' :=
  smulKron ((polyMarg P.SA W).op p.1) (proj (weylOf W) p.2)

end SimulPair

/-- **Displays `eq:qld-pulling-2` and `eq:qld-pulling-2b`: the exact Pauli measurement, indexed the
chain's way.** `eq:tilde_M` sums over the pair measurement's outcomes `g` with a syndrome projector
attached; the chain sums over pairs `(g, h)` cut out by the pairing condition. The two are the same
sum, because the syndrome projector is by definition the fibre of the spectral family over that
pairing, and in characteristic two the shift the definition carries is the sum the chain's label is
written with. -/
theorem mTildeAnc_eq_sum_chainIdx (P : SimulPair M S K ι δ) (W : Bas) (v : Anc F m) (a : F) :
    P.mTildeAnc W v a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a, P.chainOp W p := by
  rw [chainIdx, Finset.sum_filter, Fintype.sum_prod_type, SimulPair.mTildeAnc, mTilde]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [sCoarse_eq_polyMarg, syn, kron_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  exact if_congr (by rw [dotF_chainLabel_eq_iff]) rfl rfl

/-- **The chain's summands are a projective measurement** in the pair `(g, h)`: a marginal of a
projective pair measurement, tensored with a Weyl spectral projector. -/
theorem isPVM_chainOp [StarModule ℂ 𝒜'] (P : SimulPair M S K ι δ) (W : Bas) :
    IsPVMIn fun p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m => P.chainOp W p :=
  (isPVM_polyMarg P.SA_proj W).smulKron (isPVM_proj (isWeylFamily_weylOf W)).toIn

namespace SimulPair

variable (P : SimulPair M S K ι δ)

/-- **Summing the *pair* outcome out of the summand** leaves the Weyl projector alone, the pair
measurement's outcomes being complete. This is what `eq:qld-pulling-9a` inserts. -/
theorem sum_poly_chainOp (W : Bas) (h : Anc F m) :
    (∑ g : LowIndDegPoly (F := F) (m := m) (d := d), P.chainOp W (g, h))
      = smulKron (1 : 𝒜') (proj (weylOf W) h) := by
  show (∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
      smulKron ((polyMarg P.SA W).op g) (proj (weylOf W) h)) = _
  rw [← smulKron_sum_left, (polyMarg P.SA W).sum_op]

/-- **The exact Pauli measurement, expanded over the pair outcomes.** -/
theorem mTildeAnc_eq_sum (W : Bas) (v : Anc F m) (a : F) :
    P.mTildeAnc W v a
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          smulKron ((polyMarg P.SA W).op g) (syn (weylOf W) v (dotF (cubeData g) v + a)) :=
  Finset.sum_congr rfl fun g _ => by rw [sCoarse_eq_polyMarg]

/-- **Multiplying it by one of the near-identity's terms.** The pair measurement's outcomes are
orthogonal, so only the matching one survives, and `syn_mul_syn` collapses the two syndrome
projectors onto the Weyl outcomes satisfying both conditions. -/
theorem mTildeAnc_mul_kron (W : Bas) (v : Anc F m) (u : Point F m) (a : F)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) (b : F) :
    P.mTildeAnc W v a * smulKron ((polyMarg P.SA W).op g) (syn (weylOf W) (indVec u) b)
      = ∑ h ∈ univ.filter fun h : Anc F m =>
            dotF h v = dotF (cubeData g) v + a ∧ dotF h (indVec u) = b,
          smulKron ((polyMarg P.SA W).op g) (proj (weylOf W) h) := by
  classical
  rw [mTildeAnc_eq_sum, Finset.sum_mul,
    Finset.sum_eq_single g (fun g' _ hg' => by
      rw [smulKron_mul, (isPVM_polyMarg P.SA_proj W).orthogonal hg', smulKron_zero_left])
      fun hmem => absurd (Finset.mem_univ g) hmem,
    smulKron_mul, (isPVM_polyMarg P.SA_proj W).idem,
    syn_mul_syn (isWeylFamily_weylOf W), kron_sum]

/-- **The chain's summand splits into the pair measurement's marginal and the Weyl outcome.** -/
theorem chainOp_eq_mul (W : Bas) (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    P.chainOp W p
      = diagonal (fun _ : Anc F m => (polyMarg P.SA W).op p.1)
        * smulKron (1 : 𝒜') (proj (weylOf W) p.2) :=
  smulKron_eq_diagonal_mul _ _

/-- **The outcome the chain's index pair carries**, the paper's `(g - g_h)(u)`: the pair outcome's
value at the sampled point, shifted by the Weyl outcome's own encoding there. -/
def chainShift (u : Point F m) (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) : F :=
  p.1.eval u + dotF p.2 (indVec u)

/-! ### The Weyl projector across the pair measurement's model -/

/-- **Display `eq:qld-pulling-3a`: the Weyl projector transports across the model of the pair
measurement.** The two halves of the register model's pair are maximally entangled and the
projectors are symmetric (`stateVec_hatVec_proj`), and the embedding `ι` intertwines each player's
operators and carries the state to the state. -/
theorem stateVec_ancProj (_P : SimulPair M S K ι δ) (W : Bas) (h : Anc F m) :
    K.π (K.πA (ι.ΦA (smulKron 1 (proj (weylOf W) h)))) K.ψ
      = K.π (K.πB (ι.ΦB (smulKron 1 (proj (weylOf W) h)))) K.ψ := by
  rw [← ι.W_ψ, ι.intertwineA, ι.intertwineB, stateVec_hatVec_proj]

/-- **Display `eq:qld-pulling-4`: the matched pairs of Weyl projectors leave the state alone.** By
the transport each matched pair acts as the projector on one side alone, and those sum to the
identity. -/
theorem sum_ancProj_mulVec (_P : SimulPair M S K ι δ) (W : Bas) :
    K.π (∑ h : Anc F m, K.πA (ι.ΦA (smulKron 1 (proj (weylOf W) h)))
        * K.πB (ι.ΦB (smulKron 1 (proj (weylOf W) h)))) K.ψ = K.ψ := by
  have hP := (isPVM_proj (isWeylFamily_weylOf (F := F) (m := m) W)).toIn
  have hstep : ∀ h : Anc F m,
      K.π (K.πA (ι.ΦA (smulKron 1 (proj (weylOf W) h)))
          * K.πB (ι.ΦB (smulKron 1 (proj (weylOf W) h)))) K.ψ
        = K.π (K.πA (ι.ΦA (smulKron 1 (proj (weylOf W) h)))) K.ψ := fun h => by
    rw [map_mul, mul_apply_eq_comp, ← _P.stateVec_ancProj W h, ← mul_apply_eq_comp, ← map_mul,
      ← map_mul, ← map_mul, smulKron_mul, one_mul, hP.idem h]
  rw [map_sum, _root_.sum_apply, Finset.sum_congr rfl fun h _ => hstep h, ← _root_.sum_apply,
    ← map_sum, ← map_sum, ← map_sum, ← smulKron_sum_right, hP.sum_eq_one, smulKron_one_one,
    ι.ΦA_one, map_one, map_one, one_apply_eq_self]

/-! ### `eq:qld-pulling-13`, the chain's only Cauchy--Schwarz

The swap that completes `eq:qld-pulling-10`. It is stated on a `SimulPair`, in the model that
pair's measurements live in, because that is where both placements of the point measurement are
local: the one that sandwiches is the first party's own, the one that replaces it is the second
party's. The mirror then makes it Bob's. -/

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-13`**: moving the sandwiching point measurement from the party that
carries the pair measurement to the other one. The cost is twice the square root of the two
placements' summed squared state distance, and no more: the pair measurement's outcomes are
orthogonal, so summing the deviation over them leaves one copy rather than one per outcome. -/
theorem abs_sum_qform_ne_swap_le (W : Bas) (u : Point F m) {εu : ℝ}
    (hcons : ∑ a : F, K.xSqNorm (ι.ΦA (hatMats S.PA W u a)) (ι.ΦB (hatMats S.PB W u a)) ≤ εu) :
    |(∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
          q.2 ≠ q.1.eval u,
        K.qform (K.πB (ι.ΦB (hatMats S.PB W u q.2)) * K.πA ((polyMarg P.SA W).op q.1)))
      - ∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
          q.2 ≠ q.1.eval u,
        K.qform (K.πA (ι.ΦA (hatMats S.PA W u q.2)) * K.πA ((polyMarg P.SA W).op q.1)
          * K.πA (ι.ΦA (hatMats S.PA W u q.2)))|
      ≤ 2 * Real.sqrt εu := by
  have hSpvm : IsPVMIn fun g : LowIndDegPoly (F := F) (m := m) (d := d) =>
      K.πA ((polyMarg P.SA W).op g) := (isPVM_polyMarg P.SA_proj W).map K.πA
  have hXpvm : IsPVMIn fun c : F => K.πB (ι.ΦB (hatMats S.PB W u c)) :=
    ((isPVM_hatMats S.projB W u).pushforward ι.ΦB_one).map K.πB
  have hYpvm : IsPVMIn fun c : F => K.πA (ι.ΦA (hatMats S.PA W u c)) :=
    ((isPVM_hatMats S.projA W u).pushforward ι.ΦA_one).map K.πA
  have hdrop : ∀ Z : F → 𝒞',
      (∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
          q.2 ≠ q.1.eval u, K.snorm (K.πA ((polyMarg P.SA W).op q.1) * Z q.2) ^ 2)
        ≤ ∑ c : F, K.snorm (Z c) ^ 2 := by
    intro Z
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun q _ _ => sq_nonneg _) (le_of_eq ?_)
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← K.snorm_sq_sum_orthogonal hSpvm (Z c) univ, hSpvm.sum_eq_one, one_mul]
  have hmass : ∀ Z : F → 𝒞', IsPVMIn Z →
      (∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
          q.2 ≠ q.1.eval u, K.snorm (K.πA ((polyMarg P.SA W).op q.1) * Z q.2) ^ 2) ≤ 1 := by
    intro Z hZ
    refine le_trans (hdrop Z) (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => show
        K.snorm (Z c) ^ 2 = K.snorm (Z c * 1) ^ 2 from by rw [mul_one],
      ← K.snorm_sq_sum_orthogonal hZ 1 univ, hZ.sum_eq_one, one_mul, K.snorm_one P.ψ_unit,
      one_pow]
  have hε : (∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
        q.2 ≠ q.1.eval u, K.snorm (K.πA ((polyMarg P.SA W).op q.1)
          * (K.πB (ι.ΦB (hatMats S.PB W u q.2)) - K.πA (ι.ΦA (hatMats S.PA W u q.2)))) ^ 2)
      ≤ εu := by
    refine le_trans (hdrop fun c => K.πB (ι.ΦB (hatMats S.PB W u c))
      - K.πA (ι.ΦA (hatMats S.PA W u c))) (le_trans (le_of_eq ?_) hcons)
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [BipartiteModel.xSqNorm_eq_sq, BipartiteModel.xNorm, K.snorm_sub_comm]
  have hcomm : ∀ q : LowIndDegPoly (F := F) (m := m) (d := d) × F,
      K.πB (ι.ΦB (hatMats S.PB W u q.2)) * K.πA ((polyMarg P.SA W).op q.1)
        = K.πA ((polyMarg P.SA W).op q.1) * K.πB (ι.ΦB (hatMats S.PB W u q.2)) := fun q =>
    ((K.commute ((polyMarg P.SA W).op q.1) (ι.ΦB (hatMats S.PB W u q.2))).eq).symm
  have hY := hmass _ hYpvm
  have hX := hmass _ hXpvm
  exact abs_sum_qform_swap_proj_le K.toStateModel _
    (X := fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
      K.πB (ι.ΦB (hatMats S.PB W u q.2)))
    (Y := fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
      K.πA (ι.ΦA (hatMats S.PA W u q.2)))
    (S := fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
      K.πA ((polyMarg P.SA W).op q.1))
    (fun q => hXpvm.star_eq q.2) (fun q => hXpvm.idem q.2)
    (fun q => hYpvm.star_eq q.2) (fun q => hSpvm.star_eq q.1) (fun q => hSpvm.idem q.1)
    hcomm hε hY hX

set_option maxHeartbeats 1000000 in
/-- **The swapped side, read as a Born probability.** Summing the other party's point measurement
over the outcomes its own value excludes leaves the complement of that value. -/
theorem sum_qform_ne_eq (W : Bas) (u : Point F m) :
    (∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
        q.2 ≠ q.1.eval u,
      K.qform (K.πB (ι.ΦB (hatMats S.PB W u q.2)) * K.πA ((polyMarg P.SA W).op q.1)))
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          K.bornProb ((polyMarg P.SA W).op g) (1 - ι.ΦB (hatMats S.PB W u (g.eval u))) := by
  classical
  have hB : IsPVMIn fun c : F => ι.ΦB (hatMats S.PB W u c) :=
    (isPVM_hatMats S.projB W u).pushforward ι.ΦB_one
  have hne : ∀ g : LowIndDegPoly (F := F) (m := m) (d := d),
      (∑ c ∈ univ.filter fun c : F => c ≠ g.eval u, ι.ΦB (hatMats S.PB W u c))
        = 1 - ι.ΦB (hatMats S.PB W u (g.eval u)) := by
    intro g
    rw [Finset.filter_ne', Finset.sum_erase_eq_sub (mem_univ (g.eval u)), hB.sum_eq_one]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_filter,
    Finset.sum_congr rfl fun c (_ : c ∈ univ.filter fun c : F => c ≠ g.eval u) => show
      K.qform (K.πB (ι.ΦB (hatMats S.PB W u c)) * K.πA ((polyMarg P.SA W).op g))
        = K.bornProb ((polyMarg P.SA W).op g) (ι.ΦB (hatMats S.PB W u c)) from by
      rw [BipartiteModel.bornProb, ((K.commute _ _).eq)],
    ← K.bornProb_sum_right, hne g]

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-10`, complete**: the whole cost of moving the point measurement
across and then dropping it is the helper's own `delta_S` plus twice the square root of the point
measurements' cross-party deviation. The average over the sampled point goes inside the square
root by Cauchy--Schwarz against the constant one. -/
theorem sum_uniform_qform_ne_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas) :
    (∑ u, uniform (Point F m) u
        * ∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
            q.2 ≠ q.1.eval u,
          K.qform (K.πA (ι.ΦA (hatMats S.PA W u q.2)) * K.πA ((polyMarg P.SA W).op q.1)
            * K.πA (ι.ΦA (hatMats S.PA W u q.2))))
      ≤ δ + 2 * Real.sqrt (172 * ε) := by
  classical
  set dev : Point F m → ℝ := fun u =>
    ∑ a : F, K.xSqNorm (ι.ΦA (hatMats S.PA W u a)) (ι.ΦB (hatMats S.PB W u a)) with hdevdef
  have hdev0 : ∀ u, 0 ≤ dev u := fun u =>
    Finset.sum_nonneg fun a _ => K.xSqNorm_nonneg _ _
  have hstep : ∀ u : Point F m,
      (∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
          q.2 ≠ q.1.eval u,
        K.qform (K.πA (ι.ΦA (hatMats S.PA W u q.2)) * K.πA ((polyMarg P.SA W).op q.1)
          * K.πA (ι.ΦA (hatMats S.PA W u q.2))))
        ≤ (∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            K.bornProb ((polyMarg P.SA W).op g) (1 - ι.ΦB (hatMats S.PB W u (g.eval u))))
          + 2 * Real.sqrt (dev u) := by
    intro u
    have h := P.abs_sum_qform_ne_swap_le W u (le_refl (dev u))
    rw [P.sum_qform_ne_eq W u] at h
    have := abs_le.mp h
    linarith [this.1]
  have havg := Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hstep u) (uniform_nonneg (Point F m) u)
  have hsplit : (∑ u, uniform (Point F m) u
        * ((∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            K.bornProb ((polyMarg P.SA W).op g) (1 - ι.ΦB (hatMats S.PB W u (g.eval u))))
          + 2 * Real.sqrt (dev u)))
      = (∑ u, uniform (Point F m) u
          * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            K.bornProb ((polyMarg P.SA W).op g) (1 - ι.ΦB (hatMats S.PB W u (g.eval u))))
        + 2 * ∑ u, uniform (Point F m) u * Real.sqrt (dev u) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit] at havg
  have hsqrt : (∑ u, uniform (Point F m) u * Real.sqrt (dev u))
      ≤ Real.sqrt (172 * ε) := by
    refine le_trans (sum_weighted_sqrt_le (uniform (Point F m)) dev
      (uniform_nonneg (Point F m)) (sum_uniform_eq_one (Point F m)) hdev0) ?_
    exact Real.sqrt_le_sqrt (P.sum_xSqNorm_hat_le hfail W)
  linarith [P.sum_bornProb_polyMarg_one_sub_le W]

end SimulPair

end Summand

/-! ## The chain's first displays, on the physical model

Displays `eq:qld-pulling-0` to `-3b` concern one simultaneous pair measurement on the first cut of
the physical state, and run in the physical model, which has the first cut's state: the exact Pauli
measurement there is the first player's `compHom (P.mTildeAnc …)`, on `(A'', (Ea, A'))`. -/

section First

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {hm : m ∣ Fintype.card F} {N : BipartiteModel 𝒞 𝒜 ℬ}
  {S : N.ProjStrat (qldGame (d := d) hm)} {K : ℕ} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

namespace SimulPair

variable (P : CutSimul N S K δ)

/-- **The helper's near-identity**, an element of the physical model's algebra: the agreement
operator of the first cut, of Alice's pair-measurement marginals against Bob's expanded point
measurements carried along `ι₁`, which is what `lem:qld-helper` bounds. The first cut and the
physical model share their state model, so no regrouping is needed to read it physically. -/
def nearId (W : Bas) (u : Point F m) :
    Matrix (PhysReg (Anc F m) F m d K × PhysReg (Anc F m) F m d K)
      (PhysReg (Anc F m) F m d K × PhysReg (Anc F m) F m d K) 𝒞 :=
  agreeOp (cut1 (Anc F m) F m d N K)
    (fun g : LowIndDegPoly (F := F) (m := m) (d := d) => (polyMarg P.SA W).op g)
    (fun g => (ι₁ (Anc F m) F m d N K).ΦB (hatMats S.PB W u (g.eval u)))

/-- **Display `eq:qld-pulling-1`, as an identity.** Inserting the near-identity costs exactly its
own deficit on the state, with no loss at all. -/
theorem sum_snorm_sq_nearId (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, (phys (Anc F m) F m d N K).snorm
        ((phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a))
          - (phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a)) * P.nearId W u) ^ 2
      = 1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          (cut1 (Anc F m) F m d N K).bornProb ((polyMarg P.SA W).op g)
            ((ι₁ (Anc F m) F m d N K).ΦB (hatMats S.PB W u (g.eval u))) := by
  have hP : IsPVMIn fun a : F =>
      (phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a)) :=
    ((P.isPVM_mTildeAnc W v).pushforward compHom_one).map _
  rw [sum_snorm_sq_sub_mul (phys (Anc F m) F m d N K).toStateModel hP (P.nearId W u)]
  exact snorm_sq_one_sub_agreeOp P.ψ_unit (isPVM_polyMarg P.SA_proj W)
    (fun g => by rw [← map_star, hatMats_conjTranspose])
    (fun g => by rw [← map_mul, (isPVM_hatMats S.projB W u).idem])

/-- **And its cost**, which is item 1 of `lem:qld-helper`. -/
theorem sum_uniform_snorm_sq_nearId_le (W : Bas) (v : Anc F m) :
    ∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d N K).snorm
            ((phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a))
              - (phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a)) * P.nearId W u) ^ 2
      ≤ δ := by
  have hsplit : ∀ u : Point F m,
      (∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          (cut1 (Anc F m) F m d N K).bornProb ((polyMarg P.SA W).op g)
            (1 - (ι₁ (Anc F m) F m d N K).ΦB (hatMats S.PB W u (g.eval u))))
        = 1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            (cut1 (Anc F m) F m d N K).bornProb ((polyMarg P.SA W).op g)
              ((ι₁ (Anc F m) F m d N K).ΦB (hatMats S.PB W u (g.eval u))) := by
    intro u
    rw [Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        (cut1 (Anc F m) F m d N K).bornProb_sub_right ((polyMarg P.SA W).op g) 1
          ((ι₁ (Anc F m) F m d N K).ΦB (hatMats S.PB W u (g.eval u))),
      Finset.sum_sub_distrib, ← (cut1 (Anc F m) F m d N K).bornProb_sum_left,
      (polyMarg P.SA W).sum_op, (cut1 (Anc F m) F m d N K).bornProb_one_one P.ψ_unit]
  have h := P.sum_bornProb_polyMarg_one_sub_le W
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hsplit u]] at h
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [P.sum_snorm_sq_nearId W v u]]
  exact h

/-- Alice's copy of the strategy's point measurement, on her physical registers, which it does not
see. -/
def ptA (_P : CutSimul N S K δ) (W : Bas) (u : Point F m) (k : F) :
    Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) 𝒜 :=
  (physInert (Anc F m) F m d N K).ΦA ((ptAtPOVM S.PA W u).op k)

/-- Bob's, on his. -/
def ptB (_P : CutSimul N S K δ) (W : Bas) (u : Point F m) (k : F) :
    Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) ℬ :=
  (physInert (Anc F m) F m d N K).ΦB ((ptAtPOVM S.PB W u).op k)

/-- **The near-identity, expanded**: on the physical model it is a sum of products of Alice's pair
measurement and the syndrome on `A''` against Bob's point measurement. -/
theorem nearId_eq_sum (W : Bas) (u : Point F m) :
    P.nearId W u
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), ∑ a' : F,
          (phys (Anc F m) F m d N K).πA (compHom (smulKron ((polyMarg P.SA W).op g)
              (syn (weylOf W) (indVec u) (g.eval u + a'))))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u a') := by
  rw [nearId, agreeOp]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← sum_kron_syn_eq_hatMats S.PB W u (g.eval u), map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [ι₁_ΦB_smulKron, cut1_πA, cut1_πB, ← mul_assoc, ← map_mul, ← map_mul,
    ← smulKron_eq_diagonal_mul, synPOVM_mats]
  rfl

/-- **Display `eq:qld-pulling-2b` at the interface.** Expanding both factors, the pair
measurement's orthogonality picks out one outcome, `syn_mul_syn` fuses the two syndrome projectors,
and the sum over Bob's point outcome collapses --- for each Weyl outcome `h` exactly one of them
survives, namely `(g - g_h)(u)`. What is left is a sum over the chain's own index set. -/
theorem aOp_mTildeAnc_mul_nearId (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    (phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a)) * P.nearId W u
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
          (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p)) := by
  classical
  rw [nearId_eq_sum, Finset.mul_sum, chainIdx, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  have hterm : ∀ a' : F,
      (phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a))
          * ((phys (Anc F m) F m d N K).πA (compHom (smulKron ((polyMarg P.SA W).op g)
              (syn (weylOf W) (indVec u) (g.eval u + a'))))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u a'))
        = ∑ h : Anc F m, (if dotF h v = dotF (cubeData g) v + a
              ∧ dotF h (indVec u) = g.eval u + a' then
            (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W (g, h)))
              * (phys (Anc F m) F m d N K).πB (P.ptB W u a') else 0) := by
    intro a'
    rw [← mul_assoc, ← map_mul, ← map_mul, P.mTildeAnc_mul_kron W v u a g, map_sum, map_sum,
      Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => hterm a', Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hA : dotF h v = dotF (cubeData g) v + a
  · rw [if_pos ((dotF_chainLabel_eq_iff g h v a).mpr hA),
      Finset.sum_eq_single (g.eval u + dotF h (indVec u))
        (fun a' _ hne => if_neg fun hc => hne (by rw [hc.2, ← add_assoc, add_self, zero_add]))
        (fun hmem => absurd (mem_univ _) hmem)]
    exact if_pos ⟨hA, by rw [← add_assoc, add_self, zero_add]⟩
  · rw [if_neg fun hc => hA ((dotF_chainLabel_eq_iff g h v a).mp hc)]
    exact Finset.sum_eq_zero fun a' _ => if_neg fun hc => hA hc.1

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-3`.** Inserting Alice's copy of the point measurement beside each
term of the chain costs the point measurements' own cross-consistency and nothing else. Two things
hold the bound down: the chain's terms are a projective family in the pair `(g, h)`, so the
outcomes do not interfere (`StateModel.snorm_sq_sum_orthogonal'`) and the fibres of the outcome map
are seen only once (`sum_snorm_sq_proj_comp_le`, inside `sum_snorm_sq_insert_le`). -/
theorem sum_snorm_sq_insert_chain (W : Bas) (v : Anc F m) (u : Point F m) {ε : ℝ}
    (hcons : ∑ k : F, (phys (Anc F m) F m d N K).xSqNorm (P.ptA W u k) (P.ptB W u k) ≤ ε) :
    ∑ a : F, (phys (Anc F m) F m d N K).snorm (∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
        (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
          * ((1 - (phys (Anc F m) F m d N K).πA (P.ptA W u (chainShift u p)))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p)))) ^ 2
      ≤ ε := by
  classical
  have hP : IsPVMIn fun p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m =>
      (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p)) :=
    ((isPVM_chainOp P W).pushforward compHom_one).map _
  have hB : IsPVMIn fun k : F => P.ptB W u k :=
    (isPVM_ptAtPOVM S.projB W u).pushforward (physInert (Anc F m) F m d N K).ΦB_one
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    (phys (Anc F m) F m d N K).snorm_sq_sum_orthogonal' hP _ _]
  refine le_trans (le_of_eq ?_)
    (sum_snorm_sq_insert_le (phys (Anc F m) F m d N K) hP (chainShift u) (P.ptA W u)
      (fun k => hB.star_eq k) (fun k => hB.idem k) hcons)
  simp only [chainIdx]
  exact Finset.sum_fiberwise
    (univ : Finset (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m))
    (fun p => dotF (chainLabel p.1 p.2) v)
    (fun p => (phys (Anc F m) F m d N K).snorm
      ((phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
        * ((1 - (phys (Anc F m) F m d N K).πA (P.ptA W u (chainShift u p)))
          * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p)))) ^ 2)

/-! ### The chain's first four terms, and the three steps between them

`chainS` names the terms displays `eq:qld-pulling-0` to `-3` run through, as elements of the
physical model's algebra, and the three lemmas below are those displays read as bounds on
consecutive deviations --- which is the form `StateModel.sum_snorm_sq_chain_le` consumes. -/

/-- **The chain's first four terms, on the physical model.** `eq:qld-pulling-0` through
`eq:qld-pulling-3`: the exact Pauli measurement, that measurement times the near-identity, the
same written over the chain's index, and the same with Alice's copy of the point measurement
inserted. -/
def chainS (W : Bas) (v : Anc F m) (u : Point F m) :
    ℕ → F → Matrix (PhysReg (Anc F m) F m d K × PhysReg (Anc F m) F m d K)
      (PhysReg (Anc F m) F m d K × PhysReg (Anc F m) F m d K) 𝒞
  | 0 => fun a => (phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a))
  | 1 => fun a => (phys (Anc F m) F m d N K).πA (compHom (P.mTildeAnc W v a)) * P.nearId W u
  | 2 => fun a => ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
        * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p))
  | _ => fun a => ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
        * ((phys (Anc F m) F m d N K).πA (P.ptA W u (chainShift u p))
          * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p)))

/-- **Displays `eq:qld-pulling-2` and `-2b` say the second and third terms are one.** -/
theorem chainS_one_eq_two (W : Bas) (v : Anc F m) (u : Point F m) :
    P.chainS W v u 1 = P.chainS W v u 2 := by
  funext a
  exact P.aOp_mTildeAnc_mul_nearId W v u a

/-- **And the third and fourth differ by what `eq:qld-pulling-3` bounds.** -/
theorem chainS_two_sub_three (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    P.chainS W v u 2 a - P.chainS W v u 3 a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
        (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
          * ((1 - (phys (Anc F m) F m d N K).πA (P.ptA W u (chainShift u p)))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p))) := by
  show (∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
        * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p)))
    - (∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
        * ((phys (Anc F m) F m d N K).πA (P.ptA W u (chainShift u p))
          * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p)))) = _
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [sub_mul, one_mul, mul_sub]

/-- **Step 0 to 1 is `eq:qld-pulling-1`**, at item 1 of `lem:qld-helper`'s own constant. -/
theorem sum_uniform_snorm_sq_chainS_zero_one (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d N K).snorm
            (P.chainS W v u 0 a - P.chainS W v u 1 a) ^ 2) ≤ δ :=
  P.sum_uniform_snorm_sq_nearId_le W v

/-- **Step 1 to 2 is free**, being displays `eq:qld-pulling-2` and `-2b`, which are identities. -/
theorem sum_snorm_sq_chainS_one_two (W : Bas) (v : Anc F m) (u : Point F m) :
    (∑ a : F, (phys (Anc F m) F m d N K).snorm
        (P.chainS W v u 1 a - P.chainS W v u 2 a) ^ 2) = 0 := by
  rw [P.chainS_one_eq_two W v u]
  simp only [sub_self, StateModel.snorm_zero]
  simp

/-- **Step 2 to 3 is `eq:qld-pulling-3`**, the insertion. -/
theorem sum_snorm_sq_chainS_two_three {ε : ℝ} (W : Bas) (v : Anc F m) (u : Point F m)
    (hcons : ∑ k : F, (phys (Anc F m) F m d N K).xSqNorm (P.ptA W u k) (P.ptB W u k) ≤ ε) :
    (∑ a : F, (phys (Anc F m) F m d N K).snorm
        (P.chainS W v u 2 a - P.chainS W v u 3 a) ^ 2) ≤ ε := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by rw [P.chainS_two_sub_three W v u a]]
  exact P.sum_snorm_sq_insert_chain W v u hcons

/-! ### Displays `eq:qld-pulling-3a` and `-3b`: Alice's own pair

The physical model gives Alice both halves of her pair `(A'', A')`; on the physical state a Weyl
projector on the near half acts as the same projector on the far half (`physE_mirror_A`), and once
it is there Alice's copy of the point measurement and her hatted point measurement agree. -/

/-- Alice's Weyl spectral projector on the near half `A'` of her own pair. -/
def ancA (_P : CutSimul N S K δ) (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) 𝒜 :=
  smulKron 1 ((1 : Matrix (Anc F m) (Anc F m) ℂ)
    ⊗ₖ ((1 : Matrix (PadAnc F m d K) (PadAnc F m d K) ℂ) ⊗ₖ proj (weylOf W) h))

/-- The same projector on the far half `A''`, which the physical model also gives her. -/
def ancB (_P : CutSimul N S K δ) (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) 𝒜 :=
  compHom (smulKron (1 : Matrix (PadAnc F m d K × Anc F m) (PadAnc F m d K × Anc F m) 𝒜)
    (proj (weylOf W) h))

/-- **Display `eq:qld-pulling-3a` on the physical state**: the two halves of Alice's pair are
maximally entangled and the projectors are symmetric. -/
theorem ancProj_mulVec_mVec (W : Bas) (h : Anc F m) :
    (phys (Anc F m) F m d N K).π ((phys (Anc F m) F m d N K).πA (P.ancA W h))
        (phys (Anc F m) F m d N K).ψ
      = (phys (Anc F m) F m d N K).π ((phys (Anc F m) F m d N K).πA (P.ancB W h))
        (phys (Anc F m) F m d N K).ψ := by
  rw [ancA, ancB, physE_mirror_A, proj_weylOf_transpose, compHom_smulKron_one]

/-- **Alice's hatted point measurement**, on her physical registers: on `(A, A')`, with the padding
and the far half inert. -/
def hatA (_P : CutSimul N S K δ) (W : Bas) (u : Point F m) (c : F) :
    Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) 𝒜 :=
  compHom (diagonal fun _ : Anc F m => (ι₁ (Anc F m) F m d N K).ΦA (hatMats S.PA W u c))

/-- **Display `eq:qld-pulling-3b` on Alice's physical registers.** -/
theorem ptA_mul_ancA (W : Bas) (u : Point F m) (c : F) (h : Anc F m) :
    P.ptA W u (c + dotF h (indVec u)) * P.ancA W h = P.hatA W u c * P.ancA W h := by
  have hA : P.ancA W h = compHom (diagonal fun _ : Anc F m =>
      (ι₁ (Anc F m) F m d N K).ΦA (smulKron (1 : 𝒜) (proj (weylOf W) h))) := by
    rw [ι₁_ΦA, compHom_diagonal_compHom_diagonal_smulKron]
    rfl
  have hp : ∀ k : F, P.ptA W u k = compHom (diagonal fun _ : Anc F m =>
      (ι₁ (Anc F m) F m d N K).ΦA
        (smulKron ((ptAtPOVM S.PA W u).op k) (1 : Matrix (Anc F m) (Anc F m) ℂ))) := by
    intro k
    rw [ι₁_ΦA, compHom_diagonal_compHom_diagonal_smulKron, one_kronecker_one, one_kronecker_one,
      smulKron_one_right]
    rfl
  rw [hA, hp, hatA, ← map_mul, ← map_mul, diagonal_mul_diagonal, diagonal_mul_diagonal,
    ← map_mul, ← map_mul, smulKron_mul, mul_one, one_mul, hatMats_mul_proj]

/-- **Displays `eq:qld-pulling-3a` and `-3b` together.** Inserting Alice's own near half beside the
far half the chain already carries changes nothing on the state, and once it is there the point
measurement and the hatted point measurement agree. -/
theorem ancB_ptA_mulVec (W : Bas) (u : Point F m) (c : F) (h : Anc F m)
    (Y : Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) ℬ) :
    (phys (Anc F m) F m d N K).π
        ((phys (Anc F m) F m d N K).πA (P.ancB W h * P.ptA W u (c + dotF h (indVec u)))
          * (phys (Anc F m) F m d N K).πB Y) (phys (Anc F m) F m d N K).ψ
      = (phys (Anc F m) F m d N K).π
        ((phys (Anc F m) F m d N K).πA (P.ancB W h * P.hatA W u c)
          * (phys (Anc F m) F m d N K).πB Y) (phys (Anc F m) F m d N K).ψ := by
  have hmove : ∀ Z : Matrix (PadAnc F m d K × Anc F m) (PadAnc F m d K × Anc F m) 𝒜,
      (phys (Anc F m) F m d N K).π ((phys (Anc F m) F m d N K).πA
          (P.ancB W h * compHom (diagonal fun _ : Anc F m => Z))
          * (phys (Anc F m) F m d N K).πB Y) (phys (Anc F m) F m d N K).ψ
        = (phys (Anc F m) F m d N K).π ((phys (Anc F m) F m d N K).πA
          (compHom (diagonal fun _ : Anc F m => Z) * P.ancA W h)
          * (phys (Anc F m) F m d N K).πB Y) (phys (Anc F m) F m d N K).ψ := by
    intro Z
    have hc : P.ancB W h * compHom (diagonal fun _ : Anc F m => Z)
        = compHom (diagonal fun _ : Anc F m => Z) * P.ancB W h := by
      rw [ancB, ← map_mul, ← map_mul, smulKron_one_mul_diagonal, ← smulKron_eq_diagonal_mul]
    have e : ∀ T : Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) 𝒜,
        (phys (Anc F m) F m d N K).πA (compHom (diagonal fun _ : Anc F m => Z) * T)
            * (phys (Anc F m) F m d N K).πB Y
          = ((phys (Anc F m) F m d N K).πA (compHom (diagonal fun _ : Anc F m => Z))
            * (phys (Anc F m) F m d N K).πB Y) * (phys (Anc F m) F m d N K).πA T := by
      intro T
      rw [map_mul, mul_assoc, ((phys (Anc F m) F m d N K).commute T Y).eq, ← mul_assoc]
    rw [hc, e, e, map_mul (phys (Anc F m) F m d N K).π _ ((phys (Anc F m) F m d N K).πA (P.ancB W h)),
      map_mul (phys (Anc F m) F m d N K).π _ ((phys (Anc F m) F m d N K).πA (P.ancA W h)),
      mul_apply_eq_comp, mul_apply_eq_comp, P.ancProj_mulVec_mVec W h]
  have hp : P.ptA W u (c + dotF h (indVec u)) = compHom (diagonal fun _ : Anc F m =>
      diagonal fun _ : PadAnc F m d K × Anc F m => (ptAtPOVM S.PA W u).op (c + dotF h (indVec u))) :=
    (compHom_diagonal_diagonal _).symm
  have key := P.ptA_mul_ancA W u c h
  rw [hp, hatA] at key
  rw [hp, hmove, hatA, hmove, key]

/-- **Display `eq:qld-pulling-3b`'s term**: the chain's third term with Alice's own hatted point
measurement in place of her copy of the point measurement. -/
def chainS3b (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Matrix (PhysReg (Anc F m) F m d K × PhysReg (Anc F m) F m d K)
      (PhysReg (Anc F m) F m d K × PhysReg (Anc F m) F m d K) 𝒞 :=
  ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
    (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p) * P.hatA W u (p.1.eval u))
      * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p))

/-- **Displays `eq:qld-pulling-3a` and `-3b`, on the chain's third term.** -/
theorem chainS_three_mulVec (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    (phys (Anc F m) F m d N K).π (P.chainS W v u 3 a) (phys (Anc F m) F m d N K).ψ
      = (phys (Anc F m) F m d N K).π (P.chainS3b W v u a) (phys (Anc F m) F m d N K).ψ := by
  classical
  have hterm : ∀ p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
      (phys (Anc F m) F m d N K).π ((phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
          * ((phys (Anc F m) F m d N K).πA (P.ptA W u (chainShift u p))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p))))
          (phys (Anc F m) F m d N K).ψ
        = (phys (Anc F m) F m d N K).π
          ((phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p) * P.hatA W u (p.1.eval u))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p)))
          (phys (Anc F m) F m d N K).ψ := by
    intro p
    have hD : compHom (P.chainOp W p)
        = compHom (diagonal fun _ : Anc F m => (polyMarg P.SA W).op p.1) * P.ancB W p.2 := by
      rw [P.chainOp_eq_mul W p, map_mul]
      rfl
    have e1 : ∀ (X : Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) 𝒜)
        (Y : Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) ℬ),
        (phys (Anc F m) F m d N K).πA
            (compHom (diagonal fun _ : Anc F m => (polyMarg P.SA W).op p.1) * P.ancB W p.2)
          * ((phys (Anc F m) F m d N K).πA X * (phys (Anc F m) F m d N K).πB Y)
        = (phys (Anc F m) F m d N K).πA
            (compHom (diagonal fun _ : Anc F m => (polyMarg P.SA W).op p.1))
          * ((phys (Anc F m) F m d N K).πA (P.ancB W p.2 * X)
            * (phys (Anc F m) F m d N K).πB Y) := by
      intro X Y
      rw [map_mul, map_mul]
      simp only [mul_assoc]
    have e2 : (phys (Anc F m) F m d N K).πA
          (compHom (diagonal fun _ : Anc F m => (polyMarg P.SA W).op p.1) * P.ancB W p.2
            * P.hatA W u (p.1.eval u))
          * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p))
        = (phys (Anc F m) F m d N K).πA
            (compHom (diagonal fun _ : Anc F m => (polyMarg P.SA W).op p.1))
          * ((phys (Anc F m) F m d N K).πA (P.ancB W p.2 * P.hatA W u (p.1.eval u))
            * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p))) := by
      rw [map_mul, map_mul, map_mul]
      simp only [mul_assoc]
    rw [hD, e1, e2, show chainShift u p = p.1.eval u + dotF p.2 (indVec u) from rfl,
      map_mul (phys (Anc F m) F m d N K).π, mul_apply_eq_comp,
      P.ancB_ptA_mulVec W u (p.1.eval u) p.2, ← mul_apply_eq_comp, ← map_mul]
  show (phys (Anc F m) F m d N K).π (∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
      (phys (Anc F m) F m d N K).πA (compHom (P.chainOp W p))
        * ((phys (Anc F m) F m d N K).πA (P.ptA W u (chainShift u p))
          * (phys (Anc F m) F m d N K).πB (P.ptB W u (chainShift u p))))
      (phys (Anc F m) F m d N K).ψ = _
  rw [chainS3b, map_sum, map_sum, _root_.sum_apply, _root_.sum_apply]
  exact Finset.sum_congr rfl fun p _ => hterm p

end SimulPair

end First

end MIPRE.QLD

end

end
