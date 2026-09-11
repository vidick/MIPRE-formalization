/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/EntropicArena.lean
-/
/-
# The entropic resolver arena: construction (node 1.2.6, proof layer)

The arena of `resolver_arena_entropic` (04_resolver_corner.tex, thm
common-resolver-arena together with lem resolver-entropy-cutoffs), built as
planned in `PLAN-resolver-entropic.md`:

* the algebra is the matrix amplification `N = M_d(vnAlg M)` of the concrete
  von Neumann algebra (`VN/ConcreteVN.lean`), `d = card (I ⊕ Unit ⊕ J)`;
* the Alice columns are `cᵢ = √𝒦_A ∘ (matrix unit (i, src))` where `𝒦_A` is
  the block operator of the resolver Gram kernels `K(L Fᵢ, L Fᵢ')`
  (`Resolver/ResolverKernel.lean`), positive as a limit of integrals of
  squares; so `cᵢ'* cᵢ = E(K(Fᵢ', Fᵢ))` and `cᵢ* cᵢ = E(Fᵢ)` (`kern_self`);
  Bob's rows `dⱼ` mirror this with `dⱼ dⱼ'* = E(K(Gⱼ, Gⱼ'))`;
* the POVMs are the singular-safe Douglas POVMs of `Resolver/Douglas.lean`
  attached to the factors of the refinements, so `cᵢ* 𝖠ᵢᵃ cᵢ = E(Fᵢᵃ)` and
  `dⱼ 𝖡ⱼᵇ dⱼ* = E(Gⱼᵇ)` (eqs resolver-refinement-identities);
* the branch is `√d • ι(cᵢ E(σ) dⱼ)` (eq joint-rectangular-branch) and the two
  exact pairing identities follow from the traciality of `N.τ`.

The entropy budgets are proved in `Resolver/EntropicArenaBudget.lean`.
Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.ArenaDef
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.ResolverKernel
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.Douglas
import MIPRE.Background.Repetition.CommutingRepetition.VN.BlockOperators

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace EntropicArena

noncomputable section

open scoped BigOperators InnerProductSpace Topology
open StdTracialAlgebra Resolver Block Filter MeasureTheory

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

variable (M : StdTracialAlgebra.{0})
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]

/-! ## The block index -/

/-- The block index: Alice's `I`, the source coordinate, Bob's `J`. -/
abbrev Idx (I J : Type) : Type := I ⊕ Unit ⊕ J

variable (I J) in
/-- The source coordinate. -/
def src : Idx I J := Sum.inr (Sum.inl ())

/-- Alice's coordinates. -/
def ai (i : I) : Idx I J := Sum.inl i

/-- Bob's coordinates. -/
def bj (j : J) : Idx I J := Sum.inr (Sum.inr j)

instance : Nonempty (Idx I J) := ⟨src I J⟩

theorem ai_injective : Function.Injective (ai (I := I) (J := J)) := fun _ _ h => Sum.inl_injective h

theorem bj_injective : Function.Injective (bj (I := I) (J := J)) := fun _ _ h =>
  Sum.inr_injective (Sum.inr_injective h)

variable (I J) in
/-- The block Hilbert space. -/
abbrev 𝓑 : Type := Block.BH M (Idx I J)

variable (I J) in
/-- The block algebra. -/
abbrev 𝔑 : StarSubalgebra ℂ (𝓑 M I J →L[ℂ] 𝓑 M I J) := Block.blockAlg M (Idx I J)

variable (I J) in
/-- The arena algebra. -/
abbrev N : StdTracialAlgebra.{0} := Block.N M (Idx I J)

variable (I J) in
/-- The amplification dimension. -/
abbrev d : ℕ := Block.dim (Idx I J)

/-! ## The left representation into `vnAlg` -/

/-- `L a` as an element of `vnAlg M`. -/
def Lv (a : M.A) : ↥M.vnAlg := ⟨M.L a, M.L_mem_vnAlg a⟩

theorem Lv_val (a : M.A) : (Lv M a).1 = M.L a := rfl

theorem Lv_mul (a b : M.A) : Lv M (a * b) = Lv M a * Lv M b := Subtype.ext (map_mul M.L a b)

theorem Lv_star (a : M.A) : Lv M (star a) = star (Lv M a) := Subtype.ext (map_star M.L a)

theorem Lv_one : Lv M 1 = 1 := Subtype.ext (map_one M.L)

theorem Lv_sum {ι : Type*} (s : Finset ι) (f : ι → M.A) :
    Lv M (∑ x ∈ s, f x) = ∑ x ∈ s, Lv M (f x) := by
  apply Subtype.ext
  rw [Lv_val, map_sum]
  exact (map_sum M.vnAlg.subtype (fun x => Lv M (f x)) s).symm

theorem Lv_sub (a b : M.A) : Lv M (a - b) = Lv M a - Lv M b := Subtype.ext (map_sub M.L a b)

theorem L_nonneg {a : M.A} (ha : IsPosElem a) : (0 : M.H →L[ℂ] M.H) ≤ M.L a := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact M.L_isPositive ha

theorem L_le_one {a : M.A} (ha : IsPosElem (1 - a)) : M.L a ≤ 1 := by
  have := L_nonneg M ha
  rw [map_sub, map_one] at this
  exact sub_nonneg.mp this

/-! ## The data -/

variable (F : I → A → M.A) (G : J → B → M.A)

/-- The hypotheses of `resolver_arena_entropic`. -/
structure Hyp : Prop where
  hF : ∀ i a, IsPosElem (F i a)
  hG : ∀ j b, IsPosElem (G j b)
  hF1 : ∀ i, IsPosElem (1 - ∑ a, F i a)
  hG1 : ∀ j, IsPosElem (1 - ∑ b, G j b)

/-- Alice's totals. -/
abbrev FA (i : I) : M.A := ∑ a, F i a

/-- Bob's totals. -/
abbrev GB (j : J) : M.A := ∑ b, G j b

/-- Alice's totals as operators. -/
abbrev LF (i : I) : M.H →L[ℂ] M.H := M.L (FA M F i)

/-- Bob's totals as operators. -/
abbrev LG (j : J) : M.H →L[ℂ] M.H := M.L (GB M G j)

variable {F G} (h : Hyp M F G)
include h

theorem LF_nonneg (i : I) : 0 ≤ LF M F i :=
  L_nonneg M (isPosElem_sum _ _ fun a _ => h.hF i a)

theorem LF_le_one (i : I) : LF M F i ≤ 1 := L_le_one M (h.hF1 i)

theorem LG_nonneg (j : J) : 0 ≤ LG M G j :=
  L_nonneg M (isPosElem_sum _ _ fun b _ => h.hG j b)

theorem LG_le_one (j : J) : LG M G j ≤ 1 := L_le_one M (h.hG1 j)

/-! ## The kernels -/

/-- Alice's kernel entries `K(L Fᵢ, L Fᵢ')` in `vnAlg M`. -/
noncomputable def KA (i i' : I) : ↥M.vnAlg :=
  ⟨kern (LF M F i) (LF M F i'), kern_mem M.isClosed_vnAlg (LF_nonneg M h i) (LF_nonneg M h i')
    (M.L_mem_vnAlg _) (M.L_mem_vnAlg _)⟩

/-- Bob's kernel entries `K(L Gⱼ, L Gⱼ')`. -/
noncomputable def KB (j j' : J) : ↥M.vnAlg :=
  ⟨kern (LG M G j) (LG M G j'), kern_mem M.isClosed_vnAlg (LG_nonneg M h j) (LG_nonneg M h j')
    (M.L_mem_vnAlg _) (M.L_mem_vnAlg _)⟩

theorem KA_val (i i' : I) : (KA M h i i').1 = kern (LF M F i) (LF M F i') := rfl

theorem KB_val (j j' : J) : (KB M h j j').1 = kern (LG M G j) (LG M G j') := rfl

theorem KA_self (i : I) : KA M h i i = Lv M (FA M F i) :=
  Subtype.ext (kern_self (LF_nonneg M h i) (LF_le_one M h i))

theorem KB_self (j : J) : KB M h j j = Lv M (GB M G j) :=
  Subtype.ext (kern_self (LG_nonneg M h j) (LG_le_one M h j))

/-! ## Block kernels and their positivity -/

/-- The block kernel of a positive family placed at coordinates `c`. -/
def blockKern {ι : Type} [Fintype ι] (c : ι → Idx I J) (Fs : ι → M.H →L[ℂ] M.H) :
    𝓑 M I J →L[ℂ] 𝓑 M I J :=
  ∑ i, ∑ i', place M (Idx I J) (c i) (c i') (kern (Fs i) (Fs i'))

omit h in
theorem blockKern_mem {ι : Type} [Fintype ι] (c : ι → Idx I J) (Fs : ι → M.H →L[ℂ] M.H)
    (hFs0 : ∀ i, 0 ≤ Fs i) (hmem : ∀ i, Fs i ∈ M.vnAlg) :
    blockKern M c Fs ∈ 𝔑 M I J := by
  refine sum_mem fun i _ => sum_mem fun i' _ => ?_
  exact place_mem M (Idx I J) _ _
    (kern_mem M.isClosed_vnAlg (hFs0 i) (hFs0 i') (hmem i) (hmem i'))

omit h in
theorem entry_blockKern {ι : Type} [Fintype ι] {c : ι → Idx I J} (hc : Function.Injective c)
    (Fs : ι → M.H →L[ℂ] M.H) (i i' : ι) :
    entry M (Idx I J) (blockKern M c Fs) (c i) (c i') = kern (Fs i) (Fs i') := by
  unfold blockKern
  rw [entry_sum]
  simp only [entry_sum, entry_place]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i']
    · simp
    · intro q _ hq
      simp [hc.ne (Ne.symm hq)]
    · intro hq; exact absurd (Finset.mem_univ i') hq
  · intro q _ hq
    refine Finset.sum_eq_zero fun q' _ => ?_
    simp [hc.ne (Ne.symm hq)]
  · intro hq; exact absurd (Finset.mem_univ i) hq

omit h in
/-- **Positivity of the block kernel**: it is the limit of the integrals
`∫ ρ(u)* ρ(u) du` over the cutoffs. -/
theorem blockKern_nonneg {ι : Type} [Fintype ι] (c : ι → Idx I J) (Fs : ι → M.H →L[ℂ] M.H)
    (hFs0 : ∀ i, 0 ≤ Fs i) : 0 ≤ blockKern M c Fs := by
  -- the row operator
  set ρ : ℝ → 𝓑 M I J →L[ℂ] 𝓑 M I J :=
    fun u => ∑ i', place M (Idx I J) (src I J) (c i') (fib (Fs i') u) with hρ
  have hρsq : ∀ u, 0 < u → star (ρ u) * ρ u
      = ∑ i, ∑ i', place M (Idx I J) (c i) (c i') (fib (Fs i) u * fib (Fs i') u) := by
    intro u hu
    show star (∑ i', place M (Idx I J) (src I J) (c i') (fib (Fs i') u))
      * (∑ i', place M (Idx I J) (src I J) (c i') (fib (Fs i') u)) = _
    rw [ContinuousLinearMap.star_eq_adjoint, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [← ContinuousLinearMap.star_eq_adjoint, star_place, place_mul_place, if_pos rfl,
      (fib_isSelfAdjoint (F := Fs i) (u := u)).star_eq]
  have hcont : ∀ i, ContinuousOn (fun u => fib (Fs i) u) (Set.Ioi 0) :=
    fun i => continuousOn_fib_param (hFs0 i)
  have hρcont : ContinuousOn ρ (Set.Ioi 0) := by
    simp only [hρ]
    exact continuousOn_finsetSum _ fun i' _ =>
      (place M (Idx I J) _ _).continuous.comp_continuousOn (hcont i')
  -- the cutoff integrals are positive
  have hpos : ∀ n : ℕ, 0 ≤ ∫ u in αseq n..Tseq n, star (ρ u) * ρ u := by
    intro n
    refine intervalIntegral_nonneg_of_nonneg (αseq_le_Tseq n) ?_ fun u _ => star_mul_self_nonneg _
    have hstar : ContinuousOn (fun u => star (ρ u)) (Set.uIcc (αseq n) (Tseq n)) := by
      have : (fun u => star (ρ u)) = fun u => ContinuousLinearMap.adjoint (ρ u) := by
        funext u; exact ContinuousLinearMap.star_eq_adjoint _
      rw [this]
      exact (ContinuousLinearMap.adjoint (E := 𝓑 M I J) (F := 𝓑 M I J)).continuous.comp_continuousOn
        (hρcont.mono (uIcc_subset_Ioi n))
    exact (hstar.mul (hρcont.mono (uIcc_subset_Ioi n))).intervalIntegrable
  -- and equal the placed cutoff kernels
  have hint : ∀ n : ℕ, ∫ u in αseq n..Tseq n, star (ρ u) * ρ u
      = ∑ i, ∑ i', place M (Idx I J) (c i) (c i')
          (∫ u in αseq n..Tseq n, fib (Fs i) u * fib (Fs i') u) := by
    intro n
    have hII : ∀ i i', IntervalIntegrable (fun u => fib (Fs i) u * fib (Fs i') u) volume
        (αseq n) (Tseq n) := fun i i' => intervalIntegrable_fib_mul_fib (hFs0 i) (hFs0 i') n
    have hIP : ∀ i i', IntervalIntegrable
        (fun u => place M (Idx I J) (c i) (c i') (fib (Fs i) u * fib (Fs i') u)) volume
        (αseq n) (Tseq n) := fun i i' =>
      ((place M (Idx I J) (c i) (c i')).continuous.comp_continuousOn
        (((hcont i).mul (hcont i')).mono (uIcc_subset_Ioi n))).intervalIntegrable
    have hIS : ∀ i, IntervalIntegrable
        (fun u => ∑ i', place M (Idx I J) (c i) (c i') (fib (Fs i) u * fib (Fs i') u)) volume
        (αseq n) (Tseq n) := fun i =>
      (continuousOn_finsetSum _ fun i' _ =>
        (place M (Idx I J) (c i) (c i')).continuous.comp_continuousOn
          (((hcont i).mul (hcont i')).mono (uIcc_subset_Ioi n))).intervalIntegrable
    rw [intervalIntegral.integral_congr (fun u hu => hρsq u (uIcc_subset_Ioi n hu)),
      intervalIntegral.integral_finsetSum (fun i _ => hIS i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun i' _ => hIP i i')]
    refine Finset.sum_congr rfl fun i' _ => ?_
    exact ContinuousLinearMap.intervalIntegral_comp_comm _ (hII i i')
  -- pass to the limit
  have hlim : Tendsto (fun n => ∑ i, ∑ i', place M (Idx I J) (c i) (c i')
      (∫ u in αseq n..Tseq n, fib (Fs i) u * fib (Fs i') u)) atTop (𝓝 (blockKern M c Fs)) := by
    unfold blockKern
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun i' _ => ?_
    exact ((place M (Idx I J) (c i) (c i')).continuous.tendsto _).comp
      (tendsto_intervalIntegral_kern (hFs0 i) (hFs0 i'))
  refine ge_of_tendsto' hlim fun n => ?_
  rw [← hint n]
  exact hpos n

/-! ## The block kernels and their square roots -/

/-- Alice's block kernel `[K(L Fᵢ, L Fᵢ')]` on the `I`-block. -/
def 𝒦A (_h : Hyp M F G) : 𝓑 M I J →L[ℂ] 𝓑 M I J := blockKern M (ai (J := J)) (LF M F)

/-- Bob's block kernel `[K(L Gⱼ, L Gⱼ')]` on the `J`-block. -/
def 𝒦B (_h : Hyp M F G) : 𝓑 M I J →L[ℂ] 𝓑 M I J := blockKern M (bj (I := I)) (LG M G)

theorem 𝒦A_mem : 𝒦A M h ∈ 𝔑 M I J :=
  blockKern_mem M _ _ (LF_nonneg M h) fun _ => M.L_mem_vnAlg _

theorem 𝒦B_mem : 𝒦B M h ∈ 𝔑 M I J :=
  blockKern_mem M _ _ (LG_nonneg M h) fun _ => M.L_mem_vnAlg _

theorem 𝒦A_nonneg : 0 ≤ 𝒦A M h := blockKern_nonneg M _ _ (LF_nonneg M h)

theorem 𝒦B_nonneg : 0 ≤ 𝒦B M h := blockKern_nonneg M _ _ (LG_nonneg M h)

theorem entry_𝒦A (i i' : I) :
    entry M (Idx I J) (𝒦A M h) (ai i) (ai i') = (KA M h i i').1 :=
  entry_blockKern M ai_injective _ i i'

theorem entry_𝒦B (j j' : J) :
    entry M (Idx I J) (𝒦B M h) (bj j) (bj j') = (KB M h j j').1 :=
  entry_blockKern M bj_injective _ j j'

/-- `𝒞_A = √𝒦_A`. -/
def 𝒞A : 𝓑 M I J →L[ℂ] 𝓑 M I J := CFC.sqrt (𝒦A M h)

/-- `𝒞_B = √𝒦_B`. -/
def 𝒞B : 𝓑 M I J →L[ℂ] 𝓑 M I J := CFC.sqrt (𝒦B M h)

theorem 𝒞A_sq : 𝒞A M h * 𝒞A M h = 𝒦A M h := CFC.sqrt_mul_sqrt_self _ (𝒦A_nonneg M h)

theorem 𝒞B_sq : 𝒞B M h * 𝒞B M h = 𝒦B M h := CFC.sqrt_mul_sqrt_self _ (𝒦B_nonneg M h)

theorem 𝒞A_sa : IsSelfAdjoint (𝒞A M h) := by
  have h0 : 0 ≤ 𝒞A M h := CFC.sqrt_nonneg _
  exact IsSelfAdjoint.of_nonneg h0

theorem 𝒞B_sa : IsSelfAdjoint (𝒞B M h) := by
  have h0 : 0 ≤ 𝒞B M h := CFC.sqrt_nonneg _
  exact IsSelfAdjoint.of_nonneg h0

omit h in
theorem sqrt_mem {T : 𝓑 M I J →L[ℂ] 𝓑 M I J} (hT0 : 0 ≤ T) (hT : T ∈ 𝔑 M I J) :
    CFC.sqrt T ∈ 𝔑 M I J := by
  rw [CFC.sqrt_eq_real_sqrt _ hT0, cfcₙ_eq_cfc (hf0 := by simp)]
  exact cfc_mem (𝕜' := ℂ) (hs := isClosed_blockAlg M (Idx I J)) Real.sqrt hT

theorem 𝒞A_mem : 𝒞A M h ∈ 𝔑 M I J := sqrt_mem M (𝒦A_nonneg M h) (𝒦A_mem M h)

theorem 𝒞B_mem : 𝒞B M h ∈ 𝔑 M I J := sqrt_mem M (𝒦B_nonneg M h) (𝒦B_mem M h)

/-! ## Matrix units, columns and rows -/

omit h in
/-- The matrix unit `e_{r r'}`. -/
def U (r r' : Idx I J) : ↥(𝔑 M I J) :=
  ⟨place M (Idx I J) r r' 1, place_mem M _ r r' (one_mem _)⟩

omit h in
theorem U_val (r r' : Idx I J) : (U M r r').1 = place M (Idx I J) r r' 1 := rfl

omit h in
theorem star_U (r r' : Idx I J) : star (U M r r') = U M r' r := by
  apply Subtype.ext
  show star (place M (Idx I J) r r' 1) = place M (Idx I J) r' r 1
  rw [star_place, star_one]

/-- `𝒞_A` as an element of the block algebra. -/
def CA : ↥(𝔑 M I J) := ⟨𝒞A M h, 𝒞A_mem M h⟩

/-- `𝒞_B` as an element of the block algebra. -/
def CB : ↥(𝔑 M I J) := ⟨𝒞B M h, 𝒞B_mem M h⟩

/-- Alice's column `cᵢ = 𝒞_A e_{i, src}`. -/
def cA (i : I) : ↥(𝔑 M I J) := CA M h * U M (ai i) (src I J)

/-- Bob's row `dⱼ = e_{src, j} 𝒞_B`. -/
def dB (j : J) : ↥(𝔑 M I J) := U M (src I J) (bj j) * CB M h

/-- The corner copy at the source coordinate. -/
abbrev Ecor (T : ↥M.vnAlg) : ↥(𝔑 M I J) := Block.E M (Idx I J) (src I J) T

omit h in
theorem Ecor_val (T : ↥M.vnAlg) :
    (Ecor M (I := I) (J := J) T).1 = place M (Idx I J) (src I J) (src I J) T.1 := rfl

/-- `cᵢ'* cᵢ = E(K(Fᵢ', Fᵢ))` (eq resolver-square-identities, polarized). -/
theorem star_cA_mul_cA (i i' : I) :
    star (cA M h i') * cA M h i = Ecor M (KA M h i' i) := by
  apply Subtype.ext
  show star (𝒞A M h * place M (Idx I J) (ai i') (src I J) 1)
      * (𝒞A M h * place M (Idx I J) (ai i) (src I J) 1)
    = place M (Idx I J) (src I J) (src I J) (KA M h i' i).1
  rw [star_mul, star_place, star_one, (𝒞A_sa M h).star_eq, mul_assoc, ← mul_assoc (𝒞A M h),
    𝒞A_sq, ← mul_assoc, place_one_mul_mul_place_one, entry_𝒦A]

/-- `dⱼ dⱼ'* = E(K(Gⱼ, Gⱼ'))`. -/
theorem dB_mul_star_dB (j j' : J) :
    dB M h j * star (dB M h j') = Ecor M (KB M h j j') := by
  apply Subtype.ext
  show (place M (Idx I J) (src I J) (bj j) 1 * 𝒞B M h)
      * star (place M (Idx I J) (src I J) (bj j') 1 * 𝒞B M h)
    = place M (Idx I J) (src I J) (src I J) (KB M h j j').1
  rw [star_mul, star_place, star_one, (𝒞B_sa M h).star_eq, mul_assoc, ← mul_assoc (𝒞B M h),
    𝒞B_sq, ← mul_assoc, place_one_mul_mul_place_one, entry_𝒦B]

theorem star_cA_mul_cA_self (i : I) :
    star (cA M h i) * cA M h i = Ecor M (Lv M (FA M F i)) := by
  rw [star_cA_mul_cA, KA_self]

theorem dB_mul_star_dB_self (j : J) :
    dB M h j * star (dB M h j) = Ecor M (Lv M (GB M G j)) := by
  rw [dB_mul_star_dB, KB_self]

/-! ## Algebra of the corner copy -/

omit h in
theorem Ecor_Lv_mul (a b : M.A) :
    Ecor M (I := I) (J := J) (Lv M a) * Ecor M (Lv M b) = Ecor M (Lv M (a * b)) := by
  rw [← E_mul, ← Lv_mul]

omit h in
theorem star_Ecor_Lv (a : M.A) :
    star (Ecor M (I := I) (J := J) (Lv M a)) = Ecor M (Lv M (star a)) := by
  rw [← E_star, ← Lv_star]

omit h in
/-- Coercion of a sum in the block algebra. -/
theorem coe_sum_𝔑 {ι : Type*} (t : Finset ι) (f : ι → ↥(𝔑 M I J)) :
    ((∑ x ∈ t, f x : ↥(𝔑 M I J)) : 𝓑 M I J →L[ℂ] 𝓑 M I J) = ∑ x ∈ t, (f x : 𝓑 M I J →L[ℂ] 𝓑 M I J) :=
  map_sum (𝔑 M I J).subtype f t

/-! ## The Douglas POVMs -/

variable [Nonempty A] [Nonempty B]
variable (kA : I → A → ℕ) (xA : ∀ i a, Fin (kA i a) → M.A)
  (hxA : ∀ i a, F i a = ∑ k, star (xA i a k) * xA i a k)
variable (kB : J → B → ℕ) (yB : ∀ j b, Fin (kB j b) → M.A)
  (hyB : ∀ j b, G j b = ∑ l, star (yB j b l) * yB j b l)

/-- Alice's factor index at `i`. -/
abbrev IdxA (i : I) : Type := Σ a : A, Fin (kA i a)

/-- Bob's factor index at `j`. -/
abbrev IdxB (j : J) : Type := Σ b : B, Fin (kB j b)

omit h in
/-- The factors of Alice's refinements, as corner operators. -/
def xopA (i : I) (p : IdxA kA i) : 𝓑 M I J →L[ℂ] 𝓑 M I J :=
  (Ecor M (Lv M (xA i p.1 p.2))).1

omit h in
/-- The factors of Bob's refinements, as corner operators. -/
def yopB (j : J) (p : IdxB kB j) : 𝓑 M I J →L[ℂ] 𝓑 M I J :=
  (Ecor M (Lv M (yB j p.1 p.2))).1

omit h in
theorem xopA_mem (i : I) (p : IdxA kA i) : xopA M kA xA i p ∈ 𝔑 M I J :=
  (Ecor M (Lv M (xA i p.1 p.2))).2

omit h in
theorem yopB_mem (j : J) (p : IdxB kB j) : yopB M kB yB j p ∈ 𝔑 M I J :=
  (Ecor M (Lv M (yB j p.1 p.2))).2

include hxA in
/-- `∑ x* x = cᵢ* cᵢ` for Alice. -/
theorem hxeA (i : I) :
    ∑ p, star (xopA M kA xA i p) * xopA M kA xA i p = star (cA M h i).1 * (cA M h i).1 := by
  have e1 : ∑ p, star (xopA M kA xA i p) * xopA M kA xA i p
      = ((∑ p : IdxA kA i, Ecor M (I := I) (J := J) (Lv M (star (xA i p.1 p.2) * xA i p.1 p.2)) :
          ↥(𝔑 M I J)) : 𝓑 M I J →L[ℂ] 𝓑 M I J) := by
    rw [coe_sum_𝔑]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Ecor_Lv_mul, ← star_Ecor_Lv]
    rfl
  rw [e1, ← E_sum, ← Lv_sum, Fintype.sum_sigma]
  simp only [← hxA]
  show _ = (star (cA M h i) * cA M h i).1
  rw [star_cA_mul_cA_self]

include hyB in
/-- `∑ y* y = dⱼ dⱼ*` for Bob (with `c := dⱼ*`). -/
theorem hyeB (j : J) :
    ∑ p, star (yopB M kB yB j p) * yopB M kB yB j p
      = star (star (dB M h j)).1 * (star (dB M h j)).1 := by
  have e1 : ∑ p, star (yopB M kB yB j p) * yopB M kB yB j p
      = ((∑ p : IdxB kB j, Ecor M (I := I) (J := J) (Lv M (star (yB j p.1 p.2) * yB j p.1 p.2)) :
          ↥(𝔑 M I J)) : 𝓑 M I J →L[ℂ] 𝓑 M I J) := by
    rw [coe_sum_𝔑]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Ecor_Lv_mul, ← star_Ecor_Lv]
    rfl
  rw [e1, ← E_sum, ← Lv_sum, Fintype.sum_sigma]
  simp only [← hyB]
  show _ = (star (star (dB M h j)) * star (dB M h j)).1
  rw [star_star, dB_mul_star_dB_self]

include hxA in
/-- Alice's Douglas factors. -/
def zA (i : I) (p : IdxA kA i) : 𝓑 M I J →L[ℂ] 𝓑 M I J :=
  Douglas.z (hxeA M h kA xA hxA i).le p

include hyB in
/-- Bob's Douglas factors. -/
def zB (j : J) (p : IdxB kB j) : 𝓑 M I J →L[ℂ] 𝓑 M I J :=
  Douglas.z (hyeB M h kB yB hyB j).le p

include hxA in
theorem zA_mem (i : I) (p : IdxA kA i) : zA M h kA xA hxA i p ∈ 𝔑 M I J := by
  rw [mem_blockAlg_iff_comm]
  intro b
  refine Douglas.z_comm _ ?_ ?_ ?_ p
  · exact (mem_blockAlg_iff_comm M _).mp (cA M h i).2 b
  · rw [star_Rt]
    exact (mem_blockAlg_iff_comm M _).mp (cA M h i).2 (star b)
  · intro p'
    exact (mem_blockAlg_iff_comm M _).mp (xopA_mem M kA xA i p') b

include hyB in
theorem zB_mem (j : J) (p : IdxB kB j) : zB M h kB yB hyB j p ∈ 𝔑 M I J := by
  rw [mem_blockAlg_iff_comm]
  intro b
  refine Douglas.z_comm _ ?_ ?_ ?_ p
  · exact (mem_blockAlg_iff_comm M _).mp (star (dB M h j)).2 b
  · rw [star_Rt]
    exact (mem_blockAlg_iff_comm M _).mp (star (dB M h j)).2 (star b)
  · intro p'
    exact (mem_blockAlg_iff_comm M _).mp (yopB_mem M kB yB j p') b

/-- The fallback answers. -/
def a₀ : A := Classical.arbitrary A

def b₀ : B := Classical.arbitrary B

include hxA in
/-- Alice's POVM element at `(i, a)`, as an operator. -/
def Aop (i : I) (a : A) : 𝓑 M I J →L[ℂ] 𝓑 M I J :=
  Douglas.povm (fun p : IdxA kA i => p.1) (a₀ (A := A)) (hxeA M h kA xA hxA i) a

include hyB in
/-- Bob's POVM element at `(j, b)`, as an operator. -/
def Bop (j : J) (b : B) : 𝓑 M I J →L[ℂ] 𝓑 M I J :=
  Douglas.povm (fun p : IdxB kB j => p.1) (b₀ (B := B)) (hyeB M h kB yB hyB j) b

include hxA in
theorem ZA_mem (i : I) : Douglas.Z (hxeA M h kA xA hxA i) ∈ 𝔑 M I J :=
  sum_mem fun p _ => mul_mem (star_mem (zA_mem M h kA xA hxA i p)) (zA_mem M h kA xA hxA i p)

include hyB in
theorem ZB_mem (j : J) : Douglas.Z (hyeB M h kB yB hyB j) ∈ 𝔑 M I J :=
  sum_mem fun p _ => mul_mem (star_mem (zB_mem M h kB yB hyB j p)) (zB_mem M h kB yB hyB j p)

include hxA in
theorem Aop_mem (i : I) (a : A) : Aop M h kA xA hxA i a ∈ 𝔑 M I J := by
  unfold Aop Douglas.povm
  refine add_mem (sum_mem fun p _ => ?_) ?_
  · split_ifs
    · exact mul_mem (star_mem (zA_mem M h kA xA hxA i p)) (zA_mem M h kA xA hxA i p)
    · exact zero_mem _
  · split_ifs
    · exact sub_mem (one_mem _) (ZA_mem M h kA xA hxA i)
    · exact zero_mem _

include hyB in
theorem Bop_mem (j : J) (b : B) : Bop M h kB yB hyB j b ∈ 𝔑 M I J := by
  unfold Bop Douglas.povm
  refine add_mem (sum_mem fun p _ => ?_) ?_
  · split_ifs
    · exact mul_mem (star_mem (zB_mem M h kB yB hyB j p)) (zB_mem M h kB yB hyB j p)
    · exact zero_mem _
  · split_ifs
    · exact sub_mem (one_mem _) (ZB_mem M h kB yB hyB j)
    · exact zero_mem _

include hxA in
/-- Alice's POVM element in the block algebra. -/
def Ame (i : I) (a : A) : ↥(𝔑 M I J) := ⟨Aop M h kA xA hxA i a, Aop_mem M h kA xA hxA i a⟩

include hyB in
/-- Bob's POVM element in the block algebra. -/
def Bme (j : J) (b : B) : ↥(𝔑 M I J) := ⟨Bop M h kB yB hyB j b, Bop_mem M h kB yB hyB j b⟩

include hxA in
theorem Ame_sum (i : I) : ∑ a, Ame M h kA xA hxA i a = 1 := by
  apply Subtype.ext
  rw [coe_sum_𝔑]
  exact Douglas.sum_povm _ _ _

include hyB in
theorem Bme_sum (j : J) : ∑ b, Bme M h kB yB hyB j b = 1 := by
  apply Subtype.ext
  rw [coe_sum_𝔑]
  exact Douglas.sum_povm _ _ _

omit h in
/-- Regrouping a labelled sigma sum. -/
theorem sum_sigma_label {k : A → ℕ} (f : ∀ a, Fin (k a) → 𝓑 M I J →L[ℂ] 𝓑 M I J) (a : A) :
    ∑ p : Σ a, Fin (k a), (if p.1 = a then f p.1 p.2 else 0) = ∑ x, f a x := by
  rw [Fintype.sum_sigma]
  have : ∀ a', ∑ x, (if a' = a then f a' x else 0) = if a' = a then ∑ x, f a' x else 0 := by
    intro a'
    split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp

include hxA in
/-- `cᵢ* 𝖠ᵢᵃ cᵢ = E(Fᵢᵃ)` (eq resolver-refinement-identities). -/
theorem star_cA_mul_Ame_mul_cA (i : I) (a : A) :
    star (cA M h i) * Ame M h kA xA hxA i a * cA M h i = Ecor M (Lv M (F i a)) := by
  apply Subtype.ext
  show star (cA M h i).1 * Aop M h kA xA hxA i a * (cA M h i).1 = (Ecor M (Lv M (F i a))).1
  unfold Aop
  rw [Douglas.star_c_mul_povm_mul_c]
  rw [sum_sigma_label M (fun a k => star (xopA M kA xA i ⟨a, k⟩) * xopA M kA xA i ⟨a, k⟩)]
  have e1 : ∑ x : Fin (kA i a), star (xopA M kA xA i ⟨a, x⟩) * xopA M kA xA i ⟨a, x⟩
      = ((∑ x : Fin (kA i a), Ecor M (I := I) (J := J) (Lv M (star (xA i a x) * xA i a x)) :
          ↥(𝔑 M I J)) : 𝓑 M I J →L[ℂ] 𝓑 M I J) := by
    rw [coe_sum_𝔑]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Ecor_Lv_mul, ← star_Ecor_Lv]
    rfl
  rw [e1, ← E_sum, ← Lv_sum, ← hxA]

include hyB in
/-- `dⱼ 𝖡ⱼᵇ dⱼ* = E(Gⱼᵇ)`. -/
theorem dB_mul_Bme_mul_star_dB (j : J) (b : B) :
    dB M h j * Bme M h kB yB hyB j b * star (dB M h j) = Ecor M (Lv M (G j b)) := by
  have e : dB M h j * Bme M h kB yB hyB j b * star (dB M h j)
      = star (star (dB M h j)) * Bme M h kB yB hyB j b * star (dB M h j) := by rw [star_star]
  rw [e]
  apply Subtype.ext
  show star (star (dB M h j)).1 * Bop M h kB yB hyB j b * (star (dB M h j)).1
    = (Ecor M (Lv M (G j b))).1
  unfold Bop
  rw [Douglas.star_c_mul_povm_mul_c]
  rw [sum_sigma_label M (fun b l => star (yopB M kB yB j ⟨b, l⟩) * yopB M kB yB j ⟨b, l⟩)]
  have e1 : ∑ x : Fin (kB j b), star (yopB M kB yB j ⟨b, x⟩) * yopB M kB yB j ⟨b, x⟩
      = ((∑ x : Fin (kB j b), Ecor M (I := I) (J := J) (Lv M (star (yB j b x) * yB j b x)) :
          ↥(𝔑 M I J)) : 𝓑 M I J →L[ℂ] 𝓑 M I J) := by
    rw [coe_sum_𝔑]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Ecor_Lv_mul, ← star_Ecor_Lv]
    rfl
  rw [e1, ← E_sum, ← Lv_sum, ← hyB]

/-! ## Positivity of the lifted POVMs -/

/-- The lift into the arena algebra. -/
abbrev lft : ↥(𝔑 M I J) →⋆ₐ[ℂ] (N M I J).A := Block.lift M (Idx I J)

omit h in
theorem isPosElem_lft_star_mul_self (x : ↥(𝔑 M I J)) : IsPosElem (lft M (star x * x)) := by
  rw [map_mul, map_star]
  exact isPosElem_star_mul_self _

omit h in
theorem isPosElem_lft_zero : IsPosElem (lft M (0 : ↥(𝔑 M I J))) := by
  rw [map_zero]
  exact isPosElem_zero

omit h in
theorem isPosElem_lft_ite {P : Prop} [Decidable P] (x : ↥(𝔑 M I J)) :
    IsPosElem (lft M (if P then star x * x else 0)) := by
  split_ifs
  · exact isPosElem_lft_star_mul_self M x
  · exact isPosElem_lft_zero M

include hxA in
theorem Ame_isPos (i : I) (a : A) : IsPosElem (lft M (Ame M h kA xA hxA i a)) := by
  -- the defect and its square root
  have hZ1 : Douglas.Z (hxeA M h kA xA hxA i) ≤ 1 := Douglas.Z_le_one _
  have hQ0 : (0 : 𝓑 M I J →L[ℂ] 𝓑 M I J) ≤ 1 - Douglas.Z (hxeA M h kA xA hxA i) :=
    sub_nonneg.mpr hZ1
  have hQmem : (1 : 𝓑 M I J →L[ℂ] 𝓑 M I J) - Douglas.Z (hxeA M h kA xA hxA i) ∈ 𝔑 M I J :=
    sub_mem (one_mem _) (ZA_mem M h kA xA hxA i)
  set Q : ↥(𝔑 M I J) := ⟨CFC.sqrt (1 - Douglas.Z (hxeA M h kA xA hxA i)), sqrt_mem M hQ0 hQmem⟩
    with hQ
  have hQsq : star Q * Q = ⟨1 - Douglas.Z (hxeA M h kA xA hxA i), hQmem⟩ := by
    apply Subtype.ext
    have hsa : IsSelfAdjoint (CFC.sqrt (1 - Douglas.Z (hxeA M h kA xA hxA i))) := by
      have h0 : 0 ≤ CFC.sqrt (1 - Douglas.Z (hxeA M h kA xA hxA i)) := CFC.sqrt_nonneg _
      exact IsSelfAdjoint.of_nonneg h0
    show star (CFC.sqrt _) * CFC.sqrt _ = _
    rw [hsa.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ hQ0
  set zz : IdxA kA i → ↥(𝔑 M I J) :=
    fun p => ⟨zA M h kA xA hxA i p, zA_mem M h kA xA hxA i p⟩ with hzz
  have e : Ame M h kA xA hxA i a
      = (∑ p, if p.1 = a then star (zz p) * zz p else 0) + if a = a₀ then star Q * Q else 0 := by
    apply Subtype.ext
    rw [hQsq]
    show Douglas.povm _ _ _ a = _
    unfold Douglas.povm
    rw [AddMemClass.coe_add, coe_sum_𝔑]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> rfl
    · split_ifs <;> rfl
  clear_value zz Q
  rw [e, map_add, map_sum]
  exact IsPosElem.add (isPosElem_sum _ _ fun p _ => isPosElem_lft_ite M _)
    (isPosElem_lft_ite M _)

include hyB in
theorem Bme_isPos (j : J) (b : B) : IsPosElem (lft M (Bme M h kB yB hyB j b)) := by
  have hZ1 : Douglas.Z (hyeB M h kB yB hyB j) ≤ 1 := Douglas.Z_le_one _
  have hQ0 : (0 : 𝓑 M I J →L[ℂ] 𝓑 M I J) ≤ 1 - Douglas.Z (hyeB M h kB yB hyB j) :=
    sub_nonneg.mpr hZ1
  have hQmem : (1 : 𝓑 M I J →L[ℂ] 𝓑 M I J) - Douglas.Z (hyeB M h kB yB hyB j) ∈ 𝔑 M I J :=
    sub_mem (one_mem _) (ZB_mem M h kB yB hyB j)
  set Q : ↥(𝔑 M I J) := ⟨CFC.sqrt (1 - Douglas.Z (hyeB M h kB yB hyB j)), sqrt_mem M hQ0 hQmem⟩
    with hQ
  have hQsq : star Q * Q = ⟨1 - Douglas.Z (hyeB M h kB yB hyB j), hQmem⟩ := by
    apply Subtype.ext
    have hsa : IsSelfAdjoint (CFC.sqrt (1 - Douglas.Z (hyeB M h kB yB hyB j))) := by
      have h0 : 0 ≤ CFC.sqrt (1 - Douglas.Z (hyeB M h kB yB hyB j)) := CFC.sqrt_nonneg _
      exact IsSelfAdjoint.of_nonneg h0
    show star (CFC.sqrt _) * CFC.sqrt _ = _
    rw [hsa.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ hQ0
  set zz : IdxB kB j → ↥(𝔑 M I J) :=
    fun p => ⟨zB M h kB yB hyB j p, zB_mem M h kB yB hyB j p⟩ with hzz
  have e : Bme M h kB yB hyB j b
      = (∑ p, if p.1 = b then star (zz p) * zz p else 0) + if b = b₀ then star Q * Q else 0 := by
    apply Subtype.ext
    rw [hQsq]
    show Douglas.povm _ _ _ b = _
    unfold Douglas.povm
    rw [AddMemClass.coe_add, coe_sum_𝔑]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> rfl
    · split_ifs <;> rfl
  clear_value zz Q
  rw [e, map_add, map_sum]
  exact IsPosElem.add (isPosElem_sum _ _ fun p _ => isPosElem_lft_ite M _)
    (isPosElem_lft_ite M _)

/-! ## The branch and the trace bookkeeping -/

/-- The branch block `cᵢ E(σ) dⱼ`. -/
def Xb (σ : M.A) (i : I) (j : J) : ↥(𝔑 M I J) := cA M h i * Ecor M (Lv M σ) * dB M h j

/-- The branch vector `√d • ι(cᵢ E(σ) dⱼ)`. -/
def branch (σ : M.A) (i : I) (j : J) : (N M I J).H :=
  ((Real.sqrt (d I J) : ℝ) : ℂ) • (N M I J).ι (lft M (Xb M h σ i j))

omit h in
theorem d_pos : (0 : ℝ) < d I J := by exact_mod_cast Fintype.card_pos

omit h in
theorem sqrt_d_sq : ((Real.sqrt (d I J) : ℝ) : ℂ) * ((Real.sqrt (d I J) : ℝ) : ℂ)
    * ((d I J : ℂ))⁻¹ = 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (d_pos (I := I) (J := J)).le,
    Complex.ofReal_natCast]
  exact mul_inv_cancel₀ (by exact_mod_cast (d_pos (I := I) (J := J)).ne')

omit h in
/-- Traciality of the arena trace, conjugation form. -/
theorem τ_conj (D W : ↥(𝔑 M I J)) :
    (N M I J).τ (lft M (star D * W * D)) = (N M I J).τ (lft M (W * (D * star D))) := by
  rw [mul_assoc, map_mul, (N M I J).τ_mul_comm, ← map_mul, mul_assoc]

omit h in
theorem τ_conj' (D W V : ↥(𝔑 M I J)) :
    (N M I J).τ (lft M (star D * W * D * V)) = (N M I J).τ (lft M (W * (D * V * star D))) := by
  rw [show star D * W * D * V = star D * (W * D * V) by simp only [mul_assoc], map_mul,
    (N M I J).τ_mul_comm, ← map_mul]
  congr 2

omit h in
theorem τ_lft_Ecor_Lv (a : M.A) :
    (N M I J).τ (lft M (Ecor M (Lv M a))) = ((d I J : ℂ))⁻¹ * M.τ a := by
  rw [τ_lift_E, Lv_val, M.traceState_L]

theorem star_Xb_mul_Xb (σ : M.A) (i : I) (j : J) :
    star (Xb M h σ i j) * Xb M h σ i j
      = star (dB M h j) * Ecor M (Lv M (star σ * FA M F i * σ)) * dB M h j := by
  have e1 : star (Xb M h σ i j) * Xb M h σ i j
      = star (dB M h j) * (star (Ecor M (Lv M σ)) * (star (cA M h i) * cA M h i)
          * Ecor M (Lv M σ)) * dB M h j := by
    unfold Xb
    rw [star_mul, star_mul]
    noncomm_ring
  rw [e1, star_cA_mul_cA_self, star_Ecor_Lv, Ecor_Lv_mul, Ecor_Lv_mul]

include hxA hyB in
theorem star_Xb_mul_Ame_Xb_Bme (σ : M.A) (i : I) (j : J) (a : A) (b : B) :
    star (Xb M h σ i j) * (Ame M h kA xA hxA i a * Xb M h σ i j * Bme M h kB yB hyB j b)
      = star (dB M h j) * Ecor M (Lv M (star σ * F i a * σ)) * dB M h j
          * Bme M h kB yB hyB j b := by
  have e1 : star (Xb M h σ i j) * (Ame M h kA xA hxA i a * Xb M h σ i j * Bme M h kB yB hyB j b)
      = star (dB M h j) * (star (Ecor M (Lv M σ))
          * (star (cA M h i) * Ame M h kA xA hxA i a * cA M h i) * Ecor M (Lv M σ))
          * dB M h j * Bme M h kB yB hyB j b := by
    unfold Xb
    rw [star_mul, star_mul]
    noncomm_ring
  rw [e1, star_cA_mul_Ame_mul_cA, star_Ecor_Lv, Ecor_Lv_mul, Ecor_Lv_mul]

/-! ## The arena -/

include hxA hyB in
/-- **The entropic resolver arena.** -/
def arena : ResolverArena M F G where
  N := N M I J
  Ameas i a := lft M (Ame M h kA xA hxA i a)
  Bmeas j b := lft M (Bme M h kB yB hyB j b)
  Ameas_pos i a := Ame_isPos M h kA xA hxA i a
  Bmeas_pos j b := Bme_isPos M h kB yB hyB j b
  Ameas_sum i := by rw [← map_sum, Ame_sum, map_one]
  Bmeas_sum j := by rw [← map_sum, Bme_sum, map_one]
  branch σ i j := branch M h σ i j
  branch_norm σ i j := by
    unfold branch
    rw [inner_smul_left, inner_smul_right, StdTracialAlgebra.ι_inner, ← map_star, ← map_mul,
      star_Xb_mul_Xb, τ_conj, dB_mul_star_dB_self, Ecor_Lv_mul, τ_lft_Ecor_Lv, Complex.conj_ofReal,
      ← mul_assoc, ← mul_assoc, sqrt_d_sq, one_mul]
    congr 1
    simp only [mul_assoc]
  branch_answer σ i j a b := by
    unfold branch
    rw [inner_smul_left, map_smul, map_smul, inner_smul_right, StdTracialAlgebra.inner_L_R,
      ← map_star, ← map_mul, ← map_mul, ← map_mul, star_Xb_mul_Ame_Xb_Bme, τ_conj',
      dB_mul_Bme_mul_star_dB, Ecor_Lv_mul, τ_lft_Ecor_Lv, Complex.conj_ofReal,
      ← mul_assoc, ← mul_assoc, sqrt_d_sq, one_mul]
    congr 1
    simp only [mul_assoc]

end

end EntropicArena

end CommutingRepetition
