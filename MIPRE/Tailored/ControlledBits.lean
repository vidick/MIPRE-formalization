/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Bits
public import MIPRE.Tailored.Intro.Input
public import Mathlib.Data.List.GetD
public import MIPRE.Tactics

@[expose] public section

/-!
# Bits controlled by readable data

The honest strategy of the answer-reduced game (slice P4d of `planning/aldous-lyons-track.md`)
data-processes a Z-aligned permutation strategy along maps that are `F₂`-affine in the linear
answer bits, with coefficients read off the readable ones (cor:encodings, II:1150): the oracle's
linear codewords are affine in the isolated players' linear answers, with coefficients read off
their readable answers. This file supplies the closure lemmas for such bits.

* `isSignedPerm_controlledSum`: a sum `∑_k E_k W_k` over a diagonal projective measurement `E`,
  each `W_k` a signed permutation commuting with `E`, is a signed permutation. On the basis
  vectors of outcome `k` it acts as `W_k`, which keeps them there.
* `isXBit_controlledBy`: the bit `g_{ρ(a)}(a)`, controlled by a function `ρ` of the outcome whose
  coarse-graining is diagonal, is a signed permutation when each `g_k` is.
* `isZBit_comp_of_isDiag`: a function of such a `ρ` is a Z-bit.
* `isDiag_coarse_of_isZBit`: the coarse-graining along the bits of the outcome below a readable
  length is diagonal when those bits are Z-bits, which is how `ρ` arises.
* `isXBit_affine`: an `F₂`-affine function of X-bits is an X-bit, and
  `isXBit_of_controlledAffine`, `isZBit_of_readable` put the pieces together: a bit that is a
  function of Z-bits is a Z-bit, and a bit that is, for each value of the Z-bits, an affine
  function of X-bits is an X-bit.
* `PermStrategy.toSync_bit`: the answer bits of the synchronous strategy of a permutation
  strategy (`lem:zpc-pcc`) are X-bits, and Z-bits below the readable length.
-/

namespace MIPRE.Tailored

open Finset Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Diagonal projective measurements -/

section Diagonal

variable {K : Type*} [Fintype K] {E : K → Matrix Ω Ω ℂ}

theorem diag_mem_zero_one (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag) (k : K) (i : Ω) :
    E k i i = 0 ∨ E k i i = 1 := by
  have h := congrFun (congrFun (hE.idem k) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hd k hl.symm, zero_mul])
    (fun h => absurd (mem_univ i) h)] at h
  rcases mul_eq_zero.mp (show E k i i * (E k i i - 1) = 0 by linear_combination h) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (sub_eq_zero.mp h1)

theorem diag_sum_eq_one (hE : IsPVMIn E) (i : Ω) : ∑ k, E k i i = 1 := by
  have h := congrFun (congrFun hE.sum_eq_one i) i
  rwa [Matrix.sum_apply, Matrix.one_apply_eq] at h

theorem diag_mul_diag_eq_zero (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag) {j k : K} (hjk : j ≠ k)
    (i : Ω) : E j i i * E k i i = 0 := by
  have h := congrFun (congrFun (hE.orthogonal hjk) i) i
  rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hd j hl.symm, zero_mul])
    (fun h => absurd (mem_univ i) h), Matrix.zero_apply] at h

/-- **A diagonal projective measurement puts each basis vector in exactly one outcome.** -/
theorem existsUnique_diag_eq_one (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag) (i : Ω) :
    ∃! k, E k i i = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, E k i i = 1 := by
    by_contra hne
    push Not at hne
    have h0 : ∀ k, E k i i = 0 := fun k =>
      (diag_mem_zero_one hE hd k i).resolve_right (hne k)
    have := diag_sum_eq_one hE i
    simp [h0] at this
  refine ⟨k, hk, fun j hj => ?_⟩
  by_contra hjk
  have := diag_mul_diag_eq_zero hE hd hjk i
  rw [hj, hk, one_mul] at this
  exact one_ne_zero this

/-- The outcome of a basis vector. -/
noncomputable def diagOutcome (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag) (i : Ω) : K :=
  (existsUnique_diag_eq_one hE hd i).exists.choose

theorem diag_diagOutcome (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag) (i : Ω) :
    E (diagOutcome hE hd i) i i = 1 :=
  (existsUnique_diag_eq_one hE hd i).exists.choose_spec

theorem diag_eq_ite [DecidableEq K] (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag) (k : K) (i : Ω) :
    E k i i = if k = diagOutcome hE hd i then 1 else 0 := by
  split_ifs with h
  · rw [h, diag_diagOutcome hE hd]
  · refine (diag_mem_zero_one hE hd k i).resolve_right fun h1 => h ?_
    exact (existsUnique_diag_eq_one hE hd i).unique h1 (diag_diagOutcome hE hd i)

/-- **A signed permutation commuting with a diagonal projective measurement keeps the outcome
of every basis vector.** -/
theorem diagOutcome_perm (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag) (σ : Equiv.Perm Ω)
    (s : Ω → Bool) (hc : ∀ j, E j * signedPermMatrix σ s = signedPermMatrix σ s * E j) (l : Ω) :
    diagOutcome hE hd (σ l) = diagOutcome hE hd l := by
  have key : ∀ j, E j (σ l) (σ l) = E j l l := by
    intro j
    have h := congrFun (congrFun (hc j) (σ l)) l
    rw [Matrix.mul_apply, Matrix.mul_apply,
      Finset.sum_eq_single (σ l) (fun m _ hm => by rw [hd j (Ne.symm hm), zero_mul])
        (fun h => absurd (mem_univ _) h),
      Finset.sum_eq_single l (fun m _ hm => by rw [hd j hm, mul_zero])
        (fun h => absurd (mem_univ _) h)] at h
    have hne : signedPermMatrix σ s (σ l) l ≠ 0 := by
      simp only [signedPermMatrix, ite_true]
      cases s l <;> simp [bitSign]
    exact mul_right_cancel₀ hne (by rw [h, mul_comm])
  apply (existsUnique_diag_eq_one hE hd l).unique
  · rw [← key]
    exact diag_diagOutcome hE hd (σ l)
  · exact diag_diagOutcome hE hd l

/-- **A controlled signed permutation**: `∑_k E_k W_k`, over a diagonal projective measurement
`E` and signed permutations `W_k` commuting with it, is a signed permutation. -/
theorem isSignedPerm_controlledSum (hE : IsPVMIn E) (hd : ∀ k, (E k).IsDiag)
    (W : K → Matrix Ω Ω ℂ) (hW : ∀ k, IsSignedPerm (W k))
    (hc : ∀ j k, E j * W k = W k * E j) : IsSignedPerm (∑ k, E k * W k) := by
  classical
  choose σ s hσ using hW
  set κ := diagOutcome hE hd with hκ
  have hperm : ∀ k l, κ (σ k l) = κ l := fun k l =>
    diagOutcome_perm hE hd (σ k) (s k) (fun j => by rw [← hσ k]; exact hc j k) l
  -- the permutation: on a basis vector of outcome `k`, the permutation of `W_k`
  have hinj : Function.Injective fun l => σ (κ l) l := by
    intro l l' h
    have hk : κ l = κ l' := by
      have h1 := hperm (κ l) l
      have h2 := hperm (κ l') l'
      dsimp only at h
      rw [h] at h1
      exact h1.symm.trans h2
    dsimp only at h
    rw [hk] at h
    exact (σ (κ l')).injective h
  let τ : Equiv.Perm Ω := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  refine ⟨τ, fun l => s (κ l) l, ?_⟩
  ext i l
  rw [Matrix.sum_apply]
  have hsum : ∑ k, (E k * W k) i l = W (κ i) i l := by
    rw [Finset.sum_eq_single (κ i)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i (fun m _ hm => by rw [hd _ (Ne.symm hm),
        zero_mul]) (fun h => absurd (mem_univ i) h), diag_diagOutcome hE hd, one_mul]
    · intro k _ hk
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun m _ hm => by rw [hd _ (Ne.symm hm),
        zero_mul]) (fun h => absurd (mem_univ i) h), diag_eq_ite hE hd, ite_eq_right hk,
        zero_mul]
    · exact fun h => absurd (mem_univ _) h
  rw [hsum, hσ]
  simp only [signedPermMatrix, τ, Equiv.ofBijective_apply]
  by_cases h : σ (κ l) l = i
  · have hk : κ i = κ l := by rw [← h]; exact hperm _ l
    rw [hk]
  · rw [ite_eq_right h]
    refine ite_eq_right fun h' => h ?_
    have hk : κ i = κ l := by
      have := hperm (κ i) l
      rwa [h'] at this
    rw [← hk]
    exact h'

end Diagonal

/-! ## Controlled bits -/

section Bits

omit [Fintype Ω] [DecidableEq Ω] in
/-- A sum of diagonal matrices is diagonal. -/
theorem isDiag_finsetSum {ι : Type*} (s : Finset ι) {A : ι → Matrix Ω Ω ℂ}
    (h : ∀ i, (A i).IsDiag) : (∑ i ∈ s, A i).IsDiag := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a).add ih

variable {Λ : Type*} [Fintype Λ] {K : Type*} [Fintype K] [DecidableEq K]
  {P : Λ → Matrix Ω Ω ℂ}

/-- The coarse-graining of `P` along `ρ`. -/
noncomputable def coarseAlong (P : Λ → Matrix Ω Ω ℂ) (ρ : Λ → K) (k : K) : Matrix Ω Ω ℂ :=
  ∑ a ∈ univ.filter fun a => ρ a = k, P a

omit [Fintype K] in
theorem coarseAlong_mul_bitObs (hP : IsPVMIn P) (ρ : Λ → K) (k : K) (g : Λ → Bool) :
    coarseAlong P ρ k * bitObs P g = ∑ a ∈ univ.filter fun a => ρ a = k, bitSign (g a) • P a := by
  classical
  rw [coarseAlong, bitObs, pvmObs, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single a]
  · rw [Matrix.mul_smul, hP.idem]
  · intro b _ hb
    rw [Matrix.mul_smul, hP.orthogonal (Ne.symm hb), smul_zero]
  · exact fun h => absurd (mem_univ a) h

/-- **A bit observable controlled by `ρ`** is the controlled sum of the bit observables. -/
theorem bitObs_controlled (hP : IsPVMIn P) (ρ : Λ → K) (g : K → Λ → Bool) :
    bitObs P (fun a => g (ρ a) a) = ∑ k, coarseAlong P ρ k * bitObs P (g k) := by
  classical
  simp_rw [coarseAlong_mul_bitObs hP ρ]
  rw [bitObs, pvmObs, ← Finset.sum_fiberwise (s := univ) (g := ρ)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

omit [Fintype K] in
theorem commute_coarseAlong_bitObs (hP : IsPVMIn P) (ρ : Λ → K) (k : K) (g : Λ → Bool) :
    coarseAlong P ρ k * bitObs P g = bitObs P g * coarseAlong P ρ k := by
  classical
  rw [coarseAlong, sum_filter_eq_pvmObs, bitObs, hP.pvmObs_mul, hP.pvmObs_mul]
  congr 1
  funext a
  exact mul_comm _ _

/-- **A bit controlled by readable data**: if the coarse-graining of `P` along `ρ` is diagonal,
the bit `g_{ρ(a)}(a)` is a signed permutation when each `g_k` is. -/
theorem isXBit_controlledBy (hP : IsPVMIn P) (ρ : Λ → K) (hd : ∀ k, (coarseAlong P ρ k).IsDiag)
    (g : K → Λ → Bool) (hg : ∀ k, IsXBit P (g k)) : IsXBit P fun a => g (ρ a) a := by
  classical
  unfold IsXBit
  rw [bitObs_controlled hP ρ g]
  refine isSignedPerm_controlledSum (hP.coarse ρ) hd _ hg fun j k => ?_
  exact commute_coarseAlong_bitObs hP ρ j (g k)

/-- **A function of readable data is a Z-bit.** -/
theorem isZBit_comp_of_isDiag (hP : IsPVMIn P) (ρ : Λ → K) (hd : ∀ k, (coarseAlong P ρ k).IsDiag)
    (f : K → Bool) : IsZBit P (f ∘ ρ) := by
  classical
  have e : bitObs P (f ∘ ρ) = ∑ k, coarseAlong P ρ k * (bitSign (f k) • (1 : Matrix Ω Ω ℂ)) := by
    have := bitObs_controlled hP ρ (fun k _ => f k)
    rw [show (fun a => (fun k (_ : Λ) => f k) (ρ a) a) = f ∘ ρ from rfl] at this
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [bitObs_const hP]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact isSignedPerm_controlledSum (hP.coarse ρ) hd _
      (fun k => isSignedPerm_bitSign_smul_one _) fun j k => by
        rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  · rw [e]
    exact isDiag_finsetSum univ fun k => isDiag_mul (hd k) (isDiag_bitSign_smul_one _)

/-- **Readable bits give a diagonal coarse-graining**: if the bits of the outcome below `r` are
Z-bits, the coarse-graining along those bits is diagonal. -/
theorem isDiag_coarse_of_isZBit (hP : IsPVMIn P) {r : ℕ} (bits : Λ → Fin r → Bool)
    (hZ : ∀ i, IsZBit P fun a => bits a i) (v : Fin r → Bool) :
    (coarseAlong P bits v).IsDiag := by
  rw [coarseAlong, ← fourierProj_encObs hP bits v]
  exact isDiag_fourierProj (fun i => (hZ i).2) v

end Bits

/-! ## Affine bits -/

section Affine

open MIPRE.LowDegree (ofBool)

/-- An `F₂`-affine function on `F₂^ι`: `h (u + v) + h 0 = h u + h v`. -/
def IsAffine2 {ι : Type*} (h : (ι → ZMod 2) → ZMod 2) : Prop :=
  ∀ u v, h (u + v) + h 0 = h u + h v

theorem two_eq_zero_zmod2 (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

/-- **An affine function is its value at `0` plus a linear form.** -/
theorem IsAffine2.eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {h : (ι → ZMod 2) → ZMod 2}
    (hh : IsAffine2 h) (v : ι → ZMod 2) : h v = h 0 + ∑ m, (h (Pi.single m 1) + h 0) * v m := by
  let h' : (ι → ZMod 2) →+ ZMod 2 :=
    { toFun := fun v => h v + h 0
      map_zero' := two_eq_zero_zmod2 _
      map_add' := fun u w => by
        have := hh u w
        linear_combination this - two_eq_zero_zmod2 (h 0) }
  have hv : v = ∑ m, v m • (Pi.single m 1 : ι → ZMod 2) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have key : h' v = ∑ m, (h (Pi.single m 1) + h 0) * v m := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    show h (v m • Pi.single m 1) + h 0 = _
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (v m) with hc | hc
    · rw [hc, zero_smul, mul_zero, two_eq_zero_zmod2]
    · rw [hc, one_smul, mul_one]
  have : h v + h 0 = ∑ m, (h (Pi.single m 1) + h 0) * v m := key
  linear_combination this - two_eq_zero_zmod2 (h 0)

theorem decide_add_eq_one (x y : ZMod 2) :
    decide (x + y = 1) = xor (decide (x = 1)) (decide (y = 1)) := by
  fin_cases x <;> fin_cases y <;> rfl

theorem decide_mul_ofBool_eq_one (c : ZMod 2) (b : Bool) :
    decide (c * ofBool b = 1) = (decide (c = 1) && b) := by
  fin_cases c <;> cases b <;> rfl

variable {Λ : Type*} [Fintype Λ] {P : Λ → Matrix Ω Ω ℂ}

/-- **An `F₂`-affine function of X-bits is an X-bit.** -/
theorem isXBit_affine (hP : IsPVMIn P) {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : Λ → ι → Bool)
    (hν : ∀ m, IsXBit P fun a => ν a m) {h : (ι → ZMod 2) → ZMod 2} (hh : IsAffine2 h) :
    IsXBit P fun a => decide (h (fun m => ofBool (ν a m)) = 1) := by
  classical
  have key : ∀ (S : Finset ι) (c : ι → ZMod 2) (c0 : ZMod 2),
      IsXBit P fun a => decide (c0 + ∑ m ∈ S, c m * ofBool (ν a m) = 1) := by
    intro S c c0
    induction S using Finset.induction_on with
    | empty => simpa using (isZBit_const hP (decide (c0 = 1))).isXBit
    | insert m S hm ih =>
      have e : (fun a => decide (c0 + ∑ m' ∈ insert m S, c m' * ofBool (ν a m') = 1)) =
          fun a => xor (decide (c0 + ∑ m' ∈ S, c m' * ofBool (ν a m') = 1))
            (decide (c m = 1) && ν a m) := by
        funext a
        rw [Finset.sum_insert hm, ← decide_mul_ofBool_eq_one, ← decide_add_eq_one,
          add_comm (c m * _), add_assoc]
      rw [e]
      refine ih.xor hP ?_
      by_cases hc : c m = 1
      · simpa [hc] using hν m
      · simpa [hc] using (isZBit_const hP false).isXBit
  have e : (fun a => decide (h (fun m => ofBool (ν a m)) = 1)) = fun a =>
      decide (h 0 + ∑ m ∈ Finset.univ, (h (Pi.single m 1) + h 0) * ofBool (ν a m) = 1) := by
    funext a
    rw [hh.eq_sum]
  rw [e]
  exact key _ _ _

/-- **A bit that is, for each value of some Z-bits, an affine function of X-bits is an
X-bit.** -/
theorem isXBit_of_controlledAffine (hP : IsPVMIn P) {R : ℕ} (ρ : Λ → Fin R → Bool)
    (hρ : ∀ i, IsZBit P fun a => ρ a i) {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : Λ → ι → Bool)
    (hν : ∀ m, IsXBit P fun a => ν a m) (h : (Fin R → Bool) → (ι → ZMod 2) → ZMod 2)
    (hh : ∀ k, IsAffine2 (h k)) (f : Λ → Bool)
    (hf : ∀ a, P a ≠ 0 → ofBool (f a) = h (ρ a) (fun m => ofBool (ν a m))) :
    IsXBit P f :=
  (isXBit_controlledBy hP ρ (isDiag_coarse_of_isZBit hP ρ hρ)
    (fun k a => decide (h k (fun m => ofBool (ν a m)) = 1))
    (fun k => isXBit_affine hP ν hν (hh k))).congr fun a ha => by
      rw [← hf a ha]
      cases f a <;> rfl

/-- **A bit that is a function of some Z-bits is a Z-bit.** -/
theorem isZBit_of_readable (hP : IsPVMIn P) {R : ℕ} (ρ : Λ → Fin R → Bool)
    (hρ : ∀ i, IsZBit P fun a => ρ a i) (φ : (Fin R → Bool) → Bool) (f : Λ → Bool)
    (hf : ∀ a, P a ≠ 0 → f a = φ (ρ a)) : IsZBit P f :=
  (isZBit_comp_of_isDiag hP ρ (isDiag_coarse_of_isZBit hP ρ hρ) φ).congr fun a ha =>
    (hf a ha).symm

end Affine

/-! ## The answer bits of the synchronous strategy of a permutation strategy -/

namespace PermStrategy

variable {X : Type*} [Fintype X] {G : TailoredGame X} (S : PermStrategy G.doubled)

/-- **The synchronous strategy charges only answers of the game's lengths.** -/
theorem toSync_len (p : Bool × X) (a : Verifier.Answers G.maxLen) (ha : S.toSync.P.M p a ≠ 0) :
    a.1.length = G.len p.2 := by
  change S.ansProj G.maxLen p a ≠ 0 at ha
  unfold ansProj at ha
  split_ifs at ha with hl
  · exact hl
  · exact absurd rfl ha

/-- **The answer bits of the synchronous strategy are X-bits, and Z-bits below the readable
length.** -/
theorem toSync_bit (p : Bool × X) (j : ℕ) :
    IsXBit (S.toSync.P.M p) (fun a => a.1.getD j false) ∧
      (j < G.lenR p.2 → IsZBit (S.toSync.P.M p) (fun a => a.1.getD j false)) := by
  have hle := G.len_le_maxLen p.2
  have e : bitObs (S.toSync.P.M p) (fun a => a.1.getD j false) =
      encObs (S.ansProj G.maxLen p) (fun a (_ : Fin 1) => a.1.getD j false) 0 := rfl
  unfold IsXBit IsZBit
  rw [e]
  by_cases hj : j < G.doubled.len p
  · rw [S.encObs_ansProj_bit p hle _ 0 ⟨j, hj⟩ fun v => by
      simp [ofVec, List.getD_eq_getElem?_getD, hj]]
    exact ⟨S.signedPerm p _, fun h => ⟨S.signedPerm p _, S.zAligned p _ h⟩⟩
  · rw [S.encObs_ansProj_const p hle _ 0 false fun v =>
      List.getD_eq_default _ _ (by simp [ofVec]; omega)]
    exact ⟨isSignedPerm_bitSign_smul_one _, fun _ =>
      ⟨isSignedPerm_bitSign_smul_one _, isDiag_bitSign_smul_one _⟩⟩

end PermStrategy

end MIPRE.Tailored

end
