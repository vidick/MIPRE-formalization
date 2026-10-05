/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.Strategy
public import MIPRE.Tailored.Verifier
public import MIPRE.Foundations.Repeat.RepSampler
public import MIPRE.Foundations.GameTransport
public import MIPRE.Foundations.GameAdapt
public import MIPRE.Tactics

@[expose] public section

/-!
# Repeated tailored verifiers, from the specification of their programs

Paper II, `thm:repetition` (II:11103), at the level of tailored verifiers, in the direct form of
the plan (`planning/aldous-lyons-track.md`, Phase 2). The repeated verifier `repTV V λ τ L P`
has the repeated sampler of the existing pipeline (`MIPRE.Repeat.repSampler`, `k(n)` independent
copies of `V`'s sampler) and two programs `L`, `P` for the answer-length calculator and the
linear-constraints processor. This file proves completeness, and the comparison of its games
with the input's that soundness rests on, from a *specification* of `L` and `P` at the index
`n` (`RepSpec`), which the programs of `MIPRE.Background.Tailored.Repetition` meet:

* at a question all of whose coordinates have their lengths defined, `L` outputs the sums of the
  coordinates' lengths, and it halts at no other question;
* at two such questions, with readable answers of the right lengths, `P` halts exactly when the
  input's processor halts on every coordinate, and then outputs the constraints of the
  tailored product `(V.tgame n).repeat k` (`MIPRE.Tailored.TailoredGame.repeat`).

The results:

* `RepSpec.accepts_of_accepts`: whatever the repeated verifier's game accepts at `(x, y)`, the
  tailored product accepts at the tuples of coordinates; and conversely at questions whose
  coordinates all have their lengths (`RepSpec.accepts_iff`);
* `RepSpec.hasPerfectZPC`: **completeness**, a perfect ZPC strategy for `𝒱_n` gives one for
  `𝒱^rep_n`, the tensor power of `MIPRE.Tailored.Repeat.Strategy` pulled back along the blocks
  of the questions — the questions on an edge have all their lengths, because a perfect strategy
  is accepted somewhere on every edge (`PermStrategy.exists_accepts`);
* `quantumValue_le_of_coarse`, on `ProjectiveMeasurement.mergeAt` of
  `MIPRE.Foundations.GameAdapt` at the identity map of questions: a game whose accepted answers, read through a map of the answers
  that may depend on the question, are accepted by a second game on equivalent questions, has
  at most its value. Soundness (`MIPRE.Background.Tailored.Repetition`) applies it to the
  repeated verifier's game and the direct repetition of `𝒱_n`.
-/

namespace MIPRE

open Finset

/-! ## Coarse-graining along a map of the answers that depends on the question -/


section Coarse

open Matrix Kronecker

variable {X Y A A' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype A'] [DecidableEq A']

/-- **Merging the answers of a strategy at each question can only raise its value**, when every
accepted tuple of the first game is accepted after merging. -/
theorem TensorProductStrategy.value_le_mergeAt {G : Game X X A A} (S : TensorProductStrategy G)
    (H : Game X X A' A') (r : X → A → A') (hμ : ∀ x y, H.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → H.D x y (r x a) (r y b) = true) :
    S.value ≤ (⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.mergeAt id r,
      S.PB.mergeAt id r⟩ : TensorProductStrategy H).value := by
  unfold TensorProductStrategy.value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  set w : A → A → ℝ :=
    fun a b => (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re with hw
  have hw0 : ∀ a b, 0 ≤ w a b := fun a b => S.re_dotProduct_nonneg x y a b
  have hbil : ∀ a' b', (star S.ψ ⬝ᵥ (((S.PA.mergeAt id r).M x a' ⊗ₖ
      (S.PB.mergeAt id r).M y b') *ᵥ S.ψ)).re =
        ∑ a ∈ Finset.univ.filter (fun a => r x a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => r y b = b'), w a b := by
    intro a' b'
    have hsplit : (S.PA.mergeAt id r).M x a' ⊗ₖ
        (S.PB.mergeAt id r).M y b' =
          ∑ a ∈ Finset.univ.filter (fun a => r x a = a'),
            ∑ b ∈ Finset.univ.filter (fun b => r y b = b'), S.PA.M x a ⊗ₖ S.PB.M y b := by
      ext p q
      simp only [ProjectiveMeasurement.mergeAt_M, id, Matrix.sum_apply, kroneckerMap_apply,
        Finset.sum_mul_sum]
    rw [hsplit, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  show ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * w a b ≤
    ∑ a', ∑ b', H.μ x y * (if H.D x y a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ (((S.PA.mergeAt id r).M x a' ⊗ₖ
        (S.PB.mergeAt id r).M y b') *ᵥ S.ψ)).re
  simp_rw [hbil]
  calc ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) * w a b
      ≤ ∑ a, ∑ b, H.μ x y * (if H.D x y (r x a) (r y b) then 1 else 0) * w a b := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [hμ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
          (hw0 a b)
        cases h : G.D x y a b with
        | false => by_cases h' : H.D x y (r x a) (r y b) = true <;> simp [h']
        | true => rw [hD x y a b h]
    _ = ∑ a', ∑ a ∈ Finset.univ.filter (fun a => r x a = a'), ∑ b',
          ∑ b ∈ Finset.univ.filter (fun b => r y b = b'),
            H.μ x y * (if H.D x y (r x a) (r y b) then 1 else 0) * w a b := by
        rw [Finset.sum_fiberwise Finset.univ (r x)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_fiberwise Finset.univ (r y)]
    _ = ∑ a', ∑ a ∈ Finset.univ.filter (fun a => r x a = a'), ∑ b',
          ∑ b ∈ Finset.univ.filter (fun b => r y b = b'),
            H.μ x y * (if H.D x y a' b' then 1 else 0) * w a b := by
        refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a ha =>
          Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b hb => ?_
        rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
    _ = ∑ a', ∑ b', H.μ x y * (if H.D x y a' b' then 1 else 0) *
          ∑ a ∈ Finset.univ.filter (fun a => r x a = a'),
            ∑ b ∈ Finset.univ.filter (fun b => r y b = b'), w a b := by
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- **Coarse-graining with a relabeling of the questions**: if every tuple `G` accepts at
`(x, y)` is accepted by `H` at `(e x, e y)` after reading the answers through `r x`, `r y`,
on matching distributions, then `val*(G) ≤ val*(H)`. -/
theorem quantumValue_le_of_coarse (G : Game X X A A) (H : Game Y Y A' A') (e : X ≃ Y)
    (r : X → A → A') (hμ : ∀ x y, G.μ x y = H.μ (e x) (e y))
    (hD : ∀ x y a b, G.D x y a b = true → H.D (e x) (e y) (r x a) (r y b) = true) :
    quantumValue G ≤ quantumValue H := by
  -- `H`, read on the questions of `G`
  let H₀ : Game X X A' A' :=
    { μ := fun x y => H.μ (e x) (e y)
      μ_nonneg := fun x y => H.μ_nonneg _ _
      μ_sum_one := by
        rw [← H.μ_sum_one]
        exact Fintype.sum_equiv e _ _ fun x => Fintype.sum_equiv e _ _ fun y => rfl
      D := fun x y => H.D (e x) (e y) }
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  let S₀ : TensorProductStrategy H₀ := ⟨S.dA, S.dB, S.ψ, S.ψ_unit,
    S.PA.mergeAt id r, S.PB.mergeAt id r⟩
  have h₁ : S.value ≤ S₀.value :=
    S.value_le_mergeAt H₀ r (fun x y => (hμ x y).symm) hD
  have h₂ : (S₀.relabel H e.symm e.symm (Equiv.refl _) (Equiv.refl _)).value = S₀.value :=
    S₀.value_relabel H e.symm e.symm (Equiv.refl _) (Equiv.refl _)
      (fun x y => by simp [H₀]) (fun x y a b => by simp [H₀])
  exact h₁.trans (h₂ ▸ le_ciSup (TensorProductStrategy.bddAbove_range_value H) _)

end Coarse

end MIPRE

namespace MIPRE.Tailored

open Cost CL Finset

/-! ## Perfect strategies are accepted on every edge -/

namespace PermStrategy

variable {X : Type*} [Fintype X] {G : TailoredGame X} (S : PermStrategy G)

/-- **A perfect permutation strategy is accepted on every edge**: some pair of answers is. -/
theorem exists_accepts (hS : S.value = 1) {x y : X} (hxy : 0 < G.μ x y) :
    ∃ a b, G.Accepts x y a b := by
  by_contra hne
  push Not at hne
  have h0 : ∀ a b, S.proj x a * S.proj y b = 0 := fun a b =>
    S.proj_mul_eq_zero_of_value_eq_one hS hxy (hne _ _)
  have h1 : ∑ a, ∑ b, S.proj x a * S.proj y b = 1 := by
    simp_rw [← Finset.mul_sum, S.sum_proj y, mul_one]
    exact S.sum_proj x
  simp only [h0, Finset.sum_const_zero] at h1
  have : (1 : Matrix (Fin S.m) (Fin S.m) ℂ) ⟨0, S.m_pos⟩ ⟨0, S.m_pos⟩ = 0 := by
    rw [← h1]; rfl
  simp at this

end PermStrategy

namespace TailoredGame

variable {X : Type*} [Fintype X] {G : TailoredGame X}

/-- A game with a perfect ZPC strategy is accepted on every edge. -/
theorem HasPerfectZPC.exists_accepts (h : G.HasPerfectZPC) {x y : X} (hxy : 0 < G.μ x y) :
    ∃ a b, G.Accepts x y a b := by
  obtain ⟨S, hS⟩ := h
  exact S.exists_accepts hS hxy

/-- A constraint list containing a rejecting constraint accepts nothing. -/
theorem not_accepts_of_reject_mem {x y : X} {a b : BitStr} {d : ℕ}
    (h : rejectConstraint d ∈ G.cons x y (a.take (G.lenR x)) (b.take (G.lenR y))) :
    ¬G.Accepts x y a b := fun hacc =>
  not_satisfies_rejectConstraint d (a ++ b) (hacc.2.2 _ h)

end TailoredGame

/-! ## Repeated tailored verifiers -/

namespace TailoredVerifier

variable {ℓ : ℕ} (V : TailoredVerifier ℓ) (lam tau : ℕ)

/-- The number of repetitions at index `n`. -/
abbrev K (n : ℕ) : ℕ := Repetition.reps lam tau n

/-- The questions of the repeated verifier are tuples of questions of `V`. -/
noncomputable abbrev qEquiv (n : ℕ) :
    (Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) ≃ (Fin (K lam tau n) → V.Questions n) :=
  blockEquiv (finProdFinEquiv (m := K lam tau n) (n := V.sampler.dim n))

/-- The `i`-th coordinate of a question of the repeated verifier. -/
noncomputable abbrev qc (n : ℕ) (x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) (i : Fin (K lam tau n)) :
    V.Questions n := qEquiv V lam tau n x i

/-- The repeated tailored verifier: the repeated sampler, and the programs `L`, `P`. -/
noncomputable def repTV (L P : Decider) : TailoredVerifier ℓ :=
  ⟨Repeat.repSampler V.sampler lam tau, L, P⟩

/-- **The specification of the repeated programs at index `n`.** Write `x⃗ = qEquiv x` for the
tuple of coordinates of a question `x`, and call `x` *good* when every coordinate has its
lengths (`V.LenDefined`). -/
structure RepSpec (L P : Decider) (n : ℕ) : Prop where
  /-- At a good question, `L` outputs the sums of the coordinates' lengths. -/
  len_eq : ∀ x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂,
    (∀ i, V.LenDefined n (toBits (qc V lam tau n x i))) → ∀ κ,
      LenIs L n (toBits x) κ (∑ i, V.lenOf n (toBits (qc V lam tau n x i)) κ)
  /-- `L` halts at good questions only. -/
  good_of_len : ∀ (x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) κ m,
    LenIs L n (toBits x) κ m → ∀ i, V.LenDefined n (toBits (qc V lam tau n x i))
  /-- At good questions and readable answers of the right lengths, `P` halts exactly when the
  input's processor halts on every coordinate, and then outputs the product's constraints. -/
  lp_iff : ∀ (x y : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) (aR bR : BitStr),
    (∀ i, V.LenDefined n (toBits (qc V lam tau n x i))) →
    (∀ i, V.LenDefined n (toBits (qc V lam tau n y i))) →
    aR.length = (V.tgame n).lenRSum (qEquiv V lam tau n x) →
    bR.length = (V.tgame n).lenRSum (qEquiv V lam tau n y) → ∀ cs,
      (LpIs P n (toBits x) (toBits y) aR bR cs ↔
        (∀ i, ∃ c, LpIs V.lp n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
          ((V.tgame n).coordR (qEquiv V lam tau n x) aR i)
          ((V.tgame n).coordR (qEquiv V lam tau n y) bR i) c) ∧
        cs = ((V.tgame n).repeat (K lam tau n)).cons (qEquiv V lam tau n x)
          (qEquiv V lam tau n y) aR bR)

variable {V lam tau} {L P : Decider} {n : ℕ}

/-- The distribution of the repeated verifier's game is the product's. -/
theorem repTV_μ (x y : (repTV V lam tau L P).Questions n) :
    ((repTV V lam tau L P).tgame n).μ x y =
      ((V.tgame n).repeat (K lam tau n)).μ (qEquiv V lam tau n x) (qEquiv V lam tau n y) :=
  clDist_famSum finProdFinEquiv _ _ x y

namespace RepSpec

variable (h : RepSpec V lam tau L P n)
include h

/-- At a good question, the repeated verifier's lengths are the product's. -/
theorem lenOf_eq {x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂}
    (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i))) (κ : Bool) :
    (repTV V lam tau L P).lenOf n (toBits x) κ =
      ∑ i, V.lenOf n (toBits (qc V lam tau n x i)) κ := by
  have hL := h.len_eq x hx κ
  have hex : ∃ m, LenIs (repTV V lam tau L P).len n (toBits x) κ m := ⟨_, hL⟩
  rw [lenOf, dite_eq_left hex]
  exact hex.choose_spec.unique hL

theorem lenDefined {x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂}
    (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i))) :
    (repTV V lam tau L P).LenDefined n (toBits x) := fun κ => ⟨_, h.len_eq x hx κ⟩

/-- At a good question, the repeated verifier's game has the product's lengths. -/
theorem sameLens {x : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂}
    (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i))) :
    ((repTV V lam tau L P).tgame n).lenR x =
        ((V.tgame n).repeat (K lam tau n)).lenR (qEquiv V lam tau n x) ∧
      ((repTV V lam tau L P).tgame n).lenL x =
        ((V.tgame n).repeat (K lam tau n)).lenL (qEquiv V lam tau n x) :=
  ⟨h.lenOf_eq hx false, h.lenOf_eq hx true⟩

omit h in
/-- Every coordinate of an accepted question pair of the product has its lengths. -/
theorem good_of_repeat_accepts {x y : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂} {a b : BitStr}
    (hacc : ((V.tgame n).repeat (K lam tau n)).Accepts (qEquiv V lam tau n x)
      (qEquiv V lam tau n y) a b) (i : Fin (K lam tau n)) :
    V.LenDefined n (toBits (qc V lam tau n x i)) ∧ V.LenDefined n (toBits (qc V lam tau n y i)) := by
  obtain ⟨-, -, hall⟩ := ((V.tgame n).repeat_accepts_iff _ _ a b).1 hacc
  have hi := hall i
  by_contra hne
  have hc : V.consOf n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
      (((V.tgame n).coord (qEquiv V lam tau n x) a i).take ((V.tgame n).lenR (qc V lam tau n x i)))
      (((V.tgame n).coord (qEquiv V lam tau n y) b i).take ((V.tgame n).lenR (qc V lam tau n y i))) =
        [rejectConstraint (V.lenOf n (toBits (qc V lam tau n x i)) false +
          V.lenOf n (toBits (qc V lam tau n x i)) true + V.lenOf n (toBits (qc V lam tau n y i)) false +
          V.lenOf n (toBits (qc V lam tau n y i)) true)] := by
    unfold consOf
    rw [dite_eq_right fun h' => hne ⟨h'.1, h'.2.1⟩]
  exact TailoredGame.not_accepts_of_reject_mem (G := V.tgame n) (by
    change _ ∈ V.consOf n _ _ _ _
    rw [hc]
    exact List.mem_singleton_self _) hi

/-- **At good questions the two games accept the same answers.** -/
theorem accepts_iff {x y : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂} {a b : BitStr}
    (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i)))
    (hy : ∀ i, V.LenDefined n (toBits (qc V lam tau n y i))) :
    ((repTV V lam tau L P).tgame n).Accepts x y a b ↔
      ((V.tgame n).repeat (K lam tau n)).Accepts (qEquiv V lam tau n x) (qEquiv V lam tau n y)
        a b := by
  obtain ⟨hRx, hLx⟩ := h.sameLens hx
  obtain ⟨hRy, hLy⟩ := h.sameLens hy
  set W := repTV V lam tau L P
  set G := V.tgame n
  set R := G.repeat (K lam tau n)
  have hlenx : (W.tgame n).len x = R.len (qEquiv V lam tau n x) := by
    unfold TailoredGame.len; rw [hRx, hLx]
  have hleny : (W.tgame n).len y = R.len (qEquiv V lam tau n y) := by
    unfold TailoredGame.len; rw [hRy, hLy]
  by_cases hab : a.length = R.len (qEquiv V lam tau n x) ∧ b.length = R.len (qEquiv V lam tau n y)
  swap
  · exact iff_of_false (fun hacc => hab ⟨hacc.1.trans hlenx, hacc.2.1.trans hleny⟩)
      (fun hacc => hab ⟨hacc.1, hacc.2.1⟩)
  have haR : (a.take (G.lenRSum (qEquiv V lam tau n x))).length = G.lenRSum (qEquiv V lam tau n x) := by
    rw [List.length_take, hab.1, TailoredGame.repeat_len]; omega
  have hbR : (b.take (G.lenRSum (qEquiv V lam tau n y))).length = G.lenRSum (qEquiv V lam tau n y) := by
    rw [List.length_take, hab.2, TailoredGame.repeat_len]; omega
  have hWcons : (W.tgame n).cons x y (a.take ((W.tgame n).lenR x)) (b.take ((W.tgame n).lenR y)) =
      W.consOf n (toBits x) (toBits y) (a.take (G.lenRSum (qEquiv V lam tau n x)))
        (b.take (G.lenRSum (qEquiv V lam tau n y))) := by
    rw [hRx, hRy]; rfl
  have hRcons : R.cons (qEquiv V lam tau n x) (qEquiv V lam tau n y)
      (a.take (R.lenR (qEquiv V lam tau n x))) (b.take (R.lenR (qEquiv V lam tau n y))) =
      R.cons (qEquiv V lam tau n x) (qEquiv V lam tau n y)
        (a.take (G.lenRSum (qEquiv V lam tau n x))) (b.take (G.lenRSum (qEquiv V lam tau n y))) :=
    rfl
  by_cases hall : ∀ i, ∃ c, LpIs V.lp n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
      (G.coordR (qEquiv V lam tau n x) (a.take (G.lenRSum (qEquiv V lam tau n x))) i)
      (G.coordR (qEquiv V lam tau n y) (b.take (G.lenRSum (qEquiv V lam tau n y))) i) c
  · have hP := (h.lp_iff x y _ _ hx hy haR hbR _).2 ⟨hall, rfl⟩
    have hc := consOf_eq_of W (h.lenDefined hx) (h.lenDefined hy) hP
    constructor
    · rintro ⟨-, -, h3⟩
      refine ⟨hab.1, hab.2, fun c hcm => h3 c ?_⟩
      rw [hWcons, hc]
      rw [hRcons] at hcm
      exact hcm
    · rintro ⟨-, -, h3⟩
      refine ⟨hab.1.trans hlenx.symm, hab.2.trans hleny.symm, fun c hcm => h3 c ?_⟩
      rw [hWcons, hc] at hcm
      rw [hRcons]
      exact hcm
  · have hnP : ¬∃ cs, LpIs P n (toBits x) (toBits y) (a.take (G.lenRSum (qEquiv V lam tau n x)))
        (b.take (G.lenRSum (qEquiv V lam tau n y))) cs :=
      fun ⟨cs, hcs⟩ => hall ((h.lp_iff x y _ _ hx hy haR hbR cs).1 hcs).1
    have hrej : W.consOf n (toBits x) (toBits y) (a.take (G.lenRSum (qEquiv V lam tau n x)))
        (b.take (G.lenRSum (qEquiv V lam tau n y))) =
          [rejectConstraint (W.lenOf n (toBits x) false + W.lenOf n (toBits x) true +
            W.lenOf n (toBits y) false + W.lenOf n (toBits y) true)] := by
      unfold consOf
      split_ifs with hc
      · exact absurd hc.2.2 hnP
      · rfl
    refine iff_of_false (fun hacc => ?_) (fun hacc => ?_)
    · exact not_satisfies_rejectConstraint _ (a ++ b)
        (hacc.2.2 _ (by rw [hWcons, hrej]; exact List.mem_singleton_self _))
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      obtain ⟨hla, hlb, hcoord⟩ := (G.repeat_accepts_iff _ _ a b).1 hacc
      have hci := hcoord i
      have hbase : V.consOf n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
          (G.coordR (qEquiv V lam tau n x) (a.take (G.lenRSum (qEquiv V lam tau n x))) i)
          (G.coordR (qEquiv V lam tau n y) (b.take (G.lenRSum (qEquiv V lam tau n y))) i) =
            [rejectConstraint (V.lenOf n (toBits (qc V lam tau n x i)) false +
              V.lenOf n (toBits (qc V lam tau n x i)) true +
              V.lenOf n (toBits (qc V lam tau n y i)) false +
              V.lenOf n (toBits (qc V lam tau n y i)) true)] := by
        unfold consOf
        split_ifs with hc
        · exact absurd hc.2.2.choose_spec (hi _)
        · rfl
      exact TailoredGame.not_accepts_of_reject_mem (G := G)
        (d := V.lenOf n (toBits (qc V lam tau n x i)) false +
          V.lenOf n (toBits (qc V lam tau n x i)) true +
          V.lenOf n (toBits (qc V lam tau n y i)) false +
          V.lenOf n (toBits (qc V lam tau n y i)) true) (by
          change _ ∈ V.consOf n _ _ _ _
          rw [← G.coordR_take _ hla, ← G.coordR_take _ hlb, hbase]
          exact List.mem_singleton_self _) hci

/-- **The repeated verifier accepts only what the product accepts.** -/
theorem accepts_of_accepts {x y : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂} {a b : BitStr}
    (hacc : ((repTV V lam tau L P).tgame n).Accepts x y a b) :
    ((V.tgame n).repeat (K lam tau n)).Accepts (qEquiv V lam tau n x) (qEquiv V lam tau n y)
      a b := by
  by_cases hdef : (repTV V lam tau L P).LenDefined n (toBits x) ∧
      (repTV V lam tau L P).LenDefined n (toBits y) ∧
      ∃ cs, LpIs (repTV V lam tau L P).lp n (toBits x) (toBits y)
        (a.take (((repTV V lam tau L P).tgame n).lenR x))
        (b.take (((repTV V lam tau L P).tgame n).lenR y)) cs
  · obtain ⟨hdx, hdy, -⟩ := hdef
    obtain ⟨mx, hmx⟩ := hdx false
    obtain ⟨my, hmy⟩ := hdy false
    exact (h.accepts_iff (h.good_of_len x false mx hmx) (h.good_of_len y false my hmy)).1 hacc
  · exfalso
    have hrej : ((repTV V lam tau L P).tgame n).cons x y
        (a.take (((repTV V lam tau L P).tgame n).lenR x))
        (b.take (((repTV V lam tau L P).tgame n).lenR y)) =
          [rejectConstraint ((repTV V lam tau L P).lenOf n (toBits x) false +
            (repTV V lam tau L P).lenOf n (toBits x) true +
            (repTV V lam tau L P).lenOf n (toBits y) false +
            (repTV V lam tau L P).lenOf n (toBits y) true)] := by
      change (repTV V lam tau L P).consOf n _ _ _ _ = _
      unfold consOf
      split_ifs with hc
      · exact absurd hc hdef
      · rfl
    exact TailoredGame.not_accepts_of_reject_mem (by rw [hrej]; exact List.mem_singleton_self _)
      hacc

/-- **Completeness of the repeated verifier.** -/
theorem hasPerfectZPC (hV : V.HasPerfectZPC n) : (repTV V lam tau L P).HasPerfectZPC n := by
  have hrep : ((V.tgame n).repeat (K lam tau n)).doubled.HasPerfectZPC :=
    TailoredGame.HasPerfectZPC.repeat_doubled hV
  obtain ⟨T, hT⟩ := hrep
  let φ : Bool × (repTV V lam tau L P).Questions n →
      Bool × (Fin (K lam tau n) → V.Questions n) := fun p => (p.1, qEquiv V lam tau n p.2)
  -- the endpoints of an edge are good
  have hgood : ∀ p q, 0 < ((repTV V lam tau L P).tgame n).doubled.μ p q →
      (∀ i, V.LenDefined n (toBits (qc V lam tau n p.2 i))) ∧
        (∀ i, V.LenDefined n (toBits (qc V lam tau n q.2 i))) ∧
          0 < ((V.tgame n).repeat (K lam tau n)).doubled.μ (φ p) (φ q) := by
    rintro ⟨s, x⟩ ⟨t, y⟩ hpos
    have hpos' : 0 < ((V.tgame n).repeat (K lam tau n)).doubled.μ (φ (s, x)) (φ (t, y)) := by
      simp only [TailoredGame.doubled_μ] at hpos ⊢
      rwa [← repTV_μ]
    obtain ⟨a, b, hacc⟩ := T.exists_accepts hT hpos'
    exact ⟨fun i => (good_of_repeat_accepts hacc i).1,
      fun i => (good_of_repeat_accepts hacc i).2, hpos'⟩
  have hedge : ∀ p q, 0 < ((repTV V lam tau L P).tgame n).doubled.μ p q →
      SameLens ((V.tgame n).repeat (K lam tau n)).doubled ((repTV V lam tau L P).tgame n).doubled
          φ p ∧
        SameLens ((V.tgame n).repeat (K lam tau n)).doubled
          ((repTV V lam tau L P).tgame n).doubled φ q ∧
          0 < ((V.tgame n).repeat (K lam tau n)).doubled.μ (φ p) (φ q) := by
    intro p q hpq
    obtain ⟨hp, hq, hpos⟩ := hgood p q hpq
    exact ⟨h.sameLens hp, h.sameLens hq, hpos⟩
  refine ⟨T.comap _ φ hedge, T.value_comap_eq_one hT φ hedge fun p q hpq a b hacc => ?_⟩
  obtain ⟨hp, hq, -⟩ := hgood p q hpq
  exact (h.accepts_iff hp hq).2 hacc

end RepSpec

end TailoredVerifier

end MIPRE.Tailored

end
