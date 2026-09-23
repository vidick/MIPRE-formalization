/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundRelations
import MIPRE.Background.AnswerReduction.TypedComplete
import MIPRE.Background.LIDT.BlockPoly
import MIPRE.Background.LIDT.Coefficients

/-!
# Soundness of answer reduction: from evaluations to polynomials

Piece AR-5d of `planning/answer-reduction.md`, the Schwartz--Zippel step of `lem:ar-ar`
(`eq:ld-strat-con-def`): the evaluated relations of `SoundRelations` between the sixth copy's
`J` and copy `i`'s `G` become relations between their polynomial outcomes. Copy `i`'s polynomial,
in `m` variables, is placed on its block of the sixth copy's `m'` variables
(`LowIndDegPoly.liftIdx` along `blockEmb i`); two distinct polynomials in `m'` variables of
individual degree `d` agree at a uniform point with probability at most `m' d / q`
(`sum_uniform_eval_eq_le`), so the polynomial outcomes of `J`'s `i`-th component and of the placed
`G` disagree with probability at most their evaluated disagreement plus `m' d / q`
(`sum_dis_poly_JA_le`, and its mirror image).

This replaces the paper's giant sandwich `Λ` of `claim:ar-5`: the oracle's measurement here is
`J` itself, whose components are placed polynomials except with the probability this file bounds.
-/

noncomputable section

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}

omit [Fintype F] [DecidableEq F] in
theorem LowIndDegPoly.eval_sub (f g : LowIndDegPoly (F := F) (m := n) (d := d)) (u : Point F n) :
    (f - g).eval u = f.eval u - g.eval u := by
  simp only [LowIndDegPoly.eval, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **Schwartz--Zippel for coefficient vectors**: two distinct polynomials of individual degree `d`
in `n` variables agree at a uniform point with probability at most `n d / q`. -/
theorem sum_uniform_eval_eq_le {f g : LowIndDegPoly (F := F) (m := n) (d := d)} (hfg : f ≠ g) :
    ∑ u : Point F n, uniform (Point F n) u * (if f.eval u = g.eval u then 1 else 0)
      ≤ (n : ℝ) * d / Fintype.card F := by
  have h := card_eval_eq_zero_le (G := f - g) (sub_ne_zero.mpr hfg)
  have hcard : (Fintype.card (Point F n) : ℝ) = (Fintype.card F : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  calc ∑ u : Point F n, uniform (Point F n) u * (if f.eval u = g.eval u then 1 else 0)
      = ((univ.filter fun u : Point F n => (f - g).eval u = 0).card : ℝ)
          / (Fintype.card F : ℝ) ^ n := by
        simp only [uniform, ← Finset.mul_sum, LowIndDegPoly.eval_sub, sub_eq_zero,
          Finset.sum_boole, hcard]
        rw [inv_mul_eq_div]
    _ ≤ _ := h

end MIPRE.LIDT

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ) (T : TensorProductStrategy (typedGame V n P hk S S' check B))

/-- A polynomial of copy `i`, placed on its block of the sixth copy's variables. -/
def liftBlk (i : Fin 5) (g : LowIndDegPoly (F := Fq P hk) (m := P.m) (d := dPcp)) :
    LowIndDegPoly (F := Fq P hk) (m := P.m') (d := dPcp) :=
  g.liftIdx (blockEmb (P := P) i)

omit [NeZero P.m] in
theorem eval_liftBlk (i : Fin 5) (g : LowIndDegPoly (F := Fq P hk) (m := P.m) (d := dPcp))
    (z : Fin P.m' → Fq P hk) : (liftBlk P hk i g).eval z = g.eval (P.block i z) :=
  LowIndDegPoly.eval_liftIdx (blockEmb_injective i) g z

/-- The error of the Schwartz--Zippel step, `m' d / q`. -/
def errSZ : ℝ := (P.m' : ℝ) * dPcp / Fintype.card (Fq P hk)

omit [NeZero P.m] in
theorem errSZ_nonneg : 0 ≤ errSZ P hk := by unfold errSZ; positivity

omit [NeZero P.m] in
/-- **The multiplicity of the sixth copy's point**: a uniform PCP vector carries a uniform point,
so averaging over one is averaging over the other. -/
theorem sum_ptOf6_div (D : (Fin P.m' → Fq P hk) → ℝ) :
    (∑ w : Coord P → Fq P hk, D ((regs6 P).ptOf w)) / Fintype.card (Coord P → Fq P hk)
      = ∑ z, uniform (Fin P.m' → Fq P hk) z * D z := by
  have hK : ((Fintype.card (Fq P hk) ^ (Fintype.card (Coord P) - P.m') : ℕ) : ℝ) ≠ 0 := by
    positivity
  rw [(regs6 P).sum_ptOf, nsmul_eq_mul, ← (regs6 P).card_mul_card_points, Nat.cast_mul,
    mul_div_mul_left _ _ hK, Finset.sum_div]
  simp only [uniform, inv_mul_eq_div]

/-- The outcome-level disagreement of Alice's `J`, component `i`, against Bob's `G` of copy `i`
placed on its block, at oracle half `x`. -/
def disPolyA (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  dis T.ψ (((JA V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x)).toPOVM
      ()).map fun f => f (blk P i))
    (((GB1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
      fun g => liftBlk P hk i (g 0))

/-- The mirror image: Alice's `G` of copy `i` placed on its block against Bob's `J`, component
`i`. -/
def disPolyB (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  dis T.ψ (((GA1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
      fun g => liftBlk P hk i (g 0))
    (((JB V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x)).toPOVM
      ()).map fun f => f (blk P i))

/-- **From evaluations to polynomials, Alice's `J`**: at each oracle half, the outcome-level
disagreement is at most the evaluated one, averaged over the PCP vectors, plus `m' d / q`. -/
theorem disPolyA_le (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂) :
    disPolyA V n P hk S S' check B T i x
      ≤ (∑ w, dis T.ψ (JAe V n P hk S S' check B T (blk P i) (x, w))
          (GBe V n P hk S S' check B T i (x, w))) / Fintype.card (Coord P → Fq P hk)
        + errSZ P hk := by
  have hν0 : ∀ z, 0 ≤ uniform (Fin P.m' → Fq P hk) z := fun z => by simp [uniform]
  have hν1 : ∑ z, uniform (Fin P.m' → Fq P hk) z = 1 := by simp [uniform, Finset.card_univ]
  have h := dis_le_sum_dis_map_add T.ψ_unit
    (((JA V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x)).toPOVM
      ()).map fun f => f (blk P i))
    (((GB1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
      fun g => liftBlk P hk i (g 0))
    hν0 hν1 (fun z f => f.eval z) (errSZ_nonneg P hk)
    (fun f f' hff' => sum_uniform_eval_eq_le hff')
  have hw : ∀ w, dis T.ψ (JAe V n P hk S S' check B T (blk P i) (x, w))
      (GBe V n P hk S S' check B T i (x, w))
      = dis T.ψ ((((JA V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval
          x)).toPOVM ()).map fun f => f (blk P i)).map fun f => f.eval ((regs6 P).ptOf w))
        ((((GB1 V n P hk S S' check B T (roleOf i) i
          ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
          fun g => liftBlk P hk i (g 0)).map fun f => f.eval ((regs6 P).ptOf w)) := fun w => by
    rw [POVM.map_map, POVM.map_map]
    have hf : (fun g : Poly1 P hk => (liftBlk P hk i (g 0)).eval ((regs6 P).ptOf w))
        = fun g => (g 0).eval ((regs P i).ptOf w) :=
      funext fun g => by rw [eval_liftBlk, block_ptOf_regs6]
    rw [hf]
    rfl
  rw [Finset.sum_congr rfl fun w _ => hw w, sum_ptOf6_div P hk (fun z => dis T.ψ
    ((((JA V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval
      x)).toPOVM ()).map fun f => f (blk P i)).map fun f => f.eval z)
    ((((GB1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
      fun g => liftBlk P hk i (g 0)).map fun f => f.eval z))]
  exact h

/-- **From evaluations to polynomials, Bob's `J`.** -/
theorem disPolyB_le (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂) :
    disPolyB V n P hk S S' check B T i x
      ≤ (∑ w, dis T.ψ (GAe V n P hk S S' check B T i (x, w))
          (JBe V n P hk S S' check B T (blk P i) (x, w))) / Fintype.card (Coord P → Fq P hk)
        + errSZ P hk := by
  have hν0 : ∀ z, 0 ≤ uniform (Fin P.m' → Fq P hk) z := fun z => by simp [uniform]
  have hν1 : ∑ z, uniform (Fin P.m' → Fq P hk) z = 1 := by simp [uniform, Finset.card_univ]
  have h := dis_le_sum_dis_map_add T.ψ_unit
    (((GA1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
      fun g => liftBlk P hk i (g 0))
    (((JB V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x)).toPOVM
      ()).map fun f => f (blk P i))
    hν0 hν1 (fun z f => f.eval z) (errSZ_nonneg P hk)
    (fun f f' hff' => sum_uniform_eval_eq_le hff')
  have hw : ∀ w, dis T.ψ (GAe V n P hk S S' check B T i (x, w))
      (JBe V n P hk S S' check B T (blk P i) (x, w))
      = dis T.ψ ((((GA1 V n P hk S S' check B T (roleOf i) i
          ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
          fun g => liftBlk P hk i (g 0)).map fun f => f.eval ((regs6 P).ptOf w))
        ((((JB V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval
          x)).toPOVM ()).map fun f => f (blk P i)).map fun f => f.eval ((regs6 P).ptOf w)) :=
      fun w => by
    rw [POVM.map_map, POVM.map_map]
    have hf : (fun g : Poly1 P hk => (liftBlk P hk i (g 0)).eval ((regs6 P).ptOf w))
        = fun g => (g 0).eval ((regs P i).ptOf w) :=
      funext fun g => by rw [eval_liftBlk, block_ptOf_regs6]
    rw [hf]
    rfl
  rw [Finset.sum_congr rfl fun w _ => hw w, sum_ptOf6_div P hk (fun z => dis T.ψ
    ((((GA1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()).map
      fun g => liftBlk P hk i (g 0)).map fun f => f.eval z)
    ((((JB V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval
      x)).toPOVM ()).map fun f => f (blk P i)).map fun f => f.eval z))]
  exact h

/-- **Summed over the oracle halves**, Alice's `J` against Bob's placed `G`. -/
theorem sum_disPolyA_le (i : Fin 5) :
    ∑ x, disPolyA V n P hk S S' check B T i x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (11 * (err6 V n P hk S S' check B T
        + 2916 * (1 - T.value) + err1 V n P hk S S' check B T) + errSZ P hk) := by
  have hW : (0 : ℝ) < Fintype.card (Coord P → Fq P hk) := by positivity
  have h := sum_dis_JAe_GBe_le V n P hk S S' check B T i
  rw [Fintype.sum_prod_type, card_idx_eq, mul_assoc] at h
  calc ∑ x, disPolyA V n P hk S S' check B T i x
      ≤ ∑ x, ((∑ w, dis T.ψ (JAe V n P hk S S' check B T (blk P i) (x, w))
          (GBe V n P hk S S' check B T i (x, w))) / Fintype.card (Coord P → Fq P hk)
        + errSZ P hk) := Finset.sum_le_sum fun x _ => disPolyA_le V n P hk S S' check B T i x
    _ = (∑ x, ∑ w, dis T.ψ (JAe V n P hk S S' check B T (blk P i) (x, w))
          (GBe V n P hk S S' check B T i (x, w))) / Fintype.card (Coord P → Fq P hk)
        + Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errSZ P hk := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ ≤ _ := by
        have : (∑ x, ∑ w, dis T.ψ (JAe V n P hk S S' check B T (blk P i) (x, w))
            (GBe V n P hk S S' check B T i (x, w))) / Fintype.card (Coord P → Fq P hk)
            ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (11 * (err6 V n P hk S S' check B T
              + 2916 * (1 - T.value) + err1 V n P hk S S' check B T)) := by
          rw [div_le_iff₀ hW]
          linarith
        linarith

/-- **Summed over the oracle halves**, Alice's placed `G` against Bob's `J`. -/
theorem sum_disPolyB_le (i : Fin 5) :
    ∑ x, disPolyB V n P hk S S' check B T i x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (11 * (err1 V n P hk S S' check B T
        + 2916 * (1 - T.value) + err6 V n P hk S S' check B T) + errSZ P hk) := by
  have hW : (0 : ℝ) < Fintype.card (Coord P → Fq P hk) := by positivity
  have h := sum_dis_GAe_JBe_le V n P hk S S' check B T i
  rw [Fintype.sum_prod_type, card_idx_eq, mul_assoc] at h
  calc ∑ x, disPolyB V n P hk S S' check B T i x
      ≤ ∑ x, ((∑ w, dis T.ψ (GAe V n P hk S S' check B T i (x, w))
          (JBe V n P hk S S' check B T (blk P i) (x, w))) / Fintype.card (Coord P → Fq P hk)
        + errSZ P hk) := Finset.sum_le_sum fun x _ => disPolyB_le V n P hk S S' check B T i x
    _ = (∑ x, ∑ w, dis T.ψ (GAe V n P hk S S' check B T i (x, w))
          (JBe V n P hk S S' check B T (blk P i) (x, w))) / Fintype.card (Coord P → Fq P hk)
        + Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errSZ P hk := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ ≤ _ := by
        have : (∑ x, ∑ w, dis T.ψ (GAe V n P hk S S' check B T i (x, w))
            (JBe V n P hk S S' check B T (blk P i) (x, w))) / Fintype.card (Coord P → Fq P hk)
            ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (11 * (err1 V n P hk S S' check B T
              + 2916 * (1 - T.value) + err6 V n P hk S S' check B T)) := by
          rw [div_le_iff₀ hW]
          linarith
        linarith

end MIPRE.AnswerReduction

end
