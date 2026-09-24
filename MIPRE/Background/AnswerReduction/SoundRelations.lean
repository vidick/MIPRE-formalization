/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundExtract
import MIPRE.Foundations.Disagreement

/-!
# Soundness of answer reduction: the cross relations

Piece AR-5d of `planning/answer-reduction.md` (`claim:ar-2`, the first item of `claim:ar-4`, and
the input of `claim:ar-5`). Every relation is a disagreement (`MIPRE.dis`) between a family of
Alice's measurements and a family of Bob's, on the common index `(x, w)` of an oracle half and a
PCP vector, both uniform: the typed question of a type at `(x, w)` is `tq`, and a point answer is
read by `rd1` (copies `1`–`5`) or `rd6` (a component of the sixth copy's answer).

The relations come from two sources:

* **the typed game**, at one type pair (`sum_dis_edge_le`): a subtest whose acceptance forces two
  readings to agree bounds their disagreement by the failure on that pair, at most `54²` times
  the typed failure after summing;
* **the extraction** (`sum_dis_ext1_le`, `sum_dis_ext6_le`, ...): `clSoundness`'s conclusions,
  reindexed from a uniform point of the copy to the point the copy's registers carry in a uniform
  PCP vector, and averaged over the oracle halves.

They chain across the two players (`sum_dis_triangle`): Alice's evaluated `J` against Bob's
evaluated `G` for each of the five copies (`sum_dis_JA_GB_le`), and the mirror image.
-/

noncomputable section

namespace MIPRE.LIDT.CL.Regs

open Finset

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] [Fintype ι] [Field F] [Fintype F] [DecidableEq F] in
theorem ptOf_eq_comp (x : ι → F) : R.ptOf x = x ∘ R.pt := rfl

omit [Field F] in
/-- **Uniform content gives a uniform point**: summing a function of the point the registers
carry over all vectors is summing it over all points, `q^{|ι| - n}` times. -/
theorem sum_ptOf {M : Type*} [AddCommMonoid M] (g : (Fin n → F) → M) :
    ∑ x : ι → F, g (R.ptOf x)
      = (Fintype.card F ^ (Fintype.card ι - n)) • ∑ u : Fin n → F, g u := by
  have h := MIPRE.CL.sum_comp_injective R.pt R.pt_injective g
  rw [Fintype.card_fin] at h
  exact h

omit [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F] in
include R in
theorem n_le_card : n ≤ Fintype.card ι := by
  have := Fintype.card_le_of_injective R.pt R.pt_injective
  rwa [Fintype.card_fin] at this

omit [Field F] [DecidableEq F] in
include R in
/-- The multiplicity of `sum_ptOf`, times the number of points, is the number of vectors. -/
theorem card_mul_card_points :
    Fintype.card F ^ (Fintype.card ι - n) * Fintype.card (Fin n → F)
      = Fintype.card (ι → F) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_add,
    Nat.sub_add_cancel (n_le_card R)]

/-- **A bound on the points gives a bound on the vectors**: if a nonnegative function of the point
averages at most `δ`, so does its value at the point a vector carries. -/
theorem sum_ptOf_le (g : (Fin n → F) → ℝ) {δ : ℝ}
    (hg : ∑ u, g u ≤ Fintype.card (Fin n → F) * δ) :
    ∑ x : ι → F, g (R.ptOf x) ≤ Fintype.card (ι → F) * δ := by
  rw [R.sum_ptOf, nsmul_eq_mul, ← card_mul_card_points R, Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hg (by positivity)

end MIPRE.LIDT.CL.Regs

namespace MIPRE

open Finset Matrix

section Bridges

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] {G : Game X Y A B}

/-- A strategy's conditional failure is the conditional failure of its measurements, as POVMs. -/
theorem TensorProductStrategy.failAt_eq_condFail (T : TensorProductStrategy G) (x : X) (y : Y) :
    T.failAt x y = condFail G T.ψ (fun x => T.PA.toPOVM x) (fun y => T.PB.toPOVM y) x y := rfl

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

/-- `inconsistency` on a uniform index is the average disagreement. -/
theorem inconsistency_uniform {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : X → POVM Λ dA)
    (N : X → POVM Λ dB) :
    inconsistency (uniform X) ψ M N = (∑ x, dis ψ (M x) (N x)) / Fintype.card X := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [inconsistency]
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hμ1 : ∑ x, uniform X x = 1 := by simp [uniform, Finset.card_univ]
  rw [LIDT.Simul.inconsistency_eq_one_sub hμ1 hψ, ← one_sub_agreeSum_uniform]
  rfl

/-- **A bound on `inconsistency` is a bound on the summed disagreement.** -/
theorem sum_dis_le_of_inconsistency {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) {δ : ℝ}
    (h : inconsistency (uniform X) ψ M N ≤ δ) :
    ∑ x, dis ψ (M x) (N x) ≤ Fintype.card X * δ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [inconsistency_uniform hψ, div_le_iff₀ hc] at h
  linarith

end Bridges

end MIPRE

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)

/-! ## The index, the questions and the readings -/

/-- The role at which copy `i ≤ 5` is tested by its point: Alice's for copy `1`, Bob's for copy
`2`, an oracle's for copies `3`, `4`, `5`. -/
def roleOf (i : Fin 5) : Role :=
  if (i : ℕ) = 0 then .alice else if (i : ℕ) = 1 then .bob else .oracle

omit [NeZero P.m] in
theorem ldStep_roleOf (i : Fin 5) : LDStep (roleOf i) i := by
  unfold LDStep roleOf
  fin_cases i <;> simp [roleIdx]

/-- The typed question of type `u` at oracle half `x` and PCP vector `w`. -/
def tq (u : ArTy) (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    Detyping.Question ArTy (Fin (dim V n P)) :=
  (u, (cl V n P hk S S' u).eval (Fin.append x (pcpBits P hk w)))

/-- The value a point answer of copy `i ≤ 5` carries, after parsing. -/
def rd1 (i : Fin 5) (a : Verifier.Answers B) : Fq P hk :=
  val1 (P := P) ((parse (fld P hk) (i.castSucc, .point) a.1).getD (.inl (.values 0)))

/-- The `j`-th value a `Point_6` answer carries, after parsing. -/
def rd6 (j : Fin (P.m' + 6)) (a : Verifier.Answers B) : Fq P hk :=
  val6 (P := P) j ((parse (fld P hk) ((5 : Fin 6), .point) a.1).getD (.inr (.values 0)))

/-- All the values a `Point_6` answer carries, after parsing. -/
def rd6all (a : Verifier.Answers B) : Fin (P.m' + 6) → Fq P hk :=
  vals6 (P := P) ((parse (fld P hk) ((5 : Fin 6), .point) a.1).getD (.inr (.values 0)))

omit [NeZero P.m] in
theorem valsOf_ans1 (u : Ans P (Fq P hk)) : Simul.valsOf (ans1 u) 0 = val1 u := by
  rcases u with (a | a | a) | a <;> rfl

omit [NeZero P.m] in
theorem valsOf_ans6 (u : Ans P (Fq P hk)) (j : Fin (P.m' + 6)) :
    Simul.valsOf (ans6 u) j = val6 j u := by
  rcases u with a | (a | a | a) <;> rfl

omit [NeZero P.m] in
theorem valsOf_ans6' (u : Ans P (Fq P hk)) : Simul.valsOf (ans6 u) = vals6 u := by
  rcases u with a | (a | a | a) <;> rfl

omit [NeZero P.m] in
theorem valsOf_readAns1 (i : Fin 5) (u : Fin P.m → Fq P hk) (a : Verifier.Answers B) :
    Simul.valsOf (readAns1 P hk B i (.point u) a) 0 = rd1 P hk B i a :=
  valsOf_ans1 P hk _

omit [NeZero P.m] in
theorem valsOf_readAns6 (u : Fin P.m' → Fq P hk) (a : Verifier.Answers B) (j : Fin (P.m' + 6)) :
    Simul.valsOf (readAns6 P hk B (.point u) a) j = rd6 P hk B j a :=
  valsOf_ans6 P hk _ j

/-- The component of the sixth copy's point answer that copy `i ≤ 5`'s point answer is checked
against. -/
def blk (i : Fin 5) : Fin (P.m' + 6) :=
  ⟨i, Nat.lt_add_left P.m' (Nat.lt_of_lt_of_le i.isLt (by norm_num))⟩

/-! ## What the typed predicate forces on one type pair -/

/-- **Step 2 or step 4(a)**: at the type pair of copy `i`'s point and the sixth copy's point, both
at the roles that test it, acceptance forces the two readings to agree. -/
theorem rd_eq_of_typedPred (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk)
    {a b : Verifier.Answers B}
    (h : typedPred V n P hk S S' check B (tq V n P hk S S' (roleOf i, (i.castSucc, .point)) x w)
      (tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) x w) a b = true) :
    rd1 P hk B i a = rd6 P hk B (blk P i) b := by
  obtain ⟨u, v, hu, hv, hacc⟩ := accepts_of_typedPred V n P hk S S' check h
  have hu' : parse (fld P hk) (i.castSucc, .point) a.1 = some u := hu
  have hv' : parse (fld P hk) ((5 : Fin 6), .point) b.1 = some v := hv
  simp only [rd1, rd6, hu', hv', Option.getD_some]
  simp only [accepts, Bool.and_eq_true] at hacc
  obtain ⟨⟨-, hs⟩, hs'⟩ := hacc
  fin_cases i <;>
    simp [side, decodeQ, tq, roleOf, roleIdx, blk, Bool.and_eq_true] at hs hs' ⊢
  all_goals first
    | exact hs
    | exact hs'.1.symm
    | exact (of_decide_eq_true hs'.1).symm

/-- The mirror image, with the sixth copy's point asked to Alice. -/
theorem rd_eq_of_typedPred' (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk)
    {a b : Verifier.Answers B}
    (h : typedPred V n P hk S S' check B (tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) x w)
      (tq V n P hk S S' (roleOf i, (i.castSucc, .point)) x w) a b = true) :
    rd6 P hk B (blk P i) a = rd1 P hk B i b := by
  obtain ⟨u, v, hu, hv, hacc⟩ := accepts_of_typedPred V n P hk S S' check h
  have hu' : parse (fld P hk) ((5 : Fin 6), .point) a.1 = some u := hu
  have hv' : parse (fld P hk) (i.castSucc, .point) b.1 = some v := hv
  simp only [rd1, rd6, hu', hv', Option.getD_some]
  simp only [accepts, Bool.and_eq_true] at hacc
  obtain ⟨⟨-, hs⟩, hs'⟩ := hacc
  fin_cases i <;>
    simp [side, decodeQ, tq, roleOf, roleIdx, blk, Bool.and_eq_true] at hs hs' ⊢
  all_goals first
    | exact hs'.symm
    | exact hs.1
    | exact of_decide_eq_true hs.1

/-! ## The measurement families on the index -/

variable (T : TensorProductStrategy (typedGame V n P hk S S' check B))

/-- The index of the relations: an oracle half and a PCP vector. -/
abbrev Idx := (Fin (V.sampler.dim n) → 𝔽₂) × (Coord P → Fq P hk)

/-- Alice's point measurement of copy `i ≤ 5` at the role that tests it, read. -/
def MA1 (i : Fin 5) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dA) :=
  (T.PA.toPOVM (tq V n P hk S S' (roleOf i, (i.castSucc, .point)) p.1 p.2)).map (rd1 P hk B i)

/-- Bob's point measurement of copy `i ≤ 5` at the role that tests it, read. -/
def MB1 (i : Fin 5) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dB) :=
  (T.PB.toPOVM (tq V n P hk S S' (roleOf i, (i.castSucc, .point)) p.1 p.2)).map (rd1 P hk B i)

/-- Alice's `Point_6` measurement, its `j`-th value read. -/
def MA6 (j : Fin (P.m' + 6)) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dA) :=
  (T.PA.toPOVM (tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) p.1 p.2)).map (rd6 P hk B j)

/-- Bob's `Point_6` measurement, its `j`-th value read. -/
def MB6 (j : Fin (P.m' + 6)) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dB) :=
  (T.PB.toPOVM (tq V n P hk S S' (.oracle, ((5 : Fin 6), .point)) p.1 p.2)).map (rd6 P hk B j)

/-- Alice's extracted polynomial of copy `i ≤ 5`, evaluated at the copy's point. -/
def GAe (i : Fin 5) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dA) :=
  ((GA1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval p.1)).toPOVM ()).map
    fun g => (g 0).eval ((regs P i).ptOf p.2)

/-- Bob's extracted polynomial of copy `i ≤ 5`, evaluated at the copy's point. -/
def GBe (i : Fin 5) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dB) :=
  ((GB1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval p.1)).toPOVM ()).map
    fun g => (g 0).eval ((regs P i).ptOf p.2)

/-- Alice's extracted `j`-th polynomial of the sixth copy, evaluated at its point. -/
def JAe (j : Fin (P.m' + 6)) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dA) :=
  ((JA V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval p.1)).toPOVM ()).map
    fun f => (f j).eval ((regs6 P).ptOf p.2)

/-- Bob's extracted `j`-th polynomial of the sixth copy, evaluated at its point. -/
def JBe (j : Fin (P.m' + 6)) (p : Idx V n P hk) : POVM (Fq P hk) (Fin T.dB) :=
  ((JB V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval p.1)).toPOVM ()).map
    fun f => (f j).eval ((regs6 P).ptOf p.2)

/-! ## The relations from the typed game -/

omit [NeZero P.m] in
theorem card_idx : (Fintype.card (Fin (dim V n P) → 𝔽₂) : ℝ) = Fintype.card (Idx V n P hk) := by
  rw [← Fintype.card_congr (Fin.appendEquiv _ _), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_congr (pcpBitsEquiv P hk).symm]

/-- **One type pair of the typed game bounds a summed disagreement**: at most `54²` times the
typed failure, per index. -/
theorem sum_dis_edge_le (uv : ArTy × ArTy) {C : Type*} [Fintype C] [DecidableEq C]
    (f g : Verifier.Answers B → C)
    (hD : ∀ x w a b, typedPred V n P hk S S' check B (tq V n P hk S S' uv.1 x w)
      (tq V n P hk S S' uv.2 x w) a b = true → f a = g b) :
    ∑ p : Idx V n P hk, dis T.ψ ((T.PA.toPOVM (tq V n P hk S S' uv.1 p.1 p.2)).map f)
        ((T.PB.toPOVM (tq V n P hk S S' uv.2 p.1 p.2)).map g)
      ≤ 2916 * Fintype.card (Idx V n P hk) * (1 - T.value) := by
  have h := sum_edges_le V n P hk S S' check B T (fun _ : Unit => uv) (fun _ _ _ => rfl)
  rw [card_arTy_sq, card_idx V n P hk, Fintype.sum_unique] at h
  push_cast at h
  refine le_trans ?_ h
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun w _ => ?_
  rw [edgeFail, TensorProductStrategy.failAt_eq_condFail]
  exact dis_map_le_condFail f g fun a b h => hD x w a b h

/-- **Step 2 and step 4(a)**: Alice's point of copy `i` against Bob's `Point_6`. -/
theorem sum_dis_MA1_MB6_le (i : Fin 5) :
    ∑ p, dis T.ψ (MA1 V n P hk S S' check B T i p) (MB6 V n P hk S S' check B T (blk P i) p)
      ≤ 2916 * Fintype.card (Idx V n P hk) * (1 - T.value) :=
  sum_dis_edge_le V n P hk S S' check B T ((roleOf i, (i.castSucc, .point)),
    (.oracle, ((5 : Fin 6), .point))) _ _
    fun x w _ _ h => rd_eq_of_typedPred V n P hk S S' check B i x w h

/-- The mirror image: Alice's `Point_6` against Bob's point of copy `i`. -/
theorem sum_dis_MA6_MB1_le (i : Fin 5) :
    ∑ p, dis T.ψ (MA6 V n P hk S S' check B T (blk P i) p) (MB1 V n P hk S S' check B T i p)
      ≤ 2916 * Fintype.card (Idx V n P hk) * (1 - T.value) :=
  sum_dis_edge_le V n P hk S S' check B T ((.oracle, ((5 : Fin 6), .point)),
    (roleOf i, (i.castSucc, .point))) _ _
    fun x w _ _ h => rd_eq_of_typedPred' V n P hk S S' check B i x w h

/-! ## The relations from the extraction -/

theorem tuplePOVMA_copy (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂)
    (u : Fin P.m → Fq P hk) :
    (Simul.tuplePOVMA hm (copyStrategy V n P hk S S' check B T r i y) u).map (fun v => v 0)
      = (T.PA.toPOVM (arQ1 V n P hk S r i y (.point u))).map (rd1 P hk B i) := by
  unfold Simul.tuplePOVMA copyStrategy TensorProductStrategy.adapt
  rw [Simul.toPOVM_mergeAt, POVM.map_map, POVM.map_map]
  exact congrArg (fun f => POVM.map f _) (funext fun a => valsOf_readAns1 P hk B i u a)

theorem tuplePOVMB_copy (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂)
    (u : Fin P.m → Fq P hk) :
    (Simul.tuplePOVMB hm (copyStrategy V n P hk S S' check B T r i y) u).map (fun v => v 0)
      = (T.PB.toPOVM (arQ1 V n P hk S r i y (.point u))).map (rd1 P hk B i) := by
  unfold Simul.tuplePOVMB copyStrategy TensorProductStrategy.adapt
  rw [Simul.toPOVM_mergeAt, POVM.map_map, POVM.map_map]
  exact congrArg (fun f => POVM.map f _) (funext fun a => valsOf_readAns1 P hk B i u a)

theorem tuplePOVMA_copy6 (y : Fin (V.sampler.dim n) → 𝔽₂) (u : Fin P.m' → Fq P hk)
    (j : Fin (P.m' + 6)) :
    (Simul.tuplePOVMA hm' (copyStrategy6 V n P hk S S' check B T y) u).map (fun v => v j)
      = (T.PA.toPOVM (arQ6 V n P hk S' .oracle y (.point u))).map (rd6 P hk B j) := by
  unfold Simul.tuplePOVMA copyStrategy6 TensorProductStrategy.adapt
  rw [Simul.toPOVM_mergeAt, POVM.map_map, POVM.map_map]
  exact congrArg (fun f => POVM.map f _) (funext fun a => valsOf_readAns6 P hk B u a j)

theorem tuplePOVMB_copy6 (y : Fin (V.sampler.dim n) → 𝔽₂) (u : Fin P.m' → Fq P hk)
    (j : Fin (P.m' + 6)) :
    (Simul.tuplePOVMB hm' (copyStrategy6 V n P hk S S' check B T y) u).map (fun v => v j)
      = (T.PB.toPOVM (arQ6 V n P hk S' .oracle y (.point u))).map (rd6 P hk B j) := by
  unfold Simul.tuplePOVMB copyStrategy6 TensorProductStrategy.adapt
  rw [Simul.toPOVM_mergeAt, POVM.map_map, POVM.map_map]
  exact congrArg (fun f => POVM.map f _) (funext fun a => valsOf_readAns6 P hk B u a j)

omit [NeZero P.m] in
theorem evalTuplePOVM_map {M r : ℕ} {D : Type*} [Fintype D] [DecidableEq D]
    (G : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := Fq P hk) (m := M) (d := dPcp))
      (Matrix D D ℂ)) (u : Fin M → Fq P hk) (j : Fin r) :
    (Simul.evalTuplePOVM G u).map (fun v => v j) = (G.toPOVM ()).map fun g => (g j).eval u := by
  rw [Simul.evalTuplePOVM, POVM.map_map]

/-- The typed question of copy `i`'s point at `(x, w)` is the per-seed strategy's question of the
point the copy's registers carry. -/
theorem tq_point (i : Fin 5) (r : Role) (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    tq V n P hk S S' (r, (i.castSucc, .point)) x w
      = arQ1 V n P hk S r i ((roleFamily (V.sampler.cl n) r).eval x) (.point ((regs P i).ptOf w)) :=
  cl_eval_append V n P hk S S' r i .point x w

/-- The typed question of the sixth copy's point at `(x, w)`. -/
theorem tq_point6 (r : Role) (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    tq V n P hk S S' (r, ((5 : Fin 6), .point)) x w
      = arQ6 V n P hk S' r ((roleFamily (V.sampler.cl n) r).eval x) (.point ((regs6 P).ptOf w)) :=
  cl_eval_append6 V n P hk S S' r .point x w

omit [NeZero P.m] in
theorem card_idx_eq : (Fintype.card (Idx V n P hk) : ℝ)
    = Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * Fintype.card (Coord P → Fq P hk) := by
  rw [Fintype.card_prod, Nat.cast_mul]

omit [NeZero P.m] in
/-- **Averaging over the oracle halves.** -/
theorem sum_idx_le {F : Idx V n P hk → ℝ} (r : Role) (δ : (Fin (V.sampler.dim n) → 𝔽₂) → ℝ)
    {D : ℝ} (hx : ∀ x, ∑ w, F (x, w)
      ≤ Fintype.card (Coord P → Fq P hk) * δ ((roleFamily (V.sampler.cl n) r).eval x))
    (hD : ∑ x, δ ((roleFamily (V.sampler.cl n) r).eval x)
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * D) :
    ∑ p, F p ≤ Fintype.card (Idx V n P hk) * D := by
  rw [Fintype.sum_prod_type, card_idx_eq]
  calc ∑ x, ∑ w, F (x, w)
      ≤ ∑ x, (Fintype.card (Coord P → Fq P hk) : ℝ) *
          δ ((roleFamily (V.sampler.cl n) r).eval x) := Finset.sum_le_sum fun x _ => hx x
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left hD
          (by positivity : (0 : ℝ) ≤ Fintype.card (Coord P → Fq P hk))
        linarith

/-- **Alice's point of copy `i` against Bob's extracted polynomial**, from the extraction. -/
theorem sum_dis_MA1_GBe_le (i : Fin 5) :
    ∑ p, dis T.ψ (MA1 V n P hk S S' check B T i p) (GBe V n P hk S S' check B T i p)
      ≤ Fintype.card (Idx V n P hk) *
        Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (324 * (1 - T.value)) := by
  refine sum_idx_le V n P hk (roleOf i)
    (fun y => Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1
      (eps1 V n P hk S S' check B T (roleOf i) i y)) (fun x => ?_)
    (sum_deltaSim1_le V n P hk S S' check B T (ldStep_roleOf i))
  set y := (roleFamily (V.sampler.cl n) (roleOf i)).eval x with hy
  obtain ⟨h1, -, -⟩ := ext1_spec V n P hk S S' check B T (roleOf i) i y
  have h1' := sum_dis_le_of_inconsistency T.ψ_unit _ _ h1
  have key : ∀ w, dis T.ψ (MA1 V n P hk S S' check B T i (x, w))
      (GBe V n P hk S S' check B T i (x, w)) = dis T.ψ
      ((T.PA.toPOVM (arQ1 V n P hk S (roleOf i) i y (.point ((regs P i).ptOf w)))).map
        (rd1 P hk B i))
      (((GB1 V n P hk S S' check B T (roleOf i) i y).toPOVM ()).map
        fun g => (g 0).eval ((regs P i).ptOf w)) := fun w => by
    simp only [MA1, GBe]
    rw [tq_point, ← hy]
  rw [Finset.sum_congr rfl fun w _ => key w]
  have h2 : ∑ u : Fin P.m → Fq P hk, dis T.ψ
      ((T.PA.toPOVM (arQ1 V n P hk S (roleOf i) i y (.point u))).map (rd1 P hk B i))
      (((GB1 V n P hk S S' check B T (roleOf i) i y).toPOVM ()).map fun g => (g 0).eval u)
      ≤ (Fintype.card (Fin P.m → Fq P hk) : ℝ) * Simul.deltaSim (Fintype.card (Fq P hk)) P.m
        dPcp 1 (eps1 V n P hk S S' check B T (roleOf i) i y) := by
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) h1'
    rw [← tuplePOVMA_copy, ← evalTuplePOVM_map]
    exact dis_map_le _ _ _ _
  exact (regs P i).sum_ptOf_le _ h2

/-- **Alice's extracted polynomial of copy `i` against Bob's point**, from the extraction. -/
theorem sum_dis_GAe_MB1_le (i : Fin 5) :
    ∑ p, dis T.ψ (GAe V n P hk S S' check B T i p) (MB1 V n P hk S S' check B T i p)
      ≤ Fintype.card (Idx V n P hk) *
        Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (324 * (1 - T.value)) := by
  refine sum_idx_le V n P hk (roleOf i)
    (fun y => Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1
      (eps1 V n P hk S S' check B T (roleOf i) i y)) (fun x => ?_)
    (sum_deltaSim1_le V n P hk S S' check B T (ldStep_roleOf i))
  set y := (roleFamily (V.sampler.cl n) (roleOf i)).eval x with hy
  obtain ⟨-, h2, -⟩ := ext1_spec V n P hk S S' check B T (roleOf i) i y
  have h2' := sum_dis_le_of_inconsistency T.ψ_unit _ _ h2
  have key : ∀ w, dis T.ψ (GAe V n P hk S S' check B T i (x, w))
      (MB1 V n P hk S S' check B T i (x, w)) = dis T.ψ
      (((GA1 V n P hk S S' check B T (roleOf i) i y).toPOVM ()).map
        fun g => (g 0).eval ((regs P i).ptOf w))
      ((T.PB.toPOVM (arQ1 V n P hk S (roleOf i) i y (.point ((regs P i).ptOf w)))).map
        (rd1 P hk B i)) := fun w => by
    simp only [MB1, GAe]
    rw [tq_point, ← hy]
  rw [Finset.sum_congr rfl fun w _ => key w]
  have h3 : ∑ u : Fin P.m → Fq P hk, dis T.ψ
      (((GA1 V n P hk S S' check B T (roleOf i) i y).toPOVM ()).map fun g => (g 0).eval u)
      ((T.PB.toPOVM (arQ1 V n P hk S (roleOf i) i y (.point u))).map (rd1 P hk B i))
      ≤ (Fintype.card (Fin P.m → Fq P hk) : ℝ) * Simul.deltaSim (Fintype.card (Fq P hk)) P.m
        dPcp 1 (eps1 V n P hk S S' check B T (roleOf i) i y) := by
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) h2'
    rw [← tuplePOVMB_copy, ← evalTuplePOVM_map]
    exact dis_map_le _ _ _ _
  exact (regs P i).sum_ptOf_le _ h3

/-- **Alice's extracted `j`-th polynomial of the sixth copy against Bob's `Point_6`.** -/
theorem sum_dis_JAe_MB6_le (j : Fin (P.m' + 6)) :
    ∑ p, dis T.ψ (JAe V n P hk S S' check B T j p) (MB6 V n P hk S S' check B T j p)
      ≤ Fintype.card (Idx V n P hk) *
        Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6) (324 * (1 - T.value)) := by
  refine sum_idx_le V n P hk .oracle
    (fun y => Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
      (eps6 V n P hk S S' check B T y)) (fun x => ?_)
    (sum_deltaSim6_le V n P hk S S' check B T)
  set y := (roleFamily (V.sampler.cl n) .oracle).eval x with hy
  obtain ⟨-, h2, -⟩ := ext6_spec V n P hk S S' check B T y
  have h2' := sum_dis_le_of_inconsistency T.ψ_unit _ _ h2
  have key : ∀ w, dis T.ψ (JAe V n P hk S S' check B T j (x, w))
      (MB6 V n P hk S S' check B T j (x, w)) = dis T.ψ
      (((JA V n P hk S S' check B T y).toPOVM ()).map fun f => (f j).eval ((regs6 P).ptOf w))
      ((T.PB.toPOVM (arQ6 V n P hk S' .oracle y (.point ((regs6 P).ptOf w)))).map
        (rd6 P hk B j)) := fun w => by
    simp only [MB6, JAe]
    rw [tq_point6, ← hy]
  rw [Finset.sum_congr rfl fun w _ => key w]
  have h3 : ∑ u : Fin P.m' → Fq P hk, dis T.ψ
      (((JA V n P hk S S' check B T y).toPOVM ()).map fun f => (f j).eval u)
      ((T.PB.toPOVM (arQ6 V n P hk S' .oracle y (.point u))).map (rd6 P hk B j))
      ≤ (Fintype.card (Fin P.m' → Fq P hk) : ℝ) * Simul.deltaSim (Fintype.card (Fq P hk)) P.m'
        dPcp (P.m' + 6) (eps6 V n P hk S S' check B T y) := by
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) h2'
    rw [← tuplePOVMB_copy6, ← evalTuplePOVM_map]
    exact dis_map_le _ _ _ _
  exact (regs6 P).sum_ptOf_le _ h3

/-- **Alice's `Point_6` against Bob's extracted `j`-th polynomial of the sixth copy.** -/
theorem sum_dis_MA6_JBe_le (j : Fin (P.m' + 6)) :
    ∑ p, dis T.ψ (MA6 V n P hk S S' check B T j p) (JBe V n P hk S S' check B T j p)
      ≤ Fintype.card (Idx V n P hk) *
        Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6) (324 * (1 - T.value)) := by
  refine sum_idx_le V n P hk .oracle
    (fun y => Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
      (eps6 V n P hk S S' check B T y)) (fun x => ?_)
    (sum_deltaSim6_le V n P hk S S' check B T)
  set y := (roleFamily (V.sampler.cl n) .oracle).eval x with hy
  obtain ⟨h1, -, -⟩ := ext6_spec V n P hk S S' check B T y
  have h1' := sum_dis_le_of_inconsistency T.ψ_unit _ _ h1
  have key : ∀ w, dis T.ψ (MA6 V n P hk S S' check B T j (x, w))
      (JBe V n P hk S S' check B T j (x, w)) = dis T.ψ
      ((T.PA.toPOVM (arQ6 V n P hk S' .oracle y (.point ((regs6 P).ptOf w)))).map
        (rd6 P hk B j))
      (((JB V n P hk S S' check B T y).toPOVM ()).map fun f => (f j).eval ((regs6 P).ptOf w)) :=
    fun w => by
    simp only [MA6, JBe]
    rw [tq_point6, ← hy]
  rw [Finset.sum_congr rfl fun w _ => key w]
  have h3 : ∑ u : Fin P.m' → Fq P hk, dis T.ψ
      ((T.PA.toPOVM (arQ6 V n P hk S' .oracle y (.point u))).map (rd6 P hk B j))
      (((JB V n P hk S S' check B T y).toPOVM ()).map fun f => (f j).eval u)
      ≤ (Fintype.card (Fin P.m' → Fq P hk) : ℝ) * Simul.deltaSim (Fintype.card (Fq P hk)) P.m'
        dPcp (P.m' + 6) (eps6 V n P hk S S' check B T y) := by
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) h1'
    rw [← tuplePOVMA_copy6, ← evalTuplePOVM_map]
    exact dis_map_le _ _ _ _
  exact (regs6 P).sum_ptOf_le _ h3

/-! ## The chains -/

/-- The error of copies `1`–`5`'s extraction, at `324` times the typed failure. -/
def err1 : ℝ :=
  Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (324 * (1 - T.value))

/-- The error of the sixth copy's extraction, at `324` times the typed failure. -/
def err6 : ℝ :=
  Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6) (324 * (1 - T.value))

/-- **Alice's evaluated `J` against Bob's evaluated `G`, on copy `i`**: through Bob's `Point_6`
and Alice's point of copy `i`. -/
theorem sum_dis_JAe_GBe_le (i : Fin 5) :
    ∑ p, dis T.ψ (JAe V n P hk S S' check B T (blk P i) p) (GBe V n P hk S S' check B T i p)
      ≤ Fintype.card (Idx V n P hk) * (11 * (err6 V n P hk S S' check B T
        + 2916 * (1 - T.value) + err1 V n P hk S S' check B T)) := by
  refine le_trans (sum_dis_triangle T.ψ_unit (JAe V n P hk S S' check B T (blk P i))
    (MA1 V n P hk S S' check B T i) (MB6 V n P hk S S' check B T (blk P i))
    (GBe V n P hk S S' check B T i)) ?_
  have h1 := sum_dis_JAe_MB6_le V n P hk S S' check B T (blk P i)
  have h2 := sum_dis_MA1_MB6_le V n P hk S S' check B T i
  have h3 := sum_dis_MA1_GBe_le V n P hk S S' check B T i
  rw [err1, err6]
  nlinarith

/-- **Alice's evaluated `G` against Bob's evaluated `J`, on copy `i`**: through Bob's point of copy
`i` and Alice's `Point_6`. -/
theorem sum_dis_GAe_JBe_le (i : Fin 5) :
    ∑ p, dis T.ψ (GAe V n P hk S S' check B T i p) (JBe V n P hk S S' check B T (blk P i) p)
      ≤ Fintype.card (Idx V n P hk) * (11 * (err1 V n P hk S S' check B T
        + 2916 * (1 - T.value) + err6 V n P hk S S' check B T)) := by
  refine le_trans (sum_dis_triangle T.ψ_unit (GAe V n P hk S S' check B T i)
    (MA6 V n P hk S S' check B T (blk P i)) (MB1 V n P hk S S' check B T i)
    (JBe V n P hk S S' check B T (blk P i))) ?_
  have h1 := sum_dis_GAe_MB1_le V n P hk S S' check B T i
  have h2 := sum_dis_MA6_MB1_le V n P hk S S' check B T i
  have h3 := sum_dis_MA6_JBe_le V n P hk S S' check B T (blk P i)
  rw [err1, err6]
  nlinarith

end MIPRE.AnswerReduction

end
