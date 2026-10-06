/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArFamily
public import MIPRE.Background.AnswerReduction.SoundDecoded

@[expose] public section

/-!
# Soundness of the answer-reduced game: the per-role low-degree games

The first step of the soundness of `𝔄𝔫𝔰ℜ𝔢𝔡` (prop:completeness_soundness_combi_ans_red, II:10487),
for a projective strategy `T` in a bipartite model for the answer-reduced typed game `arGame` on
the CL functions of an answer-reduced sampler (`ArSampler`).

A typed question carries the oracularized input question of its role and a question of the seeded
low-degree test (`ArSampler`): at the seed `(z, w)` of the input sampler and the test's registers,
the question of type `(r, τ)` is `arQr r (oq r z) (ldq τ w)`, the typed question presenting the
role's oracularized question and the test's question of type `τ` of the sample `w` carries
(`eval_seed`). So:

* the typed failure is the average over the `81` type pairs and the seeds `(z, w)` of `T`'s failure
  at those questions (`one_sub_value_eq_sum`), and any set of type pairs weighs at most `81` times
  the typed failure (`sum_edges_le`);
* `T` played at one role and one oracularized question, through `arQr` and the reading `decAns` of
  the role's codewords, is a strategy for the seeded low-degree test with one codeword per slot of
  the role (`roleStrat`): the typed data's low-degree check is the test's predicate
  (`arDt_role`), so it loses no acceptance;
* its failures average, over the seeds of the input sampler, to at most `9` times the typed
  failure (`sum_one_sub_value_roleStrat_le`): a role's nine type pairs are `1/9` of the `81`, and
  the registers of a uniform vector carry a uniform sample (`Regs.sum_sampleOf_retype`, with
  multiplicity `1`, the test's registers being all of `F_q^{D}`).

The paper runs the test inside its first perturbation (II:10623); its type graph has the
low-degree test's own (`ALine – Point – DLine`), here the complete graph with loops, which changes
the constant only.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.SAT MIPRE.LIDT

/-! ## Vectors and typed questions -/

section Questions

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ}

variable (t ht j) in
/-- The bits of a low-degree vector, in the numbering of a typed question's low-degree half. -/
def ldBits (w : Fin (D j) → Fq t ht) : Fin (D j * t) → 𝔽₂ :=
  reindexEquiv finProdFinEquiv (downsizeEquiv (shoupPowerBasis t ht) w)

variable (t ht j) in
/-- The bits of a low-degree vector, as an equivalence. -/
def ldBitsEquiv : (Fin (D j) → Fq t ht) ≃ (Fin (D j * t) → 𝔽₂) :=
  ((downsizeEquiv (shoupPowerBasis t ht)).trans (reindexEquiv finProdFinEquiv)).toEquiv

theorem ldBitsEquiv_apply (w : Fin (D j) → Fq t ht) : ldBitsEquiv t ht j w = ldBits t ht j w :=
  rfl

theorem append_leftPart_rightPart {a b : ℕ} (x : Fin (a + b) → 𝔽₂) :
    Fin.append (leftPart x) (rightPart x) = x := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [leftPart]
  · simp [rightPart]

theorem ldPart_append (rV : ℕ) (y : Fin rV → 𝔽₂) (w : Fin (D j) → Fq t ht) :
    ldPart t ht j rV (Fin.append y (ldBits t ht j w)) = w := by
  simp [ldPart, ldBits]

theorem rolePart_append (rV : ℕ) (y : Fin rV → 𝔽₂) (w : Fin (D j) → Fq t ht) :
    rolePart t j rV (Fin.append y (ldBits t ht j w)) = y := by
  simp [rolePart]

variable {hM : 2 ^ j ∣ Fintype.card (Fq t ht)} (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM)

/-- **The typed question of a question of the low-degree test**, at role `r` and oracularized
question `y`: the low-degree half presents the test's question, the role half is `y`. -/
def arQr (rV : ℕ) (r : Role) (y : Fin rV → 𝔽₂) (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) :
    CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (rV + D j * t)) :=
  ((r, q.ty), Fin.append y (ldBits t ht j ((regs j).embedQ sel q)))

theorem ldQ_arQr (rV : ℕ) (r : Role) (y : Fin rV → 𝔽₂) (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) :
    ldQ t ht j rV sel (arQr sel rV r y q).1.2 (arQr sel rV r y q).2 = q := by
  rw [arQr, ldQ, ldPart_append, LIDT.CL.Regs.questionOf_embedQ]

theorem rolePart_arQr (rV : ℕ) (r : Role) (y : Fin rV → 𝔽₂)
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) : rolePart t j rV (arQr sel rV r y q).2 = y :=
  rolePart_append rV y _

/-- The question of type `τ` of the sample the registers of the low-degree vector `w` carry. -/
abbrev ldq (τ : LIDT.CL.Ty) (w : Fin (D j) → Fq t ht) : LIDT.CL.Question (Fq t ht) (2 ^ j) :=
  ((regs j).sampleOf sel τ w).question hM τ

end Questions

/-! ## The questions of an answer-reduced sampler -/

section Sampler

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM) {ℓV : ℕ} (V : TailoredVerifier ℓV) (n : ℕ)

/-- The oracularized question of role `r` at the seed `z` of the input sampler. -/
abbrev oq (r : Role) (z : V.Questions n) : V.Questions n := ((inSeeded V n).oquestion r z).2

variable {V n} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ}

/-- **The typed question at a seed**: at the seed `(z, w)`, the question of type `(r, τ)` of an
answer-reduced sampler is the typed question presenting the oracularized question of role `r` at
`z` and the low-degree test's question of type `τ` of the sample `w` carries. -/
theorem eval_seed (hP : ArSampler hM sel V n P) (b : Bool) (u : Role × LIDT.CL.Ty)
    (z : V.Questions n) (w : Fin (D j) → Fq t ht) :
    (u, (P b u).eval (Fin.append z (ldBits t ht j w))) =
      arQr sel (V.sampler.dim n) u.1 (oq V n u.1 z) (ldq sel u.2 w) := by
  obtain ⟨r, τ⟩ := u
  have h1 := hP.role b (r, τ) (Fin.append z (ldBits t ht j w))
  have h2 := hP.ld b (r, τ) (Fin.append z (ldBits t ht j w))
  rw [leftPart_append] at h1
  rw [ldPart_append, LIDT.CL.Regs.pres_eval] at h2
  refine Prod.ext (by simp [arQr]) ?_
  have e : ∀ x : Fin (V.sampler.dim n + D j * t) → 𝔽₂,
      rightPart x = ldBits t ht j (ldPart t ht j (V.sampler.dim n) x) := fun x => by
    simp [ldPart, ldBits]
  have hl : leftPart ((P b (r, τ)).eval (Fin.append z (ldBits t ht j w))) = oq V n r z := h1
  have hr : rightPart ((P b (r, τ)).eval (Fin.append z (ldBits t ht j w))) =
      ldBits t ht j ((regs j).embedQ sel (ldq sel τ w)) := by
    rw [e, h2]
  rw [← append_leftPart_rightPart ((P b (r, τ)).eval _), hl, hr]
  rfl

end Sampler

/-! ## The per-role low-degree strategies -/

section Strategy

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}

open Classical in
/-- **The low-degree check of the typed data is the test's predicate**: at two typed questions of
one role presenting questions of the test, an answer pair the typed data accepts reads, through
the role's codewords, as an answer pair the seeded test accepts. -/
theorem arDt_role (r : Role) (y : V.Questions n) (x x' : LIDT.CL.Question (Fq t ht) (2 ^ j))
    {a b : Verifier.Answers B}
    (h : arDt d hM sel L hLM V n Cc hm B (arQr sel _ r y x) (arQr sel _ r y x') a b = true) :
    LIDT.CL.accepts hM x x' (decAns t ht j d L r x.ty a.1)
      (decAns t ht j d L r x'.ty b.1) = true := by
  have h' := (accepts_iff t ht j d L _ sel hLM _ _ _ a.1 b.1).1 (of_decide_eq_true h)
  have h1 := h'.2.2.1 r rfl rfl
  rw [ldQ_arQr, ldQ_arQr] at h1
  exact h1

variable (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B))

/-- **The per-role low-degree strategy** at role `r` and oracularized question `y`: `T` played
through `arQr` and the reading `decAns` of the role's codewords, both players at role `r`. At the
seed `z` of the input sampler the oracularized question is `oq r z`: the seed itself for the
oracle, the original player's question for an isolated player. -/
def roleStrat (r : Role) (y : V.Questions n) :
    M.ProjStrat (LIDT.CL.clGame (F := Fq t ht) (m := 2 ^ j) (d := d)
      (ldc := (slotsOf L r).length) hM) :=
  T.adapt _ (arQr sel _ r y) (arQr sel _ r y) (fun q a => decAns t ht j d L r q.ty a.1)
    (fun q b => decAns t ht j d L r q.ty b.1)

/-- **The per-role failure** is at most the average of `T`'s failures at the typed questions of
the test's samples. -/
theorem one_sub_value_roleStrat_le (r : Role) (y : V.Questions n) :
    1 - (roleStrat T r y).value
      ≤ (∑ sm : LIDT.CL.Sample (Fq t ht) (2 ^ j), T.failAt (arQr sel _ r y (sm.question hM sm.tyA))
          (arQr sel _ r y (sm.question hM sm.tyB)))
        / Fintype.card (LIDT.CL.Sample (Fq t ht) (2 ^ j)) := by
  rw [LIDT.CL.one_sub_value_clGame]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sm _ => ?_) (by positivity)
  exact BipartiteModel.ProjStrat.failAt_adapt_le T _ _ _ _ _ _ _ fun a b h =>
    arDt_role r y _ _ h

/-! ## The typed failure, by type pair and seed -/

theorem card_ty_sq : Fintype.card ((Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty)) = 81 := rfl

theorem arGraph_edges : CL.Graph.edges arGraph = (univ : Finset ((Role × LIDT.CL.Ty) ×
    (Role × LIDT.CL.Ty))) :=
  Finset.filter_true_of_mem fun _ _ => trivial

theorem card_seeds : (Fintype.card (Fin (V.sampler.dim n + D j * t) → ZMod 2) : ℝ) =
    Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht) := by
  rw [← Fintype.card_congr (Fin.appendEquiv _ _), Fintype.card_prod,
    Fintype.card_congr (ldBitsEquiv t ht j).symm]
  push_cast
  rfl

/-- `T`'s failure at the typed questions of the type pair `uv` at the seed `(z, w)`. -/
def edgeFail (uv : (Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty)) (z : V.Questions n)
    (w : Fin (D j) → Fq t ht) : ℝ :=
  T.failAt (arQr sel _ uv.1.1 (oq V n uv.1.1 z) (ldq sel uv.1.2 w))
    (arQr sel _ uv.2.1 (oq V n uv.2.1 z) (ldq sel uv.2.2 w))

theorem edgeFail_nonneg (uv : (Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty)) (z : V.Questions n)
    (w : Fin (D j) → Fq t ht) : 0 ≤ edgeFail T uv z w :=
  T.failAt_nonneg _ _

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **The typed failure** is the average over the type pairs and the seeds `(z, w)` of `T`'s
failure at the typed questions they determine. -/
theorem one_sub_value_eq_sum (hP : ArSampler hM sel V n P) :
    1 - T.value = (∑ uv, ∑ z, ∑ w, edgeFail T uv z w) /
      (81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht))) := by
  have h := CL.Detyping.typed_failure_povm M arGraph arGraph_nonempty P
    (arDt d hM sel L hLM V n Cc hm B) T.PA T.PB
  rw [arGraph_edges, Finset.card_univ, card_ty_sq, card_seeds (V := V) (n := n) (ht := ht)] at h
  refine h.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun uv _ => ?_
  rw [← (Fin.appendEquiv _ _).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← (ldBitsEquiv t ht j).sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e1 := eval_seed sel hP false uv.1 z w
  have e2 := eval_seed sel hP true uv.2 z w
  change M.condFail _ T.PA T.PB (uv.1, (P false uv.1).eval (Fin.append z (ldBits t ht j w)))
    (uv.2, (P true uv.2).eval (Fin.append z (ldBits t ht j w))) = _
  rw [e1, e2]
  rfl

/-- **Any set of type pairs inside the typed failure**: the failures at an injective family of
type pairs, summed over the seeds, add up to at most `81` times the number of seeds times the
typed failure. -/
theorem sum_edges_le (hP : ArSampler hM sel V n P) {ι : Type*} [Fintype ι]
    (e : ι → (Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty)) (he : Function.Injective e) :
    ∑ k, ∑ z, ∑ w, edgeFail T (e k) z w
      ≤ 81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht)) *
        (1 - T.value) := by
  classical
  have hpos : (0 : ℝ) < 81 * (Fintype.card (V.Questions n) *
      Fintype.card (Fin (D j) → Fq t ht)) := by positivity
  rw [one_sub_value_eq_sum T hP, mul_div_cancel₀ _ hpos.ne']
  calc ∑ k, ∑ z, ∑ w, edgeFail T (e k) z w
      = ∑ uv ∈ Finset.univ.image e, ∑ z, ∑ w, edgeFail T uv z w :=
        (Finset.sum_image (f := fun uv => ∑ z, ∑ w, edgeFail T uv z w)
          fun x _ y _ h => he h).symm
    _ ≤ ∑ uv, ∑ z, ∑ w, edgeFail T uv z w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun uv _ _ =>
          Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun w _ => edgeFail_nonneg T uv z w

/-- **A single type pair inside the typed failure.** -/
theorem sum_edge_le (hP : ArSampler hM sel V n P) (uv : (Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty)) :
    ∑ z, ∑ w, edgeFail T uv z w
      ≤ 81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht)) *
        (1 - T.value) := by
  have h := sum_edges_le T hP (fun _ : Unit => uv) (fun _ _ _ => rfl)
  rwa [Fintype.sum_unique] at h

/-! ## The per-role failures average to the typed failure -/

theorem card_regs_sub : Fintype.card (Fin (D j)) - (2 * 2 ^ j + 1) = 0 := by
  simp [D]

/-- **The per-role failures average to at most `9` times the typed failure**: a role's nine type
pairs are `1/9` of the `81`, and on them the registers of a uniform vector carry a uniform
sample. -/
theorem sum_one_sub_value_roleStrat_le (hP : ArSampler hM sel V n P) (r : Role) :
    ∑ z, (1 - (roleStrat T r (oq V n r z)).value)
      ≤ Fintype.card (V.Questions n) * (9 * (1 - T.value)) := by
  set Sc : ℝ := (Fintype.card (LIDT.CL.Sample (Fq t ht) (2 ^ j)) : ℝ)
  set Zc : ℝ := (Fintype.card (V.Questions n) : ℝ)
  set Wc : ℝ := (Fintype.card (Fin (D j) → Fq t ht) : ℝ)
  -- a uniform vector's registers carry a uniform sample, with multiplicity `1`
  have hsm : ∀ g : LIDT.CL.Sample (Fq t ht) (2 ^ j) → ℝ,
      ∑ sm, g sm = ∑ a : LIDT.CL.Ty, ∑ b : LIDT.CL.Ty, ∑ w : Fin (D j) → Fq t ht,
        g (((regs j).sampleOf sel a w).retype a b) := by
    intro g
    rw [LIDT.CL.Regs.sum_sampleOf_retype (regs j) sel g, card_regs_sub, pow_zero, one_smul]
  have hS : Sc = 9 * Wc := by
    have h := hsm fun _ => 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    simp only [Sc, Wc]
    rw [h]
    have h3 : (Fintype.card LIDT.CL.Ty : ℝ) = 3 := by exact_mod_cast (rfl : Fintype.card _ = 3)
    rw [h3]
    ring
  have hW : 0 < Wc := by positivity
  -- the role's nine type pairs
  let e : LIDT.CL.Ty × LIDT.CL.Ty → (Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty) :=
    fun ab => ((r, ab.1), (r, ab.2))
  have he : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [e, Prod.mk.injEq, true_and] at h
    rw [h.1, h.2]
  have h9 := sum_edges_le T hP e he
  have hpt : ∀ z, ∑ sm : LIDT.CL.Sample (Fq t ht) (2 ^ j),
      T.failAt (arQr sel _ r (oq V n r z) (sm.question hM sm.tyA))
        (arQr sel _ r (oq V n r z) (sm.question hM sm.tyB))
      = ∑ ab : LIDT.CL.Ty × LIDT.CL.Ty, ∑ w, edgeFail T (e ab) z w := by
    intro z
    rw [hsm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun w _ => ?_
    have hA : (((regs j).sampleOf sel a w).retype a b).question hM
        (((regs j).sampleOf sel a w).retype a b).tyA = ldq sel a w :=
      LIDT.CL.Sample.question_retype hM _ a b a
    have hB : (((regs j).sampleOf sel a w).retype a b).question hM
        (((regs j).sampleOf sel a w).retype a b).tyB = ldq sel b w :=
      (LIDT.CL.Sample.question_retype hM _ a b b).trans
        (LIDT.CL.Sample.question_retype hM ((regs j).sampleOf sel a w) b b b).symm
    simp only [edgeFail, e]
    rw [hA, hB]
  calc ∑ z, (1 - (roleStrat T r (oq V n r z)).value)
      ≤ ∑ z, (∑ ab : LIDT.CL.Ty × LIDT.CL.Ty, ∑ w, edgeFail T (e ab) z w) / Sc :=
        Finset.sum_le_sum fun z _ => (one_sub_value_roleStrat_le T r _).trans_eq (by rw [hpt])
    _ = (∑ ab : LIDT.CL.Ty × LIDT.CL.Ty, ∑ z, ∑ w, edgeFail T (e ab) z w) / Sc := by
        rw [← Finset.sum_div, Finset.sum_comm]
    _ ≤ 81 * (Zc * Wc) * (1 - T.value) / Sc := div_le_div_of_nonneg_right h9 (by positivity)
    _ = Zc * (9 * (1 - T.value)) := by
        rw [hS]
        field_simp
        ring

end Strategy

end MIPRE.Tailored.AnsRed.Typed

end
