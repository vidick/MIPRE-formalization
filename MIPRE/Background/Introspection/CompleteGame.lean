/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.CompleteSampled
import MIPRE.Foundations.Introspection.TypedEstimates

/-! # Perfect PCC completeness of the concrete full typed introspection game

The sampler is the twenty-six-type Pauli CL presentation, with all auxiliary
vertices, and the predicate is the actual parsed introspection predicate with
the QLD decider. A perfect original PCC strategy gives a perfect PCC strategy
on the common seed register tensor the original auxiliary space tensor one
qubit. Original CL seeds are indexed by the Pauli field register; no executable
compiler or arbitrary seed-padding claim is made here.
-/

noncomputable section
namespace MIPRE.Introspection.Complete
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun F (Fin m → Bool) ℓ)
  (D : Seed F m → Seed F m → A → A → Bool)

abbrev Question (m t ℓ : ℕ) :=
  CL.Detyping.Question (QuestionType QLD.Ty ℓ) (Fin ((3*m+3)*t))

def pauliCheck (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QLD.Ty) (x y : Fin ((3*m+3)*t) → ZMod 2) :
    QLD.Answer F m d → QLD.Answer F m d → Bool :=
  QLD.accepts hm (QLD.PauliCL.binaryQuestion b p x) (QLD.PauliCL.binaryQuestion b q y)

def game (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) :=
  TypedEstimates.parsedGame QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm b) L (project (d := d)) D (pauliCheck hm b)

def query (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p : QuestionType QLD.Ty ℓ) (c : QLD.Content F m) : Question m t ℓ :=
  (p, (TypedPresentation.family (QLD.PauliCL.binaryPresentation hm b) p).eval
    (QLD.PauliCL.binaryVectorEquiv b (QLD.PauliCL.contentVector c)))

variable (R : SyncStrategy (Honest.sourceGame L D).doubled)

def op (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (q : Question m t ℓ) :
    Answer F A m d → Matrix (Space L D R) (Space L D R) ℂ :=
  match q.1 with
  | .inl p => pauliOp L D R hm (QLD.PauliCL.binaryQuestion b p q.2)
  | .inr p => auxOp L D R hL p

theorem op_isPVM (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (q : Question m t ℓ) :
    IsPVM (op (d := d) L D R hm b hL q) := by
  rcases q with ⟨q,x⟩
  cases q with
  | inl p => exact pauliOp_isPVM L D R hm _
  | inr p => exact auxOp_isPVM L D R hL p

theorem op_query (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (p : QuestionType QLD.Ty ℓ)
    (c : QLD.Content F m) (a : Answer F A m d) :
    op L D R hm b hL (query hm b p c) a = sampleOp L D R hm hL c p a := by
  cases p with
  | inl p =>
    change pauliOp L D R hm (QLD.PauliCL.binaryQuestion b p
      ((QLD.PauliCL.binaryPresentation hm b p).eval _)) a = _
    rw [QLD.PauliCL.binaryQuestion_presentation]
    rfl
  | inr p => rfl

set_option backward.isDefEq.respectTransparency false in
theorem check_query (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QuestionType QLD.Ty ℓ) (c : QLD.Content F m) (a a' : Answer F A m d) :
    (game L D hm b).D (query hm b p c) (query hm b q c) a a' =
      sampleCheck L D hm c p q a a' := by
  change TypedEstimates.questionCheck L (.pauli .X) (.pauli .Z) project D (pauliCheck hm b)
    (query hm b p c) (query hm b q c) a a' = _
  cases p <;> cases q <;> cases a <;> cases a' <;>
    simp only [TypedEstimates.questionCheck, sampleCheck, TypedPredicate.check,
      query, TypedPresentation.family, pauliCheck, QLD.PauliCL.binaryQuestion_presentation]

/-- A positive-probability question pair retains an actual common content
witness and an edge of the full introspection graph. -/
theorem game_positive_content (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (q r : Question m t ℓ)
    (h : 0 < (game (d := d) L D hm b).μ q r) :
    ∃ (c : QLD.Content F m) (p s : QuestionType QLD.Ty ℓ),
      TypeGraph.Adj QLD.adj (.pauli .X) (.pauli .Z) p s ∧
      q = query hm b p c ∧ r = query hm b s c := by
  let E := TypeGraph.Adj (ℓ := ℓ) QLD.adj (.pauli .X) (.pauli .Z)
  let P := fun _ : Bool => TypedPresentation.family (ℓ := ℓ) (QLD.PauliCL.binaryPresentation hm b)
  have hex : ∃ z : CL.Detyping.TypedSeed E (Fin ((3*m+3)*t)),
      (CL.Detyping.typedQuestion P false z, CL.Detyping.typedQuestion P true z) = (q,r) := by
    by_contra hn
    push Not at hn
    have hz : (game (d := d) L D hm b).μ q r = 0 := by
      change SampledGame.dist (CL.Detyping.typedQuestion P false)
        (CL.Detyping.typedQuestion P true) q r = 0
      simp only [SampledGame.dist, if_neg (hn _), sum_const_zero, mul_zero]
    rw [hz] at h
    exact (lt_irrefl 0 h).elim
  obtain ⟨⟨e,x⟩,he⟩ := hex
  obtain ⟨c,hc⟩ := (QLD.PauliCL.contentEquiv.trans
    (QLD.PauliCL.binaryVectorEquiv (m := m) b).toEquiv).surjective x
  change QLD.PauliCL.binaryVectorEquiv b (QLD.PauliCL.contentVector c) = x at hc
  subst x
  refine ⟨c,e.val.1,e.val.2,?_,?_,?_⟩
  · simpa only [CL.Graph.edges, mem_filter, mem_univ, true_and] using e.property
  · exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.snd he).symm

theorem op_commute (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC)
    (q r : Question m t ℓ) (h : 0 < (game (d := d) L D hm b).μ q r)
    (a a' : Answer F A m d) :
    Commute (op L D R hm b hL q a) (op L D R hm b hL r a') := by
  obtain ⟨c,p,s,he,rfl,rfl⟩ := game_positive_content L D hm b q r h
  rw [op_query, op_query]
  exact sampleOp_commute L D R hm hL hR c p s he a a'

theorem op_reject (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1)
    (q r : Question m t ℓ) (h : 0 < (game (d := d) L D hm b).μ q r)
    (a a' : Answer F A m d) (hr : (game L D hm b).D q r a a' = false) :
    op L D R hm b hL q a * op L D R hm b hL r a' = 0 := by
  obtain ⟨c,p,s,he,rfl,rfl⟩ := game_positive_content L D hm b q r h
  rw [op_query, op_query]
  rw [check_query] at hr
  exact sampleOp_reject L D R hm hd hL hR hv c p s he a a' hr

/-- The actual common-carrier strategy for the complete typed game. -/
def strategy (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) : SyncStrategy (game (d := d) L D hm b).doubled where
  d := Fintype.card (Space L D R)
  d_pos := by
    let : Nonempty (Fin R.d) := Fin.pos_iff_nonempty.mp R.d_pos
    exact Fintype.card_pos
  P :=
    { M := fun q a => registerOp (Fintype.equivFin (Space L D R)).symm (op L D R hm b hL q.2 a)
      selfAdjoint := fun q a => by
        rw [Matrix.star_eq_conjTranspose]
        exact (registerOp_isPVM _ (op_isPVM L D R hm b hL q.2)).isSelfAdjoint a
      projective := fun q a => (registerOp_isPVM _ (op_isPVM L D R hm b hL q.2)).idem a
      normalized := fun q => (registerOp_isPVM _ (op_isPVM L D R hm b hL q.2)).sum_eq_one }

private theorem doubled_positive (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (p q : Bool × Question m t ℓ)
    (h : 0 < (game (d := d) L D hm b).doubled.μ p q) :
    (p.1 = false ∧ q.1 = true) ∧ 0 < (game (d := d) L D hm b).μ p.2 q.2 := by
  have ht : p.1 = false ∧ q.1 = true := by
    by_contra hn
    simp only [Game.doubled_μ, if_neg hn] at h
    exact (lt_irrefl 0 h).elim
  exact ⟨ht,by simpa only [Game.doubled_μ, if_pos ht] using h⟩

set_option backward.isDefEq.respectTransparency false in
theorem strategy_isPCC (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) :
    (strategy (d := d) L D R hm b hL).IsPCC := by
  intro p q h a a'
  have hh := congrArg (registerOp (Fintype.equivFin (Space L D R)).symm)
    (op_commute L D R hm b hL hR p.2 q.2 (doubled_positive L D hm b p q h).2 a a').eq
  simpa only [strategy, registerOp_mul] using hh

set_option backward.isDefEq.respectTransparency false in
theorem strategy_value (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    (strategy (d := d) L D R hm b hL).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro p q h a a' hr
  obtain ⟨ht,hμ⟩ := doubled_positive L D hm b p q h
  have hd' : (game L D hm b).D p.2 q.2 a a' = false := by
    change (if p.1 = false ∧ q.1 = true then (game L D hm b).D p.2 q.2 a a' else false) = false at hr
    simpa only [if_pos ht] using hr
  have hh := congrArg (registerOp (Fintype.equivFin (Space L D R)).symm)
    (op_reject L D R hm b hd hL hR hv p.2 q.2 hμ a a' hd')
  rw [show registerOp (Fintype.equivFin (Space L D R)).symm
    (0 : Matrix (Space L D R) (Space L D R) ℂ) = 0 from rfl] at hh
  have hz : (strategy (d := d) L D R hm b hL).P.M p a * (strategy L D R hm b hL).P.M q a' = 0 := by
    simpa only [strategy, registerOp_mul] using hh
  rw [hz, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

/-- Full typed-game completeness with explicit register and source dimension. -/
theorem exists_perfectPCC (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (game (d := d) L D hm b).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (Seed F m) * R.d := by
  refine ⟨strategy L D R hm b hL, strategy_isPCC L D R hm b hL hR,
    strategy_value L D R hm b hd hL hR hv, ?_⟩
  simp [strategy, Space, Fintype.card_prod]
  ring

end MIPRE.Introspection.Complete
end
