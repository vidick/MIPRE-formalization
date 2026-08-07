/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.Strategy.ProjectorStrategy
import MIPRE.LCS.Strategy.ObservableStrategy

/-!
# Equivalence between Observable-based and Projector-based Strategies

This module establishes the equivalence between the two main formalisms for LCS strategies:
1. **Observable-based strategies**: Defined in terms of self-adjoint involutive operators
   $A_j, B_k$ satisfying local commutation constraints.
2. **Projector-based strategies**: Defined in terms of projector measurement systems
   $E_{i,x}, F_{j,y}$ satisfying similar commutation and consistency constraints.

The main construction in this file is `ObservableStrategy.toProjectorStrategy`,
which converts an `ObservableStrategy` into an `ProjectorStrategy`. It proves that:
- The induced Alice measurements $E_{i,x}$ (defined as products of projectors) and Bob
  measurements $F_{j,y}$ (derived from Bob's observables) form valid measurement systems.
- Alice and Bob's measurements commute as required by the LCS game structure.
-/

namespace MIPRE.LCS




variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {G : Layout}

/-- Bob's two-outcome measurement obtained from his observable via
$P_y = (1/2)(1 + (-1)^y B_j)$. -/
noncomputable def ObservableStrategy.bobMeasurement
  (S : ObservableStrategy R G) :
  Fin G.s → ZMod 2 → R :=
  fun j y ↦ observableToProjector (S.bobObs j) y

/-- For each question $j$, Bob's observable-induced projectors form a measurement system. -/
lemma ObservableStrategy.isMeasurementSystem_bobMeasurement
  (S : ObservableStrategy R G) (j : Fin G.s) :
  IsMeasurementSystem (ObservableStrategy.bobMeasurement S j) where
  sum_one := by
    rw [sum_univ_zmod_two]
    exact sum_one_observableToProjector (S.bobObs j)
  idempotent y := idempotent_observableToProjector (S.bobObs j) (S.bob_isObservable j) y
  orthogonal y y' hy := by
    rcases zmod_two_eq_zero_or_one y with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one y' with rfl | rfl
    · exact absurd rfl hy
    · simpa [ObservableStrategy.bobMeasurement] using
        orthogonal_observableToProjector (S.bobObs j) (S.bob_isObservable j)
    · have h := orthogonal_observableToProjector (S.bobObs j) (S.bob_isObservable j)
      have hcomm : Commute (observableToProjector (S.bobObs j) 1)
          (observableToProjector (S.bobObs j) 0) :=
        commute_observableToProjector (Commute.refl (S.bobObs j)) 1 0
      exact hcomm.eq.trans (by simpa [ObservableStrategy.bobMeasurement] using h)
    · exact absurd rfl hy
  self_adjoint y := star_observableToProjector (S.bobObs j) (S.bob_isObservable j) y

omit [StarModule ℂ R] in
/-- Projectors built from Alice observables belonging to the same equation commute,
because the underlying observables commute. -/
lemma ObservableStrategy.projector_commute_in_equation
  (S : ObservableStrategy R G)
  (i : Fin G.r) (j k : G.V i) (a b : ZMod 2) :
    Commute (observableToProjector (S.aliceObs j.1) a)
      (observableToProjector (S.aliceObs k.1) b) := by
  by_cases hjk : j = k
  · subst hjk
    exact commute_observableToProjector (Commute.refl _) a b
  · exact commute_observableToProjector ((S.sameEquation_comm i) hjk) a b

/-- Alice's projector for an assignment $x$ is the product
$E_{i,x} = \prod_{j \in V_i} (1/2)(1 + (-1)^{x_j} A_j)$. -/
noncomputable def ObservableStrategy.aliceMeasurement
  (S : ObservableStrategy R G) :
  ∀ i, Layout.Assignment G i → R :=
  fun i assignment ↦
    (Finset.univ : Finset (G.V i)).noncommProd
      (fun j_idx ↦ observableToProjector (S.aliceObs j_idx.1) (assignment j_idx))
      (by
        intro j hj j' hj' hne
        exact ObservableStrategy.projector_commute_in_equation S i j j'
          (assignment j) (assignment j'))

/-- Partial joint measurement over a finite subset $s \subseteq V_i$.
This is used to prove the normalization of Alice's full measurement by induction on $s$. -/
noncomputable def ObservableStrategy.jointOn
  (S : ObservableStrategy R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : ∀ j ∈ s, ZMod 2) : R :=
  s.noncommProd
    (fun j ↦
      if hj : j ∈ s then
        observableToProjector (S.aliceObs j.1) (assignment j hj)
      else 1)
    (by
      intro j hj j' hj' hne
      have hjs : j ∈ s := hj
      have hj's : j' ∈ s := hj'
      simpa [Function.onFun, hjs, hj's] using
        (ObservableStrategy.projector_commute_in_equation S i j j'
          (assignment j hjs) (assignment j' hj's)))

omit [StarModule ℂ R] in
/-- Summing the partial joint projectors over all assignments on $s = V_i$ gives $1$. -/
lemma ObservableStrategy.jointOn_sum_one
  (S : ObservableStrategy R G) :
  ∀ i, (∑ assignment : ∀ j ∈ (Finset.univ : Finset (G.V i)), ZMod 2,
      ObservableStrategy.jointOn S i (Finset.univ : Finset (G.V i)) assignment) = 1 := by
  classical
  intro i
  let sumJointOn :
      ∀ s : Finset (G.V i),
        (∑ assignment : ∀ j ∈ s, ZMod 2, ObservableStrategy.jointOn S i s assignment) = 1 := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp [ObservableStrategy.jointOn]
    | @insert a s ha ih =>
        let assignEquiv :=
          Finset.insertPiProdEquiv (fun _ : G.V i ↦ ZMod 2) (s := s) (a := a) ha
        calc
          (∑ assignment : ∀ j ∈ insert a s, ZMod 2,
            ObservableStrategy.jointOn S i (insert a s) assignment)
              = ∑ p : ZMod 2 × (∀ j ∈ s, ZMod 2),
                  ObservableStrategy.jointOn S i (insert a s) (assignEquiv.symm p) := by
                    refine Fintype.sum_equiv assignEquiv _ _ ?_
                    intro assignment
                    simp [congrArg (fun y ↦ ObservableStrategy.jointOn S i (insert a s) y)
                      (assignEquiv.left_inv assignment).symm]
          _ = ∑ p : ZMod 2 × (∀ j ∈ s, ZMod 2),
                observableToProjector (S.aliceObs a.1) p.1 *
                  ObservableStrategy.jointOn S i s p.2 := by
                refine Finset.sum_congr rfl ?_
                intro p
                simp only [Finset.mem_univ, true_implies]
                rcases p with ⟨b, β⟩
                unfold ObservableStrategy.jointOn
                rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
                have ha_eval : assignEquiv.symm (b, β) a (Finset.mem_insert_self a s) = b := by
                  change Finset.prodPiInsert (fun _ : G.V i ↦ ZMod 2) (b, β) a
                    (Finset.mem_insert_self a s) = b
                  simp [Finset.prodPiInsert]
                simp only [ha_eval, Finset.mem_insert, true_or, ↓reduceDIte]
                apply congrArg (fun z ↦ observableToProjector (S.aliceObs a.1) b * z)
                refine Finset.noncommProd_congr rfl ?_ ?_
                · intro x hx
                  have hxa : x ≠ a := by
                    intro h
                    apply ha
                    simpa [h] using hx
                  have hx_eval :
                      assignEquiv.symm (b, β) x (Finset.mem_insert_of_mem hx) = β x hx := by
                    change Finset.prodPiInsert (fun _ : G.V i ↦ ZMod 2) (b, β) x
                      (Finset.mem_insert_of_mem hx) = β x hx
                    simp [Finset.prodPiInsert, hxa]
                  simp [hx, hx_eval]
          _ = ∑ β : ∀ j ∈ s, ZMod 2,
                (∑ b : ZMod 2, observableToProjector (S.aliceObs a.1) b) *
                  ObservableStrategy.jointOn S i s β := by
                rw [Fintype.sum_prod_type]
                simp [sum_univ_zmod_two, add_mul, Finset.sum_add_distrib]
          _ = ∑ β : ∀ j ∈ s, ZMod 2, ObservableStrategy.jointOn S i s β := by
                have hsum : (∑ b : ZMod 2, observableToProjector (S.aliceObs a.1) b) = 1 := by
                  rw [sum_univ_zmod_two]
                  exact sum_one_observableToProjector (S.aliceObs a.1)
                simp [hsum]
          _ = 1 := ih
  simpa using sumJointOn (Finset.univ : Finset (G.V i))

omit [StarModule ℂ R] in
/-- Alice's full assignment-indexed projectors sum to $1$. -/
lemma ObservableStrategy.aliceMeasurement_sum_one
  (S : ObservableStrategy R G) (i : Fin G.r) :
  (∑ assignment : Layout.Assignment G i,
    ObservableStrategy.aliceMeasurement S i assignment) = 1 := by
  classical
  let e : Layout.Assignment G i ≃ (∀ j ∈ (Finset.univ : Finset (G.V i)), ZMod 2) := {
    toFun := fun assignment j _ ↦ assignment j
    invFun := fun assignment j ↦ assignment j (by simp)
    left_inv := by
      intro assignment
      funext j
      rfl
    right_inv := by
      intro assignment
      funext j hj
      simp
  }
  calc
    (∑ assignment : Layout.Assignment G i, ObservableStrategy.aliceMeasurement S i assignment)
      = ∑ assignment : ∀ j ∈ (Finset.univ : Finset (G.V i)), ZMod 2,
            ObservableStrategy.aliceMeasurement S i (e.symm assignment) := by
              refine Fintype.sum_equiv e _ _ ?_
              intro assignment
              rfl
    _ = ∑ assignment : ∀ j ∈ (Finset.univ : Finset (G.V i)), ZMod 2,
          ObservableStrategy.jointOn S i (Finset.univ : Finset (G.V i)) assignment := by
            refine Finset.sum_congr rfl ?_
            intro assignment h
            simp [ObservableStrategy.aliceMeasurement, ObservableStrategy.jointOn, e]
            rfl
    _ = 1 := ObservableStrategy.jointOn_sum_one S i

omit [StarModule ℂ R] in
/-- Two distinct outcomes for the projector associated to a single observable are orthogonal. -/
private lemma projector_orthogonal_of_ne
  (O : R) (hO : IsObservable O) (a b : ZMod 2) (hab : a ≠ b) :
  observableToProjector O a * observableToProjector O b = 0 := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · exact absurd rfl hab
  · simpa using orthogonal_observableToProjector O hO
  · have h := orthogonal_observableToProjector O hO
    have hcomm : Commute (observableToProjector O 1) (observableToProjector O 0) :=
      commute_observableToProjector (Commute.refl O) 1 0
    exact hcomm.eq.trans (by simpa using h)
  · exact absurd rfl hab

omit [StarModule ℂ R] in
/-- The partial Alice measurement over $s$ is idempotent. -/
private lemma alice_partial_idempotent
  (S : ObservableStrategy R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : Layout.Assignment G i) :
  let f : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (assignment j)
  (s.noncommProd f (by
    intro j _ j' _ _
    exact ObservableStrategy.projector_commute_in_equation S i j j'
      (assignment j) (assignment j'))) *
  (s.noncommProd f (by
    intro j _ j' _ _
    exact ObservableStrategy.projector_commute_in_equation S i j j'
      (assignment j) (assignment j'))) =
  (s.noncommProd f (by
    intro j _ j' _ _
    exact ObservableStrategy.projector_commute_in_equation S i j j'
      (assignment j) (assignment j'))) := by
  classical
  dsimp
  let f : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (assignment j)
  let comm : (s : Set (G.V i)).Pairwise (fun x y ↦ Commute (f x) (f y)) := by
    intro j hj j' hj' hne
    simpa [f] using
      ObservableStrategy.projector_commute_in_equation S i j j' (assignment j) (assignment j')
  have hmul := Finset.noncommProd_mul_distrib (s := s) f f comm comm comm
  calc
    s.noncommProd f comm * s.noncommProd f comm
      = s.noncommProd (fun j ↦ f j * f j) (Finset.noncommProd_mul_distrib_aux comm comm comm) := by
          symm
          exact hmul
    _ = s.noncommProd f comm := by
          refine Finset.noncommProd_congr rfl ?_ (Finset.noncommProd_mul_distrib_aux comm comm comm)
          intro j hj
          simp [f, idempotent_observableToProjector, S.alice_isObservable]

/-- The partial Alice measurement over $s$ is self-adjoint. -/
private lemma alice_partial_selfAdjoint
  (S : ObservableStrategy R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : Layout.Assignment G i) :
  let f : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (assignment j)
  star (s.noncommProd f (by
    intro j _ j' _ _
    exact ObservableStrategy.projector_commute_in_equation S i j j'
      (assignment j) (assignment j'))) =
  s.noncommProd f (by
    intro j _ j' _ _
    exact ObservableStrategy.projector_commute_in_equation S i j j'
      (assignment j) (assignment j')) := by
  classical
  dsimp
  let f : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (assignment j)
  let comm : (s : Set (G.V i)).Pairwise (fun x y ↦ Commute (f x) (f y)) := by
    intro j hj j' hj' hne
    simpa [f] using
      ObservableStrategy.projector_commute_in_equation S i j j' (assignment j) (assignment j')
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hcomm_a_s :
          Commute (f a) (s.noncommProd f (comm.mono fun _ ↦ Finset.mem_insert_of_mem)) := by
        refine Finset.noncommProd_commute s f (comm.mono fun _ ↦ Finset.mem_insert_of_mem) (f a) ?_
        intro x hx
        exact comm (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hx) (by
          intro hxa
          exact ha (hxa.symm ▸ hx))
      rw [Finset.noncommProd_insert_of_notMem _ _ _ comm ha]
      rw [star_mul, ih]
      have hsa : star (f a) = f a := by
        simp [f, star_observableToProjector, S.alice_isObservable]
      rw [hsa, hcomm_a_s.eq]

omit [StarModule ℂ R] in
/-- If two assignments differ at some $j₀ \in s$, then the corresponding partial Alice
projectors are orthogonal. -/
private lemma alice_partial_orthogonal
  (S : ObservableStrategy R G) (i : Fin G.r)
  (s : Finset (G.V i)) (α β : Layout.Assignment G i) (j0 : G.V i) (hj0 : j0 ∈ s)
  (hneq : α j0 ≠ β j0) :
  let fα : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (α j)
  let fβ : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (β j)
  (s.noncommProd fα (by
    intro j _ j' _ _
    exact ObservableStrategy.projector_commute_in_equation S i j j' (α j) (α j'))) *
  (s.noncommProd fβ (by
    intro j _ j' _ _
    exact ObservableStrategy.projector_commute_in_equation S i j j' (β j) (β j'))) = 0 := by
  classical
  dsimp
  let fα : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (α j)
  let fβ : G.V i → R := fun j ↦ observableToProjector (S.aliceObs j.1) (β j)
  let commα : (s : Set (G.V i)).Pairwise (fun x y ↦ Commute (fα x) (fα y)) := by
    intro j hj j' hj' hne
    simpa [fα] using ObservableStrategy.projector_commute_in_equation S i j j' (α j) (α j')
  let commβ : (s : Set (G.V i)).Pairwise (fun x y ↦ Commute (fβ x) (fβ y)) := by
    intro j hj j' hj' hne
    simpa [fβ] using ObservableStrategy.projector_commute_in_equation S i j j' (β j) (β j')
  let commβα : (s : Set (G.V i)).Pairwise (fun x y ↦ Commute (fβ x) (fα y)) := by
    intro j hj j' hj' hne
    simpa [fα, fβ] using
      (ObservableStrategy.projector_commute_in_equation S i j' j (α j') (β j)).symm
  have hmul := Finset.noncommProd_mul_distrib (s := s) fα fβ commα commβ commβα
  have hcomm_prod : (s : Set (G.V i)).Pairwise (fun x y ↦ Commute (fα x * fβ x) (fα y * fβ y)) :=
    Finset.noncommProd_mul_distrib_aux commα commβ commβα
  calc
    s.noncommProd fα commα * s.noncommProd fβ commβ
      = s.noncommProd (fun j ↦ fα j * fβ j) hcomm_prod := by
          symm
          exact hmul
    _ = (s.erase j0).noncommProd (fun j ↦ fα j * fβ j) (by
          intro j hj j' hj' hne
          exact hcomm_prod (s.mem_of_mem_erase hj)
            (s.mem_of_mem_erase hj') hne) * (fα j0 * fβ j0) := by
            symm
            exact Finset.noncommProd_erase_mul s hj0 (fun j ↦ fα j * fβ j) hcomm_prod
    _ = 0 := by
          have hj0zero : fα j0 * fβ j0 = 0 := by
            exact projector_orthogonal_of_ne (S.aliceObs j0.1) (S.alice_isObservable j0.1) (α j0)
              (β j0) hneq
          simp [hj0zero]

/-- For each equation $i$, the assignment-indexed family of Alice projectors
is a measurement system. -/
lemma ObservableStrategy.isMeasurementSystem_aliceMeasurement
  (S : ObservableStrategy R G) (i : Fin G.r) :
  IsMeasurementSystem (ObservableStrategy.aliceMeasurement S i) := by
  classical
  refine ⟨ObservableStrategy.aliceMeasurement_sum_one S i, ?_, ?_, ?_⟩
  · intro assignment
    simpa [ObservableStrategy.aliceMeasurement] using
      (alice_partial_idempotent S i (Finset.univ : Finset (G.V i)) assignment)
  · intro α β hαβ
    have hex : ∃ j : G.V i, α j ≠ β j := by
      by_contra h
      apply hαβ
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    rcases hex with ⟨j0, hj0neq⟩
    simpa [ObservableStrategy.aliceMeasurement] using
      (alice_partial_orthogonal S i (Finset.univ : Finset (G.V i)) α β j0 (by simp) hj0neq)
  · intro assignment
    simpa [ObservableStrategy.aliceMeasurement] using
      (alice_partial_selfAdjoint S i (Finset.univ : Finset (G.V i)) assignment)

omit [StarModule ℂ R] in
/-- Every Alice projector commutes with every Bob projector, because each Alice observable
commutes with each Bob observable and commutation is preserved by the projector construction. -/
lemma ObservableStrategy.aliceMeasurement_commute_bobMeasurement
  (S : ObservableStrategy R G)
  (i : Fin G.r) (j : Fin G.s) (α : Layout.Assignment G i) (β : ZMod 2) :
  ObservableStrategy.aliceMeasurement S i α * ObservableStrategy.bobMeasurement S j β =
    ObservableStrategy.bobMeasurement S j β * ObservableStrategy.aliceMeasurement S i α := by
  classical
  let f : G.V i → R := fun k ↦ observableToProjector (S.aliceObs k.1) (α k)
  let comm : ((Finset.univ : Finset (G.V i)) : Set (G.V i)).Pairwise
      (fun x y ↦ Commute (f x) (f y)) := by
    intro x hx y hy hxy
    simpa [f] using ObservableStrategy.projector_commute_in_equation S i x y (α x) (α y)
  have hBob : ∀ x ∈ (Finset.univ : Finset (G.V i)),
      Commute (ObservableStrategy.bobMeasurement S j β) (f x) := by
    intro x hx
    simpa [ObservableStrategy.bobMeasurement, f] using
      commute_observableToProjector (S.alice_bob_commute x.1 j).symm β (α x)
  have hcomm_prod :
      Commute (ObservableStrategy.bobMeasurement S j β)
        ((Finset.univ : Finset (G.V i)).noncommProd f comm) :=
    Finset.noncommProd_commute (Finset.univ : Finset (G.V i)) f comm _ hBob
  simpa [ObservableStrategy.aliceMeasurement, ObservableStrategy.bobMeasurement] using
    hcomm_prod.eq.symm

omit [StarModule ℂ R] in
lemma ObservableStrategy.aliceObs_mul_aliceMeasurement
    (S : ObservableStrategy R G)
    (i : Fin G.r) (j : G.V i) (assignment : Layout.Assignment G i) :
    S.aliceObs j.1 * ObservableStrategy.aliceMeasurement S i assignment =
      ((-1 : ℂ) ^ (assignment j).val) •
        ObservableStrategy.aliceMeasurement S i assignment := by
  classical
  let f : G.V i → R :=
    fun k ↦ observableToProjector (S.aliceObs k.1) (assignment k)
  let comm : ((Finset.univ : Finset (G.V i)) : Set (G.V i)).Pairwise
      (fun x y ↦ Commute (f x) (f y)) := by
    intro x hx y hy hxy
    simpa [f] using
      ObservableStrategy.projector_commute_in_equation S i x y (assignment x) (assignment y)
  let restComm : (((Finset.univ : Finset (G.V i)).erase j) : Set (G.V i)).Pairwise
      (fun x y ↦ Commute (f x) (f y)) := by
    intro x hx y hy hxy
    exact comm
      ((Finset.univ : Finset (G.V i)).mem_of_mem_erase hx)
      ((Finset.univ : Finset (G.V i)).mem_of_mem_erase hy) hxy
  have hsplit :
      ((Finset.univ : Finset (G.V i)).erase j).noncommProd f restComm * f j =
      (Finset.univ : Finset (G.V i)).noncommProd f comm := by
    exact Finset.noncommProd_erase_mul
      (Finset.univ : Finset (G.V i)) (by simp) f comm
  have hcomm_rest :
      Commute (S.aliceObs j.1)
        (((Finset.univ : Finset (G.V i)).erase j).noncommProd f restComm) := by
    refine Finset.noncommProd_commute _ _ _ _ ?_
    intro k hk
    have hkj : k ≠ j := by
      intro h
      exact (Finset.mem_erase.mp hk).1 h
    have hobs : Commute (S.aliceObs j.1) (S.aliceObs k.1) := by
      simpa [Function.onFun] using (S.sameEquation_comm i) hkj.symm
    change Commute (S.aliceObs j.1)
      (observableToProjector (S.aliceObs k.1) (assignment k))
    rw [observableToProjector]
    apply Commute.smul_right
    apply Commute.add_right (.one_right _)
    exact hobs.smul_right _
  calc
    S.aliceObs j.1 * ObservableStrategy.aliceMeasurement S i assignment
        = S.aliceObs j.1 *
            ((Finset.univ : Finset (G.V i)).noncommProd f comm) := by
              simp [ObservableStrategy.aliceMeasurement, f]
    _ = S.aliceObs j.1 *
            ((((Finset.univ : Finset (G.V i)).erase j).noncommProd f restComm) *
              f j) := by rw [hsplit]
    _ = ((Finset.univ : Finset (G.V i)).erase j).noncommProd f restComm *
            (S.aliceObs j.1 * f j) := by
              rw [← mul_assoc, hcomm_rest.eq, mul_assoc]
    _ = ((Finset.univ : Finset (G.V i)).erase j).noncommProd f restComm *
            (((-1 : ℂ) ^ (assignment j).val) • f j) := by
              rw [observable_mul_observableToProjector]
              exact S.alice_isObservable j.1
    _ = ((-1 : ℂ) ^ (assignment j).val) •
            (((Finset.univ : Finset (G.V i)).erase j).noncommProd f restComm * f j) := by
              rw [mul_smul_comm]
    _ = ((-1 : ℂ) ^ (assignment j).val) •
          ObservableStrategy.aliceMeasurement S i assignment := by
            rw [hsplit]
            simp [ObservableStrategy.aliceMeasurement, f]


/-- The observable strategy data induces a projector-valued LCS strategy by taking, for each
observable, its associated two-outcome spectral projectors. -/
noncomputable def ObservableStrategy.toProjectorStrategy
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : Layout}
  (S : ObservableStrategy R G)
 :
  ProjectorStrategy R G :=
  {
    E := ObservableStrategy.aliceMeasurement S
    F := ObservableStrategy.bobMeasurement S
    alice_ms := ObservableStrategy.isMeasurementSystem_aliceMeasurement S
    bob_ms := ObservableStrategy.isMeasurementSystem_bobMeasurement S
    alice_bob_commute := ObservableStrategy.aliceMeasurement_commute_bobMeasurement S
  }

lemma ObservableStrategy.toProjectorStrategy_aliceObs
    (S : ObservableStrategy R G)
    (i : Fin G.r) (j : G.V i) :
    ProjectorStrategy.aliceObs (ObservableStrategy.toProjectorStrategy S) i j = S.aliceObs j.1 := by
  classical
  refine IsMeasurementSystem.eq_of_forall_mul_eq
    ((ObservableStrategy.toProjectorStrategy S).alice_ms i) ?_
  intro assignment
  rw [ProjectorStrategy.aliceObs_mul_E]
  simpa [ObservableStrategy.toProjectorStrategy] using
    (ObservableStrategy.aliceObs_mul_aliceMeasurement S i j assignment).symm

/-- The Bob observable recovered from the projector strategy is the original
observable supplied to the observable strategy. -/
lemma ObservableStrategy.toProjectorStrategy_bobObs
    (S : ObservableStrategy R G)
    (j : Fin G.s) :
    ProjectorStrategy.bobObs (ObservableStrategy.toProjectorStrategy S) j = S.bobObs j := by
  change observableOfMeasurementSystem (ObservableStrategy.bobMeasurement S j) =
    S.bobObs j
  unfold observableOfMeasurementSystem ObservableStrategy.bobMeasurement
    observableToProjector observableSign
  norm_num
  rw [← add_smul]
  norm_num

namespace BipartiteObservableStrategy

/-- The projector strategy induced by a bipartite observable strategy through
`toObservableStrategy`. -/
noncomputable def toProjectorStrategy
    {n : Type*} [Fintype n] [DecidableEq n] {G : Layout}
    (strat : BipartiteObservableStrategy n G) :
    ProjectorStrategy (Matrix (n × n) (n × n) ℂ) G :=
  ObservableStrategy.toProjectorStrategy strat.toObservableStrategy

@[simp] lemma toProjectorStrategy_aliceObs
    {n : Type*} [Fintype n] [DecidableEq n] {G : Layout}
    (strat : BipartiteObservableStrategy n G) (i : Fin G.r) (j : G.V i) :
    ProjectorStrategy.aliceObs strat.toProjectorStrategy i j =
      bipartiteAliceLift (strat.obs j.1) := by
  simpa [toProjectorStrategy] using
    ObservableStrategy.toProjectorStrategy_aliceObs strat.toObservableStrategy i j

@[simp] lemma toProjectorStrategy_bobObs
    {n : Type*} [Fintype n] [DecidableEq n] {G : Layout}
    (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
    ProjectorStrategy.bobObs strat.toProjectorStrategy j = bipartiteBobLift (strat.obs j) := by
  simpa [toProjectorStrategy] using
    ObservableStrategy.toProjectorStrategy_bobObs strat.toObservableStrategy j

end BipartiteObservableStrategy

end MIPRE.LCS
