/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.PcpClauses
import MIPRE.Foundations.SAT.FiniteCircuitArithmetization

/-!
# The circuit polynomial in the PCP clause coordinates
-/

noncomputable section

namespace MIPRE.SAT.PcpParams

open LowDegree MvPolynomial

variable {F : Type*} [Field F] [CharP F 2]

/-- The exact finite circuit polynomial transported to the advertised PCP dimension. -/
def circuitArith (P : PcpParams) (C : Circuit) (h : C.inputs + C.size = P.m') :
    MvPolynomial (Fin P.m') F := rename (Fin.cast h) C.finiteArith

theorem eval_circuitArith (P : PcpParams) (C : Circuit) (h : C.inputs + C.size = P.m')
    (y : Fin P.m' → F) :
    eval y (P.circuitArith C h) = eval (y ∘ Fin.cast h) C.finiteArith := by
  simp only [circuitArith, MvPolynomial.eval_rename]

theorem degreeOf_circuitArith (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (h : C.inputs + C.size = P.m') (i : Fin P.m') :
    (P.circuitArith (F := F) C h).degreeOf i ≤ 5 := by
  have he : i = Fin.cast h (Fin.cast h.symm i) := by simp
  rw [he, circuitArith, degreeOf_rename_of_injective (Fin.cast_injective h)]
  exact C.degreeOf_finiteArith_le hC _

theorem eval_circuitArith_bool (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (h : C.inputs + C.size = P.m') (y : Fin P.m' → Bool) :
    eval (pt y) (P.circuitArith (F := F) C h) = 0 ∨
      eval (pt y) (P.circuitArith (F := F) C h) = 1 := by
  rw [eval_circuitArith]
  exact C.eval_finiteArith_bool hC (y ∘ Fin.cast h)

/-- Every accepting input extends to a Boolean PCP point on which the circuit
polynomial is one, and all its original input coordinates are retained. -/
theorem eval_iff_exists_circuitArith (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (h : C.inputs + C.size = P.m') (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ y : Fin P.m' → Bool,
      (∀ i : Fin C.inputs, y (Fin.cast h (Fin.castAdd C.size i)) = x i) ∧
      eval (pt y) (P.circuitArith (F := F) C h) = 1 := by
  rw [C.eval_iff_exists_finiteArith (F := F) hC]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u ∘ Fin.cast h.symm, ?_, ?_⟩
    · simpa using hu
    · simpa [eval_circuitArith, Function.comp_def, pt] using he
  · rintro ⟨y, hy, he⟩
    refine ⟨y ∘ Fin.cast h, hy, ?_⟩
    simpa [eval_circuitArith, Function.comp_def, pt] using he

private theorem inputSlice_getD (P : PcpParams) (y : Fin P.m' → Bool)
    (j : ℕ) (hj : j < 5 * P.m + 5) :
    (P.inputSlice y).getD j false = y ⟨j, by unfold m'; omega⟩ := by
  simp only [inputSlice, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj,
    Option.getD_some]

/-- On a satisfying Boolean point, the encoded clause belongs to the describer's
actual five-block formula. -/
theorem pointClause_mem_of_circuitArith (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (y : Fin P.m' → Bool) (hy : eval (pt y) (P.circuitArith (F := F) C h) = 1) :
    P.pointClause y ∈ C.formula5 P.m P.m := by
  let u := y ∘ Fin.cast h
  have hu : eval (fun i => (ofBool (u i) : F)) C.finiteArith = 1 := by
    simpa [u, eval_circuitArith, pt, Function.comp_def] using hy
  have hv := (C.eval_finiteArith_iff hC u).mp hu
  have ha := (C.eval_iff_routedConsistent hC.nonempty (C.inputPart u)).mpr
    ⟨C.gatePart u, hv⟩
  change C.eval (fun j => (clauseInput5 P.m P.m (P.pointClause y)).getD j false) = true
  rw [clauseInput5_pointClause]
  rw [C.eval_congr hC.inputsLt (C.inputPart u) (fun j => (P.inputSlice y).getD j false) ?_] at ha
  · exact ha
  · intro j hj
    rw [inputSlice_getD P y j (by omega)]
    simp [Circuit.inputPart, hj, u]

/-- Every actual clause has a Boolean witness point whose blocks and signs
decode back to precisely that clause. -/
theorem exists_point_of_clause_mem (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) (hc : c ∈ C.formula5 P.m P.m) :
    ∃ y : Fin P.m' → Bool, P.pointClause y = c ∧
      eval (pt y) (P.circuitArith (F := F) C h) = 1 := by
  obtain ⟨y, hy, he⟩ := (P.eval_iff_exists_circuitArith (F := F) C hC h
    (fun j => (clauseInput5 P.m P.m c).getD j false)).mp hc
  refine ⟨y, ?_, he⟩
  apply clauseInput5_injective P.m
  rw [clauseInput5_pointClause]
  apply List.ext_getElem
  · simp only [length_inputSlice, length_clauseInput5]
    omega
  · intro j hj hj'
    have hji : j < C.inputs := by rw [hI]; simpa using hj
    have hh := hy ⟨j, hji⟩
    change y ⟨j, _⟩ = _ at hh
    simpa only [inputSlice, List.getElem_ofFn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some] using hh

/-- A satisfying tuple for the describer's formula supplies an honest degree-seven
PCP proof for the concrete circuit polynomial. -/
theorem exists_proof_of_formula5_sat (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (a : Fin 5 → Fin (2 ^ P.m) → Bool)
    (ha : (C.formula5 P.m P.m).Sat (a 0) (a 1) (a 2) (a 3) (a 4)) :
    ∃ pf : PcpProof P F,
      (∀ i, pf.g i = ldEnc (fun u => ofBool (a i (cubeIndex u)))) ∧
      ∀ z, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z) := by
  apply PcpAlgebra.exists_proof_of_satisfying_assignment
    (P.circuitArith C h) (fun j => (P.degreeOf_circuitArith C hC h j).trans (by decide))
    (P.eval_circuitArith_bool C hC h) (fun i u => a i (cubeIndex u))
  intro y hy
  have hs := ha _ (P.pointClause_mem_of_circuitArith C hC hI h y hy)
  obtain ⟨i, hi⟩ := (Clause5.eval_iff_exists (P.pointClause y) a).mp hs
  exact ⟨i, by simpa only [pointClause_literals] using hi⟩

/-- The Boolean assignment read from one low-degree answer polynomial. -/
def decodedAssignment [DecidableEq F] {P : PcpParams} (pf : PcpProof P F)
    (i : Fin 5) (j : Fin (2 ^ P.m)) : Bool := decide (coded (pf.g i) (indexCube j) = 1)

theorem ofBool_decodedAssignment [DecidableEq F] {P : PcpParams} (pf : PcpProof P F)
    (i : Fin 5) (j : Fin (2 ^ P.m)) :
    (ofBool (decodedAssignment pf i j) : F) = coded (pf.g i) (indexCube j) := by
  rcases coded_eq (pf.g i) (indexCube j) with h | h <;>
    simp [decodedAssignment, h, ofBool]

private theorem ofBool_injective : Function.Injective (ofBool : Bool → F) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofBool]

/-- Majority acceptance supplies an actual satisfying five-tuple for the
succinctly described clause set, including every Boolean clause witness. -/
theorem formula5_sat_of_majority [Fintype F] [DecidableEq F]
    (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
    (S : Finset (Fin P.m' → F))
    (hS : ∀ z ∈ S, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z))
    (hmajority : Fintype.card F ^ P.m' < 2 * S.card) :
    (C.formula5 P.m P.m).Sat (decodedAssignment pf 0) (decodedAssignment pf 1)
      (decodedAssignment pf 2) (decodedAssignment pf 3) (decodedAssignment pf 4) := by
  intro c hc
  obtain ⟨y, hcy, hy⟩ := P.exists_point_of_clause_mem (F := F) C hC hI h c hc
  obtain ⟨i, hi⟩ := PcpAlgebra.decoded_clause_of_majority (P.circuitArith C h)
    (fun j => (P.degreeOf_circuitArith C hC h j).trans (by decide)) pf hq S hS hmajority y hy
  have hv := congrArg (fun d => (d.literals i).var) hcy
  have ho := congrArg (fun d => (d.literals i).pos) hcy
  simp only [pointClause_literals] at hv ho
  have hb : P.block i y = indexCube (c.literals i).var := by
    simpa using congrArg indexCube hv
  apply (Clause5.eval_iff_exists c (decodedAssignment pf)).mpr
  refine ⟨i, ofBool_injective (F := F) ?_⟩
  rw [ofBool_decodedAssignment, ← hb, hi, ho]

/-- Typed PCP completeness against the describer's actual accepting answer tapes. -/
theorem completeness_of_describes (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (D : Decider) (n T : ℕ) (x y ap bp : Cost.BitStr)
    (hD : C.DescribesDecider P.m P.m D n x y T)
    (hap : ap.length ≤ T) (hbp : bp.length ≤ T)
    (hacc : D.AcceptsWithin n x y ap bp T) :
    ∃ pf : PcpProof P F,
      pf.g 0 = ldEnc (answerVec F P.m ap) ∧
      pf.g 1 = ldEnc (answerVec F P.m bp) ∧
      ∀ z, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z) := by
  obtain ⟨w₁, w₂, w₃, hs⟩ := (hD (fun j => tapeBits ap j) (fun j => tapeBits bp j)).mpr
    ⟨ap, bp, hap, hbp, (fun _ => rfl), (fun _ => rfl), hacc⟩
  let a : Fin 5 → Fin (2 ^ P.m) → Bool :=
    ![fun j => tapeBits ap j, fun j => tapeBits bp j, w₁, w₂, w₃]
  obtain ⟨pf, hg, hv⟩ := P.exists_proof_of_formula5_sat (F := F) C hC hI h a hs
  refine ⟨pf, ?_, ?_, hv⟩
  · change pf.g 0 = ldEnc (fun u => ofBool (tapeBits ap (Cost.bitsVal (List.ofFn u))))
    exact hg 0
  · change pf.g 1 = ldEnc (fun u => ofBool (tapeBits bp (Cost.bitsVal (List.ofFn u))))
    exact hg 1

/-- Typed PCP soundness yields accepted prefixes and the entire decoded answer
tapes, using the describer's exact tape relation. -/
theorem soundness_of_describes [Fintype F] [DecidableEq F]
    (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (D : Decider) (n T : ℕ) (x y : Cost.BitStr)
    (hD : C.DescribesDecider P.m P.m D n x y T)
    (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
    (S : Finset (Fin P.m' → F))
    (hS : ∀ z ∈ S, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z))
    (hmajority : Fintype.card F ^ P.m' < 2 * S.card) :
    ∃ ap bp : Cost.BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧
      D.AcceptsWithin n x y ap bp T ∧
      coded (pf.g 0) = answerVec F P.m ap ∧ coded (pf.g 1) = answerVec F P.m bp := by
  have hs := P.formula5_sat_of_majority C hC hI h pf hq S hS hmajority
  obtain ⟨ap, bp, hap, hbp, ha, hb, hacc⟩ :=
    (hD (decodedAssignment pf 0) (decodedAssignment pf 1)).mp ⟨_, _, _, hs⟩
  refine ⟨ap, bp, hap, hbp, hacc, ?_, ?_⟩
  · funext u
    have he := ofBool_decodedAssignment pf 0 (cubeIndex u)
    rw [indexCube_cubeIndex, ha] at he
    exact he.symm
  · funext u
    have he := ofBool_decodedAssignment pf 1 (cubeIndex u)
    rw [indexCube_cubeIndex, hb] at he
    exact he.symm

end MIPRE.SAT.PcpParams

end
