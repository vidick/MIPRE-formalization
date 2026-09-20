/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.Layout
import MIPRE.Foundations.SAT.PcpBlocks

/-!
# Clause indices and the five Boolean PCP blocks

The describer reads five little-endian indices followed by their signs. This
module identifies that input format with the Boolean coordinates used by the
low-degree PCP, including both directions of the index encoding.
-/

namespace MIPRE.SAT

open Cost LowDegree MvPolynomial

/-- A Boolean cube point as a little-endian index. -/
def cubeIndex {m : ℕ} (y : Fin m → Bool) : Fin (2 ^ m) :=
  ⟨bitsVal (List.ofFn y), by simpa using bitsVal_lt (List.ofFn y)⟩

/-- The Boolean cube point named by a little-endian index. -/
def indexCube {m : ℕ} (i : Fin (2 ^ m)) : Fin m → Bool := fun j => i.val.testBit j

@[simp] theorem bitsOfNat_cubeIndex {m : ℕ} (y : Fin m → Bool) :
    bitsOfNat m (cubeIndex y) = List.ofFn y := by
  simpa [cubeIndex] using TM.CookLevin.Desc.bitsOfNat_bitsVal (List.ofFn y)

@[simp] theorem cubeIndex_indexCube {m : ℕ} (i : Fin (2 ^ m)) : cubeIndex (indexCube i) = i := by
  apply Fin.ext
  change bitsVal (bitsOfNat m i) = i
  rw [TM.CookLevin.Desc.bitsVal_bitsOfNat, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem indexCube_cubeIndex {m : ℕ} (y : Fin m → Bool) : indexCube (cubeIndex y) = y := by
  apply List.ofFn_injective
  exact bitsOfNat_cubeIndex y

/-- The concrete bijection used when decoding the five answer assignments. -/
def cubeIndexEquiv (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) where
  toFun := cubeIndex
  invFun := indexCube
  left_inv := indexCube_cubeIndex
  right_inv := cubeIndex_indexCube

theorem bitsOfNat_injective_fin (m : ℕ) :
    Function.Injective (fun i : Fin (2 ^ m) => bitsOfNat m i) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg bitsVal h
  simpa only [TM.CookLevin.Desc.bitsVal_bitsOfNat, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] using hv

/-- Equal-width clause encodings lose neither an index nor a sign. -/
theorem clauseInput5_injective (m : ℕ) : Function.Injective (clauseInput5 m m) := by
  rintro ⟨⟨a, sa⟩, ⟨b, sb⟩, ⟨c, sc⟩, ⟨d, sd⟩, ⟨e, se⟩⟩
    ⟨⟨a', sa'⟩, ⟨b', sb'⟩, ⟨c', sc'⟩, ⟨d', sd'⟩, ⟨e', se'⟩⟩ h
  simp only [clauseInput5, List.append_assoc] at h
  obtain ⟨ha, h⟩ := List.append_inj h (by simp)
  obtain ⟨hb, h⟩ := List.append_inj h (by simp)
  obtain ⟨hc, h⟩ := List.append_inj h (by simp)
  obtain ⟨hd, h⟩ := List.append_inj h (by simp)
  obtain ⟨he, h⟩ := List.append_inj h (by simp)
  have ha' := bitsOfNat_injective_fin m ha
  have hb' := bitsOfNat_injective_fin m hb
  have hc' := bitsOfNat_injective_fin m hc
  have hd' := bitsOfNat_injective_fin m hd
  have he' := bitsOfNat_injective_fin m he
  simp only [List.cons.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := h
  subst a'; subst b'; subst c'; subst d'; subst e'
  rfl

namespace Clause5

variable {V : Type*}

/-- Uniformly indexed literals of a clause with equally sized variable blocks. -/
def literals (c : Clause5 V V V V V) : Fin 5 → Lit V :=
  ![c.l₁, c.l₂, c.l₃, c.l₄, c.l₅]

def ofLiterals (l : Fin 5 → Lit V) : Clause5 V V V V V :=
  ⟨l 0, l 1, l 2, l 3, l 4⟩

@[simp] theorem literals_ofLiterals (l : Fin 5 → Lit V) : (ofLiterals l).literals = l := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem ofLiterals_literals (c : Clause5 V V V V V) : ofLiterals c.literals = c := by
  cases c
  rfl

private theorem lit_true_iff (l : Lit V) (a : V → Bool) : l.eval a = true ↔ a l.var = l.pos := by
  cases h : l.pos <;> cases ha : a l.var <;> simp [Lit.eval, h, ha]

/-- The five Boolean disjuncts are precisely the satisfying-literal condition
in the algebraic PCP completeness and decoding lemmas. -/
theorem eval_iff_exists (c : Clause5 V V V V V) (a : Fin 5 → V → Bool) :
    c.eval (a 0) (a 1) (a 2) (a 3) (a 4) = true ↔
      ∃ i : Fin 5, a i (c.literals i).var = (c.literals i).pos := by
  simp only [Clause5.eval, Bool.or_eq_true, lit_true_iff]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [literals]

end Clause5

namespace PcpParams

/-- The clause described by the first five blocks and sign coordinates of a point. -/
def pointClause (P : PcpParams) (y : Fin P.m' → Bool) :
    Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) :=
  Clause5.ofLiterals (fun i => ⟨cubeIndex (P.block i y), y (P.signIndex i)⟩)

@[simp] theorem pointClause_literals (P : PcpParams) (y : Fin P.m' → Bool) (i : Fin 5) :
    (P.pointClause y).literals i = ⟨cubeIndex (P.block i y), y (P.signIndex i)⟩ := by
  simp [pointClause]

/-- The circuit-input slice of a Boolean PCP point. -/
def inputSlice (P : PcpParams) (y : Fin P.m' → Bool) : List Bool :=
  List.ofFn (fun j : Fin (5 * P.m + 5) => y ⟨j, by have := j.isLt; unfold m'; omega⟩)

@[simp] theorem length_inputSlice (P : PcpParams) (y : Fin P.m' → Bool) :
    (P.inputSlice y).length = 5 * P.m + 5 := List.length_ofFn

/-- The describer's actual input order agrees with the five PCP blocks and signs. -/
theorem clauseInput5_pointClause (P : PcpParams) (y : Fin P.m' → Bool) :
    clauseInput5 P.m P.m (P.pointClause y) = P.inputSlice y := by
  have hb (i : Fin 5) : P.block i y = fun j => y (P.blockIndex i j) := rfl
  simp only [pointClause, Clause5.ofLiterals, clauseInput5, bitsOfNat_cubeIndex]
  unfold inputSlice
  rw [List.ofFn_add, List.ofFn_mul]
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]
  simp [hb, PcpParams.blockIndex, PcpParams.signIndex]

/-- Extend a described clause to a PCP point, initially setting all gate
coordinates to false. Those coordinates may subsequently be replaced by a witness. -/
def pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) : Fin P.m' → Bool :=
  fun j => (clauseInput5 P.m P.m c).getD j false

theorem inputSlice_pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) :
    P.inputSlice (P.pointFromClause c) = clauseInput5 P.m P.m c := by
  apply List.ext_getElem
  · simp only [length_inputSlice, length_clauseInput5]
    omega
  · intro i hi hj
    simp only [inputSlice, List.getElem_ofFn, pointFromClause,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

@[simp] theorem pointClause_pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) : P.pointClause (P.pointFromClause c) = c := by
  apply clauseInput5_injective P.m
  rw [clauseInput5_pointClause, inputSlice_pointFromClause]

theorem block_pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) (i : Fin 5) :
    P.block i (P.pointFromClause c) = indexCube (c.literals i).var := by
  have h := congrArg (fun d => (d.literals i).var) (P.pointClause_pointFromClause c)
  simp only [pointClause_literals] at h
  simpa using congrArg indexCube h

@[simp] theorem sign_pointFromClause (P : PcpParams)
    (c : Clause5 (Fin (2 ^ P.m)) (Fin (2 ^ P.m)) (Fin (2 ^ P.m))
      (Fin (2 ^ P.m)) (Fin (2 ^ P.m))) (i : Fin 5) :
    P.pointFromClause c (P.signIndex i) = (c.literals i).pos := by
  have h := congrArg (fun d => (d.literals i).pos) (P.pointClause_pointFromClause c)
  simpa only [pointClause_literals] using h

end PcpParams

end MIPRE.SAT
