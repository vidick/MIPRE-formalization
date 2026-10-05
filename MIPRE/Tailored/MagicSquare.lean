/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.ZPC
public import MIPRE.Tactics

@[expose] public section

/-!
# The Magic Square game has a perfect ZPC strategy

Paper II, Examples 2.13–2.14 (II:1300–1370): the Mermin–Peres Magic Square, as a linear
constraint system game tailored with *all variables unreadable*, has a perfect Z-aligned
permutation strategy commuting along edges, on the signed set `(F₂²)_±` of eight points — while
the system itself has no solution, so the game has no perfect classical strategy, and no perfect
ZPC strategy when tailored with all variables readable (Remark II:1250). This is the
non-vacuity witness of plan §5, Phase 1: perfect ZPC strategies are not classical strategies in
disguise.

* `game`: the questions are the six constraints (rows `(false, r)`, columns `(true, c)`) and the
  nine cells; an edge joins a constraint to one of its three cells, with weight `1/18`; each edge
  checks consistency (`a_t = b`) and the constraint (`a₀ + a₁ + a₂ = parity`, rows `0`, columns
  `1`) as two linear constraints.
* `obs`: the paper's grid of signed permutations of `F₂² ≅ Fin 4` (II:1363), built from the bit
  flip `pX` and the conditional sign flip `pZ` on one bit. Its group identities — involutions,
  commuting along rows and columns, rows multiplying to `Id` and columns to `-Id` — are checked by
  `decide`, in the group `SignedPerm (Fin 4)`, and transported to matrices by
  `SignedPerm.toMatrixHom`.
* `strategy`, `value_strategy`: the perfect ZPC strategy; `hasPerfectZPC`, and through the
  doubled game `valStar_eq_one`.
-/

namespace MIPRE.Tailored.MagicSquare

open Cost

/-! ## The game -/

/-- The constraints: rows `(false, r)` and columns `(true, c)`. -/
abbrev Cons := Bool × Fin 3

/-- The variables: the cells of the grid. -/
abbrev Var := Fin 3 × Fin 3

/-- The questions: a constraint, or a cell. -/
abbrev Question := Cons ⊕ Var

/-- The `t`-th cell of a constraint. -/
def cell (c : Cons) (t : Fin 3) : Var := if c.1 then (t, c.2) else (c.2, t)

/-- The parity of a constraint: rows sum to `0`, columns to `1` (II:1342). -/
def parity (c : Cons) : Bool := c.1

/-- An edge joins a constraint to one of its cells. -/
def isEdge : Question → Question → Bool
  | .inl c, .inr v => (List.finRange 3).any fun t => cell c t == v
  | _, _ => false

theorem isEdge_iff {x y : Question} :
    isEdge x y = true ↔ ∃ c t, x = .inl c ∧ y = .inr (cell c t) := by
  constructor
  · intro h
    rcases x with c | v <;> rcases y with c' | v' <;> simp only [isEdge, Bool.false_eq_true] at h
    obtain ⟨t, -, ht⟩ := List.any_eq_true.1 h
    exact ⟨c, t, rfl, by rw [beq_iff_eq.1 ht]⟩
  · rintro ⟨c, t, rfl, rfl⟩
    exact List.any_eq_true.2 ⟨t, List.mem_finRange t, beq_self_eq_true _⟩

/-- The number of linear variables: three at a constraint, one at a cell. -/
def lenL : Question → ℕ
  | .inl _ => 3
  | .inr _ => 1

/-- The two constraints of an edge `(c, v)`, over the variables of `c`, of `v`, and `J`:
consistency, `a_t + b = 0` for the position `t` of `v` in `c`; and the constraint itself,
`a₀ + a₁ + a₂ + parity = 0`. -/
def edgeConstraints (c : Cons) (v : Var) : List BitStr :=
  [List.ofFn (fun i : Fin 3 => decide (cell c i = v)) ++ List.ofFn (fun _ : Fin 1 => true) ++
      [false],
    List.ofFn (fun _ : Fin 3 => true) ++ List.ofFn (fun _ : Fin 1 => false) ++ [parity c]]

theorem card_edges :
    (∑ x : Question, ∑ y : Question, if isEdge x y then (1 : ℕ) else 0) = 18 := by
  decide

/-- **The Magic Square game** (II:1335), tailored with all variables unreadable (II:1310). -/
noncomputable def game : TailoredGame Question where
  μ x y := if isEdge x y then 1 / 18 else 0
  μ_nonneg x y := by split_ifs <;> norm_num
  μ_sum_one := by
    have h := congrArg (fun n : ℕ => (n : ℝ) * (1 / 18)) card_edges
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul, ite_mul,
      one_mul, zero_mul] at h
    rw [h]
    norm_num
  lenR _ := 0
  lenL := lenL
  cons x y _ _ := match x, y with
    | .inl c, .inr v => edgeConstraints c v
    | _, _ => []

theorem game_len_inl (c : Cons) : game.len (.inl c) = 3 := rfl

theorem game_len_inr (v : Var) : game.len (.inr v) = 1 := rfl

theorem edge_of_pos {x y : Question} (h : 0 < game.μ x y) :
    ∃ c t, x = .inl c ∧ y = .inr (cell c t) := by
  refine isEdge_iff.1 ?_
  by_contra hne
  simp only [game, Bool.not_eq_true] at h hne
  rw [hne] at h
  simp at h

/-! ## The strategy -/

/-- The bit flip `X` on one bit. -/
def pX : SignedPerm (Fin 2) := ⟨Equiv.swap 0 1, fun _ => false⟩

/-- The conditional sign flip `Z` on one bit. -/
def pZ : SignedPerm (Fin 2) := ⟨1, fun i => decide (i = 1)⟩

/-- `g ⊗ h` on two bits, as a signed permutation of `Fin 4`. -/
def two (g h : SignedPerm (Fin 2)) : SignedPerm (Fin 4) := (g.prod h).map finProdFinEquiv

/-- **The paper's grid** (II:1363): `X ⊗ I, I ⊗ X, XX`; `I ⊗ Z, Z ⊗ I, ZZ`; and minus the
products of the first two rows' cells. -/
def obs (v : Var) : SignedPerm (Fin 4) :=
  ![![two pX 1, two 1 pX, two pX pX],
    ![two 1 pZ, two pZ 1, two pZ pZ],
    ![SignedPerm.negOne * (two pX 1 * two 1 pZ), SignedPerm.negOne * (two 1 pX * two pZ 1),
      SignedPerm.negOne * (two pX pX * two pZ pZ)]] v.1 v.2

theorem obs_mul_self : ∀ v, obs v * obs v = 1 := by decide

theorem obs_comm : ∀ c t t', obs (cell c t) * obs (cell c t') = obs (cell c t') * obs (cell c t) := by
  decide

/-- The two linear constraints of each edge, as identities between signed permutations:
consistency squares a cell's observable to `Id`; the rows multiply to `Id` and the columns to
`-Id`. -/
theorem obs_consistency : ∀ c t,
    ((List.finRange 3).map fun i => if decide (cell c i = cell c t) then obs (cell c i) else 1).prod *
      ((List.finRange 1).map fun _ => if true then obs (cell c t) else 1).prod = 1 := by
  decide

theorem obs_parity : ∀ c t,
    ((List.finRange 3).map fun i => if true then obs (cell c i) else 1).prod *
      ((List.finRange 1).map fun _ => if false then obs (cell c t) else 1).prod =
        if parity c then SignedPerm.negOne else 1 := by
  decide

/-- The observables at each question. -/
def obsAt : (x : Question) → Fin (game.len x) → SignedPerm (Fin 4)
  | .inl c => fun i => obs (cell c i)
  | .inr v => fun _ => obs v

theorem obsAt_mul_self (x : Question) (i : Fin (game.len x)) : obsAt x i * obsAt x i = 1 := by
  rcases x with c | v
  · exact obs_mul_self _
  · exact obs_mul_self _

theorem obsAt_comm (x : Question) (i j : Fin (game.len x)) :
    obsAt x i * obsAt x j = obsAt x j * obsAt x i := by
  rcases x with c | v
  · exact obs_comm c i j
  · rfl

/-- **The perfect ZPC strategy** (II:1362): every variable is unreadable, so Z-alignment is
vacuous. -/
noncomputable def strategy : PermStrategy game where
  m := 4
  m_pos := by norm_num
  U x i := (obsAt x i).toMatrix
  signedPerm x i := (obsAt x i).isSignedPerm_toMatrix
  invol x i := by rw [← SignedPerm.toMatrix_mul, obsAt_mul_self, SignedPerm.toMatrix_one]
  comm x i j := by rw [← SignedPerm.toMatrix_mul, ← SignedPerm.toMatrix_mul, obsAt_comm]
  zAligned x i hi := absurd hi (Nat.not_lt_zero _)
  commEdges x y hxy i j := by
    obtain ⟨c, t, rfl, rfl⟩ := edge_of_pos hxy
    rw [← SignedPerm.toMatrix_mul, ← SignedPerm.toMatrix_mul]
    exact congrArg SignedPerm.toMatrix (obs_comm c i t)

/-- The observable of a linear constraint of signed permutation observables is the matrix of the
product of the signed permutations. -/
theorem obsChar_toMatrix {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
    (g : Fin k → SignedPerm Ω) (α : Fin k → Bool) :
    obsChar (fun i => (g i).toMatrix) α =
      (((List.finRange k).map fun i => if α i then g i else 1).prod).toMatrix := by
  unfold obsChar
  rw [← SignedPerm.toMatrixHom_apply, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  split_ifs
  · rfl
  · exact SignedPerm.toMatrix_one.symm

theorem toMatrix_ite_negOne {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (γ : Bool) :
    (if γ then SignedPerm.negOne else (1 : SignedPerm Ω)).toMatrix = bitSign γ • 1 := by
  cases γ
  · simp [SignedPerm.toMatrix_one]
  · simp [SignedPerm.toMatrix_negOne]

/-- **The strategy is perfect.** -/
theorem value_strategy : strategy.value = 1 := by
  apply PermStrategy.value_eq_one_of
  intro x y hxy a b hrej
  by_contra hne
  apply hrej
  obtain ⟨c, t, rfl, rfl⟩ := edge_of_pos hxy
  refine ⟨List.length_ofFn, List.length_ofFn, fun cv hcv => ?_⟩
  -- the constraint's observable is a scalar, so the constraint holds on the sampled answers
  have key : ∀ (α : Fin (game.len (.inl c)) → Bool) (β : Fin (game.len (.inr (cell c t))) → Bool)
      (γ : Bool),
      (((List.finRange 3).map fun i => if α i then obs (cell c i) else 1).prod *
        ((List.finRange 1).map fun i => if β i then obs (cell c t) else 1).prod =
          if γ then SignedPerm.negOne else 1) →
      Satisfies (List.ofFn α ++ List.ofFn β ++ [γ]) (List.ofFn a ++ List.ofFn b ++ [true]) := by
    intro α β γ hg
    rw [satisfies_ofFn_iff]
    refine strategy.dotBit_of_obsChar hxy ?_ hne
    have hobs : obsChar (strategy.U (.inl c)) α * obsChar (strategy.U (.inr (cell c t))) β =
        bitSign γ • (1 : Matrix (Fin strategy.m) (Fin strategy.m) ℂ) := by
      show obsChar (fun i => (obsAt (.inl c) i).toMatrix) α *
          obsChar (fun i => (obsAt (.inr (cell c t)) i).toMatrix) β =
        bitSign γ • (1 : Matrix (Fin 4) (Fin 4) ℂ)
      rw [obsChar_toMatrix, obsChar_toMatrix, ← SignedPerm.toMatrix_mul]
      exact (congrArg SignedPerm.toMatrix hg).trans (toMatrix_ite_negOne γ)
    rw [hobs, smul_mul_assoc, one_mul]
  simp only [game, edgeConstraints, List.mem_cons, List.not_mem_nil, or_false] at hcv
  rcases hcv with rfl | rfl
  · exact key _ _ false (obs_consistency c t)
  · exact key _ _ (parity c) (obs_parity c t)

/-- **The Magic Square game has a perfect ZPC strategy** (II:1352). -/
theorem hasPerfectZPC : game.HasPerfectZPC := ⟨strategy, value_strategy⟩

/-- Hence its quantum value is `1`, through the doubled game (`lem:zpc-pcc`). -/
theorem valStar_eq_one : game.valStar = 1 := hasPerfectZPC.doubled.valStar_eq_one

end MIPRE.Tailored.MagicSquare

end
