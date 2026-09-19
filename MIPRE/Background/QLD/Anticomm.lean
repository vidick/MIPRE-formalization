/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Sign
import MIPRE.Foundations.Dilation
import MIPRE.Foundations.StateDistance
import MIPRE.Foundations.PVM
import MIPRE.Foundations.POVMValue
import MIPRE.Foundations.OpBound
import MIPRE.LCS.MagicSquare.Game

/-!
# Direct Magic Square anticommutation

Blueprint `lem:ms-direct-anticomm`: a strategy failing the Magic Square game with probability
`ε` has `‖{B₁, B₅}|ψ⟩‖² ≤ 186624 ε` for the *original* `±1`-observables of the two players ---
no isometry, no projectivity, no extracted EPR pairs. This is the only thing the Pauli basis
test consumes from the Magic Square, and it is much weaker than the full rigidity theorem
`thm:ms-rigidity`, which this repository does not prove.

## The shape of the argument

Alice's constraint answers are **repaired** to parity-valid ones and pushed forward to a POVM
with four outcomes (`repPOVM`), then **dilated** to a projective measurement on one shared
ancilla (`MIPRE.exists_projective_dilation`). Signed sums of that measurement are reflections
that commute within a constraint and multiply to its sign *exactly*
(`MIPRE.pvmObs_mul_mul`) --- that is what the dilation buys, and it is why the repair has to
happen first.

The rest is norm bookkeeping on the dilated state, in the operator-bound calculus of
`MIPRE/Foundations/OpBound.lean`: each of Alice's reflections is within `γ` of the
corresponding Bob observable, `γ² ≤ 144 ε`; a Bob word of length `t` can be replaced by the
reversed word of Alice reflections at cost `t γ`; a within-constraint relation costs `3 γ`; and
the six-step path through the six constraints turns `d a e b` into `- d e a b` at cost `24 γ`.
-/

noncomputable section

namespace MIPRE.QLD.MS

open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder

/-! ## Alice's repaired outcomes

A parity-valid answer to a constraint is determined by its bits at the first two cells, so the
repaired outcome set is `ZMod 2 × ZMod 2` and the bit at the third cell is read off the
constraint's right-hand side. -/

/-- The repaired outcome set of a constraint. -/
abbrev PV : Type := ZMod 2 × ZMod 2

/-- The bit that outcome `k` assigns to cell `j` of constraint `c`. -/
def pvBit (c : Fin layout.r) (k : PV) (j : Fin 3) : ZMod 2 :=
  if j = 0 then k.1 else if j = 1 then k.2 else game.b c + k.1 + k.2

theorem pvBit_sum (c : Fin layout.r) (k : PV) :
    pvBit c k 0 + pvBit c k 1 + pvBit c k 2 = game.b c := by
  revert c k
  decide

/-- The sign weighting of constraint `c` at its `j`-th cell. -/
def csgn (c : Fin layout.r) (j : Fin 3) : PV → ℂ := fun k => sgn (pvBit c k j)

theorem csgn_mul_self (c : Fin layout.r) (j : Fin 3) (k : PV) :
    csgn c j k * csgn c j k = 1 := sgn_mul_self _

theorem star_csgn (c : Fin layout.r) (j : Fin 3) (k : PV) :
    star (csgn c j k) = csgn c j k := star_sgn _

/-- **The three signs of a constraint multiply to its sign.** -/
theorem csgn_prod (c : Fin layout.r) (k : PV) :
    csgn c 0 k * csgn c 1 k * csgn c 2 k = sgn (game.b c) := by
  rw [csgn, csgn, csgn, ← sgn_add, ← sgn_add, pvBit_sum]

/-! ## The repaired and dilated Alice measurement -/

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- Alice's answer to a constraint, **repaired** to a parity-valid outcome: an assignment
satisfying the constraint keeps its bits at the first two cells, and everything else --- an
assignment violating the parity, or an answer of the wrong shape --- is sent to `(0, 0)`. This
preserves every originally winning pair, which is all the argument needs. -/
def rep (c : Fin layout.r) : layout.Answer → PV
  | .inl a => if (∑ k ∈ layout.V c, a k) = game.b c then (a (cell c 0), a (cell c 1)) else (0, 0)
  | .inr _ => (0, 0)

/-- **On a parity-valid answer the repair loses nothing**: the outcome's bit at each cell is the
answer's. For the third cell this is the parity condition. -/
theorem pvBit_rep (c : Fin layout.r) {a : Fin layout.s → ZMod 2}
    (ha : (∑ k ∈ layout.V c, a k) = game.b c) (j : Fin 3) :
    pvBit c (rep c (Sum.inl a)) j = a (cell c j) := by
  have hrep : rep c (Sum.inl a) = (a (cell c 0), a (cell c 1)) := by
    rw [rep, if_pos ha]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [hrep]
  fin_cases j
  · rfl
  · rfl
  · show game.b c + a (cell c 0) + a (cell c 1) = a (cell c 2)
    rw [← ha, sum_cells, show a (cell c 0) + a (cell c 1) + a (cell c 2) + a (cell c 0)
        + a (cell c 1) = (a (cell c 0) + a (cell c 0))
          + ((a (cell c 1) + a (cell c 1)) + a (cell c 2)) from by ring,
      h2, h2, zero_add, zero_add]

/-- Alice's repaired constraint POVM, with the four parity-valid outcomes. -/
def repPOVM (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r) (k : PV) :
    Matrix dA dA ℂ :=
  ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k}, ((MA (Sum.inl c)).mats d).val

theorem repPOVM_eq (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r) (k : PV) :
    repPOVM MA c k
      = ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k},
          ((MA (Sum.inl c)).mats d).val := rfl

theorem repPOVM_nonneg (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r)
    (k : PV) : (0 : Matrix dA dA ℂ) ≤ repPOVM MA c k :=
  Finset.sum_nonneg fun d _ => Subtype.coe_le_coe.mpr ((MA (Sum.inl c)).nonneg d)

theorem repPOVM_posSemidef (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r)
    (k : PV) : (repPOVM MA c k).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (repPOVM_nonneg MA c k)

theorem sum_repPOVM (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r) :
    ∑ k, repPOVM MA c k = (1 : Matrix dA dA ℂ) := by
  classical
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => repPOVM_eq MA c k,
    Finset.sum_fiberwise (univ : Finset layout.Answer) (rep c)
      fun d => ((MA (Sum.inl c)).mats d).val]
  exact POVM.sum_val _

/-- The fixed ancilla embedding of Alice's space. -/
def emb (dA : Type) [DecidableEq dA] : Matrix (dA × PV) dA ℂ := ancillaEmbed dA ((0, 0) : PV)

theorem emb_isometry (dA : Type) [Fintype dA] [DecidableEq dA] :
    (emb dA)ᴴ * emb dA = (1 : Matrix dA dA ℂ) := ancillaEmbed_isometry _

/-- **The dilated Alice measurement.** For each constraint, a projective measurement on
`dA × PV` whose compression by the *fixed* ancilla embedding is the repaired POVM. The
embedding not depending on the constraint is what lets all six act on one state, and it is why
`MIPRE.exists_projective_dilation` has to extend the dilating isometry to a unitary. -/
structure Dilated (MA : layout.Question → POVM layout.Answer dA) where
  /-- The projective measurement at each constraint. -/
  P : Fin layout.r → PV → Matrix (dA × PV) (dA × PV) ℂ
  /-- Each is a projective measurement. -/
  isPVM : ∀ c, IsPVM (P c)
  /-- Each compresses to the repaired POVM, along the same embedding. -/
  compress : ∀ c k, (emb dA)ᴴ * (P c k * emb dA) = repPOVM MA c k

theorem nonempty_dilated (MA : layout.Question → POVM layout.Answer dA) :
    Nonempty (Dilated MA) := by
  obtain ⟨P, hsa, hidem, hsum, hcomp⟩ := exists_projective_dilation ((0, 0) : PV)
    (E := repPOVM MA) (fun c k => repPOVM_posSemidef MA c k) (sum_repPOVM MA)
  exact ⟨{ P := P
           isPVM := fun c => ⟨fun k => by
              rw [← Matrix.star_eq_conjTranspose]; exact hsa c k, hidem c, hsum c⟩
           compress := hcomp }⟩

/-! ## Alice's reflections -/

variable {MA : layout.Question → POVM layout.Answer dA}

/-- Alice's reflection for constraint `c` at its `j`-th cell. -/
def refl (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    Matrix (dA × PV) (dA × PV) ℂ :=
  pvmObs (D.P c) (csgn c j)

theorem refl_conjTranspose (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    (refl D c j)ᴴ = refl D c j :=
  pvmObs_isSelfAdjoint (D.isPVM c) fun k => star_csgn c j k

theorem refl_mul_self (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    refl D c j * refl D c j = 1 :=
  pvmObs_mul_self (D.isPVM c) fun k => csgn_mul_self c j k

theorem refl_comm (D : Dilated MA) (c : Fin layout.r) (i j : Fin 3) :
    refl D c i * refl D c j = refl D c j * refl D c i :=
  pvmObs_comm (D.isPVM c) _ _

/-- **The three reflections of a constraint multiply to its sign, exactly.** -/
theorem refl_prod (D : Dilated MA) (c : Fin layout.r) :
    refl D c 0 * refl D c 1 * refl D c 2 = sgn (game.b c) • 1 :=
  pvmObs_mul_mul (D.isPVM c) fun k => csgn_prod c k

/-! ## Numerals for the magic square -/

/-- Variable `k`, in row-major order. -/
def var (k : ℕ) (h : k < layout.s := by decide) : Fin layout.s := ⟨k, h⟩

/-- Constraint `c`: the three rows then the three columns. -/
def con (c : ℕ) (h : c < layout.r := by decide) : Fin layout.r := ⟨c, h⟩

/-! ## The dilated state -/

/-- The state, with Alice's ancilla adjoined in its initial state. -/
def dst (ψ : dA × dB → ℂ) : (dA × PV) × dB → ℂ :=
  ((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ

theorem norm_dst (ψ : dA × dB → ℂ) : ‖evec (dst ψ)‖ = ‖evec ψ‖ := by
  refine norm_evec_mulVec_eq ?_ ψ
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    emb_isometry, Matrix.one_mul, Matrix.one_kronecker_one]

theorem norm_dst_eq_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec (dst ψ)‖ = 1 := by
  rw [norm_dst]
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]

/-! ## Bob's observables and Alice's reflections, on the product space -/

/-- Bob's `±1`-observable at variable `j`: the difference of the two bit outcomes. Answers of
the wrong shape contribute zero, which is exactly the paper's convention. -/
def bobs (MB : layout.Question → POVM layout.Answer dB) (j : Fin layout.s) :
    Matrix dB dB ℂ :=
  ((MB (Sum.inr j)).mats (Sum.inr 0)).val - ((MB (Sum.inr j)).mats (Sum.inr 1)).val

variable {MB : layout.Question → POVM layout.Answer dB}

theorem bobs_conjTranspose (j : Fin layout.s) : (bobs MB j)ᴴ = bobs MB j :=
  POVM.sub_conjTranspose _ _ _

theorem bnd_bobs (j : Fin layout.s) :
    Bnd (bOp (bobs MB j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 := by
  refine bnd_bOp ?_
  rw [bobs_conjTranspose]
  exact POVM.sub_mul_self_le_one _ _ _

variable {MA : layout.Question → POVM layout.Answer dA}

theorem alice_isometry (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    ((aOp (refl D c j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ))ᴴ * aOp (refl D c j) = 1 := by
  refine isometry_aOp ?_
  rw [refl_conjTranspose]
  exact refl_mul_self D c j

theorem bnd_alice (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    Bnd (aOp (refl D c j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 :=
  bnd_one_of_isometry (alice_isometry D c j)

/-- **The three reflections of a constraint, in the form the relations use**: the product of the
first two is the constraint's sign times the third. -/
theorem refl_two_eq (D : Dilated MA) (c : Fin layout.r) :
    refl D c 0 * refl D c 1 = sgn (game.b c) • refl D c 2 := by
  have h := refl_prod D c
  calc refl D c 0 * refl D c 1 = refl D c 0 * refl D c 1 * refl D c 2 * refl D c 2 := by
        rw [mul_assoc (refl D c 0 * refl D c 1), refl_mul_self, mul_one]
    _ = (sgn (game.b c) • (1 : Matrix (dA × PV) (dA × PV) ℂ)) * refl D c 2 := by rw [h]
    _ = sgn (game.b c) • refl D c 2 := by rw [Matrix.smul_mul, Matrix.one_mul]

/-! ## The distance between two of Bob's operators on the state -/

/-- `‖(X - Y) ⊗ Id |ψ'⟩‖`, the quantity every step of the word argument estimates. -/
def dd (ψ : dA × dB → ℂ) (X Y : Matrix dB dB ℂ) : ℝ :=
  snorm (dst ψ) (bOp X - bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)

theorem dd_comm (ψ : dA × dB → ℂ) (X Y : Matrix dB dB ℂ) : dd ψ X Y = dd ψ Y X :=
  snorm_sub_comm _ _ _

theorem dd_nonneg (ψ : dA × dB → ℂ) (X Y : Matrix dB dB ℂ) : 0 ≤ dd ψ X Y := snorm_nonneg _ _

theorem dd_triangle (ψ : dA × dB → ℂ) (X Y Z : Matrix dB dB ℂ) :
    dd ψ X Z ≤ dd ψ X Y + dd ψ Y Z := by
  have h : (bOp X - bOp Z : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = (bOp X - bOp Y) + (bOp Y - bOp Z) := by abel
  rw [dd, h]
  exact snorm_add_le _ _ _

/-- Negating both sides changes nothing. -/
theorem dd_neg (ψ : dA × dB → ℂ) (X Y : Matrix dB dB ℂ) : dd ψ (-X) (-Y) = dd ψ X Y := by
  have h : (bOp (-X) - bOp (-Y) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = (-1 : ℂ) • (bOp X - bOp Y) := by
    rw [show (-X) = (-1 : ℂ) • X from by module, show (-Y) = (-1 : ℂ) • Y from by module,
      bOp_smul, bOp_smul]
    module
  rw [dd, dd, h, snorm_smul]
  norm_num

/-! ## Replacing Bob's letters by Alice's reflections

A Bob word of length `t` agrees on the state with the *reversed* word of Alice reflections to
within `t γ`: replace the letters one at a time from the right, each replacement costing `γ`,
and cross the tensor factors so the Alice letters accumulate in the opposite order. Only lengths
one, two and three occur in the argument, so the three cases are spelled out rather than
induced. -/

section Words

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

/-- A product of Bob observables is a contraction. -/
theorem bnd_bobs_mul (X Y : Matrix dB dB ℂ)
    (hX : Bnd (bOp X : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1)
    (hY : Bnd (bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1) :
    Bnd (bOp (X * Y) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 := by
  rw [bOp_mul]
  simpa using Bnd.mul (by norm_num : (0:ℝ) ≤ 1) hX hY

theorem word1 (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) (j : Fin 3) :
    snorm (dst ψ) (bOp (bobs MB (cell c j)) - aOp (refl D c j)) ≤ γ := by
  rw [snorm_sub_comm]
  exact hγ c j

theorem word2 (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c c' : Fin layout.r) (i j : Fin 3) :
    snorm (dst ψ) (bOp (bobs MB (cell c i) * bobs MB (cell c' j))
      - aOp (refl D c' j * refl D c i)) ≤ 2 * γ := by
  have h1 : (aOp (refl D c' j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * bOp (bobs MB (cell c i)) = bOp (bobs MB (cell c i)) * aOp (refl D c' j) :=
    aOp_mul_bOp _ _
  have hsplit : (bOp (bobs MB (cell c i) * bobs MB (cell c' j))
        - aOp (refl D c' j * refl D c i) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = bOp (bobs MB (cell c i)) * (bOp (bobs MB (cell c' j)) - aOp (refl D c' j))
        + aOp (refl D c' j) * (bOp (bobs MB (cell c i)) - aOp (refl D c i)) := by
    rw [bOp_mul, aOp_mul, mul_sub, mul_sub, h1]
    abel
  rw [hsplit]
  refine le_trans (snorm_add_le _ _ _) ?_
  have hb := snorm_mul_le (dst ψ) (bnd_bobs (dA := dA) (MB := MB) (cell c i))
    (bOp (bobs MB (cell c' j)) - aOp (refl D c' j))
  have ha := snorm_mul_le (dst ψ) (bnd_alice (dB := dB) D c' j)
    (bOp (bobs MB (cell c i)) - aOp (refl D c i))
  have hw1 := word1 hγ c' j
  have hw2 := word1 hγ c i
  linarith

theorem word3 (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c c' c'' : Fin layout.r) (i j k : Fin 3) :
    snorm (dst ψ) (bOp (bobs MB (cell c i) * bobs MB (cell c' j) * bobs MB (cell c'' k))
      - aOp (refl D c'' k * (refl D c' j * refl D c i))) ≤ 3 * γ := by
  have hcomm : (aOp (refl D c'' k) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * bOp (bobs MB (cell c i) * bobs MB (cell c' j))
      = bOp (bobs MB (cell c i) * bobs MB (cell c' j)) * aOp (refl D c'' k) :=
    aOp_mul_bOp _ _
  have hsplit : (bOp (bobs MB (cell c i) * bobs MB (cell c' j) * bobs MB (cell c'' k))
        - aOp (refl D c'' k * (refl D c' j * refl D c i))
          : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = bOp (bobs MB (cell c i) * bobs MB (cell c' j))
          * (bOp (bobs MB (cell c'' k)) - aOp (refl D c'' k))
        + aOp (refl D c'' k)
          * (bOp (bobs MB (cell c i) * bobs MB (cell c' j))
              - aOp (refl D c' j * refl D c i)) := by
    rw [bOp_mul (bobs MB (cell c i) * bobs MB (cell c' j)), aOp_mul (refl D c'' k), mul_sub,
      mul_sub, hcomm]
    abel
  rw [hsplit]
  refine le_trans (snorm_add_le _ _ _) ?_
  have hbb := bnd_bobs_mul (dA := dA) (bobs MB (cell c i)) (bobs MB (cell c' j))
    (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have hb := snorm_mul_le (dst ψ) hbb (bOp (bobs MB (cell c'' k)) - aOp (refl D c'' k))
  have ha := snorm_mul_le (dst ψ) (bnd_alice (dB := dB) D c'' k)
    (bOp (bobs MB (cell c i) * bobs MB (cell c' j)) - aOp (refl D c' j * refl D c i))
  have hw1 := word1 hγ c'' k
  have hw2 := word2 hγ c c' i j
  linarith

end Words

/-! ## Rewriting inside a word -/

section Rewrites

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

theorem refl_isometry (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    (refl D c j)ᴴ * refl D c j = 1 := by
  rw [refl_conjTranspose]
  exact refl_mul_self D c j

theorem isometry_mul {X Y : Matrix (dA × PV) (dA × PV) ℂ} (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1) :
    (X * Y)ᴴ * (X * Y) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc Yᴴ * Xᴴ * (X * Y) = Yᴴ * (Xᴴ * X) * Y := by simp only [mul_assoc]
    _ = Yᴴ * Y := by rw [hX, mul_one]
    _ = 1 := hY

/-- A Bob prefix does not increase the distance. -/
theorem dd_prefix {P : Matrix dB dB ℂ}
    (hP : Bnd (bOp P : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1) (X Y : Matrix dB dB ℂ) :
    dd ψ (P * X) (P * Y) ≤ dd ψ X Y := by
  have h : (bOp (P * X) - bOp (P * Y) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = bOp P * (bOp X - bOp Y) := by rw [bOp_mul, bOp_mul, mul_sub]
  rw [dd, h]
  have := snorm_mul_le (dst ψ) hP (bOp X - bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
  rw [one_mul] at this
  exact this

/-- **Appending a Bob suffix costs twice its replacement cost.** -/
theorem dd_suffix {X Y W : Matrix dB dB ℂ} {XD : Matrix (dA × PV) (dA × PV) ℂ} {δ : ℝ}
    (hX : Bnd (bOp X : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1)
    (hY : Bnd (bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1)
    (hXD : XDᴴ * XD = 1)
    (hδ : snorm (dst ψ) (bOp W - aOp XD) ≤ δ) :
    dd ψ (X * W) (Y * W) ≤ dd ψ X Y + 2 * δ := by
  have hZ : Bnd (bOp X - bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 2 := by
    have h := Bnd.sub hX hY
    rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
    exact h
  have hcomm : (aOp XD : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) * (bOp X - bOp Y)
      = (bOp X - bOp Y) * aOp XD := by
    rw [mul_sub, sub_mul, aOp_mul_bOp, aOp_mul_bOp]
  have h : (bOp (X * W) - bOp (Y * W) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = (bOp X - bOp Y) * bOp W := by rw [bOp_mul, bOp_mul, sub_mul]
  rw [dd, h]
  exact snorm_mul_swap (dst ψ) (isometry_aOp hXD) hcomm hZ (by norm_num) hδ

/-- **A within-constraint relation costs `3 γ`.** The two Bob letters are transported to the
constraint's two Alice reflections, which costs `2 γ`; their product *is* the third reflection
times the constraint's sign, with no error; and that reflection is returned to Bob for a
further `γ`. -/
theorem relation_core
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) (i j : Fin 3)
    (hij : refl D c j * refl D c i = sgn (game.b c) • refl D c 2) :
    dd ψ (bobs MB (cell c i) * bobs MB (cell c j)) (sgn (game.b c) • bobs MB (cell c 2))
      ≤ 3 * γ := by
  have h1 := word2 hγ c c i j
  rw [hij] at h1
  have h2 : snorm (dst ψ) (aOp (sgn (game.b c) • refl D c 2)
      - bOp (sgn (game.b c) • bobs MB (cell c 2))) ≤ γ := by
    rw [aOp_smul, bOp_smul, ← smul_sub, snorm_smul, norm_sgn, one_mul]
    exact hγ c 2
  have hsplit : (bOp (bobs MB (cell c i) * bobs MB (cell c j))
        - bOp (sgn (game.b c) • bobs MB (cell c 2))
          : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = (bOp (bobs MB (cell c i) * bobs MB (cell c j)) - aOp (sgn (game.b c) • refl D c 2))
        + (aOp (sgn (game.b c) • refl D c 2)
            - bOp (sgn (game.b c) • bobs MB (cell c 2))) := by
    abel
  rw [dd, hsplit]
  refine le_trans (snorm_add_le _ _ _) ?_
  linarith

theorem relation10
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) :
    dd ψ (bobs MB (cell c 1) * bobs MB (cell c 0)) (sgn (game.b c) • bobs MB (cell c 2))
      ≤ 3 * γ :=
  relation_core hγ c 1 0 (refl_two_eq D c)

theorem relation01
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) :
    dd ψ (bobs MB (cell c 0) * bobs MB (cell c 1)) (sgn (game.b c) • bobs MB (cell c 2))
      ≤ 3 * γ :=
  relation_core hγ c 0 1 (by rw [refl_comm]; exact refl_two_eq D c)

end Rewrites

/-! ## The six-step path

`d a e b` becomes `- d e a b` by applying the six constraints in turn --- column one, column
two, row three, column three, row two, row one --- at a total cost of `24 γ`. The sign appears
exactly once, at column three, which is the constraint of product `-1`. -/

section Path

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

/-- **The six-step path.** -/
theorem path (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ) :
    dd ψ (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1)))
      (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1)))) ≤ 24 * γ := by
  have c00 : cell (con 0) 0 = var 0 := rfl
  have c01 : cell (con 0) 1 = var 1 := rfl
  have c02 : cell (con 0) 2 = var 2 := rfl
  have c10 : cell (con 1) 0 = var 3 := rfl
  have c11 : cell (con 1) 1 = var 4 := rfl
  have c12 : cell (con 1) 2 = var 5 := rfl
  have c20 : cell (con 2) 0 = var 6 := rfl
  have c21 : cell (con 2) 1 = var 7 := rfl
  have c22 : cell (con 2) 2 = var 8 := rfl
  have c30 : cell (con 3) 0 = var 0 := rfl
  have c31 : cell (con 3) 1 = var 3 := rfl
  have c32 : cell (con 3) 2 = var 6 := rfl
  have c40 : cell (con 4) 0 = var 1 := rfl
  have c41 : cell (con 4) 1 = var 4 := rfl
  have c42 : cell (con 4) 2 = var 7 := rfl
  have c50 : cell (con 5) 0 = var 2 := rfl
  have c51 : cell (con 5) 1 = var 5 := rfl
  have c52 : cell (con 5) 2 = var 8 := rfl
  have hb0 : game.b (con 0) = 0 := by decide
  have hb1 : game.b (con 1) = 0 := by decide
  have hb2 : game.b (con 2) = 0 := by decide
  have hb3 : game.b (con 3) = 0 := by decide
  have hb4 : game.b (con 4) = 0 := by decide
  have hb5 : game.b (con 5) = 1 := by decide
  have hb34 : Bnd (bOp (bobs MB (var 3) * bobs MB (var 4)) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 :=
    bnd_bobs_mul (dA := dA) _ _ (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have hb30 : Bnd (bOp (bobs MB (var 3) * bobs MB (var 0)) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 :=
    bnd_bobs_mul (dA := dA) _ _ (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  -- the six within-constraint relations
  have r3 : dd ψ (bobs MB (var 3) * bobs MB (var 0)) (bobs MB (var 6)) ≤ 3 * γ := by
    have h := relation10 hγ (con 3)
    rw [c31, c30, c32, hb3, sgn_zero, one_smul] at h
    exact h
  have r4 : dd ψ (bobs MB (var 4) * bobs MB (var 1)) (bobs MB (var 7)) ≤ 3 * γ := by
    have h := relation10 hγ (con 4)
    rw [c41, c40, c42, hb4, sgn_zero, one_smul] at h
    exact h
  have r2 : dd ψ (bobs MB (var 6) * bobs MB (var 7)) (bobs MB (var 8)) ≤ 3 * γ := by
    have h := relation01 hγ (con 2)
    rw [c20, c21, c22, hb2, sgn_zero, one_smul] at h
    exact h
  have r5 : dd ψ (bobs MB (var 5) * bobs MB (var 2)) (-bobs MB (var 8)) ≤ 3 * γ := by
    have h := relation10 hγ (con 5)
    rw [c51, c50, c52, hb5, sgn_one, neg_one_smul] at h
    exact h
  have r1 : dd ψ (bobs MB (var 5)) (bobs MB (var 3) * bobs MB (var 4)) ≤ 3 * γ := by
    have h := relation01 hγ (con 1)
    rw [c10, c11, c12, hb1, sgn_zero, one_smul] at h
    rw [dd_comm]
    exact h
  have r0 : dd ψ (bobs MB (var 2)) (bobs MB (var 0) * bobs MB (var 1)) ≤ 3 * γ := by
    have h := relation01 hγ (con 0)
    rw [c00, c01, c02, hb0, sgn_zero, one_smul] at h
    rw [dd_comm]
    exact h
  -- step 1: `d a e b` to `g e b`, with the suffix `e b`
  have s1 : dd ψ (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) ≤ 7 * γ := by
    have hsuf := word2 hγ (con 4) (con 4) 1 0
    rw [c41, c40] at hsuf
    have h := dd_suffix (ψ := ψ) (X := bobs MB (var 3) * bobs MB (var 0)) (Y := bobs MB (var 6)) (W := bobs MB (var 4) * bobs MB (var 1))
      hb30 (bnd_bobs (dA := dA) (MB := MB) _)
      (isometry_mul (refl_isometry D (con 4) 0) (refl_isometry D (con 4) 1)) hsuf
    linarith
  -- step 2: `g e b` to `g h`, behind the prefix `g`
  have s2 : dd ψ (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * bobs MB (var 7)) ≤ 3 * γ := by
    have h := dd_prefix (ψ := ψ) (P := bobs MB (var 6)) (bnd_bobs (dA := dA) (MB := MB) _) (bobs MB (var 4) * bobs MB (var 1)) (bobs MB (var 7))
    linarith
  -- step 3: `g h` to `i`
  have s3 : dd ψ (bobs MB (var 6) * bobs MB (var 7)) (bobs MB (var 8)) ≤ 3 * γ := r2
  -- step 4: `i` to `- f c`, the one constraint of product `-1`
  have s4 : dd ψ (bobs MB (var 8)) (-(bobs MB (var 5) * bobs MB (var 2))) ≤ 3 * γ := by
    rw [dd_comm]
    have h := dd_neg ψ (bobs MB (var 5) * bobs MB (var 2)) (-bobs MB (var 8))
    rw [neg_neg] at h
    rw [h]
    exact r5
  -- step 5: `- f c` to `- d e c`, with the suffix `c`
  have s5 : dd ψ (-(bobs MB (var 5) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * bobs MB (var 2))) ≤ 5 * γ := by
    have hw := word1 hγ (con 0) 2
    rw [c02] at hw
    have h := dd_suffix (ψ := ψ) (X := bobs MB (var 5)) (Y := bobs MB (var 3) * bobs MB (var 4)) (W := bobs MB (var 2))
      (bnd_bobs (dA := dA) (MB := MB) _) hb34 (refl_isometry D (con 0) 2) hw
    rw [dd_neg]
    linarith
  -- step 6: `- d e c` to `- d e a b`, behind the prefix `d e`
  have s6 : dd ψ (-(bobs MB (var 3) * bobs MB (var 4) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1)))) ≤ 3 * γ := by
    have h := dd_prefix (ψ := ψ) (P := bobs MB (var 3) * bobs MB (var 4)) hb34 (bobs MB (var 2)) (bobs MB (var 0) * bobs MB (var 1))
    rw [dd_neg]
    linarith
  -- chain the six steps
  have t1 := dd_triangle ψ (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t2 := dd_triangle ψ (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * bobs MB (var 7)) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t3 := dd_triangle ψ (bobs MB (var 6) * bobs MB (var 7)) (bobs MB (var 8)) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t4 := dd_triangle ψ (bobs MB (var 8)) (-(bobs MB (var 5) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t5 := dd_triangle ψ (-(bobs MB (var 5) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  linarith

end Path


/-! ## Removing the two outer letters

The path bounds `‖d (a e + e a) b |ψ'⟩‖`. Removing `d` costs the non-projectivity of `b_3`,
which is `‖(Id - b_3²) W |ψ'⟩‖ ≤ (2 + t) γ` for a word of length `t`; removing `b` costs `2 γ`,
because Alice's reflection for variable `1` is unitary and commutes with the anticommutator. -/

section Final

variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

/-- `{B₀, B₄}`, the anticommutator the Pauli basis test consumes. -/
def anti (MB : layout.Question → POVM layout.Answer dB) : Matrix dB dB ℂ :=
  bobs MB (var 0) * bobs MB (var 4) + bobs MB (var 4) * bobs MB (var 0)

theorem bnd_anti :
    Bnd (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 2 := by
  rw [anti, bOp_add]
  have h1 := bnd_bobs_mul (dA := dA) (bobs MB (var 0)) (bobs MB (var 4))
    (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have h2 := bnd_bobs_mul (dA := dA) (bobs MB (var 4)) (bobs MB (var 0))
    (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have h := Bnd.add h1 h2
  rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
  exact h

/-- **`Id - b²` is a contraction**, because `0 ≤ b² ≤ 1`. -/
theorem bnd_one_sub_sq (j : Fin layout.s) :
    Bnd (bOp (1 - bobs MB j * bobs MB j)
      : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 := by
  have hy0 : (0 : Matrix dB dB ℂ) ≤ bobs MB j * bobs MB j := by
    have h : bobs MB j * bobs MB j = (bobs MB j)ᴴ * bobs MB j := by rw [bobs_conjTranspose]
    rw [h]
    exact Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self _)
  have hy1 : bobs MB j * bobs MB j ≤ (1 : Matrix dB dB ℂ) := POVM.sub_mul_self_le_one _ _ _
  have h0 : (0 : Matrix dB dB ℂ) ≤ 1 - bobs MB j * bobs MB j := sub_nonneg.mpr hy1
  have h1 : (1 : Matrix dB dB ℂ) - bobs MB j * bobs MB j ≤ 1 := sub_le_self _ hy0
  refine bnd_bOp ?_
  have hsa : ((1 : Matrix dB dB ℂ) - bobs MB j * bobs MB j)ᴴ
      = 1 - bobs MB j * bobs MB j := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      bobs_conjTranspose]
  rw [hsa]
  exact le_trans (mul_self_le_of_le_one h0 h1) h1

/-- **`‖(Id - b²)|ψ'⟩‖ ≤ 2 γ`**, from `Id - b² = (D + b)(D - b)` across the two factors. -/
theorem snorm_one_sub_sq (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j)
      - bOp (bobs MB (cell c j))) ≤ γ) (c : Fin layout.r) (j : Fin 3) :
    snorm (dst ψ) (bOp (1 - bobs MB (cell c j) * bobs MB (cell c j))) ≤ 2 * γ := by
  have hcomm : (aOp (refl D c j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * bOp (bobs MB (cell c j)) = bOp (bobs MB (cell c j)) * aOp (refl D c j) :=
    aOp_mul_bOp _ _
  have hfac : (bOp (1 - bobs MB (cell c j) * bobs MB (cell c j))
        : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = (aOp (refl D c j) + bOp (bobs MB (cell c j)))
        * (aOp (refl D c j) - bOp (bobs MB (cell c j))) := by
    rw [bOp_sub, bOp_one, bOp_mul, add_mul, mul_sub, mul_sub, hcomm, ← aOp_mul,
      refl_mul_self, aOp_one]
    abel
  rw [hfac]
  have hb : Bnd ((aOp (refl D c j) + bOp (bobs MB (cell c j))
      : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)) 2 := by
    have h := Bnd.add (bnd_alice (dB := dB) D c j) (bnd_bobs (dA := dA) (MB := MB) (cell c j))
    rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
    exact h
  refine le_trans (snorm_mul_le (dst ψ) hb _) ?_
  exact mul_le_mul_of_nonneg_left (hγ c j) (by norm_num)

/-- **The anticommutator is within `36 γ` of zero on the state.** -/
theorem snorm_anti
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ) :
    snorm (dst ψ) (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 36 * γ := by
  have c02 : cell (con 0) 2 = var 2 := rfl
  have c10 : cell (con 1) 0 = var 3 := rfl
  have c11 : cell (con 1) 1 = var 4 := rfl
  have c40 : cell (con 4) 0 = var 1 := rfl
  have c41 : cell (con 4) 1 = var 4 := rfl
  have c30 : cell (con 3) 0 = var 0 := rfl
  -- the word `T = (a e + e a) b`
  set T : Matrix dB dB ℂ := anti MB * bobs MB (var 1) with hT
  -- step A: the path, rearranged
  have hA : snorm (dst ψ) (bOp (bobs MB (var 3) * T)
      : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 24 * γ := by
    have h := path hγ
    rw [dd] at h
    rw [show (bOp (bobs MB (var 3) * T) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
        = bOp (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1)))
          - bOp (-(bobs MB (var 3) * bobs MB (var 4)
              * (bobs MB (var 0) * bobs MB (var 1)))) from by
      rw [← bOp_sub]
      congr 1
      rw [hT, anti]
      noncomm_ring]
    exact h
  -- step B: the two length-three words, with `Id - b₃²` in front
  have hB : snorm (dst ψ) (bOp ((1 - bobs MB (var 3) * bobs MB (var 3)) * T)
      : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 10 * γ := by
    have hz := snorm_one_sub_sq (D := D) hγ (con 1) 0
    rw [c10] at hz
    have hzb := bnd_one_sub_sq (dA := dA) (MB := MB) (var 3)
    have hstep : ∀ (X Y Z : Matrix dB dB ℂ) (cX cY cZ : Fin layout.r) (iX iY iZ : Fin 3),
        X = bobs MB (cell cX iX) → Y = bobs MB (cell cY iY) → Z = bobs MB (cell cZ iZ) →
        snorm (dst ψ) (bOp ((1 - bobs MB (var 3) * bobs MB (var 3)) * (X * Y * Z))
          : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 5 * γ := by
      intro X Y Z cX cY cZ iX iY iZ hX hY hZ
      subst hX; subst hY; subst hZ
      have hw := word3 hγ cX cY cZ iX iY iZ
      have hcomm : (aOp (refl D cZ iZ * (refl D cY iY * refl D cX iX))
            : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
          * bOp (1 - bobs MB (var 3) * bobs MB (var 3))
          = bOp (1 - bobs MB (var 3) * bobs MB (var 3))
            * aOp (refl D cZ iZ * (refl D cY iY * refl D cX iX)) := aOp_mul_bOp _ _
      have hiso := isometry_mul (refl_isometry D cZ iZ)
        (isometry_mul (refl_isometry D cY iY) (refl_isometry D cX iX))
      have h := snorm_mul_swap (dst ψ) (isometry_aOp hiso) hcomm hzb (by norm_num) hw
      rw [← bOp_mul] at h
      linarith
    have h1 := hstep (bobs MB (var 0)) (bobs MB (var 4)) (bobs MB (var 1))
      (con 3) (con 1) (con 4) 0 1 0 (congrArg (bobs MB) c30.symm)
      (congrArg (bobs MB) c11.symm) (congrArg (bobs MB) c40.symm)
    have h2 := hstep (bobs MB (var 4)) (bobs MB (var 0)) (bobs MB (var 1))
      (con 1) (con 3) (con 4) 1 0 0 (congrArg (bobs MB) c11.symm)
      (congrArg (bobs MB) c30.symm) (congrArg (bobs MB) c40.symm)
    have hsplit : ((1 : Matrix dB dB ℂ) - bobs MB (var 3) * bobs MB (var 3)) * T
        = (1 - bobs MB (var 3) * bobs MB (var 3))
            * (bobs MB (var 0) * bobs MB (var 4) * bobs MB (var 1))
          + (1 - bobs MB (var 3) * bobs MB (var 3))
            * (bobs MB (var 4) * bobs MB (var 0) * bobs MB (var 1)) := by
      rw [hT, anti]
      noncomm_ring
    rw [hsplit, bOp_add]
    refine le_trans (snorm_add_le _ _ _) ?_
    linarith
  -- step C: `T` itself
  have hC : snorm (dst ψ) (bOp T : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      ≤ 34 * γ := by
    have hsplit : T = (1 - bobs MB (var 3) * bobs MB (var 3)) * T
        + bobs MB (var 3) * (bobs MB (var 3) * T) := by noncomm_ring
    have hlast : snorm (dst ψ) (bOp (bobs MB (var 3) * (bobs MB (var 3) * T))
        : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 24 * γ := by
      rw [bOp_mul]
      refine le_trans (snorm_mul_le (dst ψ) (bnd_bobs (dA := dA) (MB := MB) (var 3)) _) ?_
      rw [one_mul]
      exact hA
    rw [hsplit, bOp_add]
    refine le_trans (snorm_add_le _ _ _) ?_
    linarith
  -- step D: remove the trailing `b`
  have hD2 := hγ (con 4) 0
  rw [c40] at hD2
  have hiso := alice_isometry (dB := dB) D (con 4) 0
  have hcomm : (aOp (refl D (con 4) 0) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * bOp (anti MB) = bOp (anti MB) * aOp (refl D (con 4) 0) := aOp_mul_bOp _ _
  have hrewrite : snorm (dst ψ) (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = snorm (dst ψ) (bOp (anti MB) * aOp (refl D (con 4) 0)) := by
    rw [← hcomm, snorm_mul_of_isometry (dst ψ) hiso]
  have hsplit : (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * aOp (refl D (con 4) 0)
      = bOp T + bOp (anti MB) * (aOp (refl D (con 4) 0) - bOp (bobs MB (var 1))) := by
    rw [mul_sub, hT, bOp_mul]
    abel
  rw [hrewrite, hsplit]
  refine le_trans (snorm_add_le _ _ _) ?_
  have hlast := snorm_mul_le (dst ψ) (bnd_anti (dA := dA) (MB := MB))
    ((aOp (refl D (con 4) 0) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      - bOp (bobs MB (var 1)))
  linarith

end Final

/-! ## From the game's value to the closeness hypothesis

The correlation `⟨ψ'| C_{c,j} ⊗ B_j |ψ'⟩` is agreement minus disagreement between Alice's
repaired outcome bit and Bob's answer bit, and every *winning* answer pair agrees --- that is
what the repair preserves. So the correlation is at least `1 - 2 ℓ_{c,j}`, and since
`δ²_{c,j} = 2 - 2⟨ψ'| C B |ψ'⟩ - (1 - ⟨ψ'| B² |ψ'⟩) ≤ 2 - 2⟨ψ'| C B |ψ'⟩`, the reflection is
within `2√ℓ` of the observable. -/

section Correlation

/-- `(-1)^x` for a bit, as a real. -/
def rsgn (x : ZMod 2) : ℝ := if x.val = 1 then -1 else 1

theorem sgn_eq_rsgn (x : ZMod 2) : sgn x = ((rsgn x : ℝ) : ℂ) := by
  rw [sgn, rsgn]; split_ifs <;> norm_num

theorem val_inj (x y : ZMod 2) (h : x.val = y.val) : x = y := by
  revert x y
  decide

theorem rsgn_mul_eq (x y : ZMod 2) :
    rsgn x * rsgn y = 2 * (if x = y then (1 : ℝ) else 0) - 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hy : y.val < 2 := ZMod.val_lt y
  have hiff : (x = y) ↔ (x.val = y.val) :=
    ⟨fun h => by rw [h], fun h => val_inj x y h⟩
  rw [rsgn, rsgn, show (if x = y then (1 : ℝ) else 0)
      = (if x.val = y.val then (1 : ℝ) else 0) from by
    by_cases h : x = y
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]]
  interval_cases h1 : x.val <;> interval_cases h2 : y.val <;> norm_num

variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}

/-- The signed Born mass at an incidence: Alice's repaired outcome bit against Bob's answer
bit, agreement counting `+1` and disagreement `-1`. -/
def corr (ψ : dA × dB → ℂ) (MA : layout.Question → POVM layout.Answer dA)
    (MB : layout.Question → POVM layout.Answer dB) (c : Fin layout.r) (j : Fin 3) : ℝ :=
  ∑ d : layout.Answer, ∑ w : ZMod 2,
    rsgn (pvBit c (rep c d) j) * rsgn w
      * bornProb ψ (((MA (Sum.inl c)).mats d).val)
          (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val)

/-- The total Born mass on Bob's *bit* answers is at most one. -/
theorem sum_bornProb_inr_le (hψ : star ψ ⬝ᵥ ψ = 1) (c : Fin layout.r) (k : Fin layout.s) :
    ∑ d : layout.Answer, ∑ w : ZMod 2,
      bornProb ψ (((MA (Sum.inl c)).mats d).val) (((MB (Sum.inr k)).mats (Sum.inr w)).val)
      ≤ 1 := by
  rw [← sum_bornProb hψ (MA (Sum.inl c)) (MB (Sum.inr k))]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have h : (0 : ℝ) ≤ ∑ a' : Fin layout.s → ZMod 2,
      bornProb ψ (((MA (Sum.inl c)).mats d).val) (((MB (Sum.inr k)).mats (Sum.inl a')).val) :=
    Finset.sum_nonneg fun a' _ =>
      bornProb_nonneg ψ ((MA (Sum.inl c)).posSemidef d) ((MB (Sum.inr k)).posSemidef _)
  linarith

/-- **Every winning answer pair agrees**, so the accepted mass is at most the agreeing mass. -/
theorem condWin_le_agree (c : Fin layout.r) (j : Fin 3) :
    condWin nonlocalGame ψ MA MB (Sum.inl c) (Sum.inr (cell c j))
      ≤ ∑ d : layout.Answer, ∑ w : ZMod 2,
          (if pvBit c (rep c d) j = w then (1 : ℝ) else 0)
            * bornProb ψ (((MA (Sum.inl c)).mats d).val)
                (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val) := by
  rw [condWin]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have hzero : ∀ a' : Fin layout.s → ZMod 2,
      (if nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inl a') then (1 : ℝ) else 0)
        * bornProb ψ (((MA (Sum.inl c)).mats d).val)
            (((MB (Sum.inr (cell c j))).mats (Sum.inl a')).val) = 0 := by
    intro a'
    have : nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inl a') = false := by
      cases d <;> rfl
    rw [this, if_neg (by simp), zero_mul]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => hzero a', Finset.sum_const_zero, zero_add]
  refine Finset.sum_le_sum fun w _ => ?_
  refine mul_le_mul_of_nonneg_right ?_
    (bornProb_nonneg ψ ((MA (Sum.inl c)).posSemidef d) ((MB _).posSemidef _))
  by_cases hacc : nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inr w)
  · rw [if_pos hacc]
    -- an accepted pair has Alice's answer parity-valid and agreeing with Bob's bit
    have hd : ∃ a : Fin layout.s → ZMod 2, d = Sum.inl a := by
      cases d with
      | inl a => exact ⟨a, rfl⟩
      | inr x => exact absurd hacc (by simp [nonlocalGame, Game.toNonlocalGame, Game.accepts])
    obtain ⟨a, rfl⟩ := hd
    have hacc' : (decide ((cell c j) ∈ layout.V c)
        && decide ((∑ k ∈ layout.V c, a k) = game.b c) && decide (a (cell c j) = w)) = true := by
      simpa [nonlocalGame, Game.toNonlocalGame, Game.accepts] using hacc
    have hpar : (∑ k ∈ layout.V c, a k) = game.b c := by
      simpa using (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hacc').1).2
    have hval : a (cell c j) = w := by
      simpa using (Bool.and_eq_true _ _ |>.mp hacc').2
    rw [if_pos (by rw [pvBit_rep c hpar j, hval])]
  · rw [if_neg hacc]
    split_ifs <;> norm_num

/-- **The correlation is at least `1 - 2 ℓ`.** -/
theorem one_sub_two_mul_condFail_le_corr (hψ : star ψ ⬝ᵥ ψ = 1) (c : Fin layout.r) (j : Fin 3) :
    1 - 2 * condFail nonlocalGame ψ MA MB (Sum.inl c) (Sum.inr (cell c j))
      ≤ corr ψ MA MB c j := by
  set q : layout.Answer → ZMod 2 → ℝ := fun d w =>
    bornProb ψ (((MA (Sum.inl c)).mats d).val)
      (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val) with hq
  have hexp : corr ψ MA MB c j
      = 2 * (∑ d : layout.Answer, ∑ w : ZMod 2,
            (if pvBit c (rep c d) j = w then (1 : ℝ) else 0) * q d w)
        - ∑ d : layout.Answer, ∑ w : ZMod 2, q d w := by
    rw [corr, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rsgn_mul_eq]
    ring
  have hS := sum_bornProb_inr_le (MA := MA) (MB := MB) hψ c (cell c j)
  have hQ := condWin_le_agree (ψ := ψ) (MA := MA) (MB := MB) c j
  rw [hexp, condFail]
  linarith

end Correlation

/-! ## The correlation is the quadratic form -/

section Assemble

variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}

theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ w : ZMod 2, f w = f 0 + f 1 := by
  show ∑ w : Fin 2, f w = f 0 + f 1
  exact Fin.sum_univ_two f

theorem aOp_mul_bOp_eq (X : Matrix (dA × PV) (dA × PV) ℂ) (Y : Matrix dB dB ℂ) :
    (aOp X : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) * bOp Y = X ⊗ₖ Y := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- The quadratic form on the dilated state compresses the Alice factor. -/
theorem qform_dst (X : Matrix (dA × PV) (dA × PV) ℂ) (Y : Matrix dB dB ℂ) :
    qform (dst ψ) (X ⊗ₖ Y) = qform ψ (((emb dA)ᴴ * (X * emb dA)) ⊗ₖ Y) := by
  have hmat : (((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)))ᴴ
      * ((X ⊗ₖ Y) * ((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)))
      = ((emb dA)ᴴ * (X * emb dA)) ⊗ₖ Y := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [qform, qform, dst, Matrix.mulVec_mulVec, star_mulVec_dotProduct, hmat]

/-- **The compression of Alice's reflection is her repaired POVM, signed.** -/
theorem emb_compress_refl (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    (emb dA)ᴴ * (refl D c j * emb dA)
      = ∑ d : layout.Answer, csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val := by
  classical
  have hstep : (emb dA)ᴴ * (refl D c j * emb dA)
      = ∑ k : PV, csgn c j k • repPOVM MA c k := by
    rw [refl, pvmObs, Matrix.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, D.compress c k]
  rw [hstep]
  have hfib : ∀ k : PV, csgn c j k • repPOVM MA c k
      = ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k},
          csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val := by
    intro k
    rw [repPOVM_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [(Finset.mem_filter.mp hd).2]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  exact Finset.sum_fiberwise (univ : Finset layout.Answer) (rep c)
    fun d => csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val

/-- **The correlation is the quadratic form of `C_{c,j} ⊗ B_j`.** -/
theorem qform_eq_corr (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    qform (dst ψ) (aOp (refl D c j) * bOp (bobs MB (cell c j))) = corr ψ MA MB c j := by
  classical
  rw [aOp_mul_bOp_eq, qform_dst, emb_compress_refl]
  -- expand the Alice sum
  rw [sum_kronecker_left, qform_sum]
  rw [corr]
  refine Finset.sum_congr rfl fun d _ => ?_
  -- pull out the sign
  rw [show (csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val) ⊗ₖ bobs MB (cell c j)
      = ((rsgn (pvBit c (rep c d) j) : ℝ) : ℂ)
        • (((MA (Sum.inl c)).mats d).val ⊗ₖ bobs MB (cell c j)) from by
    rw [Matrix.smul_kronecker, csgn, sgn_eq_rsgn], qform_smul_real]
  -- expand Bob's observable
  rw [sum_zmod2 (fun w => rsgn (pvBit c (rep c d) j) * rsgn w
    * bornProb ψ (((MA (Sum.inl c)).mats d).val)
        (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val))]
  rw [show (((MA (Sum.inl c)).mats d).val ⊗ₖ bobs MB (cell c j))
      = (((MA (Sum.inl c)).mats d).val ⊗ₖ ((MB (Sum.inr (cell c j))).mats (Sum.inr 0)).val)
        + (((-1 : ℝ) : ℂ)) • (((MA (Sum.inl c)).mats d).val
            ⊗ₖ ((MB (Sum.inr (cell c j))).mats (Sum.inr 1)).val) from by
    rw [← Matrix.kronecker_smul, ← Matrix.kronecker_add, bobs]
    congr 1
    module, qform_add, qform_smul_real]
  have h0 : rsgn (0 : ZMod 2) = 1 := by rw [rsgn]; norm_num
  have h1 : rsgn (1 : ZMod 2) = -1 := by rw [rsgn]; norm_num
  rw [h0, h1, bornProb, bornProb, qform, qform]
  ring

/-! ## The closeness hypothesis, from the game's value -/

theorem snorm_sq_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) (D : Dilated MA) (c : Fin layout.r)
    (j : Fin 3) :
    snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ^ 2
      ≤ 4 * condFail nonlocalGame ψ MA MB (Sum.inl c) (Sum.inr (cell c j)) := by
  have hv : ‖evec (dst ψ)‖ = 1 := norm_dst_eq_one hψ
  set A : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ := aOp (refl D c j) with hA
  set B : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ := bOp (bobs MB (cell c j)) with hB
  have hAsa : Aᴴ = A := by rw [hA, aOp_conjTranspose, refl_conjTranspose]
  have hBsa : Bᴴ = B := by rw [hB, bOp_conjTranspose, bobs_conjTranspose]
  have hAA : A * A = 1 := by rw [hA, ← aOp_mul, refl_mul_self, aOp_one]
  have hcomm : A * B = B * A := by rw [hA, hB, aOp_mul_bOp]
  have hexp : (A - B)ᴴ * (A - B) = 1 - (((2 : ℝ) : ℂ)) • (A * B) + B * B := by
    rw [Matrix.conjTranspose_sub, hAsa, hBsa]
    have h : (A - B) * (A - B) = A * A - A * B - B * A + B * B := by noncomm_ring
    rw [h, hAA, ← hcomm]
    module
  rw [snorm_sq_eq_qform, hexp, qform_add, qform_sub, qform_one _ hv, qform_smul_real]
  have hBB : qform (dst ψ) (B * B) ≤ 1 := by
    have h : qform (dst ψ) (B * B) = snorm (dst ψ) B ^ 2 := by
      rw [snorm_sq_eq_qform, hBsa]
    rw [h]
    have hb : snorm (dst ψ) B ≤ 1 := by
      have := bnd_bobs (dA := dA) (MB := MB) (cell c j) (dst ψ)
      rw [one_mul, hv] at this
      exact this
    nlinarith [snorm_nonneg (dst ψ) B, hb]
  have hcorr := one_sub_two_mul_condFail_le_corr (MA := MA) (MB := MB) hψ c j
  rw [qform_eq_corr]
  linarith

/-- **The closeness hypothesis, with `γ = 12 √ε`.** -/
theorem close_of_fail (hψ : star ψ ⬝ᵥ ψ = 1) (D : Dilated MA) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - povmValue nonlocalGame ψ MA MB ≤ ε) :
    ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j)))
      ≤ 12 * Real.sqrt ε := by
  intro c j
  have hμ : nonlocalGame.μ (Sum.inl c) (Sum.inr (cell c j)) = 1 / 36 := by
    have hmem : cell c j ∈ layout.V c := cell_mem c j
    have hcard : (layout.V c).card = 3 := by fin_cases c <;> decide
    rw [nonlocalGame, Game.toNonlocalGame_μ]
    show (if cell c j ∈ layout.V c then 1 / (2 * (layout.r : ℝ) * ((layout.V c).card : ℝ))
      else 0) = 1 / 36
    rw [if_pos hmem, hcard, show ((layout.r : ℕ) : ℝ) = 6 from by norm_num [layout]]
    norm_num
  have hℓ := condFail_le_div (G := nonlocalGame) (MA := MA) (MB := MB) hψ hfail
    (x := Sum.inl c) (y := Sum.inr (cell c j)) (by rw [hμ]; norm_num)
  rw [hμ] at hℓ
  have hsq := snorm_sq_le_condFail (MA := MA) (MB := MB) hψ D c j
  have hsq' : snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ^ 2 ≤ 144 * ε := by
    have : (4 : ℝ) * (ε / (1/36)) = 144 * ε := by ring
    linarith [hsq, hℓ, this]
  have hnn := snorm_nonneg (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j)))
  have hs : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  nlinarith [hsq', hnn, Real.sqrt_nonneg ε, hs]

end Assemble

/-! ## The lemma, for the player who receives the variables -/

/-- The dilated state's norm of a Bob operator is the original state's. -/
theorem snorm_bOp_eq (ψ : dA × dB → ℂ) (R : Matrix dB dB ℂ) :
    snorm (dst ψ) (bOp R : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = ‖stateVecB ψ R‖ := by
  have hiso : (((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)))ᴴ * ((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ))
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      emb_isometry, Matrix.one_mul, Matrix.one_kronecker_one]
  have hmat : (bOp R : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
        * ((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ))
      = ((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)) * ((1 : Matrix dA dA ℂ) ⊗ₖ R) := by
    rw [bOp, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  rw [snorm, dst, Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec,
    norm_evec_mulVec_eq hiso]
  rfl

/-- **Direct Magic Square anticommutation** (blueprint `lem:ms-direct-anticomm`), for the player
who receives the variable questions. No projectivity, no isometry, no extracted EPR pairs: the
bound is on the original observables and the original state. -/
theorem ms_direct_anticomm {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : layout.Question → POVM layout.Answer dA)
    (MB : layout.Question → POVM layout.Answer dB)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - povmValue nonlocalGame ψ MA MB ≤ ε) :
    ‖stateVecB ψ (anti MB)‖ ^ 2 ≤ 186624 * ε := by
  obtain ⟨D⟩ := nonempty_dilated MA
  have h36 := snorm_anti (MB := MB) (close_of_fail (MB := MB) hψ D hε hfail)
  rw [snorm_bOp_eq] at h36
  have hs : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  have hb : ‖stateVecB ψ (anti MB)‖ ≤ 432 * Real.sqrt ε := by
    calc ‖stateVecB ψ (anti MB)‖ ≤ 36 * (12 * Real.sqrt ε) := h36
      _ = 432 * Real.sqrt ε := by ring
  nlinarith [norm_nonneg (stateVecB ψ (anti MB)), Real.sqrt_nonneg ε, hb, hs]

/-! ## The other player, by the symmetry of the game

Exchanging the players is an automorphism of the Magic Square game
(`MIPRE.LCS.Layout.questionDist_symm`, `MIPRE.LCS.Game.accepts_symm`), so Alice's half of the
lemma is Bob's half applied to the swapped strategy. -/

section Swap

omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_swapVec (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb (swapVec ψ) EB EA = bornProb ψ EA EB := by
  classical
  have inner : ∀ (i : dA) (j : dB),
      (((EB ⊗ₖ EA) *ᵥ swapVec ψ) (j, i)) = (((EA ⊗ₖ EB) *ᵥ ψ) (i, j)) := by
    intro i j
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    refine Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun q => ?_
    obtain ⟨l, k⟩ := q
    show (EB ⊗ₖ EA) (j, i) (l, k) * (swapVec ψ) (l, k)
        = (EA ⊗ₖ EB) (i, j) (k, l) * ψ (k, l)
    show EB j l * EA i k * ψ (k, l) = EA i k * EB j l * ψ (k, l)
    ring
  have key : star (swapVec ψ) ⬝ᵥ ((EB ⊗ₖ EA) *ᵥ swapVec ψ)
      = star ψ ⬝ᵥ ((EA ⊗ₖ EB) *ᵥ ψ) := by
    rw [dotProduct, dotProduct]
    refine Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun p => ?_
    obtain ⟨j, i⟩ := p
    show star (swapVec ψ) (j, i) * (((EB ⊗ₖ EA) *ᵥ swapVec ψ) (j, i))
        = star ψ (i, j) * (((EA ⊗ₖ EB) *ᵥ ψ) (i, j))
    rw [inner i j]
    rfl
  rw [bornProb, bornProb, key]

theorem povmValue_swapVec (ψ : dA × dB → ℂ)
    (MA : layout.Question → POVM layout.Answer dA)
    (MB : layout.Question → POVM layout.Answer dB) :
    povmValue nonlocalGame (swapVec ψ) MB MA = povmValue nonlocalGame ψ MA MB := by
  classical
  have hterm : ∀ x y : layout.Question,
      nonlocalGame.μ x y * condWin nonlocalGame (swapVec ψ) MB MA x y
        = nonlocalGame.μ y x * condWin nonlocalGame ψ MA MB y x := by
    intro x y
    have hμ : nonlocalGame.μ x y = nonlocalGame.μ y x := by
      rw [nonlocalGame, Game.toNonlocalGame_μ, Game.toNonlocalGame_μ]
      exact Layout.questionDist_symm _ x y
    have hcw : condWin nonlocalGame (swapVec ψ) MB MA x y
        = condWin nonlocalGame ψ MA MB y x := by
      have h : ∀ a b : layout.Answer,
          (if nonlocalGame.D x y a b then (1 : ℝ) else 0)
              * bornProb (swapVec ψ) (((MB x).mats a).val) (((MA y).mats b).val)
            = (if nonlocalGame.D y x b a then (1 : ℝ) else 0)
              * bornProb ψ (((MA y).mats b).val) (((MB x).mats a).val) := by
        intro a b
        rw [bornProb_swapVec]
        congr 2
        rw [nonlocalGame, Game.toNonlocalGame_D, Game.toNonlocalGame_D,
          Game.accepts_symm game x y a b]
      rw [condWin, condWin, Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        Finset.sum_congr rfl fun b (_ : b ∈ univ) => h a b]
      exact Finset.sum_comm
    rw [hμ, hcw]
  rw [povmValue, povmValue, Finset.sum_congr rfl fun x (_ : x ∈ univ) =>
    Finset.sum_congr rfl fun y (_ : y ∈ univ) => hterm x y]
  exact Finset.sum_comm

omit [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
theorem swapVec_swapVec (ψ : dA × dB → ℂ) : swapVec (swapVec ψ) = ψ := rfl

/-- **Direct Magic Square anticommutation for the other player.** The game is symmetric in the
players, so this is `ms_direct_anticomm` for the swapped strategy. -/
theorem ms_direct_anticomm' {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : layout.Question → POVM layout.Answer dA)
    (MB : layout.Question → POVM layout.Answer dB)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - povmValue nonlocalGame ψ MA MB ≤ ε) :
    ‖stateVec ψ (anti MA)‖ ^ 2 ≤ 186624 * ε := by
  have hψ' : star (swapVec ψ) ⬝ᵥ swapVec ψ = 1 := by rw [swapVec_dotProduct]; exact hψ
  have hfail' : 1 - povmValue nonlocalGame (swapVec ψ) MB MA ≤ ε := by
    rw [povmValue_swapVec]
    exact hfail
  have h := ms_direct_anticomm hψ' MB MA hε hfail'
  rw [norm_stateVecB, swapVec_swapVec] at h
  exact h

/-- **The averaged form.** The bound is pointwise, so averaging it over a family of strategies
on the same pair of spaces costs nothing --- no Jensen step, and the same constant. -/
theorem ms_direct_anticomm_avg {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (ψ : Ω → dA × dB → ℂ) (hψ : ∀ ω, star (ψ ω) ⬝ᵥ ψ ω = 1)
    (MA : Ω → layout.Question → POVM layout.Answer dA)
    (MB : Ω → layout.Question → POVM layout.Answer dB)
    (ε : Ω → ℝ) (hε : ∀ ω, 0 ≤ ε ω)
    (hfail : ∀ ω, 1 - povmValue nonlocalGame (ψ ω) (MA ω) (MB ω) ≤ ε ω) :
    ∑ ω, ν ω * ‖stateVecB (ψ ω) (anti (MB ω))‖ ^ 2 ≤ 186624 * ∑ ω, ν ω * ε ω := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h := ms_direct_anticomm (hψ ω) (MA ω) (MB ω) (hε ω) (hfail ω)
  calc ν ω * ‖stateVecB (ψ ω) (anti (MB ω))‖ ^ 2 ≤ ν ω * (186624 * ε ω) :=
        mul_le_mul_of_nonneg_left h (hν ω)
    _ = 186624 * (ν ω * ε ω) := by ring

end Swap

end MIPRE.QLD.MS

end
