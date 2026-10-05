/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Game
public import MIPRE.Foundations.Pipeline.Budget
public import MIPRE.Foundations.Cost.Fold

@[expose] public section

/-!
# Tailored normal form verifiers

Paper II of the Aldous–Lyons track (Bowen–Chapman–Vidick, arXiv:2501.00173), §2.6
(II:1630–1832). A *tailored normal form verifier* is four machines `(S, L, LP, D)`: a
conditionally linear sampler, an answer-length calculator, a linear-constraints processor, and
the fixed canonical decider. Here the canonical decider is not a field — it is the same for
every verifier (`TailoredGame.Accepts`) — so a `TailoredVerifier ℓ` is the other three:

* `sampler`, a `CL.Sampler ℓ`, as in `MIPRE.Verifier`;
* `len`, the answer-length calculator: on `encode (n, x, κ)` it outputs the number `ℓ^κ(x)` of
  readable (`κ = false`) or linear (`κ = true`) variables at the question `x` of the `n`-th game
  (`LenIs`);
* `lp`, the linear-constraints processor: on `encode (n, x, y, a^R, b^R)` it outputs the list of
  constraints `L_xy(a^R, b^R)` (`LpIs`).

Both are closed programs whose input starts with the index `n`, so the structure
`MIPRE.Decider` and its running-time bound `Decider.TimeBoundAt` serve for them; only the
decider's notion of acceptance does not apply. Their outputs are read *totally*, so that no
output is malformed and the canonical decider, which has to read them, needs no validity
check: a length in unary, as the paper writes it (II:1781) — the length of the output's spine,
`(Cost.Data.spineList d).length` — and a constraint list by `Cost.Data.bitsListD`, which on
the encoding of a list of bit strings is that list. The length bound is still a separate clause
(`LenBound`), in `IsBounded` and in the budgets, though the running time bounds a unary
output.

* `TailoredVerifier.tgame n`: the `n`-th game `𝒱_n`, a `TailoredGame` on the sampler's questions,
  read off the programs: a question at which `len` does not halt, or a pair at which `lp` does
  not, gets the constraint list that rejects everything, as a timeout is a rejection in the
  paper. The programs being deterministic, the choices made in reading them off are immaterial.
* `valStar n`, `HasPerfectZPC n`: the value of `𝒱_n`, and the completeness notion of the track,
  a perfect Z-aligned permutation strategy commuting along edges of the doubled game — what
  `Verifier.HasPerfectPCC` is for the existing pipeline.
* `IsBounded λ` (II:1800) and `Within n R`: the paper's `λ`-boundedness and the budgets of the
  stage contracts, in the relative-cost reading of `MIPRE.Verifier.IsBounded`, with the length
  clause added.

`TailoredVerifier.ofTNFV` (`MIPRE.Tailored.OfTNFV`) packages a tailored verifier as a
`MIPRE.Verifier`, the canonical decider written as a program (`MIPRE.Tailored.Canonical`).
-/

namespace MIPRE.Cost.Data

/-! ## Total readings of data -/

/-- The elements along the right spine: the list a datum encodes, every datum encoding one. -/
def spineList : Data → List Data
  | nil => []
  | cons a d => a :: spineList d

@[simp] theorem spineList_nil : spineList nil = [] := rfl

@[simp] theorem spineList_cons (a d : Data) : spineList (cons a d) = a :: spineList d := rfl

theorem ofList_id_spineList (d : Data) : ofList id (spineList d) = d := by
  induction d with
  | nil => rfl
  | cons a d _ ih => simp [ofList, ih]

theorem spineList_ofList {α : Type*} (f : α → Data) (l : List α) :
    spineList (ofList f l) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, ih]

/-- A length written in unary is read back. -/
theorem length_spineList_ofNat (k : ℕ) : (spineList (ofNat k)).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ofNat, ih]

/-- A datum read as a bit: `nil` is `false`, a node `true`. -/
def bitD : Data → Bool
  | nil => false
  | cons _ _ => true

@[simp] theorem bitD_ofBool (b : Bool) : bitD (ofBool b) = b := by cases b <;> rfl

/-- A datum read as a bit string: its spine, elementwise. -/
def bitsD (d : Data) : BitStr := (spineList d).map bitD

/-- A datum read as a list of bit strings. -/
def bitsListD (d : Data) : List BitStr := (spineList d).map bitsD

theorem bitsD_encode (s : BitStr) : bitsD (encode s) = s := by
  change (spineList (ofList ofBool s)).map bitD = s
  rw [spineList_ofList, List.map_map]
  conv_rhs => rw [← List.map_id s]
  exact List.map_congr_left fun b _ => bitD_ofBool b

theorem bitsListD_encode (cs : List BitStr) : bitsListD (encode cs) = cs := by
  change (spineList (ofList encode cs)).map bitsD = cs
  rw [spineList_ofList, List.map_map]
  conv_rhs => rw [← List.map_id cs]
  exact List.map_congr_left fun s _ => bitsD_encode s

end MIPRE.Cost.Data

namespace MIPRE.Tailored

open Cost

/-! ## The answer-length calculator and the linear-constraints processor -/

/-- The answer-length calculator `L` outputs `k` on `(n, x, κ)`: `ℓ^κ(x) = k` at the question
`x` of the `n`-th game, readable for `κ = false`, linear for `κ = true` — read in unary, as the
length of the spine of `L`'s output (II:1781). -/
def LenIs (L : Decider) (n : ℕ) (x : BitStr) (κ : Bool) (k : ℕ) : Prop :=
  ∃ t d, L.prog.Runs (encode (n, x, κ)) d t ∧ (Data.spineList d).length = k

/-- The lengths `L` outputs at index `n` are at most `B`. -/
def LenBound (L : Decider) (n B : ℕ) : Prop := ∀ x κ k, LenIs L n x κ k → k ≤ B

/-- `L` halts on every question of dimension `d` at index `n`: the paper's requirement that the
answer-length calculator never output `error` on the sampler's questions (II:1863). -/
def LenTotal (L : Decider) (n d : ℕ) : Prop :=
  ∀ x : BitStr, x.length = d → ∀ κ, ∃ k, LenIs L n x κ k

/-- The linear-constraints processor `P` outputs the constraint list `cs` on
`(n, x, y, a^R, b^R)`, its output read by `Data.bitsListD`. -/
def LpIs (P : Decider) (n : ℕ) (x y aR bR : BitStr) (cs : List BitStr) : Prop :=
  ∃ t d, P.prog.Runs (encode (n, x, y, aR, bR)) d t ∧ Data.bitsListD d = cs

/-! ## Tailored normal form verifiers -/

/-- A tailored normal form verifier (II:1758), its canonical decider left implicit. -/
structure TailoredVerifier (ℓ : ℕ) where
  /-- The sampler, producing the questions. -/
  sampler : CL.Sampler ℓ
  /-- The answer-length calculator. -/
  len : Decider
  /-- The linear-constraints processor. -/
  lp : Decider

namespace TailoredVerifier

variable {ℓ : ℕ} (V : TailoredVerifier ℓ)

/-- The three programs, what the procedures of the pipeline read. -/
def progs : Prog × Prog × Prog := (V.sampler.prog, V.len.prog, V.lp.prog)

/-- The description length `|𝒱|`, the largest of the three. -/
def size : ℕ := max V.sampler.size (max V.len.size V.lp.size)

/-- The question alphabet of `𝒱_n`: `𝔽₂^{s(n)}`. -/
abbrev Questions (n : ℕ) : Type := Fin (V.sampler.dim n) → CL.𝔽₂

open Classical in
/-- The length `len` outputs on `(n, x, κ)`, and `0` when it does not halt. -/
noncomputable def lenOf (n : ℕ) (x : BitStr) (κ : Bool) : ℕ :=
  if h : ∃ k, LenIs V.len n x κ k then h.choose else 0

/-- `len` halts at the question `x` of index `n`, for both kinds of variables. -/
def LenDefined (n : ℕ) (x : BitStr) : Prop := ∀ κ, ∃ k, LenIs V.len n x κ k

open Classical in
/-- The constraints at `(x, y)`: what `lp` outputs when `len` halts at both questions and `lp`
halts; otherwise the list that rejects everything. -/
noncomputable def consOf (n : ℕ) (x y aR bR : BitStr) : List BitStr :=
  if h : V.LenDefined n x ∧ V.LenDefined n y ∧ ∃ cs, LpIs V.lp n x y aR bR cs then
    h.2.2.choose
  else
    [rejectConstraint (V.lenOf n x false + V.lenOf n x true + V.lenOf n y false +
      V.lenOf n y true)]

/-- The `n`-th game `𝒱_n` (the paper's `def:normal-game` for tailored verifiers): questions
`𝔽₂^{s(n)}` distributed as the sampler prescribes, lengths and constraints as `len` and `lp`
compute them. -/
noncomputable def tgame (n : ℕ) : TailoredGame (V.Questions n) where
  μ := V.sampler.dist n
  μ_nonneg := V.sampler.dist_nonneg n
  μ_sum_one := V.sampler.sum_dist n
  lenR x := V.lenOf n (CL.toBits x) false
  lenL x := V.lenOf n (CL.toBits x) true
  cons x y := V.consOf n (CL.toBits x) (CL.toBits y)

/-- `val*(𝒱_n)`. -/
noncomputable def valStar (n : ℕ) : ℝ := (V.tgame n).valStar

/-- `𝒱_n` has a perfect Z-aligned permutation strategy commuting along edges, on the doubled
question set (Alice asked `(false, x)`, Bob `(true, y)`), the reading of the paper's
completeness clause that `Verifier.HasPerfectPCC` makes for the existing pipeline. -/
def HasPerfectZPC (n : ℕ) : Prop := (V.tgame n).doubled.HasPerfectZPC

/-- `λ`-bounded (II:1800): for `n ≥ 2`, the dimension and the running times of the three
programs are at most `n^λ` — the times at degree `λ` in the size of the input, as in
`MIPRE.Verifier.IsBounded` — the lengths `len` outputs are at most `n^λ` (the paper's unary
output makes this a consequence of the time bound), and `|𝒱| ≤ λ`. -/
def IsBounded (lam : ℕ) : Prop :=
  (∀ n, 2 ≤ n → V.sampler.dim n ≤ n ^ lam ∧ V.sampler.TimeBoundAt n (n ^ lam) lam ∧
    V.len.TimeBoundAt n (n ^ lam) lam ∧ V.lp.TimeBoundAt n (n ^ lam) lam ∧
    LenBound V.len n (n ^ lam)) ∧ V.size ≤ lam

/-- `𝒱` is within the budget `R` at index `n`: the sampler within `R.S` and of dimension at most
`R.d`, the answer-length calculator and the linear-constraints processor within `R.D`, all at
degree `R.k`, and the lengths at most `R.B` — the reading of `MIPRE.Verifier.Within` for
tailored verifiers, the decider's time becoming that of the two programs and its answer bound
the bound on the lengths. -/
def Within (n : ℕ) (R : Budget) : Prop :=
  V.sampler.TimeBoundAt n R.S R.k ∧ V.sampler.dim n ≤ R.d ∧
    V.len.TimeBoundAt n R.D R.k ∧ V.lp.TimeBoundAt n R.D R.k ∧ LenBound V.len n R.B

end TailoredVerifier

end MIPRE.Tailored

end
