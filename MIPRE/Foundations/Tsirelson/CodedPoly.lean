/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.ValueApprox.RawPrimrec

/-!
# Coded polynomials and the upper-bound certificate check

The coded layer of the upper semidecision of the commuting-operator value
(`planning/tsirelson-campaign.md`, §3.5–§3.6). Everything here is a finite list computation on
naturals, primitive recursive, and independent of the algebra `NCPoly` that gives it meaning; the
semantic layer decodes it.

**Coded polynomials.** A letter (`Letter`) is `inl (x, a)`, the first player's effect `e_xa`, or
`inr (y, b)`, the second player's `f_yb`; a word is a `List Letter`. A coded polynomial
(`CPoly`) is a list of monomials `(w, c)`, a word and a coded Gaussian integer (`GInt`), and it
denotes `Σ c·w`; the list is not normalized, so a word may occur several times. The operations
are the list-level ones: `cadd` concatenates, `cneg` and `cscale c` act on the coefficients,
`cmul` multiplies every monomial of one factor by every monomial of the other, `cstar` reverses
the words and conjugates the coefficients (the letters are self-adjoint), and `cconst c`,
`cword w`, `cletter l` are the one-monomial polynomials.

**Merged coefficients and dominance.** The coefficient of a word `w` in `l` is the sum of the
coefficients of the monomials of `l` with word `w` (`coeffRaw`); its complex value is the sum of
the complex values of those coefficients (`toC_coeffRaw`, `toC_coeffRaw_eq_sum_ite`). The
distinct words of `l` are `words l = (l.map Prod.fst).dedup`, and the off-diagonal mass
`offMass l` is the sum, over the nonempty distinct words, of the taxicab norm `taxi` of the merged
coefficient, where `taxi z = |Re z| + |Im z|` is computed on naturals (`taxi_eq`). A coded
polynomial is dominant (`IsDominant`) if the real part of its merged constant coefficient
strictly exceeds its off-diagonal mass. `isDominant_iff_sum` restates this over any finite set of
words containing those of `l`: `Σ_{w ≠ ∅} (|Re l_w| + |Im l_w|) < Re l_∅`.

**Relations and the game polynomial.** A relation index (`RelIdx`) is `inl x` (the first
player's normalization `Σ_{a ≤ nA} e_xa − 1`), `inr (inl y)` (the second player's,
`Σ_{b ≤ nA} f_yb − 1`), or `inr (inr (x, y, a, b))` (the commutator `e_xa f_yb − f_yb e_xa`);
`relPoly nA` gives the polynomial. For a game description `d`, `Wint d` is the integer game
polynomial `Σ_{x, y ≤ nX} Σ_{a, b ≤ nA} wt(x, y) [Draw(x, y, a, b)] e_xa f_yb`, which is `W d`
times the game polynomial of `d.game`. Letters and relation indices are validated against the
alphabets of `d.game` (questions `≤ nX`, answers `≤ nA`, for both players): `ValidLetter`,
`ValidWord`, `ValidCPoly`, `ValidRel`, and every construction here preserves validity
(`validCPoly_certR`).

**Certificates.** A certificate (`Cert`) is a triple `(N, sos, ideal)`: a natural `N`, a list of
sum-of-squares terms `(g, s)` standing for `s⋆ g s` (with `g = none` read as `1`), and a list of
ideal monomials `(c, w, ρ, w')` standing for `c · w · relPoly ρ · w'`. With `D = N²`, the
residual is
`certR d p q (N, sos, ideal) = D·(p·W d·1 − q·Wint d) − Σ s⋆ g s − Σ c·w·ρ·w'`,
and `CheckUpper (d, p, q) cert` accepts iff `q > 0`, `N ≥ 1`, all letters and relation indices of
the certificate are valid, and the hermitian residual `certRh = certR + certR⋆` is dominant. The
test `q > 0` is essential: `p / 0 = 0` in the consumer `CommutingUpperRE`. The test runs on
merged coefficients, without which it would be sound but never complete.

The main result is `primrecRel_checkUpper : PrimrecRel CheckUpper`, which with
`MIPRE.ValueApprox.REPred.of_primrecRel_exists` makes the set of accepted `(d, p, q)` recursively
enumerable.

## Main declarations

* `Letter`, `CPoly`, `cadd`, `cneg`, `cscale`, `cmul`, `cstar`, `cconst`, `cword`, `cletter`;
* `gneg`, `ptaxi`, `taxi`, `taxi_eq`, `taxi_congr`;
* `coeffRaw`, `toC_coeffRaw`, `toC_coeffRaw_eq_sum_ite`, `coeffRaw_eq_zero_of_notMem`, and the
  coefficients of `cadd`, `cneg`, `cscale`, `cstar`;
* `words`, `dedup_eq_foldr`, `offMass`, `offMass_eq_sum`, `offMass_eq_sum_of_subset`,
  `IsDominant`, `isDominant_iff`, `isDominant_iff_sum`;
* `ValidLetter`, `ValidWord`, `ValidCPoly`, `ValidOptLetter`, `RelIdx`, `ValidRel`, `relPoly`,
  `Wint`, `Cert`, `optPoly`, `sosSum`, `idealSum`, `certR`, `certRh`, `ValidCert`, `CheckUpper`,
  and the validity lemmas `validCPoly_certR`, `validCPoly_certRh`;
* primitive recursiveness of every definition, ending with `primrecRel_checkUpper`.
-/

namespace MIPRE.Tsirelson.Coded

open MIPRE.ValueApprox
open HaltingGameValue (GameData)
open Primrec

/-! ## Coded Gaussian integers: negation and the taxicab norm -/

/-- The negation of a coded Gaussian integer. -/
def gneg (z : GInt) : GInt := (PInt.neg z.1, PInt.neg z.2)

/-- Negation of coded Gaussian integers is negation of their complex values. -/
@[simp] theorem toC_gneg (z : GInt) : GInt.toC (gneg z) = -GInt.toC z := by
  apply Complex.ext <;> simp [gneg]

/-- The absolute value of a coded integer `a - b`, as the natural number `(a - b) + (b - a)`
(truncated subtraction). -/
def ptaxi (x : PInt) : ℕ := (x.1 - x.2) + (x.2 - x.1)

/-- `ptaxi x` is the absolute value of the integer coded by `x`. -/
theorem natCast_ptaxi (x : PInt) : (ptaxi x : ℤ) = |x.toInt| := by
  unfold ptaxi PInt.toInt
  rcases le_total x.1 x.2 with h | h
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega

/-- The taxicab norm `|Re z| + |Im z|` of a coded Gaussian integer, as a natural number. -/
def taxi (z : GInt) : ℕ := ptaxi z.1 + ptaxi z.2

/-- The taxicab norm computed on naturals is `|Re z| + |Im z|`. -/
theorem taxi_eq (z : GInt) : (taxi z : ℝ) = |(GInt.toC z).re| + |(GInt.toC z).im| := by
  rw [GInt.re_toC, GInt.im_toC, ← Int.cast_abs, ← Int.cast_abs, ← natCast_ptaxi,
    ← natCast_ptaxi]
  simp [taxi]

/-- The coded zero has taxicab norm `0`. -/
@[simp] theorem taxi_zero : taxi GInt.zero = 0 := rfl

/-- The taxicab norm depends only on the complex number denoted. -/
theorem taxi_congr {z z' : GInt} (h : GInt.toC z = GInt.toC z') : taxi z = taxi z' := by
  have h' : (taxi z : ℝ) = taxi z' := by rw [taxi_eq, taxi_eq, h]
  exact_mod_cast h'

/-! ## Coded polynomials -/

/-- A letter: `inl (x, a)` is the first player's effect `e_xa`, `inr (y, b)` the second
player's effect `f_yb`. -/
abbrev Letter := (ℕ × ℕ) ⊕ (ℕ × ℕ)

/-- A coded polynomial: a list of monomials `(w, c)`, a word and a coded Gaussian coefficient,
denoting `Σ c·w`. The list is not normalized: a word may occur several times. -/
abbrev CPoly := List (List Letter × GInt)

/-- The sum of coded polynomials: concatenation. -/
def cadd (p q : CPoly) : CPoly := p ++ q

/-- The negation of a coded polynomial. -/
def cneg (p : CPoly) : CPoly := p.map fun m => (m.1, gneg m.2)

/-- The multiple `c • p` of a coded polynomial. -/
def cscale (c : GInt) (p : CPoly) : CPoly := p.map fun m => (m.1, GInt.mul c m.2)

/-- The product of coded polynomials: every monomial of `p` times every monomial of `q`. -/
def cmul (p q : CPoly) : CPoly :=
  p.flatMap fun m => q.map fun m' => (m.1 ++ m'.1, GInt.mul m.2 m'.2)

/-- The star of a coded polynomial: reverse the words and conjugate the coefficients (the
letters are self-adjoint). -/
def cstar (p : CPoly) : CPoly := p.map fun m => (m.1.reverse, GInt.conj m.2)

/-- The constant polynomial `c`. -/
def cconst (c : GInt) : CPoly := [([], c)]

/-- The word `w`, as a monomial with coefficient `1`. -/
def cword (w : List Letter) : CPoly := [(w, GInt.ofNat 1)]

/-- The letter `l`, as a polynomial. -/
def cletter (l : Letter) : CPoly := cword [l]

/-! ## Merged coefficients and dominance -/

/-- The merged coefficient of the word `w` in `l`: the sum of the coefficients of the monomials
of `l` with word `w`. -/
def coeffRaw (l : CPoly) (w : List Letter) : GInt :=
  GInt.sum ((l.filter fun m => m.1 = w).map Prod.snd)

/-- The distinct words of `l`. -/
def words (l : CPoly) : List (List Letter) := (l.map Prod.fst).dedup

/-- The off-diagonal mass of `l`: the sum of the taxicab norms of the merged coefficients of
the distinct nonempty words of `l`. -/
def offMass (l : CPoly) : ℕ :=
  (((words l).filter fun w => w ≠ []).map fun w => taxi (coeffRaw l w)).sum

/-- Dominance: the real part of the merged constant coefficient of `l` strictly exceeds its
off-diagonal mass. -/
def IsDominant (l : CPoly) : Prop := PInt.Lt' (PInt.ofNat (offMass l)) (coeffRaw l []).1

/-- Dominance is decidable: it compares two coded integers. -/
instance : DecidablePred IsDominant := fun l =>
  inferInstanceAs (Decidable (PInt.Lt' (PInt.ofNat (offMass l)) (coeffRaw l []).1))

/-! ## Validation, relations and the game polynomial -/

/-- The question index of a letter. -/
def letterQ : Letter → ℕ
  | Sum.inl t => t.1
  | Sum.inr t => t.1

/-- The answer index of a letter. -/
def letterA : Letter → ℕ
  | Sum.inl t => t.2
  | Sum.inr t => t.2

/-- A letter is valid for questions `≤ nX` and answers `≤ nA`, the alphabets `Fin (nX + 1)` and
`Fin (nA + 1)` of both players in `GameData.game`. -/
def ValidLetter (nX nA : ℕ) (l : Letter) : Prop := letterQ l ≤ nX ∧ letterA l ≤ nA

/-- Validity of a letter is decidable. -/
instance (nX nA : ℕ) : DecidablePred (ValidLetter nX nA) := fun l =>
  inferInstanceAs (Decidable (letterQ l ≤ nX ∧ letterA l ≤ nA))

/-- A first-player letter `e_xa` is valid iff `x ≤ nX` and `a ≤ nA`. -/
@[simp] theorem validLetter_inl (nX nA x a : ℕ) :
    ValidLetter nX nA (Sum.inl (x, a)) ↔ x ≤ nX ∧ a ≤ nA := Iff.rfl

/-- A second-player letter `f_yb` is valid iff `y ≤ nX` and `b ≤ nA`. -/
@[simp] theorem validLetter_inr (nX nA y b : ℕ) :
    ValidLetter nX nA (Sum.inr (y, b)) ↔ y ≤ nX ∧ b ≤ nA := Iff.rfl

/-- Every letter of the word is valid. -/
def ValidWord (nX nA : ℕ) (w : List Letter) : Prop := ∀ l ∈ w, ValidLetter nX nA l

/-- Validity of a word is decidable. -/
instance (nX nA : ℕ) : DecidablePred (ValidWord nX nA) := fun w => by
  unfold ValidWord; infer_instance

/-- Every word of the coded polynomial is valid. -/
def ValidCPoly (nX nA : ℕ) (p : CPoly) : Prop := ∀ m ∈ p, ValidWord nX nA m.1

/-- Validity of a coded polynomial is decidable. -/
instance (nX nA : ℕ) : DecidablePred (ValidCPoly nX nA) := fun p => by
  unfold ValidCPoly; infer_instance

/-- An optional letter is valid if it is absent or valid. -/
def ValidOptLetter (nX nA : ℕ) : Option Letter → Prop
  | none => True
  | some l => ValidLetter nX nA l

/-- Validity of an optional letter is decidable. -/
instance (nX nA : ℕ) : DecidablePred (ValidOptLetter nX nA)
  | none => isTrue trivial
  | some l => inferInstanceAs (Decidable (ValidLetter nX nA l))

/-- A relation index: `inl x` is the first player's normalization at question `x`,
`inr (inl y)` the second player's at `y`, and `inr (inr (x, y, a, b))` the commutator of
`e_xa` and `f_yb`. -/
abbrev RelIdx := ℕ ⊕ ℕ ⊕ (ℕ × ℕ × ℕ × ℕ)

/-- A relation index is valid if its questions are `≤ nX` and its answers `≤ nA`. -/
def ValidRel (nX nA : ℕ) : RelIdx → Prop
  | Sum.inl x => x ≤ nX
  | Sum.inr (Sum.inl y) => y ≤ nX
  | Sum.inr (Sum.inr t) => t.1 ≤ nX ∧ t.2.1 ≤ nX ∧ t.2.2.1 ≤ nA ∧ t.2.2.2 ≤ nA

/-- Validity of a relation index is decidable. -/
instance (nX nA : ℕ) : DecidablePred (ValidRel nX nA)
  | Sum.inl x => inferInstanceAs (Decidable (x ≤ nX))
  | Sum.inr (Sum.inl y) => inferInstanceAs (Decidable (y ≤ nX))
  | Sum.inr (Sum.inr t) =>
    inferInstanceAs (Decidable (t.1 ≤ nX ∧ t.2.1 ≤ nX ∧ t.2.2.1 ≤ nA ∧ t.2.2.2 ≤ nA))

/-- The first player's normalization at `x`: `Σ_{a ≤ nA} e_xa − 1`. -/
def aliceNorm (nA x : ℕ) : CPoly :=
  ((List.range (nA + 1)).map fun a => ([Sum.inl (x, a)], GInt.ofNat 1)) ++
    cconst (gneg (GInt.ofNat 1))

/-- The second player's normalization at `y`: `Σ_{b ≤ nA} f_yb − 1`. -/
def bobNorm (nA y : ℕ) : CPoly :=
  ((List.range (nA + 1)).map fun b => ([Sum.inr (y, b)], GInt.ofNat 1)) ++
    cconst (gneg (GInt.ofNat 1))

/-- The commutator `e_xa f_yb − f_yb e_xa` at `t = (x, y, a, b)`. -/
def commPoly (t : ℕ × ℕ × ℕ × ℕ) : CPoly :=
  [([Sum.inl (t.1, t.2.2.1), Sum.inr (t.2.1, t.2.2.2)], GInt.ofNat 1),
    ([Sum.inr (t.2.1, t.2.2.2), Sum.inl (t.1, t.2.2.1)], gneg (GInt.ofNat 1))]

/-- The relation polynomial of a relation index, for answers `≤ nA`. -/
def relPoly (nA : ℕ) : RelIdx → CPoly
  | Sum.inl x => aliceNorm nA x
  | Sum.inr (Sum.inl y) => bobNorm nA y
  | Sum.inr (Sum.inr t) => commPoly t

/-- The integer game polynomial of a description:
`Σ_{x, y ≤ nX} Σ_{a, b ≤ nA} wt(x, y) [Draw(x, y, a, b)] e_xa f_yb`, which is `W d` times the
game polynomial of `d.game`. -/
def Wint (d : GameData) : CPoly :=
  (List.range (d.nX + 1)).flatMap fun x => (List.range (d.nX + 1)).flatMap fun y =>
    (List.range (d.nA + 1)).flatMap fun a => (List.range (d.nA + 1)).map fun b =>
      ([Sum.inl (x, a), Sum.inr (y, b)], GInt.ofNat (wt d x y * if Draw d x y a b then 1 else 0))

/-! ## Certificates and the check -/

/-- A certificate `(N, sos, ideal)`: the scale `N` (with `D = N²`), the sum-of-squares terms
`(g, s)` standing for `s⋆ g s` (`g = none` is `1`), and the ideal monomials `(c, w, ρ, w')`
standing for `c · w · relPoly ρ · w'`. -/
abbrev Cert := ℕ × List (Option Letter × CPoly) × List (GInt × List Letter × RelIdx × List Letter)

/-- The polynomial of an optional letter: `1` for `none`. -/
def optPoly : Option Letter → CPoly
  | none => cconst (GInt.ofNat 1)
  | some l => cletter l

/-- The sum of squares `Σ s⋆ g s` of a list of terms `(g, s)`. -/
def sosSum (sos : List (Option Letter × CPoly)) : CPoly :=
  sos.flatMap fun t => cmul (cmul (cstar t.2) (optPoly t.1)) t.2

/-- The ideal element `Σ c · w · relPoly ρ · w'` of a list of monomials `(c, w, ρ, w')`. -/
def idealSum (nA : ℕ) (ideal : List (GInt × List Letter × RelIdx × List Letter)) : CPoly :=
  ideal.flatMap fun t => cscale t.1 (cmul (cmul (cword t.2.1) (relPoly nA t.2.2.1)) (cword t.2.2.2))

/-- The residual of a certificate for the bound `p / q` on the description `d`:
`N²·(p·W d·1 − q·Wint d) − Σ s⋆ g s − Σ c·w·ρ·w'`. -/
def certR (d : GameData) (p q : ℕ) (cert : Cert) : CPoly :=
  cscale (GInt.ofNat (cert.1 * cert.1 * p * W d)) (cconst (GInt.ofNat 1)) ++
    cneg (cscale (GInt.ofNat (cert.1 * cert.1 * q)) (Wint d)) ++
    cneg (sosSum cert.2.1) ++ cneg (idealSum d.nA cert.2.2)

/-- The hermitian residual `R + R⋆`. -/
def certRh (d : GameData) (p q : ℕ) (cert : Cert) : CPoly :=
  certR d p q cert ++ cstar (certR d p q cert)

/-- Every letter and relation index of the certificate is valid. -/
def ValidCert (nX nA : ℕ) (cert : Cert) : Prop :=
  (∀ t ∈ cert.2.1, ValidOptLetter nX nA t.1 ∧ ValidCPoly nX nA t.2) ∧
    ∀ t ∈ cert.2.2, ValidWord nX nA t.2.1 ∧ ValidRel nX nA t.2.2.1 ∧ ValidWord nX nA t.2.2.2

/-- Validity of a certificate is decidable. -/
instance (nX nA : ℕ) : DecidablePred (ValidCert nX nA) := fun cert => by
  unfold ValidCert; infer_instance

/-- The upper certificate check: `cert` certifies `val_co(d.game) < p / q` for
`x = (d, p, q)`. It requires `q > 0`, `N ≥ 1`, a valid certificate, and a dominant hermitian
residual. -/
def CheckUpper (x : GameData × ℕ × ℕ) (cert : Cert) : Prop :=
  0 < x.2.2 ∧ 1 ≤ cert.1 ∧ ValidCert x.1.nX x.1.nA cert ∧ IsDominant (certRh x.1 x.2.1 x.2.2 cert)

/-- The upper certificate check is decidable. -/
instance (x : GameData × ℕ × ℕ) (cert : Cert) : Decidable (CheckUpper x cert) := by
  unfold CheckUpper; infer_instance

/-! ## Merged coefficients -/

/-- The empty coded polynomial has merged coefficient zero at every word. -/
theorem coeffRaw_nil (w : List Letter) : coeffRaw [] w = GInt.zero := rfl

/-- The merged coefficient of `m :: l` adds the coefficient of `m` when its word is `w`. -/
theorem coeffRaw_cons (m : List Letter × GInt) (l : CPoly) (w : List Letter) :
    coeffRaw (m :: l) w = if m.1 = w then GInt.add m.2 (coeffRaw l w) else coeffRaw l w := by
  by_cases h : m.1 = w <;> simp [coeffRaw, h, GInt.sum]

/-- The complex value of a merged coefficient is the sum of the values of the coefficients of
the matching monomials. -/
theorem toC_coeffRaw (l : CPoly) (w : List Letter) :
    GInt.toC (coeffRaw l w) = ((l.filter fun m => m.1 = w).map fun m => GInt.toC m.2).sum := by
  rw [coeffRaw, GInt.toC_sum, List.map_map]
  rfl

/-- The complex value of a merged coefficient, as a sum over all monomials. -/
theorem toC_coeffRaw_eq_sum_ite (l : CPoly) (w : List Letter) :
    GInt.toC (coeffRaw l w) = (l.map fun m => if m.1 = w then GInt.toC m.2 else 0).sum := by
  induction l with
  | nil => simp [coeffRaw_nil]
  | cons m l ih =>
    rw [coeffRaw_cons, List.map_cons, List.sum_cons, ← ih]
    split_ifs <;> simp

/-- The merged coefficient of a word that does not occur in `l` is zero. -/
theorem coeffRaw_eq_zero_of_notMem {l : CPoly} {w : List Letter} (h : w ∉ l.map Prod.fst) :
    coeffRaw l w = GInt.zero := by
  have hf : (l.filter fun m => m.1 = w) = [] := by
    rw [List.filter_eq_nil_iff]
    intro m hm hmw
    exact h (List.mem_map.mpr ⟨m, hm, of_decide_eq_true hmw⟩)
  rw [coeffRaw, hf]
  rfl

/-- The complex value of a merged coefficient is additive under concatenation. -/
theorem toC_coeffRaw_append (p q : CPoly) (w : List Letter) :
    GInt.toC (coeffRaw (p ++ q) w) = GInt.toC (coeffRaw p w) + GInt.toC (coeffRaw q w) := by
  rw [toC_coeffRaw_eq_sum_ite, toC_coeffRaw_eq_sum_ite, toC_coeffRaw_eq_sum_ite, List.map_append,
    List.sum_append]

/-- The complex value of a merged coefficient of a coded sum. -/
theorem toC_coeffRaw_cadd (p q : CPoly) (w : List Letter) :
    GInt.toC (coeffRaw (cadd p q) w) = GInt.toC (coeffRaw p w) + GInt.toC (coeffRaw q w) :=
  toC_coeffRaw_append p q w

/-- The complex value of a merged coefficient of a coded negation. -/
theorem toC_coeffRaw_cneg (p : CPoly) (w : List Letter) :
    GInt.toC (coeffRaw (cneg p) w) = -GInt.toC (coeffRaw p w) := by
  induction p with
  | nil => simp [cneg, coeffRaw_nil]
  | cons m p ih =>
    simp only [cneg, List.map_cons] at ih ⊢
    rw [coeffRaw_cons, coeffRaw_cons]
    split_ifs <;> simp [ih]
    ring

/-- The complex value of a merged coefficient of a coded multiple. -/
theorem toC_coeffRaw_cscale (c : GInt) (p : CPoly) (w : List Letter) :
    GInt.toC (coeffRaw (cscale c p) w) = GInt.toC c * GInt.toC (coeffRaw p w) := by
  induction p with
  | nil => simp [cscale, coeffRaw_nil]
  | cons m p ih =>
    simp only [cscale, List.map_cons] at ih ⊢
    rw [coeffRaw_cons, coeffRaw_cons]
    split_ifs <;> simp [ih]
    ring

/-- The merged coefficient of `w` in `p⋆` is the conjugate of that of `w.reverse` in `p`. -/
theorem toC_coeffRaw_cstar (p : CPoly) (w : List Letter) :
    GInt.toC (coeffRaw (cstar p) w) = star (GInt.toC (coeffRaw p w.reverse)) := by
  induction p with
  | nil => simp [cstar, coeffRaw_nil]
  | cons m p ih =>
    simp only [cstar, List.map_cons] at ih ⊢
    rw [coeffRaw_cons, coeffRaw_cons]
    have hiff : m.1.reverse = w ↔ m.1 = w.reverse := List.reverse_eq_iff
    by_cases h : m.1 = w.reverse
    · rw [if_pos (hiff.mpr h), if_pos h]
      simp [ih]
    · rw [if_neg (mt hiff.mp h), if_neg h, ih]

/-! ## Distinct words and dominance -/

/-- `List.dedup` as a right fold that keeps an element when it does not occur later. -/
theorem dedup_eq_foldr {β : Type*} [DecidableEq β] (l : List β) :
    l.dedup = l.foldr (fun a acc => if a ∈ acc then acc else a :: acc) [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ← ih]
    by_cases h : a ∈ l
    · rw [List.dedup_cons_of_mem h, if_pos (List.mem_dedup.mpr h)]
    · rw [List.dedup_cons_of_notMem h, if_neg (mt List.mem_dedup.mp h)]

/-- The distinct words of `l` are the words of its monomials. -/
theorem mem_words {l : CPoly} {w : List Letter} : w ∈ words l ↔ w ∈ l.map Prod.fst :=
  List.mem_dedup

/-- The distinct words of `l` have no duplicates. -/
theorem nodup_words (l : CPoly) : (words l).Nodup := List.nodup_dedup _

/-- The off-diagonal mass as a finite sum over the nonempty words of `l`. -/
theorem offMass_eq_sum (l : CPoly) :
    offMass l = ∑ w ∈ (l.map Prod.fst).toFinset.erase [], taxi (coeffRaw l w) := by
  have hnd : ((words l).filter fun w => w ≠ []).Nodup := (nodup_words l).filter _
  rw [offMass, ← List.sum_toFinset _ hnd]
  congr 1
  ext w
  simp [mem_words, and_comm]

/-- The off-diagonal mass as a finite sum over the nonempty words of any set containing the
words of `l`. -/
theorem offMass_eq_sum_of_subset (l : CPoly) {S : Finset (List Letter)}
    (hS : ∀ m ∈ l, m.1 ∈ S) : offMass l = ∑ w ∈ S.erase [], taxi (coeffRaw l w) := by
  rw [offMass_eq_sum]
  apply Finset.sum_subset
  · intro w hw
    rw [Finset.mem_erase, List.mem_toFinset, List.mem_map] at hw
    obtain ⟨hne, m, hm, rfl⟩ := hw
    exact Finset.mem_erase.mpr ⟨hne, hS m hm⟩
  · intro w hwS hw
    have hw' : w ∉ l.map Prod.fst := fun h =>
      hw (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hwS).1, List.mem_toFinset.mpr h⟩)
    rw [coeffRaw_eq_zero_of_notMem hw', taxi_zero]

/-- The real part of a merged coefficient, read as an integer. -/
theorem toInt_coeffRaw_fst (l : CPoly) (w : List Letter) :
    (((coeffRaw l w).1.toInt : ℤ) : ℝ) = (GInt.toC (coeffRaw l w)).re :=
  (GInt.re_toC _).symm

/-- Dominance in real numbers. -/
theorem isDominant_iff (l : CPoly) :
    IsDominant l ↔ (offMass l : ℝ) < (GInt.toC (coeffRaw l [])).re := by
  rw [IsDominant, PInt.lt'_iff, PInt.toInt_ofNat, GInt.re_toC]
  norm_cast

/-- Dominance as the strict inequality `Σ_{w ≠ ∅} (|Re l_w| + |Im l_w|) < Re l_∅`, the sum over
the nonempty words of any set containing the words of `l`. -/
theorem isDominant_iff_sum (l : CPoly) {S : Finset (List Letter)} (hS : ∀ m ∈ l, m.1 ∈ S) :
    IsDominant l ↔ ∑ w ∈ S.erase [], (|(GInt.toC (coeffRaw l w)).re| +
      |(GInt.toC (coeffRaw l w)).im|) < (GInt.toC (coeffRaw l [])).re := by
  rw [isDominant_iff, offMass_eq_sum_of_subset l hS]
  push_cast
  simp_rw [taxi_eq]

/-! ## Validity -/

section Validity

variable {nX nA : ℕ}

/-- A concatenation of words is valid iff both words are. -/
theorem validWord_append {w w' : List Letter} :
    ValidWord nX nA (w ++ w') ↔ ValidWord nX nA w ∧ ValidWord nX nA w' :=
  List.forall_mem_append

/-- A reversed word is valid iff the word is. -/
theorem validWord_reverse {w : List Letter} : ValidWord nX nA w.reverse ↔ ValidWord nX nA w := by
  simp [ValidWord]

/-- A concatenation of coded polynomials is valid iff both are. -/
theorem validCPoly_append {p q : CPoly} :
    ValidCPoly nX nA (p ++ q) ↔ ValidCPoly nX nA p ∧ ValidCPoly nX nA q :=
  List.forall_mem_append

/-- Negation preserves and reflects validity. -/
theorem validCPoly_cneg {p : CPoly} : ValidCPoly nX nA (cneg p) ↔ ValidCPoly nX nA p := by
  simp only [ValidCPoly, cneg, List.forall_mem_map]

/-- Scaling preserves and reflects validity. -/
theorem validCPoly_cscale {c : GInt} {p : CPoly} :
    ValidCPoly nX nA (cscale c p) ↔ ValidCPoly nX nA p := by
  simp only [ValidCPoly, cscale, List.forall_mem_map]

/-- The star preserves and reflects validity. -/
theorem validCPoly_cstar {p : CPoly} : ValidCPoly nX nA (cstar p) ↔ ValidCPoly nX nA p := by
  simp only [ValidCPoly, cstar, List.forall_mem_map, validWord_reverse]

/-- A product of valid coded polynomials is valid. -/
theorem validCPoly_cmul {p q : CPoly} (hp : ValidCPoly nX nA p) (hq : ValidCPoly nX nA q) :
    ValidCPoly nX nA (cmul p q) := by
  intro m hm
  simp only [cmul, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hm
  exact validWord_append.mpr ⟨hp m₁ hm₁, hq m₂ hm₂⟩

/-- A coded constant is valid. -/
theorem validCPoly_cconst (c : GInt) : ValidCPoly nX nA (cconst c) := by
  simp [ValidCPoly, cconst, ValidWord]

/-- The monomial of a valid word is valid. -/
theorem validCPoly_cword {w : List Letter} (h : ValidWord nX nA w) :
    ValidCPoly nX nA (cword w) := by
  simpa [ValidCPoly, cword] using h

/-- The polynomial of a valid letter is valid. -/
theorem validCPoly_cletter {l : Letter} (h : ValidLetter nX nA l) :
    ValidCPoly nX nA (cletter l) :=
  validCPoly_cword (by simpa [ValidWord] using h)

/-- The relation polynomial of a valid relation index is valid. -/
theorem validCPoly_relPoly {ρ : RelIdx} (h : ValidRel nX nA ρ) :
    ValidCPoly nX nA (relPoly nA ρ) := by
  rcases ρ with x | y | ⟨x, y, a, b⟩
  · refine validCPoly_append.mpr ⟨?_, validCPoly_cconst _⟩
    intro m hm
    simp only [List.mem_map, List.mem_range] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    simp only [ValidRel] at h
    simp [ValidWord]
    omega
  · refine validCPoly_append.mpr ⟨?_, validCPoly_cconst _⟩
    intro m hm
    simp only [List.mem_map, List.mem_range] at hm
    obtain ⟨b, hb, rfl⟩ := hm
    simp only [ValidRel] at h
    simp [ValidWord]
    omega
  · simp only [ValidRel] at h
    simp [relPoly, commPoly, ValidCPoly, ValidWord, h]

/-- The integer game polynomial of a description is valid for its alphabets. -/
theorem validCPoly_Wint (d : GameData) : ValidCPoly d.nX d.nA (Wint d) := by
  intro m hm
  simp only [Wint, List.mem_flatMap, List.mem_map, List.mem_range] at hm
  obtain ⟨x, hx, y, hy, a, ha, b, hb, rfl⟩ := hm
  simp [ValidWord]
  omega

/-- The polynomial of a valid optional letter is valid. -/
theorem validCPoly_optPoly {g : Option Letter} (h : ValidOptLetter nX nA g) :
    ValidCPoly nX nA (optPoly g) := by
  cases g with
  | none => exact validCPoly_cconst _
  | some l => exact validCPoly_cletter h

/-- A sum of squares with valid terms is valid. -/
theorem validCPoly_sosSum {sos : List (Option Letter × CPoly)}
    (h : ∀ t ∈ sos, ValidOptLetter nX nA t.1 ∧ ValidCPoly nX nA t.2) :
    ValidCPoly nX nA (sosSum sos) := by
  intro m hm
  simp only [sosSum, List.mem_flatMap] at hm
  obtain ⟨t, ht, hm⟩ := hm
  exact validCPoly_cmul (validCPoly_cmul (validCPoly_cstar.mpr (h t ht).2)
    (validCPoly_optPoly (h t ht).1)) (h t ht).2 m hm

/-- An ideal element with valid monomials is valid. -/
theorem validCPoly_idealSum {ideal : List (GInt × List Letter × RelIdx × List Letter)}
    (h : ∀ t ∈ ideal, ValidWord nX nA t.2.1 ∧ ValidRel nX nA t.2.2.1 ∧ ValidWord nX nA t.2.2.2) :
    ValidCPoly nX nA (idealSum nA ideal) := by
  intro m hm
  simp only [idealSum, List.mem_flatMap] at hm
  obtain ⟨t, ht, hm⟩ := hm
  obtain ⟨h1, h2, h3⟩ := h t ht
  exact validCPoly_cscale.mpr (validCPoly_cmul (validCPoly_cmul (validCPoly_cword h1)
    (validCPoly_relPoly h2)) (validCPoly_cword h3)) m hm

/-- The residual of a valid certificate is valid. -/
theorem validCPoly_certR {d : GameData} {cert : Cert} (h : ValidCert d.nX d.nA cert) (p q : ℕ) :
    ValidCPoly d.nX d.nA (certR d p q cert) := by
  refine validCPoly_append.mpr ⟨validCPoly_append.mpr ⟨validCPoly_append.mpr
    ⟨validCPoly_cscale.mpr (validCPoly_cconst _),
      validCPoly_cneg.mpr (validCPoly_cscale.mpr (validCPoly_Wint d))⟩,
    validCPoly_cneg.mpr (validCPoly_sosSum h.1)⟩, validCPoly_cneg.mpr (validCPoly_idealSum h.2)⟩

/-- The hermitian residual of a valid certificate is valid. -/
theorem validCPoly_certRh {d : GameData} {cert : Cert} (h : ValidCert d.nX d.nA cert)
    (p q : ℕ) : ValidCPoly d.nX d.nA (certRh d p q cert) :=
  validCPoly_append.mpr ⟨validCPoly_certR h p q, validCPoly_cstar.mpr (validCPoly_certR h p q)⟩

end Validity

/-! ## Primitive recursiveness: coefficients and operations -/

/-- Negation of coded Gaussian integers is primitive recursive. -/
theorem primrec_gneg : Primrec gneg :=
  (PInt.primrec_neg.comp fst).pair (PInt.primrec_neg.comp snd)

/-- The absolute value `ptaxi` of a coded integer is primitive recursive. -/
theorem primrec_ptaxi : Primrec ptaxi :=
  nat_add.comp (nat_sub.comp fst snd) (nat_sub.comp snd fst)

/-- The taxicab norm is primitive recursive. -/
theorem primrec_taxi : Primrec taxi :=
  nat_add.comp (primrec_ptaxi.comp fst) (primrec_ptaxi.comp snd)

/-- The sum of coded polynomials is primitive recursive. -/
theorem primrec_cadd : Primrec₂ cadd := list_append

/-- The negation of coded polynomials is primitive recursive. -/
theorem primrec_cneg : Primrec cneg :=
  list_map Primrec.id ((fst.comp snd).pair (primrec_gneg.comp (snd.comp snd))).to₂

/-- The multiple of a coded polynomial is primitive recursive. -/
theorem primrec_cscale : Primrec₂ cscale :=
  list_map snd ((fst.comp snd).pair (GInt.primrec_mul.comp (fst.comp fst) (snd.comp snd))).to₂

/-- The product of coded polynomials is primitive recursive. -/
theorem primrec_cmul : Primrec₂ cmul := by
  -- the inner map, at `((p, q), m)`, over `m' ∈ q`
  have hinner : Primrec₂ fun (x : CPoly × CPoly) (m : List Letter × GInt) =>
      x.2.map fun m' => (m.1 ++ m'.1, GInt.mul m.2 m'.2) :=
    list_map (snd.comp fst)
      ((list_append.comp (fst.comp (snd.comp fst)) (fst.comp snd)).pair
        (GInt.primrec_mul.comp (snd.comp (snd.comp fst)) (snd.comp snd))).to₂
  exact list_flatMap fst hinner

/-- The star of coded polynomials is primitive recursive. -/
theorem primrec_cstar : Primrec cstar :=
  list_map Primrec.id
    ((list_reverse.comp (fst.comp snd)).pair (GInt.primrec_conj.comp (snd.comp snd))).to₂

/-- The constant coded polynomial is primitive recursive. -/
theorem primrec_cconst : Primrec cconst :=
  list_cons.comp ((const []).pair Primrec.id) (const [])

/-- The monomial of a word is primitive recursive. -/
theorem primrec_cword : Primrec cword :=
  list_cons.comp (Primrec.id.pair (const (GInt.ofNat 1))) (const [])

/-- The polynomial of a letter is primitive recursive. -/
theorem primrec_cletter : Primrec cletter :=
  primrec_cword.comp (list_cons.comp Primrec.id (const []))

/-- The merged coefficient is primitive recursive. -/
theorem primrec_coeffRaw : Primrec₂ coeffRaw := by
  have hR : PrimrecRel fun (m : List Letter × GInt) (w : List Letter) => m.1 = w :=
    Primrec.eq.comp (fst.comp fst) snd
  have hmap := list_map hR.listFilter (snd.comp snd).to₂
  exact (GInt.primrec_sum.comp hmap).of_eq fun _ => rfl

/-- `List.dedup` is primitive recursive. -/
theorem primrec_dedup {β : Type*} [Primcodable β] [DecidableEq β] :
    Primrec (List.dedup : List β → List β) := by
  have hmem : PrimrecRel fun (acc : List β) (a : β) => a ∈ acc :=
    (PrimrecRel.exists_mem_list (R := fun b a : β => b = a) Primrec.eq).of_eq fun acc a => by
      simp
  have hstep : Primrec₂ fun (_ : List β) (p : β × List β) =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2 :=
    (Primrec.ite (hmem.comp (snd.comp snd) (fst.comp snd)) (snd.comp snd)
      (list_cons.comp (fst.comp snd) (snd.comp snd))).to₂
  exact (list_foldr Primrec.id (const []) hstep).of_eq fun l => (dedup_eq_foldr l).symm

/-- The distinct words of a coded polynomial are primitive recursive. -/
theorem primrec_words : Primrec words :=
  primrec_dedup.comp (list_map Primrec.id (fst.comp snd).to₂)

/-- The off-diagonal mass is primitive recursive. -/
theorem primrec_offMass : Primrec offMass := by
  have hne : PrimrecPred fun w : List Letter => w ≠ [] :=
    PrimrecPred.not (Primrec.eq.comp Primrec.id (const []))
  have hfilt := (Primrec.listFilter hne).comp primrec_words
  have hmap := list_map hfilt (primrec_taxi.comp (primrec_coeffRaw.comp fst snd)).to₂
  exact (primrec_natSum.comp hmap).of_eq fun _ => rfl

/-- Dominance is a primitive recursive predicate. -/
theorem primrecPred_isDominant : PrimrecPred IsDominant :=
  (PInt.primrecRel_lt'.comp (PInt.primrec_ofNat.comp primrec_offMass)
    (fst.comp (primrec_coeffRaw.comp Primrec.id (const [])))).of_eq fun _ => Iff.rfl

/-! ## Primitive recursiveness: validation -/

/-- The question index of a letter is primitive recursive. -/
theorem primrec_letterQ : Primrec letterQ :=
  (sumCasesOn Primrec.id (fst.comp snd).to₂ (fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

/-- The answer index of a letter is primitive recursive. -/
theorem primrec_letterA : Primrec letterA :=
  (sumCasesOn Primrec.id (snd.comp snd).to₂ (snd.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

/-- Validity of a letter is primitive recursive in the letter and the bounds `(nX, nA)`. -/
theorem primrecRel_validLetter :
    PrimrecRel fun (l : Letter) (n : ℕ × ℕ) => ValidLetter n.1 n.2 l :=
  (PrimrecPred.and (nat_le.comp (primrec_letterQ.comp fst) (fst.comp snd))
    (nat_le.comp (primrec_letterA.comp fst) (snd.comp snd))).of_eq fun _ => Iff.rfl

/-- Validity of a word is primitive recursive in the word and the bounds. -/
theorem primrecRel_validWord :
    PrimrecRel fun (w : List Letter) (n : ℕ × ℕ) => ValidWord n.1 n.2 w :=
  (PrimrecRel.forall_mem_list primrecRel_validLetter).of_eq fun _ _ => Iff.rfl

/-- Validity of a coded polynomial is primitive recursive. -/
theorem primrecRel_validCPoly :
    PrimrecRel fun (p : CPoly) (n : ℕ × ℕ) => ValidCPoly n.1 n.2 p :=
  (PrimrecRel.forall_mem_list (R := fun (m : List Letter × GInt) (n : ℕ × ℕ) =>
    ValidWord n.1 n.2 m.1) (primrecRel_validWord.comp (fst.comp fst) snd)).of_eq
      fun _ _ => Iff.rfl

/-- Validity of an optional letter is primitive recursive. -/
theorem primrecRel_validOptLetter :
    PrimrecRel fun (g : Option Letter) (n : ℕ × ℕ) => ValidOptLetter n.1 n.2 g := by
  have hl : Primrec₂ fun (x : Option Letter × (ℕ × ℕ)) (l : Letter) =>
      decide (ValidLetter x.2.1 x.2.2 l) :=
    (primrecRel_validLetter.decide.comp snd (snd.comp fst)).to₂
  refine ⟨inferInstance, (option_casesOn fst (const true) hl).of_eq fun x => ?_⟩
  rcases x with ⟨_ | l, n⟩ <;> rfl

/-- Validity of a relation index is primitive recursive. -/
theorem primrecRel_validRel :
    PrimrecRel fun (ρ : RelIdx) (n : ℕ × ℕ) => ValidRel n.1 n.2 ρ := by
  have hA : Primrec₂ fun (x : RelIdx × (ℕ × ℕ)) (i : ℕ) => decide (i ≤ x.2.1) :=
    (nat_le.decide.comp snd (fst.comp (snd.comp fst))).to₂
  have hC : Primrec₂ fun (x : (RelIdx × (ℕ × ℕ)) × (ℕ ⊕ ℕ × ℕ × ℕ × ℕ)) (t : ℕ × ℕ × ℕ × ℕ) =>
      decide (t.1 ≤ x.1.2.1 ∧ t.2.1 ≤ x.1.2.1 ∧ t.2.2.1 ≤ x.1.2.2 ∧ t.2.2.2 ≤ x.1.2.2) := by
    have hnX : Primrec fun z : ((RelIdx × (ℕ × ℕ)) × (ℕ ⊕ ℕ × ℕ × ℕ × ℕ)) ×
        (ℕ × ℕ × ℕ × ℕ) => z.1.1.2.1 := fst.comp (snd.comp (fst.comp fst))
    have hnA : Primrec fun z : ((RelIdx × (ℕ × ℕ)) × (ℕ ⊕ ℕ × ℕ × ℕ × ℕ)) ×
        (ℕ × ℕ × ℕ × ℕ) => z.1.1.2.2 := snd.comp (snd.comp (fst.comp fst))
    exact (PrimrecPred.and (nat_le.comp (fst.comp snd) hnX)
      (PrimrecPred.and (nat_le.comp (fst.comp (snd.comp snd)) hnX)
        (PrimrecPred.and (nat_le.comp (fst.comp (snd.comp (snd.comp snd))) hnA)
          (nat_le.comp (snd.comp (snd.comp (snd.comp snd))) hnA)))).decide.to₂
  have hB' : Primrec₂ fun (x : (RelIdx × (ℕ × ℕ)) × (ℕ ⊕ ℕ × ℕ × ℕ × ℕ)) (y : ℕ) =>
      decide (y ≤ x.1.2.1) :=
    (nat_le.decide.comp snd (fst.comp (snd.comp (fst.comp fst)))).to₂
  have hB := (sumCasesOn snd hB' hC).to₂
  refine ⟨inferInstance, (sumCasesOn fst hA hB).of_eq fun x => ?_⟩
  rcases x with ⟨x | y | t, n⟩ <;> rfl

/-- Validity of a certificate is primitive recursive. -/
theorem primrecRel_validCert :
    PrimrecRel fun (cert : Cert) (n : ℕ × ℕ) => ValidCert n.1 n.2 cert := by
  have hsos := PrimrecRel.forall_mem_list
    (R := fun (t : Option Letter × CPoly) (n : ℕ × ℕ) =>
      ValidOptLetter n.1 n.2 t.1 ∧ ValidCPoly n.1 n.2 t.2)
    (PrimrecPred.and (primrecRel_validOptLetter.comp (fst.comp fst) snd)
      (primrecRel_validCPoly.comp (snd.comp fst) snd))
  have hideal := PrimrecRel.forall_mem_list
    (R := fun (t : GInt × List Letter × RelIdx × List Letter) (n : ℕ × ℕ) =>
      ValidWord n.1 n.2 t.2.1 ∧ ValidRel n.1 n.2 t.2.2.1 ∧ ValidWord n.1 n.2 t.2.2.2)
    (PrimrecPred.and (primrecRel_validWord.comp (fst.comp (snd.comp fst)) snd)
      (PrimrecPred.and (primrecRel_validRel.comp (fst.comp (snd.comp (snd.comp fst))) snd)
        (primrecRel_validWord.comp (snd.comp (snd.comp (snd.comp fst))) snd)))
  exact (PrimrecPred.and (hsos.comp (fst.comp (snd.comp fst)) snd)
    (hideal.comp (snd.comp (snd.comp fst)) snd)).of_eq fun _ => Iff.rfl

/-! ## Primitive recursiveness: relations and the game polynomial -/

/-- The first player's coded normalization is primitive recursive. -/
theorem primrec_aliceNorm : Primrec₂ aliceNorm :=
  list_append.comp
    (list_map (list_range.comp (succ.comp fst))
      ((list_cons.comp (sumInl.comp ((snd.comp fst).pair snd)) (const [])).pair
        (const (GInt.ofNat 1))).to₂)
    (const (cconst (gneg (GInt.ofNat 1))))

/-- The second player's coded normalization is primitive recursive. -/
theorem primrec_bobNorm : Primrec₂ bobNorm :=
  list_append.comp
    (list_map (list_range.comp (succ.comp fst))
      ((list_cons.comp (sumInr.comp ((snd.comp fst).pair snd)) (const [])).pair
        (const (GInt.ofNat 1))).to₂)
    (const (cconst (gneg (GInt.ofNat 1))))

/-- The coded commutator is primitive recursive. -/
theorem primrec_commPoly : Primrec commPoly := by
  have he : Primrec fun t : ℕ × ℕ × ℕ × ℕ => (Sum.inl (t.1, t.2.2.1) : Letter) :=
    sumInl.comp (fst.pair (fst.comp (snd.comp snd)))
  have hf : Primrec fun t : ℕ × ℕ × ℕ × ℕ => (Sum.inr (t.2.1, t.2.2.2) : Letter) :=
    sumInr.comp ((fst.comp snd).pair (snd.comp (snd.comp snd)))
  have hef := list_cons.comp he (list_cons.comp hf (const []))
  have hfe := list_cons.comp hf (list_cons.comp he (const []))
  exact list_cons.comp (hef.pair (const (GInt.ofNat 1)))
    (list_cons.comp (hfe.pair (const (gneg (GInt.ofNat 1)))) (const []))

/-- The relation polynomial is primitive recursive. -/
theorem primrec_relPoly : Primrec₂ relPoly := by
  have hb : Primrec₂ fun (x : (ℕ × RelIdx) × (ℕ ⊕ ℕ × ℕ × ℕ × ℕ)) (y : ℕ) => bobNorm x.1.1 y :=
    (primrec_bobNorm.comp (fst.comp (fst.comp fst)) snd).to₂
  have hc : Primrec₂ fun (_ : (ℕ × RelIdx) × (ℕ ⊕ ℕ × ℕ × ℕ × ℕ)) (t : ℕ × ℕ × ℕ × ℕ) =>
      commPoly t :=
    (primrec_commPoly.comp snd).to₂
  have hB := (sumCasesOn snd hb hc).to₂
  exact (sumCasesOn snd (primrec_aliceNorm.comp (fst.comp fst) snd).to₂ hB).of_eq fun x => by
    rcases x with ⟨nA, x | y | t⟩ <;> rfl

/-- The contexts of `Wint`, from the innermost level `((((d, x), y), a), b)` out. -/
abbrev WCtx4 := (((GameData × ℕ) × ℕ) × ℕ) × ℕ
/-- The context `(((d, x), y), a)` of the map over `b` in `Wint`. -/
abbrev WCtx3 := ((GameData × ℕ) × ℕ) × ℕ
/-- The context `((d, x), y)` of the map over `a` in `Wint`. -/
abbrev WCtx2 := (GameData × ℕ) × ℕ

/-- The innermost term of `Wint`. -/
theorem primrec_WintBody : Primrec fun z : WCtx4 =>
    (([Sum.inl (z.1.1.1.2, z.1.2), Sum.inr (z.1.1.2, z.2)] : List Letter),
      GInt.ofNat (wt z.1.1.1.1 z.1.1.1.2 z.1.1.2 *
        if Draw z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 then 1 else 0)) := by
  have hd : Primrec fun z : WCtx4 => z.1.1.1.1 := fst.comp (fst.comp (fst.comp fst))
  have hx : Primrec fun z : WCtx4 => z.1.1.1.2 := snd.comp (fst.comp (fst.comp fst))
  have hy : Primrec fun z : WCtx4 => z.1.1.2 := snd.comp (fst.comp fst)
  have ha : Primrec fun z : WCtx4 => z.1.2 := snd.comp fst
  have hb : Primrec fun z : WCtx4 => z.2 := snd
  have hwt := primrec_wt.comp (hd.pair (hx.pair hy))
  have hD := primrec_Draw.comp (hd.pair (hx.pair (hy.pair (ha.pair hb))))
  have hind := Primrec.ite (Primrec.eq.comp hD (const true)) (const 1) (const 0)
  have hcoef := GInt.primrec_ofNat.comp (nat_mul.comp hwt hind)
  have he : Primrec fun z : WCtx4 => (Sum.inl (z.1.1.1.2, z.1.2) : Letter) :=
    sumInl.comp (hx.pair ha)
  have hf : Primrec fun z : WCtx4 => (Sum.inr (z.1.1.2, z.2) : Letter) :=
    sumInr.comp (hy.pair hb)
  exact (list_cons.comp he (list_cons.comp hf (const []))).pair hcoef

/-- The map over `b` in `Wint`, in the context `(((d, x), y), a)`, is primitive recursive. -/
theorem primrec_Wint3 : Primrec fun z : WCtx3 =>
    (List.range (z.1.1.1.nA + 1)).map fun b =>
      (([Sum.inl (z.1.1.2, z.2), Sum.inr (z.1.2, b)] : List Letter),
        GInt.ofNat (wt z.1.1.1 z.1.1.2 z.1.2 *
          if Draw z.1.1.1 z.1.1.2 z.1.2 z.2 b then 1 else 0)) :=
  list_map (list_range.comp (succ.comp (GameData.primrec_nA.comp (fst.comp (fst.comp fst)))))
    primrec_WintBody.to₂

/-- The map over `a` in `Wint`, in the context `((d, x), y)`, is primitive recursive. -/
theorem primrec_Wint2 : Primrec fun z : WCtx2 =>
    (List.range (z.1.1.nA + 1)).flatMap fun a => (List.range (z.1.1.nA + 1)).map fun b =>
      (([Sum.inl (z.1.2, a), Sum.inr (z.2, b)] : List Letter),
        GInt.ofNat (wt z.1.1 z.1.2 z.2 * if Draw z.1.1 z.1.2 z.2 a b then 1 else 0)) :=
  list_flatMap (list_range.comp (succ.comp (GameData.primrec_nA.comp (fst.comp fst))))
    primrec_Wint3.to₂

/-- The map over `y` in `Wint`, in the context `(d, x)`, is primitive recursive. -/
theorem primrec_Wint1 : Primrec fun z : GameData × ℕ =>
    (List.range (z.1.nX + 1)).flatMap fun y =>
      (List.range (z.1.nA + 1)).flatMap fun a => (List.range (z.1.nA + 1)).map fun b =>
        (([Sum.inl (z.2, a), Sum.inr (y, b)] : List Letter),
          GInt.ofNat (wt z.1 z.2 y * if Draw z.1 z.2 y a b then 1 else 0)) :=
  list_flatMap (list_range.comp (succ.comp (GameData.primrec_nX.comp fst))) primrec_Wint2.to₂

/-- The integer game polynomial is primitive recursive. -/
theorem primrec_Wint : Primrec Wint :=
  (list_flatMap (list_range.comp (succ.comp GameData.primrec_nX)) primrec_Wint1.to₂).of_eq
    fun _ => rfl

/-! ## Primitive recursiveness: certificates and the check -/

/-- The polynomial of an optional letter is primitive recursive. -/
theorem primrec_optPoly : Primrec optPoly :=
  (option_casesOn Primrec.id (const (cconst (GInt.ofNat 1))) (primrec_cletter.comp snd).to₂).of_eq
    fun g => by cases g <;> rfl

/-- The sum of squares of a list of terms is primitive recursive. -/
theorem primrec_sosSum : Primrec sosSum :=
  list_flatMap Primrec.id
    (primrec_cmul.comp
      (primrec_cmul.comp (primrec_cstar.comp (snd.comp snd)) (primrec_optPoly.comp (fst.comp snd)))
      (snd.comp snd)).to₂

/-- The ideal element of a list of monomials is primitive recursive. -/
theorem primrec_idealSum : Primrec₂ idealSum := by
  have ht : Primrec fun y : (ℕ × List (GInt × List Letter × RelIdx × List Letter)) ×
      (GInt × List Letter × RelIdx × List Letter) => y.2 := snd
  have hw := primrec_cword.comp (fst.comp (snd.comp ht))
  have hρ := primrec_relPoly.comp (fst.comp fst) (fst.comp (snd.comp (snd.comp ht)))
  have hw' := primrec_cword.comp (snd.comp (snd.comp (snd.comp ht)))
  exact list_flatMap snd
    (primrec_cscale.comp (fst.comp ht) (primrec_cmul.comp (primrec_cmul.comp hw hρ) hw')).to₂

/-- The residual of a certificate is primitive recursive. -/
theorem primrec_certR :
    Primrec fun x : (GameData × ℕ × ℕ) × Cert => certR x.1.1 x.1.2.1 x.1.2.2 x.2 := by
  have hd : Primrec fun x : (GameData × ℕ × ℕ) × Cert => x.1.1 := fst.comp fst
  have hp : Primrec fun x : (GameData × ℕ × ℕ) × Cert => x.1.2.1 := fst.comp (snd.comp fst)
  have hq : Primrec fun x : (GameData × ℕ × ℕ) × Cert => x.1.2.2 := snd.comp (snd.comp fst)
  have hN : Primrec fun x : (GameData × ℕ × ℕ) × Cert => x.2.1 := fst.comp snd
  have hNN := nat_mul.comp hN hN
  have h1 := primrec_cscale.comp
    (GInt.primrec_ofNat.comp (nat_mul.comp (nat_mul.comp hNN hp) (primrec_W.comp hd)))
    (const (cconst (GInt.ofNat 1)))
  have h2 := primrec_cneg.comp (primrec_cscale.comp
    (GInt.primrec_ofNat.comp (nat_mul.comp hNN hq)) (primrec_Wint.comp hd))
  have hsos : Primrec fun x : (GameData × ℕ × ℕ) × Cert => x.2.2.1 := fst.comp (snd.comp snd)
  have hideal : Primrec fun x : (GameData × ℕ × ℕ) × Cert => x.2.2.2 := snd.comp (snd.comp snd)
  have h3 := primrec_cneg.comp (primrec_sosSum.comp hsos)
  have h4 := primrec_cneg.comp (primrec_idealSum.comp (GameData.primrec_nA.comp hd) hideal)
  exact (list_append.comp (list_append.comp (list_append.comp h1 h2) h3) h4).of_eq fun _ => rfl

/-- The hermitian residual of a certificate is primitive recursive. -/
theorem primrec_certRh :
    Primrec fun x : (GameData × ℕ × ℕ) × Cert => certRh x.1.1 x.1.2.1 x.1.2.2 x.2 :=
  list_append.comp primrec_certR (primrec_cstar.comp primrec_certR)

/-- **The upper certificate check is primitive recursive.** -/
theorem primrecRel_checkUpper : PrimrecRel CheckUpper := by
  have hn : Primrec fun x : (GameData × ℕ × ℕ) × Cert => (x.1.1.nX, x.1.1.nA) :=
    (GameData.primrec_nX.comp (fst.comp fst)).pair (GameData.primrec_nA.comp (fst.comp fst))
  exact (PrimrecPred.and (nat_lt.comp (const 0) (snd.comp (snd.comp fst)))
    (PrimrecPred.and (nat_le.comp (const 1) (fst.comp snd))
      (PrimrecPred.and (primrecRel_validCert.comp snd hn)
        (primrecPred_isDominant.comp primrec_certRh)))).of_eq fun _ => Iff.rfl

end MIPRE.Tsirelson.Coded
