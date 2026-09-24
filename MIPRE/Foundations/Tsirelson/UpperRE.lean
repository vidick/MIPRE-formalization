/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Tsirelson.Certificate
import MIPRE.Foundations.Tsirelson.Closed
import MIPRE.Foundations.Tsirelson.CodedPoly
import MIPRE.Foundations.ValueApprox.RawSemantics
import MIPRE.Foundations.ValueApprox.RE

/-!
# The commuting-operator value is recursively enumerable from above

Step §3.6 of the Tsirelson route (`planning/tsirelson-campaign.md`): the coded certificate check
`MIPRE.Tsirelson.Coded.CheckUpper` of `MIPRE.Foundations.Tsirelson.CodedPoly` decides exactly the
certificates of `MIPRE.Foundations.Tsirelson.Certificate`, so the thresholds above the
commuting-operator value of a described game form a recursively enumerable set
(`commutingUpperRE`, blueprint `lem:valco-upper-re`), and with the halting reduction the
negative answer to Tsirelson's problem follows (`tsirelson_of_haltingReduction`).

**Decoding.** For a game description `d` with `nX`, `nA`, both players of `d.game` have questions
`Fin (nX + 1)` and answers `Fin (nA + 1)`, and the letters of its game algebra are
`FinGen nX nA`. A coded letter `inl (x, a)` decodes to `e_xa` and `inr (y, b)` to `f_yb`, with the
indices clamped into range (`decodeLetter`), a coded word to the product of its letters
(`decodeWord`), and a coded polynomial `[(w, c), …]` to `Σ c · w` (`interp`). The decoding is a
homomorphism for every coded operation, with no validity hypothesis: sums (`interp_append`),
negation, scaling, products (`interp_cmul`) and the star (`interp_cstar`). Every relation index
decodes to one of the relations `rels` (`interp_relPoly_mem`), and every relation is the decoding
of a valid index (`exists_relIdx`). The coded game polynomial is `W_d` times the game polynomial
(`interp_Wint`), since `μ(x, y) = wt(x, y) / W_d` and the predicates agree.

**Coefficients.** On valid letters, `encodeLetter` is a left inverse of the decoding, so
`decodeWord` is injective on valid words (`decodeWord_injOn`). Hence the merged coefficient of a
valid word in a valid coded polynomial is the coefficient of its decoding
(`coeff_interp`), the support of the decoding lies in the decoded words
(`support_interp_subset`), and the coded dominance test is the dominance of the decoding
(`isDominant_iff_dominant_interp`).

**The check.** A certificate decodes to a scale `N`, hermitian squares and ideal monomials
(`decodeSos`, `decodeIdeal`), and its residual to

  `N² (κ r·1 - κ W_G) - Σ s⋆ g s - Σ c · w ρ w'`,  `κ = q·W_d`, `r = p / q`

(`interp_certR_eq`), the residual of `Certificate`. So an accepted certificate bounds the value
below `p / q` (`checkUpper_sound`, by `commutingOperatorValue_lt_of_certificate`). Conversely, if
the value is below `p / q`, then `q > 0` (for `q = 0` the threshold is `0`, and the value is
nonnegative), and `exists_certificate_of_lt` gives a certificate with Gaussian-integer
coefficients, which is encoded exactly (`encodeC`, `encodePoly`, `encodeSos`, `encodeIdeal`) into
an accepted coded certificate (`checkUpper_complete`).

## Main declarations

* `FinGen`, `FinRels`, `decodeLetter`, `encodeLetter`, `decodeWord`, `encodeWord`,
  `decodeWord_injOn`;
* `interp`, `interp_append`, `interp_cneg`, `interp_cscale`, `interp_cmul`, `interp_cstar`,
  `interp_relPoly_mem`, `exists_relIdx`, `interp_Wint`;
* `coeff_interp`, `support_interp_subset`, `isDominant_iff_dominant_interp`;
* `decodeSos`, `decodeIdeal`, `interp_certR_eq`, `checkUpper_sound`;
* `encodeC`, `encodePoly`, `encodeSos`, `encodeIdeal`, `checkUpper_complete`, `checkUpper_iff`;
* `MIPRE.commutingUpperRE`, `MIPRE.tsirelson_of_haltingReduction`.
-/

noncomputable section

open ComplexConjugate

namespace MIPRE

namespace Tsirelson

open NCPoly
open MIPRE.ValueApprox
open HaltingGameValue (GameData)
open Coded (Letter CPoly RelIdx Cert cadd cneg cscale cmul cstar cconst cword cletter coeffRaw
  ValidLetter ValidWord ValidCPoly ValidRel ValidCert optPoly aliceNorm bobNorm
  commPoly relPoly Wint sosSum idealSum certR certRh CheckUpper)

/-! ## Letters and words -/

/-- The letters of the game algebra of a described game: both players have questions
`Fin (nX + 1)` and answers `Fin (nA + 1)`. -/
abbrev FinGen (nX nA : ℕ) := Gen (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1))

/-- The relations of the game algebra of a described game. -/
abbrev FinRels (nX nA : ℕ) : Set (NCPoly (FinGen nX nA)) :=
  rels (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1))

/-- A natural clamped into `Fin (n + 1)`. -/
def finOf (n a : ℕ) : Fin (n + 1) := ⟨min a n, Nat.lt_succ_of_le (min_le_right a n)⟩

/-- The clamp is the identity in range. -/
theorem val_finOf {n a : ℕ} (h : a ≤ n) : (finOf n a : ℕ) = a := min_eq_left h

/-- Clamping the value of an element of `Fin (n + 1)` returns it. -/
@[simp] theorem finOf_val {n : ℕ} (i : Fin (n + 1)) : finOf n i = i :=
  Fin.ext (min_eq_left (Nat.lt_succ_iff.mp i.2))

variable {nX nA : ℕ}

/-- The decoding of a coded letter: `inl (x, a)` is `e_xa` and `inr (y, b)` is `f_yb`, with the
indices clamped into range. -/
def decodeLetter (nX nA : ℕ) : Letter → FinGen nX nA :=
  Sum.map (fun t => (finOf nX t.1, finOf nA t.2)) (fun t => (finOf nX t.1, finOf nA t.2))

/-- The code of a letter. -/
def encodeLetter : FinGen nX nA → Letter :=
  Sum.map (fun p => ((p.1 : ℕ), (p.2 : ℕ))) (fun p => ((p.1 : ℕ), (p.2 : ℕ)))

/-- Decoding inverts the code of a letter. -/
@[simp] theorem decodeLetter_encodeLetter (g : FinGen nX nA) :
    decodeLetter nX nA (encodeLetter g) = g := by
  rcases g with ⟨x, a⟩ | ⟨y, b⟩ <;> simp [decodeLetter, encodeLetter]

/-- On valid letters, the code inverts the decoding. -/
theorem encodeLetter_decodeLetter {l : Letter} (h : ValidLetter nX nA l) :
    encodeLetter (decodeLetter nX nA l) = l := by
  rcases l with ⟨x, a⟩ | ⟨y, b⟩ <;>
    simp only [Coded.validLetter_inl, Coded.validLetter_inr] at h <;>
    simp [decodeLetter, encodeLetter, val_finOf h.1, val_finOf h.2]

/-- The code of a letter is valid. -/
theorem validLetter_encodeLetter (g : FinGen nX nA) : ValidLetter nX nA (encodeLetter g) := by
  rcases g with ⟨x, a⟩ | ⟨y, b⟩ <;> simp only [encodeLetter, Sum.map_inl, Sum.map_inr,
    Coded.validLetter_inl, Coded.validLetter_inr] <;> omega

/-- The decoding of a coded word: the product of its decoded letters. -/
def decodeWord (nX nA : ℕ) (w : List Letter) : FreeMonoid (FinGen nX nA) :=
  FreeMonoid.ofList (w.map (decodeLetter nX nA))

/-- The code of a word. -/
def encodeWord (u : FreeMonoid (FinGen nX nA)) : List Letter := u.toList.map encodeLetter

/-- The empty coded word decodes to the empty word. -/
@[simp] theorem decodeWord_nil : decodeWord nX nA [] = 1 := rfl

/-- A one-letter coded word decodes to its letter. -/
@[simp] theorem decodeWord_singleton (l : Letter) :
    decodeWord nX nA [l] = FreeMonoid.of (decodeLetter nX nA l) := rfl

/-- The decoding of words is multiplicative. -/
theorem decodeWord_append (w w' : List Letter) :
    decodeWord nX nA (w ++ w') = decodeWord nX nA w * decodeWord nX nA w' := by
  rw [decodeWord, List.map_append, FreeMonoid.ofList_append]
  rfl

/-- The decoding of words commutes with reversal. -/
theorem decodeWord_reverse (w : List Letter) :
    decodeWord nX nA w.reverse = (decodeWord nX nA w).reverse := by
  rw [decodeWord, List.map_reverse]
  rfl

/-- Only the empty coded word decodes to the empty word. -/
theorem decodeWord_eq_one_iff {w : List Letter} : decodeWord nX nA w = 1 ↔ w = [] := by
  constructor
  · intro h
    have := congrArg FreeMonoid.toList h
    rwa [decodeWord, FreeMonoid.toList_ofList, FreeMonoid.toList_one, List.map_eq_nil_iff] at this
  · rintro rfl
    rfl

/-- Decoding inverts the code of a word. -/
@[simp] theorem decodeWord_encodeWord (u : FreeMonoid (FinGen nX nA)) :
    decodeWord nX nA (encodeWord u) = u := by
  rw [decodeWord, encodeWord, List.map_map]
  exact congrArg FreeMonoid.ofList (List.map_id'' decodeLetter_encodeLetter u.toList)

/-- On valid words, the code inverts the decoding. -/
theorem encodeWord_decodeWord {w : List Letter} (h : ValidWord nX nA w) :
    encodeWord (decodeWord nX nA w) = w := by
  rw [decodeWord, encodeWord, FreeMonoid.toList_ofList, List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun l hl => encodeLetter_decodeLetter (h l hl)

/-- The code of a word is valid. -/
theorem validWord_encodeWord (u : FreeMonoid (FinGen nX nA)) : ValidWord nX nA (encodeWord u) := by
  intro l hl
  obtain ⟨g, -, rfl⟩ := List.mem_map.mp hl
  exact validLetter_encodeLetter g

/-- The decoding is injective on valid words: the code is a left inverse there. -/
theorem decodeWord_injOn {w w' : List Letter} (hw : ValidWord nX nA w) (hw' : ValidWord nX nA w')
    (h : decodeWord nX nA w = decodeWord nX nA w') : w = w' := by
  rw [← encodeWord_decodeWord hw, h, encodeWord_decodeWord hw']

/-! ## Decoding coded polynomials -/

/-- The decoding of a coded polynomial `[(w, c), …]`: the polynomial `Σ c · w`. -/
def interp (nX nA : ℕ) (l : CPoly) : NCPoly (FinGen nX nA) :=
  (l.map fun m => single (decodeWord nX nA m.1) (GInt.toC m.2)).sum

/-- The empty coded polynomial decodes to `0`. -/
@[simp] theorem interp_nil : interp nX nA [] = 0 := rfl

/-- The decoding, one monomial at a time. -/
@[simp] theorem interp_cons (m : List Letter × GInt) (l : CPoly) :
    interp nX nA (m :: l) = single (decodeWord nX nA m.1) (GInt.toC m.2) + interp nX nA l := by
  simp [interp]

/-- The decoding is additive. -/
theorem interp_append (p q : CPoly) : interp nX nA (p ++ q) = interp nX nA p + interp nX nA q := by
  simp [interp]

/-- The decoding of a coded sum. -/
theorem interp_cadd (p q : CPoly) : interp nX nA (cadd p q) = interp nX nA p + interp nX nA q :=
  interp_append p q

/-- The decoding of a coded negation. -/
theorem interp_cneg (p : CPoly) : interp nX nA (cneg p) = -interp nX nA p := by
  induction p with
  | nil => simp [cneg]
  | cons m p ih =>
    simp only [cneg, List.map_cons] at ih ⊢
    rw [interp_cons, ih, interp_cons, Coded.toC_gneg, single_neg, neg_add]

/-- The decoding of a coded multiple. -/
theorem interp_cscale (c : GInt) (p : CPoly) :
    interp nX nA (cscale c p) = GInt.toC c • interp nX nA p := by
  induction p with
  | nil => simp [cscale]
  | cons m p ih =>
    simp only [cscale, List.map_cons] at ih ⊢
    rw [interp_cons, ih, interp_cons, GInt.toC_mul, smul_add, smul_single]

/-- The decoding of a monomial times a coded polynomial. -/
theorem interp_map_mul (m : List Letter × GInt) (q : CPoly) :
    interp nX nA (q.map fun m' => (m.1 ++ m'.1, GInt.mul m.2 m'.2)) =
      single (decodeWord nX nA m.1) (GInt.toC m.2) * interp nX nA q := by
  induction q with
  | nil => simp
  | cons m' q ih =>
    rw [List.map_cons, interp_cons, ih, interp_cons, mul_add, single_mul_single,
      decodeWord_append, GInt.toC_mul]

/-- The decoding is multiplicative. -/
theorem interp_cmul (p q : CPoly) : interp nX nA (cmul p q) = interp nX nA p * interp nX nA q := by
  induction p with
  | nil => simp [cmul]
  | cons m p ih =>
    simp only [cmul, List.flatMap_cons] at ih ⊢
    rw [interp_append, interp_map_mul, ih, interp_cons, add_mul]

/-- The decoding commutes with the star. -/
theorem interp_cstar (p : CPoly) : interp nX nA (cstar p) = star (interp nX nA p) := by
  induction p with
  | nil => simp [cstar]
  | cons m p ih =>
    simp only [cstar, List.map_cons] at ih ⊢
    rw [interp_cons, ih, interp_cons, star_add, star_single, decodeWord_reverse, GInt.toC_conj,
      starRingEnd_apply]

/-- The decoding of a coded constant. -/
theorem interp_cconst (c : GInt) : interp nX nA (cconst c) = single 1 (GInt.toC c) := by
  simp [cconst]

/-- The decoding of a coded word with coefficient `1`. -/
theorem interp_cword (w : List Letter) :
    interp nX nA (cword w) = single (decodeWord nX nA w) 1 := by
  simp [cword]

/-- The decoding of the polynomial of an optional letter: `1` or a generator. -/
theorem interp_optPoly (g : Option Letter) :
    interp nX nA (optPoly g) = (g.map (decodeLetter nX nA)).elim 1 gen := by
  cases g with
  | none => simp [Coded.optPoly, interp_cconst, one_def]
  | some l => simp [Coded.optPoly, cletter, interp_cword, gen]

/-- The decoding of a concatenation of coded polynomials. -/
theorem interp_flatMap {β : Type*} (l : List β) (f : β → CPoly) :
    interp nX nA (l.flatMap f) = (l.map fun b => interp nX nA (f b)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.flatMap_cons, interp_append, ih, List.map_cons, List.sum_cons]

/-- The decoding of a list of monomials. -/
theorem interp_map {β : Type*} (l : List β) (f : β → List Letter × GInt) :
    interp nX nA (l.map f) =
      (l.map fun b => single (decodeWord nX nA (f b).1) (GInt.toC (f b).2)).sum := by
  rw [interp, List.map_map]
  rfl

/-- A sum over `List.range n` as a sum over `Fin n`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ i : Fin n, g i := by
  rw [← Finset.sum_range]
  rfl

/-! ## Relations and the game polynomial -/

/-- The first player's coded normalization decodes to `Σ_a e_xa - 1`. -/
theorem interp_aliceNorm (x : ℕ) :
    interp nX nA (aliceNorm nA x) =
      ∑ a, eG (Y := Fin (nX + 1)) (B := Fin (nA + 1)) (finOf nX x) a - 1 := by
  rw [aliceNorm, interp_append, interp_map, sum_map_range, interp_cconst, Coded.toC_gneg,
    GInt.toC_ofNat, Nat.cast_one, single_neg, ← one_def, ← sub_eq_add_neg]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [decodeLetter, eG, gen]

/-- The second player's coded normalization decodes to `Σ_b f_yb - 1`. -/
theorem interp_bobNorm (y : ℕ) :
    interp nX nA (bobNorm nA y) =
      ∑ b, fG (X := Fin (nX + 1)) (A := Fin (nA + 1)) (finOf nX y) b - 1 := by
  rw [bobNorm, interp_append, interp_map, sum_map_range, interp_cconst, Coded.toC_gneg,
    GInt.toC_ofNat, Nat.cast_one, single_neg, ← one_def, ← sub_eq_add_neg]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [decodeLetter, fG, gen]

/-- The coded commutator decodes to `e_xa f_yb - f_yb e_xa`. -/
theorem interp_commPoly (t : ℕ × ℕ × ℕ × ℕ) :
    interp nX nA (commPoly t) =
      eG (finOf nX t.1) (finOf nA t.2.2.1) * fG (finOf nX t.2.1) (finOf nA t.2.2.2) -
        fG (finOf nX t.2.1) (finOf nA t.2.2.2) * eG (finOf nX t.1) (finOf nA t.2.2.1) := by
  simp [commPoly, eG, fG, gen, decodeWord, decodeLetter, Coded.toC_gneg, single_neg,
    sub_eq_add_neg]

/-- Every relation index decodes to a relation. -/
theorem interp_relPoly_mem (ρ : RelIdx) : interp nX nA (relPoly nA ρ) ∈ FinRels nX nA := by
  rcases ρ with x | y | t
  · exact Or.inl (Or.inl ⟨finOf nX x, (interp_aliceNorm x).symm⟩)
  · exact Or.inl (Or.inr ⟨finOf nX y, (interp_bobNorm y).symm⟩)
  · exact Or.inr ⟨(finOf nX t.1, finOf nX t.2.1, finOf nA t.2.2.1, finOf nA t.2.2.2),
      (interp_commPoly t).symm⟩

/-- Every relation is the decoding of a valid relation index. -/
theorem exists_relIdx {ρ : NCPoly (FinGen nX nA)} (hρ : ρ ∈ FinRels nX nA) :
    ∃ i : RelIdx, ValidRel nX nA i ∧ interp nX nA (relPoly nA i) = ρ := by
  rcases hρ with (⟨x, rfl⟩ | ⟨y, rfl⟩) | ⟨⟨x, y, a, b⟩, rfl⟩
  · refine ⟨Sum.inl x, Nat.lt_succ_iff.mp x.2, ?_⟩
    rw [relPoly, interp_aliceNorm, finOf_val]
  · refine ⟨Sum.inr (Sum.inl y), Nat.lt_succ_iff.mp y.2, ?_⟩
    rw [relPoly, interp_bobNorm, finOf_val]
  · refine ⟨Sum.inr (Sum.inr (x, y, a, b)), ⟨Nat.lt_succ_iff.mp x.2, Nat.lt_succ_iff.mp y.2,
      Nat.lt_succ_iff.mp a.2, Nat.lt_succ_iff.mp b.2⟩, ?_⟩
    rw [relPoly, interp_commPoly]
    simp only [finOf_val]

/-- The coded game polynomial decodes to `W_d` times the game polynomial. -/
theorem interp_Wint (d : GameData) :
    interp d.nX d.nA (Wint d) = ((W d : ℕ) : ℂ) • gamePoly d.game := by
  have hW : ((W d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp d.one_le_W)
  rw [Wint, interp_flatMap, sum_map_range, gamePoly, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [interp_flatMap, sum_map_range, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [interp_flatMap, sum_map_range, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [interp_map, sum_map_range, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [HaltingGameValue.GameData.game_μ_eq, HaltingGameValue.GameData.game_D_eq, smul_smul]
  have hword : decodeWord d.nX d.nA [Sum.inl ((x : ℕ), (a : ℕ)), Sum.inr ((y : ℕ), (b : ℕ))] =
      FreeMonoid.of (Sum.inl (x, a)) * FreeMonoid.of (Sum.inr (y, b)) := by
    simp [decodeWord, decodeLetter]
  rw [hword, eG, fG, gen, gen, single_mul_single, smul_single, mul_one, GInt.toC_ofNat]
  congr 1
  split_ifs
  · push_cast
    field_simp
  · simp

/-! ## Coefficients and dominance -/

/-- The merged coefficient of a valid word in a valid coded polynomial is the coefficient of its
decoding. -/
theorem coeff_interp {l : CPoly} (hl : ValidCPoly nX nA l) {w : List Letter}
    (hw : ValidWord nX nA w) :
    (interp nX nA l).coeff (decodeWord nX nA w) = GInt.toC (coeffRaw l w) := by
  classical
  induction l with
  | nil => simp [Coded.coeffRaw_nil]
  | cons m l ih =>
    rw [interp_cons, coeff_add, Finsupp.add_apply,
      ih fun m' hm' => hl m' (List.mem_cons_of_mem _ hm'), Coded.coeffRaw_cons, coeff_single_apply]
    by_cases h : m.1 = w
    · rw [if_pos (congrArg _ h), if_pos h, GInt.toC_add]
    · have h' : decodeWord nX nA m.1 ≠ decodeWord nX nA w := fun h' =>
        h (decodeWord_injOn (hl m List.mem_cons_self) hw h')
      rw [if_neg h', if_neg h, zero_add]

/-- The support of the decoding lies in the decoded words. -/
theorem support_interp_subset [DecidableEq (FreeMonoid (FinGen nX nA))] (l : CPoly) :
    (interp nX nA l).coeff.support ⊆ (l.map Prod.fst).toFinset.image (decodeWord nX nA) := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rw [interp_cons, coeff_add, coeff_single]
    refine Finsupp.support_add.trans (Finset.union_subset ?_ (ih.trans ?_))
    · refine Finsupp.support_single_subset.trans ?_
      simp
    · apply Finset.image_subset_image
      simp [List.toFinset_cons, Finset.subset_insert]

/-- **The coded dominance test is dominance of the decoding**, for valid coded polynomials. -/
theorem isDominant_iff_dominant_interp {l : CPoly} (hl : ValidCPoly nX nA l) :
    Coded.IsDominant l ↔ Dominant (interp nX nA l) := by
  classical
  set S := (l.map Prod.fst).toFinset with hSdef
  have hS : ∀ m ∈ l, m.1 ∈ S := fun m hm => List.mem_toFinset.mpr (List.mem_map_of_mem hm)
  have hvS : ∀ w ∈ S, ValidWord nX nA w := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
    exact hl m hm
  have himg : (S.image (decodeWord nX nA)).erase 1 = (S.erase []).image (decodeWord nX nA) := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hu, w, hw, rfl⟩
      exact ⟨w, ⟨fun h => hu (decodeWord_eq_one_iff.mpr h), hw⟩, rfl⟩
    · rintro ⟨w, ⟨hne, hw⟩, rfl⟩
      exact ⟨fun h => hne (decodeWord_eq_one_iff.mp h), w, hw, rfl⟩
  have hinj : Set.InjOn (decodeWord nX nA) (S.erase [] : Set (List Letter)) :=
    fun w hw w' hw' h => decodeWord_injOn (hvS w (Finset.mem_of_mem_erase hw))
      (hvS w' (Finset.mem_of_mem_erase hw')) h
  rw [Coded.isDominant_iff_sum l hS, dominant_iff_of_subset _ (support_interp_subset l), himg,
    Finset.sum_image hinj, ← decodeWord_nil, coeff_interp hl (fun _ h => absurd h List.not_mem_nil)]
  refine Iff.of_eq (congrArg₂ _ (Finset.sum_congr rfl fun w hw => ?_) rfl)
  rw [coeff_interp hl (hvS w (Finset.mem_of_mem_erase hw))]

/-! ## Decoded certificates -/

/-- The decoded hermitian squares of a certificate. -/
def decodeSos (nX nA : ℕ) (sos : List (Option Letter × CPoly)) :
    List (Option (FinGen nX nA) × NCPoly (FinGen nX nA)) :=
  sos.map fun t => (t.1.map (decodeLetter nX nA), interp nX nA t.2)

/-- The decoded ideal monomials of a certificate. -/
def decodeIdeal (nX nA : ℕ) (ideal : List (GInt × List Letter × RelIdx × List Letter)) :
    List (ℂ × FreeMonoid (FinGen nX nA) × {ρ // ρ ∈ FinRels nX nA} × FreeMonoid (FinGen nX nA)) :=
  ideal.map fun t => (GInt.toC t.1, decodeWord nX nA t.2.1,
    ⟨interp nX nA (relPoly nA t.2.2.1), interp_relPoly_mem t.2.2.1⟩, decodeWord nX nA t.2.2.2)

/-- The decoding of the coded hermitian squares of a certificate. -/
theorem interp_sosSum (sos : List (Option Letter × CPoly)) :
    interp nX nA (sosSum sos) = sosPoly (decodeSos nX nA sos) := by
  induction sos with
  | nil => simp [sosSum, decodeSos]
  | cons t sos ih =>
    simp only [sosSum, decodeSos, List.flatMap_cons, List.map_cons] at ih ⊢
    rw [interp_append, ih, sosPoly_cons, interp_cmul, interp_cmul, interp_cstar, interp_optPoly]

/-- The decoding of the coded ideal monomials of a certificate. -/
theorem interp_idealSum (ideal : List (GInt × List Letter × RelIdx × List Letter)) :
    interp nX nA (idealSum nA ideal) = idealPoly (decodeIdeal nX nA ideal) := by
  induction ideal with
  | nil => simp [idealSum, decodeIdeal]
  | cons t ideal ih =>
    simp only [idealSum, decodeIdeal, List.flatMap_cons, List.map_cons] at ih ⊢
    rw [interp_append, ih, idealPoly_cons, interp_cscale, interp_cmul, interp_cmul, interp_cword,
      interp_cword]

/-- The decoded residual of a certificate. -/
theorem interp_certR (d : GameData) (p q : ℕ) (cert : Cert) :
    interp d.nX d.nA (certR d p q cert) =
      ((cert.1 * cert.1 * p * W d : ℕ) : ℂ) • (1 : NCPoly (FinGen d.nX d.nA)) -
        ((cert.1 * cert.1 * q : ℕ) : ℂ) • (((W d : ℕ) : ℂ) • gamePoly d.game) -
        sosPoly (decodeSos d.nX d.nA cert.2.1) - idealPoly (decodeIdeal d.nX d.nA cert.2.2) := by
  rw [certR, interp_append, interp_append, interp_append, interp_cneg, interp_cneg, interp_cneg,
    interp_cscale, interp_cscale, interp_cconst, interp_Wint, interp_sosSum, interp_idealSum,
    GInt.toC_ofNat, GInt.toC_ofNat, GInt.toC_ofNat, Nat.cast_one, ← one_def]
  abel

/-- The decoded residual of a certificate is the residual of `Certificate`, at `κ = q·W_d` and
`r = p / q`. -/
theorem interp_certR_eq (d : GameData) (p : ℕ) {q : ℕ} (hq : q ≠ 0) (cert : Cert) :
    interp d.nX d.nA (certR d p q cert) =
      ((cert.1 : ℂ) ^ 2) • ((((q : ℝ) * W d) * ((p : ℝ) / q)) •
          (1 : NCPoly (FinGen d.nX d.nA)) - ((q : ℝ) * W d) • gamePoly d.game) -
        sosPoly (decodeSos d.nX d.nA cert.2.1) - idealPoly (decodeIdeal d.nX d.nA cert.2.2) := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hreal : ∀ (c : ℝ) (x : NCPoly (FinGen d.nX d.nA)), c • x = (c : ℂ) • x := fun _ _ => rfl
  rw [interp_certR, hreal, hreal, smul_sub, smul_smul, smul_smul, smul_smul]
  congr 4
  · push_cast
    field_simp
  · push_cast
    ring

/-- The decoded hermitian residual of a certificate. -/
theorem interp_certRh (d : GameData) (p q : ℕ) (cert : Cert) :
    interp d.nX d.nA (certRh d p q cert) =
      interp d.nX d.nA (certR d p q cert) + star (interp d.nX d.nA (certR d p q cert)) := by
  rw [certRh, interp_append, interp_cstar]

/-! ## Soundness -/

/-- The normalizing weight of a description is positive. -/
theorem cast_W_pos (d : GameData) : (0 : ℝ) < W d := by
  have := d.one_le_W
  positivity

/-- **Soundness of the coded check**: an accepted certificate for `(d, p, q)` bounds the
commuting-operator value of `d.game` strictly below `p / q`. -/
theorem checkUpper_sound {d : GameData} {p q : ℕ} {cert : Cert} (h : CheckUpper (d, p, q) cert) :
    commutingOperatorValue d.game < (p : ℝ) / q := by
  obtain ⟨hq, hN, hvalid, hdom⟩ := h
  have hκ : (0 : ℝ) < q * W d := mul_pos (Nat.cast_pos.mpr hq) (cast_W_pos d)
  rw [isDominant_iff_dominant_interp (Coded.validCPoly_certRh hvalid p q), interp_certRh,
    interp_certR_eq d p hq.ne' cert] at hdom
  exact commutingOperatorValue_lt_of_certificate d.game hκ hN _ _ hdom

/-! ## Encoding certificates -/

/-- The code of a complex number, read off the floors of its parts; exact on Gaussian
integers. -/
def encodeC (z : ℂ) : GInt := GInt.ofInt ⌊z.re⌋ ⌊z.im⌋

/-- The code of a Gaussian integer is exact. -/
theorem toC_encodeC {z : ℂ} (h : ∃ m n : ℤ, z = m + n * Complex.I) : GInt.toC (encodeC z) = z := by
  obtain ⟨m, n, rfl⟩ := h
  simp [encodeC]

/-- The code of a polynomial: its monomials, in the order of `Finset.toList`. -/
def encodePoly (s : NCPoly (FinGen nX nA)) : CPoly :=
  s.coeff.support.toList.map fun w => (encodeWord w, encodeC (s.coeff w))

/-- The code of a polynomial with Gaussian-integer coefficients is exact. -/
theorem interp_encodePoly {s : NCPoly (FinGen nX nA)}
    (hs : ∀ w, ∃ m n : ℤ, s.coeff w = m + n * Complex.I) : interp nX nA (encodePoly s) = s := by
  rw [encodePoly, interp_map, Finset.sum_map_toList]
  conv_rhs => rw [← sum_support_single s]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [decodeWord_encodeWord, toC_encodeC (hs w)]

/-- The code of a polynomial is valid. -/
theorem validCPoly_encodePoly (s : NCPoly (FinGen nX nA)) : ValidCPoly nX nA (encodePoly s) := by
  intro m hm
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hm
  exact validWord_encodeWord w

/-- The code of a relation: a valid relation index decoding to it. -/
def relIdxOf (ρ : {ρ // ρ ∈ FinRels nX nA}) : RelIdx := Classical.choose (exists_relIdx ρ.2)

/-- The code of a relation is valid. -/
theorem validRel_relIdxOf (ρ : {ρ // ρ ∈ FinRels nX nA}) : ValidRel nX nA (relIdxOf ρ) :=
  (Classical.choose_spec (exists_relIdx ρ.2)).1

/-- The code of a relation decodes to it. -/
theorem interp_relPoly_relIdxOf (ρ : {ρ // ρ ∈ FinRels nX nA}) :
    interp nX nA (relPoly nA (relIdxOf ρ)) = ρ.1 :=
  (Classical.choose_spec (exists_relIdx ρ.2)).2

/-- The code of a list of hermitian squares. -/
def encodeSos (σ : List (Option (FinGen nX nA) × NCPoly (FinGen nX nA))) :
    List (Option Letter × CPoly) :=
  σ.map fun t => (t.1.map encodeLetter, encodePoly t.2)

/-- The code of a list of ideal monomials. -/
def encodeIdeal
    (ι : List (ℂ × FreeMonoid (FinGen nX nA) × {ρ // ρ ∈ FinRels nX nA} ×
      FreeMonoid (FinGen nX nA))) : List (GInt × List Letter × RelIdx × List Letter) :=
  ι.map fun t => (encodeC t.1, encodeWord t.2.1, relIdxOf t.2.2.1, encodeWord t.2.2.2)

/-- The code of hermitian squares with Gaussian-integer coefficients is exact. -/
theorem decodeSos_encodeSos {σ : List (Option (FinGen nX nA) × NCPoly (FinGen nX nA))}
    (hσ : ∀ t ∈ σ, ∀ w, ∃ m n : ℤ, t.2.coeff w = m + n * Complex.I) :
    decodeSos nX nA (encodeSos σ) = σ := by
  rw [decodeSos, encodeSos, List.map_map]
  conv_rhs => rw [← List.map_id σ]
  refine List.map_congr_left fun t ht => ?_
  simp [Option.map_map, Function.comp_def, interp_encodePoly (hσ t ht)]

/-- The code of ideal monomials with Gaussian-integer coefficients is exact. -/
theorem decodeIdeal_encodeIdeal
    {ι : List (ℂ × FreeMonoid (FinGen nX nA) × {ρ // ρ ∈ FinRels nX nA} ×
      FreeMonoid (FinGen nX nA))}
    (hι : ∀ t ∈ ι, ∃ m n : ℤ, t.1 = m + n * Complex.I) :
    decodeIdeal nX nA (encodeIdeal ι) = ι := by
  rw [decodeIdeal, encodeIdeal, List.map_map]
  conv_rhs => rw [← List.map_id ι]
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp_apply, decodeWord_encodeWord, toC_encodeC (hι t ht), id]
  congr
  exact interp_relPoly_relIdxOf t.2.2.1

/-- The code of a certificate is valid. -/
theorem validCert_encode (N : ℕ) (σ : List (Option (FinGen nX nA) × NCPoly (FinGen nX nA)))
    (ι : List (ℂ × FreeMonoid (FinGen nX nA) × {ρ // ρ ∈ FinRels nX nA} ×
      FreeMonoid (FinGen nX nA))) :
    ValidCert nX nA (N, encodeSos σ, encodeIdeal ι) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨u, -, rfl⟩ := List.mem_map.mp ht
    refine ⟨?_, validCPoly_encodePoly _⟩
    cases u.1 with
    | none => trivial
    | some g => exact validLetter_encodeLetter g
  · obtain ⟨u, -, rfl⟩ := List.mem_map.mp ht
    exact ⟨validWord_encodeWord _, validRel_relIdxOf _, validWord_encodeWord _⟩

/-! ## Completeness -/

/-- **Completeness of the coded check**: if the commuting-operator value of `d.game` is strictly
below `p / q`, some certificate for `(d, p, q)` is accepted. -/
theorem checkUpper_complete {d : GameData} {p q : ℕ}
    (h : commutingOperatorValue d.game < (p : ℝ) / q) : ∃ cert, CheckUpper (d, p, q) cert := by
  have hq : q ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, div_zero] at h
    exact absurd h (not_lt.mpr (commutingOperatorValue_nonneg d.game))
  have hκ : (0 : ℝ) < q * W d := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)) (cast_W_pos d)
  obtain ⟨N, hN, σ, ι, hσ, hι, hdom⟩ := exists_certificate_of_lt d.game hκ h
  have hv := validCert_encode (nX := d.nX) (nA := d.nA) N σ ι
  refine ⟨(N, encodeSos σ, encodeIdeal ι), Nat.pos_of_ne_zero hq, hN, hv, ?_⟩
  rw [isDominant_iff_dominant_interp (Coded.validCPoly_certRh hv p q), interp_certRh,
    interp_certR_eq d p hq, decodeSos_encodeSos hσ, decodeIdeal_encodeIdeal hι]
  exact hdom

/-- **The coded check characterizes the thresholds above the commuting-operator value.** -/
theorem checkUpper_iff (x : GameData × ℕ × ℕ) :
    (∃ cert, CheckUpper x cert) ↔ commutingOperatorValue x.1.game < (x.2.1 : ℝ) / x.2.2 :=
  ⟨fun ⟨_, h⟩ => checkUpper_sound h, checkUpper_complete⟩

end Tsirelson

/-- **The commuting-operator value is recursively enumerable from above** (blueprint
`lem:valco-upper-re`): the triples `(d, p, q)` with `valco(G_d) < p / q` form an r.e. set. The
semidecider searches for a certificate accepted by the primitive recursive check
`Tsirelson.Coded.CheckUpper`. -/
theorem commutingUpperRE : CommutingUpperRE :=
  (ValueApprox.REPred.of_primrecRel_exists Tsirelson.Coded.primrecRel_checkUpper).of_eq
    Tsirelson.checkUpper_iff

/-- **Tsirelson's problem, negative answer, given the halting reduction** (blueprint
`cor:tsirelson`): `C_qa ⊊ C_qc` in some finite scenario with equal question alphabets
`Fin (nX + 1)` and equal answer alphabets `Fin (nA + 1)` for both players. -/
theorem tsirelson_of_haltingReduction (hred : HaltingReductionQuantum) :
    ∃ nX nA : ℕ, Cqa (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) ⊂
      Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) :=
  tsirelson_of_upperRE hred commutingUpperRE

end MIPRE
