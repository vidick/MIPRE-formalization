/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularTensor
import MIPRE.Foundations.OracularComplete
import MIPRE.Foundations.CL.DetypingGame
import MIPRE.Foundations.GapCompression
import MIPRE.Foundations.Halting.Descriptions

/-!
# The typed oracularized game

Piece O2 of `planning/oracularization.md` (issue #189): the game of the paper's typed
oracularized verifier (`sec:orac-def`) at one index, in the vocabulary the detyping compiler
consumes (`MIPRE.CL.Detyping.typedGame`), and its two value transfers to the input verifier.

* **The typed sampler's distribution.** Types are the three roles, on the complete type graph with
  loops (`roleGraph`); the CL functions are the identity for the oracle and the input sampler's
  two functions for the isolated players (`roleFamily`, with `CL.CLFun.ident` the identity as an
  `(ℓ + 1)`-level function). The typed game samples an ordered pair of roles and one common seed,
  and its distribution is exactly that of `SeededGame.oracular` (`typedGame_mu`).
* **Soundness.** For any typed predicate whose acceptance implies the oracularized predicate
  after a question-dependent reading of the answers (`quantumValue_typedGame_le`), `val*` of the
  typed game is at most `val*` of the oracularization, so by `lem:oracular-soundness-tensor`
  it bounds the input verifier's value (`valStar_ge_of_typed`).
* **Completeness.** For any typed predicate that accepts the honest encodings of accepted answer
  pairs, a value-`1` PCC strategy of `𝒱_n` gives one of the *doubled* typed game
  (`exists_typed_perfectPCC`) --- the form `CL.Detyping.DeciderProgram.verifier_hasPerfectPCC`
  takes. It is `oracleStrategy` (identical operators for the two players), doubled, and pushed
  forward along the encoding (`SyncStrategy.pushTo`).
* **The bit-string predicate.** Answers of the typed verifier are bit strings. An oracle answers
  the serialization of a pair (`pairEnc`, read back by `pairDec`), an isolated player a single
  string; each is parsed against the cut `B` according to the role (`parseAns`), and a failed
  parse is rejected (`oraclePred`). This is the predicate of `fig:oracle-decider`, with the
  bounded parse that repairs 3 and 4 of `rem:oracularization-repairs` ask for, and it satisfies
  both hypotheses (`valStar_ge_of_oraclePred`, `exists_oraclePred_perfectPCC`). The typed decider
  program (piece O4) is to be shown to implement it.
-/

namespace MIPRE

open Finset

/-! ## The identity as a CL function -/

namespace CL.CLFun

variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The zero function with `ℓ` levels, every level on the empty register. -/
def trivialOn : (ℓ : ℕ) → CLFun F ι ℓ
  | 0 => zero
  | ℓ + 1 => cons ∅ 0 fun _ => trivialOn ℓ

@[simp] theorem eval_trivialOn (ℓ : ℕ) (x : ι → F) : (trivialOn ℓ : CLFun F ι ℓ).eval x = 0 := by
  induction ℓ generalizing x with
  | zero => rfl
  | succ ℓ ih => simp [trivialOn, ih]

theorem exactlyOn_trivialOn (ℓ : ℕ) : (trivialOn ℓ : CLFun F ι ℓ).ExactlyOn ∅ := by
  induction ℓ with
  | zero => exact (exactlyOn_zero _).mpr rfl
  | succ ℓ ih => exact ⟨Finset.Subset.refl _, fun _ => by simpa using ih⟩

/-- **The identity**, as an `(ℓ + 1)`-level CL function: the whole space at the first level,
trivial levels after it. The oracularized sampler gives it to the oracle, who receives the seed
itself. -/
def ident (ℓ : ℕ) : CLFun F ι (ℓ + 1) := cons univ (RegLinear.id univ) fun _ => trivialOn ℓ

@[simp] theorem eval_ident (ℓ : ℕ) (x : ι → F) : (ident ℓ : CLFun F ι (ℓ + 1)).eval x = x := by
  funext i
  simp [ident]

theorem exactlyOn_ident (ℓ : ℕ) : (ident ℓ : CLFun F ι (ℓ + 1)).ExactlyOn univ :=
  ⟨Finset.Subset.refl _, fun _ => by simpa using exactlyOn_trivialOn ℓ⟩

end CL.CLFun

/-! ## The typed sampler's CL functions and type graph -/

section Roles

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- **The oracularized sampler's CL functions**, one per role and the same for both players: the
identity for the oracle, and the input sampler's function of the corresponding original player
for an isolated player. -/
def roleFamily (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1)) : Role → CL.CLFun CL.𝔽₂ ι (ℓ + 1)
  | .oracle => CL.CLFun.ident ℓ
  | .alice => L .alice
  | .bob => L .bob

theorem exactlyOn_roleFamily {L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1)}
    (hL : ∀ w, (L w).ExactlyOn univ) (r : Role) : (roleFamily L r).ExactlyOn univ := by
  cases r
  · exact CL.CLFun.exactlyOn_ident ℓ
  · exact hL _
  · exact hL _

/-- The complete type graph on the three roles, loops included: every ordered pair of roles is
sampled. -/
def roleGraph : Role → Role → Prop := fun _ _ => True

instance : DecidableRel roleGraph := fun _ _ => isTrue trivial

theorem mem_roleGraph_edges (p : Role × Role) : p ∈ CL.Graph.edges roleGraph :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩

theorem roleGraph_nonempty : (CL.Graph.edges roleGraph).Nonempty :=
  ⟨(Role.oracle, Role.oracle), mem_roleGraph_edges _⟩

theorem roleGraph_symm (u v : Role) (_ : roleGraph u v) : roleGraph v u := trivial

end Roles

/-! ## The seeded game of a CL pair, and the typed game -/

namespace SeededGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} {A : Type*}

/-- The seeded game presented by a pair of CL functions and a decision predicate: the game of a
normal form verifier at one index, with the seed space its question space. -/
def ofCL (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1))
    (D : (ι → CL.𝔽₂) → (ι → CL.𝔽₂) → A → A → Bool) : SeededGame (ι → CL.𝔽₂) A :=
  ⟨(L .alice).eval, (L .bob).eval, D⟩

/-- The role family's question is the oracularized game's. -/
theorem roleFamily_question (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1))
    (D : (ι → CL.𝔽₂) → (ι → CL.𝔽₂) → A → A → Bool) (r : Role) (z : ι → CL.𝔽₂) :
    (r, (roleFamily L r).eval z) = (ofCL L D).oquestion r z := by
  cases r
  · simp [roleFamily]
  · rfl
  · rfl

/-- The typed seeds of the complete graph are the ordered pairs of roles with a seed. -/
def typedSeedEquiv : CL.Detyping.TypedSeed roleGraph ι ≃ Role × Role × (ι → ZMod 2) :=
  (Equiv.prodCongr (Equiv.subtypeUnivEquiv mem_roleGraph_edges) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem typedSeedEquiv_apply (s : CL.Detyping.TypedSeed roleGraph ι) :
    typedSeedEquiv s = (s.1.val.1, s.1.val.2, s.2) := rfl

/-- **The typed game has the oracularization's distribution**: a uniform ordered pair of roles
and one common uniform seed, the oracle receiving the seed and an isolated player its original
question. -/
theorem typedGame_mu (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1))
    (D : (ι → CL.𝔽₂) → (ι → CL.𝔽₂) → A → A → Bool) {A' : Type*} [Fintype A']
    (D' : CL.Detyping.Question Role ι → CL.Detyping.Question Role ι → A' → A' → Bool)
    (p q : Role × (ι → CL.𝔽₂)) :
    (CL.Detyping.typedGame roleGraph roleGraph_nonempty (fun _ => roleFamily L) D').μ p q
      = (ofCL L D).oDist p q := by
  change SampledGame.dist
    (CL.Detyping.typedQuestion (E := roleGraph) (fun _ => roleFamily L) false)
    (CL.Detyping.typedQuestion (E := roleGraph) (fun _ => roleFamily L) true) p q = _
  rw [SampledGame.dist, oDist, Finset.mul_sum, Fintype.card_congr typedSeedEquiv]
  refine Fintype.sum_equiv typedSeedEquiv _ _ fun s => ?_
  obtain ⟨⟨⟨u, v⟩, huv⟩, z⟩ := s
  simp only [typedSeedEquiv_apply, CL.Detyping.typedQuestion, Bool.false_eq_true, if_false, if_true]
  rw [roleFamily_question L D u z, roleFamily_question L D v z]
  congr 1

variable [Fintype A] [DecidableEq A]

/-- **Soundness through a reading of the answers.** A typed predicate whose acceptance implies the
oracularized predicate, after the answers are read by a map that may depend on the question, has
no larger quantum value than the oracularization: a strategy is played through the reading, on
the same state, and the two games have the same distribution. -/
theorem quantumValue_typedGame_le (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1))
    (D : (ι → CL.𝔽₂) → (ι → CL.𝔽₂) → A → A → Bool) {A' : Type*} [Fintype A']
    (D' : CL.Detyping.Question Role ι → CL.Detyping.Question Role ι → A' → A' → Bool)
    (rA : CL.Detyping.Question Role ι → A' → OAns A)
    (hD : ∀ p q a b, D' p q a b = true → (ofCL L D).oaccepts p q (rA p a) (rA q b) = true) :
    quantumValue (CL.Detyping.typedGame roleGraph roleGraph_nonempty (fun _ => roleFamily L) D')
      ≤ quantumValue (ofCL L D).oracular.toGame := by
  refine Real.iSup_le (fun R => ?_) (quantumValue_nonneg _)
  refine le_trans ?_ (le_ciSup (TensorProductStrategy.bddAbove_range_value _)
    (R.adapt (ofCL L D).oracular.toGame id id rA rA))
  rw [TensorProductStrategy.value_eq_sum_succAt, TensorProductStrategy.value_eq_sum_succAt]
  refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
  rw [typedGame_mu L D D' p q]
  exact mul_le_mul_of_nonneg_left
    (R.succAt_le_succAt_adapt _ id id rA rA p q (hD p q)) ((ofCL L D).oDist_nonneg p q)

end SeededGame

/-! ## Pushing a synchronous strategy into another game -/

namespace SyncStrategy

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

/-- Play a synchronous strategy on another game with the same questions, its outcomes pushed
forward along `f`: the operator for `a'` is the sum over the fibre above it. -/
noncomputable def pushTo (S : SyncStrategy G) {A' : Type*} [Fintype A'] [DecidableEq A']
    (G' : SynchronousGame X A') (f : A → A') : SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.push f⟩

/-- **Pushing forward loses no value** when every accepted tuple stays accepted and the
distribution is the same. -/
theorem value_le_pushTo (S : SyncStrategy G) {A' : Type*} [Fintype A'] [DecidableEq A']
    (G' : SynchronousGame X A') (f : A → A') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y (f a) (f b) = true) :
    S.value ≤ (S.pushTo G' f).value := by
  rw [value_eq_ntr, value_eq_ntr]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  rw [hμ x y]
  have hreg : ∑ a', ∑ b', G.μ x y * (if G'.D x y a' b' then 1 else 0) *
        ntr ((S.pushTo G' f).P.M x a' * (S.pushTo G' f).P.M y b')
      = ∑ a, ∑ b, G.μ x y * (if G'.D x y (f a) (f b) then 1 else 0) *
          ntr (S.P.M x a * S.P.M y b) := by
    rw [← sum_sum_fiberwise₂ f f (fun a b => G.μ x y * (if G'.D x y (f a) (f b) then 1 else 0) *
      ntr (S.P.M x a * S.P.M y b))]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
    change G.μ x y * (if G'.D x y a' b' then 1 else 0) *
        ntr ((∑ a ∈ univ.filter fun a => f a = a', S.P.M x a) *
          (∑ b ∈ univ.filter fun b => f b = b', S.P.M y b)) = _
    rw [Finset.sum_mul_sum, ntr_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ntr_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
  rw [hreg]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
    (S.ntr_mul_nonneg x y a b)
  by_cases h : G.D x y a b = true
  · rw [if_pos h, if_pos (hD x y a b h)]
  · rw [if_neg h]
    split_ifs <;> norm_num

/-- **Pushing forward keeps the PCC property**: sums over fibres of pairwise commuting operators
commute. -/
theorem isPCC_pushTo {S : SyncStrategy G} (hS : S.IsPCC) {A' : Type*} [Fintype A']
    [DecidableEq A'] (G' : SynchronousGame X A') (f : A → A') (hμ : ∀ x y, G'.μ x y = G.μ x y) :
    (S.pushTo G' f).IsPCC := by
  intro x y hxy a' b'
  rw [hμ] at hxy
  change (∑ a ∈ univ.filter fun a => f a = a', S.P.M x a) *
      (∑ b ∈ univ.filter fun b => f b = b', S.P.M y b)
    = (∑ b ∈ univ.filter fun b => f b = b', S.P.M y b) *
      (∑ a ∈ univ.filter fun a => f a = a', S.P.M x a)
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => hS x y hxy a b

end SyncStrategy

/-! ## The two transfers, at a normal form verifier -/

namespace Verifier

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

instance (T : ℕ) : Inhabited (Answers T) := ⟨⟨[], Nat.zero_le T⟩⟩

/-- `𝒱_n` with answers of length at most `B`, as a seeded game: the seed space is the question
space, and the seed's two images are the questions. -/
noncomputable abbrev seeded (n B : ℕ) : SeededGame (V.Questions n) (Answers B) :=
  SeededGame.ofCL (V.sampler.cl n) (V.game n B).D

theorem seeded_toGame (n B : ℕ) : (V.seeded n B).toGame = V.game n B := rfl

/-- **Soundness of the typed oracularized game.** For a typed predicate whose acceptance implies
the oracularized predicate after a reading of the answers, `val*` of the typed game above
`1 - ε` puts `val* (𝒱_n)` at least `1 - 24√ε`. -/
theorem valStar_ge_of_typed (n B : ℕ) {A' : Type*} [Fintype A']
    (D' : CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
      CL.Detyping.Question Role (Fin (V.sampler.dim n)) → A' → A' → Bool)
    (rA : CL.Detyping.Question Role (Fin (V.sampler.dim n)) → A' → OAns (Answers B))
    (hD : ∀ p q a b, D' p q a b = true → (V.seeded n B).oaccepts p q (rA p a) (rA q b) = true)
    {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue (CL.Detyping.typedGame roleGraph roleGraph_nonempty
      (fun _ => roleFamily (V.sampler.cl n)) D')) :
    1 - 24 * √ε ≤ V.valStar n B := by
  have h1 := (V.seeded n B).quantumValue_ge_of_oracular hε
    (lt_of_lt_of_le h (SeededGame.quantumValue_typedGame_le _ _ D' rA hD))
  rwa [seeded_toGame] at h1

/-- **Completeness of the typed oracularized game.** For a typed predicate that accepts the
encodings of every answer pair the oracularized predicate accepts, a value-`1` PCC strategy of
`𝒱_n` gives one of the doubled typed game: `oracleStrategy`, with identical measurement
operators for the two players, doubled and pushed forward along the encoding. -/
theorem exists_typed_perfectPCC (n B : ℕ) (hV : V.HasPerfectPCC n B) {A' : Type*} [Fintype A']
    [DecidableEq A']
    (D' : CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
      CL.Detyping.Question Role (Fin (V.sampler.dim n)) → A' → A' → Bool)
    (f : OAns (Answers B) → A')
    (hf : ∀ p q u v, (V.seeded n B).oaccepts p q u v = true → D' p q (f u) (f v) = true) :
    ∃ R : SyncStrategy (CL.Detyping.typedGame roleGraph roleGraph_nonempty
        (fun _ => roleFamily (V.sampler.cl n)) D').doubled, R.IsPCC ∧ R.value = 1 := by
  obtain ⟨T, hT, hval⟩ := hV
  have hN1 := (V.seeded n B).oracleStrategy_value_eq_one T hT hval
  have hNp := (V.seeded n B).isPCC_oracleStrategy T hT
  have hμ : ∀ p q, (CL.Detyping.typedGame roleGraph roleGraph_nonempty
      (fun _ => roleFamily (V.sampler.cl n)) D').doubled.μ p q
        = (V.seeded n B).oracular.toGame.doubled.μ p q := by
    intro p q
    simp only [Game.doubled_μ]
    split_ifs
    · exact SeededGame.typedGame_mu _ _ D' p.2 q.2
    · rfl
  have hD : ∀ p q u v, (V.seeded n B).oracular.toGame.doubled.D p q u v = true →
      (CL.Detyping.typedGame roleGraph roleGraph_nonempty
        (fun _ => roleFamily (V.sampler.cl n)) D').doubled.D p q (f u) (f v) = true := by
    intro p q u v h
    simp only [Game.doubled_D] at h ⊢
    split_ifs at h ⊢ with hpq
    exact hf p.2 q.2 u v h
  refine ⟨((V.seeded n B).oracleStrategy T hT).double.pushTo _ f,
    SyncStrategy.isPCC_pushTo (SyncStrategy.isPCC_double hNp) _ f hμ,
    le_antisymm (SyncStrategy.value_le_one _) ?_⟩
  calc (1 : ℝ) = ((V.seeded n B).oracleStrategy T hT).double.value := by
        rw [SyncStrategy.value_double, hN1]
    _ ≤ _ := SyncStrategy.value_le_pushTo _ _ f hμ hD

end Verifier

/-! ## The bit-string predicate -/

section Bits

open Cost

/-- The serialization of an oracle's pair of answers: the postorder bits of the encoded pair
(`Cost.Data.toBitsPost`), the format the repeated decider already parses. -/
def pairEnc (a b : BitStr) : BitStr := (encode (a, b) : Data).toBitsPost

/-- Reading a pair back from its serialization. -/
def pairDec (s : BitStr) : Option (BitStr × BitStr) := decode (Data.parse s)

@[simp] theorem pairDec_pairEnc (a b : BitStr) : pairDec (pairEnc a b) = some (a, b) := by
  simp [pairDec, pairEnc, SizedEncoding.decode_encode]

theorem length_pairEnc_le (a b : BitStr) :
    (pairEnc a b).length ≤ 4 * (a.length + b.length) + 3 := by
  have ha := esize_bitStr_le a
  have hb := esize_bitStr_le b
  have h : (pairEnc a b).length = esize a + esize b + 1 := by
    rw [pairEnc, Data.length_toBitsPost]
    exact esize_prod a b
  omega

/-- **The bounded parse**, by the role of the player who answered: an oracle's answer must be the
serialization of a pair of answers of length at most `B`, an isolated player's a single answer of
length at most `B`. Anything else fails to parse, and the predicate rejects it: the paper's
grouping of failed parses into one rejected outcome (repair 3), and its truncation to the cut
(repair 4) made explicit. -/
def parseAns (B : ℕ) : Role → BitStr → Option (OAns (Verifier.Answers B))
  | .oracle, s =>
    match pairDec s with
    | some (a, b) =>
      if h : a.length ≤ B ∧ b.length ≤ B then some (.pair ⟨a, h.1⟩ ⟨b, h.2⟩) else none
    | none => none
  | .alice, s => if h : s.length ≤ B then some (.single ⟨s, h⟩) else none
  | .bob, s => if h : s.length ≤ B then some (.single ⟨s, h⟩) else none

/-- **The typed oracularized predicate** on bit-string answers (`fig:oracle-decider`): both
answers are parsed by role, a failed parse is rejected, and otherwise the decision is the
oracularized game's. -/
def oraclePred {V : Type*} {B : ℕ} (S : SeededGame V (Verifier.Answers B)) (p q : Role × V)
    (a b : BitStr) : Bool :=
  match parseAns B p.1 a, parseAns B q.1 b with
  | some u, some v => S.oaccepts p q u v
  | _, _ => false

/-- The honest encoding of an oracularized answer: an oracle's pair serialized, an isolated
player's answer as it is. -/
def encAns {B : ℕ} : OAns (Verifier.Answers B) → BitStr
  | .pair a b => pairEnc a.1 b.1
  | .single a => a.1

theorem length_encAns_le {B : ℕ} (u : OAns (Verifier.Answers B)) :
    (encAns u).length ≤ 8 * B + 3 := by
  rcases u with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨⟨a, ha⟩⟩
  · have h := length_pairEnc_le a b
    simp only [encAns]
    omega
  · simp only [encAns]
    omega

/-- An answer of the right shape parses back from its honest encoding. -/
theorem parseAns_encAns {B : ℕ} {r : Role} {u : OAns (Verifier.Answers B)}
    (h : SeededGame.shapeOk r u = true) : parseAns B r (encAns u) = some u := by
  rcases u with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨⟨a, ha⟩⟩ <;> cases r <;>
    simp_all [SeededGame.shapeOk, parseAns, encAns]

variable {V : Type*} {B : ℕ} {S : SeededGame V (Verifier.Answers B)}

/-- **Acceptance of the bit-string predicate is acceptance of the oracularized one**, after the
answers are read by the bounded parse. -/
theorem oaccepts_of_oraclePred {p q : Role × V} {a b : BitStr} (h : oraclePred S p q a b = true) :
    S.oaccepts p q ((parseAns B p.1 a).getD default) ((parseAns B q.1 b).getD default) = true := by
  unfold oraclePred at h
  split at h
  · rename_i u v hu hv
    simp [hu, hv, h]
  · exact absurd h Bool.false_ne_true

/-- **The bit-string predicate accepts the honest encodings** of every answer pair the
oracularized predicate accepts. -/
theorem oraclePred_encAns {p q : Role × V} {u v : OAns (Verifier.Answers B)}
    (h : S.oaccepts p q u v = true) : oraclePred S p q (encAns u) (encAns v) = true := by
  have hu : SeededGame.shapeOk p.1 u = true := by
    cases hs : SeededGame.shapeOk p.1 u
    · simp [SeededGame.oaccepts, hs] at h
    · rfl
  have hv : SeededGame.shapeOk q.1 v = true := by
    cases hs : SeededGame.shapeOk q.1 v
    · simp [SeededGame.oaccepts, hs] at h
    · rfl
  simp only [oraclePred, parseAns_encAns hu, parseAns_encAns hv, h]

end Bits

namespace Verifier

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

/-- The typed oracularized predicate of `𝒱_n`, with parse cut `B`, on answers of length at most
`T`. -/
noncomputable abbrev oracleTypedPred (n B T : ℕ) :
    CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
      CL.Detyping.Question Role (Fin (V.sampler.dim n)) → Answers T → Answers T → Bool :=
  fun p q a b => oraclePred (V.seeded n B) p q a.1 b.1

/-- **Soundness of the typed oracularized game of `𝒱_n`**: its quantum value above `1 - ε`, at
any output cut, puts `val* (𝒱_n)` at the parse cut `B` at least `1 - 24√ε`. -/
theorem valStar_ge_of_oraclePred (n B T : ℕ) {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue (CL.Detyping.typedGame roleGraph roleGraph_nonempty
      (fun _ => roleFamily (V.sampler.cl n)) (V.oracleTypedPred n B T))) :
    1 - 24 * √ε ≤ V.valStar n B :=
  V.valStar_ge_of_typed n B (V.oracleTypedPred n B T)
    (fun p a => (parseAns B p.1 a.1).getD default) (fun _ _ _ _ h => oaccepts_of_oraclePred h)
    hε h

/-- **Completeness of the typed oracularized game of `𝒱_n`**: a value-`1` PCC strategy of `𝒱_n`
at the parse cut `B` gives one of the doubled typed game, at any output cut `T ≥ 8B + 3`, which
holds every honest encoding. -/
theorem exists_oraclePred_perfectPCC (n B T : ℕ) (hT : 8 * B + 3 ≤ T)
    (hV : V.HasPerfectPCC n B) :
    ∃ R : SyncStrategy (CL.Detyping.typedGame roleGraph roleGraph_nonempty
        (fun _ => roleFamily (V.sampler.cl n)) (V.oracleTypedPred n B T)).doubled,
      R.IsPCC ∧ R.value = 1 :=
  V.exists_typed_perfectPCC n B hV (V.oracleTypedPred n B T)
    (fun u => ⟨encAns u, (length_encAns_le u).trans hT⟩) fun _ _ _ _ h => oraclePred_encAns h

end Verifier

end MIPRE
