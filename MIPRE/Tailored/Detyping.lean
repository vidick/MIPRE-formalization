/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Game
public import MIPRE.Foundations.CL.DetypingGame
public import MIPRE.Foundations.CL.DetypingCompleteSupport

@[expose] public section

/-!
# Detyping tailored games

The repository's verifiers are typed and then detyped (`MIPRE.CL.Detyping`): a question is a
graph view followed by a content register, and the detyped predicate calls the typed one on the
views of an edge, and accepts otherwise (`Detyping.accepts`). This file does the same for
tailored games. Typed tailored data (`TypedData`) fixes the numbers of readable and linear
variables of each type and the constraints at each pair of typed questions; the detyped tailored
game (`TypedData.detype`) has, at a question, the lengths of the type its graph view decodes to
(none when it decodes to nothing) and, at a pair of questions, the typed constraints on the views
of an edge and no constraint otherwise.

The two transport lemmas reduce the obligations of `MIPRE.Tailored.valStar_le_of_dec` and
`MIPRE.Tailored.hasPerfectZPC_of_sync`, for a detyped game presented by a detyped tailored game,
to the typed questions of the edges: `detype_accepts_of` (a pair the tailored game accepts on an
edge is a pair the typed constraints accept) and `detype_accepts` (conversely).
-/

namespace MIPRE.Tailored

open Cost MIPRE.CL MIPRE.CL.Detyping Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
variable (E : T → T → Prop) [DecidableRel E]

/-- The type a detyped question's graph view decodes to, for either player. -/
noncomputable def typeOf (x : Coord T ι → ZMod 2) : Option T :=
  (decodeView E (pull .inl x)).map Prod.snd

/-- The edge a pair of detyped questions sits on, Alice's view first: the typed pair. -/
noncomputable def edgeOf (x y : Coord T ι → ZMod 2) : Option (Question T ι × Question T ι) :=
  match select E false (pull .inl x), select E true (pull .inl y) with
  | some u, some v =>
    if E u v ∧ pull .inl x = view E false u ∧ pull .inl y = view E true v then
      some ((u, pull .inr x), (v, pull .inr y))
    else none
  | _, _ => none

omit [Fintype ι] [DecidableEq ι] in
/-- The detyped predicate of `MIPRE.CL.Detyping` calls the typed one on `edgeOf`, and accepts
off it. -/
theorem accepts_eq_edgeOf {A B : Type*} (D : Question T ι → Question T ι → A → B → Bool)
    (x y : Coord T ι → ZMod 2) (a : A) (b : B) :
    Detyping.accepts E D x y a b = match edgeOf E x y with
      | some (u, v) => D u v a b
      | none => true := by
  unfold Detyping.accepts edgeOf
  cases select E false (pull .inl x) <;> cases select E true (pull .inl y) <;> try rfl
  dsimp only
  split_ifs <;> rfl

/-- **Typed tailored data**: the numbers of readable and linear variables of each type and the
controlled linear constraints at each pair of typed questions. -/
structure TypedData (T ι : Type*) where
  lenR : T → ℕ
  lenL : T → ℕ
  cons : Question T ι → Question T ι → BitStr → BitStr → List BitStr

namespace TypedData

variable {E} (D : TypedData T ι)

/-- The typed acceptance: both answers have their type's lengths, and every constraint holds. -/
def Accepts (x y : Question T ι) (a b : BitStr) : Prop :=
  a.length = D.lenR x.1 + D.lenL x.1 ∧ b.length = D.lenR y.1 + D.lenL y.1 ∧
    ∀ c ∈ D.cons x y (a.take (D.lenR x.1)) (b.take (D.lenR y.1)), Satisfies c (a ++ b ++ [true])

variable (E)

/-- **The detyped tailored game**, with the question distribution `μ` of a detyped game. -/
noncomputable def detype (μ : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → ℝ)
    (hμ : ∀ x y, 0 ≤ μ x y) (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    TailoredGame (Coord T ι → ZMod 2) where
  μ := μ
  μ_nonneg := hμ
  μ_sum_one := hμ1
  lenR x := ((typeOf E x).map D.lenR).getD 0
  lenL x := ((typeOf E x).map D.lenL).getD 0
  cons x y aR bR := match edgeOf E x y with
    | some (u, v) => D.cons u v aR bR
    | none => []

variable {μ : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → ℝ} {hμ : ∀ x y, 0 ≤ μ x y}
  {hμ1 : ∑ x, ∑ y, μ x y = 1}

omit [Fintype ι] [DecidableEq ι] in
theorem typeOf_of_edgeOf {x y : Coord T ι → ZMod 2} {u v : Question T ι}
    (h : edgeOf E x y = some (u, v)) :
    typeOf E x = some u.1 ∧ typeOf E y = some v.1 ∧ u.2 = pull .inr x ∧ v.2 = pull .inr y := by
  unfold edgeOf at h
  split at h
  · split_ifs at h with hc
    · obtain ⟨-, hx, hy⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_, rfl, rfl⟩
      · simp [typeOf, hx, decodeView_view]
      · simp [typeOf, hy, decodeView_view]
  · exact absurd h (by simp)

theorem detype_len_of_edgeOf {x y : Coord T ι → ZMod 2} {u v : Question T ι}
    (h : edgeOf E x y = some (u, v)) :
    (D.detype E μ hμ hμ1).lenR x = D.lenR u.1 ∧ (D.detype E μ hμ hμ1).lenL x = D.lenL u.1 ∧
      (D.detype E μ hμ hμ1).lenR y = D.lenR v.1 ∧ (D.detype E μ hμ hμ1).lenL y = D.lenL v.1 := by
  obtain ⟨hx, hy, -, -⟩ := typeOf_of_edgeOf E h
  simp [detype, hx, hy]

/-- **On an edge, the detyped tailored game accepts exactly what the typed data accepts.** -/
theorem detype_accepts_iff_of_edgeOf {x y : Coord T ι → ZMod 2} {u v : Question T ι}
    (h : edgeOf E x y = some (u, v)) (a b : BitStr) :
    (D.detype E μ hμ hμ1).Accepts x y a b ↔ D.Accepts u v a b := by
  obtain ⟨h1, h2, h3, h4⟩ := D.detype_len_of_edgeOf E (μ := μ) (hμ := hμ) (hμ1 := hμ1) h
  unfold TailoredGame.Accepts TailoredGame.len Accepts
  rw [h1, h2, h3, h4]
  simp only [detype, h]

/-- **Off the edges, the detyped tailored game accepts every pair of the right lengths.** -/
theorem detype_accepts_of_edgeOf_none {x y : Coord T ι → ZMod 2} (h : edgeOf E x y = none)
    (a b : BitStr) (ha : a.length = (D.detype E μ hμ hμ1).len x)
    (hb : b.length = (D.detype E μ hμ hμ1).len y) :
    (D.detype E μ hμ hμ1).Accepts x y a b := by
  refine ⟨ha, hb, fun c hc => ?_⟩
  simp [detype, h] at hc

/-! ## The two reductions to typed questions -/

variable {A : Type*} (Dt : Question T ι → Question T ι → A → A → Bool)

/-- Decode a detyped answer through its question's type, `a₀` off the decodable views. -/
noncomputable def decD (decT : Question T ι → BitStr → A) (a₀ : A) (x : Coord T ι → ZMod 2)
    (a : BitStr) : A :=
  match typeOf E x with
  | some t => decT (t, pull .inr x) a
  | none => a₀

/-- Encode a detyped answer through its question's type, `[]` off the decodable views. -/
noncomputable def encD (encT : Question T ι → A → BitStr) (x : Coord T ι → ZMod 2) (a : A) :
    BitStr :=
  match typeOf E x with
  | some t => encT (t, pull .inr x) a
  | none => []

omit [Fintype ι] [DecidableEq ι] in
theorem decD_of_edgeOf {decT : Question T ι → BitStr → A} {a₀ : A}
    {x y : Coord T ι → ZMod 2} {u v : Question T ι} (h : edgeOf E x y = some (u, v))
    (a b : BitStr) : decD E decT a₀ x a = decT u a ∧ decD E decT a₀ y b = decT v b := by
  obtain ⟨hx, hy, hux, hvy⟩ := typeOf_of_edgeOf E h
  simp [decD, hx, hy, ← hux, ← hvy]

omit [Fintype ι] [DecidableEq ι] in
theorem encD_of_edgeOf {encT : Question T ι → A → BitStr}
    {x y : Coord T ι → ZMod 2} {u v : Question T ι} (h : edgeOf E x y = some (u, v))
    (a b : A) : encD E encT x a = encT u a ∧ encD E encT y b = encT v b := by
  obtain ⟨hx, hy, hux, hvy⟩ := typeOf_of_edgeOf E h
  simp [encD, hx, hy, ← hux, ← hvy]

/-- **Soundness, reduced to the edges**: if on every edge a pair the typed data accepts decodes
to a pair the typed predicate accepts, then every pair the detyped tailored game accepts decodes
to a pair the detyped predicate accepts. -/
theorem detype_accepts_dec (decT : Question T ι → BitStr → A) (a₀ : A)
    (h : ∀ u v a b, E u.1 v.1 → D.Accepts u v a b → Dt u v (decT u a) (decT v b) = true)
    (x y : Coord T ι → ZMod 2) (a b : BitStr) (hab : (D.detype E μ hμ hμ1).Accepts x y a b) :
    Detyping.accepts E Dt x y (decD E decT a₀ x a) (decD E decT a₀ y b) = true := by
  rw [accepts_eq_edgeOf]
  cases he : edgeOf E x y with
  | none => rfl
  | some uv =>
    obtain ⟨u, v⟩ := uv
    obtain ⟨hda, hdb⟩ := decD_of_edgeOf E (decT := decT) (a₀ := a₀) he a b
    dsimp only
    rw [hda, hdb]
    have hE : E u.1 v.1 := by
      unfold edgeOf at he
      split at he
      · split_ifs at he with hc
        · simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hc.1
      · exact absurd he (by simp)
    exact h u v a b hE ((D.detype_accepts_iff_of_edgeOf E he a b).1 hab)

/-- **Completeness, reduced to the edges**: if the typed encodings have the typed lengths, and
on every edge an accepted pair of encodable answers encodes to a pair the typed data accepts,
then every accepted pair of encodable detyped answers encodes to a pair the detyped tailored
game accepts. Off the decodable views the only encodable answer encodes to `[]`. -/
theorem detype_accepts_enc (encT : Question T ι → A → BitStr) (okT : Question T ι → A → Prop)
    (hlen : ∀ u a, okT u a → (encT u a).length = D.lenR u.1 + D.lenL u.1)
    (h : ∀ u v a b, E u.1 v.1 → okT u a → okT v b → Dt u v a b = true →
      D.Accepts u v (encT u a) (encT v b))
    (x y : Coord T ι → ZMod 2) (a b : A)
    (ha : ∀ t, typeOf E x = some t → okT (t, pull .inr x) a)
    (hb : ∀ t, typeOf E y = some t → okT (t, pull .inr y) b)
    (hab : Detyping.accepts E Dt x y a b = true) :
    (D.detype E μ hμ hμ1).Accepts x y (encD E encT x a) (encD E encT y b) := by
  have hlenD : ∀ (z : Coord T ι → ZMod 2) (c : A),
      (∀ t, typeOf E z = some t → okT (t, pull .inr z) c) →
        (encD E encT z c).length = (D.detype E μ hμ hμ1).len z := by
    intro z c hc
    unfold encD TailoredGame.len
    cases hz : typeOf E z with
    | none => simp [detype, hz]
    | some t => simp [detype, hz, hlen _ _ (hc t hz)]
  rw [accepts_eq_edgeOf] at hab
  cases he : edgeOf E x y with
  | none =>
    exact D.detype_accepts_of_edgeOf_none E he _ _ (hlenD x a ha) (hlenD y b hb)
  | some uv =>
    obtain ⟨u, v⟩ := uv
    rw [he] at hab
    obtain ⟨hx, hy, hux, hvy⟩ := typeOf_of_edgeOf E he
    obtain ⟨hea, heb⟩ := encD_of_edgeOf E (encT := encT) he a b
    rw [D.detype_accepts_iff_of_edgeOf E he, hea, heb]
    have hE : E u.1 v.1 := by
      unfold edgeOf at he
      split at he
      · split_ifs at he with hc
        · simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hc.1
      · exact absurd he (by simp)
    have hu : okT u a := by
      have := ha u.1 hx
      rwa [← hux] at this
    have hv : okT v b := by
      have := hb v.1 hy
      rwa [← hvy] at this
    exact h u v a b hE hu hv hab

end TypedData

end MIPRE.Tailored

end
