/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgRoute
import MIPRE.Foundations.CL.DetypingGame

/-! # The executable detyping decision router

This is an explicit ambient adaptation of `types.tex`'s detyped decider.
Canonical field encodings and question dimensions are checked first. An outer answer cutoff is
enforced globally, as required by the ambient verifier budget. Within that
cutoff nonedge views accept, and edge views use the source typed answer
cutoff before invoking the typed decider. No uniform graph compilation or
absolute source-model timeout bound is claimed here.

Thus malformed graph patterns in binary questions accept within the outer
cutoff, while noncanonical raw data encodings reject. The latter convention
has no effect on the finite games, whose fields are binary strings.
-/

noncomputable section

namespace MIPRE.CL.Detyping.DeciderProgram

set_option linter.unusedSectionVars false

open Cost Cost.PolyTimeFun Detyping.Program

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]

/-- Recognize a genuine ordered edge from the complete graph-view patterns. -/
def selectedEdge (E : T → T → Prop) [DecidableRel E]
    (x y : Graph.Coord T → 𝔽₂) : Option (T × T) :=
  match select E false x, select E true y with
  | some u, some v => if E u v ∧ x = view E false u ∧ y = view E true v then some (u, v) else none
  | _, _ => none

/-- Valid embedded views recover precisely their original edge. -/
theorem selectedEdge_views (E : T → T → Prop) [DecidableRel E]
    (u v : T) (h : E u v) : selectedEdge E (view E false u) (view E true v) = some (u, v) := by
  simp [selectedEdge, select_view, h]

def edgeData (E : T → T → Prop) [DecidableRel E]
    (x y : Graph.Coord T → 𝔽₂) : Data :=
  match selectedEdge E x y with
  | none => .nil
  | some uv => .cons (encode uv.1) (encode uv.2)

/-- The finite graph recognition table is an actual ambient program. -/
def edgeAction (E : T → T → Prop) [DecidableRel E] :
    PolyTimeFun ((Fin (graphDim T) → 𝔽₂) × (Fin (graphDim T) → 𝔽₂)) Data :=
  finiteFunction fun p => edgeData E (pull graphEquiv.toEmbedding p.1) (pull graphEquiv.toEmbedding p.2)

def lengthNat : PolyTimeFun BitStr ℕ := ap₂ addUnary (const 0) length

@[simp] theorem lengthNat_apply (x : BitStr) : lengthNat x = x.length := by simp [lengthNat]

/-- A raw input context after the dimension and cutoff routines have returned. -/
def context (input : Data) (s inner outer : ℕ) : Data :=
  .cons (.cons input (encode s)) (encode (inner, outer))

def inputReader : PolyTimeFun Data Data := treeHead.comp treeHead
def indexReader : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp inputReader)
def xReader : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (treeTail.comp inputReader))
def yReader : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (treeTail.comp (treeTail.comp inputReader)))
def aReader : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp inputReader))))
def bReader : PolyTimeFun Data BitStr := readBits.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp inputReader))))
def dimensionReader : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp treeHead)
def innerReader : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp treeTail)
def outerReader : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp treeTail)

/-- The typed decider is called using the seven-field input convention from the source. -/
def typedArgument (n : ℕ) (u v : Data) (x y a b : BitStr) : Data :=
  .cons (encode n) (.cons u (.cons (encode x) (.cons v (encode (y, a, b)))))

theorem typedArgument_encode (n : ℕ) (u v : T) (x y a b : BitStr) :
    typedArgument n (encode u) (encode v) x y a b = encode (n, u, x, v, y, a, b) := rfl

/-- The precise routing rule, including every malformed-input branch. -/
def routeResult (E : T → T → Prop) [DecidableRel E] (c : Data) : Bool × Data :=
  let input := inputReader c
  let n := indexReader c
  let x := xReader c
  let y := yReader c
  let a := aReader c
  let b := bReader c
  let dim := graphDim T + dimensionReader c
  let inner := innerReader c
  let outer := outerReader c
  let edge := edgeData E (graphOfBits x) (graphOfBits y)
  if input = encode (n, x, y, a, b) ∧ x.length = dim ∧ y.length = dim ∧
      a.length ≤ outer ∧ b.length ≤ outer then
    if rawTruth edge then
      if a.length ≤ inner ∧ b.length ≤ inner then
        (true, .cons (typedArgument n (treeHead edge) (treeTail edge)
          (x.drop (graphDim T)) (y.drop (graphDim T)) a b) .nil)
      else (false, encode false)
    else (false, encode true)
  else (false, encode false)

/-- All routing and format checks are concrete polynomial-time ambient computations. -/
def route (E : T → T → Prop) [DecidableRel E] : PolyTimeFun Data (Bool × Data) :=
  let n := indexReader
  let x := xReader
  let y := yReader
  let a := aReader
  let b := bReader
  let canonical := encoded.comp (n.pair (x.pair (y.pair (a.pair b))))
  let dim := ap₂ addUnary dimensionReader (const (unary (graphDim T)))
  let edge := (edgeAction E).comp (((readVector (graphDim T)).comp x).pair ((readVector (graphDim T)).comp y))
  let x' := ap₂ drop x (const (unary (graphDim T)))
  let y' := ap₂ drop y (const (unary (graphDim T)))
  let request := ap₂ treePair (encoded.comp n) (ap₂ treePair (treeHead.comp edge)
    (ap₂ treePair (encoded.comp x') (ap₂ treePair (treeTail.comp edge)
      (encoded.comp (y'.pair (a.pair b))))))
  let call := (const true).pair (ap₂ treePair request (const Data.nil))
  let reject := const (false, encode false)
  ite (ap₂ treeEq inputReader canonical)
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp x) dim)
      (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp y) dim)
        (ite (ap₂ leNat (lengthNat.comp a) outerReader)
          (ite (ap₂ leNat (lengthNat.comp b) outerReader)
            (ite (rawTruthProg.comp edge)
              (ite (ap₂ leNat (lengthNat.comp a) innerReader)
                (ite (ap₂ leNat (lengthNat.comp b) innerReader) call reject) reject)
              (const (false, encode true))) reject) reject) reject) reject) reject

theorem route_apply (E : T → T → Prop) [DecidableRel E] (c : Data) : route E c = routeResult E c := by
  simp only [route, routeResult, edgeAction, ap₂_apply, comp_apply, pair_apply,
    const_apply, encoded_apply, treePair_apply, treeEq_apply, SAT.ArrayProg.eqNat_apply,
    lengthNat_apply, leNat_apply, addUnary_apply, length_unary, drop_apply, finiteFunction_apply,
    readVector_apply, PolyTimeFun.ite_apply, graphOfBits, rawTruthProg, typedArgument,
    decide_eq_true_eq]
  simp only [Nat.add_comm]
  split_ifs <;> simp_all

theorem route_context (E : T → T → Prop) [DecidableRel E]
    (n s inner outer : ℕ) (x y a b : BitStr) :
    route E (context (encode (n, x, y, a, b)) s inner outer) =
      if x.length = graphDim T + s ∧ y.length = graphDim T + s ∧
          a.length ≤ outer ∧ b.length ≤ outer then
        match selectedEdge E (graphOfBits x) (graphOfBits y) with
        | none => (false, encode true)
        | some uv => if a.length ≤ inner ∧ b.length ≤ inner then
            (true, .cons (encode (n, uv.1, x.drop (graphDim T), uv.2, y.drop (graphDim T), a, b)) .nil)
          else (false, encode false)
      else (false, encode false) := by
  rw [route_apply]
  simp only [routeResult, context, inputReader, indexReader, xReader, yReader, aReader, bReader,
    dimensionReader, innerReader, outerReader, comp_apply, encode_prod, treeHead_cons, treeTail_cons,
    readNat_encode, readBits_encode, true_and]
  cases h : selectedEdge E (graphOfBits x) (graphOfBits y) <;>
    simp [edgeData, h, rawTruth, typedArgument, encode_prod]

/-- Successful routing preserves the normalized original index on all raw input trees. -/
theorem route_preserves (E : T → T → Prop) [DecidableRel E] (c payload : Data)
    (h : route E c = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons (encode (indexReader c)) d) ctx := by
  rw [route_apply] at h
  dsimp only [routeResult] at h
  split_ifs at h <;> simp only [Prod.mk.injEq, Bool.false_eq_true, false_and, true_and] at h
  all_goals first | contradiction | (subst payload; exact ⟨_, _, rfl⟩)

/-- An arbitrary typed output is accepted exactly when it is the canonical Boolean true. -/
def post : PolyTimeFun (Data × Data) Data :=
  encoded.comp (ap₂ treeEq snd (const (encode true)))

theorem post_apply (ctx out : Data) : post (ctx, out) = encode (decide (out = encode true)) := rfl

end MIPRE.CL.Detyping.DeciderProgram
