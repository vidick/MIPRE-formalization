/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgParse
import MIPRE.Foundations.CL.DetypingProgBits
import MIPRE.Foundations.CL.DetypingProgCall
import MIPRE.Foundations.Cost.BinaryCompare

/-! # Executable routing of detyped queries

The fixed finite graph is compiled into a table. The variable content is
processed by list operations and at most one call to the original typed
sampler. Padding follows the supplied content vector, so malformed queries
never cause an unbounded dimension allocation.
-/

noncomputable section

namespace MIPRE.CL.Detyping.Program

open Cost Cost.PolyTimeFun

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]

abbrev GraphArgs (T : Type*) [Fintype T] :=
  Bool × Bool × (Fin (graphDim T) → 𝔽₂) × (Fin (graphDim T) → 𝔽₂)
abbrev GraphResult := BitStr × BitStr × BitStr × Data

def graphResult (E : T → T → Prop) [DecidableRel E] (a : GraphArgs T) : GraphResult :=
  let g := pull graphEquiv.toEmbedding a.2.2.1
  let y := pull graphEquiv.toEmbedding a.2.2.2
  let L := Graph.presentation E a.1
  ((if a.2.1 then graphBits ((L.truncate 1).eval g) else graphBits (L.eval g)),
   graphBits (L.mapOfPrefix (if a.2.1 then 0 else 1) g y),
   indicatorBits ((L.factorOfPrefix (if a.2.1 then 0 else 1) g).map graphEquiv.toEmbedding),
   match select E a.1 g with
   | none => .nil
   | some t => .cons (encode t) .nil)

def graphAction (E : T → T → Prop) [DecidableRel E] : PolyTimeFun (GraphArgs T) GraphResult :=
  finiteFunction (graphResult E)

def pIndex : PolyTimeFun Parsed Data := fst
def pKind : PolyTimeFun Parsed ℕ := fst.comp snd
def pPlayer : PolyTimeFun Parsed Bool := fst.comp (snd.comp snd)
def pLevel : PolyTimeFun Parsed ℕ := fst.comp (snd.comp (snd.comp snd))
def pU : PolyTimeFun Parsed BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def pY : PolyTimeFun Parsed BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def graphArgs : PolyTimeFun Parsed (GraphArgs T) :=
  pPlayer.pair ((ap₂ SAT.ArrayProg.eqNat pLevel (const 1)).pair
    ((readVector (graphDim T)).comp pU |>.pair ((readVector (graphDim T)).comp pY)))

abbrev Context := Parsed × GraphResult

def content (g : ℕ) (u : BitStr) : BitStr := u.drop g
def pad (b : Bool) (u : BitStr) : BitStr := u.map (fun _ => b)
def directResult (u : BitStr) : Bool × Data := (false, encode u)
def withPrefix (preBits : BitStr) : Data := .cons .nil (encode preBits)
def callResult (arg ctx : Data) : Bool × Data := (true, .cons arg ctx)

def typedRequest (n typ : Data) (kind : ℕ) (w : Bool) (j : ℕ) (u y : BitStr) : Data :=
  .cons n (.cons typ (encode (kind, w, j, u, y)))

def routeResult (g : ℕ) (p : Parsed) (a : GraphResult) : Bool × Data :=
  let n := p.1
  let k := p.2.1
  let w := p.2.2.1
  let j := p.2.2.2.1
  let u := content g p.2.2.2.2.1
  let y := content g p.2.2.2.2.2
  let zeros := List.replicate g false
  let typ := treeHead a.2.2.2
  if k = 0 then callResult (.cons n .nil) .nil
  else if k = 1 then
    if j ≤ 2 then directResult (a.1 ++ pad false u)
    else if rawTruth a.2.2.2 then
      callResult (typedRequest n typ 1 w (j - 2) u []) (withPrefix a.1)
    else directResult (a.1 ++ pad false u)
  else if k = 2 then
    if j ≤ 2 then directResult (a.2.1 ++ pad false y)
    else if rawTruth a.2.2.2 then
      callResult (typedRequest n typ 2 w (j - 2) u y) (withPrefix zeros)
    else directResult (zeros ++ pad false y)
  else if k = 3 then
    if j ≤ 2 then directResult (a.2.2.1 ++ pad false u)
    else if rawTruth a.2.2.2 then
      callResult (typedRequest n typ 3 w (j - 2) u []) (withPrefix zeros)
    else directResult (zeros ++ pad (decide (j = 3)) u)
  else (false, .nil)

private def directP (u : PolyTimeFun Context BitStr) : PolyTimeFun Context (Bool × Data) :=
  (const false).pair (encoded.comp u)

private def callP (arg ctx : PolyTimeFun Context Data) : PolyTimeFun Context (Bool × Data) :=
  (const true).pair (ap₂ treePair arg ctx)

private def prefixP (u : PolyTimeFun Context BitStr) : PolyTimeFun Context Data :=
  ap₂ treePair (const Data.nil) (encoded.comp u)

def routeParsed (g : ℕ) : PolyTimeFun Context (Bool × Data) :=
  let n := pIndex.comp fst
  let k := pKind.comp fst
  let w := pPlayer.comp fst
  let j := pLevel.comp fst
  let u := ap₂ drop (pU.comp fst) (const (unary g))
  let y := ap₂ drop (pY.comp fst) (const (unary g))
  let zeros := const (List.replicate g false)
  let zu := (map (const false)).comp u
  let zy := (map (const false)).comp y
  let marg := fst.comp snd
  let lin := fst.comp (snd.comp snd)
  let fac := fst.comp (snd.comp (snd.comp snd))
  let sel := snd.comp (snd.comp (snd.comp snd))
  let typ := treeHead.comp sel
  let chosen := rawTruthProg.comp sel
  let early := ap₂ leNat j (const 2)
  let r := ap₂ subUnary j (const (unary 2))
  let req := fun (kind : ℕ) (v : PolyTimeFun Context BitStr) =>
    ap₂ treePair n (ap₂ treePair typ
      (encoded.comp ((const kind).pair (w.pair (r.pair (u.pair v))))))
  ite (ap₂ SAT.ArrayProg.eqNat k (const 0))
    (callP (ap₂ treePair n (const Data.nil)) (const Data.nil))
    (ite (ap₂ SAT.ArrayProg.eqNat k (const 1))
      (ite early (directP (ap₂ append marg zu))
        (ite chosen (callP (req 1 (const [])) (prefixP marg)) (directP (ap₂ append marg zu))))
      (ite (ap₂ SAT.ArrayProg.eqNat k (const 2))
        (ite early (directP (ap₂ append lin zy))
          (ite chosen (callP (req 2 y) (prefixP zeros)) (directP (ap₂ append zeros zy))))
        (ite (ap₂ SAT.ArrayProg.eqNat k (const 3))
          (ite early (directP (ap₂ append fac zu))
            (ite chosen (callP (req 3 (const [])) (prefixP zeros))
              (directP (ap₂ append zeros
                (ite (ap₂ SAT.ArrayProg.eqNat j (const 3)) ((map (const true)).comp u) zu)))))
          (const (false, Data.nil)))))

theorem routeParsed_apply (g : ℕ) (p : Parsed) (a : GraphResult) :
    routeParsed g (p, a) = routeResult g p a := by
  have hf : (const false : PolyTimeFun Bool Bool).toFun = fun _ => false := rfl
  have ht : (const true : PolyTimeFun Bool Bool).toFun = fun _ => true := rfl
  simp only [routeParsed, routeResult, pIndex, pKind, pPlayer, pLevel, pU, pY,
    directP, callP, prefixP, directResult, callResult, typedRequest, withPrefix,
    ap₂_apply, PolyTimeFun.ite_apply, pair_apply, comp_apply, fst_apply, snd_apply, const_apply,
    treePair_apply, encoded_apply, SAT.ArrayProg.eqNat_apply, leNat_apply,
    subUnary_apply, drop_apply, length_unary, map_apply, append_apply,
    rawTruthProg, decide_eq_true_eq, content, pad, hf, ht]
  split_ifs <;> simp_all

def route (E : T → T → Prop) [DecidableRel E] : PolyTimeFun Data (Bool × Data) :=
  (routeParsed (graphDim T)).comp
    ((PolyTimeFun.id Parsed).pair ((graphAction E).comp graphArgs) |>.comp parse)

def post (g : ℕ) : PolyTimeFun (Data × Data) Data :=
  ite (rawTruthProg.comp fst)
    (encoded.comp (ap₂ append (readBits.comp (treeTail.comp fst)) (readBits.comp snd)))
    (encoded.comp (ap₂ addUnary (readNat.comp snd) (const (unary g))))

theorem post_dimension (g s : ℕ) : post g (.nil, encode s) = encode (s + g) := by
  change encode (readNat (encode s) + (unary g).length) = _
  rw [readNat_encode, length_unary]

theorem post_prefix (g : ℕ) (preBits result : BitStr) :
    post g (withPrefix preBits, encode result) = encode (preBits ++ result) := by
  change encode (readBits (encode preBits) ++ readBits (encode result)) = _
  rw [readBits_encode, readBits_encode]

theorem routeResult_preserves (g : ℕ) (p : Parsed) (a : GraphResult) (payload : Data)
    (h : routeResult g p a = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons p.1 d) ctx := by
  dsimp only [routeResult] at h
  split_ifs at h <;> simp only [callResult, directResult, typedRequest, Prod.mk.injEq,
    Bool.false_eq_true, false_and, true_and] at h
  all_goals first | contradiction | (subst payload; exact ⟨_, _, rfl⟩)

theorem route_preserves (E : T → T → Prop) [DecidableRel E] (n : ℕ) (q payload : Data)
    (h : route E (.cons (encode n) q) = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons (encode n) d) ctx := by
  simp only [route, comp_apply, pair_apply, id_apply, routeParsed_apply] at h
  exact routeResult_preserves _ _ _ _ h

end MIPRE.CL.Detyping.Program
