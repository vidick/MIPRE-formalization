/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedPresentation
import MIPRE.Foundations.CL.DetypingProgRoute
import MIPRE.Foundations.CL.DetypingProgCost

/-! # The executable typed introspection sampler router

Dimension queries and Pauli queries call the supplied sampler once. Auxiliary
queries write the zero vector or the appropriate factor indicator, using the
length of the supplied vector. This total router needs no decoding of the
ambient dimension and does not depend on the number of hiding types.
-/

noncomputable section

namespace MIPRE.Introspection.SamplerProgram

open Cost Cost.PolyTimeFun CL CL.Detyping.Program

def auxResult (p : Parsed) : BitStr :=
  if p.2.1 = 2 then pad false p.2.2.2.2.2
  else if p.2.1 = 3 then pad (decide (p.2.2.2.1 = 1)) p.2.2.2.2.1
  else pad false p.2.2.2.2.1

def aux : PolyTimeFun Parsed BitStr :=
  ite (ap₂ SAT.ArrayProg.eqNat pKind (const 2)) ((map (const false)).comp pY)
    (ite (ap₂ SAT.ArrayProg.eqNat pKind (const 3))
      (ite (ap₂ SAT.ArrayProg.eqNat pLevel (const 1))
        ((map (const true)).comp pU) ((map (const false)).comp pU))
      ((map (const false)).comp pU))

theorem aux_apply (p : Parsed) : aux p = auxResult p := by
  have hf : (const false : PolyTimeFun Bool Bool).toFun = fun _ => false := rfl
  have ht : (const true : PolyTimeFun Bool Bool).toFun = fun _ => true := rfl
  simp only [aux, auxResult, pKind, pLevel, pU, pY, pad, PolyTimeFun.ite_apply,
    ap₂_apply, SAT.ArrayProg.eqNat_apply, const_apply, comp_apply, map_apply,
    fst_apply, snd_apply, decide_eq_true_eq, hf, ht]
  split_ifs <;> simp_all

def routeResult (x : Data) : Bool × Data :=
  let n := treeHead x
  let q := treeTail x
  if rawTruth q then
    if rawTruth (treeHead (treeHead q)) then
      directResult (auxResult (parse (.cons n (treeTail q))))
    else callResult (.cons n (.cons (treeTail (treeHead q)) (treeTail q))) .nil
  else callResult (.cons n .nil) .nil

def route : PolyTimeFun Data (Bool × Data) :=
  let n := treeHead
  let q := treeTail
  let typ := treeHead.comp q
  let body := treeTail.comp q
  let call := fun a : PolyTimeFun Data Data =>
    (const true).pair (ap₂ treePair a (const Data.nil))
  ite (rawTruthProg.comp q)
    (ite (rawTruthProg.comp (treeHead.comp typ))
      ((const false).pair (encoded.comp (aux.comp (parse.comp (ap₂ treePair n body)))))
      (call (ap₂ treePair n (ap₂ treePair (treeTail.comp typ) body))))
    (call (ap₂ treePair n (const Data.nil)))

theorem route_apply (x : Data) : route x = routeResult x := by
  simp only [route, routeResult, PolyTimeFun.ite_apply, comp_apply, pair_apply, const_apply,
    ap₂_apply, treePair_apply, encoded_apply, aux_apply, directResult, callResult,
    rawTruthProg]

theorem route_dimension {P : Type*} [SizedEncoding P] (n : ℕ) :
    route (encode (n, (TypedSampler.Query.dimension : TypedSampler.Query P))) =
      callResult (.cons (encode n) .nil) .nil := by
  rw [route_apply]
  rfl

theorem route_pauli {P : Type*} [SizedEncoding P] (ℓ n : ℕ) (p : P) (q : Sampler.Query) :
    route (encode (n, TypedSampler.Query.atType (QuestionType.pauli (ℓ := ℓ) p) q)) =
      callResult (encode (n, TypedSampler.Query.atType p q)) .nil := by
  rw [route_apply]
  rfl

theorem route_aux {P : Type*} [SizedEncoding P] {ℓ : ℕ} (n : ℕ)
    (t : AuxType ℓ) (role : Bool) (q : Sampler.Query) :
    route (encode (n, TypedSampler.Query.atType (.inr (t, role) : QuestionType P ℓ) q)) =
      directResult (auxResult (encode n, q.toTuple.1, q.toTuple.2.1.toBool,
        q.toTuple.2.2.1, q.toTuple.2.2.2.1, q.toTuple.2.2.2.2)) := by
  rw [route_apply]
  change directResult (auxResult (parse (encode (n, q)))) = _
  rw [parse_query]

theorem route_preserves (n : ℕ) (q a : Data)
    (h : route (.cons (encode n) q) = (true, a)) :
    ∃ d ctx, a = .cons (.cons (encode n) d) ctx := by
  rw [route_apply] at h
  simp only [routeResult, treeHead_cons, treeTail_cons] at h
  by_cases hq : rawTruth q = true
  · by_cases ht : rawTruth (treeHead (treeHead q)) = true
    · simp [hq, ht, directResult] at h
    · simp [hq, ht, callResult] at h
      exact ⟨_, .nil, h.symm⟩
  · simp [hq, callResult] at h
    exact ⟨.nil, .nil, h.symm⟩

def post : PolyTimeFun (Data × Data) Data := snd

theorem post_apply (ctx r : Data) : post (ctx, r) = r := rfl

def prog {P : Type*} [SizedEncoding P] (S : TypedSampler 3 P) : Prog :=
  Prog.routeOneCall route S.prog post

theorem prog_closed {P : Type*} [SizedEncoding P] (S : TypedSampler 3 P) :
    (prog S).WellScoped 1 := Prog.routeOneCall_closed _ S.closed _

theorem prog_halts {P : Type*} [SizedEncoding P] (S : TypedSampler 3 P) (n : ℕ) (d : Data) :
    Halts (prog S) (.cons (encode n) d) :=
  Prog.routeOneCall_halts _ S.closed _ n d (S.halts n) (route_preserves n d)

theorem prog_run_call {P : Type*} [SizedEncoding P] (S : TypedSampler 3 P)
    (x a r : Data) (time : ℕ) (h : route x = callResult a .nil)
    (hr : S.prog.Runs a r time) : ∃ t, (prog S).Runs x r t :=
  Prog.routeOneCall_indirect route S.closed post x a .nil r time h hr

theorem prog_run_direct {P : Type*} [SizedEncoding P] (S : TypedSampler 3 P)
    (x : Data) (out : BitStr) (h : route x = directResult out) :
    ∃ t, (prog S).Runs x (encode out) t := Prog.routeOneCall_direct route S.prog post x _ h

end MIPRE.Introspection.SamplerProgram
