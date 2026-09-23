/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularTyped
import MIPRE.Foundations.CL.TypedSampler
import MIPRE.Foundations.CL.DetypingProgRoute
import MIPRE.Foundations.Cost.Universal
import MIPRE.Foundations.Repeat.SamplerCost
import MIPRE.Foundations.CL.DetypingProgCost

/-!
# The typed oracularized sampler

Piece O3 of `planning/oracularization.md` (issue #189): the sampler of the paper's typed
oracularized verifier (`sec:orac-def`) as a `CL.TypedSampler` over the three roles, whose typed CL
functions are `roleFamily` of the input sampler's (the identity for the oracle, the input's for the
isolated players) — the half of `lem:oracle-effective-interface` about the sampler.

The program is the fixed core `OracleSampler.core`, run on the input sampler's program through
the s-m-n construction `hardcode`, as the repeated sampler is. The core routes a typed query with
at most one call to the input sampler, through the universal machine:

* the dimension query is forwarded unchanged;
* a query at an isolated role is forwarded as the query of the corresponding original player;
* a query at the oracle role is answered from the query itself, with no call at all: the
  identity's marginals are the seed, its first stage map is the identity and its later ones zero,
  its first factor space is everything and its later ones nothing. The zero vectors are written
  over the supplied vector rather than over the dimension, so the core never allocates by a
  dimension it has not been given.
-/

namespace MIPRE

open Cost Cost.PolyTimeFun

/-! ## The identity's queries -/

namespace CL.CLFun

variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem factorOfPrefix_trivialOn (ℓ k : ℕ) (u : ι → F) :
    (trivialOn ℓ : CLFun F ι ℓ).factorOfPrefix k u = ∅ := by
  induction ℓ generalizing k u with
  | zero => rfl
  | succ ℓ ih => cases k <;> simp [trivialOn, ih]

theorem mapOfPrefix_trivialOn (ℓ k : ℕ) (u : ι → F) :
    (trivialOn ℓ : CLFun F ι ℓ).mapOfPrefix k u = 0 := by
  induction ℓ generalizing k u with
  | zero => rfl
  | succ ℓ ih =>
    cases k with
    | zero => rfl
    | succ k => simp [trivialOn, ih]

/-- Every marginal of the identity from the first on is the identity. -/
theorem eval_truncate_ident (ℓ j : ℕ) (hj : 1 ≤ j) (x : ι → F) :
    ((ident ℓ : CLFun F ι (ℓ + 1)).truncate j).eval x = x := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  funext i
  simp [ident]

theorem mapOfPrefix_ident_zero (ℓ : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).mapOfPrefix 0 u = proj Finset.univ := rfl

theorem mapOfPrefix_ident_succ (ℓ k : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).mapOfPrefix (k + 1) u = 0 :=
  mapOfPrefix_trivialOn ℓ k _

theorem factorOfPrefix_ident_zero (ℓ : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).factorOfPrefix 0 u = Finset.univ := rfl

theorem factorOfPrefix_ident_succ (ℓ k : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).factorOfPrefix (k + 1) u = ∅ :=
  factorOfPrefix_trivialOn ℓ k _

end CL.CLFun

namespace CL

theorem toBits_zero' (s : ℕ) : toBits (0 : Fin s → 𝔽₂) = List.replicate s false := by
  simp [toBits]

theorem indicatorBits_univ_eq (s : ℕ) :
    indicatorBits (Finset.univ : Finset (Fin s)) = List.replicate s true := by
  simp [indicatorBits]

theorem indicatorBits_empty_eq (s : ℕ) :
    indicatorBits (∅ : Finset (Fin s)) = List.replicate s false := by
  simp [indicatorBits]

theorem map_const_eq_replicate {α β : Type*} (b : β) (l : List α) :
    l.map (fun _ => b) = List.replicate l.length b := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

@[simp] theorem _root_.MIPRE.Cost.PolyTimeFun.const_toFun {α β : Type*} [SizedEncoding α]
    [SizedEncoding β] (b : β) : (PolyTimeFun.const b : PolyTimeFun α β).toFun = fun _ => b := rfl

@[simp] theorem encode_typedQuery_dimension {T : Type*} [SizedEncoding T] :
    (encode (TypedSampler.Query.dimension : TypedSampler.Query T) : Data) = .nil := rfl

@[simp] theorem encode_typedQuery_atType {T : Type*} [SizedEncoding T] (t : T)
    (q : Sampler.Query) :
    (encode (TypedSampler.Query.atType t q) : Data) = .cons (encode t) (encode q) := rfl

/-- A query with its player replaced; the dimension query has none. -/
def Sampler.Query.withPlayer (w : Player) : Sampler.Query → Sampler.Query
  | .dimension => .dimension
  | .marginal _ j z => .marginal w j z
  | .linear _ j u y => .linear w j u y
  | .factor _ j u => .factor w j u

end CL

/-! ## Roles as data -/

/-- The roles as numbers: the oracle `0`, the isolated Alice `1`, the isolated Bob `2`. -/
def Role.toNat : Role → ℕ
  | .oracle => 0
  | .alice => 1
  | .bob => 2

/-- Reading a role back. -/
def Role.ofNat? : ℕ → Option Role
  | 0 => some .oracle
  | 1 => some .alice
  | 2 => some .bob
  | _ => none

instance : SizedEncoding Role where
  encode r := encode r.toNat
  decode d := (decode d : Option ℕ).bind Role.ofNat?
  decode_encode r := by cases r <;> simp [SizedEncoding.decode_encode, Role.toNat, Role.ofNat?]

theorem encode_role_oracle : (encode Role.oracle : Data) = .nil := rfl

theorem encode_role_alice : (encode Role.alice : Data) = .cons (.cons .nil .nil) .nil := rfl

theorem encode_role_bob : (encode Role.bob : Data) = .cons .nil (.cons (.cons .nil .nil) .nil) :=
  rfl

/-! ## The core -/

namespace OracleSampler

open CL CL.Detyping.Program

/-- The input sampler's program, hardcoded first. -/
noncomputable def sD : PolyTimeFun Data Data := treeHead
/-- The index. -/
noncomputable def nD : PolyTimeFun Data Data := treeHead.comp treeTail
/-- The typed query, `nil` for the dimension query. -/
noncomputable def qD : PolyTimeFun Data Data := treeTail.comp treeTail
/-- The type of a typed query. -/
noncomputable def tagD : PolyTimeFun Data Data := treeHead.comp qD
/-- The untyped query of a typed query. -/
noncomputable def queryD : PolyTimeFun Data Data := treeTail.comp qD

/-- A call to the input sampler, through the universal machine, on the query `q`. -/
noncomputable def request (q : PolyTimeFun Data Data) : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (ap₂ treePair sD (ap₂ treePair nD q)) (const Data.nil))

/-- An isolated role's query, as the query of the corresponding original player. -/
noncomputable def asPlayer (w : Player) : PolyTimeFun Data Data :=
  ap₂ treePair (treeHead.comp queryD)
    (ap₂ treePair (const (encode w)) (treeTail.comp (treeTail.comp queryD)))

/-- The untyped query, parsed: `(n, kind, w, j, u, y)`. -/
noncomputable def parsedQ : PolyTimeFun Data Parsed := parse.comp (ap₂ treePair nD queryD)

/-- **The oracle's answers**, read off the query alone: the marginal of the identity is the seed;
its first stage map is the identity and its later ones zero; its first factor space is everything
and its later ones nothing. -/
noncomputable def oracleBits : PolyTimeFun Data BitStr :=
  let k := pKind.comp parsedQ
  let j := pLevel.comp parsedQ
  let u := pU.comp parsedQ
  let y := pY.comp parsedQ
  let first := ap₂ SAT.ArrayProg.eqNat j (const 1)
  ite (ap₂ SAT.ArrayProg.eqNat k (const 1)) u
    (ite (ap₂ SAT.ArrayProg.eqNat k (const 2)) (ite first y ((map (const false)).comp y))
      (ite (ap₂ SAT.ArrayProg.eqNat k (const 3))
        (ite first ((map (const true)).comp u) ((map (const false)).comp u)) (const [])))

/-- **The router**: the dimension query and the isolated roles' queries go to the input sampler,
the oracle's are answered directly. -/
noncomputable def route : PolyTimeFun Data (Bool × Data) :=
  ite (ap₂ treeEq qD (const Data.nil)) (request (const (encode Sampler.Query.dimension)))
    (ite (ap₂ treeEq tagD (const (encode Role.alice))) (request (asPlayer .alice))
      (ite (ap₂ treeEq tagD (const (encode Role.bob))) (request (asPlayer .bob))
        ((const false).pair (encoded.comp oracleBits))))

/-- The answer of the call is the answer. -/
noncomputable def post : PolyTimeFun (Data × Data) Data := snd

/-- The core of the typed oracularized sampler. -/
noncomputable def core : Prog := Prog.routeOneCall route selfUniversal.univ post

theorem core_closed : core.WellScoped 1 :=
  Prog.routeOneCall_closed route selfUniversal.closed post

/-! ### The router on well-formed queries -/

variable (sp : Prog) (n : ℕ)

theorem route_dimension :
    route (.cons (encode sp) (encode (n, (TypedSampler.Query.dimension :
      TypedSampler.Query Role)))) =
      (true, .cons (.cons (encode sp) (encode (n, Sampler.Query.dimension))) .nil) := by
  simp [route, request, qD, sD, nD, encode_prod]

theorem route_alice (q : Sampler.Query) (hq : q ≠ .dimension) :
    route (.cons (encode sp) (encode (n, TypedSampler.Query.atType Role.alice q))) =
      (true, .cons (.cons (encode sp) (encode (n, q.withPlayer .alice))) .nil) := by
  cases q with
  | dimension => exact absurd rfl hq
  | marginal w j z => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | linear w j u y => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | factor w j u => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl


theorem route_bob (q : Sampler.Query) (hq : q ≠ .dimension) :
    route (.cons (encode sp) (encode (n, TypedSampler.Query.atType Role.bob q))) =
      (true, .cons (.cons (encode sp) (encode (n, q.withPlayer .bob))) .nil) := by
  cases q with
  | dimension => exact absurd rfl hq
  | marginal w j z => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | linear w j u y => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | factor w j u => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl

/-- The oracle's answer to an untyped query, as the core computes it. -/
def oracleAnswer : Sampler.Query → BitStr
  | .dimension => []
  | .marginal _ _ z => z
  | .linear _ j _ y => if j = 1 then y else y.map fun _ => false
  | .factor _ j u => if j = 1 then u.map fun _ => true else u.map fun _ => false

theorem parsedQ_apply (d : Data) (q : Sampler.Query) :
    parsedQ (.cons (encode sp) (.cons (encode n) (.cons d (encode q)))) =
      (encode n, q.toTuple.1, q.toTuple.2.1.toBool, q.toTuple.2.2.1, q.toTuple.2.2.2.1,
        q.toTuple.2.2.2.2) := by
  simp only [parsedQ, comp_apply, ap₂_apply, treePair_apply, nD, queryD, qD, treeHead_cons,
    treeTail_cons]
  exact parse_query n q

theorem route_oracle (q : Sampler.Query) :
    route (.cons (encode sp) (encode (n, TypedSampler.Query.atType Role.oracle q))) =
      (false, encode (oracleAnswer q)) := by
  have hq := parsedQ_apply sp n Data.nil q
  simp only [encode_prod, encode_typedQuery_atType, encode_role_oracle]
  cases q with
  | dimension =>
    simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
      encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
  | marginal w j z =>
    simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
      encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
  | linear w j u y =>
    by_cases hj : j = 1
    · subst hj
      simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
    · simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple, hj]
  | factor w j u =>
    by_cases hj : j = 1
    · subst hj
      simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
    · simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple, hj]

/-- Every call the router makes keeps the hardcoded program and the index. -/
theorem route_call_shape (sD' nD' qd' payload : Data)
    (h : route (.cons sD' (.cons nD' qd')) = (true, payload)) :
    ∃ q', payload = .cons (.cons sD' (.cons nD' q')) .nil := by
  simp only [route, PolyTimeFun.ite_apply, request, pair_apply, const_apply, ap₂_apply,
    treePair_apply, sD, nD, comp_apply, treeHead_cons, treeTail_cons, treeEq_apply] at h
  by_cases h1 : qD (.cons sD' (.cons nD' qd')) = .nil
  · simp only [h1, decide_true, if_true] at h
    exact ⟨_, (Prod.mk.inj h).2.symm⟩
  · simp only [h1, decide_false, Bool.false_eq_true, if_false] at h
    by_cases h2 : tagD (.cons sD' (.cons nD' qd')) = encode Role.alice
    · simp only [h2, decide_true, if_true] at h
      exact ⟨_, (Prod.mk.inj h).2.symm⟩
    · simp only [h2, decide_false, Bool.false_eq_true, if_false] at h
      by_cases h3 : tagD (.cons sD' (.cons nD' qd')) = encode Role.bob
      · simp only [h3, decide_true, if_true] at h
        exact ⟨_, (Prod.mk.inj h).2.symm⟩
      · simp only [h3, decide_false, Bool.false_eq_true, if_false] at h
        exact absurd (Prod.mk.inj h).1 (by decide)

/-! ## The typed sampler -/

/-- The program of the typed oracularized sampler on the input sampler's program `sp`. -/
noncomputable def prog (sp : Prog) : Prog := hardcode core (encode sp)

theorem prog_closed (sp : Prog) : (prog sp).WellScoped 1 := hardcode_wellScoped core_closed _

variable {ℓ : ℕ} (S : Sampler (ℓ + 1))

/-- A forwarded query is answered by the input sampler, through the universal machine. -/
theorem prog_runs_forward (x : Data) (q : Sampler.Query) (r : Data) (t : ℕ)
    (hroute : route (.cons (encode S.prog) x) =
      (true, .cons (.cons (encode S.prog) (encode (n, q))) .nil))
    (hS : S.prog.Runs (encode (n, q)) r t) : ∃ t', (prog S.prog).Runs x r t' := by
  obtain ⟨tu, -, hu⟩ := selfUniversal.time_le S.prog (encode (n, q)) r t hS
  obtain ⟨tc, hc⟩ := Prog.routeOneCall_indirect route selfUniversal.closed post _ _ .nil r tu
    hroute hu
  exact ⟨_, hardcode_time core_closed hc⟩

/-- An oracle query is answered directly. -/
theorem prog_runs_oracle (q : Sampler.Query) :
    ∃ t, (prog S.prog).Runs (encode (n, TypedSampler.Query.atType Role.oracle q))
      (encode (oracleAnswer q)) t := by
  obtain ⟨tc, hc⟩ := Prog.routeOneCall_direct route selfUniversal.univ post _ _
    (route_oracle S.prog n q)
  exact ⟨_, hardcode_time core_closed hc⟩

end OracleSampler

open OracleSampler CL

variable {ℓ : ℕ} (S : Sampler (ℓ + 1))

/-- **The typed oracularized sampler** (the sampler of `sec:orac-def`): the typed CL functions
are the identity for the oracle and the input sampler's own for the isolated players, the same
for both players; the program answers an isolated role's query as the input sampler answers the
corresponding original player's, and an oracle query directly. It depends on the input sampler
alone. -/
noncomputable def oracleSampler : TypedSampler (ℓ + 1) Role where
  prog := OracleSampler.prog S.prog
  closed := prog_closed S.prog
  dim := S.dim
  cl n _ t := roleFamily (S.cl n) t
  cl_exactlyOn n _ t := exactlyOn_roleFamily (S.cl_exactlyOn n) t
  runs_dimension n := by
    obtain ⟨t, h⟩ := S.runs_dimension n
    exact prog_runs_forward n S _ _ _ t (route_dimension S.prog n) h
  runs_marginal n w t j z hj hℓ hz := by
    cases t with
    | oracle =>
      have h : toBits (((roleFamily (S.cl n) Role.oracle).truncate j).eval (ofBits (S.dim n) z))
          = oracleAnswer (.marginal w j z) := by
        simp only [roleFamily, CLFun.eval_truncate_ident _ _ hj, toBits_ofBits hz, oracleAnswer]
      rw [h]
      exact prog_runs_oracle n S _
    | alice =>
      obtain ⟨t, h⟩ := S.runs_marginal n .alice j z hj hℓ hz
      exact prog_runs_forward n S _ _ _ t (route_alice S.prog n (.marginal w j z) (by simp)) h
    | bob =>
      obtain ⟨t, h⟩ := S.runs_marginal n .bob j z hj hℓ hz
      exact prog_runs_forward n S _ _ _ t (route_bob S.prog n (.marginal w j z) (by simp)) h
  runs_linear n w t j u y hj hℓ hu hy := by
    cases t with
    | oracle =>
      have h : toBits ((roleFamily (S.cl n) Role.oracle).mapOfPrefix (j - 1)
            (ofBits (S.dim n) u) (ofBits (S.dim n) y)) = oracleAnswer (.linear w j u y) := by
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        cases k with
        | zero =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.mapOfPrefix_ident_zero, oracleAnswer,
            if_true]
          have : proj (Finset.univ : Finset (Fin (S.dim n))) (ofBits (S.dim n) y)
              = ofBits (S.dim n) y := by funext i; simp
          rw [this, toBits_ofBits hy]
        | succ k =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.mapOfPrefix_ident_succ,
            LinearMap.zero_apply, oracleAnswer, show k + 1 + 1 ≠ 1 by omega, if_false,
            toBits_zero', map_const_eq_replicate, hy]
      rw [h]
      exact prog_runs_oracle n S _
    | alice =>
      obtain ⟨t, h⟩ := S.runs_linear n .alice j u y hj hℓ hu hy
      exact prog_runs_forward n S _ _ _ t (route_alice S.prog n (.linear w j u y) (by simp)) h
    | bob =>
      obtain ⟨t, h⟩ := S.runs_linear n .bob j u y hj hℓ hu hy
      exact prog_runs_forward n S _ _ _ t (route_bob S.prog n (.linear w j u y) (by simp)) h
  runs_factor n w t j u hj hℓ hu := by
    cases t with
    | oracle =>
      have hlen : u.length = S.dim n := by
        obtain ⟨x, rfl⟩ := hu
        exact length_toBits _
      have h : indicatorBits ((roleFamily (S.cl n) Role.oracle).factorOfPrefix (j - 1)
            (ofBits (S.dim n) u)) = oracleAnswer (.factor w j u) := by
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        cases k with
        | zero =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.factorOfPrefix_ident_zero,
            oracleAnswer, if_true, indicatorBits_univ_eq, map_const_eq_replicate, hlen]
        | succ k =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.factorOfPrefix_ident_succ,
            oracleAnswer, show k + 1 + 1 ≠ 1 by omega, if_false, indicatorBits_empty_eq,
            map_const_eq_replicate, hlen]
      rw [h]
      exact prog_runs_oracle n S _
    | alice =>
      obtain ⟨t, h⟩ := S.runs_factor n .alice j u hj hℓ hu
      exact prog_runs_forward n S _ _ _ t (route_alice S.prog n (.factor w j u) (by simp)) h
    | bob =>
      obtain ⟨t, h⟩ := S.runs_factor n .bob j u hj hℓ hu
      exact prog_runs_forward n S _ _ _ t (route_bob S.prog n (.factor w j u) (by simp)) h
  halts n d := by
    have hcore : Halts core (.cons (encode S.prog) (.cons (encode n) d)) := by
      cases h : route (.cons (encode S.prog) (.cons (encode n) d)) with
      | mk call payload =>
        cases call with
        | false =>
          obtain ⟨t, hr⟩ := Prog.routeOneCall_direct route selfUniversal.univ post _ payload h
          exact ⟨payload, t, hr⟩
        | true =>
          obtain ⟨q', rfl⟩ := route_call_shape _ _ _ _ h
          obtain ⟨r, t, hr⟩ := S.halts n q'
          obtain ⟨tu, -, hu⟩ := selfUniversal.time_le S.prog _ r t hr
          obtain ⟨tc, hc⟩ := Prog.routeOneCall_indirect route selfUniversal.closed post _ _ .nil
            r tu h hu
          exact ⟨_, tc, hc⟩
    obtain ⟨r, t, hr⟩ := hcore
    exact ⟨r, _, hardcode_time core_closed hr⟩

@[simp] theorem oracleSampler_dim (n : ℕ) : (oracleSampler S).dim n = S.dim n := rfl

@[simp] theorem oracleSampler_cl (n : ℕ) (w : Player) (t : Role) :
    (oracleSampler S).cl n w t = roleFamily (S.cl n) t := rfl


/-! ## The running time -/

namespace OracleSampler

open Repeat

theorem size_treeHead_le (e : Data) : (treeHead e).size ≤ e.size := by
  cases e with
  | nil => exact le_refl _
  | cons a b => simp only [treeHead_cons, Data.size_cons]; omega

theorem size_treeTail_le (e : Data) : (treeTail e).size ≤ e.size := by
  cases e with
  | nil => exact le_refl _
  | cons a b => simp only [treeTail_cons, Data.size_cons]; omega

/-- **A forwarded query is at most twice the typed query**, plus a constant: it is the
dimension query, or the typed query's own fields with the player replaced. -/
theorem size_call_le (sD' nD' d q' : Data)
    (h : route (.cons sD' (.cons nD' d)) = (true, .cons (.cons sD' (.cons nD' q')) .nil)) :
    q'.size ≤ 2 * d.size + 9 := by
  have hq : ∀ w : Player, ((asPlayer w) (.cons sD' (.cons nD' d))).size ≤ 2 * d.size + 9 := by
    intro w
    have hw : (encode w : Data).size ≤ 3 := by cases w <;> decide
    have h1 := size_treeHead_le (treeTail d)
    have h2 := size_treeTail_le (treeTail (treeTail d))
    have h3 := size_treeTail_le (treeTail d)
    have h4 := size_treeTail_le d
    simp only [asPlayer, ap₂_apply, treePair_apply, comp_apply, const_apply, queryD, qD,
      treeTail_cons, Data.size_cons]
    omega
  simp only [route, PolyTimeFun.ite_apply, request, pair_apply, const_apply, ap₂_apply,
    treePair_apply, sD, nD, comp_apply, treeHead_cons, treeTail_cons, treeEq_apply] at h
  by_cases h1 : qD (.cons sD' (.cons nD' d)) = .nil
  · simp only [h1, decide_true, if_true] at h
    have := (Data.cons.inj (Data.cons.inj (Data.cons.inj (Prod.mk.inj h).2).1).2).2
    rw [← this]
    have h9 : (encode Sampler.Query.dimension : Data).size = 9 := rfl
    rw [h9]
    omega
  · simp only [h1, decide_false, Bool.false_eq_true, if_false] at h
    by_cases h2 : tagD (.cons sD' (.cons nD' d)) = encode Role.alice
    · simp only [h2, decide_true, if_true] at h
      have := (Data.cons.inj (Data.cons.inj (Data.cons.inj (Prod.mk.inj h).2).1).2).2
      rw [← this]
      exact hq .alice
    · simp only [h2, decide_false, Bool.false_eq_true, if_false] at h
      by_cases h3 : tagD (.cons sD' (.cons nD' d)) = encode Role.bob
      · simp only [h3, decide_true, if_true] at h
        have := (Data.cons.inj (Data.cons.inj (Data.cons.inj (Prod.mk.inj h).2).1).2).2
        rw [← this]
        exact hq .bob
      · simp only [h3, decide_false, Bool.false_eq_true, if_false] at h
        exact absurd (Prod.mk.inj h).1 (by decide)

/-- The explicit cost of the core on an input of size `xs`, at the input sampler's coefficient
`B` and degree `k`, with `X` one more than the size of the typed query. -/
noncomputable def coreCost (xs B k X : ℕ) : ℕ :=
  let Rt := route.timeBound.eval xs
  let tU := selfUniversal.bound.eval (xs + Rt + B * X ^ (5 * k))
  5 * Rt + 2 * tU + post.timeBound.eval (tU + 2) + 25

variable {ℓ : ℕ} (S : Sampler (ℓ + 1))

/-- **The core halts within `coreCost`** on every input of the typed sampler, well formed or
not: the router, at most one call to the input sampler through the universal machine, and the
postprocessing. -/
theorem core_runs_within (n : ℕ) {B k : ℕ} (hS : S.TimeBoundAt n B k) (d : Data) :
    ∃ r t, t ≤ coreCost (Data.cons (encode S.prog) (.cons (encode n) d)).size B k (d.size + 1) ∧
      core.Runs (.cons (encode S.prog) (.cons (encode n) d)) r t := by
  set x : Data := .cons (encode S.prog) (.cons (encode n) d) with hx
  have hRt := route.esize_apply_le x
  have hd1 : 1 ≤ d.size := Data.size_pos d
  cases h : route x with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_direct_cost route selfUniversal.univ post x payload h
      refine ⟨payload, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_false, esize_data] at hRt ht
      simp only [coreCost]
      omega
    | true =>
      obtain ⟨q', rfl⟩ := route_call_shape _ _ _ _ h
      have hq := size_call_le _ _ _ _ h
      obtain ⟨r, tS, htS, hSr⟩ := hS q'
      obtain ⟨tU, htU, hU⟩ := selfUniversal.time_le S.prog _ r tS hSr
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_indirect_cost route selfUniversal.closed post x _
        .nil r tU h hU
      refine ⟨_, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_true, esize_data, Data.size_cons] at hRt ht
      have hr_le : r.size ≤ tU := hU.size_le
      -- the input sampler's time on the forwarded query, at degree `5k`
      have hX : 2 ≤ d.size + 1 := by omega
      have hpow : (q'.size + 1) ^ k ≤ (d.size + 1) ^ (5 * k) := by
        rw [pow_mul]
        refine Nat.pow_le_pow_left ?_ k
        have h16 : 16 ≤ (d.size + 1) ^ 4 := by
          calc 16 = 2 ^ 4 := rfl
            _ ≤ (d.size + 1) ^ 4 := Nat.pow_le_pow_left hX 4
        nlinarith
      have htS' : tS ≤ B * (d.size + 1) ^ (5 * k) := htS.trans (Nat.mul_le_mul_left B hpow)
      have hes : esize S.prog = (encode S.prog : Data).size := rfl
      have hsz : esize S.prog + (Data.cons (encode n) q').size + tS ≤
          x.size + route.timeBound.eval x.size + B * (d.size + 1) ^ (5 * k) := by
        simp only [Data.size_cons] at hRt ⊢
        omega
      have htU' := htU.trans (polynomial_eval_mono _ hsz)
      have hpost := polynomial_eval_mono post.timeBound
        (show Data.nil.size + r.size + 1 ≤ tU + 2 by simp only [Data.size_nil]; omega)
      have hpost2 := polynomial_eval_mono post.timeBound (show tU + 2 ≤
        selfUniversal.bound.eval (x.size + route.timeBound.eval x.size +
          B * (d.size + 1) ^ (5 * k)) + 2 by omega)
      simp only [coreCost]
      omega

/-- **The running time of the typed oracularized sampler**: constants `c, m, e` uniform in
everything such that, whenever `W` dominates the input sampler's coefficient, its description
length and the index, and the input sampler runs within `B (|d| + 1)^k` at `n`, the typed
sampler runs within `c (W + 1)^m (|d| + 1)^{e (k + 1)}`. A forwarded query is at most a constant
factor larger than the typed query, and since `|d| + 1 ≥ 2` that factor is absorbed into the
degree, so no term exponential in `k` enters the coefficient. -/
theorem oracleSampler_timeBound : ∃ c m e, ∀ {ℓ : ℕ} (S : Sampler (ℓ + 1)) (n B k W : ℕ),
    B ≤ W → esize S.prog ≤ W → n ≤ W → S.TimeBoundAt n B k →
    (oracleSampler S).TimeBoundAt n (c * (W + 1) ^ m) (e * (k + 1)) := by
  -- the three polynomials, at dominated arguments
  have dom_poly : ∀ (Q : Polynomial ℕ) (cy my ey : ℕ), ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X →
      1 ≤ y → Dom W X K cy my ey y → Dom W X K c m e (Q.eval y) := fun Q cy my ey =>
    ⟨_, _, _, fun W X K {y} _ hy h =>
      ((Dom.const _).mul (h.pow Q.natDegree)).of_le (polynomial_eval_le_sum_coeff_mul_pow Q hy)⟩
  -- the size of the core's input
  have dom_xs : ∃ c m e, ∀ (W X K : ℕ) {p n D : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → D + 1 = X →
      Dom W X K c m e (p + esize n + D + 2) := ⟨_, _, _, fun W X K {p n D} hX hp hn hD => by
    subst hD
    exact (((Dom.ofLeW hp).add hX (dom_esize hn)).add hX (Dom.ofLeX hX (by omega))).add hX
      (Dom.const 2)⟩
  obtain ⟨cx, mx, ex, hxs⟩ := dom_xs
  obtain ⟨cR, mR, eR, hR⟩ := dom_poly route.timeBound cx mx ex
  -- the argument of the universal machine's bound
  have dom_uarg : ∃ c m e, ∀ (W X K : ℕ) {xs B : ℕ}, 1 ≤ X → 1 ≤ xs → B ≤ W →
      Dom W X K cx mx ex xs → Dom W X K c m e (xs + route.timeBound.eval xs + B * X ^ (5 * K)) :=
    ⟨_, _, _, fun W X K {xs B} hX hxs1 hB h => by
      have hp : Dom W X K 1 0 5 (X ^ (5 * K)) := by
        have := (Dom.powK (W := W) (K := K) hX).pow 5
        simpa [pow_mul, mul_comm] using this
      exact (h.add hX (hR W X K hX hxs1 h)).add hX ((Dom.ofLeW hB).mul hp)⟩
  obtain ⟨cA, mA, eA, hA⟩ := dom_uarg
  obtain ⟨cU', mU', eU', hU⟩ := dom_poly selfUniversal.bound cA mA eA
  have dom_tU2 : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X → Dom W X K cU' mU' eU' y →
      Dom W X K c m e (y + 2) := ⟨_, _, _, fun W X K {y} hX h => h.add hX (Dom.const 2)⟩
  obtain ⟨c2, m2, e2, h2⟩ := dom_tU2
  obtain ⟨cP, mP, eP, hP⟩ := dom_poly post.timeBound c2 m2 e2
  exact ⟨_, _, _, fun {ℓ} S n B k W hB hsp hn hS d => by
    obtain ⟨r, t, ht, run⟩ := core_runs_within S n hS d
    refine ⟨r, _, ?_, hardcode_time core_closed run⟩
    have hX : 1 ≤ d.size + 1 := by omega
    have hxsz : (Data.cons (encode S.prog) (.cons (encode n) d)).size =
        esize S.prog + esize n + d.size + 2 := by
      simp only [Data.size_cons, esize]
      omega
    have hx := hxs W (d.size + 1) k hX hsp hn rfl
    rw [← hxsz] at hx
    have hx1 : 1 ≤ (Data.cons (encode S.prog) (.cons (encode n) d)).size := Data.size_pos _
    have hRt := hR W (d.size + 1) k hX hx1 hx
    have hua := hA W (d.size + 1) k hX hx1 hB hx
    have hu := hU W (d.size + 1) k hX (by omega) hua
    have hp := hP W (d.size + 1) k hX (by omega) (h2 W (d.size + 1) k hX hu)
    have hcore : Dom W (d.size + 1) k _ _ _
        (coreCost (Data.cons (encode S.prog) (.cons (encode n) d)).size B k (d.size + 1)) :=
      ((((Dom.const 5).mul hRt).add hX ((Dom.const 2).mul hu)).add hX hp).add hX (Dom.const 25)
    have hsz1 : (encode S.prog : Data).size ≤ W := hsp
    have hin : (Data.cons (encode n) d).size = esize n + d.size + 1 := by
      simp only [Data.size_cons, esize]
    have htot := (((hcore.add hX (Dom.ofLeW hsz1)).add hX
      (((dom_esize hn).add hX (Dom.ofLeX hX (le_refl _))).add hX (Dom.const 1))).add hX
      (Dom.const 3))
    refine le_trans ?_ htot.le
    rw [hin]
    omega⟩

/-- **The program is a polynomial-time function of the input sampler's program**: the s-m-n map
at the fixed core. -/
noncomputable def samplerProgFun : PolyTimeFun Prog Prog :=
  (PolyTimeFun.smn Prog).comp ((PolyTimeFun.const core).pair (PolyTimeFun.id Prog))

theorem samplerProgFun_apply (sp : Prog) : samplerProgFun sp = prog sp := rfl

end OracleSampler

end MIPRE
