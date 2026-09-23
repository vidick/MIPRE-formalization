/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularSampler
import MIPRE.Foundations.CL.DetypingClock
import MIPRE.Foundations.CL.DetypingDeciderGame
import MIPRE.Foundations.Halting.Serial
import MIPRE.Foundations.Cost.Kleene

/-!
# The typed oracularized decider

Piece O4 of `planning/oracularization.md` (issue #189): the decider of the paper's typed
oracularized verifier (`sec:orac-def`, `fig:oracle-decider`) as a total `CL.TypedDecider` over the
three roles, whose acceptance law is O2's bit-string predicate `oraclePred`.

The paper runs the input decider in its *timeout-counter form*, which halts within a bound
`B_𝒟(n)` read off its description, and parses answers against that bound. The ambient model has
no such form, and the detyping compiler needs a total typed decider, so the timeout is made
explicit: an *index routine* (`OracleDecider.Index`) supplies at index `n` a parse cut `B n` and a
simulation budget `K n`, and the decider runs an unclocked core under the clocked universal
machine for `K n` steps. Three programs, each fixed, with the input programs as data:

* `gameProg j`, the **game check**: on `(S̄, D̄, n, z, a₁, a₂)`, ask the input sampler for the
  marginals `L^𝖠_{≤ j} z` and `L^𝖡_{≤ j} z` and run the input decider on
  `(n, L^𝖠 z, L^𝖡 z, a₁, a₂)`, all through the universal machine;
* `core j`, on `((S̄, D̄, B), (n, t, x, u, y, a, b))`: parse each answer by its role against `B`,
  run the game check for each oracle, and accept iff every check of `fig:oracle-decider` passes;
* `shell j`, on `((S̄, D̄, Ī), input)`: ask the index routine `Ī` for `(K n, B n)` and run the core
  on `((S̄, D̄, B n), input)` under the clocked universal machine with budget `K n`.

The decider is `hardcode (shell j) (encode (S̄, D̄, Ī))`, so its program is the s-m-n function of
the three programs. It halts on every input, whatever the input programs do
(`oracleDecider_total`), and it accepts exactly when the core accepts within the budget
(`oracleDecider_accepts_iff`). The core's acceptance law is `oraclePred` exactly, with no
hypothesis on the input verifier (`core_accepts_iff`): the input decider need not halt on the
inputs it rejects, which is why both directions go through inversion lemmas of the programs.
So the decider's acceptance implies `oraclePred` unconditionally (`accepts_sound`), and
`oraclePred` implies acceptance once the core's run fits in the budget (`accepts_complete`) —
the role the timeout bound plays in the paper's completeness.
-/

namespace MIPRE

open Cost Cost.PolyTimeFun

/-! ## Inverting the routing combinators -/

namespace Cost.Prog

/-- Sequencing two closed programs. -/
theorem let_closed_runs {p q : Prog} (hq : q.WellScoped 1) {x v r : Data} {s t : ℕ}
    (hp : p.Runs x v s) (hq' : q.Runs v r t) : (Prog.let_ p q).Runs x r (s + t + 1) :=
  Eval.let_ hp (Eval.append_of_wellScoped hq' hq [x])

/-- Inverting the sequence of two closed programs. -/
theorem let_closed_inv {p q : Prog} (hq : q.WellScoped 1) {x r : Data} {t : ℕ}
    (h : (Prog.let_ p q).Runs x r t) : ∃ v s t', p.Runs x v s ∧ q.Runs v r t' := by
  change Eval [x] (.let_ p q) r t at h
  cases h with
  | let_ h₁ h₂ =>
    exact ⟨_, _, _, h₁, Eval.of_append_of_wellScoped (env := [_]) (extra := [x]) h₂ hq⟩

/-- Inverting `callWithContext`: a run is a run of the callee on the argument, followed by the
postprocessor. -/
theorem callWithContext_inv {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) {a ctx r : Data} {t : ℕ}
    (h : (callWithContext p post).Runs (.cons a ctx) r t) :
    ∃ r' t', p.Runs a r' t' ∧ r = post (ctx, r') := by
  change Eval [Data.cons a ctx] (.let_ fstProg (.let_ p
    (.let_ (.cons (callVar 2 sndProg) (.var 0)) post.code))) r t at h
  cases h with
  | let_ h₁ h₂ =>
    rw [(Eval.deterministic h₁ (fstProg_runs a ctx)).1] at h₂
    cases h₂ with
    | let_ h₃ h₄ =>
      have h₃' : p.Runs a _ _ :=
        Eval.of_append_of_wellScoped (env := [a]) (extra := [Data.cons a ctx]) h₃ hp
      refine ⟨_, _, h₃', ?_⟩
      cases h₄ with
      | let_ h₅ h₆ =>
        cases h₅ with
        | cons h₇ h₈ =>
          obtain ⟨t₇, -, h₇'⟩ := callVar_runs_rev sndProg_wellScoped h₇
          have hc := (Eval.deterministic h₇' (sndProg_runs a ctx)).1
          cases h₈
          rw [hc] at h₆
          have h₆' := Eval.of_append_of_wellScoped (env := [_]) (extra := _) h₆ post.closed
          obtain ⟨tp, -, hpost⟩ := post.computes (ctx, _)
          exact (Eval.deterministic h₆' hpost).1

/-- Inverting a routed call: when the router calls, a run is a run of the callee on the
argument, followed by the postprocessor. -/
theorem routeOneCall_indirect_inv (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    {x a ctx r : Data} {t : ℕ} (hroute : route x = (true, .cons a ctx))
    (h : (routeOneCall route p post).Runs x r t) :
    ∃ r' t', p.Runs a r' t' ∧ r = post (ctx, r') := by
  obtain ⟨tr, -, hr⟩ := route.computes x
  rw [hroute] at hr
  change Eval [x] (.let_ route.code (.elim 0 .nil (.elim 0 (.var 1)
    (callVar 3 (callWithContext p post))))) r t at h
  cases h with
  | let_ h₁ h₂ =>
    have hv := (Eval.deterministic h₁ hr).1
    subst hv
    cases h₂ with
    | elim_nil hn _ => simp [encode, Data.ofBool] at hn
    | elim_cons hc h₃ =>
      simp only [Env.get, encode_prod] at hc
      obtain ⟨rfl, rfl⟩ := Data.cons.inj hc
      cases h₃ with
      | elim_nil hn _ => simp [encode, Data.ofBool] at hn
      | elim_cons hc' h₄ =>
        obtain ⟨t₄, -, h₄'⟩ := callVar_runs_rev (callWithContext_closed hp post) h₄
        simp only [Env.get] at h₄'
        exact callWithContext_inv hp post h₄'

/-- Inverting a routed call when the router answers directly. -/
theorem routeOneCall_direct_inv (route : PolyTimeFun Data (Bool × Data))
    (p : Prog) (post : PolyTimeFun (Data × Data) Data) {x r₀ r : Data} {t : ℕ}
    (hroute : route x = (false, r₀)) (h : (routeOneCall route p post).Runs x r t) : r = r₀ := by
  obtain ⟨t₀, h₀⟩ := routeOneCall_direct route p post x r₀ hroute
  exact (Eval.deterministic h h₀).1

end Cost.Prog

namespace OracleDecider

open CL CL.Detyping.Program

/-! ## The game check -/

/-- The input sampler's program, first field of a game check's input. -/
noncomputable def gS : PolyTimeFun Data Data := treeHead
/-- The input decider's program. -/
noncomputable def gD : PolyTimeFun Data Data := treeHead.comp treeTail
/-- The index. -/
noncomputable def gN : PolyTimeFun Data Data := treeHead.comp (treeTail.comp treeTail)
/-- The seed. -/
noncomputable def gZ : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp treeTail))
/-- The pair of answers. -/
noncomputable def gA : PolyTimeFun Data Data :=
  treeTail.comp (treeTail.comp (treeTail.comp treeTail))

/-- The marginal query `(n, w, marginal, j, z)` at the game check's seed. -/
noncomputable def margQuery (w : Player) (j : ℕ) : PolyTimeFun Data Data :=
  ap₂ treePair gN (ap₂ treePair (const (encode (1 : ℕ))) (ap₂ treePair (const (encode w))
    (ap₂ treePair (const (encode j)) (ap₂ treePair gZ (const (encode ([] : BitStr)))))))

/-- First call: Alice's marginal. -/
noncomputable def gRoute₁ (j : ℕ) : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (ap₂ treePair gS (margQuery .alice j)) (PolyTimeFun.id Data))

/-- Second call: Bob's marginal. -/
noncomputable def gRoute₂ (j : ℕ) : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair
    (ap₂ treePair (gS.comp treeHead) ((margQuery .bob j).comp treeHead)) (PolyTimeFun.id Data))

/-- Third call: the input decider on the two questions and the two answers. -/
noncomputable def gRoute₃ : PolyTimeFun Data (Bool × Data) :=
  let g := treeHead.comp treeHead
  (const true).pair (ap₂ treePair (ap₂ treePair (gD.comp g) (ap₂ treePair (gN.comp g)
    (ap₂ treePair (treeTail.comp treeHead) (ap₂ treePair treeTail (gA.comp g)))))
    (const Data.nil))

/-- The three stages of the game check. -/
noncomputable def gStage₁ (j : ℕ) : Prog :=
  Prog.routeOneCall (gRoute₁ j) selfUniversal.univ treePair
noncomputable def gStage₂ (j : ℕ) : Prog :=
  Prog.routeOneCall (gRoute₂ j) selfUniversal.univ treePair
noncomputable def gStage₃ : Prog :=
  Prog.routeOneCall gRoute₃ selfUniversal.univ CL.Detyping.DeciderProgram.post

/-- **The game check** at level `j`. -/
noncomputable def gameProg (j : ℕ) : Prog := .let_ (gStage₁ j) (.let_ (gStage₂ j) gStage₃)

theorem gStage₁_closed (j : ℕ) : (gStage₁ j).WellScoped 1 :=
  Prog.routeOneCall_closed _ selfUniversal.closed _
theorem gStage₂_closed (j : ℕ) : (gStage₂ j).WellScoped 1 :=
  Prog.routeOneCall_closed _ selfUniversal.closed _
theorem gStage₃_closed : gStage₃.WellScoped 1 :=
  Prog.routeOneCall_closed _ selfUniversal.closed _

theorem gTail_closed (j : ℕ) : (Prog.let_ (gStage₂ j) gStage₃).WellScoped 1 :=
  ⟨gStage₂_closed j, gStage₃_closed.mono (by omega) _⟩

theorem gameProg_closed (j : ℕ) : (gameProg j).WellScoped 1 :=
  ⟨gStage₁_closed j, (gTail_closed j).mono (by omega) _⟩

/-- The input of a game check. -/
def gInput (sp dp : Prog) (n : ℕ) (z a₁ a₂ : BitStr) : Data :=
  .cons (encode sp) (.cons (encode dp) (encode (n, z, a₁, a₂)))

theorem gRoute₁_apply (j : ℕ) (sp dp : Prog) (n : ℕ) (z a₁ a₂ : BitStr) :
    gRoute₁ j (gInput sp dp n z a₁ a₂) = (true, .cons (.cons (encode sp)
      (encode (n, Sampler.Query.marginal .alice j z))) (gInput sp dp n z a₁ a₂)) := by
  simp [gRoute₁, margQuery, gS, gN, gZ, gInput, encode_prod]
  rfl

theorem gRoute₂_apply (j : ℕ) (sp dp : Prog) (n : ℕ) (z a₁ a₂ : BitStr) (rA : Data) :
    gRoute₂ j (.cons (gInput sp dp n z a₁ a₂) rA) = (true, .cons (.cons (encode sp)
      (encode (n, Sampler.Query.marginal .bob j z))) (.cons (gInput sp dp n z a₁ a₂) rA)) := by
  simp [gRoute₂, margQuery, gS, gN, gZ, gInput, encode_prod]
  rfl

theorem gRoute₃_apply (sp dp : Prog) (n : ℕ) (z a₁ a₂ : BitStr) (rA rB : Data) :
    gRoute₃ (.cons (.cons (gInput sp dp n z a₁ a₂) rA) rB) = (true, .cons (.cons (encode dp)
      (.cons (encode n) (.cons rA (.cons rB (encode (a₁, a₂)))))) .nil) := by
  simp [gRoute₃, gD, gN, gA, gInput, encode_prod]

variable {ℓ : ℕ} (S : Sampler ℓ)

/-- The question the game check computes for player `w` from the seed `z`. -/
noncomputable def margBits (n j : ℕ) (w : Player) (z : BitStr) : BitStr :=
  toBits (((S.cl n w).truncate j).eval (ofBits (S.dim n) z))

/-- The input decider's input in a game check. -/
noncomputable def gameArg (n j : ℕ) (z a₁ a₂ : BitStr) : Data :=
  encode (n, margBits S n j .alice z, margBits S n j .bob z, a₁, a₂)

/-- The two marginal calls, through the universal machine. -/
theorem univ_marginal (n j : ℕ) (hj₁ : 1 ≤ j) (hj : j ≤ ℓ) (w : Player) (z : BitStr)
    (hz : z.length = S.dim n) :
    ∃ t, selfUniversal.univ.Runs (.cons (encode S.prog)
      (encode (n, Sampler.Query.marginal w j z))) (encode (margBits S n j w z)) t := by
  obtain ⟨t, ht⟩ := S.runs_marginal n w j z hj₁ hj hz
  obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ ht
  exact ⟨t', h'⟩

/-- **The game check runs** the input decider on the two questions and the two answers, and
returns whether it accepted. -/
theorem gameProg_runs (dp : Prog) (n j : ℕ) (hj₁ : 1 ≤ j) (hj : j ≤ ℓ) (z a₁ a₂ : BitStr)
    (hz : z.length = S.dim n) {rD : Data} {tD : ℕ} (hD : dp.Runs (gameArg S n j z a₁ a₂) rD tD) :
    ∃ t, (gameProg j).Runs (gInput S.prog dp n z a₁ a₂) (encode (decide (rD = encode true))) t := by
  obtain ⟨tA, hA⟩ := univ_marginal S n j hj₁ hj .alice z hz
  obtain ⟨tB, hB⟩ := univ_marginal S n j hj₁ hj .bob z hz
  obtain ⟨tD', -, hD'⟩ := selfUniversal.time_le _ _ _ _ hD
  obtain ⟨t₁, h₁⟩ := Prog.routeOneCall_indirect (gRoute₁ j) selfUniversal.closed treePair _ _ _ _
    tA (gRoute₁_apply j S.prog dp n z a₁ a₂) hA
  obtain ⟨t₂, h₂⟩ := Prog.routeOneCall_indirect (gRoute₂ j) selfUniversal.closed treePair _ _ _ _
    tB (gRoute₂_apply j S.prog dp n z a₁ a₂ _) hB
  obtain ⟨t₃, h₃⟩ := Prog.routeOneCall_indirect gRoute₃ selfUniversal.closed
    CL.Detyping.DeciderProgram.post _ _ _ _ tD' (gRoute₃_apply S.prog dp n z a₁ a₂ _ _)
    (by simpa [gameArg, encode_prod] using hD')
  exact ⟨_, Prog.let_closed_runs (gTail_closed j) h₁ (Prog.let_closed_runs gStage₃_closed h₂ h₃)⟩

/-- The sampler's run on a marginal query, read back through the universal machine. -/
theorem univ_marginal_inv (n j : ℕ) (hj₁ : 1 ≤ j) (hj : j ≤ ℓ) (w : Player) (z : BitStr)
    (hz : z.length = S.dim n) {r : Data} {t : ℕ}
    (h : selfUniversal.univ.Runs (.cons (encode S.prog)
      (encode (n, Sampler.Query.marginal w j z))) r t) : r = encode (margBits S n j w z) := by
  obtain ⟨t', h'⟩ := selfUniversal.halts_of _ _ _ _ h
  obtain ⟨t'', h''⟩ := S.runs_marginal n w j z hj₁ hj hz
  exact (Eval.deterministic h' h'').1

/-- **Inverting the game check**: every run of it is a run of the input decider on the two
questions and the two answers, whose verdict it returns. -/
theorem gameProg_inv (dp : Prog) (n j : ℕ) (hj₁ : 1 ≤ j) (hj : j ≤ ℓ) (z a₁ a₂ : BitStr)
    (hz : z.length = S.dim n) {r : Data} {t : ℕ}
    (h : (gameProg j).Runs (gInput S.prog dp n z a₁ a₂) r t) :
    ∃ rD tD, dp.Runs (gameArg S n j z a₁ a₂) rD tD ∧ r = encode (decide (rD = encode true)) := by
  obtain ⟨v₁, s₁, t₁, h₁, hrest⟩ := Prog.let_closed_inv (gTail_closed j) h
  obtain ⟨v₂, s₂, t₂, h₂, h₃⟩ := Prog.let_closed_inv gStage₃_closed hrest
  obtain ⟨rA, tA, hA, rfl⟩ := Prog.routeOneCall_indirect_inv (gRoute₁ j) selfUniversal.closed
    treePair (gRoute₁_apply j S.prog dp n z a₁ a₂) h₁
  have eA := univ_marginal_inv S n j hj₁ hj .alice z hz hA
  subst eA
  obtain ⟨rB, tB, hB, rfl⟩ := Prog.routeOneCall_indirect_inv (gRoute₂ j) selfUniversal.closed
    treePair (gRoute₂_apply j S.prog dp n z a₁ a₂ _) h₂
  have eB := univ_marginal_inv S n j hj₁ hj .bob z hz hB
  subst eB
  obtain ⟨rD, tD, hD, rfl⟩ := Prog.routeOneCall_indirect_inv gRoute₃ selfUniversal.closed
    CL.Detyping.DeciderProgram.post (gRoute₃_apply S.prog dp n z a₁ a₂ _ _) h₃
  obtain ⟨tD', hD'⟩ := selfUniversal.halts_of _ _ _ _ hD
  exact ⟨rD, tD', by simpa [gameArg, encode_prod] using hD', rfl⟩

/-- **The game check accepts exactly when the input decider does** on the two questions and the
two answers. -/
theorem gameProg_accepts_iff (dp : Prog) (n j : ℕ) (hj₁ : 1 ≤ j) (hj : j ≤ ℓ)
    (z a₁ a₂ : BitStr) (hz : z.length = S.dim n) :
    (∃ t, (gameProg j).Runs (gInput S.prog dp n z a₁ a₂) (encode true) t) ↔
      ∃ tD, dp.Runs (gameArg S n j z a₁ a₂) (encode true) tD := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨rD, tD, hD, he⟩ := gameProg_inv S dp n j hj₁ hj z a₁ a₂ hz ht
    have hb := encode_injective he
    exact ⟨tD, of_decide_eq_true hb.symm ▸ hD⟩
  · rintro ⟨tD, hD⟩
    obtain ⟨t, ht⟩ := gameProg_runs S dp n j hj₁ hj z a₁ a₂ hz hD
    exact ⟨t, by simpa using ht⟩

/-! ## Parsing an answer by its role -/

theorem toBool?_eq_some {d : Data} {b : Bool} : Data.toBool? d = some b ↔ d = Data.ofBool b := by
  rcases d with _ | ⟨_ | ⟨x, y⟩, _ | ⟨z, w⟩⟩ <;> cases b <;> simp [Data.toBool?, Data.ofBool]

/-- A datum decodes to a bit string exactly when it is its encoding. -/
theorem decode_bitStr_eq_some {d : Data} {x : BitStr} :
    (decode d : Option BitStr) = some x ↔ d = encode x := by
  constructor
  · change Data.toList? Data.toBool? d = some x → d = Data.ofList Data.ofBool x
    induction d generalizing x with
    | nil =>
      intro h
      simp only [Data.toList?, Option.some.injEq] at h
      subst h
      rfl
    | cons h tl _ ihtl =>
      intro hx
      simp only [Data.toList?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hx
      obtain ⟨b, hb, l, hl, rfl⟩ := hx
      rw [toBool?_eq_some.mp hb, ihtl hl]
      rfl
  · rintro rfl
    exact SizedEncoding.decode_encode x

theorem toList?_toBool?_eq_some {d : Data} {x : BitStr} :
    Data.toList? Data.toBool? d = some x ↔ d = encode x :=
  decode_bitStr_eq_some

/-- An oracle's answer parses to a pair exactly when its postorder parse is the encoding of that
pair. -/
theorem pairDec_eq_some (s a₁ a₂ : BitStr) :
    pairDec s = some (a₁, a₂) ↔ Data.parse s = .cons (encode a₁) (encode a₂) := by
  constructor
  · intro h
    unfold pairDec at h
    generalize Data.parse s = d at h ⊢
    rcases d with _ | ⟨p, q⟩
    · simp [decode] at h
    · simp only [decode] at h
      rcases hp : Data.toList? Data.toBool? p with _ | x <;>
        rcases hq : Data.toList? Data.toBool? q with _ | y <;>
        simp only [hp, hq, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [toList?_toBool?_eq_some.mp hp, toList?_toBool?_eq_some.mp hq]
  · intro h
    rw [pairDec, h]
    exact SizedEncoding.decode_encode (a₁, a₂)

theorem parseAns_oracle (B : ℕ) (s : BitStr) :
    parseAns B .oracle s = (match pairDec s with
      | some (a, b) =>
        if h : a.length ≤ B ∧ b.length ≤ B then some (.pair ⟨a, h.1⟩ ⟨b, h.2⟩) else none
      | none => none) := rfl

theorem parseAns_alice (B : ℕ) (s : BitStr) :
    parseAns B .alice s = if h : s.length ≤ B then some (.single ⟨s, h⟩) else none := rfl

theorem parseAns_bob (B : ℕ) (s : BitStr) :
    parseAns B .bob s = if h : s.length ≤ B then some (.single ⟨s, h⟩) else none := rfl

/-- Postorder parsing, as a polynomial-time function (`Prog.parseProg`). -/
noncomputable def parseF : PolyTimeFun BitStr Data where
  toFun := Data.parse
  code := Prog.parseProg
  closed := Prog.parseProg_wellScoped
  timeBound := (Polynomial.X + Polynomial.C 2) * (Polynomial.C 3 * Polynomial.X + Polynomial.C 25)
  computes x := by
    obtain ⟨t, ht, hr⟩ := Prog.parseProg_runs x
    refine ⟨t, ?_, by simpa using hr⟩
    have hL := length_le_esize_bitStr x
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    refine ht.trans (Nat.mul_le_mul (by omega) ?_)
    have he : esize x = (encode x : Data).size := rfl
    omega

@[simp] theorem parseF_apply (x : BitStr) : parseF x = Data.parse x := rfl

/-- `a ∧ b` on Boolean-valued functions. -/
noncomputable def andB {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const false)

@[simp] theorem andB_apply {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andB f g x = (f x && g x) := by
  simp only [andB, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> rfl

/-- `¬ a ∨ b` on Boolean-valued functions. -/
noncomputable def impB {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const true)

@[simp] theorem impB_apply {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    impB f g x = (!f x || g x) := by
  simp only [impB, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp

/-- Equality of two raw trees. -/
noncomputable def eqD {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Data) :
    PolyTimeFun α Bool := ap₂ treeEq f g

@[simp] theorem eqD_apply {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Data) (x : α) :
    eqD f g x = decide (f x = g x) := by
  simp [eqD]

/-- Whether a role datum is the oracle's. -/
noncomputable def isOracle (r : PolyTimeFun Data Data) : PolyTimeFun Data Bool :=
  eqD r (const (encode Role.oracle))

/-- The postorder parse of an answer datum. -/
noncomputable def treeOf (s : PolyTimeFun Data Data) : PolyTimeFun Data Data :=
  parseF.comp (readBits.comp s)

/-- A bit string datum of length at most the cut. -/
noncomputable def lenOk (s : PolyTimeFun Data Data) (B : PolyTimeFun Data ℕ) :
    PolyTimeFun Data Bool :=
  ap₂ leNat (CL.Detyping.DeciderProgram.lengthNat.comp (readBits.comp s)) B

/-- **The bounded parse, as a check**: an oracle's answer must parse to the encoding of a pair of
strings of length at most the cut, an isolated player's must have length at most the cut. -/
noncomputable def okAns (r s : PolyTimeFun Data Data) (B : PolyTimeFun Data ℕ) :
    PolyTimeFun Data Bool :=
  let d := treeOf s
  ite (isOracle r)
    (andB (eqD d (ap₂ treePair (encoded.comp (readBits.comp (treeHead.comp d)))
      (encoded.comp (readBits.comp (treeTail.comp d)))))
      (andB (lenOk (treeHead.comp d) B) (lenOk (treeTail.comp d) B)))
    (lenOk s B)

/-- The parsed answer, as a datum: the parse tree of an oracle's answer, an isolated player's
answer as it is. -/
noncomputable def reprAns (r s : PolyTimeFun Data Data) : PolyTimeFun Data Data :=
  ite (isOracle r) (treeOf s) s

@[simp] theorem answers_mk_inj {B : ℕ} {a b : BitStr} (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (⟨a, ha⟩ : Verifier.Answers B) = ⟨b, hb⟩ ↔ a = b :=
  ⟨fun h => congrArg Subtype.val h, fun h => by subst h; rfl⟩

/-- The datum a parsed answer is represented by. -/
def ansData {B : ℕ} : OAns (Verifier.Answers B) → Data
  | .pair a b => .cons (encode a.1) (encode b.1)
  | .single a => encode a.1

/-- Two answers of the same shape are equal exactly when their data are. -/
theorem ansData_inj {B : ℕ} {r : Role} {U W : OAns (Verifier.Answers B)}
    (hU : SeededGame.shapeOk r U = true) (hW : SeededGame.shapeOk r W = true) :
    ansData U = ansData W ↔ U = W := by
  constructor
  · intro h
    rcases U with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨⟨a, ha⟩⟩ <;>
      rcases W with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ | ⟨⟨c, hc⟩⟩ <;>
      cases r <;> simp_all [SeededGame.shapeOk, ansData, encode_injective.eq_iff]
  · rintro rfl
    rfl

section ParseSpec

variable (r s : PolyTimeFun Data Data) (B : PolyTimeFun Data ℕ)

/-- **The parse check is the bounded parse**, and the parsed datum represents the parse. -/
theorem okAns_spec (c : Data) (role : Role) (str : BitStr) (hr : r c = encode role)
    (hs : s c = encode str) :
    (okAns r s B c = true ↔ (parseAns (B c) role str).isSome) ∧
      ∀ U, parseAns (B c) role str = some U → reprAns r s c = ansData U := by
  cases role with
  | oracle =>
    have hro : isOracle r c = true := by simp [isOracle, hr]
    simp only [okAns, reprAns, PolyTimeFun.ite_apply, hro, if_true, treeOf, comp_apply, hs,
      readBits_encode, parseF_apply, andB_apply, eqD_apply, ap₂_apply, treePair_apply,
      encoded_apply, lenOk, CL.Detyping.DeciderProgram.lengthNat_apply, leNat_apply,
      Bool.and_eq_true, decide_eq_true_eq, parseAns_oracle]
    cases hp : pairDec str with
    | none =>
      refine ⟨⟨fun ⟨hd, _, _⟩ => ?_, fun h => by simp at h⟩, fun U hU => by simp at hU⟩
      have := (pairDec_eq_some _ _ _).mpr hd
      rw [hp] at this
      cases this
    | some pr =>
      obtain ⟨a₁, a₂⟩ := pr
      have hd := (pairDec_eq_some _ _ _).mp hp
      simp only [hd, treeHead_cons, treeTail_cons, readBits_encode, true_and]
      refine ⟨?_, fun U hU => ?_⟩
      · by_cases hab : a₁.length ≤ B c ∧ a₂.length ≤ B c
        · simp [hab]
        · simp only [hab, dif_neg, not_false_eq_true, Option.isSome_none, Bool.false_eq_true]
      · split_ifs at hU with hab
        cases hU
        rfl
  | alice =>
    have hro : isOracle r c = false := by simp [isOracle, hr, encode_role_alice, encode_role_oracle]
    simp only [okAns, reprAns, PolyTimeFun.ite_apply, hro, Bool.false_eq_true, if_false, lenOk,
      comp_apply, ap₂_apply, hs, readBits_encode, CL.Detyping.DeciderProgram.lengthNat_apply,
      leNat_apply, decide_eq_true_eq, parseAns_alice]
    refine ⟨?_, fun U hU => ?_⟩
    · by_cases h : str.length ≤ B c <;> simp [h]
    · split_ifs at hU with h
      cases hU
      rfl
  | bob =>
    have hro : isOracle r c = false := by simp [isOracle, hr, encode_role_bob, encode_role_oracle]
    simp only [okAns, reprAns, PolyTimeFun.ite_apply, hro, Bool.false_eq_true, if_false, lenOk,
      comp_apply, ap₂_apply, hs, readBits_encode, CL.Detyping.DeciderProgram.lengthNat_apply,
      leNat_apply, decide_eq_true_eq, parseAns_bob]
    refine ⟨?_, fun U hU => ?_⟩
    · by_cases h : str.length ≤ B c <;> simp [h]
    · split_ifs at hU with h
      cases hU
      rfl

end ParseSpec

/-- The bounded parse returns answers of the role's shape. -/
theorem shapeOk_of_parseAns {B : ℕ} {r : Role} {s : BitStr} {U : OAns (Verifier.Answers B)}
    (h : parseAns B r s = some U) : SeededGame.shapeOk r U = true := by
  cases r with
  | oracle =>
    rw [parseAns_oracle] at h
    split at h
    · split_ifs at h
      cases h
      rfl
    · cases h
  | alice =>
    rw [parseAns_alice] at h
    split_ifs at h
    cases h
    rfl
  | bob =>
    rw [parseAns_bob] at h
    split_ifs at h
    cases h
    rfl

/-! ## The core -/

/-- The fields of the core's input `((S̄, D̄, B), (n, t, x, u, y, a, b))`. -/
noncomputable def cSp : PolyTimeFun Data Data := treeHead.comp treeHead
noncomputable def cDp : PolyTimeFun Data Data := treeHead.comp (treeTail.comp treeHead)
noncomputable def cB : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp (treeTail.comp treeHead))
noncomputable def cN : PolyTimeFun Data Data := treeHead.comp treeTail
noncomputable def cT : PolyTimeFun Data Data := treeHead.comp (treeTail.comp treeTail)
noncomputable def cX : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp treeTail))
noncomputable def cU : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))
noncomputable def cY : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail))))
noncomputable def cA : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp
    (treeTail.comp treeTail)))))
noncomputable def cBb : PolyTimeFun Data Data :=
  treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp
    (treeTail.comp treeTail)))))

/-- The core's input. -/
def cInput (sp dp : Prog) (B n : ℕ) (t : Role) (x : BitStr) (u : Role) (y a b : BitStr) : Data :=
  encode ((sp, dp, B), (n, t, x, u, y, a, b))

section Fields

variable (sp dp : Prog) (B n : ℕ) (t : Role) (x : BitStr) (u : Role) (y a b : BitStr)

@[simp] theorem cSp_cInput : cSp (cInput sp dp B n t x u y a b) = encode sp := by
  simp [cSp, cInput, encode_prod]
@[simp] theorem cDp_cInput : cDp (cInput sp dp B n t x u y a b) = encode dp := by
  simp [cDp, cInput, encode_prod]
@[simp] theorem cB_cInput : cB (cInput sp dp B n t x u y a b) = B := by
  simp [cB, cInput, encode_prod, readNat_encode]
@[simp] theorem cN_cInput : cN (cInput sp dp B n t x u y a b) = encode n := by
  simp [cN, cInput, encode_prod]
@[simp] theorem cT_cInput : cT (cInput sp dp B n t x u y a b) = encode t := by
  simp [cT, cInput, encode_prod]
@[simp] theorem cX_cInput : cX (cInput sp dp B n t x u y a b) = encode x := by
  simp [cX, cInput, encode_prod]
@[simp] theorem cU_cInput : cU (cInput sp dp B n t x u y a b) = encode u := by
  simp [cU, cInput, encode_prod]
@[simp] theorem cY_cInput : cY (cInput sp dp B n t x u y a b) = encode y := by
  simp [cY, cInput, encode_prod]
@[simp] theorem cA_cInput : cA (cInput sp dp B n t x u y a b) = encode a := by
  simp [cA, cInput, encode_prod]
@[simp] theorem cBb_cInput : cBb (cInput sp dp B n t x u y a b) = encode b := by
  simp [cBb, cInput, encode_prod]

end Fields

/-- The parse checks and the parsed answers of the two players. -/
noncomputable def okA : PolyTimeFun Data Bool := okAns cT cA cB
noncomputable def okB : PolyTimeFun Data Bool := okAns cU cBb cB
noncomputable def repA : PolyTimeFun Data Data := reprAns cT cA
noncomputable def repB : PolyTimeFun Data Data := reprAns cU cBb

/-- Check 2(a): equal roles force equal answers. -/
noncomputable def sameCheck : PolyTimeFun Data Bool := impB (eqD cT cU) (eqD repA repB)

/-- Check 2(b), for the role `r` against the role `r'`: an oracle's component for an isolated
player's role must be that player's answer. -/
noncomputable def ovpCheck (r r' rep rep' : PolyTimeFun Data Data) : PolyTimeFun Data Bool :=
  impB (isOracle r)
    (andB (impB (eqD r' (const (encode Role.alice))) (eqD (treeHead.comp rep) rep'))
      (impB (eqD r' (const (encode Role.bob))) (eqD (treeTail.comp rep) rep')))

/-- **The checks that need no call**: both parses, check 2(a) and check 2(b) both ways. -/
noncomputable def localCheck : PolyTimeFun Data Bool :=
  andB okA (andB okB (andB sameCheck (andB (ovpCheck cT cU repA repB)
    (ovpCheck cU cT repB repA))))

theorem ovpCheck_spec {B : ℕ} (r r' rep rep' : PolyTimeFun Data Data) (c : Data) (t u : Role)
    (U W : OAns (Verifier.Answers B)) (hU : SeededGame.shapeOk t U = true)
    (hW : SeededGame.shapeOk u W = true) (hr : r c = encode t) (hr' : r' c = encode u)
    (hrep : rep c = ansData U) (hrep' : rep' c = ansData W) {V : Type*} (z z' : V) :
    ovpCheck r r' rep rep' c = SeededGame.oracleVsPlayer (t, z) (u, z') U W := by
  rcases U with ⟨⟨a₁, h₁⟩, ⟨a₂, h₂⟩⟩ | ⟨⟨a, h⟩⟩ <;>
    rcases W with ⟨⟨b₁, g₁⟩, ⟨b₂, g₂⟩⟩ | ⟨⟨b, g⟩⟩ <;>
    cases t <;> cases u <;>
    simp_all [ovpCheck, isOracle, SeededGame.oracleVsPlayer, SeededGame.shapeOk, ansData,
      encode_role_oracle, encode_role_alice, encode_role_bob, encode_injective.eq_iff] <;>
    exact ⟨fun h => by subst h; rfl, fun h => congrArg Subtype.val h⟩

theorem sameCheck_spec {B : ℕ} (c : Data) (t u : Role) (U W : OAns (Verifier.Answers B))
    (hU : SeededGame.shapeOk t U = true) (hW : SeededGame.shapeOk u W = true)
    (ht : cT c = encode t) (hu : cU c = encode u) (hrA : repA c = ansData U)
    (hrB : repB c = ansData W) :
    sameCheck c = (if t = u then decide (U = W) else true) := by
  simp only [sameCheck, impB_apply, eqD_apply, ht, hu, hrA, hrB, encode_injective.eq_iff]
  by_cases htu : t = u
  · subst htu
    simp [ansData_inj hU hW]
  · simp [htu]

/-- **The local checks are the checks of `oaccepts` that need no call.** -/
theorem localCheck_spec (sp dp : Prog) (B n : ℕ) (t : Role) (x : BitStr) (u : Role)
    (y a b : BitStr) {V : Type*} (z z' : V) :
    localCheck (cInput sp dp B n t x u y a b) = true ↔
      ∃ U W, parseAns B t a = some U ∧ parseAns B u b = some W ∧
        (if t = u then decide (U = W) else true) = true ∧
        SeededGame.oracleVsPlayer (t, z) (u, z') U W = true ∧
        SeededGame.oracleVsPlayer (u, z') (t, z) W U = true := by
  set c := cInput sp dp B n t x u y a b
  have hA := okAns_spec cT cA cB c t a (cT_cInput ..) (cA_cInput ..)
  have hB := okAns_spec cU cBb cB c u b (cU_cInput ..) (cBb_cInput ..)
  rw [show cB c = B from cB_cInput ..] at hA hB
  constructor
  · intro h
    simp only [localCheck, andB_apply, Bool.and_eq_true] at h
    obtain ⟨hokA, hokB, hsame, hov, hov'⟩ := h
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (hA.1.mp hokA)
    obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp (hB.1.mp hokB)
    have hsU := shapeOk_of_parseAns hU
    have hsW := shapeOk_of_parseAns hW
    refine ⟨U, W, hU, hW, ?_, ?_, ?_⟩
    · rw [← sameCheck_spec c t u U W hsU hsW (cT_cInput ..) (cU_cInput ..) (hA.2 U hU)
        (hB.2 W hW)]
      exact hsame
    · rw [← ovpCheck_spec cT cU repA repB c t u U W hsU hsW (cT_cInput ..) (cU_cInput ..)
        (hA.2 U hU) (hB.2 W hW)]
      exact hov
    · rw [← ovpCheck_spec cU cT repB repA c u t W U hsW hsU (cU_cInput ..) (cT_cInput ..)
        (hB.2 W hW) (hA.2 U hU)]
      exact hov'
  · rintro ⟨U, W, hU, hW, hsame, hov, hov'⟩
    have hsU := shapeOk_of_parseAns hU
    have hsW := shapeOk_of_parseAns hW
    simp only [localCheck, andB_apply, Bool.and_eq_true]
    refine ⟨hA.1.mpr (by simp [hU]), hB.1.mpr (by simp [hW]), ?_, ?_, ?_⟩
    · rw [sameCheck_spec c t u U W hsU hsW (cT_cInput ..) (cU_cInput ..) (hA.2 U hU) (hB.2 W hW)]
      exact hsame
    · rw [ovpCheck_spec cT cU repA repB c t u U W hsU hsW (cT_cInput ..) (cU_cInput ..)
        (hA.2 U hU) (hB.2 W hW) z z']
      exact hov
    · rw [ovpCheck_spec cU cT repB repA c u t W U hsW hsU (cU_cInput ..) (cT_cInput ..)
        (hB.2 W hW) (hA.2 U hU) z' z]
      exact hov'

/-! ### The game checks and the verdict -/

/-- The game check's input for the answer datum `rep` at the seed `z`. -/
noncomputable def gArg (z rep : PolyTimeFun Data Data) : PolyTimeFun Data Data :=
  ap₂ treePair cSp (ap₂ treePair cDp (ap₂ treePair cN (ap₂ treePair z rep)))

/-- Route a game check: when `cond` holds of the core's input (read through `view`), call the game
check on `arg`; otherwise pass `true` on. The whole state is the context either way. -/
noncomputable def gameRoute (cond : PolyTimeFun Data Bool) (arg view : PolyTimeFun Data Data) :
    PolyTimeFun Data (Bool × Data) :=
  ite (cond.comp view) ((const true).pair (ap₂ treePair (arg.comp view) (PolyTimeFun.id Data)))
    ((const false).pair (ap₂ treePair (PolyTimeFun.id Data) (const (encode true))))

/-- The game check of each player runs when that player is an oracle whose answer parsed. -/
noncomputable def cond₁ : PolyTimeFun Data Bool := andB (isOracle cT) okA
noncomputable def cond₂ : PolyTimeFun Data Bool := andB (isOracle cU) okB
noncomputable def arg₁ : PolyTimeFun Data Data := gArg cX repA
noncomputable def arg₂ : PolyTimeFun Data Data := gArg cY repB

/-- A routed game check. -/
noncomputable def gameStage (j : ℕ) (cond : PolyTimeFun Data Bool)
    (arg view : PolyTimeFun Data Data) : Prog :=
  Prog.routeOneCall (gameRoute cond arg view) (gameProg j) treePair

theorem gameStage_closed (j : ℕ) (cond : PolyTimeFun Data Bool) (arg view : PolyTimeFun Data Data) :
    (gameStage j cond arg view).WellScoped 1 :=
  Prog.routeOneCall_closed _ (gameProg_closed j) _

/-- The verdict: the local checks passed and both game checks returned `true`. -/
noncomputable def verdict : PolyTimeFun Data Bool :=
  andB (localCheck.comp (treeHead.comp treeHead))
    (andB (eqD (treeTail.comp treeHead) (const (encode true))) (eqD treeTail (const (encode true))))

/-- The second game check and the verdict. -/
noncomputable def coreTail (j : ℕ) : Prog :=
  .let_ (gameStage j cond₂ arg₂ treeHead) verdict.code

theorem coreTail_closed (j : ℕ) : (coreTail j).WellScoped 1 :=
  ⟨gameStage_closed j _ _ _, verdict.closed.mono (by omega) _⟩

/-- **The core** of the typed oracularized decider. -/
noncomputable def core (j : ℕ) : Prog :=
  .let_ (gameStage j cond₁ arg₁ (PolyTimeFun.id Data)) (coreTail j)

theorem core_closed (j : ℕ) : (core j).WellScoped 1 :=
  ⟨gameStage_closed j _ _ _, (coreTail_closed j).mono (by omega) _⟩

section Stage

variable (j : ℕ) (cond : PolyTimeFun Data Bool) (arg view : PolyTimeFun Data Data)

theorem gameStage_inv {s r : Data} {t : ℕ} (h : (gameStage j cond arg view).Runs s r t) :
    (cond (view s) = false ∧ r = .cons s (encode true)) ∨
      (cond (view s) = true ∧ ∃ v tv, (gameProg j).Runs (arg (view s)) v tv ∧ r = .cons s v) := by
  cases hc : cond (view s)
  · refine Or.inl ⟨rfl, Prog.routeOneCall_direct_inv _ _ _ ?_ h⟩
    simp [gameRoute, hc]
  · refine Or.inr ⟨rfl, ?_⟩
    obtain ⟨v, tv, hv, rfl⟩ := Prog.routeOneCall_indirect_inv _ (gameProg_closed j) treePair
      (a := arg (view s)) (ctx := s) (by simp [gameRoute, hc]) h
    exact ⟨v, tv, hv, rfl⟩

theorem gameStage_shape {s r : Data} {t : ℕ} (h : (gameStage j cond arg view).Runs s r t) :
    ∃ v, r = .cons s v := by
  rcases gameStage_inv j cond arg view h with ⟨_, rfl⟩ | ⟨_, v, _, _, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨v, rfl⟩

theorem gameStage_runs_false (s : Data) (hc : cond (view s) = false) :
    ∃ t, (gameStage j cond arg view).Runs s (.cons s (encode true)) t :=
  Prog.routeOneCall_direct _ _ _ _ _ (by simp [gameRoute, hc])

theorem gameStage_runs_true (s : Data) (hc : cond (view s) = true) {v : Data} {tv : ℕ}
    (hv : (gameProg j).Runs (arg (view s)) v tv) :
    ∃ t, (gameStage j cond arg view).Runs s (.cons s v) t :=
  Prog.routeOneCall_indirect _ (gameProg_closed j) treePair _ _ _ _ tv
    (by simp [gameRoute, hc]) hv

end Stage

/-! ### The core's acceptance law -/

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

/-- The input decider's input in the game check at a seed is the query of `𝒱_n`'s predicate. -/
theorem gameArg_seed (n B : ℕ) (z : V.Questions n) (a₁ a₂ : BitStr) :
    gameArg V.sampler n (ℓ + 1) (toBits z) a₁ a₂ =
      encode (n, toBits ((V.seeded n B).LA z), toBits ((V.seeded n B).LB z), a₁, a₂) := by
  simp [gameArg, margBits, SeededGame.ofCL, CLFun.truncate_self]

/-- **One game check is the game check of `fig:oracle-decider`.** -/
theorem gameProg_accepts_iff_gameCheck (n B : ℕ) (z : V.Questions n)
    (a₁ a₂ : Verifier.Answers B) :
    (∃ t, (gameProg (ℓ + 1)).Runs (gInput V.sampler.prog V.decider.prog n (toBits z) a₁.1 a₂.1)
      (encode true) t) ↔ (V.seeded n B).gameCheck (.oracle, z) (.pair a₁ a₂) = true := by
  rw [gameProg_accepts_iff V.sampler V.decider.prog n (ℓ + 1) (by omega) le_rfl _ _ _
    (length_toBits z), gameArg_seed V n B]
  simp only [SeededGame.gameCheck, SeededGame.ofCL, Verifier.game, decide_eq_true_iff]
  rfl

/-- A game-check stage returns `true` only if the role's game check holds. -/
theorem gameStage_sound (n B : ℕ) (cond : PolyTimeFun Data Bool) (arg view : PolyTimeFun Data Data)
    (s : Data) (role : Role) (z : V.Questions n) (U : OAns (Verifier.Answers B))
    (hU : SeededGame.shapeOk role U = true) (hcond : cond (view s) = decide (role = .oracle))
    (harg : ∀ a₁ a₂, U = .pair a₁ a₂ →
      arg (view s) = gInput V.sampler.prog V.decider.prog n (toBits z) a₁.1 a₂.1)
    {r : Data} {t : ℕ} (h : (gameStage (ℓ + 1) cond arg view).Runs s r t) :
    ∃ v, r = .cons s v ∧ (v = encode true → (V.seeded n B).gameCheck (role, z) U = true) := by
  rcases gameStage_inv _ cond arg view h with ⟨hc, rfl⟩ | ⟨hc, v, tv, hv, rfl⟩
  · refine ⟨_, rfl, fun _ => ?_⟩
    cases role
    · simp at hcond; rw [hcond] at hc; cases hc
    · rfl
    · rfl
  · refine ⟨v, rfl, fun hvt => ?_⟩
    cases role
    · rcases U with ⟨a₁, a₂⟩ | ⟨a⟩
      · rw [harg a₁ a₂ rfl, hvt] at hv
        exact (gameProg_accepts_iff_gameCheck V n B z a₁ a₂).mp ⟨tv, hv⟩
      · simp [SeededGame.shapeOk] at hU
    · rfl
    · rfl

/-- A game-check stage returns `true` when the role's game check holds. -/
theorem gameStage_complete (n B : ℕ) (cond : PolyTimeFun Data Bool)
    (arg view : PolyTimeFun Data Data)
    (s : Data) (role : Role) (z : V.Questions n) (U : OAns (Verifier.Answers B))
    (hU : SeededGame.shapeOk role U = true) (hcond : cond (view s) = decide (role = .oracle))
    (harg : ∀ a₁ a₂, U = .pair a₁ a₂ →
      arg (view s) = gInput V.sampler.prog V.decider.prog n (toBits z) a₁.1 a₂.1)
    (hg : (V.seeded n B).gameCheck (role, z) U = true) :
    ∃ t, (gameStage (ℓ + 1) cond arg view).Runs s (.cons s (encode true)) t := by
  cases role with
  | oracle =>
    rcases U with ⟨a₁, a₂⟩ | ⟨a⟩
    · obtain ⟨tv, hv⟩ := (gameProg_accepts_iff_gameCheck V n B z a₁ a₂).mpr hg
      exact gameStage_runs_true _ cond arg view s (by simpa using hcond) (harg a₁ a₂ rfl ▸ hv)
    · simp [SeededGame.shapeOk] at hU
  | alice => exact gameStage_runs_false _ cond arg view s (by simpa using hcond)
  | bob => exact gameStage_runs_false _ cond arg view s (by simpa using hcond)

/-- `oraclePred` accepts exactly the pairs that parse to answers `oaccepts` accepts. -/
theorem oraclePred_eq_true_iff {V' : Type*} {B : ℕ} (S : SeededGame V' (Verifier.Answers B))
    (p q : Role × V') (a b : BitStr) :
    oraclePred S p q a b = true ↔
      ∃ U W, parseAns B p.1 a = some U ∧ parseAns B q.1 b = some W ∧ S.oaccepts p q U W = true := by
  unfold oraclePred
  cases hU : parseAns B p.1 a <;> cases hW : parseAns B q.1 b <;> simp

theorem oaccepts_eq_true_iff {V' A : Type*} [DecidableEq A] (S : SeededGame V' A)
    (p q : Role × V') (U W : OAns A) :
    S.oaccepts p q U W = true ↔
      SeededGame.shapeOk p.1 U = true ∧ SeededGame.shapeOk q.1 W = true ∧
        S.gameCheck p U = true ∧ S.gameCheck q W = true ∧
        (if p.1 = q.1 then decide (U = W) else true) = true ∧
        SeededGame.oracleVsPlayer p q U W = true ∧ SeededGame.oracleVsPlayer q p W U = true := by
  simp only [SeededGame.oaccepts, Bool.and_eq_true, and_assoc]

/-- **The core's acceptance law is `oraclePred`**, with no hypothesis on the input verifier: the
input decider need not halt on the inputs it rejects. -/
theorem core_accepts_iff (B n : ℕ) (t u : Role) (x y : V.Questions n) (a b : BitStr) :
    (∃ time, (core (ℓ + 1)).Runs
      (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b) (encode true) time) ↔
      oraclePred (V.seeded n B) (t, x) (u, y) a b = true := by
  obtain ⟨c, hc⟩ :
      ∃ c, c = cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b := ⟨_, rfl⟩
  rw [← hc]
  have hSp : cSp c = encode V.sampler.prog := by rw [hc]; simp
  have hDp : cDp c = encode V.decider.prog := by rw [hc]; simp
  have hN : cN c = encode n := by rw [hc]; simp
  have hT : cT c = encode t := by rw [hc]; simp
  have hX : cX c = encode (toBits x) := by rw [hc]; simp
  have hU' : cU c = encode u := by rw [hc]; simp
  have hY : cY c = encode (toBits y) := by rw [hc]; simp
  have hA := okAns_spec cT cA cB c t a hT (by rw [hc]; simp)
  have hB := okAns_spec cU cBb cB c u b hU' (by rw [hc]; simp)
  rw [show cB c = B by rw [hc]; simp] at hA hB
  have hloc_iff : localCheck c = true ↔
      ∃ U W, parseAns B t a = some U ∧ parseAns B u b = some W ∧
        (if t = u then decide (U = W) else true) = true ∧
        SeededGame.oracleVsPlayer (t, x) (u, y) U W = true ∧
        SeededGame.oracleVsPlayer (u, y) (t, x) W U = true := by
    rw [hc]
    exact localCheck_spec V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b x y
  have hcond₁ : ∀ U, parseAns B t a = some U → cond₁ c = decide (t = .oracle) := fun U hU => by
    simp only [cond₁, andB_apply, isOracle, eqD_apply, const_apply, hT, okA,
      hA.1.mpr (by simp [hU]), Bool.and_true, encode_injective.eq_iff]
  have hcond₂ : ∀ W, parseAns B u b = some W → ∀ v : Data,
      cond₂ (treeHead (.cons c v)) = decide (u = .oracle) := fun W hW v => by
    simp only [treeHead_cons, cond₂, andB_apply, isOracle, eqD_apply, const_apply, hU', okB,
      hB.1.mpr (by simp [hW]), Bool.and_true, encode_injective.eq_iff]
  have harg₁ : ∀ U, parseAns B t a = some U → ∀ a₁ a₂, U = .pair a₁ a₂ →
      arg₁ (PolyTimeFun.id Data c) =
        gInput V.sampler.prog V.decider.prog n (toBits x) a₁.1 a₂.1 := fun U hU a₁ a₂ he => by
    have hr := hA.2 U hU
    rw [he] at hr
    simp only [id_apply, arg₁, gArg, ap₂_apply, treePair_apply, hSp, hDp, hN, hX, repA, hr,
      ansData, gInput, encode_prod]
  have harg₂ : ∀ W, parseAns B u b = some W → ∀ b₁ b₂, W = .pair b₁ b₂ → ∀ v : Data,
      arg₂ (treeHead (.cons c v)) =
        gInput V.sampler.prog V.decider.prog n (toBits y) b₁.1 b₂.1 := fun W hW b₁ b₂ he v => by
    have hr := hB.2 W hW
    rw [he] at hr
    simp only [treeHead_cons, arg₂, gArg, ap₂_apply, treePair_apply, hSp, hDp, hN, hY, repB, hr,
      ansData, gInput, encode_prod]
  rw [oraclePred_eq_true_iff]
  constructor
  · rintro ⟨time, h⟩
    obtain ⟨s₁, _, _, h₁, hrest⟩ := Prog.let_closed_inv (coreTail_closed _) h
    obtain ⟨s₂, _, _, h₂, h₃⟩ := Prog.let_closed_inv verdict.closed hrest
    obtain ⟨tv, -, hvr⟩ := verdict.computes s₂
    have hv : verdict s₂ = true := (encode_injective (Eval.deterministic h₃ hvr).1).symm
    obtain ⟨v₁, rfl⟩ := gameStage_shape _ _ _ _ h₁
    obtain ⟨v₂, rfl⟩ := gameStage_shape _ _ _ _ h₂
    simp only [verdict, andB_apply, comp_apply, treeHead_cons, treeTail_cons, eqD_apply,
      const_apply, Bool.and_eq_true] at hv
    obtain ⟨hloc, hv₁, hv₂⟩ := hv
    obtain ⟨U, W, hU, hW, hsame, hov, hov'⟩ := hloc_iff.mp hloc
    obtain ⟨v₁', he₁, hg₁⟩ := gameStage_sound V n B cond₁ arg₁ (PolyTimeFun.id Data) c t x U
      (shapeOk_of_parseAns hU) (by simpa using hcond₁ U hU) (harg₁ U hU) h₁
    obtain ⟨v₂', he₂, hg₂⟩ := gameStage_sound V n B cond₂ arg₂ treeHead (.cons c v₁) u y W
      (shapeOk_of_parseAns hW) (hcond₂ W hW v₁) (fun b₁ b₂ he => harg₂ W hW b₁ b₂ he v₁) h₂
    obtain ⟨-, rfl⟩ := Data.cons.inj he₁
    obtain ⟨-, rfl⟩ := Data.cons.inj he₂
    refine ⟨U, W, hU, hW, ?_⟩
    rw [oaccepts_eq_true_iff]
    exact ⟨shapeOk_of_parseAns hU, shapeOk_of_parseAns hW, hg₁ (of_decide_eq_true hv₁),
      hg₂ (of_decide_eq_true hv₂), hsame, hov, hov'⟩
  · rintro ⟨U, W, hU, hW, hacc⟩
    rw [oaccepts_eq_true_iff] at hacc
    obtain ⟨hsU, hsW, hg₁, hg₂, hsame, hov, hov'⟩ := hacc
    have hloc : localCheck c = true := hloc_iff.mpr ⟨U, W, hU, hW, hsame, hov, hov'⟩
    obtain ⟨t₁, h₁⟩ := gameStage_complete V n B cond₁ arg₁ (PolyTimeFun.id Data) c t x U hsU
      (by simpa using hcond₁ U hU) (harg₁ U hU) hg₁
    obtain ⟨t₂, h₂⟩ := gameStage_complete V n B cond₂ arg₂ treeHead (.cons c (encode true)) u y W
      hsW (hcond₂ W hW _) (fun b₁ b₂ he => harg₂ W hW b₁ b₂ he _) hg₂
    obtain ⟨tv, -, hvr⟩ := verdict.computes (.cons (.cons c (encode true)) (encode true))
    have hv : verdict (.cons (.cons c (encode true)) (encode true)) = true := by
      simp [verdict, hloc]
    rw [hv] at hvr
    exact ⟨_, Prog.let_closed_runs (coreTail_closed _) h₁
      (Prog.let_closed_runs verdict.closed h₂ hvr)⟩

/-! ## The shell: the index routine and the clock -/

/-- **The index routine** of the oracularized decider: at index `n`, a simulation budget `K n`,
in unary, and a parse cut `B n` — the explicit form of the paper's timeout bound `B_𝒟(n)`, which
plays both roles there. -/
structure Index where
  /-- The parse cut. -/
  cut : ℕ → ℕ
  /-- The simulation budget. -/
  budget : ℕ → ℕ
  /-- The routine. -/
  prog : Prog
  /-- On `n` it returns `(K n, B n)`. -/
  runs : ∀ n, ∃ t, prog.Runs (encode n) (.cons (.ofNat (budget n)) (encode (cut n))) t

/-- The index routine's program, third of the hardcoded programs. -/
noncomputable def sIp : PolyTimeFun Data Data := treeTail.comp (treeTail.comp treeHead)
/-- The index of the typed input. -/
noncomputable def sIndex : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp treeTail)

/-- Call the index routine on the index. -/
noncomputable def indexRoute : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (ap₂ treePair sIp (encoded.comp sIndex)) (PolyTimeFun.id Data))

/-- Assemble the clocked simulation's input `(K, (core, ((S̄, D̄, B), input)))` from the index
routine's answer `(K, B)`. -/
noncomputable def indexPost (j : ℕ) : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (treeHead.comp snd) (ap₂ treePair (const (encode (core j)))
    (ap₂ treePair (ap₂ treePair (treeHead.comp (treeHead.comp fst))
      (ap₂ treePair (treeHead.comp (treeTail.comp (treeHead.comp fst))) (treeTail.comp snd)))
      (treeTail.comp fst)))

/-- The index stage. -/
noncomputable def indexStage (j : ℕ) : Prog :=
  Prog.routeOneCall indexRoute selfUniversal.univ (indexPost j)

/-- **The shell**: the index stage, the clocked simulation of the core, and the check of its
result. -/
noncomputable def shell (j : ℕ) : Prog :=
  .let_ (indexStage j)
    (.let_ selfClockedUniversal.univT CL.Detyping.ClockProgram.checkResult.code)

theorem shellTail_closed :
    (Prog.let_ selfClockedUniversal.univT CL.Detyping.ClockProgram.checkResult.code).WellScoped 1 :=
  ⟨selfClockedUniversal.closed, CL.Detyping.ClockProgram.checkResult.closed.mono (by omega) _⟩

theorem shell_closed (j : ℕ) : (shell j).WellScoped 1 :=
  ⟨Prog.routeOneCall_closed _ selfUniversal.closed _, shellTail_closed.mono (by omega) _⟩

/-- The shell's run on every input with the hardcoded programs: the verdict of the core, clocked
at the budget, on the input with the parse cut. -/
theorem shell_runs (j : ℕ) (sp dp : Prog) (I : Index) (input : Data) :
    ∃ time, (shell j).Runs (.cons (encode (sp, dp, I.prog)) input)
      (encode (decide (clockedResult (core j)
        (.cons (encode (sp, dp, I.cut (readNat (treeHead input)))) input)
        (I.budget (readNat (treeHead input))) = .cons (encode true) (encode true)))) time := by
  set m := readNat (treeHead input)
  obtain ⟨ti, hi⟩ := I.runs m
  obtain ⟨ti', -, hi'⟩ := selfUniversal.time_le _ _ _ _ hi
  have hroute : indexRoute (.cons (encode (sp, dp, I.prog)) input) =
      (true, .cons (.cons (encode I.prog) (encode m)) (.cons (encode (sp, dp, I.prog)) input)) := by
    simp [indexRoute, sIp, sIndex, encode_prod, m]
  obtain ⟨t₁, h₁⟩ := Prog.routeOneCall_indirect indexRoute selfUniversal.closed (indexPost j) _ _ _
    _ ti' hroute hi'
  have hpost : indexPost j (.cons (encode (sp, dp, I.prog)) input,
      .cons (.ofNat (I.budget m)) (encode (I.cut m))) =
      .cons (.ofNat (I.budget m)) (.cons (encode (core j))
        (.cons (encode (sp, dp, I.cut m)) input)) := by
    simp [indexPost, encode_prod]
  rw [hpost] at h₁
  obtain ⟨tu, -, hu⟩ := selfClockedUniversal.run (core j)
    (.cons (encode (sp, dp, I.cut m)) input) (I.budget m)
  obtain ⟨tc, -, hc⟩ := CL.Detyping.ClockProgram.checkResult.computes
    (clockedResult (core j) (.cons (encode (sp, dp, I.cut m)) input) (I.budget m))
  exact ⟨_, Prog.let_closed_runs shellTail_closed h₁
    (Prog.let_closed_runs CL.Detyping.ClockProgram.checkResult.closed hu hc)⟩

/-- **The typed oracularized decider**, at level `j`, of the input programs `S̄, D̄` with the index
routine `I`. -/
noncomputable def oracleDecider (j : ℕ) (sp dp : Prog) (I : Index) :
    CL.Detyping.TypedDecider Role where
  prog := hardcode (shell j) (encode (sp, dp, I.prog))
  closed := hardcode_wellScoped (shell_closed j) _

/-- **The decider halts on every input**, whatever the input programs do. -/
theorem oracleDecider_total (j : ℕ) (sp dp : Prog) (I : Index) :
    (oracleDecider j sp dp I).Total := fun n d => by
  obtain ⟨t, ht⟩ := shell_runs j sp dp I (.cons (encode n) d)
  exact ⟨_, _, hardcode_time (shell_closed j) ht⟩

/-- **The decider accepts exactly when the core accepts within the budget.** -/
theorem oracleDecider_accepts_iff (j : ℕ) (sp dp : Prog) (I : Index) (n : ℕ) (t : Role)
    (x : BitStr) (u : Role) (y a b : BitStr) :
    (oracleDecider j sp dp I).Accepts n t x u y a b ↔
      ∃ time ≤ I.budget n,
        (core j).Runs (cInput sp dp (I.cut n) n t x u y a b) (encode true) time := by
  obtain ⟨time, hout⟩ := shell_runs j sp dp I (encode (n, t, x, u, y, a, b))
  have hn : readNat (treeHead (encode (n, t, x, u, y, a, b))) = n := by
    simp [encode_prod, readNat_encode]
  rw [hn] at hout
  change (∃ t', (hardcode (shell j) (encode (sp, dp, I.prog))).Runs (encode (n, t, x, u, y, a, b))
    (encode true) t') ↔ _
  rw [show cInput sp dp (I.cut n) n t x u y a b =
    .cons (encode (sp, dp, I.cut n)) (encode (n, t, x, u, y, a, b)) from rfl,
    ← CL.Detyping.ClockProgram.clockedResult_eq_iff]
  constructor
  · rintro ⟨t', ht'⟩
    obtain ⟨t'', -, h''⟩ := hardcode_time_rev (shell_closed j) ht'
    exact of_decide_eq_true (encode_injective (Eval.deterministic hout h'').1)
  · intro h
    rw [h] at hout
    exact ⟨_, hardcode_time (shell_closed j) (by simpa using hout)⟩

/-- **Soundness of the acceptance law**: the decider accepts only answers `oraclePred` accepts, at
the index routine's cut, whatever the budget. -/
theorem accepts_sound (I : Index) (n : ℕ) (t u : Role) (x y : V.Questions n) (a b : BitStr)
    (h : (oracleDecider (ℓ + 1) V.sampler.prog V.decider.prog I).Accepts n t (toBits x) u
      (toBits y) a b) :
    oraclePred (V.seeded n (I.cut n)) (t, x) (u, y) a b = true := by
  obtain ⟨time, -, hr⟩ := (oracleDecider_accepts_iff _ _ _ I n t _ u _ a b).mp h
  exact (core_accepts_iff V (I.cut n) n t u x y a b).mp ⟨time, hr⟩

/-- **Completeness of the acceptance law**: the decider accepts the answers `oraclePred` accepts
once the core's accepting run fits in the budget. -/
theorem accepts_complete (I : Index) (n : ℕ) (t u : Role) (x y : V.Questions n) (a b : BitStr)
    (h : oraclePred (V.seeded n (I.cut n)) (t, x) (u, y) a b = true)
    (hK : ∀ time, (core (ℓ + 1)).Runs (cInput V.sampler.prog V.decider.prog (I.cut n) n t (toBits x)
      u (toBits y) a b) (encode true) time → time ≤ I.budget n) :
    (oracleDecider (ℓ + 1) V.sampler.prog V.decider.prog I).Accepts n t (toBits x) u
      (toBits y) a b := by
  obtain ⟨time, hr⟩ := (core_accepts_iff V (I.cut n) n t u x y a b).mpr h
  exact (oracleDecider_accepts_iff _ _ _ I n t _ u _ a b).mpr ⟨time, hK time hr, hr⟩

/-- The decider's program as a polynomial-time function of the three programs: the s-m-n map. -/
noncomputable def deciderProgFun (j : ℕ) : PolyTimeFun (Prog × Prog × Prog) Prog :=
  (PolyTimeFun.smn (Prog × Prog × Prog)).comp
    ((PolyTimeFun.const (shell j)).pair (PolyTimeFun.id (Prog × Prog × Prog)))

theorem deciderProgFun_apply (j : ℕ) (sp dp : Prog) (I : Index) :
    deciderProgFun j (sp, dp, I.prog) = (oracleDecider j sp dp I).prog := rfl

/-! ## The typed predicate of the detyping compiler

The detyping compiler reads a typed decider through `typedPredicate`, whose typed game over the
complete graph on the roles is O2's (`oracleSampler_cl`). Its acceptance factors through the
bounded parse, and it accepts the honest encodings once the core's runs on them fit in the budget:
the two forms in which O2's value transfers take a typed predicate. -/

section Typed

open CL.Detyping.DeciderProgram (typedPredicate)

variable (I : Index) (C : CL.Detyping.CutoffProgram)

/-- The compiler's typed predicate of the oracularized decider accepts only what `oaccepts`
accepts after the bounded parse. -/
theorem typedPredicate_sound (n : ℕ) (p q : CL.Detyping.Question Role (Fin (V.sampler.dim n)))
    (a b : Verifier.Answers (C.outer n))
    (h : typedPredicate (oracleSampler V.sampler) (oracleDecider (ℓ + 1) V.sampler.prog
      V.decider.prog I) C n p q a b = true) :
    (V.seeded n (I.cut n)).oaccepts p q ((parseAns (I.cut n) p.1 a.1).getD default)
      ((parseAns (I.cut n) q.1 b.1).getD default) = true := by
  simp only [typedPredicate, decide_eq_true_eq] at h
  exact oaccepts_of_oraclePred (accepts_sound V I n p.1 q.1 p.2 q.2 a.1 b.1 h.2.2)

/-- The compiler's typed predicate of the oracularized decider accepts the honest encodings of
every answer pair `oaccepts` accepts, when the inner cut holds them and the core's accepting runs
fit in the budget. -/
theorem typedPredicate_complete (n : ℕ) (hin : 8 * I.cut n + 3 ≤ C.inner n)
    (hout : C.inner n ≤ C.outer n)
    (hK : ∀ (t u : Role) (x y : V.Questions n) (a b : BitStr), a.length ≤ C.inner n →
      b.length ≤ C.inner n → ∀ time, (core (ℓ + 1)).Runs (cInput V.sampler.prog V.decider.prog
        (I.cut n) n t (toBits x) u (toBits y) a b) (encode true) time → time ≤ I.budget n)
    (p q : CL.Detyping.Question Role (Fin (V.sampler.dim n)))
    (U W : OAns (Verifier.Answers (I.cut n)))
    (h : (V.seeded n (I.cut n)).oaccepts p q U W = true) :
    typedPredicate (oracleSampler V.sampler) (oracleDecider (ℓ + 1) V.sampler.prog V.decider.prog I)
      C n p q ⟨encAns U, ((length_encAns_le U).trans hin).trans hout⟩
      ⟨encAns W, ((length_encAns_le W).trans hin).trans hout⟩ = true := by
  have hU := (length_encAns_le U).trans hin
  have hW := (length_encAns_le W).trans hin
  simp only [typedPredicate, decide_eq_true_eq]
  exact ⟨hU, hW, accepts_complete V I n p.1 q.1 p.2 q.2 _ _ (oraclePred_encAns h)
    (hK p.1 q.1 p.2 q.2 _ _ hU hW)⟩

/-- **Soundness of the compiled typed game**: its quantum value above `1 - ε` puts `val*(𝒱_n)` at
the parse cut at least `1 - 24√ε`, whatever the budget. -/
theorem valStar_ge_of_typedPredicate (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue (CL.Detyping.typedGame roleGraph roleGraph_nonempty
      (fun _ => roleFamily (V.sampler.cl n)) (typedPredicate (oracleSampler V.sampler)
        (oracleDecider (ℓ + 1) V.sampler.prog V.decider.prog I) C n))) :
    1 - 24 * √ε ≤ V.valStar n (I.cut n) :=
  V.valStar_ge_of_typed n (I.cut n) _ (fun p a => (parseAns (I.cut n) p.1 a.1).getD default)
    (fun p q a b h => typedPredicate_sound V I C n p q a b h) hε h

/-- **Completeness of the compiled typed game**: a value-`1` PCC strategy of `𝒱_n` at the parse
cut gives one of the doubled typed game, when the inner cut holds every honest encoding and the
core's accepting runs fit in the budget. -/
theorem exists_typedPredicate_perfectPCC (n : ℕ) (hin : 8 * I.cut n + 3 ≤ C.inner n)
    (hout : C.inner n ≤ C.outer n)
    (hK : ∀ (t u : Role) (x y : V.Questions n) (a b : BitStr), a.length ≤ C.inner n →
      b.length ≤ C.inner n → ∀ time, (core (ℓ + 1)).Runs (cInput V.sampler.prog V.decider.prog
        (I.cut n) n t (toBits x) u (toBits y) a b) (encode true) time → time ≤ I.budget n)
    (hV : V.HasPerfectPCC n (I.cut n)) :
    ∃ R : SyncStrategy (CL.Detyping.typedGame roleGraph roleGraph_nonempty
        (fun _ => roleFamily (V.sampler.cl n)) (typedPredicate (oracleSampler V.sampler)
          (oracleDecider (ℓ + 1) V.sampler.prog V.decider.prog I) C n)).doubled,
      R.IsPCC ∧ R.value = 1 :=
  V.exists_typed_perfectPCC n (I.cut n) hV _
    (fun U => ⟨encAns U, ((length_encAns_le U).trans hin).trans hout⟩)
    (fun p q U W h => typedPredicate_complete V I C n hin hout hK p q U W h)

end Typed

end OracleDecider

end MIPRE
