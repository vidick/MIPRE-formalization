# TM infrastructure — roadmap and execution plan (Milestones A & B)

## Context

Goal: build the Turing-machine infrastructure needed by the MIP*=RE formalization —
ultimately: canonical, serializable machine descriptions, a universal interpreter with
polynomial overhead, and input-hardwiring, per the program proposed in a GPT-authored design
document (2026-08-05) and reviewed/verified by Claude the same day. This file records the
**full roadmap** (Milestones A–G) and the **detailed execution plan for Milestones A and B**,
which are what we implement now:

- **Milestone A — multi-input semantics**: `MultiInputTM i w Symbol State`, a generalization
  of CSLib's merged `Turing.MultiTapeTM` from one read-only input tape to `i` of them, with
  exact equivalence at `i = 1`. The paper needs multi-input machines natively (blueprint
  `def:decider`: "a 5-input Turing machine"; `def:sampler`, `def:lambda-bounded` state
  per-index bounds `TIME_𝒟(n)`), and concatenation-packing would pollute every later time
  bound with the lengths of unrelated inputs.
- **Milestone B — finite machine syntax**: `RawCode`/`WellFormed`/`Code i` (dense,
  canonically ordered transition tables) with an executable interpretation
  `Code.toTM : Code i → MultiInputTM …`. Principle: *machine code is primary syntax; the
  operational machine is its interpretation*. This is the prerequisite for serialization,
  self-reference, `|𝒟|` size measures, and hardwiring; starting from arbitrary Lean
  transition functions provably dead-ends (see verified facts below).

### Verified facts this plan relies on (checked 2026-08-05 against live sources)

1. **CSLib upstream** (`leanprover/cslib` `main` @ `3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc`,
   2026-08-03): `Cslib/Computability/Machines/Turing/MultiTape/` = exactly
   `Deterministic.lean` (531 lines) + `TapeLemmas.lean` (150 lines), merged 2026-07-24
   (#384; fixes #743/#745; lemmas #768). Model and names as assumed by the GPT program
   (`MultiTapeTM`, input-indexed `Cfg`, `step`, `configs`, `outputString`, `spaceUsed`,
   `ComputesInTimeAndSpace`, `haltsAtStep`, `RelatesInSteps` bridge). One import dependency:
   `Cslib/Foundations/Data/RelatesInSteps.lean` (221 lines). Files use the Lean module system
   (`module`, `public import`, `@[expose] public section`).
2. **Toolchain gap**: CSLib main is on `leanprover/lean4:v4.33.0-rc2` (Mathlib pinned to
   `v4.33.0-rc2`); the MultiTape files never existed on a `v4.32.0` CSLib commit (the v4.32.0
   window closed 2026-07-16, before the merge). This repo pins Lean `v4.32.0` + Mathlib
   `v4.32.0` stable ⇒ CSLib **cannot** be a lake dependency today ⇒ we vendor (decision D1).
3. **Experimental branches** (`crei/cslib`): `rtm` has the `Data`/`Prog`/`InPlace`/simulator
   stack; its simulation semantics are proved but all 4 `sorry`s are the quantitative bounds,
   and its transition-table extraction is `noncomputable` via `Fintype.elems`
   (`TMSimulator.lean:690`) — the concrete demonstration of why code-first is mandatory.
   `utm` is older (3 `sorry`s incl. universal-step correctness); ideas only. Relevant to
   Milestones E–G, not A/B.
4. **This repo's architecture** (must not be contradicted): the ambient cost model for all
   polynomial-time statements is `Turing.ToPartrec.Code` + `TimedEval`
   (decision record in `MIPRE/Foundations/Cost/Basic.lean`); final computability statements
   use `Nat.Partrec.Code` (`MIPRE/HaltingGameValue.lean`, blueprint
   `sec:computability-conventions`). Per that record (R3), a low-level machine appears only
   inside the succinct Cook–Levin gateway (`thm:succinct-sat`); `Cost/Toolkit.lean` notes its
   ambient universal-machine theorems "should share design" with that gateway's interpreter.
   **Roles of this TM layer**: (a) substrate for `thm:succinct-sat`; (b) CSLib-upstreamable
   infrastructure; (c) possible later paper-literal normal-form-verifier statements.
   The "who owns the universal interpreter" question is deliberately deferred to the
   Milestone E gate (see Roadmap).

### Fork findings — crei/cslib (checked 2026-08-05, after Milestones A/B landed)

Christian Reitwiessner's fork (github.com/crei/cslib) was inventoried branch by branch.
Impact on this plan:

- **Milestones A and B are not superseded**: the fork contains no multi-input machines
  anywhere, and its only `Fin`-typed machine sketch (`rtmfun3:HierarchyTheorems.lean`,
  `NormalizedTM`, 9 sorries, single-tape) is not a serializable dense-table code.
- **Adopted for Milestone A**: the `congrState`/`congrSymbol` relabeling API of
  `finite_in_fin:Regular.lean` (sorry-free, v4.32.0-rc1, tip `4a149e2`), ported to
  `MIPRE/TM/MultiInput/Congr.lean` (WP3b). The fork file itself targets the pre-#745
  model (its `Cfg` still has an `output` field), so it cannot be vendored against the
  current upstream model; the port also replaces the fork's `noncomputable`
  embedding-plus-`Function.invFun` `congrState` with a computable `Equiv`-based one
  (its only consumer instantiates with an `Equiv` anyway), keeping decision D5 intact.
  The fork's DFA simulation and regular-language results were deliberately not ported.
- **Later-milestone material** (descriptions updated in the roadmap below): the `rtm`
  branch is the Milestone E port target; `utm:Satisfiability.lean` (sorry-free verified
  5-tape SAT-verifier TM) is design evidence for the succinct-SAT gateway; open upstream
  PRs #767 (Classes/SpaceInTime) and #772 (ConfigBound) plus the fork's `BigO` are
  Milestone G alignment targets. crei's upstream pipeline (issue #611) overlaps
  Milestones B/F/G — **coordinate before building anything it may deliver upstream.**

## Fixed decisions (modifications to the GPT program)

- **D1 — vendor CSLib, don't depend.** Vendor 3 files byte-faithfully (adaptations listed in
  WP1) under `MIPRE/Cslib/…` mirroring upstream paths, keeping upstream copyright headers
  (Apache 2.0; authors Reitwiessner, Bailey) plus a provenance block (upstream path, SHA
  `3aa9d44`, date, adaptation list). Names/namespaces unchanged (`Turing.MultiTapeTM`,
  `Relation.RelatesInSteps`) so un-vendoring later = delete files + add `require` +
  fix imports; all downstream proofs survive. Revisit when Lean v4.33.0 is stable and
  Mathlib/CSLib align with this repo.
- **D2 — `RawAction` carries no phantom arity parameter.** Its fields are plain `Array`s;
  only `RawCode.WellFormed` constrains sizes. `i` stays on `RawCode i`/`Code i`.
- **D3 — executable well-formedness.** `RawCode.wellFormedB : Bool` +
  `wellFormedB_iff : wellFormedB c = true ↔ c.WellFormed`, in Milestone B (the Milestone C
  parser and `by decide` examples consume the Bool form).
- **D4 — resource-bound packaging over length vectors.** The primitive is the exact-run
  relation `ComputesInTimeAndSpace … (t s : ℕ)` (mirroring CSLib clause-for-clause, D8);
  the packaged form `ComputesFunWithBounds` takes `timeBound spaceBound : (Fin i → ℕ) → ℕ`.
  No `Σ|xⱼ|`-vs-`max|xⱼ|` convention is baked in anywhere (GPT §1.2), and this fixes the
  GPT draft's type mismatch (its `List IOSymbol` bounds).
- **D5 — computability acceptance criterion, restated.** Every definition in the evaluation
  path is computable (no `noncomputable`, `#eval` succeeds) and no *definition* depends on
  `Fintype.elems`, hash/enumeration order, or choice. Proof terms may be classical (Mathlib
  is); that is harmless and not gated on.
- **D6 — `defaultRejectCode` lands in Milestone B** (it is a concrete `Code` and a needed
  test machine), though its consumer (total decoding) is Milestone C.
- **D7 — placement and namespaces.** Vendored files: `MIPRE/Cslib/…` (upstream namespaces).
  New model code: `MIPRE/TM/MultiInput/…` and `MIPRE/TM/Code/…`, namespace `Turing`
  (upstream-shaped for CSLib upstreaming; project-specific glue in later milestones uses
  `MIPRE.*`). Mathlib style + docstrings on every declaration (repo CONTRIBUTING).
- **D8 — mirror CSLib semantics exactly.** Same `Cfg` shape (input-indexed; no output field),
  same halting convention (`state = none`, halted configs are fixed points), space = visited
  work-tape cells, `ComputesInTimeAndSpace` = (halted at `t`) ∧ (output equal) ∧ (space
  exactly `s`). Reuse vendored `Turing.moveInputPos` verbatim (it is arity-agnostic).
- **Policy: all six work packages are sorry-free** (CONTRIBUTING allows merged sorries only
  for blueprint-tracked nodes; nothing here needs one). Every WP runs `lake exe mk_all` and
  commits the regenerated `MIPRE.lean`.

## Roadmap (full GPT program; A–B detailed below, C–G tracked here)

| Milestone | Content | Status |
|---|---|---|
| **A** | Multi-input semantics + CSLib equivalence at `i = 1` (WP1–WP3) | ✅ 2026-08-05 |
| **B** | Finite machine syntax `Code i` + executable `Code.toTM` (WP4–WP6) | ✅ 2026-08-05 |
| C | Exact binary serialization: prefix-free nat codec, `encodeCode`/`decodeCodeExact`/`decodeCodeExact_sound`, total `decodeCode` via `defaultRejectCode`, `codeSize` (**detailed plan below**, WP7–WP9) | ☐ |
| D | Pure reference evaluator: `Code.runFor`, `Code.evalWithin`, `Code.Produces` + execution laws | ☐ |
| E | Port `rtm` semantic core (`Data`, codecs, `Prog`, `InPlace`, controller-style simulator consuming `Code`, never `Fintype.elems`). Port target: crei/cslib `rtm` branch (tip 2026-06-24, v4.32.0-rc1): `Data`/`DataEncode`/`Prog`/`ProgSem`+`InPlace` core sorry-free; `PB` 7 sorries, `TMSimulator` 4 (all quantitative) | ☐ |
| F | Compile the fixed universal program → `boundedUniversalCode i : Code (i+2)`, `universalCode i : Code (i+1)` + correctness. Design evidence: `utm:Satisfiability.lean` (sorry-free verified 5-tape SAT-verifier TM — also a gateway prototype for `thm:succinct-sat`); `rtmfun3:HierarchyTheorems.lean` (`NormalizedTM`, quadratic-overhead universal spec; sketch, 9 sorries) | ☐ |
| G | Quantitative bounds → `universal_polynomial_overhead` (coarse polynomial; degree not optimized). Align with crei's open upstream PRs: #772 `ConfigBound` (#configs ≤ (n+2)·a·2^(c·s)), #767 `Classes`/`SpaceInTime` (DTIME/DSPACE, L⊆P, PSPACE⊆EXP), fork `landau_calculus:BigO` | ☐ |

**Gate before E/F (record the decision here when made):** one interpreter or two — TM-level
`universalCode` vs the ambient-model `exists_efficient_universal`/`exists_clocked_universal`
of `Cost/Toolkit.lean`, vs one compiled artifact discharging both (likely: an
`InPlace`-compiled interpreter *of the ambient `ToPartrec.Code` model*, serving
`thm:succinct-sat` and the toolkit simultaneously — cf. Toolkit's "should share design").
Also deferred until after C stabilizes: `specialize` (hardwiring) — per GPT §6.

---

## Milestone A — multi-input semantics

### WP1 — vendor CSLib files (+ commit this plan)

**Files created:**

```
planning/tm-infrastructure.md                                    (this document)
MIPRE/Cslib/Foundations/Data/RelatesInSteps.lean                 (221 lines upstream)
MIPRE/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean   (531 lines)
MIPRE/Cslib/Computability/Machines/Turing/MultiTape/TapeLemmas.lean      (150 lines)
```

Upstream sources pinned to SHA `3aa9d44`; re-fetch if ever needed:
`gh api "repos/leanprover/cslib/contents/<path>?ref=3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc" -H "Accept: application/vnd.github.raw"`.

**Adaptation checklist (the only permitted differences from upstream):**

1. Delete the `module` line; `public import X` → `import X`; remove the
   `@[expose] public section` line.
2. `import Cslib.Init` → drop; if something breaks (e.g. attribute registrations), inline
   the minimal needed piece with a provenance comment.
3. `import Cslib.Foundations.Data.RelatesInSteps` →
   `import MIPRE.Cslib.Foundations.Data.RelatesInSteps` (similarly for the
   `MultiTape.Deterministic` import in `TapeLemmas.lean`).
4. `open Cslib Relation` → `open Relation` (the `Cslib` namespace is not vendored).
5. Add `set_option autoImplicit true` and `set_option relaxedAutoImplicit true` (upstream
   compiles with Lean's defaults; this repo's lakefile disables them globally).
6. Mathlib import paths verified to exist at `v4.32.0` (all do, incl.
   `Mathlib.Data.Sign.Defs`); the `lia` tactic verified available on `v4.32.0`.
7. Below each original header: provenance block — upstream repo/path, SHA `3aa9d44`,
   fetch date 2026-08-05, and this adaptation list. **No declaration names, statements, or
   proofs may change**; if a proof breaks on v4.32.0 Mathlib, repair minimally and add the
   repair to the provenance block.

**Acceptance:** `lake build` green; diff against the pinned upstream sources shows only the
listed adaptations; `lake exe mk_all` committed.

> **Completed 2026-08-05.** One extra adaptation was needed, recorded in the file's
> provenance block: `RelatesInSteps.lean` additionally imports `Mathlib.Data.Nat.Notation`
> (upstream gets the `ℕ` notation via `Cslib.Init`, which we drop). All three files
> otherwise compile unchanged on Lean v4.32.0 / Mathlib v4.32.0; `lia` is available there.

### WP2 — the model: `MIPRE/TM/MultiInput/Deterministic.lean` + `TapeLemmas.lean`

Namespace `Turing`, then `namespace MultiInputTM`. Mirror the vendored file
section-for-section; port is componentwise (`∀ j : Fin i` plumbing), same lemma names.

**Core structures:**

```lean
structure TransitionOut (i w : ℕ) (Symbol State : Type*) where
  inputMoves  : Fin i → SignType
  workActions : Fin w → Option (Option Symbol) × SignType
  outS        : Option Symbol
  q'          : Option State

structure MultiInputTM (i w : ℕ) (Symbol State : Type*) where
  q₀ : State
  tr (q : State) (inputs : Fin i → Option Symbol) (work : Fin w → Option Symbol) :
    TransitionOut i w Symbol State

@[ext] structure Cfg (i w : ℕ) (Symbol State : Type*) (input : Fin i → List Symbol) where
  state       : Option State
  inputPos    : (j : Fin i) → Fin ((input j).length + 2)
  workTapes   : Fin w → ℤ → Option Symbol
  workTapePos : Fin w → ℤ
deriving Inhabited
```

**Port map (upstream `MultiTapeTM` decl → `MultiInputTM` decl, same name unless noted):**

- `moveInputPos` — **not ported**; reuse vendored `Turing.moveInputPos` (arity-agnostic).
- `Cfg.inputSymbol` → `Cfg.inputSymbol (j : Fin i)`; add
  `Cfg.inputSymbols : Fin i → Option Symbol := fun j => cfg.inputSymbol j`;
  `inputSymbolInner` → per-tape variant.
- `Cfg.workTapeSymbols`, `step` (input heads move via `moveInputPos (cfg.inputPos j)
  (out.inputMoves j)`), `outputSymbol`, `initCfg` (state `some q₀`, every input head at `1`,
  blank tapes, work heads at `0`), `step_of_halt`, `configs`, `configs_zero`,
  `configs_succ_eq_step`, `configs_succ_eq_step'`, `configs_add`, `configs_of_halts`,
  `outputSymbol_of_halt`, `workTapePos_step_le` — all direct.
- `TransitionRelation`, `outputString` + `outputString_succ`/`_halt`/`_add_eq_append`/
  `_eq_of_halt`, `relatesInSteps_iff_configs_eq`, `haltsAtStep`, `halting_step_unique`,
  `not_halts_of_repeat_nonhalt` — all direct.
- `TapeLemmas.lean`: port all 10 lemmas (`step_workTapes_eq_of_ne`, `mem_visitedByTapeHead`
  (+`_self`), `visitedByTapeHead_mono`, `uIcc_workTapePos_subset_visitedByTapeHead`,
  `mem_visitedByTapeHead_of_workTapes_ne`, `natAbs_le_spaceUsedByTape_of_mem_visited`,
  `content_natAbs_le_spaceUsedByTape`, `spaceUsedByTape_le`, `spaceUsed_linear`,
  `spaceUsedByTape_mono`, `spaceUsed_mono`) plus the `Space` section defs
  (`visitedByTapeHead`, `spaceUsedByTape`, `spaceUsed`, `spaceUsed_zero_tapes_eq_zero`,
  `spaceUsedByTape_le_spaceUsed`).

Upstream proofs are short and `grind`/`omega`-heavy; expect them to port with minor edits.

**Acceptance:** builds sorry-free; every upstream declaration has its multi-input
counterpart under the same name.

### WP3 — resource packaging + CSLib equivalence

**`MIPRE/TM/MultiInput/Complexity.lean`:**

```lean
def ComputesInTimeAndSpace (M : MultiInputTM i w Symbol State)
    (input : Fin i → List Symbol) (output : List Symbol) (t s : ℕ) : Prop :=
  (M.configs (M.initCfg input) t).state = none ∧
  M.outputString (M.initCfg input) t = output ∧
  M.spaceUsed (M.initCfg input) t = s

def ComputesFunWithBounds (M : MultiInputTM i w Symbol State) {IOSymbol : Type*}
    (f : (Fin i → List IOSymbol) → List IOSymbol) (emb : IOSymbol ↪ Symbol)
    (timeBound spaceBound : (Fin i → ℕ) → ℕ) : Prop :=
  ∀ x, ∃ t ≤ timeBound (fun j => (x j).length), ∃ s ≤ spaceBound (fun j => (x j).length),
    M.ComputesInTimeAndSpace (fun j => (x j).map emb) ((f x).map emb) t s
```

**`MIPRE/TM/MultiInput/OneInputEquiv.lean`:** for `M : MultiInputTM 1 w Symbol State`,
`N : MultiTapeTM w Symbol State`, `input : List Symbol`; use `fun _ : Fin 1 => input`
(never `![input]` — keeps the dependent `inputPos` transport definitional):

```lean
def MultiInputTM.toCSLib (M : MultiInputTM 1 w Symbol State) : MultiTapeTM w Symbol State
def MultiInputTM.ofCSLib (N : MultiTapeTM w Symbol State) : MultiInputTM 1 w Symbol State
def cfgEquiv : MultiTapeTM.Cfg w Symbol State input
             ≃ MultiInputTM.Cfg 1 w Symbol State (fun _ => input)

theorem toCSLib_ofCSLib : (N.ofCSLib).toCSLib = N        -- and ofCSLib_toCSLib
theorem toCSLib_initCfg : cfgEquiv (M.toCSLib.initCfg input) = M.initCfg (fun _ => input)
theorem toCSLib_step    : cfgEquiv (M.toCSLib.step c)    = M.step (cfgEquiv c)
theorem toCSLib_configs : cfgEquiv (M.toCSLib.configs c t) = M.configs (cfgEquiv c) t
theorem toCSLib_outputString : M.toCSLib.outputString c t = M.outputString (cfgEquiv c) t
theorem toCSLib_spaceUsed    : M.toCSLib.spaceUsed c t    = M.spaceUsed (cfgEquiv c) t
theorem toCSLib_computesInTimeAndSpace :
    M.toCSLib.ComputesInTimeAndSpace input out t s ↔
      M.ComputesInTimeAndSpace (fun _ => input) out t s
```

Proof shape: `toCSLib_step` by `cases cfg.state` + `TransitionOut`/`Cfg` ext + `grind`;
`_configs` by induction on `t` from `_step`; `_outputString` by induction via
`outputString_succ`; `_spaceUsed` from configs-commutation (`visitedByTapeHead` images
agree pointwise). Round trips need only `Subsingleton (Fin 1)`-style extensionality.

**Milestone A acceptance (all sorry-free):**
`#check` `MultiInputTM.step` / `.configs` / `.outputString` / `.ComputesInTimeAndSpace`;
theorems `toCSLib_step`/`toCSLib_configs`/`toCSLib_outputString`/`toCSLib_spaceUsed` (+
`_computesInTimeAndSpace`, round trips). **Interface freeze:** no universal-machine work
(Milestones E–G) starts before this is merged and stable.

---

## Milestone B — finite machine syntax

Design rule enforced in review: **no definition may mention `Fintype.elems`, enumeration
order, or choice** (D5). WP4 is independent of WP1–3; WP5 depends on WP4; WP6 on WP2+WP5.

### WP4 — raw syntax and observation indexing

**`MIPRE/TM/Code/Raw.lean`:**

```lean
inductive Move | left | stay | right          deriving DecidableEq, Repr
def Move.toSignType : Move → SignType
inductive RawWrite | keep | blank | symbol (a : ℕ)   deriving DecidableEq, Repr
structure RawWorkAction where write : RawWrite; move : Move   deriving DecidableEq, Repr
structure RawAction where                     -- D2: no arity parameter
  inputMoves : Array Move; workActions : Array RawWorkAction
  output : Option Bool; nextState : Option ℕ  deriving DecidableEq, Repr
structure RawCode (i : ℕ) where
  workTapeCount alphabetSize stateCount startState : ℕ
  table : Array RawAction                     deriving DecidableEq, Repr
```

Module docstring records the I/O convention: alphabet symbols `0`/`1` are reserved for
binary input/output; larger alphabets are internal-only.

**`MIPRE/TM/Code/Observation.lean`** — the codec, with this **normative order** in the
module docstring (cited later by the serialization format and the UTM lookup proofs):

> `transitionIndex q as bs = q · (σ+1)^(i+w) + obs`, where `obs` is the Horner evaluation,
> radix `σ+1`, of the digit string: input-tape symbols in ascending tape order, then
> work-tape symbols in ascending tape order (input tape 0 most significant); digit of
> blank (`none`) is `0`, of symbol `a` is `a+1`. Never dependent on `Fintype.elems`,
> hash order, or a chosen basis.

```lean
def encodeSymbol? : Option (Fin σ) → Fin (σ + 1)      -- none ↦ 0, some a ↦ a+1
def decodeSymbol? : Fin (σ + 1) → Option (Fin σ)
def encodeObservation (as : Fin i → Option (Fin σ)) (bs : Fin w → Option (Fin σ)) :
    Fin ((σ + 1) ^ (i + w))
def decodeObservation : Fin ((σ+1)^(i+w)) → (Fin i → Option (Fin σ)) × (Fin w → Option (Fin σ))
def transitionIndex (q : Fin Q) (as …) (bs …) : Fin (Q * (σ + 1) ^ (i + w))
def decodeTransitionIndex : Fin (Q * (σ+1)^(i+w)) → Fin Q × (Fin i → …) × (Fin w → …)
```

Implementation: hand-rolled Horner fold over `List.ofFn` digits with a `div`/`mod` inverse
(helpers `encodeDigits : List (Fin (r+1)) → ℕ`, `decodeDigits`, round-trip + bound lemmas by
list induction and `omega`). Deliberately **not** `finFunctionFinEquiv` — we own and document
the order. Prove **both** inverse laws for symbols, observations, and `transitionIndex`
(injectivity as corollary); the decode direction is consumed by Milestone C's parser and the
UTM's table scan.

### WP5 — well-formedness and the `Code` type

**`MIPRE/TM/Code/WellFormed.lean`:**

```lean
def RawCode.WellFormed (c : RawCode i) : Prop :=
  2 ≤ c.alphabetSize ∧ 0 < c.stateCount ∧ c.startState < c.stateCount ∧
  c.table.size = c.stateCount * (c.alphabetSize + 1) ^ (i + c.workTapeCount) ∧
  ∀ a ∈ c.table,
    a.inputMoves.size = i ∧ a.workActions.size = c.workTapeCount ∧
    (∀ wa ∈ a.workActions, ∀ s, wa.write = .symbol s → s < c.alphabetSize) ∧
    (∀ q ∈ a.nextState, q < c.stateCount)

def RawCode.wellFormedB (c : RawCode i) : Bool           -- D3
theorem RawCode.wellFormedB_iff : c.wellFormedB = true ↔ c.WellFormed

structure Code (i : ℕ) where raw : RawCode i; wf : raw.WellFormed
theorem Code.ext (h : c₁.raw = c₂.raw) : c₁ = c₂         -- proof irrelevance
instance : DecidableEq (Code i)
abbrev Code.workTapeCount / alphabetSize / stateCount / startState   -- := raw.*
```

Shared lookup helper (confines all dependent-index pain to one place):

```lean
def Code.actionAt (c : Code i) (q : Fin c.stateCount)
    (as : Fin i → Option (Fin c.alphabetSize))
    (bs : Fin c.workTapeCount → Option (Fin c.alphabetSize)) : RawAction
theorem Code.actionAt_mem : c.actionAt q as bs ∈ c.raw.table
theorem Code.actionAt_inputMoves_size  : (c.actionAt q as bs).inputMoves.size = i
theorem Code.actionAt_workActions_size : (…).workActions.size = c.workTapeCount
theorem Code.actionAt_write_lt / actionAt_nextState_lt                -- from wf
```

### WP6 — interpretation and executable tests

**`MIPRE/TM/Code/Semantics.lean`:**

```lean
abbrev Code.Symbol (c : Code i) := Fin c.alphabetSize
abbrev Code.State  (c : Code i) := Fin c.stateCount
def Code.bitEmbedding (c : Code i) : Bool ↪ c.Symbol      -- ⟨0⟩/⟨1⟩, from 2 ≤ σ
def Code.bitInputs (c : Code i) (x : Fin i → List Bool) : Fin i → List c.Symbol
def Code.toTM (c : Code i) : MultiInputTM i c.workTapeCount c.Symbol c.State
theorem Code.toTM_q₀ : c.toTM.q₀ = ⟨c.startState, …⟩
theorem Code.toTM_tr : c.toTM.tr q as bs = interpretAction c (c.actionAt q as bs) …
theorem Code.outputSymbol_isBit :                          -- coded machines emit only 0/1
    c.toTM.outputSymbol cfg = none ∨ ∃ b, c.toTM.outputSymbol cfg = some (c.bitEmbedding b)
def Code.decodeBitOutput : List c.Symbol → List Bool       -- total; faithful by _isBit
theorem Code.decodeBitOutput_map_bitEmbedding : c.decodeBitOutput (l.map c.bitEmbedding) = l
```

`interpretAction` conversions: `Move.toSignType` per input tape (sizes from
`actionAt_inputMoves_size`); `RawWrite.keep ↦ none`, `.blank ↦ some none`,
`.symbol s ↦ some (some ⟨s, actionAt_write_lt …⟩)`; `output.map bitEmbedding`;
`nextState` to `Option c.State` via `actionAt_nextState_lt`. Primary style: dependent,
wf-threaded through the `actionAt_*` lemmas. **Recorded fallback** if proof-threading turns
ugly: a total clamping interpretation `RawCode.toTMRaw` + one lemma
`WellFormed → toTM = toTMRaw`-agreement; downstream statements unchanged.

**`MIPRE/TM/Code/Examples.lean`:** `defaultRejectCode (i) : Code i` (σ=2, Q=1, w=0, table =
`Array.replicate (3^i)` of {stay moves, output `some false`, halt}; `wf` by lemmas, not
`decide`, since `i` is generic) and the six concrete test machines (wf by `decide`):

1. output `0` and halt (≈ `defaultRejectCode 1`);
2. copy the first input bit (i=1, w=0, Q≈2) — pin: input `[true]` ↦ output `[true]`;
3. move left onto the blank boundary — pin `inputPos` clamps at `0`, `inputSymbol = none`;
4. move right past the last symbol — pin clamp at `length + 1`;
5. write/move/return/reread on one work tape (i=1, w=1, Q≈3) — pin output `[true]`;
6. two-state non-halting loop — pin `(configs … 100).state ≠ none` and
   `haltsAtStep … t = false` for sampled `t`.

Local display helpers (`Cfg` holds functions, so inspect by projection): state and head
positions after `t` steps, a work-tape window `List (Option ℕ)` over `[lo, hi]`,
`decodeBitOutput` of `outputString`. Pin expected values with `example : … := by decide`
where the kernel cooperates (machines are tiny); `#eval`-with-expected-output comment as
fallback. **No `native_decide`.** A passing `#eval` on every example is itself acceptance
evidence for D5.

**Milestone B acceptance (all sorry-free):** `RawCode`/`WellFormed`(+`wellFormedB_iff`)/
`Code`/observation codec (both inverse laws)/`Code.toTM`/`toTM_tr` landed; normative order
documented in `Observation.lean`; all states/symbols canonically numbered via `Fin`; every
evaluation-path definition computable and `#eval`-verified; six examples + `defaultRejectCode`
evaluate to pinned results.

---

## Milestone C — exact binary serialization

Machine codes become bit strings: `Code i ↔ {0,1}*` with a canonical encoder, an exact
partial decoder, and a total decoder defaulting to `defaultRejectCode i`. This is the
paper's "description `α` of a machine": prerequisite for `|𝒟|` measures, the universal
machine's input format, and self-reference.

**Decisions (extending D1–D8):**

- **D9 — TM-side only.** The codec lives in the `Turing` namespace over plain
  `List Bool`; no dependency on, or bridge to, `MIPRE.Cost.SizedEncoding` yet (a
  `SizedEncoding (Code i)` instance is deferred to the succinct-SAT gateway, the first
  place ambient-model programs manipulate TM descriptions).
- **D10 — kernel-evaluable codecs.** Every encoder/parser is structurally recursive
  (fuel where needed, `List` loops, no `Array.all`-style opaque recursion), so all
  round-trip and malformed-input tests are `by decide` — same discipline as Milestone B.
- **D11 — soundness by prefix-free design, not re-encoding.** Every field codec is
  prefix-free and canonical (the nat parser rejects digit strings with a trailing
  `false`), and every parser comes with a paired soundness lemma
  `parse s = some (a, rest) → s = encode a ++ rest`. `decodeCodeExact_sound` then falls
  out compositionally. Recorded fallback if a soundness proof turns ugly: accept only
  strings with `encode (parsed) == input` — trivially sound, less elegant.

**Normative format** (cited by Milestones E–G; must never change):
`encodeNat 0 (version) · workTapeCount · alphabetSize · stateCount · startState · the
Q·(σ+1)^(i+w) table entries in `transitionIndex` order`. Naturals use the
self-delimiting code `1^L 0 d₀…d_{L−1}` (`d` = little-endian binary digits, canonical:
last digit of a nonzero number is `1`; `L` = their count). Per entry: `i` moves
(`stay = 0`, `right = 10`, `left = 11`), `w` work actions (write `keep = 0`,
`blank = 10`, `symbol s = 11·encodeNat s`, then the move), output
(`none = 0`, `some b = 1·b`), successor (`none = 0`, `some q = 1·encodeNat q`).
The arity `i` stays external (the paper's `[α]_i`). `decodeCodeExact` demands full
consumption (trailing garbage rejected) and gates on `wellFormedB`.

### WP7 — the self-delimiting nat codec (`Code/Encoding/Nat.lean`)

`natToBits`/`bitsToNat` (little-endian digits, structural via fuel + fuel-irrelevance
lemma), `encodeNat`, `parseUnary`, `parseNat`. Theorems: both digit round trips
(`bitsToNat_natToBits`; `natToBits_bitsToNat` on canonical strings), canonicality
(`natToBits_getLast?_ne_false`), the length characterization
(`n < 2 ^ (natToBits n).length`, `n < 2^k → length ≤ k` — avoids `Nat.log2`), prefix
property (`parseNat (encodeNat n ++ rest) = some (n, rest)`), soundness
(`parseNat_sound`), injectivity, `encodeNat_length` (`= 2L + 1`) and its `2k + 1` bound.

### WP8 — machine serialization (`Code/Encoding/MachineCode.lean`)

Field codecs (`Move`, `RawWrite`, output, successor, `RawWorkAction`) each with prefix +
soundness lemmas; the generic fixed-count combinator `parseCount` /`encodeListWith` with
membership-scoped prefix and soundness lemmas; `encodeAction`/`parseAction i w` (prefix
lemma assumes the entry's arities — supplied by well-formedness at the call site);
`encodeRawCode`/`encodeCode`/`parseRawCode`/`decodeCodeExact`. Theorems:
`decodeCodeExact_encodeCode` (simp), `encodeCode_injective`, `decodeCodeExact_sound`.

### WP9 — total decoding, size, tests (`Code/Encoding/Total.lean`)

`decodeCode i s := (decodeCodeExact i s).getD (defaultRejectCode i)` with
`decodeCode_encodeCode` (simp); `codeSize c := (encodeCode c).length` with `codeSize_eq`
and an explicit upper bound `codeSize_le` (header nat-lengths + table count × per-entry
bound; the later `|𝒱| ≤ λ` arithmetic consumes this). Tests, all `by decide`: encode/
decode round trips for all six Milestone B machines and `defaultRejectCode 1`; the
malformed battery — empty string, zero states, alphabet of size one, wrong table
length, out-of-range successor state, out-of-range work symbol, trailing garbage — each
pinned to `decodeCodeExact = none` **and** `decodeCode = defaultRejectCode 1`.

**Milestone C acceptance (all sorry-free):** the four theorem families
(`decode_encode`, `encode_injective`, `decode_sound`, `codeSize_eq`+`codeSize_le`)
landed; format documented normatively; every malformed string decodes totally to the
canonical default machine; all tests kernel-evaluated (no `native_decide`).

---

## Verification (every WP; CI-equivalent locally)

```bash
lake build                    # green; no warnings beyond the pre-existing Foundations sorries
lake exe mk_all               # then commit the regenerated MIPRE.lean
```

- `grep -rn "sorry" MIPRE/TM MIPRE/Cslib` → empty.
- `grep -rn "noncomputable\|Fintype.elems" MIPRE/TM` → empty (D5; note Milestone A/B never
  needs `Polynomial ℕ`, so nothing here is forced noncomputable).
- WP1: adaptation-only diff against the pinned upstream sources.
- WP6: all `example := by decide` pins compile; every `#eval` in `Examples.lean` runs.
- Optional spot check: `#print axioms` on one example-machine evaluation to observe the
  data path (classical axioms appearing via *proof* terms are acceptable per D5).

## Risks and mitigations

1. **Vendored proofs vs Mathlib v4.32.0 drift** — contained to WP1; repair minimally and log
   in the provenance block.
2. **Dependent `Fin`/`Array` proof-threading in WP5/6** — confined by design to
   `Code.actionAt*`; total-clamping fallback recorded in WP6.
3. **Kernel `decide` performance on `ℤ`-indexed tape functions** — machines are tiny; fall
   back to `#eval` pins, never `native_decide`.
4. **Upstream CSLib drift while vendored** — SHA pinned here; un-vendor at the next
   toolchain alignment (Lean v4.33.0 stable).
5. **Interpreter duplication at Milestone E/F** — blocked by the explicit gate in the
   Roadmap; decision to be recorded in this file.

## Progress checklist

- [x] **WP1** vendor CSLib (3 files) + commit `planning/tm-infrastructure.md` (2026-08-05)
- [x] **WP2** `MultiInput/Deterministic.lean` + `MultiInput/TapeLemmas.lean` (2026-08-05; note: `moveInputPos` lives in the `MultiTapeTM` namespace, reused via selective `open`; `TransitionOut` is namespaced as `MultiInputTM.TransitionOut` to avoid clashing with the vendored `Turing.TransitionOut`)
- [x] **WP3** `MultiInput/Complexity.lean` + `MultiInput/OneInputEquiv.lean` → **Milestone A done** (2026-08-05; all acceptance theorems proved, incl. `toCSLib_computesInTimeAndSpace` and both round trips — `toCSLib_ofCSLib` is `rfl`)
- [x] **WP3b** `MultiInput/Congr.lean` — relabeling along `State ≃ State'` / `Symbol ≃ Symbol'` transporting `step`/`configs`/`outputString`/`spaceUsed`/`ComputesInTimeAndSpace`; ported from crei/cslib `finite_in_fin:Regular.lean` (see Fork findings; Equiv-based and computable, unlike the fork's) (2026-08-05)
- [x] **WP4** `Code/Raw.lean` + `Code/Observation.lean` (2026-08-05; both inverse laws proved at all three levels: symbols, observations, transition indices)
- [x] **WP5** `Code/WellFormed.lean` (incl. `actionAt` layer) (2026-08-05; `WellFormed` is `Decidable` through `wellFormedB`, so literal codes certify by `decide`)
- [x] **WP6** `Code/Semantics.lean` + `Code/Examples.lean` → **Milestone B done** (2026-08-05.
  Notes: `wellFormedB`'s table loops were switched to `List.all` over `toList` — `Array.all`
  does not kernel-reduce on v4.32.0, `List.all` does, and literals now certify by `decide`;
  the 100-step `loopForever` pins need a local `set_option maxRecDepth 4000`; axiom spot
  check: `Code.toTM` and the example machines depend only on `propext` and `Quot.sound` —
  not even `Classical.choice` appears in the data path.)
- [ ] **WP7** `Code/Encoding/Nat.lean` — self-delimiting nat codec
- [ ] **WP8** `Code/Encoding/MachineCode.lean` — machine serialization + exact decoder
- [ ] **WP9** `Code/Encoding/Total.lean` — total decode, `codeSize`, test battery → **Milestone C done**
- [ ] Roadmap statuses updated; E/F interpreter-ownership decision recorded when taken

Each WP is one commit on `turing-machines` (mergeable as its own PR if the FLT-style
issue/PR workflow is wanted for these), updating this checklist in the same commit.
