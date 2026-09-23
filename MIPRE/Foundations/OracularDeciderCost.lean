/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.OracularDecider

/-!
# The running times of the typed oracularized decider

Piece O4b of `planning/oracularization.md` (issue #189): the two running times of the typed
oracularized decider of `Foundations/OracularDecider.lean`.

* **The core's**, on well-formed inputs, in terms of the input verifier's time bounds at the index
  (`core_timeBound`). It is what the simulation budget must cover for completeness
  (`OracleDecider.accepts_complete`). The sizes of the intermediate results matter here: the
  input sampler's answer to a marginal query is read off its correctness clause, a vector of
  length `s(n)`, and not off its running time — otherwise the input decider's time, polynomial of
  degree `k` in its input, would compound into degree `k²`.
* **The decider's**, on every input, in terms of the budget, the parse cut and the index
  routine's running time (`oracleDecider_timeBound`): the clocked universal machine's overhead
  and nothing of the input verifier, whose time enters only through the budget.
-/

namespace MIPRE

open Cost Cost.PolyTimeFun

namespace OracleDecider

open CL CL.Detyping.Program

/-! ## Sizes -/

theorem size_marginal_le (w : Player) (j : ℕ) (z : BitStr) :
    esize (Sampler.Query.marginal w j z) ≤ esize z + esize j + 13 := by
  have h1 : esize (1 : ℕ) ≤ 5 := by
    have := esize_nat_le 1
    simpa using this
  have hw : esize w ≤ 3 := by cases w <;> decide
  have he : esize (Sampler.Query.marginal w j z) =
      esize (1 : ℕ) + esize w + esize j + esize z + esize ([] : BitStr) + 4 := by
    change esize (Sampler.Query.marginal w j z).toTuple = _
    simp only [Sampler.Query.toTuple, esize_prod]
    ring
  have hn : esize ([] : BitStr) = 1 := rfl
  omega

theorem size_gInput (sp dp : Prog) (n : ℕ) (z a₁ a₂ : BitStr) :
    (gInput sp dp n z a₁ a₂).size =
      esize sp + esize dp + esize n + esize z + esize a₁ + esize a₂ + 5 := by
  simp only [gInput, Data.size_cons, encode_prod, esize]
  omega

/-! ## The game check's running time -/

section Game

variable {ℓ : ℕ} (S : Sampler ℓ)

/-- The cost of the game check at level `j` on an input of size at most `G`, when the input
sampler runs within `TS (|d| + 1)^k` and the input decider within `TD (|d| + 1)^k`. -/
noncomputable def gameCost (j G TS TD k : ℕ) : ℕ :=
  let A := G + esize j + 15
  let R := 4 * G + 1
  let tU := selfUniversal.bound.eval (A + TS * (G + esize j + 15) ^ k)
  let S₁ := G + R + 1
  let S₂ := S₁ + R + 1
  let tUD := selfUniversal.bound.eval (G + 2 * R + 5 + TD * (G + 2 * R + 4) ^ k)
  ((gRoute₁ j).timeBound.eval G + 3 * A + 3 * G + R + tU + treePair.timeBound.eval (G + R + 1) +
      18) +
    ((gRoute₂ j).timeBound.eval S₁ + 3 * A + 3 * S₁ + R + tU +
      treePair.timeBound.eval (S₁ + R + 1) + 18) +
    (gRoute₃.timeBound.eval S₂ + 3 * (G + 2 * R + 5) + 3 + tUD + tUD +
      CL.Detyping.DeciderProgram.post.timeBound.eval (tUD + 2) + 18) + 2

/-- A marginal call through the universal machine, with its cost and the size of its answer. -/
theorem univ_marginal_within (n TS k : ℕ) (hS : S.TimeBoundAt n TS k) (j : ℕ) (hj₁ : 1 ≤ j)
    (hj : j ≤ ℓ) (w : Player) (z : BitStr) (hz : z.length = S.dim n) :
    ∃ t ≤ selfUniversal.bound.eval (esize S.prog + esize n + esize z + esize j + 14 +
        TS * (esize z + esize j + 14) ^ k),
      selfUniversal.univ.Runs (.cons (encode S.prog) (encode (n, Sampler.Query.marginal w j z)))
        (encode (margBits S n j w z)) t := by
  obtain ⟨r, tS, htS, hr⟩ := hS (encode (Sampler.Query.marginal w j z))
  obtain ⟨t', ht'⟩ := S.runs_marginal n w j z hj₁ hj hz
  have he := (Eval.deterministic hr ht').1
  subst he
  obtain ⟨tU, htU, hU⟩ := selfUniversal.time_le _ _ _ _ hr
  have hm := size_marginal_le w j z
  refine ⟨tU, htU.trans (polynomial_eval_mono _ ?_), hU⟩
  have hTS : tS ≤ TS * (esize z + esize j + 14) ^ k :=
    htS.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      change esize (Sampler.Query.marginal w j z) + 1 ≤ _; omega) _))
  simp only [esize, Data.size_cons] at hm hTS ⊢
  omega

/-- The answer to a marginal query is a vector of the seed's length. -/
theorem size_margBits_le (n j : ℕ) (w : Player) (z : BitStr) (hz : z.length = S.dim n) :
    esize (margBits S n j w z) ≤ 4 * esize z + 1 := by
  have h1 := esize_bitStr_le (margBits S n j w z)
  have h2 : (margBits S n j w z).length = z.length := by simp [margBits, hz]
  have h3 := length_le_esize_bitStr z
  omega

/-- **The game check's running time** on a well-formed seed. -/
theorem gameProg_runs_within (dp : Prog) (n TS TD k : ℕ) (hS : S.TimeBoundAt n TS k)
    (hD : ∀ d, HaltsWithin dp (.cons (encode n) d) (TD * (d.size + 1) ^ k)) (j : ℕ)
    (hj₁ : 1 ≤ j) (hj : j ≤ ℓ) (z a₁ a₂ : BitStr) (hz : z.length = S.dim n) {G : ℕ}
    (hG : (gInput S.prog dp n z a₁ a₂).size ≤ G) :
    ∃ (v : Bool) (t : ℕ), (gameProg j).Runs (gInput S.prog dp n z a₁ a₂) (encode v) t ∧
      t ≤ gameCost j G TS TD k := by
  have hsz := size_gInput S.prog dp n z a₁ a₂
  have hrA := size_margBits_le S n j .alice z hz
  have hrB := size_margBits_le S n j .bob z hz
  have hmA := size_marginal_le .alice j z
  have hmB := size_marginal_le .bob j z
  have hzG : esize z ≤ G := by omega
  -- the two marginal calls
  obtain ⟨tA, htA, hA⟩ := univ_marginal_within S n TS k hS j hj₁ hj .alice z hz
  obtain ⟨tB, htB, hB⟩ := univ_marginal_within S n TS k hS j hj₁ hj .bob z hz
  obtain ⟨t₁, ht₁, h₁⟩ := Prog.routeOneCall_indirect_cost (gRoute₁ j) selfUniversal.closed treePair
    _ _ _ _ tA (gRoute₁_apply j S.prog dp n z a₁ a₂) hA
  obtain ⟨t₂, ht₂, h₂⟩ := Prog.routeOneCall_indirect_cost (gRoute₂ j) selfUniversal.closed treePair
    _ _ _ _ tB (gRoute₂_apply j S.prog dp n z a₁ a₂ _) hB
  -- the decider call
  obtain ⟨rD, tD, htD, hDr⟩ := hD (.cons (encode (margBits S n j .alice z))
    (.cons (encode (margBits S n j .bob z)) (encode (a₁, a₂))))
  obtain ⟨tUD, htUD, hUD⟩ := selfUniversal.time_le _ _ _ _ hDr
  obtain ⟨t₃, ht₃, h₃⟩ := Prog.routeOneCall_indirect_cost gRoute₃ selfUniversal.closed
    CL.Detyping.DeciderProgram.post _ _ .nil rD tUD (gRoute₃_apply S.prog dp n z a₁ a₂ _ _) hUD
  refine ⟨decide (rD = encode true), _, Prog.let_closed_runs (gTail_closed j) h₁
    (Prog.let_closed_runs gStage₃_closed h₂ h₃), ?_⟩
  -- the bound, term by term
  have hrD : rD.size ≤ tUD := hUD.size_le
  simp only [Data.size_cons, Data.size_nil, encode_prod] at ht₁ ht₂ ht₃ ⊢
  simp only [Data.size_cons, encode_prod, esize] at htD htUD hrA hrB hmA hmB
  simp only [esize] at hsz hzG hrD htA htB
  have hU₁ : ∀ {t : ℕ}, t ≤ selfUniversal.bound.eval ((encode S.prog).size + (encode n).size +
      (encode z).size + (encode j).size + 14 + TS * ((encode z).size + (encode j).size + 14) ^ k) →
      t ≤ selfUniversal.bound.eval (G + (encode j).size + 15 +
        TS * (G + (encode j).size + 15) ^ k) := fun h =>
    h.trans (polynomial_eval_mono _ (Nat.add_le_add (by omega)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))))
  have hA' := hU₁ htA
  have hB' := hU₁ htB
  have hDt : tD ≤ TD * (G + 2 * (4 * G + 1) + 4) ^ k :=
    htD.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hUD' : tUD ≤ selfUniversal.bound.eval (G + 2 * (4 * G + 1) + 5 +
      TD * (G + 2 * (4 * G + 1) + 4) ^ k) :=
    htUD.trans (polynomial_eval_mono _ (by omega))
  have hR₁ := polynomial_eval_mono (gRoute₁ j).timeBound hG
  have hR₂ := polynomial_eval_mono (gRoute₂ j).timeBound
    (show (gInput S.prog dp n z a₁ a₂).size + (encode (margBits S n j Player.alice z)).size + 1 ≤
      G + (4 * G + 1) + 1 by omega)
  have hR₃ := polynomial_eval_mono gRoute₃.timeBound
    (show (gInput S.prog dp n z a₁ a₂).size + (encode (margBits S n j Player.alice z)).size + 1 +
      (encode (margBits S n j Player.bob z)).size + 1 ≤
      G + (4 * G + 1) + 1 + (4 * G + 1) + 1 by omega)
  have hP₁ := polynomial_eval_mono treePair.timeBound
    (show (gInput S.prog dp n z a₁ a₂).size + (encode (margBits S n j Player.alice z)).size + 1 ≤
      G + (4 * G + 1) + 1 by omega)
  have hP₂ := polynomial_eval_mono treePair.timeBound
    (show (gInput S.prog dp n z a₁ a₂).size + (encode (margBits S n j Player.alice z)).size + 1 +
      (encode (margBits S n j Player.bob z)).size + 1 ≤
      G + (4 * G + 1) + 1 + (4 * G + 1) + 1 by omega)
  have hQ := polynomial_eval_mono CL.Detyping.DeciderProgram.post.timeBound
    (show 1 + rD.size + 1 ≤ selfUniversal.bound.eval (G + 2 * (4 * G + 1) + 5 +
      TD * (G + 2 * (4 * G + 1) + 4) ^ k) + 2 by omega)
  simp only [gameCost, esize]
  omega

end Game

/-! ## The core's running time -/

section CoreCost

/-- An affine function of `X ≥ 2` is below a power of `X`. -/
theorem affine_le_pow {X a b : ℕ} (hX : 2 ≤ X) : a * X + b ≤ X ^ (a + b) := by
  rcases Nat.eq_zero_or_pos (a + b) with h | h
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    simp
  · obtain ⟨q, hq⟩ : ∃ q, a + b = q + 1 := ⟨a + b - 1, by omega⟩
    rw [hq, pow_succ]
    have h1 : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
    have h2 : 2 ^ q ≤ X ^ q := Nat.pow_le_pow_left hX q
    calc a * X + b ≤ (q + 1) * X := by nlinarith
      _ ≤ X ^ q * X := Nat.mul_le_mul_right _ (h1.trans h2)

variable (sp dp : Prog) (B n : ℕ) (t : Role) (x : BitStr) (u : Role) (y a b : BitStr)

theorem size_cInput : (cInput sp dp B n t x u y a b).size =
    esize sp + esize dp + esize B + esize n + esize t + esize x + esize u + esize y + esize a +
      esize b + 9 := by
  simp only [cInput, encode_prod, Data.size_cons, esize]
  omega

/-- When the first game check is called, it is called on a game check's input. -/
theorem arg₁_of_cond (h : cond₁ (cInput sp dp B n t x u y a b) = true) :
    ∃ a₁ a₂, arg₁ (PolyTimeFun.id Data (cInput sp dp B n t x u y a b)) =
      gInput sp dp n x a₁ a₂ := by
  have hA := okAns_spec cT cA cB (cInput sp dp B n t x u y a b) t a (cT_cInput ..) (cA_cInput ..)
  rw [cB_cInput] at hA
  simp only [cond₁, andB_apply, Bool.and_eq_true, isOracle, eqD_apply, const_apply, cT_cInput,
    decide_eq_true_eq, encode_injective.eq_iff, okA] at h
  obtain ⟨rfl, hok⟩ := h
  obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (hA.1.mp hok)
  have hs := shapeOk_of_parseAns hU
  rcases U with ⟨a₁, a₂⟩ | ⟨a'⟩
  · refine ⟨a₁.1, a₂.1, ?_⟩
    have hr := hA.2 _ hU
    simp only [id_apply, arg₁, gArg, ap₂_apply, treePair_apply, cSp_cInput, cDp_cInput, cN_cInput,
      cX_cInput, repA, hr, ansData, gInput, encode_prod]
  · simp [SeededGame.shapeOk] at hs

/-- When the second game check is called, it is called on a game check's input. -/
theorem arg₂_of_cond (h : cond₂ (cInput sp dp B n t x u y a b) = true) (v : Data) :
    ∃ b₁ b₂, arg₂ (treeHead (.cons (cInput sp dp B n t x u y a b) v)) =
      gInput sp dp n y b₁ b₂ := by
  have hB := okAns_spec cU cBb cB (cInput sp dp B n t x u y a b) u b (cU_cInput ..)
    (cBb_cInput ..)
  rw [cB_cInput] at hB
  simp only [cond₂, andB_apply, Bool.and_eq_true, isOracle, eqD_apply, const_apply, cU_cInput,
    decide_eq_true_eq, encode_injective.eq_iff, okB] at h
  obtain ⟨rfl, hok⟩ := h
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp (hB.1.mp hok)
  have hs := shapeOk_of_parseAns hW
  rcases W with ⟨b₁, b₂⟩ | ⟨b'⟩
  · refine ⟨b₁.1, b₂.1, ?_⟩
    have hr := hB.2 _ hW
    simp only [treeHead_cons, arg₂, gArg, ap₂_apply, treePair_apply, cSp_cInput, cDp_cInput,
      cN_cInput, cY_cInput, repB, hr, ansData, gInput, encode_prod]
  · simp [SeededGame.shapeOk] at hs

theorem size_repA_le : (repA (cInput sp dp B n t x u y a b)).size ≤ esize a := by
  have hp := Data.size_parse_le a
  have hl := length_le_esize_bitStr a
  have h1 : 1 ≤ esize a := Data.size_pos _
  simp only [repA, reprAns, PolyTimeFun.ite_apply, treeOf, comp_apply, cA_cInput, readBits_encode,
    parseF_apply]
  split_ifs
  · omega
  · exact le_rfl

theorem size_repB_le : (repB (cInput sp dp B n t x u y a b)).size ≤ esize b := by
  have hp := Data.size_parse_le b
  have hl := length_le_esize_bitStr b
  have h1 : 1 ≤ esize b := Data.size_pos _
  simp only [repB, reprAns, PolyTimeFun.ite_apply, treeOf, comp_apply, cBb_cInput, readBits_encode,
    parseF_apply]
  split_ifs
  · omega
  · exact le_rfl

theorem size_arg₁_le : (arg₁ (PolyTimeFun.id Data (cInput sp dp B n t x u y a b))).size ≤
    (cInput sp dp B n t x u y a b).size := by
  have h := size_repA_le sp dp B n t x u y a b
  have hsz := size_cInput sp dp B n t x u y a b
  simp only [id_apply, arg₁, gArg, ap₂_apply, treePair_apply, cSp_cInput, cDp_cInput, cN_cInput,
    cX_cInput, Data.size_cons] at h ⊢
  simp only [esize] at hsz h ⊢
  omega

theorem size_arg₂_le (v : Data) : (arg₂ (treeHead (.cons (cInput sp dp B n t x u y a b) v))).size ≤
    (cInput sp dp B n t x u y a b).size := by
  have h := size_repB_le sp dp B n t x u y a b
  have hsz := size_cInput sp dp B n t x u y a b
  simp only [treeHead_cons, arg₂, gArg, ap₂_apply, treePair_apply, cSp_cInput, cDp_cInput,
    cN_cInput, cY_cInput, Data.size_cons] at h ⊢
  simp only [esize] at hsz h ⊢
  omega

end CoreCost

theorem size_encode_bool_le (v : Bool) : (encode v : Data).size ≤ 3 := by
  cases v <;> decide

/-- **A routed game check's running time**, both when it calls and when it does not. -/
theorem gameStage_runs_within (j : ℕ) (cond : PolyTimeFun Data Bool)
    (arg view : PolyTimeFun Data Data)
    (s : Data) {A Sz tG : ℕ} (hs : s.size ≤ Sz) (harg : (arg (view s)).size ≤ A)
    (hcall : cond (view s) = true →
      ∃ (v : Bool) (t : ℕ), (gameProg j).Runs (arg (view s)) (encode v) t ∧ t ≤ tG) :
    ∃ (v : Bool) (t : ℕ), (gameStage j cond arg view).Runs s (.cons s (encode v)) t ∧
      t ≤ (gameRoute cond arg view).timeBound.eval Sz + 3 * A + 3 * Sz + 3 + tG +
        treePair.timeBound.eval (Sz + 4) + 18 + (Sz + 8) := by
  have hR := polynomial_eval_mono (gameRoute cond arg view).timeBound hs
  cases hc : cond (view s)
  · obtain ⟨t, ht, h⟩ := Prog.routeOneCall_direct_cost (gameRoute cond arg view) (gameProg j)
      treePair s (.cons s (encode true)) (by simp [gameRoute, hc])
    refine ⟨true, t, h, ?_⟩
    have h3 := size_encode_bool_le true
    simp only [Data.size_cons] at ht
    omega
  · obtain ⟨v, tv, hv, htv⟩ := hcall hc
    obtain ⟨t, ht, h⟩ := Prog.routeOneCall_indirect_cost (gameRoute cond arg view)
      (gameProg_closed j) treePair s (arg (view s)) s (encode v) tv
      (by simp [gameRoute, hc]) hv
    refine ⟨v, t, h, ?_⟩
    have h3 := size_encode_bool_le v
    have hP := polynomial_eval_mono treePair.timeBound
      (show s.size + (encode v : Data).size + 1 ≤ Sz + 4 by omega)
    omega

/-- The cost of the core at level `j` on an input of size `S₀`. -/
noncomputable def coreCost (j S₀ TS TD k : ℕ) : ℕ :=
  let tG := gameCost j S₀ TS TD k
  ((gameRoute cond₁ arg₁ (PolyTimeFun.id Data)).timeBound.eval S₀ + 3 * S₀ + 3 * S₀ + 3 + tG +
      treePair.timeBound.eval (S₀ + 4) + 18 + (S₀ + 8)) +
    ((gameRoute cond₂ arg₂ treeHead).timeBound.eval (S₀ + 4) + 3 * S₀ + 3 * (S₀ + 4) + 3 + tG +
      treePair.timeBound.eval (S₀ + 4 + 4) + 18 + (S₀ + 4 + 8)) +
    verdict.timeBound.eval (S₀ + 8) + 2

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

/-- **The core's running time** on a well-formed input, when the input verifier's sampler and
decider run within `TS (|d| + 1)^k` and `TD (|d| + 1)^k` at the index. -/
theorem core_runs_within (B n TS TD k : ℕ) (hS : V.sampler.TimeBoundAt n TS k)
    (hD : V.decider.TimeBoundAt n TD k) (t u : Role) (x y : V.Questions n) (a b : BitStr) :
    ∃ r time, (core (ℓ + 1)).Runs
      (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b) r time ∧
      time ≤ coreCost (ℓ + 1)
        (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b).size TS TD k := by
  set S₀ := (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b).size with hS₀
  have hcall : ∀ z a₁ a₂, z = toBits x ∨ z = toBits y →
      (gInput V.sampler.prog V.decider.prog n z a₁ a₂).size ≤ S₀ →
      ∃ (v : Bool) (t' : ℕ),
        (gameProg (ℓ + 1)).Runs (gInput V.sampler.prog V.decider.prog n z a₁ a₂) (encode v) t' ∧
          t' ≤ gameCost (ℓ + 1) S₀ TS TD k := by
    intro z a₁ a₂ hz hG
    have hzl : z.length = V.sampler.dim n := by rcases hz with rfl | rfl <;> exact length_toBits _
    exact gameProg_runs_within V.sampler V.decider.prog n TS TD k hS hD (ℓ + 1) (by omega) le_rfl
      z a₁ a₂ hzl hG
  obtain ⟨v₁, t₁, h₁, ht₁⟩ := gameStage_runs_within (ℓ + 1) cond₁ arg₁ (PolyTimeFun.id Data)
    (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b)
    (A := S₀) (Sz := S₀) (tG := gameCost (ℓ + 1) S₀ TS TD k) le_rfl
    (size_arg₁_le _ _ _ _ _ _ _ _ _ _) (fun hc => by
      obtain ⟨a₁, a₂, he⟩ := arg₁_of_cond _ _ _ _ _ _ _ _ _ _ hc
      rw [he]
      exact hcall _ a₁ a₂ (Or.inl rfl) (he ▸ size_arg₁_le _ _ _ _ _ _ _ _ _ _))
  obtain ⟨v₂, t₂, h₂, ht₂⟩ := gameStage_runs_within (ℓ + 1) cond₂ arg₂ treeHead
    (.cons (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b) (encode v₁))
    (A := S₀) (Sz := S₀ + 4) (tG := gameCost (ℓ + 1) S₀ TS TD k)
    (by have := size_encode_bool_le v₁; simp only [Data.size_cons]; omega)
    (size_arg₂_le _ _ _ _ _ _ _ _ _ _ _) (fun hc => by
      have hc' : cond₂ (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b) =
          true := by simpa using hc
      obtain ⟨b₁, b₂, he⟩ := arg₂_of_cond _ _ _ _ _ _ _ _ _ _ hc' (encode v₁)
      rw [he]
      exact hcall _ b₁ b₂ (Or.inr rfl) (he ▸ size_arg₂_le _ _ _ _ _ _ _ _ _ _ _))
  obtain ⟨tv, htv, hv⟩ := verdict.computes (.cons (.cons
    (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b) (encode v₁))
    (encode v₂))
  refine ⟨_, _, Prog.let_closed_runs (coreTail_closed _) h₁
    (Prog.let_closed_runs verdict.closed h₂ hv), ?_⟩
  have hV := polynomial_eval_mono verdict.timeBound
    (show esize (Data.cons (.cons (cInput V.sampler.prog V.decider.prog B n t (toBits x) u
      (toBits y) a b) (encode v₁)) (encode v₂)) ≤ S₀ + 8 by
      have := size_encode_bool_le v₁
      have := size_encode_bool_le v₂
      simp only [esize_data, Data.size_cons]
      omega)
  simp only [coreCost]
  omega

/-! ## Domination -/

open Repeat (Dom)

/-- `TS · G^K`, for `TS ≤ W` and `G` affine in `X ≥ 2`. -/
theorem dom_mul_pow {W X K TS G a b : ℕ} (hX : 2 ≤ X) (hTS : TS ≤ W) (hG : G ≤ a * X + b) :
    Dom W X K 1 1 (a + b) (TS * G ^ K) := by
  unfold Dom
  have h1 : G ^ K ≤ X ^ ((a + b) * (K + 1)) := by
    calc G ^ K ≤ (X ^ (a + b)) ^ K := Nat.pow_le_pow_left (hG.trans (affine_le_pow hX)) K
      _ = X ^ ((a + b) * K) := by rw [← pow_mul]
      _ ≤ X ^ ((a + b) * (K + 1)) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega))
  calc TS * G ^ K ≤ (W + 1) * X ^ ((a + b) * (K + 1)) := Nat.mul_le_mul (by omega) h1
    _ = 1 * (W + 1) ^ 1 * X ^ ((a + b) * (K + 1)) := by ring

/-- A polynomial at a dominated argument. -/
theorem dom_poly (Q : Polynomial ℕ) (cy my ey : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X →
    1 ≤ y → Dom W X K cy my ey y → Dom W X K c m e (Q.eval y) :=
  ⟨_, _, _, fun _ _ _ {_} _ hy h =>
    ((Dom.const _).mul (h.pow Q.natDegree)).of_le (polynomial_eval_le_sum_coeff_mul_pow Q hy)⟩

/-- The polynomials of the game check. -/
noncomputable def gamePoly (j : ℕ) : Polynomial ℕ :=
  (gRoute₁ j).timeBound + (gRoute₂ j).timeBound + gRoute₃.timeBound + treePair.timeBound +
    selfUniversal.bound

/-- The one argument dominating every argument of a polynomial in `gameCost`. -/
def gameArgBound (j G TS TD K : ℕ) : ℕ :=
  9 * G + esize j + 30 + TS * (G + esize j + 15) ^ K + TD * (G + 2 * (4 * G + 1) + 4) ^ K

theorem gameCost_le (j G TS TD K : ℕ) :
    gameCost j G TS TD K ≤ 9 * (gamePoly j).eval (gameArgBound j G TS TD K) +
      CL.Detyping.DeciderProgram.post.timeBound.eval ((gamePoly j).eval
        (gameArgBound j G TS TD K) + 2) + 23 * gameArgBound j G TS TD K + 74 := by
  set M := gameArgBound j G TS TD K with hM
  have hQ : ∀ (P : Polynomial ℕ) (y : ℕ), y ≤ M → P.eval y ≤ P.eval M :=
    fun P y h => polynomial_eval_mono P h
  have hsum : ∀ y ≤ M, (gRoute₁ j).timeBound.eval y + (gRoute₂ j).timeBound.eval y +
      gRoute₃.timeBound.eval y + treePair.timeBound.eval y + selfUniversal.bound.eval y ≤
      (gamePoly j).eval M := fun y h => by
    have := polynomial_eval_mono (gamePoly j) h
    simp only [gamePoly, Polynomial.eval_add] at this ⊢
    exact this
  have hM' := hsum M le_rfl
  have hA := hQ (gRoute₁ j).timeBound G (by rw [hM]; unfold gameArgBound; omega)
  have hB := hQ (gRoute₂ j).timeBound (G + (4 * G + 1) + 1) (by rw [hM]; unfold gameArgBound; omega)
  have hC := hQ gRoute₃.timeBound (G + (4 * G + 1) + 1 + (4 * G + 1) + 1)
    (by rw [hM]; unfold gameArgBound; omega)
  have hP₁ := hQ treePair.timeBound (G + (4 * G + 1) + 1) (by rw [hM]; unfold gameArgBound; omega)
  have hP₂ := hQ treePair.timeBound (G + (4 * G + 1) + 1 + (4 * G + 1) + 1)
    (by rw [hM]; unfold gameArgBound; omega)
  have hU := hQ selfUniversal.bound (G + esize j + 15 + TS * (G + esize j + 15) ^ K)
    (by rw [hM]; unfold gameArgBound; omega)
  have hUD := hQ selfUniversal.bound (G + 2 * (4 * G + 1) + 5 + TD * (G + 2 * (4 * G + 1) + 4) ^ K)
    (by rw [hM]; unfold gameArgBound; omega)
  have hpost := polynomial_eval_mono CL.Detyping.DeciderProgram.post.timeBound
    (show selfUniversal.bound.eval (G + 2 * (4 * G + 1) + 5 + TD * (G + 2 * (4 * G + 1) + 4) ^ K) +
      2 ≤ (gamePoly j).eval M + 2 by omega)
  have hG : 9 * G + esize j + 30 ≤ M := by rw [hM]; unfold gameArgBound; omega
  simp only [gameCost]
  omega

/-- **The game check's cost, dominated.** -/
theorem dom_gameCost (j : ℕ) : ∃ c m e, ∀ (W X K G TS TD : ℕ), 2 ≤ X → G ≤ X → TS ≤ W →
    TD ≤ W → Dom W X K c m e (gameCost j G TS TD K) := by
  have dom_arg : ∃ c m e, ∀ (W X K G TS TD : ℕ), 2 ≤ X → G ≤ X → TS ≤ W → TD ≤ W →
      Dom W X K c m e (gameArgBound j G TS TD K) := ⟨_, _, _, fun W X K G TS TD hX hG hTS hTD =>
    (((Dom.ofAffineX (a := 9) (b := esize j + 30) (by omega) (by omega)).add (by omega)
      (dom_mul_pow (a := 1) (b := esize j + 15) hX hTS (by omega))).add (by omega)
      (dom_mul_pow (a := 9) (b := 6) hX hTD (by omega)))⟩
  obtain ⟨cM, mM, eM, hM⟩ := dom_arg
  obtain ⟨cQ, mQ, eQ, hQ⟩ := dom_poly (gamePoly j) cM mM eM
  have dom_q2 : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X → Dom W X K cQ mQ eQ y →
      Dom W X K c m e (y + 2) := ⟨_, _, _, fun W X K {y} hX h => h.add hX (Dom.const 2)⟩
  obtain ⟨c2, m2, e2, h2⟩ := dom_q2
  obtain ⟨cP, mP, eP, hP⟩ := dom_poly CL.Detyping.DeciderProgram.post.timeBound c2 m2 e2
  exact ⟨_, _, _, fun W X K G TS TD hX hG hTS hTD => by
    have hX1 : 1 ≤ X := by omega
    have hm := hM W X K G TS TD hX hG hTS hTD
    have hm1 : 1 ≤ gameArgBound j G TS TD K := by unfold gameArgBound; omega
    have hq := hQ W X K hX1 hm1 hm
    have hp := hP W X K hX1 (by omega) (h2 W X K hX1 hq)
    exact ((((Dom.const 9).mul hq).add hX1 hp).add hX1 ((Dom.const 23).mul hm)).add hX1
      (Dom.const 74) |>.of_le (gameCost_le j G TS TD K)⟩

/-- The polynomials of the core. -/
noncomputable def corePoly : Polynomial ℕ :=
  (gameRoute cond₁ arg₁ (PolyTimeFun.id Data)).timeBound +
    (gameRoute cond₂ arg₂ treeHead).timeBound + treePair.timeBound + verdict.timeBound

theorem coreCost_le (j S₀ TS TD K : ℕ) :
    coreCost j S₀ TS TD K ≤
      2 * gameCost j S₀ TS TD K + 5 * corePoly.eval (S₀ + 8) + 14 * S₀ + 76 := by
  have hsum : ∀ y ≤ S₀ + 8, (gameRoute cond₁ arg₁ (PolyTimeFun.id Data)).timeBound.eval y +
      (gameRoute cond₂ arg₂ treeHead).timeBound.eval y + treePair.timeBound.eval y +
      verdict.timeBound.eval y ≤ corePoly.eval (S₀ + 8) := fun y h => by
    have := polynomial_eval_mono corePoly h
    simp only [corePoly, Polynomial.eval_add] at this ⊢
    exact this
  have h₁ := hsum S₀ (by omega)
  have h₂ := hsum (S₀ + 4) (by omega)
  have h₃ := hsum (S₀ + 4 + 4) (by omega)
  have h₄ := hsum (S₀ + 8) le_rfl
  simp only [coreCost]
  omega

/-- **The core's cost, dominated.** -/
theorem dom_coreCost (j : ℕ) : ∃ c m e, ∀ (W X K S₀ TS TD : ℕ), 2 ≤ X → S₀ + 1 = X → TS ≤ W →
    TD ≤ W → Dom W X K c m e (coreCost j S₀ TS TD K) := by
  obtain ⟨cG, mG, eG, hG⟩ := dom_gameCost j
  obtain ⟨cQ, mQ, eQ, hQ⟩ := dom_poly corePoly 8 0 1
  exact ⟨_, _, _, fun W X K S₀ TS TD hX hS₀ hTS hTD => by
    have hX1 : 1 ≤ X := by omega
    have hg := hG W X K S₀ TS TD hX (by omega) hTS hTD
    have h8 : Dom W X K (1 + 7) 0 1 (S₀ + 8) := Dom.ofAffineX hX1 (by omega)
    have hq := hQ W X K hX1 (by omega) h8
    have hs : Dom W X K 1 0 1 S₀ := Dom.ofLeX hX1 (by omega)
    exact ((((Dom.const 2).mul hg).add hX1 ((Dom.const 5).mul hq)).add hX1
      ((Dom.const 14).mul hs)).add hX1 (Dom.const 76) |>.of_le (coreCost_le j S₀ TS TD K)⟩

/-- **The core's running time, dominated**: on a well-formed input `c`, within
`c₀ (W + 1)^m (|c| + 1)^{e (k + 1)}` whenever the input verifier's sampler and decider run within
`TS (|d| + 1)^k` and `TD (|d| + 1)^k` at the index and `TS, TD ≤ W`. -/
theorem core_timeBound (ℓ : ℕ) : ∃ c m e, ∀ (V : Verifier (ℓ + 1)) (B n TS TD k W : ℕ),
    V.sampler.TimeBoundAt n TS k → V.decider.TimeBoundAt n TD k → TS ≤ W → TD ≤ W →
    ∀ (t u : Role) (x y : V.Questions n) (a b : BitStr), ∃ r time,
      (core (ℓ + 1)).Runs
        (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b) r time ∧
      time ≤ c * (W + 1) ^ m *
        ((cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b).size + 1) ^
          (e * (k + 1)) := by
  obtain ⟨c, m, e, h⟩ := dom_coreCost (ℓ + 1)
  refine ⟨c, m, e, fun V B n TS TD k W hS hD hTS hTD t u x y a b => ?_⟩
  obtain ⟨r, time, hr, ht⟩ := core_runs_within V B n TS TD k hS hD t u x y a b
  have h2 : 2 ≤ (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b).size + 1 :=
    by
      have := Data.size_pos
        (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b)
      omega
  exact ⟨r, time, hr, ht.trans (h W _ k _ TS TD h2 rfl hTS hTD)⟩

/-- **The budget hypothesis, discharged**: every accepting run of the core on a well-formed input
takes at most `c₀ (W + 1)^m (|c| + 1)^{e (k + 1)}`. -/
theorem core_accepting_le (ℓ : ℕ) : ∃ c m e, ∀ (V : Verifier (ℓ + 1)) (B n TS TD k W : ℕ),
    V.sampler.TimeBoundAt n TS k → V.decider.TimeBoundAt n TD k → TS ≤ W → TD ≤ W →
    ∀ (t u : Role) (x y : V.Questions n) (a b : BitStr) (time : ℕ),
      (core (ℓ + 1)).Runs (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b)
        (encode true) time →
      time ≤ c * (W + 1) ^ m *
        ((cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b).size + 1) ^
          (e * (k + 1)) := by
  obtain ⟨c, m, e, h⟩ := core_timeBound ℓ
  refine ⟨c, m, e, fun V B n TS TD k W hS hD hTS hTD t u x y a b time hrun => ?_⟩
  obtain ⟨r, time', hr, ht⟩ := h V B n TS TD k W hS hD hTS hTD t u x y a b
  rw [(Eval.deterministic hrun hr).2]
  exact ht

/-! ## The decider's running time -/

/-- The cost of the decider on `(n, d)`, with `P = |(S̄, D̄, Ī)|`, `N = |n|`, `K` the budget, `Bz`
the size of the cut, `TI` the index routine's time and `D = |d|`. -/
noncomputable def deciderCost (j P N K Bz TI D : ℕ) : ℕ :=
  let Sx := P + N + D + 2
  let r := 2 * K + Bz + 2
  let tU := selfUniversal.bound.eval (P + N + TI)
  let tC := selfClockedUniversal.bound.eval (K + esize (core j) + P + Bz + N + D + 4)
  (indexRoute.timeBound.eval Sx + 3 * (P + N + 1) + 3 * Sx + r + tU +
      (indexPost j).timeBound.eval (Sx + r + 1) + 18) +
    (tC + CL.Detyping.ClockProgram.checkResult.timeBound.eval tC + 1) + 1 + P + (N + D + 1) + 3

/-- **The decider's running time** on `(n, d)`: the index routine's, the clocked universal
machine's overhead on the budget and the input, and nothing of the input programs' behaviour. -/
theorem oracleDecider_runs_within (j : ℕ) (sp dp : Prog) (I : Index) (n : ℕ) (d : Data) {TI : ℕ}
    (hI : HaltsWithin I.prog (encode n) TI) :
    ∃ r t, (oracleDecider j sp dp I).prog.Runs (.cons (encode n) d) r t ∧
      t ≤ deciderCost j (esize (sp, dp, I.prog)) (esize n) (I.budget n) (esize (I.cut n)) TI
        d.size := by
  obtain ⟨rI, tI, htI, hrI⟩ := hI
  obtain ⟨tI', hI'⟩ := I.runs n
  have he := (Eval.deterministic hrI hI').1
  subst he
  obtain ⟨tU, htU, hU⟩ := selfUniversal.time_le _ _ _ _ hrI
  have hroute : indexRoute (.cons (encode (sp, dp, I.prog)) (.cons (encode n) d)) =
      (true, .cons (.cons (encode I.prog) (encode n))
        (.cons (encode (sp, dp, I.prog)) (.cons (encode n) d))) := by
    simp [indexRoute, sIp, sIndex, encode_prod, readNat_encode]
  obtain ⟨t₁, ht₁, h₁⟩ := Prog.routeOneCall_indirect_cost indexRoute selfUniversal.closed
    (indexPost j) _ _ _ _ tU hroute hU
  have hpost : indexPost j (.cons (encode (sp, dp, I.prog)) (.cons (encode n) d),
      .cons (.ofNat (I.budget n)) (encode (I.cut n))) =
      .cons (.ofNat (I.budget n)) (.cons (encode (core j))
        (.cons (encode (sp, dp, I.cut n)) (.cons (encode n) d))) := by
    simp [indexPost, encode_prod]
  rw [hpost] at h₁
  obtain ⟨tC, htC, hC⟩ := selfClockedUniversal.run (core j)
    (.cons (encode (sp, dp, I.cut n)) (.cons (encode n) d)) (I.budget n)
  obtain ⟨tR, htR, hR⟩ := CL.Detyping.ClockProgram.checkResult.computes
    (clockedResult (core j) (.cons (encode (sp, dp, I.cut n)) (.cons (encode n) d)) (I.budget n))
  refine ⟨_, _, hardcode_time (shell_closed j) (Prog.let_closed_runs shellTail_closed h₁
    (Prog.let_closed_runs CL.Detyping.ClockProgram.checkResult.closed hC hR)), ?_⟩
  -- the bound
  have e1 : (Data.cons (encode (sp, dp, I.prog)) (.cons (encode n) d)).size =
      esize (sp, dp, I.prog) + esize n + d.size + 2 := by
    simp only [Data.size_cons, esize]; omega
  have e2 : (Data.cons (encode I.prog) (encode n)).size = esize I.prog + esize n + 1 := rfl
  have e3 : (Data.cons (Data.ofNat (I.budget n)) (encode (I.cut n))).size =
      2 * I.budget n + esize (I.cut n) + 2 := by
    simp only [Data.size_cons, Data.size_ofNat, esize]; omega
  have e4 : (Data.cons (encode (sp, dp, I.cut n)) (.cons (encode n) d)).size =
      esize (sp, dp, I.cut n) + esize n + d.size + 2 := by
    simp only [Data.size_cons, esize]; omega
  have e5 : esize (sp, dp, I.cut n) = esize sp + esize dp + esize (I.cut n) + 2 := by
    simp only [esize_prod]; omega
  have e6 : esize (sp, dp, I.prog) = esize sp + esize dp + esize I.prog + 2 := by
    simp only [esize_prod]; omega
  have e7 : (encode (sp, dp, I.prog) : Data).size = esize (sp, dp, I.prog) := rfl
  have e8 : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
  have e9 : (encode n : Data).size = esize n := rfl
  rw [e1, e2, e3] at ht₁
  rw [e4] at htC
  rw [e9] at htU
  have hU' := polynomial_eval_mono selfUniversal.bound
    (show esize I.prog + esize n + tI ≤ esize (sp, dp, I.prog) + esize n + TI by omega)
  have hC' := polynomial_eval_mono selfClockedUniversal.bound
    (show I.budget n + esize (core j) + (esize (sp, dp, I.cut n) + esize n + d.size + 2) ≤
      I.budget n + esize (core j) + esize (sp, dp, I.prog) + esize (I.cut n) + esize n + d.size +
        4 by omega)
  have hres : esize (clockedResult (core j) (.cons (encode (sp, dp, I.cut n)) (.cons (encode n) d))
      (I.budget n)) ≤ tC := hC.size_le
  have hR' := polynomial_eval_mono CL.Detyping.ClockProgram.checkResult.timeBound
    (show esize (clockedResult (core j) (.cons (encode (sp, dp, I.cut n)) (.cons (encode n) d))
      (I.budget n)) ≤ selfClockedUniversal.bound.eval (I.budget n + esize (core j) +
        esize (sp, dp, I.prog) + esize (I.cut n) + esize n + d.size + 4) by omega)
  rw [e7, e8]
  simp only [deciderCost]
  omega

/-- The polynomials of the shell. -/
noncomputable def shellPoly (j : ℕ) : Polynomial ℕ :=
  indexRoute.timeBound + (indexPost j).timeBound + selfUniversal.bound + selfClockedUniversal.bound

/-- The one argument dominating every argument of a polynomial in `deciderCost`. -/
noncomputable def shellArgBound (j P N K Bz TI D : ℕ) : ℕ :=
  3 * K + P + Bz + N + D + TI + esize (core j) + 10

theorem deciderCost_le (j P N K Bz TI D : ℕ) :
    deciderCost j P N K Bz TI D ≤ 4 * (shellPoly j).eval (shellArgBound j P N K Bz TI D) +
      CL.Detyping.ClockProgram.checkResult.timeBound.eval
        ((shellPoly j).eval (shellArgBound j P N K Bz TI D) + 1) +
      7 * shellArgBound j P N K Bz TI D + 35 := by
  set M := shellArgBound j P N K Bz TI D with hM
  have hsum : ∀ y ≤ M, indexRoute.timeBound.eval y + (indexPost j).timeBound.eval y +
      selfUniversal.bound.eval y + selfClockedUniversal.bound.eval y ≤ (shellPoly j).eval M :=
    fun y h => by
      have := polynomial_eval_mono (shellPoly j) h
      simp only [shellPoly, Polynomial.eval_add] at this ⊢
      exact this
  have h₁ := hsum (P + N + D + 2) (by rw [hM]; unfold shellArgBound; omega)
  have h₂ := hsum (P + N + D + 2 + (2 * K + Bz + 2) + 1) (by rw [hM]; unfold shellArgBound; omega)
  have h₃ := hsum (P + N + TI) (by rw [hM]; unfold shellArgBound; omega)
  have h₄ := hsum (K + esize (core j) + P + Bz + N + D + 4)
    (by rw [hM]; unfold shellArgBound; omega)
  have hc := polynomial_eval_mono CL.Detyping.ClockProgram.checkResult.timeBound
    (show selfClockedUniversal.bound.eval (K + esize (core j) + P + Bz + N + D + 4) ≤
      (shellPoly j).eval M + 1 by omega)
  have hMge : P + N + D + K + Bz ≤ M := by rw [hM]; unfold shellArgBound; omega
  simp only [deciderCost]
  omega

/-- **The decider's running time, dominated**: on `(n, d)` within `c (W + 1)^m (|d| + 1)^e`,
whenever the budget, the cut and the index routine's time at `n`, the description lengths of the
three programs and `n` are at most `W`. The degree `e` is fixed: the input verifier's degree
enters only through the budget. -/
theorem oracleDecider_timeBound (j : ℕ) : ∃ c m e, ∀ (sp dp : Prog) (I : Index) (n TI W : ℕ),
    HaltsWithin I.prog (encode n) TI → esize sp ≤ W → esize dp ≤ W → esize I.prog ≤ W →
    n ≤ W → I.budget n ≤ W → I.cut n ≤ W → TI ≤ W → ∀ d : Data,
      HaltsWithin (oracleDecider j sp dp I).prog (.cons (encode n) d)
        (c * (W + 1) ^ m * (d.size + 1) ^ e) := by
  have dom_arg : ∃ c m e, ∀ (W X P N K Bz TI D : ℕ), 1 ≤ X → P ≤ 3 * W + 2 → N ≤ 4 * W + 1 →
      K ≤ W → Bz ≤ 4 * W + 1 → TI ≤ W → D ≤ X →
      Dom W X 0 c m e (shellArgBound j P N K Bz TI D) :=
    ⟨_, _, _, fun W X P N K Bz TI D hX hP hN hK hB hT hD =>
      ((Dom.ofAffine (a := 15) (b := esize (core j) + 14) (v := 3 * K + P + Bz + N + TI +
        esize (core j) + 10) (by omega)).add hX (Dom.ofLeX hX hD)).of_le
        (by unfold shellArgBound; omega)⟩
  obtain ⟨cM, mM, eM, hM⟩ := dom_arg
  obtain ⟨cQ, mQ, eQ, hQ⟩ := dom_poly (shellPoly j) cM mM eM
  have dom_q1 : ∃ c m e, ∀ (W X : ℕ) {y : ℕ}, 1 ≤ X → Dom W X 0 cQ mQ eQ y →
      Dom W X 0 c m e (y + 1) := ⟨_, _, _, fun W X {y} hX h => h.add hX (Dom.const 1)⟩
  obtain ⟨c1, m1, e1, h1⟩ := dom_q1
  obtain ⟨cR, mR, eR, hR⟩ := dom_poly CL.Detyping.ClockProgram.checkResult.timeBound c1 m1 e1
  exact ⟨_, _, _, fun sp dp I n TI W hI hsp hdp hip hn hK hB hTI d => by
    obtain ⟨r, t, hrun, ht⟩ := oracleDecider_runs_within j sp dp I n d hI
    have hX : 1 ≤ d.size + 1 := by omega
    have hP : esize (sp, dp, I.prog) ≤ 3 * W + 2 := by simp only [esize_prod]; omega
    have hN : esize n ≤ 4 * W + 1 := (Repeat.esize_nat_le' n).trans (by omega)
    have hBz : esize (I.cut n) ≤ 4 * W + 1 := (Repeat.esize_nat_le' _).trans (by omega)
    have hm := hM W (d.size + 1) (esize (sp, dp, I.prog)) (esize n) (I.budget n)
      (esize (I.cut n)) TI d.size hX hP hN hK hBz hTI (by omega)
    have hm1 : 1 ≤ shellArgBound j (esize (sp, dp, I.prog)) (esize n) (I.budget n)
        (esize (I.cut n)) TI d.size := by unfold shellArgBound; omega
    have hq := hQ W (d.size + 1) 0 (y := shellArgBound j (esize (sp, dp, I.prog)) (esize n)
      (I.budget n) (esize (I.cut n)) TI d.size) hX hm1 hm
    have hr := hR W (d.size + 1) 0 hX (by omega) (h1 W (d.size + 1) hX hq)
    have htot := ((((Dom.const 4).mul hq).add hX hr).add hX ((Dom.const 7).mul hm)).add hX
      (Dom.const 35) |>.of_le (deciderCost_le j _ _ _ _ _ _)
    exact ⟨r, t, ht.trans htot.le, hrun⟩⟩

/-! ## Completeness at an explicit budget -/

theorem esize_role_le (r : Role) : esize r ≤ 7 := by
  cases r <;> decide

/-- The size of the core's input on answers within the inner cut. -/
def coreInputBound (V : Verifier (ℓ + 1)) (B n T : ℕ) : ℕ :=
  esize V.sampler.prog + esize V.decider.prog + esize B + esize n + 8 * V.sampler.dim n + 8 * T + 27

theorem size_cInput_le (B n T : ℕ) (t u : Role) (x y : V.Questions n) (a b : BitStr)
    (ha : a.length ≤ T) (hb : b.length ≤ T) :
    (cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b).size ≤
      coreInputBound V B n T := by
  have h := size_cInput V.sampler.prog V.decider.prog B n t (toBits x) u (toBits y) a b
  have ht := esize_role_le t
  have hu := esize_role_le u
  have hx := esize_bitStr_le (toBits x)
  have hy := esize_bitStr_le (toBits y)
  have ha' := esize_bitStr_le a
  have hb' := esize_bitStr_le b
  simp only [length_toBits] at hx hy
  unfold coreInputBound
  omega

/-- **The budget hypothesis at an explicit budget**: every accepting run of the core on answers
within the inner cut fits in any budget above `c (W + 1)^m (Z + 1)^{e (k + 1)}`, `Z` the bound on
the core's input. -/
theorem budget_sufficient (ℓ : ℕ) : ∃ c m e, ∀ (V : Verifier (ℓ + 1)) (I : Index)
    (T n TS TD k W : ℕ),
    V.sampler.TimeBoundAt n TS k → V.decider.TimeBoundAt n TD k → TS ≤ W → TD ≤ W →
    c * (W + 1) ^ m * (coreInputBound V (I.cut n) n T + 1) ^ (e * (k + 1)) ≤ I.budget n →
    ∀ (t u : Role) (x y : V.Questions n) (a b : BitStr), a.length ≤ T → b.length ≤ T →
      ∀ time, (core (ℓ + 1)).Runs (cInput V.sampler.prog V.decider.prog (I.cut n) n t (toBits x)
        u (toBits y) a b) (encode true) time → time ≤ I.budget n := by
  obtain ⟨c, m, e, h⟩ := core_accepting_le ℓ
  refine ⟨c, m, e, fun V I T n TS TD k W hS hD hTS hTD hK t u x y a b ha hb time hrun => ?_⟩
  refine le_trans (h V (I.cut n) n TS TD k W hS hD hTS hTD t u x y a b time hrun) (le_trans ?_ hK)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by have := size_cInput_le V (I.cut n) n T t u x y a b ha hb; omega) _)

/-- **Completeness of the compiled typed game at an explicit budget**: a value-`1` PCC strategy of
`𝒱_n` at the parse cut gives one of the doubled typed game, when the inner cut holds every honest
encoding and the budget is above the core's running time on answers within the inner cut. -/
theorem exists_typedPredicate_perfectPCC_within (ℓ : ℕ) : ∃ c m e, ∀ (V : Verifier (ℓ + 1))
    (I : Index) (C : CL.Detyping.CutoffProgram) (n TS TD k W : ℕ),
    V.sampler.TimeBoundAt n TS k → V.decider.TimeBoundAt n TD k → TS ≤ W → TD ≤ W →
    8 * I.cut n + 3 ≤ C.inner n → C.inner n ≤ C.outer n →
    c * (W + 1) ^ m * (coreInputBound V (I.cut n) n (C.inner n) + 1) ^ (e * (k + 1)) ≤
      I.budget n →
    V.HasPerfectPCC n (I.cut n) →
    ∃ R : SyncStrategy (CL.Detyping.typedGame roleGraph roleGraph_nonempty
        (fun _ => roleFamily (V.sampler.cl n))
        (CL.Detyping.DeciderProgram.typedPredicate (oracleSampler V.sampler)
          (oracleDecider (ℓ + 1) V.sampler.prog V.decider.prog I) C n)).doubled,
      R.IsPCC ∧ R.value = 1 := by
  obtain ⟨c, m, e, h⟩ := budget_sufficient ℓ
  exact ⟨c, m, e, fun V I C n TS TD k W hS hD hTS hTD hin hout hK hV =>
    exists_typedPredicate_perfectPCC V I C n hin hout
      (h V I (C.inner n) n TS TD k W hS hD hTS hTD hK) hV⟩

end OracleDecider

end MIPRE
