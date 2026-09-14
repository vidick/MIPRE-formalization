/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Classes
import MIPRE.Foundations.Halting.Arith
import MIPRE.Foundations.Cost.Kleene

/-!
# Reading a string as a normal form verifier: the wrapper decider

Blueprint `rem:compression-abstract`, item 1: a string of the compressibility criterion is a
pair `(λ, 𝒟)` of a parameter and a decider program, read as the verifier
`(S^compr_λ, wrap 𝒟)`. The wrapper is what makes the pair a *normal form* verifier: the one
structural requirement of `def:normal-verifier` is `Verifier.accepts_length`, that the decider
accept only questions of the sampler's dimension — the paper's step 1, "compute the dimension
`s(n)` of the sampler and check `|x| = |y| = s(n)`; if not, reject".

Nothing else has to be enforced. Synchronicity at an index and the answer-length bound are
conditions on *membership in the classes* (`Verifier.InClassA`, `InClassB`), not on
well-formedness, so the wrapper leaves them to the class definition; and the paper's timeout
counter is likewise not needed here, since a decider that fails to halt simply fails to be
`n`-bounded, and its string then lies in neither class.

* `Prog.wrapCore univ sampProg dec`: on input `(N, x, y, a, b)`, run `sampProg` on
  `(N, dimension)` through the universal machine `univ`, convert the dimension to unary, compare
  it with the lengths of `x` and of `y`, and run `dec` on the whole input through `univ` if both
  match, rejecting otherwise.
* The three forward runs (`wrapCore_runs_of_eq`, `wrapCore_runs_of_ne_left`,
  `wrapCore_runs_of_ne_right`) and the inversion `wrapCore_halts_of`, which is what turns them
  into the characterization of acceptance.
* `Decider.wrap`, `Decider.wrap_accepts`, and `Verifier.ofSamplerDecider`, the normal form
  verifier a pair denotes.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

open Data

/-! ## The program -/

/-- One length check, reusable for both questions: read the length of the bit string at index
`i`, compare it with the unary numeral at index `j`, and continue with `c` if they agree,
rejecting otherwise. -/
def wrapCheck (i j : ℕ) (c : Prog) : Prog :=
  .let_ (callVar i lenProg)
    (.let_ (.cons (.var 0) (.var (j + 1)))
      (.let_ (callVar 0 eqBitsProg)
        (.elim 0 .nil c)))

/-- The environment `wrapCheck` hands to its continuation. -/
def wrapCheckEnv (l : BitStr) (m : ℕ) (env : Env) : Env :=
  .nil :: .nil :: encode true :: .cons (Data.ofNat l.length) (Data.ofNat m) ::
    Data.ofNat l.length :: env

/-- The last step: run the string's decider `dec` on the whole input, through `univ`. At this
point the input sits at index `19`. -/
def wrapTail (univ dec : Prog) : Prog :=
  .let_ (.cons (.const (encode dec)) (.var 19)) (callVar 0 univ)

/-- The prefix: compute the sampler's dimension at the input index, in unary, and take the two
questions apart. -/
def wrapPre (univ sampProg c : Prog) : Prog :=
  .elim 0 .nil
    (.let_ (.cons (.const (encode sampProg))
        (.cons (.var 0) (.const (encode CL.Sampler.Query.dimension))))
      (.let_ (callVar 0 univ)
        (.let_ (callVar 0 toUnaryProg)
          (.elim 4 .nil (.elim 1 .nil c)))))

/-- The wrapper's program. Input: `encode (N, x, y, a, b)`. -/
def wrapCore (univ sampProg dec : Prog) : Prog :=
  wrapPre univ sampProg (wrapCheck 2 4 (wrapCheck 5 9 (wrapTail univ dec)))

theorem wrapCheck_wellScoped {i j n : ℕ} (hi : i < n) (hj : j < n) {c : Prog}
    (hc : c.WellScoped (n + 5)) : (wrapCheck i j c).WellScoped n :=
  ⟨callVar_wellScoped hi lenProg_wellScoped,
    ⟨⟨by simp [WellScoped], by simpa [WellScoped] using hj⟩,
      ⟨callVar_wellScoped (by omega) eqBitsProg_wellScoped,
        ⟨by simp, trivial, by simpa [show n + 1 + 1 + 1 + 2 = n + 5 by omega] using hc⟩⟩⟩⟩

theorem wrapTail_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (dec : Prog) :
    (wrapTail univ dec).WellScoped 20 :=
  ⟨⟨trivial, by simp [WellScoped]⟩, callVar_wellScoped (by simp) hU⟩

theorem wrapPre_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (sampProg : Prog) {c : Prog}
    (hc : c.WellScoped 10) : (wrapPre univ sampProg c).WellScoped 1 := by
  refine ⟨by simp, trivial, ?_⟩
  refine ⟨⟨trivial, ⟨by simp [WellScoped], trivial⟩⟩, ?_⟩
  refine ⟨callVar_wellScoped (by simp) hU, ?_⟩
  refine ⟨callVar_wellScoped (by simp) toUnaryProg_wellScoped, ?_⟩
  refine ⟨by simp, trivial, ?_⟩
  exact ⟨by simp, trivial, hc⟩

theorem wrapCore_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (sampProg dec : Prog) :
    (wrapCore univ sampProg dec).WellScoped 1 :=
  wrapPre_wellScoped hU sampProg
    (wrapCheck_wellScoped (by omega) (by omega)
      (wrapCheck_wellScoped (by omega) (by omega) (wrapTail_wellScoped hU dec)))

/-! ## The length check -/

section Check

variable {i j : ℕ} {c : Prog} {env : Env} {l : BitStr} {m : ℕ}

private theorem len_run (z : BitStr) :
    ∃ t, lenProg.Runs (encode z) (Data.ofNat z.length) t := by
  obtain ⟨t, -, h⟩ := lenProg_runs (z.map Data.ofBool)
  refine ⟨t, ?_⟩
  rw [encode_bitStr_eq_list]
  simpa using h

private theorem eq_run (p q : ℕ) :
    ∃ t, eqBitsProg.Runs (.cons (Data.ofNat p) (Data.ofNat q)) (encode (decide (p = q))) t := by
  obtain ⟨t, -, h⟩ := eqBitsProg_runs (Data.ofNat p) (Data.ofNat q) []
    ((Data.ofNat p).size + (Data.ofNat q).size) le_rfl
  rw [eqBits_ofNat] at h
  exact ⟨t, h⟩

theorem wrapCheck_runs_of_ne (hi : env.get i = encode l) (hj : env.get j = Data.ofNat m)
    (hne : l.length ≠ m) : ∃ t, Eval env (wrapCheck i j c) .nil t := by
  obtain ⟨t₁, h₁⟩ := len_run l
  obtain ⟨t₂, h₂⟩ := eq_run l.length m
  exact ⟨_, Eval.let_ (callVar_eval lenProg_wellScoped hi h₁)
    (Eval.let_ (Eval.cons
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := 0)
          (v := Data.ofNat l.length) (by simp))
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := j + 1)
          (v := Data.ofNat m) (by simpa using hj)))
      (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat l.length) (Data.ofNat m)) (by simp) h₂)
        (Eval.elim_nil (i := 0)
          (show Env.get (encode (decide (l.length = m)) ::
              Data.cons (Data.ofNat l.length) (Data.ofNat m) ::
              Data.ofNat l.length :: env) 0 = Data.nil by
            simp [hne, encode_bool, Data.ofBool])
          (Eval.nil _))))⟩

theorem wrapCheck_runs_of_eq (hi : env.get i = encode l) (hj : env.get j = Data.ofNat m)
    (heq : l.length = m) {r : Data} {t : ℕ} (hc : Eval (wrapCheckEnv l m env) c r t) :
    ∃ t', Eval env (wrapCheck i j c) r t' := by
  obtain ⟨t₁, h₁⟩ := len_run l
  obtain ⟨t₂, h₂⟩ := eq_run l.length m
  have hc' : Eval (Data.nil :: Data.nil :: encode (decide (l.length = m)) ::
      Data.cons (Data.ofNat l.length) (Data.ofNat m) :: Data.ofNat l.length :: env) c r t := by
    simpa [wrapCheckEnv, heq] using hc
  exact ⟨_, Eval.let_ (callVar_eval lenProg_wellScoped hi h₁)
    (Eval.let_ (Eval.cons
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := 0)
          (v := Data.ofNat l.length) (by simp))
        (Eval.var_of_get (env := Data.ofNat l.length :: env) (i := j + 1)
          (v := Data.ofNat m) (by simpa using hj)))
      (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat l.length) (Data.ofNat m)) (by simp) h₂)
        (Eval.elim_cons (i := 0) (a := .nil) (b := .nil)
          (by simp [heq, encode_bool, Data.ofBool]) hc')))⟩

/-- **Inversion.** A run of the check either fails the comparison and returns `nil`, or passes
it and is a run of the continuation. -/
theorem wrapCheck_inv (hi : env.get i = encode l) (hj : env.get j = Data.ofNat m)
    {r : Data} {t : ℕ} (h : Eval env (wrapCheck i j c) r t) :
    (l.length ≠ m ∧ r = .nil) ∨ (l.length = m ∧ ∃ t', Eval (wrapCheckEnv l m env) c r t') := by
  obtain ⟨t₁, h₁⟩ := len_run l
  obtain ⟨t₂, h₂⟩ := eq_run l.length m
  change Eval env (.let_ (callVar i lenProg) _) r t at h
  cases h with
  | let_ hA hB =>
    obtain ⟨rfl, -⟩ := hA.deterministic (callVar_eval lenProg_wellScoped hi h₁)
    cases hB with
    | let_ hC hD =>
      obtain ⟨rfl, -⟩ := hC.deterministic
        (Eval.cons (Eval.var_of_get (i := 0) (v := Data.ofNat l.length) (by simp))
          (Eval.var_of_get (i := j + 1) (v := Data.ofNat m) (by simpa using hj)))
      cases hD with
      | let_ hE hF =>
        obtain ⟨rfl, -⟩ := hE.deterministic (callVar_eval eqBitsProg_wellScoped (i := 0)
          (v := .cons (Data.ofNat l.length) (Data.ofNat m)) (by simp) h₂)
        by_cases hlm : l.length = m
        · refine Or.inr ⟨hlm, ?_⟩
          cases hF with
          | elim_nil hn _ => simp [hlm, encode_bool, Data.ofBool] at hn
          | elim_cons hcx hrest =>
            simp only [Env.get_cons_zero, hlm, decide_true, encode_bool, Data.ofBool] at hcx
            obtain ⟨rfl, rfl⟩ := Data.cons.inj hcx
            exact ⟨_, by simpa [wrapCheckEnv, hlm] using hrest⟩
        · refine Or.inl ⟨hlm, ?_⟩
          cases hF with
          | elim_nil _ hnil => cases hnil; rfl
          | elim_cons hcx _ => simp [hlm, encode_bool, Data.ofBool] at hcx

end Check

/-! ## The whole run -/

section Runs

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog)
  (n : ℕ) (x y a b : BitStr)

/-- The environment the prefix hands to the first length check. -/
def wrapPreEnv : Env :=
  [encode y, .cons (encode a) (encode b), encode x,
    .cons (encode y) (.cons (encode a) (encode b)), Data.ofNat (S.dim n), encode (S.dim n),
    .cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension)), encode n,
    .cons (encode x) (.cons (encode y) (.cons (encode a) (encode b))), encode (n, x, y, a, b)]

private theorem dim_run :
    ∃ t, U.univ.Runs (.cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension)))
      (encode (S.dim n)) t := by
  obtain ⟨t, ht⟩ := S.runs_dimension n
  obtain ⟨t', -, h⟩ := U.time_le S.prog _ _ t ht
  exact ⟨t', h⟩

private theorem toUnary_run (k : ℕ) : ∃ t, toUnaryProg.Runs (encode k) (Data.ofNat k) t := by
  obtain ⟨t, -, h⟩ := toUnaryProg_runs k
  exact ⟨t, h⟩

private theorem input_cons :
    (encode (n, x, y, a, b) : Data) =
      .cons (encode n) (.cons (encode x) (.cons (encode y) (.cons (encode a) (encode b)))) := rfl

/-- The prefix runs, whatever the continuation does. -/
theorem wrapPre_runs {c : Prog} {r : Data} {t : ℕ}
    (hc : Eval (wrapPreEnv S n x y a b) c r t) :
    ∃ t', Eval [encode (n, x, y, a, b)] (wrapPre U.univ S.prog c) r t' := by
  obtain ⟨t₁, h₁⟩ := dim_run U S n
  obtain ⟨t₂, h₂⟩ := toUnary_run (S.dim n)
  exact ⟨_, Eval.elim_cons (env := [encode (n, x, y, a, b)]) (i := 0) (a := encode n)
    (b := .cons (encode x) (.cons (encode y) (.cons (encode a) (encode b))))
    (by rw [Env.get_cons_zero, input_cons])
    (Eval.let_ (Eval.cons (Eval.const _ _)
        (Eval.cons (Eval.var_of_get (i := 0) (v := encode n) (by simp)) (Eval.const _ _)))
      (Eval.let_ (callVar_eval U.closed (i := 0)
          (v := .cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension))) (by simp) h₁)
        (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 0) (v := encode (S.dim n))
            (by simp) h₂)
          (Eval.elim_cons (i := 4) (a := encode x)
              (b := .cons (encode y) (.cons (encode a) (encode b))) (by simp)
            (Eval.elim_cons (i := 1) (a := encode y) (b := .cons (encode a) (encode b))
              (by simp) hc)))))⟩

/-- **Inversion of the prefix.** -/
theorem wrapPre_inv {c : Prog} {r : Data} {t : ℕ}
    (h : Eval [encode (n, x, y, a, b)] (wrapPre U.univ S.prog c) r t) :
    ∃ t', Eval (wrapPreEnv S n x y a b) c r t' := by
  obtain ⟨t₁, h₁⟩ := dim_run U S n
  obtain ⟨t₂, h₂⟩ := toUnary_run (S.dim n)
  change Eval [encode (n, x, y, a, b)] (.elim 0 .nil _) r t at h
  cases h with
  | elim_nil hn _ => rw [Env.get_cons_zero, input_cons] at hn; exact absurd hn (by simp)
  | @elim_cons _ _ _ _ A B _ _ hcx hA =>
    rw [Env.get_cons_zero, input_cons] at hcx
    obtain ⟨rfl, rfl⟩ := Data.cons.inj hcx.symm
    cases hA with
    | let_ hB hC =>
      obtain ⟨rfl, -⟩ := hB.deterministic (Eval.cons (Eval.const _ _)
        (Eval.cons (Eval.var_of_get (i := 0) (v := encode n) (by simp)) (Eval.const _ _)))
      cases hC with
      | let_ hD hE =>
        obtain ⟨rfl, -⟩ := hD.deterministic (callVar_eval U.closed (i := 0)
          (v := .cons (encode S.prog) (Data.cons (encode n) (encode CL.Sampler.Query.dimension))) (by simp) h₁)
        cases hE with
        | let_ hF hG =>
          obtain ⟨rfl, -⟩ := hF.deterministic (callVar_eval toUnaryProg_wellScoped (i := 0)
            (v := encode (S.dim n)) (by simp) h₂)
          cases hG with
          | elim_nil hn _ => simp at hn
          | @elim_cons _ _ _ _ A₂ B₂ _ _ hc₂ hH =>
            obtain ⟨rfl, rfl⟩ := Data.cons.inj (by simpa using hc₂.symm)
            cases hH with
            | elim_nil hn _ => simp at hn
            | @elim_cons _ _ _ _ A₃ B₃ _ _ hc₃ hI =>
              obtain ⟨rfl, rfl⟩ := Data.cons.inj (by simpa using hc₃.symm)
              exact ⟨_, hI⟩

/-! ### The three outcomes -/

theorem wrapCore_runs_of_ne_left (hx : x.length ≠ S.dim n) :
    ∃ t, (wrapCore U.univ S.prog dec).Runs (encode (n, x, y, a, b)) .nil t := by
  obtain ⟨t, h⟩ := wrapCheck_runs_of_ne (i := 2) (j := 4) (env := wrapPreEnv S n x y a b)
    (c := wrapCheck 5 9 (wrapTail U.univ dec)) rfl rfl hx
  exact wrapPre_runs U S n x y a b h

theorem wrapCore_runs_of_ne_right (hx : x.length = S.dim n) (hy : y.length ≠ S.dim n) :
    ∃ t, (wrapCore U.univ S.prog dec).Runs (encode (n, x, y, a, b)) .nil t := by
  obtain ⟨t, h⟩ := wrapCheck_runs_of_ne (i := 5) (j := 9)
    (env := wrapCheckEnv x (S.dim n) (wrapPreEnv S n x y a b))
    (c := wrapTail U.univ dec) rfl rfl hy
  obtain ⟨t', h'⟩ := wrapCheck_runs_of_eq (i := 2) (j := 4) (env := wrapPreEnv S n x y a b)
    rfl rfl hx h
  exact wrapPre_runs U S n x y a b h'

theorem wrapCore_runs_of_eq (hx : x.length = S.dim n) (hy : y.length = S.dim n)
    {r : Data} {td : ℕ} (hd : dec.Runs (encode (n, x, y, a, b)) r td) :
    ∃ t, (wrapCore U.univ S.prog dec).Runs (encode (n, x, y, a, b)) r t := by
  obtain ⟨t₇, -, h₇⟩ := U.time_le dec _ _ td hd
  have htail : Eval (wrapCheckEnv y (S.dim n) (wrapCheckEnv x (S.dim n)
      (wrapPreEnv S n x y a b))) (wrapTail U.univ dec) r _ :=
    Eval.let_ (Eval.cons (Eval.const _ _)
      (Eval.var_of_get (i := 19) (v := encode (n, x, y, a, b)) (by simp [wrapCheckEnv,
        wrapPreEnv]))) (callVar_eval U.closed (i := 0)
      (v := .cons (encode dec) (encode (n, x, y, a, b))) (by simp) h₇)
  obtain ⟨t, h⟩ := wrapCheck_runs_of_eq (i := 5) (j := 9)
    (env := wrapCheckEnv x (S.dim n) (wrapPreEnv S n x y a b)) rfl rfl hy htail
  obtain ⟨t', h'⟩ := wrapCheck_runs_of_eq (i := 2) (j := 4) (env := wrapPreEnv S n x y a b)
    rfl rfl hx h
  exact wrapPre_runs U S n x y a b h'

/-- **The wrapper halts only if the string's decider does.** -/
theorem wrapCore_halts_inv {r : Data} {t : ℕ}
    (h : (wrapCore U.univ S.prog dec).Runs (encode (n, x, y, a, b)) r t) :
    r = .nil ∨ ∃ t', dec.Runs (encode (n, x, y, a, b)) r t' := by
  obtain ⟨t₁, h₁⟩ := wrapPre_inv U S n x y a b h
  rcases wrapCheck_inv (i := 2) (j := 4) (env := wrapPreEnv S n x y a b) rfl rfl h₁ with
    ⟨-, hr⟩ | ⟨-, t₂, h₂⟩
  · exact Or.inl hr
  rcases wrapCheck_inv (i := 5) (j := 9)
      (env := wrapCheckEnv x (S.dim n) (wrapPreEnv S n x y a b)) rfl rfl h₂ with
    ⟨-, hr⟩ | ⟨-, t₃, h₃⟩
  · exact Or.inl hr
  refine Or.inr ?_
  change Eval _ (.let_ _ (callVar 0 U.univ)) r t₃ at h₃
  cases h₃ with
  | let_ hA hB =>
    obtain ⟨rfl, -⟩ := hA.deterministic (Eval.cons (Eval.const _ _)
      (Eval.var_of_get (i := 19) (v := encode (n, x, y, a, b))
        (by simp [wrapCheckEnv, wrapPreEnv])))
    obtain ⟨t₄, -, h₄⟩ := callVar_runs_rev U.closed hB
    simp only [Env.get_cons_zero] at h₄
    exact U.halts_of dec _ _ _ h₄

end Runs

end Cost.Prog

/-! ## The wrapped decider and the verifier a pair denotes -/

namespace Decider

open Cost Cost.Prog

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog)

/-- The decider a string denotes: the string's own decider `dec`, wrapped in the
question-length check against the sampler `S`. -/
def wrap : Decider :=
  ⟨wrapCore U.univ S.prog dec, wrapCore_wellScoped U.closed _ _⟩

@[simp] theorem wrap_prog : (wrap U S dec).prog = wrapCore U.univ S.prog dec := rfl

/-- **Acceptance of the wrapped decider**: the two questions have the sampler's dimension and
the string's own decider accepts. -/
theorem wrap_accepts (n : ℕ) (x y a b : BitStr) :
    (wrap U S dec).Accepts n x y a b ↔
      (x.length = S.dim n ∧ y.length = S.dim n ∧
        ∃ t, dec.Runs (encode (n, x, y, a, b)) (encode true) t) := by
  constructor
  · rintro ⟨t, ht⟩
    have hne : (encode true : Data) ≠ .nil := by simp [encode_bool, Data.ofBool]
    have hx : x.length = S.dim n := by
      by_contra hx
      obtain ⟨t', h'⟩ := wrapCore_runs_of_ne_left U S dec n x y a b hx
      exact hne (Eval.deterministic ht h').1
    have hy : y.length = S.dim n := by
      by_contra hy
      obtain ⟨t', h'⟩ := wrapCore_runs_of_ne_right U S dec n x y a b hx hy
      exact hne (Eval.deterministic ht h').1
    rcases wrapCore_halts_inv U S dec n x y a b ht with hr | hd
    · exact absurd hr hne
    · exact ⟨hx, hy, hd⟩
  · rintro ⟨hx, hy, td, hd⟩
    exact wrapCore_runs_of_eq U S dec n x y a b hx hy hd

/-- The wrapped decider accepts only questions of the sampler's dimension: the one structural
requirement of `def:normal-verifier`. -/
theorem wrap_accepts_length (n : ℕ) (x y a b : BitStr)
    (h : (wrap U S dec).Accepts n x y a b) : x.length = S.dim n ∧ y.length = S.dim n :=
  ⟨((wrap_accepts U S dec n x y a b).1 h).1, ((wrap_accepts U S dec n x y a b).1 h).2.1⟩

end Decider

namespace Verifier

open Cost

/-- **The verifier a pair `(S, 𝒟)` denotes**: the sampler `S`, and the string's decider wrapped
in the question-length check. Every pair denotes one, well formed or not. -/
def ofSamplerDecider {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog) :
    Verifier ℓ where
  sampler := S
  decider := Decider.wrap U S dec
  accepts_length n x y a b h := Decider.wrap_accepts_length U S dec n x y a b h

variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog)

@[simp] theorem ofSamplerDecider_sampler : (ofSamplerDecider U S dec).sampler = S := rfl

theorem ofSamplerDecider_accepts (n : ℕ) (x y a b : BitStr) :
    (ofSamplerDecider U S dec).decider.Accepts n x y a b ↔
      (x.length = S.dim n ∧ y.length = S.dim n ∧
        ∃ t, dec.Runs (encode (n, x, y, a, b)) (encode true) t) :=
  Decider.wrap_accepts U S dec n x y a b

/-- Two strings with the same sampler whose deciders agree at index `n` denote verifiers with
the same `val*` and the same perfect PCC strategies there. -/
theorem ofSamplerDecider_congr {dec dec' : Prog} {n T : ℕ}
    (h : ∀ x y a b : BitStr, (∃ t, dec.Runs (encode (n, x, y, a, b)) (encode true) t) ↔
      ∃ t, dec'.Runs (encode (n, x, y, a, b)) (encode true) t) :
    (ofSamplerDecider U S dec).valStar n T = (ofSamplerDecider U S dec').valStar n T :=
  valStar_congr rfl fun x y a b => by
    rw [ofSamplerDecider_accepts, ofSamplerDecider_accepts]
    exact and_congr_right fun _ => and_congr_right fun _ => h x y a b

end Verifier

end MIPRE
