/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.OutSampler
public import MIPRE.Background.AnswerReduction.ArDecider

@[expose] public section

/-!
# The parameter routine of the answer-reduced verifier

Slice P4h of `planning/aldous-lyons-track.md`. At an index `n` the output verifier of the answer
reduction runs at parameters — the field width `t`, the selector width `j` with `M = 2^j`, the
degree `d` and the dimensions `ℓ, ◇, r, s` of the PCP — that grow like a power of `(λn + 1)^μ`.
Its programs read them in unary, which no polynomial-time function of the index can write: the
index is read in binary. So, as the MIP* answer reduction's parameter routine
(`MIPRE.AnswerReduction.parProg`), the parameters are computed by a program run as a stage of
the output's programs, on `((λ, μ, σ), n)`, and the cost of that stage is bounded separately.

* `ArParams`, `arParams`: the parameters at an index, in unary, with data for the circuit
  function; `readParams` reads them back.
* `ArRoutine`: the parameter functions, the closed program `parCore` computing them, and the
  circuit function `circF` giving the circuit of a seed from the input verifier's programs, the
  parameters and the seed's two questions, well formed with the PCP's `nIn` inputs and `s`
  gates. The routine is fixed in P4i.
* `ArRoutine.toLd`: the routine of the low-degree half of the sampler (`LdRoutine`), the
  parameter program projected to the half's parameters.
* `ArRoutine.circ`: the circuit of each seed of the input verifier.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT

/-! ## The parameters at an index -/

/-- **The parameters of the answer-reduced verifier at an index**, in unary: the field width `t`,
the selector width `j`, `M = 2^j`, the degree `d`, the dimensions `ℓ, ◇, r, s` of the PCP, then
data for the circuit function. -/
abbrev ArParams : Type := Unary × Unary × Unary × Unary × Unary × Unary × Unary × Unary × Data

/-- The parameters of the typed data, as `ArParams`. -/
def arParams (t j d : ℕ) (L : PcpDims) (e : Data) : ArParams :=
  (unary t, unary j, unary (2 ^ j), unary d, unary L.ℓ, unary L.dm, unary L.r, unary L.s, e)

theorem unary_ext {u v : Unary} (h : u.length = v.length) : u = v := by
  rw [← unary_length u, ← unary_length v, h]

/-- The field width. -/
def pT : PolyTimeFun ArParams Unary := fst
/-- The selector width. -/
def pJ : PolyTimeFun ArParams Unary := fst.comp snd
/-- `M = 2^j`. -/
def pM : PolyTimeFun ArParams Unary := fst.comp (snd.comp snd)
/-- The degree. -/
def pD : PolyTimeFun ArParams Unary := fst.comp (snd.comp (snd.comp snd))
/-- The window width `ℓ` of the PCP. -/
def pL : PolyTimeFun ArParams Unary := fst.comp (snd.comp (snd.comp (snd.comp snd)))
/-- The index width `◇` of the PCP. -/
def pDm : PolyTimeFun ArParams Unary := fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
/-- The witness index width `r` of the PCP. -/
def pR : PolyTimeFun ArParams Unary :=
  fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
/-- The number `s` of gates of the circuits. -/
def pS : PolyTimeFun ArParams Unary :=
  fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))))
/-- The data of the circuit function. -/
def pE : PolyTimeFun ArParams Data :=
  snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))))

section Read

variable (t j d : ℕ) (L : PcpDims) (e : Data)

@[simp] theorem pT_arParams : pT (arParams t j d L e) = unary t := rfl
@[simp] theorem pJ_arParams : pJ (arParams t j d L e) = unary j := rfl
@[simp] theorem pM_arParams : pM (arParams t j d L e) = unary (2 ^ j) := rfl
@[simp] theorem pD_arParams : pD (arParams t j d L e) = unary d := rfl
@[simp] theorem pL_arParams : pL (arParams t j d L e) = unary L.ℓ := rfl
@[simp] theorem pDm_arParams : pDm (arParams t j d L e) = unary L.dm := rfl
@[simp] theorem pR_arParams : pR (arParams t j d L e) = unary L.r := rfl
@[simp] theorem pS_arParams : pS (arParams t j d L e) = unary L.s := rfl
@[simp] theorem pE_arParams : pE (arParams t j d L e) = e := rfl

end Read

/-- The `i`-th field of a nested pair. -/
def fieldAt : ℕ → PolyTimeFun Data Data
  | 0 => treeHead
  | i + 1 => (fieldAt i).comp treeTail

/-- The tail of a nested pair after `i` fields. -/
def tailAt : ℕ → PolyTimeFun Data Data
  | 0 => PolyTimeFun.id Data
  | i + 1 => (tailAt i).comp treeTail

/-- **The parameters, read back.** -/
def readParams : PolyTimeFun Data ArParams :=
  (AnswerReduction.readU.comp (fieldAt 0)).pair ((AnswerReduction.readU.comp (fieldAt 1)).pair
    ((AnswerReduction.readU.comp (fieldAt 2)).pair ((AnswerReduction.readU.comp (fieldAt 3)).pair
      ((AnswerReduction.readU.comp (fieldAt 4)).pair ((AnswerReduction.readU.comp
        (fieldAt 5)).pair ((AnswerReduction.readU.comp (fieldAt 6)).pair
          ((AnswerReduction.readU.comp (fieldAt 7)).pair (tailAt 8))))))))

@[simp] theorem readParams_encode (p : ArParams) : readParams (encode p) = p := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, e⟩ := p
  simp only [readParams, fieldAt, tailAt, pair_apply, comp_apply, encode_prod, treeHead_cons,
    treeTail_cons, AnswerReduction.readU_encode, PolyTimeFun.id_apply, encode_data]

/-- The parameters of the low-degree half, `LdFamily.pd`: `t`, `M` and the copy's description. -/
def ldPdF : PolyTimeFun ArParams Data :=
  Detyping.Program.encoded.comp
    (pT.pair (pM.pair ((const (unary 0)).pair (pM.pair (pJ.pair (const (unary 0)))))))

theorem ldPdF_arParams (F : LdFamily) (n d : ℕ) (L : PcpDims) (e : Data) :
    ldPdF (arParams (F.t n) (F.j n) d L e) = F.pd n := by
  simp only [ldPdF, comp_apply, pair_apply, const_apply, Detyping.Program.encoded_apply,
    pT_arParams, pM_arParams, pJ_arParams, LdFamily.pd, ldDesc]

/-! ## The routine -/

/-- The input of the circuit function: the input verifier's programs, `(λ, μ, σ)`, the index,
the parameters, and the two questions of a seed. -/
abbrev CircIn : Type := (Prog × Prog × Prog) × (ℕ × ℕ × ℕ) × ℕ × ArParams × BitStr × BitStr

/-- **A parameter routine of the answer-reduced verifier**: the parameters at each `(λ, μ, σ)`
and index, a closed program computing them from `((λ, μ, σ), n)`, and a polynomial-time circuit
function, whose circuits are well formed with the PCP's `nIn` inputs and `s` gates. -/
structure ArRoutine where
  /-- The field and selector widths. -/
  fam : ℕ → ℕ → ℕ → LdFamily
  /-- The degree. -/
  d : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- The dimensions of the PCP. -/
  L : ℕ → ℕ → ℕ → ℕ → PcpDims
  hLM : ∀ lam mu sigma n, (L lam mu sigma n).m ≤ 2 ^ (fam lam mu sigma).j n
  /-- The data of the circuit function. -/
  extra : ℕ → ℕ → ℕ → ℕ → Data
  /-- The parameter program. -/
  parCore : Prog
  closed : parCore.WellScoped 1
  runs : ∀ lam mu sigma n, ∃ τ, parCore.Runs (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ))
    (encode (arParams ((fam lam mu sigma).t n) ((fam lam mu sigma).j n) (d lam mu sigma n)
      (L lam mu sigma n) (extra lam mu sigma n))) τ
  /-- The circuit function. -/
  circF : PolyTimeFun CircIn Circuit
  circ_wf : ∀ inp, (circF inp).WellFormed
  circ_inputs : ∀ (V : Prog × Prog × Prog) lam mu sigma n (x y : BitStr),
    (circF (V, (lam, mu, sigma), n, arParams ((fam lam mu sigma).t n) ((fam lam mu sigma).j n)
      (d lam mu sigma n) (L lam mu sigma n) (extra lam mu sigma n), x, y)).inputs =
      (L lam mu sigma n).nIn
  circ_size : ∀ (V : Prog × Prog × Prog) lam mu sigma n (x y : BitStr),
    (circF (V, (lam, mu, sigma), n, arParams ((fam lam mu sigma).t n) ((fam lam mu sigma).j n)
      (d lam mu sigma n) (L lam mu sigma n) (extra lam mu sigma n), x, y)).size =
      (L lam mu sigma n).s

namespace ArRoutine

variable (R : ArRoutine) (lam mu sigma n : ℕ)

/-- The parameters at `(λ, μ, σ)` and `n`. -/
def params : ArParams :=
  arParams ((R.fam lam mu sigma).t n) ((R.fam lam mu sigma).j n) (R.d lam mu sigma n)
    (R.L lam mu sigma n) (R.extra lam mu sigma n)

theorem parCore_runs : ∃ τ, R.parCore.Runs (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ))
    (encode (R.params lam mu sigma n)) τ :=
  R.runs lam mu sigma n

/-! ### The low-degree half's routine -/

/-- The parameter program, projected to the parameters of the low-degree half. -/
def ldCore : Prog := seqProg R.parCore (ldPdF.comp readParams).code

theorem ldCore_closed : R.ldCore.WellScoped 1 := seqProg_closed R.closed (PolyTimeFun.closed _)

theorem ldCore_runs : ∃ τ, R.ldCore.Runs (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ))
    ((R.fam lam mu sigma).pd n) τ := by
  obtain ⟨τ₁, h₁⟩ := R.parCore_runs lam mu sigma n
  obtain ⟨τ₂, -, h₂⟩ := (ldPdF.comp readParams).computes (encode (R.params lam mu sigma n))
  have e : (ldPdF.comp readParams) (encode (R.params lam mu sigma n)) =
      (R.fam lam mu sigma).pd n := by
    rw [comp_apply, readParams_encode, params, ldPdF_arParams]
  rw [e, encode_data, encode_data] at h₂
  exact ⟨_, seqProg_runs (PolyTimeFun.closed _) h₁ h₂⟩

/-- **The routine of the low-degree half**: the projected parameter program, with `(λ, μ, σ)`
hardcoded. -/
def toLd : LdRoutine where
  fam := R.fam
  parPF := (PolyTimeFun.smn (ℕ × ℕ × ℕ)).comp ((const R.ldCore).pair (PolyTimeFun.id _))
  closed _ _ _ := hardcode_wellScoped R.ldCore_closed _
  runs lam mu sigma n := by
    obtain ⟨τ, h⟩ := R.ldCore_runs lam mu sigma n
    rw [encode_prod] at h
    exact ⟨_, hardcode_time R.ldCore_closed h⟩

@[simp] theorem toLd_fam : R.toLd.fam = R.fam := rfl

/-! ### The circuits -/

/-- **The circuit of a seed** of the input verifier: the circuit function at the seed's two
questions. -/
def circ {ℓ : ℕ} (V : TailoredVerifier ℓ) (z : V.Questions n) : Circuit :=
  R.circF (V.progs, (lam, mu, sigma), n, R.params lam mu sigma n,
    CL.toBits ((V.sampler.cl n .alice).eval z), CL.toBits ((V.sampler.cl n .bob).eval z))

theorem circ_inputs' {ℓ : ℕ} (V : TailoredVerifier ℓ) (z : V.Questions n) :
    (R.circ lam mu sigma n V z).inputs = (R.L lam mu sigma n).nIn :=
  R.circ_inputs V.progs lam mu sigma n _ _

theorem circ_size' {ℓ : ℕ} (V : TailoredVerifier ℓ) (z : V.Questions n) :
    (R.circ lam mu sigma n V z).size = (R.L lam mu sigma n).s :=
  R.circ_size V.progs lam mu sigma n _ _

theorem circ_wires {ℓ : ℕ} (V : TailoredVerifier ℓ) (z : V.Questions n) :
    (R.circ lam mu sigma n V z).inputs + (R.circ lam mu sigma n V z).size =
      (R.L lam mu sigma n).m := by
  rw [R.circ_inputs', R.circ_size']
  rfl

end ArRoutine

end MIPRE.Tailored.AnsRed.Typed

end
