/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArRoutine
public import MIPRE.Tailored.AnsRed.ArHonestHyp
public import MIPRE.TM.CookLevin.LayoutProg

@[expose] public section

/-!
# The circuit function of the answer reduction

Slice P4i of `planning/aldous-lyons-track.md`: the circuit function of the routine, in polynomial
time (`arCircF`). From the input verifier's programs, the index, the parameters and a seed's two
questions, it computes the window describer's description of the output indicator `L*` at the
parameters `(ℓ, ◇)` — the windows `ℓ + 1, ℓ + 1, oW + 1`, the program of `L*` (from a
polynomial-time builder `B` of `L*`'s program at constant parameters), `T = 2^K`, `Q = ℓ` and
`σ'`, read from the parameters' data — then pads it to the gate count `s`. At the routine's
parameters it is the circuit `Params.arCirc` of the honest PCPs' hypotheses (`arCircF_apply`);
it is well formed with the PCP's inputs and `s` gates (`arCircF_wf`, `arCircF_inputs`,
`arCircF_size`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT TM.CookLevin.Desc

variable (B : PolyTimeFun ((Prog × Prog) × (Unary × Unary)) Prog)

/-- **The circuit function**, from a builder `B` of the output indicator's program. -/
def arCircF : PolyTimeFun CircIn Circuit :=
  let Vp : PolyTimeFun CircIn (Prog × Prog × Prog) := fst
  let L : PolyTimeFun CircIn Prog := fst.comp (snd.comp Vp)
  let P : PolyTimeFun CircIn Prog := snd.comp (snd.comp Vp)
  let n : PolyTimeFun CircIn ℕ := fst.comp (snd.comp snd)
  let par : PolyTimeFun CircIn ArParams := fst.comp (snd.comp (snd.comp snd))
  let x : PolyTimeFun CircIn BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
  let y : PolyTimeFun CircIn BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))
  let lu : PolyTimeFun CircIn Unary := pL.comp par
  let du : PolyTimeFun CircIn Unary := pDm.comp par
  let su : PolyTimeFun CircIn Unary := pS.comp par
  let e : PolyTimeFun CircIn Data := pE.comp par
  let Ku : PolyTimeFun CircIn Unary := AnswerReduction.readU.comp (treeHead.comp e)
  let σu : PolyTimeFun CircIn Unary := AnswerReduction.readU.comp (treeTail.comp e)
  let ua : PolyTimeFun CircIn Unary := addU.comp (lu.pair (const (unary 1)))
  let oWu : PolyTimeFun CircIn Unary :=
    addU.comp ((addU.comp (lu.pair lu)).pair (addU.comp ((nsmulU 3).comp du |>.pair
      (const (unary 6)))))
  let uc : PolyTimeFun CircIn Unary := addU.comp (oWu.pair (const (unary 1)))
  let prog : PolyTimeFun CircIn Prog := B.comp ((L.pair P).pair (lu.pair du))
  let inp : PolyTimeFun CircIn Desc6Input :=
    (ua.pair (ua.pair uc)).pair ((prog.pair (n.pair ((pow2P.comp Ku).pair
      ((PolyTimeFun.unaryToBin.comp lu).pair (PolyTimeFun.unaryToBin.comp σu))))).pair
        (x.pair y))
  Circuit.padToProg.comp ((windowDescriber.describe.comp inp).pair su)

variable {B}

theorem unary_add_one (k : ℕ) : unary k ++ unary 1 = unary (k + 1) :=
  unary_ext (by simp)

set_option maxRecDepth 100000 in
/-- **At the routine's parameters, the circuit function computes `Params.arCirc`.** -/
theorem arCircF_apply (hB : ∀ L P p, B ((L, P), p) = lstarProg (const p) L P)
    (κ : Params.ArConsts) (V : Prog × Prog × Prog) (lam mu sigma n : ℕ) (x y : BitStr) :
    arCircF B (V, (lam, mu, sigma), n, arParams (Params.pTw κ lam mu sigma n)
      (Params.pJ κ lam mu sigma n) Params.pD (Params.pL κ lam mu sigma n)
      (Params.pExtra κ lam mu sigma n), x, y) =
      Params.arCirc κ lam mu sigma n V.2.1 V.2.2 x y := by
  obtain ⟨S, L, P⟩ := V
  have hoW : unary (Params.pEll lam mu n) ++ unary (Params.pEll lam mu n) ++
      (unary (3 * Params.pDm lam mu n) ++ unary 6) ++ unary 1 =
      unary (Params.pOW lam mu n + 1) := unary_ext (by simp; unfold Params.pOW; ring)
  have h3 : ∀ k, nsmulU 3 (unary k) = unary (3 * k) := fun k => unary_ext (by simp)
  simp only [arCircF, comp_apply, pair_apply, fst_apply, snd_apply, const_apply, pL_arParams,
    pDm_arParams, pS_arParams, pE_arParams, Params.pL_ℓ, Params.pL_dm, Params.pL_s,
    Params.pExtra, encode_prod, treeHead_cons, treeTail_cons, AnswerReduction.readU_encode,
    addU_apply, h3, unary_add_one, hoW, hB, Circuit.padToProg_apply, length_unary, pow2P_apply,
    PolyTimeFun.unaryToBin_apply]
  rfl

theorem arCircF_wf (inp : CircIn) : (arCircF B inp).WellFormed := by
  simp only [arCircF, comp_apply, pair_apply, Circuit.padToProg_apply]
  exact Circuit.wellFormed_padTo (windowDescriber.wellFormed _) _

theorem arCircF_inputs (hB : ∀ L P p, B ((L, P), p) = lstarProg (const p) L P)
    (κ : Params.ArConsts) (V : Prog × Prog × Prog) (lam mu sigma n : ℕ) (x y : BitStr) :
    (arCircF B (V, (lam, mu, sigma), n, arParams (Params.pTw κ lam mu sigma n)
      (Params.pJ κ lam mu sigma n) Params.pD (Params.pL κ lam mu sigma n)
      (Params.pExtra κ lam mu sigma n), x, y)).inputs = (Params.pL κ lam mu sigma n).nIn := by
  rw [arCircF_apply hB]
  exact Params.arCirc_inputs κ lam mu sigma n _ _ _ _

theorem arCircF_size (hB : ∀ L P p, B ((L, P), p) = lstarProg (const p) L P)
    (κ : Params.ArConsts) (V : Prog × Prog × Prog) (lam mu sigma n : ℕ) (x y : BitStr) :
    (arCircF B (V, (lam, mu, sigma), n, arParams (Params.pTw κ lam mu sigma n)
      (Params.pJ κ lam mu sigma n) Params.pD (Params.pL κ lam mu sigma n)
      (Params.pExtra κ lam mu sigma n), x, y)).size = (Params.pL κ lam mu sigma n).s := by
  rw [arCircF_apply hB]
  exact Params.arCirc_size κ lam mu sigma n _ _ _ _

end MIPRE.Tailored.AnsRed.Typed

end

end
