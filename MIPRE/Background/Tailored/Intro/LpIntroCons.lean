/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.LpIntroAux
public import MIPRE.Background.Tailored.Intro.PauliHideProg
public import MIPRE.Background.Tailored.Intro.PauliConsProg
public import MIPRE.Background.Tailored.Intro.LenIntro
public import MIPRE.Foundations.Cost.FiniteChoice
public import MIPRE.Background.Tailored.Intro.Sound

@[expose] public section

/-!
# The constraints of the introspection processor at a pair of detyped questions

Issue #281. The processor's core (`mainP`) on the environment, the two readable answers and the
two detyped questions: it decodes the edge of the two graph views (`edgeSel`, the router's
`selectedEdge` as a finite table), branches on it over the finite label alphabet
(`Cost.PolyTimeFun.choose`), checks the readable lengths, and computes the constraints of
`Typed.consRaw` at the edge's labels (`rawP`): the Pauli basis test (`pauliConsProg`), the Pauli
to auxiliary clauses (`pauliAuxP`, in either order), and the auxiliary pairs (`auxPairP`).

`mainP_spec`: on the environment of a bounded input and the bits of two detyped questions, the
output is the detyped game's constraints, `TypedData.detype`'s `cons` on `Sound.tdata`.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.LpIntro

open Cost Cost.Data Cost.PolyTimeFun CL MIPRE.Introspection InputRuns MIPRE.QLD
open CL.Detyping CL.Detyping.Program

/-- The labels. -/
abbrev Label := DecisionKernel.Label

/-! ## The lengths of a label -/

/-- The length of kind `κ` of a label, in unary (`LenIntro.lin` on the parameters). -/
def lenU (t : Label) (κ : Bool) : PolyTimeFun Env Unary :=
  LenIntro.linF.comp ((const (LenIntro.ucoef (LenIntro.coef t κ))).pair
    ((fst.comp ePar).pair ((snd.comp (snd.comp ePar)).pair (eQ.pair eR))))

/-- The total length of a label, in unary. -/
def totLenU (t : Label) : PolyTimeFun Env Unary := catF (lenU t false) (lenU t true)

theorem envT_par (c lam n : ℕ) (T : TailoredVerifier 7) :
    (envT c lam n T).2.2.2.1 =
      (unary (kk c lam n), unary (jj c lam n), unary (2 ^ jj c lam n)) := rfl

theorem length_lenU (c lam n : ℕ) (T : TailoredVerifier 7) (t : Label) (κ : Bool) :
    (lenU t κ (envT c lam n T)).length =
      if κ then Typed.len (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) t -
        Typed.lenR (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) t
      else Typed.lenR (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) t := by
  simp only [lenU, comp_apply, pair_apply, const_apply, fst_apply, snd_apply, ePar_apply,
    eQ_apply, eR_apply, envT_par, envT_Q, envT_R]
  rw [LenIntro.length_linF]
  exact LenIntro.lin_coef _ _ _ t κ

theorem length_lenU_false (c lam n : ℕ) (T : TailoredVerifier 7) (t : Label) :
    (lenU t false (envT c lam n T)).length =
      Typed.lenR (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) t := by
  rw [length_lenU]; rfl

theorem length_totLenU (c lam n : ℕ) (T : TailoredVerifier 7) (t : Label) :
    (totLenU t (envT c lam n T)).length = Typed.len (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) t := by
  rw [totLenU, catF_apply, List.length_append, length_lenU, length_lenU]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have := Typed.lenR_le_len (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) t
  omega

/-! ## The Pauli to auxiliary clauses -/

variable (U : ClockedUniversalMachine)

/-- `Q` zeros. -/
abbrev zD : PolyTimeFun DIn BitStr := zerosOf (eQ.comp dE)

/-- The first hiding edge's constraints (`pauliHideCons` at the first factor and its kernel
generators), role `w`. -/
def pauliHideP (w : Bool) : PolyTimeFun DIn (List BitStr) :=
  PauliHideProg.pauliHideProg.comp ((ePar.comp dE).pair
    ((kAt (CLData.factor U 0) w zD).pair (kAt (CLData.kernelGenerators U 0) w zD)))

/-- The directed clauses from a Pauli label to an auxiliary one (`Typed.pauliDir`). -/
def pauliDirP (p : Ty) (t : AuxType 7 × Bool) : PolyTimeFun DIn (List BitStr) :=
  catF (if p = .pauli .Z ∧ t.1 = .sample then
      guardOf (PauliConsProg.zGuardProg.comp ((ePar.comp dE).pair (dA.pair yb)))
        (catF ((totLenU (.inl p)).comp dE) ((totLenU (.inr t)).comp dE))
    else const [])
    (if p = .pauli .X ∧ t.1 = .hide 0 then pauliHideP U t.2 else const [])

/-- The constraints from a Pauli label to an auxiliary one (`Typed.pauliAux`). -/
def pauliAuxP (p : Ty) (t : AuxType 7 × Bool) : PolyTimeFun DIn (List BitStr) :=
  ite (atReg (GP U t) yb) (pauliDirP U p t)
    (guardOf (const false) (catF ((totLenU (.inl p)).comp dE) ((totLenU (.inr t)).comp dE)))

/-! ## The pair of questions -/

/-- The environment, the two readable answers and the two questions' bits. -/
abbrev IIn := DIn × BitStr × BitStr

def iD : PolyTimeFun IIn DIn := fst
def iX : PolyTimeFun IIn BitStr := fst.comp snd
def iY : PolyTimeFun IIn BitStr := snd.comp snd

@[simp] theorem iD_apply (i : IIn) : iD i = i.1 := rfl
@[simp] theorem iX_apply (i : IIn) : iX i = i.2.1 := rfl
@[simp] theorem iY_apply (i : IIn) : iY i = i.2.2 := rfl

/-- The number of bits of a graph view. -/
abbrev gd : ℕ := graphDim Label

/-- The content of a question: its bits after the graph view. -/
def contentOf (x : PolyTimeFun IIn BitStr) : PolyTimeFun IIn BitStr :=
  dropOf x (const (unary gd))

@[simp] theorem contentOf_apply (x : PolyTimeFun IIn BitStr) (i : IIn) :
    contentOf x i = (x i).drop gd := by
  simp [contentOf]

/-- The edge of the two graph views (the router's `selectedEdge`), by a finite table. -/
def edgeSel : PolyTimeFun IIn (Option (Label × Label)) :=
  (finiteFunction fun p : (Fin gd → 𝔽₂) × (Fin gd → 𝔽₂) =>
      DeciderProgram.selectedEdge DecisionCompiler.graph (pull graphEquiv.toEmbedding p.1)
        (pull graphEquiv.toEmbedding p.2)).comp
    (((readVector gd).comp iX).pair ((readVector gd).comp iY))

theorem edgeSel_apply (i : IIn) :
    edgeSel i = DeciderProgram.selectedEdge DecisionCompiler.graph (graphOfBits i.2.1)
      (graphOfBits i.2.2) := rfl

/-- The constraints at a pair of labels before the length check (`Typed.consRaw`). -/
def rawP : Label → Label → PolyTimeFun IIn (List BitStr)
  | .inl p, .inl q => PauliConsProg.pauliConsProg.comp ((ePar.comp (dE.comp iD)).pair
      ((eQ.comp (dE.comp iD)).pair (((const p).pair (contentOf iX)).pair
        ((const q).pair (contentOf iY)))))
  | .inl p, .inr t => (pauliAuxP U p t).comp iD
  | .inr t, .inl p => swapConsF.comp (((pauliAuxP U p t).comp (swapD.comp iD)).pair
      (((totLenU (.inr t)).comp (dE.comp iD)).pair ((totLenU (.inl p)).comp (dE.comp iD))))
  | .inr t, .inr u => (auxPairP U t u).comp iD

/-- The constraints at an edge (`Typed.consL`), none off the edges. -/
def consP : Option (Label × Label) → PolyTimeFun IIn (List BitStr)
  | none => const []
  | some (u, v) => ite (andOf (eqUOf (length.comp (dA.comp iD)) ((lenU u false).comp (dE.comp iD)))
      (eqUOf (length.comp (dB.comp iD)) ((lenU v false).comp (dE.comp iD)))) (rawP U u v) (const [])

/-- **The core of the processor**: branch on the edge. -/
def mainP : PolyTimeFun IIn (List BitStr) := choose edgeSel (consP U) (const [])

/-! ## Correctness -/

/-- The edge of a pair of detyped questions is the router's selected edge, with the contents. -/
theorem edgeOf_eq_selectedEdge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : Coord Label ι → ZMod 2) :
    edgeOf DecisionCompiler.graph x y =
      (DeciderProgram.selectedEdge DecisionCompiler.graph (pull .inl x) (pull .inl y)).map
        fun uv => ((uv.1, pull .inr x), (uv.2, pull .inr y)) := by
  unfold edgeOf DeciderProgram.selectedEdge
  cases select DecisionCompiler.graph false (pull .inl x) <;>
    cases select DecisionCompiler.graph true (pull .inl y) <;> try rfl
  dsimp only
  split_ifs <;> rfl

section Correct

variable {c lam n : ℕ} (hc : 1 ≤ c) (he : Even c) (T : TailoredVerifier 7) (V : Verifier 7)
  (hT : T.IsBounded lam) (hV : V.IsBounded lam) (hn : 1 ≤ n)
  (hsamp : V.sampler.prog = T.sampler.prog)
  (hs : V.sampler.dim (2 ^ n) ≤ QQ c lam n)

include hT hV hn hsamp in
/-- **The first hiding edge's constraints.** -/
theorem pauliHideP_spec (w : Bool) (aR bR : BitStr) :
    pauliHideP U w (envT c lam n T, aR, bR) =
      PauliHide.pauliHideCons (kk c lam n) (PauliSamplerParameters.fieldBits_pos c lam n)
        (PauliSamplerParameters.fieldBits_odd he lam n) (jj c lam n) (LL V hs w)
        (regKerGens (QQ c lam n) _ (CLChecks.stageLinear (LL V hs w) 0 0)) := by
  refine Eq.trans ?_ (PauliHideProg.pauliHideProg_eq _ _ _ _ _ _)
  rw [regKerGens_toBits]
  have hf := CLData.factor_correct U V hV hn hs w (k := 0) (by omega) 0 (CLData.guard_zero V hs w 0)
  have hg := CLData.kernelGenerators_correct U V hV hn hs w (k := 0) (by omega) 0
    (CLData.guard_zero V hs w 0)
  rw [toBits_zero] at hf hg
  simp only [pauliHideP, comp_apply, pair_apply, ePar_apply, dE_apply, kAt_apply,
    ctxP_envT T V hT hsamp, zerosOf_apply, envT_par, eQ_apply, envT_Q, length_unary, hf, hg]

theorem pauliLenR_Z (k m : ℕ) : PauliCons.pauliLenR k m (.pauli .Z) = pauliLen m k (.pauli .Z) := by
  simp [PauliCons.pauliLenR, pauliRead]

include hT hV hn hsamp in
/-- **The directed clauses from a Pauli label to an auxiliary one.** -/
theorem pauliDirP_spec (p : Ty) (t : AuxType 7 × Bool) (aR bR : BitStr)
    (ha : aR.length = PauliCons.pauliLenR (kk c lam n) (2 ^ jj c lam n) p) :
    pauliDirP U p t (envT c lam n T, aR, bR) =
      Typed.pauliDir (kk c lam n) (PauliSamplerParameters.fieldBits_pos c lam n)
        (PauliSamplerParameters.fieldBits_odd he lam n) (jj c lam n) ((2 ^ n) ^ lam) V hs
        (regKerGens (QQ c lam n)) p t aR bR := by
  rw [pauliDirP, catF_apply]
  delta Typed.pauliDir
  congr 1
  · by_cases h : p = .pauli .Z ∧ t.1 = .sample
    · rw [ite_eq_left h, ite_eq_left h, guardOf_apply, catF_apply, List.length_append]
      obtain ⟨rfl, -⟩ := h
      simp only [comp_apply, pair_apply, ePar_apply, dE_apply, dA_apply, regOf_apply, dB_apply,
        envT_par, envT_Q, length_unary, length_totLenU]
      rw [PauliConsProg.zGuardProg_eq _ (PauliSamplerParameters.fieldBits_pos c lam n)
        (PauliSamplerParameters.fieldBits_odd he lam n) _ _ _ (ha.trans (pauliLenR_Z _ _))]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
      rfl
  · by_cases h : p = .pauli .X ∧ t.1 = .hide 0
    · rw [ite_eq_left h, ite_eq_left h]
      exact pauliHideP_spec U he T V hT hV hn hsamp hs t.2 aR bR
    · rw [ite_eq_right h, ite_eq_right h]
      rfl

include hT hV hn hsamp in
/-- **The constraints from a Pauli label to an auxiliary one.** -/
theorem pauliAuxP_spec (p : Ty) (t : AuxType 7 × Bool) (aR bR : BitStr)
    (ha : aR.length = PauliCons.pauliLenR (kk c lam n) (2 ^ jj c lam n) p)
    (hb : bR.length = auxLenR (QQ c lam n) ((2 ^ n) ^ lam) t.1) :
    pauliAuxP U p t (envT c lam n T, aR, bR) =
      Typed.pauliAux (kk c lam n) (PauliSamplerParameters.fieldBits_pos c lam n)
        (PauliSamplerParameters.fieldBits_odd he lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs
        (regKerGens (QQ c lam n)) p t aR bR := by
  have hb' : QQ c lam n ≤ bR.length := hb ▸ auxLenR_add_le t.1
  have hG := GP_envT U T V hT hV hn hsamp hs t _ (length_win_Q hb')
  delta Typed.pauliAux
  rw [pauliAuxP, PolyTimeFun.ite_apply, atReg_apply, regOf_apply, dB_apply, envT_Q,
    length_unary]
  by_cases hg : Typed.G (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs t (win bR 0 (QQ c lam n))
  · rw [ite_eq_left (hG.2 hg), ite_eq_left hg]
    exact pauliDirP_spec U he T V hT hV hn hsamp hs p t aR bR ha
  · rw [ite_eq_right (fun h => hg (hG.1 h)), ite_eq_right hg, guardOf_apply, catF_apply]
    simp only [comp_apply, dE_apply, List.length_append, length_totLenU, const_apply]
    rfl

include hc hT hV hn hsamp in
/-- **The constraints at a pair of labels**, before the length check, for readable answers of
the labels' readable lengths and contents of the sampler's dimension. -/
theorem rawP_spec (u v : Label) (aR bR xs ys : BitStr)
    (hx : (xs.drop gd).length = PauliSampler.dimension c lam n)
    (hy : (ys.drop gd).length = PauliSampler.dimension c lam n)
    (ha : aR.length = Typed.lenR (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) u)
    (hb : bR.length = Typed.lenR (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) v) :
    rawP U u v ((envT c lam n T, aR, bR), xs, ys) =
      Typed.consRaw (kk c lam n) (PauliSamplerParameters.fieldBits_pos c lam n)
        (PauliSamplerParameters.fieldBits_odd he lam n) (jj c lam n) (CanonicalGame.divides c hc lam n)
        ((2 ^ n) ^ lam) T V hs (regKerGens (QQ c lam n)) u v (xs.drop gd) (ys.drop gd) aR bR := by
  rcases u with p | t <;> rcases v with q | u
  · have h := PauliConsProg.pauliConsProg_eq (k := kk c lam n)
      (hk := PauliSamplerParameters.fieldBits_pos c lam n)
      (hodd := PauliSamplerParameters.fieldBits_odd he lam n) (j := jj c lam n)
      (PauliSamplerParameters.selectorBits_le_fieldBits hc lam n)
      (CanonicalGame.divides c hc lam n) p q _ _ aR bR hx hy
    simp only [PauliConsProg.inputOf] at h
    simp only [rawP, comp_apply, pair_apply, ePar_apply, eQ_apply, dE_apply, iD_apply,
      const_apply, contentOf_apply, iX_apply, iY_apply, envT_par, envT_Q]
    exact h
  · exact pauliAuxP_spec U he T V hT hV hn hsamp hs p u aR bR ha hb
  · simp only [rawP, comp_apply, pair_apply, iD_apply, swapConsF_apply, swapD_apply, dE_apply,
      length_totLenU, pauliAuxP_spec U he T V hT hV hn hsamp hs q t bR aR hb ha]
    rfl
  · exact auxPairP_spec U T V hT hV hn hsamp hs t u aR bR ha hb

include hc hT hV hn hsamp in
/-- **The core of the processor at two detyped questions**: the detyped game's constraints. -/
theorem mainP_spec (x y : Coord Label (Fin (PauliSampler.dimension c lam n)) → 𝔽₂)
    (aR bR : BitStr) :
    mainP U ((envT c lam n T, aR, bR), CL.toBits (DeciderProgram.vectorEquiv _ x),
        CL.toBits (DeciderProgram.vectorEquiv _ y)) =
      match edgeOf DecisionCompiler.graph x y with
      | some (u, v) => (Sound.tdata c hc he lam n T V hs (regKerGens (QQ c lam n))).cons u v aR bR
      | none => [] := by
  have hvx : DeciderProgram.vectorEquiv (PauliSampler.dimension c lam n) x =
      push (registerEquiv _).toEmbedding x := rfl
  have hvy : DeciderProgram.vectorEquiv (PauliSampler.dimension c lam n) y =
      push (registerEquiv _).toEmbedding y := rfl
  rw [mainP, choose_apply, edgeSel_apply, edgeOf_eq_selectedEdge, hvx, hvy,
    DeciderProgram.graphOfBits_register, DeciderProgram.graphOfBits_register]
  cases hsel : DeciderProgram.selectedEdge DecisionCompiler.graph (pull .inl x) (pull .inl y) with
  | none => rfl
  | some uv =>
    obtain ⟨u, v⟩ := uv
    simp only [consP, Option.map_some, Sound.tdata, Typed.consL, PolyTimeFun.ite_apply, andOf_apply,
      eqUOf_apply, comp_apply, length_apply, iD_apply, dA_apply, dB_apply, dE_apply,
      length_unary, length_lenU_false, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs with h
    · rw [rawP_spec U hc he T V hT hV hn hsamp hs u v aR bR _ _ (by
        rw [DeciderProgram.drop_register, CL.length_toBits]) (by
        rw [DeciderProgram.drop_register, CL.length_toBits]) h.1 h.2,
        DeciderProgram.drop_register, DeciderProgram.drop_register]
    · rfl

end Correct

end MIPRE.Tailored.Intro.LpIntro

end
