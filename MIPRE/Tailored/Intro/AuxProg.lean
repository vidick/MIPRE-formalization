/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.FormProg

@[expose] public section

/-!
# The auxiliary comparisons of the introspection processor, in polynomial time

The clauses of the auxiliary checks between two answers of the padded layout (`AuxCons.lean`:
`sampleCons`, `readCons`, `hideReadCons`, `hideNextCons`, `sameCons`, `sourceCons`) are lists of
constraints determined by a few readable data: the register length `Q` and the original cutoff
`R`, the readable conditions (as Booleans), the input's split of its answer at the register, the
coordinate sets of the hiding stages (as bit masks), the generators of a kernel, and the input's
own constraints. This file builds each clause as a `Cost.PolyTimeFun` of those data, computed
elsewhere, with `Q`, `R` and the split in unary:

* `sampleConsF`, `readConsF` on `((Q, R), (guard, source guard), sL)`;
* `hideReadConsF` on `((Q, R), guard)`;
* `hideNextConsF` on `(Q, guard, (masks), generators)`;
* `sameConsF` on `((Q, R), (hide?, read?), (guard, source guard), sL)`, the kind of the label
  given by two Booleans (`isHideT`, `isReadT`) so that one program serves every label;
* `sourceConsF` on `((Q, R), ((sRa, sLa), (sRb, sLb)), the input's constraints)`;
* `auxLenF`, the length `auxLen` of a label's answers, for the swap (`swapConsF`);
* `auxPairF`, the assembly `auxPair` at a pair of labels from the consistency list and the two
  directed lists (`dirAux`), computed by the caller.

Each `_spec` lemma states that on the encodings of the semantic data the program outputs the
semantic list.
-/

namespace MIPRE.Tailored.Intro

open Cost Cost.PolyTimeFun Polynomial CL MIPRE.Introspection

/-! ## The forms on a generic input -/

section Generic

variable {ι : Type} [SizedEncoding ι]

/-- `guardCons b d`. -/
noncomputable def guardOf (b : PolyTimeFun ι Bool) (d : PolyTimeFun ι Unary) :
    PolyTimeFun ι (List BitStr) :=
  guardConsF.comp (b.pair d)

@[simp] theorem guardOf_apply (b : PolyTimeFun ι Bool) (d : PolyTimeFun ι Unary) (a : ι) :
    guardOf b d a = guardCons (b a) (d a).length := by
  simp [guardOf]

/-- `eqCons la lb oa ob m`. -/
noncomputable def eqOf (la lb oa ob m : PolyTimeFun ι Unary) : PolyTimeFun ι (List BitStr) :=
  eqConsF.comp (((la.pair oa).pair (lb.pair ob)).pair m)

@[simp] theorem eqOf_apply (la lb oa ob m : PolyTimeFun ι Unary) (a : ι) :
    eqOf la lb oa ob m a =
      eqCons (la a).length (lb a).length (oa a).length (ob a).length (m a).length := by
  simp [eqOf]

/-- `projEqCons la lb oa ob S`, the set given by its mask. -/
noncomputable def projEqOf (la lb oa ob : PolyTimeFun ι Unary) (m : PolyTimeFun ι BitStr) :
    PolyTimeFun ι (List BitStr) :=
  projEqConsF.comp (((la.pair oa).pair (lb.pair ob)).pair m)

@[simp] theorem projEqOf_apply (la lb oa ob : PolyTimeFun ι Unary) (m : PolyTimeFun ι BitStr)
    (a : ι) :
    projEqOf la lb oa ob m a = projEqConsF (lay (la a).length (oa a).length (lb a).length
      (ob a).length, m a) := by
  simp [projEqOf, lay, unary_length]

/-- `dualCons la lb oa ob S gens`, the set given by its mask, the generators by their bits. -/
noncomputable def dualOf (la lb oa ob : PolyTimeFun ι Unary) (m : PolyTimeFun ι BitStr)
    (gs : PolyTimeFun ι (List BitStr)) : PolyTimeFun ι (List BitStr) :=
  dualConsF.comp (((la.pair oa).pair (lb.pair ob)).pair (m.pair gs))

@[simp] theorem dualOf_apply (la lb oa ob : PolyTimeFun ι Unary) (m : PolyTimeFun ι BitStr)
    (gs : PolyTimeFun ι (List BitStr)) (a : ι) :
    dualOf la lb oa ob m gs a = dualConsF (lay (la a).length (oa a).length (lb a).length
      (ob a).length, m a, gs a) := by
  simp [dualOf, lay, unary_length]

/-- The input-answer equality `srcEqCons`: the guard `g` on `la + lb` bits, and the equality of
the linear windows at `oLa`, `oLb`, of length `s`. -/
noncomputable def srcEqOf (la lb oLa oLb : PolyTimeFun ι Unary) (g : PolyTimeFun ι Bool)
    (s : PolyTimeFun ι Unary) : PolyTimeFun ι (List BitStr) :=
  catF (guardOf g (catF la lb)) (eqOf la lb oLa oLb s)

@[simp] theorem srcEqOf_apply (la lb oLa oLb : PolyTimeFun ι Unary) (g : PolyTimeFun ι Bool)
    (s : PolyTimeFun ι Unary) (a : ι) :
    srcEqOf la lb oLa oLb g s a = guardCons (g a) ((la a).length + (lb a).length) ++
      eqCons (la a).length (lb a).length (oLa a).length (oLb a).length (s a).length := by
  simp [srcEqOf]

/-- The sum of three unary numbers. -/
noncomputable def add3 (u v w : PolyTimeFun ι Unary) : PolyTimeFun ι Unary := catF u (catF v w)

@[simp] theorem length_add3 (u v w : PolyTimeFun ι Unary) (a : ι) :
    (add3 u v w a).length = (u a).length + ((v a).length + (w a).length) := by
  simp [add3]

end Generic

/-! ## The register and the cutoff -/

section QR

variable {ι : Type} [SizedEncoding ι] (Q R : PolyTimeFun ι Unary)

/-- `Q + R`. -/
noncomputable def uQR : PolyTimeFun ι Unary := catF Q R
/-- `Q + 2R`. -/
noncomputable def uQ2R : PolyTimeFun ι Unary := add3 Q R R
/-- `2Q + R`. -/
noncomputable def u2QR : PolyTimeFun ι Unary := add3 Q Q R
/-- `2Q + 2R`. -/
noncomputable def u2Q2R : PolyTimeFun ι Unary := catF (catF Q Q) (catF R R)
/-- `2Q`. -/
noncomputable def u2Q : PolyTimeFun ι Unary := catF Q Q
/-- `3Q`. -/
noncomputable def u3Q : PolyTimeFun ι Unary := add3 Q Q Q

variable (a : ι)

@[simp] theorem length_uQR : (uQR Q R a).length = (Q a).length + (R a).length := by simp [uQR]
@[simp] theorem length_uQ2R : (uQ2R Q R a).length = (Q a).length + 2 * (R a).length := by
  simp [uQ2R]; omega
@[simp] theorem length_u2QR : (u2QR Q R a).length = 2 * (Q a).length + (R a).length := by
  simp [u2QR]; omega
@[simp] theorem length_u2Q2R : (u2Q2R Q R a).length = 2 * (Q a).length + 2 * (R a).length := by
  simp [u2Q2R]; omega
@[simp] theorem length_u2Q : (u2Q Q a).length = 2 * (Q a).length := by simp [u2Q]; omega
@[simp] theorem length_u3Q : (u3Q Q a).length = 3 * (Q a).length := by simp [u3Q]; omega

end QR

/-- The register length and the cutoff of an input `((Q, R), _)`. -/
noncomputable def inQ {β : Type} [SizedEncoding β] : PolyTimeFun ((Unary × Unary) × β) Unary :=
  fst.comp fst
noncomputable def inR {β : Type} [SizedEncoding β] : PolyTimeFun ((Unary × Unary) × β) Unary :=
  snd.comp fst

@[simp] theorem inQ_apply {β : Type} [SizedEncoding β] (p : (Unary × Unary) × β) :
    inQ p = p.1.1 := rfl
@[simp] theorem inR_apply {β : Type} [SizedEncoding β] (p : (Unary × Unary) × β) :
    inR p = p.1.2 := rfl

variable (Q R : ℕ) (sR sL : AuxType 7 × Bool → BitStr → ℕ) (L : Bool → CL.CLFun 𝔽₂ (Fin Q) 7)

/-! ## Sampling and reading -/

/-- The input of the sampling and reading comparisons: `((Q, R), (guard, source guard), sL)`. -/
abbrev PairIn := (Unary × Unary) × (Bool × Bool) × Unary

/-- **The sampling comparison** `sampleCons`. -/
noncomputable def sampleConsF : PolyTimeFun PairIn (List BitStr) :=
  catF (guardOf (fst.comp (fst.comp snd)) (catF (uQ2R inQ inR) (uQ2R inQ inR)))
    (srcEqOf (uQ2R inQ inR) (uQ2R inQ inR) (uQR inQ inR) (uQR inQ inR)
      (snd.comp (fst.comp snd)) (snd.comp snd))

@[simp] theorem sampleConsF_apply (Q R : Unary) (g₁ g₂ : Bool) (s : Unary) :
    sampleConsF ((Q, R), (g₁, g₂), s) =
      guardCons g₁ (Q.length + 2 * R.length + (Q.length + 2 * R.length)) ++
        (guardCons g₂ (Q.length + 2 * R.length + (Q.length + 2 * R.length)) ++
          eqCons (Q.length + 2 * R.length) (Q.length + 2 * R.length) (Q.length + R.length)
            (Q.length + R.length) s.length) := by
  simp [sampleConsF]

/-- **The sampling comparison, on the encoded data.** -/
theorem sampleConsF_spec (w : Bool) (aR bR : BitStr) :
    sampleConsF ((unary Q, unary R),
      (decide (ofBits Q (win aR 0 Q) = (L w).eval (ofBits Q (win bR 0 Q))),
        decide (sR (.introspect, w) (win aR 0 Q) = sR (.sample, w) (win bR 0 Q) ∧
          sL (.introspect, w) (win aR 0 Q) = sL (.sample, w) (win bR 0 Q) ∧
          win aR Q (sR (.introspect, w) (win aR 0 Q)) = win bR Q (sR (.sample, w) (win bR 0 Q)))),
      unary (sL (.introspect, w) (win aR 0 Q))) =
    sampleCons Q R sR sL L w aR bR := by
  simp [sampleCons, srcEqCons, auxLen]

/-- **The reading comparison** `readCons`. -/
noncomputable def readConsF : PolyTimeFun PairIn (List BitStr) :=
  catF (guardOf (fst.comp (fst.comp snd)) (catF (uQ2R inQ inR) (u2Q2R inQ inR)))
    (srcEqOf (uQ2R inQ inR) (u2Q2R inQ inR) (uQR inQ inR) (u2QR inQ inR)
      (snd.comp (fst.comp snd)) (snd.comp snd))

@[simp] theorem readConsF_apply (Q R : Unary) (g₁ g₂ : Bool) (s : Unary) :
    readConsF ((Q, R), (g₁, g₂), s) =
      guardCons g₁ (Q.length + 2 * R.length + (2 * Q.length + 2 * R.length)) ++
        (guardCons g₂ (Q.length + 2 * R.length + (2 * Q.length + 2 * R.length)) ++
          eqCons (Q.length + 2 * R.length) (2 * Q.length + 2 * R.length) (Q.length + R.length)
            (2 * Q.length + R.length) s.length) := by
  simp [readConsF]

/-- **The reading comparison, on the encoded data.** -/
theorem readConsF_spec (w : Bool) (aR bR : BitStr) :
    readConsF ((unary Q, unary R),
      (decide (win aR 0 Q = win bR 0 Q),
        decide (sR (.introspect, w) (win aR 0 Q) = sR (.read, w) (win bR 0 Q) ∧
          sL (.introspect, w) (win aR 0 Q) = sL (.read, w) (win bR 0 Q) ∧
          win aR Q (sR (.introspect, w) (win aR 0 Q)) = win bR Q (sR (.read, w) (win bR 0 Q)))),
      unary (sL (.introspect, w) (win aR 0 Q))) =
    readCons Q R sR sL w aR bR := by
  simp [readCons, srcEqCons, auxLen]

/-! ## Hiding -/

/-- **The comparison of the last Hide with Read** `hideReadCons`, on `((Q, R), guard)`. -/
noncomputable def hideReadConsF : PolyTimeFun ((Unary × Unary) × Bool) (List BitStr) :=
  catF (guardOf snd (catF (u3Q inQ) (u2Q2R inQ inR)))
    (eqOf (u3Q inQ) (u2Q2R inQ inR) inQ (uQR inQ inR) inQ)

@[simp] theorem hideReadConsF_apply (Q R : Unary) (g : Bool) :
    hideReadConsF ((Q, R), g) =
      guardCons g (3 * Q.length + (2 * Q.length + 2 * R.length)) ++
        eqCons (3 * Q.length) (2 * Q.length + 2 * R.length) Q.length (Q.length + R.length)
          Q.length := by
  simp [hideReadConsF]

/-- **The comparison of the last Hide with Read, on the encoded data.** -/
theorem hideReadConsF_spec (w : Bool) (aR bR : BitStr) :
    hideReadConsF ((unary Q, unary R),
      decide ((L w).outputPrefix 6 (ofBits Q (win aR 0 Q)) =
        (L w).outputPrefix 6 (ofBits Q (win bR 0 Q)))) =
    hideReadCons Q R L w aR bR := by
  simp [hideReadCons, auxLen]

/-- The input of the comparison of consecutive Hide levels: `Q`, the guard, the masks of the
prefix register of the next level, of that of the level after it (complemented by the program)
and of the factor of the dual, and the bits of the kernel generators. -/
abbrev HideIn := Unary × Bool × (BitStr × BitStr × BitStr) × List BitStr

/-- The complement of a mask. -/
noncomputable def notMaskF : PolyTimeFun BitStr BitStr := map (ite (PolyTimeFun.id _)
  (const false) (const true))

@[simp] theorem notMaskF_apply (m : BitStr) : notMaskF m = m.map not := by
  simp only [notMaskF, map_apply]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

theorem maskOf_compl {s : ℕ} (S : Finset (Fin s)) : maskOf Sᶜ = (maskOf S).map not := by
  simp [maskOf, List.map_ofFn, Function.comp_def]

/-- **The comparison of consecutive Hide levels** `hideNextCons`. -/
noncomputable def hideNextConsF : PolyTimeFun HideIn (List BitStr) :=
  let Q : PolyTimeFun HideIn Unary := fst
  let m₁ : PolyTimeFun HideIn BitStr := fst.comp (fst.comp (snd.comp snd))
  let m₂ : PolyTimeFun HideIn BitStr :=
    notMaskF.comp (fst.comp (snd.comp (fst.comp (snd.comp snd))))
  let m₃ : PolyTimeFun HideIn BitStr := snd.comp (snd.comp (fst.comp (snd.comp snd)))
  catF (catF (catF (guardOf (fst.comp snd) (catF (u3Q Q) (u3Q Q)))
      (projEqOf (u3Q Q) (u3Q Q) Q Q m₁))
      (projEqOf (u3Q Q) (u3Q Q) (u2Q Q) (u2Q Q) m₂))
    (dualOf (u3Q Q) (u3Q Q) (u2Q Q) Q m₃ (snd.comp (snd.comp snd)))

/-- **The comparison of consecutive Hide levels, on the encoded data.** -/
theorem hideNextConsF_spec (kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂))
    (w : Bool) (k : ℕ) (aR bR : BitStr) :
    hideNextConsF (unary Q,
      decide ((L w).outputPrefix k (ofBits Q (win aR 0 Q)) =
        (L w).outputPrefix k (ofBits Q (win bR 0 Q))),
      (maskOf (CLChecks.prefixRegister (L w) (k + 1) (ofBits Q (win bR 0 Q))),
        maskOf (CLChecks.prefixRegister (L w) (k + 2) (ofBits Q (win bR 0 Q))),
        maskOf ((L w).factorOfPrefix (k + 1) (ofBits Q (win bR 0 Q)))),
      (kg _ (CLChecks.stageLinear (L w) (k + 1) (ofBits Q (win bR 0 Q)))).map CL.toBits) =
    hideNextCons Q L kg w k aR bR := by
  simp only [hideNextConsF, catF_apply, guardOf_apply, projEqOf_apply, dualOf_apply, comp_apply,
    fst_apply, snd_apply, notMaskF_apply, ← maskOf_compl, length_unary, List.length_append,
    length_u3Q, length_u2Q, dualConsF_spec, hideNextCons]
  rw [projEqConsF_spec, projEqConsF_spec]

/-! ## Consistency at one label -/

/-- Whether a label is a Hide label. -/
def isHideT : AuxType 7 → Bool
  | .hide _ => true
  | _ => false

/-- Whether a label is the Read label. -/
def isReadT : AuxType 7 → Bool
  | .read => true
  | _ => false

/-- The input of the consistency comparison: `((Q, R), (hide?, read?), (guard, source guard),
sL)`. -/
abbrev SameIn := (Unary × Unary) × (Bool × Bool) × (Bool × Bool) × Unary

section Same

/-- The guard, the source guard and the split of the consistency comparison. -/
noncomputable def sG : PolyTimeFun SameIn Bool := fst.comp (fst.comp (snd.comp snd))
noncomputable def sG₂ : PolyTimeFun SameIn Bool := snd.comp (fst.comp (snd.comp snd))
noncomputable def sS : PolyTimeFun SameIn Unary := snd.comp (snd.comp snd)

/-- **Consistency at one label** `sameCons`, the kind of the label given by two Booleans. -/
noncomputable def sameConsF : PolyTimeFun SameIn (List BitStr) :=
  ite (fst.comp (fst.comp snd))
    (catF (guardOf sG (catF (u3Q inQ) (u3Q inQ)))
      (catF (eqOf (u3Q inQ) (u3Q inQ) inQ inQ inQ)
        (eqOf (u3Q inQ) (u3Q inQ) (u2Q inQ) (u2Q inQ) inQ)))
    (ite (snd.comp (fst.comp snd))
      (catF (guardOf sG (catF (u2Q2R inQ inR) (u2Q2R inQ inR)))
        (catF (eqOf (u2Q2R inQ inR) (u2Q2R inQ inR) (uQR inQ inR) (uQR inQ inR) inQ)
          (srcEqOf (u2Q2R inQ inR) (u2Q2R inQ inR) (u2QR inQ inR) (u2QR inQ inR) sG₂ sS)))
      (catF (guardOf sG (catF (uQ2R inQ inR) (uQ2R inQ inR)))
        (srcEqOf (uQ2R inQ inR) (uQ2R inQ inR) (uQR inQ inR) (uQR inQ inR) sG₂ sS)))

end Same

/-- **Consistency at one label, on the encoded data.** -/
theorem sameConsF_spec (t : AuxType 7 × Bool) (aR bR : BitStr) :
    sameConsF ((unary Q, unary R), (isHideT t.1, isReadT t.1),
      (decide (win aR 0 Q = win bR 0 Q),
        decide (sR t (win aR 0 Q) = sR t (win bR 0 Q) ∧ sL t (win aR 0 Q) = sL t (win bR 0 Q) ∧
          win aR Q (sR t (win aR 0 Q)) = win bR Q (sR t (win bR 0 Q)))),
      unary (sL t (win aR 0 Q))) =
    sameCons Q R sR sL t aR bR := by
  obtain ⟨t, v⟩ := t
  cases t <;>
    simp [sameConsF, sameCons, isHideT, isReadT, sG, sG₂, sS, srcEqCons, auxLen]

/-! ## The source game -/

/-- The input of the source comparison: `((Q, R), ((sRa, sLa), (sRb, sLb)), constraints)`. -/
abbrev SourceIn := (Unary × Unary) × ((Unary × Unary) × (Unary × Unary)) × List BitStr

/-- **The source game's constraints** `sourceCons`: the input's constraints, re-indexed. -/
noncomputable def sourceConsF : PolyTimeFun SourceIn (List BitStr) :=
  (mapWith reindexF).comp ((snd.comp snd).pair
    (fst.pair ((fst.comp snd).pair ((uQ2R inQ inR).pair (uQ2R inQ inR)))))

@[simp] theorem sourceConsF_apply (Q R sRa sLa sRb sLb : Unary) (cs : List BitStr) :
    sourceConsF ((Q, R), ((sRa, sLa), (sRb, sLb)), cs) =
      cs.map (reindex Q.length R.length sRa.length sLa.length sRb.length sLb.length
        (Q.length + 2 * R.length) (Q.length + 2 * R.length)) := by
  simp [sourceConsF]

/-- **The source game's constraints, on the encoded data**: the last input is the input's
constraint list at the two registers and readable input answers. -/
theorem sourceConsF_spec (srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr)
    (aR bR : BitStr) :
    sourceConsF ((unary Q, unary R),
      ((unary (sR (.introspect, false) (win aR 0 Q)), unary (sL (.introspect, false) (win aR 0 Q))),
        (unary (sR (.introspect, true) (win bR 0 Q)), unary (sL (.introspect, true) (win bR 0 Q)))),
      srcCons (win aR 0 Q) (win bR 0 Q) (win aR Q (sR (.introspect, false) (win aR 0 Q)))
        (win bR Q (sR (.introspect, true) (win bR 0 Q)))) =
    sourceCons Q R sR sL srcCons aR bR := by
  simp [sourceCons, auxLen]

/-! ## The length of a label's answers -/

/-- **The length of a label's answers** `auxLen`, on `((Q, R), (hide?, read?))`. -/
noncomputable def auxLenF : PolyTimeFun ((Unary × Unary) × (Bool × Bool)) Unary :=
  ite (fst.comp snd) (u3Q inQ) (ite (snd.comp snd) (u2Q2R inQ inR) (uQ2R inQ inR))

theorem auxLenF_spec (t : AuxType 7) :
    auxLenF ((unary Q, unary R), (isHideT t, isReadT t)) = unary (auxLen Q R t) := by
  rw [← unary_length (auxLenF _)]
  congr 1
  cases t <;> simp [auxLenF, isHideT, isReadT, auxLen]

/-! ## A pair of auxiliary answers -/

/-- The input of the assembly at a pair of labels: `((guard, labels equal?), (la, lb), (same,
directed, reverse directed))`, the three lists already computed. -/
abbrev PairAsmIn := (Bool × Bool) × (Unary × Unary) × (List BitStr × List BitStr × List BitStr)

/-- **The constraints at a pair of auxiliary labels** `auxPair`, from the consistency list and the
two directed lists: when the guard holds, the consistency list when the labels agree, the
directed list, and the reverse one swapped; otherwise the rejecting constraint. -/
noncomputable def auxPairF : PolyTimeFun PairAsmIn (List BitStr) :=
  let la : PolyTimeFun PairAsmIn Unary := fst.comp (fst.comp snd)
  let lb : PolyTimeFun PairAsmIn Unary := snd.comp (fst.comp snd)
  ite (fst.comp fst)
    (catF (ite (snd.comp fst) (fst.comp (snd.comp snd)) (const []))
      (catF (fst.comp (snd.comp (snd.comp snd)))
        (swapConsF.comp ((snd.comp (snd.comp (snd.comp snd))).pair (la.pair lb)))))
    (guardOf (const false) (catF la lb))

@[simp] theorem auxPairF_apply (g e : Bool) (la lb : Unary) (same dir rev : List BitStr) :
    auxPairF ((g, e), (la, lb), (same, dir, rev)) =
      if g then (if e then same else []) ++ (dir ++ rev.map (swapCon la.length lb.length))
      else [rejectConstraint (la.length + lb.length)] := by
  cases g <;> cases e <;> simp [auxPairF, guardCons]

open Classical in
/-- **The constraints at a pair of auxiliary labels, on the encoded data.** -/
theorem auxPairF_spec (G : AuxType 7 × Bool → BitStr → Prop)
    (kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂))
    (srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr)
    (t u : AuxType 7 × Bool) (aR bR : BitStr) :
    auxPairF ((decide (G t (win aR 0 Q) ∧ G u (win bR 0 Q)), decide (t = u)),
      (unary (auxLen Q R t.1), unary (auxLen Q R u.1)),
      (sameCons Q R sR sL t aR bR, dirAux Q R sR sL L kg srcCons t u aR bR,
        dirAux Q R sR sL L kg srcCons u t bR aR)) =
    auxPair Q R sR sL L G kg srcCons t u aR bR := by
  rw [auxPairF_apply, auxPair]
  simp only [length_unary, decide_eq_true_eq]

end MIPRE.Tailored.Intro

end
