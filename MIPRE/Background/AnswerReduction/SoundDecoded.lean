/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundGameCheck
import MIPRE.Foundations.OracularTyped

/-!
# Soundness of answer reduction: the decoded strategy

Piece AR-5e of `planning/answer-reduction.md` (`lem:ar-ora`): a POVM strategy for the typed
oracularized game of the input verifier, on the typed strategy's state. An oracle measures the
extracted simultaneous measurement `J` and answers the pair decoded from the first two answer
polynomials its outcome carries on their blocks (`decO`); an isolated player measures the
extracted `G` of its own copy and answers the decoded polynomial (`decV`). The decoder `dec` is a
parameter here.

Each of the nine ordered pairs of roles fails at most (`condFail_OO_le`, `condFail_Ov_le`, ...):

* the game check of an oracle's decoded pair, which fails only if `J`'s outcome is not placed on
  its blocks or the PCP check rejects it at at least half the points (the hypothesis `hgc`, the
  contrapositive of the PCP's soundness): `gcA_le`;
* the disagreement of the decoded answers, which is at most that of the polynomials.

The failure of the decoded strategy is then at most a constant times the errors of
`SoundRelations`, `SoundPoly` and `SoundGameCheck` (`one_sub_povmValue_decoded_le`).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp
open scoped ComplexOrder

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ) (T : TensorProductStrategy (typedGame V n P hk S S' check B)) (B' : ℕ)
  (dec : MvPolynomial (Fin P.m) (Fq P hk) → Verifier.Answers B')

/-! ## The decoding -/

/-- The answer polynomial of copy `i` an outcome of `J` carries: its `i`-th component read on
copy `i`'s block. -/
def gPoly (i : Fin 5) (f : Poly6 P hk) : MvPolynomial (Fin P.m) (Fq P hk) :=
  ((f (blk P i)).blockPoly (blockEmb (P := P) i)).toMv

/-- **An oracle's decoded answer**: the pair decoded from the first two answer polynomials. -/
def decO (f : Poly6 P hk) : OAns (Verifier.Answers B') :=
  .pair (dec (gPoly P hk 0 f)) (dec (gPoly P hk 1 f))

/-- **An isolated player's decoded answer.** -/
def decV (g : Poly1 P hk) : OAns (Verifier.Answers B') :=
  .single (dec (g 0).toMv)

/-- An outcome of `J` is **placed on its blocks** when each of its first five components is the
placement of its reading on its block. -/
def BlockLocal (f : Poly6 P hk) : Prop :=
  ∀ i : Fin 5, f (blk P i) = liftBlk P hk i ((f (blk P i)).blockPoly (blockEmb (P := P) i))

/-- The component of an oracle's answer an isolated player's role checks. -/
def comp {A : Type*} : Role → OAns A → A
  | .bob, .pair _ b => b
  | _, .pair a _ => a
  | _, .single a => a

/-- The answer of an isolated player. -/
def sgl {A : Type*} : OAns A → A
  | .pair a _ => a
  | .single a => a

/-- The typed oracularized game of the input verifier at index `n`, answers of length `B'`. -/
abbrev oGame := CL.Detyping.typedGame roleGraph roleGraph_nonempty
  (fun _ => roleFamily (V.sampler.cl n)) (V.seeded n B').oaccepts

/-- **Alice's decoded measurements.** -/
def MAo : CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
    POVM (OAns (Verifier.Answers B')) (Fin T.dA)
  | (.oracle, y) => ((JA V n P hk S S' check B T y).toPOVM ()).map (decO P hk B' dec)
  | (.alice, y) =>
      ((GA1 V n P hk S S' check B T (roleOf 0) 0 y).toPOVM ()).map (decV P hk B' dec)
  | (.bob, y) =>
      ((GA1 V n P hk S S' check B T (roleOf 1) 1 y).toPOVM ()).map (decV P hk B' dec)

/-- **Bob's decoded measurements.** -/
def MBo : CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
    POVM (OAns (Verifier.Answers B')) (Fin T.dB)
  | (.oracle, y) => ((JB V n P hk S S' check B T y).toPOVM ()).map (decO P hk B' dec)
  | (.alice, y) =>
      ((GB1 V n P hk S S' check B T (roleOf 0) 0 y).toPOVM ()).map (decV P hk B' dec)
  | (.bob, y) =>
      ((GB1 V n P hk S S' check B T (roleOf 1) 1 y).toPOVM ()).map (decV P hk B' dec)

/-- The weight of Alice's `J` outcomes whose decoded pair fails the game check. -/
def gcA (y : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  ∑ f, (if (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true then 0 else
    bornProb T.ψ ((((JA V n P hk S S' check B T y).toPOVM ()).mats f).val)
      (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ))

/-- The weight of Bob's `J` outcomes whose decoded pair fails the game check. -/
def gcB (y : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  ∑ f, (if (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true then 0 else
    bornProb T.ψ (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ)
      ((((JB V n P hk S S' check B T y).toPOVM ()).mats f).val))

/-! ## The nine pairs of roles -/

omit [NeZero P.m] in
theorem dis_map_decO_le {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : dA × dB → ℂ) (M : POVM (Poly6 P hk) dA) (N : POVM (Poly6 P hk) dB) :
    dis ψ ((M.map (decO P hk B' dec)).map id) ((N.map (decO P hk B' dec)).map id) ≤ dis ψ M N := by
  rw [POVM.map_map, POVM.map_map]
  exact dis_map_le ψ M N _

/-- **Two oracles**: the two game checks and the disagreement of the two `J`. -/
theorem condFail_OO_le (y : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec) (.oracle, y) (.oracle, y)
      ≤ gcA V n P hk S S' check B T B' dec y + gcB V n P hk S S' check B T B' dec y
        + dis T.ψ ((JA V n P hk S S' check B T y).toPOVM ())
          ((JB V n P hk S S' check B T y).toPOVM ()) := by
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.oracle, y)) (y := (.oracle, y))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬(SeededGame.shapeOk .oracle a = true ∧
      (V.seeded n B').gameCheck (.oracle, y) a = true))
    (fun b => ¬(SeededGame.shapeOk .oracle b = true ∧
      (V.seeded n B').gameCheck (.oracle, y) b = true)) id id (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        subst hab
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer])
  refine h.trans (add_le_add (add_le_add (le_of_eq ?_) (le_of_eq ?_)) ?_)
  · simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_map_decO_le P hk B' dec T.ψ _ _

omit [NeZero P.m] in
/-- The decoded answer an oracle's `v`-th component and an isolated player's answer agree
whenever the polynomials agree, as placed polynomials. -/
theorem dis_decO_decV_le (i : Fin 5) (v : Role)
    (hv : ∀ f, comp v (decO P hk B' dec f) = dec (gPoly P hk i f)) {dA dB : Type*} [Fintype dA]
    [DecidableEq dA] [Fintype dB] [DecidableEq dB] (ψ : dA × dB → ℂ) (M : POVM (Poly6 P hk) dA)
    (N : POVM (Poly1 P hk) dB) :
    dis ψ ((M.map (decO P hk B' dec)).map (comp v)) ((N.map (decV P hk B' dec)).map sgl)
      ≤ dis ψ (M.map fun f => f (blk P i)) (N.map fun g => liftBlk P hk i (g 0)) := by
  set h : LowIndDegPoly (F := Fq P hk) (m := P.m') (d := dPcp) → Verifier.Answers B' :=
    fun F => dec ((F.blockPoly (blockEmb (P := P) i)).toMv)
  have e1 : (fun f => comp v (decO P hk B' dec f)) = fun f => h (f (blk P i)) :=
    funext fun f => hv f
  have e2 : (fun g => sgl (decV P hk B' dec g)) = fun g => h (liftBlk P hk i (g 0)) :=
    funext fun g => by
      simp only [sgl, decV, h, liftBlk, LowIndDegPoly.blockPoly_liftIdx (blockEmb_injective i)]
  rw [POVM.map_map, POVM.map_map, e1, e2, ← POVM.map_map M (fun f => f (blk P i)) h,
    ← POVM.map_map N (fun g => liftBlk P hk i (g 0)) h]
  exact dis_map_le ψ _ _ h

omit [NeZero P.m] in
/-- The mirror image. -/
theorem dis_decV_decO_le (i : Fin 5) (v : Role)
    (hv : ∀ f, comp v (decO P hk B' dec f) = dec (gPoly P hk i f)) {dA dB : Type*} [Fintype dA]
    [DecidableEq dA] [Fintype dB] [DecidableEq dB] (ψ : dA × dB → ℂ) (N : POVM (Poly1 P hk) dA)
    (M : POVM (Poly6 P hk) dB) :
    dis ψ ((N.map (decV P hk B' dec)).map sgl) ((M.map (decO P hk B' dec)).map (comp v))
      ≤ dis ψ (N.map fun g => liftBlk P hk i (g 0)) (M.map fun f => f (blk P i)) := by
  set h : LowIndDegPoly (F := Fq P hk) (m := P.m') (d := dPcp) → Verifier.Answers B' :=
    fun F => dec ((F.blockPoly (blockEmb (P := P) i)).toMv)
  have e1 : (fun f => comp v (decO P hk B' dec f)) = fun f => h (f (blk P i)) :=
    funext fun f => hv f
  have e2 : (fun g => sgl (decV P hk B' dec g)) = fun g => h (liftBlk P hk i (g 0)) :=
    funext fun g => by
      simp only [sgl, decV, h, liftBlk, LowIndDegPoly.blockPoly_liftIdx (blockEmb_injective i)]
  rw [POVM.map_map, POVM.map_map, e1, e2, ← POVM.map_map M (fun f => f (blk P i)) h,
    ← POVM.map_map N (fun g => liftBlk P hk i (g 0)) h]
  exact dis_map_le ψ _ _ h

theorem dis_map_const {A dA dB : Type*} [Fintype A] [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM A dA) (N : POVM A dB) :
    dis ψ (M.map fun _ => ()) (N.map fun _ => ()) = 0 := by
  rw [dis_map_eq_sum hψ]
  simp

/-- **An oracle and Alice**: the oracle's game check and the disagreement of its first answer
polynomial with Alice's. -/
theorem condFail_Oa_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)
      ≤ gcA V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyA V n P hk S S' check B T 0 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.oracle, yO))
    (y := (.alice, (roleFamily (V.sampler.cl n) .alice).eval x))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬(SeededGame.shapeOk .oracle a = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) a = true))
    (fun b => ¬SeededGame.shapeOk .alice b = true) (comp .alice) sgl (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hB : ∑ b, (if ¬SeededGame.shapeOk .alice b = true then bornProb T.ψ
      (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ) (((MBo V n P hk S S' check B T B' dec
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)).mats b).val) else 0) = 0 := by
    simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hB, add_zero]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decO_decV_le P hk B' dec 0 .alice (fun f => rfl) T.ψ _ _

/-- **An oracle and Bob.** -/
theorem condFail_Ob_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)
      ≤ gcA V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyA V n P hk S S' check B T 1 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.oracle, yO))
    (y := (.bob, (roleFamily (V.sampler.cl n) .bob).eval x))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬(SeededGame.shapeOk .oracle a = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) a = true))
    (fun b => ¬SeededGame.shapeOk .bob b = true) (comp .bob) sgl (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hB : ∑ b, (if ¬SeededGame.shapeOk .bob b = true then bornProb T.ψ
      (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ) (((MBo V n P hk S S' check B T B' dec
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)).mats b).val) else 0) = 0 := by
    simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hB, add_zero]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decO_decV_le P hk B' dec 1 .bob (fun f => rfl) T.ψ _ _

/-- **Alice and an oracle.** -/
theorem condFail_aO_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec)
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ gcB V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyB V n P hk S S' check B T 0 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit
    (x := (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)) (y := (.oracle, yO))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬SeededGame.shapeOk .alice a = true)
    (fun b => ¬(SeededGame.shapeOk .oracle b = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) b = true)) sgl (comp .alice) (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .alice a = true then bornProb T.ψ
      (((MAo V n P hk S S' check B T B' dec
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)).mats a).val)
      (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ) else 0) = 0 := by
    simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  rw [hA, zero_add]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decV_decO_le P hk B' dec 0 .alice (fun f => rfl) T.ψ _ _

/-- **Bob and an oracle.** -/
theorem condFail_bO_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec)
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ gcB V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyB V n P hk S S' check B T 1 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit
    (x := (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)) (y := (.oracle, yO))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬SeededGame.shapeOk .bob a = true)
    (fun b => ¬(SeededGame.shapeOk .oracle b = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) b = true)) sgl (comp .bob) (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .bob a = true then bornProb T.ψ
      (((MAo V n P hk S S' check B T B' dec
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)).mats a).val)
      (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ) else 0) = 0 := by
    simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  rw [hA, zero_add]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decV_decO_le P hk B' dec 1 .bob (fun f => rfl) T.ψ _ _

/-- **Alice and Alice**: the disagreement of the two extracted polynomial measurements. -/
theorem condFail_aa_le (y : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec) (.alice, y) (.alice, y)
      ≤ dis T.ψ ((GA1 V n P hk S S' check B T (roleOf 0) 0 y).toPOVM ())
          ((GB1 V n P hk S S' check B T (roleOf 0) 0 y).toPOVM ()) := by
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.alice, y)) (y := (.alice, y))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬SeededGame.shapeOk .alice a = true) (fun b => ¬SeededGame.shapeOk .alice b = true)
    id id (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        subst hab
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .alice a = true then bornProb T.ψ
      (((MAo V n P hk S S' check B T B' dec (.alice, y)).mats a).val)
      (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ) else 0) = 0 := by
    simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .alice b = true then bornProb T.ψ
      (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ)
      (((MBo V n P hk S S' check B T B' dec (.alice, y)).mats b).val) else 0) = 0 := by
    simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, zero_add, zero_add]
  simp only [MAo, MBo]
  rw [POVM.map_map, POVM.map_map]
  exact dis_map_le T.ψ _ _ _

/-- **Alice and Bob** never fail: only the formats are checked. -/
theorem condFail_ab_le (y y' : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec) (.alice, y) (.bob, y') ≤ 0 := by
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.alice, y)) (y := (.bob, y'))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬SeededGame.shapeOk .alice a = true) (fun b => ¬SeededGame.shapeOk .bob b = true)
    (fun _ => ()) (fun _ => ()) (fun a b ha hb _ => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans (le_of_eq ?_)
  have hA : ∑ a, (if ¬SeededGame.shapeOk .alice a = true then bornProb T.ψ
      (((MAo V n P hk S S' check B T B' dec (.alice, y)).mats a).val)
      (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ) else 0) = 0 := by
    simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .bob b = true then bornProb T.ψ
      (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ)
      (((MBo V n P hk S S' check B T B' dec (.bob, y')).mats b).val) else 0) = 0 := by
    simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, dis_map_const T.ψ_unit]
  norm_num

/-- **Bob and Bob**: the disagreement of the two extracted polynomial measurements. -/
theorem condFail_bb_le (y : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec) (.bob, y) (.bob, y)
      ≤ dis T.ψ ((GA1 V n P hk S S' check B T (roleOf 1) 1 y).toPOVM ())
          ((GB1 V n P hk S S' check B T (roleOf 1) 1 y).toPOVM ()) := by
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.bob, y)) (y := (.bob, y))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬SeededGame.shapeOk .bob a = true) (fun b => ¬SeededGame.shapeOk .bob b = true)
    id id (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        subst hab
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .bob a = true then bornProb T.ψ
      (((MAo V n P hk S S' check B T B' dec (.bob, y)).mats a).val)
      (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ) else 0) = 0 := by
    simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .bob b = true then bornProb T.ψ
      (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ)
      (((MBo V n P hk S S' check B T B' dec (.bob, y)).mats b).val) else 0) = 0 := by
    simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, zero_add, zero_add]
  simp only [MAo, MBo]
  rw [POVM.map_map, POVM.map_map]
  exact dis_map_le T.ψ _ _ _

/-- **Bob and Alice** never fail: only the formats are checked. -/
theorem condFail_ba_le (y y' : Fin (V.sampler.dim n) → 𝔽₂) :
    condFail (oGame V n B') T.ψ (MAo V n P hk S S' check B T B' dec)
        (MBo V n P hk S S' check B T B' dec) (.bob, y) (.alice, y') ≤ 0 := by
  have h := condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.bob, y)) (y := (.alice, y'))
    (MA := MAo V n P hk S S' check B T B' dec) (MB := MBo V n P hk S S' check B T B' dec)
    (fun a => ¬SeededGame.shapeOk .bob a = true) (fun b => ¬SeededGame.shapeOk .alice b = true)
    (fun _ => ()) (fun _ => ()) (fun a b ha hb _ => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans (le_of_eq ?_)
  have hA : ∑ a, (if ¬SeededGame.shapeOk .bob a = true then bornProb T.ψ
      (((MAo V n P hk S S' check B T B' dec (.bob, y)).mats a).val)
      (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ) else 0) = 0 := by
    simp only [MAo]
    rw [sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .alice b = true then bornProb T.ψ
      (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ)
      (((MBo V n P hk S S' check B T B' dec (.alice, y')).mats b).val) else 0) = 0 := by
    simp only [MBo]
    rw [sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, dis_map_const T.ψ_unit]
  norm_num

/-! ## The game check -/

/-- **The PCP's soundness, as the decoded strategy needs it**: an outcome of `J` placed on its
blocks, whose evaluations the check accepts at more than half the points, decodes to a pair the
input's game check accepts. -/
def PcpSound : Prop :=
  ∀ (y : Fin (V.sampler.dim n) → 𝔽₂) (f : Poly6 P hk), BlockLocal P hk f →
    Fintype.card (Fin P.m' → Fq P hk) <
      2 * (univ.filter fun z => check y z (fun j => (f j).eval z) = true).card →
    (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true

/-- The fraction of points at which the check rejects an outcome's evaluations. -/
def rejFrac (y : Fin (V.sampler.dim n) → 𝔽₂) (f : Poly6 P hk) : ℝ :=
  ∑ z, uniform (Fin P.m' → Fq P hk) z *
    (if Rej V n P hk check y z (fun j => (f j).eval z) then 1 else 0)

omit [NeZero P.m] in
theorem rejFrac_nonneg (y : Fin (V.sampler.dim n) → 𝔽₂) (f : Poly6 P hk) :
    0 ≤ rejFrac V n P hk check y f :=
  Finset.sum_nonneg fun z _ => mul_nonneg (by simp [uniform]) (by split_ifs <;> norm_num)

omit [NeZero P.m] in
/-- **A placed outcome whose decoded pair fails the game check is rejected at at least half the
points.** -/
theorem one_le_two_mul_rejFrac (hgc : PcpSound V n P hk check B' dec)
    (y : Fin (V.sampler.dim n) → 𝔽₂) (f : Poly6 P hk) (hbl : BlockLocal P hk f)
    (hg : ¬ (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true) :
    1 ≤ 2 * rejFrac V n P hk check y f := by
  have hn : ¬ (Fintype.card (Fin P.m' → Fq P hk) <
      2 * (univ.filter fun z => check y z (fun j => (f j).eval z) = true).card) :=
    fun h => hg (hgc y f hbl h)
  push Not at hn
  have hsplit := Finset.card_filter_add_card_filter_not (s := univ)
    (fun z : Fin P.m' → Fq P hk => check y z (fun j => (f j).eval z) = true)
  have hN : (0 : ℝ) < Fintype.card (Fin P.m' → Fq P hk) := by positivity
  have hcongr : (univ.filter fun z : Fin P.m' → Fq P hk =>
      ¬ check y z (fun j => (f j).eval z) = true)
      = univ.filter fun z => Rej V n P hk check y z (fun j => (f j).eval z) :=
    Finset.filter_congr fun z _ => by simp [Rej]
  rw [hcongr, Finset.card_univ] at hsplit
  have hrej : rejFrac V n P hk check y f
      = ((univ.filter fun z => Rej V n P hk check y z (fun j => (f j).eval z)).card : ℝ)
        / Fintype.card (Fin P.m' → Fq P hk) := by
    simp only [rejFrac, uniform, ← Finset.mul_sum]
    rw [Finset.sum_boole, inv_mul_eq_div]
  rw [hrej, mul_div_assoc', le_div_iff₀ hN, one_mul]
  have : (Fintype.card (Fin P.m' → Fq P hk) : ℝ) ≤
      2 * ((univ.filter fun z => Rej V n P hk check y z (fun j => (f j).eval z)).card : ℝ) := by
    exact_mod_cast (by omega : Fintype.card (Fin P.m' → Fq P hk) ≤
      2 * (univ.filter fun z => Rej V n P hk check y z (fun j => (f j).eval z)).card)
  exact this

omit [NeZero P.m] in
/-- An outcome not placed on block `i` differs from every placed polynomial. -/
theorem ne_liftBlk_of_not {i : Fin 5} {f : Poly6 P hk}
    (h : ¬ f (blk P i) = liftBlk P hk i ((f (blk P i)).blockPoly (blockEmb (P := P) i)))
    (g : LowIndDegPoly (F := Fq P hk) (m := P.m) (d := dPcp)) : f (blk P i) ≠ liftBlk P hk i g := by
  intro hfg
  apply h
  rw [hfg]
  simp only [liftBlk, LowIndDegPoly.blockPoly_liftIdx (blockEmb_injective i)]

/-- **The oracle's game check under Alice's `J`**: the outcomes not placed on their blocks, which
disagree with Bob's placed `G`, plus twice the weight of the rejected evaluations. -/
theorem gcA_le (hgc : PcpSound V n P hk check B' dec) (x : Fin (V.sampler.dim n) → 𝔽₂) :
    gcA V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ ∑ i : Fin 5, disPolyA V n P hk S S' check B T i x
        + 2 * gcEvA V n P hk S S' check B T x := by
  set y := (roleFamily (V.sampler.cl n) .oracle).eval x
  set M := (JA V n P hk S S' check B T y).toPOVM ()
  set β : Poly6 P hk → ℝ := fun f =>
    bornProb T.ψ ((M.mats f).val) (1 : Matrix (Fin T.dB) (Fin T.dB) ℂ)
  have hβ0 : ∀ f, 0 ≤ β f := fun f => bornProb_nonneg T.ψ (M.posSemidef f)
    Matrix.PosSemidef.one
  -- the placed-block failures
  have hdis : ∀ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
        ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
      ≤ disPolyA V n P hk S S' check B T i x := by
    intro i
    set N := (GB1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()
    have hd : disPolyA V n P hk S S' check B T i x
        = ∑ f, ∑ g, (if f (blk P i) = liftBlk P hk i (g 0) then 0 else 1)
          * bornProb T.ψ ((M.mats f).val) ((N.mats g).val) :=
      dis_map_eq_sum T.ψ_unit M N _ _
    rw [hd]
    refine Finset.sum_le_sum fun f _ => ?_
    split_ifs with hbl
    · exact Finset.sum_nonneg fun g _ => mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg T.ψ (M.posSemidef f) (N.posSemidef g))
    · simp only [β]
      rw [bornProb_one_right T.ψ _ N]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [if_neg (ne_liftBlk_of_not P hk hbl (g 0)), one_mul]
  -- the rejected evaluations
  have hev : gcEvA V n P hk S S' check B T x = ∑ f, rejFrac V n P hk check y f * β f := by
    simp only [gcEvA, rejFrac, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [β, M, y]
    split_ifs <;> ring
  -- pointwise
  have hpt : ∀ f, (if (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true then 0
        else β f)
      ≤ ∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * (rejFrac V n P hk check y f * β f) := by
    intro f
    have hsum0 : 0 ≤ ∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
        ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hβ0 f]
    have hr0 := mul_nonneg (rejFrac_nonneg V n P hk check y f) (hβ0 f)
    split_ifs with hg
    · linarith
    · by_cases hbl : BlockLocal P hk f
      · have h1 := one_le_two_mul_rejFrac V n P hk check B' dec hgc y f hbl hg
        nlinarith [hβ0 f]
      · simp only [BlockLocal, not_forall] at hbl
        obtain ⟨i, hi⟩ := hbl
        have hle : (if f (blk P i) = liftBlk P hk i
            ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
            ≤ ∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
              ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f) :=
          Finset.single_le_sum (f := fun i => if f (blk P i) = liftBlk P hk i
              ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
            (fun i _ => by split_ifs <;> simp [hβ0 f]) (Finset.mem_univ i)
        rw [if_neg hi] at hle
        linarith
  calc gcA V n P hk S S' check B T B' dec y
      ≤ ∑ f, (∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * (rejFrac V n P hk check y f * β f)) := Finset.sum_le_sum fun f _ => hpt f
    _ = ∑ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * gcEvA V n P hk S S' check B T x := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, hev, Finset.mul_sum]
    _ ≤ _ := by
        have := Finset.sum_le_sum fun i (_ : i ∈ univ) => hdis i
        linarith

/-- **The oracle's game check under Bob's `J`**, the mirror image. -/
theorem gcB_le (hgc : PcpSound V n P hk check B' dec) (x : Fin (V.sampler.dim n) → 𝔽₂) :
    gcB V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ ∑ i : Fin 5, disPolyB V n P hk S S' check B T i x
        + 2 * gcEvB V n P hk S S' check B T x := by
  set y := (roleFamily (V.sampler.cl n) .oracle).eval x
  set M := (JB V n P hk S S' check B T y).toPOVM ()
  set β : Poly6 P hk → ℝ := fun f =>
    bornProb T.ψ (1 : Matrix (Fin T.dA) (Fin T.dA) ℂ) ((M.mats f).val)
  have hβ0 : ∀ f, 0 ≤ β f := fun f => bornProb_nonneg T.ψ Matrix.PosSemidef.one (M.posSemidef f)
  have hdis : ∀ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
        ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
      ≤ disPolyB V n P hk S S' check B T i x := by
    intro i
    set N := (GA1 V n P hk S S' check B T (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ()
    have hd : disPolyB V n P hk S S' check B T i x
        = ∑ g, ∑ f, (if liftBlk P hk i (g 0) = f (blk P i) then 0 else 1)
          * bornProb T.ψ ((N.mats g).val) ((M.mats f).val) :=
      dis_map_eq_sum T.ψ_unit N M _ _
    rw [hd, Finset.sum_comm]
    refine Finset.sum_le_sum fun f _ => ?_
    split_ifs with hbl
    · exact Finset.sum_nonneg fun g _ => mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg T.ψ (N.posSemidef g) (M.posSemidef f))
    · simp only [β]
      rw [bornProb_one_left T.ψ N]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [if_neg (Ne.symm (ne_liftBlk_of_not P hk hbl (g 0))), one_mul]
  have hev : gcEvB V n P hk S S' check B T x = ∑ f, rejFrac V n P hk check y f * β f := by
    simp only [gcEvB, rejFrac, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [β, M, y]
    split_ifs <;> ring
  have hpt : ∀ f, (if (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true then 0
        else β f)
      ≤ ∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * (rejFrac V n P hk check y f * β f) := by
    intro f
    have hsum0 : 0 ≤ ∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
        ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hβ0 f]
    have hr0 := mul_nonneg (rejFrac_nonneg V n P hk check y f) (hβ0 f)
    split_ifs with hg
    · linarith
    · by_cases hbl : BlockLocal P hk f
      · have h1 := one_le_two_mul_rejFrac V n P hk check B' dec hgc y f hbl hg
        nlinarith [hβ0 f]
      · simp only [BlockLocal, not_forall] at hbl
        obtain ⟨i, hi⟩ := hbl
        have hle : (if f (blk P i) = liftBlk P hk i
            ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
            ≤ ∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
              ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f) :=
          Finset.single_le_sum (f := fun i => if f (blk P i) = liftBlk P hk i
              ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
            (fun i _ => by split_ifs <;> simp [hβ0 f]) (Finset.mem_univ i)
        rw [if_neg hi] at hle
        linarith
  calc gcB V n P hk S S' check B T B' dec y
      ≤ ∑ f, (∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * (rejFrac V n P hk check y f * β f)) := Finset.sum_le_sum fun f _ => hpt f
    _ = ∑ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * gcEvB V n P hk S S' check B T x := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, hev, Finset.mul_sum]
    _ ≤ _ := by
        have := Finset.sum_le_sum fun i (_ : i ∈ univ) => hdis i
        linarith

/-! ## The value of the decoded strategy -/

theorem one_sub_value_nonneg : 0 ≤ 1 - T.value := sub_nonneg.mpr (T.value_le_one)

theorem err1_nonneg : 0 ≤ err1 V n P hk S S' check B T :=
  Simul.deltaSim_nonneg _ _ _ _ <| by
    have := one_sub_value_nonneg V n P hk S S' check B T; positivity

theorem err6_nonneg : 0 ≤ err6 V n P hk S S' check B T :=
  Simul.deltaSim_nonneg _ _ _ _ <| by
    have := one_sub_value_nonneg V n P hk S S' check B T; positivity

/-- The combined error of the decoded strategy's analysis. -/
def errD : ℝ :=
  11 * (err6 V n P hk S S' check B T + 2916 * (1 - T.value) + err1 V n P hk S S' check B T)
    + errSZ P hk

theorem sum_disPolyA_le' (i : Fin 5) :
    ∑ x, disPolyA V n P hk S S' check B T i x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T :=
  sum_disPolyA_le V n P hk S S' check B T i

theorem sum_disPolyB_le' (i : Fin 5) :
    ∑ x, disPolyB V n P hk S S' check B T i x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T := by
  have h := sum_disPolyB_le V n P hk S S' check B T i
  unfold errD
  linarith

/-- **Alice's oracles' game checks**, summed over the oracle halves. -/
theorem sum_gcA_le (hgc : PcpSound V n P hk check B' dec) :
    ∑ x, gcA V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (7 * errD V n P hk S S' check B T) := by
  have h1 := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    gcA_le V n P hk S S' check B T B' dec hgc x
  have h2 := sum_gcEvA_le V n P hk S S' check B T
  have h3 : ∑ i : Fin 5, ∑ x, disPolyA V n P hk S S' check B T i x
      ≤ ∑ _i : Fin 5, Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T :=
    Finset.sum_le_sum fun i _ => sum_disPolyA_le' V n P hk S S' check B T i
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  have hX : (0 : ℝ) ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) := by positivity
  have he1 := err1_nonneg V n P hk S S' check B T
  have hsz := errSZ_nonneg P hk
  have hθ := one_sub_value_nonneg V n P hk S S' check B T
  have he6 := err6_nonneg V n P hk S S' check B T
  have hG : err6 V n P hk S S' check B T + 2916 * (1 - T.value)
      ≤ errD V n P hk S S' check B T := by unfold errD; linarith
  have := mul_le_mul_of_nonneg_left hG hX
  push_cast at h3
  nlinarith

/-- **Bob's oracles' game checks**, summed over the oracle halves. -/
theorem sum_gcB_le (hgc : PcpSound V n P hk check B' dec) :
    ∑ x, gcB V n P hk S S' check B T B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (7 * errD V n P hk S S' check B T) := by
  have h1 := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    gcB_le V n P hk S S' check B T B' dec hgc x
  have h2 := sum_gcEvB_le V n P hk S S' check B T
  have h3 : ∑ i : Fin 5, ∑ x, disPolyB V n P hk S S' check B T i x
      ≤ ∑ _i : Fin 5, Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T :=
    Finset.sum_le_sum fun i _ => sum_disPolyB_le' V n P hk S S' check B T i
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  have hX : (0 : ℝ) ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) := by positivity
  have he1 := err1_nonneg V n P hk S S' check B T
  have hsz := errSZ_nonneg P hk
  have hθ := one_sub_value_nonneg V n P hk S S' check B T
  have he6 := err6_nonneg V n P hk S S' check B T
  have hG : err6 V n P hk S S' check B T + 2916 * (1 - T.value)
      ≤ errD V n P hk S S' check B T := by unfold errD; linarith
  have := mul_le_mul_of_nonneg_left hG hX
  push_cast at h3
  nlinarith

/-- **The two oracles' `J` disagree** at most the sixth copy's extraction error, on average. -/
theorem sum_dis_JA_JB_le :
    ∑ x, dis T.ψ ((JA V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x)).toPOVM
        ()) ((JB V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x)).toPOVM ())
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * err6 V n P hk S S' check B T := by
  refine le_trans (Finset.sum_le_sum fun x _ => ?_) (sum_deltaSim6_le V n P hk S S' check B T)
  obtain ⟨-, -, h3⟩ := ext6_spec V n P hk S S' check B T
    ((roleFamily (V.sampler.cl n) .oracle).eval x)
  have := sum_dis_le_of_inconsistency T.ψ_unit _ _ h3
  simpa using this

/-- **Two isolated players' `G` disagree** at most copy `i`'s extraction error, on average. -/
theorem sum_dis_GA_GB_le (i : Fin 5) :
    ∑ x, dis T.ψ ((GA1 V n P hk S S' check B T (roleOf i) i
        ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ())
        ((GB1 V n P hk S S' check B T (roleOf i) i
          ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)).toPOVM ())
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * err1 V n P hk S S' check B T := by
  refine le_trans (Finset.sum_le_sum fun x _ => ?_)
    (sum_deltaSim1_le V n P hk S S' check B T (ldStep_roleOf i))
  obtain ⟨-, -, h3⟩ := ext1_spec V n P hk S S' check B T (roleOf i) i
    ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)
  have := sum_dis_le_of_inconsistency T.ψ_unit _ _ h3
  simpa using this

end MIPRE.AnswerReduction

end
