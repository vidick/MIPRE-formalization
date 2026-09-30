/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.AnswerReduction.SoundGameCheck
public import MIPRE.Foundations.OracularValue

@[expose] public section

/-!
# Soundness of answer reduction: the decoded strategy

Piece AR-5e of `planning/answer-reduction.md` (`lem:ar-ora`): a strategy for the typed
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

The decoded measurements are coarse-grainings of the extracted projective ones, so the decoded
strategy is a projective strategy in the same model (`decoded`), and no dilation is needed: its
value is at most `ω` of the typed oracularized game in every value model `ω` that dominates the
model (`ValueModel.Dominates`), and oracularization's soundness in `ω` bounds the input verifier
(`val_ge_decoded`). The matrix proof dilated a POVM strategy here (Naimark); that step is gone.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp
open scoped ComplexOrder

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ) (T : M.ProjStrat (typedGame V n P hk S S' check B)) (hL : LIDT.Simul.SoundIn M)
  (B' : ℕ)
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
def MAo : CL.Detyping.Question Role (Fin (V.sampler.dim n)) → POVMIn (OAns (Verifier.Answers B')) 𝒜
  | (.oracle, y) => (JA V n P hk S S' check B T hL y).map (decO P hk B' dec)
  | (.alice, y) => (GA1 V n P hk S S' check B T hL (roleOf 0) 0 y).map (decV P hk B' dec)
  | (.bob, y) => (GA1 V n P hk S S' check B T hL (roleOf 1) 1 y).map (decV P hk B' dec)

/-- **Bob's decoded measurements.** -/
def MBo : CL.Detyping.Question Role (Fin (V.sampler.dim n)) → POVMIn (OAns (Verifier.Answers B')) ℬ
  | (.oracle, y) => (JB V n P hk S S' check B T hL y).map (decO P hk B' dec)
  | (.alice, y) => (GB1 V n P hk S S' check B T hL (roleOf 0) 0 y).map (decV P hk B' dec)
  | (.bob, y) => (GB1 V n P hk S S' check B T hL (roleOf 1) 1 y).map (decV P hk B' dec)

/-- **Alice's decoded measurements are projective**: coarse-grainings of the extracted
projective measurements. -/
theorem MAo_proj :
    ∀ q, IsPVMIn (MAo V n P hk S S' check B T hL B' dec q).op
  | (.oracle, y) => POVMIn.isPVMIn_map (ext6_proj V n P hk S S' check B T hL y).1 _
  | (.alice, y) => POVMIn.isPVMIn_map (ext1_proj V n P hk S S' check B T hL (roleOf 0) 0 y).1 _
  | (.bob, y) => POVMIn.isPVMIn_map (ext1_proj V n P hk S S' check B T hL (roleOf 1) 1 y).1 _

/-- **Bob's decoded measurements are projective.** -/
theorem MBo_proj :
    ∀ q, IsPVMIn (MBo V n P hk S S' check B T hL B' dec q).op
  | (.oracle, y) => POVMIn.isPVMIn_map (ext6_proj V n P hk S S' check B T hL y).2 _
  | (.alice, y) => POVMIn.isPVMIn_map (ext1_proj V n P hk S S' check B T hL (roleOf 0) 0 y).2 _
  | (.bob, y) => POVMIn.isPVMIn_map (ext1_proj V n P hk S S' check B T hL (roleOf 1) 1 y).2 _

/-- **The decoded strategy**: a projective strategy in the model, on the typed strategy's state,
for the typed oracularized game of the input verifier. -/
def decoded : M.ProjStrat (oGame V n B') where
  PA := MAo V n P hk S S' check B T hL B' dec
  PB := MBo V n P hk S S' check B T hL B' dec
  projA := MAo_proj V n P hk S S' check B T hL B' dec
  projB := MBo_proj V n P hk S S' check B T hL B' dec
  ψ_unit := T.ψ_unit

/-- The weight of Alice's `J` outcomes whose decoded pair fails the game check. -/
def gcA (y : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  ∑ f, (if (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true then 0 else
    M.bornProb ((JA V n P hk S S' check B T hL y).op f) 1)

/-- The weight of Bob's `J` outcomes whose decoded pair fails the game check. -/
def gcB (y : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  ∑ f, (if (V.seeded n B').gameCheck (.oracle, y) (decO P hk B' dec f) = true then 0 else
    M.bornProb 1 ((JB V n P hk S S' check B T hL y).op f))

/-! ## The nine pairs of roles -/

omit [NeZero P.m] in
variable (M) in
theorem dis_map_decO_le (Mj : POVMIn (Poly6 P hk) 𝒜) (Nj : POVMIn (Poly6 P hk) ℬ) :
    M.dis ((Mj.map (decO P hk B' dec)).map id) ((Nj.map (decO P hk B' dec)).map id)
      ≤ M.dis Mj Nj := by
  rw [POVMIn.map_map, POVMIn.map_map]
  exact M.dis_map_le Mj Nj _

/-- **Two oracles**: the two game checks and the disagreement of the two `J`. -/
theorem condFail_OO_le (y : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec) (.oracle, y) (.oracle, y)
      ≤ gcA V n P hk S S' check B T hL B' dec y + gcB V n P hk S S' check B T hL B' dec y
        + M.dis (JA V n P hk S S' check B T hL y)
          (JB V n P hk S S' check B T hL y) := by
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.oracle, y)) (y := (.oracle, y))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
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
    rw [M.sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_map_decO_le M P hk B' dec _ _

omit [NeZero P.m] in
variable (M) in
/-- The decoded answer an oracle's `v`-th component and an isolated player's answer agree
whenever the polynomials agree, as placed polynomials. -/
theorem dis_decO_decV_le (i : Fin 5) (v : Role)
    (hv : ∀ f, comp v (decO P hk B' dec f) = dec (gPoly P hk i f)) (Mj : POVMIn (Poly6 P hk) 𝒜)
    (N : POVMIn (Poly1 P hk) ℬ) :
    M.dis ((Mj.map (decO P hk B' dec)).map (comp v)) ((N.map (decV P hk B' dec)).map sgl)
      ≤ M.dis (Mj.map fun f => f (blk P i)) (N.map fun g => liftBlk P hk i (g 0)) := by
  set h : LowIndDegPoly (F := Fq P hk) (m := P.m') (d := dPcp) → Verifier.Answers B' :=
    fun F => dec ((F.blockPoly (blockEmb (P := P) i)).toMv)
  have e1 : (fun f => comp v (decO P hk B' dec f)) = fun f => h (f (blk P i)) :=
    funext fun f => hv f
  have e2 : (fun g => sgl (decV P hk B' dec g)) = fun g => h (liftBlk P hk i (g 0)) :=
    funext fun g => by
      simp only [sgl, decV, h, liftBlk, LowIndDegPoly.blockPoly_liftIdx (blockEmb_injective i)]
  rw [POVMIn.map_map, POVMIn.map_map, e1, e2, ← POVMIn.map_map Mj (fun f => f (blk P i)) h,
    ← POVMIn.map_map N (fun g => liftBlk P hk i (g 0)) h]
  exact M.dis_map_le _ _ h

omit [NeZero P.m] in
variable (M) in
/-- The mirror image. -/
theorem dis_decV_decO_le (i : Fin 5) (v : Role)
    (hv : ∀ f, comp v (decO P hk B' dec f) = dec (gPoly P hk i f)) (N : POVMIn (Poly1 P hk) 𝒜)
    (Mj : POVMIn (Poly6 P hk) ℬ) :
    M.dis ((N.map (decV P hk B' dec)).map sgl) ((Mj.map (decO P hk B' dec)).map (comp v))
      ≤ M.dis (N.map fun g => liftBlk P hk i (g 0)) (Mj.map fun f => f (blk P i)) := by
  set h : LowIndDegPoly (F := Fq P hk) (m := P.m') (d := dPcp) → Verifier.Answers B' :=
    fun F => dec ((F.blockPoly (blockEmb (P := P) i)).toMv)
  have e1 : (fun f => comp v (decO P hk B' dec f)) = fun f => h (f (blk P i)) :=
    funext fun f => hv f
  have e2 : (fun g => sgl (decV P hk B' dec g)) = fun g => h (liftBlk P hk i (g 0)) :=
    funext fun g => by
      simp only [sgl, decV, h, liftBlk, LowIndDegPoly.blockPoly_liftIdx (blockEmb_injective i)]
  rw [POVMIn.map_map, POVMIn.map_map, e1, e2, ← POVMIn.map_map Mj (fun f => f (blk P i)) h,
    ← POVMIn.map_map N (fun g => liftBlk P hk i (g 0)) h]
  exact M.dis_map_le _ _ h

omit [NeZero P.m] in
variable (M) in
theorem dis_map_const {A : Type*} [Fintype A] (hψ : ‖M.ψ‖ = 1) (Mj : POVMIn A 𝒜) (N : POVMIn A ℬ) :
    M.dis (Mj.map fun _ => ()) (N.map fun _ => ()) = 0 := by
  rw [M.dis_map_eq_sum hψ]
  simp

/-- **An oracle and Alice**: the oracle's game check and the disagreement of its first answer
polynomial with Alice's. -/
theorem condFail_Oa_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)
      ≤ gcA V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyA V n P hk S S' check B T hL 0 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.oracle, yO))
    (y := (.alice, (roleFamily (V.sampler.cl n) .alice).eval x))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬(SeededGame.shapeOk .oracle a = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) a = true))
    (fun b => ¬SeededGame.shapeOk .alice b = true) (comp .alice) sgl (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hB : ∑ b, (if ¬SeededGame.shapeOk .alice b = true then M.bornProb 1
      ((MBo V n P hk S S' check B T hL B' dec
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)).op b) else 0) = 0 := by
    simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hB, add_zero]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decO_decV_le M P hk B' dec 0 .alice (fun f => rfl) _ _

/-- **An oracle and Bob.** -/
theorem condFail_Ob_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)
      ≤ gcA V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyA V n P hk S S' check B T hL 1 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.oracle, yO))
    (y := (.bob, (roleFamily (V.sampler.cl n) .bob).eval x))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬(SeededGame.shapeOk .oracle a = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) a = true))
    (fun b => ¬SeededGame.shapeOk .bob b = true) (comp .bob) sgl (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hB : ∑ b, (if ¬SeededGame.shapeOk .bob b = true then M.bornProb 1
      ((MBo V n P hk S S' check B T hL B' dec
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)).op b) else 0) = 0 := by
    simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hB, add_zero]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decO_decV_le M P hk B' dec 1 .bob (fun f => rfl) _ _

/-- **Alice and an oracle.** -/
theorem condFail_aO_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec)
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ gcB V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyB V n P hk S S' check B T hL 0 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit
    (x := (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)) (y := (.oracle, yO))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬SeededGame.shapeOk .alice a = true)
    (fun b => ¬(SeededGame.shapeOk .oracle b = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) b = true)) sgl (comp .alice) (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .alice a = true then M.bornProb
      ((MAo V n P hk S S' check B T hL B' dec
        (.alice, (roleFamily (V.sampler.cl n) .alice).eval x)).op a) 1 else 0) = 0 := by
    simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  rw [hA, zero_add]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decV_decO_le M P hk B' dec 0 .alice (fun f => rfl) _ _

/-- **Bob and an oracle.** -/
theorem condFail_bO_le (x : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec)
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)
        (.oracle, (roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ gcB V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
        + disPolyB V n P hk S S' check B T hL 1 x := by
  set yO := (roleFamily (V.sampler.cl n) .oracle).eval x
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit
    (x := (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)) (y := (.oracle, yO))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬SeededGame.shapeOk .bob a = true)
    (fun b => ¬(SeededGame.shapeOk .oracle b = true ∧
      (V.seeded n B').gameCheck (.oracle, yO) b = true)) sgl (comp .bob) (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck, comp, sgl])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .bob a = true then M.bornProb
      ((MAo V n P hk S S' check B T hL B' dec
        (.bob, (roleFamily (V.sampler.cl n) .bob).eval x)).op a) 1 else 0) = 0 := by
    simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  rw [hA, zero_add]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · exact dis_decV_decO_le M P hk B' dec 1 .bob (fun f => rfl) _ _

/-- **Alice and Alice**: the disagreement of the two extracted polynomial measurements. -/
theorem condFail_aa_le (y : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec) (.alice, y) (.alice, y)
      ≤ M.dis (GA1 V n P hk S S' check B T hL (roleOf 0) 0 y)
          (GB1 V n P hk S S' check B T hL (roleOf 0) 0 y) := by
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.alice, y)) (y := (.alice, y))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬SeededGame.shapeOk .alice a = true) (fun b => ¬SeededGame.shapeOk .alice b = true)
    id id (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        subst hab
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .alice a = true then
      M.bornProb ((MAo V n P hk S S' check B T hL B' dec (.alice, y)).op a) 1 else 0) = 0 := by
    simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .alice b = true then
      M.bornProb 1 ((MBo V n P hk S S' check B T hL B' dec (.alice, y)).op b) else 0) = 0 := by
    simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, zero_add, zero_add]
  simp only [MAo, MBo]
  rw [POVMIn.map_map, POVMIn.map_map]
  exact M.dis_map_le _ _ _

/-- **Alice and Bob** never fail: only the formats are checked. -/
theorem condFail_ab_le (y y' : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec) (.alice, y) (.bob, y') ≤ 0 := by
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.alice, y)) (y := (.bob, y'))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬SeededGame.shapeOk .alice a = true) (fun b => ¬SeededGame.shapeOk .bob b = true)
    (fun _ => ()) (fun _ => ()) (fun a b ha hb _ => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans (le_of_eq ?_)
  have hA : ∑ a, (if ¬SeededGame.shapeOk .alice a = true then
      M.bornProb ((MAo V n P hk S S' check B T hL B' dec (.alice, y)).op a) 1 else 0) = 0 := by
    simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .bob b = true then
      M.bornProb 1 ((MBo V n P hk S S' check B T hL B' dec (.bob, y')).op b) else 0) = 0 := by
    simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, dis_map_const M T.ψ_unit]
  norm_num

/-- **Bob and Bob**: the disagreement of the two extracted polynomial measurements. -/
theorem condFail_bb_le (y : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec) (.bob, y) (.bob, y)
      ≤ M.dis (GA1 V n P hk S S' check B T hL (roleOf 1) 1 y)
          (GB1 V n P hk S S' check B T hL (roleOf 1) 1 y) := by
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.bob, y)) (y := (.bob, y))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬SeededGame.shapeOk .bob a = true) (fun b => ¬SeededGame.shapeOk .bob b = true)
    id id (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        subst hab
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk .bob a = true then
      M.bornProb ((MAo V n P hk S S' check B T hL B' dec (.bob, y)).op a) 1 else 0) = 0 := by
    simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .bob b = true then
      M.bornProb 1 ((MBo V n P hk S S' check B T hL B' dec (.bob, y)).op b) else 0) = 0 := by
    simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, zero_add, zero_add]
  simp only [MAo, MBo]
  rw [POVMIn.map_map, POVMIn.map_map]
  exact M.dis_map_le _ _ _

/-- **Bob and Alice** never fail: only the formats are checked. -/
theorem condFail_ba_le (y y' : Fin (V.sampler.dim n) → 𝔽₂) :
    M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec) (.bob, y) (.alice, y') ≤ 0 := by
  have h := M.condFail_le_of (G := oGame V n B') T.ψ_unit (x := (.bob, y)) (y := (.alice, y'))
    (MA := MAo V n P hk S S' check B T hL B' dec) (MB := MBo V n P hk S S' check B T hL B' dec)
    (fun a => ¬SeededGame.shapeOk .bob a = true) (fun b => ¬SeededGame.shapeOk .alice b = true)
    (fun _ => ()) (fun _ => ()) (fun a b ha hb _ => by
        simp only [not_not] at ha hb
        show (V.seeded n B').oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
            SeededGame.gameCheck])
  refine h.trans (le_of_eq ?_)
  have hA : ∑ a, (if ¬SeededGame.shapeOk .bob a = true then
      M.bornProb ((MAo V n P hk S S' check B T hL B' dec (.bob, y)).op a) 1 else 0) = 0 := by
    simp only [MAo]
    rw [M.sum_ite_bornProb_one_map]
    simp [decV, SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk .alice b = true then
      M.bornProb 1 ((MBo V n P hk S S' check B T hL B' dec (.alice, y')).op b) else 0) = 0 := by
    simp only [MBo]
    rw [M.sum_ite_bornProb_one_map']
    simp [decV, SeededGame.shapeOk]
  rw [hA, hB, dis_map_const M T.ψ_unit]
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
    gcA V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ ∑ i : Fin 5, disPolyA V n P hk S S' check B T hL i x
        + 2 * gcEvA V n P hk S S' check B T hL x := by
  set y := (roleFamily (V.sampler.cl n) .oracle).eval x
  set Mj := JA V n P hk S S' check B T hL y
  set β : Poly6 P hk → ℝ := fun f => M.bornProb (Mj.op f) 1
  have hβ0 : ∀ f, 0 ≤ β f := fun f => M.bornProb_nonneg (Mj.op_nonneg f) zero_le_one
  -- the placed-block failures
  have hdis : ∀ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
        ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
      ≤ disPolyA V n P hk S S' check B T hL i x := by
    intro i
    set N := GB1 V n P hk S S' check B T hL (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)
    have hd : disPolyA V n P hk S S' check B T hL i x
        = ∑ f, ∑ g, (if f (blk P i) = liftBlk P hk i (g 0) then 0 else 1)
          * M.bornProb (Mj.op f) (N.op g) :=
      M.dis_map_eq_sum T.ψ_unit Mj N _ _
    rw [hd]
    refine Finset.sum_le_sum fun f _ => ?_
    split_ifs with hbl
    · exact Finset.sum_nonneg fun g _ => mul_nonneg (by split_ifs <;> norm_num)
        (M.bornProb_nonneg (Mj.op_nonneg f) (N.op_nonneg g))
    · simp only [β]
      rw [M.bornProb_one_right _ N]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [ite_eq_right (ne_liftBlk_of_not P hk hbl (g 0)), one_mul]
  -- the rejected evaluations
  have hev : gcEvA V n P hk S S' check B T hL x = ∑ f, rejFrac V n P hk check y f * β f := by
    simp only [gcEvA, rejFrac, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [β, Mj, y]
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
        rw [ite_eq_right hi] at hle
        linarith
  calc gcA V n P hk S S' check B T hL B' dec y
      ≤ ∑ f, (∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * (rejFrac V n P hk check y f * β f)) := Finset.sum_le_sum fun f _ => hpt f
    _ = ∑ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * gcEvA V n P hk S S' check B T hL x := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, hev, Finset.mul_sum]
    _ ≤ _ := by
        have := Finset.sum_le_sum fun i (_ : i ∈ univ) => hdis i
        linarith

/-- **The oracle's game check under Bob's `J`**, the mirror image. -/
theorem gcB_le (hgc : PcpSound V n P hk check B' dec) (x : Fin (V.sampler.dim n) → 𝔽₂) :
    gcB V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ ∑ i : Fin 5, disPolyB V n P hk S S' check B T hL i x
        + 2 * gcEvB V n P hk S S' check B T hL x := by
  set y := (roleFamily (V.sampler.cl n) .oracle).eval x
  set Mj := JB V n P hk S S' check B T hL y
  set β : Poly6 P hk → ℝ := fun f => M.bornProb 1 (Mj.op f)
  have hβ0 : ∀ f, 0 ≤ β f := fun f => M.bornProb_nonneg zero_le_one (Mj.op_nonneg f)
  have hdis : ∀ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
        ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
      ≤ disPolyB V n P hk S S' check B T hL i x := by
    intro i
    set N := GA1 V n P hk S S' check B T hL (roleOf i) i
      ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)
    have hd : disPolyB V n P hk S S' check B T hL i x
        = ∑ g, ∑ f, (if liftBlk P hk i (g 0) = f (blk P i) then 0 else 1)
          * M.bornProb (N.op g) (Mj.op f) :=
      M.dis_map_eq_sum T.ψ_unit N Mj _ _
    rw [hd, Finset.sum_comm]
    refine Finset.sum_le_sum fun f _ => ?_
    split_ifs with hbl
    · exact Finset.sum_nonneg fun g _ => mul_nonneg (by split_ifs <;> norm_num)
        (M.bornProb_nonneg (N.op_nonneg g) (Mj.op_nonneg f))
    · simp only [β]
      rw [M.bornProb_one_left N]
      refine Finset.sum_le_sum fun g _ => ?_
      rw [ite_eq_right (Ne.symm (ne_liftBlk_of_not P hk hbl (g 0))), one_mul]
  have hev : gcEvB V n P hk S S' check B T hL x = ∑ f, rejFrac V n P hk check y f * β f := by
    simp only [gcEvB, rejFrac, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [β, Mj, y]
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
        rw [ite_eq_right hi] at hle
        linarith
  calc gcB V n P hk S S' check B T hL B' dec y
      ≤ ∑ f, (∑ i : Fin 5, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * (rejFrac V n P hk check y f * β f)) := Finset.sum_le_sum fun f _ => hpt f
    _ = ∑ i : Fin 5, ∑ f, (if f (blk P i) = liftBlk P hk i
          ((f (blk P i)).blockPoly (blockEmb (P := P) i)) then 0 else β f)
        + 2 * gcEvB V n P hk S S' check B T hL x := by
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
    ∑ x, disPolyA V n P hk S S' check B T hL i x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T :=
  sum_disPolyA_le V n P hk S S' check B T hL i

theorem sum_disPolyB_le' (i : Fin 5) :
    ∑ x, disPolyB V n P hk S S' check B T hL i x
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T := by
  have h := sum_disPolyB_le V n P hk S S' check B T hL i
  unfold errD
  linarith

/-- **Alice's oracles' game checks**, summed over the oracle halves. -/
theorem sum_gcA_le (hgc : PcpSound V n P hk check B' dec) :
    ∑ x, gcA V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (7 * errD V n P hk S S' check B T) := by
  have h1 := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    gcA_le V n P hk S S' check B T hL B' dec hgc x
  have h2 := sum_gcEvA_le V n P hk S S' check B T hL
  have h3 : ∑ i : Fin 5, ∑ x, disPolyA V n P hk S S' check B T hL i x
      ≤ ∑ _i : Fin 5, Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T :=
    Finset.sum_le_sum fun i _ => sum_disPolyA_le' V n P hk S S' check B T hL i
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
    ∑ x, gcB V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval x)
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (7 * errD V n P hk S S' check B T) := by
  have h1 := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    gcB_le V n P hk S S' check B T hL B' dec hgc x
  have h2 := sum_gcEvB_le V n P hk S S' check B T hL
  have h3 : ∑ i : Fin 5, ∑ x, disPolyB V n P hk S S' check B T hL i x
      ≤ ∑ _i : Fin 5, Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * errD V n P hk S S' check B T :=
    Finset.sum_le_sum fun i _ => sum_disPolyB_le' V n P hk S S' check B T hL i
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
    ∑ x, M.dis (JA V n P hk S S' check B T hL ((roleFamily (V.sampler.cl n) .oracle).eval x))
        (JB V n P hk S S' check B T hL ((roleFamily (V.sampler.cl n) .oracle).eval x))
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * err6 V n P hk S S' check B T := by
  refine le_trans (Finset.sum_le_sum fun x _ => ?_) (sum_deltaSim6_le V n P hk S S' check B T)
  obtain ⟨-, -, h3⟩ := ext6_spec V n P hk S S' check B T hL
    ((roleFamily (V.sampler.cl n) .oracle).eval x)
  have := M.sum_dis_le_of_inconsistency T.ψ_unit _ _ h3
  simpa using this

/-- **Two isolated players' `G` disagree** at most copy `i`'s extraction error, on average. -/
theorem sum_dis_GA_GB_le (i : Fin 5) :
    ∑ x, M.dis (GA1 V n P hk S S' check B T hL (roleOf i) i
        ((roleFamily (V.sampler.cl n) (roleOf i)).eval x))
        (GB1 V n P hk S S' check B T hL (roleOf i) i
          ((roleFamily (V.sampler.cl n) (roleOf i)).eval x))
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * err1 V n P hk S S' check B T := by
  refine le_trans (Finset.sum_le_sum fun x _ => ?_)
    (sum_deltaSim1_le V n P hk S S' check B T (ldStep_roleOf i))
  obtain ⟨-, -, h3⟩ := ext1_spec V n P hk S S' check B T hL (roleOf i) i
    ((roleFamily (V.sampler.cl n) (roleOf i)).eval x)
  have := M.sum_dis_le_of_inconsistency T.ψ_unit _ _ h3
  simpa using this

omit [NeZero P.m] [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
variable (M) in
/-- **The failure of a strategy for a typed oracularized game** is the average, over the ordered
pairs of roles and the seed, of its failure at the questions they determine. -/
theorem one_sub_povmValue_typed {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ' : ℕ}
    (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ' + 1)) {A' : Type*} [Fintype A']
    (D' : CL.Detyping.Question Role ι → CL.Detyping.Question Role ι → A' → A' → Bool)
    (MA : CL.Detyping.Question Role ι → POVMIn A' 𝒜)
    (MB : CL.Detyping.Question Role ι → POVMIn A' ℬ) :
    1 - M.povmValue (CL.Detyping.typedGame roleGraph roleGraph_nonempty (fun _ => roleFamily L) D')
        MA MB
      = (9 * Fintype.card (ι → CL.𝔽₂) : ℝ)⁻¹ * ∑ z : ι → CL.𝔽₂, ∑ u : Role, ∑ v : Role,
          M.condFail (CL.Detyping.typedGame roleGraph roleGraph_nonempty (fun _ => roleFamily L) D')
            MA MB (u, (roleFamily L u).eval z) (v, (roleFamily L v).eval z) := by
  rw [M.one_sub_povmValue_eq]
  change ∑ p, ∑ q, SampledGame.dist
    (CL.Detyping.typedQuestion (E := roleGraph) (fun _ => roleFamily L) false)
    (CL.Detyping.typedQuestion (E := roleGraph) (fun _ => roleFamily L) true) p q * _ = _
  rw [SampledGame.sum_dist_mul, Fintype.card_congr SeededGame.typedSeedEquiv,
    SeededGame.card_role_prod_prod, div_eq_inv_mul]
  congr 1
  rw [← Fintype.sum_equiv SeededGame.typedSeedEquiv.symm _ _ fun _ => rfl,
    Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
  rfl

/-- **The decoded strategy's failure** at a seed, over the nine ordered pairs of roles. -/
theorem sum_roles_condFail_le (hgc : PcpSound V n P hk check B' dec)
    (z : Fin (V.sampler.dim n) → 𝔽₂) :
    ∑ u : Role, ∑ v : Role, M.condFail (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec) (u, (roleFamily (V.sampler.cl n) u).eval z)
        (v, (roleFamily (V.sampler.cl n) v).eval z)
      ≤ 3 * gcA V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval z)
        + 3 * gcB V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval z)
        + M.dis
            (JA V n P hk S S' check B T hL ((roleFamily (V.sampler.cl n) .oracle).eval z))
            (JB V n P hk S S' check B T hL ((roleFamily (V.sampler.cl n) .oracle).eval z))
        + (disPolyA V n P hk S S' check B T hL 0 z + disPolyA V n P hk S S' check B T hL 1 z
          + disPolyB V n P hk S S' check B T hL 0 z + disPolyB V n P hk S S' check B T hL 1 z)
        + M.dis (GA1 V n P hk S S' check B T hL (roleOf 0) 0
            ((roleFamily (V.sampler.cl n) (roleOf 0)).eval z))
            (GB1 V n P hk S S' check B T hL (roleOf 0) 0
              ((roleFamily (V.sampler.cl n) (roleOf 0)).eval z))
        + M.dis (GA1 V n P hk S S' check B T hL (roleOf 1) 1
            ((roleFamily (V.sampler.cl n) (roleOf 1)).eval z))
            (GB1 V n P hk S S' check B T hL (roleOf 1) 1
              ((roleFamily (V.sampler.cl n) (roleOf 1)).eval z)) := by
  have hgA := gcA_le V n P hk S S' check B T hL B' dec hgc z
  have hgB := gcB_le V n P hk S S' check B T hL B' dec hgc z
  simp only [Role.sum_eq]
  have := condFail_OO_le V n P hk S S' check B T hL B' dec
    ((roleFamily (V.sampler.cl n) .oracle).eval z)
  have := condFail_Oa_le V n P hk S S' check B T hL B' dec z
  have := condFail_Ob_le V n P hk S S' check B T hL B' dec z
  have := condFail_aO_le V n P hk S S' check B T hL B' dec z
  have := condFail_bO_le V n P hk S S' check B T hL B' dec z
  have := condFail_aa_le V n P hk S S' check B T hL B' dec
    ((roleFamily (V.sampler.cl n) .alice).eval z)
  have := condFail_bb_le V n P hk S S' check B T hL B' dec
    ((roleFamily (V.sampler.cl n) .bob).eval z)
  have := condFail_ab_le V n P hk S S' check B T hL B' dec
    ((roleFamily (V.sampler.cl n) .alice).eval z)
    ((roleFamily (V.sampler.cl n) .bob).eval z)
  have := condFail_ba_le V n P hk S S' check B T hL B' dec
    ((roleFamily (V.sampler.cl n) .bob).eval z)
    ((roleFamily (V.sampler.cl n) .alice).eval z)
  have hg0 :
      0 ≤ gcA V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval z) :=
    Finset.sum_nonneg fun f _ => by
      split_ifs
      · exact le_refl 0
      · exact M.bornProb_nonneg ((JA V n P hk S S' check B T hL _).op_nonneg f) zero_le_one
  have hg1 :
      0 ≤ gcB V n P hk S S' check B T hL B' dec ((roleFamily (V.sampler.cl n) .oracle).eval z) :=
    Finset.sum_nonneg fun f _ => by
      split_ifs
      · exact le_refl 0
      · exact M.bornProb_nonneg zero_le_one ((JB V n P hk S S' check B T hL _).op_nonneg f)
  change _ ≤ _ + M.dis (GA1 V n P hk S S' check B T hL (roleOf 0) 0
            ((roleFamily (V.sampler.cl n) .alice).eval z))
            (GB1 V n P hk S S' check B T hL (roleOf 0) 0
              ((roleFamily (V.sampler.cl n) .alice).eval z))
        + M.dis (GA1 V n P hk S S' check B T hL (roleOf 1) 1
            ((roleFamily (V.sampler.cl n) .bob).eval z))
            (GB1 V n P hk S S' check B T hL (roleOf 1) 1
              ((roleFamily (V.sampler.cl n) .bob).eval z))
  linarith

/-- **The decoded strategy fails the typed oracularized game** with probability at most `6` times
the combined error, given the PCP's soundness in the form `hgc`. -/
theorem one_sub_povmValue_decoded_le (hgc : PcpSound V n P hk check B' dec) :
    1 - M.povmValue (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
        (MBo V n P hk S S' check B T hL B' dec)
      ≤ 6 * errD V n P hk S S' check B T := by
  rw [one_sub_povmValue_typed M]
  have h := Finset.sum_le_sum fun z (_ : z ∈ univ) =>
    sum_roles_condFail_le V n P hk S S' check B T hL B' dec hgc z
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hA := sum_gcA_le V n P hk S S' check B T hL B' dec hgc
  have hB := sum_gcB_le V n P hk S S' check B T hL B' dec hgc
  have hJ := sum_dis_JA_JB_le V n P hk S S' check B T hL
  have hG0 := sum_dis_GA_GB_le V n P hk S S' check B T hL 0
  have hG1 := sum_dis_GA_GB_le V n P hk S S' check B T hL 1
  have hA0 := sum_disPolyA_le' V n P hk S S' check B T hL 0
  have hA1 := sum_disPolyA_le' V n P hk S S' check B T hL 1
  have hB0 := sum_disPolyB_le' V n P hk S S' check B T hL 0
  have hB1 := sum_disPolyB_le' V n P hk S S' check B T hL 1
  have he1 := err1_nonneg V n P hk S S' check B T
  have he6 := err6_nonneg V n P hk S S' check B T
  have hsz := errSZ_nonneg P hk
  have hθ := one_sub_value_nonneg V n P hk S S' check B T
  have hD : 11 * (err6 V n P hk S S' check B T + err1 V n P hk S S' check B T)
      ≤ errD V n P hk S S' check B T := by unfold errD; linarith
  set X : ℝ := (Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) : ℝ) with hX
  have hXpos : 0 < X := by rw [hX]; exact_mod_cast Fintype.card_pos
  have htot : ∑ z, ∑ u : Role, ∑ v : Role, M.condFail (oGame V n B')
      (MAo V n P hk S S' check B T hL B' dec) (MBo V n P hk S S' check B T hL B' dec)
      (u, (roleFamily (V.sampler.cl n) u).eval z) (v, (roleFamily (V.sampler.cl n) v).eval z)
      ≤ X * (54 * errD V n P hk S S' check B T) := by
    have hXe1 := mul_le_mul_of_nonneg_left hD hXpos.le
    nlinarith
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

/-! ## The input verifier's value -/

omit [NeZero P.m] in
theorem errSZ_pos : 0 < errSZ P hk := by
  have h1 := one_le_dPcp
  have h5 : 5 ≤ P.m' := by simp only [PcpParams.m']; omega
  have hq : 0 < Fintype.card (Fq P hk) := Fintype.card_pos
  unfold errSZ
  have : (5 : ℝ) ≤ P.m' := by exact_mod_cast h5
  have : (1 : ℝ) ≤ dPcp := by exact_mod_cast h1
  positivity

theorem errD_pos : 0 < errD V n P hk S S' check B T := by
  have := err1_nonneg V n P hk S S' check B T
  have := err6_nonneg V n P hk S S' check B T
  have := one_sub_value_nonneg V n P hk S S' check B T
  have := errSZ_pos P hk
  unfold errD
  positivity

include hL in
/-- **The input verifier's value** is close to `1`, in a value model where oracularization is
sound and which dominates the model: the decoded strategy is a projective strategy in the model,
on the typed strategy's state, for the typed oracularized game, and fails it with probability at
most `6` times the combined error. No dilation is needed, since the decoded measurements are
coarse-grainings of the extracted projective ones (`MAo_proj`). -/
theorem val_ge_decoded {ω : ValueModel} (hω : ω.OracularSound) (hdom : ω.Dominates M)
    (hgc : PcpSound V n P hk check B' dec) :
    1 - 24 * √(7 * errD V n P hk S S' check B T) ≤ V.val ω n B' := by
  have hpos := errD_pos V n P hk S S' check B T
  refine V.val_ge_of_typed hω n B' ((V.seeded n B').oaccepts) (fun _ a => a)
    (fun _ _ _ _ h => h) (by positivity) ?_
  have h1 := one_sub_povmValue_decoded_le V n P hk S S' check B T hL B' dec hgc
  have h2 := hdom (oGame V n B') (decoded V n P hk S S' check B T hL B' dec)
  change 1 - M.povmValue (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
    (MBo V n P hk S S' check B T hL B' dec) ≤ _ at h1
  change M.povmValue (oGame V n B') (MAo V n P hk S S' check B T hL B' dec)
    (MBo V n P hk S S' check B T hL B' dec) ≤ _ at h2
  linarith

end MIPRE.AnswerReduction

end

end
