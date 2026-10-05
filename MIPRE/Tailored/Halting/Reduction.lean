/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Halting.Search
public import MIPRE.Foundations.Halting.Paper.Build
public import MIPRE.Foundations.Cost.FromPartrec
public import MIPRE.Foundations.Cost.Universal

@[expose] public section

/-!
# The halting problem reduces to tailored games

Paper II, II:1505 (`thm:tailored_MIP*=RE`), from a tailored gap compression: the statement
`TailoredGameValue.TailoredHaltingReduction` of `MIPRE/TailoredGameValue.lean`, which mentions
Mathlib alone.

The reduction sends a machine `M` to the tabulation, at the level `C`, of the tailored halting
verifier `V^{M,λ}` with the search program of `Tailored/Halting/Search.lean` and
`λ = Λ₀ + 4|M|` (`gameOf`). That verifier is `λ`-bounded (`Lam0_spec`), so its tabulation
presents the doubled game at `C` (`presents_tabT`), which has no weight on its loops:

* if `M` halts, `V^{M,λ}` has a perfect ZPC strategy at `C` (`halting_tailored_search`), which,
  padded with identities, is one of the tabulation (`Presents.hasPerfectZPC`);
* if not, `V^{M,λ}` has value at most `1/2` at `C`, which is the quantum value of the
  tabulation (`Presents.quantumValue_eq`), and the synchronous value is at most that
  (`TailoredGameData.gameValue_le_quantumValue`).

The map is computable because the processor's description is a fixed tree around the
encodings of `M` and `λ` (`lpBuild`, built from the three shapes of
`Halting/Paper/Build.lean`, which are generic in the body), and the tabulation is computable
(`computable_tabT`). Machines are `Nat.Partrec.Code`, carried to programs by `exists_compile`;
the universal machines are those of `Cost/Universal.lean`.

`tailored_halting_reduction_quantum_of` is the stronger form the library proves, with the
soundness clause in the quantum value; `tailored_halting_reduction_of` is the statement.
-/

namespace MIPRE.Tailored.Halting

open Cost Cost.Prog Cost.PolyTimeFun TailoredGameValue

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ) (U : UniversalMachine)
  (UT : ClockedUniversalMachine)

/-! ## The processor's description, in polynomial time -/

theorem toData_F_code (S' M : Prog) (lam : ℕ) :
    (F TG U UT S' M lam).code.toData =
      MIPRE.Halting.fcodeData (body TG U UT S').toData M.toData (encode lam) := rfl

/-- **The processor's description from `(M, λ)`**, in polynomial time: the description of
`LP^{M,λ}` is that of the existing decider `dec M λ` with the tailored body. -/
noncomputable def lpBuild (S' : Prog) : PolyTimeFun (Prog × ℕ) Prog :=
  cast (MIPRE.Halting.fixF.comp ((MIPRE.Halting.kleeneF U.univ.toData).comp
      (MIPRE.Halting.fcodeF (body TG U UT S').toData)))
    (fun p => lpProg TG U UT S' p.1 p.2) (fun p => by
      show (lpProg TG U UT S' p.1 p.2).toData = _
      rw [lpProg, MIPRE.Halting.toData_kleeneFix, MIPRE.Halting.toData_kleeneProg,
        toData_F_code]
      rfl)

@[simp] theorem lpBuild_apply (S' : Prog) (p : Prog × ℕ) :
    lpBuild TG U UT S' p = lpProg TG U UT S' p.1 p.2 := rfl

/-! ## The reduction -/

/-- The parameter at the machine `M`: `Λ₀ + 4|M|`. -/
noncomputable def lamOf (M : Prog) : ℕ := lamThreshold TG U UT + 4 * esize M

/-- The description string of `V^{M,λ}` at `λ = Λ₀ + 4|M|`. -/
noncomputable def descM (M : Prog) : BitStr :=
  MIPRE.Halting.descOf (lamOf TG U UT M) (lpProg TG U UT (search TG) M (lamOf TG U UT M))

/-- **The reduction's output at `M`**: the tabulation of `V^{M,λ}` at the level `C`, for
`λ = Λ₀ + 4|M|`. -/
noncomputable def gameOf (M : Prog) : TailoredGameData := tabT TG (descM TG U UT M) (C TG)

/-- The output presents the doubled game of `V^{M,λ}` at the level `C`. -/
theorem presents_gameOf (M : Prog) :
    ∃ e, Presents (gameOf TG U UT M) ((VT TG U UT M (lamOf TG U UT M)).tgame (C TG)).doubled e :=
  presents_tabT TG _ (lp TG U UT (search TG) M (lamOf TG U UT M))
    (Lam0_spec TG U UT (search TG) M _ le_rfl) (two_le_C TG)

/-- **Completeness**: if `M` halts on the empty input, the output has a perfect ZPC strategy. -/
theorem hasPerfectZPC_gameOf (M : Prog) (hM : Halts M .nil) : (gameOf TG U UT M).HasPerfectZPC := by
  obtain ⟨e, hP⟩ := presents_gameOf TG U UT M
  exact hP.hasPerfectZPC (TailoredGame.doubled_μ_self _)
    ((halting_tailored_search TG U UT M _ le_rfl).1 hM)

/-- The quantum value of the output is the value of `V^{M,λ}` at the level `C`. -/
theorem quantumValue_gameOf (M : Prog) :
    quantumValue (gameOf TG U UT M).game = (VT TG U UT M (lamOf TG U UT M)).valStar (C TG) := by
  obtain ⟨e, hP⟩ := presents_gameOf TG U UT M
  rw [hP.quantumValue_eq (TailoredGame.doubled_μ_self _),
    TailoredGame.quantumValue_doubled_eq_valStar]
  rfl

/-- **Soundness**: if `M` does not halt on the empty input, the output has quantum value at most
`1/2`. -/
theorem quantumValue_gameOf_le (M : Prog) (hM : ¬ Halts M .nil) :
    quantumValue (gameOf TG U UT M).game ≤ 1 / 2 := by
  rw [quantumValue_gameOf]
  exact (halting_tailored_search TG U UT M _ le_rfl).2 hM

/-- **The reduction is computable**, along any computable family of encoded machines. -/
theorem computable_gameOf {α : Type*} [Primcodable α] (f : α → Prog)
    (hf : Computable fun a => (encode (f a) : Data)) :
    Computable fun a => gameOf TG U UT (f a) := by
  have hsize : Computable fun a => esize (f a) := Data.primrec_size.to_comp.comp hf
  have hlam : Computable fun a => lamOf TG U UT (f a) :=
    (Primrec.nat_add.comp (Primrec.const _) (Primrec.nat_mul.comp (Primrec.const 4)
      Primrec.id)).to_comp.comp hsize
  have hpair : Computable fun a => (encode (f a, lamOf TG U UT (f a)) : Data) :=
    Data.primrec_cons.to_comp.comp hf (Data.primrec_encode_nat.to_comp.comp hlam)
  have hlp : Computable fun a =>
      (encode (lpBuild TG U UT (search TG) (f a, lamOf TG U UT (f a))) : Data) :=
    PolyTimeFun.computable_encode_comp (lpBuild TG U UT (search TG))
      (fun a => (f a, lamOf TG U UT (f a))) hpair
  have hdesc : Computable fun a => MIPRE.Halting.descPoly (lamOf TG U UT (f a),
      lpBuild TG U UT (search TG) (f a, lamOf TG U UT (f a))) :=
    PolyTimeFun.computable_comp MIPRE.Halting.descPoly
      (fun a => (lamOf TG U UT (f a), lpBuild TG U UT (search TG) (f a, lamOf TG U UT (f a))))
      (Data.primrec_cons.to_comp.comp (Data.primrec_encode_nat.to_comp.comp hlam) hlp)
      Data.primrec_decode_bitStr.to_comp
  have h := (computable_tabT TG).comp (hdesc.pair (Computable.const (C TG)))
  exact h.of_eq fun _ => rfl

end MIPRE.Tailored.Halting

namespace MIPRE.Tailored

open Cost TailoredGameValue

variable {ℓ : ℕ}

/-- **The halting problem reduces to tailored games, in the quantum value**, from a tailored gap
compression: a computable map from `Nat.Partrec.Code` to tailored game descriptions with a perfect
ZPC strategy on the machines that halt on the empty input and quantum value at most `1/2` on the
others. -/
theorem tailored_halting_reduction_quantum_of (TG : TailoredGapCompression ℓ) :
    ∃ g : Nat.Partrec.Code → TailoredGameData, Computable g ∧
      ∀ c : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput c → (g c).HasPerfectZPC) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput c → quantumValue (g c).game ≤ 1 / 2) := by
  obtain ⟨U⟩ := exists_efficient_universal
  obtain ⟨UT⟩ := exists_clocked_universal
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  exact ⟨fun c => Halting.gameOf TG U UT (compile c), Halting.computable_gameOf TG U UT compile hc,
    fun c => ⟨fun h => Halting.hasPerfectZPC_gameOf TG U UT _ ((hspec c).2 h),
      fun h => Halting.quantumValue_gameOf_le TG U UT _ fun h' => h ((hspec c).1 h')⟩⟩

/-- **`thm:tailored_MIP*=RE` from tailored compression** (II:1505): a tailored gap compression
gives `TailoredGameValue.TailoredHaltingReduction`, the synchronous value being at most the
quantum value. -/
theorem tailored_halting_reduction_of (TG : TailoredGapCompression ℓ) :
    TailoredHaltingReduction := by
  obtain ⟨g, hg, hgap⟩ := tailored_halting_reduction_quantum_of TG
  exact ⟨g, hg, fun c => ⟨(hgap c).1, fun h =>
    ((g c).gameValue_le_quantumValue).trans ((hgap c).2 h)⟩⟩

end MIPRE.Tailored

end
