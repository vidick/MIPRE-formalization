/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Halting.Reduction
public import MIPRE.Foundations.Halting.Corollaries

@[expose] public section

/-!
# The class `TMIP*`, and `TMIP* = RE` from tailored compression

Paper II, II:787 and II:6997: the class reading of `thm:tailored_MIP*=RE`, as
`Foundations/ClassMIPStarComputable.lean` and `Halting/Corollaries.lean` give it for `MIP*`.

* `TMIPStarComputable L`: there is a computable map from strings to tailored game descriptions
  with a perfect ZPC strategy on the members of `L` and quantum value at most `1/2` on the
  others. This is the computable version of the class, with soundness in the quantum value, as
  the paper's (II:1505) and `MIPStarComputable`'s are.
* `TMIPStarComputable.mipStar`: `TMIP* ⊆ MIP*`. A perfect ZPC strategy gives quantum value `1`
  (`TailoredGameData.HasPerfectZPC.quantumValue_eq_one`), and the conversion to a game
  description keeps the quantum value (`TailoredGameData.quantumValue_toGameData`). Hence
  `TMIPStarComputable.isRE`: `TMIP* ⊆ RE`, unconditionally, by the lower semicomputability of
  the quantum value.
* `re_subset_tmipStarComputable_of`, `tmipStarComputable_eq_re_of`: `RE ⊆ TMIP*`, hence
  `TMIP* = RE`, from a tailored gap compression. An r.e. language many-one reduces to halting
  (`Halting.exists_code_halts_of_isRE`), which reduces to tailored games
  (`tailored_halting_reduction_quantum_of`).

The plan had `TMIP* ⊆ RE` by enumerating signed-permutation strategies, on which perfection is
decidable. The route through the quantum value needs no new semidecider: the class's soundness
clause is in the quantum value, so membership is `val* > 1/2`.
-/

namespace MIPRE.Tailored

open Cost TailoredGameValue

/-- **`TMIP*`, computable version** (II:787): a language `L` is in `TMIPStarComputable` if there
is a computable map from strings to tailored game descriptions whose game has a perfect ZPC
strategy when `x ∈ L` and quantum value at most `1/2` when `x ∉ L`. -/
def TMIPStarComputable (L : Set BitStr) : Prop :=
  ∃ g : BitStr → TailoredGameData, Computable g ∧
    ∀ x, (x ∈ L → (g x).HasPerfectZPC) ∧ (x ∉ L → quantumValue (g x).game ≤ 1 / 2)

/-- **`TMIP* ⊆ MIP*`**: a perfect ZPC strategy gives value `1`, and a tailored game description
converts computably to a game description with the same quantum value. -/
theorem TMIPStarComputable.mipStar {L : Set BitStr} (h : TMIPStarComputable L) :
    MIPStarComputable L := by
  obtain ⟨g, hg, hgap⟩ := h
  refine ⟨fun x => (g x).toGameData, TailoredGameData.primrec_toGameData.to_comp.comp hg,
    fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · show quantumValue (g x).toGameData.game = 1
    rw [TailoredGameData.quantumValue_toGameData]
    exact ((hgap x).1 hx).quantumValue_eq_one
  · show quantumValue (g x).toGameData.game ≤ 1 / 2
    rw [TailoredGameData.quantumValue_toGameData]
    exact (hgap x).2 hx

/-- **`TMIP* ⊆ RE`** (II:1838), unconditionally. -/
theorem TMIPStarComputable.isRE {L : Set BitStr} (h : TMIPStarComputable L) : IsRE L :=
  h.mipStar.isRE

variable {ℓ : ℕ}

/-- **`RE ⊆ TMIP*`**, from a tailored gap compression. -/
theorem re_subset_tmipStarComputable_of (TG : TailoredGapCompression ℓ) {L : Set BitStr}
    (h : IsRE L) : TMIPStarComputable L := by
  obtain ⟨r, hr, hrL⟩ := MIPRE.Halting.exists_code_halts_of_isRE h
  obtain ⟨g, hg, hgap⟩ := tailored_halting_reduction_quantum_of TG
  refine ⟨fun x => g (r x), hg.comp hr, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · exact (hgap (r x)).1 ((hrL x).2 hx)
  · exact (hgap (r x)).2 fun hd => hx ((hrL x).1 hd)

/-- **`TMIP* = RE`** (II:787, II:6997), from a tailored gap compression: the two classes
coincide, as predicates on languages. -/
theorem tmipStarComputable_eq_re_of (TG : TailoredGapCompression ℓ) :
    TMIPStarComputable = IsRE :=
  funext fun _ => propext ⟨TMIPStarComputable.isRE, re_subset_tmipStarComputable_of TG⟩

end MIPRE.Tailored

end
