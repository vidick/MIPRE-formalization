/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.ModelTransport
public import MIPRE.Foundations.AmplCommutant

@[expose] public section

/-!
# The low-individual-degree test in the extensions of a commuting-operator model

`LIDT.Simul.SoundCo`, the hypothesis on the low-individual-degree test, is soundness of the seeded
CL test in the model `S.toModel` of every commuting-operator strategy `S`. The Pauli basis analysis
of Phase 5 of `planning/mipco-track.md` needs it in the ancilla extensions `S.toModel.expand e`.
An extension by a unit vector is isomorphic to the model of a commuting-operator strategy on the
same space and state, `S.expandStrategy e he`, through the commutant of a matrix amplification
(`CommutingOperatorStrategy.expandIso`, `MIPRE/Foundations/AmplCommutant.lean`), and soundness
passes along isomorphisms (`SoundIn.of_iso`): so the hypothesis holds in every such extension as it
stands (`SoundCo.expand`).
-/

namespace MIPRE.LIDT.Simul

/-- **The seeded CL test is sound in every extension of a commuting-operator model by a unit
vector**, when it is sound in the commuting-operator model: the extension is the model of the
commuting-operator strategy `S.expandStrategy e he`, up to isomorphism
(`CommutingOperatorStrategy.expandIso`). -/
theorem SoundCo.expand (h : SoundCo) {X A : Type*} {Y B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (S : CommutingOperatorStrategy X Y A B) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (e : α × β → ℂ) (he : ‖evec e‖ = 1) :
    SoundIn (S.toModel.expand e) :=
  SoundIn.of_iso (S.expandIso e he) (h (S.expandStrategy e he))

end MIPRE.LIDT.Simul

end
