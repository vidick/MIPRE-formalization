/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/Arena.lean
-/
/-
# The common finite-trace resolver arena (node 1.2.5): the existence theorem

The consumed-form structure `ResolverArena` is stated verbatim in
`Resolver/ArenaDef.lean` (moved there unchanged so that the block
construction of `Resolver/BlockArena.lean` can be imported here); this file
keeps the frozen existence statement `resolver_arena` and proves it from that
construction.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.ArenaDef
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.BlockArena

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

open scoped BigOperators InnerProductSpace

/-- **Common finite-trace resolver arena** (node 1.2.5;
04_resolver_corner.tex, thm common-resolver-arena, consumed form): every
pair of finite refined `[0,1]`-effect families over nonempty answer sets
(the manuscript's fallback answers `a₀ ∈ A`, `b₀ ∈ B`; without them a
POVM over an empty outcome set would be demanded — review #10, R1)
admits a resolver arena. The construction — semifinite linking algebra, columns and rows via the
resolver integral, polar data, the finite corner, and the normalization
unitary — is nodes 1.2.5.1–1.2.5.6 (Stage B). -/
theorem resolver_arena (M : StdTracialAlgebra.{0})
    {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (F : I → A → M.A) (G : J → B → M.A)
    (hF : ∀ i a, IsPosElem (F i a)) (hG : ∀ j b, IsPosElem (G j b))
    (hF1 : ∀ i, IsPosElem (1 - ∑ a : A, F i a))
    (hG1 : ∀ j, IsPosElem (1 - ∑ b : B, G j b)) :
    Nonempty (ResolverArena M F G) := by
  -- Proof layer: Resolver/BlockArena.lean (the block construction in the
  -- matrix amplification, driven by the sums-of-squares positivity).
  -- The contraction bounds `hF1`/`hG1` are not needed by this construction.
  have _ := hF1
  have _ := hG1
  classical
  choose kA cA hA using fun i a => hF i a
  choose kB cB hB using fun j b => hG j b
  exact ⟨BlockArena.arena kA kB (fun r => cA r.1 r.2.1 r.2.2) (fun s => cB s.1 s.2.1 s.2.2) F G
    (Classical.arbitrary A) (Classical.arbitrary B) (fun i a => hA i a) (fun j b => hB j b)⟩

end CommutingRepetition
