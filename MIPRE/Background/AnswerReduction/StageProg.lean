/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.StageLists
import MIPRE.Foundations.Introspection.SeededLineProg
import MIPRE.Foundations.Introspection.LineRepresentativeProg
import MIPRE.Foundations.SAT.NormalElementProg
import MIPRE.Foundations.CL.DetypingProgParse
import MIPRE.Foundations.Introspection.BinaryBlockProg

/-!
# The stage programs of a copy of the PCP sampler

Piece AR-3d of `planning/answer-reduction.md`: polynomial-time functions answering the queries
of one copy of the seeded test, on the three runs of `k`-bit blocks (`MIPRE/Background/
AnswerReduction/Layout`). A copy is described by its offset `o`, length `sz = 2^jw`, selector
width `jw` and seed index `c`, all in unary (`Desc`), and a test type numbered `0, 1, 2`.

The answers are first written as plain functions of the blocks (`margL`, `linL`, `facL`),
with the field arithmetic done by the introspection stage programs (`selectedDirectionProg`,
`axisRepresentativeProg`, `lineRepresentativeProg`); `copyProg` computes them.
-/

noncomputable section

namespace MIPRE.AnswerReduction.StageProg

open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram

/-- A copy: offset, length, selector width and seed index, in unary. -/
abbrev Desc := Unary × Unary × Unary × Unary

/-- The three runs of blocks: point, direction, seeds. -/
abbrev Blocks := List BitStr × List BitStr × List BitStr

/-! ## The answers, as functions of the blocks -/

section Spec

variable (k : Unary) (d : Desc) (τ : ℕ)

/-- The zero field element. -/
def zb : BitStr := k.map fun _ => false

/-- Every block replaced by zero. -/
def zeroed (l : List BitStr) : List BitStr := l.map fun _ => zb k

/-- The copy's seed. -/
def seedOf (seeds : List BitStr) : BitStr := (seeds.drop d.2.2.2.length).headD []

/-- The selected direction of a diagonal line. -/
def selDirL (s : BitStr) (w : List BitStr) : List BitStr :=
  selectedDirectionProg ((k, d.2.2.1, s), w)

/-- The third stage's map of the point register. -/
def ptMapL (s : BitStr) (dir w : List BitStr) : List BitStr :=
  if τ = 1 then axisRepresentativeProg ((k, d.2.2.1, s), w)
  else if τ = 2 then lineRepresentativeProg (k, w, dir) else w

/-- The seed run of the first stage. -/
def seedOut (s : BitStr) (seeds : List BitStr) : List BitStr :=
  if τ = 0 then zeroed k seeds else placeL (zb k) d.2.2.2.length [s] seeds

/-- The direction run of the second stage. -/
def dirOut (s : BitStr) (dirs : List BitStr) : List BitStr :=
  if τ = 2 then placeL (zb k) d.1.length (selDirL k d s (sliceL d.1.length d.2.1.length dirs)) dirs
  else zeroed k dirs

/-- The point run of the third stage. -/
def ptOut (s : BitStr) (dir pts : List BitStr) : List BitStr :=
  placeL (zb k) d.1.length (ptMapL k d τ s dir (sliceL d.1.length d.2.1.length pts)) pts

/-- **The marginal** at level `j`. -/
def margL (j : ℕ) (x : Blocks) : Blocks :=
  let s := seedOf d x.2.2
  (if 3 ≤ j then ptOut k d τ s (selDirL k d s (sliceL d.1.length d.2.1.length x.2.1)) x.1
    else zeroed k x.1,
   if 2 ≤ j then dirOut k d τ s x.2.1 else zeroed k x.2.1,
   seedOut k d τ s x.2.2)

/-- **The stage map** at level `j`, from the prefix `u`, applied to `y`. -/
def linL (j : ℕ) (u y : Blocks) : Blocks :=
  if j = 1 then (zeroed k y.1, zeroed k y.2.1, seedOut k d τ (seedOf d y.2.2) y.2.2)
  else if j = 2 then (zeroed k y.1, dirOut k d τ (seedOf d u.2.2) y.2.1, zeroed k y.2.2)
  else if j = 3 then
    (ptOut k d τ (seedOf d u.2.2) (sliceL d.1.length d.2.1.length u.2.1) y.1, zeroed k y.2.1,
      zeroed k y.2.2)
  else (zeroed k y.1, zeroed k y.2.1, zeroed k y.2.2)

/-- The block of `k` copies of a bit. -/
def blk (b : Bool) : BitStr := k.map fun _ => b

/-- **The factor space** at level `j`, as blocks of indicator bits. -/
def facL (j : ℕ) (u : Blocks) : Blocks :=
  if j = 1 then (u.1.map fun _ => blk k false, u.2.1.map fun _ => blk k false,
    placeL (blk k false) d.2.2.2.length [blk k true] u.2.2)
  else if j = 2 then (u.1.map fun _ => blk k false,
    placeL (blk k false) d.1.length (List.replicate d.2.1.length (blk k true)) u.2.1,
    u.2.2.map fun _ => blk k false)
  else if j = 3 then (u.1.map fun _ => blk k true,
    placeL (blk k true) d.1.length (List.replicate d.2.1.length (blk k false)) u.2.1,
    placeL (blk k true) d.2.2.2.length [blk k false] u.2.2)
  else (u.1.map fun _ => blk k false, u.2.1.map fun _ => blk k false,
    u.2.2.map fun _ => blk k false)

/-- The runs of a bit string of `2m' + 6` blocks of `k` bits. -/
def blocksOf (m' : Unary) (z : BitStr) : Blocks :=
  let l := Introspection.BinaryBlock.splitBlocks (m'.length + (m'.length + 6)) k.length z
  (l.take m'.length, (l.drop m'.length).take m'.length, (l.drop m'.length).drop m'.length)

/-- The bits of three runs. -/
def bitsOf (x : Blocks) : BitStr := (x.1 ++ x.2.1 ++ x.2.2).flatten

/-- **The answer of a copy** to a query of kind `kind` at level `j` with vectors `u`, `y`. -/
def copyAnswer (m' : Unary) (kind j : ℕ) (u y : BitStr) : BitStr :=
  if kind = 1 then bitsOf (margL k d τ j (blocksOf k m' u))
  else if kind = 2 then bitsOf (linL k d τ j (blocksOf k m' u) (blocksOf k m' y))
  else if kind = 3 then bitsOf (facL k d j (blocksOf k m' u))
  else []

end Spec

/-! ## The programs -/

/-- Placing, as a program: `(fill, o, w, l) ↦ placeL fill o w l`. -/
def placeP : PolyTimeFun (BitStr × Unary × List BitStr × List BitStr) (List BitStr) :=
  let fill := fst
  let o := fst.comp snd
  let w := fst.comp (snd.comp snd)
  let l := snd.comp (snd.comp snd)
  ap₂ append (ap₂ append ((mapWith snd).comp ((take.comp (l.pair o)).pair fill)) w)
    ((mapWith snd).comp ((drop.comp (l.pair (ap₂ append o (length.comp w)))).pair fill))

@[simp] theorem placeP_apply (fill : BitStr) (o : Unary) (w l : List BitStr) :
    placeP (fill, o, w, l) = placeL fill o.length w l := by
  simp only [placeP, ap₂_apply, append_apply, comp_apply, mapWith_apply, pair_apply, take_apply,
    fst_apply, snd_apply, drop_apply, length_apply, List.length_append, length_unary, placeL]

/-- Slicing, as a program: `(o, sz, l) ↦ sliceL o sz l`. -/
def sliceP : PolyTimeFun (Unary × Unary × List BitStr) (List BitStr) :=
  take.comp ((drop.comp ((snd.comp snd).pair fst)).pair (fst.comp snd))

@[simp] theorem sliceP_apply (o sz : Unary) (l : List BitStr) :
    sliceP (o, sz, l) = sliceL o.length sz.length l := rfl

/-- The input of a copy's program: `(k, d, τ, m', kind, j, u, y)`. -/
abbrev Input := Unary × Desc × ℕ × Unary × ℕ × ℕ × BitStr × BitStr

section Prog

def kI : PolyTimeFun Input Unary := fst
def dI : PolyTimeFun Input Desc := fst.comp snd
def τI : PolyTimeFun Input ℕ := fst.comp (snd.comp snd)
def mI : PolyTimeFun Input Unary := fst.comp (snd.comp (snd.comp snd))
def kindI : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def jI : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
def uI : PolyTimeFun Input BitStr :=
  fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
def yI : PolyTimeFun Input BitStr :=
  snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd)))))
def oI : PolyTimeFun Input Unary := fst.comp dI
def szI : PolyTimeFun Input Unary := fst.comp (snd.comp dI)
def jwI : PolyTimeFun Input Unary := fst.comp (snd.comp (snd.comp dI))
def cI : PolyTimeFun Input Unary := snd.comp (snd.comp (snd.comp dI))

def zbP : PolyTimeFun Input BitStr := (map (const false)).comp kI
def blkP (b : Bool) : PolyTimeFun Input BitStr := (map (const b)).comp kI
def zeroedP (l : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input (List BitStr) :=
  (mapWith snd).comp (l.pair zbP)
def isτ (t : ℕ) : PolyTimeFun Input Bool := ap₂ SAT.ArrayProg.eqNat τI (const t)

def blocksP (z : PolyTimeFun Input BitStr) : PolyTimeFun Input Blocks :=
  let n := ap₂ append mI (ap₂ append mI (const (unary 6)))
  let l := Introspection.BinaryBlock.splitBlocksProg.comp (n.pair (kI.pair z))
  (take.comp (l.pair mI)).pair ((take.comp ((drop.comp (l.pair mI)).pair mI)).pair
    (drop.comp ((drop.comp (l.pair mI)).pair mI)))

def seedOfP (seeds : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input BitStr :=
  (headD []).comp (drop.comp (seeds.pair cI))

def selDirP (s : PolyTimeFun Input BitStr) (w : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  selectedDirectionProg.comp ((kI.pair (jwI.pair s)).pair w)

def ptMapP (s : PolyTimeFun Input BitStr) (dir w : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  ite (isτ 1) (axisRepresentativeProg.comp ((kI.pair (jwI.pair s)).pair w))
    (ite (isτ 2) (lineRepresentativeProg.comp (kI.pair (w.pair dir))) w)

def sliceI (l : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input (List BitStr) :=
  sliceP.comp (oI.pair (szI.pair l))

def seedOutP (s : PolyTimeFun Input BitStr) (seeds : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  ite (isτ 0) (zeroedP seeds) (placeP.comp (zbP.pair (cI.pair ((s.cons (const [])).pair seeds))))

def dirOutP (s : PolyTimeFun Input BitStr) (dirs : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  ite (isτ 2) (placeP.comp (zbP.pair (oI.pair ((selDirP s (sliceI dirs)).pair dirs))))
    (zeroedP dirs)

def ptOutP (s : PolyTimeFun Input BitStr) (dir pts : PolyTimeFun Input (List BitStr)) :
    PolyTimeFun Input (List BitStr) :=
  placeP.comp (zbP.pair (oI.pair ((ptMapP s dir (sliceI pts)).pair pts)))

def margP (x : PolyTimeFun Input Blocks) : PolyTimeFun Input Blocks :=
  let pts := fst.comp x
  let dirs := fst.comp (snd.comp x)
  let seeds := snd.comp (snd.comp x)
  let s := seedOfP seeds
  (ite (ap₂ leNat (const 3) jI) (ptOutP s (selDirP s (sliceI dirs)) pts) (zeroedP pts)).pair
    ((ite (ap₂ leNat (const 2) jI) (dirOutP s dirs) (zeroedP dirs)).pair (seedOutP s seeds))

def isJ (t : ℕ) : PolyTimeFun Input Bool := ap₂ SAT.ArrayProg.eqNat jI (const t)

def linP (u y : PolyTimeFun Input Blocks) : PolyTimeFun Input Blocks :=
  let ypts := fst.comp y
  let ydirs := fst.comp (snd.comp y)
  let yseeds := snd.comp (snd.comp y)
  let su := seedOfP (snd.comp (snd.comp u))
  ite (isJ 1) ((zeroedP ypts).pair ((zeroedP ydirs).pair (seedOutP (seedOfP yseeds) yseeds)))
    (ite (isJ 2) ((zeroedP ypts).pair ((dirOutP su ydirs).pair (zeroedP yseeds)))
      (ite (isJ 3) ((ptOutP su (sliceI (fst.comp (snd.comp u))) ypts).pair
          ((zeroedP ydirs).pair (zeroedP yseeds)))
        ((zeroedP ypts).pair ((zeroedP ydirs).pair (zeroedP yseeds)))))

def constBlk (b : Bool) (l : PolyTimeFun Input (List BitStr)) : PolyTimeFun Input (List BitStr) :=
  (mapWith snd).comp (l.pair (blkP b))

def facP (u : PolyTimeFun Input Blocks) : PolyTimeFun Input Blocks :=
  let pts := fst.comp u
  let dirs := fst.comp (snd.comp u)
  let seeds := snd.comp (snd.comp u)
  ite (isJ 1) ((constBlk false pts).pair ((constBlk false dirs).pair
      (placeP.comp ((blkP false).pair (cI.pair (((blkP true).cons (const [])).pair seeds))))))
    (ite (isJ 2) ((constBlk false pts).pair ((placeP.comp ((blkP false).pair (oI.pair
        ((replicate.comp (szI.pair (blkP true))).pair dirs)))).pair (constBlk false seeds)))
      (ite (isJ 3) ((constBlk true pts).pair ((placeP.comp ((blkP true).pair (oI.pair
          ((replicate.comp (szI.pair (blkP false))).pair dirs)))).pair
          (placeP.comp ((blkP true).pair (cI.pair (((blkP false).cons (const [])).pair seeds))))))
        ((constBlk false pts).pair ((constBlk false dirs).pair (constBlk false seeds)))))

def bitsP (x : PolyTimeFun Input Blocks) : PolyTimeFun Input BitStr :=
  Introspection.BinaryBlock.flattenProg.comp
    (ap₂ append (ap₂ append (fst.comp x) (fst.comp (snd.comp x))) (snd.comp (snd.comp x)))

def isKind (t : ℕ) : PolyTimeFun Input Bool := ap₂ SAT.ArrayProg.eqNat kindI (const t)

/-- **The program of a copy.** -/
def copyProg : PolyTimeFun Input BitStr :=
  ite (isKind 1) (bitsP (margP (blocksP uI)))
    (ite (isKind 2) (bitsP (linP (blocksP uI) (blocksP yI)))
      (ite (isKind 3) (bitsP (facP (blocksP uI))) (const [])))

end Prog

section Apply

variable (x : Input)

theorem blocksP_apply (z : PolyTimeFun Input BitStr) :
    blocksP z x = blocksOf (kI x) (mI x) (z x) := by
  simp only [blocksP, blocksOf, pair_apply, comp_apply, take_apply, drop_apply, ap₂_apply,
    append_apply, const_apply, Introspection.BinaryBlock.splitBlocksProg_apply,
    List.length_append, length_unary]

theorem ptMapP_apply (s : PolyTimeFun Input BitStr) (dir w : PolyTimeFun Input (List BitStr)) :
    ptMapP s dir w x = ptMapL (kI x) (dI x) (τI x) (s x) (dir x) (w x) := by
  simp only [ptMapP, ptMapL, PolyTimeFun.ite_apply, isτ, ap₂_apply, SAT.ArrayProg.eqNat_apply,
    const_apply, decide_eq_true_eq, comp_apply, pair_apply]
  rfl

theorem seedOutP_apply (s : PolyTimeFun Input BitStr) (seeds : PolyTimeFun Input (List BitStr)) :
    seedOutP s seeds x = seedOut (kI x) (dI x) (τI x) (s x) (seeds x) := by
  simp only [seedOutP, seedOut, PolyTimeFun.ite_apply, isτ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, comp_apply, pair_apply,
    cons_apply]
  split_ifs
  · rfl
  · exact placeP_apply _ _ _ _

theorem dirOutP_apply (s : PolyTimeFun Input BitStr) (dirs : PolyTimeFun Input (List BitStr)) :
    dirOutP s dirs x = dirOut (kI x) (dI x) (τI x) (s x) (dirs x) := by
  simp only [dirOutP, dirOut, PolyTimeFun.ite_apply, isτ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, comp_apply, pair_apply]
  split_ifs
  · exact placeP_apply _ _ _ _
  · rfl

theorem ptOutP_apply (s : PolyTimeFun Input BitStr) (dir pts : PolyTimeFun Input (List BitStr)) :
    ptOutP s dir pts x = ptOut (kI x) (dI x) (τI x) (s x) (dir x) (pts x) := by
  simp only [ptOutP, ptOut, comp_apply, pair_apply, ptMapP_apply]
  exact placeP_apply _ _ _ _

theorem margP_apply (X : PolyTimeFun Input Blocks) :
    margP X x = margL (kI x) (dI x) (τI x) (jI x) (X x) := by
  simp only [margP, margL, pair_apply, PolyTimeFun.ite_apply, ap₂_apply, leNat_apply,
    const_apply, decide_eq_true_eq, ptOutP_apply, dirOutP_apply, seedOutP_apply, comp_apply]
  rfl

theorem linP_apply (U Y : PolyTimeFun Input Blocks) :
    linP U Y x = linL (kI x) (dI x) (τI x) (jI x) (U x) (Y x) := by
  simp only [linP, linL, pair_apply, PolyTimeFun.ite_apply, isJ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, ptOutP_apply, dirOutP_apply,
    seedOutP_apply, comp_apply]
  rfl

theorem facP_apply (U : PolyTimeFun Input Blocks) :
    facP U x = facL (kI x) (dI x) (jI x) (U x) := by
  simp only [facP, facL, pair_apply, PolyTimeFun.ite_apply, isJ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, comp_apply, cons_apply,
    placeP_apply, replicate_apply]
  rfl

theorem bitsP_apply (X : PolyTimeFun Input Blocks) : bitsP X x = bitsOf (X x) := rfl

end Apply

theorem copyProg_apply (k : Unary) (d : Desc) (τ : ℕ) (m' : Unary) (kind j : ℕ) (u y : BitStr) :
    copyProg (k, d, τ, m', kind, j, u, y) = copyAnswer k d τ m' kind j u y := by
  simp only [copyProg, copyAnswer, PolyTimeFun.ite_apply, isKind, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, kindI, comp_apply, fst_apply, snd_apply, const_apply,
    decide_eq_true_eq, bitsP_apply, margP_apply, linP_apply, facP_apply, blocksP_apply]
  rfl

end MIPRE.AnswerReduction.StageProg

end
