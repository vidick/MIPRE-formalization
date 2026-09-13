#!/usr/bin/env python3
"""Blueprint: tag the finished Lean code that the blueprint did not yet name.

Every edit is an exact-string replacement. Run with --check first: it asserts that
each anchor occurs exactly once in its file and that no replacement text is already
present, then exits without writing.

The Lean names introduced here were verified sorry-free by `#print axioms` (only
[propext, Classical.choice, Quot.sound] or less), except
`HaltingGameValue.halting_reduces_to_gameValue`, which carries a `sorry` and is
therefore given a statement-level \\leanok only.
"""
import sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
CONTENT = ROOT / "blueprint" / "src" / "content"

EDITS = []

def edit(fname, anchor, replacement, why, marker):
    """marker: a string unique to the replacement, used to detect a re-run."""
    EDITS.append((fname, anchor, replacement, why, marker))

# --------------------------------------------------------------------------
# 1. def:game-description -- HaltingGameValue.GameData is the Lean object the
#    definition already names in prose; make it machine-checkable.
# --------------------------------------------------------------------------
edit("02_foundations.tex",
"""\\begin{definition}[Game description]
\\label{def:game-description}
\\uses{def:sync-game}
""",
"""\\begin{definition}[Game description]
\\label{def:game-description}
\\uses{def:sync-game}
\\lean{HaltingGameValue.GameData, HaltingGameValue.GameData.toGame}
\\leanok
""",
"tag def:game-description with GameData and GameData.toGame",
     "HaltingGameValue.GameData.toGame")

# --------------------------------------------------------------------------
# 2. thm:main -- the project's formalization target, previously named only in prose.
#    The Lean proof is `sorry`, so no proof-level \leanok.
# --------------------------------------------------------------------------
edit("07_main_theorem.tex",
"""\\label{thm:main}
\\uses{thm:halting,def:game-description,def:sync-value,def:re}
""",
"""\\label{thm:main}
\\uses{thm:halting,def:game-description,def:sync-value,def:re}
\\lean{HaltingGameValue.halting_reduces_to_gameValue}
\\leanok
""",
"tag thm:main with the Lean main statement",
     "HaltingGameValue.halting_reduces_to_gameValue")

# --------------------------------------------------------------------------
# 3. A remark recording the remaining definitions of the standalone restatement.
# --------------------------------------------------------------------------
edit("07_main_theorem.tex",
"""\\begin{corollary}[Halting reduces to the quantum value]
\\label{cor:main-quantum}""",
"""\\begin{remark}[The standalone restatement]
\\label{rem:standalone-restatement}
\\uses{def:game-description,def:sync-value}
\\lean{HaltingGameValue.gameValue, HaltingGameValue.GameData.equivTuple}
\\leanok
The Lean main statement is deliberately self-contained: the file
\\texttt{MIPRE/HaltingGameValue.lean} imports nothing from the rest of this development,
re-declaring the synchronous game, the synchronous strategy and the value on top of
Mathlib alone, so that Theorem~\\ref{thm:main} can be read without any of the vocabulary
built in Section~\\ref{ch:foundations}. In that reduced vocabulary \\texttt{gameValue} is
the synchronous value of Definition~\\ref{def:sync-value} and \\texttt{equivTuple}
exhibits the canonical G\\"odel numbering asserted in
Definition~\\ref{def:game-description} as an explicit equivalence between game
descriptions and a tuple of integers and lists, which is what supplies the
\\texttt{Encodable} instance the computability clause quantifies over. The duplication is
the price of a statement that stands alone, and keeping the two vocabularies in step is a
maintenance obligation rather than a mathematical one: the definitions match one for one,
and this is the list of the ones that do.
\\end{remark}

\\begin{corollary}[Halting reduces to the quantum value]
\\label{cor:main-quantum}""",
"record the standalone restatement's own definitions",
     "rem:standalone-restatement")

# --------------------------------------------------------------------------
# 4. ch04: the halting-problem form of the two reduction lemmas. Both Lean
#    statements are sorry-free and were not named anywhere in the blueprint.
# --------------------------------------------------------------------------
edit("04_computability.tex",
"""The Lean proof reuses the toolkit of Section~\\ref{sec:rr-computability}: the search
branch runs the semidecision procedure through the clocked universal machine, and the
start level of the recursion is carried as data next to the current level.
""",
"""The Lean proof reuses the toolkit of Section~\\ref{sec:rr-computability}: the search
branch runs the semidecision procedure through the clocked universal machine, and the
start level of the recursion is carried as data next to the current level.

\\effortEasy

\\begin{lemma}[Halting form of the two reduction lemmas]
\\label{lem:halting-form}
\\uses{lem:recursive-compression,lem:compressible-criterion,def:re}
\\lean{MIPRE.Cost.recursive_compression_halting,
MIPRE.Cost.compressibility_criterion_halting}
\\leanok
Lemma~\\ref{lem:recursive-compression} and Lemma~\\ref{lem:compressible-criterion} both
hold with the halting problem taken in the ambient formalization's own form: the reduction
may be presented as a computable map defined on the codes of a fixed G\\"odel numbering of
the partial recursive functions, halting being halting of the code on input $0$, rather
than on the programs of the cost model in which the two lemmas are proved.
\\end{lemma}

\\begin{proof}
\\leanok
\\uses{lem:recursive-compression,lem:compressible-criterion}
Compose the reduction with a compiler from codes to programs of the cost model that is
computable on descriptions and preserves halting on the empty input: hardcode the code's
index into a fixed program for the universal partial function, which exists because that
partial function is partial recursive, and observe that the description of the result is a
fixed primitive recursive tree around the index. Only the interface changes; neither
lemma's content is touched, and the compiler carries no time bound, which is why this step
is available for the computable version of the main theorem and not for the
polynomial-time one.
\\end{proof}

\\paragraph{Comments.} This is the seam at which the development meets Mathlib's halting
problem, hence the form Theorem~\\ref{thm:main} consumes: \\texttt{Nat.Partrec.Code} is
what \\texttt{Computable} is stated against, while the two reduction lemmas are proved
about programs of the cost model of Section~\\ref{sec:rr-computability}, whose
polynomial-time predicate the fixed-point construction needs. Separating the two keeps the
cost model out of the main statement entirely.
""",
"new lemma: the Mathlib-halting form of the reduction lemmas",
     "lem:halting-form")

# --------------------------------------------------------------------------
# 5. ch03: the groundwork for lem:value-lower-approx that is already in Lean.
# --------------------------------------------------------------------------
edit("03_background_results.tex",
"""\\paragraph{Comments.} This is the easy inclusion $\\MIPstar \\subseteq \\RE$ and one half
of Theorem~\\ref{thm:mipstar-eq-re}.""",
"""\\begin{lemma}[Decidable candidate set: a norm constraint is two psd tests]
\\label{lem:norm-two-psd}
\\uses{lem:value-lower-approx}
\\lean{MIPRE.ValueApprox.posSemidef_realSmul_one_add_and_sub_iff}
\\leanok
\\ledgernode{1.1.7.2.1}
Let $M$ be a Hermitian matrix and $c$ a real number. Then $c\\Id + M \\succeq 0$ and
$c\\Id - M \\succeq 0$ both hold if and only if $-c\\norm{x}^2 \\leq \\bra{x} M \\ket{x}
\\leq c \\norm{x}^2$ for every vector $x$ --- which for Hermitian $M$ says
$\\norm{M} \\leq c$.
\\end{lemma}

\\begin{proof}
\\leanok
Both directions are the defining property of positive semidefiniteness applied to the
quadratic form, read once forwards and once backwards; the scalar step is
$\\bra{x}(c\\Id \\pm M)\\ket{x} = c\\norm{x}^2 \\pm \\bra{x} M \\ket{x}$.
\\end{proof}

\\begin{lemma}[The perturbation split]
\\label{lem:perturbation-split}
\\uses{lem:value-lower-approx,def:q-value}
\\lean{MIPRE.ValueApprox.dotProduct_mulVec_perturb,
MIPRE.ValueApprox.kronecker_sub_kronecker,
MIPRE.ValueApprox.dotProduct_kronecker_perturb}
\\leanok
\\ledgernode{1.1.7.2.3}
\\ledgernode{1.1.7.2.4}
For matrices $M, N$ and vectors $\\psi, \\phi$,
\\[
\\bra{\\psi} M \\ket{\\psi} - \\bra{\\phi} N \\ket{\\phi}
  = \\bra{\\psi} (M - N) \\ket{\\psi} + \\bra{\\psi - \\phi} N \\ket{\\psi}
    + \\bra{\\phi} N \\ket{\\psi - \\phi},
\\]
and $A \\ot B - A' \\ot B' = (A - A') \\ot B + A' \\ot (B - B')$; combining the two splits a
bipartite Born expectation in which both players' operators and the state have moved into
four terms, each moving exactly one of $A$, $B$ and $\\psi$.
\\end{lemma}

\\begin{proof}
\\leanok
Expand and cancel. Both identities are exact: no norm and no estimate occurs in either,
and the analytic bounds are obtained afterwards by bounding the terms separately.
\\end{proof}

\\paragraph{Comments.} This is the easy inclusion $\\MIPstar \\subseteq \\RE$ and one half
of Theorem~\\ref{thm:mipstar-eq-re}.""",
"new lemmas: the ValueApprox groundwork already proved in Lean",
     "lem:perturbation-split")


def main():
    check = "--check" in sys.argv
    seen = {}
    problems = []
    for fname, anchor, repl, why, marker in EDITS:
        p = CONTENT / fname
        text = seen.get(fname, p.read_text())
        n = text.count(anchor)
        if n != 1:
            problems.append(f"{fname}: anchor for '{why}' occurs {n} times, expected 1")
            continue
        if marker not in repl:
            problems.append(f"{fname}: marker {marker!r} is not in the replacement for '{why}'")
            continue
        if marker in text:
            problems.append(f"{fname}: '{why}' already applied ({marker!r} present)")
            continue
        seen[fname] = text.replace(anchor, repl, 1)
        print(f"  ok  {fname}: {why}")
    if problems:
        for q in problems:
            print("  FAIL " + q, file=sys.stderr)
        return 1
    if check:
        print("check passed; nothing written")
        return 0
    for fname, text in seen.items():
        (CONTENT / fname).write_text(text)
        print(f"wrote {fname}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
