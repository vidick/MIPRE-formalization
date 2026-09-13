#!/usr/bin/env python3
r"""Repair lem:dhalt-values: item 2 is a transfer, not an absolute bound.

Checked against paper/recursive.tex in vidick/mipre-proof. The paper's item 2 reads
"if M does not halt in n steps then V^halt_n has a value-1 PCC strategy if and only if
V^compr_n does, and Ent(V^halt_n, 1/2) = Ent(V^compr_n, 1/2)", and its proof gives the
reason: when M does not halt within n steps, D^halt accepts exactly when D^compr does
and the two verifiers share the sampler, so the two games coincide up to an
identification of the answer alphabets.

The blueprint had item 2 as "val*(V^halt_n) <= 1/2" from the same hypothesis. That is
false, and the paper's own completeness proof is the counterexample: for C_0 <= n < T
with T the halting time of a machine that *does* halt, M does not halt within n steps,
and the paper applies item 2 there to conclude that game_n has value *1*, by downward
induction from level 2^n. The absolute bound holds only when M never halts, and is the
conclusion of the recursion in thm:halting rather than a per-level fact.

Exact-string replacement; --check asserts each anchor occurs exactly once.
"""
import sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
F = ROOT / "blueprint/src/content/06_proof_structure.tex"

EDITS = [
(r"""\uses{lem:halt-construction,lem:lambda,thm:compression,def:pcc,def:q-value}
For every $n$:
\begin{enumerate}
\item if $\machine$ halts within $n$ steps then $\valstar(\vhalt_n) = 1$, witnessed by a
  value-$1$ PCC strategy;
\item if $\machine$ does not halt within $n$ steps then $\valstar(\vhalt_n) \leq
  \frac12$.
\end{enumerate}
\end{lemma}
\begin{proof}
Item 1 is the fixed-answer strategy. Item 2 applies the soundness clause of
Theorem~\ref{thm:compression} to the verifier built from $F$'s description; the induction
is over scales and is well founded, the self-reference introducing no circularity because
$\dhalt$ at index $n$ only ever invokes compression at strictly smaller scales. This is
the node the companion repository's audit challenged twice; the two challenges concerned
the well-foundedness and the answer-alphabet identification, and both were resolved
in the source.
\end{proof}
""",
r"""\uses{lem:halt-construction,lem:lambda,lem:compress-sampler-indep,def:pcc,def:q-value}
For every $n$:
\begin{enumerate}
\item if $\machine$ halts within $n$ steps then $\valstar(\vhalt_n) = 1$, witnessed by a
  value-$1$ PCC strategy;
\item if $\machine$ does not halt within $n$ steps then $\vhalt_n$ and $\vcompr_n$ are the
  same game up to an identification of the answer alphabets; in particular
  $\valstar(\vhalt_n) = \valstar(\vcompr_n)$, and $\vhalt_n$ has a value-$1$ PCC strategy
  if and only if $\vcompr_n$ does.
\end{enumerate}
\end{lemma}
\begin{proof}
Item 1 is the fixed-answer strategy: when $\machine$ halts within $n$ steps, $\dhalt$
accepts every answer pair on every question pair in the support, so any strategy has value
$1$ and the constant-$0$ strategy is PCC. For item 2, $\dhalt$ at index $n$ performs the
same question-length check as $\dcompr$ and then runs $\dcompr(n, x, y, a, b)$ verbatim,
with $\mathtt{TIMEOUT}$ rejecting in both, so the two deciders accept on exactly the same
inputs; and the two verifiers share the sampler $\shalt = \mathtt{ComputeSampler}(\lambda)$
(Lemma~\ref{lem:compress-sampler-indep}), so a strategy for either is a strategy for the
other with the same winning probability. The timeout counter of $\dhalt$ does not
interfere: its bound is chosen in Lemma~\ref{lem:lambda} so that the computations above
finish first.
\end{proof}

\begin{remark}[Item 2 is a transfer, not a bound]
\label{rem:dhalt-transfer}
\uses{lem:dhalt-values,thm:halting,thm:compression}
Item 2 is deliberately not ``$\valstar(\vhalt_n) \leq \frac12$''. That per-level bound is
false: if $\machine$ halts for the first time at step $T$, then for every $n < T$ it does
not halt within $n$ steps, yet $\valstar(\vhalt_n) = 1$ --- item 1 gives value $1$ at every
level $\geq T$, and item 2 together with the completeness clause of
Theorem~\ref{thm:compression} carries it \emph{downward} from level $2^n$ to level $n$,
which is exactly how the completeness half of Theorem~\ref{thm:halting} is proved. The
absolute bound needs $\machine$ never to halt, and is then the conclusion of the recursion
in Theorem~\ref{thm:halting}, not an ingredient of it. Recorded here because an earlier
revision of this chapter did state item 2 as the bound, and because the ledger node
`1.6.3' states it that way too; the formalization should follow the paper.
\end{remark}
"""),
]


def main():
    check = "--check" in sys.argv
    text = F.read_text()
    problems = []
    for anchor, repl in EDITS:
        n = text.count(anchor)
        if n != 1:
            problems.append(f"anchor occurs {n} times, expected 1")
            continue
        if "rem:dhalt-transfer" in text:
            problems.append("already applied (rem:dhalt-transfer present)")
            continue
        text = text.replace(anchor, repl, 1)
    if problems:
        for q in problems:
            print("  FAIL " + q, file=sys.stderr)
        return 1
    if check:
        print("check passed; nothing written")
        return 0
    F.write_text(text)
    print("wrote 06_proof_structure.tex")
    return 0


if __name__ == "__main__":
    sys.exit(main())
