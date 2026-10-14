Lemma 5.1 of Marks, Nezhadi and Yuen, *The recursive compression method for proving undecidability results* (manuscript), in the form of blueprint node `lem:recursive-compression`.

Let $f$ assign to every bit string a value in $\mathbb{N} \cup \{\infty\}$, and let $A$ be a set of bit strings that contains some string $y_0$ and on which $f$ is finite. Suppose that a polynomial-time map $\mathrm{Compr}$, taking a program $c$, a size budget $m$ and a level $n$, satisfies the following whenever $c$ with budget $m$ is a succinct description of the string $x$:

1. $f(\mathrm{Compr}(c, m, n)) \ge \max(f(x), n)$, and
2. if $x \in A$ then $\mathrm{Compr}(c, m, n) \in A$.

Then there is a polynomial-time map $g$ from programs to bit strings such that, for every program $e$:

1. if $e$ halts on the empty input, then $g(e) \in A$;
2. if $e$ does not halt on the empty input, then $f(g(e)) = \infty$.

This is the fixed-point lemma that turns a gap-preserving compression procedure into a reduction from the halting problem: in the application, $A$ is the set of game descriptions with value $1$ and $f$ measures the level up to which a description certifies value at most one half. Lin's compressibility criterion (blueprint node `lem:compressible-criterion`) is derived from it, and it is the step of the proof of $\mathrm{MIP}^* = \mathrm{RE}$ whose statement involves computation alone.
