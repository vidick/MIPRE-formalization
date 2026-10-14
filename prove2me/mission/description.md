## Why the value of a nonlocal game matters

In a **two-player one-round nonlocal game**, a verifier samples a pair of questions, sends one to each of two players who cannot communicate, and accepts or rejects the pair of answers. The players may share an arbitrary quantum state and measure it; the **entangled value** of the game is the supremum of their acceptance probability over all such strategies. Nonlocal games are the operational form of Bell's theorem, the model behind device-independent cryptography and self-testing, and the engine of the complexity class $\mathrm{MIP}^*$ of languages decidable by a polynomial-time verifier interacting with entangled provers (Cleve, Høyer, Toner, Watrous, 2004, [arXiv:quant-ph/0404076](https://arxiv.org/abs/quant-ph/0404076)).

With classical provers, multiprover interactive proofs decide exactly $\mathrm{NEXP}$ (Babai, Fortnow, Lund, 1991, [doi:10.1007/BF01200056](https://doi.org/10.1007/BF01200056)). For entangled provers the lower bounds grew in steps: $\mathrm{NEXP} \subseteq \mathrm{MIP}^*$ (Ito, Vidick, 2012, [arXiv:1207.0550](https://arxiv.org/abs/1207.0550)), $\mathrm{NEEXP} \subseteq \mathrm{MIP}^*$ (Natarajan, Wright, 2019, [arXiv:1904.05870](https://arxiv.org/abs/1904.05870)), and finally $\mathrm{MIP}^* = \mathrm{RE}$ (Ji, Natarajan, Vidick, Wright, Yuen, 2020, [arXiv:2001.04383](https://arxiv.org/abs/2001.04383)): every recursively enumerable language, the halting problem included, has a two-prover one-round interactive proof with entangled provers, and the entangled value of a game cannot be approximated by any algorithm. Through the equivalences of Fritz (2012, [arXiv:1008.1168](https://arxiv.org/abs/1008.1168)), Junge, Navascués, Palazuelos, Pérez-García, Scholz, Werner (2011, [arXiv:1008.1142](https://arxiv.org/abs/1008.1142)) and Ozawa (2013, [arXiv:1212.1700](https://arxiv.org/abs/1212.1700)), the theorem gives a negative answer to Tsirelson's problem and to Connes' embedding problem for von Neumann algebras.

## Synchronous games, their value, and game descriptions

Everything below is defined from scratch; the formal development uses exactly these objects.

A **synchronous game** $G = (X, A, \mu, D)$ has a finite question alphabet $X$ and a finite answer alphabet $A$, shared by both players, a probability distribution $\mu$ on $X \times X$, and a decision predicate $D(x, y, a, b) \in \{0, 1\}$ which, on equal questions $x = y$, rejects every pair of unequal answers $a \ne b$.

A **synchronous strategy** of dimension $d \ge 1$ assigns to each question $x$ a **projective measurement** $(M^x_a)_{a \in A}$ on $\mathbb{C}^d$: positive semidefinite matrices summing to the identity, each idempotent. Both players use the same measurements, and probabilities are taken in the normalized trace $\tau(M) = \operatorname{Tr}(M)/d$. The **value** of the strategy is

$$
\omega(G, M) \;=\; \sum_{x, y \in X} \sum_{a, b \in A} \mu(x, y)\, D(x, y, a, b)\, \frac{\operatorname{Tr}\bigl(M^x_a M^y_b\bigr)}{d},
$$

the acceptance probability when the players measure a maximally entangled state of dimension $d$. The **synchronous value** $\omega_{\mathrm{s}}(G)$ is the supremum of $\omega(G, M)$ over all synchronous strategies of all dimensions. A synchronous strategy is a tensor-product strategy, so $\omega_{\mathrm{s}}(G) \le \omega^*(G)$, the entangled value.

A **game description** $g$ is a finite object from which a synchronous game is read off: natural numbers $n_X, n_A$ fixing $X = \{0, \dots, n_X\}$ and $A = \{0, \dots, n_A\}$, a finite list of weighted question pairs $(x, y, w)$ and a finite list of accepted tuples $(x, y, a, b)$. The game $G_g$ has $\mu(x, y)$ proportional to the total weight listed for $(x, y)$ (the point mass at $(0, 0)$ if the total weight is zero), and $D$ accepts exactly the listed tuples, except that unequal answers to equal questions are rejected. Descriptions are coded as natural numbers, so a map from machines to descriptions can be computable.

**Turing machines** are Gödel numbers $c \in \mathcal{C}$ of partial recursive functions, an equivalent model of computation; "$c$ halts on the empty input" means that $c$ applied to $0$ is defined.

## Formalization targets

### Goal: halting reduces to the synchronous game value

There is a computable map $g$ from machines to game descriptions such that for every machine $c$,

$$
c \text{ halts on the empty input} \;\Longrightarrow\; \omega_{\mathrm{s}}\bigl(G_{g(c)}\bigr) = 1,
\qquad
c \text{ does not halt} \;\Longrightarrow\; \omega_{\mathrm{s}}\bigl(G_{g(c)}\bigr) \le \tfrac12 .
$$

This is Theorem 12.2 of [arXiv:2001.04383](https://arxiv.org/abs/2001.04383) in synchronous form, with the running time of $g$ relaxed from polynomial to computable. It leaves the running time and the choice of value unfixed, and it is the weakest statement that already makes the game value uncomputable: no algorithm decides whether a game has synchronous value $1$ or at most $\tfrac12$.

### Stronger: polynomial time, and the entangled value

The paper's statement has $g$ computable in polynomial time, and both the synchronous and the entangled value satisfy the two clauses. With polynomial time the goal gives $\mathrm{RE} \subseteq \mathrm{MIP}^*$ for the class $\mathrm{MIP}^*_{1, 1/2}(2, 1)$ of two-prover one-round proofs with completeness $1$ and soundness $\tfrac12$, and with the elementary inclusion $\mathrm{MIP}^* \subseteq \mathrm{RE}$ this is $\mathrm{MIP}^* = \mathrm{RE}$. These statements need a model of polynomial time and a definition of tensor-product strategies, and will be added as milestones once those definitions are published here.

## Significance

*The result.* Approximating $\omega^*(G)$ to within a constant is as hard as the halting problem. A hierarchy of semidefinite programs converges from above to the commuting-operator value $\omega^{\mathrm{co}}(G)$, so the two values cannot coincide for every game: a negative answer to Tsirelson's problem and, by the equivalences cited above, to Connes' embedding problem, open since 1976. On the complexity side, $\mathrm{MIP}^* = \mathrm{RE}$ is the exact characterization of the power of entangled provers.

*Formalizing it.* The theorem is proved and its proof is machine-checked: `HaltingGameValue.halting_reduces_to_gameValue` in the Lean 4 development [vidick/MIPRE-formalization](https://github.com/vidick/MIPRE-formalization) proves exactly the goal above over Mathlib, with `propext`, `Classical.choice` and `Quot.sound` as its only axioms. The development is about 1,200 modules and 410,000 lines, including vendored components and a separate library for the low individual degree test; its [blueprint](https://vidick.github.io/MIPRE-formalization/blueprint/) records every statement, the dependency graph and the correspondence with the paper. This mission makes the result a fixed, auditable target: the definitional layer above is written over Mathlib alone, so the goal can be checked from first principles, and the components of the proof whose developments are self-contained are published as milestones with their proofs, to be imported, reused and re-proved. The first milestone, the recursive compression lemma of Marks, Nezhadi and Yuen (Lemma 5.1 of their manuscript; blueprint node `lem:recursive-compression`), comes with a complete proof over a dependency tree of 22 definition bundles and 60 theorems: a cost model of computation, an efficient universal machine, the s-m-n and Kleene recursion theorems, succinct descriptions.

## Difficulty

The obvious approach fails at once: a verifier runs in time polynomial in its input, while a machine may run for arbitrarily long before halting, so no fixed game can check halting by simulation. What makes $\mathrm{RE}$ reachable is **gap-preserving compression**: a polynomial-time transformation of verifiers such that the compressed verifier, at index $n$, has value $1$ when the original verifier at index $2^n$ does, and value at most $\tfrac12$ when the original does. The compressed game is exponentially cheaper than the game it certifies, and a fixed-point argument through Kleene's recursion theorem, in the abstract form of the recursive compression lemma, turns compression into the halting reduction. Compression rests on three components, each with a central ingredient that is a theorem in its own right: **question reduction by introspection**, in which the players sample their own questions and a Pauli basis self-test built on the **quantum low individual degree test** certifies that they did; **answer reduction**, in which the players prove through a probabilistically checkable proof that their answers would have been accepted; and **gap amplification by parallel repetition**. In each component soundness must hold against strategies of unbounded dimension, where no finite enumeration or compactness argument is available, and the quantitative losses must compose so that the threshold $\tfrac12$ is preserved exactly.

## Formalization scope

The goal is stated with the synchronous value, projective measurements on $\mathbb{C}^d$ with $d \ge 1$, and the normalized trace in place of a state vector; the real part of the trace is taken in the strategy value, and the synchronous value is the supremum, in $\mathbb{R}$, over all strategies of all dimensions (the values lie in $[0, 1]$). Game descriptions are interpreted with the fallback distribution above, so that the interpretation is total. Machines are Mathlib's `Nat.Partrec.Code` and computability is Mathlib's `Computable`; polynomial time is not fixed by the goal.

No trivializing formalization is available: the game depends on $c$ only through $g$, and the two clauses demand values $1$ and at most $\tfrac12$ on complementary sets of machines, so no map that ignores its argument, or produces only descriptions of zero total weight, satisfies the statement.

A complete development needs four layers: (i) a model of computation with costs, with polynomial-time maps, an efficient universal machine, the s-m-n and Kleene recursion theorems and succinct descriptions, which is the recursive compression milestone's dependency tree and is reusable in any undecidability argument by compression; (ii) normal form verifiers, conditionally linear samplers, the Pauli basis test and the quantum low individual degree test; (iii) the three transformations, with answer reduction over a PCP decider built from a succinct Cook–Levin theorem and direct parallel repetition in value form, and their soundness; (iv) the halting reduction from compression and the passage from the tensor-product to the synchronous value. Statements and proofs of these components over the shared definitional layer are welcome, as are alternative proofs of the goal from the same definitions, the polynomial-time and entangled-value strengthenings, and the inclusion $\mathrm{MIP}^* \subseteq \mathrm{RE}$.

## Selected references

- Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, *MIP\* = RE*, 2020 (revised 2022). [arXiv:2001.04383](https://arxiv.org/abs/2001.04383)
- Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, *Quantum soundness of the classical low individual degree test*, 2020. [arXiv:2009.12982](https://arxiv.org/abs/2009.12982)
- A. Marks, S. S. Nezhadi, H. Yuen, *The recursive compression method for proving undecidability results*, manuscript.
- J. Lin, *Tracially embeddable strategies: lifting MIP\* tricks to MIP^co*, 2023. [arXiv:2304.01940](https://arxiv.org/abs/2304.01940)
- A. Natarajan, J. Wright, *NEEXP ⊆ MIP\**, FOCS 2019. [arXiv:1904.05870](https://arxiv.org/abs/1904.05870)
- T. Ito, T. Vidick, *A multi-prover interactive proof for NEXP sound against entangled provers*, FOCS 2012. [arXiv:1207.0550](https://arxiv.org/abs/1207.0550)
- R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal strategies*, CCC 2004. [arXiv:quant-ph/0404076](https://arxiv.org/abs/quant-ph/0404076)
- L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive protocols*, Computational Complexity 1 (1991). [doi:10.1007/BF01200056](https://doi.org/10.1007/BF01200056)
- T. Fritz, *Tsirelson's problem and Kirchberg's conjecture*, Reviews in Mathematical Physics 24 (2012). [arXiv:1008.1168](https://arxiv.org/abs/1008.1168)
- M. Junge, M. Navascués, C. Palazuelos, D. Pérez-García, V. B. Scholz, R. F. Werner, *Connes' embedding problem and Tsirelson's problem*, Journal of Mathematical Physics 52 (2011). [arXiv:1008.1142](https://arxiv.org/abs/1008.1142)
- N. Ozawa, *About the Connes embedding conjecture: algebraic approaches*, Japanese Journal of Mathematics 8 (2013). [arXiv:1212.1700](https://arxiv.org/abs/1212.1700)
- The Lean development: [vidick/MIPRE-formalization](https://github.com/vidick/MIPRE-formalization) (statement `MIPRE/HaltingGameValue.lean`, proof `MIPRE/MainTheorem.lean`) and its [blueprint](https://vidick.github.io/MIPRE-formalization/blueprint/).
