The definitions from which the main theorem of "MIP\* = RE" (Ji, Natarajan, Vidick, Wright, Yuen, arXiv:2001.04383, Theorem 12.2) is stated, written from scratch over Mathlib: elementary linear algebra and computability, and nothing from the rest of the formalization.

1. **POVM.** For a finite index set $X$ and a finite dimension index $d$, a POVM is a family $(E_x)_{x \in X}$ of self-adjoint complex $d \times d$ matrices that are positive semidefinite (nonnegative in the Loewner order) and sum to the identity.

2. **Synchronous game.** A synchronous game on a finite question alphabet $X$ and a finite answer alphabet $A$ consists of a probability distribution $\mu$ on $X \times X$ (nonnegative weights summing to one) and a decision predicate $D : X \times X \times A \times A \to \{\text{accept}, \text{reject}\}$ such that on equal questions $x = y$ every pair of unequal answers $a \ne b$ is rejected.

3. **Synchronous strategy.** A synchronous strategy for such a game is a dimension $d \ge 1$ together with, for every question $x$, a POVM $(M^x_a)_{a \in A}$ on $\mathbb{C}^d$ each of whose elements is idempotent, $M^x_a M^x_a = M^x_a$, that is, a projective measurement. Measurements for different questions need not commute. There is no state vector: outcome probabilities are computed in the normalized trace $\tau(M) = \operatorname{Tr}(M)/d$.

4. **Strategy value and synchronous value.** The value of a strategy is
$$
\omega(G, M) = \sum_{x, y} \sum_{a, b} \mu(x, y)\, D(x, y, a, b)\, \frac{\operatorname{Re}\operatorname{Tr}\bigl(M^x_a M^y_b\bigr)}{d},
$$
the probability that the players, measuring the shared maximally entangled state of dimension $d$ with the same measurements, give accepted answers. The synchronous value $\omega_{\mathrm{s}}(G)$ is the supremum of $\omega(G, M)$ over all synchronous strategies of all dimensions.

5. **Game descriptions.** A game description is a tuple of two natural numbers $n_X, n_A$, a finite list of weighted question pairs $(x, y, w) \in \mathbb{N}^3$ and a finite list of accepted tuples $(x, y, a, b) \in \mathbb{N}^4$. Game descriptions are in computable bijection with such tuples, hence codable as natural numbers. The description is interpreted as the synchronous game on $X = \{0, \dots, n_X\}$ and $A = \{0, \dots, n_A\}$ whose question distribution is proportional to the listed weights, with the point mass at $(0, 0)$ when the total listed weight is zero so that the interpretation is total, and whose decision predicate accepts exactly the listed tuples except that unequal answers to equal questions are rejected.

6. **Halting.** A Turing machine is a Gödel number of a partial recursive function; it halts on the empty input when its value at $0$ is defined.

7. **The statement.** The proposition *halting reduces to the game value* asserts the existence of a computable map $g$ from machines to game descriptions such that, for every machine $c$, the game $G_{g(c)}$ has synchronous value $1$ if $c$ halts on the empty input and synchronous value at most $\tfrac12$ if it does not. This proposition is the goal theorem of the mission.

These definitions are the fixed interface of the mission: every milestone and every proof is stated against them, so that an auditor can check the goal from first principles without reading the rest of the development.

**Formalization Note** The file is `MIPRE/HaltingGameValue.lean` of https://github.com/vidick/MIPRE-formalization at commit `70cbf1c`, reproduced verbatim. Matrices are Mathlib matrices over $\mathbb{C}$ with the Loewner order (`MatrixOrder`); `POVM` matches the QuantumLib definition with `selfAdjoint (Matrix d d ℂ)` spelled out. Machines are `Nat.Partrec.Code`, computability is Mathlib's `Computable`, and `GameData` is `Primcodable` through its bijection with a tuple of naturals and lists. The real part of the trace is taken in the strategy value, and the synchronous value is Lean's `iSup` over strategies in $\mathbb{R}$. The normalization proof inside `GameData.toGame` is the only proof in the file.
