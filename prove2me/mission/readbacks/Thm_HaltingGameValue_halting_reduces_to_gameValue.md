# Read-back: `HaltingGameValue.halting_reduces_to_gameValue`

**What the declaration is.** A theorem with no parameters: no universally quantified variables, no hypotheses, no implicit arguments and no typeclass assumptions at the top level. Its statement is the single proposition `HaltingGameValue.HaltingReducesToGameValue`, which is unfolded in full below. The proof body is `sorry` and is not part of this read-back. The only typeclass instances involved anywhere are the canonical finiteness and decidable-equality instances on the finite types $\{0,\dots,n\}$ that appear inside the definitions, so they place no constraint on the claim.

## 1. The proposition asserted

Write $\mathrm{Code}$ for Mathlib's type of codes of partial recursive functions (§2), $\varphi_c : \mathbb{N} \rightharpoonup \mathbb{N}$ for the partial function computed by the code $c$, $\mathrm{GameData}$ for the type of game descriptions (§3), $\mathcal{G}_{g}$ for the synchronous game that a description $g$ denotes (§4), and $\omega_s(\mathcal{G})$ for the synchronous value of a game (§6). The theorem asserts exactly:

$$
\exists\, g : \mathrm{Code} \to \mathrm{GameData}\ \text{ such that }\quad
g \text{ is computable (§3)}\ \ \wedge\ \
\forall c \in \mathrm{Code}:\
\Big(\varphi_c(0)\!\downarrow\ \Longrightarrow\ \omega_s(\mathcal{G}_{g(c)}) = 1\Big)
\ \wedge\
\Big(\varphi_c(0)\!\uparrow\ \Longrightarrow\ \omega_s(\mathcal{G}_{g(c)}) \le \tfrac12\Big).
$$

Here $\varphi_c(0)\!\downarrow$ is the predicate the file names "halts on the empty input" (§2), $\varphi_c(0)\!\uparrow$ is its negation, and $1$ and $\tfrac12$ are **real numbers**: $\omega_s$ is real-valued, so $1/2$ is real division, i.e. $0.5$, not natural-number division. The inequality $\le$ is non-strict.

The existential is plain existence ($\exists$), not unique existence. The map $g$ is chosen once, before $c$, and must work for every code $c$. The game $\mathcal{G}_{g(c)}$ has question and answer alphabets of sizes $n_X + 1$ and $n_A + 1$ where $n_X, n_A$ are read off $g(c)$, so the alphabets may depend on $c$. Nothing in the statement bounds the size of the description $g(c)$ in terms of $c$, and "computable" carries no resource bound (§3).

## 2. Codes and the "halting" predicate

$\mathrm{Code}$ is Mathlib's `Nat.Partrec.Code`: an inductive datatype of programs built from the constant-zero function, the successor function, the two coordinate projections of Mathlib's pairing bijection $\mathbb{N}\times\mathbb{N} \to \mathbb{N}$, and closed under pairing of two programs, composition, primitive recursion and unbounded search (the $\mu$-operator). Each code $c$ computes a partial function $\varphi_c : \mathbb{N} \rightharpoonup \mathbb{N}$ (Mathlib's `Nat.Partrec.Code.eval`).

The predicate written `HaltsOnEmptyInput c` is, literally,

$$
\varphi_c(0)\!\downarrow \qquad\text{i.e.}\qquad \text{the partial function } \varphi_c \text{ is defined (converges) at the natural number } 0 .
$$

Nothing else is encoded: "the empty input" is the number $0 \in \mathbb{N}$, and no other input is mentioned. The negation $\varphi_c(0)\!\uparrow$ means $\varphi_c$ is undefined at $0$.

## 3. Game descriptions and the computability notion

A **game description** $g \in \mathrm{GameData}$ is a quadruple

$$
g = (n_X,\ n_A,\ w,\ \mathrm{acc})
$$

with $n_X, n_A \in \mathbb{N}$, $w$ a finite list of triples $(x', y', k) \in \mathbb{N}^3$ and $\mathrm{acc}$ a finite list of quadruples $(x', y', a', b') \in \mathbb{N}^4$. There are **no** constraints on these data: the lists may be empty, may contain repeated entries, may contain entries whose coordinates exceed $n_X$ or $n_A$, and weights $k$ may be $0$. The reading of the coordinates as $(x', y', \text{weight})$ and $(x', y', a', b')$ is fixed only by how §4 uses them.

**Gödel numbering.** $\mathrm{GameData}$ is in evident bijection with $\mathbb{N}\times\mathbb{N}\times \mathrm{List}(\mathbb{N}^3)\times\mathrm{List}(\mathbb{N}^4)$, $g \mapsto (n_X, n_A, w, \mathrm{acc})$, and its Gödel numbering is Mathlib's standard encoding of that tuple type (nested pairing via Mathlib's pairing bijection, and the standard encoding of lists of naturals), transported along this bijection. $\mathrm{Code}$ carries Mathlib's own standard Gödel numbering, under which every natural number is the number of some code.

**Computability.** "$g$ is computable" is Mathlib's `Computable g`: the partial function on Gödel numbers

$$
n \ \longmapsto\ \ulcorner g(c)\urcorner \qquad\text{where } c \text{ is the code with Gödel number } n
$$

is partial recursive in the sense of Mathlib's inductively defined class `Nat.Partrec` — the least class of partial functions $\mathbb{N}\rightharpoonup\mathbb{N}$ containing zero, successor and the two pairing projections and closed under pairing, composition, primitive recursion and unbounded search (the Kleene partial recursive functions). This is computability only; no bound on time or space is asserted.

## 4. The synchronous game denoted by a description

Fix $g = (n_X, n_A, w, \mathrm{acc})$. Its game $\mathcal{G}_g$ has

- question alphabet $X_g = \{0, 1, \dots, n_X\}$, so $|X_g| = n_X + 1 \ge 1$ (never empty);
- answer alphabet $A_g = \{0, 1, \dots, n_A\}$, so $|A_g| = n_A + 1 \ge 1$ (never empty).

**Weights.** For arbitrary $x, y \in \mathbb{N}$, the weight of the pair $(x,y)$ is the natural number

$$
W_g(x,y) \;=\; \sum_{\substack{(x',y',k)\in w\\ x' = x,\ y' = y}} k ,
$$

a sum over list *entries* (an entry occurring twice in $w$ contributes twice). The total weight is

$$
T_g \;=\; \sum_{x=0}^{n_X}\ \sum_{y=0}^{n_X} W_g(x,y) \ \in \mathbb{N},
$$

so an entry of $w$ with $x' > n_X$ or $y' > n_X$ contributes to no $W_g(x,y)$ with $x, y \le n_X$ and is ignored by $T_g$ and by everything below.

**Question distribution.** For $x, y \in X_g$,

$$
\mu_g(x,y) \;=\;
\begin{cases}
\mathbf{1}[\,x = 0 \ \wedge\ y = 0\,] & \text{if } T_g = 0,\\[6pt]
\dfrac{W_g(x,y)}{T_g} & \text{if } T_g \neq 0,
\end{cases}
$$

a real number. Thus $\mu_g$ is a rational-valued probability distribution on $X_g \times X_g$; when $T_g = 0$ — which happens when $w$ is empty, when every weight in $w$ is $0$, or when every entry of $w$ with nonzero weight has a coordinate exceeding $n_X$ — it is the point mass at the question pair $(0,0)$, which always exists since $0 \in X_g$. The structure carries proofs that $\mu_g(x,y) \ge 0$ for all $x,y$ and $\sum_{x,y}\mu_g(x,y) = 1$; the division is never by zero because of the case split. No symmetry $\mu_g(x,y) = \mu_g(y,x)$ is imposed.

**Decision predicate.** For $x, y \in X_g$ and $a, b \in A_g$,

$$
D_g(x,y,a,b) \;=\;
\begin{cases}
\text{false} & \text{if } x = y \text{ and } a \neq b,\\[4pt]
\mathbf{1}\big[(x,y,a,b) \in \mathrm{acc}\big] & \text{otherwise},
\end{cases}
$$

where membership is membership of the quadruple of natural numbers in the list $\mathrm{acc}$ (repetitions in $\mathrm{acc}$ are irrelevant). In particular: on equal questions $x = y$, equal answers $a = b$ are accepted **only if** $(x,x,a,a)$ is listed in $\mathrm{acc}$ — equal answers are not automatically accepted; on $x \neq y$ acceptance is exactly membership of $(x,y,a,b)$ in $\mathrm{acc}$, with no symmetry $D_g(x,y,a,b) = D_g(y,x,b,a)$ imposed; entries of $\mathrm{acc}$ with a coordinate $> n_X$ in the first two places or $> n_A$ in the last two are never consulted.

## 5. Synchronous games in general

A **synchronous game** on finite types $X$ (questions) and $A$ (answers, with decidable equality) is a pair $(\mu, D)$ where $\mu : X\times X \to \mathbb{R}$ satisfies $\mu(x,y) \ge 0$ for all $x,y$ and $\sum_{x\in X}\sum_{y\in X}\mu(x,y) = 1$, and $D : X\times X\times A\times A \to \{\text{true},\text{false}\}$ satisfies $D(x,x,a,b) = \text{false}$ whenever $a \ne b$. No other condition (symmetry of $\mu$ or of $D$, nontriviality, etc.) is part of the definition. $\mathcal{G}_g$ of §4 is such a game with $X = X_g$, $A = A_g$, $\mu = \mu_g$, $D = D_g$.

## 6. Strategies, strategy value, and the game value

**POVM.** For a finite index set $A$ and a dimension $d$ (matrices indexed by $\{0,\dots,d-1\}$, i.e. $d\times d$ matrices), a POVM is a family $(M_a)_{a \in A}$ of complex $d \times d$ matrices such that each $M_a$ is self-adjoint ($M_a^* = M_a$, conjugate transpose), each $M_a$ is positive semidefinite in the Loewner order ($v^* M_a v \ge 0$ for all $v \in \mathbb{C}^d$), and $\sum_{a\in A} M_a = I_d$, the identity matrix.

**Synchronous strategy.** For a synchronous game $\mathcal{G}$ on $(X, A)$, a synchronous strategy $S$ consists of

- a natural number $d$ with $d \ge 1$ (the dimension; every finite $d \ge 1$ is allowed, and no infinite-dimensional object appears);
- for each question $x \in X$, a POVM $(M^x_a)_{a\in A}$ of $d\times d$ matrices as above;
- the idempotence condition $M^x_a\, M^x_a = M^x_a$ for every $x \in X$ and $a \in A$.

(A self-adjoint idempotent matrix is an orthogonal projection, so each family $(M^x_a)_a$ is a projection-valued measure on $\mathbb{C}^d$.) No relation between $M^x_a$ and $M^y_b$ for $x\neq y$ is required — in particular no commutation. There is no state vector among the data. The strategy data refer to $\mathcal{G}$ only through its alphabets $X$ and $A$: $\mu$ and $D$ play no role in what counts as a strategy, only in the value below.

**Strategy value.** The value of $S$ in $\mathcal{G} = (\mu, D)$ is the real number

$$
v(\mathcal{G}, S) \;=\; \sum_{x\in X}\sum_{y\in X}\sum_{a\in A}\sum_{b\in A}\
\mu(x,y)\ \cdot\ \mathbf{1}[D(x,y,a,b)]\ \cdot\ \frac{\operatorname{Re}\operatorname{Tr}\!\big(M^x_a\, M^y_b\big)}{d},
$$

where $\mathbf{1}[\cdot]$ is $1$ for true and $0$ for false, $\operatorname{Tr}$ is the trace of the complex matrix product $M^x_a M^y_b$ (in that order), and $\operatorname{Re}$ takes its real part. The same single family $(M^x_a)_{x,a}$ is used in both question slots. Division is by the real number $d \ge 1$, so it is never division by zero. (For self-adjoint $M, N$ the number $\operatorname{Tr}(MN)$ is real, and for positive semidefinite $M, N$ it is $\ge 0$; the definition takes the real part regardless.)

**Game value.** The synchronous value of $\mathcal{G}$ is

$$
\omega_s(\mathcal{G}) \;=\; \sup_{S}\ v(\mathcal{G}, S),
$$

the supremum over **all** synchronous strategies $S$ of all finite dimensions $d \ge 1$, taken in $\mathbb{R}$ with Mathlib's convention for real suprema: if the set of values $\{v(\mathcal{G},S) : S\}$ is nonempty and bounded above, $\omega_s(\mathcal{G})$ is its least upper bound; **if that set is empty or not bounded above, $\omega_s(\mathcal{G})$ is $0$.** The definition does not itself record which case obtains. (A reader can check that for the games of §4 the strategy type is nonempty — e.g. $d = 1$, $M^x_0 = (1)$, $M^x_a = (0)$ for $a \neq 0$ — and that every strategy value lies in $[0,1]$, since each term is $\ge 0$ and $\sum_{a,b}\operatorname{Tr}(M^x_aM^y_b) = \operatorname{Tr}(I_d\, I_d) = d$; so for these games the supremum is a genuine least upper bound in $[0,1]$ and the fallback to $0$ is not triggered. This is a consequence, not something the definition states.) Because it is a supremum, $\omega_s(\mathcal{G}) = 1$ asserts that strategy values come arbitrarily close to $1$; it does **not** assert that some finite-dimensional strategy attains $1$.

## 7. Degenerate and edge cases, collected

- **Alphabets are never empty**: $|X_g| = n_X+1$ and $|A_g| = n_A+1$. Singletons are allowed. If $n_X = 0$ there is a single question $0$ and $\mu_g(0,0) = 1$ in both branches of the definition. If $n_A = 0$ there is a single answer $0$, every POVM is forced to be $M^x_0 = I_d$, and every strategy has the same value $\sum_{x,y}\mu_g(x,y)\,\mathbf{1}[(x,y,0,0)\in\mathrm{acc}]$.
- **Zero total weight** ($T_g = 0$): $\mu_g$ is the point mass at the question pair $(0,0)$.
- **Out-of-range list entries** (first two coordinates $> n_X$ in $w$ or $\mathrm{acc}$; last two coordinates $> n_A$ in $\mathrm{acc}$) are silently ignored. **Duplicates** in $w$ are summed; duplicates in $\mathrm{acc}$ are irrelevant.
- **Equal questions with equal answers** are accepted only when $(x,x,a,a) \in \mathrm{acc}$.
- **Weights are natural numbers**, so $\mu_g$ is rational-valued; zero weights are allowed and contribute nothing.
- **Division**: by $T_g$ only in the branch $T_g \neq 0$; by $d$ only with $d \ge 1$. No division by zero occurs.
- **Real part** of the trace $\operatorname{Tr}(M^x_a M^y_b)$ is taken.
- **Supremum fallback**: value $0$ for an empty or unbounded family of strategy values (§6 notes why this case does not arise for the games $\mathcal{G}_g$).
- **$1/2$** is the real number $0.5$.
- **"Halting"** is convergence of $\varphi_c$ at the single input $0 \in \mathbb{N}$.
- **"Computable"** is Mathlib's `Computable` with respect to the standard Gödel numberings of §3; no complexity bound of any kind.
- **Only finite-dimensional strategies** ($d \in \mathbb{N}$, $d \ge 1$) enter the supremum; nothing infinite-dimensional or commuting-operator is involved, and the projections for different questions need not commute.

## 8. Exact logical shape

- The outer connective is $\exists g$ (existence, not uniqueness), followed by a conjunction: computability of $g$, and a universal statement over all codes $c$.
- For each $c$ both clauses are asserted. Completeness is an **equality** $\omega_s(\mathcal{G}_{g(c)}) = 1$ (exactly $1$, as a supremum). Soundness is a **non-strict** inequality $\omega_s(\mathcal{G}_{g(c)}) \le \tfrac12$.
- Each clause is a one-directional implication. Since for every $c$ exactly one of $\varphi_c(0)\!\downarrow$ and $\varphi_c(0)\!\uparrow$ holds, the two clauses together are equivalent (using only excluded middle) to: for all $c$,

$$
\omega_s(\mathcal{G}_{g(c)}) \in (-\infty, \tfrac12] \cup \{1\},
\qquad
\varphi_c(0)\!\downarrow \iff \omega_s(\mathcal{G}_{g(c)}) = 1 \iff \omega_s(\mathcal{G}_{g(c)}) > \tfrac12 .
$$

In particular the value is never in the open interval $(\tfrac12, 1)$.

- Nothing is asserted about any strategy attaining the value, about the dimension needed to approach it, about the behaviour of $\varphi_c$ on inputs other than $0$, or about $g$ beyond its computability and the two value conditions.
