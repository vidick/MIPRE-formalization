# Read-back of `Def_MIPRE_HaltingGameValue.lean`

*Scope.* This read-back renders what the thirteen declarations of the bundle literally define, in source order, together with the one shared binder context that sits between them. The bundle contains **no theorem**: every item is a structure, a definition or an instance, and the last item *defines a proposition* (a statement that may be true or false) without proving or assuming it. Two pieces of ambient context apply throughout: (i) the bundle imports only Mathlib (its matrix-order module and its partial-recursive-code module), so every notion not defined in the bundle is Mathlib's; (ii) it switches on Mathlib's *scoped* Loewner order on complex matrices, under which, in the words of the bundle's own comment, $0 \le A$ holds exactly when $A$ is positive semidefinite. Throughout, "finite type" means a type equipped with a finiteness structure (a `Fintype` assumption), and every sum $\sum_{x \in X}$ over such a type is the finite sum over all of its elements, equal to $0$ when the type is empty.

### 1. `POVM X d` (structure)

Parameters: two types $X$ and $d$, in arbitrary universes, together with three typeclass assumptions: $X$ is finite, $d$ is finite, and $d$ has decidable equality. (No decidable equality is assumed on $X$.) A term of this structure consists of three fields:

- **`mats`**: a function assigning to each $x \in X$ a *self-adjoint* complex matrix $M_x$ with rows and columns indexed by $d$; that is, $M_x \in \mathbb{C}^{d \times d}$ with $M_x^{*} = M_x$, where $^{*}$ is the conjugate transpose. Formally each $M_x$ is an element of the additive subgroup of self-adjoint elements of the matrix ring, so it carries its self-adjointness proof with it; later declarations write `.val` for its underlying matrix.
- **`nonneg`**: for every $x \in X$, $0 \le M_x$, where $\le$ is the scoped Loewner order restricted to self-adjoint matrices. By the bundle's stated reading of that order, this says that $M_x$ is positive semidefinite: $M_x$ is Hermitian (already guaranteed by the previous field) and $v^{*} M_x v \ge 0$ for every $v \in \mathbb{C}^{d}$.
- **`normalized`**: $\sum_{x \in X} M_x = 1$, the sum being taken in the additive group of self-adjoint matrices and $1$ being the identity matrix $I_d$; so $\sum_{x \in X} M_x = I_d$ as matrices.

Edge cases. If $X$ is empty, the sum is the zero matrix and the third field demands $0 = I_d$, which holds only when $d$ is empty (the unique $0 \times 0$ matrix). If $d$ is empty, $\mathbb{C}^{d \times d}$ has a single element, which is simultaneously $0$ and $I_d$, so *every* family qualifies. Nothing in the structure requires the $M_x$ to be projections, to commute with one another, to be nonzero, or to be pairwise distinct.

### 2. `SynchronousGame X A` (structure)

Parameters: two types $X$ (read as questions) and $A$ (read as answers), in arbitrary universes, with three typeclass assumptions: $X$ finite, $A$ finite, and $A$ with decidable equality. The decidable-equality assumption on $A$ is carried as a parameter; none of the five fields refers to it. The fields:

- **`μ`**: a real-valued function $\mu : X \times X \to \mathbb{R}$ (given in curried form, written $\mu(x,y)$);
- **`μ_nonneg`**: $\mu(x,y) \ge 0$ for all $x, y \in X$;
- **`μ_sum_one`**: $\displaystyle \sum_{x \in X} \sum_{y \in X} \mu(x,y) = 1$;
- **`D`**: a Boolean-valued function $D : X \times X \times A \times A \to \{\mathtt{true}, \mathtt{false}\}$;
- **`synchronous`**: for all $x \in X$ and all $a, b \in A$ with $a \ne b$, $D(x, x, a, b) = \mathtt{false}$.

Edge cases and non-requirements. Since the double sum must equal $1$ and an empty sum is $0$, **no** synchronous game exists on an empty question type $X$. The answer type $A$ may be empty, in which case $D$ is the empty function and the last field holds vacuously. Nothing requires $\mu$ to be symmetric ($\mu(x,y) = \mu(y,x)$), $D$ to be symmetric ($D(x,y,a,b) = D(y,x,b,a)$), $\mu$ to have full support, or $D(x,x,a,a)$ to take any particular value: on equal questions only the *unequal*-answer case is forced to $\mathtt{false}$.

### Shared binder context (items 3, 4, 5)

After item 2 the source fixes implicit parameters $X$ and $A$ (arbitrary types in arbitrary universes) with the assumptions $X$ finite, $A$ finite, $A$ with decidable equality. Items 3, 4 and 5 below each take these as additional implicit arguments, whether or not their bodies use them.

### 3. `SyncStrategy G` (structure)

Parameter: a synchronous game $G$ on $(X, A)$ as in item 2, with the implicit $X$, $A$ and the three assumptions of the shared context. A term consists of four fields:

- **`d`**: a natural number $d$;
- **`d_pos`**: $0 < d$, i.e. $d \ge 1$;
- **`povm`**: for every question $x \in X$, a POVM in the sense of item 1 whose index type is $A$ and whose matrix index type is $\{0, 1, \dots, d-1\}$ (with its standard finiteness and decidable-equality structure). Unfolded: for each $x \in X$ and $a \in A$ a matrix $M^{x}_{a} \in \mathbb{C}^{d \times d}$ with $(M^x_a)^{*} = M^x_a$ and $v^{*} M^{x}_{a} v \ge 0$ for all $v \in \mathbb{C}^d$, and, for each $x$, $\sum_{a \in A} M^{x}_{a} = I_d$;
- **`projective`**: for all $x \in X$ and $a \in A$, $M^{x}_{a}\, M^{x}_{a} = M^{x}_{a}$ as $d \times d$ matrices (idempotence under matrix multiplication).

Observations. The game $G$ appears only as a parameter: none of the four fields mentions $\mu$ or $D$, so two games with the same $X$ and $A$ have literally the same strategies. No relation between operators attached to *different* questions is imposed; in particular $M^x_a$ and $M^y_b$ for $x \ne y$ need not commute. No state (vector or density matrix) is part of a strategy. Because $d \ge 1$, the identity $I_d$ is nonzero, so the normalization $\sum_{a \in A} M^x_a = I_d$ cannot be met when $A$ is empty: for $A = \emptyset$ the type of strategies is empty (whenever a game exists at all, i.e. $X \ne \emptyset$). For $A \ne \emptyset$ strategies exist in every dimension $d \ge 1$, for instance $M^x_{a_0} = I_d$ for one fixed answer $a_0$ and $M^x_a = 0$ for $a \ne a_0$.

### 4. `strategyValue G S` (definition; a real number)

Inputs: a synchronous game $G$ on $(X, A)$ (item 2) and a synchronous strategy $S$ for it (item 3), with the implicit $X$, $A$ and assumptions of the shared context. Writing $\mu$ and $D$ for the fields of $G$, and $d$ and $M^{x}_{a}$ for those of $S$, the definition is the finite sum

$$
\omega(G, S) \;:=\; \sum_{x \in X} \sum_{y \in X} \sum_{a \in A} \sum_{b \in A}\; \mu(x,y)\cdot \mathbf{1}\big[D(x,y,a,b) = \mathtt{true}\big]\cdot \frac{\operatorname{Re}\,\operatorname{tr}\!\big(M^{x}_{a}\, M^{y}_{b}\big)}{d},
$$

where: $\mathbf{1}[\cdot]$ is the real indicator, equal to $1$ if $D(x,y,a,b)$ is $\mathtt{true}$ and to $0$ if it is $\mathtt{false}$; $M^x_a M^y_b$ is the matrix product, with the operator belonging to the *first* question $x$ on the left; $\operatorname{tr}$ is the complex trace of that $d \times d$ matrix; $\operatorname{Re}$ takes its real part, so whatever imaginary part the trace has is discarded; and the division is real division by the real number $d$, which is nonzero because $d \ge 1$. The result is a real number; the definition itself builds in no bound on its sign or size.

### 5. `gameValue G` (definition; a real number)

Input: a synchronous game $G$ on $(X, A)$, with the implicit $X$, $A$ and assumptions of the shared context. The definition is

$$
\omega(G) \;:=\; \sup_{S}\; \omega(G, S),
$$

the supremum in $\mathbb{R}$ of the family $\big(\omega(G,S)\big)_S$ of item 4, indexed by *all* synchronous strategies $S$ for $G$ in the sense of item 3: all dimensions $d \ge 1$ and all families of positive semidefinite Hermitian idempotent matrices $(M^x_a)$ with $\sum_a M^x_a = I_d$, simultaneously, so in general an infinite family. This is Mathlib's supremum of a real-valued family, which equals the least upper bound when the family is nonempty and bounded above, and is **defined to be $0$ otherwise**, that is, when no strategy exists at all (for instance when $A$ is empty) or when the set of values is not bounded above. The bundle contains no statement bounding $\omega(G,S)$, so this convention is part of the literal meaning. The supremum is not asserted to be attained by any strategy.

### 6. `GameData` (structure)

No parameters. A term consists of four fields with no constraints between them: a natural number $n_X$; a natural number $n_A$; a finite list $w$ of triples $(x, y, k)$ of natural numbers; and a finite list $\mathrm{acc}$ of quadruples $(x, y, a, b)$ of natural numbers. (The products are right-nested, $\mathbb{N} \times (\mathbb{N} \times \mathbb{N})$ and $\mathbb{N} \times (\mathbb{N} \times (\mathbb{N} \times \mathbb{N}))$, which is how later definitions project out the components.) Either list may be empty, may contain repeated entries, and may contain entries whose coordinates exceed $n_X$ or $n_A$; the structure itself imposes nothing.

### 7. `GameData.equivTuple` (definition; a bijection)

A bijection (equivalence of types) between the type of item 6 and $\mathbb{N} \times \mathbb{N} \times \mathrm{List}(\mathbb{N}^3) \times \mathrm{List}(\mathbb{N}^4)$, given in the forward direction by $g \mapsto (n_X, n_A, w, \mathrm{acc})$ and in the backward direction by reassembling a tuple into the four fields in the same order. Only the two maps are written in the source; the two inverse-law fields of the equivalence are not spelled out in the text.

### 8. `instance : Primcodable GameData`

This declares that game descriptions are *primitively codable* in Mathlib's sense (an injective encoding into $\mathbb{N}$ whose decoding is primitive recursive), by transporting along the bijection of item 7 the encoding Mathlib already provides for the tuple type: a game description $g$ is encoded as the natural number that Mathlib's standard encoding (pairing for products, the standard encoding of lists of naturals) assigns to $(n_X, n_A, w, \mathrm{acc})$, and decoding goes back through the inverse bijection. The role of this instance in the bundle is to give meaning, in item 13, to "a function with values in game descriptions is computable".

### 9. `GameData.questionWeight g x y` (definition; a natural number)

Inputs: a game description $g$ (item 6) and two natural numbers $x, y$ (arbitrary naturals, not restricted to be $\le n_X$). The value is

$$
W_g(x,y) \;:=\; \sum_{\substack{(x', y', k) \in w \\ x' = x,\; y' = y}} k ,
$$

the sum, over the entries of the list $w$ in order and with multiplicity, of the third component $k$ of every entry whose first two components are exactly $(x, y)$. If no entry matches (in particular if $w$ is empty) the value is $0$.

### 10. `GameData.totalWeight g` (definition; a natural number)

Input: a game description $g$. The value is

$$
T_g \;:=\; \sum_{x = 0}^{n_X} \sum_{y = 0}^{n_X} W_g(x, y),
$$

the double sum of item 9 over $x, y \in \{0, 1, \dots, n_X\}$. Entries of $w$ whose first or second coordinate exceeds $n_X$ contribute nothing to $T_g$ (though they do contribute to $W_g$ at their own coordinates). $T_g = 0$ exactly when every entry of $w$ with both coordinates in $\{0, \dots, n_X\}$ has weight $k = 0$, including the case that there is no such entry.

### 11. `GameData.toGame g` (definition; a synchronous game)

Input: a game description $g$. Output: a synchronous game in the sense of item 2 whose question type is $X = \{0, 1, \dots, n_X\}$ and whose answer type is $A = \{0, 1, \dots, n_A\}$; both have at least one element whatever $n_X$ and $n_A$ are. Its fields are:

- the distribution

$$
\mu(x,y) \;=\; \begin{cases} 1 & \text{if } T_g = 0,\ x = 0 \text{ and } y = 0,\\[2pt] 0 & \text{if } T_g = 0 \text{ and } (x,y) \ne (0,0),\\[2pt] W_g(x,y)\,/\,T_g & \text{if } T_g \ne 0, \end{cases}
$$

with $W_g$ and $T_g$ as in items 9 and 10, the division being real division of the real casts of two natural numbers. So when $T_g \ne 0$, $\mu(x,y)$ is the ratio of the in-range weight of $(x,y)$ to the total in-range weight; when $T_g = 0$, $\mu$ is the point mass at the question pair $(0, 0)$;

- the decision function

$$
D(x,y,a,b) \;=\; \begin{cases} \mathtt{false} & \text{if } x = y \text{ and } a \ne b,\\[2pt] \big[(x, y, a, b) \in \mathrm{acc}\big] & \text{otherwise,} \end{cases}
$$

where $[(x,y,a,b) \in \mathrm{acc}]$ is $\mathtt{true}$ exactly when the quadruple of underlying natural numbers occurs at least once in the list $\mathrm{acc}$. In particular: for $x \ne y$ the answer pair $(a,b)$ is accepted if and only if $(x,y,a,b)$ is listed, whether or not $a = b$; for $x = y$ and $a = b$ it is accepted if and only if $(x,x,a,a)$ is listed; for $x = y$ and $a \ne b$ it is rejected regardless of $\mathrm{acc}$. Entries of $\mathrm{acc}$ with any coordinate outside the two alphabets are never consulted, and repetitions in $\mathrm{acc}$ are irrelevant;

- the three propositional fields of item 2 (nonnegativity of $\mu$, total mass $1$, the synchronous constraint on $D$) are discharged by proofs written in the source.

### 12. `HaltsOnEmptyInput c` (definition; a proposition)

Input: a term $c$ of Mathlib's type of codes for partial recursive functions (its inductive Gödel numbering of the partial recursive functions $\mathbb{N} \rightharpoonup \mathbb{N}$, with its evaluation map $c \mapsto \varphi_c$). The proposition is that the partial function $\varphi_c$ is *defined at the input $0$*, written $\varphi_c(0)\!\downarrow$. The input is literally the natural number $0$; the words "empty input" in the name are the docstring's gloss and are not part of the definition.

### 13. `HaltingReducesToGameValue` (definition of a proposition; not a theorem)

No inputs. This defines the following proposition; the bundle neither proves nor assumes it.

$$
\exists\, g : \mathrm{Code} \to \mathrm{GameData}\ \text{ such that }\ \mathrm{Computable}(g)\ \wedge\ \forall c : \mathrm{Code},\ \Big( \varphi_c(0)\!\downarrow\ \Rightarrow\ \omega\big(\mathrm{toGame}(g(c))\big) = 1 \Big)\ \wedge\ \Big( \neg\,\varphi_c(0)\!\downarrow\ \Rightarrow\ \omega\big(\mathrm{toGame}(g(c))\big) \le \tfrac12 \Big).
$$

Unfolding every ingredient. $\mathrm{Code}$ is Mathlib's type of codes and $\varphi_c(0)\!\downarrow$ is the proposition of item 12 ("$\varphi_c$ is defined at the natural number $0$"). $g$ is an arbitrary total function from codes to game descriptions (item 6). $\mathrm{Computable}(g)$ is Mathlib's notion: with codes and game descriptions each encoded into $\mathbb{N}$ (the latter by item 8), the function on natural numbers that decodes $n$ to a code where possible, applies $g$, and encodes the result, is a partial recursive function in Mathlib's sense. Nothing else is required of $g$: no injectivity and no resource bound, only computability. For each code $c$, $\mathrm{toGame}(g(c))$ is the synchronous game of item 11 built from the description $g(c)$: its question alphabet is $\{0, \dots, n_X\}$ and its answer alphabet $\{0, \dots, n_A\}$, where $n_X$ and $n_A$ are the first two components of $g(c)$ (so the alphabet sizes depend on $c$); its distribution is the normalized in-range weight list of $g(c)$, or the point mass at $(0,0)$ when the total in-range weight is $0$; and its decision function accepts exactly the quadruples listed in $g(c)$'s acceptance list, except that unequal answers to equal questions are always rejected. $\omega(\cdot)$ is the game value of item 5: the real supremum, over all dimensions $d \ge 1$ and all families $(M^x_a)_{x \in X, a \in A}$ of Hermitian, positive semidefinite, idempotent $d \times d$ complex matrices with $\sum_{a} M^x_a = I_d$ for every $x$, of the quantity $\sum_{x, y, a, b} \mu(x,y)\, \mathbf{1}[D(x,y,a,b) = \mathtt{true}]\, \operatorname{Re}\operatorname{tr}(M^x_a M^y_b)/d$ of item 4, with Mathlib's convention that the supremum of an empty or not-bounded-above family is $0$. For the games produced by item 11 the indexing family is nonempty (both alphabets are nonempty, so the one-dimensional strategy $M^x_0 = (1)$, $M^x_a = (0)$ for $a \ne 0$ exists for every such game); the bundle contains no statement that the family of values is bounded above, and under the convention a not-bounded-above family would have supremum $0$.

The two conclusions are stated as implications, not as biconditionals. "$= 1$" is an equality of real numbers between the supremum and $1$; it does not assert that any strategy attains the value $1$. "$\le \tfrac12$" is a non-strict inequality in $\mathbb{R}$, where $\tfrac12$ is the real number one half (real division $1/2$, not integer division). Since, classically, every code either satisfies $\varphi_c(0)\!\downarrow$ or does not, the two implications together say something about every code.
