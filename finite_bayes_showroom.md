# Bayes on a Finite Grid

### A Constructive Alternative to Kolmogorov, with $1/D$ Error Bound

*Konrad Wojnowski — VOID Theory*

---

## 1. The thesis

Kolmogorov's axioms of probability presuppose an infinite $\sigma$-algebra of events. The construction is not optional: countable additivity (Axiom III, sometimes Axiom 6 depending on edition) is what makes the standard machinery — limits, expectations, integration over hypothesis spaces — well-defined. Without it, classical Bayes loses its closure properties. With it, every Bayesian inference becomes formally entangled with the actual infinite.

This document presents a constructive alternative. We define probability on a finite grid $\{0, 1/D, 2/D, \ldots, 1\}$ for a fixed denominator $D \in \mathbb{N}$, replace $\sigma$-algebras with simple integer pairs, and show that Bayesian updating on this grid carries a worst-case error of $1/D$, derived as a theorem rather than assumed as a limit. No countable additivity is invoked at any point. No real-valued continuum is required. The whole construction is machine-verified in Coq.

The argument is short. Section 2 shows where infinity sits in the standard setup. Section 3 gives the finitist construction. Section 4 states the key theorem and indicates the proof. Section 5 says what is given up and what is gained.

---

## 2. Where infinity sits in standard Bayes

The classical Bayesian update is

$$
P(H \mid E) \;=\; \frac{P(E \mid H) \cdot P(H)}{P(E \mid H) \cdot P(H) + P(E \mid \neg H) \cdot P(\neg H)}.
$$

This formula is finite-looking, but its mathematical foundation is not. Three places of infinitary commitment:

**(i) The probability space.** Kolmogorov requires a triple $(\Omega, \mathcal{F}, P)$ where $\mathcal{F}$ is a $\sigma$-algebra over $\Omega$: closed under complement and *countable* unions. Even when $\Omega$ is finite, the requirement of countable additivity ensures coherence with limit arguments and integration. The whole apparatus is inherited from real analysis.

**(ii) The values.** Probabilities are real-valued: $P : \mathcal{F} \to [0, 1] \subset \mathbb{R}$. The codomain is uncountable.

**(iii) The observer.** Bayesian rationality, in its idealised form, presupposes an agent capable of performing the update with infinite precision and without computational cost. This is occasionally acknowledged (*e.g.* in bounded rationality literature) but rarely formalised; the cost is either zero or unmentioned.

These three commitments are coupled. Each can be relaxed in isolation, but the standard machinery breaks if any of them is dropped without replacement.

---

## 3. The finitist construction

We replace each commitment with a finite analogue.

### 3.1 Finite probability

Fix $D \in \mathbb{N}$, the *denominator* (also: *resolution*). A probability is a pair

$$
p = (n, D), \qquad n \in \{0, 1, \ldots, D\},
$$

read as $p = n/D$. We call this a *frozen* probability when $D$ is treated as a parameter shared across an inference (analogous to fixing the resolution of a measurement instrument).

The probability values live on a finite grid

$$
G_D = \left\{ \tfrac{0}{D},\; \tfrac{1}{D},\; \tfrac{2}{D},\; \ldots,\; \tfrac{D}{D} \right\}.
$$

Probabilistic statements are statements over $G_D$, not over $[0,1] \subset \mathbb{R}$.

### 3.2 No absolute certainty, no absolute impossibility

We further constrain the numerator to lie strictly between the endpoints:

$$
n \in \{1, 2, \ldots, D-1\}.
$$

The endpoints $0$ and $D$ are excluded as a structural axiom: nothing is ever assigned probability exactly $0$ (impossibility) or exactly $1$ (certainty). This is the void-theoretic commitment that absolute knowledge is unavailable to a finite observer. Any update that would push the numerator to $0$ or $D$ is *clamped* — the system saturates at $1/D$ from below and at $(D-1)/D$ from above.

### 3.3 The three-valued epistemic state

A Boolean comparison in this framework returns not $\{\top, \bot\}$ but

$$
\mathrm{Bool}_3 \;=\; \{\top,\; \bot,\; \mathrm{B}_{?}\}.
$$

The third value $\mathrm{B}_{?}$ ("BUnknown") is reserved for the case where the comparison cannot be performed within the available budget. It is *not* the same as undecidability in the recursion-theoretic sense; it is *budget exhaustion*. Granted enough budget, every $\mathrm{B}_{?}$ resolves to $\top$ or $\bot$. The third value is thus a *temporary* epistemic state, not a permanent metaphysical one.

### 3.4 Budget and trace

Every operation in the system — comparison, addition, multiplication, division — consumes from a finite budget $B \in \mathbb{N}$ and emits an irreversible residue $\sigma \in \mathbb{N}$ (the *Spur*). The signature of a typical operation is

$$
\mathrm{op} : \mathrm{Input} \times B \;\longrightarrow\; \mathrm{Output} \times B' \times \sigma,
$$

with $B' \le B$ and $\sigma + B' = B$ (conservation). When $B$ is exhausted, the operation returns $\mathrm{B}_{?}$. No operation is free; no result is ever produced without paying.

This replaces commitment (iii) — the unbounded ideal observer — with an explicit cost accounting.

---

## 4. Finite Bayes

### 4.1 Two implementations

The Bayesian update on the finite grid admits two implementations. Both preserve the denominator $D$ throughout the computation.

**Exact (multiplicative).** Given a prior $\pi = n/D$, a likelihood $P(E \mid H) = a/D$, and a counter-likelihood $P(E \mid \neg H) = c/D$, compute

$$
\pi^{\mathrm{exact}}_n \;=\; \left\lfloor \frac{D \cdot a \cdot n}{a \cdot n + c \cdot (D - n)} \right\rfloor.
$$

This is the standard Bayes formula evaluated in integer arithmetic, with floor division to keep the result on the grid. It costs $O(D^2)$ operations in the worst case and consumes budget for each multiplication, addition, subtraction, and division.

**Additive (approximate).** Replace the full computation with a precomputed *shift* $s$ and an *evidence direction* $d \in \{\mathrm{Supports}, \mathrm{Refutes}, \mathrm{Neutral}\}$:

$$
\pi^{\mathrm{add}}_n \;=\;
\begin{cases}
\min(n + s,\; D-1) & \text{if } d = \mathrm{Supports}, \\
\max(n - s,\; 1)   & \text{if } d = \mathrm{Refutes}, \\
n                  & \text{if } d = \mathrm{Neutral}.
\end{cases}
$$

This costs only addition, subtraction, and clamping. The shift $s$ is itself derived from the likelihoods, but once derived can be reused across many updates.

The two implementations agree exactly when no clamping is required. They differ only at the boundary, where the additive version is forced to saturate.

### 4.2 The error bound

We state the result of the file `void_finite_bayes.v`:

> **Theorem (`pure_bayes_error_bound`).** *For every exact posterior numerator $n^\star$ and every denominator $D$, if $n^\star \le D$, then*
>
> $$
> \big|\, n^\star - \min(n^\star, D-1) \,\big| \;\le\; 1
> \qquad \text{and} \qquad
> \big|\, \max(n^\star, 1) - n^\star \,\big| \;\le\; 1.
> $$

In words: **clamping the posterior to the interval $[1/D,\; (D-1)/D]$ moves it by at most one grid-step of resolution**. Translated into rational form,

$$
\big|\, p^{\mathrm{add}} - p^{\mathrm{exact}} \,\big| \;\le\; \tfrac{1}{D}.
$$

The proof is purely structural. It uses no real numbers, no measure theory, no limits. It is an induction on $\mathrm{Fin}$, the finite inductive type, and is fully machine-checked.

This theorem is the Kolmogorov critique in one line: *Bayesian updating on a finite grid with clamping introduces at most $1/D$ error*, and the bound is tight. There is no $\sigma$-algebra anywhere in the statement or in the proof.

### 4.3 The compressed slogan

| Standard Bayes | Finite Bayes |
| --- | --- |
| $\sigma$-algebra over $\Omega$ | finite grid $G_D$ |
| Real-valued $P : \mathcal{F} \to [0,1]$ | Pair $(n, D)$ with $n \in \{1, \ldots, D-1\}$ |
| Idealised observer | Budget-bounded observer |
| Limit of error: $\lim_{D \to \infty} 1/D = 0$ | Theorem: error $\le 1/D$ |
| $1/\infty = 0$ (assumed) | $1/D$ for chosen $D$ (proved) |

The right column buys, with no infinity in the premises, what the left column buys at the cost of a countably infinite axiom system.

---

## 5. What is given up; what is gained

### Given up

- **Real-valued precision.** Probability values come at finite resolution $1/D$. For applications where $D$ can be made very large at acceptable cost, this is no loss. For applications that genuinely require continuum-valued probabilities (some physics, some gauge theories), the construction does not apply.
- **Limit arguments.** Theorems that depend on $\lim_{n \to \infty}$ are unavailable in this framework. Whether this is a loss depends on whether the limit was doing real work or smuggling unbounded computation through the back door.
- **Conjugate priors and continuous distributions.** Beta, Dirichlet, Gaussian — these are continuous-domain objects and have no direct analogue here. Discrete approximations on $G_D$ exist; whether they suffice is a question for the application.

### Gained

- **No infinity is invoked.** The whole construction is finite. There is no axiom of choice, no countable additivity, no real number. The mathematics is constructive in the strict sense.
- **Every operation is paid for.** The budget mechanism makes computational cost a first-class quantity. An update is not an idealised inference; it is a process with a price tag and a receipt.
- **Every operation is auditable.** The Spur (residue) records what was paid, irreversibly. A computation can be inspected for what it cost and where the cost went.
- **Budget exhaustion is a primitive epistemic state.** $\mathrm{B}_{?}$ is not "I don't know" in the philosophical sense; it is "I cannot afford to know right now." This is honest about the conditions under which an inference is even attempted.
- **The $1/D$ bound is a theorem, not an assumption.** It is derived from the structure of finite arithmetic. It holds for any $D$ the user chooses. The error is *known*, not asymptotic.

---

## 6. Why this matters

The standard Bayesian framework is mathematically well-founded but built on an inheritance whose costs are now coming due. The infinitary commitments — $\sigma$-algebras, real-valued measures, idealised observers — are not free. They require infinite computational resources to instantiate exactly, and the gap between the ideal and the implementation is generally papered over by approximation arguments that themselves rely on limits.

A finitist alternative is not a degraded version of the standard framework. It is a different framework that produces verifiable bounds in place of asymptotic guarantees, and it pays explicit budget where the standard framework assumes free computation.

For applications where computational sustainability matters — bounded-resource learning, AI systems running on real hardware, formal verification of probabilistic claims — the trade is favourable. The user picks $D$ to set the resolution; the system gives back, in return, a guarantee that no inference will silently exceed its stated cost.

This document concerns only the Bayesian fragment of VOID Theory. The full system extends this approach to observation, learning, geometry, and entropy, all on the same finitist primitives. The Coq sources are open and machine-verified end to end.

---

*Source file: `void_finite_bayes.v`. Companion modules: `void_finite_minimal.v` (primitives), `void_probability_minimal.v` (operations on $G_D$). The full repository is finitistic throughout, with no axioms beyond the existence of a maximum finite number.*
